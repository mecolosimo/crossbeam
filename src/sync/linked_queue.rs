use std::sync::atomic::Ordering::{Acquire, Release, Relaxed};
use std::sync::{Arc, Mutex, Condvar, MutexGuard};
use std::{ptr};
use std::time::{Duration, Instant};

use mem::epoch::{self, Atomic, Owned, Shared};
use mem::CachePadded;

// #[derive(Debug)] // Condvar doesn't have Debug trait
pub struct LinkedBlockingQueue<T> {
    capacity: u64,
    count: Atomic<u64>,                             // atomic u64 would be nice, but seems to be an issue
    // head of linked list; head.item == null
    head: CachePadded<Atomic<Node<T>>>,
    // tail of linked list; tail.next == null
    tail: CachePadded<Atomic<Node<T>>>,

    // locks and conditionals
    not_empty: Arc< (Mutex<bool>, Condvar) >,      // take lock
    not_full: Arc< (Mutex<bool>, Condvar) >,       // put lock

}

#[derive(Debug)]
struct Node<T> {
    /// Linked list node
    item: Option<T>,
    // Either:
    //      - the real successor Node
    //      - this Node, successor is head.next
    //      - null, meaning there is no successor (this is the tail node)
    next: Atomic<Node<T>>,
}

impl<T> LinkedBlockingQueue<T> {
    /// Create a new, unlimited, empty queue.
    pub fn new(capacity: Option<u64>) -> LinkedBlockingQueue<T> {
        let mut c = u64::max_value();
        if capacity.is_some() {
            c = capacity.unwrap();
        }
        let q =  LinkedBlockingQueue {
            capacity: c,
            count: Atomic::new(0u64),
            head: CachePadded::new(Atomic::null()),
            tail: CachePadded::new(Atomic::null()),
            not_empty: Arc::new((Mutex::new(false), Condvar::new())),
            not_full: Arc::new((Mutex::new(true), Condvar::new()) ),

        };

        let head = Owned::new( Node {
            item: None,
            next: Atomic::null(),
        });
        let guard = epoch::pin();
        let tail = q.head.store_and_ref(head, Relaxed, &guard);
        q.tail.store_shared(Some(tail), Relaxed);

        q
    }

    pub fn remaining_capacity(&self) -> u64 {
        let guard = epoch::pin();
        let count =  self.count.load(Relaxed, &guard).unwrap();
        self.capacity - **count
    }

    pub fn size(&self) -> u64 {
        self.capacity
    }

    pub fn is_empty(&self) -> bool {
        let guard = epoch::pin();
        let count =  self.count.load(Relaxed, &guard).unwrap();
        **count == 0u64
    }

    #[inline(always)]
    fn signal_not_full(&self) {
        let &(ref lock, ref cvar) = &*self.not_full;
        let mut not_full = lock.lock().unwrap();
        *not_full = true;
        cvar.notify_one();
    }

    #[inline(always)]
    fn signal_not_empty(&self) {
        let &(ref lock, ref cvar) = &*self.not_empty;
        let mut not_empty = lock.lock().unwrap();
        *not_empty = true;
        cvar.notify_one();
    }

    #[inline(always)]
    fn enqueue(&self, guard: &epoch::Guard,
               onto: Shared<Node<T>>,
               n: Owned<Node<T>>)
               -> Result<(), Owned<Node<T>>> {

        // is `onto` the actual tail?
        if let Some(next) = onto.next.load(Acquire, guard) {
            // if not, try to "help" by moving the tail pointer forward
            self.tail.cas_shared(Some(onto), Some(next), Release);
            Err(n)
        } else {
            // looks like the actual tail; attempt to link in `n`
            onto.next.cas_and_ref(None, n, Release, guard).map(|shared| {
                // try to move the tail pointer forward
                self.tail.cas_shared(Some(onto), Some(shared), Release);
            })
        }
    }

    fn put_internal(&self, t: T,  timeout: Option<Duration>) -> bool {
        let guard = epoch::pin();
        let &(ref lock, ref cvar) = &*self.not_full;

        // allocate up front
        let mut node = Owned::new( Node {
            item: Some(t),
            next: Atomic::null(),
        } );

        {
            // scope for not_full Mutex
            let mut not_full = lock.lock().unwrap();        // locked
            if let Some(duration) = timeout {
                let start = Instant::now();
                loop {
                    if *not_full == false {
                        if start.elapsed() > duration {
                            // waited long enough and still empty (might have returned early)
                            return false;
                        }
                        let (mg, mtr) = cvar.wait_timeout(not_full, duration).unwrap();
                        if mtr.timed_out() {
                            return false;
                        }
                        not_full = mg;

                    } else {
                        break;
                    }
                }
            } else {
                loop {
                    if *not_full == false {
                        not_full = cvar.wait(not_full).unwrap();
                    } else {
                        break;
                    }
                }
            }
            // have lock-back and should have capacity
            // increase count (a take can happen before we get back)
            loop {
                let count = self.count.load(Acquire, &guard).unwrap();
                let new_count = Owned::new(**count + 1);
                // break if set, otherwise loop - it should have only decreased
                match self.count.cas(Some(count), Some(new_count), Release) {
                    Ok(_) => break,
                    Err(_) => {},       // possible take
                }
            }

            // insert
            loop {
                let tail = self.tail.load(Acquire, &guard).unwrap();

                // Attempt to insert onto the `tail` snapshot; fails if
                // `tail.next` has changed.
                match self.enqueue(&guard, tail, node) {
                    Ok(_) => break,
                    Err(n) => {
                        // replace the node, retry whole thing
                        node = n
                    }
                }
            }

            let count = self.count.load(Acquire, &guard).unwrap();
            if **count == self.capacity {
                *not_full = false;          // we are full
            }
        } // unlocked not_full (drops out of scope, only way to release lock)

        let count = self.count.load(Acquire, &guard).unwrap();
        if **count > 0 {                // a take could have occurred
            self.signal_not_empty();    // signal threads waiting to take
        }
        true
    }

    pub fn put_timeout(&self, t: T, timeout: Duration) -> bool {
        self.put_internal(t, Some(timeout))
    }

    pub fn put(&self, t: T) {
        self.put_internal(t, None);
    }

    #[inline(always)]
    fn dequeue(&self, guard: &epoch::Guard ) -> Result<Option<T>, ()>  {
        let head = self.head.load(Acquire, guard).unwrap();
        if let Some(next) = head.next.load(Acquire, guard) {
                if self.head.cas_shared(Some(head), Some(next), Release) {
                    if let Some(ref t) = next.item {
                        unsafe {
                            guard.unlinked(head);
                            Ok(Some(ptr::read(t)))
                        }
                    } else {
                        Ok(None)
                    }
                } else {
                    Err(())
                }

        } else {
            Ok(None)
        }
    }

    fn take_internal(&self, guard: &epoch::Guard, mut not_empty: MutexGuard<bool>) -> T {
        // loops until we can decrease the count, shouldn't be looping until something is available
        loop {
            match self.dequeue(&guard) {
                Ok(Some(r)) => {
                    // decrease count
                    loop {
                        let count = self.count.load(Acquire, &guard).unwrap();
                        let new_count = Owned::new(**count - 1);
                        // break if set, otherwise loop - it should have only increased
                        match self.count.cas_and_ref(Some(count), new_count, Release, &guard) {
                            Ok(count) => {
                                if **count == 0 {
                                    *not_empty = false;         // we are empty
                                }
                                // till holding the  not_empty mutex, if we call signal_not_empty, could dead-lock
                                if **count < self.capacity {
                                    // a put could have occurred
                                    self.signal_not_full();    // signal threads waiting to put
                                }
                                break;
                            },
                            Err(_) => {},       // possible put
                        }
                    }

                    return r;
                },
                Ok(None) => {},                             // odd, loop again
                Err(()) => {},                              // race condition!, loop again
            }
        }
    }

    pub fn take_timeout(&self,  timeout: Duration) -> Option<T> {
        let guard = epoch::pin();
        let &(ref lock, ref cvar) = &*self.not_empty;

        let start = Instant::now();
        let mut not_empty = lock.lock().unwrap();       // locked
        loop {
            if *not_empty == false {
                if start.elapsed() > timeout {
                    // waited long enough and still empty (might have returned early
                    return None;
                }
                let (mg, mtr) = cvar.wait_timeout(not_empty, timeout).unwrap();
                if mtr.timed_out() {
                    return None;
                }
                not_empty = mg;

            } else {
                break;
            }

        }

        // have lock back (not_empty) and there should be something to take
        Some(self.take_internal(&guard, not_empty))
    }

    pub fn take(&self) -> T {
        let guard = epoch::pin();
        let &(ref lock, ref cvar) = &*self.not_empty;

            let mut not_empty = lock.lock().unwrap();       // locked
            loop {
                if *not_empty == false {
                    not_empty = cvar.wait(not_empty).unwrap();
                } else {
                    break;
                }
            }

        // have lock back (not_empty) and there should be something to take
        self.take_internal(&guard, not_empty)
    }
}


#[cfg(test)]
mod test {
    const CONC_COUNT: i64 = 1000000;

    use scope;
    use super::*;

    use std::time::Duration;
    use std::thread;

    #[test]
    fn put_take_1() {
        let q: LinkedBlockingQueue<i64> = LinkedBlockingQueue::new(Some(2));
        assert!(q.is_empty());
        assert_eq!(q.size(), 2);
        assert_eq!(q.remaining_capacity(), 2);
        q.put(37);
        assert_eq!(q.remaining_capacity(), 1);
        assert!(!q.is_empty());
        assert_eq!(q.take(), 37);
        assert!(q.is_empty());
        assert_eq!(q.remaining_capacity(), 2);
    }

    #[test]
    fn put_take_timeout_1() {
        let q: LinkedBlockingQueue<i64> = LinkedBlockingQueue::new(Some(1));
        assert!(q.is_empty());
        let duration = Duration::new(1,0);
        assert_eq!(q.take_timeout(duration), None);
        q.put(37);
        assert_eq!(q.take_timeout(duration), Some(37));
        assert!(q.is_empty());
        q.put(37);
        assert!(!q.put_timeout(38, duration));
        assert!(!q.is_empty());
    }

    #[test]
    fn put_take_many_spsc() {
        let half_count = (CONC_COUNT / 2) as u64;
        let q: LinkedBlockingQueue<i64> = LinkedBlockingQueue::new(Some(half_count));
        assert!(q.is_empty());

        scope(|scope| {
            scope.spawn(|| {
                for i in 0..CONC_COUNT {
                    q.put(i)
                }
            });

            // fill up then take.
            loop {
                if q.remaining_capacity() != 0 {
                    thread::sleep(Duration::new(1,0));
                } else {
                    break;
                }
            }

            let mut next = 0;
            while next < CONC_COUNT {
                let elem = q.take();
                assert_eq!(elem, next);
                next += 1;
            }
        });
    }

    #[test]
    fn put_take_many_mpmc() {
        enum LR { Left(i64), Right(i64) }

        let count = 10i64;
        let q: LinkedBlockingQueue<LR> = LinkedBlockingQueue::new(Some(count as u64));
        assert!(q.is_empty());

        scope(|scope| {
            for _t in 0..2 {
                scope.spawn(|| {
                    for i in 0..count {
                        q.put(LR::Left(i))
                    }
                });
                scope.spawn(|| {
                    for i in 0..count {
                        q.put(LR::Right(i))
                    }
                });
                scope.spawn(|| {
                    let mut vl = vec![];
                    let mut vr = vec![];
                    for _i in 0..count * 2 {
                        match q.take() {
                            LR::Left(x) => vl.push(x),
                            LR::Right(x) => vr.push(x),
                        }
                    }

                    let mut vl2 = vl.clone();
                    let mut vr2 = vr.clone();
                    vl2.sort();
                    vr2.sort();

                    assert_eq!(vl, vl2);
                    assert_eq!(vr, vr2);
                });
            }
        });
    }
}


