// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// With enough care, it is possible to share the same mutex-protected
// data structure across FFI, and contend for the same lock.

extern crate crossbeam;
extern crate flexible_locks;
#[macro_use]
extern crate flexible_locks_derive;

use std::sync::mpsc::channel;

use flexible_locks::{Mutex, RawMutex};

// Pick your choice of raw mutex;
#[cfg(unix)]
use flexible_locks::pthread_mutex_t as RawOsMutex;
#[cfg(windows)]
use flexible_locks::CRITICAL_SECTION as RawOsMutex;

// Shared definition with ffi.c.
#[repr(C)]
#[derive(MutexProtected, Default)]
struct Data {
    a: usize,
    b: usize,
    #[mutex]
    m: RawOsMutex,
}

#[link(name = "ffi", kind = "static")]
extern "C" {
    fn data_new() -> *mut Data;
    fn data_inc(_: *mut Data);
    fn data_free(_: *mut Data);
}

// Code similar to the `lots_and_lots` test in the flexible-locks crate,
// originally copied from std::sync::Mutex tests, but using scoped threads
// from the crossbeam crate to avoid using an Arc.
fn lots_and_lots(d: &mut Mutex<Data>) {
    const J: usize = 1000;
    const K: usize = 3;

    {
        let data = &*d;
        let (tx, rx) = channel();
        crossbeam::scope(|scope| {
            // Set up K threads doing J data increments through FFI, and K
            // other threads doing J data increments in rust.
            for _ in 0..K {
                let tx2 = tx.clone();
                scope.spawn(move || {
                    for _ in 0..J {
                        unsafe {
                            // More realistic use cases would probably not pass
                            // the data constantly through FFI, thus shouldn't
                            // require so much casting.
                            data_inc(data as *const _ as *const Data as *mut Data);
                        }
                    }
                    tx2.send(()).unwrap();
                });
                let tx2 = tx.clone();
                scope.spawn(move || {
                    for _ in 0..J {
                        // Same as data_inc.
                        let mut data = data.lock();
                        data.a += 1;
                        if data.a % 9 == 0 {
                            data.b += 1;
                        }
                    }
                    tx2.send(()).unwrap();
                });
            }
        });

        drop(tx);
        for _ in 0..2 * K {
            rx.recv().unwrap();
        }
    }

    // At this point, we statically know no thread may access the data, so
    // we use `get_mut()` instead of `lock()`.
    assert_eq!(d.get_mut().a, J * K * 2);
    assert_eq!(d.get_mut().b, J * K * 2 / 9);
}

fn main() {
    // Perform the work with data initialized from FFI.
    let data = unsafe { std::mem::transmute::<&mut Data, &mut Mutex<Data>>(&mut *data_new()) };

    lots_and_lots(data);

    unsafe {
        let data = std::mem::transmute::<&mut Mutex<Data>, &mut Data>(data);
        data_free(data);
    }

    // Perform the work again with data initialized from rust.
    let mut data = Mutex::new(Data::default());

    lots_and_lots(&mut data);
}
