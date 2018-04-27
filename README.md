# Flexible Locks

This crate aims at providing generic, flexible implementations of locking
primitives. For now, it only provides `Mutex` types (i.e. no `RwLock`, etc.),
without [poisoning], and without `try_lock`. Support for those can be
added in the future if there is interest (patches welcome). Poisoning is not
necessary with panic=abort.

[poisoning]: https://doc.rust-lang.org/std/sync/struct.Mutex.html#poisoning

The provided types allow flexibility in layout and locking implementation.

## Differences from `std::sync::Mutex`

- No poisoning.
- No `try_lock`.
- The underlying raw mutex primitive can be of any kind, within a `Box` or
  not, as long as the `RawMutex` trait is implemented. Choose carefully.
- The raw mutex primitive can be embedded anywhere in the data type. See the
  `MutexWrap` type for a variant that looks more like `std::sync::Mutex`,
  but still allows to use a specific raw mutex primitive.

## Examples

```rust
extern crate flexible_locks;
#[macro_use]
extern crate flexible_locks_derive;
use flexible_locks::{Mutex, RawMutex};

// Pick your choice of raw mutex;
#[cfg(windows)]
use flexible_locks::SRWLOCK as RawOsMutex;
#[cfg(unix)]
use flexible_locks::pthread_mutex_t as RawOsMutex;

use std::sync::Arc;
use std::thread;
use std::sync::mpsc::channel;

#[derive(MutexProtected, Default)]
struct Data {
    a: usize,
    b: usize,
    #[mutex]
    mutex: RawOsMutex,
}

const N: usize = 10;

fn main() {
    // Spawn a few threads to increment a shared variable (non-atomically),
    // and let the main thread know once all increments are done.
    //
    // Here we're using an Arc to share memory among threads, and the data
    // inside the Arc is protected with a mutex.
    let data = Arc::new(Mutex::new(Data::default()));

    let (tx, rx) = channel();
    for _ in 0..N {
        let (data, tx) = (data.clone(), tx.clone());
        thread::spawn(move || {
            // The shared state can only be accessed once the lock is held.
            // Our non-atomic increment is safe because we're the only thread
            // which can access the shared state when the lock is held.
            let mut data = data.lock();
            data.a += 1;
            if data.a == N {
                tx.send(()).unwrap();
            }
            // the lock is unlocked here when `data` goes out of scope.
        });
    }
     
    rx.recv().unwrap();
}
```

## Features

The `parking_lot` feature can be enabled, providing a `RawMutex`
implementation for `parking_log::Mutex<()>`.

License: Apache-2.0/MIT
