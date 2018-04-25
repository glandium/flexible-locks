## Custom Derive for Flexible Locks

This crate provides custom derives for traits describing types that can
be wrapped in Flexible Locks types.

For now, Flexible Locks only provides a `Mutex` type, so this crate provides
a `#[derive(MutexProtected)]`.

The `#[mutex]` attribute is used to indicate the data field containing the raw
mutex type.

### Examples

```rust
extern crate flexible_locks;
#[macro_use]
extern crate flexible_locks_derive;
use flexible_locks::{Mutex, RawMutex};

// Pick your choice of raw mutex;
#[cfg(windows)]
use flexible_locks::CRITICAL_SECTION as RawOsMutex;
#[cfg(unix)]
use flexible_locks::pthread_mutex_t as RawOsMutex;

#[derive(MutexProtected)]
struct Data {
    a: usize,
    #[mutex]
    mutex: RawOsMutex,
    b: usize,
}
```
