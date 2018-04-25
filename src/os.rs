// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::cell::UnsafeCell;
use core::mem;

#[cfg(windows)]
use winapi::um::synchapi::{AcquireSRWLockExclusive, DeleteCriticalSection, EnterCriticalSection,
                           InitializeCriticalSection, LeaveCriticalSection,
                           ReleaseSRWLockExclusive, SRWLOCK_INIT};

#[cfg(unix)]
use libc;

mod raw {
#[cfg(windows)]
pub use winapi::um::minwinbase::CRITICAL_SECTION;
#[cfg(windows)]
pub use winapi::um::synchapi::SRWLOCK;
#[cfg(unix)]
pub use libc::pthread_mutex_t;
#[cfg(any(target_os = "macos", target_os = "ios"))]
pub type OSSpinLock = i32;
}

use RawMutex;

/// Platform mutex primitives for use with [`Mutex`] and [`MutexWrap`].
///
/// While the [`std::sync::Mutex`] type only uses one kind of platform mutex
/// primitive (except on Windows, where things are a little convoluted),
/// flexible-locks allow to use different kinds.
///
/// [`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
///
/// The available primitives are:
/// - [`pthread_mutex_t`], on Unix-like systems, including macOS,
/// - [`OSSpinLock`] on macOS,
/// - [`SRWLock`] on Windows,
/// - [`CRITICAL_SECTION`] on Windows.
///
/// Other primitives could be added in the future, such as [`os_unfair_lock_t`]
/// on macOS.
///
/// [`pthread_mutex_t`]: http://pubs.opengroup.org/onlinepubs/7908799/xsh/pthread_mutex_init.html
/// [`OSSpinLock`]: https://developer.apple.com/documentation/kernel/osspinlock
/// [`SRWLock`]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa904937(v=vs.85).aspx
/// [`CRITICAL_SECTION`]: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682530(v=vs.85).aspx
/// [`os_unfair_lock_t`]: https://developer.apple.com/documentation/os/os_unfair_lock_t
///
/// For types that can be statically initialized, until `const fn` is
/// stabilized, initializer macros are provided:
/// - [`pthread_mutex_new`]
/// - [`osspinlock_new`]
/// - [`srwlock_new`]
///
/// For non-static initialization, `Default::default()` can be used for these.
///
/// [`pthread_mutex_new`]: ../x86_64-unknown-linux-gnu/flexible_locks/macro.pthread_mutex_new.html
/// [`osspinlock_new`]: ../x86_64-apple-darwin/flexible_locks/macro.osspinlock_new.html
/// [`srwlock_new`]: ../x86_64-pc-windows-msvc/flexible_locks/macro.srwlock_new.html
///
/// For more specific non default use cases, you may want to implement your own
/// type and implement the [`RawMutex`] trait for it.
///
/// ## Safety
///
/// Generally speaking, platform mutex primitives cannot be moved in memory.
/// That is, they must stay at the same address. Please ensure that is the
/// case when you use them.
pub struct RawOsMutex<T> {
    #[doc(hidden)]
    pub __inner: UnsafeCell<T>,
}

unsafe impl<T> Send for RawOsMutex<T> {}
unsafe impl<T> Sync for RawOsMutex<T> {}

/// Initializes a `RawOsMutex`
#[doc(hidden)]
#[macro_export]
macro_rules! raw_os_mutex_new {
    ($e:expr) => {
        $crate::RawOsMutex {
            __inner: $crate::UnsafeCell::new($e),
        }
    };
}

/// [`RawOsMutex`] wrapper for `winapi::um::synchapi::SRWLOCK`.
#[cfg(windows)]
pub type SRWLOCK = RawOsMutex<raw::SRWLOCK>;

#[cfg(windows)]
impl RawMutex for SRWLOCK {
    #[inline]
    unsafe fn init(&mut self) {}

    #[inline]
    unsafe fn lock(&self) {
        AcquireSRWLockExclusive(self.__inner.get())
    }

    #[inline]
    unsafe fn unlock(&self) {
        ReleaseSRWLockExclusive(self.__inner.get())
    }

    #[inline]
    unsafe fn destroy(&self) {}
}

/// Statically initializes a [`SRWLOCK`]
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate flexible_locks;
/// use flexible_locks::SRWLOCK;
/// static MUTEX: SRWLOCK = srwlock_new!();
/// # fn main() {}
/// ```
#[cfg(windows)]
#[macro_export]
macro_rules! srwlock_new {
    () => {
        raw_os_mutex_new!(SRWLOCK_INIT)
    };
}

#[cfg(windows)]
impl Default for SRWLOCK {
    #[inline]
    fn default() -> Self {
        srwlock_new!()
    }
}

/// [`RawOsMutex`] wrapper for `winapi::um::minwinbase::CRITICAL_SECTION`.
#[cfg(windows)]
#[allow(non_camel_case_types)]
pub type CRITICAL_SECTION = RawOsMutex<raw::CRITICAL_SECTION>;

#[cfg(windows)]
impl RawMutex for CRITICAL_SECTION {
    #[inline]
    unsafe fn init(&mut self) {
        InitializeCriticalSection(self.__inner.get())
    }

    #[inline]
    unsafe fn lock(&self) {
        EnterCriticalSection(self.__inner.get())
    }

    #[inline]
    unsafe fn unlock(&self) {
        LeaveCriticalSection(self.__inner.get())
    }

    #[inline]
    unsafe fn destroy(&self) {
        DeleteCriticalSection(self.__inner.get())
    }
}

#[cfg(windows)]
impl Default for CRITICAL_SECTION {
    #[inline]
    fn default() -> Self {
        unsafe {
            mem::uninitialized()
        }
    }
}

#[cfg(unix)]
#[doc(hidden)]
pub use libc::PTHREAD_MUTEX_INITIALIZER;

/// [`RawOsMutex`] wrapper for `libc::pthread_mutex_t`.
#[cfg(unix)]
#[allow(non_camel_case_types)]
pub type pthread_mutex_t = RawOsMutex<raw::pthread_mutex_t>;

#[cfg(unix)]
impl RawMutex for pthread_mutex_t {
    unsafe fn init(&mut self) {
        let mut attr: libc::pthread_mutexattr_t = mem::uninitialized();
        let r = libc::pthread_mutexattr_init(&mut attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutexattr_settype(&mut attr, libc::PTHREAD_MUTEX_NORMAL);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutex_init(self.__inner.get(), &attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutexattr_destroy(&mut attr);
        debug_assert_eq!(r, 0);
    }

    #[inline]
    unsafe fn lock(&self) {
        libc::pthread_mutex_lock(self.__inner.get());
    }

    #[inline]
    unsafe fn unlock(&self) {
        libc::pthread_mutex_unlock(self.__inner.get());
    }

    #[inline]
    unsafe fn destroy(&self) {
        libc::pthread_mutex_destroy(self.__inner.get());
    }
}

/// Statically initializes a [`pthread_mutex_t`]
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate flexible_locks;
/// use flexible_locks::pthread_mutex_t;
/// static MUTEX: pthread_mutex_t = pthread_mutex_new!();
/// # fn main() {}
/// ```
#[cfg(unix)]
#[macro_export]
macro_rules! pthread_mutex_new {
    () => {
        raw_os_mutex_new!($crate::PTHREAD_MUTEX_INITIALIZER)
    };
    ($e:expr) => {
        raw_os_mutex_new!($e)
    };
}

#[cfg(unix)]
impl Default for pthread_mutex_t {
    #[inline]
    fn default() -> Self {
        pthread_mutex_new!()
    }
}

#[cfg(any(target_os = "macos", target_os = "ios"))]
#[doc(hidden)]
pub const OS_SPINLOCK_INIT: raw::OSSpinLock = 0;

#[cfg(any(target_os = "macos", target_os = "ios"))]
#[link(name = "System")]
extern "C" {
    fn OSSpinLockLock(lock: *mut raw::OSSpinLock);
    fn OSSpinLockUnLock(lock: *mut raw::OSSpinLock);
}

/// [`RawOsMutex`] wrapper for `OSSpinLock`.
#[cfg(any(target_os = "macos", target_os = "ios"))]
pub type OSSpinLock = RawOsMutex<raw::OSSpinLock>;

#[cfg(any(target_os = "macos", target_os = "ios"))]
impl RawMutex for OSSpinLock {
    #[inline]
    unsafe fn init(&mut self) {}

    #[inline]
    unsafe fn lock(&self) {
        OSSpinLockLock(self.__inner.get())
    }

    #[inline]
    unsafe fn unlock(&self) {
        OSSpinLockUnLock(self.__inner.get())
    }

    #[inline]
    unsafe fn destroy(&self) {}
}

/// Statically initializes a [`OSSpinLock`]
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate flexible_locks;
/// use flexible_locks::OSSpinLock;
/// static MUTEX: OSSpinLock = osspinlock_new!();
/// # fn main() {}
/// ```
#[cfg(any(target_os = "macos", target_os = "ios"))]
#[macro_export]
macro_rules! osspinlock_new {
    () => {
        raw_os_mutex_new!($crate::OS_SPINLOCK_INIT)
    };
}

#[cfg(any(target_os = "macos", target_os = "ios"))]
impl Default for OSSpinLock {
    #[inline]
    fn default() -> Self {
        osspinlock_new!()
    }
}
