// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::cell::UnsafeCell;
use core::fmt;
use core::mem;

#[cfg(windows)]
use winapi::um::synchapi::{AcquireSRWLockExclusive, DeleteCriticalSection, EnterCriticalSection,
                           InitializeCriticalSection, LeaveCriticalSection,
                           ReleaseSRWLockExclusive};

#[cfg(unix)]
use libc;

mod raw {
    #[cfg(unix)]
    pub use libc::pthread_mutex_t;
    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
    #[allow(non_camel_case_types)]
    #[repr(transparent)]
    pub struct pthread_mutex_adaptive_t(pub libc::pthread_mutex_t);
    #[cfg(windows)]
    pub use winapi::um::minwinbase::CRITICAL_SECTION;
    #[cfg(windows)]
    pub use winapi::um::synchapi::SRWLOCK;
    #[cfg(any(target_os = "macos", target_os = "ios"))]
    #[repr(transparent)]
    pub struct OSSpinLock(pub i32);
}

use RawMutex;

/// A trait for unsafe raw mutual exclusion primitives.
///
/// Types implementing this trait are meant to be wrapped with [`RawOsMutex`],
/// bringing them an automatic [`RawMutex`] implementation.
pub trait UnsafeRawOsMutex {
    /// Initialize the raw mutex.
    ///
    /// See [`RawMutex::init`].
    unsafe fn init(_mutex: *mut Self) {}

    /// Destroy the raw mutex.
    ///
    /// See [`RawMutex::destroy`]
    unsafe fn destroy(_mutex: *mut Self) {}

    /// Acquire the raw mutex.
    ///
    /// See [`RawMutex::lock`]
    unsafe fn lock(mutex: *mut Self);

    /// Release the raw mutex.
    ///
    /// See [`RawMutex::unlock`]
    unsafe fn unlock(mutex: *mut Self);
}

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
/// - `pthread_mutex_adaptive_t`, on Linux and FreeBSD, like `pthread_mutex_t`, initialized as
/// PTHREAD_MUTEX_ADAPTIVE_NP.
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
/// - [`pthread_mutex_adaptive_new`]
/// - [`osspinlock_new`]
/// - [`srwlock_new`]
///
/// For non-static initialization, `Default::default()` can be used for these.
///
/// [`pthread_mutex_new`]: ../x86_64-unknown-linux-gnu/flexible_locks/macro.pthread_mutex_new.html
/// [`pthread_mutex_adaptive_new`]: ../x86_64-unknown-linux-gnu/flexible_locks/macro.pthread_mutex_adaptive_new.html
/// [`osspinlock_new`]: ../x86_64-apple-darwin/flexible_locks/macro.osspinlock_new.html
/// [`srwlock_new`]: ../x86_64-pc-windows-msvc/flexible_locks/macro.srwlock_new.html
///
/// For more specific non default use cases, you may want to implement your own
/// type and implement the [`RawMutex`] or [`UnsafeRawOsMutex`] trait for it.
///
/// ## Safety
///
/// Generally speaking, platform mutex primitives cannot be moved in memory.
/// That is, they must stay at the same address. Please ensure that is the
/// case when you use them.
#[repr(transparent)]
pub struct RawOsMutex<T: UnsafeRawOsMutex> {
    #[doc(hidden)]
    pub __inner: UnsafeCell<T>,
}

unsafe impl<T: UnsafeRawOsMutex> Send for RawOsMutex<T> {}
unsafe impl<T: UnsafeRawOsMutex> Sync for RawOsMutex<T> {}

impl<T: UnsafeRawOsMutex> RawMutex for RawOsMutex<T> {
    unsafe fn init(&mut self) {
        T::init(self.__inner.get());
    }

    unsafe fn lock(&self) {
        T::lock(self.__inner.get());
    }

    unsafe fn unlock(&self) {
        T::unlock(self.__inner.get());
    }

    unsafe fn destroy(&self) {
        T::destroy(self.__inner.get());
    }
}

/// Statically initializes a [`RawOsMutex`]
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate flexible_locks;
/// use flexible_locks::{RawOsMutex, UnsafeRawOsMutex};
///
/// struct FakeRawMutex;
///
/// impl UnsafeRawOsMutex for FakeRawMutex {
///     unsafe fn lock(mutex: *mut Self) {
///         // Real implementation goes here.
///     }
///     unsafe fn unlock(mutex: *mut Self) {
///         // Real implementation goes here.
///     }
/// }
///
/// static MUTEX: RawOsMutex<FakeRawMutex> = raw_os_mutex_new!(FakeRawMutex);
/// # fn main() {}
/// ```
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
impl fmt::Debug for SRWLOCK {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("SRWLOCK")
    }
}

#[cfg(windows)]
impl UnsafeRawOsMutex for raw::SRWLOCK {
    #[inline]
    unsafe fn lock(mutex: *mut Self) {
        AcquireSRWLockExclusive(mutex);
    }

    #[inline]
    unsafe fn unlock(mutex: *mut Self) {
        ReleaseSRWLockExclusive(mutex);
    }
}

#[cfg(windows)]
#[doc(hidden)]
pub use winapi::um::synchapi::SRWLOCK_INIT;

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
        raw_os_mutex_new!($crate::SRWLOCK_INIT)
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
impl fmt::Debug for CRITICAL_SECTION {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("CRITICAL_SECTION")
    }
}

#[cfg(windows)]
impl UnsafeRawOsMutex for raw::CRITICAL_SECTION {
    #[inline]
    unsafe fn init(mutex: *mut Self) {
        InitializeCriticalSection(mutex);
    }

    #[inline]
    unsafe fn lock(mutex: *mut Self) {
        EnterCriticalSection(mutex);
    }

    #[inline]
    unsafe fn unlock(mutex: *mut Self) {
        LeaveCriticalSection(mutex);
    }

    #[inline]
    unsafe fn destroy(mutex: *mut Self) {
        DeleteCriticalSection(mutex);
    }
}

#[cfg(windows)]
impl Default for CRITICAL_SECTION {
    #[inline]
    fn default() -> Self {
        unsafe { mem::uninitialized() }
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
impl fmt::Debug for pthread_mutex_t {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("pthread_mutex_t")
    }
}

#[cfg(unix)]
impl UnsafeRawOsMutex for raw::pthread_mutex_t {
    unsafe fn init(mutex: *mut Self) {
        let mut attr: libc::pthread_mutexattr_t = mem::uninitialized();
        let r = libc::pthread_mutexattr_init(&mut attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutexattr_settype(&mut attr, libc::PTHREAD_MUTEX_NORMAL);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutex_init(mutex, &attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutexattr_destroy(&mut attr);
        debug_assert_eq!(r, 0);
    }

    #[inline]
    unsafe fn lock(mutex: *mut Self) {
        libc::pthread_mutex_lock(mutex);
    }

    #[inline]
    unsafe fn unlock(mutex: *mut Self) {
        libc::pthread_mutex_unlock(mutex);
    }

    #[inline]
    unsafe fn destroy(mutex: *mut Self) {
        libc::pthread_mutex_destroy(mutex);
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

#[cfg(target_os = "linux")]
#[doc(hidden)]
pub const PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP: raw::pthread_mutex_adaptive_t = raw::pthread_mutex_adaptive_t(libc::PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP);

/// [`RawOsMutex`] wrapper for `libc::pthread_mutex_t`, initialized as
/// PTHREAD_MUTEX_ADAPTIVE_NP.
#[cfg(any(target_os = "linux", target_os = "freebsd"))]
#[allow(non_camel_case_types)]
pub type pthread_mutex_adaptive_t = RawOsMutex<raw::pthread_mutex_adaptive_t>;

#[cfg(any(target_os = "linux", target_os = "freebsd"))]
impl fmt::Debug for pthread_mutex_adaptive_t {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("pthread_mutex_adaptive_t")
    }
}

#[cfg(any(target_os = "linux", target_os = "freebsd"))]
impl UnsafeRawOsMutex for raw::pthread_mutex_adaptive_t {
    unsafe fn init(mutex: *mut Self) {
        let mut attr: libc::pthread_mutexattr_t = mem::uninitialized();
        let r = libc::pthread_mutexattr_init(&mut attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutexattr_settype(&mut attr, libc::PTHREAD_MUTEX_ADAPTIVE_NP);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutex_init(&mut (*mutex).0, &attr);
        debug_assert_eq!(r, 0);
        let r = libc::pthread_mutexattr_destroy(&mut attr);
        debug_assert_eq!(r, 0);
    }

    #[inline]
    unsafe fn lock(mutex: *mut Self) {
        UnsafeRawOsMutex::lock(&mut (*mutex).0);
    }

    #[inline]
    unsafe fn unlock(mutex: *mut Self) {
        UnsafeRawOsMutex::unlock(&mut (*mutex).0);
    }

    #[inline]
    unsafe fn destroy(mutex: *mut Self) {
        UnsafeRawOsMutex::destroy(&mut (*mutex).0);
    }
}

/// Statically initializes a [`pthread_mutex_adaptive_t`]
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate flexible_locks;
/// use flexible_locks::pthread_mutex_adaptive_t;
/// static MUTEX: pthread_mutex_adaptive_t = pthread_mutex_adaptive_new!();
/// # fn main() {}
/// ```
#[cfg(target_os = "linux")]
#[macro_export]
macro_rules! pthread_mutex_adaptive_new {
    () => {
        raw_os_mutex_new!($crate::PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP)
    };
    ($e:expr) => {
        raw_os_mutex_new!($e)
    };
}

#[cfg(target_os = "linux")]
impl Default for pthread_mutex_adaptive_t {
    #[inline]
    fn default() -> Self {
        pthread_mutex_adaptive_new!()
    }
}

#[cfg(any(target_os = "macos", target_os = "ios"))]
#[doc(hidden)]
pub const OS_SPINLOCK_INIT: raw::OSSpinLock = raw::OSSpinLock(0);

#[cfg(any(target_os = "macos", target_os = "ios"))]
#[link(name = "System")]
extern "C" {
    fn OSSpinLockLock(lock: *mut raw::OSSpinLock);
    fn OSSpinLockUnlock(lock: *mut raw::OSSpinLock);
}

/// [`RawOsMutex`] wrapper for `OSSpinLock`.
#[cfg(any(target_os = "macos", target_os = "ios"))]
pub type OSSpinLock = RawOsMutex<raw::OSSpinLock>;

#[cfg(any(target_os = "macos", target_os = "ios"))]
impl fmt::Debug for OSSpinLock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("OSSpinLock")
    }
}

#[cfg(any(target_os = "macos", target_os = "ios"))]
impl UnsafeRawOsMutex for raw::OSSpinLock {
    #[inline]
    unsafe fn lock(mutex: *mut Self) {
        OSSpinLockLock(mutex);
    }

    #[inline]
    unsafe fn unlock(mutex: *mut Self) {
        OSSpinLockUnlock(mutex);
    }
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
