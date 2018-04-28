// Copyright 2018 Mike Hommey
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! # Flexible Locks
//!
//! This crate aims at providing generic, flexible implementations of locking
//! primitives. For now, it only provides `Mutex` types (i.e. no `RwLock`, etc.),
//! without [poisoning], and without `try_lock`. Support for those can be
//! added in the future if there is interest (patches welcome). Poisoning is not
//! necessary with panic=abort.
//!
//! [poisoning]: https://doc.rust-lang.org/std/sync/struct.Mutex.html#poisoning
//!
//! The provided types allow flexibility in layout and locking implementation.
//! See the [`Mutex`], [`MutexWrap`] and [`RawOsMutex`] documentation for more
//! details.
//!
//! # Features
//!
//! The `parking_lot` feature can be enabled, providing a [`RawMutex`]
//! implementation for `parking_log::Mutex<()>`.
#![no_std]
#![deny(missing_docs)]

#[cfg(any(feature = "std", test))]
extern crate std;
#[cfg(any(feature = "std", test))]
use std::prelude::v1::*;

#[cfg(windows)]
extern crate winapi;

#[cfg(unix)]
extern crate libc;

#[macro_use]
extern crate flexible_locks_derive;

#[cfg(feature = "allocator_api")]
extern crate allocator_api;

#[cfg(feature = "parking_lot")]
extern crate parking_lot;

// Public for the *_new macros.
#[doc(hidden)]
pub use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr;

// For #[derive(MutexProtected)]
mod flexible_locks {
    pub use super::MutexProtected;
}

mod os;

pub use os::*;

/// A trait for raw mutual exclusion primitives.
pub trait RawMutex: Send + Sync {
    /// Initialize the raw mutex.
    ///
    /// Because initializing an instance may involve moving its location
    /// when doing e.g. `Box::new(Foo::new())`, because some types
    /// of raw mutex primitives need to be initialized at their final,
    /// permanent location (e.g. [`CRITICAL_SECTION`]), or because some
    /// may not be statically initialized to an entirely satisfying state
    /// (e.g. [`pthread_mutex_t`], see [issue #33770]), this method is called
    /// from [`Mutex::new`] to finish the raw mutex initialization.
    ///
    /// [`CRITICAL_SECTION`]: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682530(v=vs.85).aspx
    /// [`pthread_mutex_t`]: http://pubs.opengroup.org/onlinepubs/7908799/xsh/pthread_mutex_init.html
    /// [issue #33770]: https://github.com/rust-lang/rust/issues/33770
    unsafe fn init(&mut self) {}

    /// Destroy the raw mutex.
    ///
    /// In some cases, raw mutex primitives need to be cleaned up after
    /// use, so this method is called when a [`Mutex`] is dropped.
    unsafe fn destroy(&self) {}

    /// Acquire the raw mutex.
    unsafe fn lock(&self);

    /// Release the raw mutex.
    unsafe fn unlock(&self);
}

/// Wrapping a `RawMutex` in a `Box` is just as good a valid `RawMutex`.
///
/// Ideally, any type that derefs to a `RawMutex` would be good too, but
/// without specialization, this would prevent implementing `RawMutex` on
/// your own mutex types.
//
// Ideally, this would be:
// `impl<T: RawMutex, U: DerefMut<Target = T> + Send + Sync> RawMutex for U`
#[cfg(any(feature = "std", test))]
impl<T: RawMutex> RawMutex for Box<T> {
    unsafe fn init(&mut self) {
        self.as_mut().init()
    }

    unsafe fn lock(&self) {
        self.as_ref().lock()
    }

    unsafe fn unlock(&self) {
        self.as_ref().unlock()
    }

    unsafe fn destroy(&self) {
        self.as_ref().destroy()
    }
}

/// A trait describing types that can be wrapped in a [`Mutex`].
///
/// It is not recommended to implement this trait manually. Instead, use the
/// `flexible-locks_derive` crate that provides a custom
/// `#[derive(MutexProtected)]`.
///
/// When using that custom derive, the `#[mutex]` attribute is used to
/// indicate the data field containing the raw mutex type.
///
/// # Examples
///
/// ```
/// extern crate flexible_locks;
/// #[macro_use]
/// extern crate flexible_locks_derive;
/// use flexible_locks::{Mutex, RawMutex};
///
/// // Pick your choice of raw mutex;
/// #[cfg(windows)]
/// use flexible_locks::CRITICAL_SECTION as RawOsMutex;
/// #[cfg(unix)]
/// use flexible_locks::pthread_mutex_t as RawOsMutex;
///
/// #[derive(MutexProtected)]
/// struct Data {
///     a: usize,
///     #[mutex]
///     mutex: RawOsMutex,
///     b: usize,
/// }
/// # fn main() {}
/// ```
pub trait MutexProtected {
    /// Raw mutex pritimive used to protect the data type.
    type MutexType: RawMutex;

    /// Data type that [`Mutex::lock`] will give access to.
    ///
    /// `[derive(MutexProtected)]` makes this `Self` when the type is large,
    /// but when there are only two fields in the struct (whichever their
    /// order is), it will set the `DataType` to the type of the non-mutex
    /// field.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::{Mutex, RawMutex};
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// #[derive(MutexProtected, Default)]
    /// struct Data {
    ///     a: usize,
    ///     b: usize,
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    /// }
    ///
    /// #[derive(MutexProtected, Default)]
    /// struct Data2 {
    ///     a: usize,
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    /// }
    ///
    /// #[derive(MutexProtected, Default)]
    /// struct Data3 {
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    ///     a: usize,
    /// }
    ///
    /// fn main() {
    ///     let mut mutex = Mutex::new(Data::default());
    ///     mutex.lock().a = 10;
    ///     let mut mutex = Mutex::new(Data2::default());
    ///     *mutex.lock() = 10;
    ///     let mut mutex = Mutex::new(Data3::default());
    ///     *mutex.lock() = 10;
    /// }
    /// ```
    ///
    /// `MutexWrap<RawOsMutex, usize>` should be preferred to `Mutex<Data2>`
    /// and `Mutex<Data3>`.
    type DataType: ?Sized;

    /// Return an immutable reference to the raw mutex.
    fn get_mutex(&self) -> &Self::MutexType;

    /// Return a mutable reference to the raw mutex.
    fn get_mutex_mut(&mut self) -> &mut Self::MutexType;

    /// Return an immutable reference to the data.
    fn get_data(&self) -> &Self::DataType;

    /// Return a mutable reference to the data.
    fn get_data_mut(&mut self) -> &mut Self::DataType;

    /// Consumes the wrapping type, returning the underlying data.
    fn into_data(self) -> Self::DataType
    where
        Self::DataType: Sized;
}

// FIXME: specialization should allow to just use (M, T) directly,
// and to turn MutexWrap into a type alias.
#[doc(hidden)]
#[derive(MutexProtected)]
pub struct MutexWrapper<M: RawMutex, T: ?Sized>(#[mutex] pub M, pub T);

impl<M: RawMutex + Default, T> From<T> for MutexWrapper<M, T> {
    fn from(t: T) -> Self {
        MutexWrapper(Default::default(), t)
    }
}

/// A mutual exclusion primitive useful for protecting shared data
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can be statically initialized via the [`mutex_new`] macro, or created
/// via a [`new`] constructor. Each mutex has a type parameter which represents
/// the data that it is protecting. The data can only be accessed through the
/// RAII guards returned from [`lock`], which guarantees that the data is only
/// ever accessed when the mutex is locked.
///
/// [`new`]: #method.new
/// [`lock`]: #method.lock
///
/// # Differences from [`std::sync::Mutex`]
///
/// - No poisoning.
/// - No `try_lock`.
/// - The underlying raw mutex primitive can be of any kind, within a `Box` or
///   not, as long as the [`RawMutex`] trait is implemented. Choose carefully.
/// - The raw mutex primitive can be embedded anywhere in the data type. See
///   the [`MutexWrap`] type for a variant that looks more like
///   [`std::sync::Mutex`] but still allows to use a specific raw mutex
///   primitive.
/// - With care, this can allow to share data through FFI and contend on the
///   same locks. See the `ffi-example` directory.
///
/// [`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
/// [`RawMutex`]: trait.RawMutex.html
///
/// # Examples
///
/// ```
/// extern crate flexible_locks;
/// #[macro_use]
/// extern crate flexible_locks_derive;
/// use flexible_locks::{Mutex, RawMutex};
///
/// // Pick your choice of raw mutex;
/// #[cfg(windows)]
/// use flexible_locks::SRWLOCK as RawOsMutex;
/// #[cfg(unix)]
/// use flexible_locks::pthread_mutex_t as RawOsMutex;
///
/// use std::sync::Arc;
/// use std::thread;
/// use std::sync::mpsc::channel;
///
/// #[derive(MutexProtected, Default)]
/// struct Data {
///     a: usize,
///     b: usize,
///     #[mutex]
///     mutex: RawOsMutex,
/// }
///
/// const N: usize = 10;
///
/// fn main() {
///     // Spawn a few threads to increment a shared variable (non-atomically),
///     // and let the main thread know once all increments are done.
///     //
///     // Here we're using an Arc to share memory among threads, and the data
///     // inside the Arc is protected with a mutex.
///     let data = Arc::new(Mutex::new(Data::default()));
///
///     let (tx, rx) = channel();
///     for _ in 0..N {
///         let (data, tx) = (data.clone(), tx.clone());
///         thread::spawn(move || {
///             // The shared state can only be accessed once the lock is held.
///             // Our non-atomic increment is safe because we're the only thread
///             // which can access the shared state when the lock is held.
///             let mut data = data.lock();
///             data.a += 1;
///             if data.a == N {
///                 tx.send(()).unwrap();
///             }
///             // the lock is unlocked here when `data` goes out of scope.
///         });
///     }
///     
///     rx.recv().unwrap();
/// }
/// ```
///
/// Please note that `#[derive(MutexProtected)]` treats structs containing only
/// two fields including the raw mutex differently, such that the data handed
/// by [`Mutex::lock`] is the non-mutex field, rather than the whole data.
/// In that case, it is preferable to use [`MutexWrap`] instead.
/// See [`MutexProtected::DataType`].
pub struct Mutex<T: MutexProtected + ?Sized> {
    #[doc(hidden)]
    pub __wrapper: UnsafeCell<T>,
}

unsafe impl<T: MutexProtected + ?Sized + Send> Send for Mutex<T> {}
unsafe impl<T: MutexProtected + ?Sized + Send> Sync for Mutex<T> {}

/// Statically initializes a [`Mutex`] or a [`MutexWrap`].
///
/// This skips the [`RawMutex::init`] method, so please be careful when using
/// this, and ensure the statically initialized raw mutex is properly usable.
///
/// For non-static initialization, it is recommended to use [`Mutex::new`] or
/// [`MutexWrap::new`].
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate flexible_locks;
/// #[macro_use]
/// extern crate flexible_locks_derive;
/// use flexible_locks::{Mutex, MutexWrap, RawMutex};
///
/// // Pick your choice of raw mutex;
/// #[cfg(windows)]
/// use flexible_locks::SRWLOCK as RawOsMutex;
/// #[cfg(unix)]
/// use flexible_locks::pthread_mutex_t as RawOsMutex;
///
/// #[derive(MutexProtected)]
/// struct Data {
///     a: usize,
///     b: usize,
///     #[mutex]
///     mutex: RawOsMutex,
/// }
///
/// static DATA: Mutex<Data> = mutex_new!(Data {
///     a: 2,
///     b: 1,
///     #[cfg(windows)]
///     mutex: srwlock_new!(),
///     #[cfg(unix)]
///     mutex: pthread_mutex_new!(),
/// });
///
/// struct Data2 {
///     a: usize,
///     b: usize,
/// }
///
/// #[cfg(windows)]
/// macro_rules! raw_os_mutex {
///     () => { srwlock_new!() };
/// }
/// #[cfg(unix)]
/// macro_rules! raw_os_mutex {
///     () => { pthread_mutex_new!() };
/// }
///
/// static DATA2: MutexWrap<RawOsMutex, Data2> = mutex_new!(
///     raw_os_mutex!(),
///     Data2 { a: 2, b: 1 }
/// );
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! mutex_new {
    ($m:expr, $d:expr) => {
        $crate::MutexWrap {
            __inner: mutex_new!($crate::MutexWrapper($m, $d)),
        }
    };
    ($e:expr) => {
        $crate::Mutex {
            __wrapper: $crate::UnsafeCell::new($e),
        }
    };
}

impl<T: MutexProtected> Mutex<T>
where
    T::DataType: Sized,
{
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::{Mutex, RawMutex};
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// #[derive(MutexProtected)]
    /// struct Data {
    ///     a: usize,
    ///     b: usize,
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    /// }
    ///
    /// fn main() {
    ///     let mutex = Mutex::new(Data {
    ///         a: 2,
    ///         b: 1,
    ///         mutex: Default::default(),
    ///     });
    /// }
    /// ```
    pub fn new(t: T) -> Self {
        let m = mutex_new!(t);
        unsafe {
            let wrapper: &mut T = &mut *m.__wrapper.get();
            wrapper.get_mutex_mut().init();
        }
        m
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// When the data type contains the raw mutex, which happens with
    /// `#[derive(MutexProtected)]`, the returned data obviously still
    /// contains it. It is however in a destroyed state and may not be
    /// reused.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::{Mutex, RawMutex};
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// #[derive(MutexProtected)]
    /// struct Data {
    ///     a: usize,
    ///     b: usize,
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    /// }
    ///
    /// fn main() {
    ///     let mutex = Mutex::new(Data {
    ///         a: 2,
    ///         b: 1,
    ///         mutex: Default::default(),
    ///     });
    ///     let data = mutex.into_inner();
    ///     assert_eq!(data.a, 2);
    ///     assert_eq!(data.b, 1);
    /// }
    /// ```
    pub fn into_inner(self) -> T::DataType {
        unsafe {
            let wrapper = ptr::read(&self.__wrapper);
            core::mem::forget(self);
            wrapper.into_inner().into_data()
        }
    }
}

impl<T: MutexProtected> From<T> for Mutex<T>
where
    T::DataType: Sized,
{
    fn from(t: T) -> Self {
        Mutex::<T>::new(t)
    }
}

impl<T: MutexProtected<DataType = T> + Sized + Default> Default for Mutex<T> {
    fn default() -> Self {
        Mutex::<T>::new(Default::default())
    }
}

impl<T: MutexProtected + ?Sized> Mutex<T> {
    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// The exact behavior on locking a mutex in the thread which already holds
    /// the lock depends on the underlying raw mutex implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::{Mutex, RawMutex};
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// #[derive(MutexProtected, Default)]
    /// struct Data {
    ///     a: usize,
    ///     b: usize,
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    /// }
    ///
    /// fn main() {
    ///     let mutex = Arc::new(Mutex::new(Data::default()));
    ///     let c_mutex = mutex.clone();
    ///
    ///     thread::spawn(move || {
    ///         c_mutex.lock().a = 10;
    ///     }).join().expect("thread::spawn failed");
    ///     assert_eq!(mutex.lock().a, 10);
    /// }
    /// ```
    pub fn lock(&self) -> MutexGuard<T> {
        unsafe {
            let wrapper = &mut *self.__wrapper.get();
            wrapper.get_mutex().lock();
            MutexGuard::new(wrapper)
        }
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place---the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::{Mutex, RawMutex};
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// #[derive(MutexProtected, Default)]
    /// struct Data {
    ///     a: usize,
    ///     b: usize,
    ///     #[mutex]
    ///     mutex: RawOsMutex,
    /// }
    ///
    /// fn main() {
    ///     let mut mutex = Mutex::new(Data::default());
    ///     mutex.get_mut().a = 10;
    ///     assert_eq!(mutex.lock().a, 10);
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut T::DataType {
        let wrapper = unsafe { &mut *self.__wrapper.get() };
        T::get_data_mut(wrapper)
    }
}

impl<T: MutexProtected + ?Sized> Drop for Mutex<T> {
    fn drop(&mut self) {
        unsafe {
            let wrapper: &T = &*self.__wrapper.get();
            wrapper.get_mutex().destroy();
        }
    }
}

/// A mutual exclusion primitive useful for protecting shared data
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can be statically initialized via the [`mutex_new`] macro, or created
/// via a [`new`] constructor. Each mutex has a raw mutex and a type parameter
/// which represents the data that it is protecting. The data can only be
/// accessed through the RAII guards returned from [`lock`], which guarantees
/// that the data is only ever accessed when the mutex is locked.
///
/// [`new`]: #method.new
/// [`lock`]: #method.lock
///
/// # Differences from [`std::sync::Mutex`]
///
/// - No poisoning.
/// - No `try_lock`.
/// - The underlying raw mutex primitive can be of any kind, within a `Box` or
///   not, as long as the [`RawMutex`] trait is implemented. Choose carefully.
/// - With care, this can allow to share data through FFI and contend on the
///   same locks. See the `ffi-example` directory.
///
/// # Examples
///
/// ```
/// extern crate flexible_locks;
/// #[macro_use]
/// extern crate flexible_locks_derive;
/// use flexible_locks::MutexWrap;
///
/// // Pick your choice of raw mutex;
/// #[cfg(windows)]
/// use flexible_locks::SRWLOCK as RawOsMutex;
/// #[cfg(unix)]
/// use flexible_locks::pthread_mutex_t as RawOsMutex;
///
/// use std::sync::Arc;
/// use std::thread;
/// use std::sync::mpsc::channel;
///
/// const N: usize = 10;
///
/// fn main() {
///     // Spawn a few threads to increment a shared variable (non-atomically),
///     // and let the main thread know once all increments are done.
///     //
///     // Here we're using an Arc to share memory among threads, and the data
///     // inside the Arc is protected with a mutex.
///     let data = Arc::new(MutexWrap::<RawOsMutex, _>::new(0));
///
///     let (tx, rx) = channel();
///     for _ in 0..N {
///         let (data, tx) = (data.clone(), tx.clone());
///         thread::spawn(move || {
///             // The shared state can only be accessed once the lock is held.
///             // Our non-atomic increment is safe because we're the only thread
///             // which can access the shared state when the lock is held.
///             let mut data = data.lock();
///             *data += 1;
///             if *data == N {
///                 tx.send(()).unwrap();
///             }
///             // the lock is unlocked here when `data` goes out of scope.
///         });
///     }
///     
///     rx.recv().unwrap();
/// }
/// ```
pub struct MutexWrap<M: RawMutex, T: ?Sized> {
    #[doc(hidden)]
    pub __inner: Mutex<MutexWrapper<M, T>>,
}

impl<M: RawMutex + Default, T> MutexWrap<M, T> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::MutexWrap;
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// fn main() {
    ///     let mutex = MutexWrap::<RawOsMutex, _>::new(0);
    /// }
    /// ```
    pub fn new(t: T) -> Self {
        MutexWrap {
            __inner: Mutex::new(MutexWrapper(Default::default(), t)),
        }
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// #[macro_use]
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::MutexWrap;
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// fn main() {
    ///     let mutex = MutexWrap::<RawOsMutex, _>::new(0);
    ///     assert_eq!(mutex.into_inner(), 0);
    /// }
    /// ```
    pub fn into_inner(self) -> T {
        self.__inner.into_inner()
    }
}

impl<M: RawMutex + Default, T> From<T> for MutexWrap<M, T> {
    fn from(t: T) -> Self {
        MutexWrap::new(t)
    }
}

impl<M: RawMutex + Default, T: Default> Default for MutexWrap<M, T> {
    fn default() -> Self {
        MutexWrap::new(Default::default())
    }
}

impl<M: RawMutex, T: ?Sized> MutexWrap<M, T> {
    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// The exact behavior on locking a mutex in the thread which already holds
    /// the lock depends on the underlying raw mutex implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::MutexWrap;
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// fn main() {
    ///     let mutex = Arc::new(MutexWrap::<RawOsMutex, _>::new(0));
    ///     let c_mutex = mutex.clone();
    ///
    ///     thread::spawn(move || {
    ///         *c_mutex.lock() = 10;
    ///     }).join().expect("thread::spawn failed");
    ///     assert_eq!(*mutex.lock(), 10);
    /// }
    /// ```
    pub fn lock(&self) -> MutexGuard<MutexWrapper<M, T>> {
        self.__inner.lock()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place---the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate flexible_locks;
    /// #[macro_use]
    /// extern crate flexible_locks_derive;
    /// use flexible_locks::MutexWrap;
    ///
    /// // Pick your choice of raw mutex;
    /// #[cfg(windows)]
    /// use flexible_locks::SRWLOCK as RawOsMutex;
    /// #[cfg(unix)]
    /// use flexible_locks::pthread_mutex_t as RawOsMutex;
    ///
    /// fn main() {
    ///     let mut mutex = MutexWrap::<RawOsMutex, _>::new(0);
    ///     *mutex.get_mut() = 10;
    ///     assert_eq!(*mutex.lock(), 10);
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.__inner.get_mut()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be accessed through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is created by [`Mutex::lock`] and [`MutexWrap::lock`].
#[must_use]
pub struct MutexGuard<'a, T: MutexProtected + ?Sized + 'a> {
    __wrapper: &'a mut T,
    marker: PhantomData<*mut ()>, // prevents an automatic impl Send.
}

unsafe impl<'a, T: MutexProtected + ?Sized + Sync> Sync for MutexGuard<'a, T> {}

impl<'a, T: MutexProtected + ?Sized + 'a> MutexGuard<'a, T> {
    fn new(wrapper: &'a mut T) -> Self {
        MutexGuard {
            __wrapper: wrapper,
            marker: PhantomData,
        }
    }
}

impl<'a, T: MutexProtected + ?Sized + 'a> Drop for MutexGuard<'a, T> {
    fn drop(&mut self) {
        unsafe {
            self.__wrapper.get_mutex().unlock();
        }
    }
}

impl<'a, T: MutexProtected + ?Sized + 'a> Deref for MutexGuard<'a, T> {
    type Target = T::DataType;

    fn deref(&self) -> &T::DataType {
        T::get_data(&self.__wrapper)
    }
}

impl<'a, T: MutexProtected + ?Sized + 'a> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T::DataType {
        T::get_data_mut(&mut self.__wrapper)
    }
}

/// Type alias for `parking_lot::Mutex<()>`.
#[cfg(feature = "parking_lot")]
pub type ParkingLotMutex = parking_lot::Mutex<()>;

#[cfg(feature = "parking_lot")]
impl RawMutex for ParkingLotMutex {
    unsafe fn lock(&self) {
        self.raw_lock()
    }

    unsafe fn unlock(&self) {
        self.raw_unlock()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(windows)]
    type RawOsMutex = SRWLOCK;
    #[cfg(unix)]
    type RawOsMutex = pthread_mutex_t;

    mod base {
        use super::*;

        static mut INITIALIZED: usize = 0;
        static mut LOCKED: usize = 0;
        static mut UNLOCKED: usize = 0;
        static mut DESTROYED: usize = 0;

        #[derive(PartialEq, Debug, Default)]
        struct FakeMutex;

        unsafe impl Send for FakeMutex {}
        unsafe impl Sync for FakeMutex {}

        impl RawMutex for FakeMutex {
            unsafe fn init(&mut self) {
                INITIALIZED += 1;
            }

            unsafe fn lock(&self) {
                LOCKED += 1;
            }

            unsafe fn unlock(&self) {
                UNLOCKED += 1;
            }

            unsafe fn destroy(&self) {
                DESTROYED += 1;
            }
        }

        #[derive(MutexProtected, PartialEq, Debug, Default)]
        struct WithEmbeddedMutex<M: RawMutex>(usize, #[mutex] M, usize);

        #[test]
        fn smoke() {
            macro_rules! smoke_test {
                ($m:expr, $drop:expr) => {
                    unsafe {
                        INITIALIZED = 0;
                        LOCKED = 0;
                        UNLOCKED = 0;
                        DESTROYED = 0;
                    }
                    let m = $m;
                    unsafe {
                        assert_eq!(INITIALIZED, 1);
                        assert_eq!(LOCKED, 0);
                        assert_eq!(UNLOCKED, 0);
                        assert_eq!(DESTROYED, 0);
                    }
                    for i in 0..2 {
                        let data = m.lock();
                        unsafe {
                            assert_eq!(INITIALIZED, 1);
                            assert_eq!(LOCKED, i + 1);
                            assert_eq!(UNLOCKED, i);
                            assert_eq!(DESTROYED, 0);
                        }
                        drop(data);
                        unsafe {
                            assert_eq!(INITIALIZED, 1);
                            assert_eq!(LOCKED, i + 1);
                            assert_eq!(UNLOCKED, i + 1);
                            assert_eq!(DESTROYED, 0);
                        }
                    }
                    $drop(m);
                    unsafe {
                        assert_eq!(INITIALIZED, 1);
                        assert_eq!(LOCKED, 2);
                        assert_eq!(UNLOCKED, 2);
                        assert_eq!(DESTROYED, 1);
                    }
                };
            }

            smoke_test!(MutexWrap::<FakeMutex, usize>::new(42), drop);
            smoke_test!(
                MutexWrap::<FakeMutex, usize>::new(42),
                |m: MutexWrap<_, _>| assert_eq!(m.into_inner(), 42)
            );
            smoke_test!(MutexWrap::<Box<FakeMutex>, usize>::new(42), drop);
            smoke_test!(
                MutexWrap::<Box<FakeMutex>, usize>::new(42),
                |m: MutexWrap<_, _>| assert_eq!(m.into_inner(), 42)
            );
            smoke_test!(Mutex::new(WithEmbeddedMutex(42, FakeMutex, 42)), drop);
            smoke_test!(
                Mutex::new(WithEmbeddedMutex(42, FakeMutex, 42)),
                |m: Mutex<_>| assert_eq!(m.into_inner(), WithEmbeddedMutex(42, FakeMutex, 42))
            );
            smoke_test!(
                Mutex::new(WithEmbeddedMutex(42, Box::new(FakeMutex), 42)),
                drop
            );
            smoke_test!(
                Mutex::new(WithEmbeddedMutex(42, Box::new(FakeMutex), 42)),
                |m: Mutex<_>| assert_eq!(
                    m.into_inner(),
                    WithEmbeddedMutex(42, Box::new(FakeMutex), 42)
                )
            );
        }
    }

    mod wrap {
        use super::*;
        type Mutex<T> = super::MutexWrap<RawOsMutex, T>;
        include!("tests.rs");
    }

    mod boxed {
        use super::*;
        type Mutex<T> = super::MutexWrap<Box<RawOsMutex>, T>;
        include!("tests.rs");
    }

    #[cfg(feature = "parking_lot")]
    mod parking_lot {
        use super::*;
        type Mutex<T> = super::MutexWrap<ParkingLotMutex, T>;
        include!("tests.rs");
    }

    #[cfg(windows)]
    mod critical_section {
        use super::*;
        type Mutex<T> = super::MutexWrap<CRITICAL_SECTION, T>;
        include!("tests.rs");
    }

    #[cfg(any(target_os = "macos", target_os = "ios"))]
    mod osspinlock {
        use super::*;
        type Mutex<T> = super::MutexWrap<OSSpinLock, T>;
        include!("tests.rs");
    }
}
