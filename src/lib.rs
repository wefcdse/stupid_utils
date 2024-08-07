//! # Decription
//! A crate that provides some simple and maybe stupid or useful tools
//!
//! # Example
//! ```
//! use std::collections::HashMap;
//! use stupid_utils::predule::*;
//!
//! let a = HashMap::new().mutable_init(|m| {
//!     m.insert(1, 4.box_up());
//!     m.insert(
//!         2,
//!         Some(9)
//!             .map_value(|v| match v {
//!                 Some(v) => v,
//!                 None => 3,
//!             })
//!             .box_up(),
//!     );
//!     let cond = true;
//!     m.insert(cond.select(3, 4), select(cond, 3, 4).box_up());
//! });
//!
//! let b = {
//!     let mut m = HashMap::new();
//!     m.insert(1, Box::new(4));
//!     m.insert(
//!         2,
//!         Box::new({
//!             let v = Some(9);
//!             match v {
//!                 Some(v) => v,
//!                 None => 3,
//!             }
//!         }),
//!     );
//!     let cond = true;
//!     m.insert(if cond { 3 } else { 4 }, Box::new(if cond { 3 } else { 4 }));
//!     m
//! };
//!
//! assert_eq!(a, b);
//! ```

pub mod predule {
    pub use crate::arc_mutex::ArcMutex;
    pub use crate::arc_mutex_new::arc_mutex_new;
    pub use crate::box_up::BoxUp;
    pub use crate::defer::Defer;
    pub use crate::disable;
    pub use crate::dot_drop::DotDrop;
    pub use crate::dot_ref::DotRef;
    pub use crate::extend_map_iter::{ExtendMap, ExtendMapIter, PushOnlyVec};
    pub use crate::find_in_vec::FindInVec;
    pub use crate::if_iter_remains::IfIterRemains;
    pub use crate::just_provide::just_provide;
    pub use crate::map_value::MapValue;
    pub use crate::mutable_init::MutableInit;
    pub use crate::mutex_lock_and_unwrap::MutexLockAndUnwrap;
    pub use crate::option_to_result::{OptionToResult, OptionUnwrapOnNoneError};
    pub use crate::print_on_drop::{PrintOnDrop, PrintOnDropNoInfo};
    pub use crate::result_to_option::ResultToOption;
    pub use crate::select::{select, DotSelect};
    pub use crate::wrap_in_whatever::WrapInWhatever;
    // pub use crate::short_unwrap::ShortUnwrap;
    // pub use crate::stack_struct::{PopFirst, PushFirst, Stack, Value};
}
pub mod short_unwrap {

    /// a shorter unwrap
    /// instead of calling `unwrap()`, just call `u()`
    /// # Example
    /// ```
    /// use stupid_utils::short_unwrap::ShortUnwrap;
    /// let a: Result<i32,()> = Ok(42);
    /// let b: Result<i32,()> = Ok(42);
    /// assert_eq!(a.unwrap(), b.u());
    /// ```
    pub trait ShortUnwrap<T> {
        /// equals to [`unwrap`]
        ///
        /// see also [`ShortUnwrap`][`crate::short_unwrap::ShortUnwrap`]
        fn u(self) -> T;
    }

    impl<T, E: std::fmt::Debug> ShortUnwrap<T> for Result<T, E> {
        fn u(self) -> T {
            self.unwrap()
        }
    }

    #[test]
    fn test() {
        let a: Result<u32, &str> = Ok(1);
        let b = a.u();
        assert_eq!(b, 1);
    }
}

pub mod option_to_result {

    /// the `Error` type when a `Option` is converted to Result
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
    pub struct OptionUnwrapOnNoneError;
    impl std::fmt::Display for OptionUnwrapOnNoneError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Option value is None")?;
            Ok(())
        }
    }

    impl std::error::Error for OptionUnwrapOnNoneError {}

    /// convert `Option` to `Result`, and then can use `?` in a function that returns `Result`
    /// # Example
    /// ```
    /// use stupid_utils::option_to_result::{OptionToResult, OptionUnwrapOnNoneError};
    ///
    /// let a = Some(42);
    /// let b: Result<i32, OptionUnwrapOnNoneError> = Ok(42);
    ///
    /// assert_eq!(a.to_result(), b);
    ///
    /// ```
    pub trait OptionToResult<T> {
        /// convert `Option` to `Result`
        ///
        /// see also trait doc [`OptionToResult`][`crate::option_to_result::OptionToResult`]
        fn to_result(self) -> Result<T, OptionUnwrapOnNoneError>;
    }

    impl<T> OptionToResult<T> for Option<T> {
        fn to_result(self) -> Result<T, OptionUnwrapOnNoneError> {
            match self {
                Some(v) => Ok(v),
                None => Err(OptionUnwrapOnNoneError),
            }
        }
    }

    #[test]
    fn t() {
        let a: Option<u32> = None;
        let b = a.to_result();
        assert_eq!(b, Err(OptionUnwrapOnNoneError));

        let a: Option<u32> = Some(3);
        let b = a.to_result();
        assert_eq!(b, Ok(3));
    }
}

pub mod mutex_lock_and_unwrap {

    /// just `lock` and `unwrap` in a single method
    ///
    /// # Example
    /// ```
    /// use stupid_utils::mutex_lock_and_unwrap::MutexLockAndUnwrap;
    /// use std::sync::Mutex;
    ///
    /// let a = Mutex::new(42);
    /// let b = Mutex::new(42);
    ///
    /// assert_eq!(*a.lock_and_unwrap(), *b.lock().unwrap());
    /// ```
    pub trait MutexLockAndUnwrap<T>
    where
        T: ?Sized,
    {
        /// `lock` and `unwrap`
        ///
        /// see also [`MutexLockAndUnwrap`][`crate::mutex_lock_and_unwrap::MutexLockAndUnwrap`]
        fn lock_and_unwrap(&self) -> std::sync::MutexGuard<'_, T>;
    }

    impl<T: ?Sized> MutexLockAndUnwrap<T> for std::sync::Mutex<T> {
        fn lock_and_unwrap(&self) -> std::sync::MutexGuard<'_, T> {
            self.lock().unwrap()
        }
    }
}

pub mod arc_mutex_new {
    use std::sync::{Arc, Mutex};

    /// a function equals to `Arc::new(Mutex::new(value))`
    pub fn arc_mutex_new<T>(value: T) -> Arc<Mutex<T>> {
        Arc::new(Mutex::new(value))
    }
}

pub mod arc_mutex {
    use std::sync::{Arc, Mutex};

    pub type ArcMutex<T> = Arc<Mutex<T>>;
}

pub mod select {

    /// same as `cond? a : b` operator in c/cpp
    /// # Example
    /// ```
    /// use stupid_utils::select::select;
    ///
    /// assert_eq!(select(true, 2, 3), 2);
    /// assert_eq!(select(false, 2, 3), 3);
    /// ```
    #[inline(always)]
    pub fn select<T>(condition: bool, true_value: T, false_value: T) -> T {
        if condition {
            true_value
        } else {
            false_value
        }
    }

    /// same as `cond? a : b` operator in c/cpp, but as a method of `bool`
    /// # Example
    /// ```
    /// use stupid_utils::select::DotSelect;
    ///
    /// assert_eq!(true.select(2, 3), 2);
    /// assert_eq!(false.select(2, 3), 3);
    /// ```
    pub trait DotSelect<T> {
        /// same as `cond? a : b` operator in c/cpp, but as a method of `bool`
        ///
        /// see also [`DotSelect`][`crate::select::DotSelect`]
        fn select(&self, true_value: T, false_value: T) -> T;
    }
    impl<T> DotSelect<T> for bool {
        #[inline(always)]
        fn select(&self, true_value: T, false_value: T) -> T {
            if *self {
                true_value
            } else {
                false_value
            }
        }
    }
}

pub mod dot_drop {
    /// `drop` function as a method
    /// # Example
    /// ```
    /// use stupid_utils::dot_drop::DotDrop;
    ///
    /// let a = String::new();
    /// a.drop();
    /// // now 'a' has droped, using a will cause a compile error
    /// // &a;
    /// ```
    pub trait DotDrop: Sized {
        /// `drop` function as a method
        ///
        /// see also [`DotDrop`]
        #[inline(always)]
        fn drop(self) {
            drop(self)
        }
    }
    impl<T> DotDrop for T {}
}

pub mod result_to_option {

    /// convert a `Result` to an `Option`
    /// # Example
    /// ```
    /// use stupid_utils::result_to_option::ResultToOption;
    ///
    /// let a: Result<i32, ()> = Ok(32);
    /// let b: Result<(), i32> = Err(32);
    ///
    /// assert_eq!(a.to_option(), Some(32));
    /// assert_eq!(b.to_option(), None);
    ///
    /// ```
    pub trait ResultToOption<T> {
        /// convert a `Result` to an `Option`
        ///
        /// see also [`ResultToOption`]
        fn to_option(self) -> Option<T>;
    }
    impl<T, E> ResultToOption<T> for Result<T, E> {
        fn to_option(self) -> Option<T> {
            match self {
                Ok(v) => Some(v),
                Err(_) => None,
            }
        }
    }
}

pub mod defer {

    /// a struct to call a closure when it's dropped
    ///
    /// inspired by Zig's `defer` keyword
    ///
    /// note that the `Defer` struct contains a closure, so if it captures a mutable reference to a variable,
    /// the variable will not be able to use until the `Defer` struct is dropped
    ///
    /// # Example
    /// ```
    /// use stupid_utils::defer::Defer;
    ///
    /// let d1 = Defer::new(|| println!("drop"));
    /// // do something
    /// drop(d1); // will print "drop" here
    /// ```
    pub struct Defer<F>
    where
        F: FnOnce(),
    {
        f: Option<F>,
    }

    impl<F> Defer<F>
    where
        F: FnOnce(),
    {
        pub fn new(f: F) -> Self {
            Defer { f: Some(f) }
        }
        pub fn keep_alive(&self) {}
    }

    impl<F> Drop for Defer<F>
    where
        F: FnOnce(),
    {
        fn drop(&mut self) {
            if let Some(f) = self.f.take() {
                f()
            };
        }
    }

    pub fn defer<F>(f: F) -> Defer<F>
    where
        F: FnOnce(),
    {
        Defer::new(f)
    }

    #[test]
    fn t() {
        let v = 12321;
        let s = "ascbasj".to_string();
        let _a = Defer::new(|| println!("drop a,v = {},s = {}", v, s));
    }

    #[test]
    fn block() {
        let mut a = 0;
        fn add(v: &mut i32) {
            *v += 1;
        }
        {
            let d = Defer::new(|| {
                add(&mut a);
                println!("drop d")
            });
            d.keep_alive();
        }
        println!("a = {}", a);
    }

    #[test]
    fn late_init() {
        let mut a = 0;
        fn add(v: &mut i32) {
            *v += 1;
        }
        {
            add(&mut a);
            let d = Defer::new(|| {
                add(&mut a);
                println!("drop d")
            });
            d.keep_alive();
        }
        println!("a = {}", a);
    }

    #[test]
    fn size() {
        let s = String::new();
        let d1 = Defer::new(move || {
            let _s = s;
            println!("drop d1")
        });
        let d2 = Defer::new(|| println!("drop d2"));
        struct F1<F> {
            _f: F,
        }
        let f = F1 { _f: || println!() };
        use std::mem::{size_of, size_of_val};
        assert_eq!(size_of_val(&f), 0);
        assert_eq!(size_of_val(&d1), size_of::<String>());
        assert_eq!(size_of_val(&d2), 1);
    }

    #[test]
    fn defer_fn() {
        let d = defer(|| println!("drop"));
        defer(|| println!("drop temp"));
        let a = &defer(|| println!("drop ref"));
        println!("not stopped");
        a.keep_alive();
        d.keep_alive();
    }
}

pub mod find_in_vec {

    /// a `find` method for `Vec` returning the first matched index
    ///
    /// # Example
    /// ```
    /// use stupid_utils::find_in_vec::FindInVec;
    ///
    /// let v = vec![43, 44, 45, 46];
    ///
    /// assert_eq!(v.find(&44), Some(1));
    /// assert_eq!(v.find(&45), Some(2));
    /// assert_eq!(v.find(&128), None);
    ///
    /// ```
    pub trait FindInVec<T> {
        /// a `find` method for `Vec` returning the first matched index
        ///
        /// see also [`FindInVec`]
        fn find(&self, value: &T) -> Option<usize>;
    }

    impl<T: Eq> FindInVec<T> for Vec<T> {
        fn find(&self, value: &T) -> Option<usize> {
            for (i, v) in self.iter().enumerate() {
                if v == value {
                    return Some(i);
                }
            }
            None
        }
    }

    #[test]
    fn t() {
        let a = vec!["1".to_owned()];
        a.find(&"aaa".to_owned());
    }
}

pub mod map_value {
    /// a `map` method for every value
    /// # Example
    /// ```
    /// use stupid_utils::map_value::MapValue;
    ///
    /// let a = 32.max(35).map_value(|v| format!("number is {}", v));
    /// assert_eq!(a, "number is 35");
    ///
    /// ```

    pub trait MapValue<F, U>: Sized
    where
        F: FnOnce(Self) -> U,
    {
        /// a `map` method for every value
        ///
        /// see also [`MapValue`]
        fn map_value(self, op: F) -> U {
            op(self)
        }
    }
    impl<T, F, U> MapValue<F, U> for T
    where
        T: Sized,
        F: FnOnce(Self) -> U,
    {
    }

    #[test]
    fn t() {
        let _a = "".to_owned().map_value(|_s| 32);
    }
}

pub mod box_up {

    /// a method equals to `Box::new`
    ///
    /// # Example
    /// ```
    /// use stupid_utils::box_up::BoxUp;
    ///
    /// let a = 32_i32.box_up();
    /// let b: Box<i32> = a;
    ///
    /// ```
    pub trait BoxUp {
        /// a method equals to `Box::new`
        ///
        /// see also [`BoxUp`]
        fn box_up(self) -> Box<Self>;
    }
    impl<T> BoxUp for T {
        fn box_up(self) -> Box<Self> {
            Box::new(self)
        }
    }
}

pub mod dot_debug {
    use std::fmt::Debug;
    /// a debug method
    /// a little stupid (because this will print "Self=", and will show a wrong line)
    pub trait DotDebug {
        fn dot_debug(self) -> Self;
        fn dot_debug_with_info(self, info: &str) -> Self;
    }
    impl<T: Debug> DotDebug for T {
        #[inline(always)]
        fn dot_debug(self) -> Self {
            dbg!(self)
        }

        #[inline(always)]
        fn dot_debug_with_info(self, info: &str) -> Self {
            println!("{} {:#?}", info, self);
            self
        }
    }
}

pub mod mutable_init {

    /// a method takes an owned value, changes it in a closure, then return it;
    /// # Example
    /// ```
    /// use stupid_utils::mutable_init::MutableInit;
    /// use std::collections::HashMap;
    /// let a = HashMap::new().mutable_init(|m| {
    ///     m.insert(32, 42);
    ///     m.insert(33, 43);
    /// });
    ///
    /// let b = {
    ///     let mut v = HashMap::new();
    ///     v.insert(32, 42);
    ///     v.insert(33, 43);
    ///     v
    /// };
    ///
    /// assert_eq!(a, b);
    ///
    pub trait MutableInit {
        /// a method takes an owned value, changes it in a closure, then return it;
        ///
        /// see also [`MutableInit`]
        fn mutable_init<F>(self, f: F) -> Self
        where
            F: FnOnce(&mut Self);

        /// a method takes an owned value, changes it in a closure, then return what the closure returns;
        ///
        /// usahe:
        /// ```
        /// use stupid_utils::mutable_init::MutableInit;
        ///
        /// let a = [1, 2, 3];
        /// let a = a.iter();
        /// let (a1, a2, a3) = a.mutable_cast(|iter| {
        ///     (iter.next(), iter.next(), iter.next())
        /// });
        /// ```
        fn mutable_cast<F, O>(self, f: F) -> O
        where
            F: FnOnce(&mut Self) -> O;
    }

    impl<T> MutableInit for T {
        fn mutable_init<F>(mut self, f: F) -> Self
        where
            F: FnOnce(&mut Self),
        {
            f(&mut self);
            self
        }

        fn mutable_cast<F, O>(mut self, f: F) -> O
        where
            F: FnOnce(&mut Self) -> O,
        {
            f(&mut self)
        }
    }

    #[test]
    fn t() {
        let a = Vec::new().mutable_init(|s| {
            s.push(3);
            s.push(4);
            s.push(5);
        });
        assert_eq!(a, vec![3, 4, 5]);
    }
}

#[allow(unused)]
mod fake_truple {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::thread;
    use std::time::Duration;
    use std::{fmt::Debug, marker::PhantomData};

    use crate::predule::ArcMutex;

    struct Tr<T1, T2> {
        v1: T1,
        v2: T2,
    }

    impl<T1, T2> Tr<T1, T2> {
        pub fn new(v1: T1, v2: T2) -> Self {
            Self { v1, v2 }
        }
        pub fn mix<T3>(self, v3: T3) -> Tr<Self, T3> {
            Tr { v1: self, v2: v3 }
        }
        pub fn split(self) -> (T1, T2) {
            (self.v1, self.v2)
        }
    }
    trait M {}

    impl<T1, T2> Tr<Box<T1>, T2> {
        pub fn unpack(self) -> (Box<T1>, T2) {
            (self.v1, self.v2)
        }
    }

    impl<T1, T2, T3> Tr<Tr<T1, T2>, T3> {
        pub fn unpack(self) -> (Tr<T1, T2>, T3) {
            (
                Tr {
                    v1: self.v1.v1,
                    v2: self.v1.v2,
                },
                self.v2,
            )
        }
    }

    trait Show {
        fn show(&self) -> String;
    }

    impl<T1: Show, T2: Show> Show for Tr<T1, T2> {
        fn show(&self) -> String {
            format!("{:?},{:?}", self.v1.show(), self.v2.show())
        }
    }

    impl<T1: Debug, T2: Debug> Debug for Tr<T1, T2> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("Tr")
                .field("v1", &self.v1)
                .field("v2", &self.v2)
                .finish()
        }
    }
    #[test]
    fn t() {
        use crate::box_up::BoxUp;
        use crate::dot_debug::DotDebug;
        use crate::map_value::MapValue;

        let a = Tr::new(1, 2)
            .mix(3)
            .mix("32")
            .mix("2".to_owned())
            .mix(PhantomData::<f32>);
        dbg!(&a);

        let a = Tr::new(32.box_up(), "asda".box_up())
            .mix("asgdsadasiud".box_up())
            .mix(PhantomData::<f32>.box_up())
            .mix(3249239.box_up())
            .mix("v3".box_up())
            .mix((Box::new(0)).box_up())
            .mix(3.box_up());
        impl<T: Debug> Show for Box<T> {
            fn show(&self) -> String {
                format!("{:?}", self)
            }
        }

        println!("{}", a.show());

        a.unpack()
            .map_value(|(tr, v)| {
                dbg!(v);
                tr
            })
            .unpack()
            .map_value(|(tr, v)| {
                dbg!(v);
                tr
            })
            .unpack()
            .map_value(|(tr, v)| {
                dbg!(v);
                tr
            })
            .unpack()
            .map_value(|(tr, v)| {
                dbg!(v);
                tr
            })
            .dot_debug();
    }

    use crate::predule::*;
    use crate::short_unwrap::ShortUnwrap;
    fn dead_lock() {
        let lock1 = arc_mutex_new(1);
        let lock2 = arc_mutex_new(2);
        static C: AtomicU64 = AtomicU64::new(0);
        let l1 = lock1.clone();
        let l2 = lock2.clone();
        thread::sleep(Duration::from_secs_f32(f32::sin(
            C.load(Ordering::SeqCst) as f32 / 1000.,
        )));

        let a = thread::spawn(move || loop {
            let g1 = l1.lock().u();

            let g2 = l2.lock().u();

            print!("a,{},{} ", *g1, *g2);
            println!("{}", C.fetch_add(1, Ordering::SeqCst));
            drop(g1);
            drop(g2);
        });

        let l1 = lock1.clone();
        let l2 = lock2.clone();
        let b = thread::spawn(move || loop {
            // let g2 = l2.lock().u();

            // let g1 = l1.lock().u();

            let (g1, g2) = loop {
                if let (Ok(g1), Ok(g2)) = (l1.try_lock(), l2.try_lock()) {
                    break (g1, g2);
                }
            };

            print!("b,{},{} ", *g1, *g2);
            println!("{}", C.fetch_add(1, Ordering::SeqCst));
            drop(g1);
            drop(g2);
        });

        a.join();
        b.join();
    }

    trait M1 {}
    trait M2 {}
    trait M3 {}

    impl M1 for i32 {}
    impl M3 for i32 {}
    impl<T: M1> M2 for T {}
    impl M2 for i64 {}
}

pub mod stack_struct {
    use std::{
        fmt::Debug,
        ops::{Deref, DerefMut},
    };

    pub use self::pop_first::PopFirst;
    pub use self::push_first::PushFirst;
    /// just for fun (also is interesting)
    pub struct Stack<T1, T2> {
        v1: T1,
        v2: T2,
    }
    impl<T1: Debug, T2: Debug> Debug for Stack<T1, T2> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("Stack")
                .field("v1", &self.v1)
                .field("v2", &self.v2)
                .finish()
        }
    }
    /// just for fun
    pub struct Value<T>(T);
    impl<T: Debug> Debug for Value<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_tuple("Value").field(&self.0).finish()
        }
    }
    impl<T> Deref for Value<T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }
    impl<T> DerefMut for Value<T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }
    impl<T> From<T> for Value<T> {
        fn from(value: T) -> Self {
            Value(value)
        }
    }

    impl<T> Value<T> {
        pub fn into_inner(self) -> T {
            self.0
        }
        pub fn pop(self) -> T {
            self.into_inner()
        }
        pub fn pop_first(self) -> T {
            self.into_inner()
        }
        pub fn push<T2>(self, v: T2) -> Stack<Value<T>, Value<T2>> {
            Stack {
                v1: self,
                v2: Value(v),
            }
        }
    }

    impl<T1, T2> Stack<T1, T2> {
        pub const fn push<T3>(self, v: T3) -> Stack<Stack<T1, T2>, Value<T3>> {
            Stack {
                v1: self,
                v2: Value(v),
            }
        }
    }
    impl<T1, T2> Stack<T1, Value<T2>> {
        pub fn pop(self) -> (T1, T2) {
            (self.v1, self.v2.0)
        }
        pub const fn last(&self) -> &T2 {
            &self.v2.0
        }
        pub fn last_mut(&mut self) -> &mut T2 {
            &mut self.v2.0
        }
    }
    impl<T1, T2> Stack<Value<T1>, Value<T2>> {
        pub const fn from_two_value(v1: T1, v2: T2) -> Self {
            Self {
                v1: Value(v1),
                v2: Value(v2),
            }
        }
    }
    mod pop_first {

        use super::{Stack, Value};

        pub trait PopFirst<First, Remain> {
            fn depth(&self) -> usize;
            fn first(&self) -> &First;
            fn first_mut(&mut self) -> &mut First;
            fn pop_first(self) -> (Remain, First);
        }

        impl<T1, T2> PopFirst<T1, Value<T2>> for Stack<Value<T1>, Value<T2>> {
            fn pop_first(self) -> (Value<T2>, T1) {
                (self.v2, self.v1.0)
            }

            fn depth(&self) -> usize {
                2
            }

            fn first(&self) -> &T1 {
                &self.v1.0
            }

            fn first_mut(&mut self) -> &mut T1 {
                &mut self.v1.0
            }
        }

        impl<S, First, Remain, T> PopFirst<First, Stack<Remain, T>> for Stack<S, T>
        where
            S: PopFirst<First, Remain>,
        {
            fn pop_first(self) -> (Stack<Remain, T>, First) {
                let Stack { v1, v2 } = self;
                let (remain, first) = v1.pop_first();
                (Stack { v1: remain, v2 }, first)
            }

            fn depth(&self) -> usize {
                self.v1.depth() + 1
            }

            fn first(&self) -> &First {
                self.v1.first()
            }

            fn first_mut(&mut self) -> &mut First {
                self.v1.first_mut()
            }
        }
        #[test]
        fn t() {
            use crate::dot_debug::DotDebug;
            let mut s = Stack::from_two_value(1, "2").push(3.).push("4".to_owned());
            let _f = s.first();
            let _l = s.last();
            let _f = s.first_mut();
            let _l = s.last_mut();

            s.depth().dot_debug_with_info("depth is");
            let (s, v1) = s.pop_first();
            let (s, v2) = s.pop_first();
            let (s, v3) = s.pop_first();
            let v4 = s.into_inner();
            dbg!((v1, v2, v3, v4));
        }
    }
    mod push_first {

        use super::{Stack, Value};

        pub trait PushFirst<First, After> {
            fn push_first(self, v: First) -> After;
        }

        impl<First, T> PushFirst<First, Stack<Value<First>, Value<T>>> for Value<T> {
            fn push_first(self, v: First) -> Stack<Value<First>, Value<T>> {
                Stack {
                    v1: Value(v),
                    v2: self,
                }
            }
        }

        impl<S, First, After, T> PushFirst<First, Stack<After, T>> for Stack<S, T>
        where
            S: PushFirst<First, After>,
        {
            fn push_first(self, v: First) -> Stack<After, T> {
                let Stack { v1, v2 } = self;
                Stack {
                    v1: v1.push_first(v),
                    v2,
                }
            }
        }

        #[test]
        fn t() {
            use crate::{dot_debug::DotDebug, stack_struct::pop_first::PopFirst};
            use std::mem::size_of_val;
            let t: (f64, String, &str, i32) = (1., "2".to_owned(), "3", 4);

            let s = Value::from(4)
                .push_first("3")
                .push_first("2".to_owned())
                .push_first(1.)
                .dot_debug();

            assert_eq!(size_of_val(&t), size_of_val(&s));

            let _f = s.first();

            let (s, v4) = s.pop();
            let (s, v3) = s.pop();
            let (s, v2) = s.pop();
            let v1 = s.pop();

            let _t2 = dbg!((v1, v2, v3, v4));
        }
    }
    #[test]
    fn t() {
        use crate::predule::*;
        let s = Stack::from_two_value(1, "2").push(3.);
        let (s, _v1) = s.pop();
        let s = s
            .push("4".to_owned())
            .push(134)
            .push(2.box_up())
            .push_first("d".to_owned().box_up().box_up())
            .push(2)
            .push(213.box_up().box_up())
            .push("")
            .push(413.)
            .push(9)
            .push("4".to_owned())
            .push(134)
            .push(2.box_up())
            .push_first("d".to_owned().box_up().box_up().box_up())
            .push(2)
            .push(213.box_up().box_up())
            .push("")
            .push(413.)
            .push(9);
        dbg!(s.depth());
        dbg!(s);
    }
}

pub mod print_on_drop {
    /// a struct that will print some infomation when drop
    /// the info can be set when creating a new struct
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct PrintOnDrop {
        info: String,
    }

    /// a struct that will print some infomation when drop
    /// the info is fixed `droped a PrintOnDropNoInfo`
    /// the struct is zero-sized
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct PrintOnDropNoInfo;
    impl PrintOnDrop {
        pub fn new(info: &str) -> Self {
            Self {
                info: info.to_owned(),
            }
        }
    }
    impl Drop for PrintOnDrop {
        fn drop(&mut self) {
            println!("{}", self.info);
        }
    }

    impl Drop for PrintOnDropNoInfo {
        fn drop(&mut self) {
            println!("droped a PrintOnDropNoInfo")
        }
    }

    #[test]
    fn test() {
        use std::mem::MaybeUninit;
        let _a = PrintOnDrop::new("1");
        let _a = PrintOnDrop::new("2");
        let _a: PrintOnDrop = PrintOnDrop::new("3");
        #[allow(invalid_value)]
        let _a: PrintOnDropNoInfo = unsafe { MaybeUninit::uninit().assume_init() };
        println!("here");
    }
}

pub mod one_or_many {
    use std::fmt::Debug;
    /// a struct that can contain one or many value,
    ///
    /// note than [`OneOrMany::Many`] does not guarantee the vec really contains 2+ values, it many be empty or only contains a single value
    ///
    /// why use this instead of [`Vec<T>`]:
    /// [`Vec<T>`] will always allocate memory on heap, even if the vec only contains a single value
    ///
    /// why use [`Vec<T>`] instead of this:
    /// [`Vec<T>`]'s size is basically fixed 24bit, but this struct's size is expected to be bigger than `T`
    ///
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub enum OneOrMany<T> {
        One(T),
        Many(Vec<T>),
    }

    impl<T> OneOrMany<T> {
        pub fn from_one(value: T) -> Self {
            OneOrMany::One(value)
        }
        pub fn from_vec(mut value: Vec<T>) -> Option<Self> {
            if value.len() > 1 {
                Some(OneOrMany::Many(value))
            } else {
                Some(OneOrMany::One(value.pop()?))
            }
        }
        pub fn push(&mut self, value: T) {
            // this function will never panic
            // it does not call any of T's methods including destructor

            // now self is uninit, dropping it is ub
            // old_value is a valid value
            let old_value = unsafe {
                std::ptr::read(self)
                // std::mem::replace(self, MaybeUninit::uninit().assume_init())
            };

            // constructing a new OneOrMany from old_value, no value is dropped
            let value_1 = match old_value {
                OneOrMany::One(value0) => vec![value0, value],
                OneOrMany::Many(mut vec0) => {
                    vec0.push(value);
                    vec0
                }
            };
            let mut new_value = OneOrMany::Many(value_1);

            // now new_value is uninit, it should not be dropped
            std::mem::swap(&mut new_value, self);

            // move new_value without calling the destructor
            std::mem::forget(new_value);

            // new_value is moved, so this line will not compile
            // &new_value;
        }
        pub fn is_many(&self) -> bool {
            match self {
                OneOrMany::One(_) => false,
                OneOrMany::Many(vec) => vec.len() > 1,
            }
        }
        pub fn is_one(&self) -> bool {
            match self {
                OneOrMany::One(_) => true,
                OneOrMany::Many(vec) => vec.len() == 1,
            }
        }
        pub fn is_zero(&self) -> bool {
            match self {
                OneOrMany::One(_) => false,
                OneOrMany::Many(vec) => vec.is_empty(),
            }
        }
        pub fn pop(&mut self) -> Option<T> {
            let vec = match self {
                OneOrMany::One(_) => return None,
                OneOrMany::Many(v) => v,
            };
            match vec.len() {
                0 => None,
                1 => {
                    let v = vec.pop()?;
                    *self = OneOrMany::One(v);
                    None
                }
                2 => {
                    let v2 = vec.pop()?;
                    let v1 = vec.pop()?;
                    *self = OneOrMany::One(v1);
                    Some(v2)
                }
                3.. => vec.pop(),
                // _ => {
                //     unreachable!()
                // }
            }
        }
        pub fn take_one(self) -> Result<T, Self> {
            match self {
                OneOrMany::One(v) => Ok(v),
                OneOrMany::Many(mut vec) => {
                    if vec.len() == 1 {
                        if let Some(v) = vec.pop() {
                            Ok(v)
                        } else {
                            unreachable!("vec with len 1 should always pop a Some(T) value")
                        }
                    } else {
                        Err(OneOrMany::Many(vec))
                    }
                }
            }
        }
    }

    #[test]
    fn test() {
        // enum E1 {
        //     A(String),
        //     B(String),
        // }
        // impl E1 {
        //     fn a_to_b(&mut self) {
        //         *self = match *self {
        //             E1::A(v) => E1::B(v),
        //             E1::B(v) => E1::B(v),
        //         };
        //     }
        // }

        use crate::print_on_drop::{PrintOnDrop, PrintOnDropNoInfo};
        let mut a = OneOrMany::One(PrintOnDropNoInfo);
        dbg!((a.is_one(), a.is_many()));
        a.push(PrintOnDropNoInfo);
        dbg!((a.is_one(), a.is_many()));

        let mut a1 = OneOrMany::One(PrintOnDrop::new("a"));
        dbg!((a1.is_one(), a1.is_many()));
        a1.push(PrintOnDrop::new("b"));
        dbg!((a1.is_one(), a1.is_many()));

        let oa1 = Some(a1.clone());
        assert_eq!(std::mem::size_of_val(&oa1), std::mem::size_of_val(&a1));

        let mut a2 = OneOrMany::from_one(2);
        assert_eq!(a2, OneOrMany::One(2));

        a2.push(3);
        assert_eq!(a2, OneOrMany::Many(vec![2, 3]));

        a2.push(4);
        assert_eq!(a2, OneOrMany::Many(vec![2, 3, 4]));

        let a2 = a2.take_one();
        assert_eq!(a2, Err(OneOrMany::Many(vec![2, 3, 4])));

        let mut a2 = a2.unwrap_err();
        assert_eq!(a2, OneOrMany::Many(vec![2, 3, 4]));

        assert_eq!(a2.pop(), Some(4));
        assert_eq!(a2, OneOrMany::Many(vec![2, 3]));

        assert_eq!(a2.pop(), Some(3));
        assert_eq!(a2, OneOrMany::One(2));

        assert_eq!(a2.pop(), None);
        assert_eq!(a2, OneOrMany::One(2));

        assert_eq!(a2.take_one(), Ok(2));
        println!("end");
    }
}

pub mod extend_map_iter {
    /// similer to [Vec], but only provides [`PushOnlyVec::push`][`crate::extend_map_iter::PushOnlyVec`] method  
    #[derive(Debug)]
    pub struct PushOnlyVec<T> {
        inner: Vec<T>,
    }
    impl<T> PushOnlyVec<T> {
        /// push a value
        pub fn push(&mut self, value: T) {
            self.inner.push(value);
        }
        fn new() -> Self {
            Self { inner: vec![] }
        }
    }

    pub struct ExtendMapIter<F, T, T1, Iter>
    where
        F: FnMut(T, &mut PushOnlyVec<T1>),
        Iter: Iterator<Item = T>,
    {
        f: F,
        iter: Iter,
        old_value: PushOnlyVec<T1>,
    }

    impl<F, T, T1, Iter> Iterator for ExtendMapIter<F, T, T1, Iter>
    where
        F: FnMut(T, &mut PushOnlyVec<T1>),
        Iter: Iterator<Item = T>,
    {
        type Item = T1;

        fn next(&mut self) -> Option<Self::Item> {
            while self.old_value.inner.is_empty() {
                let value = self.iter.next()?;
                (self.f)(value, &mut self.old_value);
            }
            self.old_value.inner.pop()
        }
    }

    pub trait ExtendMap<F, T, T1, Iter>
    where
        F: FnMut(T, &mut PushOnlyVec<T1>),
        Iter: Iterator<Item = T>,
    {
        /// similer to `map()`, but one value can create many value;
        ///
        /// `f` takes two args, first is the value produced from the iterator, second is a [PushOnlyVec] where you can push some values into
        /// # Example
        /// ```
        /// use stupid_utils::predule::*;
        /// assert_eq!(
        ///     vec![0, 1, 2, 3]
        ///         .into_iter()
        ///         .extend_map(|v, out| {
        ///             for _ in 0..v {
        ///                 out.push(v);
        ///             }
        ///         })
        ///         .collect::<Vec<_>>(),
        ///     vec![1, 2, 2, 3, 3, 3]
        /// )
        /// ```
        fn extend_map(self, f: F) -> ExtendMapIter<F, T, T1, Iter>;
    }

    impl<F, T, T1, Iter> ExtendMap<F, T, T1, Iter> for Iter
    where
        F: FnMut(T, &mut PushOnlyVec<T1>),
        Iter: Iterator<Item = T>,
    {
        fn extend_map(self, f: F) -> ExtendMapIter<F, T, T1, Iter> {
            ExtendMapIter {
                f,
                iter: self,
                old_value: PushOnlyVec::new(),
            }
        }
    }

    #[test]
    fn test() {
        for _i in vec![0, 1, 2, 3]
            .into_iter()
            .extend_map(|v, out| {
                for _ in 0..v {
                    out.push(v);
                }
            })
            .extend_map(|v, out| {
                for _ in 0..v {
                    out.push(v);
                }
            })
        {
            // println!("{}", i);
        }

        assert_eq!(
            vec![0, 1, 2, 3]
                .into_iter()
                .extend_map(|v, out| {
                    for _ in 0..v {
                        out.push(v);
                    }
                })
                .collect::<Vec<_>>(),
            vec![1, 2, 2, 3, 3, 3]
        )
    }
}

pub mod wrap_in_whatever {
    pub trait WrapInWhatever: Sized {
        /// wrap value in `Some`
        fn some_wrap(self) -> Option<Self> {
            Some(self)
        }
        /// wrap value in `Ok`
        fn ok_wrap<Err>(self) -> Result<Self, Err> {
            Ok(self)
        }
        /// wrao value in `Err`
        fn err_wrap<T>(self) -> Result<T, Self> {
            Err(self)
        }
    }
    impl<T> WrapInWhatever for T {}
}

pub mod just_provide {
    /// used in `map`, ignore input and just return a fixed value
    ///
    /// ## Example
    /// ```
    /// use stupid_utils::just_provide::just_provide;
    ///
    /// let a: Result<(), i32> = Err(42);
    /// let b = a.map_err(just_provide("40 + 2".to_owned()));
    ///
    /// assert_eq!(b, Err("40 + 2".to_owned()));
    /// ```
    pub fn just_provide<T, P>(value: T) -> impl FnOnce(P) -> T {
        |_| value
    }
    // fn a() {
    //     let a = String::new();
    //     // let b = || drop(a);
    // }
}

pub mod disabled {
    /// disables a identfier
    #[macro_export]
    macro_rules! disable {
        ($name:ident) => {
            let $name = {
                struct Disabled;
                Disabled
            };
            #[allow(clippy::drop_non_drop)]
            ::std::mem::drop($name);
        };
    }
    #[test]
    #[allow(unused)]
    fn _a() {
        let a = 32;
        let a = {
            struct Disabled;

            Disabled
        };
        #[allow(clippy::drop_non_drop)]
        ::std::mem::drop(a);
        let b = 31;
        disable!(b);
        // b;
    }
}

pub mod instant_run {
    #[macro_export]
    macro_rules! instant_run {
        () => {
            ()
        };
        ($e:expr) => {
            (|| {
                ();
                $e
            })()
        };
        ($($e:tt)*) => {
            (|| {
                ();
                $($e)*
            })()
        };
        // ($e:q) => {};
    }
    #[test]
    fn _a() {
        let a = instant_run!({
            let d = Some(1)?;
            let _g = None?;
            dbg!(d);
            Some(())
        });
        dbg!(a);
    }
}

pub mod dot_ref {
    /// returns `&self` and `&mut self` in methods
    pub trait DotRef {
        /// just returns a `&self`
        fn dot_ref(&self) -> &Self {
            self
        }
        /// just returns a `&mut self`
        fn dot_mut(&mut self) -> &mut Self {
            self
        }
    }
    impl<T: ?Sized> DotRef for T {}
    #[test]
    fn t() {
        let a = 32;
        let _b = a.dot_ref();
        let mut c = 32;
        let _d = c.dot_mut();
    }
}

pub mod if_iter_remains {
    use std::iter::FusedIterator;

    pub trait IfIterRemains: Iterator + Sized {
        /// wrap the iter into a new iter which can cache one item and thus can tells if there is item left
        ///
        /// this will cause `self` to run [Iterator::next] once instantly (but will not lose any item)
        fn into_testable_iter(self) -> CacheOneIter<Self>;
        fn into_iter_with_test_info(self) -> IterWithRemainingInfo<Self> {
            IterWithRemainingInfo(self.into_testable_iter())
        }
    }
    #[test]
    fn a() {
        let a = [14, 116, 18];
        let mut a = a.iter().into_testable_iter();
        assert!(a.remains());
        assert_eq!(a.next(), Some(&14));
        assert!(a.remains());
        assert_eq!(a.next(), Some(&116));
        assert!(a.remains());
        assert_eq!(a.next(), Some(&18));
        assert!(!a.remains());
        assert_eq!(a.next(), None);

        let a = ["14".to_owned(), "116".to_owned(), "18".to_owned()];
        let mut a = a.into_iter().into_testable_iter();
        assert!(a.remains());
        assert_eq!(a.next(), Some("14".to_owned()));
        assert!(a.remains());
        assert_eq!(a.next(), Some("116".to_owned()));
        assert!(a.remains());
        assert_eq!(a.next(), Some("18".to_owned()));
        assert!(!a.remains());
        assert_eq!(a.next(), None);
    }
    impl<T: Iterator> IfIterRemains for T {
        fn into_testable_iter(mut self) -> CacheOneIter<Self> {
            CacheOneIter {
                next_item: self.next(),
                iter: self,
            }
        }
    }
    pub struct CacheOneIter<Iter: Iterator> {
        next_item: Option<Iter::Item>,
        iter: Iter,
    }
    pub struct IterWithRemainingInfo<Iter: Iterator>(CacheOneIter<Iter>);
    impl<Iter: Iterator> FusedIterator for IterWithRemainingInfo<Iter> {}
    impl<Iter: Iterator> Iterator for IterWithRemainingInfo<Iter> {
        type Item = (Iter::Item, bool);

        fn next(&mut self) -> Option<Self::Item> {
            let item = self.0.next()?;
            let remains = self.0.remains();
            Some((item, remains))
        }
    }

    impl<Iter: Iterator> CacheOneIter<Iter> {
        /// tells if there is any item left
        pub fn remains(&self) -> bool {
            self.next_item.is_some()
        }
    }
    impl<Iter: Iterator> FusedIterator for CacheOneIter<Iter> {}
    impl<Iter: Iterator> Iterator for CacheOneIter<Iter> {
        type Item = Iter::Item;

        fn next(&mut self) -> Option<Self::Item> {
            if self.next_item.is_none() {
                return None;
            }
            let next_item = self.next_item.take();
            self.next_item = self.iter.next();
            next_item
        }
    }
}
