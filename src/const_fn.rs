
macro_rules! const_fn {
    ($(#[$attr:meta])* pub const unsafe fn $($f:tt)*) => (

        $(#[$attr])*
        #[cfg(feature = "const-fn")]
        pub const unsafe fn $($f)*

        $(#[$attr])*
        #[cfg(not(feature = "const-fn"))]
        pub unsafe fn $($f)*
    );
    ($(#[$attr:meta])* pub const fn $($f:tt)*) => (

        $(#[$attr])*
        #[cfg(feature = "const-fn")]
        pub const fn $($f)*

        $(#[$attr])*
        #[cfg(not(feature = "const-fn"))]
        pub fn $($f)*
    );
    ($(#[$attr:meta])* const fn $($f:tt)*) => (
        $(#[$attr])*
        #[cfg(feature = "const-fn")]
        const fn $($f)*

        $(#[$attr])*
        #[cfg(not(feature = "const-fn"))]
        fn $($f)*
    );
}
