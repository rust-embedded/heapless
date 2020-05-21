use crate::{
    ArrayLength,
    bytebuf::ByteBuf,
    string::String,
    vec::Vec,
};

impl<N> ufmt::uDebug for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite + ?Sized,
    {
        <[u8] as ufmt::uDebug>::fmt(self, f)
    }
}

impl<N> ufmt::uDebug for String<N>
where
    N: ArrayLength<u8>,
{
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite + ?Sized,
    {
        <[u8] as ufmt::uDebug>::fmt(self.as_str().as_bytes(), f)
    }
}

impl<N, T> ufmt::uDebug for Vec<T, N>
where
    N: ArrayLength<T>,
    T: ufmt::uDebug,
{
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite + ?Sized,
    {
        <[T] as ufmt::uDebug>::fmt(self, f)
    }
}

impl<N> ufmt::uWrite for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    type Error = ();
    fn write_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.extend_from_slice(s.as_bytes())
    }
}

impl<N> ufmt::uWrite for String<N>
where
    N: ArrayLength<u8>,
{
    type Error = ();
    fn write_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.push_str(s)
    }
}

impl<N> ufmt::uWrite for Vec<u8, N>
where
    N: ArrayLength<u8>,
{
    type Error = ();
    fn write_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.extend_from_slice(s.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use ufmt::{derive::uDebug, uwrite};

    use crate::consts::*;

    #[derive(uDebug)]
    struct Pair {
        x: u32,
        y: u32,
    }

    #[test]
    fn test_string() {
        let a = 123;
        let b = Pair { x: 0, y: 1234 };

        let mut s = String::<U32>::new();
        uwrite!(s, "{} -> {:?}", a, b).unwrap();

        assert_eq!(s, "123 -> Pair { x: 0, y: 1234 }");
    }

    #[test]
    fn test_string_err() {
        let p = Pair { x: 0, y: 1234 };
        let mut s = String::<U4>::new();
        assert!(uwrite!(s, "{:?}", p).is_err());
    }

    #[test]
    fn test_vec() {
        let a = 123;
        let b = Pair { x: 0, y: 1234 };

        let mut v = Vec::<u8, U32>::new();
        uwrite!(v, "{} -> {:?}", a, b).unwrap();

        assert_eq!(v, b"123 -> Pair { x: 0, y: 1234 }");
    }
}
