use crate::{
    string::{StringInner, StringStorage},
    vec::{VecInner, VecStorage},
    CapacityError,
};
use ufmt_write::uWrite;

impl<S: StringStorage + ?Sized> uWrite for StringInner<S> {
    type Error = CapacityError;
    fn write_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.push_str(s)
    }
}

impl<S: VecStorage<u8> + ?Sized> uWrite for VecInner<u8, S> {
    type Error = CapacityError;
    fn write_str(&mut self, s: &str) -> Result<(), Self::Error> {
        self.extend_from_slice(s.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use crate::{String, Vec};

    use ufmt::{derive::uDebug, uwrite};

    #[derive(uDebug)]
    struct Pair {
        x: u32,
        y: u32,
    }

    #[test]
    fn test_string() {
        let a = 123;
        let b = Pair { x: 0, y: 1234 };

        let mut s = String::<32>::new();
        uwrite!(s, "{} -> {:?}", a, b).unwrap();

        assert_eq!(s, "123 -> Pair { x: 0, y: 1234 }");
    }

    #[test]
    fn test_string_err() {
        let p = Pair { x: 0, y: 1234 };
        let mut s = String::<4>::new();
        assert!(uwrite!(s, "{:?}", p).is_err());
    }

    #[test]
    fn test_vec() {
        let a = 123;
        let b = Pair { x: 0, y: 1234 };

        let mut v = Vec::<u8, 32>::new();
        uwrite!(v, "{} -> {:?}", a, b).unwrap();

        assert_eq!(v, b"123 -> Pair { x: 0, y: 1234 }");
    }
}
