# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.5.0] - 2019-07-04 (ETA)

### Added

- `Pool` now implements the `Sync` trait when targeting ARMv7-R.

- Most data structures can now be constructed in "const context" (e.g. `static
  [mut]` variables) using a newtype in `heapless::i`.

- `Pool` has gained a `grow_exact` method to more efficiently use statically
  allocated memory.

- The `pool!` macro now accepts attributes.

- `mpmc::Q*` a family of fixed capacity multiple-producer multiple-consumer
  lock-free queues.

### Changed

- [breaking-change] `binary_heap::Kind` is now a sealed trait.

### Removed

- [breaking-change] The "smaller-atomics" feature has been removed. It is now
  always enabled.

- [breaking-change] The "min-const-fn" feature has been removed. It is now
  always enabled.

- [breaking-change] The MSRV has been bumped to Rust 1.36.0.

- [breaking-change] The version of the `generic-array` dependency has been
  bumped to v0.13.0.

## [v0.4.4] - 2019-05-02

### Added

- Implemented `PartialEq`, `PartialOrd`, `Eq`, `Ord` and `Hash` for `pool::Box`
  and `pool::singleton::Box`.

### Fixed

- Fixed UB in our internal, stable re-implementation of `core::mem::MaybeUninit`
  that occurred when using some of our data structures with types that implement
  `Drop`.

## [v0.4.3] - 2019-04-22

### Added

- Added a memory pool that's lock-free and interrupt-safe on the ARMv7-M
architecture.

- `IndexMap` have gained `Eq` and `PartialEq` implementations.

## [v0.4.2] - 2019-02-12

### Added

- All containers now implement `Clone`

- `spsc::Queue` now implements `Debug`, `Hash`, `PartialEq` and `Eq`

- `LinearMap` now implements `Debug`, `FromIterator`, `IntoIter`, `PartialEq`,
  `Eq` and `Default`

- `BinaryHeap` now implements `Debug` and `Default`

- `String` now implements `FromStr`, `Hash`, `From<uxx>` and `Default`

- `Vec` now implements `Hash` and `Default`

- A "serde" Cargo feature that when enabled adds a `serde::Serialize` and
  `serde::Deserialize` implementations to each collection.

## [v0.4.1] - 2018-12-16

### Changed

- Add a new type parameter to `spsc::Queue` that indicates whether the queue is
  only single-core safe, or multi-core safe. By default the queue is multi-core
  safe; this preserves the current semantics. New `unsafe` constructors have
  been added to create the single-core variant.

## [v0.4.0] - 2018-10-19

### Changed

- [breaking-change] All Cargo features are disabled by default. This crate now
  compiles on stable by default.

- [breaking-change] RingBuffer has been renamed to spsc::Queue. The ring_buffer
  module has been renamed to spsc.

- [breaking-change] The bounds on spsc::Queue have changed.

### Removed

- [breaking-change] The sealed `Uxx` trait has been removed from the public API.

## [v0.3.7] - 2018-08-19

### Added

- Implemented `IntoIterator` and `FromIterator` for `Vec`
- `ready` methods to `ring_buffer::{Consumer,Producer}`
- An opt-out "const-fn" Cargo feature that turns `const` functions into normal functions when
  disabled.
- An opt-out "smaller-atomics" Cargo feature that removes the ability to shrink the size of
  `RingBuffer` when disabled.

### Changed

- This crate now compiles on stable when both the "const-fn" and "smaller-atomics" features are
  disabled.

### Fixed

- The `RingBuffer.len` function
- Compilation on recent nightlies

## [v0.3.6] - 2018-05-04

### Fixed

- The capacity of `RingBuffer`. It should be the requested capacity plus not twice that plus one.

## [v0.3.5] - 2018-05-03

### Added

- `RingBuffer.enqueue_unchecked` an unchecked version of `RingBuffer.enqueue`

## [v0.3.4] - 2018-04-28

### Added

- `BinaryHeap.pop_unchecked` an unchecked version of `BinaryHeap.pop`

## [v0.3.3] - 2018-04-28

### Added

- `BinaryHeap.push_unchecked` an unchecked version of `BinaryHeap.push`

## [v0.3.2] - 2018-04-27

### Added

- A re-export of `generic_array::ArrayLength`, for convenience.

## [v0.3.1] - 2018-04-23

### Added

- Fixed capacity implementations of `IndexMap` and `IndexSet`.
- A `Extend` implementation to `Vec`
- More `PartialEq` implementations to `Vec`

## [v0.3.0] - 2018-04-22

### Changed

- [breaking-change] The capacity of all data structures must now be specified using type level
  integers (cf. `typenum`). See documentation for details.

- [breaking-change] `BufferFullError` has been removed in favor of (a) returning ownership of the
  item that couldn't be added to the collection (cf. `Vec.push`), or (b) returning the unit type
  when the argument was not consumed (cf. `Vec.extend_from_slice`).

## [v0.2.7] - 2018-04-20

### Added

- Unchecked methods to dequeue and enqueue items into a `RingBuffer` via the `Consumer` and
  `Producer` end points.

### Changed

- `RingBuffer` now has a generic index type, which default to `usize` for backward compatibility.
  Changing the index type to `u8` or `u16` reduces the footprint of the `RingBuffer` but limits its
  maximum capacity (254 and 65534, respectively).

## [v0.2.6] - 2018-04-18

### Added

- A `BinaryHeap` implementation. `BinaryHeap` is a priority queue implemented with a binary heap.

## [v0.2.5] - 2018-04-13

### Fixed

- Dereferencing `heapless::Vec` no longer incurs in a bounds check.

## [v0.2.4] - 2018-03-12

### Fixed

- `LinerMap::new` is now a const fn

## [v0.2.3] - 2018-03-11

### Added

- A `swap_remove` method to `Vec`
- A `LinearMap` implementation. `LinearMap` is a map / dict backed by an array and that performs
  lookups via linear search.

## [v0.2.2] - 2018-03-01

### Added

- Fixed size version of `std::String`

## [v0.2.1] - 2017-12-21

### Added

- `Vec` now implements both `fmt::Debug`, `PartialEq` and `Eq`.

- `resize` and `resize_default` methods to `Vec`.

## [v0.2.0] - 2017-11-22

### Added

- A single producer single consumer mode to `RingBuffer`.

- A `truncate` method to `Vec`.

### Changed

- [breaking-change] Both `Vec::new` and `RingBuffer::new` no longer require an initial value. The
  signature of `new` is now `const fn() -> Self`.

- [breaking-change] The error type of all operations that may fail has changed from `()` to
  `BufferFullError`.

- Both `RingBuffer` and `Vec` now support arrays of *any* size for their backup storage.

## [v0.1.0] - 2017-04-27

- Initial release

[Unreleased]: https://github.com/japaric/heapless/compare/v0.5.0...HEAD
[v0.5.0]: https://github.com/japaric/heapless/compare/v0.4.4...v0.5.0
[v0.4.4]: https://github.com/japaric/heapless/compare/v0.4.3...v0.4.4
[v0.4.3]: https://github.com/japaric/heapless/compare/v0.4.2...v0.4.3
[v0.4.2]: https://github.com/japaric/heapless/compare/v0.4.1...v0.4.2
[v0.4.1]: https://github.com/japaric/heapless/compare/v0.4.0...v0.4.1
[v0.4.0]: https://github.com/japaric/heapless/compare/v0.3.7...v0.4.0
[v0.3.7]: https://github.com/japaric/heapless/compare/v0.3.6...v0.3.7
[v0.3.6]: https://github.com/japaric/heapless/compare/v0.3.5...v0.3.6
[v0.3.5]: https://github.com/japaric/heapless/compare/v0.3.4...v0.3.5
[v0.3.4]: https://github.com/japaric/heapless/compare/v0.3.3...v0.3.4
[v0.3.3]: https://github.com/japaric/heapless/compare/v0.3.2...v0.3.3
[v0.3.2]: https://github.com/japaric/heapless/compare/v0.3.1...v0.3.2
[v0.3.1]: https://github.com/japaric/heapless/compare/v0.3.0...v0.3.1
[v0.3.0]: https://github.com/japaric/heapless/compare/v0.2.7...v0.3.0
[v0.2.7]: https://github.com/japaric/heapless/compare/v0.2.6...v0.2.7
[v0.2.6]: https://github.com/japaric/heapless/compare/v0.2.5...v0.2.6
[v0.2.5]: https://github.com/japaric/heapless/compare/v0.2.4...v0.2.5
[v0.2.4]: https://github.com/japaric/heapless/compare/v0.2.3...v0.2.4
[v0.2.3]: https://github.com/japaric/heapless/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/japaric/heapless/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/japaric/heapless/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/japaric/heapless/compare/v0.1.0...v0.2.0
