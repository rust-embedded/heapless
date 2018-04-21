# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

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

[Unreleased]: https://github.com/japaric/heapless/compare/v0.3.0...HEAD
[v0.3.0]: https://github.com/japaric/heapless/compare/v0.2.7...v0.3.0
[v0.2.7]: https://github.com/japaric/heapless/compare/v0.2.6...v0.2.7
[v0.2.6]: https://github.com/japaric/heapless/compare/v0.2.5...v0.2.6
[v0.2.5]: https://github.com/japaric/heapless/compare/v0.2.4...v0.2.5
[v0.2.4]: https://github.com/japaric/heapless/compare/v0.2.3...v0.2.4
[v0.2.3]: https://github.com/japaric/heapless/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/japaric/heapless/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/japaric/heapless/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/japaric/heapless/compare/v0.1.0...v0.2.0
