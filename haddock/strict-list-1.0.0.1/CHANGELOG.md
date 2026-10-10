## v1.0.0.0

### Breaking changes

- The strict list type was renamed from `List` to `StrictList` throughout the API to avoid confusion with the `List` type alias from `base`.
- `Ord` for `StrictList` now matches the standard lazy list ordering, so empty lists compare smaller than non-empty lists and lexicographic comparison follows the usual `[]` semantics.

### Other changes

- Added `Arbitrary` support in the test suite.
