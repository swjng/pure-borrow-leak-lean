import Lake
open Lake DSL

package "PureBorrowLeak" where
  -- self-contained, no Mathlib dependency

lean_lib «PureBorrowLeak» where
  roots := #[`PureBorrowLeak]
