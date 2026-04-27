# PureBorrowLeak

A minimal Lean 4 formalisation of the static side of the leak-freedom
argument from the blog post *Pure Borrow + Leak: footnote 24
따라가보기*.

The post extends Pure Borrow (Matsushita & Ishii, PLDI 2026) with a
`class Leak` and an `LRc` reference-counting primitive, and conjectures
that leak freedom (Theorem 5.3) generalises.  This repo discharges the
*type-level* obligations of that argument; the runtime side (full
association system, reduction, `Theorem 5.3*` proof) is deferred and
exposed as a single `axiom`.

## What is mechanised

| File | Content | Status |
| --- | --- | --- |
| `PureBorrowLeak.lean` | Type syntax, `Leak`, `LinearOnly` | full proofs |
| same | `linearOnly_not_leak` | proved |
| same | `lend_static_iff`, `share_static_iff` | proved |
| same | `fn_not_leak`, `linFn_not_leak` | proved |
| same | `Leak.decidable` | proved |
| same | `WellSeparated`, `.nil`, `.cons_linear`, `.cons_rc` | proved |
| same | `theorem_5_3_star` | **axiom** (deferred) |

`linearOnly_not_leak` is the structural backbone: any LinearOnly type
is uninhabited under `Leak`.  This justifies the post's blanket
classification of `Linearly`, `Now^α`, `Ref a`, `Mut^α a`, `BO^α a` as
`!Leak` without case-by-case argument.

`WellSeparated` and its constructors prove Lemma 3 (linear / RC heap
disjointness): the well-separation invariant is preserved by appending
a fresh linear or RC pointer that does not alias any existing pointer
of the opposite kind.  This is the structural heart of the argument
that `assoc-linear` and the new RC association rule do not interfere.

## What is *not* mechanised

The runtime side: a reduction relation on `Config`, the full
association judgement `Γ̊ ⊢ t̂ ∝ ṫ :: T̊`, and the case analysis over
paper §B's 37 pages of association rules to discharge `Theorem 5.3*`.
Estimated 5–7 weeks.  See `axiom theorem_5_3_star` near the bottom of
`PureBorrowLeak.lean` for the precise statement.

## Build

```sh
lake build PureBorrowLeak
```

Tested with Lean 4.16.0.

## License

CC0 / public domain.  Comments / corrections welcome.
