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

### Static side — `PureBorrowLeak.lean`

| Theorem | Status |
| --- | --- |
| `linearOnly_not_leak` | proved |
| `lend_static_iff`, `share_static_iff` | proved |
| `fn_not_leak`, `linFn_not_leak` | proved |
| `Leak.decidable` | proved |
| `WellSeparated.{nil,cons_linear,cons_rc}` (Lemma 3) | proved |

### Runtime side — `PureBorrowLeak/Runtime.lean`

A minimal core calculus (`Tm`, `Heap`, small-step `Step`, RT-closure
`StepStar`) with the four heap operations (`newRef`, `freeRef`,
`newLRc`, `freeLRc`).

| Theorem | Status |
| --- | --- |
| `RLeakInv.{empty,cons_iff,filter}` | proved |
| `step_preserves_rleak` | proved |
| `stepStar_preserves_rleak` | proved |
| **`theorem_5_3_star_b`** — every reachable RC cell has Leak content | **proved** |
| `theorem_5_3_a` — paper Theorem 5.3 (`M = ∅` at normal form) | axiom (inherited) |
| **`theorem_5_3_star`** — combined (a) ∧ (b) | **proved** modulo `theorem_5_3_a` |

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

* Paper Theorem 5.3 (`M = ∅` at normal form) is inherited as an
  axiom.  Discharging it needs the full association judgment
  `Γ̊ ⊢ t̂ ∝ ṫ :: T̊` from paper §B (37 pages of rules).  Estimated
  5–7 weeks.  Until then `theorem_5_3_star` is *conditionally* proved.
* Closure analysis (paper footnote 19, `FnMut`-style).  Our `Leak`
  predicate has no rule for function types, which is the conservative
  position; refining this needs the closure-capture extension that
  paper itself defers.
* The minimal core calculus omits `let`, `λ`, application, and
  congruence reductions under contexts.  Adding them is mechanical
  and does not affect the R-Leak invariant proof — every additional
  rule either touches neither heap or reduces to one of the four
  cases we handle.

## Build

```sh
lake build PureBorrowLeak
```

Tested with Lean 4.16.0.

## License

CC0 / public domain.  Comments / corrections welcome.
