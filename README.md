# PureBorrowLeak

Lean 4 formalisation of part of the leak-freedom argument from the
blog post *Pure Borrow + Leak: chasing footnote 24*
([EN](https://swjeong.netlify.app/notes/2026/04/27/pure-borrow-leak-rc-en.html) /
[KO](https://swjeong.netlify.app/notes/2026/04/27/pure-borrow-leak-rc.html)).

The post extends Pure Borrow (Matsushita & Ishii, PLDI 2026) with a
`class Leak` and an `LRc` reference-counting primitive, conjecturing
that leak freedom (Theorem 5.3) generalises.  This repo discharges:

* the **qualitative classification** — which types are `Leak` /
  `!Leak` and why, including a lifetime-aware refinement `LeakIn`
  that strictly strengthens the paper's conjecture;
* the **runtime-trace half** of the generalised theorem
  (Theorem 5.3$^*$ (b)) — every reachable RC cell has Leak content;
* a **decomposition** of the paper's original Theorem 5.3 (linear
  half) into three small `Discipline` axioms, isolating exactly the
  obligations that the paper's §B association system must discharge.

The full mechanisation of paper Theorem 5.3 itself (the Linear
Haskell type system in Fig. 25–29 plus the association judgment in
Fig. 39–40) is left as separate work.

## What is mechanised

### Static side — `PureBorrowLeak.lean`

| Theorem | Status |
| --- | --- |
| `linearOnly_not_leak` | proved |
| `lend_static_iff`, `share_static_iff` | proved |
| `fn_not_leak`, `linFn_not_leak` | proved |
| `Leak.decidable` | proved |
| `WellSeparated.{nil,cons_linear,cons_rc}` (Lemma 3) | proved |
| `LifetimeLe` (paper §A.1 partial order) | defined |
| `LeakIn α t` — lifetime-aware refinement of `Leak` | defined |
| `Leak.toLeakIn_static` | proved |
| `LeakIn.antitone` (smaller `α` ⇒ more permissive) | proved |
| `linearOnly_not_leakIn` (lifetime-indexed strengthening) | proved |

`linearOnly_not_leak` is the structural backbone: any `LinearOnly`
type is uninhabited under `Leak`.  This justifies the post's blanket
classification of `Linearly`, `Now^α`, `Ref a`, `Mut^α a`, `BO^α a`
as `!Leak` without case-by-case argument.

`WellSeparated` and its constructors prove Lemma 3 (linear / RC heap
disjointness): the well-separation invariant is preserved by
appending a fresh linear or RC pointer that does not alias any
existing pointer of the opposite kind.  This is the structural heart
of the argument that `assoc-linear` and the new RC association rule
do not interfere.

### Runtime side — minimal core, `PureBorrowLeak/Runtime.lean`

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

### Runtime side — extended core, `PureBorrowLeak/Extended.lean`

Adds binders (`var`, `lam`, `app`, `letIn`), the `linearly` block
(`urVal`, `useUr`), `shift` and `subst` (de Bruijn), congruence
reductions under `letIn` and `useUr`, and β-reduction.

| Theorem | Status |
| --- | --- |
| **`step_preserves_rleak`** (extended `Step`) | **proved**: 11 cases (4 heap, 7 non-heap pass-through) |
| `stepStar_preserves_rleak` | proved |
| **`theorem_5_3_star_b_extended`** | **proved** |
| `Discipline e` — abstract Linear Haskell typing obligation | axiom |
| `Discipline.preserved` — one-step preservation | axiom |
| `Discipline.atValue_empty` — discipline ⇒ `M = []` at value | axiom |
| `Discipline.preserved_star` — many-step preservation | proved |
| **`theorem_5_3_a`** | **proved** modulo the 3 `Discipline` axioms |
| **`theorem_5_3_star`** | **proved** modulo the 3 `Discipline` axioms |

The 3 `Discipline.*` axioms together carve out *exactly* what paper
Theorem 5.3 needs to establish via the association system in §B.
The extended file does the reduction-trace bookkeeping; what remains
is to unfold `Discipline` to a concrete typing judgment and
discharge the three obligations from association rules.

## What is not mechanised

* Paper Theorem 5.3 itself (`M = ∅` at normal form).  Discharging it
  needs the multiplicity-tracked Linear Haskell type system
  (paper Fig. 25–29) and the association judgment
  `Γ̊ ⊢ t̂ ∝ ṫ :: T̊` (paper §B, Fig. 39–40 — 37 pages of rules).
  Until then `theorem_5_3_star` is *conditionally* proved.
* Closure analysis (paper footnote 19, `FnMut`-style).  Our `Leak`
  predicate has no rule for function types, which is the
  conservative position; refining this needs the closure-capture
  extension that the paper itself defers.

## Numbers

* `sorry` count: 0.
* Axiom count: 4 — Runtime's `theorem_5_3_a` for the minimal core,
  plus the 3 `Discipline` axioms in Extended.

## Build

```sh
lake build PureBorrowLeak
```

Tested with Lean 4.16.0.

## License

CC0 / public domain.  Comments and corrections welcome.
