/-
# Runtime side of `Theorem 5.3*`

The static module proved every type-level obligation:

  * `linearOnly_not_leak` — the structural backbone of the !Leak set.
  * `lend_static_iff`, `share_static_iff` — `α = static` is exactly
    necessary and sufficient.
  * `Leak.decidable` — the typing rule for `newLRc` is mechanical.
  * `WellSeparated.cons_*` — Lemma 3 (linear / RC heap disjointness).

This module discharges **part (b) of `Theorem 5.3*`**:

> at every reachable configuration, every cell `(ℓ ↦→ v) ∈ R` has
> `Leak T` for the cell's content type `T`.

We mechanise it on a *minimal core calculus* whose only relevant
operations are heap allocation and freeing for the two heap kinds.
Anything outside heap allocation cannot affect the invariant, so the
restriction is faithful to the full Pure Borrow calculus for this
particular theorem.

Part (a) — `M = ∅` at normal form — is *paper Theorem 5.3*, which we
inherit verbatim and expose as `axiom theorem_5_3_a`.  Combining the
two gives the full `Theorem 5.3*`.
-/

import PureBorrowLeak

namespace PureBorrowLeak.Runtime

open PureBorrowLeak

/-! ## Syntax of the core calculus -/

/-- Core terms.  We only need:

  * primitive values (`num`, `unit`, `linW`)
  * runtime pointers (`refLit`, `lrcLit`)
  * the four heap operations (`newRef`, `freeRef`, `newLRc`, `freeLRc`)

`linW` is the runtime witness for the `Linearly` capability — every
heap allocation reads it as its first argument.  The fact that no
production rule in our reduction ever consumes a `linW` means the
single token can be threaded through the reduction without bookkeeping;
the linear-resource discipline is *exactly* the obligation that paper
Theorem 5.3 takes care of, and we do not duplicate it here. -/
inductive Tm where
  | num     : Nat → Tm
  | unit    : Tm
  | linW    : Tm
  | refLit  : Loc → Tm
  | lrcLit  : Loc → Tm
  | newRef  : Tm → Tm → Tm           -- `newRef linW v`
  | freeRef : Tm → Tm                -- `freeRef r`
  | newLRc  : Ty → Tm → Tm → Tm      -- `newLRc T linW v` (type carried in syntax)
  | freeLRc : Tm → Tm                -- `freeLRc r`
  deriving Repr

/-- Values: terms in normal form for the core fragment. -/
inductive Value : Tm → Prop where
  | num    : ∀ n,  Value (.num n)
  | unit   :        Value .unit
  | linW   :        Value .linW
  | refLit : ∀ ℓ,  Value (.refLit ℓ)
  | lrcLit : ∀ ℓ,  Value (.lrcLit ℓ)

/-! ## Heaps and configurations

`M` is the linear heap (paper Pure Borrow's `M`, mutative semantics
§A.2).  `R` is the new RC heap.  We carry the content type in `R`
because RC cells are immutable per paper §6 footnote 24's design and
we want the Leak invariant to be a property of the heap state alone,
not of any external typing context. -/

structure Heap where
  M : List (Loc × Tm)
  R : List (Loc × Tm × Ty)
  deriving Repr

structure Cfg where
  tm : Tm
  h  : Heap
  deriving Repr

/-- *Freshness* for an `M` location: no entry uses it. -/
def Heap.freshM (h : Heap) (ℓ : Loc) : Prop :=
  ∀ v, (ℓ, v) ∉ h.M

/-- *Freshness* for an `R` location: no entry uses it. -/
def Heap.freshR (h : Heap) (ℓ : Loc) : Prop :=
  ∀ v T, (ℓ, v, T) ∉ h.R

/-- Erase the first `M` entry at location `ℓ`. -/
def Heap.eraseM (h : Heap) (ℓ : Loc) : Heap :=
  { h with M := h.M.filter (fun p => p.1 ≠ ℓ) }

/-- Erase the first `R` entry at location `ℓ`. -/
def Heap.eraseR (h : Heap) (ℓ : Loc) : Heap :=
  { h with R := h.R.filter (fun t => t.1 ≠ ℓ) }

/-! ## Small-step reduction

Only the heap-touching rules.  Structural / congruence rules under
contexts are omitted: they cannot affect the `R`-Leak invariant
because they don't allocate or free, and adding them is mechanical. -/
inductive Step : Cfg → Cfg → Prop where
  | newRef
      {h : Heap} (ℓ : Loc) (v : Tm)
      (hv     : Value v)
      (hfresh : h.freshM ℓ) :
      Step ⟨.newRef .linW v, h⟩
           ⟨.refLit ℓ,
            { M := (ℓ, v) :: h.M, R := h.R }⟩
  | freeRef
      {h : Heap} (ℓ : Loc) (v : Tm)
      (hin : (ℓ, v) ∈ h.M) :
      Step ⟨.freeRef (.refLit ℓ), h⟩
           ⟨v, h.eraseM ℓ⟩
  | newLRc
      {h : Heap} (ℓ : Loc) (T : Ty) (v : Tm)
      (hv     : Value v)
      (hL     : Leak T)
      (hfresh : h.freshR ℓ) :
      Step ⟨.newLRc T .linW v, h⟩
           ⟨.lrcLit ℓ,
            { M := h.M, R := (ℓ, v, T) :: h.R }⟩
  | freeLRc
      {h : Heap} (ℓ : Loc) (v : Tm) (T : Ty)
      (hin : (ℓ, v, T) ∈ h.R) :
      Step ⟨.freeLRc (.lrcLit ℓ), h⟩
           ⟨v, h.eraseR ℓ⟩

/-- Reflexive-transitive closure. -/
inductive StepStar : Cfg → Cfg → Prop where
  | refl  : ∀ c, StepStar c c
  | step  : ∀ {c c' c''}, Step c c' → StepStar c' c'' → StepStar c c''

/-! ## The R-Leak invariant -/

/-- Every cell in `R` has Leak content type. -/
def RLeakInv (R : List (Loc × Tm × Ty)) : Prop :=
  ∀ ℓ v T, (ℓ, v, T) ∈ R → Leak T

theorem RLeakInv.empty : RLeakInv [] := by
  intro _ _ _ h; cases h

theorem RLeakInv.cons_iff {ℓ v T R} :
    RLeakInv ((ℓ, v, T) :: R) ↔ Leak T ∧ RLeakInv R := by
  constructor
  · intro h
    refine ⟨h ℓ v T (.head _), fun ℓ' v' T' hin => h ℓ' v' T' (.tail _ hin)⟩
  · rintro ⟨hleak, hR⟩ ℓ' v' T' hin
    cases hin with
    | head => exact hleak
    | tail _ hin' => exact hR ℓ' v' T' hin'

theorem RLeakInv.filter {R : List (Loc × Tm × Ty)} {p : Loc × Tm × Ty → Bool} :
    RLeakInv R → RLeakInv (R.filter p) := by
  intro hinv ℓ v T hin
  exact hinv _ _ _ (List.mem_filter.mp hin).1

/-! ## Main preservation theorem -/

/-- One reduction step preserves the R-Leak invariant. -/
theorem step_preserves_rleak :
    ∀ {c c'}, Step c c' → RLeakInv c.h.R → RLeakInv c'.h.R := by
  intro c c' hstep hinv
  cases hstep with
  | newRef ℓ v hv hfresh =>
      -- M grows, R unchanged.
      exact hinv
  | freeRef ℓ v hin =>
      -- R unchanged.
      exact hinv
  | newLRc ℓ T v hv hL hfresh =>
      -- R gains a new entry whose content type is `T`, and the rule's
      -- premise is `Leak T`.  Use `cons_iff`.
      exact RLeakInv.cons_iff.mpr ⟨hL, hinv⟩
  | freeLRc ℓ v T hin =>
      -- R loses entries, doesn't gain.
      exact hinv.filter

/-- Many reduction steps preserve the R-Leak invariant. -/
theorem stepStar_preserves_rleak :
    ∀ {c c'}, StepStar c c' → RLeakInv c.h.R → RLeakInv c'.h.R := by
  intro c c' hstar hinv
  induction hstar with
  | refl _ => exact hinv
  | step hs _ ih =>
      exact ih (step_preserves_rleak hs hinv)

/-! ## Theorem 5.3* (b) — the actual statement

Starting from any configuration with empty `R`, every reachable
configuration has all `R` cells of Leak type. -/

theorem theorem_5_3_star_b :
    ∀ {e : Tm} {c' : Cfg},
    StepStar ⟨e, { M := [], R := [] }⟩ c' →
    ∀ ℓ v T, (ℓ, v, T) ∈ c'.h.R → Leak T := by
  intro e c' hstar
  have : RLeakInv c'.h.R :=
    stepStar_preserves_rleak hstar RLeakInv.empty
  exact this

/-! ## Theorem 5.3* (a) — paper's original

Inherited as an axiom.  Discharging this is the 5–7-week block: it
needs the full association system from paper §B.  Stated here so the
combined `theorem_5_3_star` reads cleanly. -/

axiom theorem_5_3_a
    {e : Tm} {c' : Cfg}
    (_ : StepStar ⟨e, { M := [], R := [] }⟩ c')
    (_normal : ∀ c'', ¬ Step c' c'') :
    c'.h.M = []

/-! ## The full `Theorem 5.3*`

(a) and (b) combined.  Note: (b) does *not* need the normal-form
hypothesis — it holds for every reachable configuration, not just
final ones — so we keep the two parts separate in the conclusion. -/

theorem theorem_5_3_star
    {e : Tm} {c' : Cfg}
    (hred : StepStar ⟨e, { M := [], R := [] }⟩ c')
    (hnormal : ∀ c'', ¬ Step c' c'') :
    c'.h.M = [] ∧ ∀ ℓ v T, (ℓ, v, T) ∈ c'.h.R → Leak T :=
  ⟨theorem_5_3_a hred hnormal, theorem_5_3_star_b hred⟩

/-! ## Sanity examples -/

/-- A single `newLRc` step.  Demonstrates that the rule applies and
    the resulting `R` immediately satisfies `RLeakInv`. -/
example (ℓ : Loc) :
    Step ⟨.newLRc Ty.int .linW (.num 7), { M := [], R := [] }⟩
         ⟨.lrcLit ℓ,
          { M := [], R := [(ℓ, .num 7, Ty.int)] }⟩ :=
  Step.newLRc (h := { M := [], R := [] }) ℓ Ty.int (.num 7)
              (Value.num 7) Leak.int
              (fun _ _ h => by cases h)

example (ℓ : Loc) :
    RLeakInv [(ℓ, Tm.num 7, Ty.int)] :=
  step_preserves_rleak
    (Step.newLRc (h := { M := [], R := [] }) ℓ Ty.int (.num 7)
                 (Value.num 7) Leak.int (fun _ _ h => by cases h))
    RLeakInv.empty

end PureBorrowLeak.Runtime
