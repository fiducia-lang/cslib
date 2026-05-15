/-
Copyright (c) 2026 Yan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Liu
-/

module

public import Cslib.Init
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Fin.Basic

/-! # Classic Timed Automata (Alur–Dill)

Classic timed automata as introduced in [AlurDill1994]. Following the CSLib design principles, we
mirror the layout of `Cslib.Languages.CCS`: this file contains the syntax, while `Semantics.lean`
gives the dense-time labelled transition system and `BehaviouralTheory.lean` develops the
behavioural theory (timed weak bisimulation).

A *timed automaton* (TA) is a finite-state automaton extended with a finite set of real-valued
clocks. Edges are guarded by *clock constraints* (conjunctions of atoms `x ⊲ c` and `x − y ⊲ c`
with integer constants), labelled with an action, and may *reset* a subset of clocks. Each location
is annotated with an *invariant* — a clock constraint that must hold whenever the automaton resides
in that location, including during time-elapse.

## Main definitions

- `Clock n`: a clock index in a TA with `n` clocks.
- `ClockVal n`: a clock valuation, mapping clocks to non-negative reals.
- `DiffOp`: the comparison operators allowed in atomic clock constraints (`<`, `≤`, `=`, `≥`, `>`).
- `AtomicConstraint n`: an atomic clock constraint of the form `x ⊲ c` (single-clock) or
  `x − y ⊲ c` (difference) with integer constant `c`.
- `ClockConstraint n`: a conjunction of atomic constraints.
- `Guard n` and `Invariant n`: aliases for `ClockConstraint n`.
- `Edge n L A`: an edge between two locations of type `L`, with an action label of type `A`,
  a guard, and a set of clocks to reset.
- `TA n L A`: a timed automaton with `n` clocks, locations from `L`, actions from `A`.

## Design notes

- Clocks are an `n`-indexed family using `Fin n`. This matches `Mathlib`'s `Fin n` and keeps
  clock sets statically bounded, which is enough for the case studies that build on this module
  (`XTA` in `Lean4Corefi`).
- Clock values are non-negative reals (`NNReal = ℝ≥0`).
- Integer constants only in guards (no rationals); this matches Alur–Dill and is what real
  model-checkers like UPPAAL accept.
- The reset set is represented as a `List` rather than a `Finset`; cheaper to construct for small
  TAs and easy to fold into the operational semantics.
- We deliberately keep this file abstract over the action type `A`; the semantics file lifts it
  into an `LTS` with a sum label type (action ∪ delay) so that classic LTS bisimulation applies
  uniformly to both transition kinds.

## References

* [R. Alur and D. L. Dill, *A theory of timed automata*][AlurDill1994]
* [J. Bengtsson and W. Yi, *Timed automata: Semantics, algorithms and tools*][BengtssonYi2003]

-/

@[expose] public section

namespace Cslib.TimedAutomata

universe u v

/-! ## Clocks and clock valuations -/

/-- A clock index in a timed automaton with `n` clocks. -/
abbrev Clock (n : ℕ) := Fin n

/-- A clock valuation: an assignment of non-negative reals to clocks. -/
abbrev ClockVal (n : ℕ) := Clock n → NNReal

namespace ClockVal

variable {n : ℕ}

/-- The all-zero clock valuation. -/
@[scoped grind =]
def zero : ClockVal n := fun _ => 0

instance : Zero (ClockVal n) := ⟨ClockVal.zero⟩

/-- The all-zero valuation maps every clock to `0`. -/
@[simp, scoped grind =]
theorem zero_apply (x : Clock n) : (0 : ClockVal n) x = 0 := rfl

/-- Advance every clock by `Δt`. This is the time-elapse operation. -/
@[scoped grind =]
def elapse (v : ClockVal n) (Δt : NNReal) : ClockVal n := fun x => v x + Δt

/-- Elapsing by zero is the identity. -/
@[simp, scoped grind =]
theorem elapse_zero (v : ClockVal n) : v.elapse 0 = v := by
  funext x
  simp [elapse]

/-- Elapsing is additive in the duration. -/
@[scoped grind =]
theorem elapse_add (v : ClockVal n) (Δt₁ Δt₂ : NNReal) :
    (v.elapse Δt₁).elapse Δt₂ = v.elapse (Δt₁ + Δt₂) := by
  funext x
  simp [elapse, add_assoc]

/-- Reset a single clock to zero. -/
@[scoped grind =]
def resetOne (v : ClockVal n) (x : Clock n) : ClockVal n :=
  fun y => if y = x then 0 else v y

/-- Reset every clock in a list to zero. Other clocks keep their value. -/
@[scoped grind =]
def reset (v : ClockVal n) : List (Clock n) → ClockVal n
  | [] => v
  | x :: xs => (v.reset xs).resetOne x

@[simp, scoped grind =]
theorem reset_nil (v : ClockVal n) : v.reset [] = v := rfl

/-- A clock that appears in the reset list is mapped to `0`. -/
theorem reset_mem (v : ClockVal n) (R : List (Clock n)) (x : Clock n) (h : x ∈ R) :
    v.reset R x = 0 := by
  induction R with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head => simp [reset, resetOne]
    | tail _ h' =>
      simp only [reset, resetOne]
      split
      · rfl
      · exact ih h'

/-- A clock that does not appear in the reset list keeps its value. -/
theorem reset_not_mem (v : ClockVal n) (R : List (Clock n)) (x : Clock n) (h : x ∉ R) :
    v.reset R x = v x := by
  induction R with
  | nil => rfl
  | cons y ys ih =>
    simp only [reset, resetOne]
    have hxy : x ≠ y := fun h' => h (h' ▸ List.mem_cons_self)
    have hxys : x ∉ ys := fun h' => h (List.mem_cons_of_mem _ h')
    simp [hxy, ih hxys]

end ClockVal

/-! ## Clock constraints -/

/-- Comparison operator in an atomic clock constraint. -/
inductive DiffOp : Type where
  | lt
  | le
  | eq
  | ge
  | gt
deriving DecidableEq, Repr

namespace DiffOp

/-- Evaluate a comparison operator on non-negative reals against an integer constant.

The integer `c` is interpreted via `Int.cast` into `ℝ` and compared with `v` (coerced from
`NNReal`). This is the standard Alur–Dill convention. -/
@[scoped grind =]
def eval (op : DiffOp) (v : NNReal) (c : ℤ) : Prop :=
  match op with
  | lt => (v : ℝ) < c
  | le => (v : ℝ) ≤ c
  | eq => (v : ℝ) = c
  | ge => (v : ℝ) ≥ c
  | gt => (v : ℝ) > c

-- Note: `eval` is not constructively decidable because it ranges over `ℝ`. Downstream code that
-- needs to decide a constraint at run-time (e.g. a model-checker or simulator) should work with
-- a more restricted clock value type (rationals, fixed-point ints) and re-derive `Decidable`
-- instances there. The classical semantics is sufficient for the bisimulation proofs Lean4Corefi
-- relies on.

end DiffOp

/-- An atomic clock constraint.

`single x op c` represents `x ⊲ c`; `diff x y op c` represents `x − y ⊲ c`.

The difference form takes a *signed* real value `(v x : ℝ) − (v y : ℝ)`, so all five operators
make sense (otherwise `lt 0` on `NNReal` would be vacuous). -/
inductive AtomicConstraint (n : ℕ) : Type where
  | single (x : Clock n) (op : DiffOp) (c : ℤ)
  | diff (x y : Clock n) (op : DiffOp) (c : ℤ)
deriving DecidableEq

namespace AtomicConstraint

variable {n : ℕ}

/-- Semantics of an atomic constraint under a clock valuation. -/
@[scoped grind]
def sat (v : ClockVal n) : AtomicConstraint n → Prop
  | single x op c => op.eval (v x) c
  | diff x y op c =>
    match op with
    | DiffOp.lt => ((v x : ℝ) - (v y : ℝ)) < c
    | DiffOp.le => ((v x : ℝ) - (v y : ℝ)) ≤ c
    | DiffOp.eq => ((v x : ℝ) - (v y : ℝ)) = c
    | DiffOp.ge => ((v x : ℝ) - (v y : ℝ)) ≥ c
    | DiffOp.gt => ((v x : ℝ) - (v y : ℝ)) > c

end AtomicConstraint

/-- A clock constraint is a finite conjunction of atomic constraints. We represent the conjunction
as a list of atoms; the empty list is the trivially-true constraint. -/
abbrev ClockConstraint (n : ℕ) := List (AtomicConstraint n)

namespace ClockConstraint

variable {n : ℕ}

/-- A valuation satisfies a clock constraint if it satisfies every atom. -/
@[scoped grind]
def sat (v : ClockVal n) (g : ClockConstraint n) : Prop :=
  ∀ a ∈ g, a.sat v

/-- The trivially-true constraint: empty conjunction. Satisfied by every valuation. -/
def top : ClockConstraint n := []

/-- Conjunction of two clock constraints. We define this in terms of `List.append` so it composes
with the underlying list operations, but expose it as a named constructor for the public API. -/
def and (g₁ g₂ : ClockConstraint n) : ClockConstraint n := g₁ ++ g₂

/-- The trivially-true constraint, satisfied by every valuation. -/
@[simp, scoped grind]
theorem sat_nil (v : ClockVal n) : ClockConstraint.sat v [] := by
  intro _ h; cases h

/-- Every valuation satisfies `top`. -/
@[simp, scoped grind]
theorem sat_top (v : ClockVal n) : ClockConstraint.sat v top := by
  unfold top; exact sat_nil v

/-- Conjunction: a valuation satisfies `g₁ ++ g₂` iff it satisfies both. -/
@[scoped grind]
theorem sat_append (v : ClockVal n) (g₁ g₂ : ClockConstraint n) :
    ClockConstraint.sat v (g₁ ++ g₂) ↔ ClockConstraint.sat v g₁ ∧ ClockConstraint.sat v g₂ := by
  simp only [sat, List.mem_append]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · intro ⟨h₁, h₂⟩ a ha
    cases ha with
    | inl h => exact h₁ a h
    | inr h => exact h₂ a h

/-- Composition lemma for `and`: this is the form downstream code (e.g. XTA elaboration) usually
needs. -/
@[simp, scoped grind]
theorem sat_and (v : ClockVal n) (g₁ g₂ : ClockConstraint n) :
    ClockConstraint.sat v (g₁.and g₂) ↔ ClockConstraint.sat v g₁ ∧ ClockConstraint.sat v g₂ :=
  sat_append v g₁ g₂

end ClockConstraint

/-- A guard on an edge: a clock constraint that must hold for the edge to fire. -/
abbrev Guard (n : ℕ) := ClockConstraint n

/-- A location invariant: a clock constraint that must hold whenever the automaton resides in the
location, including during time-elapse. -/
abbrev Invariant (n : ℕ) := ClockConstraint n

/-! ## Edges and timed automata -/

/-- An edge of a timed automaton.

* `source` and `target` are locations.
* `guard` must hold in the current valuation for the edge to fire.
* `action` labels the edge.
* `resets` is the list of clocks reset to `0` when the edge fires. -/
structure Edge (n : ℕ) (L : Type u) (A : Type v) where
  /-- Source location. -/
  source : L
  /-- Target location. -/
  target : L
  /-- Guard: must hold to fire. -/
  guard : Guard n
  /-- Action label. -/
  action : A
  /-- Clocks reset on firing. -/
  resets : List (Clock n)

/-- A timed automaton.

* `n` is the number of clocks.
* `L` is the type of locations; we assume nothing about `L` beyond decidable equality if needed
  later. The `initial` location is the starting location.
* `inv` assigns an `Invariant` to each location; the automaton can only reside in `loc` while
  `inv loc` holds in the current valuation.
* `edges` is the (finite) list of edges. -/
structure TA (n : ℕ) (L : Type u) (A : Type v) where
  /-- The initial location. -/
  initial : L
  /-- Location invariants. -/
  inv : L → Invariant n
  /-- The edges of the TA. -/
  edges : List (Edge n L A)

/-- A *state* of a TA is a pair `(location, clock valuation)`. We keep this at the
`Cslib.TimedAutomata` level (rather than under `TA`) so it can be referenced unqualified from
companion files (`Semantics.lean`, `BehaviouralTheory.lean`) without re-entering the `TA`
namespace. -/
abbrev State (n : ℕ) (L : Type u) := L × ClockVal n

namespace TA

variable {n : ℕ} {L : Type u} {A : Type v}

/-- The initial state of a TA: the initial location paired with the all-zero clock valuation. -/
@[scoped grind =]
def initialState (ta : TA n L A) : State n L := (ta.initial, 0)

/-- A clock valuation `v` satisfies the invariant of location `loc` iff `inv loc` holds in `v`. -/
@[scoped grind =]
def InvariantHolds (ta : TA n L A) (loc : L) (v : ClockVal n) : Prop :=
  ClockConstraint.sat v (ta.inv loc)

end TA

end Cslib.TimedAutomata
