/-
Copyright (c) 2026 Yan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Liu
-/

module

public import Cslib.Foundations.Semantics.LTS.HasTau
public meta import Cslib.Foundations.Semantics.LTS.Notation
public import Cslib.Languages.TimedAutomata.Basic

/-! # Dense-time semantics of timed automata

We give a labelled transition system semantics for a `TA`. The transition relation has two kinds:

* **Discrete transition** `(loc, v) ─[act a]→ (loc', v')`: an edge `e` of the automaton fires.
  The source of `e` is `loc`; `e.guard` holds in `v`; after resetting the clocks in `e.resets` we
  obtain `v'`; the invariant of the target location `e.target` holds in `v'`.

* **Time-elapse transition** `(loc, v) ─[delay Δt]→ (loc, v')`: time advances by `Δt`.
  Each clock is incremented by `Δt` (giving `v' = v.elapse Δt`); the location does not change; the
  location invariant must hold *throughout* the elapse — at every intermediate point `t ∈ [0, Δt]`.

Discrete and time-elapse transitions are uniformly captured by a single inductive `Tr` over a sum
label type `Label A := Act a | Delay Δt`. This lets us instantiate `Cslib.Foundations.Semantics.LTS`
directly and reuse the bisimulation infrastructure unchanged in `BehaviouralTheory.lean`.

## Main definitions

- `Label A`: sum of discrete actions and time delays.
- `TA.Tr`: the transition relation, annotated `@[lts ta_lts]` to auto-generate the `LTS` instance
  and the `[μ]⭢ ta_lts` notation.
- `HasTau (Label A)` instance: when `A` itself has a τ action, `Label.act τ` is the τ of the lifted
  label set. Delays are never internal — this matches the bisim discipline used in
  Lean4Corefi #4 (CoreFi↔XTA validity).

-/

@[expose] public section

namespace Cslib.TimedAutomata

universe u v

/-! ## Labels: actions ⊕ delays -/

/-- A label of the TA-LTS is either a discrete action or a time delay. -/
inductive Label (A : Type v) : Type v where
  /-- An external/discrete action. -/
  | act (a : A)
  /-- A time-elapse of `Δt : ℝ≥0`. -/
  | delay (Δt : NNReal)

namespace Label

variable {A : Type v}

/-- Lift a `HasTau` on the action type to the label type. The τ of `Label A` is the discrete
action `τ : A` lifted via `Label.act`; *not* a zero delay. -/
instance [HasTau A] : HasTau (Label A) where
  τ := Label.act (HasTau.τ : A)

end Label

/-! ## Transition relation -/

variable {n : ℕ} {L : Type u} {A : Type v} {ta : TA n L A}

/-- The dense-time transition relation of a TA.

The relation is parameterised over an implicit `ta : TA n L A`, mirroring the CCS pattern where
`defs` is a section variable. The `@[lts ta_lts]` attribute generates a fully-parameterised `LTS`
definition (`ta_lts : ∀ {ta}, LTS (State n L) (Label A)`) and registers `[μ]⭢ ta_lts` notation.

* `discrete`: an edge `e` fires from `(loc, v)`. The edge starts at `loc`, its guard holds in `v`,
  the resulting valuation `v.reset e.resets` satisfies the target location's invariant.
* `elapse`: time advances by `Δt`. The location-invariant of the current location must hold at
  every intermediate point in `[0, Δt]` (including the endpoints).
-/
@[lts ta_lts]
inductive TaTr : State n L → Label A → State n L → Prop where
  | discrete
      {loc : L} {v : ClockVal n} (e : Edge n L A)
      (h_mem : e ∈ ta.edges)
      (h_source : e.source = loc)
      (h_guard : ClockConstraint.sat v e.guard)
      (h_target_inv : ClockConstraint.sat (v.reset e.resets) (ta.inv e.target)) :
      TaTr (loc, v) (Label.act e.action) (e.target, v.reset e.resets)
  | elapse
      {loc : L} {v : ClockVal n} (Δt : NNReal)
      (h_inv : ∀ t : NNReal, t ≤ Δt → ClockConstraint.sat (v.elapse t) (ta.inv loc)) :
      TaTr (loc, v) (Label.delay Δt) (loc, v.elapse Δt)

end Cslib.TimedAutomata
