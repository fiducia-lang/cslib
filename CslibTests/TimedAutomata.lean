/-
Copyright (c) 2026 Yan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Liu
-/

import Cslib.Languages.TimedAutomata.BehaviouralTheory

/-! # Smoke tests for `Cslib.Languages.TimedAutomata`

The canonical Alur–Dill light switch:

* Two locations: `Off`, `On`.
* One clock `x`.
* Edges:
    `Off ─[press]→ On` (guard ⊤; reset `{x}`)
    `On  ─[press]→ Off` (guard `x ≥ 1`; reset `{x}`)
* Invariants:
    `inv(Off) = ⊤`
    `inv(On)  = x ≤ 10`

The TA can flip on at any time, but it must stay on for at least 1 unit and at most 10 units
before it can flip off. We verify a single press transition and a small time elapse against the
location invariant.
-/

namespace CslibTests.TimedAutomata

open Cslib.TimedAutomata

/-- Locations of the light switch. -/
inductive Loc : Type
  | Off
  | On
deriving DecidableEq, Repr

/-- Single action: pressing the switch. The TA has no τ at this level; we use a one-element
action type with a distinguished τ via the `HasTau` instance below, so the bisim infrastructure
type-checks. -/
inductive Act : Type
  | press
  | tauAct
deriving DecidableEq, Repr

instance : Cslib.HasTau Act where
  τ := Act.tauAct

/-- Light-switch TA: one clock `x : Clock 1` (i.e. `Fin 1`); two locations; two edges. -/
def lightSwitch : TA 1 Loc Act where
  initial := Loc.Off
  inv := fun
    | Loc.Off => ClockConstraint.top
    | Loc.On  => [AtomicConstraint.single 0 DiffOp.le 10]
  edges := [
    -- Off ─[press]→ On  (guard ⊤; reset {x})
    { source := Loc.Off
      target := Loc.On
      guard  := ClockConstraint.top
      action := Act.press
      resets := [0]
    },
    -- On ─[press]→ Off  (guard x ≥ 1; reset {x})
    { source := Loc.On
      target := Loc.Off
      guard  := [AtomicConstraint.single 0 DiffOp.ge 1]
      action := Act.press
      resets := [0]
    }
  ]

/-- The initial state is `(Off, x = 0)`. -/
example : lightSwitch.initialState = (Loc.Off, (0 : ClockVal 1)) := rfl

/-- The off→on edge as a named literal. -/
def offToOn : Edge 1 Loc Act :=
  { source := Loc.Off
    target := Loc.On
    guard  := ClockConstraint.top
    action := Act.press
    resets := [0] }

/-- The off→on press fires from `(Off, x=0)` and produces `(On, x=0)` (clock reset). -/
example : TaTr (ta := lightSwitch)
    (Loc.Off, (0 : ClockVal 1))
    (Label.act Act.press)
    (Loc.On,  (0 : ClockVal 1).reset [0]) := by
  refine TaTr.discrete offToOn ?_ rfl ?_ ?_
  · -- offToOn ∈ lightSwitch.edges (it's the head)
    simp [lightSwitch, offToOn]
  · -- guard is `⊤`, trivially satisfied
    exact ClockConstraint.sat_top _
  · -- target invariant `x ≤ 10` holds for `x = 0` after reset
    change ClockConstraint.sat _ (lightSwitch.inv Loc.On)
    intro a ha
    simp only [lightSwitch, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    -- atom is `x ≤ 10` with `x = 0`
    change DiffOp.eval DiffOp.le _ 10
    simp only [DiffOp.eval, ClockVal.reset, ClockVal.resetOne, offToOn]
    norm_num

/-- A 5-unit time-elapse from `(On, x=0)` lands at `(On, x=5)`; the location invariant `x ≤ 10`
holds throughout. -/
example : TaTr (ta := lightSwitch)
    (Loc.On, (0 : ClockVal 1))
    (Label.delay (5 : NNReal))
    (Loc.On, ((0 : ClockVal 1).elapse 5)) := by
  refine TaTr.elapse 5 ?_
  intro t ht
  show ClockConstraint.sat _ (lightSwitch.inv Loc.On)
  intro a ha
  simp only [lightSwitch, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  show DiffOp.eval DiffOp.le _ 10
  simp only [DiffOp.eval, ClockVal.elapse, ClockVal.zero_apply, zero_add]
  -- `(↑t : ℝ) ≤ (10 : ℤ)` since t ≤ 5 ≤ 10
  have h₁ : (t : ℝ) ≤ (5 : ℝ) := by exact_mod_cast ht
  have h₂ : ((10 : ℤ) : ℝ) = (10 : ℝ) := by norm_num
  linarith

end CslibTests.TimedAutomata
