/-
Copyright (c) 2026 Yan Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Liu
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Languages.TimedAutomata.Semantics

/-! # Behavioural theory of timed automata

We define **timed (weak) bisimulation** for timed automata as the instance of cslib's
`Bisimulation` / `WeakBisimulation` on the TA's LTS, where the label set already includes both
discrete actions (`Label.act a`) and time delays (`Label.delay Δt`). This means timed bisimulation
is just LTS bisimulation under the lifted label type — no extra infrastructure required.

Weak bisimulation requires a `HasTau` instance on the label type. We get this from
`HasTau (Label A)` (defined in `Semantics.lean`), which lifts `HasTau A` to make `Label.act τ` the
internal label and leaves *every* delay observable. This is the bisim discipline used by
Lean4Corefi#4's CoreFi↔XTA validity proof.

## Main definitions

- `TimedBisimilarity ta₁ ta₂`: strong timed bisimilarity (`Bisimilarity` on the TA LTSs).
- `TimedWeakBisimilarity ta₁ ta₂`: weak timed bisimilarity (`WeakBisimilarity` on the TA LTSs).

## Main results

- `TimedBisimilarity.eqv`, `TimedWeakBisimilarity.eqv`: timed (weak) bisimilarity is an equivalence
  on the states of a single TA — both follow immediately from the cslib core.
- `TimedBisimilarity.le_weak`: every strong bisimulation is a weak bisimulation.

Anything more substantial (congruence under TA composition, decidability for finite-state TA,
etc.) is deliberately out of scope for the initial scaffold and can be added when a concrete proof
in Lean4Corefi needs it.
-/

@[expose] public section

namespace Cslib.TimedAutomata

universe u v

variable
  {n₁ n₂ : ℕ}
  {L₁ : Type u} {L₂ : Type u}
  {A : Type v}
  {ta₁ : TA n₁ L₁ A} {ta₂ : TA n₂ L₂ A}

open Cslib.LTS

/-! ## Strong timed bisimilarity -/

/-- A relation `r` is a *strong timed bisimulation* between `ta₁` and `ta₂` if it is a
`Cslib.LTS.IsBisimulation` for the corresponding TA LTSs.

The label type already mixes discrete actions and delays uniformly, so this single definition
captures the textbook notion of timed bisimulation without a separate clause for time-elapse. -/
abbrev IsTimedBisimulation (ta₁ : TA n₁ L₁ A) (ta₂ : TA n₂ L₂ A)
    (r : State n₁ L₁ → State n₂ L₂ → Prop) : Prop :=
  IsBisimulation (ta_lts (ta := ta₁)) (ta_lts (ta := ta₂)) r

/-- Two TA states are *timed bisimilar* if some timed bisimulation relates them. -/
abbrev TimedBisimilarity (ta₁ : TA n₁ L₁ A) (ta₂ : TA n₂ L₂ A) :
    State n₁ L₁ → State n₂ L₂ → Prop :=
  Bisimilarity (ta_lts (ta := ta₁)) (ta_lts (ta := ta₂))

/-- Homogeneous timed bisimilarity (same TA on both sides). -/
abbrev HomTimedBisimilarity (ta : TA n L A) := TimedBisimilarity ta ta

/-- Homogeneous timed bisimilarity is reflexive. -/
theorem HomTimedBisimilarity.refl (ta : TA n L A) (s : State n L) :
    HomTimedBisimilarity ta s s := by
  refine ⟨Eq, rfl, ?_⟩
  intro x y hxy μ
  cases hxy
  refine ⟨fun x' htr => ⟨x', htr, rfl⟩, fun x' htr => ⟨x', htr, rfl⟩⟩

/-- Timed bisimilarity is symmetric. The proof goes through `IsBisimulation.inv`, which gives the
heterogeneous version `Bisimilarity.symm` does not. -/
theorem TimedBisimilarity.symm {s₁ : State n₁ L₁} {s₂ : State n₂ L₂}
    (h : TimedBisimilarity ta₁ ta₂ s₁ s₂) : TimedBisimilarity ta₂ ta₁ s₂ s₁ := by
  obtain ⟨r, hr, hbisim⟩ := h
  exact ⟨flip r, hr, IsBisimulation.inv hbisim⟩

/-- Timed bisimilarity is transitive. -/
theorem TimedBisimilarity.trans
    {n₃ : ℕ} {L₃ : Type u} {ta₃ : TA n₃ L₃ A}
    {s₁ : State n₁ L₁} {s₂ : State n₂ L₂} {s₃ : State n₃ L₃}
    (h₁ : TimedBisimilarity ta₁ ta₂ s₁ s₂)
    (h₂ : TimedBisimilarity ta₂ ta₃ s₂ s₃) :
    TimedBisimilarity ta₁ ta₃ s₁ s₃ := by
  obtain ⟨r₁, hr₁, hb₁⟩ := h₁
  obtain ⟨r₂, hr₂, hb₂⟩ := h₂
  exact ⟨Relation.Comp r₁ r₂, ⟨s₂, hr₁, hr₂⟩, IsBisimulation.comp hb₁ hb₂⟩

/-- Homogeneous timed bisimilarity is an equivalence relation. -/
theorem HomTimedBisimilarity.eqv {ta : TA n L A} :
    Equivalence (HomTimedBisimilarity ta) where
  refl := HomTimedBisimilarity.refl ta
  symm := TimedBisimilarity.symm
  trans := TimedBisimilarity.trans

/-! ## Weak timed bisimilarity (the one Lean4Corefi#4 actually needs) -/

/-- A relation `r` is a *weak timed bisimulation* between `ta₁` and `ta₂` if it is a
`Cslib.LTS.IsWeakBisimulation` for the corresponding TA LTSs.

The `HasTau (Label A)` instance treats `Label.act (τ : A)` as internal and every `Label.delay Δt`
as observable — so weak bisimulation only absorbs internal discrete steps, *never* delays. This is
the discipline `Lean4Corefi#4` uses for the CoreFi↔XTA translation-validity proof. -/
abbrev IsTimedWeakBisimulation [HasTau A] (ta₁ : TA n₁ L₁ A) (ta₂ : TA n₂ L₂ A)
    (r : State n₁ L₁ → State n₂ L₂ → Prop) : Prop :=
  IsWeakBisimulation (ta_lts (ta := ta₁)) (ta_lts (ta := ta₂)) r

/-- Two TA states are *weakly timed bisimilar* if some weak timed bisimulation relates them. -/
abbrev TimedWeakBisimilarity [HasTau A] (ta₁ : TA n₁ L₁ A) (ta₂ : TA n₂ L₂ A) :
    State n₁ L₁ → State n₂ L₂ → Prop :=
  WeakBisimilarity (ta_lts (ta := ta₁)) (ta_lts (ta := ta₂))

/-- Homogeneous weak timed bisimilarity (same TA on both sides). -/
abbrev HomTimedWeakBisimilarity [HasTau A] (ta : TA n L A) := TimedWeakBisimilarity ta ta

/-- Weak timed bisimilarity is symmetric. -/
theorem TimedWeakBisimilarity.symm
    [HasTau A] {s₁ : State n₁ L₁} {s₂ : State n₂ L₂}
    (h : TimedWeakBisimilarity ta₁ ta₂ s₁ s₂) :
    TimedWeakBisimilarity ta₂ ta₁ s₂ s₁ := by
  obtain ⟨r, hr, hbisim⟩ := h
  exact ⟨flip r, hr, IsWeakBisimulation.inv r hbisim⟩

/-- Weak timed bisimilarity is transitive. -/
theorem TimedWeakBisimilarity.trans
    [HasTau A]
    {n₃ : ℕ} {L₃ : Type u} {ta₃ : TA n₃ L₃ A}
    {s₁ : State n₁ L₁} {s₂ : State n₂ L₂} {s₃ : State n₃ L₃}
    (h₁ : TimedWeakBisimilarity ta₁ ta₂ s₁ s₂)
    (h₂ : TimedWeakBisimilarity ta₂ ta₃ s₂ s₃) :
    TimedWeakBisimilarity ta₁ ta₃ s₁ s₃ := by
  obtain ⟨r₁, hr₁, hb₁⟩ := h₁
  obtain ⟨r₂, hr₂, hb₂⟩ := h₂
  exact ⟨Relation.Comp r₁ r₂, ⟨s₂, hr₁, hr₂⟩, IsWeakBisimulation.comp hb₁ hb₂⟩

/-! ## Strong implies weak

This is a one-line wrapper around the cslib core fact that a `IsBisimulation` is a
`IsWeakBisimulation` (i.e., bisimilarity on the original LTS implies bisimilarity on its
τ-saturation). It's worth naming explicitly because the CoreFi↔XTA proof in Lean4Corefi#4 takes
this direction by default: prove a strong bisim where possible (strictly more information), and
weaken to the weak statement only when τ-absorption is genuinely needed. -/
theorem IsTimedBisimulation.toWeak
    [HasTau A]
    {r : State n₁ L₁ → State n₂ L₂ → Prop}
    (h : IsTimedBisimulation ta₁ ta₂ r) :
    IsTimedWeakBisimulation ta₁ ta₂ r := by
  -- A bisimulation on `lts` is one on `lts.saturate` because every direct transition is a
  -- saturated transition (`STr.single`), and the converse direction follows symmetrically.
  intro s₁ s₂ hr μ
  refine ⟨?_, ?_⟩
  · intro s₁' hstr
    cases hstr with
    | refl =>
      exact ⟨s₂, .refl, hr⟩
    | tr hτ1 htr hτ2 =>
      -- Walk the saturated transition: chase τ-prefix, the matching step, then τ-suffix.
      -- For a *strong* bisim each individual step is matched by a strong step; we lift those
      -- matches into the saturated form via `STr.single` and `STr.tr`.
      have key : ∀ {s s' s''} {μ}, r s s' → (ta_lts (ta := ta₁)).Tr s μ s'' →
          ∃ s''', (ta_lts (ta := ta₂)).Tr s' μ s''' ∧ r s'' s''' := by
        intro s s' s'' μ' hr' htr'
        exact (h hr' μ').1 _ htr'
      -- τ-prefix on side 1 ↦ corresponding τ-prefix on side 2 (state walks together).
      have lifted_τ_fst : ∀ {a b c}, r a b → (ta_lts (ta := ta₁)).τSTr a c →
          ∃ d, (ta_lts (ta := ta₂)).τSTr b d ∧ r c d := by
        intro a b c hr' hτ
        induction hτ with
        | refl => exact ⟨b, .refl, hr'⟩
        | tail _ hstep ih =>
          obtain ⟨bmid, hτmid, hrmid⟩ := ih
          obtain ⟨bnext, hstepb, hrnext⟩ := key hrmid hstep
          exact ⟨bnext, hτmid.tail hstepb, hrnext⟩
      obtain ⟨smid₂, hτmid₂, hrmid⟩ := lifted_τ_fst hr hτ1
      obtain ⟨send₂, hstepmid, hrend⟩ := key hrmid htr
      obtain ⟨s₂', hτend₂, hr₂'⟩ := lifted_τ_fst hrend hτ2
      exact ⟨s₂', .tr hτmid₂ hstepmid hτend₂, hr₂'⟩
  · intro s₂' hstr
    cases hstr with
    | refl =>
      exact ⟨s₁, .refl, hr⟩
    | tr hτ1 htr hτ2 =>
      have key : ∀ {s s' s''} {μ}, r s s' → (ta_lts (ta := ta₂)).Tr s' μ s'' →
          ∃ s''', (ta_lts (ta := ta₁)).Tr s μ s''' ∧ r s''' s'' := by
        intro s s' s'' μ' hr' htr'
        exact (h hr' μ').2 _ htr'
      have lifted_τ_snd : ∀ {a b c}, r a b → (ta_lts (ta := ta₂)).τSTr b c →
          ∃ d, (ta_lts (ta := ta₁)).τSTr a d ∧ r d c := by
        intro a b c hr' hτ
        induction hτ with
        | refl => exact ⟨a, .refl, hr'⟩
        | tail _ hstep ih =>
          obtain ⟨amid, hτmid, hrmid⟩ := ih
          obtain ⟨anext, hstepa, hrnext⟩ := key hrmid hstep
          exact ⟨anext, hτmid.tail hstepa, hrnext⟩
      obtain ⟨smid₁, hτmid₁, hrmid⟩ := lifted_τ_snd hr hτ1
      obtain ⟨send₁, hstepmid, hrend⟩ := key hrmid htr
      obtain ⟨s₁', hτend₁, hr₁'⟩ := lifted_τ_snd hrend hτ2
      exact ⟨s₁', .tr hτmid₁ hstepmid hτend₁, hr₁'⟩

/-- Strong timed bisimilarity is included in weak timed bisimilarity. -/
theorem TimedBisimilarity.le_weak
    [HasTau A] {s₁ : State n₁ L₁} {s₂ : State n₂ L₂}
    (h : TimedBisimilarity ta₁ ta₂ s₁ s₂) :
    TimedWeakBisimilarity ta₁ ta₂ s₁ s₂ := by
  unfold TimedBisimilarity TimedWeakBisimilarity Bisimilarity WeakBisimilarity at *
  obtain ⟨r, hr, hbisim⟩ := h
  exact ⟨r, hr, IsTimedBisimulation.toWeak hbisim⟩

end Cslib.TimedAutomata
