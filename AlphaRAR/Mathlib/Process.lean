/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Indistinguishable processes

A process defined through conditional expectations is only ever pinned down up to null sets, so
every uniqueness statement about one is a statement up to `Indistinguishable`: almost surely, the
two processes agree at every time.

This is the relation the `@[characterization uniqueness]` theorems of such processes are stated
up to — `AlphaRAR.predQuadVar` and `AlphaRAR.assignMart` among them — which is why it lives in a
file of its own rather than beside any one of them.
-/

@[expose] public section

open MeasureTheory

namespace AlphaRAR

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ι E : Type*} {A B : ι → Ω → E}

/-- Two processes are **indistinguishable**: almost surely they agree at every time — one null set
for the whole path, not one per time.

Over a countable index this is no stronger than agreeing a.e. at each fixed time
(`Indistinguishable.of_forall_ae_eq`), but it is the statement about paths, which is what a
uniqueness claim for a *process* should say.

A structure rather than an abbreviation because a characterization reads the "up to what" off the
head of a uniqueness statement, and an unfolded `∀ᵐ`/`∀` has none. -/
structure Indistinguishable (μ : Measure Ω) (A B : ι → Ω → E) : Prop where
  /-- Almost surely, the two processes agree at every time. -/
  ae_forall_eq : ∀ᵐ ω ∂μ, ∀ i, A i ω = B i ω

/-- Indistinguishable processes agree a.e. at each fixed time. -/
lemma Indistinguishable.ae_eq (h : Indistinguishable μ A B) (i : ι) : A i =ᵐ[μ] B i := by
  filter_upwards [h.ae_forall_eq] with ω hω using hω i

/-- Over a countable index, agreeing a.e. at each fixed time upgrades to indistinguishability: the
exceptional sets are countably many, so their union is still null. -/
lemma Indistinguishable.of_forall_ae_eq [Countable ι] (h : ∀ i, A i =ᵐ[μ] B i) :
    Indistinguishable μ A B :=
  ⟨ae_all_iff.mpr h⟩

lemma Indistinguishable.refl (μ : Measure Ω) (A : ι → Ω → E) : Indistinguishable μ A A :=
  ⟨.of_forall fun _ _ ↦ rfl⟩

lemma Indistinguishable.symm (h : Indistinguishable μ A B) : Indistinguishable μ B A := by
  refine ⟨?_⟩
  filter_upwards [h.ae_forall_eq] with ω hω i using (hω i).symm

lemma Indistinguishable.trans {C : ι → Ω → E} (h : Indistinguishable μ A B)
    (h' : Indistinguishable μ B C) : Indistinguishable μ A C := by
  refine ⟨?_⟩
  filter_upwards [h.ae_forall_eq, h'.ae_forall_eq] with ω hω hω' i using (hω i).trans (hω' i)

end AlphaRAR
