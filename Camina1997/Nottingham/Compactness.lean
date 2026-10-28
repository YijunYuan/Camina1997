/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Parameters
public import Camina1997.Nottingham.Topology
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions

/-!
# Compactness of the Nottingham group

The free coefficients of the parameter identify the congruence topology with
the product topology on a countable product of copies of the finite prime field.
Consequently the Nottingham group is compact.

Reference: Camina (1997), p. 102, the congruence topology and pro-`p` assertion.
-/

@[expose] public section

namespace Camina1997.Nottingham

open PowerSeries Filter Set
open scoped Topology

variable {p : ℕ} [Fact p.Prime]

/-- A congruence coset is exactly a cylinder fixing the initial free coefficients. -/
theorem mem_congruence_coset_iff (g h : Nottingham p) (n : ℕ) :
    h ∈ (fun u ↦ g * u) '' (congruenceSubgroup (p := p) n : Set (Nottingham p)) ↔
      ∀ i < n - 1, coefficientEquiv h i = coefficientEquiv g i := by
  change _ ↔ ∀ i < n - 1, coeff (i + 2) (h X) = coeff (i + 2) (g X)
  rw [← inv_mul_mem_congruenceSubgroup_iff_coeff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hmem
    exact ⟨g⁻¹ * h, hmem, by simp⟩

/-- Each free coefficient depends continuously on the automorphism. -/
theorem continuous_coefficient (n : ℕ) :
    Continuous (fun g : Nottingham p ↦ coefficientEquiv g n) := by
  rw [continuous_iff_continuousAt]
  intro g
  apply Filter.EventuallyEq.continuousAt (y := coefficientEquiv g n)
  apply (nhds_hasBasis g).mem_iff.mpr
  refine ⟨n + 2, trivial, ?_⟩
  intro h hh
  exact (mem_congruence_coset_iff g h (n + 2)).mp hh n (by omega)

theorem continuous_coefficientEquiv :
    Continuous (coefficientEquiv : Nottingham p → (ℕ → ZMod p)) :=
  continuous_pi continuous_coefficient

/-- Arbitrary free coefficients vary continuously in the congruence topology. -/
theorem continuous_ofCoefficients : Continuous (ofCoefficients (p := p)) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply (nhds_hasBasis (ofCoefficients a)).tendsto_right_iff.mpr
  intro n _
  have hc : Continuous (fun b : ℕ → ZMod p ↦ fun i : Fin (n - 1) ↦ b i) :=
    continuous_pi fun i ↦ continuous_apply (i : ℕ)
  have he := (hc.continuousAt (x := a)).eventually_mem
    (s := {fun i : Fin (n - 1) ↦ a i}) (by simp)
  filter_upwards [he] with b hb
  apply (mem_congruence_coset_iff _ _ n).mpr
  intro i hi
  simpa [coefficientEquiv] using congrFun hb ⟨i, hi⟩

/-- Free coefficients identify the Nottingham topology with the countable product topology. -/
noncomputable def coefficientHomeomorph : Nottingham p ≃ₜ (ℕ → ZMod p) where
  toEquiv := coefficientEquiv
  continuous_toFun := continuous_coefficientEquiv
  continuous_invFun := continuous_ofCoefficients

/-- The Nottingham group over the finite prime field is compact. -/
instance instCompactSpace : CompactSpace (Nottingham p) :=
  Function.Surjective.compactSpace continuous_ofCoefficients coefficientEquiv.symm.surjective

end Camina1997.Nottingham
