/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Extension
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Central extensions and Witt's lifted representation

The factor set and coordinates are extracted from a section of a canonical
`GroupExtension`. Their identities connect the explicit additive equations to
an injective representation of the given extension by automorphisms of the
actual Artin–Schreier quotient.

Reference: Witt (1936), pp. 238–240; Camina (1997), pp. 103–104.
-/

@[expose] public section

namespace Camina1997.Witt

variable {E G : Type*} [Group E] [Group G] {p : ℕ}
variable (S : GroupExtension (Multiplicative (ZMod p)) E G)

/-- A section that takes the identity to the identity. -/
noncomputable def normalizedSection : S.Section := by
  classical
  exact
    { toFun := fun s => if s = 1 then 1 else S.surjInvRightHom s
      rightInverse_rightHom := by
        intro s
        dsimp only
        split_ifs with h
        · simpa using h.symm
        · exact S.surjInvRightHom.rightHom_section s }

@[simp]
theorem normalizedSection_one : normalizedSection S 1 = 1 := by
  simp [normalizedSection]

theorem exists_centralCoordinate (σ : S.Section) (e : E) :
    ∃ a : ZMod p, e = S.inl (Multiplicative.ofAdd a) * σ (S.rightHom e) := by
  have hmem : e * (σ (S.rightHom e))⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a.toAdd, ?_⟩
  change e = S.inl a * σ (S.rightHom e)
  rw [ha, inv_mul_cancel_right]

/-- The prime-field coordinate of an element relative to a section. -/
noncomputable def centralCoordinate (σ : S.Section) (e : E) : ZMod p :=
  (exists_centralCoordinate S σ e).choose

theorem centralCoordinate_spec (σ : S.Section) (e : E) :
    e = S.inl (Multiplicative.ofAdd (centralCoordinate S σ e)) * σ (S.rightHom e) :=
  (exists_centralCoordinate S σ e).choose_spec

theorem centralCoordinate_unique (σ : S.Section) (e : E) (a : ZMod p)
    (h : e = S.inl (Multiplicative.ofAdd a) * σ (S.rightHom e)) :
    centralCoordinate S σ e = a := by
  apply Multiplicative.ofAdd.injective
  apply S.inl_injective
  exact mul_right_cancel ((centralCoordinate_spec S σ e).symm.trans h)

@[simp]
theorem centralCoordinate_inl_mul (σ : S.Section) (a : ZMod p) (s : G) :
    centralCoordinate S σ (S.inl (Multiplicative.ofAdd a) * σ s) = a := by
  apply centralCoordinate_unique
  simp

@[simp]
theorem centralCoordinate_section (σ : S.Section) (s : G) :
    centralCoordinate S σ (σ s) = 0 := by
  simpa using centralCoordinate_inl_mul S σ 0 s

theorem centralCoordinate_one (σ : S.Section) (hσ : σ 1 = 1) :
    centralCoordinate S σ 1 = 0 := by
  simpa only [hσ] using centralCoordinate_section S σ 1

/-- Every extension element has unique section and prime-field coordinates. -/
noncomputable def centralCoordinates (σ : S.Section) : E ≃ G × ZMod p where
  toFun e := (S.rightHom e, centralCoordinate S σ e)
  invFun z := S.inl (Multiplicative.ofAdd z.2) * σ z.1
  left_inv e := (centralCoordinate_spec S σ e).symm
  right_inv z := by ext <;> simp

/-- The factor set of the chosen section. -/
noncomputable def factorSet (σ : S.Section) (s t : G) : ZMod p :=
  centralCoordinate S σ (σ s * σ t)

theorem factorSet_spec (σ : S.Section) (s t : G) :
    σ s * σ t = S.inl (Multiplicative.ofAdd (factorSet S σ s t)) * σ (s * t) := by
  simpa only [factorSet, map_mul, σ.rightHom_section] using
    centralCoordinate_spec S σ (σ s * σ t)

@[simp]
theorem factorSet_one_left (σ : S.Section) (hσ : σ 1 = 1) (s : G) :
    factorSet S σ 1 s = 0 := by
  apply centralCoordinate_unique
  simp [hσ]

@[simp]
theorem factorSet_one_right (σ : S.Section) (hσ : σ 1 = 1) (s : G) :
    factorSet S σ s 1 = 0 := by
  apply centralCoordinate_unique
  simp [hσ]

/-- Multiplication in section coordinates, using the given centrality of the kernel. -/
theorem central_coordinates_mul (σ : S.Section)
    (hcentral : S.inl.range ≤ Subgroup.center E) (a b : ZMod p) (s t : G) :
    (S.inl (Multiplicative.ofAdd a) * σ s) * (S.inl (Multiplicative.ofAdd b) * σ t) =
      S.inl (Multiplicative.ofAdd (a + b + factorSet S σ s t)) * σ (s * t) := by
  have hcomm : σ s * S.inl (Multiplicative.ofAdd b) =
      S.inl (Multiplicative.ofAdd b) * σ s :=
    Subgroup.mem_center_iff.mp (hcentral ⟨Multiplicative.ofAdd b, rfl⟩) (σ s)
  calc
    _ = (S.inl (Multiplicative.ofAdd a) * S.inl (Multiplicative.ofAdd b)) *
        (σ s * σ t) := by
      rw [mul_assoc, ← mul_assoc (σ s), hcomm]
      group
    _ = _ := by
      rw [factorSet_spec]
      simp only [ofAdd_add, map_mul]
      group

theorem centralCoordinate_mul (σ : S.Section)
    (hcentral : S.inl.range ≤ Subgroup.center E) (e f : E) :
    centralCoordinate S σ (e * f) = centralCoordinate S σ e + centralCoordinate S σ f +
      factorSet S σ (S.rightHom e) (S.rightHom f) := by
  apply centralCoordinate_unique
  rw [map_mul]
  calc
    e * f = (S.inl (Multiplicative.ofAdd (centralCoordinate S σ e)) * σ (S.rightHom e)) *
        (S.inl (Multiplicative.ofAdd (centralCoordinate S σ f)) * σ (S.rightHom f)) := by
      rw [← centralCoordinate_spec, ← centralCoordinate_spec]
    _ = _ := central_coordinates_mul S σ hcentral _ _ _ _

/-- Associativity of the given extension supplies the factor-set cocycle identity. -/
theorem factorSet_cocycle (σ : S.Section) (hcentral : S.inl.range ≤ Subgroup.center E)
    (s t u : G) :
    factorSet S σ s t + factorSet S σ (s * t) u =
      factorSet S σ s (t * u) + factorSet S σ t u := by
  have h := congrArg (centralCoordinate S σ) (mul_assoc (σ s) (σ t) (σ u))
  simp only [centralCoordinate_mul S σ hcentral, map_mul, σ.rightHom_section,
    centralCoordinate_section, zero_add, add_zero] at h
  simpa only [add_comm] using h

section FieldAction

open Polynomial

variable {K : Type*} [Field K] [MulSemiringAction G K] [Fact p.Prime] [CharP K p]
variable (σ : S.Section) (hσ : σ 1 = 1) (hcentral : S.inl.range ≤ Subgroup.center E)
variable (γ : K) (δ : G → K) (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
variable (hδ : ∀ s t, δ s + s • δ t - δ (s * t) =
  ZMod.castHom (dvd_refl p) K (factorSet S σ s t)) (hδ1 : δ 1 = 0)

local notation "A" => AdjoinRoot (X ^ p - X - C γ)
local notation "y" => AdjoinRoot.root (X ^ p - X - C γ)

/-- The homomorphism from the given extension group to automorphisms of the actual quotient. -/
noncomputable def centralLift : E →* (A ≃+* A) where
  toFun e := wittLift γ δ hγ (S.rightHom e) (centralCoordinate S σ e)
  map_one' := by
    rw [map_one, centralCoordinate_one S σ hσ]
    exact wittLift_one γ δ hγ hδ1
  map_mul' e f := by
    rw [map_mul, centralCoordinate_mul S σ hcentral]
    exact (wittLift_mul γ δ hγ (factorSet S σ) hδ _ _ _ _).symm

theorem centralLift_injective [FaithfulSMul G K] :
    Function.Injective (centralLift S σ hσ hcentral γ δ hγ hδ hδ1) := by
  intro e f h
  apply (centralCoordinates S σ).injective
  exact wittLift_injective γ δ hγ h

@[simp]
theorem centralLift_algebraMap (e : E) (x : K) :
    centralLift S σ hσ hcentral γ δ hγ hδ hδ1 e (algebraMap K A x) =
      algebraMap K A (S.rightHom e • x) :=
  wittLift_algebraMap γ δ hγ _ _ _

@[simp]
theorem centralLift_root (e : E) :
    centralLift S σ hσ hcentral γ δ hγ hδ hδ1 e y = y + algebraMap K A
      (δ (S.rightHom e) + ZMod.castHom (dvd_refl p) K (centralCoordinate S σ e)) :=
  wittLift_root γ δ hγ _ _

section BaseAlgebra

variable {F : Type*} [CommSemiring F] [Algebra F K]
variable (hF : ∀ (s : G) (x : F), s • algebraMap F K x = algebraMap F K x)

/-- The same faithful representation by algebra automorphisms over any fixed base ring. -/
noncomputable def centralLiftAlgHom : E →* (A ≃ₐ[F] A) where
  toFun e := wittLiftAlgEquiv γ δ hγ hF (S.rightHom e) (centralCoordinate S σ e)
  map_one' := by
    apply AlgEquiv.toRingEquiv_injective
    exact (centralLift S σ hσ hcentral γ δ hγ hδ hδ1).map_one
  map_mul' e f := by
    apply AlgEquiv.toRingEquiv_injective
    exact (centralLift S σ hσ hcentral γ δ hγ hδ hδ1).map_mul e f

theorem centralLiftAlgHom_injective [FaithfulSMul G K] :
    Function.Injective (centralLiftAlgHom S σ hσ hcentral γ δ hγ hδ hδ1 hF) := by
  intro e f h
  exact centralLift_injective S σ hσ hcentral γ δ hγ hδ hδ1
    (congrArg AlgEquiv.toRingEquiv h)

@[simp]
theorem centralLiftAlgHom_algebraMap (e : E) (x : K) :
    centralLiftAlgHom S σ hσ hcentral γ δ hγ hδ hδ1 hF e (algebraMap K A x) =
      algebraMap K A (S.rightHom e • x) :=
  wittLift_algebraMap γ δ hγ _ _ _

end BaseAlgebra

omit σ hσ γ δ hγ hδ hδ1 in
/-- Every central extension with kernel of order `p` acts faithfully on an actual
Artin–Schreier quotient. The construction has not yet asserted that this quotient is a field. -/
theorem exists_centralLift [Finite G] [FaithfulSMul G K]
    (hcentral : S.inl.range ≤ Subgroup.center E) :
    ∃ γ : K, ∃ ρ : E →* (AdjoinRoot (X ^ p - X - C γ) ≃+*
      AdjoinRoot (X ^ p - X - C γ)), Function.Injective ρ ∧
      ∀ (e : E) (x : K), ρ e (algebraMap K _ x) = algebraMap K _ (S.rightHom e • x) := by
  let σ := normalizedSection S
  have hσ : σ 1 = 1 := normalizedSection_one S
  obtain ⟨δ, γ, hδ1, hδ, hγ⟩ := exists_witt_equations (L := K) (factorSet S σ)
    (factorSet_one_left S σ hσ) (factorSet_cocycle S σ hcentral)
  exact ⟨γ, centralLift S σ hσ hcentral γ δ hγ hδ hδ1,
    centralLift_injective S σ hσ hcentral γ δ hγ hδ hδ1,
    centralLift_algebraMap S σ hσ hcentral γ δ hγ hδ hδ1⟩

end FieldAction

end Camina1997.Witt
