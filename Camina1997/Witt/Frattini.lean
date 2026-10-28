/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Central
public import Mathlib.GroupTheory.Frattini
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Properness of the central Frattini lifting step

If the Artin–Schreier parameter in Witt's construction were an image, its
additive equations would construct a splitting of the central extension.
The canonical Frattini subgroup excludes such a splitting for a nontrivial
kernel. Thus the actual Artin–Schreier quotient is a field of degree `p`.

Reference: Witt (1936), p. 240; Camina (1997), p. 104.
-/

@[expose] public section

namespace Camina1997.Witt

/-- A nontrivial kernel inside the Frattini subgroup admits no group-homomorphic section. -/
theorem no_splitting_of_le_frattini {N E G : Type*} [Group N] [Group E] [Group G]
    [Finite E] [Nontrivial N] (S : GroupExtension N E G)
    (hN : S.inl.range ≤ frattini E) : ¬Nonempty S.Splitting := by
  rintro ⟨v⟩
  have htop : v.toMonoidHom.range = ⊤ := by
    apply frattini_nongenerating
    apply top_unique
    intro e _
    have hker : e * (v (S.rightHom e))⁻¹ ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      simp
    have hn : e * (v (S.rightHom e))⁻¹ ∈ v.toMonoidHom.range ⊔ frattini E :=
      (show frattini E ≤ v.toMonoidHom.range ⊔ frattini E from le_sup_right) (hN hker)
    have hv : v (S.rightHom e) ∈ v.toMonoidHom.range ⊔ frattini E :=
      (show v.toMonoidHom.range ≤ v.toMonoidHom.range ⊔ frattini E from le_sup_left)
        ⟨S.rightHom e, rfl⟩
    simpa using (v.toMonoidHom.range ⊔ frattini E).mul_mem hn hv
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  have hmem : S.inl n ∈ v.toMonoidHom.range := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := hmem
  have hg1 : g = 1 := by
    have h := congrArg S.rightHom hg
    change S.rightHom (v g) = S.rightHom (S.inl n) at h
    simpa using h
  apply hn
  apply S.inl_injective
  rw [← hg, hg1]
  simp

variable {E G K : Type*} [Group E] [Group G] [Field K] [MulSemiringAction G K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : GroupExtension (Multiplicative (ZMod p)) E G)

omit [MulSemiringAction G K] in
/-- The kernel of the Artin–Schreier map is precisely the prime field. -/
theorem exists_zmod_cast_of_pow_sub_eq_zero (x : K) (hx : x ^ p - x = 0) :
    ∃ a : ZMod p, ZMod.castHom (dvd_refl p) K a = x := by
  have hmem := (Subfield.mem_bot_iff_pow_eq_self K p).mpr (sub_eq_zero.mp hx)
  rw [← ZMod.fieldRange_castHom_eq_bot p] at hmem
  exact hmem

/-- An Artin–Schreier root of Witt's parameter constructs an actual homomorphic section. -/
theorem nonempty_splitting_of_parameter_image (σ : S.Section) (hσ : σ 1 = 1)
    (hcentral : S.inl.range ≤ Subgroup.center E) (γ : K) (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) =
      ZMod.castHom (dvd_refl p) K (factorSet S σ s t))
    (hδ1 : δ 1 = 0) (β : K) (hβ : β ^ p - β = γ) : Nonempty S.Splitting := by
  have hwp (s : G) : (δ s - (s • β - β)) ^ p - (δ s - (s • β - β)) = 0 := by
    have hmap := congrArg (fun x : K => s • x) hβ
    have hp : s • (β ^ p) = (s • β) ^ p :=
      map_pow (MulSemiringAction.toRingHom G K s) β p
    simp only [smul_sub, hp] at hmap
    rw [sub_pow_char, sub_pow_char]
    linear_combination -(hγ s) - hmap + hβ
  choose a ha using fun s => exists_zmod_cast_of_pow_sub_eq_zero _ (hwp s)
  have ha1 : a 1 = 0 := by
    apply ZMod.castHom_injective K
    simpa [hδ1] using ha 1
  have hc (s t : G) : a s + a t - a (s * t) = factorSet S σ s t := by
    apply ZMod.castHom_injective K
    have hmap := congrArg (fun x : K => s • x) (ha t)
    simp only [smul_zmod_cast, smul_sub, ← mul_smul] at hmap
    simp only [map_add, map_sub]
    linear_combination ha s + hmap - ha (s * t) + hδ s t
  refine ⟨{ toFun := fun s => S.inl (Multiplicative.ofAdd (-a s)) * σ s
            map_one' := ?_, map_mul' := ?_, rightInverse_rightHom := ?_ }⟩
  · simp [ha1, hσ]
  · intro s t
    rw [central_coordinates_mul S σ hcentral]
    have he : -a s + -a t + factorSet S σ s t = -a (s * t) := by
      linear_combination -(hc s t)
    rw [he]
  · intro s
    simp

/-- The canonical Frattini hypothesis forces Witt's parameter outside the Artin–Schreier image. -/
theorem parameter_not_image_of_le_frattini [Finite E]
    (σ : S.Section) (hσ : σ 1 = 1) (hcentral : S.inl.range ≤ Subgroup.center E)
    (hfrattini : S.inl.range ≤ frattini E) (γ : K) (δ : G → K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) =
      ZMod.castHom (dvd_refl p) K (factorSet S σ s t))
    (hδ1 : δ 1 = 0) : ∀ β : K, β ^ p - β ≠ γ := by
  intro β hβ
  exact no_splitting_of_le_frattini S hfrattini
    (nonempty_splitting_of_parameter_image S σ hσ hcentral γ δ hγ hδ hδ1 β hβ)

open Polynomial in
/-- A central Frattini extension acts faithfully on a concrete degree-`p` Artin–Schreier field.

Both the parameter and the action are produced from the given extension. This theorem supplies
the field and the faithful action; identifying it with the full Galois group over `F` is separate.
-/
theorem exists_field_centralLift [Finite E] [FaithfulSMul G K]
    {F : Type*} [Field F] [Algebra F K]
    (hF : ∀ (s : G) (x : F), s • algebraMap F K x = algebraMap F K x)
    (hcentral : S.inl.range ≤ Subgroup.center E) (hfrattini : S.inl.range ≤ frattini E) :
    ∃ γ : K, (∀ β : K, β ^ p - β ≠ γ) ∧
      IsField (AdjoinRoot (X ^ p - X - C γ)) ∧
      Module.finrank K (AdjoinRoot (X ^ p - X - C γ)) = p ∧
      ∃ ρ : E →* (AdjoinRoot (X ^ p - X - C γ) ≃ₐ[F]
        AdjoinRoot (X ^ p - X - C γ)), Function.Injective ρ ∧
        ∀ (e : E) (x : K), ρ e (algebraMap K _ x) = algebraMap K _ (S.rightHom e • x) := by
  let : Finite G := Finite.of_surjective S.rightHom S.rightHom_surjective
  let σ := normalizedSection S
  have hσ : σ 1 = 1 := normalizedSection_one S
  obtain ⟨δ, γ, hδ1, hδ, hγ⟩ := exists_witt_equations (L := K) (factorSet S σ)
    (factorSet_one_left S σ hσ) (factorSet_cocycle S σ hcentral)
  have ha := parameter_not_image_of_le_frattini S σ hσ hcentral hfrattini γ δ hγ hδ hδ1
  refine ⟨γ, ha, ArtinSchreier.isField_adjoinRoot γ ha, ArtinSchreier.finrank_adjoinRoot γ,
    centralLiftAlgHom S σ hσ hcentral γ δ hγ hδ hδ1 hF, ?_, ?_⟩
  · exact centralLiftAlgHom_injective S σ hσ hcentral γ δ hγ hδ hδ1 hF
  · exact centralLiftAlgHom_algebraMap S σ hσ hcentral γ δ hγ hδ hδ1 hF

end Camina1997.Witt
