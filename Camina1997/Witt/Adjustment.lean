/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Galois
public import Camina1997.ArtinSchreier.Restriction

/-!
# Reduced parameters with a common pole bound in Witt's construction

Subtracting an additive coboundary preserves the factor-set equation. A
base-field adjustment of the parameter preserves its other Witt equation.
The infinite-dimensional restriction image then supplies arbitrarily deep
reduced parameters and hence proper central lifting over Laurent fields.

Reference: Camina (1997), pp. 105 and 109; Witt (1936), p. 240.
-/

@[expose] public section

namespace Camina1997.Witt

section General

variable {G K : Type*} [Group G] [Field K] [MulSemiringAction G K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Subtract the additive coboundary of `μ` from the root increments. -/
def adjustedDelta (δ : G → K) (μ : K) (s : G) : K := δ s - (s • μ - μ)

@[simp]
theorem adjustedDelta_one (δ : G → K) (μ : K) (hδ : δ 1 = 0) :
    adjustedDelta δ μ 1 = 0 := by
  simp [adjustedDelta, hδ]

/-- Subtracting a coboundary leaves the two-cocycle equation unchanged. -/
theorem adjustedDelta_twoCocycle (δ : G → K) (μ : K) (c : G → G → K)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) = c s t) (s t : G) :
    adjustedDelta δ μ s + s • adjustedDelta δ μ t - adjustedDelta δ μ (s * t) = c s t := by
  simp only [adjustedDelta, smul_sub, mul_smul]
  linear_combination hδ s t

/-- A fixed-field parameter adjustment and a coboundary change preserve the other Witt equation. -/
theorem adjustedDelta_parameter (δ : G → K) (γ μ b : K)
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s) (hb : ∀ s : G, s • b = b) (s : G) :
    s • (γ + b - (μ ^ p - μ)) - (γ + b - (μ ^ p - μ)) =
      adjustedDelta δ μ s ^ p - adjustedDelta δ μ s := by
  have hp : s • (μ ^ p) = (s • μ) ^ p :=
    map_pow (MulSemiringAction.toRingHom G K s) μ p
  simp only [adjustedDelta, smul_sub, smul_add, hb, hp, sub_pow_char]
  linear_combination hγ s

end General

section Laurent

variable {p : ℕ} [Fact p.Prime]
local notation "L" => LaurentSeries (ZMod p)

variable (F : Type*) [Field F] [Module (ZMod p) F] [CharP F p]
  [Algebra F (LaurentSeries (ZMod p))]
  [FiniteDimensional F (LaurentSeries (ZMod p))] [IsGalois F (LaurentSeries (ZMod p))]

/-- One genuine reduced-pole adjustment preserves all the equations simultaneously. -/
theorem exists_adjusted_witt_equations
    (hF : ¬Module.Finite (ZMod p) (ArtinSchreier.ASQuotient p F))
    (c : (L ≃ₐ[F] L) → (L ≃ₐ[F] L) → ZMod p) (δ : (L ≃ₐ[F] L) → L) (γ : L)
    (hδ1 : δ 1 = 0)
    (hδ : ∀ s t, δ s + s • δ t - δ (s * t) = ZMod.castHom (dvd_refl p) L (c s t))
    (hγ : ∀ s, s • γ - γ = δ s ^ p - δ s) (B : ℕ) :
    ∃ (b : F) (μ r : L) (m : ℕ), ArtinSchreier.IsReduced r ∧
      r = γ + algebraMap F L b - (μ ^ p - μ) ∧ B < m ∧ ¬p ∣ m ∧
      r.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ) ∧
      adjustedDelta δ μ 1 = 0 ∧
      (∀ s t, adjustedDelta δ μ s + s • adjustedDelta δ μ t - adjustedDelta δ μ (s * t) =
        ZMod.castHom (dvd_refl p) L (c s t)) ∧
      ∀ s, s • r - r = adjustedDelta δ μ s ^ p - adjustedDelta δ μ s := by
  obtain ⟨b, μ, r, m, hr, he, hm, hpm, hord⟩ :=
    ArtinSchreier.exists_reduced_pole_adjustment_order F hF γ B
  refine ⟨b, μ, r, m, hr, he, hm, hpm, hord, adjustedDelta_one δ μ hδ1,
    adjustedDelta_twoCocycle δ μ _ hδ, ?_⟩
  intro s
  rw [he]
  exact adjustedDelta_parameter δ γ μ (algebraMap F L b) hγ (fun s => s.commutes b) s

open Polynomial in
/-- Central lifting over a Laurent field with an arbitrarily deep reduced parameter.

The infinite Artin–Schreier quotient of the base field supplies irreducibility directly,
so no Frattini hypothesis is needed. The given extension is identified with the full Galois
group of the concrete quotient, and restriction is exactly its given projection.
-/
theorem exists_reduced_galois_centralLift {E : Type*} [Group E] [Finite E]
    (S : GroupExtension (Multiplicative (ZMod p)) E (L ≃ₐ[F] L))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (hF : ¬Module.Finite (ZMod p) (ArtinSchreier.ASQuotient p F)) (B : ℕ) :
    ∃ (r : L) (m : ℕ) (hm : 0 < m) (hpm : ¬p ∣ m)
      (hord : r.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)),
      ArtinSchreier.IsReduced r ∧ B < m ∧
      letI : Fact (Irreducible (X ^ p - X - C r)) :=
        ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm r hord⟩
      Module.finrank L (AdjoinRoot (X ^ p - X - C r)) = p ∧
      IsGalois F (AdjoinRoot (X ^ p - X - C r)) ∧
      ∃ ρ : E ≃* (AdjoinRoot (X ^ p - X - C r) ≃ₐ[F]
        AdjoinRoot (X ^ p - X - C r)),
        ∀ (e : E) (x : L), ρ e (algebraMap L _ x) = algebraMap L _ (S.rightHom e x) := by
  let σ := normalizedSection S
  have hσ : σ 1 = 1 := normalizedSection_one S
  obtain ⟨δ, γ, hδ1, hδ, hγ⟩ := exists_witt_equations («L» := L) (factorSet S σ)
    (factorSet_one_left S σ hσ) (factorSet_cocycle S σ hcentral)
  obtain ⟨b, μ, r, m, hr, _, hBm, hpm, hord, hδ1', hδ', hγ'⟩ :=
    exists_adjusted_witt_equations F hF (factorSet S σ) δ γ hδ1 hδ hγ B
  have hm : 0 < m := (Nat.zero_le B).trans_lt hBm
  refine ⟨r, m, hm, hpm, hord, hr, hBm, ?_⟩
  let : Fact (Irreducible (X ^ p - X - C r)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm r hord⟩
  let A := AdjoinRoot (X ^ p - X - C r)
  let : FiniteDimensional F A := FiniteDimensional.trans F L A
  have hfix : ∀ (s : L ≃ₐ[F] L) (x : F),
      s • algebraMap F L x = algebraMap F L x := fun s x => s.commutes x
  let ρ := centralLiftAlgHom S σ hσ hcentral r (adjustedDelta δ μ) hγ' hδ' hδ1' hfix
  have hρ : Function.Injective ρ :=
    centralLiftAlgHom_injective S σ hσ hcentral r (adjustedDelta δ μ) hγ' hδ' hδ1' hfix
  have hdegree : Module.finrank L A = p := ArtinSchreier.finrank_adjoinRoot r
  have hcard : Nat.card E = Module.finrank F A := by
    rw [card_centralExtension S, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank F L A, hdegree]
  obtain ⟨hgalois, hbij⟩ := full_galois_of_card_eq_finrank ρ hρ hcard
  exact ⟨hdegree, hgalois, MulEquiv.ofBijective ρ hbij,
    centralLiftAlgHom_algebraMap S σ hσ hcentral r (adjustedDelta δ μ) hγ' hδ' hδ1' hfix⟩

omit [Algebra F (LaurentSeries (ZMod p))]
  [FiniteDimensional F (LaurentSeries (ZMod p))] [IsGalois F (LaurentSeries (ZMod p))] in
/-- A field identified with Laurent series has an infinite-dimensional Artin–Schreier quotient. -/
theorem not_moduleFinite_quotient_of_laurentEquiv (e : F ≃+* L) :
    ¬Module.Finite (ZMod p) (ArtinSchreier.ASQuotient p F) := by
  let f := ArtinSchreier.quotientMap (p := p) e.toRingHom
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, hx⟩ := (ArtinSchreier.wpLinearMap p L).range.mkQ_surjective q
    change ArtinSchreier.classMap p L x = q at hx
    refine ⟨ArtinSchreier.classMap p F (e.symm x), ?_⟩
    change ArtinSchreier.classMap p L (e (e.symm x)) = q
    simpa only [e.apply_symm_apply] using hx
  intro h
  let := h
  exact ArtinSchreier.not_moduleFinite_quotient (Module.Finite.of_surjective f hf)

open Polynomial in
/-- For a base identified with Laurent series, its proved quotient basis supplies the
infinite-dimensional input to the reduced central lift. -/
theorem exists_reduced_galois_centralLift_laurentBase {E : Type*} [Group E] [Finite E]
    (eF : F ≃+* L) (S : GroupExtension (Multiplicative (ZMod p)) E (L ≃ₐ[F] L))
    (hcentral : S.inl.range ≤ Subgroup.center E) (B : ℕ) :
    ∃ (r : L) (m : ℕ) (hm : 0 < m) (hpm : ¬p ∣ m)
      (hord : r.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)),
      ArtinSchreier.IsReduced r ∧ B < m ∧
      letI : Fact (Irreducible (X ^ p - X - C r)) :=
        ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm r hord⟩
      Module.finrank L (AdjoinRoot (X ^ p - X - C r)) = p ∧
      IsGalois F (AdjoinRoot (X ^ p - X - C r)) ∧
      ∃ ρ : E ≃* (AdjoinRoot (X ^ p - X - C r) ≃ₐ[F]
        AdjoinRoot (X ^ p - X - C r)),
        ∀ (e : E) (x : L), ρ e (algebraMap L _ x) = algebraMap L _ (S.rightHom e x) :=
  exists_reduced_galois_centralLift F S hcentral
    (not_moduleFinite_quotient_of_laurentEquiv F eF) B

end Laurent

end Camina1997.Witt
