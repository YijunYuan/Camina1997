/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Frattini

/-!
# The full Galois group in the central Frattini lifting step

The explicit faithful action has as many elements as the degree of the produced
field extension. The automorphism-count criterion makes the extension Galois,
and the lifted representation is an isomorphism with its full Galois group.

Reference: Witt (1936), pp. 238–240; Camina (1997), pp. 103–104.
-/

@[expose] public section

open Polynomial

namespace Camina1997.Witt

variable {E G : Type*} [Group E] [Group G] {p : ℕ}

/-- The section coordinates count the original extension group. -/
theorem card_centralExtension (S : GroupExtension (Multiplicative (ZMod p)) E G) :
    Nat.card E = Nat.card G * p := by
  rw [Nat.card_congr (centralCoordinates S (normalizedSection S)), Nat.card_prod, Nat.card_zmod]

/-- A faithful automorphism action whose group order equals the field degree is the full
Galois group. -/
theorem full_galois_of_card_eq_finrank {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] (ρ : E →* (L ≃ₐ[F] L))
    (hρ : Function.Injective ρ) (hcard : Nat.card E = Module.finrank F L) :
    IsGalois F L ∧ Function.Bijective ρ := by
  have hupper : Nat.card (L ≃ₐ[F] L) ≤ Nat.card E := by
    calc
      Nat.card (L ≃ₐ[F] L) ≤ Nat.card (L →ₐ[F] L) :=
        Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective
      _ ≤ Module.finrank F L := card_algHom_le_finrank F L L
      _ = Nat.card E := hcard.symm
  have hbij := hρ.bijective_of_nat_card_le hupper
  have hcount : Nat.card (L ≃ₐ[F] L) = Module.finrank F L :=
    (Nat.card_congr (Equiv.ofBijective ρ hbij)).symm.trans hcard
  exact ⟨IsGalois.of_card_aut_eq_finrank F L hcount, hbij⟩

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [IsGalois F K] [Finite E]
variable [Fact p.Prime] [CharP K p]

/-- Proper lifting across a central Frattini kernel of order `p`.

The parameter is constructed, its Artin–Schreier polynomial is proved irreducible, and the
resulting degree-`p` field has the prescribed full Galois group with the prescribed restriction.
-/
theorem exists_galois_centralLift
    (S : GroupExtension (Multiplicative (ZMod p)) E (K ≃ₐ[F] K))
    (hcentral : S.inl.range ≤ Subgroup.center E) (hfrattini : S.inl.range ≤ frattini E) :
    ∃ (γ : K) (hγ : ∀ β : K, β ^ p - β ≠ γ),
      letI : Fact (Irreducible (X ^ p - X - C γ)) :=
        ⟨Polynomial.irreducible_X_pow_sub_X_sub_C γ hγ⟩
      Module.finrank K (AdjoinRoot (X ^ p - X - C γ)) = p ∧
      IsGalois F (AdjoinRoot (X ^ p - X - C γ)) ∧
      ∃ ρ : E ≃* (AdjoinRoot (X ^ p - X - C γ) ≃ₐ[F]
        AdjoinRoot (X ^ p - X - C γ)),
        ∀ (e : E) (x : K), ρ e (algebraMap K _ x) = algebraMap K _ (S.rightHom e x) := by
  have hF : ∀ (s : K ≃ₐ[F] K) (x : F),
      s • algebraMap F K x = algebraMap F K x := fun s x => s.commutes x
  obtain ⟨γ, ha, _, hdegree, ρ, hρ, hrestrict⟩ :=
    exists_field_centralLift S hF hcentral hfrattini
  refine ⟨γ, ha, ?_⟩
  let : Fact (Irreducible (X ^ p - X - C γ)) :=
    ⟨Polynomial.irreducible_X_pow_sub_X_sub_C γ ha⟩
  let L := AdjoinRoot (X ^ p - X - C γ)
  let : FiniteDimensional F L := FiniteDimensional.trans F K L
  have hcard : Nat.card E = Module.finrank F L := by
    rw [card_centralExtension S, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank F K L, hdegree]
  obtain ⟨hgalois, hbij⟩ := full_galois_of_card_eq_finrank ρ hρ hcard
  exact ⟨hdegree, hgalois, MulEquiv.ofBijective ρ hbij, hrestrict⟩

end Camina1997.Witt
