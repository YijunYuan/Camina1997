/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.LaurentTopology
public import Camina1997.Nottingham.FiniteAction
public import Camina1997.ArtinSchreier.Completeness

/-!
# Restricting Laurent-series actions to Nottingham

An order-preserving action on the Laurent field restricts to its valuation ring.
The restriction is faithful because the Laurent field is the fraction field of
the power-series ring. In characteristic `p`, a `p`-group action is normalized.

Reference: Camina (1997), Theorem 3, p. 105.
-/

@[expose] public section

namespace LaurentSeries

variable {k : Type*} [Field k]

/-- The power-series subring is the nonnegative part of Laurent order. -/
theorem mem_powerSeries_as_subring_iff (x : LaurentSeries k) :
    x ∈ powerSeries_as_subring k ↔ 0 ≤ x.orderTop := by
  have hv : Valued.v x ≤ 1 ↔ (0 : WithTop ℤ) ≤ x.orderTop := by
    simpa using valuation_le_exp_iff_orderTop x 0
  rw [← hv, val_le_one_iff_eq_coe]
  constructor
  · rintro ⟨f, _, hf⟩
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, trivial, hf⟩

/-- Restrict an order-preserving Laurent automorphism to its valuation ring. -/
noncomputable def powerSeriesSubringEquiv (e : LaurentSeries k ≃+* LaurentSeries k)
    (he : ∀ x, (e x).orderTop = x.orderTop) :
    powerSeries_as_subring k ≃+* powerSeries_as_subring k where
  toFun x := ⟨e x, by
    rw [mem_powerSeries_as_subring_iff, he]
    exact (mem_powerSeries_as_subring_iff (x : LaurentSeries k)).mp x.property⟩
  invFun x := ⟨e.symm x, by
    rw [mem_powerSeries_as_subring_iff, ← he (e.symm x), e.apply_symm_apply]
    exact (mem_powerSeries_as_subring_iff (x : LaurentSeries k)).mp x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul e (x : LaurentSeries k) (y : LaurentSeries k))
  map_add' x y := Subtype.ext (map_add e (x : LaurentSeries k) (y : LaurentSeries k))

/-- Restriction in the canonical power-series coordinates. -/
noncomputable def restrictPowerSeriesRingEquiv (e : LaurentSeries k ≃+* LaurentSeries k)
    (he : ∀ x, (e x).orderTop = x.orderTop) : PowerSeries k ≃+* PowerSeries k :=
  (powerSeriesEquivSubring k).trans
    ((powerSeriesSubringEquiv e he).trans (powerSeriesEquivSubring k).symm)

/-- Coercion intertwines restriction with the original Laurent automorphism. -/
theorem coe_restrictPowerSeriesRingEquiv (e : LaurentSeries k ≃+* LaurentSeries k)
    (he : ∀ x, (e x).orderTop = x.orderTop) (f : PowerSeries k) :
    (restrictPowerSeriesRingEquiv e he f : LaurentSeries k) = e (f : LaurentSeries k) := by
  have h := (powerSeriesEquivSubring k).apply_symm_apply
    (powerSeriesSubringEquiv e he (powerSeriesEquivSubring k f))
  exact congrArg Subtype.val h

end LaurentSeries

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)
local notation "R" => PowerSeries (ZMod p)

/-- Extending a Nottingham automorphism preserves Laurent order exactly. -/
theorem orderTop_toLaurent (g : Nottingham p) (x : K) :
    (toLaurent g x).orderTop = x.orderTop := by
  have hbound (n : ℤ) : (n : WithTop ℤ) ≤ (toLaurent g x).orderTop ↔
      (n : WithTop ℤ) ≤ x.orderTop := by
    rw [← LaurentSeries.valuation_le_exp_iff_orderTop,
      valuation_toLaurent, LaurentSeries.valuation_le_exp_iff_orderTop]
  by_cases hx : x = 0
  · simp [hx]
  have hy : toLaurent g x ≠ 0 := by simpa using hx
  apply le_antisymm
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hy]
    exact (hbound _).mp (by rw [HahnSeries.order_eq_orderTop_of_ne_zero hy])
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx]
    exact (hbound _).mpr (by rw [HahnSeries.order_eq_orderTop_of_ne_zero hx])

/-- Every order-preserving prime-field Laurent automorphism restricts as an algebra automorphism. -/
noncomputable def restrictPowerSeries (e : K ≃ₐ[ZMod p] K)
    (he : ∀ x, (e x).orderTop = x.orderTop) : R ≃ₐ[ZMod p] R :=
  AlgEquiv.ofRingEquiv (f := LaurentSeries.restrictPowerSeriesRingEquiv e.toRingEquiv he)
    (fun a => DFunLike.congr_fun (RingHom.ext_zmod
      ((LaurentSeries.restrictPowerSeriesRingEquiv e.toRingEquiv he).toRingHom.comp
        (algebraMap (ZMod p) R)) (algebraMap (ZMod p) R)) a)

/-- The restricted algebra automorphism acts on power series by the original Laurent action. -/
theorem coe_restrictPowerSeries (e : K ≃ₐ[ZMod p] K)
    (he : ∀ x, (e x).orderTop = x.orderTop) (f : R) :
    (restrictPowerSeries e he f : K) = e (f : K) :=
  LaurentSeries.coe_restrictPowerSeriesRingEquiv e.toRingEquiv he f

variable {G : Type*} [Group G]

/-- Restriction of an order-preserving Laurent action is a power-series action. -/
noncomputable def restrictLaurentAction (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) : G →* (R ≃ₐ[ZMod p] R) where
  toFun g := restrictPowerSeries (ρ g) (hρ g)
  map_one' := by
    ext f : 1
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change (restrictPowerSeries (ρ 1) (hρ 1) f : K) = (f : K)
    rw [coe_restrictPowerSeries, map_one]
    rfl
  map_mul' g h := by
    ext f : 1
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change (restrictPowerSeries (ρ (g * h)) (hρ (g * h)) f : K) =
      (restrictPowerSeries (ρ g) (hρ g) (restrictPowerSeries (ρ h) (hρ h) f) : K)
    rw [coe_restrictPowerSeries, coe_restrictPowerSeries, coe_restrictPowerSeries,
      map_mul]
    rfl

/-- The restricted action agrees with the original action on every power series. -/
theorem coe_restrictLaurentAction (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) (g : G) (f : R) :
    (restrictLaurentAction ρ hρ g f : K) = ρ g (f : K) :=
  coe_restrictPowerSeries (ρ g) (hρ g) f

/-- The Laurent action is determined by its restriction to the power-series ring. -/
theorem restrictLaurentAction_injective_iff (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) :
    Function.Injective (restrictLaurentAction ρ hρ) ↔ Function.Injective ρ := by
  constructor
  · intro h g g' he
    apply h
    ext f : 1
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [coe_restrictLaurentAction, coe_restrictLaurentAction, he]
  · intro h g g' he
    apply h
    ext x : 1
    have hcoe (f : R) : ρ g (f : K) = ρ g' (f : K) := by
      rw [← coe_restrictLaurentAction ρ hρ, ← coe_restrictLaurentAction ρ hρ, he]
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
    simp only [map_div₀, LaurentSeries.coe_algebraMap]
    exact congrArg₂ (· / ·) (hcoe a) (hcoe b)

/-- A `p`-group action preserving Laurent order gives a Nottingham action. -/
noncomputable def ofLaurentAction (hG : IsPGroup p G) (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) : G →* Nottingham p :=
  ofPGroupAction hG (restrictLaurentAction ρ hρ)

/-- Extending the constructed Nottingham action recovers the given Laurent action. -/
theorem toLaurent_ofLaurentAction (hG : IsPGroup p G) (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) (g : G) :
    toLaurent (ofLaurentAction hG ρ hρ g) = ρ g := by
  symm
  apply toLaurent_unique
  intro f
  exact (coe_restrictLaurentAction ρ hρ g f).symm

/-- Factoring a Laurent `p`-group action into Nottingham preserves and reflects faithfulness. -/
theorem ofLaurentAction_injective_iff (hG : IsPGroup p G) (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) :
    Function.Injective (ofLaurentAction hG ρ hρ) ↔ Function.Injective ρ :=
  (ofPGroupAction_injective_iff hG (restrictLaurentAction ρ hρ)).trans
    (restrictLaurentAction_injective_iff ρ hρ)

/-- A finite faithful Laurent `p`-group action gives a closed topological Nottingham embedding. -/
theorem isClosedEmbedding_ofLaurentAction [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (hG : IsPGroup p G) (ρ : G →* (K ≃ₐ[ZMod p] K))
    (hρ : ∀ g x, (ρ g x).orderTop = x.orderTop) (hfaithful : Function.Injective ρ) :
    Topology.IsClosedEmbedding (ofLaurentAction hG ρ hρ) :=
  isClosedEmbedding_ofPGroupAction hG (restrictLaurentAction ρ hρ)
    ((restrictLaurentAction_injective_iff ρ hρ).mpr hfaithful)

end Camina1997.Nottingham
