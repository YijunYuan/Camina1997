/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Parameter

/-!
# Laurent-series coordinates for a reduced Artin–Schreier extension

Evaluation at a uniformizer extends from power series to their fraction field.
-/

@[expose] public section

open Polynomial Filter
open scoped Uniformity

namespace LaurentSeries

/-- Coercion from power series preserves its finite order. -/
theorem orderTop_coe_of_ne_zero {k : Type*} [Field k] {f : PowerSeries k}
    (hf : f ≠ 0) : (f : LaurentSeries k).orderTop = (f.order.toNat : WithTop ℤ) := by
  apply le_antisymm
  · exact HahnSeries.orderTop_le_of_coeff_ne_zero
      (by simpa using PowerSeries.coeff_order hf)
  · rw [HahnSeries.le_orderTop_iff_forall]
    intro i hi
    rw [PowerSeries.coeff_coe]
    split_ifs with hn
    · rfl
    · apply PowerSeries.coeff_of_lt_order_toNat
      have hi' : i < (f.order.toNat : ℤ) := WithTop.coe_lt_coe.mp hi
      omega

end LaurentSeries

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
variable (γ : LaurentSeries k) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "O" => weightedInteger (p := p) γ m hm hpm hγ

/-- Evaluation into the quotient field, as a homomorphism of coefficient algebras. -/
noncomputable def powerSeriesEvalAlgHom (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) : PowerSeries k →ₐ[k] L where
  toRingHom := (O).subtype.comp (powerSeriesEval γ m hm hpm hγ π hπ)
  commutes' c := by
    change (powerSeriesEval γ m hm hpm hγ π hπ (PowerSeries.C c) : L) =
      algebraMap k L c
    rw [powerSeriesEval_C, coe_constantIntegerHom]
    rw [IsScalarTower.algebraMap_apply k K L]
    simp [HahnSeries.algebraMap_apply']

/-- Extend the power-series parametrization to the fraction fields. -/
noncomputable def laurentParameterEquiv (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) : K ≃ₐ[k] L := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  let : IsFractionRing O L := inferInstanceAs
    (IsFractionRing (weightedValuation γ m hm hpm hγ).toValuation.integer L)
  refine { IsFractionRing.ringEquivOfRingEquiv
      (powerSeriesEquiv γ m hm hpm hγ π hπ) with commutes' := ?_ }
  intro c
  change IsFractionRing.ringEquivOfRingEquiv
      (powerSeriesEquiv γ m hm hpm hγ π hπ)
      (algebraMap (PowerSeries k) K (PowerSeries.C c)) = algebraMap k L c
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change (powerSeriesEval γ m hm hpm hγ π hπ (PowerSeries.C c) : L) = _
  exact (powerSeriesEvalAlgHom γ m hm hpm hγ π hπ).commutes c

@[simp]
theorem laurentParameterEquiv_algebraMap (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (f : PowerSeries k) :
    laurentParameterEquiv γ m hm hpm hγ π hπ
        (algebraMap (PowerSeries k) K f) =
      (powerSeriesEval γ m hm hpm hγ π hπ f : L) := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  let : IsFractionRing O L := inferInstanceAs
    (IsFractionRing (weightedValuation γ m hm hpm hγ).toValuation.integer L)
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (powerSeriesEquiv γ m hm hpm hγ π hπ) f

/-- The Laurent parameter preserves the normalized additive valuation. -/
theorem weightedOrder_laurentParameterEquiv (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) (f : K) :
    weightedOrder γ m (laurentParameterEquiv γ m hm hpm hγ π hπ f) = f.orderTop := by
  let : Fact (Irreducible ((X : K[X]) ^ p - X - C γ)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
  have he (a : PowerSeries k) :
      weightedOrder γ m (powerSeriesEval γ m hm hpm hγ π hπ a : L) =
        (a : K).orderTop := by
    by_cases ha : a = 0
    · simp [ha, weightedOrder_zero]
    · rw [weightedOrder_powerSeriesEval γ m hm hpm hγ π hπ ha,
        LaurentSeries.orderTop_coe_of_ne_zero ha]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (PowerSeries k) f
  rw [map_div₀, laurentParameterEquiv_algebraMap, laurentParameterEquiv_algebraMap]
  change (weightedValuation γ m hm hpm hγ) (_ / _) = (HahnSeries.addVal ℤ k) (_ / _)
  rw [AddValuation.map_div, AddValuation.map_div]
  exact congrArg₂ (· - ·) (he a) (he b)

/-- The parameter map is uniformly continuous for the two valuation topologies. -/
theorem uniformContinuous_laurentParameterEquiv (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) :
    letI := weightedValued γ m hm hpm hγ
    UniformContinuous (laurentParameterEquiv γ m hm hpm hγ π hπ) := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun q : K × K =>
    (laurentParameterEquiv γ m hm hpm hγ π hπ q.1,
      laurentParameterEquiv γ m hm hpm hγ π hπ q.2)) (𝓤 K) (𝓤 L)
  rw [LaurentSeries.orderTop_hasBasis_uniformity.tendsto_iff
    (weightedOrder_hasBasis_uniformity γ m hm hpm hγ)]
  intro n _
  refine ⟨n + 1, trivial, ?_⟩
  intro q hq
  change (n : WithTop ℤ) < weightedOrder γ m (_ - _)
  rw [← map_sub, weightedOrder_laurentParameterEquiv]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hq

/-- The inverse parameter map is uniformly continuous as well. -/
theorem uniformContinuous_laurentParameterEquiv_symm (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) :
    letI := weightedValued γ m hm hpm hγ
    UniformContinuous (laurentParameterEquiv γ m hm hpm hγ π hπ).symm := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun q : L × L =>
    ((laurentParameterEquiv γ m hm hpm hγ π hπ).symm q.1,
      (laurentParameterEquiv γ m hm hpm hγ π hπ).symm q.2)) (𝓤 L) (𝓤 K)
  rw [(weightedOrder_hasBasis_uniformity γ m hm hpm hγ).tendsto_iff
    LaurentSeries.orderTop_hasBasis_uniformity]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro q hq
  change (n : WithTop ℤ) ≤ (_ - _ : K).orderTop
  rw [← map_sub, ← weightedOrder_laurentParameterEquiv γ m hm hpm hγ π hπ,
    AlgEquiv.apply_symm_apply]
  exact le_of_lt hq

/-- Laurent-series coordinates give a homeomorphism for the canonical valuations. -/
noncomputable def laurentParameterHomeomorph (π : O)
    (hπ : weightedOrder γ m (π : L) = 1) :
    letI := weightedValued γ m hm hpm hγ
    K ≃ₜ L := by
  let := weightedValued γ m hm hpm hγ
  exact
    { (laurentParameterEquiv γ m hm hpm hγ π hπ).toEquiv with
      continuous_toFun := (uniformContinuous_laurentParameterEquiv γ m hm hpm hγ π hπ).continuous
      continuous_invFun :=
        (uniformContinuous_laurentParameterEquiv_symm γ m hm hpm hγ π hπ).continuous }

end Camina1997.ArtinSchreier
