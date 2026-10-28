/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Valuation
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Completeness of the weighted Artin–Schreier extension

The quotient coordinates identify its valuation uniformity with a finite product
of Laurent-series uniformities. Completeness follows from Laurent-series completeness.
-/

@[expose] public section

open Polynomial Filter
open scoped Uniformity

namespace Valued

open MonoidWithZeroHom.ValueGroup₀

/-- For a surjective valuation, the ambient value group itself indexes the entourages. -/
theorem hasBasis_uniformity_of_surjective {R Γ : Type*} [Ring R]
    [LinearOrderedCommGroupWithZero Γ] [h : Valued R Γ]
    (hs : Function.Surjective h.v) :
    (𝓤 R).HasBasis (fun _ : Γˣ => True)
      (fun a => {q : R × R | h.v (q.2 - q.1) < a.val}) := by
  apply (hasBasis_uniformity R Γ).to_hasBasis
  · intro a _
    refine ⟨Units.map (embedding (f := (h.v : R →*₀ Γ))) a, trivial, ?_⟩
    intro q hq
    exact (h.v.restrict_lt_iff_lt_embedding).mpr hq
  · intro a _
    obtain ⟨x, hx⟩ := hs a.val
    have hz : h.v.restrict x ≠ 0 := by
      intro hz
      have := congrArg (embedding (f := (h.v : R →*₀ Γ))) hz
      simp only [h.v.embedding_restrict, map_zero, hx] at this
      exact a.ne_zero this
    refine ⟨Units.mk0 (h.v.restrict x) hz, trivial, ?_⟩
    intro q hq
    change h.v.restrict (q.2 - q.1) < h.v.restrict x at hq
    simpa only [hx, Set.mem_ofPred_eq] using h.v.restrict_lt_iff.mp hq

end Valued

namespace LaurentSeries

open scoped WithZero

variable {k : Type*} [Field k]

/-- The multiplicative Laurent valuation and additive series order define the same bounds. -/
theorem valuation_le_exp_iff_orderTop (f : LaurentSeries k) (n : ℤ) :
    Valued.v f ≤ WithZero.exp (-n) ↔ (n : WithTop ℤ) ≤ f.orderTop := by
  rw [valuation_le_iff_coeff_lt_eq_zero k, HahnSeries.le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- Integer lower bounds on order form a basis of the Laurent-series uniformity. -/
theorem orderTop_hasBasis_uniformity :
    (𝓤 (LaurentSeries k)).HasBasis (fun _ : ℤ => True)
      (fun n => {q : LaurentSeries k × LaurentSeries k |
        (n : WithTop ℤ) ≤ (q.2 - q.1).orderTop}) := by
  apply (Valued.hasBasis_uniformity_of_surjective (valuation_surjective k)).to_hasBasis
  · intro a _
    refine ⟨-WithZero.log a.val + 1, trivial, ?_⟩
    intro q hq
    have h := (valuation_le_exp_iff_orderTop (q.2 - q.1) _).mpr hq
    exact h.trans_lt ((WithZero.lt_log_iff_exp_lt a.ne_zero).mp (by omega))
  · intro n _
    refine ⟨Units.mk0 (WithZero.exp (-n)) WithZero.exp_ne_zero, trivial, ?_⟩
    intro q hq
    exact (valuation_le_exp_iff_orderTop (q.2 - q.1) n).mp (le_of_lt hq)

end LaurentSeries

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries k) (m : ℕ)

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "Γ₀" => Multiplicative (WithTop ℤ)ᵒᵈ

/-- The valued-ring structure determined by the explicit weighted valuation. -/
@[instance_reducible]
noncomputable def weightedValued (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) : Valued L Γ₀ :=
  Valued.mk' (weightedValuation γ m hm hpm hγ).toValuation

variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

/-- Integer lower bounds on the weighted order form the valuation uniformity. -/
theorem weightedOrder_hasBasis_uniformity :
    let := weightedValued γ m hm hpm hγ
    (𝓤 L).HasBasis (fun _ : ℤ => True)
      (fun n => {q : L × L | (n : WithTop ℤ) < weightedOrder γ m (q.2 - q.1)}) := by
  let := weightedValued γ m hm hpm hγ
  have hs : Function.Surjective (Valued.v (R := L)) :=
    weightedValuation_surjective γ m hm hpm hγ
  apply (Valued.hasBasis_uniformity_of_surjective hs).to_hasBasis
  · intro a _
    have ha : (OrderDual.ofDual (Multiplicative.toAdd a.val) : WithTop ℤ) ≠ ⊤ :=
      a.ne_zero
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ha
    refine ⟨n, trivial, ?_⟩
    intro q hq
    change OrderDual.ofDual (Multiplicative.toAdd a.val) <
      weightedOrder γ m (q.2 - q.1)
    rwa [← hn]
  · intro n _
    let a : Γ₀ := Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ))
    refine ⟨Units.mk0 a (by exact WithTop.coe_ne_top), trivial, ?_⟩
    intro q hq
    exact hq

/-- Every coordinate of the quotient basis is uniformly continuous. -/
theorem uniformContinuous_rootBasis_coord (i : Fin p) :
    letI := weightedValued γ m hm hpm hγ
    UniformContinuous (fun x : L => (rootBasis γ).repr x i) := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun q : L × L =>
    ((rootBasis γ).repr q.1 i, (rootBasis γ).repr q.2 i)) (𝓤 L) (𝓤 K)
  rw [(weightedOrder_hasBasis_uniformity γ m hm hpm hγ).tendsto_iff
    LaurentSeries.orderTop_hasBasis_uniformity]
  intro n _
  refine ⟨(p : ℤ) * n - (m : ℤ) * i, trivial, ?_⟩
  intro q hq
  have ht := hq.trans_le (weightedOrder_le_term γ m (q.2 - q.1) i)
  simp only [map_sub, Finsupp.sub_apply] at ht
  by_cases hz : (rootBasis γ).repr q.2 i - (rootBasis γ).repr q.1 i = 0
  · simp only [Set.mem_ofPred_eq, hz, HahnSeries.orderTop_zero, le_top]
  · rw [termWeight_of_ne_zero m i hz, WithTop.coe_lt_coe] at ht
    change (n : WithTop ℤ) ≤
      ((rootBasis γ).repr q.2 i - (rootBasis γ).repr q.1 i).orderTop
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_le_coe]
    have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    nlinarith

/-- Each fixed basis term is uniformly continuous in its Laurent-series coefficient. -/
theorem uniformContinuous_smul_root_pow (i : Fin p) :
    letI := weightedValued γ m hm hpm hγ
    UniformContinuous (fun a : K =>
      a • AdjoinRoot.root ((X : K[X]) ^ p - X - C γ) ^ (i : ℕ)) := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun q : K × K =>
    (q.1 • AdjoinRoot.root ((X : K[X]) ^ p - X - C γ) ^ (i : ℕ),
      q.2 • AdjoinRoot.root ((X : K[X]) ^ p - X - C γ) ^ (i : ℕ))) (𝓤 K) (𝓤 L)
  rw [LaurentSeries.orderTop_hasBasis_uniformity.tendsto_iff
    (weightedOrder_hasBasis_uniformity γ m hm hpm hγ)]
  intro n _
  refine ⟨max n 0 + (m : ℤ) * i + 1, trivial, ?_⟩
  intro q hq
  change (n : WithTop ℤ) < weightedOrder γ m _
  rw [← sub_smul, weightedOrder_smul_root_pow]
  by_cases hz : q.2 - q.1 = 0
  · simp [hz]
  · rw [termWeight_of_ne_zero m i hz, WithTop.coe_lt_coe]
    change ((max n 0 + (m : ℤ) * i + 1 : ℤ) : WithTop ℤ) ≤
      (q.2 - q.1).orderTop at hq
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz, WithTop.coe_le_coe] at hq
    have hp : (1 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hmi : (0 : ℤ) ≤ (m : ℤ) * i := by positivity
    have hmax := le_max_left n 0
    have hmax0 := le_max_right n 0
    nlinarith

/-- Coordinates give a uniform equivalence with a finite product of complete Laurent fields. -/
noncomputable def rootBasisUniformEquiv :
    letI := weightedValued γ m hm hpm hγ
    L ≃ᵤ (Fin p → K) := by
  let := weightedValued γ m hm hpm hγ
  refine
    { (rootBasis γ).equivFun.toEquiv with
      uniformContinuous_toFun := ?_
      uniformContinuous_invFun := ?_ }
  · exact uniformContinuous_pi.mpr (fun i => uniformContinuous_rootBasis_coord γ m hm hpm hγ i)
  · have hsum : UniformContinuous (fun f : Fin p → K =>
        ∑ i : Fin p, f i • AdjoinRoot.root ((X : K[X]) ^ p - X - C γ) ^ (i : ℕ)) :=
      Finset.uniformContinuous_sum _ (fun i _ =>
        (uniformContinuous_smul_root_pow γ m hm hpm hγ i).comp
          (Pi.uniformContinuous_proj (fun _ : Fin p => K) i))
    convert hsum using 1
    funext f
    have h := (rootBasis γ).sum_equivFun ((rootBasis γ).equivFun.symm f)
    change (rootBasis γ).equivFun.symm f = _
    simpa only [LinearEquiv.apply_symm_apply, rootBasis_apply] using h.symm

/-- The actual reduced-pole quotient is complete for its weighted valuation. -/
theorem weightedValued_completeSpace :
    letI := weightedValued γ m hm hpm hγ
    CompleteSpace L := by
  let := weightedValued γ m hm hpm hγ
  exact (rootBasisUniformEquiv γ m hm hpm hγ).completeSpace_iff.mpr inferInstance

end Camina1997.ArtinSchreier
