/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Ramification

/-!
# Valuation preservation by semilinear automorphisms

An automorphism of a reduced Artin–Schreier extension which restricts to a
valuation-preserving automorphism of the Laurent base preserves the explicit
weighted valuation. The defining equation determines the weight of the image
of the root; the canonical polynomial basis then determines every weight.

This supplies the valuation-preservation step in Camina (1997), Theorem 3,
p. 105, without assuming uniqueness of extensions of valuations.
-/

@[expose] public section

open Polynomial Filter
open scoped Uniformity

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries k) (m : ℕ)
variable (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "y" => AdjoinRoot.root ((X : K[X]) ^ p - X - C γ)

include hm hpm hγ

/-- The Artin–Schreier equation determines the negative weight of its root. -/
theorem weightedOrder_eq_of_pow_sub (z : L)
    (hz : weightedOrder γ m (z ^ p - z) = p • (-(m : ℤ) : WithTop ℤ)) :
    weightedOrder γ m z = (-(m : ℤ) : WithTop ℤ) := by
  have hp : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hneg : p • (-(m : ℤ) : WithTop ℤ) < 0 := by
    norm_cast
    simp only [nsmul_eq_mul]
    nlinarith
  have hzt : weightedOrder γ m z ≠ ⊤ := by
    intro ht
    have he := (weightedOrder_eq_top γ m z).mp ht
    rw [he, zero_pow (Fact.out : p.Prime).ne_zero, sub_zero, weightedOrder_zero] at hz
    exact not_lt_of_ge le_top (hz.trans_lt hneg)
  lift weightedOrder γ m z to ℤ using hzt with n hn
  have hpow : weightedOrder γ m (z ^ p) = (((p : ℤ) * n : ℤ) : WithTop ℤ) := by
    rw [weightedOrder_pow γ m hm hpm hγ, ← hn]
    norm_cast
  have hnneg : n < 0 := by
    by_contra! hnneg
    have hnonneg : (0 : WithTop ℤ) ≤ weightedOrder γ m (z ^ p - z) := by
      rw [sub_eq_add_neg]
      apply le_trans _ (min_weightedOrder_le_add γ m (z ^ p) (-z))
      rw [weightedOrder_neg, ← hn, hpow]
      exact le_min (by exact_mod_cast mul_nonneg (Int.natCast_nonneg p) hnneg)
        (by exact_mod_cast hnneg)
    exact not_lt_of_ge hnonneg (hz.trans_lt hneg)
  have hlt : weightedOrder γ m (z ^ p) < weightedOrder γ m (-z) := by
    rw [weightedOrder_neg, ← hn, hpow]
    exact_mod_cast (show (p : ℤ) * n < n by nlinarith)
  have heq : (p : ℤ) * n = (p : ℤ) * -(m : ℤ) := by
    rw [sub_eq_add_neg, weightedOrder_add_eq_left γ m hlt, hpow] at hz
    exact_mod_cast hz
  exact_mod_cast (show n = -(m : ℤ) by nlinarith)

/-- A semilinear lift of a valuation-preserving base map preserves the root's weight. -/
theorem weightedOrder_semilinear_root (e : L →+* L) (s : K →+* K)
    (hes : ∀ a : K, e (algebraMap K L a) = algebraMap K L (s a))
    (hs : ∀ a : K, (s a).orderTop = a.orderTop) :
    weightedOrder γ m (e y) = (-(m : ℤ) : WithTop ℤ) := by
  apply weightedOrder_eq_of_pow_sub γ m hm hpm hγ
  rw [← map_pow, ← map_sub, root_pow_sub, hes, weightedOrder_algebraMap, hs, hγ]

/-- A semilinear lift preserves the weight of each polynomial-basis term. -/
theorem weightedOrder_semilinear_basis_term (e : L →+* L) (s : K →+* K)
    (hes : ∀ a : K, e (algebraMap K L a) = algebraMap K L (s a))
    (hs : ∀ a : K, (s a).orderTop = a.orderTop) (a : K) (i : Fin p) :
    weightedOrder γ m (e (a • y ^ (i : ℕ))) = termWeight (p := p) m i a := by
  rw [Algebra.smul_def, map_mul, hes, map_pow,
    weightedOrder_mul γ m hm hpm hγ, weightedOrder_algebraMap, hs,
    weightedOrder_pow γ m hm hpm hγ,
    weightedOrder_semilinear_root γ m hm hpm hγ e s hes hs]
  rw [termWeight]
  congr 1
  norm_cast
  simp [mul_comm]

/-- A semilinear lift cannot decrease weighted order. -/
theorem weightedOrder_le_semilinear (e : L →+* L) (s : K →+* K)
    (hes : ∀ a : K, e (algebraMap K L a) = algebraMap K L (s a))
    (hs : ∀ a : K, (s a).orderTop = a.orderTop) (x : L) :
    weightedOrder γ m x ≤ weightedOrder γ m (e x) := by
  conv_rhs => rw [← sum_rootBasis_repr γ x, map_sum]
  apply le_weightedOrder_sum
  intro i _
  rw [weightedOrder_semilinear_basis_term γ m hm hpm hγ e s hes hs]
  exact weightedOrder_le_term γ m x i

/-- Every semilinear automorphism over a valuation-preserving base automorphism is isometric. -/
theorem weightedOrder_semilinear (e : L ≃+* L) (s : K ≃+* K)
    (hes : ∀ a : K, e (algebraMap K L a) = algebraMap K L (s a))
    (hs : ∀ a : K, (s a).orderTop = a.orderTop) (x : L) :
    weightedOrder γ m (e x) = weightedOrder γ m x := by
  have hinv (a : K) : e.symm (algebraMap K L a) = algebraMap K L (s.symm a) := by
    apply e.injective
    rw [e.apply_symm_apply, hes, s.apply_symm_apply]
  have hsinv (a : K) : (s.symm a).orderTop = a.orderTop := by
    simpa only [s.apply_symm_apply] using (hs (s.symm a)).symm
  apply le_antisymm
  · simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e.symm_apply_apply] using
      weightedOrder_le_semilinear γ m hm hpm hγ e.symm.toRingHom s.symm.toRingHom
        hinv hsinv (e x)
  · exact weightedOrder_le_semilinear γ m hm hpm hγ e.toRingHom s.toRingHom hes hs x

/-- The semilinear automorphism preserves every entourage of the weighted valuation. -/
theorem uniformContinuous_semilinear (e : L ≃+* L) (s : K ≃+* K)
    (hes : ∀ a : K, e (algebraMap K L a) = algebraMap K L (s a))
    (hs : ∀ a : K, (s a).orderTop = a.orderTop) :
    letI := weightedValued γ m hm hpm hγ
    UniformContinuous e := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun q : L × L => (e q.1, e q.2)) (𝓤 L) (𝓤 L)
  rw [(weightedOrder_hasBasis_uniformity γ m hm hpm hγ).tendsto_iff
    (weightedOrder_hasBasis_uniformity γ m hm hpm hγ)]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro q hq
  change (n : WithTop ℤ) < weightedOrder γ m (e q.2 - e q.1)
  rw [← map_sub, weightedOrder_semilinear γ m hm hpm hγ e s hes hs]
  exact hq

end Camina1997.ArtinSchreier
