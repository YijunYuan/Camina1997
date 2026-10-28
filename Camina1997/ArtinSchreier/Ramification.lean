/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Completeness

/-!
# Ramification of cyclic Artin–Schreier translations

The translations of the adjoined root preserve the explicit weighted valuation.
A uniformizer obtained from a Bézout relation computes their ramification depth.

Reference: Camina (1997), p. 108.
-/

@[expose] public section

open Polynomial Filter
open scoped Uniformity

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
variable (γ : LaurentSeries k) (m : ℕ)

local notation "K" => LaurentSeries k
local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "y" => AdjoinRoot.root ((X : K[X]) ^ p - X - C γ)


/-- The weighted order satisfies the lower bound for a finite sum. -/
theorem le_weightedOrder_sum {ι : Type*} (s : Finset ι) (f : ι → L)
    {q : WithTop ℤ} (hf : ∀ i ∈ s, q ≤ weightedOrder γ m (f i)) :
    q ≤ weightedOrder γ m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
      (min_weightedOrder_le_add γ m _ _)

/-- The weighted order of powers is additive in the exponent. -/
theorem weightedOrder_pow (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (x : L) (n : ℕ) :
    weightedOrder γ m (x ^ n) = n • weightedOrder γ m x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, weightedOrder_mul γ m hm hpm hγ, ih, succ_nsmul]

/-- A nonzero constant has Laurent order zero. -/
theorem orderTop_laurent_algebraMap {c : k} (hc : c ≠ 0) :
    (algebraMap k K c).orderTop = 0 := by
  rw [HahnSeries.algebraMap_apply']
  simpa using HahnSeries.orderTop_single (a := (0 : ℤ)) hc

/-- Every constant has nonnegative Laurent order. -/
theorem nonneg_orderTop_laurent_algebraMap (c : k) :
    (0 : WithTop ℤ) ≤ (algebraMap k K c).orderTop := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [orderTop_laurent_algebraMap hc]

variable [CharP k p]

/-- Prime-field constants in the Laurent field agree with the coefficient-field inclusion. -/
theorem castHom_laurent (c : ZMod p) :
    ZMod.castHom (dvd_refl p) K c =
      algebraMap k K (ZMod.castHom (dvd_refl p) k c) := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective c
  simp only [map_natCast]

/-- Prime-field constants have nonnegative weighted order in the extension. -/
theorem nonneg_weightedOrder_primeField (c : ZMod p) :
    (0 : WithTop ℤ) ≤ weightedOrder (p := p) γ m
      (algebraMap K L (ZMod.castHom (dvd_refl p) K c)) := by
  rw [weightedOrder_algebraMap, castHom_laurent]
  exact nsmul_nonneg (nonneg_orderTop_laurent_algebraMap _) _

/-- A nonzero prime-field constant has weighted order zero. -/
theorem weightedOrder_primeField {c : ZMod p} (hc : c ≠ 0) :
    weightedOrder (p := p) γ m
      (algebraMap K L (ZMod.castHom (dvd_refl p) K c)) = 0 := by
  rw [weightedOrder_algebraMap, castHom_laurent,
    orderTop_laurent_algebraMap (by simpa only [map_zero] using (ZMod.castHom_injective k).ne hc)]
  simp

/-- Translation does not change the weighted order of the root. -/
theorem weightedOrder_translation_root (hm : 0 < m) (c : ZMod p) :
    weightedOrder (p := p) γ m (translation γ c y) = (-(m : ℤ) : WithTop ℤ) := by
  rw [translation_root, weightedOrder_add_eq_left, weightedOrder_root]
  apply lt_of_lt_of_le _ (nonneg_weightedOrder_primeField γ m c)
  rw [weightedOrder_root]
  exact_mod_cast (show -(m : ℤ) < 0 by omega)

omit [CharP k p] in
/-- An automorphism preserving the root weight cannot decrease any weighted order. -/
theorem weightedOrder_le_algEquiv (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))
    (e : L ≃ₐ[K] L) (he : weightedOrder γ m (e y) = weightedOrder γ m y)
    (x : L) : weightedOrder γ m x ≤ weightedOrder γ m (e x) := by
  have ht (a : K) (i : Fin p) :
      weightedOrder γ m (e (a • y ^ (i : ℕ))) =
        termWeight (p := p) m i a := by
    rw [map_smul, map_pow, weightedOrder_smul,
      weightedOrder_pow γ m hm hpm hγ, he,
      ← weightedOrder_pow γ m hm hpm hγ y, weightedOrder_root_pow_lt γ m i.isLt]
    rfl
  rw [← sum_rootBasis_repr γ x, map_sum]
  apply le_weightedOrder_sum
  intro i _
  rw [ht]
  simpa only [sum_rootBasis_repr] using weightedOrder_le_term γ m x i

/-- Every cyclic translation preserves the weighted order. -/
theorem weightedOrder_translation (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (c : ZMod p) (x : L) :
    weightedOrder γ m (translation γ c x) = weightedOrder γ m x := by
  have h (d : ZMod p) (z : L) :
      weightedOrder γ m z ≤ weightedOrder γ m (translation γ d z) :=
    weightedOrder_le_algEquiv γ m hm hpm hγ (translation γ d)
      ((weightedOrder_translation_root γ m hm d).trans (weightedOrder_root γ m).symm) z
  apply le_antisymm
  · have h' := h (-c) (translation γ c x)
    have hinv : translation γ (-c) (translation γ c x) = x :=
      (translation γ c).symm_apply_apply x
    rwa [hinv] at h'
  · exact h c x

/-- Translation preserves every weighted-valuation entourage. -/
theorem uniformContinuous_translation (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (c : ZMod p) :
    letI := weightedValued γ m hm hpm hγ
    UniformContinuous (translation γ c) := by
  let := weightedValued γ m hm hpm hγ
  change Tendsto (fun q : L × L => (translation γ c q.1, translation γ c q.2))
    (𝓤 L) (𝓤 L)
  rw [(weightedOrder_hasBasis_uniformity γ m hm hpm hγ).tendsto_iff
    (weightedOrder_hasBasis_uniformity γ m hm hpm hγ)]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro q hq
  change (n : WithTop ℤ) <
    weightedOrder γ m (translation γ c q.2 - translation γ c q.1)
  rw [← map_sub, weightedOrder_translation γ m hm hpm hγ]
  exact hq

/-- Translation is continuous for the valuation topology. -/
theorem continuous_translation (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (c : ZMod p) :
    letI := weightedValued γ m hm hpm hγ
    Continuous (translation γ c) := by
  let := weightedValued γ m hm hpm hγ
  exact (uniformContinuous_translation γ m hm hpm hγ c).continuous

omit [CharP k p] in
/-- A nonzero coefficient-field constant times a basis vector has the expected weight. -/
theorem weightedOrder_const_smul_root_pow {d : k} (hd : d ≠ 0) {i : ℕ} (hi : i < p) :
    weightedOrder γ m (algebraMap k K d • y ^ i) =
      ((-(m : ℤ) * i : ℤ) : WithTop ℤ) := by
  rw [weightedOrder_smul_root_pow γ m _ ⟨i, hi⟩, termWeight,
    orderTop_laurent_algebraMap hd]
  simp
omit [CharP k p] in
/-- Constant multiples of a basis vector have at least its weight. -/
theorem le_weightedOrder_const_smul_root_pow (d : k) {i : ℕ} (hi : i < p) :
    ((-(m : ℤ) * i : ℤ) : WithTop ℤ) ≤
      weightedOrder γ m (algebraMap k K d • y ^ i) := by
  by_cases hd : d = 0
  · simp [hd]
  · exact (weightedOrder_const_smul_root_pow γ m hd hi).ge

/-- The first nonzero term of a translated root power has degree one lower. -/
theorem weightedOrder_root_add_const_pow_sub (hm : 0 < m)
    {n : ℕ} (hn : n + 1 < p) {d : k} (hd : d ≠ 0) :
    weightedOrder γ m
      ((y + algebraMap K L (algebraMap k K d)) ^ (n + 1) - y ^ (n + 1)) =
        ((-(m : ℤ) * n : ℤ) : WithTop ℤ) := by
  let f : ℕ → L := fun i =>
    algebraMap k K (d ^ (n + 1 - i) * ((n + 1).choose i : k)) • y ^ i
  have hexpand :
      (y + algebraMap K L (algebraMap k K d)) ^ (n + 1) - y ^ (n + 1) =
        ∑ i ∈ Finset.range (n + 1), f i := by
    rw [add_pow, Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      add_sub_cancel_right]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    simp only [Algebra.smul_def, map_mul, map_pow, map_natCast, AdjoinRoot.algebraMap_eq]
    ring
  have hnc : ((n + 1 : ℕ) : k) ≠ 0 := by
    intro hz
    have hdiv : p ∣ n + 1 := (CharP.cast_eq_zero_iff k p _).mp hz
    have := Nat.le_of_dvd (by omega : 0 < n + 1) hdiv
    omega
  have hfn : weightedOrder γ m (f n) = ((-(m : ℤ) * n : ℤ) : WithTop ℤ) := by
    dsimp [f]
    simp only [Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right]
    exact weightedOrder_const_smul_root_pow γ m (mul_ne_zero hd hnc) (by omega)
  have hfne : f n ≠ 0 := by
    intro hz
    rw [hz, weightedOrder_zero] at hfn
    exact WithTop.coe_ne_top hfn.symm
  rw [hexpand, weightedOrder_sum_eq_of_unique_least γ m (Finset.range (n + 1)) f
    (Finset.mem_range.mpr (by omega)) hfne, hfn]
  intro i hi hni
  rw [hfn]
  have hi' := Finset.mem_range.mp hi
  have hlt : (-(m : ℤ) * n : ℤ) < -(m : ℤ) * i := by
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have hin : (i : ℤ) < n := by omega
    nlinarith
  exact (WithTop.coe_lt_coe.mpr hlt).trans_le
    (le_weightedOrder_const_smul_root_pow γ m _ (by omega))

omit [CharP k p] in
/-- A Laurent monomial times a root power, used to choose a uniformizer. -/
noncomputable def rootMonomial (a : ℤ) (b : ℕ) : L :=
  (HahnSeries.single a 1 : K) • y ^ b
omit [CharP k p] in
/-- The weight of a root monomial is the corresponding integral linear combination. -/
theorem weightedOrder_rootMonomial (a : ℤ) {b : ℕ} (hb : b < p) :
    weightedOrder γ m (rootMonomial (p := p) γ a b) =
      (((p : ℤ) * a - (m : ℤ) * b : ℤ) : WithTop ℤ) := by
  rw [rootMonomial, weightedOrder_smul_root_pow γ m _ ⟨b, hb⟩, termWeight,
    HahnSeries.orderTop_single one_ne_zero]
  norm_cast
  simp [sub_eq_add_neg]
omit [CharP k p] in
/-- Bézout gives a positive root exponent below the characteristic for a uniformizer. -/
theorem exists_uniformizer_exponents (hpm : ¬p ∣ m) :
    ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ b < p ∧ (p : ℤ) * a - (m : ℤ) * b = 1 := by
  obtain ⟨a, i, hi⟩ := exists_weight_decomposition (p := p) m hpm 1
  refine ⟨a, i, ?_, i.isLt, hi⟩
  by_contra! hz
  have hiz : (i : ℕ) = 0 := by omega
  have ha : (p : ℤ) * a = 1 := by simpa only [hiz, Nat.cast_zero, mul_zero, sub_zero] using hi
  have hp : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rcases le_or_gt a 0 with h | h <;> nlinarith
omit [CharP k p] in
/-- The explicit Bézout monomial has weighted order one. -/
theorem weightedOrder_rootMonomial_eq_one (a : ℤ) {b : ℕ} (hb : b < p)
    (hab : (p : ℤ) * a - (m : ℤ) * b = 1) :
    weightedOrder γ m (rootMonomial (p := p) γ a b) = 1 := by
  rw [weightedOrder_rootMonomial γ m a hb, hab]
  rfl

/-- A nonidentity translation moves the explicit uniformizer by weighted order m+1. -/
theorem weightedOrder_translation_sub_uniformizer (hm : 0 < m)
    (a : ℤ) {b : ℕ} (hb0 : 0 < b) (hb : b < p)
    (hab : (p : ℤ) * a - (m : ℤ) * b = 1)
    {c : ZMod p} (hc : c ≠ 0) :
    weightedOrder γ m
      (translation γ c (rootMonomial (p := p) γ a b) - rootMonomial (p := p) γ a b) =
      ((m + 1 : ℕ) : WithTop ℤ) := by
  cases b with
  | zero => omega
  | succ n =>
    rw [rootMonomial, map_smul, map_pow, translation_root, ← smul_sub,
      weightedOrder_smul, castHom_laurent,
      weightedOrder_root_add_const_pow_sub γ m hm hb
        (by simpa only [map_zero] using (ZMod.castHom_injective k).ne hc),
      HahnSeries.orderTop_single one_ne_zero]
    norm_cast
    have he : (p : ℤ) * a + (-(m : ℤ) * n) = m + 1 := by
      push_cast at hab
      nlinarith
    simpa [nsmul_eq_mul] using he


/-- A reduced pole admits an explicit uniformizer with the prescribed translation depth. -/
theorem exists_uniformizer_translation_depth (hm : 0 < m) (hpm : ¬p ∣ m) :
    ∃ π : L, weightedOrder γ m π = 1 ∧
      ∀ c : ZMod p, c ≠ 0 →
        weightedOrder γ m (translation γ c π - π) = ((m + 1 : ℕ) : WithTop ℤ) := by
  obtain ⟨a, b, hb0, hb, hab⟩ := exists_uniformizer_exponents (p := p) m hpm
  refine ⟨rootMonomial γ a b, weightedOrder_rootMonomial_eq_one γ m a hb hab, ?_⟩
  intro c hc
  exact weightedOrder_translation_sub_uniformizer γ m hm a hb0 hb hab hc

end Camina1997.ArtinSchreier
