/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Laurent
public import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# The weighted valuation of an Artin–Schreier extension

The canonical polynomial basis defines a weighted order on the actual quotient
field. A pole of order prime to the characteristic makes the least weight unique.

Reference: Camina (1997), Lemma 3 and its following note, p. 105.
-/

@[expose] public section

open Polynomial

namespace Camina1997.ArtinSchreier

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]

local notation "K" => LaurentSeries k

/-- The weight of one coefficient times the `i`th power of the adjoined root. -/
noncomputable def termWeight (m i : ℕ) (a : K) : WithTop ℤ :=
  p • a.orderTop + ((-(m : ℤ) * i : ℤ) : WithTop ℤ)

@[simp]
theorem termWeight_zero (m i : ℕ) : termWeight (p := p) m i (0 : K) = ⊤ := by
  have hp : p = (p - 1) + 1 := by have := (Fact.out : p.Prime).pos; omega
  rw [termWeight, HahnSeries.orderTop_zero, hp, succ_nsmul]
  simp only [WithTop.add_top, WithTop.top_add]

omit [Fact p.Prime] in
theorem termWeight_of_ne_zero (m i : ℕ) {a : K} (ha : a ≠ 0) :
    termWeight (p := p) m i a = (((p : ℤ) * a.order - (m : ℤ) * i : ℤ) : WithTop ℤ) := by
  rw [termWeight, ← HahnSeries.order_eq_orderTop_of_ne_zero ha]
  norm_cast
  simp [sub_eq_add_neg]

@[simp]
theorem termWeight_eq_top (m i : ℕ) (a : K) : termWeight (p := p) m i a = ⊤ ↔ a = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [termWeight_of_ne_zero m i ha]
    exact iff_of_false WithTop.coe_ne_top ha

omit [Fact p.Prime] in
theorem min_termWeight_le_add (m i : ℕ) (a b : K) :
    min (termWeight (p := p) m i a) (termWeight (p := p) m i b) ≤
      termWeight (p := p) m i (a + b) := by
  have hm : Monotone (fun q : WithTop ℤ => p • q + ((-(m : ℤ) * i : ℤ) : WithTop ℤ)) :=
    fun _ _ h => add_le_add (nsmul_le_nsmul_right h p) le_rfl
  exact hm.map_min.symm.le.trans
    (hm HahnSeries.min_orderTop_le_orderTop_add)

omit [Fact p.Prime] in
@[simp]
theorem termWeight_neg (m i : ℕ) (a : K) :
    termWeight (p := p) m i (-a) = termWeight (p := p) m i a := by
  simp [termWeight]

omit [Fact p.Prime] in
theorem termWeight_mul (m i : ℕ) (a b : K) :
    termWeight (p := p) m i (a * b) = p • a.orderTop + termWeight (p := p) m i b := by
  simp only [termWeight, HahnSeries.orderTop_mul, nsmul_add, add_assoc]

/-- Distinct basis indices have distinct finite weights when the pole is reduced. -/
theorem termWeight_eq_imp_index_eq {m : ℕ} (hpm : ¬p ∣ m) {i j : Fin p}
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : termWeight (p := p) m i a = termWeight (p := p) m j b) : i = j := by
  rw [termWeight_of_ne_zero m i ha, termWeight_of_ne_zero m j hb,
    WithTop.coe_eq_coe] at h
  have hd : (p : ℤ) ∣ (m : ℤ) * ((i : ℤ) - j) :=
    ⟨a.order - b.order, by nlinarith [h]⟩
  have hpm' : ¬(p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpm
  obtain ⟨q, hq⟩ := ((Int.Prime.dvd_mul' (Fact.out : p.Prime) hd).resolve_left hpm')
  have hip : (i : ℤ) < p := by exact_mod_cast i.isLt
  have hjp : (j : ℤ) < p := by exact_mod_cast j.isLt
  have hi : (0 : ℤ) ≤ i := by positivity
  have hj : (0 : ℤ) ≤ j := by positivity
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hq0 : q = 0 := by
    rcases lt_trichotomy q 0 with hneg | hzero | hpos
    · have : q ≤ -1 := by omega
      nlinarith
    · exact hzero
    · have : 1 ≤ q := by omega
      nlinarith
  apply Fin.ext
  have : (i : ℤ) = j := by rw [hq0, mul_zero] at hq; omega
  exact_mod_cast this

variable (γ : LaurentSeries k) (m : ℕ)

local notation "L" => AdjoinRoot ((X : K[X]) ^ p - X - C γ)
local notation "y" => AdjoinRoot.root ((X : K[X]) ^ p - X - C γ)

/-- The least weighted order among the canonical quotient coordinates. -/
noncomputable def weightedOrder (x : L) : WithTop ℤ :=
  Finset.univ.inf fun i : Fin p => termWeight (k := k) (p := p) m i ((rootBasis γ).repr x i)

theorem weightedOrder_le_term (x : L) (i : Fin p) :
    weightedOrder γ m x ≤ termWeight (k := k) (p := p) m i ((rootBasis γ).repr x i) :=
  Finset.inf_le (Finset.mem_univ i)

theorem le_weightedOrder_iff (x : L) (q : WithTop ℤ) :
    q ≤ weightedOrder γ m x ↔
      ∀ i : Fin p, q ≤ termWeight (k := k) (p := p) m i ((rootBasis γ).repr x i) := by
  simp [weightedOrder, Finset.le_inf_iff]

@[simp]
theorem weightedOrder_zero : weightedOrder (p := p) γ m 0 = ⊤ := by
  simp [weightedOrder]

@[simp]
theorem weightedOrder_eq_top (x : L) : weightedOrder γ m x = ⊤ ↔ x = 0 := by
  rw [eq_top_iff, le_weightedOrder_iff]
  simp only [top_le_iff, termWeight_eq_top]
  constructor
  · intro h
    apply (rootBasis γ).repr.injective
    apply Finsupp.ext
    intro i
    simpa using h i
  · intro h
    simp [h]

theorem min_weightedOrder_le_add (x z : L) :
    min (weightedOrder γ m x) (weightedOrder γ m z) ≤ weightedOrder γ m (x + z) := by
  rw [le_weightedOrder_iff]
  intro i
  have h := min_le_min (weightedOrder_le_term γ m x i) (weightedOrder_le_term γ m z i)
  simpa only [map_add, Finsupp.add_apply] using h.trans (min_termWeight_le_add m i _ _)

@[simp]
theorem weightedOrder_neg (x : L) : weightedOrder γ m (-x) = weightedOrder γ m x := by
  simp [weightedOrder]

theorem weightedOrder_add_eq_left {x z : L}
    (h : weightedOrder γ m x < weightedOrder γ m z) :
    weightedOrder γ m (x + z) = weightedOrder γ m x := by
  apply le_antisymm
  · have ht := min_weightedOrder_le_add γ m (x + z) (-z)
    simp only [weightedOrder_neg, add_neg_cancel_right] at ht
    exact (min_le_iff.mp ht).resolve_right (not_le_of_gt h)
  · simpa only [min_eq_left_of_lt h] using min_weightedOrder_le_add γ m x z

/-- The finite minimum is attained by a quotient coordinate. -/
theorem exists_termWeight_eq (x : L) :
    ∃ i : Fin p, weightedOrder γ m x =
      termWeight (p := p) m i ((rootBasis γ).repr x i) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf (Finset.univ : Finset (Fin p))
    ⟨⟨0, (Fact.out : p.Prime).pos⟩, Finset.mem_univ _⟩
    (fun i => termWeight (p := p) m i ((rootBasis γ).repr x i))
  exact ⟨i, hi⟩

theorem weightedOrder_smul (a : K) (x : L) :
    weightedOrder γ m (a • x) = p • a.orderTop + weightedOrder γ m x := by
  have hc (i : Fin p) :
      termWeight (p := p) m i ((rootBasis γ).repr (a • x) i) =
        p • a.orderTop + termWeight (p := p) m i ((rootBasis γ).repr x i) := by
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
      termWeight_mul m i a ((rootBasis γ).repr x i)
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_termWeight_eq γ m x
    exact (weightedOrder_le_term γ m (a • x) i).trans_eq (by rw [hc, hi])
  · rw [le_weightedOrder_iff]
    intro i
    rw [hc]
    exact add_le_add le_rfl (weightedOrder_le_term γ m x i)

theorem weightedOrder_smul_root_pow (a : K) (i : Fin p) :
    weightedOrder γ m (a • y ^ (i : ℕ)) = termWeight (p := p) m i a := by
  have hc (j : Fin p) : (rootBasis γ).repr (a • y ^ (i : ℕ)) j =
      if i = j then a else 0 := by
    rw [← rootBasis_apply γ i]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
  apply le_antisymm
  · exact (weightedOrder_le_term γ m _ i).trans_eq (by rw [hc]; simp)
  · rw [le_weightedOrder_iff]
    intro j
    rw [hc]
    split_ifs with h
    · subst j; rfl
    · simp

theorem weightedOrder_algebraMap (a : K) :
    weightedOrder γ m (algebraMap K L a) = p • a.orderTop := by
  have h := weightedOrder_smul_root_pow γ m a ⟨0, (Fact.out : p.Prime).pos⟩
  simpa [Algebra.smul_def, termWeight] using h

@[simp]
theorem weightedOrder_one : weightedOrder (p := p) γ m 1 = 0 := by
  simpa using weightedOrder_algebraMap γ m (1 : K)

theorem weightedOrder_root : weightedOrder (p := p) γ m y = (-(m : ℤ) : WithTop ℤ) := by
  have h := weightedOrder_smul_root_pow γ m (1 : K) ⟨1, (Fact.out : p.Prime).one_lt⟩
  simpa [termWeight] using h

/-- A nonzero quotient element has one strictly least-weight coordinate. -/
theorem exists_unique_least_term (hpm : ¬p ∣ m) {x : L} (hx : x ≠ 0) :
    ∃ i : Fin p,
      (rootBasis γ).repr x i ≠ 0 ∧
      weightedOrder γ m x = termWeight (p := p) m i ((rootBasis γ).repr x i) ∧
      ∀ j : Fin p, j ≠ i →
        weightedOrder γ m x < termWeight (p := p) m j ((rootBasis γ).repr x j) := by
  obtain ⟨i, hi⟩ := exists_termWeight_eq γ m x
  have hxi : (rootBasis γ).repr x i ≠ 0 := by
    intro hz
    have : weightedOrder γ m x = ⊤ := by rw [hi, hz, termWeight_zero]
    exact hx ((weightedOrder_eq_top γ m x).mp this)
  refine ⟨i, hxi, hi, ?_⟩
  intro j hji
  apply lt_of_le_of_ne (weightedOrder_le_term γ m x j)
  intro he
  have hxj : (rootBasis γ).repr x j ≠ 0 := by
    intro hz
    have : weightedOrder γ m x = ⊤ := by rw [he, hz, termWeight_zero]
    exact hx ((weightedOrder_eq_top γ m x).mp this)
  exact hji (termWeight_eq_imp_index_eq hpm hxj hxi (he.symm.trans hi))

theorem lt_weightedOrder_sum {ι : Type*} (s : Finset ι) (f : ι → L)
    {q : WithTop ℤ} (hq : q < ⊤) (hf : ∀ i ∈ s, q < weightedOrder γ m (f i)) :
    q < weightedOrder γ m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hq
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (lt_min (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans_le
      (min_weightedOrder_le_add γ m _ _)

/-- A unique least-weight summand cannot cancel in a finite sum. -/
theorem weightedOrder_sum_eq_of_unique_least {ι : Type*}
    (s : Finset ι) (f : ι → L) {i : ι} (hi : i ∈ s)
    (hfi : f i ≠ 0)
    (hf : ∀ j ∈ s, j ≠ i → weightedOrder γ m (f i) < weightedOrder γ m (f j)) :
    weightedOrder γ m (∑ j ∈ s, f j) = weightedOrder γ m (f i) := by
  classical
  rw [← Finset.add_sum_erase s f hi]
  apply weightedOrder_add_eq_left
  apply lt_weightedOrder_sum
  · exact lt_top_iff_ne_top.mpr (fun h => hfi ((weightedOrder_eq_top γ m _).mp h))
  · intro j hj
    exact hf j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)

theorem weightedOrder_root_pow_lt {n : ℕ} (hn : n < p) :
    weightedOrder γ m (y ^ n) = ((-(m : ℤ) * n : ℤ) : WithTop ℤ) := by
  simpa [termWeight] using weightedOrder_smul_root_pow γ m (1 : K) ⟨n, hn⟩

omit [Fact p.Prime] in
/-- One use of the defining relation suffices to reduce a product of basis powers. -/
theorem root_pow_reduce {n : ℕ} (hn : p ≤ n) :
    y ^ n = y ^ (n - p + 1) + algebraMap K L γ * y ^ (n - p) := by
  have hy : y ^ p = y + algebraMap K L γ := by
    have h := root_pow_sub (p := p) γ
    linear_combination h
  calc
    y ^ n = y ^ p * y ^ (n - p) := by rw [← pow_add, Nat.add_sub_of_le hn]
    _ = y ^ (n - p + 1) + algebraMap K L γ * y ^ (n - p) := by
      rw [hy, pow_succ]
      ring

/-- Reduction of a basis product preserves its least weight. -/
theorem weightedOrder_root_pow_lt_two_mul (hm : 0 < m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))
    {n : ℕ} (hn : n < 2 * p - 1) :
    weightedOrder γ m (y ^ n) = ((-(m : ℤ) * n : ℤ) : WithTop ℤ) := by
  by_cases hnp : n < p
  · exact weightedOrder_root_pow_lt γ m hnp
  have hpn : p ≤ n := Nat.le_of_not_gt hnp
  have hlow : n - p < p := by omega
  have hhigh : n - p + 1 < p := by omega
  have hlowval : weightedOrder γ m (algebraMap K L γ * y ^ (n - p)) =
      ((-(m : ℤ) * n : ℤ) : WithTop ℤ) := by
    rw [← Algebra.smul_def, weightedOrder_smul, weightedOrder_root_pow_lt γ m hlow, hγ]
    norm_cast
    have he : (n : ℤ) = (p : ℤ) + (n - p : ℕ) := by exact_mod_cast (Nat.add_sub_of_le hpn).symm
    simp only [nsmul_eq_mul]
    nlinarith
  have hlt : weightedOrder γ m (algebraMap K L γ * y ^ (n - p)) <
      weightedOrder γ m (y ^ (n - p + 1)) := by
    rw [hlowval, weightedOrder_root_pow_lt γ m hhigh]
    apply WithTop.coe_lt_coe.mpr
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have hp' : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have he : (n : ℤ) = (p : ℤ) + (n - p : ℕ) := by exact_mod_cast (Nat.add_sub_of_le hpn).symm
    push_cast
    nlinarith
  rw [root_pow_reduce γ hpn, add_comm, weightedOrder_add_eq_left γ m hlt, hlowval]

/-- Each product of two basis terms has the sum of their weights. -/
theorem weightedOrder_mul_basis_terms (hm : 0 < m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ))
    (a b : K) (i j : Fin p) :
    weightedOrder γ m ((a • y ^ (i : ℕ)) * (b • y ^ (j : ℕ))) =
      termWeight (p := p) m i a + termWeight (p := p) m j b := by
  rw [smul_mul_smul_comm, ← pow_add, weightedOrder_smul,
    weightedOrder_root_pow_lt_two_mul γ m hm hγ (by omega), HahnSeries.orderTop_mul,
    nsmul_add]
  have hs : ((-(m : ℤ) * (((i : ℕ) + (j : ℕ) : ℕ) : ℤ) : ℤ) : WithTop ℤ) =
      ((-(m : ℤ) * i : ℤ) : WithTop ℤ) + ((-(m : ℤ) * j : ℤ) : WithTop ℤ) := by
    norm_cast
    push_cast
    ring
  rw [hs, termWeight, termWeight]
  ac_rfl

/-- The coordinate minimum is multiplicative; the least basis-product term survives reduction. -/
theorem weightedOrder_mul (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (x z : L) :
    weightedOrder γ m (x * z) = weightedOrder γ m x + weightedOrder γ m z := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hz : z = 0
  · simp [hz]
  have hxt : weightedOrder γ m x ≠ ⊤ := (weightedOrder_eq_top γ m x).not.mpr hx
  have hzt : weightedOrder γ m z ≠ ⊤ := (weightedOrder_eq_top γ m z).not.mpr hz
  obtain ⟨i, _, hi, hxi⟩ := exists_unique_least_term γ m hpm hx
  obtain ⟨j, _, hj, hzj⟩ := exists_unique_least_term γ m hpm hz
  let f : Fin p × Fin p → L := fun ij =>
    (((rootBasis γ).repr x ij.1) • y ^ (ij.1 : ℕ)) *
      (((rootBasis γ).repr z ij.2) • y ^ (ij.2 : ℕ))
  have hfval (ij : Fin p × Fin p) : weightedOrder γ m (f ij) =
      termWeight (p := p) m ij.1 ((rootBasis γ).repr x ij.1) +
        termWeight (p := p) m ij.2 ((rootBasis γ).repr z ij.2) :=
    weightedOrder_mul_basis_terms γ m hm hγ _ _ _ _
  have hfij : weightedOrder γ m (f (i, j)) = weightedOrder γ m x + weightedOrder γ m z := by
    rw [hfval, ← hi, ← hj]
  have hfij_ne : f (i, j) ≠ 0 := by
    intro he
    have ht := (weightedOrder_eq_top γ m (f (i, j))).mpr he
    rw [hfij, WithTop.add_eq_top] at ht
    exact ht.elim hxt hzt
  have hleast : ∀ ij ∈ (Finset.univ : Finset (Fin p × Fin p)), ij ≠ (i, j) →
      weightedOrder γ m (f (i, j)) < weightedOrder γ m (f ij) := by
    intro ij _ hij
    rw [hfij, hfval]
    by_cases hi' : ij.1 = i
    · have hj' : ij.2 ≠ j := by intro h; exact hij (Prod.ext hi' h)
      rw [hi', ← hi]
      exact WithTop.add_lt_add_left hxt (hzj ij.2 hj')
    · exact WithTop.add_lt_add_of_lt_of_le hzt (hxi ij.1 hi')
        (weightedOrder_le_term γ m z ij.2)
  have hprod : (∑ ij : Fin p × Fin p, f ij) = x * z := by
    simp only [f, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_rootBasis_repr, sum_rootBasis_repr]
  rw [← hprod, weightedOrder_sum_eq_of_unique_least γ m Finset.univ f
    (Finset.mem_univ (i, j)) hfij_ne hleast, hfij]

/-- The explicit additive valuation on the actual Artin–Schreier quotient. -/
noncomputable def weightedValuation (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) : AddValuation L (WithTop ℤ) :=
  AddValuation.of (weightedOrder γ m) (weightedOrder_zero γ m) (weightedOrder_one γ m)
    (min_weightedOrder_le_add γ m) (weightedOrder_mul γ m hm hpm hγ)

@[simp]
theorem weightedValuation_apply (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) (x : L) :
    weightedValuation γ m hm hpm hγ x = weightedOrder γ m x := rfl

/-- Reduced pole weights represent every integer with a basis index below `p`. -/
theorem exists_weight_decomposition (hpm : ¬p ∣ m) (n : ℤ) :
    ∃ a : ℤ, ∃ i : Fin p, (p : ℤ) * a - (m : ℤ) * i = n := by
  have hc : m.Coprime p := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpm).symm
  let b : ZMod p := (m : ZMod p)⁻¹ * -(n : ZMod p)
  have hd : (p : ℤ) ∣ n + (m : ℤ) * b.val := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp [b]
    rw [← mul_assoc, ZMod.coe_mul_inv_eq_one m hc, one_mul, add_neg_cancel]
  obtain ⟨a, ha⟩ := hd
  refine ⟨a, ⟨b.val, ZMod.val_lt b⟩, ?_⟩
  change (p : ℤ) * a - (m : ℤ) * b.val = n
  linarith

/-- A single basis term realizes any prescribed finite weighted order. -/
theorem exists_weightedOrder_eq (hpm : ¬p ∣ m) (n : ℤ) :
    ∃ x : L, weightedOrder γ m x = (n : WithTop ℤ) := by
  obtain ⟨a, i, hi⟩ := exists_weight_decomposition (p := p) m hpm n
  refine ⟨(HahnSeries.single a 1 : K) • y ^ (i : ℕ), ?_⟩
  rw [weightedOrder_smul_root_pow, termWeight, HahnSeries.orderTop_single one_ne_zero]
  norm_cast
  simpa [sub_eq_add_neg] using hi

/-- The weighted order has value group all of `ℤ`. -/
theorem weightedOrder_surjective (hpm : ¬p ∣ m) :
    Function.Surjective (weightedOrder (p := p) γ m) := by
  intro q
  induction q using WithTop.recTopCoe with
  | top => exact ⟨0, weightedOrder_zero γ m⟩
  | coe n => exact exists_weightedOrder_eq γ m hpm n

theorem weightedValuation_surjective (hm : 0 < m) (hpm : ¬p ∣ m)
    (hγ : γ.orderTop = (-(m : ℤ) : WithTop ℤ)) :
    Function.Surjective (weightedValuation (p := p) γ m hm hpm hγ) :=
  weightedOrder_surjective γ m hpm

end Camina1997.ArtinSchreier
