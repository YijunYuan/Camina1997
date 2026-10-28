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

end Camina1997.ArtinSchreier
