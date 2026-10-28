/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.Completeness
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-!
# Artin–Schreier equations for positive Laurent tails

For a Laurent series of positive order, the convergent sum of its iterated
Frobenius powers gives an explicit Artin–Schreier preimage of positive order.
-/

@[expose] public section

open Filter
open scoped Topology WithZero

namespace Valued

/-- A valued ring has a neighborhood basis of open additive subgroups. -/
theorem nonarchimedeanRing {R Γ : Type*} [Ring R]
    [LinearOrderedCommGroupWithZero Γ] [Valued R Γ] : NonarchimedeanRing R where
  is_nonarchimedean U hU := by
    obtain ⟨a, ha⟩ := mem_nhds_zero.mp hU
    exact ⟨⟨Valued.v.restrict.ltAddSubgroup a, isOpen_ball _ _⟩, ha⟩

end Valued

namespace LaurentSeries

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]


omit [Fact p.Prime] [CharP k p] in
/-- Positive integer-valued order is bounded below by one. -/
theorem one_le_orderTop_of_pos {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    (1 : WithTop ℤ) ≤ f.orderTop := by
  by_cases hz : f = 0
  · simp [hz]
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hz] at hf ⊢
    have h : (0 : ℤ) < f.order := by exact_mod_cast hf
    exact_mod_cast (show (1 : ℤ) ≤ f.order by omega)

omit [CharP k p] in
/-- Iterated Frobenius powers of a positive-order series converge to zero. -/
theorem tendsto_pow_prime_pow_zero {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    Tendsto (fun j : ℕ => f ^ (p ^ j)) atTop (𝓝 0) := by
  have hpow := Valued.tendsto_zero_pow_of_le_exp_neg_one
    ((valuation_le_exp_iff_orderTop f 1).mpr (one_le_orderTop_of_pos hf))
  have hp : Tendsto (fun j : ℕ => p ^ j) atTop atTop := by
    apply tendsto_atTop_mono (fun j => (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)
    exact tendsto_id
  exact hpow.comp hp

omit [CharP k p] in
/-- Positive-order iterated Frobenius powers are summable. -/
theorem summable_pow_prime_pow {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    Summable (fun j : ℕ => f ^ (p ^ j)) := by
  let : NonarchimedeanRing (LaurentSeries k) := Valued.nonarchimedeanRing
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_pow_prime_pow_zero hf


/-- The iterated Frobenius sum satisfies the telescoping Artin–Schreier identity. -/
theorem pow_tsum_prime_pow_sub {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    (∑' j : ℕ, f ^ (p ^ j)) ^ p - (∑' j : ℕ, f ^ (p ^ j)) = -f := by
  have hs := summable_pow_prime_pow (p := p) hf
  have hmap := hs.hasSum.map (frobenius (LaurentSeries k) p) (continuous_pow p)
  have hpow :
      (∑' j : ℕ, f ^ (p ^ j)) ^ p = ∑' j : ℕ, f ^ (p ^ (j + 1)) := by
    simpa only [Function.comp_def, frobenius_def, ← pow_mul, pow_succ] using hmap.tsum_eq.symm
  have hsum := hs.tsum_eq_zero_add
  simp only [pow_zero, pow_one] at hsum
  rw [hpow, hsum]
  ring


omit [Fact p.Prime] [CharP k p] in
/-- An integral lower bound on Laurent order defines a closed set. -/
theorem isClosed_orderTop_ge (n : ℤ) :
    IsClosed {f : LaurentSeries k | (n : WithTop ℤ) ≤ f.orderTop} := by
  have h := Valued.isClosed_closedBall (LaurentSeries k)
    (Valued.v.restrict (HahnSeries.single n 1 : LaurentSeries k))
  simpa only [Valuation.restrict_le_iff, valuation_single_zpow,
    valuation_le_exp_iff_orderTop] using h

omit [Fact p.Prime] [CharP k p] in
/-- Lower bounds on Laurent order are preserved by finite sums. -/
theorem le_orderTop_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries k)
    {n : WithTop ℤ} (hf : ∀ i ∈ s, n ≤ (f i).orderTop) :
    n ≤ (∑ i ∈ s, f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
      HahnSeries.min_orderTop_le_orderTop_add

omit [CharP k p] in
/-- The convergent iterated Frobenius sum still has positive order. -/
theorem pos_orderTop_tsum_prime_pow {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    0 < (∑' j : ℕ, f ^ (p ^ j)).orderTop := by
  have hs := summable_pow_prime_pow (p := p) hf
  have hb : (1 : WithTop ℤ) ≤ (∑' j : ℕ, f ^ (p ^ j)).orderTop := by
    apply (isClosed_orderTop_ge (k := k) 1).mem_of_tendsto hs.hasSum
    apply Filter.Eventually.of_forall
    intro s
    apply le_orderTop_sum
    intro j _
    have hp : 1 ≤ p ^ j := Nat.one_le_pow j p (Fact.out : p.Prime).pos
    calc
      (1 : WithTop ℤ) = 1 • (1 : WithTop ℤ) := by simp
      _ ≤ (p ^ j) • (1 : WithTop ℤ) := nsmul_le_nsmul_left (by positivity) hp
      _ ≤ (p ^ j) • f.orderTop := nsmul_le_nsmul_right (one_le_orderTop_of_pos hf) _
      _ = (f ^ (p ^ j)).orderTop := (orderTop_pow _ _).symm
  exact (by norm_num : (0 : WithTop ℤ) < 1).trans_le hb

/-- The negative sum of iterated Frobenius powers solves the positive-tail equation. -/
theorem artinSchreier_neg_tsum_prime_pow {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    (-(∑' j : ℕ, f ^ (p ^ j))) ^ p - (-(∑' j : ℕ, f ^ (p ^ j))) = f := by
  have hneg : (-(∑' j : ℕ, f ^ (p ^ j))) ^ p =
      -((∑' j : ℕ, f ^ (p ^ j)) ^ p) := map_neg (frobenius (LaurentSeries k) p) _
  rw [hneg]
  have h := congrArg Neg.neg (pow_tsum_prime_pow_sub (p := p) hf)
  simpa only [neg_neg, sub_eq_add_neg, neg_add_rev, add_comm] using h

/-- Every positive Laurent tail is an Artin–Schreier image of positive order. -/
theorem exists_pos_orderTop_pow_sub_eq {f : LaurentSeries k} (hf : 0 < f.orderTop) :
    ∃ h : LaurentSeries k, 0 < h.orderTop ∧ h ^ p - h = f := by
  refine ⟨-(∑' j : ℕ, f ^ (p ^ j)), ?_, artinSchreier_neg_tsum_prime_pow hf⟩
  simpa only [HahnSeries.orderTop_neg] using pos_orderTop_tsum_prime_pow (p := p) hf

end LaurentSeries
