/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ArtinSchreier.PositiveTail
public import Mathlib.Algebra.Field.ZMod

/-!
# Reduced Laurent Artin–Schreier parameters

Over the prime field, every Artin–Schreier class has a representative consisting
of a constant and finitely many poles whose orders are prime to the characteristic.

Reference: Camina (1997), Lemmas 2–3, p. 105.
-/

@[expose] public section

namespace Camina1997.ArtinSchreier

variable {p : ℕ} [Fact p.Prime]

local notation "K" => LaurentSeries (ZMod p)

/-- A Laurent parameter with only a constant and poles of order prime to p. -/
def IsReduced (f : K) : Prop :=
  (∀ i : ℤ, 0 < i → f.coeff i = 0) ∧
    ∀ n : ℕ, 0 < n → p ∣ n → f.coeff (-(n : ℤ)) = 0

theorem IsReduced.add {f g : K} (hf : IsReduced f) (hg : IsReduced g) :
    IsReduced (f + g) :=
  ⟨fun i hi => by simp [HahnSeries.coeff_add, hf.1 i hi, hg.1 i hi],
    fun n hn hd => by simp [HahnSeries.coeff_add, hf.2 n hn hd, hg.2 n hn hd]⟩

theorem IsReduced.sub {f g : K} (hf : IsReduced f) (hg : IsReduced g) :
    IsReduced (f - g) :=
  ⟨fun i hi => by simp [HahnSeries.coeff_sub, hf.1 i hi, hg.1 i hi],
    fun n hn hd => by simp [HahnSeries.coeff_sub, hf.2 n hn hd, hg.2 n hn hd]⟩
/-- Constants are reduced. -/
theorem isReduced_single_zero (a : ZMod p) : IsReduced (HahnSeries.single 0 a : K) := by
  constructor
  · intro i hi
    simp [ne_of_gt hi]
  · intro n hn _
    have hn' : -(n : ℤ) ≠ 0 := by omega
    simp [hn']
/-- A pole whose order is prime to p is already reduced. -/
theorem isReduced_single_neg {n : ℕ} (hn : 0 < n) (hpn : ¬p ∣ n) (a : ZMod p) :
    IsReduced (HahnSeries.single (-(n : ℤ)) a : K) := by
  constructor
  · intro i hi
    have hni : -(n : ℤ) ≠ i := by omega
    simp [Ne.symm hni]
  · intro m _ hpm
    have hnm : -(n : ℤ) ≠ -(m : ℤ) := by
      intro h
      have : n = m := by omega
      exact hpn (this ▸ hpm)
    simp [Ne.symm hnm]
/-- Frobenius multiplies a Laurent monomial's exponent by p and fixes its coefficient. -/
theorem single_pow_prime (i : ℤ) (a : ZMod p) :
    (HahnSeries.single i a : K) ^ p = HahnSeries.single ((p : ℤ) * i) a := by
  have ha : a ^ p = a := by
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective a
    exact map_natCast (frobenius (ZMod p) p) n
  rw [HahnSeries.single_pow, ha]
  simp
/-- One p-divisible pole is removed by an explicit Artin–Schreier coboundary. -/
theorem single_neg_mul_prime (n : ℕ) (a : ZMod p) :
    (HahnSeries.single (-((p * n : ℕ) : ℤ)) a : K) =
      HahnSeries.single (-(n : ℤ)) a +
        ((HahnSeries.single (-(n : ℤ)) a : K) ^ p -
          HahnSeries.single (-(n : ℤ)) a) := by
  rw [single_pow_prime]
  simp only [Nat.cast_mul, mul_neg]
  ring
/-- Repeated pole division constructs a reduced representative for every negative monomial. -/
theorem exists_reduced_single_neg (n : ℕ) (hn : 0 < n) (a : ZMod p) :
    ∃ r μ : K, IsReduced r ∧
      HahnSeries.single (-(n : ℤ)) a = r + (μ ^ p - μ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hpn : p ∣ n
    · obtain ⟨q, hq⟩ := hpn
      have hp : 1 < p := (Fact.out : p.Prime).one_lt
      have hq0 : 0 < q := by nlinarith
      have hqn : q < n := by nlinarith
      obtain ⟨r, μ, hr, hμ⟩ := ih q hqn hq0
      refine ⟨r, μ + HahnSeries.single (-(q : ℤ)) a, hr, ?_⟩
      rw [hq, single_neg_mul_prime, add_pow_char]
      linear_combination hμ
    · exact ⟨HahnSeries.single (-(n : ℤ)) a, 0,
        isReduced_single_neg hn hpn a, by simp [(Fact.out : p.Prime).ne_zero]⟩

/-- Removing the coefficient at an integral lower bound improves that bound by one. -/
theorem succ_le_orderTop_sub_single_coeff (f : K) (n : ℤ)
    (hf : (n : WithTop ℤ) ≤ f.orderTop) :
    ((n + 1 : ℤ) : WithTop ℤ) ≤
      (f - HahnSeries.single n (f.coeff n)).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro i hi
  have hi' : i < n + 1 := WithTop.coe_lt_coe.mp hi
  by_cases hin : i = n
  · subst i
    simp
  · have hil : i < n := by omega
    have hfi : f.coeff i = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr hil).trans_le hf)
    simp [HahnSeries.coeff_sub, hfi, hin]
/-- A finite pole bound permits elimination of all nonreduced terms. -/
theorem exists_reduced_of_orderTop_ge (N : ℕ) (f : K)
    (hf : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ f.orderTop) :
    ∃ r μ : K, IsReduced r ∧ f = r + (μ ^ p - μ) := by
  induction N generalizing f with
  | zero =>
    have hf0 : (0 : WithTop ℤ) ≤ f.orderTop := by simpa using hf
    have htail : 0 < (f - HahnSeries.single 0 (f.coeff 0)).orderTop :=
      (by norm_num : (0 : WithTop ℤ) < 1).trans_le
        (by simpa using succ_le_orderTop_sub_single_coeff f 0 hf0)
    obtain ⟨μ, _, hμ⟩ := LaurentSeries.exists_pos_orderTop_pow_sub_eq (p := p) htail
    refine ⟨HahnSeries.single 0 (f.coeff 0), μ, isReduced_single_zero _, ?_⟩
    rw [hμ]
    abel
  | succ N ih =>
    let a := f.coeff (-((N + 1 : ℕ) : ℤ))
    let g : K := f - HahnSeries.single (-((N + 1 : ℕ) : ℤ)) a
    have hg : ((-(N : ℤ) : ℤ) : WithTop ℤ) ≤ g.orderTop := by
      have h := succ_le_orderTop_sub_single_coeff f (-((N + 1 : ℕ) : ℤ)) hf
      have he : -((N + 1 : ℕ) : ℤ) + 1 = -(N : ℤ) := by push_cast; ring
      rw [he] at h
      exact h
    obtain ⟨r, μ, hr, hμ⟩ := ih g hg
    obtain ⟨s, ν, hs, hν⟩ := exists_reduced_single_neg (N + 1) (by omega) a
    refine ⟨r + s, μ + ν, hr.add hs, ?_⟩
    rw [add_pow_char]
    dsimp [g] at hμ
    push_cast at hν
    linear_combination hμ + hν
/-- Every Laurent Artin–Schreier class has a reduced representative. -/
theorem exists_reduced (f : K) :
    ∃ r μ : K, IsReduced r ∧ f = r + (μ ^ p - μ) := by
  apply exists_reduced_of_orderTop_ge f.order.natAbs f
  by_cases hf : f = 0
  · simp [hf]
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hf]
    have h : -(f.order.natAbs : ℤ) ≤ f.order := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le _
    exact_mod_cast h
/-- At a pole, the p-th power is the unique lowest-order term of an Artin–Schreier image. -/
theorem orderTop_pow_sub_of_order_neg {x : K} (hx : x.order < 0) :
    (x ^ p - x).orderTop = (((p : ℤ) * x.order : ℤ) : WithTop ℤ) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hxord : x.orderTop = (x.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hx0).symm
  have hpord : (x ^ p).orderTop = (((p : ℤ) * x.order : ℤ) : WithTop ℤ) := by
    rw [LaurentSeries.orderTop_pow, hxord]
    norm_cast
  have hlt : (x ^ p).orderTop < x.orderTop := by
    rw [hpord, hxord]
    have hp : (1 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact_mod_cast (show (p : ℤ) * x.order < x.order by nlinarith)
  rw [HahnSeries.orderTop_sub hlt, hpord]
/-- A reduced Artin–Schreier image cannot come from a Laurent series with a pole. -/
theorem nonneg_order_of_isReduced_pow_sub {x : K} (hx : IsReduced (x ^ p - x)) :
    0 ≤ x.order := by
  by_contra h
  have hn : x.order < 0 := by omega
  have hm : 0 < p * x.order.natAbs :=
    Nat.mul_pos (Fact.out : p.Prime).pos (by omega)
  have he : -((p * x.order.natAbs : ℕ) : ℤ) = (p : ℤ) * x.order := by
    rw [Nat.cast_mul, Int.natCast_natAbs, abs_of_neg hn]
    ring
  have hc := hx.2 (p * x.order.natAbs) hm (dvd_mul_right p _)
  rw [he] at hc
  exact HahnSeries.coeff_orderTop_ne (orderTop_pow_sub_of_order_neg hn) hc
/-- Artin–Schreier images of integral Laurent series have positive order over F_p. -/
theorem pos_orderTop_pow_sub_of_nonneg {x : K} (hx : 0 ≤ x.orderTop) :
    0 < (x ^ p - x).orderTop := by
  let y : K := x - HahnSeries.single 0 (x.coeff 0)
  have hy : (1 : WithTop ℤ) ≤ y.orderTop := by
    simpa [y] using succ_le_orderTop_sub_single_coeff x 0 hx
  have hyp : 0 < y.orderTop := (by norm_num : (0 : WithTop ℤ) < 1).trans_le hy
  have hypow : 0 < (y ^ p).orderTop := by
    rw [LaurentSeries.orderTop_pow]
    exact nsmul_pos hyp (Fact.out : p.Prime).ne_zero
  have he : y ^ p - y = x ^ p - x := by
    dsimp [y]
    rw [sub_pow_char, single_pow_prime]
    simp only [mul_zero]
    ring
  rw [← he]
  exact (lt_min hypow hyp).trans_le HahnSeries.min_orderTop_le_orderTop_sub
/-- A reduced Artin–Schreier coboundary is zero. -/
theorem IsReduced.eq_zero_of_pow_sub {r x : K} (hr : IsReduced r)
    (hx : x ^ p - x = r) : r = 0 := by
  have hxo : 0 ≤ x.order := nonneg_order_of_isReduced_pow_sub (hx ▸ hr)
  have hxt : (0 : WithTop ℤ) ≤ x.orderTop := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hx0]
      exact_mod_cast hxo
  have hrt : 0 < r.orderTop := hx ▸ pos_orderTop_pow_sub_of_nonneg hxt
  ext i
  by_cases hi : 0 < i
  · simpa using hr.1 i hi
  · have hil : (i : WithTop ℤ) < r.orderTop :=
      (show (i : WithTop ℤ) ≤ 0 by exact_mod_cast (le_of_not_gt hi)).trans_lt hrt
    simpa using HahnSeries.coeff_eq_zero_of_lt_orderTop hil
/-- Reduced representatives in one Artin–Schreier class are equal. -/
theorem IsReduced.eq_of_sub_eq_pow_sub {r s μ : K} (hr : IsReduced r) (hs : IsReduced s)
    (h : r - s = μ ^ p - μ) : r = s :=
  sub_eq_zero.mp ((hr.sub hs).eq_zero_of_pow_sub h.symm)
/-- Every Artin–Schreier class over F_p((t)) has a unique reduced representative. -/
theorem existsUnique_reduced (f : K) :
    ∃! r : K, IsReduced r ∧ ∃ μ : K, f = r + (μ ^ p - μ) := by
  obtain ⟨r, μ, hr, hμ⟩ := exists_reduced f
  refine ⟨r, ⟨hr, μ, hμ⟩, ?_⟩
  rintro s ⟨hs, ν, hν⟩
  apply hs.eq_of_sub_eq_pow_sub hr (μ := μ - ν)
  rw [sub_pow_char]
  linear_combination hμ - hν
/-- The support of a reduced representative is finite. -/
theorem IsReduced.finite_support {r : K} (hr : IsReduced r) : r.support.Finite := by
  apply (Set.finite_Icc r.order 0).subset
  intro i hi
  have hc : r.coeff i ≠ 0 := hi
  exact ⟨HahnSeries.order_le_of_coeff_ne_zero hc, le_of_not_gt fun h => hc (hr.1 i h)⟩
/-- An integral reduced representative consists of its constant term. -/
theorem IsReduced.eq_single_of_order_nonneg {r : K} (hr : IsReduced r)
    (h : 0 ≤ r.order) : r = HahnSeries.single 0 (r.coeff 0) := by
  ext i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have hc : r.coeff i = 0 := HahnSeries.coeff_eq_zero_of_lt_order (hi.trans_le h)
    simp [hc, ne_of_lt hi]
  · simp
  · simp [hr.1 i hi, ne_of_gt hi]
/-- Every nonconstant reduced parameter has a leading pole of order prime to p. -/
theorem IsReduced.eq_single_or_exists_pole {r : K} (hr : IsReduced r) :
    r = HahnSeries.single 0 (r.coeff 0) ∨
      ∃ m : ℕ, 0 < m ∧ ¬p ∣ m ∧ r.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
  by_cases hn : r.order < 0
  · right
    have hr0 : r ≠ 0 := by rintro rfl; simp at hn
    have he : -(r.order.natAbs : ℤ) = r.order := by
      rw [Int.natCast_natAbs, abs_of_neg hn, neg_neg]
    refine ⟨r.order.natAbs, by omega, ?_, ?_⟩
    · intro hd
      have hc := hr.2 r.order.natAbs (by omega) hd
      rw [he, HahnSeries.coeff_order_eq_zero] at hc
      exact hr0 hc
    · rw [he, HahnSeries.order_eq_orderTop_of_ne_zero hr0]
  · exact Or.inl (hr.eq_single_of_order_nonneg (le_of_not_gt hn))

/-- A nonzero Artin–Schreier class has a nonzero reduced representative of nonpositive order. -/
theorem exists_reduced_of_not_image (f : K) (hf : ¬∃ μ : K, μ ^ p - μ = f) :
    ∃ r μ : K, IsReduced r ∧ f = r + (μ ^ p - μ) ∧ r ≠ 0 ∧ r.orderTop ≤ 0 := by
  obtain ⟨r, μ, hr, hμ⟩ := exists_reduced f
  have hr0 : r ≠ 0 := by
    intro hz
    exact hf ⟨μ, by simpa [hz] using hμ.symm⟩
  refine ⟨r, μ, hr, hμ, hr0, ?_⟩
  rcases hr.eq_single_or_exists_pole with he | ⟨m, hm, _, he⟩
  · have hc : r.coeff 0 ≠ 0 := by
      intro hc
      exact hr0 (by simpa [hc] using he)
    rw [he, HahnSeries.orderTop_single hc]
    exact le_rfl
  · rw [he]
    exact_mod_cast (show -(m : ℤ) ≤ 0 by omega)

end Camina1997.ArtinSchreier
