/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.ModEq

/-!
# Separation of sparse powers

Powers of a base greater than two have unique nonzero differences, even after
reduction modulo a larger power. This isolates the support of commutators in
the Lubotzky–Wilson wreath-product construction.

Reference: Lubotzky–Wilson (1984), p. 398. The arguments include the first
block starting at exponent zero and allow composite bases such as four.
-/

@[expose] public section

namespace Camina1997

/-- Zero followed by the powers of the base, in increasing order. -/
def sparseAtom (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => q ^ n

/-- Each sparse atom exceeds the sum of any two earlier atoms. -/
theorem sparseAtom_double_lt {q : ℕ} (hq : 2 < q) {i j : ℕ} (hij : i < j) :
    sparseAtom q i + sparseAtom q i < sparseAtom q j := by
  cases j with
  | zero => omega
  | succ j =>
    cases i with
    | zero => simpa [sparseAtom] using pow_pos (by omega : 0 < q) j
    | succ i =>
      change q ^ i + q ^ i < q ^ j
      have hi : i + 1 ≤ j := by omega
      have hp : 0 < q ^ i := pow_pos (by omega) _
      calc
        q ^ i + q ^ i < q ^ (i + 1) := by
          rw [pow_succ, ← mul_two]
          exact Nat.mul_lt_mul_of_pos_left hq hp
        _ ≤ q ^ j := Nat.pow_le_pow_right (by omega) hi

theorem sparseAtom_strictMono {q : ℕ} (hq : 2 < q) : StrictMono (sparseAtom q) := by
  intro i j hij
  have := sparseAtom_double_lt hq hij
  omega

/-- Two ordered sparse atoms determine their indices from their sum. -/
theorem sparseAtom_sum_ordered_injective {q : ℕ} (hq : 2 < q)
    {i j a b : ℕ} (hij : i ≤ j) (hab : a ≤ b)
    (he : sparseAtom q i + sparseAtom q j = sparseAtom q a + sparseAtom q b) :
    i = a ∧ j = b := by
  have hmono := (sparseAtom_strictMono hq).monotone
  have hjb : j = b := by
    rcases lt_trichotomy j b with hjb | hjb | hjb
    · have := sparseAtom_double_lt hq hjb
      have := hmono hij
      omega
    · exact hjb
    · have := sparseAtom_double_lt hq hjb
      have := hmono hab
      omega
  refine ⟨(sparseAtom_strictMono hq).injective ?_, hjb⟩
  rw [hjb] at he
  omega

/-- Sparse atoms form a Sidon set: their unordered pairs are determined by sums. -/
theorem sparseAtom_sum_injective {q : ℕ} (hq : 2 < q) {i j a b : ℕ}
    (he : sparseAtom q i + sparseAtom q j = sparseAtom q a + sparseAtom q b) :
    (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  rcases le_total i j with hij | hji <;> rcases le_total a b with hab | hba
  · exact Or.inl (sparseAtom_sum_ordered_injective hq hij hab he)
  · have h := sparseAtom_sum_ordered_injective hq hij hba (by omega)
    exact Or.inr ⟨h.1, h.2⟩
  · have h := sparseAtom_sum_ordered_injective hq hji hab (by omega)
    exact Or.inr ⟨h.2, h.1⟩
  · have h := sparseAtom_sum_ordered_injective hq hji hba (by omega)
    exact Or.inl ⟨h.2, h.1⟩

private def truncatedPowerIndex (s i : ℕ) : ℕ := if i ≤ s then i + 1 else 0

private theorem truncatedPowerIndex_le (s i : ℕ) : truncatedPowerIndex s i ≤ s + 1 := by
  unfold truncatedPowerIndex
  split_ifs <;> omega

private theorem natCast_sparseAtom_truncated (q s i : ℕ) :
    (sparseAtom q (truncatedPowerIndex s i) : ZMod (q ^ (s + 1))) =
      (q : ZMod (q ^ (s + 1))) ^ i := by
  unfold truncatedPowerIndex
  split_ifs with hi
  · simp [sparseAtom]
  · simpa [sparseAtom] using (ZMod.natCast_pow_eq_zero_of_le q (by omega : s + 1 ≤ i)).symm

private theorem sparseAtom_sum_lt_modulus {q : ℕ} (hq : 2 < q) {s i j : ℕ}
    (hi : i ≤ s + 1) (hj : j ≤ s + 1) :
    sparseAtom q i + sparseAtom q j < q ^ (s + 1) := by
  have hmono := (sparseAtom_strictMono hq).monotone
  have hi' := hmono hi
  have hj' := hmono hj
  have hlt := sparseAtom_double_lt hq (Nat.lt_succ_self (s + 1))
  change sparseAtom q i ≤ q ^ s at hi'
  change sparseAtom q j ≤ q ^ s at hj'
  change q ^ s + q ^ s < q ^ (s + 1) at hlt
  omega

/-- Two distinct translated sparse powers in one block force the translation to vanish. -/
theorem sparse_pow_shift_eq_zero {q s i j a b : ℕ} (hq : 2 < q)
    (ha : a ≤ s) (hb : b ≤ s) (hab : a ≠ b)
    (k : ZMod (q ^ (s + 1)))
    (hi : k + (q : ZMod (q ^ (s + 1))) ^ i = (q : ZMod (q ^ (s + 1))) ^ a)
    (hj : k + (q : ZMod (q ^ (s + 1))) ^ j = (q : ZMod (q ^ (s + 1))) ^ b) :
    i = a ∧ j = b ∧ k = 0 := by
  have he :
      (sparseAtom q (truncatedPowerIndex s i) + sparseAtom q (b + 1) : ℕ) =
        sparseAtom q (a + 1) + sparseAtom q (truncatedPowerIndex s j) := by
    have hc :
        ((sparseAtom q (truncatedPowerIndex s i) + sparseAtom q (b + 1) : ℕ) :
          ZMod (q ^ (s + 1))) =
        ((sparseAtom q (a + 1) + sparseAtom q (truncatedPowerIndex s j) : ℕ) :
          ZMod (q ^ (s + 1))) := by
      rw [Nat.cast_add, Nat.cast_add, natCast_sparseAtom_truncated, natCast_sparseAtom_truncated]
      change (q : ZMod (q ^ (s + 1))) ^ i + (q ^ b : ℕ) =
        (q ^ a : ℕ) + (q : ZMod (q ^ (s + 1))) ^ j
      simp only [Nat.cast_pow]
      rw [← hj, ← hi]
      ac_rfl
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hc).eq_of_lt_of_lt
      (sparseAtom_sum_lt_modulus hq (truncatedPowerIndex_le s i) (by omega))
      (sparseAtom_sum_lt_modulus hq (by omega) (truncatedPowerIndex_le s j))
  rcases sparseAtom_sum_injective hq he with ⟨hei, hej⟩ | ⟨hei, hej⟩
  · have hia : i = a := by
      unfold truncatedPowerIndex at hei
      split_ifs at hei; omega
    have hjb : j = b := by
      unfold truncatedPowerIndex at hej
      split_ifs at hej; omega
    refine ⟨hia, hjb, ?_⟩
    rw [hia] at hi
    exact add_right_cancel (hi.trans (zero_add _).symm)
  · exact (hab (by omega)).elim

/-- Powers within a block remain distinct modulo the next power of the base. -/
theorem sparse_pow_injective {q s a b : ℕ} (hq : 2 < q) (ha : a ≤ s) (hb : b ≤ s)
    (he : (q : ZMod (q ^ (s + 1))) ^ a = (q : ZMod (q ^ (s + 1))) ^ b) : a = b := by
  have hlt (i : ℕ) (hi : i ≤ s) : q ^ i < q ^ (s + 1) :=
    sparseAtom_strictMono hq (by omega : i + 1 < s + 1 + 1)
  have he' : (q ^ a : ℕ) = q ^ b :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa only [Nat.cast_pow] using he)).eq_of_lt_of_lt
      (hlt a ha) (hlt b hb)
  have hab : a + 1 = b + 1 := (sparseAtom_strictMono hq).injective he'
  omega

/-- Lubotzky–Wilson's sparse-power separation lemma, in the finite cyclic group.

Two distinct translates which both belong to one exponent block force both
original exponents to lie in that block and the translation to be zero.
-/
theorem sparse_powers_separation {q r s i j : ℕ} (hq : 2 < q)
    (k : ZMod (q ^ (s + 1)))
    (hi : ∃ a : ℕ, r < a ∧ a ≤ s ∧
      k + (q : ZMod (q ^ (s + 1))) ^ i = (q : ZMod (q ^ (s + 1))) ^ a)
    (hj : ∃ b : ℕ, r < b ∧ b ≤ s ∧
      k + (q : ZMod (q ^ (s + 1))) ^ j = (q : ZMod (q ^ (s + 1))) ^ b)
    (hne : k + (q : ZMod (q ^ (s + 1))) ^ i ≠
      k + (q : ZMod (q ^ (s + 1))) ^ j) :
    r < i ∧ i ≤ s ∧ r < j ∧ j ≤ s ∧ k = 0 := by
  obtain ⟨a, hra, has, hia⟩ := hi
  obtain ⟨b, hrb, hbs, hjb⟩ := hj
  have hab : a ≠ b := by
    rintro rfl
    exact hne (hia.trans hjb.symm)
  obtain ⟨rfl, rfl, hk⟩ := sparse_pow_shift_eq_zero hq has hbs hab k hia hjb
  exact ⟨hra, has, hrb, hbs, hk⟩

end Camina1997
