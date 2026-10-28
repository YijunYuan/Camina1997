/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Data.ZMod.Basic

/-!
# Separating the Frobenius part of a prime-field power series

Separate the terms whose exponents are divisible by p from those whose
exponents are not. The former form a p-th power over the prime field.

Reference: Camina (1997), p. 106, the hypothesis preceding Lemma 4.
-/

@[expose] public section

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The coefficients at multiples of p, with exponents divided by p. -/
noncomputable def frobeniusRootPart (T : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  mk fun j => coeff (p * j) T

/-- The terms whose exponents are not divisible by p. -/
noncomputable def frobeniusRemainder (T : PowerSeries (ZMod p)) : PowerSeries (ZMod p) :=
  mk fun i => if p ∣ i then 0 else coeff i T

@[simp]
theorem coeff_frobeniusRootPart (T : PowerSeries (ZMod p)) (j : ℕ) :
    coeff j (frobeniusRootPart T) = coeff (p * j) T := coeff_mk _ _

@[simp]
theorem coeff_frobeniusRemainder (T : PowerSeries (ZMod p)) (i : ℕ) :
    coeff i (frobeniusRemainder T) = if p ∣ i then 0 else coeff i T := coeff_mk _ _

/-- Frobenius over the prime field multiplies every exponent by p. -/
theorem pow_prime_eq_expand (f : PowerSeries (ZMod p)) :
    f ^ p = expand p (Fact.out : p.Prime).ne_zero f := by
  simpa only [ZMod.card] using (FiniteField.PowerSeries.expand_card f).symm

/-- Coefficients of a p-th power over the prime field. -/
theorem coeff_pow_prime (f : PowerSeries (ZMod p)) (i : ℕ) :
    coeff i (f ^ p) = if p ∣ i then coeff (i / p) f else 0 := by
  rw [pow_prime_eq_expand, coeff_expand]

/-- Every prime-field power series splits canonically into its p-th power part and remainder. -/
theorem eq_frobeniusRootPart_pow_add (T : PowerSeries (ZMod p)) :
    T = frobeniusRootPart T ^ p + frobeniusRemainder T := by
  ext i
  rw [map_add, coeff_pow_prime, coeff_frobeniusRemainder]
  by_cases hi : p ∣ i
  · simp only [hi, ite_true, coeff_frobeniusRootPart, add_zero]
    rw [Nat.mul_div_cancel' hi]
  · simp [hi]

/-- A series of order p has Frobenius root part of order one. -/
theorem order_frobeniusRootPart_of_order_eq_prime {T : PowerSeries (ZMod p)}
    (hT : T.order = (p : ℕ∞)) : (frobeniusRootPart T).order = 1 := by
  obtain ⟨hp, hlt⟩ := order_eq_nat.mp hT
  apply order_eq_nat.mpr
  constructor
  · simpa using hp
  · intro i hi
    have : i = 0 := by omega
    subst i
    simpa using hlt 0 (Fact.out : p.Prime).pos

/-- The first nonzero coefficient at an exponent not divisible by p is the remainder's order. -/
theorem order_frobeniusRemainder {T : PowerSeries (ZMod p)} {u : ℕ}
    (hu : ¬p ∣ u) (hcoeff : coeff u T ≠ 0)
    (hlt : ∀ i < u, ¬p ∣ i → coeff i T = 0) :
    (frobeniusRemainder T).order = (u : ℕ∞) := by
  apply order_eq_nat.mpr
  constructor
  · simpa [hu] using hcoeff
  · intro i hi
    by_cases hpi : p ∣ i
    · simp [hpi]
    · simp [hpi, hlt i hi hpi]

/-- The remainder vanishes exactly for p-th powers. -/
theorem frobeniusRemainder_eq_zero_iff (T : PowerSeries (ZMod p)) :
    frobeniusRemainder T = 0 ↔ ∃ A : PowerSeries (ZMod p), A ^ p = T := by
  constructor
  · intro hT
    refine ⟨frobeniusRootPart T, ?_⟩
    simpa only [hT, add_zero] using (eq_frobeniusRootPart_pow_add T).symm
  · rintro ⟨A, rfl⟩
    ext i
    simp only [coeff_frobeniusRemainder, coeff_pow_prime, map_zero]
    split_ifs <;> rfl

/-- A series which is not a p-th power has a nonzero remainder. -/
theorem frobeniusRemainder_ne_zero {T : PowerSeries (ZMod p)}
    (hT : ∀ A : PowerSeries (ZMod p), A ^ p ≠ T) : frobeniusRemainder T ≠ 0 := by
  intro hzero
  obtain ⟨A, hA⟩ := (frobeniusRemainder_eq_zero_iff T).mp hzero
  exact hT A hA

/-- A series which is not a p-th power has a first nonzero term of exponent prime to p. -/
theorem exists_frobeniusRemainder_order {T : PowerSeries (ZMod p)}
    (hT : ∀ A : PowerSeries (ZMod p), A ^ p ≠ T) :
    ∃ u : ℕ, ¬p ∣ u ∧ coeff u T ≠ 0 ∧
      (∀ i < u, ¬p ∣ i → coeff i T = 0) ∧
      (frobeniusRemainder T).order = (u : ℕ∞) := by
  have hB := frobeniusRemainder_ne_zero hT
  have hc := coeff_order hB
  have hu : ¬p ∣ (frobeniusRemainder T).order.toNat := by
    intro hdiv
    simp [hdiv] at hc
  refine ⟨(frobeniusRemainder T).order.toNat, hu, ?_, ?_, ?_⟩
  · simpa [hu] using hc
  · intro i hi hpi
    have h := coeff_of_lt_order_toNat i hi
    simpa [hpi] using h
  · exact (coe_toNat_order hB).symm

/-- When the series starts in degree p, its first non-Frobenius term occurs strictly later. -/
theorem exists_frobeniusRemainder_order_gt_prime {T : PowerSeries (ZMod p)}
    (hord : T.order = (p : ℕ∞))
    (hT : ∀ A : PowerSeries (ZMod p), A ^ p ≠ T) :
    ∃ u : ℕ, p < u ∧ ¬p ∣ u ∧ coeff u T ≠ 0 ∧
      (frobeniusRemainder T).order = (u : ℕ∞) := by
  obtain ⟨u, hu, hc, _, hordB⟩ := exists_frobeniusRemainder_order hT
  refine ⟨u, ?_, hu, hc, hordB⟩
  by_contra hle
  have hle' : u ≤ p := by omega
  have hne : u ≠ p := by
    rintro rfl
    exact hu (dvd_refl _)
  exact hc ((order_eq_nat.mp hord).2 u (lt_of_le_of_ne hle' hne))

end PowerSeries
