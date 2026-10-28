/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Congruence
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Displacement orders of normalized automorphisms

The leading exponent controls displacement when it is nonzero in the coefficient field.
These are the coefficient producers for Camina's Lemmas 4–5 (1997), pp. 106–107.
-/

@[expose] public section

namespace PowerSeries

variable {k : Type*} [Field k]

/-- A geometric sum of a series with constant coefficient one has constant coefficient
its length. -/
theorem constantCoeff_geom_sum {u : k⟦X⟧} (hu : constantCoeff u = 1) (m : ℕ) :
    constantCoeff (∑ i ∈ Finset.range m, u ^ i) = (m : k) := by
  simp [hu]

/-- The order of a monomial displacement is exact when its exponent is nonzero in the field. -/
theorem order_pow_sub_pow_of_linear_coeff_one {y : k⟦X⟧} {m n : ℕ}
    (hy0 : constantCoeff y = 0) (hy1 : coeff 1 y = 1)
    (hy : (y - X).order = ((n + 1 : ℕ) : ℕ∞)) (hm : (m : k) ≠ 0) :
    (y ^ m - X ^ m).order = ((m + n : ℕ) : ℕ∞) := by
  have hm0 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    exact hm (by simp [this])
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr hy0
  have hu0 : constantCoeff u = 1 := by
    rw [hu] at hy1
    simpa using hy1
  let S : k⟦X⟧ := ∑ i ∈ Finset.range m, u ^ i
  have hS : S.order = 0 := by
    apply order_eq_nat.mpr
    constructor
    · simpa [S, coeff_zero_eq_constantCoeff, hu0] using hm
    · intro i hi
      omega
  have he : y ^ m - X ^ m = X ^ (m - 1) * (y - X) * S := by
    rw [hu, mul_pow]
    have hg : (u - 1) * S = u ^ m - 1 := mul_geom_sum u m
    have hx : (X : k⟦X⟧) ^ m = X ^ (m - 1) * X := by
      rw [← pow_succ, Nat.sub_add_cancel hm0]
    rw [hx]
    linear_combination -(X ^ (m - 1) * X) * hg
  rw [he, order_mul, order_mul, order_X_pow, hy, hS]
  norm_cast
  omega

/-- Displacement of every series is bounded below by displacement of the parameter. -/
theorem le_order_algEquiv_sub (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) {n : ℕ}
    (hn : (n : ℕ∞) ≤ (e X - X).order) (f : k⟦X⟧) :
    (n : ℕ∞) ≤ (e f - f).order := by
  rw [nat_le_order_iff, ← X_pow_dvd_iff] at hn ⊢
  exact X_pow_dvd_algEquiv_sub e (AlgEquiv.refl) n hn f

/-- A leading exponent nonzero in the field gives exact displacement order. -/
theorem order_algEquiv_sub_of_order (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : IsNormalized e)
    {f : k⟦X⟧} {m n : ℕ} (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hf : f.order = (m : ℕ∞)) (hm : (m : k) ≠ 0) :
    (e f - f).order = ((m + n : ℕ) : ℕ∞) := by
  have hf0 : f ≠ 0 := by
    intro hz
    simp [hz] at hf
  let u := divXPowOrder f
  have hfu : f = X ^ m * u := by
    simpa [hf, u] using (X_pow_order_mul_divXPowOrder (f := f)).symm
  have hu0 : constantCoeff u ≠ 0 :=
    (constantCoeff_divXPowOrder_eq_zero_iff).not.mpr hf0
  have heu : (e u).order = 0 := by
    apply order_eq_nat.mpr
    constructor
    · simpa [coeff_zero_eq_constantCoeff] using hu0
    · intro i hi
      omega
  let A := ((e X) ^ m - X ^ m) * e u
  let B := X ^ m * (e u - u)
  have hA : A.order = ((m + n : ℕ) : ℕ∞) := by
    dsimp [A]
    rw [order_mul, heu, add_zero]
    exact order_pow_sub_pow_of_linear_coeff_one (constantCoeff_algEquiv_X e) he hδ hm
  have hB : ((m + n + 1 : ℕ) : ℕ∞) ≤ B.order := by
    have ht := le_order_algEquiv_sub e (le_of_eq hδ.symm) u
    dsimp [B]
    rw [order_mul, order_X_pow]
    convert add_le_add_left ht (m : ℕ∞) using 1 <;> push_cast <;> ac_rfl
  have hab : A.order < B.order := by
    rw [hA]
    have hlt : ((m + n : ℕ) : ℕ∞) < ((m + n + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.lt_succ_self (m + n)
    exact hlt.trans_le hB
  have hsum : e f - f = A + B := by
    rw [hfu, map_mul, map_pow]
    dsimp [A, B]
    ring
  rw [hsum, order_add_of_order_ne _ _ (ne_of_lt hab), min_eq_left hab.le, hA]

section CharacteristicP

variable {p : ℕ} [Fact p.Prime] [CharP k p]

local instance : CharP k⟦X⟧ p :=
  charP_of_injective_algebraMap (algebraMap k k⟦X⟧).injective p

omit [Fact p.Prime] [CharP k p] in
/-- Splitting into a Frobenius power and a prime-to-p leading term gives two displacement orders. -/
theorem displacement_orders_of_frobenius_split
    (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : IsNormalized e)
    {A B : k⟦X⟧} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hA : A.order = 1) (hB : B.order = (u : ℕ∞)) (hu : (u : k) ≠ 0) :
    ((e A - A) ^ p).order = ((p * (n + 1) : ℕ) : ℕ∞) ∧
      (e B - B).order = ((u + n : ℕ) : ℕ∞) := by
  refine ⟨?_, order_algEquiv_sub_of_order e he hδ hB hu⟩
  rw [order_pow, order_algEquiv_sub_of_order e he hδ hA (by simp)]
  simp [nsmul_eq_mul, mul_add, add_comm]

/-- The displacement of a Frobenius split is bounded by the smaller of the two leading orders. -/
theorem le_order_displacement_of_frobenius_split
    (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : IsNormalized e)
    {A B : k⟦X⟧} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hA : A.order = 1) (hB : B.order = (u : ℕ∞)) (hu : (u : k) ≠ 0) :
    min ((p * (n + 1) : ℕ) : ℕ∞) ((u + n : ℕ) : ℕ∞) ≤
      (e (A ^ p + B) - (A ^ p + B)).order := by
  obtain ⟨ha, hb⟩ := displacement_orders_of_frobenius_split e he hδ hA hB hu
  have heq : e (A ^ p + B) - (A ^ p + B) = (e A - A) ^ p + (e B - B) := by
    rw [map_add, map_pow, sub_pow_char]
    ring
  rw [heq]
  exact le_trans (by rw [ha, hb]) (min_order_le_order_add _ _)

/-- Distinct leading displacement orders cannot cancel. -/
theorem order_displacement_of_frobenius_split
    (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : IsNormalized e)
    {A B : k⟦X⟧} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hA : A.order = 1) (hB : B.order = (u : ℕ∞)) (hu : (u : k) ≠ 0)
    (hne : p * (n + 1) ≠ u + n) :
    (e (A ^ p + B) - (A ^ p + B)).order =
      min ((p * (n + 1) : ℕ) : ℕ∞) ((u + n : ℕ) : ℕ∞) := by
  obtain ⟨ha, hb⟩ := displacement_orders_of_frobenius_split e he hδ hA hB hu
  have heq : e (A ^ p + B) - (A ^ p + B) = (e A - A) ^ p + (e B - B) := by
    rw [map_add, map_pow, sub_pow_char]
    ring
  rw [heq, order_add_of_order_ne _ _ (by rw [ha, hb]; exact_mod_cast hne), ha, hb]

/-- A fixed degree-p split forces equality of the two possible displacement orders. -/
theorem first_exponent_eq_of_fixed_frobenius_split
    (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : IsNormalized e)
    {A B : k⟦X⟧} {u n : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hA : A.order = 1) (hB : B.order = (u : ℕ∞)) (hu : (u : k) ≠ 0)
    (hfix : e (A ^ p + B) = A ^ p + B) : u = n * (p - 1) + p := by
  have hbal : p * (n + 1) = u + n := by
    by_contra hne
    have ho := order_displacement_of_frobenius_split e he hδ hA hB hu hne
    have hfinite : (e (A ^ p + B) - (A ^ p + B)).order ≠ ⊤ := by
      rw [ho]
      simp
    exact hfinite (by rw [hfix, sub_self, order_zero])
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp
  nlinarith

/-- Below the new degree-p ramification break, the depth is unchanged. -/
theorem depth_eq_of_frobenius_split
    (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (he : IsNormalized e)
    {A B : k⟦X⟧} {u n r d : ℕ}
    (hδ : (e X - X).order = ((n + 1 : ℕ) : ℕ∞))
    (hA : A.order = 1) (hB : B.order = (u : ℕ∞)) (hu : (u : k) ≠ 0)
    (hur : u = r * (p - 1) + p) (hrd : d < r)
    (hord : (e (A ^ p + B) - (A ^ p + B)).order = ((p * (d + 1) : ℕ) : ℕ∞)) :
    n = d := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  have hnr : n < r := by
    by_contra! hnr
    have h₁ : p * (d + 1) < p * (n + 1) := by nlinarith
    have h₂ : p * (d + 1) < u + n := by nlinarith
    have hlo := le_order_displacement_of_frobenius_split e he hδ hA hB hu
    rw [hord] at hlo
    have hlt : ((p * (d + 1) : ℕ) : ℕ∞) <
        min ((p * (n + 1) : ℕ) : ℕ∞) ((u + n : ℕ) : ℕ∞) :=
      lt_min (by exact_mod_cast h₁) (by exact_mod_cast h₂)
    exact not_lt_of_ge hlo hlt
  have hlt : p * (n + 1) < u + n := by nlinarith
  have ho := order_displacement_of_frobenius_split e he hδ hA hB hu hlt.ne
  rw [hord, min_eq_left (by exact_mod_cast hlt.le)] at ho
  have heq : p * (d + 1) = p * (n + 1) := by exact_mod_cast ho
  nlinarith

end CharacteristicP

end PowerSeries
