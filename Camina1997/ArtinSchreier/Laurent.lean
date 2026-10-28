/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Camina1997.ArtinSchreier.Extension
public import Mathlib.Algebra.CharP.Algebra

/-!
# Artin–Schreier equations with a pole

A Laurent series whose pole has order prime to the characteristic cannot be
an Artin–Schreier image. Its Artin–Schreier quotient is therefore a cyclic
Galois extension of degree `p`. Ramification is a separate result.

Reference: Camina (1997), Theorem 1 and Lemma 3, pp. 103 and 105.
-/

@[expose] public section

namespace LaurentSeries

variable {k : Type*} [Field k]

instance instCharP {p : ℕ} [CharP k p] : CharP (LaurentSeries k) p :=
  charP_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective p

/-- The order of a power is the corresponding multiple of the order. -/
theorem orderTop_pow (x : LaurentSeries k) (n : ℕ) :
    (x ^ n).orderTop = n • x.orderTop := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, HahnSeries.orderTop_mul, ih, succ_nsmul]

/-- A pole of order prime to `p` obstructs a solution of `x ^ p - x = γ`.
The valuation argument only needs `1 < p`, so it also applies in other characteristics. -/
theorem pow_sub_ne_of_orderTop {p m : ℕ} (hp : 1 < p) (hm : 0 < m)
    (hpm : ¬p ∣ m) (γ : LaurentSeries k)
    (hγ : γ.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)) (x : LaurentSeries k) :
    x ^ p - x ≠ γ := by
  intro he
  have hval : (x ^ p - x).orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ) := he ▸ hγ
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, zero_pow (Nat.ne_zero_of_lt hp), sub_zero, HahnSeries.orderTop_zero] at hval
    exact WithTop.coe_ne_top hval.symm
  have hxord : x.orderTop = (x.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hx).symm
  have hpord : (x ^ p).orderTop = (((p : ℤ) * x.order : ℤ) : WithTop ℤ) := by
    rw [orderTop_pow, hxord]
    norm_cast
  by_cases hxneg : x.order < 0
  · have hlt : (x ^ p).orderTop < x.orderTop := by
      rw [hpord, hxord]
      exact_mod_cast (show (p : ℤ) * x.order < x.order by
        have hp' : (1 : ℤ) < p := by exact_mod_cast hp
        nlinarith)
    rw [HahnSeries.orderTop_sub hlt, hpord] at hval
    have heq : (p : ℤ) * x.order = -(m : ℤ) := WithTop.coe_injective hval
    have hdiv : (p : ℤ) ∣ (m : ℤ) := ⟨-x.order, by linarith⟩
    exact hpm (by exact_mod_cast hdiv)
  · have hxnonneg : (0 : WithTop ℤ) ≤ x.orderTop := by
      rw [hxord]
      exact_mod_cast le_of_not_gt hxneg
    have hpnonneg : (0 : WithTop ℤ) ≤ (x ^ p).orderTop := by
      rw [hpord]
      exact_mod_cast mul_nonneg (Int.natCast_nonneg p) (le_of_not_gt hxneg)
    have hnonneg := (le_min hpnonneg hxnonneg).trans
      (HahnSeries.min_orderTop_le_orderTop_sub (x := x ^ p) (y := x))
    rw [hval] at hnonneg
    have : (0 : ℤ) ≤ -(m : ℤ) := by exact_mod_cast hnonneg
    omega

/-- A negative pole of order prime to the characteristic produces an irreducible
Artin–Schreier polynomial over the Laurent field. -/
theorem irreducible_X_pow_sub_X_sub_C_of_orderTop {p m : ℕ} [Fact p.Prime] [CharP k p]
    (hm : 0 < m) (hpm : ¬p ∣ m) (γ : LaurentSeries k)
    (hγ : γ.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)) :
    Irreducible ((Polynomial.X : Polynomial (LaurentSeries k)) ^ p -
      Polynomial.X - Polynomial.C γ) :=
  Polynomial.irreducible_X_pow_sub_X_sub_C (p := p) γ
    (pow_sub_ne_of_orderTop (Fact.out : p.Prime).one_lt hm hpm γ hγ)

open Polynomial Camina1997.ArtinSchreier

/-- The reduced-pole criterion supplies a field structure on the concrete quotient. -/
theorem isField_adjoinRoot_of_orderTop {p m : ℕ} [Fact p.Prime] [CharP k p]
    (hm : 0 < m) (hpm : ¬p ∣ m) (γ : LaurentSeries k)
    (hγ : γ.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)) :
    IsField (AdjoinRoot (X ^ p - X - C γ)) :=
  isField_adjoinRoot γ (pow_sub_ne_of_orderTop (Fact.out : p.Prime).one_lt hm hpm γ hγ)

/-- The full automorphism group of a reduced-pole extension is the additive prime field. -/
noncomputable def automorphismEquivOfPole {p m : ℕ} [Fact p.Prime] [CharP k p]
    (hm : 0 < m) (hpm : ¬p ∣ m) (γ : LaurentSeries k)
    (hγ : γ.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)) :
    Multiplicative (ZMod p) ≃*
      (AdjoinRoot (X ^ p - X - C γ) ≃ₐ[LaurentSeries k] AdjoinRoot (X ^ p - X - C γ)) :=
  automorphismEquiv γ (pow_sub_ne_of_orderTop (Fact.out : p.Prime).one_lt hm hpm γ hγ)

/-- The concrete reduced-pole extension is Galois for its canonical quotient field structure. -/
theorem isGalois_adjoinRoot_of_orderTop {p m : ℕ} [Fact p.Prime] [CharP k p]
    (hm : 0 < m) (hpm : ¬p ∣ m) (γ : LaurentSeries k)
    (hγ : γ.orderTop = ((-(m : ℤ) : ℤ) : WithTop ℤ)) :
    letI : Fact (Irreducible (X ^ p - X - C γ)) :=
      ⟨irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm γ hγ⟩
    IsGalois (LaurentSeries k) (AdjoinRoot (X ^ p - X - C γ)) :=
  isGalois_adjoinRoot γ (pow_sub_ne_of_orderTop (Fact.out : p.Prime).one_lt hm hpm γ hγ)

end LaurentSeries
