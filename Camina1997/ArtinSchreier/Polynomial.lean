/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Artin–Schreier polynomials

Over a field of prime characteristic `p`, a polynomial `X ^ p - X - C a`
is irreducible if it has no root. The proof sums the roots of a prospective
proper factor and uses additivity of Frobenius.

Reference: Camina (1997), Theorem 1, p. 103.
-/

@[expose] public section

open scoped Polynomial

namespace Polynomial

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime]

/-- An Artin–Schreier polynomial is monic. -/
theorem monic_X_pow_sub_X_sub_C (a : F) : (X ^ p - X - C a).Monic := by
  rw [sub_sub]
  apply monic_X_pow_sub
  simpa using (show (1 : WithBot ℕ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- An Artin–Schreier polynomial has degree equal to the characteristic. -/
theorem natDegree_X_pow_sub_X_sub_C (a : F) : (X ^ p - X - C a).natDegree = p := by
  rw [sub_sub, natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simpa using (Fact.out : p.Prime).one_lt

variable [CharP F p]

/-- For a monic factor of an Artin–Schreier polynomial, its root sum satisfies
the same additive equation multiplied by the degree of the factor. -/
theorem pow_sub_neg_nextCoeff_of_dvd_artinSchreier (a : F) (q : F[X]) (hq : q.Monic)
    (hdiv : q ∣ X ^ p - X - C a) :
    (-q.nextCoeff) ^ p - (-q.nextCoeff) = (q.natDegree : F) * a := by
  classical
  let E := q.SplittingField
  let φ : F →+* E := algebraMap F E
  let r := (q.map φ).roots
  have hsplit : (q.map φ).Splits := SplittingField.splits q
  have hcard : r.card = q.natDegree := by
    rw [← hsplit.natDegree_eq_card_roots, hq.natDegree_map]
  have hsum : φ (-q.nextCoeff) = r.sum := by
    rw [map_neg, ← nextCoeff_map_eq q φ,
      hsplit.nextCoeff_eq_neg_sum_roots_of_monic (hq.map φ), neg_neg]
  have hroot (x : E) (hx : x ∈ r) : x ^ p - x = φ a := by
    have hxq : (q.map φ).eval x = 0 := (mem_roots (hq.map φ).ne_zero).mp hx
    have hxP : ((X ^ p - X - C a).map φ).eval x = 0 := by
      obtain ⟨b, hb⟩ := hdiv
      rw [hb, Polynomial.map_mul, eval_mul, hxq, zero_mul]
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub,
      eval_pow, eval_X, eval_C, sub_eq_zero] using hxP
  have hsumAS : r.sum ^ p - r.sum = (r.card : E) * φ a := by
    rw [multiset_sum_pow_char p]
    calc
      (r.map (fun x ↦ x ^ p)).sum - r.sum =
          (r.map (fun x ↦ x ^ p - x)).sum := by
            rw [Multiset.sum_map_sub]
            simp
      _ = (r.map (fun _ ↦ φ a)).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl hroot)
      _ = _ := by simp [nsmul_eq_mul]
  apply φ.injective
  simpa only [map_sub, map_pow, map_mul, map_natCast, hsum, hcard] using hsumAS

/-- A proper monic factor of positive degree gives a root of the Artin–Schreier equation. -/
theorem exists_pow_sub_eq_of_monic_dvd_artinSchreier (a : F) (q : F[X]) (hq : q.Monic)
    (hpos : 0 < q.natDegree) (hlt : q.natDegree < p)
    (hdiv : q ∣ X ^ p - X - C a) : ∃ x : F, x ^ p - x = a := by
  have hd : (q.natDegree : F) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt hpos hlt ((CharP.cast_eq_zero_iff F p _).mp h)
  have hdFrob : (q.natDegree : F) ^ p = (q.natDegree : F) :=
    map_natCast (frobenius F p) q.natDegree
  refine ⟨-q.nextCoeff / q.natDegree, ?_⟩
  rw [div_pow, hdFrob, ← sub_div, pow_sub_neg_nextCoeff_of_dvd_artinSchreier a q hq hdiv]
  exact mul_div_cancel_left₀ a hd

/-- An Artin–Schreier polynomial without a root is irreducible. -/
theorem irreducible_X_pow_sub_X_sub_C (a : F) (ha : ∀ x : F, x ^ p - x ≠ a) :
    Irreducible (X ^ p - X - C a) := by
  rw [(monic_X_pow_sub_X_sub_C (p := p) a).irreducible_iff_natDegree]
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg natDegree h
    rw [natDegree_X_pow_sub_X_sub_C, natDegree_one] at this
    exact (Fact.out : p.Prime).ne_zero this
  · intro q r hq hr hqr
    by_contra h
    push Not at h
    have hdegree : q.natDegree + r.natDegree = p := by
      rw [← natDegree_mul hq.ne_zero hr.ne_zero, hqr, natDegree_X_pow_sub_X_sub_C]
    obtain ⟨x, hx⟩ := exists_pow_sub_eq_of_monic_dvd_artinSchreier a q hq
      (Nat.pos_of_ne_zero h.1) (by omega) ⟨r, hqr.symm⟩
    exact ha x hx

end Polynomial
