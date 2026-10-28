/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Congruence
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Parameters for the Nottingham group

Substitution by a series with zero constant coefficient and invertible linear
coefficient is an algebra automorphism. In particular, every sequence of
coefficients of degrees at least two gives a unique Nottingham automorphism.

Reference: Camina (1997), p. 102, the parameter description of `J`.
-/

@[expose] public section

namespace PowerSeries

variable {k : Type*} [Field k]

/-- Substitution by a parameter with invertible linear coefficient is an automorphism. -/
noncomputable def substAlgEquiv (f : k⟦X⟧) (h0 : constantCoeff f = 0)
    (h1 : IsUnit (coeff 1 f)) : k⟦X⟧ ≃ₐ[k] k⟦X⟧ :=
  AlgEquiv.ofAlgHom (substAlgHom (HasSubst.of_constantCoeff_zero h0))
    (substAlgHom (HasSubst.substInvOfIsUnit f h1))
    (by
      ext1 g
      simp only [AlgHom.comp_apply, AlgHom.id_apply, coe_substAlgHom]
      rw [subst_comp_subst_apply (HasSubst.substInvOfIsUnit f h1)
        (HasSubst.of_constantCoeff_zero h0), subst_substInvOfIsUnit_left f h0 h1, X_subst])
    (by
      ext1 g
      simp only [AlgHom.comp_apply, AlgHom.id_apply, coe_substAlgHom]
      rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero h0)
        (HasSubst.substInvOfIsUnit f h1), subst_substInvOfIsUnit_right f h0 h1, X_subst])

@[simp]
theorem substAlgEquiv_X (f : k⟦X⟧) (h0 : constantCoeff f = 0)
    (h1 : IsUnit (coeff 1 f)) : substAlgEquiv f h0 h1 X = f :=
  substAlgHom_X (HasSubst.of_constantCoeff_zero h0)

end PowerSeries

namespace Camina1997.Nottingham

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- Realize an arbitrary normalized parameter by substitution. -/
noncomputable def ofSeries (f : PowerSeries (ZMod p)) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1) : Nottingham p :=
  ⟨substAlgEquiv f h0 (h1 ▸ isUnit_one), by
    change coeff 1 (substAlgEquiv f h0 _ X) = 1
    simpa using h1⟩

@[simp]
theorem ofSeries_X (f : PowerSeries (ZMod p)) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1) : ofSeries f h0 h1 X = f :=
  substAlgEquiv_X f h0 _

/-- The automorphism with prescribed coefficients in degrees two and higher. -/
noncomputable def ofCoefficients (a : ℕ → ZMod p) : Nottingham p :=
  ofSeries (X + X ^ 2 * mk a) (by simp) (by simp [coeff_X_pow_mul'])

@[simp]
theorem ofCoefficients_X (a : ℕ → ZMod p) :
    ofCoefficients a X = X + X ^ 2 * mk a := ofSeries_X _ _ _

@[simp]
theorem coeff_ofCoefficients_X (a : ℕ → ZMod p) (n : ℕ) :
    coeff (n + 2) (ofCoefficients a X) = a n := by
  rw [ofCoefficients_X, map_add, coeff_X_pow_mul]
  simp [coeff_X]

/-- The coefficients beyond the linear term are free coordinates on the Nottingham group. -/
noncomputable def coefficientEquiv : Nottingham p ≃ (ℕ → ZMod p) where
  toFun g n := coeff (n + 2) (g X)
  invFun := ofCoefficients
  left_inv g := by
    apply ext_X
    apply PowerSeries.ext
    intro n
    match n with
    | 0 => simp [coeff_zero_eq_constantCoeff]
    | 1 => simp [coeff_one_apply, coeff_X_pow_mul']
    | n + 2 => simp [coeff_X]
  right_inv a := by
    funext n
    exact coeff_ofCoefficients_X a n

end Camina1997.Nottingham
