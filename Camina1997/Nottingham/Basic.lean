/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Automorphism
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The algebraic Nottingham group

`Nottingham p` is the subgroup of `ZMod p`-algebra automorphisms of formal
power series whose value on `X` is congruent to `X` modulo `X²`.
All these automorphisms and their inverses are continuous for the `(X)`-adic
topology by `PowerSeries.continuous_algEquiv`.

The coefficient criterion is equivalent to acting trivially on `(X)/(X²)`.
The group topology, congruence subgroups, and finite quotients are not defined here.

Reference: Camina, *Subgroups of the Nottingham Group* (1997), pp. 101–102.
-/

@[expose] public section

namespace PowerSeries

variable {k : Type*} [Field k]

/-- An automorphism is normalized when the linear coefficient of its parameter is one. -/
def IsNormalized (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) : Prop := coeff 1 (e X) = 1

@[simp]
theorem isNormalized_one : IsNormalized (1 : k⟦X⟧ ≃ₐ[k] k⟦X⟧) := by
  simp [IsNormalized]

theorem IsNormalized.mul {e f : k⟦X⟧ ≃ₐ[k] k⟦X⟧}
    (he : IsNormalized e) (hf : IsNormalized f) : IsNormalized (e * f) := by
  change coeff 1 (e (f X)) = 1
  rw [coeff_one_algEquiv, he, hf, mul_one]

theorem IsNormalized.inv {e : k⟦X⟧ ≃ₐ[k] k⟦X⟧}
    (he : IsNormalized e) : IsNormalized e⁻¹ := by
  change coeff 1 (e X) = 1 at he
  have h := coeff_one_algEquiv e (e.symm X)
  change coeff 1 (e.symm X) = 1
  simpa only [AlgEquiv.apply_symm_apply, coeff_one_X, he, one_mul] using h.symm

/-- The coefficient criterion is exactly the congruence in Camina's definition. -/
theorem isNormalized_iff_X_sq_dvd (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    IsNormalized e ↔ (X : k⟦X⟧) ^ 2 ∣ e X - X := by
  rw [X_pow_dvd_iff]
  constructor
  · intro he n hn
    change coeff 1 (e X) = 1 at he
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl
    · simp [coeff_zero_eq_constantCoeff]
    · simp [he]
  · intro h
    have h1 := h 1 (by decide)
    simpa [IsNormalized, sub_eq_zero] using h1

/-- A normalized automorphism induces the identity on the quotient by `(X²)`. -/
theorem isNormalized_iff_forall_X_sq_dvd (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    IsNormalized e ↔ ∀ f : k⟦X⟧, (X : k⟦X⟧) ^ 2 ∣ e f - f := by
  constructor
  · intro he f
    change coeff 1 (e X) = 1 at he
    rw [X_pow_dvd_iff]
    intro n hn
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl
    · simp [coeff_zero_eq_constantCoeff]
    · rw [map_sub, coeff_one_algEquiv, he, one_mul, sub_self]
  · intro h
    exact (isNormalized_iff_X_sq_dvd e).mpr (h X)

/-- Normalization is equivalent to the identity action on the cotangent space `(X)/(X²)`. -/
theorem isNormalized_iff_forall_X_dvd (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    IsNormalized e ↔
      ∀ f : k⟦X⟧, (X : k⟦X⟧) ∣ f → (X : k⟦X⟧) ^ 2 ∣ e f - f := by
  constructor
  · intro he f _
    exact (isNormalized_iff_forall_X_sq_dvd e).mp he f
  · intro h
    exact (isNormalized_iff_X_sq_dvd e).mpr (h X dvd_rfl)

/-- The subgroup of all normalized algebra automorphisms of `k⟦X⟧`. -/
def normalizedAutSubgroup (k : Type*) [Field k] : Subgroup (k⟦X⟧ ≃ₐ[k] k⟦X⟧) where
  carrier := {e | IsNormalized e}
  one_mem' := isNormalized_one
  mul_mem' := IsNormalized.mul
  inv_mem' := IsNormalized.inv

@[simp]
theorem mem_normalizedAutSubgroup (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    e ∈ normalizedAutSubgroup k ↔ IsNormalized e := Iff.rfl

end PowerSeries

namespace Camina1997

/-- The Nottingham group over the prime field `ZMod p`, with composition as multiplication. -/
abbrev Nottingham (p : ℕ) [Fact p.Prime] : Type :=
  ↥(PowerSeries.normalizedAutSubgroup (ZMod p))

namespace Nottingham

variable {p : ℕ} [Fact p.Prime]

/-- The underlying automorphism of the power-series algebra. -/
def toAlgEquiv (g : Nottingham p) : PowerSeries (ZMod p) ≃ₐ[ZMod p] PowerSeries (ZMod p) := g.val

instance : CoeFun (Nottingham p) (fun _ ↦ PowerSeries (ZMod p) → PowerSeries (ZMod p)) :=
  ⟨fun g ↦ g.toAlgEquiv⟩

@[ext]
theorem ext {g h : Nottingham p} (he : ∀ f, g f = h f) : g = h :=
  Subtype.ext (AlgEquiv.ext he)

@[simp]
theorem one_apply (f : PowerSeries (ZMod p)) : (1 : Nottingham p) f = f := rfl

@[simp]
theorem mul_apply (g h : Nottingham p) (f : PowerSeries (ZMod p)) :
    (g * h) f = g (h f) := rfl

@[simp]
theorem inv_apply (g : Nottingham p) (f : PowerSeries (ZMod p)) :
    g⁻¹ f = g.toAlgEquiv.symm f := rfl

@[simp]
theorem constantCoeff_apply (g : Nottingham p) (f : PowerSeries (ZMod p)) :
    PowerSeries.constantCoeff (g f) = PowerSeries.constantCoeff f :=
  PowerSeries.constantCoeff_algEquiv g.toAlgEquiv f

@[simp]
theorem coeff_one_apply (g : Nottingham p) (f : PowerSeries (ZMod p)) :
    PowerSeries.coeff 1 (g f) = PowerSeries.coeff 1 f := by
  have hg : PowerSeries.coeff 1 (g.toAlgEquiv PowerSeries.X) = 1 := g.property
  rw [PowerSeries.coeff_one_algEquiv g.toAlgEquiv, hg, one_mul]

/-- Every Nottingham automorphism fixes every series modulo `X²`. -/
theorem X_sq_dvd_sub (g : Nottingham p) (f : PowerSeries (ZMod p)) :
    PowerSeries.X ^ 2 ∣ g f - f :=
  (PowerSeries.isNormalized_iff_forall_X_sq_dvd g.toAlgEquiv).mp g.property f

/-- A Nottingham automorphism is continuous for the `(X)`-adic topology on power series. -/
theorem continuous (g : Nottingham p) :
    @Continuous (PowerSeries (ZMod p)) (PowerSeries (ZMod p))
      (Ideal.span {PowerSeries.X}).adicTopology (Ideal.span {PowerSeries.X}).adicTopology g :=
  PowerSeries.continuous_algEquiv g.toAlgEquiv

end Nottingham
end Camina1997
