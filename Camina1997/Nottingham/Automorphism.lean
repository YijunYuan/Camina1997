import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Algebra.Algebra.Equiv

/-!
# Algebra automorphisms of formal power series

Over a field, every algebra automorphism of `k⟦X⟧` preserves the constant
coefficient and is continuous for the `(X)`-adic topology. The linear coefficient
of its value on a series is the product of the two linear coefficients.

These facts justify the ring-automorphism model of the Nottingham group in
Camina, *Subgroups of the Nottingham Group* (1997), pp. 101–102.
-/

namespace PowerSeries

variable {k : Type*} [Field k]

@[simp]
theorem algEquiv_C (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (a : k) : e (C a) = C a :=
  e.commutes a

/-- An automorphism sends the parameter to a series with zero constant term. -/
@[simp]
theorem constantCoeff_algEquiv_X (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    constantCoeff (e X) = 0 := by
  by_contra h
  have hu : IsUnit (e X) := isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)
  have hx : IsUnit (X : k⟦X⟧) := by
    simpa using hu.map e.symm.toRingEquiv.toRingHom
  simp [isUnit_iff_constantCoeff] at hx

/-- Algebra automorphisms fix the residue field identified by the constant coefficient. -/
@[simp]
theorem constantCoeff_algEquiv (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (f : k⟦X⟧) :
    constantCoeff (e f) = constantCoeff f := by
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  simp

/-- The linear coefficient transforms by the linear coefficient of the image of `X`. -/
theorem coeff_one_algEquiv (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (f : k⟦X⟧) :
    coeff 1 (e f) = coeff 1 (e X) * coeff 1 f := by
  conv_lhs => rw [eq_X_mul_shift_add_const f]
  simp [coeff_one_mul]

/-- Every algebra automorphism is continuous for the actual `(X)`-adic topology. -/
theorem continuous_algEquiv (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) :
    @Continuous k⟦X⟧ k⟦X⟧
      (Ideal.span {X}).adicTopology (Ideal.span {X}).adicTopology e := by
  let : WithIdeal k⟦X⟧ := ⟨Ideal.span {X}⟩
  apply (WithIdeal.uniformContinuous_of_map_le (f := e.toRingEquiv.toRingHom) ?_).continuous
  change (Ideal.span {X}).map e.toRingEquiv.toRingHom ≤ Ideal.span {X}
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change e X ∈ Ideal.span {X}
  rw [Ideal.mem_span_singleton]
  exact X_dvd_iff.mpr (constantCoeff_algEquiv_X e)

end PowerSeries
