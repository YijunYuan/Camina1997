/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Laurent

/-!
# Valuation continuity of extended Nottingham automorphisms

The extension of a Nottingham automorphism to Laurent series preserves the
canonical `X`-adic valuation. It and its inverse are uniformly continuous for
the corresponding valuation topology.

Reference: Camina (1997), pp. 101–102.
-/

@[expose] public section

namespace PowerSeries

open scoped WithZero
open WithZero IsDedekindDomain.HeightOneSpectrum

variable {k : Type*} [Field k]

/-- Algebra automorphisms preserve the Laurent valuation of power series. -/
theorem valuation_coe_algEquiv (e : k⟦X⟧ ≃ₐ[k] k⟦X⟧) (f : k⟦X⟧) :
    Valued.v (e f : LaurentSeries k) = Valued.v (f : LaurentSeries k) := by
  have hbound (n : ℕ) :
      Valued.v (e f : LaurentSeries k) ≤ exp (-(n : ℤ)) ↔
        Valued.v (f : LaurentSeries k) ≤ exp (-(n : ℤ)) := by
    rw [LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero,
      LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero,
      ← X_pow_dvd_iff, ← X_pow_dvd_iff]
    constructor
    · intro h
      simpa using X_pow_dvd_algEquiv e.symm h
    · exact X_pow_dvd_algEquiv e
  by_cases hf : f = 0
  · simp [hf, coe_zero]
  have hex (a : k⟦X⟧) (ha : a ≠ 0) :
      ∃ n : ℕ, Valued.v (a : LaurentSeries k) = exp (-(n : ℤ)) := by
    rw [← LaurentSeries.coe_algebraMap, LaurentSeries.valuation_def,
      valuation_of_algebraMap, intValuation_if_neg _ ha]
    exact ⟨_, rfl⟩
  obtain ⟨n, hn⟩ := hex f hf
  obtain ⟨m, hm⟩ := hex (e f) (by simpa using hf)
  apply le_antisymm
  · rw [hn]
    exact (hbound n).mpr hn.le
  · rw [hm]
    exact (hbound m).mp hm.le

end PowerSeries

namespace Camina1997.Nottingham

open PowerSeries Filter
open scoped WithZero Uniformity

variable {p : ℕ} [Fact p.Prime]

/-- Extending a Nottingham automorphism to fractions preserves the canonical valuation. -/
theorem valuation_toLaurent (g : Nottingham p) (f : LaurentSeries (ZMod p)) :
    Valued.v (toLaurent g f) = Valued.v f := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (PowerSeries (ZMod p)) f
  simp only [map_div₀, toLaurent_algebraMap]
  simp only [LaurentSeries.coe_algebraMap]
  rw [valuation_coe_algEquiv g.toAlgEquiv a, valuation_coe_algEquiv g.toAlgEquiv b]

/-- The Laurent extension preserves every valuation entourage. -/
theorem uniformContinuous_toLaurent (g : Nottingham p) : UniformContinuous (toLaurent g) := by
  change Tendsto (fun q : LaurentSeries (ZMod p) × LaurentSeries (ZMod p) ↦
    (toLaurent g q.1, toLaurent g q.2)) (𝓤 _) (𝓤 _)
  rw [(Valued.hasBasis_uniformity (LaurentSeries (ZMod p)) ℤᵐ⁰).tendsto_iff
    (Valued.hasBasis_uniformity (LaurentSeries (ZMod p)) ℤᵐ⁰)]
  intro γ _
  refine ⟨γ, trivial, ?_⟩
  intro q hq
  change Valued.v.restrict (toLaurent g q.2 - toLaurent g q.1) < γ.1
  rw [← map_sub, (Valuation.restrict_inj _).mpr (valuation_toLaurent g (q.2 - q.1))]
  exact hq

theorem continuous_toLaurent (g : Nottingham p) : Continuous (toLaurent g) :=
  (uniformContinuous_toLaurent g).continuous

theorem uniformContinuous_toLaurent_symm (g : Nottingham p) :
    UniformContinuous (toLaurent g).symm := by
  change UniformContinuous ((toLaurent g)⁻¹ :
    LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p))
  rw [← map_inv]
  exact uniformContinuous_toLaurent g⁻¹

theorem continuous_toLaurent_symm (g : Nottingham p) : Continuous (toLaurent g).symm :=
  (uniformContinuous_toLaurent_symm g).continuous

/-- The Laurent extension as a homeomorphism for the canonical valuation topology. -/
noncomputable def toLaurentHomeomorph (g : Nottingham p) :
    LaurentSeries (ZMod p) ≃ₜ LaurentSeries (ZMod p) where
  toEquiv := (toLaurent g).toEquiv
  continuous_toFun := continuous_toLaurent g
  continuous_invFun := continuous_toLaurent_symm g

end Camina1997.Nottingham
