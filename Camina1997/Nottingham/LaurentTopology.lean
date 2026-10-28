/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Laurent
public import Camina1997.Nottingham.Parameters

/-!
# The Laurent-series description of the Nottingham group

The extension of a Nottingham automorphism to Laurent series preserves the
canonical `X`-adic valuation. It and its inverse are uniformly continuous for
the corresponding valuation topology. Rational-function density proves that a
continuous Laurent automorphism is determined by its parameter. Parameter
realization then identifies the continuous normalized Laurent automorphisms
with the Nottingham group, with restriction as the inverse of extension.

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

namespace LaurentSeries

open scoped RatFunc

variable {k : Type*} [Field k]

/-- Continuous Laurent-series automorphisms agreeing on the parameter are equal. -/
theorem algEquiv_ext_of_continuous
    {e f : LaurentSeries k ≃ₐ[k] LaurentSeries k}
    (he : Continuous e) (hf : Continuous f)
    (hX : e (HahnSeries.single 1 1) = f (HahnSeries.single 1 1)) : e = f := by
  let ι : Polynomial k →ₐ[k] LaurentSeries k :=
    { toRingHom := algebraMap (Polynomial k) (LaurentSeries k)
      commutes' := fun a ↦ by
        change algebraMap (Polynomial k) (LaurentSeries k) (Polynomial.C a) =
          algebraMap k (LaurentSeries k) a
        simp only [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C]
        rw [HahnSeries.algebraMap_apply']
        rfl }
  have hpoly :
      e.toAlgHom.comp ι = f.toAlgHom.comp ι := by
    apply Polynomial.algHom_ext
    simpa [ι] using hX
  apply DFunLike.ext'
  apply coe_range_dense.equalizer he hf
  funext q
  change e (algebraMap (RatFunc k) (LaurentSeries k) q) =
    f (algebraMap (RatFunc k) (LaurentSeries k) q)
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (Polynomial k) q
  simp only [map_div₀,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) (LaurentSeries k)]
  exact congrArg₂ (· / ·) (DFunLike.congr_fun hpoly a) (DFunLike.congr_fun hpoly b)

end LaurentSeries

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

/-- A continuous normalized Laurent automorphism is the extension of a unique
Nottingham automorphism. Normalization uses a power-series witness. -/
theorem existsUnique_toLaurent
    (e : LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p))
    (he : Continuous e)
    (hn : ∃ a : PowerSeries (ZMod p),
      e (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X) -
        algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X =
          algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (X ^ 2 * a)) :
    ∃! g : Nottingham p, toLaurent g = e := by
  obtain ⟨a, ha⟩ := hn
  let g := ofSeries (X + X ^ 2 * a) (by simp) (by simp [coeff_X_pow_mul'])
  have hg : toLaurent g = e := by
    apply LaurentSeries.algEquiv_ext_of_continuous (continuous_toLaurent g) he
    rw [← PowerSeries.coe_X, ← LaurentSeries.coe_algebraMap, toLaurent_algebraMap]
    change algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p))
        (ofSeries (X + X ^ 2 * a) _ _ X) = _
    rw [ofSeries_X, map_add]
    exact (add_comm _ _).trans (eq_add_of_sub_eq ha).symm
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact toLaurent_injective (hh.trans hg.symm)

/-- The image of extension is exactly the continuous normalized Laurent automorphisms. -/
theorem mem_range_toLaurent_iff
    (e : LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p)) :
    e ∈ toLaurent.range ↔ Continuous e ∧ ∃ a : PowerSeries (ZMod p),
      e (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X) -
        algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X =
          algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (X ^ 2 * a) := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨continuous_toLaurent g, ?_⟩
    exact (toLaurent_congruence_iff g 1).mp (by
      rw [mem_congruenceSubgroup_iff]
      exact X_sq_dvd_sub g X)
  · rintro ⟨he, hn⟩
    exact (existsUnique_toLaurent e he hn).exists

/-- The intrinsic image criterion can equivalently be expressed by the first two
coefficients of a power-series parameter. -/
theorem mem_range_toLaurent_iff_parameter
    (e : LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p)) :
    e ∈ toLaurent.range ↔ Continuous e ∧ ∃ f : PowerSeries (ZMod p),
      constantCoeff f = 0 ∧ coeff 1 f = 1 ∧
        e (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X) =
          algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨continuous_toLaurent g, g X, by simp, by simp, toLaurent_algebraMap g X⟩
  · rintro ⟨he, f, h0, h1, hf⟩
    refine ⟨ofSeries f h0 h1, ?_⟩
    apply LaurentSeries.algEquiv_ext_of_continuous
      (continuous_toLaurent (ofSeries f h0 h1)) he
    rw [← PowerSeries.coe_X, ← LaurentSeries.coe_algebraMap, toLaurent_algebraMap,
      ofSeries_X]
    exact hf.symm

/-- Extension is a group isomorphism onto the continuous normalized Laurent automorphisms,
characterized intrinsically by `mem_range_toLaurent_iff`. -/
noncomputable def laurentEquiv : Nottingham p ≃* (toLaurent (p := p)).range :=
  MulEquiv.ofBijective toLaurent.rangeRestrict
    ⟨fun _ _ h ↦ toLaurent_injective (congrArg Subtype.val h),
      toLaurent.rangeRestrict_surjective⟩

@[simp]
theorem coe_laurentEquiv (g : Nottingham p) :
    (laurentEquiv g : LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p)) =
      toLaurent g := rfl

/-- The inverse of extension is restriction to the power-series ring. -/
theorem laurentEquiv_symm_algebraMap (e : (toLaurent (p := p)).range)
    (f : PowerSeries (ZMod p)) :
    algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (laurentEquiv.symm e f) =
      e.val (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) f) := by
  have he : toLaurent (laurentEquiv.symm e) = e.val :=
    congrArg Subtype.val (laurentEquiv.apply_symm_apply e)
  rw [← toLaurent_algebraMap, he]

end Camina1997.Nottingham
