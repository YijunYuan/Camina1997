/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Congruence
public import Mathlib.RingTheory.LaurentSeries

/-!
# Extension of Nottingham automorphisms to Laurent series

Extension to the fraction field is an injective homomorphism from the genuine
power-series Nottingham group into the algebra automorphisms of Laurent series.
It preserves every parameter congruence. Valuation continuity and the converse
restriction of continuous normalized Laurent automorphisms are separate results.

Reference: Camina (1997), pp. 101–102.
-/

@[expose] public section

namespace Camina1997.Nottingham

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The unique extension to the Laurent-series fraction field, as an algebra equivalence. -/
noncomputable def toLaurentEquiv (g : Nottingham p) :
    LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p) where
  __ := IsFractionRing.ringEquivOfRingEquiv g.toAlgEquiv.toRingEquiv
  commutes' a := by
    change IsFractionRing.ringEquivOfRingEquiv g.toAlgEquiv.toRingEquiv
        (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p))
          (algebraMap (ZMod p) (PowerSeries (ZMod p)) a)) =
      algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p))
        (algebraMap (ZMod p) (PowerSeries (ZMod p)) a)
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact g.toAlgEquiv.commutes a

@[simp]
theorem toLaurentEquiv_algebraMap (g : Nottingham p) (f : PowerSeries (ZMod p)) :
    toLaurentEquiv g (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) f) =
      algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (g f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap g.toAlgEquiv.toRingEquiv f

/-- Extension of Nottingham automorphisms respects composition. -/
noncomputable def toLaurent :
    Nottingham p →* (LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p)) where
  toFun := toLaurentEquiv
  map_one' := by
    ext1 x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (PowerSeries (ZMod p)) x
    simp only [AlgEquiv.one_apply, map_div₀, toLaurentEquiv_algebraMap, one_apply]
  map_mul' g h := by
    ext1 x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (PowerSeries (ZMod p)) x
    simp only [AlgEquiv.mul_apply, map_div₀, toLaurentEquiv_algebraMap, mul_apply]

/-- Extension agrees with the original automorphism on power series. -/
@[simp]
theorem toLaurent_algebraMap (g : Nottingham p) (f : PowerSeries (ZMod p)) :
    toLaurent g (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) f) =
      algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (g f) :=
  toLaurentEquiv_algebraMap g f

theorem toLaurent_injective : Function.Injective (toLaurent (p := p)) := by
  intro g h he
  apply ext_X
  apply IsFractionRing.injective (PowerSeries (ZMod p)) (LaurentSeries (ZMod p))
  simpa only [toLaurent_algebraMap] using
    congrArg (fun e : LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p) ↦
      e (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X)) he

/-- The extension is uniquely determined by its restriction to power series. -/
theorem toLaurent_unique (g : Nottingham p)
    (e : LaurentSeries (ZMod p) ≃ₐ[ZMod p] LaurentSeries (ZMod p))
    (he : ∀ f : PowerSeries (ZMod p),
      e (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) f) =
        algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (g f)) :
    e = toLaurent g := by
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (PowerSeries (ZMod p)) x
  simp only [map_div₀, he, toLaurent_algebraMap]

/-- Extension preserves congruences in the power-series valuation ring. The witness remains
a power series; divisibility in the Laurent field alone would give no information. -/
theorem toLaurent_congruence_iff (g : Nottingham p) (n : ℕ) :
    g ∈ congruenceSubgroup n ↔ ∃ a : PowerSeries (ZMod p),
      toLaurent g (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X) -
        algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) X =
          algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) (X ^ (n + 1) * a) := by
  rw [mem_congruenceSubgroup_iff, toLaurent_algebraMap, ← map_sub]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg (algebraMap (PowerSeries (ZMod p)) (LaurentSeries (ZMod p))) ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, IsFractionRing.injective (PowerSeries (ZMod p)) (LaurentSeries (ZMod p)) ha⟩

end Camina1997.Nottingham
