/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Adjustment
public import Camina1997.ArtinSchreier.Semilinear
public import Camina1997.ArtinSchreier.DepthLift

/-!
# Simultaneous depth-preserving central lifting

One reduced pole beyond every nontrivial lower depth gives a faithful lifted
Nottingham action preserving all those depths. The full Galois realization is
retained in Laurent coordinates so that further central steps can use it.

Reference: Camina (1997), Theorem 4, pp. 109–110.
-/

@[expose] public section

open Polynomial

namespace Camina1997.Witt

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)

variable (F : Type*) [Field F] [Module (ZMod p) F] [CharP F p]
  [Algebra F (LaurentSeries (ZMod p))]
  [FiniteDimensional F (LaurentSeries (ZMod p))] [IsGalois F (LaurentSeries (ZMod p))]

/-- A single central lift preserves every nontrivial quotient depth simultaneously.

The conclusion retains a finite Galois Laurent realization and identifies its
full group with the constructed Nottingham action, ready for subsequent lifts.
-/
theorem exists_depth_preserving_centralLift {E : Type*} [Group E] [Finite E]
    (eF : F ≃+* K) (hE : IsPGroup p E)
    (S : GroupExtension (Multiplicative (ZMod p)) E (K ≃ₐ[F] K))
    (hcentral : S.inl.range ≤ Subgroup.center E)
    (ψ : E →* Nottingham p)
    (hψ : ∀ (g : E) (x : K), Nottingham.toLaurent (ψ g) x = S.rightHom g x) :
    ∃ a : Algebra F K, letI := a
      FiniteDimensional F K ∧ IsGalois F K ∧
      ∃ ρ : E ≃* (K ≃ₐ[F] K),
        (∀ (g : E) (x : K), (ρ g x).orderTop = x.orderTop) ∧
        ∃ φ : E →* Nottingham p, Function.Injective φ ∧
          (∀ (g : E) (x : K), Nottingham.toLaurent (φ g) x = ρ g x) ∧
          ∀ g : E, ψ g ≠ 1 → Nottingham.depth (φ g) = Nottingham.depth (ψ g) := by
  obtain ⟨B, hB⟩ := Nottingham.exists_depth_bound_of_finite ψ
  obtain ⟨r, m, hm, hpm, hr, _, hBm, _, hgal, ρ, hrestrict⟩ :=
    exists_reduced_galois_centralLift_laurentBase F eF S hcentral B
  have hr' : r.orderTop = (-(m : ℤ) : WithTop ℤ) := by exact_mod_cast hr
  let : Fact (Irreducible (X ^ p - X - C r)) :=
    ⟨LaurentSeries.irreducible_X_pow_sub_X_sub_C_of_orderTop hm hpm r hr⟩
  let A := AdjoinRoot (X ^ p - X - C r)
  let aA : Algebra F A := inferInstance
  let := aA
  let : FiniteDimensional F A := FiniteDimensional.trans F K A
  let : IsGalois F A := hgal
  let ρR : E →* (A ≃+* A) :=
    { toFun := fun g => (ρ g).toRingEquiv
      map_one' := congrArg AlgEquiv.toRingEquiv ρ.map_one
      map_mul' := fun g h => congrArg AlgEquiv.toRingEquiv (ρ.map_mul g h) }
  have hρinj : Function.Injective ρR := AlgEquiv.toRingEquiv_injective.comp ρ.injective
  have hρval (g : E) (x : A) :
      ArtinSchreier.weightedOrder r m (ρR g x) = ArtinSchreier.weightedOrder r m x := by
    apply ArtinSchreier.weightedOrder_semilinear r m hm hpm hr' (ρ g).toRingEquiv
      (S.rightHom g).toRingEquiv (hrestrict g)
    intro z
    change (S.rightHom g z).orderTop = z.orderTop
    rw [← hψ]
    exact Nottingham.orderTop_toLaurent _ _
  obtain ⟨π, hπ, hd⟩ := ArtinSchreier.exists_uniformizer_translation_depth r m hm hpm
  have hπO : π ∈ ArtinSchreier.weightedInteger r m hm hpm hr' := by
    rw [ArtinSchreier.mem_weightedInteger, hπ]
    exact zero_le_one
  let πO : ArtinSchreier.weightedInteger r m hm hpm hr' := ⟨π, hπO⟩
  let φ := ArtinSchreier.nottinghamAction r m hm hpm hr' πO hπ hE ρR hρval
  have hφ : Function.Injective φ :=
    (ArtinSchreier.nottinghamAction_injective_iff r m hm hpm hr' πO hπ hE ρR hρval).mpr hρinj
  have hdepth (g : E) (hg : ψ g ≠ 1) : Nottingham.depth (φ g) = Nottingham.depth (ψ g) := by
    obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp ((Nottingham.depth_eq_top_iff (ψ g)).not.mpr hg)
    have hdB : d ≤ B := by
      have hb := hB g hg
      rw [← hd'] at hb
      exact_mod_cast hb
    rw [← hd']
    apply ArtinSchreier.depth_nottinghamAction_of_restriction r m hm hpm hr' πO hπ hd
      hE ρR hρval ψ _ g hd'.symm (lt_of_le_of_lt hdB hBm)
    intro g x
    rw [hψ]
    exact hrestrict g x
  let e := ArtinSchreier.laurentParameterEquiv r m hm hpm hr' πO hπ
  have he (x : K) : ArtinSchreier.weightedOrder r m (e x) = x.orderTop :=
    ArtinSchreier.weightedOrder_laurentParameterEquiv r m hm hpm hr' πO hπ x
  have he' (x : A) : (e.symm x).orderTop = ArtinSchreier.weightedOrder r m x := by
    simpa only [AlgEquiv.apply_symm_apply] using (he (e.symm x)).symm
  let β : F →+* K := e.symm.toRingHom.comp (algebraMap F A)
  let a := β.toAlgebra
  refine ⟨a, ?_⟩
  let := a
  let e' : A ≃ₐ[F] K := { e.symm.toRingEquiv with commutes' := fun _ => rfl }
  refine ⟨e'.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv e',
    ρ.trans (AlgEquiv.autCongr e'), ?_, φ, hφ, ?_, hdepth⟩
  · intro g x
    change (e.symm (ρR g (e x))).orderTop = x.orderTop
    rw [he', hρval, he]
  · intro g x
    have hc := Nottingham.toLaurent_ofLaurentAction hE
      (ArtinSchreier.parameterAction r m hm hpm hr' πO hπ ρR)
      (ArtinSchreier.orderTop_parameterAction r m hm hpm hr' πO hπ ρR hρval) g
    exact DFunLike.congr_fun hc x

end Camina1997.Witt
