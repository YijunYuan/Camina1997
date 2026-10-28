/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.Depth
public import Camina1997.Witt.PrimeKernel
public import Camina1997.GroupTheory.CentralStep

/-!
# Depth-preserving lifts of finite p-group quotients

Every surjection of finite p-groups factors into central prime-order steps.
Applying the constructed Laurent lift at each step preserves the depths of
all elements with nonidentity image in the original quotient. The full Galois
realization and its Nottingham action are retained after the lift.

Reference: Camina (1997), Theorem 4 and the tower in Theorem 5, pp. 109–110.
-/

@[expose] public section

namespace Camina1997.Witt

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)

variable (F : Type*) [Field F] [Module (ZMod p) F] [CharP F p]
  [Algebra F (LaurentSeries (ZMod p))]
  [FiniteDimensional F (LaurentSeries (ZMod p))] [IsGalois F (LaurentSeries (ZMod p))]

/-- Every finite p-group surjection admits a Laurent realization preserving quotient depths.

The initial finite Galois realization and its Nottingham action are inputs. The
new realization, faithful action, and all nontrivial quotient depth equalities
are constructed by induction through central prime-order kernels.
-/
theorem exists_depth_preserving_lift
    (eF : F ≃+* K) {G : Type*} [Group G] [Finite G]
    (ρG : G ≃* (K ≃ₐ[F] K)) (ψG : G →* Nottingham p)
    (hψG : ∀ (g : G) (x : K), Nottingham.toLaurent (ψG g) x = ρG g x)
    (H : Type*) [Group H] [Finite H] (hH : IsPGroup p H)
    (q : H →* G) (hq : Function.Surjective q) :
    ∃ a : Algebra F K, letI := a
      FiniteDimensional F K ∧ IsGalois F K ∧
      ∃ ρ : H ≃* (K ≃ₐ[F] K),
        (∀ (h : H) (x : K), (ρ h x).orderTop = x.orderTop) ∧
        ∃ φ : H →* Nottingham p, Function.Injective φ ∧
          (∀ (h : H) (x : K), Nottingham.toLaurent (φ h) x = ρ h x) ∧
          ∀ h : H, ψG (q h) ≠ 1 → Nottingham.depth (φ h) = Nottingham.depth (ψG (q h)) := by
  have hψinj : Function.Injective ψG := by
    intro g g' he
    apply ρG.injective
    ext x : 1
    rw [← hψG, ← hψG, he]
  induction hn : Nat.card H using Nat.strong_induction_on generalizing H with
  | h n ih =>
    by_cases hqi : Function.Injective q
    · refine ⟨inferInstance, inferInstance, inferInstance,
        (MulEquiv.ofBijective q ⟨hqi, hq⟩).trans ρG, ?_, ψG.comp q,
        hψinj.comp hqi, ?_, ?_⟩
      · intro h x
        change (ρG (q h) x).orderTop = x.orderTop
        rw [← hψG]
        exact Nottingham.orderTop_toLaurent _ _
      · intro h x
        exact hψG (q h) x
      · intro h _
        rfl
    · have hker : q.ker ≠ ⊥ := by
        intro he
        exact hqi ((MonoidHom.ker_eq_bot_iff q).mp he)
      obtain ⟨N, hN, hNK, hc, hcard, hquot, hlt⟩ :=
        hH.exists_central_prime_step_le_normal q.ker hker
      let := hN
      let qbar : H ⧸ N →* G := QuotientGroup.lift N q hNK
      have hqbar : Function.Surjective qbar :=
        QuotientGroup.lift_surjective_of_surjective N q hq hNK
      obtain ⟨a, hfin, hgal, ρQ, hvalQ, φQ, hinjQ, hagreeQ, hdepthQ⟩ :=
        ih (Nat.card (H ⧸ N)) (by omega) (H ⧸ N) hquot qbar hqbar rfl
      let := a
      let := hfin
      let := hgal
      let s : H →* (K ≃ₐ[F] K) := ρQ.toMonoidHom.comp (QuotientGroup.mk' N)
      have hs : Function.Surjective s :=
        ρQ.surjective.comp (QuotientGroup.mk'_surjective N)
      have hsker : s.ker = N := by
        ext h
        change ρQ (QuotientGroup.mk' N h) = 1 ↔ h ∈ N
        rw [map_eq_one_iff ρQ ρQ.injective]
        exact QuotientGroup.eq_one_iff h
      let S := GroupExtension.ofPrimeKernel s hs (hsker ▸ hcard)
      have hcentral : S.inl.range ≤ Subgroup.center H := by
        rw [S.range_inl_eq_ker_rightHom]
        change s.ker ≤ Subgroup.center H
        rw [hsker]
        exact hc
      let ψ : H →* Nottingham p := φQ.comp (QuotientGroup.mk' N)
      have hψ (h : H) (x : K) : Nottingham.toLaurent (ψ h) x = S.rightHom h x :=
        hagreeQ (QuotientGroup.mk' N h) x
      obtain ⟨a', hfin', hgal', ρ, hval, φ, hinj, hagree, hdepth⟩ :=
        exists_depth_preserving_centralLift F eF hH S hcentral ψ hψ
      refine ⟨a', hfin', hgal', ρ, hval, φ, hinj, hagree, ?_⟩
      intro h hh
      have hmid : ψ h ≠ 1 := by
        intro he
        have hmk : QuotientGroup.mk' N h = 1 := (map_eq_one_iff φQ hinjQ).mp he
        have hqh : q h = 1 := by
          change qbar (QuotientGroup.mk' N h) = 1
          rw [hmk, map_one]
        exact hh (by rw [hqh, map_one])
      exact (hdepth h hmid).trans (hdepthQ (QuotientGroup.mk' N h) hh)

end Camina1997.Witt
