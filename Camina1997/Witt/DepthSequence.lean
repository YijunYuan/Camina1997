/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Witt.DepthTower
public import Camina1997.Witt.Finite

/-!
# Depth-compatible embeddings of a sequence of finite p-groups

Starting from a finite Laurent realization, recursively lift each surjection
with the depth-preserving finite lifting theorem. Each stage retains its full
Galois realization to supply the input for the next stage.

Reference: Camina (1997), the finite quotient tower in Theorem 5, p. 110.
-/

@[expose] public section

namespace Camina1997.Witt

variable {p : ℕ} [Fact p.Prime]
local notation "K" => LaurentSeries (ZMod p)

private structure DepthRealization (G : Type*) [Group G] where
  algebra : Algebra K K
  finiteDimensional : letI := algebra; letI : Module K K := algebra.toModule
    FiniteDimensional K K
  galois : letI := algebra; IsGalois K K
  equiv : letI := algebra; G ≃* (K ≃ₐ[K] K)
  action : G →* Nottingham p
  injective : Function.Injective action
  agreement : ∀ (g : G) (x : K), Nottingham.toLaurent (action g) x = equiv g x

private theorem nonempty_depthRealization (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup p G) : Nonempty (DepthRealization (p := p) G) := by
  obtain ⟨a, hfin, hgal, ρ, hval, _⟩ :=
    exists_laurent_galois_realization K (RingEquiv.refl K) G hG
  let := a
  let ψ : G →* (K ≃ₐ[ZMod p] K) :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (f := (ρ g).toRingEquiv)
        (fun c => DFunLike.congr_fun (RingHom.ext_zmod
          ((ρ g).toRingHom.comp (algebraMap (ZMod p) K))
          (algebraMap (ZMod p) K)) c)
      map_one' := by
        ext x : 1
        exact DFunLike.congr_fun ρ.map_one x
      map_mul' := fun g h => by
        ext x : 1
        exact DFunLike.congr_fun (ρ.map_mul g h) x }
  have hψ : Function.Injective ψ := by
    intro g h he
    apply ρ.injective
    ext x : 1
    exact congrArg (fun e : K ≃ₐ[ZMod p] K => e x) he
  refine ⟨⟨a, hfin, hgal, ρ, Nottingham.ofLaurentAction hG ψ hval,
    (Nottingham.ofLaurentAction_injective_iff hG ψ hval).mpr hψ, ?_⟩⟩
  intro g x
  exact congrArg (fun e : K ≃ₐ[ZMod p] K => e x)
    (Nottingham.toLaurent_ofLaurentAction hG ψ hval g)

private theorem exists_depthRealization_lift {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (r : DepthRealization (p := p) G) (hH : IsPGroup p H)
    (q : H →* G) (hq : Function.Surjective q) :
    ∃ r' : DepthRealization (p := p) H,
      ∀ h : H, q h ≠ 1 →
        Nottingham.depth (r'.action h) = Nottingham.depth (r.action (q h)) := by
  let := r.algebra
  let : Module K K := r.algebra.toModule
  let := r.finiteDimensional
  let := r.galois
  obtain ⟨a, hfin, hgal, ρ, _, φ, hinj, hagree, hdepth⟩ :=
    exists_depth_preserving_lift K (RingEquiv.refl K) r.equiv r.action r.agreement H hH q hq
  refine ⟨⟨a, hfin, hgal, ρ, φ, hinj, hagree⟩, ?_⟩
  intro h hh
  exact hdepth h (fun he => hh ((map_eq_one_iff r.action r.injective).mp he))

/-- A surjective sequence of finite p-groups has faithful Nottingham actions whose
depths are preserved whenever an element survives in the preceding quotient. -/
theorem exists_depth_compatible_sequence
    (G : ℕ → Type*) [∀ n, Group (G n)] [∀ n, Finite (G n)]
    (hG : ∀ n, IsPGroup p (G n))
    (q : ∀ n, G (n + 1) →* G n) (hq : ∀ n, Function.Surjective (q n)) :
    ∃ φ : ∀ n, G n →* Nottingham p,
      (∀ n, Function.Injective (φ n)) ∧
      ∀ (n : ℕ) (g : G (n + 1)), q n g ≠ 1 →
        Nottingham.depth (φ (n + 1) g) = Nottingham.depth (φ n (q n g)) := by
  classical
  have hstep (n : ℕ) (r : DepthRealization (p := p) (G n)) :
      ∃ r' : DepthRealization (p := p) (G (n + 1)),
        ∀ g : G (n + 1), q n g ≠ 1 →
          Nottingham.depth (r'.action g) = Nottingham.depth (r.action (q n g)) :=
    exists_depthRealization_lift r (hG (n + 1)) (q n) (hq n)
  choose next hnext using hstep
  let r : ∀ n, DepthRealization (p := p) (G n) :=
    Nat.rec (Classical.choice (nonempty_depthRealization (G 0) (hG 0))) next
  exact ⟨fun n => (r n).action, fun n => (r n).injective, fun n => hnext n (r n)⟩

end Camina1997.Witt
