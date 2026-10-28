/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.InverseLimit
public import Camina1997.Nottingham.Depth
public import Camina1997.ProP.FiniteGeneration
public import Mathlib.Topology.Sequences

/-!
# Diagonal limits of continuous Nottingham homomorphisms

Finite topological generation makes every finite quotient homomorphism set
finite. Sequential compactness of their product supplies a simultaneous limit.

Reference: Camina (1997), Theorem 5, pp. 111–112.
-/

@[expose] public section

open Filter Topology

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The continuous projection to a finite congruence quotient. -/
noncomputable def congruenceProjection (n : ℕ) :
    ContinuousMonoidHom (Nottingham p) ((congruenceQuotientDiagram (p := p)).obj n) :=
  ((congruenceLimitCone (p := p)).π.app n).hom

@[simp]
theorem congruenceProjection_apply (n : ℕ) (g : Nottingham p) :
    congruenceProjection n g = (QuotientGroup.mk g : Nottingham p ⧸ congruenceSubgroup n) := rfl

/-- A compatible family of continuous finite-quotient homomorphisms lifts continuously. -/
theorem exists_continuousMonoidHom_of_compatible
    (h : ∀ n : ℕ, ContinuousMonoidHom G ((congruenceQuotientDiagram (p := p)).obj n))
    (hh : ∀ m n (hmn : m ≤ n) (x : G),
      QuotientGroup.map (congruenceSubgroup n) (congruenceSubgroup m)
        (MonoidHom.id (Nottingham p)) (congruenceSubgroup_antitone hmn) (h n x) = h m x) :
    ∃ f : ContinuousMonoidHom G (Nottingham p),
      ∀ n, (congruenceProjection n).comp f = h n := by
  let hlim : G →* congruenceInverseLimit (p := p) :=
    { toFun := fun x => ⟨fun n => h n x, fun {_ _} f => hh _ _ (CategoryTheory.leOfHom f) x⟩
      map_one' := by apply Subtype.ext; funext n; exact map_one (h n)
      map_mul' := fun x y => by apply Subtype.ext; funext n; exact map_mul (h n) x y }
  have hcont : Continuous hlim :=
    (continuous_pi (fun n => (h n).continuous)).subtype_mk _
  let f : ContinuousMonoidHom G (Nottingham p) :=
    { toMonoidHom := (congruenceLimitEquiv (p := p)).symm.toMonoidHom.comp hlim
      continuous_toFun := (congruenceLimitEquiv (p := p)).symm.continuous.comp hcont }
  refine ⟨f, ?_⟩
  intro n
  ext x
  have he := congrArg (fun z : congruenceInverseLimit (p := p) => z.val n)
    ((congruenceLimitEquiv (p := p)).apply_symm_apply (hlim x))
  exact (congruenceLimitEquiv_apply _ n).symm.trans he

/-- A subsequence stabilizes as a whole homomorphism at each finite congruence level. -/
theorem exists_diagonal_limit (hG : TopologicallyFG G)
    (f : ℕ → ContinuousMonoidHom G (Nottingham p)) :
    ∃ (g : ContinuousMonoidHom G (Nottingham p)) (s : ℕ → ℕ), StrictMono s ∧
      ∀ n, ∀ᶠ j in atTop,
        (congruenceProjection n).comp (f (s j)) = (congruenceProjection n).comp g := by
  let H := fun n : ℕ => ContinuousMonoidHom G ((congruenceQuotientDiagram (p := p)).obj n)
  let (n : ℕ) : Finite ((congruenceQuotientDiagram (p := p)).obj n) :=
    inferInstanceAs (Finite (Nottingham p ⧸ congruenceSubgroup n))
  let (n : ℕ) : Finite (H n) := hG.finite_continuousMonoidHom
  let (n : ℕ) : TopologicalSpace (H n) := ⊥
  let (n : ℕ) : DiscreteTopology (H n) := ⟨rfl⟩
  let u : ℕ → ∀ n, H n := fun i n => (congruenceProjection n).comp (f i)
  obtain ⟨h, s, hs, hlim⟩ := CompactSpace.tendsto_subseq u
  have hev (n : ℕ) : ∀ᶠ j in atTop, u (s j) n = h n := by
    have hn := ((continuous_apply n).tendsto h).comp hlim
    exact hn ((isOpen_discrete _).mem_nhds (Set.mem_singleton (h n)))
  have hcompat : ∀ m n (hmn : m ≤ n) (x : G),
      QuotientGroup.map (congruenceSubgroup n) (congruenceSubgroup m)
        (MonoidHom.id (Nottingham p)) (congruenceSubgroup_antitone hmn) (h n x) = h m x := by
    intro m n hmn x
    obtain ⟨j, hjn, hjm⟩ := ((hev n).and (hev m)).exists
    rw [← hjn, ← hjm]
    rfl
  obtain ⟨g, hg⟩ := exists_continuousMonoidHom_of_compatible h hcompat
  refine ⟨g, s, hs, ?_⟩
  intro n
  rw [hg]
  exact hev n

/-- Eventual avoidance of a congruence subgroup prevents collapse in the diagonal limit. -/
theorem exists_closedEmbedding_of_eventually_not_mem [CompactSpace G]
    (hG : TopologicallyFG G) (f : ℕ → ContinuousMonoidHom G (Nottingham p))
    (hsep : ∀ x : G, x ≠ 1 → ∃ n : ℕ, ∀ᶠ i in atTop, f i x ∉ congruenceSubgroup n) :
    ∃ g : ContinuousMonoidHom G (Nottingham p), IsClosedEmbedding g := by
  obtain ⟨g, s, hs, hlim⟩ := exists_diagonal_limit hG f
  refine ⟨g, g.continuous.isClosedEmbedding ?_⟩
  apply (MonoidHom.ker_eq_bot_iff g.toMonoidHom).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  change g x = 1 at hx
  by_contra hne
  obtain ⟨n, hn⟩ := hsep x hne
  obtain ⟨j, hj, havoid⟩ := ((hlim n).and (hs.tendsto_atTop.eventually hn)).exists
  have he : (QuotientGroup.mk (f (s j) x) : Nottingham p ⧸ congruenceSubgroup n) = 1 := by
    have hv := congrArg (fun h : ContinuousMonoidHom G
      ((congruenceQuotientDiagram (p := p)).obj n) => h x) hj
    change (QuotientGroup.mk (f (s j) x) : Nottingham p ⧸ congruenceSubgroup n) =
      QuotientGroup.mk (g x) at hv
    exact hv.trans (congrArg
      (fun y : Nottingham p => (QuotientGroup.mk y : Nottingham p ⧸ congruenceSubgroup n)) hx)
  exact havoid ((QuotientGroup.eq_one_iff (f (s j) x)).mp he)

end Camina1997.Nottingham
