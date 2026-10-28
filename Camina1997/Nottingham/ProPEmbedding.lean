/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Diagonal
public import Camina1997.ProP.QuotientTower

/-!
# Closed embeddings from depth-preserving finite quotients

A decreasing separating finite quotient tower with depth-preserving embeddings
supplies the eventual separation needed by the continuous diagonal limit.

Reference: Camina (1997), Theorem 5, pp. 110–112.
-/

@[expose] public section

open Filter Topology

namespace Camina1997.Nottingham

variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsProPGroup p G]

/-- Depth-preserving embeddings of a separating finite quotient tower give a closed embedding. -/
theorem exists_closedEmbedding_of_quotient_depths
    (hG : TopologicallyFG G) (N : ℕ → OpenNormalSubgroup G)
    (hN : (𝓝 (1 : G)).HasAntitoneBasis (fun n => (N n : Set G)))
    (φ : ∀ n, (G ⧸ (N n).toSubgroup) →* Nottingham p)
    (hinj : ∀ n, Function.Injective (φ n))
    (hdepth : ∀ n (x : G ⧸ (N (n + 1)).toSubgroup),
      (N (n + 1)).quotientTransition (N n) (hN.antitone (Nat.le_succ n)) x ≠ 1 →
      depth (φ (n + 1) x) = depth (φ n
        ((N (n + 1)).quotientTransition (N n) (hN.antitone (Nat.le_succ n)) x))) :
    ∃ f : ContinuousMonoidHom G (Nottingham p), IsClosedEmbedding f := by
  let φc (n : ℕ) : ContinuousMonoidHom (G ⧸ (N n).toSubgroup) (Nottingham p) :=
    { toMonoidHom := φ n
      continuous_toFun := by
        let : DiscreteTopology (G ⧸ (N n).toSubgroup) :=
          inferInstanceAs (DiscreteTopology (G ⧸ (N n).toOpenSubgroup.toSubgroup))
        exact continuous_of_discreteTopology }
  let f (n : ℕ) : ContinuousMonoidHom G (Nottingham p) :=
    (φc n).comp (N n).quotientProjection
  apply exists_closedEmbedding_of_eventually_not_mem hG f
  intro x hx
  obtain ⟨n, hn⟩ := IsProPGroup.eventually_not_mem_openNormalBasis hN hx
  have hxq (m : ℕ) (hm : n ≤ m) :
      (QuotientGroup.mk x : G ⧸ (N m).toSubgroup) ≠ 1 := by
    intro he
    exact hn m hm ((QuotientGroup.eq_one_iff x).mp he)
  have hne : f n x ≠ 1 := by
    exact fun he => hxq n le_rfl ((map_eq_one_iff (φ n) (hinj n)).mp he)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp ((depth_eq_top_iff (f n x)).not.mpr hne)
  have hstable (m : ℕ) (hm : n ≤ m) : depth (f m x) = depth (f n x) := by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      exact (hdepth m (QuotientGroup.mk x) (hxq m hm)).trans ih
  refine ⟨d + 1, eventually_atTop.mpr ⟨n, ?_⟩⟩
  intro m hm
  rw [mem_congruenceSubgroup_iff_le_depth, hstable m hm, ← hd]
  exact_mod_cast Nat.not_succ_le_self d

end Camina1997.Nottingham
