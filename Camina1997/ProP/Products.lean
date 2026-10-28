/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ProP.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Compactness.Compact

/-!
# Products and closed subgroups of pro-`p` groups

An arbitrary product of finite discrete `p`-groups is pro-`p`. Its neighborhood
basis is formed by the kernels of restrictions to finitely many coordinates.
Closed subgroups of pro-`p` groups are again pro-`p`.
-/

@[expose] public section

open scoped Topology

namespace OpenNormalSubgroup

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- Pull back an open normal subgroup along a continuous group homomorphism. -/
def comap (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) :
    OpenNormalSubgroup G where
  toOpenSubgroup := N.toOpenSubgroup.comap f hf
  isNormal' := inferInstanceAs (N.toSubgroup.comap f).Normal

@[simp]
theorem mem_comap (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) (g : G) :
    g ∈ comap f hf N ↔ f g ∈ N := Iff.rfl

@[simp]
theorem comap_toSubgroup (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) :
    (comap f hf N).toSubgroup = N.toSubgroup.comap f := rfl

end OpenNormalSubgroup

namespace Camina1997.IsProPGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]

omit [Fact p.Prime] in
/-- A finite product of `p`-groups is a `p`-group. -/
theorem _root_.IsPGroup.pi {ι : Type*} [Finite ι] {A : ι → Type*} [∀ i, Group (A i)]
    (hA : ∀ i, IsPGroup p (A i)) : IsPGroup p (∀ i, A i) := by
  classical
  let := Fintype.ofFinite ι
  intro g
  choose n hn using fun i => hA i (g i)
  refine ⟨Finset.univ.sup n, ?_⟩
  funext i
  change g i ^ p ^ (Finset.univ.sup n) = 1
  have hi : n i ≤ Finset.univ.sup n := Finset.le_sup (by simp)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
  rw [hk, pow_add, pow_mul, hn i, one_pow]

/-- An arbitrary product of finite discrete `p`-groups is pro-`p`. -/
theorem pi_of_finite_discrete {ι : Type*} {A : ι → Type*} [∀ i, Group (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)] [∀ i, Finite (A i)]
    (hA : ∀ i, IsPGroup p (A i)) : IsProPGroup p (∀ i, A i) := by
  classical
  refine { nhds_one_hasBasis := ⟨fun U => ?_⟩ }
  constructor
  · intro hU
    simp only [nhds_pi, Pi.one_apply, nhds_discrete] at hU
    obtain ⟨I, hI, hIU⟩ := Filter.mem_pi_pure.mp hU
    let : Fintype I := hI.fintype
    let f : ContinuousMonoidHom (∀ i, A i) (∀ i : I, A i.val) :=
      { toFun := fun g i => g i.val
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        continuous_toFun := continuous_pi fun i => continuous_apply i.val }
    let N : OpenNormalSubgroup (∀ i, A i) :=
      { toSubgroup := f.toMonoidHom.ker
        isOpen' := f.continuous.isOpen_preimage _ (isOpen_discrete {1}) }
    refine ⟨N, ?_, ?_⟩
    · change ∃ n : ℕ, f.toMonoidHom.ker.index = p ^ n
      rw [Subgroup.index_ker]
      exact ((_root_.IsPGroup.pi fun i : I => hA i.val).to_subgroup
        f.toMonoidHom.range).exists_card_eq
    · intro g hg
      apply hIU g
      intro i hi
      exact congrFun (show f g = 1 from hg) ⟨i, hi⟩
  · rintro ⟨N, _, hNU⟩
    exact Filter.mem_of_superset N.toOpenSubgroup.mem_nhds_one hNU

/-- Closed subgroups of pro-`p` groups are pro-`p` for the subspace topology. -/
theorem of_isClosed_subgroup [IsProPGroup p G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) : IsProPGroup p H := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  refine { nhds_one_hasBasis := ⟨fun U => ?_⟩ }
  constructor
  · intro hU
    rw [nhds_subtype] at hU
    obtain ⟨N, ⟨n, hn⟩, hNU⟩ :=
      ((nhds_one_hasBasis (p := p) (G := G)).comap (Subtype.val : H → G)).mem_iff.mp hU
    refine ⟨N.comap H.subtype continuous_subtype_val, ?_, hNU⟩
    have hd : (N.toSubgroup.comap H.subtype).index ∣ p ^ n := by
      rw [Subgroup.index_comap, ← hn]
      exact N.toSubgroup.relIndex_dvd_index_of_normal _
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
    exact ⟨k, hk⟩
  · rintro ⟨N, _, hNU⟩
    exact Filter.mem_of_superset N.toOpenSubgroup.mem_nhds_one hNU

end Camina1997.IsProPGroup
