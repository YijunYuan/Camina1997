/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.Nottingham.Congruence
public import Mathlib.Topology.Algebra.FilterBasis

/-!
# The congruence topology on the Nottingham group

The congruence subgroups define a Hausdorff group topology with a countable
neighborhood basis. Reference: Camina (1997), p. 102.
-/

@[expose] public section

namespace Camina1997.Nottingham

open Filter Set
open scoped Topology Pointwise

variable {p : ℕ} [Fact p.Prime]

/-- The normal congruence subgroups form a group filter basis at the identity. -/
@[instance_reducible]
noncomputable def congruenceFilterBasis : GroupFilterBasis (Nottingham p) where
  sets := Set.range fun n ↦ (congruenceSubgroup (p := p) n : Set (Nottingham p))
  nonempty := ⟨_, ⟨0, rfl⟩⟩
  inter_sets := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    refine ⟨_, ⟨max n m, rfl⟩, ?_⟩
    intro g hg
    exact ⟨congruenceSubgroup_antitone (le_max_left _ _) hg,
      congruenceSubgroup_antitone (le_max_right _ _) hg⟩
  one' := by
    rintro _ ⟨n, rfl⟩
    exact (congruenceSubgroup n).one_mem
  mul' := by
    rintro _ ⟨n, rfl⟩
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    rintro _ ⟨g, hg, h, hh, rfl⟩
    exact (congruenceSubgroup n).mul_mem hg hh
  inv' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, fun _ hg ↦ (congruenceSubgroup n).inv_mem hg⟩
  conj' := by
    rintro g _ ⟨n, rfl⟩
    exact ⟨_, ⟨n, rfl⟩, fun h hh ↦ (congruenceSubgroup_normal n).conj_mem h hh g⟩

/-- The congruence topology of the Nottingham group. -/
noncomputable instance instTopologicalSpace : TopologicalSpace (Nottingham p) :=
  congruenceFilterBasis.topology

instance instIsTopologicalGroup : IsTopologicalGroup (Nottingham p) :=
  congruenceFilterBasis.isTopologicalGroup

/-- Congruence cosets form a countable neighborhood basis at each element. -/
theorem nhds_hasBasis (g : Nottingham p) :
    (𝓝 g).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (fun h ↦ g * h) '' (congruenceSubgroup (p := p) n : Set (Nottingham p))) := by
  apply (congruenceFilterBasis.nhds_hasBasis g).to_hasBasis
  · rintro _ ⟨n, rfl⟩
    exact ⟨n, trivial, subset_rfl⟩
  · intro n _
    exact ⟨_, ⟨n, rfl⟩, subset_rfl⟩

/-- The congruence subgroups form a countable neighborhood basis at the identity. -/
theorem nhds_one_hasBasis :
    (𝓝 (1 : Nottingham p)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ (congruenceSubgroup (p := p) n : Set (Nottingham p))) := by
  simpa using nhds_hasBasis (1 : Nottingham p)

instance instFirstCountableTopology : FirstCountableTopology (Nottingham p) :=
  ⟨fun g ↦ (nhds_hasBasis g).isCountablyGenerated⟩

instance instT2Space : T2Space (Nottingham p) := by
  apply (congruenceFilterBasis.t2Space_iff_sInter_subset rfl).mpr
  intro g hg
  apply eq_one_of_mem_congruenceSubgroup
  intro n
  exact hg _ ⟨n, rfl⟩

theorem congruenceSubgroup_mem_nhds_one (n : ℕ) :
    (congruenceSubgroup (p := p) n : Set (Nottingham p)) ∈ 𝓝 (1 : Nottingham p) :=
  nhds_one_hasBasis.mem_of_mem trivial

/-- Each congruence subgroup is open in the congruence topology. -/
theorem isOpen_congruenceSubgroup (n : ℕ) :
    IsOpen (congruenceSubgroup (p := p) n : Set (Nottingham p)) := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  apply (nhds_hasBasis g).mem_iff.mpr
  refine ⟨n, trivial, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  exact (congruenceSubgroup n).mul_mem hg hh

end Camina1997.Nottingham
