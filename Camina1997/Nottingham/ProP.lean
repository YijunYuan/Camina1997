/-
Copyright (c) 2026 Archon Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon contributors
-/
module

public import Camina1997.ProP.Basic
public import Camina1997.Nottingham.Compactness
public import Camina1997.Nottingham.FiniteQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# The Nottingham group is pro-`p`

The congruence subgroups form a basis of open normal subgroups of finite
`p`-power index. Every quotient by an open normal subgroup is a finite `p`-group.

Reference: Camina (1997), p. 102.
-/

@[expose] public section

namespace Camina1997.Nottingham

open scoped Topology

variable {p : ℕ} [Fact p.Prime]

/-- The congruence subgroups bundled as open normal subgroups. -/
def openNormalCongruenceSubgroup (n : ℕ) : OpenNormalSubgroup (Nottingham p) where
  toSubgroup := congruenceSubgroup n
  isOpen' := isOpen_congruenceSubgroup n

/-- Every open normal subgroup contains a congruence subgroup. -/
theorem exists_openNormalCongruenceSubgroup_le (N : OpenNormalSubgroup (Nottingham p)) :
    ∃ n, openNormalCongruenceSubgroup n ≤ N := by
  obtain ⟨n, _, hn⟩ := nhds_one_hasBasis.mem_iff.mp N.toOpenSubgroup.mem_nhds_one
  exact ⟨n, hn⟩

/-- The congruence basis and compactness make the Nottingham group a pro-`p` group. -/
instance instIsProPGroup : IsProPGroup p (Nottingham p) where
  toIsTopologicalGroup := inferInstance
  toCompactSpace := inferInstance
  toT2Space := inferInstance
  nhds_one_hasBasis := by
    apply nhds_one_hasBasis.to_hasBasis'
    · intro n _
      exact ⟨openNormalCongruenceSubgroup n, ⟨n - 1, index_congruenceSubgroup n⟩,
        Set.Subset.rfl⟩
    · intro N _
      exact N.toOpenSubgroup.mem_nhds_one

/-- Each congruence quotient is a finite `p`-group. -/
theorem isPGroup_quotient_congruenceSubgroup (n : ℕ) :
    IsPGroup p (Nottingham p ⧸ congruenceSubgroup n) :=
  IsPGroup.of_card (card_quotient n)

/-- Every open normal quotient of the Nottingham group is a `p`-group. -/
theorem isPGroup_quotient_openNormalSubgroup (N : OpenNormalSubgroup (Nottingham p)) :
    IsPGroup p (Nottingham p ⧸ N.toSubgroup) :=
  IsProPGroup.isPGroup_quotient N

end Camina1997.Nottingham
