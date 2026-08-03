module

import Topology_Munkres_2000.Book.Theorem_22_2.Factorization
public import Mathlib.Topology.Maps.Basic

public section

namespace Topology.IsQuotientMap

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Theorem 22.2 (1): A map constant on the fibers of a quotient map descends to
the quotient. -/
theorem exists_descend {p : X → Y} (hp : IsQuotientMap p) {g : X → Z}
    (hg : Function.FactorsThrough g p) : ∃ f : Y → Z, f ∘ p = g :=
  hp.surjective.exists_comp_eq hg

/-- A map constant on the fibers of a quotient map has a unique descent. -/
theorem existsUnique_descend {p : X → Y} (hp : IsQuotientMap p) {g : X → Z}
    (hg : Function.FactorsThrough g p) : ∃! f : Y → Z, f ∘ p = g :=
  hp.surjective.existsUnique_comp_eq hg

variable [TopologicalSpace Z]

/-- Theorem 22.2 (2): For a map induced through a quotient map, continuity is
equivalent before and after descent. -/
theorem continuous_iff_of_comp_eq {p : X → Y} (hp : IsQuotientMap p) {g : X → Z}
    {f : Y → Z} (hfp : f ∘ p = g) : Continuous f ↔ Continuous g := by
  rw [← hfp]
  exact hp.continuous_iff

/-- Theorem 22.2 (3): For a map induced through a quotient map, the quotient-map
property is equivalent before and after descent. -/
theorem isQuotientMap_iff_of_comp_eq {p : X → Y} (hp : IsQuotientMap p) {g : X → Z}
    {f : Y → Z} (hfp : f ∘ p = g) : IsQuotientMap f ↔ IsQuotientMap g := by
  rw [← hfp]
  exact hp.of_comp_iff.symm

end Topology.IsQuotientMap
