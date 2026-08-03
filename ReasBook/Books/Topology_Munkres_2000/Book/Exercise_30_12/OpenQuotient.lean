module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Maps.OpenQuotient

public section

open Set Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- The range factorization of a continuous open map is an open quotient map. -/
theorem IsOpenMap.isOpenQuotientMap_rangeFactorization (hopen : IsOpenMap f)
    (hcont : Continuous f) : IsOpenQuotientMap (rangeFactorization f) where
  surjective := rangeFactorization_surjective
  continuous := hcont.rangeFactorization
  isOpenMap := hopen.subtype_mk fun x ↦ mem_range_self x

/-- The codomain of an open quotient map from a first-countable space is first-countable. -/
theorem IsOpenQuotientMap.firstCountableTopology [FirstCountableTopology X]
    (h : IsOpenQuotientMap f) : FirstCountableTopology Y where
  nhds_generated_countable y := by
    obtain ⟨x, rfl⟩ := h.surjective y
    rw [← h.map_nhds_eq x]
    infer_instance

/-- The codomain of an open quotient map from a second-countable space is second-countable. -/
theorem IsOpenQuotientMap.secondCountableTopology [SecondCountableTopology X]
    (h : IsOpenQuotientMap f) : SecondCountableTopology Y :=
  h.isQuotientMap.secondCountableTopology h.isOpenMap
