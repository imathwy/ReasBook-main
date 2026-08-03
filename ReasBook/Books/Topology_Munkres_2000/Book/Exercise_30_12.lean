module

public import Topology_Munkres_2000.Book.Exercise_30_12.OpenQuotient

public section

open Set

universe u v

/-- Exercise 30.12 (1): A continuous open map sends a first-countable space to a
first-countable image. -/
theorem IsOpenMap.firstCountableTopology_range {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [FirstCountableTopology X] {f : X → Y}
    (hopen : IsOpenMap f) (hcont : Continuous f) :
    FirstCountableTopology (range f) :=
  (hopen.isOpenQuotientMap_rangeFactorization hcont).firstCountableTopology

/-- Exercise 30.12 (2): A continuous open map sends a second-countable space to a
second-countable image. -/
theorem IsOpenMap.secondCountableTopology_range {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [SecondCountableTopology X] {f : X → Y}
    (hopen : IsOpenMap f) (hcont : Continuous f) :
    SecondCountableTopology (range f) :=
  (hopen.isOpenQuotientMap_rangeFactorization hcont).secondCountableTopology
