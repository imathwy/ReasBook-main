import Mathlib.Topology.CWComplex.Classical.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_3_1

open Topology.RelCWComplex

universe u

-- `Topology.RelCWComplex` is the canonical mathlib owner for relative CW pairs, Chapter 6
-- formalizes the source HEP notion of cofibration as `IsCofibration`, and
-- `relCWComplexBaseInclusion` is the current-repository canonical inclusion `D ↪ C`.

variable {X : Type u} [TopologicalSpace X] {C D : Set X}

namespace Topology.RelCWComplex

/-- Corollary 10.3.2: the inclusion `D → C` of a relative CW complex is a cofibration. -/
theorem isCofibration_inclusion [RelCWComplex C D] :
    IsCofibration (relCWComplexBaseInclusion C) :=
  sorry

end Topology.RelCWComplex
