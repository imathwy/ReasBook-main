import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Maps.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4.FiniteGraph

open Topology
open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

/-- A realized graph is embeddable in the plane when its source-faithful realization admits a
topological embedding into `ℝ × ℝ`. -/
def embeddableInPlane (boundary : J ↪ Fin 2 → X₀) : Prop :=
  let _ : TopologicalSpace (graphRealization boundary) :=
    graphRealizationSourceFaithfulTopologicalSpace boundary
  ∃ f : graphRealization boundary → ℝ × ℝ, IsEmbedding f
