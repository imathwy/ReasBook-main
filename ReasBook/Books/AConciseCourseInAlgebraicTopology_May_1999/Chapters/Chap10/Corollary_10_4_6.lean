import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_4_5

open Topology
open Topology.RelCWComplex

universe u

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopic` is the canonical owner for
-- ordinary homotopy classes of maps, and Chapter 10 already formalizes absolute cellular maps by
-- applying `IsCellularMap` to `continuousMapPairHom` and cellular homotopies by the structure
-- `CellularHomotopy`.

namespace ContinuousMap

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]

/-- An ordinary map between CW complexes is cellular when its induced absolute pair map is
cellular. This is the source-facing bridge from Chapter 10's pair-level owner to ordinary
continuous maps between CW complexes. -/
abbrev IsCellular (f : C(X, Y)) : Prop :=
  Topology.RelCWComplex.IsCellularMap (Topology.CWComplex.continuousMapPairHom f)

end ContinuousMap

namespace Topology.CWComplex

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]

/-- Corollary 10.4.6 (1): for CW complexes `X` and `Y`, every map `f : X ⟶ Y` is homotopic to a
cellular map. -/
theorem exists_cellularApproximation (f : C(X, Y)) :
    ∃ g : C(X, Y), g.IsCellular ∧ f.Homotopic g := by
  sorry

namespace ContinuousMap.Homotopic

variable {f₀ f₁ : C(X, Y)}

/-- Corollary 10.4.6 (2): a homotopy between cellular maps of CW complexes can be replaced by a
cellular homotopy. This is the ordinary-map specialization of the relative cellular approximation
theorem on the cylinder relative to its boundary. -/
theorem nonempty_cellularHomotopy (h : f₀.Homotopic f₁)
    (hf₀ : f₀.IsCellular) (hf₁ : f₁.IsCellular) :
    Nonempty (CellularHomotopy f₀ f₁) := by
  sorry

end ContinuousMap.Homotopic

/-- Corollary 10.4.6 (2): if cellular maps `f₀, f₁ : X ⟶ Y` are homotopic, then they are
cellularly homotopic. -/
theorem exists_cellularHomotopy_of_homotopic_of_isCellular {f₀ f₁ : C(X, Y)}
    (hf₀ : f₀.IsCellular) (hf₁ : f₁.IsCellular) (h : f₀.Homotopic f₁) :
    Nonempty (CellularHomotopy f₀ f₁) :=
  ContinuousMap.Homotopic.nonempty_cellularHomotopy h hf₀ hf₁

end Topology.CWComplex
