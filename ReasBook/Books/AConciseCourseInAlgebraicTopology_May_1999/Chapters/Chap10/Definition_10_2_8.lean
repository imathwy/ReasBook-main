import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_7

open Topology
open Topology.RelCWComplex
open ContinuousMap.Homotopy
open scoped unitInterval

universe u

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopy` is the canonical owner for a
-- homotopy, and `ContinuousMap.Homotopy.prodSwap` is the repository's textbook-order bridge to
-- the map `X × I ⟶ Y` used by the relative pair API on absolute pairs.

namespace Topology.CWComplex

variable {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]

variable {Y : Type u} [TopologicalSpace Y] [CWComplex (Set.univ : Set Y)]

/-- The absolute pair map `(X, ∅) ⟶ (Y, ∅)` induced by a continuous map `f : X ⟶ Y`. -/
abbrev continuousMapPairHom (f : C(X, Y)) :
    SpacePair.Hom
      (relativeSpacePair (Set.univ : Set X) (∅ : Set X))
      (relativeSpacePair (Set.univ : Set Y) (∅ : Set Y)) where
  hom :=
    TopCat.ofHom
      ⟨fun x ↦ ⟨f x.1, Set.mem_univ _⟩,
        (f.continuous.comp continuous_subtype_val).subtype_mk fun _ ↦ Set.mem_univ _⟩
  map_subspace' := fun {_} hx ↦ False.elim hx

/-- Evaluating `continuousMapPairHom f` at `x : X` recovers `f x`. -/
@[simp]
theorem continuousMapPairHom_apply (f : C(X, Y)) (x : X) :
    (continuousMapPairHom f).hom ⟨x, Set.mem_univ x⟩ = ⟨f x, Set.mem_univ _⟩ := sorry

/-- The absolute pair map `((X × I), ∅) ⟶ (Y, ∅)` associated to a homotopy
`H : f₀ ≃ f₁`, via the textbook-order map `H.prodSwap : X × I ⟶ Y`. -/
abbrev homotopyCylinderPairHom {f₀ f₁ : C(X, Y)} (H : f₀.Homotopy f₁) :
    SpacePair.Hom
      (relativeSpacePair (Set.univ : Set (X × I)) (∅ : Set (X × I)))
      (relativeSpacePair (Set.univ : Set Y) (∅ : Set Y)) where
  hom :=
    TopCat.ofHom
      ⟨fun x ↦ ⟨prodSwap H x.1, Set.mem_univ _⟩,
        ((prodSwap H).continuous.comp continuous_subtype_val).subtype_mk
          fun _ ↦ Set.mem_univ _⟩
  map_subspace' := fun {_} hx ↦ False.elim hx

/-- Definition 10.2.8: a cellular homotopy between cellular maps `f₀, f₁ : X ⟶ Y` consists of a
chosen CW structure on `X × I` of the type supplied by Lemma 10.2.7 together with a homotopy
whose underlying map `X × I ⟶ Y` is cellular for that chosen cylinder structure. Semantic recall
via `lean_leansearch`: `ContinuousMap.Homotopy.apply_zero` and
`ContinuousMap.HomotopyWith.apply_one` are the canonical endpoint-evaluation theorems, so the
endpoint cellularity belongs in companion API on this owner. -/
structure CellularHomotopy (f₀ f₁ : C(X, Y)) where
  /-- The chosen CW structure on `X × I` used to test cellularity of the homotopy. -/
  cylinderCW : CWComplex (Set.univ : Set (X × I))
  /-- The chosen cylinder CW structure satisfies the boundary-subcomplex and relative-cell
  indexing condition of Lemma 10.2.7. -/
  cylinderCW_spec : IsCylinderCWStructure X cylinderCW
  /-- The underlying homotopy `f₀ ≃ f₁`. -/
  toHomotopy : f₀.Homotopy f₁
  /-- The corresponding map `X × I ⟶ Y` is cellular for the chosen cylinder CW structure. -/
  isCellular : letI := cylinderCW; IsCellularMap (homotopyCylinderPairHom toHomotopy)

/-- A cellular homotopy can be used as its underlying homotopy. -/
instance instCoeHomotopy (f₀ f₁ : C(X, Y)) :
    Coe (CellularHomotopy f₀ f₁) (f₀.Homotopy f₁) :=
  ⟨CellularHomotopy.toHomotopy⟩

instance instIsCellularMapHomotopyCylinder
    {f₀ f₁ : C(X, Y)} (H : CellularHomotopy f₀ f₁) :
    letI := H.cylinderCW
    IsCellularMap (homotopyCylinderPairHom H.toHomotopy) :=
  H.isCellular

/-- The cylinder map underlying a cellular homotopy is cellular. -/
theorem CellularHomotopy.isCellularMap
    {f₀ f₁ : C(X, Y)} (H : CellularHomotopy f₀ f₁) :
    letI := H.cylinderCW
    IsCellularMap (homotopyCylinderPairHom H.toHomotopy) :=
  H.isCellular

instance instIsCellularMapLeft
    {f₀ f₁ : C(X, Y)} (H : CellularHomotopy f₀ f₁) :
    IsCellularMap (continuousMapPairHom f₀) := by
  sorry

/-- The left endpoint of a cellular homotopy is a cellular map `X ⟶ Y`. -/
theorem CellularHomotopy.left_isCellular
    {f₀ f₁ : C(X, Y)} (H : CellularHomotopy f₀ f₁) :
    IsCellularMap (continuousMapPairHom f₀) :=
  instIsCellularMapLeft H

instance instIsCellularMapRight
    {f₀ f₁ : C(X, Y)} (H : CellularHomotopy f₀ f₁) :
    IsCellularMap (continuousMapPairHom f₁) := by
  sorry

/-- The right endpoint of a cellular homotopy is a cellular map `X ⟶ Y`. -/
theorem CellularHomotopy.right_isCellular
    {f₀ f₁ : C(X, Y)} (H : CellularHomotopy f₀ f₁) :
    IsCellularMap (continuousMapPairHom f₁) :=
  instIsCellularMapRight H

end Topology.CWComplex
