import Mathlib.Data.PNat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_2_7

open scoped TopCat Topology

noncomputable section

universe u w

-- Semantic recall: Chapter 9 already provides the canonical owner `sphereBasepoint`, while
-- Definitions 13.2.6 and 13.2.7 provide the homotopy-group and suspension-map owners used below.
-- This file therefore keeps only the source-facing wedge model and its suspension-map statement.

/-- The raw carrier for the wedge of `n`-spheres indexed by `ι`: a distinguished wedge point
together with the disjoint union of the sphere summands before identifying their basepoints. -/
private abbrev wedgeOfNSpheresRaw
    (n : ℕ) (ι : Type w) : Type w :=
  Unit ⊕ Sigma fun _ : ι ↦ 𝕊 n

/-- The points of `wedgeOfNSpheresRaw n ι` that are collapsed to the common wedge point. -/
private def wedgeOfNSpheresBasepointLocus
    (n : ℕ) (ι : Type w) : wedgeOfNSpheresRaw n ι → Prop
  | Sum.inl _ => True
  | Sum.inr ⟨_, x⟩ => x = sphereBasepoint n

/-- The equivalence relation presenting the wedge: points are identified exactly when they agree,
or when both lie in the basepoint locus. -/
private def wedgeOfNSpheresRel
    (n : ℕ) (ι : Type w) :
    wedgeOfNSpheresRaw n ι → wedgeOfNSpheresRaw n ι → Prop :=
  fun x y ↦ x = y ∨
    wedgeOfNSpheresBasepointLocus n ι x ∧ wedgeOfNSpheresBasepointLocus n ι y

/-- Reflexivity of `wedgeOfNSpheresRel`. -/
private theorem wedgeOfNSpheresRel_refl
    (n : ℕ) (ι : Type w) :
    ∀ x : wedgeOfNSpheresRaw n ι, wedgeOfNSpheresRel n ι x x := sorry

/-- Symmetry of `wedgeOfNSpheresRel`. -/
private theorem wedgeOfNSpheresRel_symm
    (n : ℕ) (ι : Type w) :
    ∀ ⦃x y : wedgeOfNSpheresRaw n ι⦄,
      wedgeOfNSpheresRel n ι x y → wedgeOfNSpheresRel n ι y x := sorry

/-- Transitivity of `wedgeOfNSpheresRel`. -/
private theorem wedgeOfNSpheresRel_trans
    (n : ℕ) (ι : Type w) :
    ∀ ⦃x y z : wedgeOfNSpheresRaw n ι⦄,
      wedgeOfNSpheresRel n ι x y →
        wedgeOfNSpheresRel n ι y z →
          wedgeOfNSpheresRel n ι x z := sorry

/-- The setoid presenting the wedge of `n`-spheres indexed by `ι`. -/
private def wedgeOfNSpheresSetoid
    (n : ℕ) (ι : Type w) : Setoid (wedgeOfNSpheresRaw n ι) where
  r := wedgeOfNSpheresRel n ι
  iseqv := ⟨
    fun x ↦ wedgeOfNSpheresRel_refl n ι x,
    fun {_ _} h ↦ wedgeOfNSpheresRel_symm n ι h,
    fun {_ _ _} hxy hyz ↦ wedgeOfNSpheresRel_trans n ι hxy hyz⟩

/-- The quotient carrier of the wedge of `n`-spheres indexed by `ι`. -/
private abbrev wedgeOfNSpheresType
    (n : ℕ) (ι : Type w) : Type w :=
  Quotient (wedgeOfNSpheresSetoid n ι)

/-- The wedge quotient carries the compactly generated replacement of its quotient topology. -/
private instance wedgeOfNSpheresTypeTopologicalSpace
    (n : ℕ) (ι : Type w) : TopologicalSpace (wedgeOfNSpheresType n ι) :=
  TopologicalSpace.compactlyGenerated.{w, w} (Quotient (wedgeOfNSpheresSetoid n ι))

/-- The quotient carrier of the wedge of `n`-spheres is compactly generated. -/
private instance wedgeOfNSpheresType_uCompactlyGeneratedSpace
    (n : ℕ) (ι : Type w) :
    UCompactlyGeneratedSpace.{w} (wedgeOfNSpheresType n ι) := sorry

/-- The distinguished wedge point in `wedgeOfNSpheresType n ι`. -/
private abbrev wedgeOfNSpheresPoint
    (n : ℕ) (ι : Type w) : wedgeOfNSpheresType n ι :=
  Quotient.mk'' (Sum.inl ())

/-- The canonical wedge of `n`-spheres indexed by `ι`, regarded as a pointed compactly generated
space. -/
abbrev wedgeOfNSpheres
    (n : ℕ) (ι : Type w) : PointedCompactlyGenerated.{w, w} :=
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (wedgeOfNSpheresType n ι))
    (wedgeOfNSpheresPoint n ι)

/-- The canonical indexed wedge `wedgeOfNSpheres (n : ℕ) ι` for a positive dimension `n`
satisfies the bijectivity conclusion of Lemma 13.2.8. -/
theorem provisionalReducedGroupSuspensionMap_bijective_of_wedgeOfNSpheresModel
    (n : ℕ+) (ι : Type w) :
    Function.Bijective
      (provisionalReducedGroupSuspensionMap (n : ℕ) (wedgeOfNSpheres (n : ℕ) ι)) := sorry

/-- Lemma 13.2.8. If `X` is a wedge of `n`-spheres, then the provisional suspension map
`H'_n(X) → H'_(n + 1)(ΣX)` is bijective. In this file, the hypothesis that `X` is a wedge of
positive-dimensional `n`-spheres is expressed by a pointed-space isomorphism
`hX : X ≅ wedgeOfNSpheres (n : ℕ) ι`. -/
theorem provisionalReducedGroupSuspensionMap_bijective_of_wedgeOfNSpheres
    (n : ℕ+) (X : PointedCompactlyGenerated.{w, w}) (ι : Type w)
    (hX : X ≅ wedgeOfNSpheres (n : ℕ) ι) :
    Function.Bijective
      (provisionalReducedGroupSuspensionMap (n : ℕ) X) := sorry
