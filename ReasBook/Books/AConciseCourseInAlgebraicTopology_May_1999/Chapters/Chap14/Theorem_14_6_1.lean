import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.ExpandingUnion

open CategoryTheory
open CategoryTheory.Limits
open SpacePair

noncomputable section

universe u

-- Semantic recall via `lean_leansearch` surfaced filtered-colimit infrastructure in `ModuleCat`
-- but no chapter-local continuity owner for homology. The repository already uses the shared
-- `ExpandingUnion` owner for the analogous Milnor continuity statement in cohomology, so this
-- file reuses that stage API and states the homology comparison as the canonical sequential-
-- colimit map.

namespace ExpandingUnion

variable {X : TopCat.{u}}

/-- The functor `ULift ℕ ⥤ ℕ` forgetting the universe lift on the sequential index. -/
private def sequentialIndexFunctor : ULift.{u} ℕ ⥤ ℕ where
  obj n := n.down
  map {_i _j} h := homOfLE h.down.down
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The absolute pair map `(X_n, ∅) ⟶ (X_(n + 1), ∅)` induced by the stage inclusion
`X_n ↪ X_(n + 1)`. -/
abbrev stageAbsoluteStep (U : ExpandingUnion X) (n : ℕ) :
    absolute (U.stageSpace n) ⟶ absolute (U.stageSpace (n + 1)) :=
  { hom := U.stageStep n
    map_subspace' := by
      intro x hx
      cases hx }

/-- The absolute pair map `(X_n, ∅) ⟶ (X, ∅)` induced by the inclusion of the `n`th stage into
the ambient space. -/
abbrev stageAbsoluteInclusion (U : ExpandingUnion X) (n : ℕ) :
    absolute (U.stageSpace n) ⟶ absolute X :=
  { hom := U.stageInclusion n
    map_subspace' := by
      intro x hx
      cases hx }

/-- The stage-to-stage and stage-to-ambient absolute pair maps compose to the direct stage-to-
ambient inclusion. -/
theorem stageAbsoluteStep_comp_stageAbsoluteInclusion (U : ExpandingUnion X) (n : ℕ) :
    U.stageAbsoluteStep n ≫ U.stageAbsoluteInclusion (n + 1) = U.stageAbsoluteInclusion n := by
  apply SpacePair.hom_ext
  rfl

/-- The degree-`q` absolute homology `ℤ`-module `E_q(X_n)` of the `n`th stage of an expanding
union. -/
abbrev homologyStage
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) : ModuleCat.{u} ℤ :=
  (H.homology q).obj (absolute (U.stageSpace n))

/-- The map `E_q(X_n) ⟶ E_q(X_(n + 1))` induced by the stage inclusion `X_n ↪ X_(n + 1)`. -/
abbrev homologyStepMap
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    U.homologyStage H q n ⟶ U.homologyStage H q (n + 1) :=
  (H.homology q).map (U.stageAbsoluteStep n)

/-- The sequential `ModuleCat ℤ`-diagram `n ↦ E_q(X_n)` attached to an expanding union. -/
def homologyDiagram
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) : ℕ ⥤ ModuleCat.{u} ℤ :=
  Functor.ofSequence (U.homologyStepMap H q)

@[simp] theorem homologyDiagram_map_succ
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    (U.homologyDiagram H q).map (homOfLE (Nat.le_add_right n 1)) = U.homologyStepMap H q n := by
  exact Functor.ofSequence_map_homOfLE_succ (U.homologyStepMap H q) n

/-- The degree-`q` map `E_q(X_n) ⟶ E_q(X)` induced by the inclusion of the `n`th stage into the
ambient space. -/
abbrev homologyCoconeMap
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    U.homologyStage H q n ⟶ (H.homology q).obj (absolute X) :=
  (H.homology q).map (U.stageAbsoluteInclusion n)

/-- The stagewise homology maps to `E_q(X)` are compatible with the successor maps in the
sequential diagram. -/
theorem homologyCoconeMap_naturality
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ℕ) :
    (U.homologyDiagram H q).map (homOfLE (Nat.le_add_right n 1)) ≫
        U.homologyCoconeMap H q (n + 1) =
      U.homologyCoconeMap H q n := by
  rw [homologyDiagram_map_succ]
  simpa [homologyStepMap, homologyCoconeMap] using
    congrArg ((H.homology q).map) (U.stageAbsoluteStep_comp_stageAbsoluteInclusion n)

/-- The canonical cocone from the sequential diagram `n ↦ E_q(X_n)` to `E_q(X)`. -/
def homologyCocone
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) : Cocone (U.homologyDiagram H q) where
  pt := (H.homology q).obj (absolute X)
  ι := NatTrans.ofSequence (U.homologyCoconeMap H q) (U.homologyCoconeMap_naturality H q)

/-- The large-universe sequential diagram used to form filtered colimits of `n ↦ E_q(X_n)` in
`ModuleCat ℤ`. -/
def homologyColimitDiagram
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) : ULift.{u} ℕ ⥤ ModuleCat.{u} ℤ :=
  sequentialIndexFunctor ⋙ U.homologyDiagram H q

/-- The canonical cocone from the large-universe sequential homology diagram to `E_q(X)`. -/
def homologyColimitCocone
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) : Cocone (U.homologyColimitDiagram H q) :=
  (U.homologyCocone H q).whisker sequentialIndexFunctor

/-- The filtered colimit of the sequential absolute-homology diagram `n ↦ E_q(X_n)` in
`ModuleCat ℤ`. -/
abbrev homologyColimit
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) :=
  ModuleCat.FilteredColimits.colimit (U.homologyColimitDiagram H q)

/-- The canonical comparison morphism `colim_i E_q(X_i) ⟶ E_q(X)` associated to an expanding
union `X = ⋃ i, X_i`. -/
noncomputable def homologyColimitDesc
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) :
    U.homologyColimit H q ⟶ (H.homology q).obj (absolute X) :=
  (ModuleCat.FilteredColimits.colimitCoconeIsColimit (U.homologyColimitDiagram H q)).desc
    (U.homologyColimitCocone H q)

@[reassoc, simp]
theorem homologyColimit_ι_desc
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (n : ULift.{u} ℕ) :
    (ModuleCat.FilteredColimits.colimitCocone (U.homologyColimitDiagram H q)).ι.app n ≫
        U.homologyColimitDesc H q =
      U.homologyCoconeMap H q n.down := by
  simpa [homologyColimitDesc] using
    ModuleCat.FilteredColimits.ι_colimitDesc
      (U.homologyColimitDiagram H q) (U.homologyColimitCocone H q) n

/-- Theorem 14.6.1: if `X` is the union of an expanding sequence `X_i`, then for every Chapter 13
pair homology theory `H` and every degree `q`, the canonical comparison morphism
`colim_i E_q(X_i) ⟶ E_q(X)`, formalized here on absolute pairs as
`ExpandingUnion.homologyColimitDesc`, is an isomorphism in `ModuleCat ℤ`. -/
instance homologyColimitDesc_isIso
    (U : ExpandingUnion X) {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) :
    IsIso (U.homologyColimitDesc H q) := sorry

end ExpandingUnion
