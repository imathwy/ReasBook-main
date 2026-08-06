import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Homotopy.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Sequence_14_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" =>
  CategoryTheory.ObjectProperty.FullSubcategory
    (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace)

-- Semantic recall via `lean_leansearch` did not surface a source-exact owner for suspension in
-- reduced homology before the later axiomatized theory. Local Chapter 14 precedent already fixes
-- `basedReducedPair`, `ReducedQuotientMap`, and the quotient comparison of Theorem 14.2.1, so
-- this file records the theorem relative to explicit cone and suspension comparison data on the
-- full subcategory of nondegenerately based spaces.

/-- The reduced-pair functor on nondegenerately based spaces. -/
abbrev nBasedReducedPairFunctor
    [CategoryWithCofibrations BasedSpace] :
    NBasedSpace ⥤ SpacePair where
  obj X := basedReducedPair X.obj
  map := fun {X Y} f ↦ basedMapReducedPairHom f.hom
  map_id := by
    intro X
    apply SpacePair.hom_ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply SpacePair.hom_ext
    rfl

/-- Reduced homology in degree `q`, restricted to nondegenerately based spaces. -/
abbrev nBasedReducedHomologyFunctor
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ) :
    NBasedSpace ⥤ ModuleCat.{u} ℤ :=
  nBasedReducedPairFunctor ⋙ H.homology q

/-- A suspension model on nondegenerately based spaces: a chosen suspension functor together
with a cone functor, cofibration inclusions of the bases into their cones, contractibility of the
cones, and quotient identifications realizing each suspension as the corresponding cone quotient.
-/
structure ReducedSuspensionModel
    [CategoryWithCofibrations BasedSpace] where
  /-- The chosen suspension endofunctor on nondegenerately based spaces. -/
  suspension : NBasedSpace ⥤ NBasedSpace
  /-- A chosen based cone on each nondegenerately based space. -/
  cone : NBasedSpace ⥤ BasedSpace
  /-- The inclusion of the base into its cone. -/
  coneBaseInclusion : ∀ X : NBasedSpace, C(X.obj.right, (cone.obj X).right)
  /-- The chosen basepoint of the cone lies on the image of the base inclusion. -/
  coneBaseBasepoint_mem :
    ∀ X : NBasedSpace,
      underTopBasepoint (cone.obj X) ∈ Set.range (coneBaseInclusion X)
  /-- The chosen base inclusion identifies `X` with the corresponding based subspace of its cone.
  -/
  coneBaseIso :
    ∀ X : NBasedSpace,
      X.obj ≅
        basedSubspace
          (cone.obj X)
          (Set.range (coneBaseInclusion X))
          (coneBaseBasepoint_mem X)
  /-- The cone inclusion is natural with respect to maps of nondegenerately based spaces. -/
  coneBaseInclusion_natural :
    ∀ {X Y : NBasedSpace} (f : X ⟶ Y) (x : X.obj.right),
      (cone.map f).right.hom (coneBaseInclusion X x) =
        coneBaseInclusion Y (f.hom.right x)
  /-- The base inclusion is a cofibration, so Theorem 14.2.1 applies to the cone quotient. -/
  coneBaseCofibration : ∀ X : NBasedSpace, IsCofibration.{u, u, u} (coneBaseInclusion X)
  /-- Each chosen cone is contractible. -/
  coneContractible : ∀ X : NBasedSpace, ContractibleSpace (cone.obj X).right
  /-- The suspension of `X` is identified with the quotient of the cone of `X` by its base. -/
  quotientComparison :
    ∀ X : NBasedSpace,
      ReducedQuotientMap
        (cone.obj X).right
        (Set.range (coneBaseInclusion X))
        (suspension.obj X).obj
  /-- The chosen quotient comparisons are natural with respect to maps of nondegenerately based
  spaces. -/
  quotientComparison_natural :
    ∀ {X Y : NBasedSpace} (f : X ⟶ Y) (x : (cone.obj X).right),
      (quotientComparison Y).quotientMap.hom ((cone.map f).right.hom x) =
        (suspension.map f).hom.right ((quotientComparison X).quotientMap.hom x)

/-- The based subspace of the chosen cone cut out by the image of the base inclusion. -/
abbrev ReducedSuspensionModel.coneBaseSubspace
    [CategoryWithCofibrations BasedSpace] (S : ReducedSuspensionModel) (X : NBasedSpace) :
    BasedSpace :=
  basedSubspace
    (S.cone.obj X)
    (Set.range (S.coneBaseInclusion X))
    (S.coneBaseBasepoint_mem X)

/-- The cone pair `(cone X, X)` whose quotient realizes the chosen suspension of `X`. -/
abbrev ReducedSuspensionModel.coneBoundaryPair
    [CategoryWithCofibrations BasedSpace] (S : ReducedSuspensionModel) (X : NBasedSpace) :
    SpacePair where
  space := (S.cone.obj X).right
  subspace := Set.range (S.coneBaseInclusion X)

/-- The canonical map from the absolute subspace pair of the cone base to its reduced pair. -/
abbrev ReducedSuspensionModel.coneBaseAbsoluteToReduced
    [CategoryWithCofibrations BasedSpace] (S : ReducedSuspensionModel) (X : NBasedSpace) :
    SpacePair.subspaceAbsolute (S.coneBoundaryPair X) ⟶
      basedReducedPair (S.coneBaseSubspace X) :=
  SpacePair.absoluteToRelative (basedReducedPair (S.coneBaseSubspace X))

/-- Reindexing `q + 1 - 1 = q` on pair-homology objects. -/
theorem pairHomologySuspensionIndexShift
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (P : SpacePair) :
    (H.homology (q + 1 - 1)).obj P = (H.homology q).obj P := sorry

/-- The canonical reduced boundary morphism of the cone pair attached to `X`, before reindexing
`q + 1 - 1` to `q`. -/
abbrev reducedConeBoundaryShifted
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (q : ℤ) (X : NBasedSpace) :
    (H.homology (q + 1)).obj (S.coneBoundaryPair X) ⟶
      (H.homology (q + 1 - 1)).obj (basedReducedPair (S.coneBaseSubspace X)) :=
  ((H.boundary (q + 1)).app (S.coneBoundaryPair X)) ≫
    ((H.homology (q + 1 - 1)).map (S.coneBaseAbsoluteToReduced X))

/-- A morphism from the cone pair of `X` to the reduced pair of its cone base is the canonical
reduced boundary comparison in degree `q` when it is the shifted cone boundary map followed by
the reindexing `q + 1 - 1 = q`. -/
def ReducedConeBoundaryComparisonSpec
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (q : ℤ) (X : NBasedSpace)
    (δ :
      (H.homology (q + 1)).obj (S.coneBoundaryPair X) ⟶
        (H.homology q).obj (basedReducedPair (S.coneBaseSubspace X))) : Prop :=
  δ =
    reducedConeBoundaryShifted H S q X ≫
      eqToHom (pairHomologySuspensionIndexShift H q (basedReducedPair (S.coneBaseSubspace X)))

/-- A natural isomorphism `η` realizes the suspension comparison of Theorem 14.3.1 when each
forward component is the composite of the reduced-homology map induced by the chosen
identification of `X` with the base of its cone, the inverse of a cone boundary comparison
specified by `ReducedConeBoundaryComparisonSpec H S q X`, and the quotient comparison
isomorphism from Theorem 14.2.1. -/
def ReducedHomologySuspensionNatIsoStrongSpec
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (q : ℤ)
    (η : nBasedReducedHomologyFunctor H q ≅
      S.suspension ⋙ nBasedReducedHomologyFunctor H (q + 1)) : Prop :=
  ∃ coneBoundaryComparison :
      ∀ X : NBasedSpace,
        (H.homology (q + 1)).obj (S.coneBoundaryPair X) ⟶
          (H.homology q).obj (basedReducedPair (S.coneBaseSubspace X)),
    (∀ X : NBasedSpace,
      ReducedConeBoundaryComparisonSpec H S q X (coneBoundaryComparison X)) ∧
    ∃ coneBoundaryInv :
      ∀ X : NBasedSpace,
        (H.homology q).obj (basedReducedPair (S.coneBaseSubspace X)) ⟶
          (H.homology (q + 1)).obj (S.coneBoundaryPair X),
      (∀ X : NBasedSpace,
        coneBoundaryInv X ≫ coneBoundaryComparison X =
          𝟙 ((H.homology q).obj (basedReducedPair (S.coneBaseSubspace X)))) ∧
      (∀ X : NBasedSpace,
        coneBoundaryComparison X ≫ coneBoundaryInv X =
          𝟙 ((H.homology (q + 1)).obj (S.coneBoundaryPair X))) ∧
      ∀ X : NBasedSpace,
        η.hom.app X =
          ((H.homology q).map (basedMapReducedPairHom (S.coneBaseIso X).hom)) ≫
            coneBoundaryInv X ≫
            ((H.homology (q + 1)).map (S.quotientComparison X).pairMap)

/-- Theorem 14.3.1: for a nondegenerately based space `X`, suspension gives a natural
isomorphism `H̃_q(X) ≅ H̃_(q + 1)(ΣX)`. Formalized here relative to a chosen reduced suspension
model `S`, this asserts the existence of a natural isomorphism
`η : nBasedReducedHomologyFunctor H q ≅
  S.suspension ⋙ nBasedReducedHomologyFunctor H (q + 1)`
with the explicit cone-boundary and quotient-comparison specification recorded by
`ReducedHomologySuspensionNatIsoStrongSpec H S q η`. -/
theorem existsReducedHomologySuspensionNatIso
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (q : ℤ) :
    ∃ η : nBasedReducedHomologyFunctor H q ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (q + 1),
      ReducedHomologySuspensionNatIsoStrongSpec H S q η := sorry
