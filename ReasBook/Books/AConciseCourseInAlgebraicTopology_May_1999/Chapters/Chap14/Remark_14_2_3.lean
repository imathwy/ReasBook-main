import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Lemma_6_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Axiom_13_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.MappingCylinderCofiber
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_2_1

open CategoryTheory
open ContinuousMap
open SpacePair

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch` only surfaced abstract cofiber APIs. The source-facing
-- Chapter 14 owner in this repo is the quotient comparison `ReducedQuotientMap` from Theorem
-- 14.2.1, applied here to the mapping-cylinder cofibration replacement of `A ↪ X`.

/-- The target inclusion `X ⟶ M_(A ↪ X)` of the mapping-cylinder factorization sends the
subspace `A ⊆ X` into the image of the mapping-cylinder cofibration `A ⟶ M_(A ↪ X)`. -/
theorem mappingCylinderTargetInclusion_mapsSubspace
    {X : TopCat.{u}} (A : Set X) {x : X} (hx : x ∈ A) :
    mappingCylinderTargetInclusion (subsetInclusion A) x ∈ mappingCylinderCofiberSubspace A := by
  refine ⟨⟨x, hx⟩, ?_⟩
  simpa [mappingCylinderCofiberSubspace, mappingCylinderIn] using
    (congrArg (fun f ↦ f ⟨x, hx⟩) (mappingCylinderTargetInclusion_comp (subsetInclusion A))).symm

/-- The canonical map of pairs from `(X, A)` to the mapping-cylinder replacement pair
`(M_(A ↪ X), im(A ⟶ M_(A ↪ X)))`. -/
def mappingCylinderTargetPairMap
    {X : TopCat.{u}} (A : Set X) :
    subsetPair X A ⟶
      subsetPair (subsetInclusion A).mappingCylinder (mappingCylinderCofiberSubspace A) where
  hom := TopCat.ofHom (mappingCylinderTargetInclusion (subsetInclusion A))
  map_subspace' := by
    intro x hx
    exact mappingCylinderTargetInclusion_mapsSubspace A hx

private theorem mappingCylinderCofiberSubspace_isCofibration
    {X : TopCat.{u}} (A : Set X) :
    IsCofibration.{u, u, u}
      (subsetInclusion (mappingCylinderCofiberSubspace A)) := by
  sorry

/-- The pair map `(X, A) ⟶ (M_(A ↪ X), im(A ⟶ M_(A ↪ X)))` is a weak equivalence of pairs. -/
theorem mappingCylinderTargetPairMap_isWeakEquivalence
    {X : TopCat.{u}} (A : Set X) :
    SpacePair.IsWeakEquivalence (mappingCylinderTargetPairMap A) := by
  let e : X ≃ₕ (subsetInclusion A).mappingCylinder :=
    { toFun := mappingCylinderTargetInclusion (subsetInclusion A)
      invFun := mappingCylinderProjection (subsetInclusion A)
      left_inv := mappingCylinderProjection_comp_targetInclusion_homotopic_id (subsetInclusion A)
      right_inv := mappingCylinderTargetInclusion_comp_projection_homotopic_id (subsetInclusion A) }
  refine ⟨e, rfl, ?_⟩
  intro y hy
  exact mappingCylinderProjection_mapsCofiberSubspace A hy

/-- The map induced by `mappingCylinderTargetPairMap A` on pair homology is an isomorphism. -/
instance mappingCylinderTargetPairMap_isIso
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} (A : Set X) :
    IsIso ((H q).map (mappingCylinderTargetPairMap A)) :=
  H.map_isIso_of_isWeakEquivalence q (mappingCylinderTargetPairMap A)
    (mappingCylinderTargetPairMap_isWeakEquivalence A)

/-- The pair map from `(X, A)` to a chosen based cofiber model `Ci` of the mapping-cylinder
cofibration `A ⟶ M_(A ↪ X)`, obtained by composing the target inclusion with the quotient map
to `Ci`. -/
def mappingCylinderCofiberPairMap
    {X : TopCat.{u}} (A : Set X) {Ci : BasedSpace}
    (Q :
      ReducedQuotientMap
        (subsetInclusion A).mappingCylinder
        (mappingCylinderCofiberSubspace A)
        Ci) :
    subsetPair X A ⟶ basedReducedPair Ci :=
  mappingCylinderTargetPairMap A ≫ Q.pairMap

/-- The homology map from `E_q(X, A)` to the reduced homology of a chosen cofiber model `Ci`
for the mapping-cylinder cofibration replacing `A ↪ X`. -/
abbrev mappingCylinderCofiberHomologyMap
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} (A : Set X) {Ci : BasedSpace}
    (Q :
      ReducedQuotientMap
        (subsetInclusion A).mappingCylinder
        (mappingCylinderCofiberSubspace A)
        Ci) :
    pairHomologyGroup H q X A →+ basedReducedHomology H q Ci :=
  ((H q).map (mappingCylinderCofiberPairMap A Q)).hom.toAddMonoidHom

/-- Remark 14.2.3: replacing the inclusion `A ↪ X` by its mapping-cylinder cofibration identifies
`E_q(X, A)` with the reduced homology of any chosen cofiber model `Ci` of that cofibration. -/
theorem mappingCylinderCofiberHomologyMap_bijective
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π) (q : ℤ)
    {X : TopCat.{u}} (A : Set X) {Ci : BasedSpace}
    (Q :
      ReducedQuotientMap
        (subsetInclusion A).mappingCylinder
        (mappingCylinderCofiberSubspace A)
        Ci) :
    Function.Bijective (mappingCylinderCofiberHomologyMap H q A Q) := by
  let hTarget : IsIso ((H q).map (mappingCylinderTargetPairMap A)) := inferInstance
  let hCofiber : IsIso ((H q).map Q.pairMap) :=
    reducedQuotientMapHomologyMap_isIso.{u, u} H q Q
      (mappingCylinderCofiberSubspace_isCofibration A)
  have hTargetBij :
      Function.Bijective (((H q).map (mappingCylinderTargetPairMap A)).hom.toAddMonoidHom) := by
    simpa using ConcreteCategory.bijective_of_isIso ((H q).map (mappingCylinderTargetPairMap A))
  have hCofiberBij :
      Function.Bijective (((H q).map Q.pairMap).hom.toAddMonoidHom) := by
    simpa using ConcreteCategory.bijective_of_isIso ((H q).map Q.pairMap)
  simpa [mappingCylinderCofiberHomologyMap, mappingCylinderCofiberPairMap, Functor.map_comp] using
    hCofiberBij.comp hTargetBij
