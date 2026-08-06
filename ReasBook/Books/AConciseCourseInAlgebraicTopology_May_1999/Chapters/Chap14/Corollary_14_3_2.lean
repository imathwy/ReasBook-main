import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Sequence_14_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Theorem_14_3_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

universe u

local notation "BasedSpace" => Under (⊤_ TopCat)
local notation "NBasedSpace" =>
  CategoryTheory.ObjectProperty.FullSubcategory
    (HomotopicalAlgebra.IsCofibrant : CategoryTheory.ObjectProperty BasedSpace)

-- Semantic recall via `lean_leansearch` surfaced only abstract long-exact-sequence connecting
-- morphisms. The source-facing Chapter 14 owners here are the quotient transport of
-- `reducedBoundaryMap`, the explicit topological boundary map of Construction 14.2.2, and an
-- explicit suspension isomorphism `η` satisfying Theorem 14.3.1.

private theorem basedReducedHomologySuccessorPredecessor
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) :
    basedReducedHomology H (q + 1 - 1) X = basedReducedHomology H q X := by
  simp [basedReducedHomology, reducedHomology]

private theorem reducedPairConnectingHomomorphismTargetEq
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) (A : Set X.right)
    (hA_mem : underTopBasepoint X ∈ A) (hA : A.Nonempty) :
    (basedReducedHomology H (q + 1) (collapseSubsetBasedSpace X.right A hA) →+
      basedReducedHomology H (q + 1 - 1) (basedSubspace X A hA_mem)) =
      (basedReducedHomology H (q + 1) (collapseSubsetBasedSpace X.right A hA) →+
        basedReducedHomology H q (basedSubspace X A hA_mem)) := by
  simpa [basedReducedHomology, reducedHomology] using
    congrArg
      (fun n : ℤ ↦
        pairHomologyGroup H (q + 1)
            (collapseSubsetBasedSpace X.right A hA).right
            ({underTopBasepoint (collapseSubsetBasedSpace X.right A hA)} :
              Set (collapseSubsetBasedSpace X.right A hA).right) →+
          pairHomologyGroup H n
            (basedSubspace X A hA_mem).right
            ({underTopBasepoint (basedSubspace X A hA_mem)} :
              Set (basedSubspace X A hA_mem).right))
      (Int.add_sub_cancel q 1)

/-- The connecting homomorphism
`H̃_(q + 1)(collapseSubsetBasedSpace X.right A hA) ⟶ H̃_q(basedSubspace X A hA_mem)` in the
reduced long exact pair sequence, obtained by transporting `reducedBoundaryMap H (q + 1) X A
hA_mem` across a chosen additive equivalence from pair homology to the reduced homology of the
quotient. -/
noncomputable abbrev reducedPairConnectingHomomorphism
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (q : ℤ) (X : BasedSpace) (A : Set X.right)
    (hA_mem : underTopBasepoint X ∈ A) (hA : A.Nonempty)
    (quotientIso :
      pairHomologyGroup H (q + 1) X.right A ≃+
        basedReducedHomology H (q + 1) (collapseSubsetBasedSpace X.right A hA)) :
    basedReducedHomology H (q + 1) (collapseSubsetBasedSpace X.right A hA) →+
      basedReducedHomology H q (basedSubspace X A hA_mem) :=
  Eq.mp
    (reducedPairConnectingHomomorphismTargetEq H q X A hA_mem hA)
    ((reducedBoundaryMap H (q + 1) X A hA_mem).comp quotientIso.symm.toAddMonoidHom)

/-- The map on reduced homology induced by the topological boundary map of Construction 14.2.2,
followed by the inverse of an explicit suspension isomorphism `η` from Theorem 14.3.1 and the
chosen identification of the nondegenerately based model `An` with the based subspace
`basedSubspace Xn.obj A hA_mem`.
-/
noncomputable abbrev topologicalBoundaryCompInverseSuspension
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (q : ℤ)
    (η : nBasedReducedHomologyFunctor H q ≅
      S.suspension ⋙ nBasedReducedHomologyFunctor H (q + 1))
    (Xn : NBasedSpace)
    (A : Set Xn.obj.right) (hA_mem : underTopBasepoint Xn.obj ∈ A)
    (hA : A.Nonempty) (An : NBasedSpace)
    (eA : An.obj ≅ basedSubspace Xn.obj A hA_mem)
    {Ci : BasedSpace}
    (data :
      CofibrationBoundaryFactorization
        Xn.obj.right
        A
        (collapseSubsetBasedSpace Xn.obj.right A hA)
        (S.suspension.obj An).obj
        Ci) :
    basedReducedHomology H (q + 1) (collapseSubsetBasedSpace Xn.obj.right A hA) →+
      basedReducedHomology H q (basedSubspace Xn.obj A hA_mem) :=
  (basedHomologyReducedMap H q eA.hom).comp
    ((((η.app An).inv.hom).toAddMonoidHom).comp
      (basedHomologyReducedMap H (q + 1) (cofibrationTopologicalBoundaryMap hA data)))

/-- Corollary 14.3.2. For a cofibration `A ↪ X` between nondegenerately based spaces, after
choosing an additive equivalence
`pairHomologyGroup H (q + 1) Xn.obj.right A ≃+
  basedReducedHomology H (q + 1) (collapseSubsetBasedSpace Xn.obj.right A hA)`
whose forward map is the quotient-induced homology map from Theorem 14.2.1, identifying `A`
with the based subspace of `X`, and identifying `X/A` with the canonical quotient owner from
Theorem 14.2.1, there exists a suspension isomorphism `η` satisfying
`ReducedHomologySuspensionNatIsoStrongSpec H S q η` such that the connecting homomorphism in the
reduced long exact pair sequence is the map on reduced homology induced by the topological
boundary map of Construction 14.2.2, followed by `η⁻¹`. -/
theorem reducedPairConnectingHomomorphism_eq_topologicalBoundary_comp_inverseSuspension
    [CategoryWithCofibrations BasedSpace]
    {π : Type u} [AddCommGroup π] (H : PairHomologyTheory π)
    (S : ReducedSuspensionModel) (q : ℤ) (Xn : NBasedSpace)
    (A : Set Xn.obj.right) (hA_mem : underTopBasepoint Xn.obj ∈ A)
    (hA : A.Nonempty)
    (quotientIso :
      pairHomologyGroup H (q + 1) Xn.obj.right A ≃+
        basedReducedHomology H (q + 1) (collapseSubsetBasedSpace Xn.obj.right A hA))
    (hquotientIso :
      quotientIso.toAddMonoidHom = cofibrationQuotientHomologyMap H (q + 1) hA)
    (An : NBasedSpace) (eA : An.obj ≅ basedSubspace Xn.obj A hA_mem)
    {Ci : BasedSpace}
    (data :
      CofibrationBoundaryFactorization
        Xn.obj.right
        A
        (collapseSubsetBasedSpace Xn.obj.right A hA)
        (S.suspension.obj An).obj
        Ci) :
    ∃ η : nBasedReducedHomologyFunctor H q ≅
        S.suspension ⋙ nBasedReducedHomologyFunctor H (q + 1),
      ReducedHomologySuspensionNatIsoStrongSpec H S q η ∧
        reducedPairConnectingHomomorphism H q Xn.obj A hA_mem hA quotientIso =
          topologicalBoundaryCompInverseSuspension H S q η Xn A hA_mem hA An eA data := sorry
