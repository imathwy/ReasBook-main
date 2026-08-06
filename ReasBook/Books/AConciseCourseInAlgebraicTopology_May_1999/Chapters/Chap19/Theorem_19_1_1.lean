import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_5

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch` did not surface a canonical mathlib owner for this
-- uniqueness statement. Local Chapter 18 precedent already packages the relevant CW-pair
-- restriction and comparison data in the bundled source-facing owner
-- `CWPairCohomologyTheory`, together with the existence theorem
-- `exists_pairCohomologyTheory_of_cwPairCohomologyTheory`, so this file should expose the
-- unconditional source-facing uniqueness consequence.

local notation "CWPair" =>
  CategoryTheory.ObjectProperty.FullSubcategory IsCWPair

private def pairCohomologyTheoryIsoSymm
    {π : Type u} [AddCommGroup π] {H K : PairCohomologyTheory π}
    (i : PairCohomologyTheory.Iso H K) :
    PairCohomologyTheory.Iso K H where
  app q := (i.app q).symm
  boundary_comm q := by
    rw [← cancel_mono ((i.app (q + 1)).hom), Category.assoc, ← i.boundary_comm q,
      ← Category.assoc, ← Functor.whiskerLeft_comp]
    simp

private def pairCohomologyTheoryIsoTrans
    {π : Type u} [AddCommGroup π] {H K L : PairCohomologyTheory π}
    (i : PairCohomologyTheory.Iso H K) (j : PairCohomologyTheory.Iso K L) :
    PairCohomologyTheory.Iso H L where
  app q := i.app q ≪≫ j.app q
  boundary_comm q := by
    change
      Functor.whiskerLeft SpacePair.subspaceFunctor.op
          ((i.app q).hom ≫ (j.app q).hom) ≫
        L.boundary q =
      H.boundary q ≫ (i.app (q + 1)).hom ≫ (j.app (q + 1)).hom
    rw [Functor.whiskerLeft_comp, Category.assoc, j.boundary_comm q, ← Category.assoc,
      i.boundary_comm q, Category.assoc]

/-- Theorem 19.1.1: a generalized cohomology theory on pairs of spaces is determined by its
restriction to CW pairs. Concretely, if two Chapter 18 pair cohomology theories induce the same
bundled restricted CW-pair cohomology theory up to degreewise natural isomorphism compatible with
the bundled CW-pair theory structure on `E`, then they are isomorphic as pair cohomology theories
in a way that respects those supplied comparison isomorphisms. -/
theorem pairCohomologyTheory_iso_of_restrictToCWPairs
    {π : Type u} [AddCommGroup π] (H K : PairCohomologyTheory π) (E : CWPairCohomologyTheory π)
    (eH : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs H q ≅ E q)
    (hH : HasCWPairCohomologyTheoryComparison H E.2 eH)
    (eK : ∀ q : ℤ, restrictPairCohomologyTheoryToCWPairs K q ≅ E q)
    (hK : HasCWPairCohomologyTheoryComparison K E.2 eK) :
    ∃ i : PairCohomologyTheory.Iso H K,
      PairCohomologyTheory.Iso.RespectsCWPairComparison i eH eK := by
  let hExt : E.HasPairCohomologyTheoryExtension :=
    exists_pairCohomologyTheory_of_cwPairCohomologyTheory E
  rcases hExt with ⟨L, eL, _, huniq⟩
  rcases huniq H eH hH with ⟨iH, hiH⟩
  rcases huniq K eK hK with ⟨iK, hiK⟩
  refine ⟨pairCohomologyTheoryIsoTrans (pairCohomologyTheoryIsoSymm iH) iK, ?_⟩
  intro q
  calc
    Functor.isoWhiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair).op
        (((pairCohomologyTheoryIsoSymm iH).app q) ≪≫ iK.app q) ≪≫ eK q
      =
        Functor.isoWhiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair).op
            ((pairCohomologyTheoryIsoSymm iH).app q) ≪≫
          (Functor.isoWhiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair).op (iK.app q) ≪≫
            eK q) := by
          simp
    _ =
        Functor.isoWhiskerLeft (CategoryTheory.ObjectProperty.ι IsCWPair).op
          ((pairCohomologyTheoryIsoSymm iH).app q) ≪≫
            eL q := by
          rw [hiK q]
    _ = eH q := by
      rw [← hiH q]
      ext P
      simp [pairCohomologyTheoryIsoSymm]
