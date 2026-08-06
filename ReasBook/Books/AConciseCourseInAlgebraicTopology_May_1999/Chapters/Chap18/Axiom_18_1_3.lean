import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Axiom_13_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` only surfaced unrelated general cohomology lemmas, while
-- local Chapter 13/18 precedent already fixes both the source-facing excision map
-- `(A, A ∩ B) ⟶ (X, B)` and the cohomology-theory owner `PairCohomologyTheory`.

/-- Axiom 18.1.3: for an excisive triad `(X; A, B)`, the inclusion
`pairHomologyExcisionInclusion A B : (A, A ∩ B) ⟶ (X, B)` induces an isomorphism
`H^q(X, B; π) ⟶ H^q(A, A ∩ B; π)` in any Chapter 18 pair cohomology theory. -/
instance pairCohomologyExcision_isIso
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso ((H q).map (pairHomologyExcisionInclusion A B).op) := by
  let hTransport :
      IsIso ((H q).map (pairHomologyExcisionSourcePairIsoRemoveSubset A B).hom.op) := by
    infer_instance
  let hRemoveSubset :
      IsIso ((H q).map (removeSubsetInclusion (pairHomologyExcisionTargetPair B) Aᶜ).op) :=
    H.excision q (pairHomologyExcisionTargetPair B) Aᶜ
      ((pairHomologyExcisionTriad_isExcisive_iff A B).mp hExcisive)
  have hMap :
      (H q).map (pairHomologyExcisionInclusion A B).op =
        (H q).map (removeSubsetInclusion (pairHomologyExcisionTargetPair B) Aᶜ).op ≫
          (H q).map (pairHomologyExcisionSourcePairIsoRemoveSubset A B).hom.op := by
    simpa [Functor.map_comp] using
      congrArg (fun f ↦ (H q).map f.op) (pairHomologyExcisionInclusion_eq_transport_comp A B)
  simpa [hMap] using (IsIso.comp_isIso' hRemoveSubset hTransport)

/-- Axiom 18.1.3: for an excisive triad `(X; A, B)`, the inclusion
`pairHomologyExcisionInclusion A B : (A, A ∩ B) ⟶ (X, B)` induces an isomorphism on the
degree-`q` cohomology object of any Chapter 18 pair cohomology theory. -/
theorem pairCohomologyExcision
    {X : Type u} [TopologicalSpace X] {π : Type u} [AddCommGroup π]
    (H : PairCohomologyTheory π) (A B : Set X) (q : ℤ)
    (hExcisive : (pairHomologyExcisionTriad A B).IsExcisive) :
    IsIso ((H q).map (pairHomologyExcisionInclusion A B).op) := by
  exact pairCohomologyExcision_isIso H A B q hExcisive
