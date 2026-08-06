import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.SubsetPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_5_2
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.CommSq

open CategoryTheory
open SpacePair

universe u

-- Semantic recall via `lean_leansearch` and local Chapter 12/13 precedent identifies
-- `ShortComplex.ShortExact.δ` as the canonical connecting-morphism owner, while
-- `CategoryTheory.CommSq` is the canonical owner for a single boundary-compatibility square.
-- This file keeps the Chapter 19 relative cellular cochain models explicit and exposes the final
-- comparison theorem directly on that source-facing surface.

/-- A source-faithful Chapter 19 model for the relative cellular cochain complex of one CW pair
chooses the ambient CW complex, its subcomplex, the absolute cellular cochain complexes from
Theorem 19.5.2, and the restriction map whose kernel is the relative complex from
Definition 19.5.3. -/
structure RelativeCellularCochainModel
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) where
  /-- The ambient space `X` of the CW pair. -/
  X : Type u
  /-- The ambient topology on `X`. -/
  topologicalSpaceX : TopologicalSpace X
  /-- The chosen CW structure on `X`. -/
  cwComplexX : Topology.CWComplex (Set.univ : Set X)
  /-- The chosen subcomplex `A ⊆ X`. -/
  A : Topology.CWComplex.Subcomplex (Set.univ : Set X)
  /-- The inherited CW structure on the chosen subcomplex `A`. -/
  cwComplexA : Topology.CWComplex (Set.univ : Set A)
  /-- The chosen cellular differential data on `X`. -/
  dataX : CellularDifferentialFamily X
  /-- The chosen cellular differential data on `A`. -/
  dataA : CellularDifferentialFamily A
  /-- The chosen absolute cellular cochain complex `C^*(X; π)`. -/
  CX : AxiomaticCellularCochainComplex H X dataX
  /-- The chosen absolute cellular cochain complex `C^*(A; π)`. -/
  CA : AxiomaticCellularCochainComplex H A dataA
  /-- The chosen restriction morphism `C^*(X; π) ⟶ C^*(A; π)`. -/
  restriction : CX.complex ⟶ CA.complex
  /-- The chosen absolute cochain complex `C^*(A; π)` has cohomology in every nonnegative
  degree. -/
  hasHomologyA : ∀ n : ℕ, HomologicalComplex.HasHomology CA.complex n
  /-- The chosen relative cochain complex `C^*(X, A; π)` has cohomology in every nonnegative
  degree. -/
  hasHomologyRelative :
    ∀ n : ℕ,
      HomologicalComplex.HasHomology
        (axiomaticRelativeCellularCochainComplex H X A dataX dataA CX CA restriction) n
  /-- The chosen restriction sequence
  `0 ⟶ C^*(X, A; π) ⟶ C^*(X; π) ⟶ C^*(A; π) ⟶ 0`
  is short exact on cochain complexes. -/
  shortExact :
    (ShortComplex.mk
      (relativeCellularCochainComplexι H X A dataX dataA CX CA restriction)
      restriction
      (relativeCellularCochainComplexι_comp_restriction
        H X A dataX dataA CX CA restriction)).ShortExact
  /-- The connecting homomorphism
  `H^n(C^*(A; π)) ⟶ H^(n + 1)(C^*(X, A; π))`
  attached to the chosen short exact cochain sequence. -/
  boundary :
    ∀ n : ℕ,
      -- Local instance justification (defeq pin): keep the stored source homology object.
      letI := hasHomologyA n
      -- Local instance justification (defeq pin): keep the stored target homology object.
      letI := hasHomologyRelative (n + 1)
      CA.complex.homology n ⟶
        (axiomaticRelativeCellularCochainComplex H X A dataX dataA CX CA restriction).homology
          (n + 1)
  /-- The chosen boundary is the canonical connecting homomorphism attached to the stored short
  exact cochain sequence. -/
  boundary_eq :
    ∀ n : ℕ,
      -- Local instance justification (defeq pin): compare in the stored source homology object.
      letI := hasHomologyA n
      -- Local instance justification (defeq pin): compare in the stored target homology object.
      letI := hasHomologyRelative (n + 1)
      boundary n = shortExact.δ n (n + 1) rfl

attribute [instance] RelativeCellularCochainModel.topologicalSpaceX
attribute [instance] RelativeCellularCochainModel.cwComplexX
attribute [instance] RelativeCellularCochainModel.cwComplexA
attribute [instance] RelativeCellularCochainModel.hasHomologyA
attribute [instance] RelativeCellularCochainModel.hasHomologyRelative

/-- The actual Chapter 19 relative cellular cochain complex attached to a chosen source-faithful
CW-pair model. -/
noncomputable abbrev RelativeCellularCochainModel.relativeComplex
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (M : RelativeCellularCochainModel H) :
    CochainComplex AddCommGrpCat ℕ :=
  axiomaticRelativeCellularCochainComplex H M.X M.A M.dataX M.dataA M.CX M.CA M.restriction

/-- The degree-`n` cohomology of the chosen absolute cochain complex `C^*(A; π)` attached to a
source-faithful Chapter 19 CW-pair model. -/
noncomputable abbrev RelativeCellularCochainModel.absoluteHomology
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (M : RelativeCellularCochainModel H) (n : ℕ) :
    AddCommGrpCat :=
  M.CA.homology n

/-- The short complex
`C^*(X, A; π) ⟶ C^*(X; π) ⟶ C^*(A; π)`
attached to a chosen Chapter 19 model. -/
noncomputable abbrev RelativeCellularCochainModel.shortComplex
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (M : RelativeCellularCochainModel H) :
    ShortComplex (CochainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk
    (relativeCellularCochainComplexι
      H M.X M.A M.dataX M.dataA M.CX M.CA M.restriction)
    M.restriction
    (relativeCellularCochainComplexι_comp_restriction
      H M.X M.A M.dataX M.dataA M.CX M.CA M.restriction)

/-- The chosen model boundary realizes the second exactness window
`H^n(C^*(X; π)) ⟶ H^n(C^*(A; π)) ⟶ H^(n + 1)(C^*(X, A; π))`
of the long exact cohomology sequence attached to the stored short exact cochain sequence. -/
theorem RelativeCellularCochainModel.boundary_exact_restriction
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (M : RelativeCellularCochainModel H) (n : ℕ)
    [HomologicalComplex.HasHomology M.CX.complex n] :
    Function.Exact (HomologicalComplex.homologyMap M.shortComplex.g n) (M.boundary n) := by
  rw [M.boundary_eq n]
  let S : ShortComplex AddCommGrpCat :=
    ShortComplex.mk
      (HomologicalComplex.homologyMap M.shortComplex.g n)
      (M.shortExact.δ n (n + 1) rfl)
      (M.shortExact.comp_δ n (n + 1) rfl)
  have hS : S.Exact := by
    simpa [S] using M.shortExact.homology_exact₃ n (n + 1) rfl
  exact S.ab_exact_iff_function_exact.1 hS

/-- The chosen model boundary realizes the third exactness window
`H^n(C^*(A; π)) ⟶ H^(n + 1)(C^*(X, A; π)) ⟶ H^(n + 1)(C^*(X; π))`
of the long exact cohomology sequence attached to the stored short exact cochain sequence. -/
theorem RelativeCellularCochainModel.boundary_exact_relativeInclusion
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (M : RelativeCellularCochainModel H) (n : ℕ)
    [HomologicalComplex.HasHomology M.CX.complex (n + 1)] :
    Function.Exact (M.boundary n) (HomologicalComplex.homologyMap M.shortComplex.f (n + 1)) := by
  rw [M.boundary_eq n]
  let S : ShortComplex AddCommGrpCat :=
    ShortComplex.mk
      (M.shortExact.δ n (n + 1) rfl)
      (HomologicalComplex.homologyMap M.shortComplex.f (n + 1))
      (M.shortExact.δ_comp n (n + 1) rfl)
  have hS : S.Exact := by
    simpa [S] using M.shortExact.homology_exact₁ n (n + 1) rfl
  exact S.ab_exact_iff_function_exact.1 hS

/-- A source-facing comparison from `H^n(X, A; π)` to the cohomology of the actual Chapter 19
relative cellular cochain complexes chooses explicit CW-pair models, a genuine degreewise natural
isomorphism in the CW pair, and cochain connecting morphisms compatible with the pair-theory
boundary maps after transport to the actual relative cellular cochain complexes. -/
structure RelativeCellularCochainComparison
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) where
  /-- A chosen CW-pair model for the actual relative cellular cochain complex attached to `P`. -/
  model : CWPair → RelativeCellularCochainModel H
  /-- Each chosen model represents the underlying CW pair `P = (X, A)`. -/
  pairIso :
    ∀ P : CWPair,
      let M := model P
      P.1 ≅ subsetPair (TopCat.of M.X) (M.A : Set (TopCat.of M.X))
  /-- A chosen CW-pair model for the subspace pair `(A, ∅)`. -/
  subspacePair : CWPair → CWPair
  /-- The chosen subspace model represents `SpacePair.subspaceAbsolute P.1`. -/
  subspaceIso : ∀ P : CWPair, (subspacePair P).1 ≅ SpacePair.subspaceAbsolute P.1
  /-- The actual relative cellular cochain complex of each chosen model has cohomology in every
  nonnegative degree. -/
  hasHomology :
    ∀ (P : CWPair) (n : ℕ),
      HomologicalComplex.HasHomology (RelativeCellularCochainModel.relativeComplex (model P)) n
  /-- The degree-`n` target functor on `CWPair` whose value at `P` is realized by the cohomology
  of the actual relative cellular cochain complex chosen for `P`. -/
  targetFunctor : ℕ → CWPairᵒᵖ ⥤ AddCommGrpCat.{u}
  /-- The degree-`n` target functor is identified objectwise with the cohomology of the actual
  relative cellular cochain complex chosen for `P`. -/
  targetIso :
    ∀ (P : CWPair) (n : ℕ),
      -- Local instance justification (defeq pin): fix the chosen homology object of `model P`.
      letI := hasHomology P n
      (targetFunctor n).obj (Opposite.op P) ≅
        (RelativeCellularCochainModel.relativeComplex (model P)).homology n
  /-- The comparison is a genuine natural isomorphism in the CW pair, degree by degree. -/
  natIso :
    ∀ n : ℕ, restrictPairCohomologyTheoryToCWPairs H (n : ℤ) ≅ targetFunctor n
  /-- The chosen subspace-pair model for `(A, ∅)` computes the same degree-`n` cohomology as the
  absolute cochain complex `C^*(A; π)` appearing in the short exact sequence for `model P`. -/
  subspaceHomologyIso :
    ∀ (P : CWPair) (n : ℕ),
      -- Local instance justification (defeq pin): fix the chosen subspace-model homology object.
      letI := hasHomology (subspacePair P) n
      let M := model P
      (RelativeCellularCochainModel.relativeComplex (model (subspacePair P))).homology n ≅
        M.absoluteHomology n
  /-- The source-facing comparison intertwines the pair-theory connecting morphisms with the
  canonical cochain connecting morphisms on the chosen models, expressed in the canonical
  `CommSq` form. -/
  boundary_comm :
    ∀ (P : CWPair) (n : ℕ),
      -- Local instance justification (defeq pin): fix the chosen subspace-model homology object.
      letI := hasHomology (subspacePair P) n
      -- Local instance justification (defeq pin): fix the chosen relative-model homology object.
      letI := hasHomology P (n + 1)
      CommSq
        ((H.boundary (n : ℤ)).app (Opposite.op P.1))
        (((H.cohomology (n : ℤ)).map (subspaceIso P).hom.op) ≫
          (((natIso n).app (Opposite.op (subspacePair P))) ≪≫
            targetIso (subspacePair P) n).hom ≫
            (subspaceHomologyIso P n).hom)
        (((natIso (n + 1)).app (Opposite.op P)) ≪≫ targetIso P (n + 1)).hom
        ((model P).boundary n)

attribute [instance] RelativeCellularCochainComparison.hasHomology

namespace RelativeCellularCochainComparison

/-- Evaluating the degreewise natural comparison on a CW pair and composing with the chosen
realization of the target functor gives the source-facing isomorphism
`H^n(X, A; π) ≅ H^n(C^*(X, A; π))`. -/
noncomputable abbrev comparisonIso
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (C : RelativeCellularCochainComparison H) (P : CWPair) (n : ℕ) :
    ((restrictPairCohomologyTheoryToCWPairs H (n : ℤ)).obj (Opposite.op P)) ≅
      (RelativeCellularCochainModel.relativeComplex (C.model P)).homology n :=
  ((C.natIso n).app (Opposite.op P)) ≪≫ C.targetIso P n

/-- The source-facing comparison for the canonical subspace pair `(A, ∅)` lands in the absolute
cochain complex `C^*(A; π)` from the chosen model of `P`. -/
noncomputable abbrev subspaceComparison
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (C : RelativeCellularCochainComparison H) (P : CWPair) (n : ℕ) :
    let M := C.model P
    ((H.cohomology (n : ℤ)).obj (Opposite.op (SpacePair.subspaceAbsolute P.1))) ⟶
      M.absoluteHomology n :=
  ((H.cohomology (n : ℤ)).map (C.subspaceIso P).hom.op) ≫
    (C.comparisonIso (C.subspacePair P) n).hom ≫
      (C.subspaceHomologyIso P n).hom

/-- The boundary square of a relative cellular cochain comparison commutes as an equality of
composites on the actual subspace and relative cochain models. -/
theorem boundary_comm_w
    {π : Type u} [AddCommGroup π] {H : PairCohomologyTheory π}
    (C : RelativeCellularCochainComparison H) (P : CWPair) (n : ℕ) :
      ((H.cohomology (n : ℤ)).map (C.subspaceIso P).hom.op) ≫
        (C.comparisonIso (C.subspacePair P) n).hom ≫ (C.subspaceHomologyIso P n).hom ≫
          (C.model P).boundary n =
      ((H.boundary (n : ℤ)).app (Opposite.op P.1)) ≫
        (C.comparisonIso P (n + 1)).hom := by
  simpa [subspaceComparison, comparisonIso] using (C.boundary_comm P n).w.symm

end RelativeCellularCochainComparison

/-- Theorem 19.5.4: for a Chapter 18 pair cohomology theory `H^*(-; π)`, there exists a
source-faithful comparison object from `H^n(X, A; π)` to the degree-`n` cohomology of the actual
relative cellular cochain complex `C^*(X, A; π)` from Definition 19.5.3, natural in the CW pair
and compatible with the connecting homomorphisms. -/
theorem exists_relativeCellularCochainComparison
    {π : Type u} [AddCommGroup π] (H : PairCohomologyTheory π) :
    Nonempty (RelativeCellularCochainComparison H) := by
  sorry
