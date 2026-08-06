import Books.AConciseCourseInAlgebraicTopology_May_1999.BasedCWComplex
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CWPair
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_1_1

open CategoryTheory Limits
open HomotopicalAlgebra

noncomputable section

universe w

-- Semantic recall via `lean_leansearch` confirmed that “are equivalent” should use the canonical
-- Lean equivalence object `≃`. This file reuses the repository owners `CWPair` and
-- `BasedCWComplex`, while the Chapter 19 pair-side axiom surface is exposed by an explicit class
-- on graded functors and only then bundled when later files want a packaged CW-pair theory.

/-- Restrict a Chapter 18 pair cohomology theory to the full subcategory of CW pairs. -/
abbrev restrictPairCohomologyTheoryToCWPairs
    {π : Type w} [AddCommGroup π] (E : PairCohomologyTheory π) :
    ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{w} :=
  fun q ↦ (CategoryTheory.ObjectProperty.ι IsCWPair).op ⋙ E.cohomology q

/-- A cohomology theory on CW pairs with underlying graded contravariant functor `E` records the
canonical CW-pair operators `(A, ∅)`, `(X, ∅)`, and excision from Chapter 13, together with the
boundary natural transformations and the dimension, exactness, excision, additivity, and
weak-equivalence axioms directly on `E`. This is the canonical source-facing owner in the file. -/
class IsCohomologyTheoryOnCWPairs
    (π : Type w) [AddCommGroup π] (E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{w}) where
  /-- The connecting morphisms `H^q(A; π) ⟶ H^(q + 1)(X, A; π)` on `CWPair`, natural in the
  canonical subspace functor `(X, A) ↦ (A, ∅)`. -/
  boundary (q : ℤ) : IsCWPair.subspaceFunctor.op ⋙ E q ⟶ E (q + 1)
  /-- Degree-zero cohomology of any CW-pair representative of the one-point pair is `π`. -/
  dimensionZero (pt : CWPair) (hpt : Nonempty (pt ≅ IsCWPair.point)) :
    Nonempty ((E 0).obj (Opposite.op pt) ≅ AddCommGrpCat.of π)
  /-- Cohomology of a CW-pair representative of the one-point pair vanishes away from degree `0`.
  -/
  dimensionHigher (pt : CWPair) (hpt : Nonempty (pt ≅ IsCWPair.point)) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((E q).obj (Opposite.op pt))
  /-- The sequence `H^q(X, A; π) ⟶ H^q(X; π) ⟶ H^q(A; π)` is exact for the canonical CW-pair
  operators. -/
  exact₁ (q : ℤ) (P : CWPair) :
    Function.Exact
      ((E q).map (IsCWPair.absoluteToRelative P).op)
      ((E q).map (IsCWPair.subspaceInclusion P).op)
  /-- The sequence `H^q(X; π) ⟶ H^q(A; π) ⟶ H^(q + 1)(X, A; π)` is exact for the canonical
  CW-pair operators. -/
  exact₂ (q : ℤ) (P : CWPair) :
    Function.Exact
      ((E q).map (IsCWPair.subspaceInclusion P).op)
      ((boundary q).app (Opposite.op P))
  /-- The sequence `H^q(A; π) ⟶ H^(q + 1)(X, A; π) ⟶ H^(q + 1)(X; π)` is exact for the canonical
  CW-pair operators. -/
  exact₃ (q : ℤ) (P : CWPair) :
    Function.Exact
      ((boundary q).app (Opposite.op P))
      ((E (q + 1)).map (IsCWPair.absoluteToRelative P).op)
  /-- Excision identifies `H^q(X, A; π)` with the cohomology of the canonical excision pair. -/
  excision (q : ℤ) (P : CWPair) (U : Set (IsCWPair.space P))
      (hU : closure U ⊆ interior (IsCWPair.subspace P)) :
    IsIso ((E q).map (IsCWPair.removeSubsetInclusion P U hU).op)
  /-- Each degree functor sends coproducts of CW pairs to products. -/
  additivity (q : ℤ) {ι : Type w} : PreservesLimitsOfShape (Discrete ι) (E q)
  /-- Weakly equivalent CW pairs induce isomorphisms in each cohomological degree. -/
  weakEquivalenceInvariant (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((E q).map f.op)

namespace IsCohomologyTheoryOnCWPairs

variable {π : Type w} [AddCommGroup π]
  {E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- The first exactness window of a CW-pair cohomology theory is
`H^q(X, A; π) ⟶ H^q(X; π) ⟶ H^q(A; π)` on the canonical CW-pair operators. -/
theorem exact_absoluteToRelative_subspaceInclusion
    (hE : IsCohomologyTheoryOnCWPairs π E) (q : ℤ) (P : CWPair) :
    Function.Exact
      ((E q).map (IsCWPair.absoluteToRelative P).op)
      ((E q).map (IsCWPair.subspaceInclusion P).op) :=
  hE.exact₁ q P

/-- The second exactness window of a CW-pair cohomology theory is
`H^q(X; π) ⟶ H^q(A; π) ⟶ H^(q + 1)(X, A; π)` on the canonical CW-pair operators. -/
theorem exact_subspaceInclusion_boundary
    (hE : IsCohomologyTheoryOnCWPairs π E) (q : ℤ) (P : CWPair) :
    Function.Exact
      ((E q).map (IsCWPair.subspaceInclusion P).op)
      ((hE.boundary q).app (Opposite.op P)) :=
  hE.exact₂ q P

/-- The third exactness window of a CW-pair cohomology theory is
`H^q(A; π) ⟶ H^(q + 1)(X, A; π) ⟶ H^(q + 1)(X; π)` on the canonical CW-pair operators. -/
theorem exact_boundary_absoluteToRelative
    (hE : IsCohomologyTheoryOnCWPairs π E) (q : ℤ) (P : CWPair) :
    Function.Exact
      ((hE.boundary q).app (Opposite.op P))
      ((E (q + 1)).map (IsCWPair.absoluteToRelative P).op) :=
  hE.exact₃ q P

/-- The connecting morphisms of a CW-pair cohomology theory are natural with respect to maps of
CW pairs. -/
theorem boundary_naturality
    (hE : IsCohomologyTheoryOnCWPairs π E) (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) :
    ((E q).map (IsCWPair.subspaceFunctor.map f).op) ≫
        (hE.boundary q).app (Opposite.op P) =
      (hE.boundary q).app (Opposite.op Q) ≫ ((E (q + 1)).map f.op) := by
  simpa using (hE.boundary q).naturality f.op

/-- Weakly equivalent CW pairs induce isomorphisms on the cohomology groups of a source-facing
CW-pair cohomology theory. -/
theorem map_isIso_of_weakEquivalence
    (hE : IsCohomologyTheoryOnCWPairs π E)
    (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((E q).map f.op) :=
  hE.weakEquivalenceInvariant q f

/-- The source-facing CW-pair cohomology axioms expose the dimension axiom, the three exactness
windows, excision, additivity, and weak-equivalence invariance on the canonical CW-pair
operators. -/
theorem spec
    (hE : IsCohomologyTheoryOnCWPairs π E) :
    (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
      Nonempty ((E 0).obj (Opposite.op pt) ≅ AddCommGrpCat.of π)) ∧
      (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
        ∀ q : ℤ, q ≠ 0 → IsZero ((E q).obj (Opposite.op pt))) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        Function.Exact
          ((E q).map (IsCWPair.absoluteToRelative P).op)
          ((E q).map (IsCWPair.subspaceInclusion P).op)) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        Function.Exact
          ((E q).map (IsCWPair.subspaceInclusion P).op)
          ((hE.boundary q).app (Opposite.op P))) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        Function.Exact
          ((hE.boundary q).app (Opposite.op P))
          ((E (q + 1)).map (IsCWPair.absoluteToRelative P).op)) ∧
      (∀ q : ℤ, ∀ P : CWPair, ∀ U : Set (IsCWPair.space P),
        ∀ hU : closure U ⊆ interior (IsCWPair.subspace P),
          IsIso ((E q).map (IsCWPair.removeSubsetInclusion P U hU).op)) ∧
      (∀ q : ℤ, ∀ {ι : Type w}, PreservesLimitsOfShape (Discrete ι) (E q)) ∧
      (∀ q : ℤ, ∀ {P Q : CWPair} (f : P ⟶ Q),
        [WeakEquivalence f] → IsIso ((E q).map f.op)) :=
  ⟨hE.dimensionZero, hE.dimensionHigher, hE.exact₁, hE.exact₂, hE.exact₃, hE.excision,
    hE.additivity,
    (by intro q P Q f _; exact hE.weakEquivalenceInvariant q f)⟩

end IsCohomologyTheoryOnCWPairs

/-- A bundled CW-pair cohomology theory packages a graded contravariant functor on `CWPair`
together with the source-facing owner `IsCohomologyTheoryOnCWPairs` on that graded functor. This
support owner is used when later files want a bundled CW-pair cohomology theory. -/
abbrev CWPairCohomologyTheory (π : Type w) [AddCommGroup π] :=
  Σ E : ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{w}, IsCohomologyTheoryOnCWPairs π E

/-- A bundled `CWPairCohomologyTheory` carries the source-facing
`IsCohomologyTheoryOnCWPairs` instance on its underlying graded functor. -/
instance instIsCohomologyTheoryOnCWPairs
    {π : Type w} [AddCommGroup π] (H : CWPairCohomologyTheory π) :
    IsCohomologyTheoryOnCWPairs π H.1 :=
  H.2

/-- A `CWPairCohomologyTheory` can be used as its underlying graded contravariant functor. -/
instance {π : Type w} [AddCommGroup π] :
    CoeFun (CWPairCohomologyTheory π)
      (fun _ ↦ ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{w}) where
  coe H := H.1

namespace CWPairCohomologyTheory

variable {π : Type w} [AddCommGroup π]

/-- A bundled CW-pair cohomology theory exposes the source-facing dimension, exactness, excision,
additivity, and weak-equivalence axioms on its underlying graded functor. -/
theorem spec (H : CWPairCohomologyTheory π) :
    (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
      Nonempty ((H 0).obj (Opposite.op pt) ≅ AddCommGrpCat.of π)) ∧
      (∀ pt : CWPair, Nonempty (pt ≅ IsCWPair.point) →
        ∀ q : ℤ, q ≠ 0 → IsZero ((H q).obj (Opposite.op pt))) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        Function.Exact
          ((H q).map (IsCWPair.absoluteToRelative P).op)
          ((H q).map (IsCWPair.subspaceInclusion P).op)) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        Function.Exact
          ((H q).map (IsCWPair.subspaceInclusion P).op)
          ((H.2.boundary q).app (Opposite.op P))) ∧
      (∀ q : ℤ, ∀ P : CWPair,
        Function.Exact
          ((H.2.boundary q).app (Opposite.op P))
          ((H (q + 1)).map (IsCWPair.absoluteToRelative P).op)) ∧
      (∀ q : ℤ, ∀ P : CWPair, ∀ U : Set (IsCWPair.space P),
        ∀ hU : closure U ⊆ interior (IsCWPair.subspace P),
          IsIso ((H q).map (IsCWPair.removeSubsetInclusion P U hU).op)) ∧
      (∀ q : ℤ, ∀ {ι : Type w}, PreservesLimitsOfShape (Discrete ι) (H q)) ∧
      (∀ q : ℤ, ∀ {P Q : CWPair} (f : P ⟶ Q),
        [WeakEquivalence f] → IsIso ((H q).map f.op)) :=
  H.2.spec

end CWPairCohomologyTheory

/-- The source-facing type of cohomology theories on CW pairs together with their coefficient
group. -/
abbrev CWPairCohomologyTheoryWithCoefficients : Type _ :=
  Σ π : AddCommGrpCat.{w}, CWPairCohomologyTheory π

/-- The coefficient group of a bundled CW-pair cohomology theory. -/
abbrev CWPairCohomologyTheoryWithCoefficients.coefficients
    (H : CWPairCohomologyTheoryWithCoefficients) : AddCommGrpCat.{w} :=
  H.1

/-- The underlying bundled CW-pair cohomology theory of a coefficient-theory pair. -/
abbrev CWPairCohomologyTheoryWithCoefficients.theory
    (H : CWPairCohomologyTheoryWithCoefficients) :
    CWPairCohomologyTheory H.coefficients :=
  H.2

/-- The underlying graded contravariant functor of a bundled CW-pair cohomology theory. -/
abbrev CWPairCohomologyTheoryWithCoefficients.cohomology
    (H : CWPairCohomologyTheoryWithCoefficients) :
    ℤ → CWPairᵒᵖ ⥤ AddCommGrpCat.{w} :=
  H.theory

/-- A bundled CW-pair cohomology theory carries the source-facing CW-pair axioms on its
underlying graded contravariant functor. -/
instance instIsCohomologyTheoryOnCWPairsOfCWPairTheoryWithCoefficients
    (H : CWPairCohomologyTheoryWithCoefficients) :
    IsCohomologyTheoryOnCWPairs H.coefficients H.cohomology :=
  H.theory.2

/-- Weakly equivalent CW pairs induce isomorphisms on the cohomology groups of a bundled
`CWPairCohomologyTheory`. -/
instance CWPairCohomologyTheory.map_isIso_of_weakEquivalence
    {π : Type w} [AddCommGroup π] (H : CWPairCohomologyTheory π)
    (q : ℤ) {P Q : CWPair} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((H q).map f.op) :=
  H.2.weakEquivalenceInvariant q f

/-- Weakly equivalent CW pairs induce isomorphisms on the cohomology groups of a bundled
coefficient-theory pair. -/
instance CWPairCohomologyTheoryWithCoefficients.map_isIso_of_weakEquivalence
    (H : CWPairCohomologyTheoryWithCoefficients) (q : ℤ) {P Q : CWPair} (f : P ⟶ Q)
    [WeakEquivalence f] :
    IsIso ((H.cohomology q).map f.op) := by
  change IsIso ((H.theory q).map f.op)
  infer_instance

/-- The source-facing type of reduced cohomology theories on based CW complexes for a fixed
Chapter 14 based-CW reduced suspension/cofiber setup. -/
abbrev BundledReducedCohomologyTheory
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup) : Type _ :=
  { E : ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat.{w} //
      ReducedCohomologyTheoryOnBasedCWComplexes.{0, w} setup E }

/-- The underlying graded contravariant functor of a bundled reduced cohomology theory on based
CW complexes. -/
abbrev BundledReducedCohomologyTheory.cohomology
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (E : BundledReducedCohomologyTheory setup) :
    ℤ → BasedCWComplexᵒᵖ ⥤ AddCommGrpCat.{w} :=
  E.1

/-- A reduced theory package on based CW complexes carries its defining reduced cohomology theory
instance on the underlying graded functor. -/
instance instReducedCohomologyTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (E : BundledReducedCohomologyTheory setup) :
    ReducedCohomologyTheoryOnBasedCWComplexes.{0, w} setup E.cohomology :=
  E.2

/-- A bundled reduced theory on based CW complexes is determined by the source-facing reduced
cohomology theory structure on its underlying graded functor. -/
theorem BundledReducedCohomologyTheory.spec
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    {setup : BasedCWReducedSuspensionCofiberSetup}
    (E : BundledReducedCohomologyTheory setup) :
    ReducedCohomologyTheoryOnBasedCWComplexes.{0, w} setup E.cohomology :=
  E.2

/-- Theorem 19.2.5: cohomology theories on CW pairs are equivalent to reduced cohomology theories
on based CW complexes. The pair side is packaged by
`CWPairCohomologyTheoryWithCoefficients`, namely a
coefficient group together with a bundled Chapter 19 owner `CWPairCohomologyTheory`, while the
reduced side is packaged by `BundledReducedCohomologyTheory setup` for the chosen Chapter 14
based-CW reduced suspension/cofiber setup `setup`. Since the reduced owner records exactness and
suspension only as existence data, the source-facing formalization exposes explicit forward and
backward transport maps together with inverse laws, without introducing a chosen global
equivalence witness carrying extra concrete CW-pair boundary data. -/
theorem pairCohomologyTheoryEquivReducedCohomologyTheoryOnBasedCWComplexes
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup) :
    ∃ toReduced :
        CWPairCohomologyTheoryWithCoefficients →
          BundledReducedCohomologyTheory setup,
      ∃ fromReduced :
          BundledReducedCohomologyTheory setup →
            CWPairCohomologyTheoryWithCoefficients,
        Function.LeftInverse fromReduced toReduced ∧
          Function.RightInverse fromReduced toReduced := by
  sorry

/-- The explicit transport maps of Theorem 19.2.5 recover the usual bundled type equivalence
between CW-pair cohomology theories and reduced cohomology theories on based CW complexes. -/
theorem pairCohomologyTheoryEquivReducedCohomologyTheoryOnBasedCWComplexes_nonempty
    [CategoryWithCofibrations BasedSpace]
    [CategoryWithCofibrations BasedCWComplex]
    [CategoryWithWeakEquivalences BasedCWComplex]
    (setup : BasedCWReducedSuspensionCofiberSetup) :
    Nonempty
      (CWPairCohomologyTheoryWithCoefficients ≃
        BundledReducedCohomologyTheory setup) := by
  rcases pairCohomologyTheoryEquivReducedCohomologyTheoryOnBasedCWComplexes setup with
    ⟨toReduced, fromReduced, hleft, hright⟩
  exact ⟨
    { toFun := toReduced
      invFun := fromReduced
      left_inv := hleft
      right_inv := hright }⟩
