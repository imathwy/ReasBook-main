import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.PairHomologyTheory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Definition_13_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_7
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra
open Topology
open scoped MonoidalCategory

universe u

open SpacePair

namespace PairHomologyTheory

variable {π : Type u} [AddCommGroup π]

/-- A `PairHomologyTheory` exposes the dimension, exactness, excision, additivity, and
weak-equivalence axioms recorded in its fields. -/
theorem spec (H : PairHomologyTheory π) :
    Nonempty ((H 0).obj point ≅ ModuleCat.of ℤ π) ∧
      (∀ q : ℤ, q ≠ 0 → IsZero ((H q).obj point)) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u},
        (CategoryTheory.ShortComplex.mk
          ((H q).map (subspaceInclusion P))
          ((H q).map (absoluteToRelative P))
          (H.exact₁_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u},
        (CategoryTheory.ShortComplex.mk
          ((H q).map (absoluteToRelative P))
          ((H.boundary q).app P)
          (H.exact₂_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u},
        (CategoryTheory.ShortComplex.mk
          ((H.boundary q).app P)
          ((H (q - 1)).map (subspaceInclusion P))
          (H.exact₃_zero q P)).Exact) ∧
      (∀ q : ℤ, ∀ P : SpacePair.{u}, ∀ U : Set P.space,
        closure U ⊆ interior P.subspace →
          IsIso ((H q).map (removeSubsetInclusion P U))) ∧
      (∀ {ι : Type u}, ∀ q : ℤ, ∀ P : ι → SpacePair.{u},
        Nonempty (((H q).obj (sigmaPair P)) ≅ ∐ fun i : ι ↦ (H q).obj (P i))) ∧
      (∀ q : ℤ, ∀ {P Q : SpacePair.{u}} (f : P ⟶ Q) [WeakEquivalence f],
        IsIso ((H q).map f)) := by
  refine ⟨H.dimensionZero, H.dimensionHigher, H.exact₁, H.exact₂, H.exact₃, ?_, ?_, ?_⟩
  · intro q P U hU
    exact H.excision q P U hU
  · intro ι q P
    exact H.additivity q P
  · intro q P Q f
    exact H.weakEquivalenceInvariant q f

/-- The first exactness window of a pair homology theory is the source-facing sequence
`H_q(A) ⟶ H_q(X) ⟶ H_q(X, A)`. -/
theorem exact_subspace_absoluteToRelative (H : PairHomologyTheory π) (q : ℤ) (P : SpacePair.{u}) :
    (CategoryTheory.ShortComplex.mk
      ((H q).map (subspaceInclusion P))
      ((H q).map (absoluteToRelative P))
      (H.exact₁_zero q P)).Exact :=
  H.exact₁ q P

/-- The second exactness window of a pair homology theory is the source-facing sequence
`H_q(X) ⟶ H_q(X, A) ⟶ H_(q - 1)(A)`. -/
theorem exact_absoluteToRelative_boundary (H : PairHomologyTheory π) (q : ℤ) (P : SpacePair.{u}) :
    (CategoryTheory.ShortComplex.mk
      ((H q).map (absoluteToRelative P))
      ((H.boundary q).app P)
      (H.exact₂_zero q P)).Exact :=
  H.exact₂ q P

/-- The third exactness window of a pair homology theory is the source-facing sequence
`H_q(X, A) ⟶ H_(q - 1)(A) ⟶ H_(q - 1)(X)`. -/
theorem exact_boundary_subspace (H : PairHomologyTheory π) (q : ℤ) (P : SpacePair.{u}) :
    (CategoryTheory.ShortComplex.mk
      ((H.boundary q).app P)
      ((H (q - 1)).map (subspaceInclusion P))
      (H.exact₃_zero q P)).Exact :=
  H.exact₃ q P

/-- The connecting morphism of a pair homology theory is natural with respect to maps of pairs. -/
theorem boundary_naturality
    (H : PairHomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q) :
    CommSq
      ((H q).map f)
      ((H.boundary q).app P)
      ((H.boundary q).app Q)
      ((H (q - 1)).map (subspaceFunctor.map f)) := by
  exact ⟨by simpa using (H.boundary q).naturality f⟩

/-- The naturality square for the connecting morphism commutes as an equality of composites. -/
theorem boundary_naturality_w
    (H : PairHomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q) :
    ((H q).map f) ≫ (H.boundary q).app Q =
      (H.boundary q).app P ≫ ((H (q - 1)).map (subspaceFunctor.map f)) :=
  (H.boundary_naturality q f).w

/-- A weak equivalence of pairs induces an isomorphism on the homology groups of a pair
homology theory. -/
instance map_isIso_of_weakEquivalence
    (H : PairHomologyTheory π) (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q)
    [WeakEquivalence f] :
    IsIso ((H q).map f) :=
  H.weakEquivalenceInvariant q f

end PairHomologyTheory

/-- Helper for Theorem 13.1.1: any bundled CW-pair homology theory has some extension to a pair
homology theory on all pairs. -/
theorem nonempty_pairHomologyTheory_of_cwPairTheory
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) :
    Nonempty (PairHomologyTheory π) := by
  -- Project the chosen extension owner from the Chapter 13 extension package.
  rcases exists_pairHomologyTheory_of_cwPairHomologyTheory E with ⟨H, _e, _he, _uniq⟩
  exact ⟨H⟩

/-- Helper for Theorem 13.1.1: two pair homology theories compared to the same bundled CW-pair
theory are isomorphic, because the Chapter 13 extension package already gives uniqueness for
extensions of that common owner. -/
theorem nonempty_iso_of_commonCWPairTheoryComparison
    {π : Type u} [AddCommGroup π] {E : CWPairHomologyTheory π} {H K : PairHomologyTheory π}
    (eH : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q)
    (hH : HasCWPairTheoryComparison H E.2 eH)
    (eK : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs K q ≅ E q)
    (hK : HasCWPairTheoryComparison K E.2 eK) :
    Nonempty (PairHomologyTheory.Iso H K) := by
  -- Choose the canonical extension owner for `E` and compare both theories to that owner.
  rcases exists_pairHomologyTheory_of_cwPairHomologyTheory E with ⟨H₀, _e₀, _h₀, huniq⟩
  rcases huniq H eH hH with ⟨iH, _hiH⟩
  rcases huniq K eK hK with ⟨iK, _hiK⟩
  -- Compose the inverse comparison to `H` with the comparison to `K`.
  exact ⟨PairHomologyTheory.Iso.trans (PairHomologyTheory.Iso.symm iH) iK⟩

/-- Helper for Theorem 13.1.1: there is a single bundled CW-pair homology theory `E` whose
comparison data can be chosen for every pair homology theory on all pairs. This is the precise
common-owner package needed to deduce both existence and uniqueness in Theorem 13.1.1. -/
abbrev CommonCWPairTheoryComparison
    (π : Type u) [AddCommGroup π] : Prop :=
  ∃ E : CWPairHomologyTheory π,
    ∀ H : PairHomologyTheory π,
      ∃ e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q,
        HasCWPairTheoryComparison H E.2 e

/-- Helper for Theorem 13.1.1: a fixed bundled CW-pair homology theory equipped with
comparison data for every pair homology theory already realizes the Chapter 13 common-owner
package. -/
theorem commonCWPairTheoryComparison_mk
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π)
    (hCompare :
      ∀ H : PairHomologyTheory π,
        ∃ e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q,
          HasCWPairTheoryComparison H E.2 e) :
    CommonCWPairTheoryComparison π := by
  -- Package the supplied comparison family under the chosen common CW-pair owner `E`.
  exact ⟨E, hCompare⟩

/-- Helper for Theorem 13.1.1: auxiliary structure on a common bundled CW-pair owner can be
discarded once only the Chapter 13 comparison package is needed. This is the precise forgetting
step required to pass from a relative-cellular comparison theorem to `CommonCWPairTheoryComparison`.
-/
theorem commonCWPairTheoryComparison_of_auxiliaryPackage
    {π : Type u} [AddCommGroup π]
    {Aux : CWPairHomologyTheory π → Sort _}
    {Extra : CWPairHomologyTheory π → Prop}
    (h :
      ∃ E : CWPairHomologyTheory π,
        ∃ _aux : Aux E,
          Extra E ∧
          ∀ H : PairHomologyTheory π,
            ∃ e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q,
              HasCWPairTheoryComparison H E.2 e) :
    CommonCWPairTheoryComparison π := by
  -- Unpack the auxiliary relative-cellular data, then forget everything except the owner
  -- `E` and its comparison family.
  rcases h with ⟨E, _aux, _hExtra, hCompare⟩
  exact commonCWPairTheoryComparison_mk E hCompare

/-- Helper for Theorem 13.1.1: once a common CW-pair owner is available, existence on all pairs
follows by extending that owner with the Chapter 13 extension theorem. -/
theorem nonempty_pairHomologyTheory_of_commonCWPairTheoryComparison
    {π : Type u} [AddCommGroup π] (hCommon : CommonCWPairTheoryComparison π) :
    Nonempty (PairHomologyTheory π) := by
  -- Extract the common bundled CW-pair owner and extend it to all pairs.
  rcases hCommon with ⟨E, _hCompare⟩
  exact nonempty_pairHomologyTheory_of_cwPairTheory E

/-- Helper for Theorem 13.1.1: once a common CW-pair owner is available, any two pair homology
theories are isomorphic because they both compare to that same owner. -/
theorem nonempty_iso_of_commonCWPairTheoryPackage
    {π : Type u} [AddCommGroup π] (hCommon : CommonCWPairTheoryComparison π)
    (H K : PairHomologyTheory π) :
    Nonempty (PairHomologyTheory.Iso H K) := by
  -- Extract the common owner and the comparison data for the two target theories.
  rcases hCommon with ⟨E, hCompare⟩
  rcases hCompare H with ⟨eH, heH⟩
  rcases hCompare K with ⟨eK, heK⟩
  -- The Chapter 13 uniqueness helper compares both theories through that shared owner.
  exact nonempty_iso_of_commonCWPairTheoryComparison eH heH eK heK

namespace CWPairHomologyTheory

/-- Helper for Theorem 13.1.1: lift the relative cellular chain complex through the module
`ULift` functor without changing the ambient topological data. This isolates the chain-level
universe transport from the still-missing coefficient/tensor transport. -/
noncomputable abbrev uliftRelativeCellularChainComplex
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ((ModuleCat.uliftFunctor.{u, u} ℤ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (relativeCellularChainComplex X A data)

/-- Helper for Theorem 13.1.1: taking homology after the module-level `ULift` transport agrees
with lifting the original relative cellular homology module. This records the reusable chain-level
comparison needed before any coefficient transport is attempted. -/
noncomputable abbrev uliftRelativeCellularChainComplexHomologyIso
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] (n : ℕ) :
    (uliftRelativeCellularChainComplex X A data).homology n ≅
      (ModuleCat.uliftFunctor.{u, u} ℤ).obj ((relativeCellularChainComplex X A data).homology n) :=
  (HomologicalComplex.homologyFunctorIso
      (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).app
    (uliftRelativeCellularChainComplex X A data) ≪≫
  (CategoryTheory.ShortComplex.homologyFunctorIso (ModuleCat.uliftFunctor.{u, u} ℤ)).app
    ((relativeCellularChainComplex X A data).sc n) ≪≫
  (ModuleCat.uliftFunctor.{u, u} ℤ).mapIso
    ((HomologicalComplex.homologyFunctorIso
        (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n).app
      (relativeCellularChainComplex X A data)).symm

/-- Helper for Theorem 13.1.1: if the original relative cellular homology group vanishes in degree
`n`, then the same-level module `ULift` transport of the relative cellular chain complex also has
zero homology in degree `n`. This is the proposition-level transport fact available before the
coefficient-owner transport is built. -/
theorem uliftRelativeCellularChainComplex_homology_isZero_of_isZero
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] (n : ℕ)
    (h : IsZero ((relativeCellularChainComplex X A data).homology n)) :
    IsZero ((uliftRelativeCellularChainComplex X A data).homology n) := by
  -- First lift the zero homology object through `ModuleCat.uliftFunctor`.
  let hLift :
      IsZero ((ModuleCat.uliftFunctor.{u, u} ℤ).obj
        ((relativeCellularChainComplex X A data).homology n)) :=
    (ModuleCat.uliftFunctor.{u, u} ℤ).map_isZero h
  -- Then compare the lifted homology with the homology of the lifted chain complex.
  exact hLift.of_iso (uliftRelativeCellularChainComplexHomologyIso X A data n)

/-- Helper for Theorem 13.1.1: move the small relative cellular chain complex to the common ring
`ULift ℤ` and the ambient carrier universe `u` before taking any tensor products. This isolates
the owner where the module-category monoidal structure is available. -/
noncomputable abbrev relativeCellularChainComplexCommonRing
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data] :
    ChainComplex (ModuleCat.{u} (ULift.{u} ℤ)) ℕ :=
  -- Route correction: reuse the already-stable carrier-universe lift
  -- `uliftRelativeCellularChainComplex`, then change rings inside the ambient universe `u`.
  ((ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (uliftRelativeCellularChainComplex X A data)

/-- Helper for Theorem 13.1.1: form the coefficient tensor product only after the relative
cellular chain complex has been transported to the common ring `ULift ℤ`. This is the coefficient
chain owner whose homology will be transported back to `ModuleCat.{u} ℤ`. -/
noncomputable abbrev relativeCellularCoefficientTensorComplexCommonRing
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π] :
    ChainComplex (ModuleCat.{u} (ULift.{u} ℤ)) ℕ :=
  -- The coefficient module is transported to the common ring by the same restriction-of-scalars
  -- bridge, so both tensor factors live in the same monoidal category.
  relativeCellularChainComplexCommonRing X A data ⊗
    coefficientComplex (ULift.{u} ℤ)
      ((ModuleCat.restrictScalars
          (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ)).obj (ModuleCat.of ℤ π))

/-- Helper for Theorem 13.1.1: universe-polymorphic relative cellular homology with coefficients.
This is the exact coefficient-homology owner needed by the relative-cellular comparison package
when the ambient CW pair lives in `Type u` instead of the current small-universe surface from
`Definition_13_3_7`. -/
noncomputable abbrev relativeCellularHomologyWithCoefficients_u
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (π : Type u) [AddCommGroup π] :
    ℕ → ModuleCat.{u} ℤ :=
  -- Route correction: take homology in the common-ring owner and then transport the resulting
  -- module back to `ModuleCat.{u} ℤ` through the ring-equivalence inverse.
  fun n ↦
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)).inverse.obj
      ((relativeCellularCoefficientTensorComplexCommonRing X A data π).homology n)

/-- Helper for Theorem 13.1.1: a theorem-local presentation of an abstract `CWPair` by an
ambient space together with an explicit relative CW structure on the designated subspace. -/
structure RelativeCWPairPresentation (P : CWPair) where
  X : TopCat.{u}
  A : Set X
  [rel : Topology.RelCWComplex (Set.univ : Set X) A]
  pairIso : (⟨X, A⟩ : SpacePair) ≅ IsCWPair.toSpacePair P

attribute [instance] RelativeCWPairPresentation.rel

/-- Helper for Theorem 13.1.1: every abstract `CWPair` admits a canonical presentation by its own
ambient space together with the stored relative CW structure on its distinguished subspace. -/
theorem nonempty_canonicalRelativeCWPairPresentation (P : CWPair) :
    Nonempty (RelativeCWPairPresentation P) := by
  classical
  let hRel :
      Topology.RelCWComplex (Set.univ : Set (IsCWPair.space P)) (IsCWPair.subspace P) :=
    Classical.choice (show Nonempty
      (Topology.RelCWComplex (Set.univ : Set (IsCWPair.space P)) (IsCWPair.subspace P)) from P.2)
  -- Local instance justification: a `CWPair` stores only `Nonempty` relative-CW data, so this is
  -- the one place where we turn that witness into the instance needed to name a concrete
  -- presentation object.
  letI : Topology.RelCWComplex (Set.univ : Set (IsCWPair.space P)) (IsCWPair.subspace P) := hRel
  -- The canonical presentation is literally the stored space pair, so the comparison is the
  -- identity isomorphism.
  exact ⟨{ X := IsCWPair.space P
           A := IsCWPair.subspace P
           rel := hRel
           pairIso := Iso.refl _ }⟩

/-- Helper for Theorem 13.1.1: fix one canonical presentation for each `CWPair` so later proofs
can talk about chosen relative-CW data without re-choosing the stored witness. -/
noncomputable def canonicalRelativeCWPairPresentation (P : CWPair) :
    RelativeCWPairPresentation P :=
  Classical.choice (nonempty_canonicalRelativeCWPairPresentation P)

/-- Helper for Theorem 13.1.1: in the canonical relative presentation of a `CWPair`, the
designated subspace is realized by the zero skeleton as a relative subcomplex. -/
theorem canonicalRelativeCWPairPresentation_hasBaseSubcomplex
    (P : CWPair) :
    ∃ A₀ : Topology.RelCWComplex.Subcomplex
      (Set.univ : Set (canonicalRelativeCWPairPresentation P).X),
      (A₀ : Set (canonicalRelativeCWPairPresentation P).X) =
        (canonicalRelativeCWPairPresentation P).A := by
  classical
  let presentation := canonicalRelativeCWPairPresentation P
  -- Use the stored relative CW witness so the relative zero skeleton is available.
  letI : Topology.RelCWComplex (Set.univ : Set presentation.X) presentation.A :=
    presentation.rel
  -- The base itself is the subcomplex containing no relative cells.  Constructing it directly
  -- avoids the unnecessary `T2Space` assumption required by the general skeleton API.
  let A₀ : Topology.RelCWComplex.Subcomplex (Set.univ : Set presentation.X) :=
    { carrier := presentation.A
      I := fun _ ↦ ∅
      closed' := Topology.RelCWComplex.isClosedBase
        (Set.univ : Set presentation.X)
      union' := by simp }
  exact ⟨A₀, rfl⟩

/-- Helper for Theorem 13.1.1: replacing the designated subspace in the canonical relative
presentation by its zero-skeleton subcomplex does not change the represented CW pair. -/
theorem canonicalRelativeCWPairPresentation_baseSubcomplexPairIso
    (P : CWPair) :
    ∃ A₀ : Topology.RelCWComplex.Subcomplex
      (Set.univ : Set (canonicalRelativeCWPairPresentation P).X),
      Nonempty
        ((⟨(canonicalRelativeCWPairPresentation P).X,
            (A₀ : Set (canonicalRelativeCWPairPresentation P).X)⟩ : SpacePair) ≅
          IsCWPair.toSpacePair P) := by
  classical
  let presentation := canonicalRelativeCWPairPresentation P
  -- Reuse the canonical relative presentation and extract its base as a subcomplex first.
  rcases canonicalRelativeCWPairPresentation_hasBaseSubcomplex P with ⟨A₀, hA₀⟩
  refine ⟨A₀, ?_⟩
  -- After rewriting the carrier of the zero skeleton to the stored base, the original pair
  -- isomorphism closes the comparison.
  refine ⟨?_⟩
  simpa [presentation, hA₀] using presentation.pairIso

/-- Helper for Theorem 13.1.1: a quotient-side presentation of a CW pair keeps one chosen
relative presentation `(X, A)` together with one chosen CW structure on the quotient `X / A`
compatible with the relative cells of `(X, A)`. This is the stable quotient owner that exists
without forcing an absolute CW structure on `X` itself. -/
structure RelativeCWQuotientPresentation (P : CWPair) where
  presentation : RelativeCWPairPresentation P
  [quotientCW :
    CWComplex (Set.univ : Set (collapseSubsetType presentation.X presentation.A))]
  quotientCompat :
    Topology.RelCWComplex.IsQuotientCWComplex presentation.A quotientCW

attribute [instance] RelativeCWQuotientPresentation.quotientCW

/-- Helper for Theorem 13.1.1: every abstract `CWPair` admits a quotient-side presentation by
choosing its canonical relative presentation and then applying the quotient CW-complex theorem to
that chosen relative pair. -/
theorem nonempty_relativeCWQuotientPresentation (P : CWPair) :
    Nonempty (RelativeCWQuotientPresentation P) := by
  classical
  let presentation := canonicalRelativeCWPairPresentation P
  -- Route correction: the failed absolute-presentation route tried to force an ambient
  -- `CWComplex/Subcomplex` on `presentation.X`; the quotient theorem gives the needed absolute CW
  -- structure on `presentation.X / presentation.A` directly, which is the stable replacement.
  letI :
      Topology.RelCWComplex (Set.univ : Set presentation.X) presentation.A :=
    presentation.rel
  -- Apply the quotient CW-complex theorem once to the chosen relative presentation.
  rcases quotientHasCWComplexWithRelativeCells presentation.X presentation.A with ⟨cw, hcw⟩
  exact ⟨
    { presentation := presentation
      quotientCW := cw
      quotientCompat := hcw }⟩

/-- Helper for Theorem 13.1.1: fix one quotient-side presentation for each `CWPair` so later
proofs can work with stable quotient CW data without re-choosing the relative presentation or the
quotient CW structure. -/
noncomputable def canonicalRelativeCWQuotientPresentation (P : CWPair) :
    RelativeCWQuotientPresentation P :=
  Classical.choice (nonempty_relativeCWQuotientPresentation P)

/-- Helper for Theorem 13.1.1: when the canonical relative presentation of `P` has empty base,
its stored relative CW structure upgrades directly to an absolute CW structure on the ambient
space. This isolates the only branch where the ambient-owner route is definitionally available. -/
theorem canonicalRelativePresentationAbsoluteCW_of_emptyBase
    (P : CWPair)
    (hAempty : (canonicalRelativeCWPairPresentation P).A = ∅) :
    Nonempty (CWComplex (Set.univ : Set (canonicalRelativeCWPairPresentation P).X)) := by
  classical
  let presentation := canonicalRelativeCWPairPresentation P
  have hAempty' : presentation.A = ∅ := hAempty
  -- Transport the stored relative-CW witness along the equality of its base with `∅`.
  letI : Topology.RelCWComplex (Set.univ : Set presentation.X) ∅ :=
    hAempty' ▸ presentation.rel
  -- The empty-base branch is exactly the `RelCWComplex.toCWComplex` situation.
  exact ⟨Topology.RelCWComplex.toCWComplex (Set.univ : Set presentation.X)⟩

/-- Helper for Theorem 13.1.1: the canonical quotient-side presentation exposes the quotient
`0`-cell equivalence coming from `IsQuotientCWComplex.zero`. This is the stable quotient-side
normal form for selecting the collapsed vertex. -/
theorem canonicalRelativeQuotientPresentation_zeroCellEquiv
    (P : CWPair) :
    Nonempty
      (cellularCell
          (collapseSubsetType
            (canonicalRelativeCWQuotientPresentation P).presentation.X
            (canonicalRelativeCWQuotientPresentation P).presentation.A) 0 ≃
        (PLift
            ((canonicalRelativeCWQuotientPresentation P).presentation.A.Nonempty) ⊕
          Topology.RelCWComplex.cell
            (Set.univ : Set (canonicalRelativeCWQuotientPresentation P).presentation.X) 0)) := by
  classical
  let presentation := canonicalRelativeCWQuotientPresentation P
  -- Unpack the stored quotient-compatibility witness on the canonical quotient presentation.
  exact presentation.quotientCompat.zero

/-- Helper for Theorem 13.1.1: if the base of the canonical quotient-side presentation is
nonempty, one can choose a quotient `0`-cell representing the collapsed vertex. This discharges
the quotient-side degree-zero side condition without rederiving the full quotient CW structure. -/
theorem canonicalRelativeQuotientPresentation_hasCollapsedZeroCell
    (P : CWPair)
    (hA :
      (canonicalRelativeCWQuotientPresentation P).presentation.A.Nonempty) :
    ∃ cellEquiv :
      cellularCell
          (collapseSubsetType
            (canonicalRelativeCWQuotientPresentation P).presentation.X
            (canonicalRelativeCWQuotientPresentation P).presentation.A) 0 ≃
        (PLift
            ((canonicalRelativeCWQuotientPresentation P).presentation.A.Nonempty) ⊕
          Topology.RelCWComplex.cell
            (Set.univ : Set (canonicalRelativeCWQuotientPresentation P).presentation.X) 0),
      ∃ collapsedZeroCell :
        cellularCell
          (collapseSubsetType
            (canonicalRelativeCWQuotientPresentation P).presentation.X
            (canonicalRelativeCWQuotientPresentation P).presentation.A) 0,
        cellEquiv collapsedZeroCell = Sum.inl ⟨hA⟩ := by
  classical
  -- Reuse the quotient `0`-cell equivalence first, then choose the preimage of the collapsed
  -- vertex under that equivalence.
  rcases canonicalRelativeQuotientPresentation_zeroCellEquiv P with ⟨cellEquiv⟩
  refine ⟨cellEquiv, cellEquiv.symm (Sum.inl ⟨hA⟩), ?_⟩
  simp

/-- Helper for Theorem 13.1.1: any absolute CW complex admits a chosen cellular differential
family. -/
theorem existsCellularDifferentialFamily
    (X : TopCat.{u}) [CWComplex (Set.univ : Set X)] :
    Nonempty (CellularDifferentialFamily X) := by
  -- Reuse the induced-chain-map existence theorem on the identity cellular map.
  have hId : IsCellularCWMap (𝟙 X) := by
    constructor
    intro n x hx
    simpa using hx
  -- The source differential family in that induced map is already the required choice on `X`.
  rcases existsInducedCellularChainMap (X := X) (Y := X) (𝟙 X) hId with
    ⟨dataX, _dataY, _φ, _hφ⟩
  exact ⟨dataX⟩

/-- Helper for Theorem 13.1.1: a nonempty quotient branch of the canonical presentation chooses
the quotient CW data that are already available before any owner-level homology theory is built.
This isolates the stable quotient-side inputs from the still-missing comparison to a bundled
`CWPairHomologyTheory`. -/
structure CanonicalRelativeQuotientBranchData (P : CWPair) where
  quotientPresentation : RelativeCWQuotientPresentation P
  baseNonempty : quotientPresentation.presentation.A.Nonempty
  quotientData :
    CellularDifferentialFamily
      (collapseSubsetType
        quotientPresentation.presentation.X
        quotientPresentation.presentation.A)
  cellEquiv :
    cellularCell
        (collapseSubsetType
          quotientPresentation.presentation.X
          quotientPresentation.presentation.A) 0 ≃
      (PLift quotientPresentation.presentation.A.Nonempty ⊕
        Topology.RelCWComplex.cell
          (Set.univ : Set quotientPresentation.presentation.X) 0)
  collapsedZeroCell :
    cellularCell
      (collapseSubsetType
        quotientPresentation.presentation.X
        quotientPresentation.presentation.A) 0
  collapsedZeroCell_spec :
    cellEquiv collapsedZeroCell = Sum.inl ⟨baseNonempty⟩

/-- Helper for Theorem 13.1.1: a nonempty canonical quotient presentation admits a chosen
cellular differential family on the quotient CW complex. -/
theorem existsCanonicalRelativeQuotientDifferentialFamily
    (P : CWPair) :
    Nonempty (
      CellularDifferentialFamily
        (collapseSubsetType
          (canonicalRelativeCWQuotientPresentation P).presentation.X
          (canonicalRelativeCWQuotientPresentation P).presentation.A)) := by
  let presentation := canonicalRelativeCWQuotientPresentation P
  -- Reuse the absolute CW-complex chooser on the quotient carrier fixed by the canonical
  -- quotient presentation.
  simpa [presentation] using
    existsCellularDifferentialFamily
      (X := TopCat.of
        (collapseSubsetType presentation.presentation.X presentation.presentation.A))

/-- Helper for Theorem 13.1.1: once the canonical quotient presentation has nonempty base, the
entire quotient-side branch data can be chosen without reopening the ambient absolute route. -/
theorem nonempty_canonicalRelativeQuotientBranchData_of_nonemptyBase
    (P : CWPair)
    (hA :
      (canonicalRelativeCWQuotientPresentation P).presentation.A.Nonempty) :
    Nonempty (CanonicalRelativeQuotientBranchData P) := by
  let presentation := canonicalRelativeCWQuotientPresentation P
  -- First choose the quotient differential family on the canonical quotient CW complex.
  rcases existsCanonicalRelativeQuotientDifferentialFamily P with ⟨quotientData⟩
  -- Then choose the collapsed quotient `0`-cell representing the image of the base.
  rcases canonicalRelativeQuotientPresentation_hasCollapsedZeroCell P hA with
    ⟨cellEquiv, collapsedZeroCell, collapsedZeroCell_spec⟩
  exact ⟨
    { quotientPresentation := presentation
      baseNonempty := hA
      quotientData := quotientData
      cellEquiv := cellEquiv
      collapsedZeroCell := collapsedZeroCell
      collapsedZeroCell_spec := collapsedZeroCell_spec }⟩

/-- Helper for Theorem 13.1.1: the empty-base branch still uses the original ambient absolute
CW-pair surface, because only in this branch does the canonical relative presentation upgrade
directly to an absolute CW complex on the ambient space. -/
structure AmbientRelativeCellularHomologyModel
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) (q : ℤ) (P : CWPair) where
  quotientPresentation : RelativeCWQuotientPresentation P
  X : TopCat.{u}
  [cw : CWComplex (Set.univ : Set X)]
  A : Topology.CWComplex.Subcomplex (Set.univ : Set X)
  pairIso : (⟨X, (A : Set X)⟩ : SpacePair) ≅ IsCWPair.toSpacePair P
  data : CellularDifferentialFamily X
  [descends : RelativeCellularDifferentialDescends X A data]
  homologyIso :
    (E q).obj P ≅ relativeCellularHomologyWithCoefficients_u X A data π (Int.toNat q)

attribute [instance] AmbientRelativeCellularHomologyModel.cw
attribute [instance] AmbientRelativeCellularHomologyModel.descends

/-- Helper for Theorem 13.1.1: the nonempty-base branch keeps the quotient presentation as the
primary model surface. The comparison target is recorded abstractly because the remaining blocker
is exactly the owner-level bridge from this quotient-side data to a bundled CW-pair homology
theory. -/
structure QuotientRelativeCellularHomologyModel
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) (q : ℤ) (P : CWPair) where
  branchData : CanonicalRelativeQuotientBranchData P
  quotientHomologyObject : ModuleCat.{u} ℤ
  homologyIso : (E q).obj P ≅ quotientHomologyObject

/-- Helper for Theorem 13.1.1: the theorem-local relative-cellular model surface is branchwise.
Empty-base pairs use the original ambient absolute route, while nonempty-base pairs stay
quotient-native instead of forcing a nonexistent absolute `CWComplex/Subcomplex` presentation on
the original ambient space. -/
inductive RelativeCellularHomologyModel
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) (q : ℤ) (P : CWPair) where
  | ambient :
      AmbientRelativeCellularHomologyModel E q P →
        RelativeCellularHomologyModel E q P
  | quotient :
      QuotientRelativeCellularHomologyModel E q P →
        RelativeCellularHomologyModel E q P

/-- Helper for Theorem 13.1.1: a bundled CW-pair homology theory carries relative cellular models
when each nonnegative degree and each CW pair admit a chosen `RelativeCellularHomologyModel`. -/
abbrev RelativeCellularModels
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) : Type (u + 1) :=
  ∀ q : ℤ, 0 ≤ q → ∀ P : CWPair, E.RelativeCellularHomologyModel q P

/-- Helper for Theorem 13.1.1: a bundled CW-pair homology theory vanishes in negative degrees
when every negative graded piece is zero on each CW pair. -/
def VanishesInNegativeDegrees
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) : Prop :=
  ∀ q : ℤ, q < 0 → ∀ P : CWPair, IsZero ((E q).obj P)

/-- Helper for Theorem 13.1.1: the boundary natural transformation of a bundled CW-pair homology
theory is the boundary of its underlying Chapter 13 CW-pair structure. -/
abbrev boundary
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) (q : ℤ) :=
  E.2.boundary q

/-- Helper for Theorem 13.1.1: a comparison isomorphism from a pair homology theory `H` to a
bundled CW-pair homology theory `E` is a degreewise natural isomorphism on the restriction of
`H` to CW pairs. -/
abbrev ComparisonIso
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) (H : PairHomologyTheory π) :
    Type (u + 1) :=
  ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q

/-- Helper for Theorem 13.1.1: a comparison isomorphism is admissible exactly when it satisfies
the Chapter 13 boundary-compatibility condition for the bundled CW-pair owner `E`. -/
def HasComparison
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) (H : PairHomologyTheory π)
    (e : E.ComparisonIso H) : Prop :=
  HasCWPairTheoryComparison H E.2 e

/-- Helper for Theorem 13.1.1: the bundled comparison condition rewrites to the explicit
commuting equation for the boundary square in each degree and each CW pair. -/
theorem hasComparison_boundary_comm
    {π : Type u} [AddCommGroup π] {E : CWPairHomologyTheory π} {H : PairHomologyTheory π}
    {e : E.ComparisonIso H} (he : E.HasComparison H e) (q : ℤ) (P : CWPair) :
    ((e q).hom.app P) ≫ (CWPairHomologyTheory.boundary E q).app P =
      ((H.boundary q).app (IsCWPair.toSpacePair P)) ≫
        ((e (q - 1)).hom.app (IsCWPair.subspacePair P)) := by
  -- Unfold the bundled comparison surface back to the Chapter 13 boundary-compatibility theorem.
  exact hasCWPairTheoryComparison_boundary_comm he q P

end CWPairHomologyTheory

/-- Helper for Theorem 13.1.1: forgetting the support wrapper on
`RelativeCellularComparisonData` leaves exactly the theorem-local package used by the Chapter 13
wrapper theorem. -/
structure RelativeCellularComparisonPackage
    {π : Type u} [AddCommGroup π] (E : CWPairHomologyTheory π) : Type (u + 1) where
  models : E.RelativeCellularModels
  vanishesInNegativeDegrees : E.VanishesInNegativeDegrees
  comparison :
    ∀ H : PairHomologyTheory π,
      ∃ e : E.ComparisonIso H,
        E.HasComparison H e

/-- Helper for Theorem 13.1.1: the canonical support datum for the remaining relative-cellular
frontier packages the common bundled CW-pair owner together with the model carrier, the
negative-degree vanishing statement, and the comparison family to every pair homology theory. -/
structure RelativeCellularComparisonData
    (π : Type u) [AddCommGroup π] : Type (u + 1) where
  theory : CWPairHomologyTheory π
  models : theory.RelativeCellularModels
  vanishesInNegativeDegrees : theory.VanishesInNegativeDegrees
  comparison :
    ∀ H : PairHomologyTheory π,
      ∃ e : theory.ComparisonIso H,
        theory.HasComparison H e

/-- Helper for Theorem 13.1.1: an explicit common-owner package immediately yields the canonical
support datum `RelativeCellularComparisonData`. This isolates the final record assembly from the
remaining existence theorem for the relative-cellular package itself. -/
theorem nonempty_relativeCellularComparisonData_ofPackage
    {π : Type u} [AddCommGroup π]
    (h :
      ∃ E : CWPairHomologyTheory π,
        ∃ _ : E.RelativeCellularModels,
          E.VanishesInNegativeDegrees ∧
          ∀ H : PairHomologyTheory π,
            ∃ e : E.ComparisonIso H,
              E.HasComparison H e) :
    Nonempty (RelativeCellularComparisonData π) := by
  -- Unpack the explicit package, then assemble the theorem-local record with those fields.
  rcases h with ⟨E, hModels, hVanishes, hComparison⟩
  exact ⟨
    { theory := E
      models := hModels
      vanishesInNegativeDegrees := hVanishes
      comparison := hComparison }⟩

/-- Helper for Theorem 13.1.1: a fixed theorem-local relative-cellular comparison package already
yields the canonical support datum by reattaching its common bundled CW-pair owner. -/
theorem nonempty_relativeCellularComparisonData_ofComparisonPackage
    {π : Type u} [AddCommGroup π] (h :
      ∃ E : CWPairHomologyTheory π,
        Nonempty (RelativeCellularComparisonPackage E)) :
    Nonempty (RelativeCellularComparisonData π) := by
  -- Unpack the common owner and then reuse the explicit-package assembler from the previous step.
  rcases h with ⟨E, ⟨hPackage⟩⟩
  exact nonempty_relativeCellularComparisonData_ofPackage
    (π := π) ⟨E, hPackage.models, hPackage.vanishesInNegativeDegrees, hPackage.comparison⟩

/-- Helper for Theorem 13.1.1: the unresolved common-ring frontier is now isolated as the
existence of one theorem-local relative-cellular comparison package. -/
theorem existsRelativeCellularCWPairTheoryComparison_ofData
    {π : Type u} [AddCommGroup π]
    (h : Nonempty (RelativeCellularComparisonData π)) :
    ∃ E : CWPairHomologyTheory π,
      Nonempty (RelativeCellularComparisonPackage E) := by
  -- Unpack the canonical support datum, then reattach the theorem-local package fields.
  rcases h with ⟨data⟩
  exact ⟨data.theory, ⟨
    { models := data.models
      vanishesInNegativeDegrees := data.vanishesInNegativeDegrees
      comparison := data.comparison }⟩⟩

/-- Helper for Theorem 13.1.1: isolate the remaining frontier as one explicit bundled CW-pair
owner equipped with the relative-cellular package fields, before repackaging it into
`RelativeCellularComparisonData`. -/
theorem existsRelativeCellularComparisonDataSupportCore
    {π : Type u} [AddCommGroup π] :
    Nonempty (RelativeCellularComparisonData π) := by
  -- Route correction: the real frontier is a single chosen support datum carrying the bundled
  -- CW-pair owner, its relative-cellular models, negative-degree vanishing, and the comparison
  -- family together. The old split owner/comparison route kept reopening the same wrong normal
  -- form instead of stabilizing one package, so the theorem-local model surface is now branchwise.
  -- The branch-local inputs are now isolated concretely: the empty-base branch uses
  -- `AmbientRelativeCellularHomologyModel`, while the nonempty-base branch packages its stable
  -- quotient-side choices in `CanonicalRelativeQuotientBranchData`.
  -- TODO for Theorem 13.1.1: construct one `RelativeCellularComparisonData π` directly from the
  -- canonical branchwise presentations. The remaining blocker is now narrower: after discharging
  -- the branch-local CW side conditions above, the file still lacks the owner-level bridge from
  -- `AmbientRelativeCellularHomologyModel` and `CanonicalRelativeQuotientBranchData` to one
  -- bundled `CWPairHomologyTheory π` carrying the required model, vanishing, and comparison
  -- fields.
  sorry

/-- Helper for Theorem 13.1.1: once the chosen support datum is fixed, the bundled CW-pair owner
and its relative-cellular model/vanishing fields are obtained by projection. -/
theorem existsCanonicalRelativeCellularCWPairTheory
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      Nonempty E.RelativeCellularModels ∧ E.VanishesInNegativeDegrees := by
  -- Project the owner and its two theorem-local support fields from the stabilized support datum.
  rcases existsRelativeCellularComparisonDataSupportCore (π := π) with ⟨data⟩
  exact ⟨data.theory, ⟨data.models⟩, data.vanishesInNegativeDegrees⟩

/-- Helper for Theorem 13.1.1: once the canonical bundled relative-cellular CW-pair theory has
been fixed, its comparison family to every pair homology theory is already stored in the chosen
support datum. -/
theorem comparisonPackageForCanonicalRelativeCellularTheory
    {π : Type u} [AddCommGroup π] (data : RelativeCellularComparisonData π) :
    ∀ H : PairHomologyTheory π,
      ∃ e : data.theory.ComparisonIso H,
        data.theory.HasComparison H e := by
  -- The chosen support datum already packages the full comparison family degreewise.
  intro H
  exact data.comparison H

/-- Helper for Theorem 13.1.1: isolate the remaining frontier as one explicit bundled CW-pair
owner equipped with the relative-cellular package fields, before repackaging it into
`RelativeCellularComparisonData`. -/
theorem existsRelativeCellularComparisonPackageSupport
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      Nonempty (RelativeCellularComparisonPackage E) := by
  -- The package wrapper is now a pure projection from the single stabilized support datum.
  rcases existsRelativeCellularComparisonDataSupportCore (π := π) with ⟨data⟩
  exact ⟨data.theory, ⟨
    { models := data.models
      vanishesInNegativeDegrees := data.vanishesInNegativeDegrees
      comparison := comparisonPackageForCanonicalRelativeCellularTheory data }⟩⟩

/-- Helper for Theorem 13.1.1: isolate the remaining frontier as one explicit bundled CW-pair
owner equipped with the relative-cellular package fields, before repackaging it into
`RelativeCellularComparisonData`. -/
theorem existsRelativeCellularComparisonDataSupport
    {π : Type u} [AddCommGroup π] :
    Nonempty (RelativeCellularComparisonData π) := by
  -- The public support theorem is now the direct alias of the unique remaining frontier.
  exact existsRelativeCellularComparisonDataSupportCore (π := π)

/-- Helper for Theorem 13.1.1: isolate the remaining frontier as one explicit bundled CW-pair
owner equipped with the relative-cellular package fields, before repackaging it into
`RelativeCellularComparisonData`. -/
theorem exists_commonOwnerRelativeCellularComparisonPackage
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      ∃ _ : E.RelativeCellularModels,
        E.VanishesInNegativeDegrees ∧
        ∀ H : PairHomologyTheory π,
          ∃ e : E.ComparisonIso H,
            E.HasComparison H e := by
  -- Unpack the stabilized support datum and forget only the theorem-local record wrapper.
  rcases existsRelativeCellularComparisonDataSupport (π := π) with ⟨data⟩
  exact ⟨data.theory, data.models, data.vanishesInNegativeDegrees, data.comparison⟩

/-- Helper for Theorem 13.1.1: the common-ring frontier is the existence of one bundled
CW-pair homology theory equipped with relative-cellular models in nonnegative degrees,
vanishing in negative degrees, and a comparison family to every pair homology theory. -/
theorem exists_relativeCellularComparisonData_fromCommonOwner
    {π : Type u} [AddCommGroup π] :
    Nonempty (RelativeCellularComparisonData π) := by
  -- Route correction: the support theorem is now the actual frontier, so this alias should point
  -- directly at that theorem instead of reopening the explicit package layer.
  exact existsRelativeCellularComparisonDataSupport (π := π)

/-- Helper for Theorem 13.1.1: the common-ring frontier is the existence of one bundled
CW-pair homology theory equipped with relative-cellular models in nonnegative degrees,
vanishing in negative degrees, and a comparison family to every pair homology theory. -/
theorem existsCommonRingRelativeCellularPackage
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      ∃ _ : E.RelativeCellularModels,
        E.VanishesInNegativeDegrees ∧
        ∀ H : PairHomologyTheory π,
          ∃ e : E.ComparisonIso H,
            E.HasComparison H e := by
  -- Unpack the stabilized theorem-local support datum and repackage its fields into the explicit
  -- existential package expected by the later wrapper theorems.
  rcases exists_relativeCellularComparisonData_fromCommonOwner (π := π) with ⟨data⟩
  exact ⟨data.theory, data.models, data.vanishesInNegativeDegrees, data.comparison⟩

/-- Helper for Theorem 13.1.1: the remaining missing premise is the source-facing support theorem
returning the canonical relative-cellular comparison datum. All later wrappers should delegate the
frontier to this theorem instead of reopening the package assembly. -/
theorem exists_relativeCellularComparisonData_fromCommonRing
    {π : Type u} [AddCommGroup π] :
    Nonempty (RelativeCellularComparisonData π) := by
  -- The public common-ring alias now delegates directly to the minimal common-owner support
  -- theorem, so later wrappers do not reopen the existential package layer.
  exact exists_relativeCellularComparisonData_fromCommonOwner (π := π)

/-- Helper for Theorem 13.1.1: the unresolved common-ring frontier is now isolated as the
existence of one theorem-local relative-cellular comparison package. -/
theorem existsRelativeCellularCWPairTheoryComparison_fromCommonRing
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      Nonempty (RelativeCellularComparisonPackage E) := by
  -- Route correction: the package theorem is now the actual frontier, so this wrapper should
  -- point directly at that theorem instead of reopening the support-record layer.
  exact existsRelativeCellularComparisonPackageSupport (π := π)

/-- Helper for Theorem 13.1.1: the remaining missing premise can now be stated as a single
universe-polymorphic support theorem returning `RelativeCellularComparisonData`. -/
theorem exists_relativeCellularComparisonData
    {π : Type u} [AddCommGroup π] :
    Nonempty (RelativeCellularComparisonData π) := by
  -- Route correction: this theorem is now only a public alias for the stabilized common-ring
  -- support frontier, so later wrappers do not reopen the package assembly.
  exact exists_relativeCellularComparisonData_fromCommonRing (π := π)

/-- Helper for Theorem 13.1.1: explicit support data for a fixed bundled CW-pair homology theory
packages directly into the theorem-local `RelativeCellularComparisonPackage`. -/
theorem nonempty_relativeCellularComparisonPackage_ofData
    {π : Type u} [AddCommGroup π] (data : RelativeCellularComparisonData π) :
    Nonempty (RelativeCellularComparisonPackage data.theory) := by
  -- Package the chosen model carrier, negative-degree vanishing, and comparison family into the
  -- theorem-local record expected by the Chapter 13 wrapper.
  exact ⟨
    { models := data.models
      vanishesInNegativeDegrees := data.vanishesInNegativeDegrees
      comparison := data.comparison }⟩

/-- Helper for Theorem 13.1.1: once the support theorem returns a common relative-cellular
comparison datum, the local wrapper theorem is a pure repackaging step. -/
theorem existsRelativeCellularCWPairTheoryComparison_ofSupport
    {π : Type u} [AddCommGroup π]
    (h : Nonempty (RelativeCellularComparisonData π)) :
    ∃ E : CWPairHomologyTheory π,
      Nonempty (RelativeCellularComparisonPackage E) := by
  -- Unpack the canonical support theorem, then forget the wrapper down to the theorem-local
  -- `RelativeCellularComparisonPackage`.
  rcases h with ⟨data⟩
  exact ⟨data.theory, nonempty_relativeCellularComparisonPackage_ofData data⟩

/-- Helper for Theorem 13.1.1: an explicit common-owner relative-cellular package already
determines the Chapter 13 common CW-pair owner package, because only the bundled owner and its
comparison family survive in the public endgame. -/
theorem commonCWPairTheoryComparison_ofRelativeCellularPackage
    {π : Type u} [AddCommGroup π]
    (h :
      ∃ E : CWPairHomologyTheory π,
        ∃ _ : E.RelativeCellularModels,
          E.VanishesInNegativeDegrees ∧
          ∀ H : PairHomologyTheory π,
            ∃ e : E.ComparisonIso H,
              E.HasComparison H e) :
    CommonCWPairTheoryComparison π := by
  -- Forget the theorem-local model and vanishing fields, then retain only the common owner and
  -- its comparison family used by the Chapter 13 extension/uniqueness endgame.
  rcases h with ⟨E, _models, _hVanishes, hComparison⟩
  exact commonCWPairTheoryComparison_mk E hComparison

/-- Helper for Theorem 13.1.1: there is a single bundled CW-pair homology theory `E` whose
abstract relative-cellular comparison package can be chosen at the ambient coefficient universe.
This isolates the precise remaining prerequisite beneath the Chapter 13 wrapper theorem. -/
theorem existsRelativeCellularCWPairTheoryComparison
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      Nonempty (RelativeCellularComparisonPackage E) := by
  -- Route correction: the remaining frontier has been stabilized directly at the theorem-local
  -- package level, so the wrapper theorem now simply exposes that common-ring package.
  exact existsRelativeCellularCWPairTheoryComparison_fromCommonRing

/-- Helper for Theorem 13.1.1: there is a single bundled CW-pair homology theory `E` whose
comparison data can be chosen for every pair homology theory on all pairs. This is the precise
common-owner package needed to deduce both existence and uniqueness in Theorem 13.1.1. -/
theorem existsCommonCWPairTheoryComparison
    {π : Type u} [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      ∀ H : PairHomologyTheory π,
        ∃ e : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q,
          HasCWPairTheoryComparison H E.2 e := by
  -- Route correction: keep the public endgame pointed directly at the actual frontier theorem,
  -- rather than reopening the intermediate theorem-local package wrappers.
  exact commonCWPairTheoryComparison_ofRelativeCellularPackage
    (exists_commonOwnerRelativeCellularComparisonPackage (π := π))

/-- Theorem 13.1.1 (1): relative to the intended weak-equivalence structure on pairs of spaces,
there exists a homology theory `H_q(X, A; π)` whose data satisfy the dimension, exactness,
excision, additivity, and weak-equivalence axioms. -/
theorem exists_pairHomologyTheory
    (π : Type u) [AddCommGroup π] :
    Nonempty (PairHomologyTheory π) := by
  -- Route correction: the only missing input is the common owner itself; once supplied, the
  -- existence proof is the short Chapter 13 extension endgame.
  exact nonempty_pairHomologyTheory_of_commonCWPairTheoryComparison
    (π := π) existsCommonCWPairTheoryComparison

/-- Theorem 13.1.1 (2): the dimension, exactness, excision, additivity, and weak-equivalence
axioms characterize `H_q(X, A; π)` up to isomorphism of graded homology theories on pairs for the
intended weak-equivalence structure on `SpacePair`. -/
theorem pairHomologyTheory_unique
    (π : Type u) [AddCommGroup π]
    (H K : PairHomologyTheory π) :
    Nonempty (PairHomologyTheory.Iso H K) := by
  -- Route correction: the uniqueness proof is finished once the common owner package is
  -- available, so isolate the remaining frontier to constructing that package.
  exact nonempty_iso_of_commonCWPairTheoryPackage
    (π := π) existsCommonCWPairTheoryComparison H K
