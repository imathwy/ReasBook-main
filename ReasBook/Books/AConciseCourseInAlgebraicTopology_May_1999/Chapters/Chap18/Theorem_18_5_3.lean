import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Lemma_10_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Construction_18_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Remark_18_2_3.LinearYoneda
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3.Coefficients
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3.Skeleton

open CategoryTheory
open HomologicalComplex
open Topology
open Topology.RelCWComplex.IsQuotientCWComplex
open scoped TopCat Topology Topology.Homotopy
open scoped CellularCohomology

noncomputable section

universe u

section

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable [CWComplex (Set.univ : Set X)]
variable (A : Topology.CWComplex.Subcomplex (Set.univ : Set X))
variable [Topology.RelCWComplex (Set.univ : Set X) (A : Set X)]
variable {Y : Type u} [TopologicalSpace Y] [CompactlyGeneratedWeakHausdorffSpace Y]

-- Semantic recall via repository reuse: the canonical relative-skeleton inclusions and
-- restrictions live in `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3.Skeleton`, and the Chapter 9
-- coefficient-system bridge from the sphere-evaluation fiber owner to `π_ n` now lives in
-- `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3.Coefficients`. This theorem file keeps the source-
-- facing extension criterion and obstruction-class predicate on top of that reusable API.

/-- A map `f : X^n → Y` extends over `X^(n + 1)` when it factors through the canonical skeletal
inclusion `X^n ↪ X^(n + 1)`. -/
@[expose] def extendsOverRelativeSkeleton
    (n : ℕ) (f : C(relativePairSkeleton A n, Y)) : Prop :=
  ∃ g : C(relativePairSkeleton A (n + 1), Y),
    g.comp
        (relativeSkeletonInclusion A n (n + 1) (Nat.le_add_right n 1)) =
      f

/-- Unfolding `extendsOverRelativeSkeleton` gives the factorization criterion through the
canonical inclusion `X^n ↪ X^(n + 1)`. -/
theorem extendsOverRelativeSkeleton_iff
    (n : ℕ) (f : C(relativePairSkeleton A n, Y)) :
    extendsOverRelativeSkeleton A n f ↔
      ∃ g : C(relativePairSkeleton A (n + 1), Y),
        g.comp
            (relativeSkeletonInclusion A n (n + 1) (Nat.le_add_right n 1)) =
          f :=
  Iff.rfl

/-- The canonical obstruction cochain from Construction 18.5.2 for
`f : X^n ⟶ Y`, restricted to the relative CW structure determined by `A ⊆ X`. -/
@[expose] abbrev relativeSkeletonObstructionCochain
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y) (f : C(relativePairSkeleton A n, Y)) :
    Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1) →
      ZerothHomotopy (sphereBasepointFiber n y₀) :=
  obstructionCochain (Set.univ : Set X) n y₀ f

private abbrev quotientRelativeChainComplex
    (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
    (quotientData : CellularDifferentialFamily (collapseSubsetType X (A : Set X)))
    (collapsedZeroCell : cw.cell 0) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  @relativeCellularQuotientReducedChainComplex X _ _ A cw quotientData collapsedZeroCell

private abbrev quotientRelativeCochainComplex
    (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
    (quotientData : CellularDifferentialFamily (collapseSubsetType X (A : Set X)))
    (collapsedZeroCell : cw.cell 0) (π : Type u) [AddCommGroup π] :
    CochainComplex (ModuleCat ℤ) ℕ :=
  (quotientRelativeChainComplex A cw quotientData collapsedZeroCell).linearYonedaObj ℤ
    (ModuleCat.of ℤ π)

private noncomputable def quotientRelativeCellEquiv
    (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
    (hcw : Topology.RelCWComplex.IsQuotientCWComplex (A : Set X) cw) (n : ℕ) :
    cw.cell (n + 1) ≃ Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1) :=
  Classical.choice (succ hcw n)

private noncomputable def quotientRelativeObstructionCochain
    (n : ℕ)
    (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
    (hcw : Topology.RelCWComplex.IsQuotientCWComplex (A : Set X) cw)
    (quotientData : CellularDifferentialFamily (collapseSubsetType X (A : Set X)))
    (collapsedZeroCell : cw.cell 0)
    {π : Type u} [AddCommGroup π]
    (κ :
      Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1) →
        π) :
    (quotientRelativeCochainComplex A cw quotientData collapsedZeroCell π).X (n + 1) := by
  change
    ModuleCat.of ℤ
        (@cellularChainGroup (collapseSubsetType X (A : Set X)) _ cw (n + 1)) ⟶
      ModuleCat.of ℤ π
  let φ :
      FreeAbelianGroup (@cellularCell (collapseSubsetType X (A : Set X)) _ cw (n + 1)) →+
        π :=
    FreeAbelianGroup.lift fun j ↦ κ (quotientRelativeCellEquiv A cw hcw n j)
  exact ModuleCat.ofHom φ.toIntLinearMap

private noncomputable def quotientToRelativeCohomologyMap
    (n : ℕ) (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
    (quotientData : CellularDifferentialFamily (collapseSubsetType X (A : Set X)))
    (collapsedZeroCell : cw.cell 0)
    (π : Type u) [AddCommGroup π]
    (e :
      relativeCellularChainComplex X A data ≅
        quotientRelativeChainComplex A cw quotientData collapsedZeroCell) :
    (quotientRelativeCochainComplex A cw quotientData collapsedZeroCell π).homology
        (n + 1) ⟶
      Hˢᶜ[n + 1](X, A, data; π) := by
  simpa [quotientRelativeChainComplex, quotientRelativeCochainComplex,
    relativeCellularCohomology_apply] using
    (homologyMap (ChainComplex.linearYonedaMap e.hom π) (n + 1))

/-- A cohomology class `c_f` is an obstruction class for extending `f : X^n ⟶ Y` over
`X^(n + 1)` when, after choosing a quotient CW model whose positive-degree cells are the relative
cells of `(X, A)`, the canonical obstruction cochain from Construction 18.5.2 is rewritten
through the public sphere-fiber-to-based-sphere-class bridge together with a chosen comparison
`comparison : HurewiczComparison n (underTopOfPoint Y y₀)` to give the coefficient cochain
`relativeSkeletonObstructionAdditiveCochain A n y₀ comparison f`. The resulting quotient-side
cocycle carries the class `c_f`, and the vanishing of `c_f` is equivalent to the existence of an
extension across the canonical inclusion `X^n ↪ X^(n + 1)`. -/
def IsRelativeSkeletonExtensionObstructionClass
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀))
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f : C(relativePairSkeleton A n, Y))
    (c_f : Hˢᶜ[n + 1](X, A, data; Additive (π_ n Y y₀))) : Prop :=
  ∃ (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
      (hcw : Topology.RelCWComplex.IsQuotientCWComplex (A : Set X) cw)
      (quotientData : CellularDifferentialFamily (collapseSubsetType X (A : Set X)))
      (collapsedZeroCell : cw.cell 0)
      (e :
        relativeCellularChainComplex X A data ≅
          quotientRelativeChainComplex A cw quotientData collapsedZeroCell),
      let Q :=
        quotientRelativeCochainComplex A cw quotientData collapsedZeroCell
          (Additive (π_ n Y y₀))
      ∃ z : Q.cycles (n + 1),
        (Q.iCycles (n + 1)) z =
            quotientRelativeObstructionCochain A n cw hcw quotientData
              collapsedZeroCell
                (relativeSkeletonObstructionAdditiveCochain A n y₀ comparison f) ∧
          quotientToRelativeCohomologyMap A n data cw quotientData collapsedZeroCell
              (Additive (π_ n Y y₀)) e ((Q.homologyπ (n + 1)) z) = c_f ∧
          (c_f = 0 ↔ extendsOverRelativeSkeleton A n f)

/-- Unfolding
`IsRelativeSkeletonExtensionObstructionClass A n y₀ comparison data f c_f`
identifies it with the existence of a quotient-cell cocycle representing the canonical
Construction 18.5.2 obstruction cochain and carrying the chosen class `c_f`, together with the
vanishing criterion for `c_f`. -/
theorem isRelativeSkeletonExtensionObstructionClass_iff
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀))
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f : C(relativePairSkeleton A n, Y))
    (c_f : Hˢᶜ[n + 1](X, A, data; Additive (π_ n Y y₀))) :
    IsRelativeSkeletonExtensionObstructionClass A n y₀ comparison data f c_f ↔
      ∃ (cw : CWComplex (Set.univ : Set (collapseSubsetType X (A : Set X))))
        (hcw : Topology.RelCWComplex.IsQuotientCWComplex (A : Set X) cw)
        (quotientData : CellularDifferentialFamily (collapseSubsetType X (A : Set X)))
        (collapsedZeroCell : cw.cell 0)
        (e :
          relativeCellularChainComplex X A data ≅
            quotientRelativeChainComplex A cw quotientData collapsedZeroCell),
        let Q :=
          quotientRelativeCochainComplex A cw quotientData collapsedZeroCell
            (Additive (π_ n Y y₀))
        ∃ z : Q.cycles (n + 1),
          (Q.iCycles (n + 1)) z =
              quotientRelativeObstructionCochain A n cw hcw quotientData
                collapsedZeroCell
                  (relativeSkeletonObstructionAdditiveCochain A n y₀ comparison f) ∧
            quotientToRelativeCohomologyMap A n data cw quotientData collapsedZeroCell
                (Additive (π_ n Y y₀)) e ((Q.homologyπ (n + 1)) z) = c_f ∧
            (c_f = 0 ↔ extendsOverRelativeSkeleton A n f) :=
  Iff.rfl

/-- Any obstruction class in the sense of
`IsRelativeSkeletonExtensionObstructionClass A n y₀ comparison data f c_f`
vanishes exactly when `f` extends over the next relative skeleton. -/
theorem isRelativeSkeletonExtensionObstructionClass_vanishing_iff
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀))
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f : C(relativePairSkeleton A n, Y))
    {c_f : Hˢᶜ[n + 1](X, A, data; Additive (π_ n Y y₀))}
    (hc_f : IsRelativeSkeletonExtensionObstructionClass A n y₀ comparison data f c_f) :
    c_f = 0 ↔ extendsOverRelativeSkeleton A n f := by
  rcases hc_f with ⟨_, _, _, _, _, _, _, _, hvanish⟩
  exact hvanish

/-- Theorem 18.5.3. For the canonical obstruction cochain
`relativeSkeletonObstructionCochain A n y₀ f` from Construction 18.5.2, there exists an
obstruction class in `Hˢᶜ[n + 1](X, A, data; Additive (π_ n Y y₀))` represented by the canonical
coefficient cochain obtained from a chosen comparison
`comparison : HurewiczComparison n (underTopOfPoint Y y₀)`, and its vanishing is equivalent to
extending `f` over `X^(n + 1)` along the canonical inclusion `X^n ↪ X^(n + 1)`. The source
writes an explicit `1 ≤ n` hypothesis, but in Lean that condition is absorbed by the ambient
coefficient-group assumption `[CommGroup (π_ n Y y₀)]`. -/
theorem relativeSkeletonExtensionObstructionCriterion
    (n : ℕ) [PathConnectedSpace Y] (y₀ : Y)
    (comparison : HurewiczComparison n (underTopOfPoint Y y₀))
    [CommGroup (π_ n Y y₀)] (data : CellularDifferentialFamily X)
    [RelativeCellularDifferentialDescends X A data]
    (f : C(relativePairSkeleton A n, Y)) :
    ∃ c_f : Hˢᶜ[n + 1](X, A, data; Additive (π_ n Y y₀)),
      IsRelativeSkeletonExtensionObstructionClass A n y₀ comparison data f c_f := sorry

end
