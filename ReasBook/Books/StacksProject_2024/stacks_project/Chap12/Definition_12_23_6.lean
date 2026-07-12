import Mathlib
import StacksProject_2024.Chap12.Lemma_12_23_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomologicalComplex.Filtered

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

section Abutment

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasCoproducts C]
  [InitialMonoClass C]

/-- Definition 12.23.6 (1): the spectral sequence associated to a filtered differential object
weakly converges to `H(K)` if the actual eventual-cycle and eventual-boundary equalities
`(12.23.5.2)` and `(12.23.5.1)` hold in every filtration degree. This is stronger than the
subquotient comparison of Lemma `12.23.5`, and it is the equality-based criterion used for weak
convergence in the later source definitions. -/
def weaklyConvergesToHomology : Prop :=
  ∀ p : ℤ,
    eventualBoundaryStep K p = homologyBoundaryStep K p ∧
      homologyCycleStep K p = eventualCycleStep K p

/-- The induced filtration on `H(K)` is separated and exhaustive. -/
def inducedHomologyFiltrationSeparatedExhaustive : Prop :=
  DecreasingFiltration.IsSeparated (inducedHomologyFiltration K) ∧
    DecreasingFiltration.IsExhaustive (inducedHomologyFiltration K)

/-- Definition 12.23.6 (2): the spectral sequence associated to a filtered differential object
abuts to `H(K)` if it weakly converges to `H(K)` and the induced filtration on `H(K)` is
separated and exhaustive. -/
def abutsToHomology : Prop :=
  weaklyConvergesToHomology K ∧ inducedHomologyFiltrationSeparatedExhaustive K

-- Proof sketch: unfold `weaklyConvergesToHomology`; this is exactly the pair of pagewise
-- equalities `(12.23.5.2)` and `(12.23.5.1)` that encode stabilization of the actual eventual
-- boundaries and cycles in the associated spectral sequence.
/-- Weak convergence is equivalent to the pagewise equalities `(12.23.5.2)` and `(12.23.5.1)` for
the underlying filtered differential object. -/
theorem weaklyConvergesToHomology_iff :
    weaklyConvergesToHomology K ↔
      ∀ p : ℤ,
        eventualBoundaryStep K p = homologyBoundaryStep K p ∧
          homologyCycleStep K p = eventualCycleStep K p :=
  Iff.rfl

-- Proof sketch: the owner predicates `DecreasingFiltration.IsSeparated` and
-- `DecreasingFiltration.IsExhaustive` are equivalent, under the available complete lattice
-- structure on subobjects, to saying that the infimum of the filtration is `⊥` and the supremum
-- is `⊤`.
/-- The induced filtration on `H(K)` is separated and exhaustive exactly when its intersection is
zero and its union is the whole homology object. -/
theorem inducedHomologyFiltrationSeparatedExhaustive_iff :
    inducedHomologyFiltrationSeparatedExhaustive K ↔
      (⨅ p : ℤ, (inducedHomologyFiltration K).obj p) = ⊥ ∧
        (⨆ p : ℤ, (inducedHomologyFiltration K).obj p) = ⊤ := by
  simp [inducedHomologyFiltrationSeparatedExhaustive,
    DecreasingFiltration.isSeparated_iff_iInf_eq_bot,
    DecreasingFiltration.isExhaustive_iff_iSup_eq_top]

-- Proof sketch: unfold `abutsToHomology`; abutment is weak convergence together with
-- separatedness and exhaustiveness of the induced filtration on `H(K)`.
/-- Abutment is weak convergence together with separatedness and exhaustiveness of the induced
homology filtration. -/
theorem abutsToHomology_iff :
    abutsToHomology K ↔
      weaklyConvergesToHomology K ∧ inducedHomologyFiltrationSeparatedExhaustive K :=
  Iff.rfl

end Abutment

end HomologicalComplex.Filtered

end CategoryTheory
