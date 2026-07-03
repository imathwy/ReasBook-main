import Mathlib
import StacksProject_2024.Chap20.Lemma_20_29_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.FilteredComplex
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})
variable [LocallySmall (RingedSpace.Modules X)] [WellPowered (RingedSpace.Modules X)]
  [HasWidePullbacks (RingedSpace.Modules X)] [HasCoproducts (RingedSpace.Modules X)]
  [InitialMonoClass (RingedSpace.Modules X)]
  [IsGrothendieckAbelian (RingedSpace.Modules X)]
  [LocallySmall (ModuleCat (globalSectionsRing X))]
  [WellPowered (ModuleCat (globalSectionsRing X))]
  [HasWidePullbacks (ModuleCat (globalSectionsRing X))]
  [HasCoproducts (ModuleCat (globalSectionsRing X))]
  [InitialMonoClass (ModuleCat (globalSectionsRing X))]

local instance : Abelian (RingedSpace.Modules X) :=
  SheafOfModules.instAbelian (RingedSpace.ringCatSheaf X)

local instance : HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

local instance :
    HasDerivedCategory (ModuleCat (globalSectionsRing X)) :=
  HasDerivedCategory.standard (ModuleCat (globalSectionsRing X))

local notation "ModΓX" => ModuleCat (globalSectionsRing X)

-- Proof sketch: choose a bounded-below filtered injective replacement with finite termwise
-- filtrations and injective graded pieces as in Derived Categories, Lemma `13.26.9`. Apply global
-- sections degreewise to that replacement and take the associated spectral sequence. Since
-- bounded-below complexes of injectives compute derived global sections, the `E₁`-page is
-- `H^{p+q}(X, gr^p(K^•))`, and the finite-filtration hypothesis gives the boundedness and
-- convergence package described in the remark. This is the hypercohomology specialization of the
-- filtered right-derived spectral sequence from Derived Categories, Lemma `13.26.14`.
/-- Remark 20.29.2: if a filtered complex `\mathcal F^\bullet` of `\mathcal O_X`-modules is
bounded below and each term has a finite filtration, then the filtered hypercohomology spectral
sequence of Lemma `20.29.1` can be constructed from a bounded-below filtered injective model of
`\mathcal F^\bullet`; equivalently, there is a filtered hypercohomology spectral sequence with
`E_1^{p,q} = H^{p+q}(X, gr^p(\mathcal F^\bullet))` under these hypotheses. -/
theorem exists_filteredHypercohomologySpectralSequence_of_boundedBelow_of_finiteFiltrations
    (K : CategoryTheory.FilteredComplex (RingedSpace.Modules X))
    (hKboundedBelow : ∃ a : ℤ, K.underlying.IsStrictlyGE a)
    (hKfin : ∀ n : ℤ, ∃ a b : ℤ,
      (K.X n).filtration.obj a = ⊤ ∧ (K.X n).filtration.obj b = ⊥) :
    ∃ (filteredComplex : CategoryTheory.FilteredComplex ModΓX)
      (spectralSequence : CohomologicalSpectralSequence ModΓX 0)
      (_ : IsAssociatedToFilteredComplex filteredComplex spectralSequence)
      (_ :
        ∀ p q : ℤ,
          (spectralSequence.page 1).X (p, q) ≅
            moduleHypercohomology X (K.gradedPiece p) (p + q))
      (_ :
        ∀ n : ℤ,
          filteredComplex.underlying.homology n ≅
            moduleHypercohomology X K.underlying n),
      CohomologicalSpectralSequence.IsBounded spectralSequence ∧
        FilteredComplex.abutsToCohomology filteredComplex := sorry

end AlgebraicGeometry.RingedSpace
