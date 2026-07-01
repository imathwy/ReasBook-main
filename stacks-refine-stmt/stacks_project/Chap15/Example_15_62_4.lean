import Mathlib
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap12.Definition_12_24_5
import stacks_project.Chap12.Lemma_12_24_11
import stacks_project.Chap12.Lemma_12_25_3
import stacks_project.Chap13.Situation_13_15_1
import stacks_project.Chap15.Definition_15_59_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped DerivedTensorProduct

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksProject

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat.{u} R)]
variable [WellPowered.{0} (ModuleCat.{u} R)]

/-
Domain-style sampling for Example `15.62.4`.
- primary domain: cohomological spectral sequences in the bounded-above derived category of
  `R`-modules and their convergence to derived tensor-product cohomology;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.firstDoubleComplexFilteredComplex`,
  `CategoryTheory.secondDoubleComplexFilteredComplex`,
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.DerivedCategory.homologyFunctor`;
- best owner abstraction: a cohomological spectral sequence `E` with source-facing Prop-valued
  predicates recording the right or left `E₂`-page formula together with the Chapter `12`
  convergence owner `F.convergesToCohomology E` for some associated filtered complex `F`;
- primitive data: `E : CohomologicalSpectralSequence ModR 0` and the existential filtered-complex
  witness `F : FilteredComplex ModR` occurring in the convergence clause;
- derived API: the right and left `E₂`-page identifications and the common abutment
  identification with `H^*(K ⊗[R]^L L)`;
- source/core/bridge triage:
  `source-facing`: `IsRightCohomologyDerivedTensorSpectralSequence` and
    `IsLeftCohomologyDerivedTensorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`, `FilteredComplex.convergesToCohomology`,
    `firstDoubleComplexFilteredComplex`, `secondDoubleComplexFilteredComplex`,
    `DerivedCategory.homologyFunctor`, and `derivedTensorProduct`;
  `bridge/view`: the local page-two and abutment abbreviations together with the shared internal
    convergence clause used to state the source-facing predicates concisely.
-/
local notation "ModR" => ModuleCat R
local notation "DModMinus" => boundedAboveDerivedCategory ModR
local notation "H" => DerivedCategory.homologyFunctor ModR
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)

/-- The abutment object `H^n(K^• \otimes_R^{\mathbf L} L^•)`. -/
private abbrev derivedTensorCohomologyAbutment
    (K L : DModMinus) (n : ℤ) : ModR :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The right-hand `E₂`-term `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`. -/
private abbrev rightDerivedTensorPageTwo
    (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (K.obj ⊗[R]^L ((single₀).obj ((H q).obj L.obj)))

/-- The left-hand `E₂`-term `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. -/
private abbrev leftDerivedTensorPageTwo
    (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (((single₀).obj ((H q).obj K.obj)) ⊗[R]^L L.obj)

/-- Internal bridge: a cohomological spectral sequence converges to
`H^*(K^• \otimes_R^{\mathbf L} L^•)` if it is associated to a filtered complex whose cohomology
identifies with that of the derived tensor product and which satisfies the Chapter `12`
convergence owner. -/
private def convergesToDerivedTensorCohomology
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  ∃ (F : FilteredComplex ModR) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedTensorCohomologyAbutment K L n)

/-- The first spectral sequence of Example `15.62.4`: its `E₂`-page is
`H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))`, and it converges to
`H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`. -/
def IsRightCohomologyDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ rightDerivedTensorPageTwo K L p q)) ∧
    convergesToDerivedTensorCohomology E K L

/-- The second spectral sequence of Example `15.62.4`: its `E₂`-page is
`H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`, and it converges to
`H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`. -/
def IsLeftCohomologyDerivedTensorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ,
      Nonempty ((E.page 2).X (p, q) ≅ leftDerivedTensorPageTwo K L p q)) ∧
    convergesToDerivedTensorCohomology E K L

-- Proof sketch: replace `K^•` and `L^•` by bounded-above complexes of projective `R`-modules and
-- apply the two spectral sequences of Homology, Section `12.25` to the double complex
-- `Tot(K^• ⊗_R L^•)`. The projective replacements compute the same derived tensor product, so the
-- two `E₂`-pages identify with `H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))` and
-- `H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)` respectively, and both abut to
-- `H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`.
/-- Example 15.62.4: for objects `K^•` and `L^•` of `D^{-}(R)`, there are two cohomological
spectral sequences converging to `H^{p+q}(K^• \otimes_R^{\mathbf L} L^•)`, one with
`E_2^{p,q} = H^p(K^• \otimes_R^{\mathbf L} H^q(L^•))` and the other with
`E_2^{p,q} = H^p(H^q(K^•) \otimes_R^{\mathbf L} L^•)`. Because both are cohomological spectral
sequences, their page-two differentials have bidegree `(2, -1)`, i.e.
`d_2^{p,q} : E_2^{p,q} → E_2^{p+2,q-1}`. -/
theorem exists_derivedTensor_cohomology_spectralSequences
    (K L : DModMinus) :
    ∃ E_right E_left : CohomologicalSpectralSequence ModR 0,
      IsRightCohomologyDerivedTensorSpectralSequence E_right K L ∧
        IsLeftCohomologyDerivedTensorSpectralSequence E_left K L := sorry

end

end StacksProject
