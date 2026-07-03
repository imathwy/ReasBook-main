import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap13.Lemma_13_13_8
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open FilteredCochainComplex
open FilteredComplex

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]
variable [LocallySmall (ModuleCat A)] [WellPowered (ModuleCat A)]
variable [HasWidePullbacks (ModuleCat A)] [HasCoproducts (ModuleCat A)]
variable [InitialMonoClass (ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)

/- Domain-style sampling:
- primary domain: cohomological spectral sequences associated to filtered complexes in
  `ModuleCat A`, together with the Chapter `15` derived-completion functor on `D(A)`;
- sampled owner/canonical declarations in this domain:
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.pageOneIso`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  the notations `gr^{p} K` and `K^∧[I, hI]`,
  and `FilteredComplex.HasFiniteFiltrations`;
- best owner abstraction: a cohomological spectral sequence `E` associated to a filtered complex
  `F`, expressed through the Chapter `12` owner `IsAssociatedToFilteredComplex F E`, with the
  derived-completion page-one and abutment identifications kept as source-facing companions;
- primitive data: the spectral sequence `E`, the filtered complex `F`, and the association witness
  `IsAssociatedToFilteredComplex F E`;
- derived API: the page-one comparison, pagewise derived-completeness, and the boundedness and
  convergence consequences under finite filtrations.

Layer triage:
- `source-facing`: the theorem below asserting existence of the derived-completion spectral
  sequence with its displayed `E₁`-page and abutment;
- `core/canonical`: `CohomologicalSpectralSequence`, `IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`, and `DerivedCategory.derivedCompletionOf`;
- `bridge/view`: the chosen filtered-complex model `F` whose associated spectral sequence realizes
  the source statement. -/

-- Proof sketch: choose a bounded complex of projective `A`-modules representing the object `C`
-- from Lemma `15.92.10`, form the filtered Hom-complex `Hom^•(P^•, K^•)`, and take its
-- associated spectral sequence from Chapter `12.24`. The graded pieces compute the derived
-- completions of `gr^p(K^•)`, every page is derived complete, and finite filtrations on the terms
-- of `K` make the resulting spectral sequence bounded and convergent by Lemma `12.24.11`.
/-- Lemma 15.92.22: if `I ⊆ A` is a finitely generated ideal and `K^•` is a filtered cochain
complex of `A`-modules, then there exists a canonical cohomological spectral sequence of bigraded
derived-complete `A`-modules whose `E_1^{p,q}`-term is
`H^{p + q}((gr^p(K^•))^∧)`. If each `K^n` has a finite filtration, then the package also records
that the spectral sequence is bounded and converges to `H^*((K^•)^∧)`. -/
theorem exists_derivedCompletion_associatedSpectralSequence
    (I : Ideal A) (hI : I.FG) (K : FilteredCochainComplex (ModuleCat A)) :
    ∃ (E : CohomologicalSpectralSequence (ModuleCat A) 0)
      (F : FilteredComplex (ModuleCat A))
      (_ : IsAssociatedToFilteredComplex F E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅
          (H (p + q)).obj
            (((Q).obj (gr^{p} K))^∧[I, hI]))
      (targetIso : ∀ n : ℤ,
        F.underlying.homology n ≅
          (H n).obj
            (((Q).obj K.underlying)^∧[I, hI])),
      (∀ r : ℕ, 1 ≤ r → ∀ p q : ℤ,
        ((E.page r).X (p, q)).IsDerivedCompleteWithRespectTo I) ∧
        (K.HasFiniteFiltrations →
          CohomologicalSpectralSequence.IsBounded E ∧ F.convergesToCohomology E) := by
  sorry

end
