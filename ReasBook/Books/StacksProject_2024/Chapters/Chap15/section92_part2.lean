import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_92_19 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open scoped DerivedTensorProduct KoszulComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling:
- primary domain: derived-complete objects in `D(A)`, tested against the canonical quotient object
  `(A / I)[0]` and the first powered Koszul stage `K_1^•` in the derived category;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.singleFunctor`,
  `CategoryTheory.derivedTensorProduct`,
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- best owner abstraction: the source-facing owner is still the derived-completeness predicate
  `K.IsDerivedCompleteWithRespectTo I`, while the positivity conditions are expressed by the
  canonical t-structure owner `DerivedCategory.IsLE 0` on the relevant derived tensor products
  with the degree-zero quotient object and the stage-`0` Koszul-power object from Situation
  `15.92.15`;
- primitive data: the generator family `f : Fin r → A`, the derived object `K`, and the owner
  hypothesis of derived completeness with respect to `Ideal.span (Set.range f)`;
- derived API: the degree-zero embedding `single₀`, the powered Koszul tower owner
  `derivedCompletionKoszulPowersDerivedInverseSystem`, and the derived tensor notation
  `K ⊗[A]^L L`, so the theorem should not expose raw functor-application or
  extension-localization internals.

Source/core/bridge triage:
- `source-facing`: the TFAE criterion for nonpositive cohomology under derived completeness;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I`, `DerivedCategory.IsLE 0`,
  `DerivedCategory.singleFunctor`, `derivedTensorProduct`, and
  `derivedCompletionKoszulPowersDerivedInverseSystem`;
- `bridge/view`: the stage-`0` powered-Koszul object realizing the textbook first Koszul complex
  `K_1^•`. -/

-- Proof sketch: `(1) → (2)` is exactness of derived tensor with the degree-zero quotient object.
-- `(2) → (3)` is the tensor-with-Koszul implication from Lemma `15.89.7`, using that the first
-- powered Koszul stage computes a bounded `I`-power-torsion object with zeroth homology `A / I`.
-- For `(3) → (1)`, descend on the Koszul length as in the textbook proof, using the
-- distinguished triangles for successive partial Koszul complexes together with derived
-- completeness and Lemmas `15.92.6` and `15.92.7` to force the positive cohomology groups to
-- vanish.
/-- Lemma 15.92.19: let `I = (f₁, \ldots, fᵣ)` and let `K` be derived complete with respect to
`I`. Then the following are equivalent: `K` has no positive cohomology; the derived tensor product
`K \otimes_A^{\mathbf L} (A / I)[0]` has no positive cohomology; and the derived tensor product
with the first Koszul complex `K_1^•` from Situation `15.92.15`, represented by the stage `0`
object of the powered Koszul inverse system, has no positive cohomology. -/
theorem derivedComplete_isLE_zero_tfae_of_span_range
    (f : Fin r → A) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    List.TFAE [
      K.IsLE 0,
      (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))).IsLE 0,
      (K ⊗[A]^L (derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op 0)).IsLE 0
    ] := sorry

end

end CategoryTheory

/-! ### Lemma_15_92_20 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.92.20:
- primary domain: vanishing criteria for derived-complete objects of `D(A)` with respect to a
  finitely generated ideal, expressed through the canonical derived tensor product with the quotient
  object `(A ⧸ I)[0]`;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `CategoryTheory.derivedTensorProduct`,
  `DerivedTensorProduct` notation `K ⊗[A]^L L`,
  `derivedTensorProduct_isZero_of_modIdealPow_of_modIdeal_isZero`,
  `derivedLimitOfKoszulPowerTensorFunctorAdjunction`;
- best owner abstraction: the source-facing owner remains the predicate
  `K.IsDerivedCompleteWithRespectTo I`; the quotient tensor object `K ⊗[A]^L (A ⧸ I)[0]` is
  derived API and should use the chapter's canonical tensor notation rather than raw functor
  application;
- primitive data: the ideal `I`, finite generation `hI`, the derived object `K`, derived
  completeness of `K` with respect to `I`, and vanishing of the quotient tensor;
- derived API: the powered-Koszul tower comparison and its adjunction consequences, which belong in
  the proof route rather than in this theorem's public surface.

Source/core/bridge triage:
- `source-facing`: the vanishing criterion below for a derived-complete object annihilated modulo
  `I`;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I` and the derived tensor owner
  `K ⊗[A]^L L`;
- `bridge/view`: finite-generator presentations of `I` and the powered-Koszul comparison machinery
  from Lemmas `15.89.8` and `15.92.18`. -/

-- Proof sketch: choose generators of the finitely generated ideal `I`, apply Lemma `15.89.8` to
-- deduce that tensoring `K` with each powered Koszul stage is zero from the vanishing modulo `I`,
-- and then use the derived-complete comparison from Lemma `15.92.18` to identify `K` with the
-- derived limit of that zero inverse system.
/-- Lemma 15.92.20: let `I` be a finitely generated ideal of a commutative ring `A`, and let
`K ∈ D(A)` be derived complete with respect to `I`. If
`K \otimes_A^{\mathbf L} (A ⧸ I)[0]` is the zero object, then `K` is the zero object. -/
theorem isZero_of_isDerivedCompleteWithRespectTo_of_derivedTensorProduct_modIdeal_isZero
    (I : Ideal A) (hI : I.FG) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (hKI : IsZero (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I)))) :
    IsZero K := sorry

end

end CategoryTheory

/-! ### Lemma_15_92_21 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Ideal

section

variable {A : Type u} [CommRing A] {r : ℕ}

/-- If an ideal of `A` is generated by `r` elements, then it is finitely generated. -/
theorem fg_of_exists_fin_generators
    (I : Ideal A) (hgen : ∃ f : Fin r → A, Ideal.span (Set.range f) = I) :
    I.FG := by
  rcases hgen with ⟨f, rfl⟩
  simpa using (Submodule.fg_span (Set.finite_range f) : (Ideal.span (Set.range f)).FG)

end

end Ideal

namespace DerivedCategory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.21:
- primary domain: cohomological amplitude bounds for the canonical derived-completion endofunctor
  on `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletion`,
  `DerivedCategory.derivedCompletionOf`,
  `CategoryTheory.derivedLimitOfKoszulPowerTensorFunctorAdjunction`,
  `Ideal.fg_of_exists_fin_generators`;
- best owner abstraction: the public map on completions should be stated directly using the chapter
  owner `DerivedCategory.derivedCompletion`; the generator witness
  `∃ f : Fin r → A, Ideal.span (Set.range f) = I` is bridge data used only to supply the
  finitely-generated ideal hypothesis required by that owner in part `(1)`, while in part `(2)`
  the same witness remains source-facing because the cohomological bound depends on `r`;
- primitive data: the ideal `I`, the canonical finite-generation datum `hI : I.FG` for part
  `(1)`, a family of `r` generators for `I` for part `(2)`, a morphism `φ : K ⟶ L`, and the
  source cohomology hypotheses on `φ`;
- derived API: the induced morphism
  `(derivedCompletion I hI).map φ` on derived completions.

Source/core/bridge triage:
- `source-facing`: the high-degree amplitude statement for finitely generated `I` in part `(1)`,
  and the low-degree amplitude statement under an `r`-generator hypothesis in part `(2)`;
- `core/canonical`: `DerivedCategory.derivedCompletion` and `Ideal.FG`;
- `bridge/view`: the chosen finite generating family for `I`, used only to build the proof
  `I.FG` in part `(1)` and to record the generator-count bound in part `(2)`. -/

-- Proof sketch: pass to the cone of `φ`, whose cohomology vanishes in degrees `≥ 0` under the
-- hypotheses. Express derived completion by the powered Koszul tower from Lemma `15.92.18`, apply
-- the Milnor short exact sequence from Lemma `15.88.4`, choose a finite generating family for
-- `I`, and use that a Koszul complex on finitely many generators lives in nonpositive degrees to
-- preserve vanishing in degrees `≥ 0`.
/-- Lemma 15.92.21 (1): if `I ⊆ A` is finitely generated and `φ : K ⟶ L` induces
isomorphisms on cohomology in degrees `i ≥ 1` and an epimorphism in degree `0`, then the induced
morphism on derived `I`-adic completions has the same property. -/
theorem derivedCompletion_map_isIso_ge_one_and_epi_zero
    (I : Ideal A) (hI : I.FG)
    {K L : DMod} (φ : K ⟶ L)
    (hφ_iso :
      ∀ i : ℤ, 1 ≤ i → IsIso ((H i).map φ))
    (hφ_epi : Epi ((H 0).map φ)) :
    (∀ i : ℤ, 1 ≤ i →
      IsIso ((H i).map ((derivedCompletion I hI).map φ))) ∧
      Epi ((H 0).map ((derivedCompletion I hI).map φ)) :=
  sorry

-- Proof sketch: pass to the cone of `φ`, whose cohomology vanishes in degrees `< 0` under the
-- hypotheses. The powered Koszul complexes for an ideal generated by `r` elements are supported in
-- degrees `-r, ..., 0`, so the Milnor short exact sequence and the distinguished triangle for the
-- completed cone show vanishing in degrees `< -r`, which yields the stated low-degree
-- isomorphism and injectivity bounds for the completed morphism.
/-- Lemma 15.92.21 (2): if `I ⊆ A` is generated by `r` elements and `φ : K ⟶ L` induces
isomorphisms on cohomology in degrees `i ≤ -1` and a monomorphism in degree `0`, then the induced
morphism on derived `I`-adic completions induces isomorphisms in degrees `i ≤ -r - 1` and a
monomorphism in degree `-r`. -/
theorem derivedCompletion_map_isIso_le_neg_r_sub_one_and_mono_neg_r
    (I : Ideal A) (hgen : ∃ f : Fin r → A, Ideal.span (Set.range f) = I)
    {K L : DMod} (φ : K ⟶ L)
    (hφ_iso :
      ∀ i : ℤ, i ≤ -1 → IsIso ((H i).map φ))
    (hφ_mono : Mono ((H 0).map φ)) :
    (∀ i : ℤ, i ≤ -((r : ℤ) + 1) →
      IsIso ((H i).map ((derivedCompletion I (Ideal.fg_of_exists_fin_generators I hgen)).map φ))) ∧
      Mono
        ((H (-(r : ℤ))).map
          ((derivedCompletion I (Ideal.fg_of_exists_fin_generators I hgen)).map φ)) := sorry

end

end DerivedCategory

/-! ### Lemma_15_92_22 (from Chap15) -/
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

/-! ### Example_15_92_23 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]
variable [LocallySmall.{0} (ModuleCat A)] [WellPowered.{0} (ModuleCat A)]
variable [HasWidePullbacks (ModuleCat A)] [HasCoproducts (ModuleCat A)]
variable [InitialMonoClass (ModuleCat A)]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Example `15.92.23`.
- primary domain: cohomological spectral sequences in `ModuleCat A` computing the cohomology of
  the derived completion of an object of `D(A)`;
- sampled owner/canonical declarations in this domain:
  `CohomologicalSpectralSequence`,
  `CohomologicalSpectralSequence.IsBounded`,
  `FilteredComplex.convergesToCohomology`,
  `DerivedCategory.derivedCompletionOf`;
- best owner abstraction: the cohomological spectral sequence
  `E : CohomologicalSpectralSequence (ModuleCat A) 0`, with the Chapter `12` convergence owner
  `F.convergesToCohomology E` on an associated filtered complex `F`;
- primitive data: only `E` and the auxiliary filtered-complex witness `F` occurring in the
  convergence clause;
- derived API: the `E₂`-page identification, pagewise derived-completeness, and the abutment
  identification with `H^*(K^∧)`;
- source/core/bridge triage:
  `source-facing`: `ConvergesToDerivedCompletionCohomology` and
    `IsDerivedCompletionCohomologySpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`,
    `CohomologicalSpectralSequence.IsBounded`,
    `FilteredComplex.convergesToCohomology`, and `DerivedCategory.derivedCompletionOf`;
  `bridge/view`: the auxiliary filtered complex in the convergence clause together with the
    internal page-two and abutment abbreviations. -/

/-- The `E₂`-term `H^i((H^j(K)[0])^∧)` of Example `15.92.23`. -/
private abbrev derivedCompletionCohomologyPageTwo
    (I : Ideal A) (hI : I.FG) (K : DMod) (i j : ℤ) : ModuleCat A :=
  (H i).obj (((single₀).obj ((H j).obj K))^∧[I, hI])

/-- The abutment term `H^n(K^∧)` of Example `15.92.23`. -/
private abbrev derivedCompletionCohomologyAbutment
    (I : Ideal A) (hI : I.FG) (K : DMod) (n : ℤ) : ModuleCat A :=
  (H n).obj (K^∧[I, hI])

/-- A cohomological spectral sequence converges to the derived-completion cohomology of `K` if it
is associated to a filtered complex whose cohomology identifies with `H^*(K^∧)` and which
satisfies the Chapter `12` convergence owner. -/
def ConvergesToDerivedCompletionCohomology
    (E : CohomologicalSpectralSequence (ModuleCat A) 0)
    (I : Ideal A) (hI : I.FG) (K : DMod) : Prop :=
  ∃ (F : FilteredComplex (ModuleCat A)) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology n ≅ derivedCompletionCohomologyAbutment I hI K n)

/-- A cohomological spectral sequence over `ModuleCat A` is a derived-completion cohomology
spectral sequence for `K ∈ D(A)` if it is bounded, every page `E_r` for `r ≥ 2` consists of
modules that are derived complete with respect to `I`, its `E₂`-page is
`H^i((H^j(K)[0])^∧)`, and it converges to `H^{i + j}(K^∧)`. -/
def IsDerivedCompletionCohomologySpectralSequence
    (E : CohomologicalSpectralSequence (ModuleCat A) 0)
    (I : Ideal A) (hI : I.FG) (K : DMod) : Prop :=
  CohomologicalSpectralSequence.IsBounded E ∧
    (∀ i j : ℤ,
      Nonempty ((E.page 2).X (i, j) ≅ derivedCompletionCohomologyPageTwo I hI K i j)) ∧
    (∀ r : ℕ, 2 ≤ r → ∀ i j : ℤ,
      ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I) ∧
    ConvergesToDerivedCompletionCohomology E I hI K

/-- A derived-completion cohomology spectral sequence is bounded. -/
theorem IsDerivedCompletionCohomologySpectralSequence.isBounded
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K) :
    CohomologicalSpectralSequence.IsBounded E :=
  hE.1

/-- The second page of a derived-completion cohomology spectral sequence computes the cohomology
of the derived completions of the cohomology modules of `K`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.pageTwoIso
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K)
    (i j : ℤ) :
    Nonempty ((E.page 2).X (i, j) ≅ (H i).obj (((single₀).obj ((H j).obj K))^∧[I, hI])) :=
  hE.2.1 i j

/-- Every page from `E₂` onward of a derived-completion cohomology spectral sequence consists of
modules that are derived complete with respect to `I`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.page_isDerivedComplete
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K)
    (r : ℕ) (hr : 2 ≤ r) (i j : ℤ) :
    ((E.page r).X (i, j)).IsDerivedCompleteWithRespectTo I :=
  hE.2.2.1 r hr i j

/-- A derived-completion cohomology spectral sequence converges to the cohomology of the derived
completion of `K`. -/
theorem IsDerivedCompletionCohomologySpectralSequence.converges
    {E : CohomologicalSpectralSequence (ModuleCat A) 0}
    {I : Ideal A} {hI : I.FG} {K : DMod}
    (hE : IsDerivedCompletionCohomologySpectralSequence E I hI K) :
    ConvergesToDerivedCompletionCohomology E I hI K :=
  hE.2.2.2

-- Proof sketch: apply Lemma `15.92.22` to the filtration `F^p K = τ_{≤ -p} K`, identify the
-- graded piece `gr^p(K)` with `H^{-p}(K)[p]`, and then renumber by `p = -j` and `q = i + 2j`.
-- The boundedness, derived-completeness of the pages, and convergence to `H^*(K^∧)` are inherited
-- from Lemma `15.92.22` after this reindexing.
/-- Example 15.92.23: for a finitely generated ideal `I ⊆ A` and any object `K ∈ D(A)`, there
is a bounded cohomological spectral sequence of bigraded derived-complete `A`-modules whose
`E_2^{i,j}`-term is `H^i(H^j(K)^∧)` and which converges to `H^{i + j}(K^∧)`. The differentials
are those of a cohomological spectral sequence, so they have bidegree `(r, -r + 1)`. -/
theorem exists_derivedCompletion_cohomology_spectralSequence
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat A) 0,
      IsDerivedCompletionCohomologySpectralSequence E I hI K := sorry

end

end DerivedCategory

/-! ### Lemma_15_92_24 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling:
- primary domain: derived completeness in derived module categories under restriction of scalars;
- sampled owner-side declarations:
  `CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition`,
  `CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingIdeal`,
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- best owner abstraction: the source-facing predicate
  `K.IsDerivedCompleteWithRespectTo I`, whose core/canonical owner is the ideal
  `K.localizationAwayDerivedHomVanishingIdeal`, together with the canonical derived
  restriction-of-scalars functor;
- primitive data: the object `L : D(B)`, the ideal `I : Ideal A`, and the algebra map `A → B`;
- derived API: this restriction/base-change equivalence for the source-facing completeness
  predicate.

Layer triage:
- `source-facing`: `isDerivedCompleteWithRespectTo_iff_restrictScalars`;
- `core/canonical`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `bridge/view`: restriction of scalars along `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`. -/

-- Proof sketch: by Definition `15.92.4`, derived completeness with respect to an ideal is the
-- vanishing of all morphisms from localization-derived categories `D(A_f)` or `D(B_g)` after
-- restriction of scalars. Using Lemma `15.92.2`, test membership in the relevant radical ideal by
-- the generators coming from `I`; the localization-away derived-Hom condition is computed in
-- abelian groups and is unchanged when `f ∈ A` is viewed in `B`, so the two vanishing conditions
-- are equivalent.
/-- Lemma 15.92.24: a derived `B`-complex lies in the inverse image of `D_{comp}(A, I)` under the
restriction functor `D(B) ⥤ D(A)` exactly when it is derived complete with respect to the
extended ideal `I B = I.map (algebraMap A B)`. -/
theorem isDerivedCompleteWithRespectTo_iff_restrictScalars
    (L : DModB) (I : Ideal A) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L).IsDerivedCompleteWithRespectTo I ↔
      L.IsDerivedCompleteWithRespectTo (I.map (algebraMap A B)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_92_25 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.ObjectProperty

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)

local notation "IB" => I.map (algebraMap A B)

/- Domain-style sampling:
- primary domain: derived-complete full subcategories in derived module categories under change of
  rings;
- sampled owner-side declarations:
  `DerivedCategory.derivedCompleteObjectProperty`,
  `ObjectProperty.lift`,
  `CategoryTheory.isDerivedCompleteWithRespectTo_iff_restrictScalars`,
  `CategoryTheory.derivedTensorWithAlgebraAdjunction`;
- best owner abstraction: the source-facing equivalence lives on the full subcategories cut out by
  `derivedCompleteObjectProperty`, and the comparison functor is the canonical
  `ObjectProperty.lift` of derived restriction of scalars;
- primitive data: the ideal `I`, the flat algebra map `A → B`, and the canonical derived
  restriction functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- derived API: the induced equivalence
  `D_comp(B, IB) ⥤ D_comp(A, I)`.

Layer triage:
- `source-facing`: the equivalence between the derived-complete full subcategories;
- `core/canonical`: `derivedCompleteObjectProperty` together with `ObjectProperty.lift`;
- `bridge/view`: `isDerivedCompleteWithRespectTo_iff_restrictScalars` and
  `derivedTensorWithAlgebraAdjunction`. -/

-- Proof sketch: Lemma `15.92.24` shows that restriction lands in the derived-complete full
-- subcategory. For essential surjectivity, use the Stacks construction
-- `K ↦ RHom_A(B, K)` from the source proof, realized through the derived change-of-rings
-- adjunction of Lemma `15.60.3`; the flatness and quotient-bijectivity hypotheses together with
-- Lemma `15.90.4` make the unit and counit become isomorphisms on the derived-complete
-- subcategories.
/-- Lemma 15.92.25: if `A → B` is flat, `I ⊆ A` is finitely generated, and the canonical quotient
map `A / I → B / I B` is bijective, then the restriction functor `D(B) ⥤ D(A)` induces an
equivalence from the full subcategory `D_{comp}(B, I B)` of `IB`-derived-complete complexes to the
full subcategory `D_{comp}(A, I)` of `I`-derived-complete complexes. -/
theorem derivedCompleteRestriction_isEquivalence_of_flat_of_quotientMap_bijective
    [Module.Flat A B] (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          IB
          (algebraMap A B)
          Ideal.le_comap_map)) :
    Functor.IsEquivalence
      ((derivedCompleteObjectProperty I).lift
        ((derivedCompleteObjectProperty IB).ι ⋙
          (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory)
        (fun L ↦ (isDerivedCompleteWithRespectTo_iff_restrictScalars L.obj I).2 L.property)) :=
  sorry

end

end CategoryTheory
