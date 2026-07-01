import Mathlib
import stacks_project.Chap12.Definition_12_24_9
import stacks_project.Chap13.Lemma_13_13_8
import stacks_project.Chap15.Definition_15_61_1
import stacks_project.Chap15.Lemma_15_60_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (A : Type u) [CommRing A] {B : Type u} [CommRing B]
variable [Algebra A B]

section

variable {A' : Type u} [CommRing A'] [Algebra A A']

local notation "ModB" => ModuleCat B
local notation "ModA'" => ModuleCat A'
local notation "BTensorAprime" => TensorProduct A B A'
local notation "ModBTensorAprime" => ModuleCat BTensorAprime
local notation "singleB" => DerivedCategory.singleFunctor ModB (0 : ℤ)
local notation "HAprime" => DerivedCategory.homologyFunctor ModA'
variable [LocallySmall.{0} (ModuleCat (TensorProduct A B A'))]
variable [WellPowered.{0} (ModuleCat (TensorProduct A B A'))]
variable [CategoryTheory.Limits.HasWidePullbacks (ModuleCat (TensorProduct A B A'))]
variable [CategoryTheory.Limits.HasCoproducts (ModuleCat (TensorProduct A B A'))]
variable [CategoryTheory.Limits.InitialMonoClass (ModuleCat (TensorProduct A B A'))]

/- 
Domain-style sampling for Example `15.62.3`.
- primary domain: cohomological spectral sequences in `ModuleCat B'` encoding the Tor
  base-change spectral sequence with its natural post-base-change module structure;
- sampled owner/canonical declarations in the same domain:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.Tor`;
- best owner abstraction: for the tensor-product ring `B' = B ⊗[A] A'`, a cohomological spectral
  sequence `E : CohomologicalSpectralSequence (ModuleCat (TensorProduct A B A')) 0` together with
  the chapter owner predicate `F.convergesToCohomology E` for an associated filtered complex
  `F : FilteredComplex (ModuleCat (TensorProduct A B A'))`;
- primitive data: the spectral sequence `E` and the filtered-complex witness `F` in the
  convergence clause;
- derived API: the textbook `A'`-module `E₂`-page objects
  `Tor_i^A(Tor_j^B(M, N), A')` and the base-changed Tor abutment in `ModuleCat B'`;
- source/core/bridge triage:
  `source-facing`: `ConvergesToTorBaseChange`, `IsTorBaseChangeSpectralSequence`, and the
    textbook page-two projection `IsTorBaseChangeSpectralSequence.pageTwoOverAprimeIso`;
  `core/canonical`: `CohomologicalSpectralSequence`, `IsAssociatedToFilteredComplex`,
    `FilteredComplex.convergesToCohomology`, `DerivedCategory.homologyFunctor`, `Tor`, 
    `derivedTensorWithAlgebra`, and `ModuleCat.extendScalars`;
  `bridge/view`: the restriction-of-scalars view along `A' → B'` used to place the page-two term
    of a spectral sequence in `ModuleCat B'` directly in the textbook `A'`-module form, together
    with the internal convergence clause below.
-/

/-- The textbook page-two term `Tor_i^A(Tor_j^B(M, N), A')`, viewed in `ModuleCat A'`. -/
private abbrev torBaseChangePageTwo
    (M N : ModB) (i j : ℕ) : ModA' :=
  (HAprime (-(i : ℤ))).obj
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        ((singleB).obj (((Tor ModB j).obj M).obj N))) ⊗[A]^L[A'])

/-- The abutment object `Tor_n^{B'}(M', N')` with its canonical `B'`-module structure. -/
private abbrev torBaseChangeAbutment
    (M N : ModB) (n : ℕ) : ModBTensorAprime :=
  (((Tor ModBTensorAprime n).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] BTensorAprime)).obj M)).obj
    ((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] BTensorAprime)).obj N))

/-- A cohomological spectral sequence converges to the change-of-rings Tor groups if it is
associated to a filtered complex whose cohomology objects are isomorphic in `ModuleCat B'` to
`Tor_*^{B'}(M', N')` and which satisfies the Chapter `12` convergence package. -/
def ConvergesToTorBaseChange
    (E : CohomologicalSpectralSequence ModBTensorAprime 0)
    (M N : ModB) : Prop :=
  ∃ (F : FilteredComplex ModBTensorAprime) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℕ,
        Nonempty (F.underlying.homology (-(n : ℤ)) ≅ torBaseChangeAbutment A M N n)

/-- The change-of-rings spectral sequence for Tor over `ModuleCat B'`: after restricting scalars
along `A' → B ⊗[A] A'`, its `E₂`-page is the textbook `A'`-module term
`Tor_i^A(Tor_j^B(M, N), A')`; its abutment is `Tor_{i + j}^{B'}(M', N')` with its natural
`B'`-module structure. -/
def IsTorBaseChangeSpectralSequence
    (E : CohomologicalSpectralSequence ModBTensorAprime 0)
    (M N : ModB) : Prop :=
  (∀ i j : ℕ,
      Nonempty
        ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
            ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅ torBaseChangePageTwo A M N i j)) ∧
    ConvergesToTorBaseChange A E M N

/-- The source-facing `E₂`-page identification in Example `15.62.3`: after restricting scalars
along `A' → B ⊗[A] A'`, the page-two term is `Tor_i^A(Tor_j^B(M, N), A')`. -/
theorem IsTorBaseChangeSpectralSequence.pageTwoOverAprimeIso
    {E : CohomologicalSpectralSequence ModBTensorAprime 0}
    {M N : ModB}
    (hE : IsTorBaseChangeSpectralSequence A E M N)
    (i j : ℕ) :
    Nonempty
      ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
          ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅
        torBaseChangePageTwo A M N i j) := by
  exact hE.1 i j

/-- The abutment half of Example `15.62.3`: a Tor base-change spectral sequence converges to
`Tor_*^{B ⊗[A] A'}(M', N')` through an associated filtered complex satisfying the Chapter `12`
convergence owner. -/
theorem IsTorBaseChangeSpectralSequence.convergesToTorBaseChange
    {E : CohomologicalSpectralSequence ModBTensorAprime 0}
    {M N : ModB}
    (hE : IsTorBaseChangeSpectralSequence A E M N) :
    ConvergesToTorBaseChange A E M N := by
  exact hE.2

-- Proof sketch: choose a free `B`-resolution `F_• → M`; because `B` is flat over `A` and `M` is
-- `A`-flat, the terms of `F_•` are `A`-flat. Tensor with `N`, then apply derived scalar extension
-- from `B` to `B' = B ⊗[A] A'`. The resulting filtered complex lives in `ModuleCat B'`; after
-- restricting the `E₂` page along `A' → B'`, its page-two terms identify with
-- `Tor_i^A(Tor_j^B(M, N), A')`, and its abutment is `Tor_{i+j}^{B'}(M', N')`.
/-- Example 15.62.3: let `A → B` and `A → A'` be ring maps, set `B' = B ⊗[A] A'`, and let `M`
and `N` be `B`-modules. If `B` is flat over `A` and `M` and `N` are flat over `A`, then there is
a spectral sequence with `E₂`-page `Tor_i^A(Tor_j^B(M, N), A')` converging to
`Tor_{i+j}^{B'}(M', N')`. In this file the source-facing `E₂`-page formula is stated directly as
an `A'`-module identification by restricting scalars on the spectral-sequence terms, while the
abutment keeps its natural `B'`-module structure. -/
theorem exists_tor_baseChange_spectralSequence
    (A' : Type u) [CommRing A'] [Algebra A A']
    [LocallySmall.{0} (ModuleCat (TensorProduct A B A'))]
    [WellPowered.{0} (ModuleCat (TensorProduct A B A'))]
    [CategoryTheory.Limits.HasWidePullbacks (ModuleCat (TensorProduct A B A'))]
    [CategoryTheory.Limits.HasCoproducts (ModuleCat (TensorProduct A B A'))]
    [CategoryTheory.Limits.InitialMonoClass (ModuleCat (TensorProduct A B A'))]
    (M N : ModB)
    (hBflat : Module.Flat A B)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (hNflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj N)) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat (TensorProduct A B A')) 0,
      IsTorBaseChangeSpectralSequence A E M N := sorry

end

end
