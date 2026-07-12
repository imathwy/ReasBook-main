import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap12.Definition_12_14_1
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Lemma_12_24_3
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap12.Lemma_12_25_3
import StacksProject_2024.Chap13.Lemma_13_13_8
import StacksProject_2024.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
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

local notation "ModA" => ModuleCat A
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

/-- Helper for Example 15.62.3: every `A`-module admits a projective resolution because module
categories over commutative rings have enough projectives coming from free modules. -/
private noncomputable instance moduleCat_hasProjectiveResolutions_of_free_resolutions :
    CategoryTheory.HasProjectiveResolutions (ModuleCat A) := by
  letI : CategoryTheory.EnoughProjectives (ModuleCat A) := inferInstance
  -- This is the standard module-category owner used to invoke Example `15.62.1` over `A`.
  infer_instance

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

/-- Helper for Example 15.62.3: once the page-two comparison and convergence witness have been
constructed, they package immediately into the source-facing predicate used in the theorem. -/
private theorem isTorBaseChangeSpectralSequence_of_data
    {E : CohomologicalSpectralSequence ModBTensorAprime 0}
    {M N : ModB}
    (hpage : ∀ i j : ℕ,
      Nonempty
        ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
            ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅
          torBaseChangePageTwo A M N i j))
    (hconv : ConvergesToTorBaseChange A E M N) :
    IsTorBaseChangeSpectralSequence A E M N := by
  -- The source-facing predicate is just the conjunction of the page-two identification and the
  -- abutment convergence package.
  exact ⟨hpage, hconv⟩

/-- Helper for Example 15.62.3: once the first filtered spectral sequence of a double complex is
chosen, finite antidiagonal support and a total-homology comparison package the abutment clause
of the Tor base-change spectral sequence. -/
private theorem convergesToTorBaseChange_of_firstDoubleComplex
    (K : HomologicalComplex₂ ModBTensorAprime (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModBTensorAprime 0)
    [hE : IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (M N : ModB)
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K)
    (habut : ∀ n : ℕ,
      Nonempty
        ((HomologicalComplex₂.total K (ComplexShape.up ℤ)).homology (-(n : ℤ)) ≅
          torBaseChangeAbutment A M N n)) :
    ConvergesToTorBaseChange A E M N := by
  refine ⟨firstDoubleComplexFilteredComplex K, hE, ?_, ?_⟩
  · -- Chapter `12` supplies convergence for the first filtered spectral sequence under finite
    -- antidiagonal support.
    exact firstDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport K E hfin
  · -- The underlying filtered complex of the first filtration is the total complex of `K`.
    simpa using habut

/-- Helper for Example 15.62.3: for a chosen first filtered spectral sequence of a double
complex, the theorem reduces to the explicit page-two and total-homology comparison isomorphisms.
-/
private theorem isTorBaseChangeSpectralSequence_of_firstDoubleComplex
    (K : HomologicalComplex₂ ModBTensorAprime (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (E : CohomologicalSpectralSequence ModBTensorAprime 0)
    [IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E]
    (M N : ModB)
    (hfin : doubleComplexHasFiniteAntidiagonalSupport K)
    (hpage : ∀ i j : ℕ,
      Nonempty
        ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
            ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅
          torBaseChangePageTwo A M N i j))
    (habut : ∀ n : ℕ,
      Nonempty
        ((HomologicalComplex₂.total K (ComplexShape.up ℤ)).homology (-(n : ℤ)) ≅
          torBaseChangeAbutment A M N n)) :
    IsTorBaseChangeSpectralSequence A E M N := by
  -- The main theorem only needs the page-two comparison and the abutment package for the chosen
  -- first-filtered spectral sequence.
  exact
    isTorBaseChangeSpectralSequence_of_data (A := A) (A' := A') hpage
      (convergesToTorBaseChange_of_firstDoubleComplex
        (A := A) (K := K) (E := E) (M := M) (N := N) hfin habut)

/-- Helper for Example 15.62.3: the chosen free `B`-resolution of `M`, extended by zero to a
cochain complex on `ℤ` supported in nonpositive degrees. -/
private abbrev tor_base_change_b_resolutionView
    (F : ChainComplex ModB ℕ) : CochainComplex ModB ℤ :=
  F.extend ComplexShape.embeddingDownNat

/-- Helper for Example 15.62.3: the chosen free `A`-resolution of `A'`, extended by zero to a
cochain complex on `ℤ` supported in nonpositive degrees. -/
private abbrev tor_base_change_aprime_resolutionView
    (P : ChainComplex ModA ℕ) : CochainComplex ModA ℤ :=
  P.extend ComplexShape.embeddingDownNat

/-- Helper for Example 15.62.3: the extended free `B`-resolution stays in nonpositive cochain
degrees. -/
private lemma tor_base_change_b_resolutionView_isStrictlyLE_zero
    (F : ChainComplex ModB ℕ) :
    (tor_base_change_b_resolutionView (B := B) F).IsStrictlyLE 0 := by
  -- The extension-by-zero owner carries the standard nonpositive support instance.
  infer_instance

/-- Helper for Example 15.62.3: the extended free `A`-resolution of `A'` stays in nonpositive
cochain degrees. -/
private lemma tor_base_change_aprime_resolutionView_isStrictlyLE_zero
    (P : ChainComplex ModA ℕ) :
    (tor_base_change_aprime_resolutionView (A := A) P).IsStrictlyLE 0 := by
  -- The extension-by-zero owner carries the standard nonpositive support instance.
  infer_instance

/-- Helper for Example 15.62.3: tensoring the chosen free `B`-resolution of `M` with `N`,
then restricting scalars along `A → B`, gives the `A`-linear chain complex whose homology
should recover `Tor_*^B(M, N)`. -/
private abbrev tor_base_change_tensor_resolution
    (F : ChainComplex ModB ℕ) (N : ModB) : ChainComplex ModA ℕ :=
  ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).obj F)

/-- Helper for Example 15.62.3: the `A`-linear tensor-resolution complex is reindexed to a
cochain complex on `ℤ` by extension by zero, matching the source proof's bounded-below model. -/
private abbrev tor_base_change_tensor_resolutionView
    (F : ChainComplex ModB ℕ) (N : ModB) : CochainComplex ModA ℤ :=
  (tor_base_change_tensor_resolution (A := A) (B := B) F N).extend
    ComplexShape.embeddingDownNat

/-- Helper for Example 15.62.3: the extended `A`-linear tensor-resolution complex is supported
in nonpositive cochain degrees. -/
private lemma tor_base_change_tensor_resolutionView_isStrictlyLE_zero
    (F : ChainComplex ModB ℕ) (N : ModB) :
    (tor_base_change_tensor_resolutionView (A := A) (B := B) F N).IsStrictlyLE 0 := by
  -- The extension-by-zero owner places all positive cochain degrees in the zero object.
  infer_instance

/-- Helper for Example 15.62.3: the chosen `A`-linear tensor-resolution cochain model is viewed
as a `ℤ`-indexed chain complex via the inverse chain/cochain equivalence. -/
private abbrev tor_base_change_tensor_resolutionChain
    (F : ChainComplex ModB ℕ) (N : ModB) : ChainComplex ModA ℤ :=
  (ChainComplex.cochainComplexEquivalence ModA).inverse.obj
    (tor_base_change_tensor_resolutionView (A := A) (B := B) F N)

/-- Helper for Example 15.62.3: applying `chainToCochain` to the chosen chain model recovers the
fixed cochain tensor-resolution view. -/
private theorem tor_base_change_tensor_resolution_chain_to_cochain_iso
    (F : ChainComplex ModB ℕ) (N : ModB) :
    Nonempty
      (((ChainComplex.chainToCochain ModA).obj
          (tor_base_change_tensor_resolutionChain (A := A) (B := B) F N)) ≅
        tor_base_change_tensor_resolutionView (A := A) (B := B) F N) := by
  refine ⟨?_⟩
  -- This is the counit isomorphism of the chain/cochain equivalence on `ModuleCat A`.
  exact
    (ChainComplex.cochainComplexEquivalence ModA).counitIso.app
      (tor_base_change_tensor_resolutionView (A := A) (B := B) F N)

/-- Helper for Example 15.62.3: the chosen chain model satisfies the bounded-below hypothesis
required by Example 15.62.1. -/
private lemma tor_base_change_tensor_resolution_chain_boundedBelow
    (F : ChainComplex ModB ℕ) (N : ModB) :
    ∃ n : ℤ,
      ((ChainComplex.chainToCochain ModA).obj
        (tor_base_change_tensor_resolutionChain (A := A) (B := B) F N)).IsStrictlyLE n := by
  obtain ⟨e⟩ :=
    tor_base_change_tensor_resolution_chain_to_cochain_iso
      (A := A) (B := B) (F := F) (N := N)
  refine ⟨0, ?_⟩
  -- Transport the explicit nonpositive support bound across the counit isomorphism.
  letI :
      (tor_base_change_tensor_resolutionView (A := A) (B := B) F N).IsStrictlyLE 0 :=
    tor_base_change_tensor_resolutionView_isStrictlyLE_zero (A := A) (B := B) F N
  simpa using
    (CochainComplex.isStrictlyLE_of_iso e.symm (0 : ℤ) :
      ((ChainComplex.chainToCochain ModA).obj
        (tor_base_change_tensor_resolutionChain (A := A) (B := B) F N)).IsStrictlyLE 0)

/-- Helper for Example 15.62.3: once the source-proof chain model
`K = F_• \otimes_B N` is fixed over `A`, the remaining structural step is to lift the first
spectral-sequence package to `ModuleCat (B ⊗[A] A')`, together with the displayed page-two and
abutment comparisons. -/
private theorem tor_base_change_lifted_first_spectral_sequence
    (M N : ModB)
    (F : ChainComplex ModB ℕ)
    (πF : F ⟶ (ChainComplex.single₀ ModB).obj M)
    [ChainComplex.IsFreeResolution πF]
    (P : ChainComplex ModA ℕ)
    (πP : P ⟶ (ChainComplex.single₀ ModA).obj (ModuleCat.of A A'))
    [ChainComplex.IsFreeResolution πP]
    (hBflat : Module.Flat A B)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (hNflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj N))
    (hK : ∃ n : ℤ,
      ((ChainComplex.chainToCochain ModA).obj
        (tor_base_change_tensor_resolutionChain (A := A) (B := B) F N)).IsStrictlyLE n) :
    ∃ (K : HomologicalComplex₂ ModBTensorAprime (ComplexShape.up ℤ) (ComplexShape.up ℤ))
      (_ : K.HasTotal (ComplexShape.up ℤ))
      (E : CohomologicalSpectralSequence ModBTensorAprime 0)
      (_ : IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K) E),
      doubleComplexHasFiniteAntidiagonalSupport K ∧
        (∀ i j : ℕ,
          Nonempty
            ((ModuleCat.restrictScalars (algebraMap A' BTensorAprime)).obj
                ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅
              torBaseChangePageTwo A M N i j)) ∧
        (∀ n : ℕ,
          Nonempty
            ((HomologicalComplex₂.total K (ComplexShape.up ℤ)).homology (-(n : ℤ)) ≅
              torBaseChangeAbutment A M N n)) := by
  -- Route correction: the unresolved work is no longer hidden in the main theorem. This helper
  -- is exactly the owner-level lift demanded by the source proof.
  --
  -- TODO: invoke Example `15.62.1` over `A` on the bounded-below chain model
  -- `tor_base_change_tensor_resolutionChain A B F N`, lift the resulting first filtered package
  -- to `ModuleCat (B ⊗[A] A')`, then compose its page-two and abutment identifications with the
  -- canonical tensor/base-change comparison isomorphisms from the source proof.
  sorry

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
      IsTorBaseChangeSpectralSequence A E M N := by
  classical
  -- The intended source-faithful route is:
  -- 1. choose a free `B`-resolution `F_• → M` and a free `A`-resolution `P_• → A'`;
  -- 2. form the first filtered spectral sequence of the resulting double complex over
  --    `B' = B ⊗[A] A'`;
  -- 3. identify its `E₂`-page with `Tor_i^A(Tor_j^B(M, N), A')` and its abutment with
  --    `Tor_{i+j}^{B'}(M', N')`;
  -- 4. package those two pieces with
  --    `isTorBaseChangeSpectralSequence_of_firstDoubleComplex`.
  obtain ⟨F, πF, hπF⟩ := module_exists_free_resolution (R := B) (M := M)
  letI : ChainComplex.IsFreeResolution πF := hπF
  let AprimeAsAModule : ModuleCat A := ModuleCat.of A A'
  obtain ⟨P, πP, hπP⟩ := module_exists_free_resolution (R := A) (M := AprimeAsAModule)
  letI : ChainComplex.IsFreeResolution πP := hπP
  have hFstrict :
      (tor_base_change_b_resolutionView (B := B) F).IsStrictlyLE 0 :=
    tor_base_change_b_resolutionView_isStrictlyLE_zero (B := B) F
  have hPstrict :
      (tor_base_change_aprime_resolutionView (A := A) P).IsStrictlyLE 0 :=
    tor_base_change_aprime_resolutionView_isStrictlyLE_zero (A := A) P
  have hKstrict :
      (tor_base_change_tensor_resolutionView (A := A) (B := B) F N).IsStrictlyLE 0 :=
    tor_base_change_tensor_resolutionView_isStrictlyLE_zero (A := A) (B := B) F N
  let _ := hFstrict
  let _ := hPstrict
  let _ := hKstrict
  let K := tor_base_change_tensor_resolutionChain (A := A) (B := B) F N
  have hK :
      ∃ n : ℤ, ((ChainComplex.chainToCochain ModA).obj K).IsStrictlyLE n := by
    -- The chosen chain model inherits bounded-below support from the explicit cochain view.
    simpa [K] using
      tor_base_change_tensor_resolution_chain_boundedBelow
        (A := A) (B := B) (F := F) (N := N)
  have hKmodel :
      ∃ n : ℤ,
        ((ChainComplex.chainToCochain ModA).obj
          (tor_base_change_tensor_resolutionChain (A := A) (B := B) F N)).IsStrictlyLE n := by
    -- Re-express the bounded-below witness in the canonical source-proof notation expected by the
    -- lifted helper theorem.
    simpa [K] using hK
  obtain ⟨K', hK'tot, E, hAssoc, hfin, hpage, habut⟩ :=
    tor_base_change_lifted_first_spectral_sequence
      (A := A) (B := B) (A' := A')
      (M := M) (N := N)
      (F := F) (πF := πF) (P := P) (πP := πP)
      hBflat hMflat hNflat hKmodel
  letI : K'.HasTotal (ComplexShape.up ℤ) := hK'tot
  letI : IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex K') E := hAssoc
  refine ⟨E, ?_⟩
  -- The main theorem now reduces to packaging the lifted first spectral sequence with its
  -- page-two and abutment transport isomorphisms.
  exact
    isTorBaseChangeSpectralSequence_of_firstDoubleComplex
      (A := A) (A' := A') (K := K') (E := E) (M := M) (N := N) hfin hpage habut

end

end
