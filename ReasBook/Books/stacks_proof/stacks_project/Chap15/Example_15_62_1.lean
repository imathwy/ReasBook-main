import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.CochainComplexOpposite
import StacksProject_2024.Chap10.Lemma_10_71_1
import StacksProject_2024.Chap12.Example_12_18_2
import StacksProject_2024.Chap12.Definition_12_14_1
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Lemma_12_25_1
import StacksProject_2024.Chap12.Lemma_12_25_3
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ChainComplex
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct HomologicalComplex₂

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksProject

section

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat.{u} R)] [WellPowered.{0} (ModuleCat.{u} R)]
variable [HasProjectiveResolutions (ModuleCat.{u} R)]

local notation "ModR" => ModuleCat R
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor ModR

/-- Internal cochain view of a chain complex, obtained from the Chapter `12`
owner `ChainComplex.chainToCochain`. -/
private abbrev cochainView
    (K : ChainComplex ModR ℤ) : CochainComplex ModR ℤ :=
  (ChainComplex.chainToCochain ModR).obj K

/-- The abutment object `H_n(K_• \otimes_R^{\mathbf L} M)`, written through the standard
chain-to-cochain transport into the derived category. -/
private abbrev derivedTensorHomologyAbutment
    (K : ChainComplex ModR ℤ) (M : ModR) (n : ℤ) : ModR :=
  (H (-n)).obj
    (DerivedCategory.Q.obj (cochainView K) ⊗[R]^L
      (single₀).obj M)

/-- The `E₂`-term `Tor_j^R(H_i(K_•), M)` in `ModuleCat R`. -/
private abbrev firstTorPageTwo
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) : ModR :=
  (((Tor ModR j).obj (K.homology i)).obj M)

/-- The homological `(i,j)` entry of the second page, read from the cohomological spectral
sequence by the sign convention of Example `15.62.1`. -/
private abbrev firstTorPageTwoObj
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) : ModR :=
  (E.page 2).X (-(j : ℤ), -i)

/-- The `E₁`-term `Tor_j^R(K_i, M)` in `ModuleCat R`. -/
private abbrev secondTorPageOne
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) : ModR :=
  (((Tor ModR j).obj (K.X i)).obj M)

/-- The homological `(i,j)` entry of the first page, again read via the sign convention of
Example `15.62.1`. -/
private abbrev secondTorPageOneObj
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) : ModR :=
  (E.page 1).X (-i, -(j : ℤ))

/-- The morphism on `Tor_j^R(-, M)` induced by the differential `K_i ⟶ K_{i - 1}`. -/
private abbrev secondTorPageOneMap
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) :
    secondTorPageOne K M i j ⟶ secondTorPageOne K M (i - 1) j :=
  (((Tor ModR j).map (K.d i (i - 1))).app M)

/-- Internal bridge: a cohomological spectral sequence converges to
`H_*(K_• \otimes_R^{\mathbf L} M)` if it is associated to a filtered complex whose reindexed
cohomology objects identify with the derived tensor-product homology abutment and which satisfies
the Chapter `12` convergence owner. -/
private def convergesToDerivedTensorHomology
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  ∃ (F : FilteredComplex ModR) (_ : IsAssociatedToFilteredComplex F E),
    F.convergesToCohomology E ∧
      ∀ n : ℤ,
        Nonempty (F.underlying.homology (-n) ≅ derivedTensorHomologyAbutment K M n)

/-- The chosen free resolution of `M` viewed as a cochain complex on `ℤ`, supported in
nonpositive degrees by extension by zero. -/
private abbrev resolutionView
    (P : ChainComplex ModR ℕ) : CochainComplex ModR ℤ :=
  P.extend ComplexShape.embeddingDownNat

/-- Helper for Example 15.62.1: the cochain view of an `ℕ`-indexed free resolution is supported
in nonpositive degrees. -/
private lemma resolutionView_isStrictlyLE_zero
    (P : ChainComplex ModR ℕ) :
    (resolutionView P).IsStrictlyLE 0 := by
  -- The extension-by-zero owner carries the standard nonpositive support instance.
  infer_instance

/-- Helper for Example 15.62.1: positive cochain degrees of the extended free resolution vanish. -/
private lemma resolutionView_isZero_of_pos
    (P : ChainComplex ModR ℕ) (q : ℤ) (hq : 0 < q) :
    IsZero ((resolutionView P).X q) := by
  -- The strict `≤ 0` support immediately kills all positive degrees.
  letI : (resolutionView P).IsStrictlyLE 0 := resolutionView_isStrictlyLE_zero P
  exact (resolutionView P).isZero_of_isStrictlyLE 0 q hq

/-- The tensor bicomplex obtained from the cochain view of `K` and the chosen free resolution of
`M`. -/
private abbrev tensorResolutionBicomplex
    (K : ChainComplex ModR ℤ) (P : ChainComplex ModR ℕ) :
    HomologicalComplex₂ ModR (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((curriedTensor ModR).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
    (cochainView K)).obj (resolutionView P)

/-- Helper for Example 15.62.1: finite antidiagonal support for the tensor bicomplex coming from
`K` and a free resolution of `M`. -/
private theorem tensor_resolution_bicomplex_hasFiniteAntidiagonalSupport
    (K : ChainComplex ModR ℤ)
    (P : ChainComplex ModR ℕ)
    (hK : ∃ n : ℤ, (cochainView K).IsStrictlyLE n) :
    doubleComplexHasFiniteAntidiagonalSupport (tensorResolutionBicomplex K P) :=
  by
    obtain ⟨N, hN⟩ := hK
    intro n
    -- A nonzero summand on the antidiagonal must lie between the lower bound forced by the
    -- resolution support and the upper bound forced by the bounded-below hypothesis on `K`.
    refine (Set.finite_Icc n N).subset ?_
    intro p hp
    constructor
    · by_contra hpn
      -- If `p < n`, then the resolution contributes in a positive cochain degree and vanishes.
      have hlt : p < n := lt_of_not_ge hpn
      have hpos : 0 < n - p := sub_pos.mpr hlt
      have hzeroRes : IsZero ((resolutionView P).X (n - p)) :=
        resolutionView_isZero_of_pos P (n - p) hpos
      have hzeroTensor :
          IsZero
            (((curriedTensor ModR).obj ((cochainView K).X p)).obj
              ((resolutionView P).X (n - p))) :=
        Functor.map_isZero _ hzeroRes
      have hzeroEntry : IsZero (((tensorResolutionBicomplex K P).X p).X (n - p)) := by
        simpa [tensorResolutionBicomplex] using hzeroTensor
      exact hp hzeroEntry
    · by_contra hNp
      -- If `N < p`, then the `K`-term itself vanishes, so the tensor summand vanishes as well.
      have hlt : N < p := lt_of_not_ge hNp
      have hzeroK : IsZero ((cochainView K).X p) := by
        letI : (cochainView K).IsStrictlyLE N := hN
        exact (cochainView K).isZero_of_isStrictlyLE N p hlt
      have hzeroTensor :
          IsZero
            ((((curriedTensor ModR).flip.obj ((resolutionView P).X (n - p))).obj
              ((cochainView K).X p))) :=
        Functor.map_isZero _ hzeroK
      have hzeroEntry : IsZero (((tensorResolutionBicomplex K P).X p).X (n - p)) := by
        simpa [tensorResolutionBicomplex] using hzeroTensor
      exact hp hzeroEntry

/-- Helper for Example 15.62.1: the chosen cochain resolution view still represents `M[0]` in the
derived category. -/
private theorem resolution_view_iso_single_zero
    (M : ModR)
    (P : ChainComplex ModR ℕ)
    (π : P ⟶ Functor.obj (ChainComplex.single₀ ModR) M)
    [IsFreeResolution π] :
    Nonempty (DerivedCategory.Q.obj (resolutionView P) ≅ (single₀).obj M) := by
  let f :
      DerivedCategory.Q.obj (resolutionView P) ⟶
        DerivedCategory.Q.obj
          (((ChainComplex.single₀ ModR).obj M).extend ComplexShape.embeddingDownNat) :=
    DerivedCategory.Q.map (HomologicalComplex.extendMap π ComplexShape.embeddingDownNat)
  have hf : IsIso f := by
    -- Extending the augmentation by zero preserves the free-resolution quasi-isomorphism.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e :
      DerivedCategory.Q.obj (resolutionView P) ≅
        DerivedCategory.Q.obj
          (((ChainComplex.single₀ ModR).obj M).extend ComplexShape.embeddingDownNat) :=
    asIso f
  refine ⟨e ≪≫ ?_⟩
  -- Now rewrite the extended chain-level single complex to the canonical derived object `M[0]`.
  exact
    (DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat M (0 : ℕ) (0 : ℤ) rfl)) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M).symm

/-- Helper for Example 15.62.1: the total complex of the tensor bicomplex is definitionally the
ordinary tensor complex of the two cochain views. -/
private theorem tensor_resolution_total_iso_tensorObj
    (K : ChainComplex ModR ℤ)
    (P : ChainComplex ModR ℕ) :
    Nonempty
      (HomologicalComplex₂.total (tensorResolutionBicomplex K P) (ComplexShape.up ℤ) ≅
        HomologicalComplex.tensorObj (cochainView K) (resolutionView P)) := by
  -- Both sides are the same totalized tensor construction.
  exact ⟨Iso.refl _⟩

/-- Helper for Example 15.62.1: the Chapter `12` chain/cochain reindexing identifies chain
homology in degree `i` with cochain homology in degree `-i`. -/
private theorem chain_to_cochain_homology_iso
    (K : ChainComplex ModR ℤ) (i : ℤ) :
    ((ChainComplex.chainToCochain ModR).obj K).homology (-i) ≅ K.homology i := by
  -- Reuse the canonical chain/cochain equivalence and its owner homology transport.
  exact
    ((((ChainComplex.cochainComplexEquivalence ModR).functor.obj K).restrictionHomologyIso
        ComplexShape.embeddingDownIntUpInt (i + 1) i (i - 1) (by simp) (by simp)
        (show ComplexShape.embeddingDownIntUpInt.f (i + 1) = -i - 1 by
          change -(i + 1) = -i - 1
          omega)
        (show ComplexShape.embeddingDownIntUpInt.f i = -i by simp)
        (show ComplexShape.embeddingDownIntUpInt.f (i - 1) = -i + 1 by
          change -(i - 1) = -i + 1
          omega)
        (show (ComplexShape.up ℤ).prev (-i) = -i - 1 by simp)
        (show (ComplexShape.up ℤ).next (-i) = -i + 1 by simp)).symm) ≪≫
      (HomologicalComplex.homologyFunctor ModR (ComplexShape.down ℤ) i).mapIso
        (((ChainComplex.cochainComplexEquivalence ModR).unitIso.app K).symm)

/-- Helper for Example 15.62.1: the total cohomology of the tensor bicomplex computes the
homology of `K_• ⊗_R^{\mathbf L} M`. -/
private theorem tensor_resolution_total_homology_iso_derivedTensorHomology
    (K : ChainComplex ModR ℤ)
    (P : ChainComplex ModR ℕ)
    (M : ModR)
    (π : P ⟶ Functor.obj (ChainComplex.single₀ ModR) M)
    [IsFreeResolution π] :
    ∀ n : ℤ,
      Nonempty
        ((HomologicalComplex₂.total (tensorResolutionBicomplex K P) (ComplexShape.up ℤ)).homology
            (-n) ≅
          derivedTensorHomologyAbutment K M n) :=
  by
    intro n
    obtain ⟨eTot⟩ := tensor_resolution_total_iso_tensorObj K P
    obtain ⟨eResolution⟩ := resolution_view_iso_single_zero M P π
    let eTensor :
        DerivedCategory.Q.obj
            (HomologicalComplex.tensorObj (cochainView K) (resolutionView P)) ≅
          (DerivedCategory.Q.obj (cochainView K)) ⊗[R]^L (single₀).obj M :=
      -- First localize the tensor complex, then replace the resolution view by the derived
      -- degree-zero single complex `M[0]`.
      (Functor.Monoidal.μIso
        (DerivedCategory.Q : CochainComplex ModR ℤ ⥤ DerivedCategory ModR)
        (cochainView K) (resolutionView P)).symm ≪≫
        ((Iso.refl _) ⊗ᵢ eResolution) ≪≫
          derivedCategory_tensorObj_iso_derivedTensorProduct
            (DerivedCategory.Q.obj (cochainView K)) ((single₀).obj M)
    refine ⟨?_⟩
    -- Transport homology across the total/tensor comparison, then across the derived tensor
    -- comparison obtained from the chosen free resolution.
    exact
      (HomologicalComplex.homologyMapIso eTot (-n)) ≪≫
        (((DerivedCategory.homologyFunctorFactors (ModuleCat R) (-n)).app
          (HomologicalComplex.tensorObj (cochainView K) (resolutionView P))).symm) ≪≫
        (H (-n)).mapIso eTensor

/-- Helper for Example 15.62.1: fixing the second index of the `E₁`-page turns the ambient page
into an ordinary cochain complex in the first index. -/
private theorem associatedPageOneComplex_shape
    (E : CohomologicalSpectralSequence ModR 0) (q : ℤ) :
    ∀ ⦃p p' : ℤ⦄,
      ¬ (ComplexShape.up ℤ).Rel p p' →
        (E.page 1).d (p, q) (p', q) = 0 := by
  intro p p' hpp'
  -- Fixing the second index rewrites the ambient bidegree shape to the ordinary cochain shape.
  have hpq :
      ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel (p, q) (p', q) := by
    simpa [ComplexShape.up'] using hpp'
  exact (E.page 1).shape (p, q) (p', q) hpq

/-- Helper for Example 15.62.1: the fixed-`q` `E₁`-slice inherits `d² = 0` from the ambient page
of the spectral sequence. -/
private theorem associatedPageOneComplex_d_comp_d
    (E : CohomologicalSpectralSequence ModR 0) (q : ℤ) :
    ∀ ⦃p p' p'' : ℤ⦄,
      (ComplexShape.up ℤ).Rel p p' →
        (ComplexShape.up ℤ).Rel p' p'' →
          (E.page 1).d (p, q) (p', q) ≫ (E.page 1).d (p', q) (p'', q) = 0 := by
  intro p p' p'' hpp' hp'p''
  -- The slice uses the same differential data as the ambient `E₁`-page at fixed second index.
  exact (E.page 1).d_comp_d (p, q) (p', q) (p'', q)

/-- Helper for Example 15.62.1: fixing the second index `q` turns the `E₁`-page into an ordinary
cochain complex in the first index. -/
private def associatedPageOneComplex
    (E : CohomologicalSpectralSequence ModR 0) (q : ℤ) : CochainComplex ModR ℤ where
  X p := (E.page 1).X (p, q)
  d p p' := (E.page 1).d (p, q) (p', q)
  shape := associatedPageOneComplex_shape E q
  d_comp_d' := associatedPageOneComplex_d_comp_d E q

/-- Helper for Example 15.62.1: the short-complex view of the fixed-`q` `E₁`-slice agrees with
the ambient short complex at bidegree `(p, q)`. -/
private theorem associatedPageOneComplexScIso
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ) :
    (associatedPageOneComplex E q).sc' (p - 1) p (p + 1) ≅
      (E.page 1).sc' (p - 1, q) (p, q) (p + 1, q) := by
  -- The fixed-`q` slice literally reuses the same objects and differentials as the ambient page.
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp [associatedPageOneComplex]
  · simp [associatedPageOneComplex]

/-- Helper for Example 15.62.1: the `p`-th homology of the fixed-`q` `E₁`-slice is the ambient
page-one homology object at bidegree `(p, q)`. -/
private theorem associatedPageOneComplex_homologyIso
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ) :
    (associatedPageOneComplex E q).homology p ≅ (E.page 1).homology (p, q) := by
  have hprevSlice : (ComplexShape.up ℤ).prev p = p - 1 := by
    exact ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  have hnextSlice : (ComplexShape.up ℤ).next p = p + 1 := by
    exact ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  have hprevPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) := by
    exact
      ComplexShape.prev_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
        (by simp [ComplexShape.up'])
  have hnextPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) := by
    exact
      ComplexShape.next_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
        (by simp [ComplexShape.up'])
  -- Compare the slice short complex with the ambient short complex, then transport homology.
  exact
    (associatedPageOneComplex E q).homologyIsoSc' (p - 1) p (p + 1) hprevSlice hnextSlice ≪≫
      ShortComplex.homologyMapIso (associatedPageOneComplexScIso E p q) ≪≫
      ((E.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hprevPage hnextPage).symm

/-- Helper for Example 15.62.1: any fixed-`q` comparison of the `E₁`-slice with an ordinary
cochain complex yields the corresponding `E₂`-page identification by taking `p`-th homology. -/
private theorem associated_pageTwo_iso_of_pageOne_complex_iso
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ)
    (C : CochainComplex ModR ℤ)
    (e : associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  refine ⟨?_⟩
  -- Rewrite the ambient `E₂` term as homology of the fixed-`q` `E₁` slice, then transport
  -- along the chosen comparison with `C`.
  exact
    (E.iso 1 2 (p, q)).symm ≪≫
      (associatedPageOneComplex_homologyIso E p q).symm ≪≫
        HomologicalComplex.homologyMapIso e p

/-- Helper for Example 15.62.1: specialize the generic page-two transport to the homological
indexing convention `(p, q) = (-j, -i)` used in the first Tor spectral sequence. -/
private theorem associated_pageTwo_iso_of_pageOne_complex_iso_tor_indices
    (E : CohomologicalSpectralSequence ModR 0)
    (i : ℤ) (j : ℕ)
    (C : CochainComplex ModR ℤ) (e : associatedPageOneComplex E (-i) ≅ C) :
    Nonempty (firstTorPageTwoObj E i j ≅ C.homology (-(j : ℤ))) := by
  -- Proof comment: this is only the generic fixed-`q` page-two transport rewritten at the
  -- textbook indices `(-j, -i)`.
  simpa [firstTorPageTwoObj] using
    associated_pageTwo_iso_of_pageOne_complex_iso E (-(j : ℤ)) (-i) C e

/-- Helper for Example 15.62.1: the fixed-`q` page-one slice evaluated at `(-i, -j)` is exactly
the object appearing in the second Tor spectral sequence statement. -/
@[simp] private theorem associatedPageOneComplex_X_tor_indices
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) :
    (associatedPageOneComplex E (-(j : ℤ))).X (-i) = secondTorPageOneObj E i j := by
  -- Proof comment: both sides are the same page-one object after expanding the local
  -- abbreviations.
  rfl

/-- Helper for Example 15.62.1: the differential in the fixed-`q` slice at consecutive
homological indices is literally the ambient `d₁` map used in the second Tor spectral sequence. -/
@[simp] private theorem associatedPageOneComplex_d_tor_indices
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) :
    (associatedPageOneComplex E (-(j : ℤ))).d (-i) (-(i - 1)) =
      (E.page 1).d (-i, -(j : ℤ)) (-(i - 1), -(j : ℤ)) := by
  -- Proof comment: the fixed-`q` slice reuses the ambient page-one differential without any extra
  -- transport.
  rfl

/-- Helper for Example 15.62.1: the `E₂`-page of the first associated spectral sequence of the
tensor bicomplex is `Tor_j^R(H_i(K_•), M)`. -/
private theorem first_associated_page_two_iso_tor_homology
    (K : ChainComplex ModR ℤ)
    (P : ChainComplex ModR ℕ)
    (M : ModR)
    (π : P ⟶ Functor.obj (ChainComplex.single₀ ModR) M)
    [IsFreeResolution π]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex
      (firstDoubleComplexFilteredComplex (tensorResolutionBicomplex K P)) E] :
    ∀ i : ℤ, ∀ j : ℕ,
      Nonempty (firstTorPageTwoObj E i j ≅ firstTorPageTwo K M i j) :=
  by
    intro i j
    -- TODO: transport `(E.page 2).X (-(j : ℤ), -i)` to the owner page
    -- `firstDoubleComplexPageTwo (tensorResolutionBicomplex K P) (-(j : ℤ)) (-i)` using the
    -- associated-spectral-sequence page identifications, then compute that owner page as
    -- `Tor_j^R(H_i(K), M)` by taking vertical homology against the chosen free resolution and
    -- horizontal homology afterwards.
    sorry

/-- Helper for Example 15.62.1: the `E₁`-page of the second associated spectral sequence of the
tensor bicomplex is `Tor_j^R(K_i, M)`. -/
private noncomputable def second_associated_page_one_iso_tor_terms
    (K : ChainComplex ModR ℤ)
    (P : ChainComplex ModR ℕ)
    (M : ModR)
    (π : P ⟶ Functor.obj (ChainComplex.single₀ ModR) M)
    [IsFreeResolution π]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex
      (secondDoubleComplexFilteredComplex (tensorResolutionBicomplex K P)) E] :
    ∀ i : ℤ, ∀ j : ℕ,
      secondTorPageOneObj E i j ≅ secondTorPageOne K M i j :=
  by
    intro i j
    -- TODO: transport `(E.page 1).X (-i, -(j : ℤ))` to the owner page
    -- `secondDoubleComplexPageOne (tensorResolutionBicomplex K P) (-i) (-(j : ℤ))`, then identify
    -- that row homology with `Tor_j^R(K_i, M)` using the chosen free resolution of `M`.
    sorry

/-- Helper for Example 15.62.1: under the page-one identifications, the `d₁` differential of the
second associated spectral sequence is induced by `K_i ⟶ K_{i-1}`. -/
private theorem second_associated_page_one_differential_commSq
    (K : ChainComplex ModR ℤ)
    (P : ChainComplex ModR ℕ)
    (M : ModR)
    (π : P ⟶ Functor.obj (ChainComplex.single₀ ModR) M)
    [IsFreeResolution π]
    (E : CohomologicalSpectralSequence ModR 0)
    [IsAssociatedToFilteredComplex
      (secondDoubleComplexFilteredComplex (tensorResolutionBicomplex K P)) E] :
    ∀ i : ℤ, ∀ j : ℕ,
      CommSq
        ((E.page 1).d (-i, -(j : ℤ)) (-(i - 1), -(j : ℤ)))
        (second_associated_page_one_iso_tor_terms K P M π E i j).hom
        (second_associated_page_one_iso_tor_terms K P M π E (i - 1) j).hom
        (secondTorPageOneMap K M i j) :=
  by
    intro i j
    -- TODO: after the page-one object identification is in place, rewrite the left map via
    -- `secondDoubleComplexPageOneDifferential_def` and the bicomplex differential formula, then
    -- check that the transported morphism is exactly
    -- `(((Tor ModR j).map (K.d i (i - 1))).app M)`.
    sorry

/-
Domain-style sampling for Example `15.62.1`.
- primary domain: cohomological spectral sequences in `ModuleCat R`, reindexed homologically, with
  convergence to the homology of the derived tensor product;
- sampled owner API:
  `CategoryTheory.CohomologicalSpectralSequence`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `CategoryTheory.FilteredComplex.convergesToCohomology`,
  `CategoryTheory.FilteredComplex.underlying`,
  `ChainComplex.chainToCochain`,
  `CategoryTheory.CommSq`,
  `CategoryTheory.DerivedCategory.homologyFunctor`;
- best owner abstraction: a cohomological spectral sequence `E` together with an associated
  filtered complex `F : FilteredComplex (ModuleCat R)` satisfying the canonical owner predicate
  `F.convergesToCohomology E`;
- primitive data: `E : CohomologicalSpectralSequence (ModuleCat R) 0`, the filtered complex
  witness `F : FilteredComplex (ModuleCat R)` in the convergence clause, and the canonical
  lower-support condition `∃ n : ℤ, ((chainToCochain ModR).obj K).IsStrictlyLE n` on the cochain
  view of the chain complex `K`, expressing that `K` is bounded below;
- derived API: the homological reindexing of the pages, the `Tor`-page identifications, the
  `d₁` comparison squares, the derived-category abutment object
  `derivedTensorHomologyAbutment`, and the shared internal bridge
  `convergesToDerivedTensorHomology`;
- source/core/bridge triage:
  `source-facing`: `IsFirstTorSpectralSequence` and `IsSecondTorSpectralSequence`;
  `core/canonical`: `CohomologicalSpectralSequence`, `FilteredComplex.convergesToCohomology`,
    `FilteredComplex.underlying`,
    `DerivedCategory.homologyFunctor`, `ChainComplex.chainToCochain`, `CommSq`;
  `bridge/view`: the internal chain-to-cochain transport via
    `ChainComplex.chainToCochain`, the shared abutment/page abbreviations, and the internal
    convergence clause `convergesToDerivedTensorHomology`.
-/

/-- The first spectral sequence of Example `15.62.1`, read in homological indexing: its `E₂`-page
is `Tor_j^R(H_i(K_•), M)`, and it converges to `H_*(K_• \otimes_R^{\mathbf L} M)`. -/
def IsFirstTorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  (∀ (i : ℤ) (j : ℕ),
      Nonempty (firstTorPageTwoObj E i j ≅ firstTorPageTwo K M i j)) ∧
    convergesToDerivedTensorHomology E K M

/-- The second spectral sequence of Example `15.62.1`, read in homological indexing: its
`E₁`-page is `Tor_j^R(K_i, M)`, the `d₁` differential is induced by `K_i ⟶ K_{i - 1}`, and it
converges to `H_*(K_• \otimes_R^{\mathbf L} M)`. -/
def IsSecondTorSpectralSequence
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  (∃ pageOneIso :
      ∀ (i : ℤ) (j : ℕ),
        secondTorPageOneObj E i j ≅ secondTorPageOne K M i j,
      ∀ (i : ℤ) (j : ℕ),
        CommSq ((E.page 1).d (-i, -(j : ℤ)) (-(i - 1), -(j : ℤ))) (pageOneIso i j).hom
          (pageOneIso (i - 1) j).hom (secondTorPageOneMap K M i j)) ∧
    convergesToDerivedTensorHomology E K M

-- Proof sketch: choose a free resolution of `M`, convert the tensor double chain complex
-- `K_• ⊗_R P_•` to the cohomological double-complex formalism of Chapter `12`, apply the two
-- spectral sequences of Lemma `12.25.3`, identify the resulting `E₂`- and `E₁`-pages with the
-- stated `Tor` groups, and then identify the total cohomology with the homology of
-- `K_• \otimes_R^{\mathbf L} M` via the canonical derived tensor product of Chapter `15`.
/-- Example 15.62.1: if `K_•` is a chain complex of `R`-modules with `K_n = 0` for `n \ll 0` and
`M` is an `R`-module, then there exist two spectral sequences converging to
`H_*(K_• \otimes_R^{\mathbf L} M)`: a first one with `E₂`-page
`Tor_j^R(H_i(K_•), M)` and a second one with `E₁`-page `Tor_j^R(K_i, M)`. -/
@[stacks 061Z]
theorem exists_tor_spectral_sequences_of_boundedBelow_chainComplex
    (K : ChainComplex ModR ℤ)
    (hK : ∃ n : ℤ, ((chainToCochain ModR).obj K).IsStrictlyLE n)
    (M : ModR) :
    ∃ E₂ E₁ : CohomologicalSpectralSequence ModR 0,
      IsFirstTorSpectralSequence E₂ K M ∧
        IsSecondTorSpectralSequence E₁ K M := by
  classical
  -- We first choose a free resolution of `M`, then form the tensor bicomplex used by both
  -- spectral sequences.
  obtain ⟨P, π, hπ⟩ := module_exists_free_resolution (R := R) (M := M)
  letI : IsFreeResolution π := hπ
  let A := tensorResolutionBicomplex K P
  let hA :
      doubleComplexHasFiniteAntidiagonalSupport A :=
    tensor_resolution_bicomplex_hasFiniteAntidiagonalSupport K P hK
  -- We now choose the associated spectral sequences for the first and second filtrations on
  -- `Tot(A)`.
  obtain ⟨E₂, hE₂⟩ :=
    exists_filteredComplexAssociatedSpectralSequence
      (firstDoubleComplexFilteredComplex A)
  obtain ⟨E₁, hE₁⟩ :=
    exists_filteredComplexAssociatedSpectralSequence
      (secondDoubleComplexFilteredComplex A)
  refine ⟨E₂, E₁, ?_, ?_⟩
  · letI : IsAssociatedToFilteredComplex (firstDoubleComplexFilteredComplex A) E₂ := hE₂
    refine ⟨?_, ?_⟩
    · -- TODO: identify the first spectral sequence page by computing the horizontal homology of the
      -- tensor bicomplex after taking vertical homology against the chosen free resolution.
      intro i j
      simpa [A] using first_associated_page_two_iso_tor_homology K P M π E₂ i j
    · -- The convergence package is the Chapter 12 convergence theorem together with the common
      -- identification of total cohomology with derived tensor homology.
      refine ⟨firstDoubleComplexFilteredComplex A, hE₂, ?_, ?_⟩
      · simpa [A] using
          firstDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport A E₂ hA
      · intro n
        simpa [A] using tensor_resolution_total_homology_iso_derivedTensorHomology K P M π n
  · letI : IsAssociatedToFilteredComplex (secondDoubleComplexFilteredComplex A) E₁ := hE₁
    refine ⟨?_, ?_⟩
    · -- TODO: identify the first page with `Tor_j^R(K_i, M)` and compare the page-one
      -- differential with the map induced by `K_i ⟶ K_{i - 1}`.
      refine ⟨
        (fun i j ↦ second_associated_page_one_iso_tor_terms K P M π E₁ i j),
        ?_⟩
      intro i j
      simpa [A] using second_associated_page_one_differential_commSq K P M π E₁ i j
    · -- The second filtration has the same total complex and therefore the same abutment.
      refine ⟨secondDoubleComplexFilteredComplex A, hE₁, ?_, ?_⟩
      · simpa [A] using
          secondDoubleComplex_convergesToTotalCohomology_of_finiteAntidiagonalSupport A E₁ hA
      · intro n
        simpa [A] using tensor_resolution_total_homology_iso_derivedTensorHomology K P M π n

end

end StacksProject
