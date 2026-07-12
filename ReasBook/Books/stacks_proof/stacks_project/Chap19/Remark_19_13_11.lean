import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Lemma_12_24_11
import StacksProject_2024.Chap13.Lemma_13_11_2
import StacksProject_2024.Chap13.Lemma_13_27_9
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap13.Remark_13_26_15
import StacksProject_2024.Chap19.Remark_19_13_8
import StacksProject_2024.Chap19.Remark_19_13_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [LocallySmall A] [WellPowered A]
  [HasWidePullbacks A] [HasCoproducts A] [InitialMonoClass A] [IsGrothendieckAbelian.{w} A]

/-- The `AddCommGrpCat`-valued filtered complexes used to package the spectral sequences in this
item. -/
abbrev AbFilteredComplex :=
  CategoryTheory.FilteredComplex AddCommGrpCat

/-- The standard derived-category model attached to a Grothendieck abelian category in this item.
-/
local instance grothendieckAbelian_hasDerivedCategoryForRemark_19_13_11 :
    HasDerivedCategory A :=
  HasDerivedCategory.standard A

/-- Helper for Remark 19.13.11: transport along source and target isomorphisms is additive on
Hom groups in any preadditive category. -/
private theorem isoHomCongrAddEquiv_map_add
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C}
    (α : X ≅ X₁) (β : Y ≅ Y₁) (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is given by composing with the isomorphism legs, so
  -- bilinearity of composition yields additivity.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Remark 19.13.11: isomorphisms on source and target induce an additive equivalence
on the corresponding Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C}
    (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := isoHomCongrAddEquiv_map_add α β

/-- Helper for Remark 19.13.11: an isomorphism in the source variable transports the derived
Ext group functorially. -/
private noncomputable def derivedExtGroupIsoOfSourceIso
    {X Y K : DerivedCategory A} (e : X ≅ Y) (n : ℤ) :
    derivedExtGroup X K n ≅ derivedExtGroup Y K n :=
  (isoHomCongrAddEquiv e (Iso.refl _)).toAddCommGrpIso

/-- Helper for Remark 19.13.11: an isomorphism in the target variable transports the derived
Ext group functorially. -/
private noncomputable def derivedExtGroupIsoOfTargetIso
    (X : DerivedCategory A) {Y Z : DerivedCategory A} (e : Y ≅ Z) (n : ℤ) :
    derivedExtGroup X Y n ≅ derivedExtGroup X Z n :=
  (isoHomCongrAddEquiv (Iso.refl _) ((shiftFunctor (DerivedCategory A) n).mapIso e)).toAddCommGrpIso

/-- Helper for Remark 19.13.11: the degree-`i` single object, viewed in the derived category,
becomes the degree-zero single object after shifting by `i`. -/
private noncomputable def singleFunctorShiftedSingleZeroIso
    (X : A) (i : ℤ) :
    (((DerivedCategory.singleFunctor A i).obj X)⟦i⟧) ≅
      (DerivedCategory.singleFunctor A 0).obj X :=
  singleFunctor_shifted_single0_iso_canonical (𝒜 := A) X i

/-- Helper for Remark 19.13.11: the derived Ext group of a single object in degree `i` can be
rewritten as the degree-zero Ext group after shifting the Ext index by `i`. -/
private noncomputable def singleFunctorDerivedExtIso
    (X : A) (K : DerivedCategory A) (i q : ℤ) :
    derivedExtGroup ((DerivedCategory.singleFunctor A i).obj X) K (q - i) ≅
      derivedExtGroup ((DerivedCategory.singleFunctor A 0).obj X) K q := by
  let eSrc :
      (DerivedCategory.singleFunctor A i).obj X ≅
        ((DerivedCategory.singleFunctor A 0).obj X)⟦-i⟧ :=
    -- Proof comment: first normalize the degree-`i` single object to the degree-zero single
    -- object, keeping track of the compensating shift.
    (shiftShiftNeg ((DerivedCategory.singleFunctor A i).obj X) i).symm ≪≫
      (shiftFunctor (DerivedCategory A) (-i)).mapIso
        (singleFunctorShiftedSingleZeroIso (A := A) X i)
  let eHom₁ :
      (((DerivedCategory.singleFunctor A i).obj X) ⟶ K⟦q - i⟧) ≃
        ((((DerivedCategory.singleFunctor A 0).obj X)⟦-i⟧) ⟶ K⟦q - i⟧) :=
    Iso.homCongr eSrc (Iso.refl _)
  let eHom₂ :
      ((((DerivedCategory.singleFunctor A 0).obj X)⟦-i⟧) ⟶ K⟦q - i⟧) ≃
        (((DerivedCategory.singleFunctor A 0).obj X) ⟶ (K⟦q - i⟧)⟦i⟧) :=
    -- Proof comment: move the common shift from the source to the target through the shift
    -- equivalence adjunction.
    ((shiftEquiv (DerivedCategory A) i).symm.toAdjunction.homEquiv
      ((DerivedCategory.singleFunctor A 0).obj X) (K⟦q - i⟧))
  let eHom₃ :
      (((DerivedCategory.singleFunctor A 0).obj X) ⟶ (K⟦q - i⟧)⟦i⟧) ≃
        (((DerivedCategory.singleFunctor A 0).obj X) ⟶ K⟦q⟧) :=
    -- Proof comment: the two successive target shifts combine to the total shift `q`.
    Iso.homCongr (Iso.refl _) <|
      (shiftFunctorAdd' (DerivedCategory A) (q - i) i q (by omega)).symm.app K
  exact (eHom₁.trans (eHom₂.trans eHom₃)).toAddCommGrpIso

/-- Helper for Remark 19.13.11: a representative complex concentrated in one degree computes the
same derived Ext groups as the corresponding degree-zero single object after reindexing. -/
private noncomputable def representativeSingleDerivedExtIso
    (L : CochainComplex A ℤ) (K : DerivedCategory A) (n q : ℤ)
    [L.IsStrictlyGE n] [L.IsStrictlyLE n] :
    derivedExtGroup (DerivedCategory.Q.obj L) K (q - n) ≅
      derivedExtGroup ((DerivedCategory.singleFunctor A 0).obj (L.X n)) K q :=
  -- Proof comment: first identify the representative with the single object in degree `n`, then
  -- shift that single object down to degree `0`.
  derivedExtGroupIsoOfSourceIso
      (representative_single_iso_of_strict_bounds (A := A) L n)
      (K := K) (n := q - n) ≪≫
    singleFunctorDerivedExtIso (A := A) (X := L.X n) (K := K) n q

/-- Helper for Remark 19.13.11: an acyclic representative becomes zero in the derived category.
-/
private theorem qObj_isZero_of_acyclic
    (L : CochainComplex A ℤ) (hL : L.Acyclic) :
    IsZero (DerivedCategory.Q.obj L) := by
  let KL : HomotopyCategory A (ComplexShape.up ℤ) :=
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L
  let eQh :
      DerivedCategory.Qh.obj KL ≅ DerivedCategory.Q.obj L := by
    simpa [KL, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso A).app L
  have hker :
      Functor.kernel
        (DerivedCategory.Qh :
          HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
        KL := by
    -- Proof comment: the Verdier kernel of `Qh` is exactly the acyclic subcategory.
    rw [subcategoryAcyclic_kernel_Qh (A := A)]
    simpa [KL, HomotopyCategory.subcategoryAcyclic,
      ObjectProperty.prop_inverseImage_iff] using hL
  exact eQh.isZero_iff.2 hker

/-- Helper for Remark 19.13.11: if the source derived object is zero, then all of its derived
Ext groups vanish. -/
private theorem derivedExtGroup_isZero_of_source_isZero
    {X K : DerivedCategory A} (hX : IsZero X) (n : ℤ) :
    IsZero (derivedExtGroup X K n) := by
  -- Proof comment: maps out of a zero object form a subsingleton Hom group.
  refine AddCommGrpCat.isZero_of_subsingleton _
  refine ⟨?_⟩
  intro f g
  exact hX.eq_of_src f g

/-- Helper for Remark 19.13.11: choose the source-level Ext spectral sequence attached to the
canonical truncation filtration on a representative of `M`. -/
private noncomputable abbrev truncationSourceExtSpectralSequenceData
    (M K : DerivedCategory A) :
    FilteredComplexSourceExtSpectralSequenceData
      ((DerivedCategory.Q.objPreimage M).truncationFiltration) K :=
  Classical.choice <|
    filteredComplexSourceExtSpectralSequence_exists
      ((DerivedCategory.Q.objPreimage M).truncationFiltration) K

/-- Helper for Remark 19.13.11: the source-level truncation-filtration abutment already computes
`Ext^*(M, K)` after transporting along the canonical representative isomorphism. -/
private noncomputable def truncationSourceAbutmentIso
    (M K : DerivedCategory A) (n : ℤ) :
    addCommGrpFilteredComplexCohomologyObject
        (truncationSourceExtSpectralSequenceData (A := A) M K).filteredHomComplex n ≅
      derivedExtGroup M K n :=
  -- Proof comment: the source theorem abuts to the chosen representative, and
  -- `Q.objPreimage` is canonically isomorphic to `M`.
  (truncationSourceExtSpectralSequenceData (A := A) M K).abutmentIso n ≪≫
    derivedExtGroupIsoOfSourceIso
      (DerivedCategory.Q.objObjPreimageIso M)
      (K := K) (n := n)

/-- Helper for Remark 19.13.11: choose the source-level Ext spectral sequence attached to the
stupid filtration on the given cochain complex. -/
private noncomputable abbrev stupidSourceExtSpectralSequenceData
    (M : CochainComplex A ℤ) (K : DerivedCategory A) :
    FilteredComplexSourceExtSpectralSequenceData M.stupidFiltration K :=
  Classical.choice <|
    filteredComplexSourceExtSpectralSequence_exists M.stupidFiltration K

/-- The bounded-below condition on a derived object, i.e. membership in `D^+(A)`. -/
def derivedCategoryPlusProperty (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, K.IsGE n

/-- The bounded-above condition on a derived object, i.e. membership in `D^-(A)`. -/
def derivedCategoryMinusProperty (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, K.IsLE n

/-- A cochain complex is bounded above when it is zero in all sufficiently high degrees. -/
def cochainComplexIsBoundedAbove (M : CochainComplex A ℤ) : Prop :=
  ∃ n : ℤ, M.IsStrictlyLE n

/-- The cohomology object `H^n(F^•)` of the underlying complex of an `AddCommGrpCat`-valued
filtered complex. -/
abbrev addCommGrpFilteredComplexCohomologyObject
    (F : AbFilteredComplex) (n : ℤ) : AddCommGrpCat :=
  (FilteredComplex.underlying F).homology n

/-- The derived object corresponding to the cohomology object `H^j(M)` placed in degree `0`. -/
abbrev derivedCohomologyAsDerivedObject
    (M : DerivedCategory A) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj ((DerivedCategory.homologyFunctor A j).obj M)

/-- The derived object corresponding to the term `M^j` of a cochain complex, placed in degree `0`.
-/
abbrev cochainTermAsDerivedObject
    (M : CochainComplex A ℤ) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj (M.X j)

/-- A chosen renumbered spectral sequence computing `Ext^*(M, K)` from the cohomology objects
`H^{-j}(M)` of `M`. The owner objects are an `AddCommGrpCat`-valued filtered complex and its
associated cohomological spectral sequence. -/
structure DerivedExtCohomologySpectralSequenceData
    (M K : DerivedCategory A) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E'_2`-page identifies with `Ext^i(H^{-j}(M), K)`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        derivedExtGroup (derivedCohomologyAsDerivedObject M (-j)) K i
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      addCommGrpFilteredComplexCohomologyObject filteredComplex n ≅
        derivedExtGroup M K n
  /-- If `M ∈ D^-(A)` and `K ∈ D^+(A)`, then the renumbered spectral sequence converges to the
  cohomology of the underlying filtered complex in the Chapter `12` sense, hence to
  `Ext^*(M, K)` via `abutmentIso`. -/
  converges_of_boundedness :
    derivedCategoryMinusProperty M →
      derivedCategoryPlusProperty K →
      filteredComplex.convergesToCohomology spectralSequence

/-- A chosen spectral sequence obtained from the filtration `F^p M^• = σ_{\ge p} M^•` on a
cochain complex `M^•`. The owner objects are an `AddCommGrpCat`-valued filtered complex and its
associated cohomological spectral sequence. -/
structure DerivedExtStupidFiltrationSpectralSequenceData
    (M : CochainComplex A ℤ) (K : DerivedCategory A) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E_1`-page identifies with `Ext^q(M^{-p}, K)`. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        derivedExtGroup (cochainTermAsDerivedObject M (-p)) K q
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, K)` for the
  derived object represented by `M^•`. -/
  abutmentIso :
    ∀ n : ℤ,
      addCommGrpFilteredComplexCohomologyObject filteredComplex n ≅
        derivedExtGroup (DerivedCategory.Q.obj M) K n
  /-- If `M^•` is bounded above and `K ∈ D^+(A)`, then the spectral sequence converges to the
  cohomology of the underlying filtered complex in the Chapter `12` sense, hence to
  `Ext^*(M, K)` via `abutmentIso`. -/
  converges_of_boundedness :
    cochainComplexIsBoundedAbove M →
      derivedCategoryPlusProperty K →
      filteredComplex.convergesToCohomology spectralSequence

attribute [instance] DerivedExtCohomologySpectralSequenceData.associated
attribute [instance] DerivedExtStupidFiltrationSpectralSequenceData.associated

/-- Helper for Remark 19.13.11: the affine coordinate change `(i, j) ↦ (-j, i + 2j)` turns the
page-`r - 1` cohomological shape into the page-`r` shape. -/
private theorem negSwapRelIff
    (r i j i' j' : ℤ) :
    (ComplexShape.up' (⟨r - 1, 1 - (r - 1)⟩ : ℤ × ℤ)).Rel
        (-j, i + 2 * j) (-j', i' + 2 * j') ↔
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (i, j) (i', j') := by
  -- Proof comment: the affine map is chosen so that bidegree `(r - 1, -r + 2)` becomes
  -- `(r, -r + 1)` after the renumbering.
  simp [ComplexShape.up']
  omega

/-- Helper for Remark 19.13.11: for each positive page `r`, reindexing by `(i, j) ↦ (-j, i + 2j)`
transports the source page `r - 1` to a cohomological page of bidegree `(r, -r + 1)`. -/
private def renumberedPositivePage
    (S : CohomologicalSpectralSequence AddCommGrpCat 0) (r : ℤ) (hr : 1 ≤ r) :
    HomologicalComplex AddCommGrpCat (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) where
  X pq := (S.page (r - 1) (by omega)).X (-pq.2, pq.1 + 2 * pq.2)
  d pq pq' := (S.page (r - 1) (by omega)).d (-pq.2, pq.1 + 2 * pq.2) (-pq'.2, pq'.1 + 2 * pq'.2)
  shape pq pq' hpq := by
    -- Proof comment: rewrite the reindexed target back to the source page before applying the
    -- original shape relation.
    apply (S.page (r - 1) (by omega)).shape
    intro hrel
    exact hpq ((negSwapRelIff r pq.1 pq.2 pq'.1 pq'.2).1 hrel)
  d_comp_d' pq pq' pq'' hpq hpq' := by
    -- Proof comment: square-zero is inherited directly from the source page after transport.
    exact
      (S.page (r - 1) (by omega)).d_comp_d
        (-pq.2, pq.1 + 2 * pq.2)
        (-pq'.2, pq'.1 + 2 * pq'.2)
        (-pq''.2, pq''.1 + 2 * pq''.2)

/-- Helper for Remark 19.13.11: fixing the second index of a page-one object produces an ordinary
cochain complex in the first index. -/
private def associatedPageOneComplex
    (E : CohomologicalSpectralSequence AddCommGrpCat 0) (q : ℤ) :
    CochainComplex AddCommGrpCat ℤ where
  X p := (E.page 1).X (p, q)
  d p p' := (E.page 1).d (p, q) (p', q)
  shape p p' hpp' := by
    -- Proof comment: fixing `q` reduces the ambient bidegree shape to the ordinary cochain shape
    -- in the remaining coordinate.
    have hpq :
        ¬ (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).Rel (p, q) (p', q) := by
      simpa [ComplexShape.up'] using hpp'
    exact (E.page 1).shape (p, q) (p', q) hpq
  d_comp_d' p p' p'' hpp' hp'p'' := by
    -- Proof comment: the fixed-`q` slice keeps the same differential data as the ambient page.
    exact (E.page 1).d_comp_d (p, q) (p', q) (p'', q)

/-- Helper for Remark 19.13.11: the short-complex view of the fixed-`q` page-one slice agrees
with the ambient short complex at bidegree `(p, q)`. -/
private noncomputable def associatedPageOneComplexScIso
    (E : CohomologicalSpectralSequence AddCommGrpCat 0) (p q : ℤ) :
    (associatedPageOneComplex E q).sc' (p - 1) p (p + 1) ≅
      (E.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [associatedPageOneComplex])
    (by simp [associatedPageOneComplex])

/-- Helper for Remark 19.13.11: the `p`-th homology of the fixed-`q` page-one slice is the
ambient page-one homology object at bidegree `(p, q)`. -/
private noncomputable def associatedPageOneComplexHomologyIso
    (E : CohomologicalSpectralSequence AddCommGrpCat 0) (p q : ℤ) :
    (associatedPageOneComplex E q).homology p ≅ (E.page 1).homology (p, q) :=
  let hprevSlice : (ComplexShape.up ℤ).prev p = p - 1 :=
    ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hnextSlice : (ComplexShape.up ℤ).next p = p + 1 :=
    ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])
  let hprevPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    ComplexShape.prev_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  let hnextPage :
      (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    ComplexShape.next_eq' (ComplexShape.up' (⟨(1 : ℤ), 0⟩ : ℤ × ℤ))
      (by simp [ComplexShape.up'])
  -- Proof comment: the fixed-`q` slice keeps exactly the same short-complex data as the ambient
  -- page-one object.
  (associatedPageOneComplex E q).homologyIsoSc' (p - 1) p (p + 1) hprevSlice hnextSlice ≪≫
    ShortComplex.homologyMapIso (associatedPageOneComplexScIso E p q) ≪≫
    ((E.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hprevPage hnextPage).symm

/-- Helper for Remark 19.13.11: a comparison between a fixed-`q` page-one slice and an ordinary
cochain complex yields the corresponding page-two identification by taking `p`-th homology. -/
private theorem associatedPageTwoIsoOfPageOneComplexIso
    (E : CohomologicalSpectralSequence AddCommGrpCat 0) (p q : ℤ)
    (C : CochainComplex AddCommGrpCat ℤ)
    (e : associatedPageOneComplex E q ≅ C) :
    Nonempty ((E.page 2).X (p, q) ≅ C.homology p) := by
  refine ⟨?_⟩
  -- Proof comment: first rewrite the ambient page-two term as page-one homology, then transport
  -- through the fixed slice and the chosen comparison with `C`.
  exact
    (E.iso 1 2 (p, q)).symm ≪≫
      (associatedPageOneComplexHomologyIso E p q).symm ≪≫
        HomologicalComplex.homologyMapIso e p

/-- Helper for Remark 19.13.11: each stage of the truncation filtration on the chosen
representative of `M` is canonically the upper truncation `τ_{\le -p}`. -/
private theorem truncationPreimageStageFactors_ιTruncLE
    (M : DerivedCategory A) (p : ℤ) :
    ∃ φ : (((DerivedCategory.Q.objPreimage M).truncationFiltration).stage p) ⟶
        (DerivedCategory.Q.objPreimage M).truncLE (-p),
      φ ≫ (DerivedCategory.Q.objPreimage M).ιTruncLE (-p) =
        (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageInclusion p) ∧
          IsIso φ := by
  -- Proof comment: specialize the public truncation-filtration comparison from
  -- Remark `13.26.15` to the chosen representative of `M`.
  simpa using
    (CochainComplex.truncationFiltration_stageInclusion_factors_ιTruncLE
      (DerivedCategory.Q.objPreimage M) p)

/-- Helper for Remark 19.13.11: choose the canonical comparison between the `p`-th truncation
filtration stage and the upper truncation `τ_{\le -p}`. -/
private noncomputable def truncationPreimageStageIsoTruncLE
    (M : DerivedCategory A) (p : ℤ) :
    (((DerivedCategory.Q.objPreimage M).truncationFiltration).stage p) ≅
      (DerivedCategory.Q.objPreimage M).truncLE (-p) :=
  let φ := Classical.choose (truncationPreimageStageFactors_ιTruncLE (A := A) M p)
  letI :
      IsIso φ :=
    (Classical.choose_spec (truncationPreimageStageFactors_ιTruncLE (A := A) M p)).2
  asIso φ

/-- Helper for Remark 19.13.11: the chosen stage comparison factors the stage inclusion through
`ιTruncLE` on the nose. -/
private theorem truncationPreimageStageIsoTruncLE_hom_comp_ιTruncLE
    (M : DerivedCategory A) (p : ℤ) :
    (truncationPreimageStageIsoTruncLE (A := A) M p).hom ≫
        (DerivedCategory.Q.objPreimage M).ιTruncLE (-p) =
      (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageInclusion p) := by
  -- Proof comment: unpack the chosen factorization of the stage inclusion.
  exact
    (Classical.choose_spec
      (truncationPreimageStageFactors_ιTruncLE (A := A) M p)).1

/-- Helper for Remark 19.13.11: the adjacent upper truncation `τ_{\le j - 1}` is still strictly
bounded above in degree `j`. -/
private theorem preimageTruncLEStep_isStrictlyLE
    (M : DerivedCategory A) (j : ℤ) :
    ((DerivedCategory.Q.objPreimage M).truncLE (j - 1)).IsStrictlyLE j := by
  -- Proof comment: an upper truncation bounded in degree `j - 1` is automatically bounded in
  -- the larger degree `j`.
  exact
    ((DerivedCategory.Q.objPreimage M).truncLE (j - 1)).isStrictlyLE_of_le
      (j - 1) j (by omega)

/-- Helper for Remark 19.13.11: the canonical one-step upper truncation map
`τ_{\le j - 1}(Q.objPreimage M) ⟶ τ_{\le j}(Q.objPreimage M)`. -/
private noncomputable def preimageTruncLEStep
    (M : DerivedCategory A) (j : ℤ) :
    (DerivedCategory.Q.objPreimage M).truncLE (j - 1) ⟶
      (DerivedCategory.Q.objPreimage M).truncLE j :=
  letI := preimageTruncLEStep_isStrictlyLE (A := A) M j
  inv (((DerivedCategory.Q.objPreimage M).truncLE (j - 1)).ιTruncLE j) ≫
    CochainComplex.truncLEMap ((DerivedCategory.Q.objPreimage M).ιTruncLE (j - 1)) j

/-- Helper for Remark 19.13.11: the one-step upper truncation map composes with `ιTruncLE j` to
the earlier inclusion `ιTruncLE (j - 1)`. -/
private theorem preimageTruncLEStep_comp_ιTruncLE
    (M : DerivedCategory A) (j : ℤ) :
    preimageTruncLEStep (A := A) M j ≫ (DerivedCategory.Q.objPreimage M).ιTruncLE j =
      (DerivedCategory.Q.objPreimage M).ιTruncLE (j - 1) := by
  -- Proof comment: rewrite the step map by the naturality square for `ιTruncLE`, then cancel
  -- the inserted inverse.
  dsimp [preimageTruncLEStep]
  rw [Category.assoc,
    (CochainComplex.ιTruncLE_naturality
      ((DerivedCategory.Q.objPreimage M).ιTruncLE (j - 1)) j).symm]
  simp [Category.assoc]

/-- Helper for Remark 19.13.11: after identifying adjacent filtration stages with neighboring
upper truncations, the stage map becomes the canonical one-step truncation map. -/
private theorem truncationPreimageStageMap_comp_stageIsoTruncLE
    (M : DerivedCategory A) (p : ℤ) :
    (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageMapOfLE
        (show p ≤ p + 1 by omega)) ≫
        (truncationPreimageStageIsoTruncLE (A := A) M p).hom =
      (truncationPreimageStageIsoTruncLE (A := A) M (p + 1)).hom ≫
        preimageTruncLEStep (A := A) M (-p) := by
  -- Proof comment: compare both sides after postcomposing with `ιTruncLE (-p)`; the source side
  -- is the filtration compatibility square, and the target side is the one-step truncation
  -- factorization.
  apply (cancel_mono ((DerivedCategory.Q.objPreimage M).ιTruncLE (-p))).1
  calc
    ((((DerivedCategory.Q.objPreimage M).truncationFiltration).stageMapOfLE
        (show p ≤ p + 1 by omega)) ≫
          (truncationPreimageStageIsoTruncLE (A := A) M p).hom) ≫
            (DerivedCategory.Q.objPreimage M).ιTruncLE (-p)
      = (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageMapOfLE
          (show p ≤ p + 1 by omega)) ≫
            (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageInclusion p) := by
              rw [Category.assoc,
                truncationPreimageStageIsoTruncLE_hom_comp_ιTruncLE]
    _ = (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageInclusion (p + 1)) := by
          simpa using
            (FilteredComplex.stageMapOfLE_comp_stageInclusion
              (K := (DerivedCategory.Q.objPreimage M).truncationFiltration)
              (p := p) (q := p + 1) (by omega))
    _ = (truncationPreimageStageIsoTruncLE (A := A) M (p + 1)).hom ≫
          (DerivedCategory.Q.objPreimage M).ιTruncLE (-p - 1) := by
            rw [truncationPreimageStageIsoTruncLE_hom_comp_ιTruncLE]
            simp
    _ = ((truncationPreimageStageIsoTruncLE (A := A) M (p + 1)).hom ≫
          preimageTruncLEStep (A := A) M (-p)) ≫
            (DerivedCategory.Q.objPreimage M).ιTruncLE (-p) := by
              rw [Category.assoc, preimageTruncLEStep_comp_ιTruncLE]

/-- Helper for Remark 19.13.11: the `p`-th graded piece of the truncation filtration is the
cokernel of the corresponding one-step upper truncation map on the chosen representative of
`M`. -/
private theorem qObjGradedPieceTruncationPreimageIsoQObjCokernelPreimageTruncLEStep
    (M : DerivedCategory A) (p : ℤ) :
    Nonempty ((DerivedCategory.Q).obj
        (((DerivedCategory.Q.objPreimage M).truncationFiltration).gradedPiece p) ≅
      (DerivedCategory.Q).obj (cokernel (preimageTruncLEStep (A := A) M (-p)))) := by
  let eCokernel :
      (((DerivedCategory.Q.objPreimage M).truncationFiltration).gradedPiece p) ≅
        cokernel (preimageTruncLEStep (A := A) M (-p)) := by
    -- Proof comment: the graded piece is the cokernel of the adjacent stage map, and
    -- `cokernel.mapIso` rewrites that map through the chosen identifications with neighboring
    -- upper truncations.
    simpa [FilteredComplex.gradedPiece, DecreasingFiltration.gradedPiece] using
      (cokernel.mapIso
        (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageMapOfLE
          (show p ≤ p + 1 by omega))
        (preimageTruncLEStep (A := A) M (-p))
        (truncationPreimageStageIsoTruncLE (A := A) M (p + 1))
        (truncationPreimageStageIsoTruncLE (A := A) M p)
        (truncationPreimageStageMap_comp_stageIsoTruncLE (A := A) M p))
  -- Proof comment: apply the derived-category quotient functor to the concrete cokernel
  -- comparison.
  exact ⟨DerivedCategory.Q.mapIso eCokernel⟩

/-- Helper for Remark 19.13.11: the raw source `E₁` term at coordinates `(-j, i + 2j)` can be
rewritten using the concrete cokernel model for the relevant truncation-filtration graded piece.
-/
private theorem rawPageOneIsoQObjCokernelPreimageTruncLEStep
    (M K : DerivedCategory A) (i j : ℤ) :
    Nonempty
      ((((truncationSourceExtSpectralSequenceData (A := A) M K).spectralSequence.page 1).X
          (-j, i + 2 * j)) ≅
        derivedExtGroup
          ((DerivedCategory.Q).obj (cokernel (preimageTruncLEStep (A := A) M j))) K (i + j)) := by
  let S := truncationSourceExtSpectralSequenceData (A := A) M K
  obtain ⟨eGraded⟩ :=
    qObjGradedPieceTruncationPreimageIsoQObjCokernelPreimageTruncLEStep
      (A := A) M (-j)
  refine ⟨?_⟩
  -- Proof comment: first normalize the source page-one formula at the affine coordinates, then
  -- transport the graded-piece term along the concrete cokernel identification.
  exact
    (by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (S.pageOneIso (-j) (i + 2 * j))) ≪≫
      derivedExtGroupIsoOfSourceIso eGraded (K := K) (n := i + j)

/-- Helper for Remark 19.13.11: after the affine coordinate change `(i, j) ↦ (-j, i + 2j)`, the
renumbered page-two term is already the raw source page-one term rewritten above. -/
private theorem renumberedPageTwoIsoOfRawPageOneNegSwap
    (M K : DerivedCategory A) (i j : ℤ) :
    Nonempty
      (((renumberedPositivePage
          (truncationSourceExtSpectralSequenceData (A := A) M K).spectralSequence 2
          (by omega)).X (i, j)) ≅
        derivedExtGroup (derivedCohomologyAsDerivedObject M (-j)) K i) := by
  -- Proof comment: at page `r = 2`, the renumbered positive-page object is definitionally the
  -- source page `1`, so the earlier raw page-one comparison closes the transformed statement.
  simpa [renumberedPositivePage] using
    rawPageOneIsoQObjCokernelPreimageTruncLEStep (A := A) M K i j

/-- Helper for Remark 19.13.11: the `p`-th stagewise quotient of the truncation filtration is the
cokernel of the corresponding stage inclusion. -/
private noncomputable def truncationPreimageQuotientIsoCokernelStageInclusion
    (M : DerivedCategory A) (p : ℤ) :
    (((DerivedCategory.Q.objPreimage M).truncationFiltration).quotient p) ≅
      cokernel (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageInclusion p) :=
  -- Proof comment: the quotient complex is defined degreewise by the cokernels of the stage
  -- inclusion maps, so the global cokernel comparison is definitional.
  eqToIso rfl

/-- Helper for Remark 19.13.11: after identifying the `p`-th truncation-filtration stage with the
upper truncation `τ_{\le -p}`, the corresponding quotient becomes the cokernel of `ιTruncLE`. -/
private noncomputable def truncationPreimageQuotientIsoCokernelTruncLE
    (M : DerivedCategory A) (p : ℤ) :
    (((DerivedCategory.Q.objPreimage M).truncationFiltration).quotient p) ≅
      cokernel ((DerivedCategory.Q.objPreimage M).ιTruncLE (-p)) :=
  -- Proof comment: rewrite the stage inclusion through the chosen stage-to-truncation
  -- isomorphism, then transport the quotient along `cokernel.mapIso`.
  truncationPreimageQuotientIsoCokernelStageInclusion (A := A) M p ≪≫
    (cokernel.mapIso
      (((DerivedCategory.Q.objPreimage M).truncationFiltration).stageInclusion p)
      ((DerivedCategory.Q.objPreimage M).ιTruncLE (-p))
      (Iso.refl _)
      (truncationPreimageStageIsoTruncLE (A := A) M p)
      (by
        simpa using
          (truncationPreimageStageIsoTruncLE_hom_comp_ιTruncLE (A := A) M p).symm))

/-- Helper for Remark 19.13.11: the derived image of the `p`-th truncation-filtration quotient is
the derived image of the cokernel of `ιTruncLE (-p)`. -/
private theorem qObjTruncationPreimageQuotientIsoQObjCokernelTruncLE
    (M : DerivedCategory A) (p : ℤ) :
    Nonempty
      ((DerivedCategory.Q).obj
          (((DerivedCategory.Q.objPreimage M).truncationFiltration).quotient p) ≅
        (DerivedCategory.Q).obj
          (cokernel ((DerivedCategory.Q.objPreimage M).ιTruncLE (-p)))) := by
  -- Proof comment: apply the derived quotient functor to the concrete quotient-cokernel
  -- comparison obtained above.
  exact ⟨(DerivedCategory.Q.mapIso
    (truncationPreimageQuotientIsoCokernelTruncLE (A := A) M p))⟩

-- Proof sketch: choose a complex representing `M`, filter it by the canonical truncations
-- `τ_{\le -p}`, apply Remark 19.13.8 to the resulting filtered Hom complex, and then renumber
-- the indices by `p = -j` and `q = i + 2j`. The resulting spectral sequence depends only on the
-- derived object `M`, not on the chosen representative, because quasi-isomorphic representatives
-- have canonically identified cohomology objects and give isomorphic filtered-Hom constructions.
/-- Remark 19.13.11: for objects `M, K` of the derived category of a Grothendieck abelian
category, there is a renumbered spectral sequence with `E'_2{}^{\, i, j} = Ext^i(H^{-j}(M), K)`;
if `M ∈ D^-(A)` and `K ∈ D^+(A)`, then this spectral sequence is bounded and converges to
`Ext^{i + j}(M, K)`. In this file, the chosen spectral sequence is packaged as
`DerivedExtCohomologySpectralSequenceData M K`. -/
@[stacks 0G20]
theorem derivedExt_cohomology_spectralSequence_exists
    (M K : DerivedCategory A) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := by
  let S := truncationSourceExtSpectralSequenceData (A := A) M K
  -- Route correction: this wrapper has to come from the source-owner filtered-complex package of
  -- Remark 19.13.10, not from the synthetic page-two package of Remark 19.13.9, because the
  -- target structure stores an actual filtered complex together with `associated` and
  -- `convergesToCohomology`.
  have habutment :
      ∀ n : ℤ,
        addCommGrpFilteredComplexCohomologyObject S.filteredHomComplex n ≅
          derivedExtGroup M K n :=
    truncationSourceAbutmentIso (A := A) M K
  -- Proof comment: the source-owner filtered complex and its abutment transport are already
  -- canonical, so the remaining work is localized to the page-two identification and the
  -- boundedness-to-convergence bridge.
  refine ⟨{
    filteredComplex := S.filteredHomComplex
    spectralSequence := S.spectralSequence
    associated := inferInstance
    pageTwoIso := ?_
    abutmentIso := habutment
    converges_of_boundedness := ?_
  }⟩
  · intro i j
    -- TODO: the direct owner `S.spectralSequence` has the wrong page-two indexing
    -- `E₂^{p,q} = Ext^{2p + q}(H^{-p}(M), K)`, so this field must use a genuinely renumbered
    -- zero-based owner. The local blocker is structural: this file has `renumberedPositivePage`
    -- and the page-zero notes from `Remark_12_22_6_Variant`, but no public constructor turning
    -- that positive-page family plus a page-one comparison into a
    -- `CohomologicalSpectralSequence AddCommGrpCat 0` together with an `associated` witness.
    sorry
  · intro hM hK
    -- TODO: convergence should still be proved on the unrenumbered source owner `S` via
    -- `S.converges_of_eventualQuotientExt_control`, but the remaining blocker is the missing
    -- public bridge identifying the quotient stages of
    -- `((DerivedCategory.Q.objPreimage M).truncationFiltration)` with the lower-tail truncation
    -- objects needed for the eventual vanishing/stabilization arguments.
    sorry

-- Proof sketch: filter the chosen cochain complex `M^•` by the stupid truncations
-- `σ_{\ge p} M^•`, apply Remark 19.13.8 to the resulting filtered Hom complex, and identify the
-- graded pieces of the filtration with the single-term complexes `M^{-p}[p]`. If `M^•` is
-- bounded above and `K ∈ D^+(A)`, the same boundedness argument gives convergence to
-- `Ext^*(DerivedCategory.Q.obj M, K)`.
/-- The stupid-filtration spectral sequence associated to a cochain complex `M^•` has
`E_1^{p,q} = Ext^q(M^{-p}, K)` and converges to `Ext^{p + q}(M, K)` when `M^•` is bounded above
and `K ∈ D^+(A)`. -/
theorem derivedExt_stupidFiltration_spectralSequence_exists
    (M : CochainComplex A ℤ) (K : DerivedCategory A) :
    Nonempty (DerivedExtStupidFiltrationSpectralSequenceData M K) := by
  let S := stupidSourceExtSpectralSequenceData (A := A) M K
  -- Proof comment: keep the source-owner filtered Hom complex and its associated spectral
  -- sequence from Remark 19.13.10, then transport the page-one and convergence fields.
  refine ⟨{
    filteredComplex := S.filteredHomComplex
    spectralSequence := S.spectralSequence
    associated := inferInstance
    pageOneIso := ?_
    abutmentIso := S.abutmentIso
    converges_of_boundedness := ?_
  }⟩
  · intro p q
    -- Proof comment: try the direct owner page-one identification first; if the graded-piece
    -- model is already definitionally the single-term complex, `simpa` closes the goal.
    simpa [cochainTermAsDerivedObject] using S.pageOneIso p q
  · intro hM hK
    -- Proof comment: the stupid filtration has finite filtrations, so the associated spectral
    -- sequence converges to the cohomology of the filtered Hom complex by the Chapter 12 owner
    -- theorem.
    exact
      FilteredComplex.convergesToCohomology_of_hasFiniteFiltrations
        S.filteredHomComplex S.spectralSequence
        (CochainComplex.stupidFiltration_hasFiniteFiltrations M)

end CategoryTheory
