import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksProject_2024.Chap04.Definition_4_22_1
import StacksProject_2024.Chap04.Definition_4_22_2
import StacksProject_2024.Chap04.Lemma_4_22_3
import StacksProject_2024.Chap04.Lemma_4_22_9
import StacksProject_2024.Chap04.Lemma_4_22_11
import StacksProject_2024.Chap13.Lemma_13_14_3
import StacksProject_2024.Chap13.Lemma_13_14_6
import StacksProject_2024.Chap13.Remark_13_12_4
import StacksProject_2024.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "H" => DerivedCategory.homologyFunctor ℬ

/-- Helper for Lemma 13.16.1: an isomorphism in `D(\mathcal B)` preserves the same lower
cohomological bound `a`. -/
lemma isGE_of_iso
    {X Y : DerivedCategory ℬ} (a : ℤ) (e : X ≅ Y) (hY : Y.IsGE a) :
    X.IsGE a := by
  rw [DerivedCategory.isGE_iff] at hY ⊢
  intro i hi
  -- Proof comment: transport the vanishing of `H^i(Y)` across the induced homology isomorphism.
  exact IsZero.of_iso (hY i hi) ((H i).mapIso e)

/-- Helper for Lemma 13.16.1: a retract of an object of `D(\mathcal B)^{≥ a}` is still in
`D(\mathcal B)^{≥ a}`. -/
lemma isGE_of_split_epi_from_isGE_stage
    (a : ℤ) {X Y : DerivedCategory ℬ} (σ : X ⟶ Y) (π : Y ⟶ X)
    (hsplit : σ ≫ π = 𝟙 X) (hY : Y.IsGE a) :
    X.IsGE a := by
  rw [DerivedCategory.isGE_iff] at hY ⊢
  intro i hi
  have hYi : IsZero ((H i).obj Y) := hY i hi
  -- Proof comment: the homology object of `X` is a retract of the zero homology object of `Y`.
  letI : IsSplitMono ((H i).map σ) := IsSplitMono.mk' ⟨(H i).map π, by
    simpa [Functor.map_comp] using congrArg ((H i).map) hsplit⟩
  exact IsZero.of_mono ((H i).map σ) hYi

/-- Helper for Lemma 13.16.1: the canonical map `K ⟶ τ_{\ge a}K` is a quasi-isomorphism as soon
as `K` has vanishing cohomology below `a`. -/
lemma quasiIso_piTruncGE_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) (hGE : K.IsGE a) :
    QuasiIso (K.πTruncGE a) := by
  letI : K.IsGE a := hGE
  -- Proof comment: mathlib already packages the canonical lower truncation map as a
  -- quasi-isomorphism under the `IsGE` hypothesis.
  infer_instance

/-- Helper for Lemma 13.16.1: a quasi-isomorphism out of a complex bounded below by `a`
transfers the same lower cohomological bound to the target complex. -/
lemma isGE_of_quasiIso_target
    (a : ℤ) {K L : CochainComplex 𝒜 ℤ} (s : K ⟶ L)
    (hsQ : Qis ((Q).map s)) (hK : K.IsGE a) :
    L.IsGE a := by
  sorry

/-- Helper for Lemma 13.16.1: if a cochain complex is strictly zero below `a`, then after
applying `F` termwise and passing to the derived category its image lies in `D(\mathcal B)^{≥ a}`.
-/
lemma mapHomotopyCategoryToDerived_obj_isGE_of_isStrictlyGE
    (a : ℤ) (L : CochainComplex 𝒜 ℤ) (hL : L.IsStrictlyGE a) :
    ((KtoD).obj ((Q).obj L)).IsGE a := by
  let M : CochainComplex ℬ ℤ := ((F.mapHomologicalComplex (up ℤ)).obj L)
  have hM : M.IsStrictlyGE a := by
    -- Proof comment: additivity preserves zero objects termwise, so the mapped complex keeps the
    -- same strict lower support bound.
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hLi : IsZero (L.X i) := by
      letI : L.IsStrictlyGE a := hL
      exact L.isZero_of_isStrictlyGE a i hi
    simpa [M, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using F.map_isZero hLi
  letI : M.IsStrictlyGE a := hM
  letI : M.IsGE a := inferInstance
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have hMi : IsZero (M.homology i) := M.isZero_of_isGE a i hi
  have hHomotopy :
      IsZero
        (((HomotopyCategory.homologyFunctor ℬ (up ℤ) i).obj
          ((F.mapHomotopyCategory (up ℤ)).obj ((Q).obj L)))) := by
    -- Proof comment: first identify homotopy-category homology with the homology of the mapped
    -- complex, then insert the vanishing just proved.
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, M] using
      (((HomotopyCategory.homologyFunctorFactors ℬ (up ℤ) i).app M).isZero_iff).2 hMi
  -- Proof comment: pass from the homotopy quotient to the derived category via the canonical
  -- comparison for the derived homology functor.
  exact
    (((DerivedCategory.homologyFunctorFactorsh ℬ i).app
      ((F.mapHomotopyCategory (up ℤ)).obj ((Q).obj L))).isZero_iff).2 hHomotopy

/-- Helper for Lemma 13.16.1: the bounded-below truncation stage `τ_{\ge a}K` is already a
pointwise-defined stage for the right derived functor whenever `RF` is defined at `K`. -/
lemma hasPointwiseRightDerivedFunctorAt_truncGE_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) (hGE : K.IsGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)] :
    Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj (K.truncGE a)) := by
  sorry

/-- Helper for Lemma 13.16.1: after truncating below at `a`, the resulting stage already lies in
`D(\mathcal B)^{≥ a}`. -/
lemma mapHomotopyCategoryToDerived_obj_truncGE_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) :
    ((KtoD).obj ((Q).obj (K.truncGE a))).IsGE a := by
  -- Proof comment: the smart truncation is strictly zero below `a`, so the previous bounded-stage
  -- lemma applies directly.
  exact
    mapHomotopyCategoryToDerived_obj_isGE_of_isStrictlyGE
      (F := F) a (K.truncGE a) inferInstance

/-- Helper for Lemma 13.16.1: a split leg from `RF(K)` to a strictly bounded-below denominator
stage forces `RF(K)` itself to lie in `D(\mathcal B)^{≥ a}`. -/
lemma rightDerivedValue_isGE_of_split_stage
    (a : ℤ) (K L : CochainComplex 𝒜 ℤ)
    (s : K ⟶ L) (hsQ : Qis ((Q).map s)) (hL : L.IsStrictlyGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)]
    (σ : rightDerivedValue Qis KtoD ((Q).obj K) ⟶ (KtoD).obj ((Q).obj L))
    (hσ :
      σ ≫ rightDerivedValueLeg Qis KtoD ((Q).map s) hsQ = 𝟙
        (rightDerivedValue Qis KtoD ((Q).obj K))) :
    (rightDerivedValue Qis KtoD ((Q).obj K)).IsGE a := by
  sorry

/-- Helper for Lemma 13.16.1: a right fraction in the homotopy localization can be replaced by a
common-target denominator square after passing to the opposite category and back. -/
lemma right_fraction_exists_target_denominator_square
    {A X : HomotopyCategory 𝒜 (up ℤ)}
    (ψ : MorphismProperty.RightFraction Qis A X) :
    ∃ (X' : HomotopyCategory 𝒜 (up ℤ)) (s : X ⟶ X') (_ : Qis s) (f : A ⟶ X'),
      ψ.s ≫ f = ψ.f ≫ s := by
  sorry

/-- Helper for Lemma 13.16.1: every ambient denominator object over `K` maps to one coming from
an actual quasi-isomorphism denominator out of `K`. -/
lemma costructuredArrow_exists_hom_to_denominator
    (K : CochainComplex 𝒜 ℤ)
    (g : CostructuredArrow (Qis).Q ((Qis).Q.obj ((Q).obj K))) :
    ∃ (L : HomotopyCategory 𝒜 (up ℤ)) (s : (Q).obj K ⟶ L) (hs : Qis s),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom (Qis).Q Qis s hs).inv)) := by
  sorry

/-- Helper for Lemma 13.16.1: every ambient denominator stage over `K` refines to an actual
quasi-isomorphic stage whose target complex is strictly zero below `a`. -/
lemma costructuredArrow_exists_hom_to_strictly_ge_denominator
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) (hGE : K.IsGE a)
    (g : CostructuredArrow (Qis).Q ((Qis).Q.obj ((Q).obj K))) :
    ∃ (L : CochainComplex 𝒜 ℤ) (s : K ⟶ L)
      (hsQ : Qis ((Q).map s)) (hL : L.IsStrictlyGE a),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom (Qis).Q Qis ((Q).map s) hsQ).inv)) := by
  sorry

/-- Helper for Lemma 13.16.1: the full subcategory of denominator stages over `K` whose target
complex is strictly zero below `a`. -/
abbrev strictly_ge_denominator_property
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) :
    ObjectProperty (CostructuredArrow (Qis).Q ((Qis).Q.obj ((Q).obj K))) :=
  fun U ↦
    let L : CochainComplex 𝒜 ℤ := U.left.as
    L.IsStrictlyGE a

/-- Helper for Lemma 13.16.1: the inclusion of strictly bounded-below denominator stages into the
ambient denominator category over `K` is final. -/
lemma strictly_ge_denominator_inclusion_final
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) (hGE : K.IsGE a) :
    Functor.Final
      (ObjectProperty.ι (strictly_ge_denominator_property (𝒜 := 𝒜) a K)) := by
  sorry

/-- Helper for Lemma 13.16.1: the ambient denominator diagram computing `RF(K)` is essentially
constant whenever the pointwise right derived functor is defined at `K`. -/
lemma ambient_denominator_diagram_is_essentially_constant
    (K : CochainComplex 𝒜 ℤ)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)] :
    IsEssentiallyConstantFilteredDiagram
      (CostructuredArrow.proj (Qis).Q ((Qis).Q.obj ((Q).obj K)) ⋙ KtoD) := by
  sorry

/-- Helper for Lemma 13.16.1: after restricting to denominator stages whose targets are strictly
zero below `a`, the right-derived denominator diagram is still essentially constant. -/
lemma strictly_ge_restricted_diagram_is_essentially_constant
    (a : ℤ) (K : CochainComplex 𝒜 ℤ) (hGE : K.IsGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)] :
    IsEssentiallyConstantFilteredDiagram
      (ObjectProperty.ι (strictly_ge_denominator_property (𝒜 := 𝒜) a K) ⋙
        CostructuredArrow.proj (Qis).Q ((Qis).Q.obj ((Q).obj K)) ⋙ KtoD) := by
  sorry

/-- Helper for Lemma 13.16.1: the point of an essentially constant colimit cocone on the strict
denominator subdiagram lies in `D(\mathcal B)^{≥ a}`. -/
lemma isGE_of_essentially_constant_strictly_ge_colimit
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (c :
      ColimitCocone
        (ObjectProperty.ι (strictly_ge_denominator_property (𝒜 := 𝒜) a K) ⋙
          CostructuredArrow.proj (Qis).Q ((Qis).Q.obj ((Q).obj K)) ⋙ KtoD))
    (hc : IsEssentiallyConstantFilteredCocone c.cocone) :
    c.cocone.pt.IsGE a := by
  sorry

/-- Helper for Lemma 13.16.1: in a distinguished triangle whose third vertex lies in
`D(\mathcal B)^{≥ a + 1}`, the first morphism induces cohomology isomorphisms in every
degree `i ≤ a`. -/
lemma isIso_homologyMap_mor₁_of_distTriang_obj₃_isGE
    (a : ℤ) (T : Pretriangulated.Triangle (DerivedCategory ℬ))
    (hT : T ∈ distTriang (DerivedCategory ℬ))
    (h₃ : T.obj₃.IsGE (a + 1))
    (i : ℤ) (hi : i ≤ a) :
    IsIso ((H i).map T.mor₁) := by
  have hmor₂_zero : (H i).map T.mor₂ = 0 := by
    -- Proof comment: the third vertex has no degree-`i` cohomology because `i < a + 1`.
    letI : T.obj₃.IsGE (a + 1) := h₃
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) i (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (i - 1) i (by omega) = 0 := by
    -- Proof comment: the connecting morphism starts from another vanishing cohomology group of
    -- the third vertex.
    letI : T.obj₃.IsGE (a + 1) := h₃
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) (i - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H i).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
  letI : Mono ((H i).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2 hδ_zero
  exact isIso_of_mono_of_epi ((H i).map T.mor₁)

/- Domain-style sampling:
- primary domain: pointwise right derived functors on homotopy categories together with the
  canonical t-structure boundedness predicates on cochain complexes and derived categories;
- sampled owner declarations:
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.rightDerivedValueMap`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `CochainComplex.isGE_iff`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.isGE_iff`;
- owner abstraction:
  `source-facing`: the three lemmas about derived boundedness and truncation;
  `core/canonical`: `rightDerivedValue`, `rightDerivedValueMap`, and `IsGE`;
  `bridge/view`: the cohomology-vanishing reformulation below. -/

-- Proof sketch: replace `K` by a bounded-below complex quasi-isomorphic to it using
-- Lemma 13.15.5, observe that applying `F` termwise to such a bounded-below representative stays
-- zero in degrees below `a`, and use the cofinality description of the pointwise right derived
-- value to conclude the same vanishing for `RF(K)`.
/-- Lemma 13.16.1 (1): if a cochain complex `K` is bounded below by `a` in the canonical
cohomological sense and the right derived functor of `K(\mathcal A) ⥤ D(\mathcal B)` induced by
`F` is defined at `K`, then `RF(K)` is bounded below by the same integer `a`. -/
theorem rightDerivedValue_isGE_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hGE : K.IsGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)] :
    (rightDerivedValue Qis KtoD ((Q).obj K)).IsGE a := by
  sorry

/-- Companion to Lemma 13.16.1 (1): the canonical bounded-below conclusion implies the textbook
degreewise vanishing statement for cohomology in every degree `< a`. -/
theorem rightDerivedValue_isZero_homology_below_of_isGE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    (hGE : K.IsGE a)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)]
    (i : ℤ) (hi : i < a) :
    IsZero ((H i).obj (rightDerivedValue Qis KtoD ((Q).obj K))) := by
  -- Proof comment: once part (1) puts `RF(K)` in `D(\mathcal B)^{≥ a}`, lower cohomology
  -- vanishes by the defining `t`-structure bound.
  let hRF : (rightDerivedValue Qis KtoD ((Q).obj K)).IsGE a :=
    rightDerivedValue_isGE_of_isGE (F := F) a K hGE
  letI : (rightDerivedValue Qis KtoD ((Q).obj K)).IsGE a := hRF
  exact DerivedCategory.isZero_of_isGE
    (rightDerivedValue Qis KtoD ((Q).obj K)) a i hi

-- Proof sketch: compare `K.truncLE a`, `K`, and `K.truncGE (a + 1)` by the standard truncation
-- triangle, transport pointwise right-derived existence across that triangle, and then use the
-- long exact cohomology sequence together with part (1) applied to `K.truncGE (a + 1)`.
/-- Lemma 13.16.1 (2): if the right derived functor induced by `F` is defined at `K` and at
`τ_{\le a}K`, then the canonical map `RF(τ_{\le a}K) ⟶ RF(K)` induces an isomorphism on
cohomology in every degree `i ≤ a`. -/
theorem rightDerivedValue_homologyMap_isIso_of_truncLE
    (a : ℤ) (K : CochainComplex 𝒜 ℤ)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj K)]
    [Functor.HasPointwiseRightDerivedFunctorAt KtoD Qis ((Q).obj (K.truncLE a))]
    (i : ℤ) (hi : i ≤ a) :
    IsIso
      ((H i).map (rightDerivedValueMap Qis KtoD ((Q).map (K.ιTruncLE a)))) := by
  sorry

end

end CategoryTheory
