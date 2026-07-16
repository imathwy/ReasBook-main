import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_9
import StacksProject_2024.stacks_project.Chap13.Lemma_13_26_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_26_6

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian (finiteFilteredObjectCat 𝒜)]

local instance instCategoryWithHomologyGradedObjectInt_13_26_8 :
    CategoryWithHomology (GradedObject ℤ 𝒜) := by
  have hzero : (Preadditive.preadditiveHasZeroMorphisms :
      HasZeroMorphisms (GradedObject ℤ 𝒜)) = GradedObject.hasZeroMorphisms ℤ :=
    HasZeroMorphisms.ext _ _
  exact hzero ▸
    (@_root_.CategoryTheory.categoryWithHomology_of_abelian (GradedObject ℤ 𝒜) _ _)

namespace CochainComplex

local notation "FilF" => Fil^f(𝒜)
local notation "FiltInjPlus" => FilteredInjectivePlus 𝒜
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)
local notation "ιFiltInjPlus" => CochainComplex.PlusWithTermsIn.ι IsFilteredInjective
private abbrev assocGraded := finiteFilteredObjectAssociatedGradedCochainFunctor 𝒜

/- Domain-style sampling for Lemma `13.26.8`.
- primary domain: horseshoe diagrams in the bounded-below filtered-complex category
  `CochainComplex.Plus (Fil^f(𝒜))`, with filtered-injective rows and filtered quasi-isomorphism
  comparison maps;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CategoryTheory.ShortComplex`,
  `ShortComplex.Hom`,
  `ShortComplex.ShortExact`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`;
- best owner abstraction: the lower row is canonically owned by
  `ShortComplex (CochainComplex.FilteredInjectivePlus 𝒜)`, its comparison with the degree-zero
  short exact sequence is owned by `ShortComplex.Hom`, and short exactness is owned by
  `ShortComplex.ShortExact`, while the source-facing termwise-split conclusion is owned by the
  degreewise family `∀ n, (T.map (HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting`
  on the underlying short complex `T`;
- primitive data: the prescribed outer filtered-injective complexes and outer vertical maps, a
  lower short complex in `CochainComplex.FilteredInjectivePlus 𝒜`, and the comparison morphism
  from `S.map single₀` to its image after applying the canonical inclusion
  `CochainComplex.PlusWithTermsIn.ι`, together with the
  degreewise splitting of the lower row;
- derived API: the lower-row short exactness deduced from the degreewise splitting family, and the
  middle filtered quasi-isomorphism deduced from that short exactness plus the outer filtered
  quasi-isomorphisms;
- source/core/bridge triage:
  `source-facing`: the existence theorem below, stated with prescribed outer filtered
    quasi-isomorphisms and an explicit degreewise-splitting conclusion;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`,
    `CochainComplex.PlusWithTermsIn.ι`,
    `ShortComplex`, `ShortComplex.Hom`, `ShortComplex.ShortExact`, and the associated-graded
    functor on `CochainComplex (Fil^f(𝒜)) ℤ`;
  `bridge/view`: the canonical bounded-below inclusion
    `CochainComplex.PlusWithTermsIn.ι`. -/

omit [EnoughInjectives 𝒜] in
/-- For a morphism between two short exact rows, if the outer vertical components are filtered
quasi-isomorphisms, then so is the middle component. -/
theorem quasiIso_middle {S : ShortComplex FilF} (hS : S.ShortExact)
    {T : ShortComplex FiltInjPlus} (φ : S.map single₀ ⟶ T.map ιFiltInjPlus)
    (hrow : (T.map ιFiltInjPlus).ShortExact)
    (hτ₁ : QuasiIso (assocGraded.map φ.τ₁))
    (hτ₃ : QuasiIso (assocGraded.map φ.τ₃)) :
    QuasiIso (assocGraded.map φ.τ₂) := by
  -- First pass to cochain complexes over `Fil^f(𝒜)`: the source short exact row lives in degree
  -- zero, and the target row already lives in bounded-below filtered-injective complexes.
  let hsingle : (S.map single₀).ShortExact :=
    @ShortComplex.ShortExact.map_of_exact
      FilF (CochainComplex FilF ℤ) _ _
      (Preadditive.preadditiveHasZeroMorphisms)
      (Preadditive.preadditiveHasZeroMorphisms) S hS
      single₀ inferInstance inferInstance inferInstance
  -- Then pass both rows to associated-graded complexes, where the ordinary middle-column
  -- quasi-isomorphism theorem applies.
  let hsingleGraded : ((S.map single₀).map assocGraded).ShortExact :=
    hsingle.map_of_exact assocGraded
  let hrowGraded : ((T.map ιFiltInjPlus).map assocGraded).ShortExact :=
    hrow.map_of_exact assocGraded
  simpa using
    CochainComplex.quasiIso_tau₂_of_shortExact
      (𝒜 := GradedObject ℤ 𝒜) hsingleGraded hrowGraded (φ.map assocGraded) hτ₁ hτ₃

/-- Helper for Lemma 13.26.8: once the left map of the given short exact sequence is known to be
strict, the degree-zero comparison map `A ⟶ I⁰` extends across `A ⟶ B`. -/
private theorem exists_degree_zero_extension_of_strict_left_map
    {S : ShortComplex FilF} (hS : S.ShortExact)
    {I : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (hf_strict : FilteredObject.Hom.Strict S.f.hom) :
    ∃ b₀ : S.X₂ ⟶ (I : CochainComplex FilF ℤ).X 0, S.f ≫ b₀ = a.f 0 := by
  letI : Mono S.f := hS.mono_f
  letI : IsFilteredInjective ((I : CochainComplex FilF ℤ).X 0) := I.property 0
  -- Proof comment: this is exactly the first extension step in the source proof, now delegated to
  -- Lemma `13.26.4`.
  obtain ⟨b₀, hb₀⟩ := IsFilteredInjective.factors (f := a.f 0) (u := S.f) hf_strict
  exact ⟨b₀, hb₀⟩

/-- Helper for Lemma 13.26.8: any degree-zero lift `b₀ : B ⟶ I⁰` extending `a.f 0` produces the
descended map `\bar b : C ⟶ I¹` forced by the cokernel description of `B ⟶ C`. -/
private theorem exists_degree_one_descend_of_degree_zero_extension
    {S : ShortComplex FilF} (hS : S.ShortExact)
    {I : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    {b₀ : S.X₂ ⟶ (I : CochainComplex FilF ℤ).X 0}
    (hb₀ : S.f ≫ b₀ = a.f 0) :
    ∃ bar_b : S.X₃ ⟶ (I : CochainComplex FilF ℤ).X 1,
      S.g ≫ bar_b = b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1 := by
  obtain ⟨hCok⟩ := (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hS.exact, hS.epi_g⟩
  have hzero : S.f ≫ (b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1) = 0 := by
    -- Proof comment: rewrite through the chosen extension and then use that `a` is a cochain map
    -- out of the degree-zero single complex.
    calc
      S.f ≫ (b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1) =
          (S.f ≫ b₀) ≫ (I : CochainComplex FilF ℤ).d 0 1 := by
            simp [Category.assoc]
      _ = a.f 0 ≫ (I : CochainComplex FilF ℤ).d 0 1 := by
            rw [hb₀]
      _ = 0 := by
            simpa using (a.comm 0 1 (by simp))
  let bar_b : S.X₃ ⟶ (I : CochainComplex FilF ℤ).X 1 :=
    hCok.desc (Limits.CokernelCofork.ofπ (b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1) hzero)
  refine ⟨bar_b, ?_⟩
  -- Proof comment: the descended morphism is characterized by the cokernel universal property.
  simpa [bar_b] using
    hCok.fac (Limits.CokernelCofork.ofπ (b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1) hzero)
      WalkingParallelPair.one

/-- Helper for Lemma 13.26.8: once the right degree-zero map `C ⟶ J⁰` is known to be a strict
monomorphism, the descended map `C ⟶ I¹` extends to the first connecting morphism `J⁰ ⟶ I¹`. -/
private theorem exists_initial_connecting_morphism_of_strict_right_map
    {S : ShortComplex FilF} (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    {b₀ : S.X₂ ⟶ (I : CochainComplex FilF ℤ).X 0}
    (hb₀ : S.f ≫ b₀ = a.f 0)
    [Mono (c.f 0)]
    (hc_strict : FilteredObject.Hom.Strict (c.f 0).hom) :
    ∃ δ₀ : (J : CochainComplex FilF ℤ).X 0 ⟶ (I : CochainComplex FilF ℤ).X 1,
    S.g ≫ c.f 0 ≫ δ₀ = b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1 := by
  obtain ⟨bar_b, hbar_b⟩ :=
    exists_degree_one_descend_of_degree_zero_extension (S := S) hS (I := I) a hb₀
  letI : IsFilteredInjective ((I : CochainComplex FilF ℤ).X 1) := I.property 1
  -- Proof comment: this is the second strict-extension step in the source proof, now across
  -- the degree-zero strict monomorphism `c.f 0`.
  obtain ⟨δ₀, hδ₀⟩ := IsFilteredInjective.factors (f := bar_b) (u := c.f 0) hc_strict
  refine ⟨δ₀, ?_⟩
  calc
    S.g ≫ c.f 0 ≫ δ₀ = S.g ≫ bar_b := by
      simp [Category.assoc, hδ₀]
    _ = b₀ ≫ (I : CochainComplex FilF ℤ).d 0 1 := hbar_b

/-- Helper for Lemma 13.26.8: the two structure maps in a short exact sequence of finite filtered
objects are strict. -/
private theorem shortExact_strict_maps
    {S : ShortComplex FilF} (hS : S.ShortExact) :
    FilteredObject.Hom.Strict S.f.hom ∧ FilteredObject.Hom.Strict S.g.hom := by
  let iFin :
      FilF ⥤ FilteredObject 𝒜 :=
    ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))
  let hSFil : (S.map iFin).ShortExact := hS.map_of_exact iFin
  let hSGr :
      ((S.map iFin).map ShortComplex.associatedGradedFunctor).ShortExact :=
    hSFil.map_of_exact ShortComplex.associatedGradedFunctor
  -- Proof comment: once the filtered short exact row is viewed in the ambient filtered category,
  -- Lemma `12.19.15` upgrades exactness of the associated graded row to strictness of both maps.
  simpa [iFin] using
    (ShortComplex.strict_of_associatedGraded_exact
      (S := S.map iFin) S.X₁.property S.X₂.property S.X₃.property hSGr.exact)

/-- Helper for Lemma 13.26.8: after taking associated graded, a degree-zero single complex has
vanishing homology in every positive degree. -/
private theorem associatedGraded_single_homology_isZero_of_pos
    (A : FilF) (q : ℤ) (hq : 0 < q) :
    IsZero ((assocGraded.obj ((single₀).obj A)).homology q) := by
  -- Proof comment: the associated graded functor acts degreewise, so the source stays a single
  -- complex concentrated in degree `0`.
  simpa using
    (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) (0 : ℤ)
      ((finiteFilteredObjectAssociatedGradedFunctor 𝒜).obj A) q (by omega))

/-- Helper for Lemma 13.26.8: a graded complex concentrated in degrees `≥ 0` has degree-`0`
homology equal to its degree-`0` cycles. -/
private noncomputable def cycles_to_homology_iso_zero_of_isStrictlyGE_zero
    (K : CochainComplex (GradedObject ℤ 𝒜) ℤ) (hKge : K.IsStrictlyGE 0) :
    K.cycles 0 ≅ K.homology 0 := by
  let _ : K.IsStrictlyGE 0 := hKge
  let S : ShortComplex (GradedObject ℤ 𝒜) := K.sc' (-1) 0 1
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have htoCycles_zero : S.toCycles = 0 := by
    -- Proof comment: the predecessor term `K.X (-1)` vanishes, so every map out of it is zero.
    let hzero := K.isZero_of_isStrictlyGE 0 (-1) (by omega)
    exact hzero.eq_of_src S.toCycles 0
  let inv : S.homology ⟶ S.cycles :=
    S.descHomology (𝟙 S.cycles) (by
      -- Proof comment: with zero predecessor differential, the identity on cycles descends.
      simpa [S] using htoCycles_zero)
  have hπinv : S.homologyπ ≫ inv = 𝟙 S.cycles := by
    -- Proof comment: this is the defining computation rule for `descHomology`.
    exact
      ShortComplex.π_descHomology (S := S) (k := 𝟙 S.cycles)
        (hk := by simpa [S] using htoCycles_zero)
  let eShort : S.cycles ≅ S.homology :=
    { hom := S.homologyπ
      inv := inv
      hom_inv_id := hπinv
      inv_hom_id := by
        -- Proof comment: `homologyπ` is epi, so its left inverse is automatically two-sided.
        apply (cancel_epi S.homologyπ).1
        calc
          S.homologyπ ≫ (inv ≫ S.homologyπ) = (S.homologyπ ≫ inv) ≫ S.homologyπ := by
            simp [Category.assoc]
          _ = 𝟙 S.cycles ≫ S.homologyπ := by rw [hπinv]
          _ = S.homologyπ := by simp
          _ = S.homologyπ ≫ 𝟙 S.homology := by simp }
  -- Proof comment: identify the ambient cycles and homology objects with the short-complex ones
  -- once, then use the explicit short-complex isomorphism.
  exact
    (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK) ≪≫
      eShort ≪≫
      (K.homologyIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 13.26.8: after identifying the degree-`0` cycles of a single complex with
the original object, the induced cycles map is the concrete `liftCycles'` morphism. -/
private theorem single_cycles_map_eq_liftCycles'
    {B : GradedObject ℤ 𝒜} {L : CochainComplex (GradedObject ℤ 𝒜) ℤ}
    (φ : (CochainComplex.singleFunctor (GradedObject ℤ 𝒜) (0 : ℤ)).obj B ⟶ L) :
    (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
        HomologicalComplex.cyclesMap φ 0 =
      L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) := by
  -- Proof comment: compare both maps after composing with the canonical cycles inclusion; they
  -- both reduce to the degree-`0` component `φ.f 0`.
  apply (cancel_mono (L.iCycles 0)).1
  calc
    ((HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
        HomologicalComplex.cyclesMap φ 0) ≫ L.iCycles 0 =
        (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
          (((CochainComplex.singleFunctor (GradedObject ℤ 𝒜) (0 : ℤ)).obj B).iCycles 0 ≫
            φ.f 0) := by
          simpa [Category.assoc] using
            congrArg
              (fun k =>
                (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫ k)
              (HomologicalComplex.cyclesMap_i φ 0)
    _ = φ.f 0 := by
          simp [Category.assoc]
    _ =
        L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫ L.iCycles 0 := by
          simp [Category.assoc]

/-- Helper for Lemma 13.26.8: for a single complex concentrated in degree `0`, the canonical map
from cycles to homology is identified with the inverse of `singleObjHomologySelfIso`. -/
private theorem single_cycles_to_homology_eq_single_homology
    (B : GradedObject ℤ 𝒜) :
    (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
        ((CochainComplex.singleFunctor (GradedObject ℤ 𝒜) (0 : ℤ)).obj B).homologyπ 0 =
      (HomologicalComplex.singleObjHomologySelfIso (up ℤ) (0 : ℤ) B).inv := by
  -- Proof comment: both maps are the canonical morphism from `B` to the degree-`0` homology of
  -- the single complex, so the standard simplifier closes the comparison.
  simp

/-- Helper for Lemma 13.26.8: the degree-`0` homology map of an associated-graded quasi-isomorphism
out of a single complex is exactly the cycles-factor route used in the source proof. -/
private theorem single_filtered_quasiIso_degree_zero_homology_factor_eq
    {A : FilF} {I : FiltInjPlus} (u : (single₀).obj A ⟶ I) :
    let B : GradedObject ℤ 𝒜 := (finiteFilteredObjectAssociatedGradedFunctor 𝒜).obj A
    let φ := assocGraded.map u
    let L := assocGraded.obj (I : CochainComplex FilF ℤ)
    L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫ L.homologyπ 0 =
      (HomologicalComplex.singleObjHomologySelfIso (up ℤ) (0 : ℤ) B).inv ≫
        HomologicalComplex.homologyMap φ 0 := by
  let B : GradedObject ℤ 𝒜 := (finiteFilteredObjectAssociatedGradedFunctor 𝒜).obj A
  let φ := assocGraded.map u
  let L := assocGraded.obj (I : CochainComplex FilF ℤ)
  -- Proof comment: rewrite the source degree-zero cycles map as the concrete `liftCycles'`,
  -- then use homology naturality and the single-complex identification on the source.
  calc
    L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫ L.homologyπ 0 =
        ((HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
          HomologicalComplex.cyclesMap φ 0) ≫ L.homologyπ 0 := by
          rw [single_cycles_map_eq_liftCycles' (φ := φ)]
    _ =
        (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
          (HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0) := by
          simp [Category.assoc]
    _ =
        (HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
          (((CochainComplex.singleFunctor (GradedObject ℤ 𝒜) (0 : ℤ)).obj B).homologyπ 0 ≫
            HomologicalComplex.homologyMap φ 0) := by
          rw [← HomologicalComplex.homologyπ_naturality]
    _ =
        ((HomologicalComplex.singleObjCyclesSelfIso (up ℤ) (0 : ℤ) B).inv ≫
          ((CochainComplex.singleFunctor (GradedObject ℤ 𝒜) (0 : ℤ)).obj B).homologyπ 0) ≫
            HomologicalComplex.homologyMap φ 0 := by
          simp [Category.assoc]
    _ =
        (HomologicalComplex.singleObjHomologySelfIso (up ℤ) (0 : ℤ) B).inv ≫
          HomologicalComplex.homologyMap φ 0 := by
          rw [single_cycles_to_homology_eq_single_homology (B := B)]

/-- Helper for Lemma 13.26.8: the source-faithful degree-`0` cycles-to-homology factor induced by
an associated-graded quasi-isomorphism is an isomorphism. -/
private theorem single_filtered_quasiIso_degree_zero_homology_factor_isIso
    {A : FilF} {I : FiltInjPlus} (u : (single₀).obj A ⟶ I)
    (hτ : QuasiIso (assocGraded.map u)) :
    let φ := assocGraded.map u
    let L := assocGraded.obj (I : CochainComplex FilF ℤ)
    IsIso
      (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫ L.homologyπ 0) := by
  let B : GradedObject ℤ 𝒜 := (finiteFilteredObjectAssociatedGradedFunctor 𝒜).obj A
  let φ := assocGraded.map u
  let L := assocGraded.obj (I : CochainComplex FilF ℤ)
  have hφ₀ : IsIso (HomologicalComplex.homologyMap φ 0) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    rw [quasiIso_iff] at hτ
    exact hτ 0
  let _ : IsIso (HomologicalComplex.homologyMap φ 0) := hφ₀
  -- Proof comment: after rewriting the factor through the source single-complex homology
  -- identification, it is a composite of two isomorphisms.
  rw [single_filtered_quasiIso_degree_zero_homology_factor_eq (u := u)]
  infer_instance

/-- Helper for Lemma 13.26.8: associated graded preserves the nonnegative concentration of a
filtered complex. -/
private theorem associatedGraded_strictlyGE_zero_of_strictlyGE_zero
    {K : CochainComplex FilF ℤ} (hKge : K.IsStrictlyGE 0) :
    (assocGraded.obj K).IsStrictlyGE 0 := by
  -- Proof comment: every negative term of `K` is already zero, and associated graded preserves
  -- zero objects degreewise.
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let hzero : IsZero (K.X n) := K.isZero_of_isStrictlyGE 0 n hn
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (finiteFilteredObjectAssociatedGradedFunctor 𝒜).map_isZero hzero

/-- Helper for Lemma 13.26.8: if the target complex is concentrated in degrees `≥ 0`, then the
degree-`0` cycles lift of a filtered quasi-isomorphism from a single complex is already an
isomorphism before passing to homology. -/
private theorem single_filtered_quasiIso_degree_zero_cycles_factor_isIso_of_isStrictlyGE_zero
    {A : FilF} {I : FiltInjPlus} (u : (single₀).obj A ⟶ I)
    (hτ : QuasiIso (assocGraded.map u))
    (hIge : (I : CochainComplex FilF ℤ).IsStrictlyGE 0) :
    let φ := assocGraded.map u
    let L := assocGraded.obj (I : CochainComplex FilF ℤ)
    IsIso (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp))) := by
  let φ := assocGraded.map u
  let L := assocGraded.obj (I : CochainComplex FilF ℤ)
  have hLge : L.IsStrictlyGE 0 :=
    associatedGraded_strictlyGE_zero_of_strictlyGE_zero (K := (I : CochainComplex FilF ℤ)) hIge
  have hfactor :
      IsIso
        (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫
          L.homologyπ 0) :=
    single_filtered_quasiIso_degree_zero_homology_factor_isIso (u := u) hτ
  let eπ : L.cycles 0 ≅ L.homology 0 :=
    cycles_to_homology_iso_zero_of_isStrictlyGE_zero L hLge
  have hπ :
      IsIso (L.homologyπ 0) := by
    change IsIso eπ.hom
    infer_instance
  have hrewrite :
      L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) =
        (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫
          L.homologyπ 0) ≫ eπ.inv := by
    simp [eπ, Category.assoc]
  -- Proof comment: once degree-`0` cycles and homology coincide on the target, the previously
  -- isolated homology-factor isomorphism upgrades the cycles lift itself to an isomorphism.
  rw [hrewrite]
  let _ :
      IsIso
        (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫
          L.homologyπ 0) := hfactor
  let _ : IsIso eπ.inv := by infer_instance
  infer_instance

/-- Helper for Lemma 13.26.8: if the target complex is concentrated in degrees `≥ 0`, then the
degree-`0` filtered map of a quasi-isomorphism from a single complex is a strict monomorphism. -/
private theorem single_filtered_quasiIso_degree_zero_mono_and_strict_of_isStrictlyGE_zero
    {A : FilF} {I : FiltInjPlus} (u : (single₀).obj A ⟶ I)
    (hτ : QuasiIso (assocGraded.map u))
    (hIge : (I : CochainComplex FilF ℤ).IsStrictlyGE 0) :
    Mono (u.f 0) ∧ FilteredObject.Hom.Strict (u.f 0).hom := by
  let φ := assocGraded.map u
  let L := assocGraded.obj (I : CochainComplex FilF ℤ)
  have hlift :
      IsIso (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp))) :=
    single_filtered_quasiIso_degree_zero_cycles_factor_isIso_of_isStrictlyGE_zero
      (u := u) hτ hIge
  have hmonoGraded : ∀ p : ℤ, Mono (gradedPieceMap (u.f 0).hom p) := by
    intro p
    have hrewrite :
        φ.f 0 =
          L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)) ≫ L.iCycles 0 := by
      -- Proof comment: the concrete cycles lift is characterized by its composite with the
      -- canonical cycles inclusion.
      apply (cancel_mono (L.iCycles 0)).1
      simp [Category.assoc]
    have hmonoEval :
        Mono ((GradedObject.eval p).map (φ.f 0)) := by
      rw [hrewrite]
      let _ :
          IsIso
            ((GradedObject.eval p).map
              (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp)))) := by
        let _ :
            IsIso
              (L.liftCycles' (φ.f 0) 1 rfl (by simpa using φ.comm 0 1 (by simp))) := hlift
        infer_instance
      let _ : Mono ((GradedObject.eval p).map (L.iCycles 0)) := by infer_instance
      infer_instance
    -- Proof comment: evaluating the degree-`0` associated-graded component is exactly taking the
    -- `p`-th graded piece of the filtered map `u.f 0`.
    simpa [assocGraded, CategoryTheory.Functor.comp_map] using hmonoEval
  have hzeroKernelGraded :
      ∀ p : ℤ, IsZero (gr^{p} (kernelFilteredObject (u.f 0).hom)) := by
    intro p
    let κ :
        gr^{p} (kernelFilteredObject (u.f 0).hom) ⟶
          gr^{p} A :=
      gradedPieceMap (kernelι (u.f 0).hom) p
    have hκmono : Mono κ := by
      simpa [κ, FilteredObject.Hom.kernelCoimageShortComplex] using
        (gradedPiece_kernel_coimage_shortExact (u.f 0).hom p).mono_f
    have hκcomp :
        κ ≫ gradedPieceMap (u.f 0).hom p = 0 := by
      simpa [κ] using
        gradedPieceMap_comp_zero
          (kernelι (u.f 0).hom) (u.f 0).hom (kernelι_comp (u.f 0).hom) p
    have hκzero : κ = 0 := by
      let _ : Mono (gradedPieceMap (u.f 0).hom p) := hmonoGraded p
      exact (cancel_mono (gradedPieceMap (u.f 0).hom p)).1 hκcomp
    exact IsZero.of_mono_eq_zero κ hκzero
  have hzeroKernelObj : IsZero (kernelFilteredObject (u.f 0).hom).obj := by
    -- Proof comment: every graded piece of the filtered kernel vanishes, and the induced kernel
    -- filtration is finite because the source filtration is finite.
    exact
      (kernelFilteredObject (u.f 0).hom).filtration.isZero_obj_of_isFinite_of_gradedPiece_isZero
        (finite_kernelFilteredObject_isFinite (u.f 0).hom A.property)
        hzeroKernelGraded
  have hzeroKernel : IsZero (kernel (u.f 0).hom) :=
    Limits.IsZero.of_iso hzeroKernelObj (kernelSubobjectIso (u.f 0).hom).symm
  have hmono : Mono (u.f 0) := by
    simpa using (mono_iff_isZero_kernel (u.f 0).hom).2 hzeroKernel
  have hExact :
      ∀ p : ℤ, (FilteredObject.Hom.kernelSourceTargetShortComplex (u.f 0).hom p).Exact := by
    intro p
    -- Proof comment: with zero graded kernel and mono graded target map, the kernel row is exact
    -- degreewise.
    exact
      ((FilteredObject.Hom.kernelSourceTargetShortComplex (u.f 0).hom p).exact_iff_mono
        ((hzeroKernelGraded p).eq_of_src _ _)).2 (hmonoGraded p)
  have hstrict :
      FilteredObject.Hom.Strict (u.f 0).hom :=
    ((FilteredObject.Hom.strict_tfae_coimageImageComparison_isIso_and_graded_exactness
      (u.f 0).hom A.property ((I : CochainComplex FilF ℤ).X 0).property).out 0 3).2 hExact
  exact ⟨hmono, hstrict⟩

/-- Helper for Lemma 13.26.8: a filtered quasi-isomorphism from a degree-zero single complex makes
the target associated graded complex exact in every positive degree. -/
private theorem positive_exact_of_quasiIso_from_single
    {A : FilF} {I : FiltInjPlus} (u : (single₀).obj A ⟶ I)
    (hτ : QuasiIso (assocGraded.map u)) (q : ℤ) (hq : 0 < q) :
    (assocGraded.obj (I : CochainComplex FilF ℤ)).ExactAt q := by
  -- Proof comment: transport the positive-degree homology vanishing of the source single complex
  -- across the associated-graded quasi-isomorphism.
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [quasiIso_iff] at hτ
  have hτq : IsIso (HomologicalComplex.homologyMap (assocGraded.map u) q) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact hτ q
  letI : IsIso (HomologicalComplex.homologyMap (assocGraded.map u) q) := hτq
  let e :
      (assocGraded.obj ((single₀).obj A)).homology q ≅
        (assocGraded.obj (I : CochainComplex FilF ℤ)).homology q :=
    asIso (HomologicalComplex.homologyMap (assocGraded.map u) q)
  exact (associatedGraded_single_homology_isZero_of_pos (A := A) q hq).of_iso e

/-- Helper for Lemma 13.26.8: the positive-degree exactness forced by the outer filtered
quasi-isomorphisms makes every nonnegative differential in the target strict. -/
private theorem strict_differential_of_quasiIso_from_single
    {A : FilF} {I : FiltInjPlus} (u : (single₀).obj A ⟶ I)
    (hτ : QuasiIso (assocGraded.map u)) (n : ℤ) (hn : 0 ≤ n) :
    FilteredObject.Hom.Strict (((I : CochainComplex FilF ℤ).d n (n + 1)).hom) := by
  let iFin :
      FilF ⥤ FilteredObject 𝒜 :=
    ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))
  let S : ShortComplex (FilteredObject 𝒜) :=
    (((I : CochainComplex FilF ℤ).sc' n (n + 1) (n + 2)).map iFin)
  have hExactAt :
      (assocGraded.obj (I : CochainComplex FilF ℤ)).ExactAt (n + 1) :=
    positive_exact_of_quasiIso_from_single (u := u) hτ (n + 1) (by omega)
  have hgr : ShortComplex.Exact (S.map ShortComplex.associatedGradedFunctor) := by
    -- Proof comment: the exactness statement at degree `n + 1` is exactly the associated graded
    -- exactness of the three-term row built from the two consecutive differentials.
    simpa [S, HomologicalComplex.exactAt_iff] using hExactAt
  -- Proof comment: apply the filtered exactness-to-strictness bridge to the degreewise row.
  exact
    (ShortComplex.strict_of_associatedGraded_exact
      (S := S)
      ((I : CochainComplex FilF ℤ).X n).property
      ((I : CochainComplex FilF ℤ).X (n + 1)).property
      ((I : CochainComplex FilF ℤ).X (n + 2)).property
      hgr).1

/-- Helper for Lemma 13.26.8: the filtered inclusion of degree-`0` cycles is strict. -/
private theorem cycles_inclusion_strict_of_strict_differential
    {I : FiltInjPlus}
    (_hstrict : FilteredObject.Hom.Strict (((I : CochainComplex FilF ℤ).d 0 1).hom)) :
    FilteredObject.Hom.Strict (kernelι (((I : CochainComplex FilF ℤ).d 0 1).hom)) := by
  let f : ((I : CochainComplex FilF ℤ).X 0) ⟶ ((I : CochainComplex FilF ℤ).X 1) :=
    ((I : CochainComplex FilF ℤ).d 0 1).hom
  letI : Mono (kernelι f).hom := by
    change Mono (kernelSubobject f.hom).arrow
    infer_instance
  -- Proof comment: the cycles object uses the induced filtration from `I⁰`, so its inclusion is
  -- strict by the mono-side characterization of strictness.
  simpa [f] using
    (FilteredObject.Hom.strict_iff_induced_filtration_of_mono (kernelι f)).2 rfl

-- Proof sketch: starting from the prescribed filtered quasi-isomorphisms on the outer terms, lift
-- the outer objects into bounded-below filtered-injective complexes, build the middle
-- filtered-injective complex degreewise by extension, and assemble the lower row directly as a
-- short complex in `CochainComplex.FilteredInjectivePlus 𝒜` together with a single comparison
-- morphism from the degree-zero short exact sequence. The lower row is recorded by the canonical
-- degreewise splitting family, which is the source-facing termwise-split conclusion.
/-- Lemma 13.26.8: given a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` in `Fil^f(𝒜)` and prescribed
filtered quasi-isomorphisms from `A[0]` and `C[0]` into bounded-below complexes of filtered
injective objects, there exists a filtered horseshoe diagram whose lower row is termwise split
and whose outer comparison maps are exactly the prescribed maps. -/
theorem exists_filtered_horseshoe_diagram
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c)) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c := by
  obtain ⟨hf_strict, hg_strict⟩ := shortExact_strict_maps (S := S) hS
  obtain ⟨b₀, hb₀⟩ :=
    exists_degree_zero_extension_of_strict_left_map (S := S) hS (I := I) a hf_strict
  have hI_d_strict :
      ∀ n : ℤ, 0 ≤ n →
        FilteredObject.Hom.Strict (((I : CochainComplex FilF ℤ).d n (n + 1)).hom) := by
    intro n hn
    -- Proof comment: every positive-degree associated graded homology of `I` vanishes, so the
    -- source-faithful strictness bridge applies to each consecutive row.
    exact strict_differential_of_quasiIso_from_single (u := a) hτ₁ n hn
  have hJ_d_strict :
      ∀ n : ℤ, 0 ≤ n →
        FilteredObject.Hom.Strict (((J : CochainComplex FilF ℤ).d n (n + 1)).hom) := by
    intro n hn
    -- Proof comment: the same positive-degree exactness argument applies to the right column.
    exact strict_differential_of_quasiIso_from_single (u := c) hτ₃ n hn
  -- Route correction: the first three source steps are now isolated above:
  -- extend `a.f 0` across `S.f`, descend `B ⟶ I⁰ ⟶ I¹` to `C ⟶ I¹`, and then extend that map
  -- across `c.f 0`. The remaining blocker is now narrower: we have strictness of `S.f`, `S.g`,
  -- and all nonnegative differentials of `I` and `J`, but we still need the degree-zero
  -- monomorphism/strictness bridge for `a.f 0` and `c.f 0` in order to build `δ₀`, recurse to a
  -- full connecting family `δⁿ`, and package the resulting upper-triangular complex.
  -- TODO: the new helper
  -- `single_filtered_quasiIso_degree_zero_mono_and_strict_of_isStrictlyGE_zero`
  -- proves exactly the required degree-zero `Mono`/`Strict` package, but it needs the
  -- source-proof hypothesis that the prescribed outer complexes vanish in negative degrees.
  -- The current Lean header only assumes `I J : FiltInjPlus`, so the local proof is now reduced
  -- to the structural blocker of recovering or reinstating those `IsStrictlyGE 0` hypotheses in
  -- a way compatible with the immutable target statement.
  sorry

-- Proof sketch: first build the horseshoe diagram from `exists_filtered_horseshoe_diagram`.
-- The degreewise splitting family implies short exactness of the lower row, so
-- `quasiIso_middle` applies to the resulting short-complex morphism and the prescribed outer
-- filtered quasi-isomorphisms.
/-- Companion consequence to Lemma 13.26.8: if the prescribed outer comparison maps are filtered
quasi-isomorphisms, then the horseshoe diagram can be chosen so that the middle comparison map is
also a filtered quasi-isomorphism. -/
theorem exists_filtered_horseshoe_diagram_of_outer_quasiIso
    (S : ShortComplex FilF) (hS : S.ShortExact)
    {I J : FiltInjPlus} (a : (single₀).obj S.X₁ ⟶ I)
    (c : (single₀).obj S.X₃ ⟶ J)
    (hτ₁ : QuasiIso (assocGraded.map a))
    (hτ₃ : QuasiIso (assocGraded.map c)) :
    ∃ (K : FiltInjPlus) (i : I ⟶ K) (p : K ⟶ J) (hip : i ≫ p = 0)
      (φ : S.map single₀ ⟶ (ShortComplex.mk i p hip).map ιFiltInjPlus)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk i p hip).map
          (ιFiltInjPlus ⋙ HomologicalComplex.eval FilF (ComplexShape.up ℤ) n)).Splitting),
        φ.τ₁ = a ∧
          φ.τ₃ = c ∧
          QuasiIso (assocGraded.map φ.τ₂) := by
  -- Route correction: once the filtered horseshoe diagram exists, the remaining input is purely
  -- formal. Degreewise split short exactness gives the lower short exact row, and
  -- `quasiIso_middle` upgrades the outer filtered quasi-isomorphisms to the middle column.
  obtain ⟨K, i, p, hip, φ, σ, hφ₁, hφ₃⟩ :=
    exists_filtered_horseshoe_diagram
      (S := S) hS a c hτ₁ hτ₃
  let hrow : ((ShortComplex.mk i p hip).map ιFiltInjPlus).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (fun n ↦ (σ n).shortExact)
  refine ⟨K, i, p, hip, φ, σ, hφ₁, hφ₃, ?_⟩
  -- Reuse the filtered five-lemma argument on the constructed short exact lower row.
  have hmid :
      QuasiIso (assocGraded.map φ.τ₂) :=
    quasiIso_middle
      (S := S) hS (T := ShortComplex.mk i p hip) φ hrow
      (by simpa [hφ₁] using hτ₁)
      (by simpa [hφ₃] using hτ₃)
  exact hmid

end CochainComplex

end CategoryTheory
