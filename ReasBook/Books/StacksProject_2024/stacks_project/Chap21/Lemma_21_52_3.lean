import StacksProject_2024.Chap12.Lemma_12_7_2
import StacksProject_2024.Chap13.Lemma_13_6_2
import StacksProject_2024.Chap13.Lemma_13_16_3
import StacksProject_2024.Chap13.Lemma_13_18_3
import StacksProject_2024.Chap18.«18_19_2_1»
import StacksProject_2024.Chap19.Lemma_19_13_4
import StacksProject_2024.Chap19.Theorem_19_8_4
import StacksProject_2024.Chap21.Lemma_21_12_2
import StacksProject_2024.Chap21.Lemma_21_20_7_core
import StacksProject_2024.Chap21.Lemma_21_30_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory
open Opposite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable (𝒪 : Sheaf J CommRingCat.{u})

attribute [local instance] HasDerivedCategory.standard

variable [modAbelian : Abelian (SheafOfModules (ringSheaf J 𝒪))]

local notation "Mod𝒪" => SheafOfModules (ringSheaf J 𝒪)
local notation "single0" => DerivedCategory.singleFunctor Mod𝒪 (0 : ℤ)
local notation "X" => RingedSite.ofCommRingSheaf J 𝒪

local instance modPreadditive : Preadditive Mod𝒪 := modAbelian.toPreadditive

/-- Helper for Lemma 21.52.3: the forgetful functor from `𝒪`-modules to presheaves of
modules is additive after passing to the underlying abelian presheaf. -/
local instance moduleForget_additive :
    (SheafOfModules.forget (ringSheaf J 𝒪)).Additive := by
  -- The module forgetful functor is left exact, hence additive by the Chapter 12 criterion.
  have hLeftExact :
      leftExactFunctor Mod𝒪 (PresheafOfModules (ringSheaf J 𝒪).1)
        (SheafOfModules.forget (ringSheaf J 𝒪)) := by
    simpa [leftExactFunctor_iff] using
      (inferInstance :
        PreservesFiniteLimits (SheafOfModules.forget (ringSheaf J 𝒪)))
  exact
    functor_additive_of_leftExact_or_rightExact
      (SheafOfModules.forget (ringSheaf J 𝒪)) (.inl hLeftExact)

/- Domain-style sampling for Lemma 21.52.3:
- primary domain: bounded-below coproduct preservation in the derived category of sheaves of
  modules, expressed by the represented `Hom` functor from `j_{U!}𝒪_U[0]`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_homEquiv`,
  `SheafOfModules.cohomologyAtObjectFunctor`,
  `DerivedCategory.singleFunctor`,
  `CategoryTheory.preadditiveCoyoneda.obj`;
- best owner abstraction: the source-facing owner is the canonical degree-zero derived object
  `((single0).obj (j![𝒪, U]))`, while the canonical hypothesis layer is the fixed-object
  cohomology owner `SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U`;
- primitive data: the object `U`, the direct-sum compatibility of the ordinary cohomology
  functors `H^p(U, -)`, and the bounded-below coproduct object `∐ M`;
- derived API: the represented `Hom`-functor coproduct comparison for
  `((single0).obj (j![𝒪, U]))`.

Source/core/bridge triage:
- `source-facing`: the bounded-below coproduct comparison for `j_{U!}𝒪_U[0]`;
- `core/canonical`: `SheafOfModules.cohomologyAtObjectFunctor` together with the owner
  `localizedStructureModuleExtensionByZero 𝒪 U`;
- `bridge/view`: `SheafOfModules.cohomologyAtObject_isomorphic` and
  `preadditiveCoyoneda.obj (op ((single0).obj (j![𝒪, U])))`.
-/

-- Proof sketch: identify `Hom_D(j_{U!}𝒪_U[0], -)` with the degree-zero objectwise
-- cohomology functor at `U` using the adjunction from `18.19.2.1`. Then choose a lower bound for
-- the coproduct object `∐ M_i`, represent the summands by uniformly bounded-below complexes of
-- injectives, take their termwise direct sum, and apply the hypothesis that `H^p(U, -)` commutes
-- with direct sums to compare the resulting cohomology groups.
/-- Helper for Lemma 21.52.3: morphisms from `j_{U!}𝒪_U[0]` into a degree-zero derived
object are just ordinary sections over `U`. -/
private noncomputable def localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
    (U : C) (ℱ : Mod𝒪) :
    ((single0).obj (j![𝒪, U]) ⟶ (single0).obj ℱ) ≃
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) := by
  -- First forget the degree-zero embedding using full faithfulness of `single0`.
  let hFF : (single0).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful single0
  let e₁ :
      (((single0).obj (j![𝒪, U])) ⟶ (single0).obj ℱ) ≃
        (j![𝒪, U] ⟶ ℱ) :=
    (Functor.FullyFaithful.homEquiv hFF).symm
  -- Then use the extension-by-zero/evaluation adjunction on the abelian heart.
  exact e₁.trans (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ)

omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.52.3: converting a section over `U` to a degree-zero morphism and back
recovers the original section. -/
@[simp] private theorem
    localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation_apply_symm_apply
    (U : C) (ℱ : Mod𝒪)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) :
    localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
        J 𝒪 U ℱ
        ((localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
          J 𝒪 U ℱ).symm s) = s := by
  -- This is the right-inverse identity of the canonical degree-zero Hom/sections equivalence.
  exact
    (localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
      J 𝒪 U ℱ).apply_symm_apply s

omit [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.52.3: converting a degree-zero morphism to a section over `U` and back
recovers the original morphism. -/
@[simp] private theorem
    localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation_symm_apply_apply
    (U : C) (ℱ : Mod𝒪)
    (f : ((single0).obj (j![𝒪, U])) ⟶ (single0).obj ℱ) :
    (localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
        J 𝒪 U ℱ).symm
        (localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
          J 𝒪 U ℱ f) = f := by
  -- This is the left-inverse identity of the same equivalence.
  exact
    (localizedStructureModuleExtensionByZeroDegreeZero_homEquiv_evaluation
      J 𝒪 U ℱ).symm_apply_apply f

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
  /-- Helper for Lemma 21.52.3: any derived object that is bounded below by `a` admits a
quasi-isomorphic bounded-below injective complex with the same lower bound. -/
private lemma bounded_below_injective_representative_of_isGE
    (K : DerivedCategory Mod𝒪) (a : ℤ) (hK : K.IsGE a) :
    ∃ (I : CochainComplex (SheafOfModules.{u} (ringSheaf J 𝒪)) ℤ)
      (_ : DerivedCategory.Q.obj I ≅ K),
      I.IsStrictlyGE a ∧ ∀ n : ℤ, Injective (I.X n) := by
  -- First truncate the canonical preimage so the lower bound becomes strict on the complex side.
  have hPreimageGE : (DerivedCategory.Q.objPreimage K).IsGE a :=
    objPreimage_isGE_of_isGE K hK
  letI : (DerivedCategory.Q.objPreimage K).IsGE a := hPreimageGE
  let A : CochainComplex (SheafOfModules.{u} (ringSheaf J 𝒪)) ℤ :=
    (DerivedCategory.Q.objPreimage K).truncGE a
  have hAiso : DerivedCategory.Q.obj A ≅ K := by
    -- The truncation map is a quasi-isomorphism because the preimage is already `IsGE a`.
    have hπ :
        IsIso (DerivedCategory.Q.map ((DerivedCategory.Q.objPreimage K).πTruncGE a)) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
      infer_instance
    let _ : IsIso (DerivedCategory.Q.map ((DerivedCategory.Q.objPreimage K).πTruncGE a)) := hπ
    exact
      (asIso (DerivedCategory.Q.map ((DerivedCategory.Q.objPreimage K).πTruncGE a))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso K
  -- Then resolve the bounded-below truncation by an injective complex with the same lower bound.
  let _ : EnoughInjectives (SheafOfModules.{u} (ringSheaf J 𝒪)) := inferInstance
  let _ : HasInjectiveResolutions (SheafOfModules.{u} (ringSheaf J 𝒪)) := inferInstance
  have hAstrict : A.IsStrictlyGE a := inferInstance
  obtain ⟨JI, hJIge, _⟩ :=
    exists_injectiveResolution_strictlyGE_with_termwise_mono a hAstrict
  refine ⟨(JI : CochainComplex (SheafOfModules.{u} (ringSheaf J 𝒪)) ℤ), ?_⟩
  refine ⟨(asIso (DerivedCategory.Q.map JI.ι)).symm ≪≫ hAiso, hJIge, ?_⟩
  intro n
  infer_instance

/-- Helper for Lemma 21.52.3: the canonical projection from a coproduct onto one fixed summand. -/
private noncomputable def summand_projection_from_coproduct
    {ι : Type (u + 1)} (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M] (i : ι) :
    (∐ M) ⟶ M i :=
  let _ : DecidableEq ι := Classical.decEq ι
  Limits.Sigma.desc fun j ↦
    if h : j = i then eqToHom (by subst h; rfl) else 0

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.52.3: the coproduct inclusion followed by the canonical projection is the
identity on the chosen summand. -/
private lemma summand_inclusion_projection
    {ι : Type (u + 1)} (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M] (i : ι) :
    Sigma.ι M i ≫ summand_projection_from_coproduct J 𝒪 M i = 𝟙 (M i) := by
  -- Evaluate the descended map on the distinguished coproduct summand.
  classical
  simp [summand_projection_from_coproduct, Limits.Sigma.ι_desc]

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.52.3: the projection onto the `i`-th coproduct summand kills every
different summand. -/
private lemma summand_inclusion_projection_of_ne
    {ι : Type (u + 1)} (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M]
    {i j : ι} (hij : j ≠ i) :
    Sigma.ι M j ≫ summand_projection_from_coproduct J 𝒪 M i = 0 := by
  -- Evaluate the coproduct projection on a different summand and use the defining `if`-branch.
  classical
  simp [summand_projection_from_coproduct, Limits.Sigma.ι_desc, hij]

/-- Helper for Lemma 21.52.3: each summand of a coproduct is a retract of the coproduct via the
canonical inclusion and projection onto that summand. -/
private noncomputable def summand_retract_of_coproduct
    {ι : Type (u + 1)} (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M] (i : ι) :
    Retract (M i) (∐ M) where
  i := Sigma.ι M i
  r := summand_projection_from_coproduct J 𝒪 M i
  retract := summand_inclusion_projection J 𝒪 M i

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Helper for Lemma 21.52.3: a uniform lower bound on the coproduct descends to each summand via
the canonical retract. -/
private lemma summand_isGE_of_coproduct_isGE
    {ι : Type (u + 1)} (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M]
    {a : ℤ} (hM : (∐ M).IsGE a) (i : ι) :
    (M i).IsGE a := by
  -- Map the summand retract through each fixed-degree homology functor and use retract-stability
  -- of the zero object property.
  rw [DerivedCategory.isGE_iff] at hM ⊢
  intro n hn
  exact
    prop_of_retract IsZero
      ((summand_retract_of_coproduct J 𝒪 M i).map
        (DerivedCategory.homologyFunctor Mod𝒪 n))
      (hM n hn)

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
/-- Helper for Lemma 21.52.3: positive objectwise cohomology over `U` vanishes on injective
`𝒪`-modules, expressed on the canonical owner `cohomologyAtObjectFunctor`. -/
lemma cohomologyAtObjectFunctor_obj_isZero_of_injective_succ
    (U : C) (n : ℕ) (ℱ : Mod𝒪) [Injective ℱ] :
    IsZero ((SheafOfModules.cohomologyAtObjectFunctor
      (ringSheaf J 𝒪) (n + 1) U).obj ℱ) := by
  -- Positive cohomology is a higher right derived functor of the forgetful functor.
  simpa [SheafOfModules.cohomologyAtObjectFunctor, SheafOfModules.cohomologyPresheafFunctor] using
    Functor.map_isZero
      (PresheafOfModules.evaluation (ringSheaf J 𝒪).obj (op U) ⋙
        forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj (op U))) AddCommGrpCat.{u})
      (Functor.isZero_rightDerived_obj_injective_succ
        (SheafOfModules.forget (ringSheaf J 𝒪)) n ℱ)

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
/-- Helper for Lemma 21.52.3: if `H^(n + 1)(U, -)` commutes with direct sums, then its value on
the direct sum of injective `𝒪`-modules is zero. -/
lemma cohomologyAtObjectFunctor_obj_isZero_of_coproduct_of_injective_succ
    (U : C) (n : ℕ) {ι : Type (u + 1)} (A : ι → Mod𝒪) [HasCoproduct A]
    (hcomm :
      PreservesColimitsOfShape (Discrete ι)
        (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) (n + 1) U))
    [∀ i, Injective (A i)] :
    IsZero ((SheafOfModules.cohomologyAtObjectFunctor
      (ringSheaf J 𝒪) (n + 1) U).obj (∐ A)) := by
  let F : Mod𝒪 ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) (n + 1) U
  let D : Discrete ι ⥤ AddCommGrpCat.{u} := Discrete.functor A ⋙ F
  have hzeroObj : ∀ i : Discrete ι, IsZero (D.obj i) := by
    intro i
    exact cohomologyAtObjectFunctor_obj_isZero_of_injective_succ
      J 𝒪 U n (A i.as)
  let c : Cocone (Discrete.functor A) := colimit.cocone (Discrete.functor A)
  let hc : IsColimit c := colimit.isColimit (Discrete.functor A)
  let _ : PreservesColimitsOfShape (Discrete ι) F := hcomm
  have hcF : IsColimit (F.mapCocone c) := by
    -- Transport the coproduct cocone through the cohomology functor using `hcomm`.
    exact isColimitOfPreserves F hc
  let z : Cocone D :=
    Cocone.mk (⊥_ AddCommGrpCat.{u}) <|
      Discrete.natTrans (fun _ ↦ 0)
  have hz : IsColimit z := by
    -- The zero object is already a colimit of a diagram whose every vertex is zero.
    refine IsColimit.mk (fun s ↦ 0) ?_ ?_
    · intro s i
      exact (hzeroObj i).eq_of_src _ _
    · intro s m hm
      exact initialIsInitial.hom_ext m 0
  -- The cocone point of `F.mapCocone c` is `F.obj (∐ A)`, so its comparison with the zero colimit
  -- above gives the desired vanishing.
  exact IsZero.of_iso initialIsInitial.isZero (hcF.coconePointUniqueUpToIso hz)

omit [HasBinaryProducts C] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] modAbelian in
/-- If `H^0(U, -)` commutes with direct sums, then the canonical sections functor
`RingedSite.Hom.moduleSectionsAsAbelianFunctor X U` commutes with the same direct sums. -/
private theorem moduleSectionsAsAbelianFunctor_preserves_coproduct_of_hcomm_zero
    (U : C) {ι : Type (u + 1)}
    (hcomm0 :
      PreservesColimitsOfShape (Discrete ι)
        (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) 0 U)) :
    PreservesColimitsOfShape (Discrete ι)
      (RingedSite.Hom.moduleSectionsAsAbelianFunctor (RingedSite.ofCommRingSheaf J 𝒪) U) := by
  let F : Mod𝒪 ⥤ AddCommGrpCat.{u} :=
    RingedSite.Hom.moduleSectionsAsAbelianFunctor (RingedSite.ofCommRingSheaf J 𝒪) U
  let e : SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) 0 U ≅ F := by
    simpa [F, RingedSite.Hom.moduleSectionsAsAbelianFunctor,
      RingedSite.Hom.underlyingAbelianSheafFunctor, SheafOfModules.evaluation] using
      (Functor.isoWhiskerRight
        (Functor.rightDerivedZeroIsoSelf (SheafOfModules.forget (ringSheaf J 𝒪)))
        (PresheafOfModules.toPresheaf (ringSheaf J 𝒪).obj ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)))
  let _ :
      PreservesColimitsOfShape (Discrete ι)
        (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) 0 U) := hcomm0
  simpa [F] using
    (CategoryTheory.Limits.preservesColimitsOfShape_of_natIso e :
      PreservesColimitsOfShape (Discrete ι) F)

/- Lemma 21.52.3: if for a ringed site `(𝒞, 𝒪)` and an object `U` the functors
`ℱ ↦ H^p(U, ℱ)` commute with direct sums for all `p`, then the degree-zero
derived object attached to `j_{U!}𝒪_U` is compact with respect to bounded-below direct
sums: whenever a family `M_i` in `D(𝒪)` has a coproduct whose total object is bounded
below, the Hom group from `j_{U!}𝒪_U[0]` to that coproduct is canonically the direct sum
of the Hom groups to the summands. In Lean this canonical direct-sum comparison is encoded as
preservation of the coproduct colimit by the represented functor. -/
theorem localizedStructureModuleExtensionByZeroDegreeZero_hom_coproduct_iso_of_boundedBelow
    (U : C) {ι : Type (u + 1)}
    (M : ι → DerivedCategory Mod𝒪) [HasCoproduct M]
    (hcomm :
      ∀ (p : ℕ) (κ : Type (u + 1)),
        PreservesColimitsOfShape (Discrete κ)
          (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U))
    (hM : ∃ a : ℤ, (∐ M).IsGE a) :
    PreservesColimit (Discrete.functor M)
      (preadditiveCoyoneda.obj
        (op ((single0).obj (j![𝒪, U])))) := by
  -- Fix the common lower bound from the hypothesis on the total coproduct.
  obtain ⟨a, hGE⟩ := hM
  -- Route correction: the old route stalled by jumping directly to a derived-sections comparison.
  -- The source proof first pushes the common lower bound from the direct sum to each summand via
  -- the direct-summand structure, and only then chooses bounded-below injective representatives.
  have hSummandGE : ∀ i : ι, (M i).IsGE a := fun i ↦
    summand_isGE_of_coproduct_isGE J 𝒪 M hGE i
  -- Then choose termwise injective representatives with the same lower bound for every summand.
  have hSummandInjectiveModel :
      ∀ i : ι,
        ∃ (I : CochainComplex Mod𝒪 ℤ) (_ : DerivedCategory.Q.obj I ≅ M i),
          I.IsStrictlyGE a ∧ ∀ n : ℤ, Injective (I.X n) := by
    intro i
    exact
      bounded_below_injective_representative_of_isGE J 𝒪 (M i) a (hSummandGE i)
  choose I eI hIrest using hSummandInjectiveModel
  have hIge : ∀ i : ι, (I i).IsStrictlyGE a := fun i ↦ (hIrest i).1
  have hIinj : ∀ i : ι, ∀ n : ℤ, Injective ((I i).X n) := fun i ↦ (hIrest i).2
  have hSectionsComm :
      PreservesColimitsOfShape (Discrete ι)
        (RingedSite.Hom.moduleSectionsAsAbelianFunctor X U) :=
    moduleSectionsAsAbelianFunctor_preserves_coproduct_of_hcomm_zero
      J 𝒪 U (hcomm 0 ι)
  let _ := hcomm
  let _ := I
  let _ := eI
  let _ := hIge
  let _ := hIinj
  let _ := hSectionsComm
  -- TODO: the remaining source-faithful step is the Leray endgame on the termwise coproduct
  -- complex `∐ I`. The current dependency-closed frontier has already pushed the common lower
  -- bound to each summand, chosen uniformly bounded-below injective representatives `I i`, and
  -- identified ordinary sections with `H^0(U,-)` so that sections already commute with the needed
  -- coproduct. Next one needs the local coproduct API for the family `I` and for the termwise
  -- sections objects `(I i).X m`, so that `∐ I` and its acyclicity under sections can be
  -- expressed directly in this file and then transported to the represented `Hom` comparison.
  sorry

end

end SheafOfModules.RingedSite
