import StacksProject_2024.stacks_project.Chap04.Definition_4_22_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_3
import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_6
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_7
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_9
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

attribute [local instance] HasDerivedCategory.standard

open SheafOfModules.RingedSite.CochainComplex
open scoped SheafOfModules.RingedSite HomologicalComplex₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 21.17.8: the degree-zero single-complex functor on `Mod(𝒪)`. -/
private abbrev single₀ {𝒪 : Sheaf J CommRingCat.{max u v}} :
    Mod(𝒪) ⥤ CochainComplex (Mod(𝒪)) ℤ :=
  CochainComplex.singleFunctor (Mod(𝒪)) (0 : ℤ)

/-- Helper for Lemma 21.17.8: module sheaves on a ringed site form an abelian category. -/
private instance instAbelianMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    Abelian (Mod(𝒪)) :=
  SheafOfModules.instAbelian (ringSheaf J 𝒪)

/-- Helper for Lemma 21.17.8: the ambient category `Mod(𝒪)` carries homology. -/
private instance instCategoryWithHomologyMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    CategoryWithHomology (Mod(𝒪)) := by
  -- Proof comment: once the ambient module category is abelian and cocomplete, the canonical
  -- homology owner is available by ordinary instance search.
  change CategoryWithHomology (SheafOfModules (ringSheaf J 𝒪))
  infer_instance

/-- Helper for Lemma 21.17.8: module sheaves on a ringed site have all colimits. -/
private instance instHasColimitsMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    HasColimits (Mod(𝒪)) := by
  -- Proof comment: later tower and tensor constructions only use the standard colimits on
  -- module sheaves.
  change HasColimits (SheafOfModules (ringSheaf J 𝒪))
  infer_instance

/-- Helper for Lemma 21.17.8: the evaluation functors jointly reflect isomorphisms on sequential
module diagrams. -/
private theorem evaluationJointlyReflectsIsomorphismsMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    JointlyReflectIsomorphisms
      ((_root_.CategoryTheory.evaluation ℕ (Mod(𝒪))).obj :
        ℕ → (ℕ ⥤ Mod(𝒪)) ⥤ Mod(𝒪)) := by
  refine ⟨fun {X Y} f _ ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  simpa using
    (inferInstance :
      IsIso (((_root_.CategoryTheory.evaluation ℕ (Mod(𝒪))).obj n).map f))

/- Domain-style sampling for Lemma 21.17.8:
- primary domain: K-flat cochain complexes of `𝒪`-modules on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isKFlat_iff`;
- best owner abstraction: the ambient module category is the Chapter 18 owner
  `ringedSiteModuleCategory J 𝒪`, and K-flatness is the Chapter 15 owner predicate `K.IsKFlat`
  on complexes in that category; bounded-above complexes use the Chapter 13 owner
  `CochainComplex.minus (ringedSiteModuleCategory J 𝒪)`, and termwise flatness uses the Chapter 21
  owner `K.IsTermwiseFlat`;
- primitive data: the complex `K`, the bounded-above hypothesis, and the termwise-flat owner
  `K.IsTermwiseFlat`;
- derived API: the K-flatness conclusion.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion on the ringed site;
- `core/canonical`: `ringedSiteModuleCategory`, `CochainComplex.minus`, and
  `CochainComplex.IsTermwiseFlat`, `CochainComplex.IsKFlat`;
- `bridge/view`: this specialization of the canonical termwise-flat and K-flat owners to
  ringed-site modules.
-/

/-- Helper for Lemma 21.17.8: exactness transports across a natural isomorphism of endofunctors on
`Mod(𝒪)`. -/
private theorem exactFunctorOfNatIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    {F G : Mod(𝒪) ⥤ Mod(𝒪)}
    (e : F ≅ G) :
    exactFunctor (Mod(𝒪)) (Mod(𝒪)) F →
      exactFunctor (Mod(𝒪)) (Mod(𝒪)) G := by
  intro hF
  -- Proof comment: exactness is equivalent to preserving finite limits and colimits, and those
  -- preservation properties transport across a natural isomorphism.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : PreservesFiniteLimits F := hF.1
  let _ : PreservesFiniteColimits F := hF.2
  exact
    ⟨CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
      CategoryTheory.Limits.preservesFiniteColimits_of_natIso e⟩

/-- Helper for Lemma 21.17.8: flatness of sheaf modules transports across an isomorphism. -/
private theorem isFlatOfIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    {X Y : Mod(𝒪)}
    (e : X ≅ Y) (hX : IsFlat 𝒪 X) :
    IsFlat 𝒪 Y := by
  -- Proof comment: identify the two right-tensor functors through `tensoringRight` and transport
  -- the exactness witness from `X` to `Y`.
  refine ⟨?_⟩
  let eTensor :
      CategoryTheory.MonoidalCategory.tensorRight X ≅
        CategoryTheory.MonoidalCategory.tensorRight Y :=
    (CategoryTheory.MonoidalCategory.tensoringRight (Mod(𝒪))).mapIso e
  exact exactFunctorOfNatIso (𝒪 := 𝒪) eTensor hX.exact_tensor

/-- Helper for Lemma 21.17.8: the zero sheaf module is flat. -/
private theorem isFlatZero
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
    [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
    [∀ ℱ : ringedSiteModuleCategory J 𝒪,
      ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]
    [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
    [Zero (ringedSiteModuleCategory J 𝒪)] :
    IsFlat 𝒪 (0 : ringedSiteModuleCategory J 𝒪) := by
  let hTensorZero :
      IsZero (CategoryTheory.MonoidalCategory.tensorRight (0 : ringedSiteModuleCategory J 𝒪)) :=
    Functor.isZero _ fun (X : ringedSiteModuleCategory J 𝒪) ↦ by
      -- Proof comment: tensoring with the zero sheaf module stays zero objectwise.
      change IsZero (((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).obj
        (0 : ringedSiteModuleCategory J 𝒪))
      exact CategoryTheory.Functor.map_isZero
        ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X)
        (isZero_zero (ringedSiteModuleCategory J 𝒪))
  let _ :
      PreservesLimitsOfSize
        (CategoryTheory.MonoidalCategory.tensorRight (0 : ringedSiteModuleCategory J 𝒪)) :=
    CategoryTheory.Functor.preservesLimitsOfSize_of_isZero
      (CategoryTheory.MonoidalCategory.tensorRight (0 : ringedSiteModuleCategory J 𝒪))
      hTensorZero
  let _ :
      PreservesColimitsOfSize
        (CategoryTheory.MonoidalCategory.tensorRight (0 : ringedSiteModuleCategory J 𝒪)) :=
    CategoryTheory.Functor.preservesColimitsOfSize_of_isZero
      (CategoryTheory.MonoidalCategory.tensorRight (0 : ringedSiteModuleCategory J 𝒪))
      hTensorZero
  exact ⟨(CategoryTheory.exactFunctor_iff
    (CategoryTheory.MonoidalCategory.tensorRight (0 : ringedSiteModuleCategory J 𝒪))).2
      ⟨PreservesLimitsOfSize.preservesFiniteLimits
          (CategoryTheory.MonoidalCategory.tensorRight
            (0 : ringedSiteModuleCategory J 𝒪)),
        PreservesColimitsOfSize.preservesFiniteColimits
          (CategoryTheory.MonoidalCategory.tensorRight
            (0 : ringedSiteModuleCategory J 𝒪))⟩⟩

/-- Helper for Lemma 21.17.8: tensoring an acyclic complex on the right by a flat sheaf module
preserves acyclicity. -/
private theorem mapHomologicalComplex_acyclic_of_tensorRight_flat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (hL : L.Acyclic) (M : Mod(𝒪))
    (hM : IsFlat 𝒪 M) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).Acyclic := by
  let hExact :
      CategoryTheory.exactFunctor (Mod(𝒪)) (Mod(𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight M) :=
    hM.exact_tensor
  let _ :
      CategoryTheory.Limits.PreservesFiniteLimits
        (CategoryTheory.MonoidalCategory.tensorRight M) :=
    (CategoryTheory.exactFunctor_iff _).1 hExact |>.1
  let _ :
      CategoryTheory.Limits.PreservesFiniteColimits
        (CategoryTheory.MonoidalCategory.tensorRight M) :=
    (CategoryTheory.exactFunctor_iff _).1 hExact |>.2
  let _ :
      (CategoryTheory.MonoidalCategory.tensorRight M).Additive :=
    inferInstance
  let _ :
      (CategoryTheory.MonoidalCategory.tensorRight M).PreservesHomology :=
    inferInstance
  -- Proof comment: rewrite acyclicity degreewise and map the exact short complex `L.sc n`
  -- through the exact right-tensor functor.
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  intro n
  rw [HomologicalComplex.exactAt_iff]
  have hLn : (L.sc n).Exact := by
    -- Unpack acyclicity into exactness at the chosen degree.
    simpa [HomologicalComplex.exactAt_iff] using hL n
  simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
    hLn.map (CategoryTheory.MonoidalCategory.tensorRight M)

/-- Helper for Lemma 21.17.8: shifting a termwise-flat complex preserves termwise flatness. -/
private theorem isTermwiseFlatShift
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (K : CochainComplex (Mod(𝒪)) ℤ)
    (hFlat : IsTermwiseFlat K) (b : ℤ) :
    IsTermwiseFlat (K⟦b⟧) := by
  refine ⟨fun i ↦ ?_⟩
  have hKi : IsFlat 𝒪 (K.X (i + b)) := hFlat.isFlat (i + b)
  -- Proof comment: the degree-`i` term of `K⟦b⟧` is canonically the translated term of `K`.
  exact isFlatOfIso (𝒪 := 𝒪)
    (K.shiftFunctorObjXIso b i (i + b) rfl).symm hKi

/-- Helper for Lemma 21.17.8: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    {K L : CochainComplex (Mod(𝒪)) ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Proof comment: read acyclicity degreewise and move exactness across the complex isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK n) e

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 21.17.8: acyclicity is preserved by cochain shifts. -/
private theorem acyclic_shift
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [CategoryWithHomology (Mod(𝒪))]
    (K : CochainComplex (Mod(𝒪)) ℤ) (n : ℤ)
    (hK : K.Acyclic) :
    (K⟦n⟧).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let K' : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ := K
  let e :
      (K'⟦n⟧).homology i ≅ K'.homology (i + n) :=
    (CochainComplex.ShiftSequence.shiftIso (ringedSiteModuleCategory J 𝒪) n i (i + n)
      (add_comm n i)).app K'
  have hZero : IsZero (K.homology (i + n)) := by
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := K) (i := i + n)).1
      ((HomologicalComplex.acyclic_iff K).1 hK (i + n))
  exact hZero.of_iso e

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Helper for Lemma 21.17.8: if a shift of a cochain complex is acyclic, then the original
complex is acyclic. -/
private theorem acyclic_of_shift
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [CategoryWithHomology (Mod(𝒪))]
    (K : CochainComplex (Mod(𝒪)) ℤ) (n : ℤ)
    (hShift : (K⟦n⟧).Acyclic) :
    K.Acyclic := by
  -- Proof comment: shift back by `-n`, identify the double shift with `K`, and transport
  -- acyclicity across that canonical isomorphism.
  have hShiftBack : ((K⟦n⟧)⟦-n⟧).Acyclic :=
    acyclic_shift (𝒪 := 𝒪) (K := K⟦n⟧) (-n) hShift
  exact acyclic_of_iso (𝒪 := 𝒪) (shiftShiftNeg K n) hShiftBack

/-- Helper for Lemma 21.17.8: tensoring on the left by a fixed complex transports an isomorphism
in the right factor. -/
private noncomputable def tensorRightIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    {K L : CochainComplex (Mod(𝒪)) ℤ}
    [HomologicalComplex.HasTensor M K]
    [HomologicalComplex.HasTensor M L]
    (e : K ≅ L) :
    HomologicalComplex.tensorObj M K ≅ HomologicalComplex.tensorObj M L :=
  { hom := HomologicalComplex.tensorHom (𝟙 M) e.hom
    inv := HomologicalComplex.tensorHom (𝟙 M) e.inv
    hom_inv_id := by
      -- Proof comment: check the inverse relation on each tensor summand of every total degree.
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      have hhom :
          HomologicalComplex.ιTensorObj M K p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n =
            (M.X p ◁ e.hom.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
            (f₁ := 𝟙 M) (f₂ := e.hom) (F := curriedTensor (Mod(𝒪)))
            (c := ComplexShape.up ℤ) p q n h)
      have hinv :
          HomologicalComplex.ιTensorObj M L p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n =
            (M.X p ◁ e.inv.f q) ≫ HomologicalComplex.ιTensorObj M K p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := K)
            (f₁ := 𝟙 M) (f₂ := e.inv) (F := curriedTensor (Mod(𝒪)))
            (c := ComplexShape.up ℤ) p q n h)
      have hq :
          e.hom.f q ≫ e.inv.f q = 𝟙 (K.X q) := by
        exact congrArg (fun α : K ⟶ K ↦ α.f q) e.hom_inv_id
      calc
        HomologicalComplex.ιTensorObj M K p q n h ≫
            ((HomologicalComplex.tensorHom (𝟙 M) e.hom ≫
              HomologicalComplex.tensorHom (𝟙 M) e.inv).f n)
          = (M.X p ◁ e.hom.f q) ≫
              (HomologicalComplex.ιTensorObj M L p q n h ≫
                (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n) := by
                  simpa [HomologicalComplex.comp_f, Category.assoc] using
                    congrArg
                      (fun k ↦ k ≫ (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n)
                      hhom
        _ = (M.X p ◁ e.hom.f q) ≫
              ((M.X p ◁ e.inv.f q) ≫ HomologicalComplex.ιTensorObj M K p q n h) := by
                rw [hinv]
        _ = (M.X p ◁ (e.hom.f q ≫ e.inv.f q)) ≫
              HomologicalComplex.ιTensorObj M K p q n h := by
                rw [← Category.assoc, ← whiskerLeft_comp]
        _ = HomologicalComplex.ιTensorObj M K p q n h := by
          simp [hq]
    inv_hom_id := by
      -- Proof comment: the reverse inverse relation is the same computation with `e.inv_hom_id`.
      apply HomologicalComplex.hom_ext
      intro n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      have hhom :
          HomologicalComplex.ιTensorObj M L p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.inv).f n =
            (M.X p ◁ e.inv.f q) ≫ HomologicalComplex.ιTensorObj M K p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := K)
            (f₁ := 𝟙 M) (f₂ := e.inv) (F := curriedTensor (Mod(𝒪)))
            (c := ComplexShape.up ℤ) p q n h)
      have hinv :
          HomologicalComplex.ιTensorObj M K p q n h ≫
              (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n =
            (M.X p ◁ e.hom.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
        simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
          HomologicalComplex.id_f] using
          (HomologicalComplex.ι_mapBifunctorMap
            (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
            (f₁ := 𝟙 M) (f₂ := e.hom) (F := curriedTensor (Mod(𝒪)))
            (c := ComplexShape.up ℤ) p q n h)
      have hq :
          e.inv.f q ≫ e.hom.f q = 𝟙 (L.X q) := by
        exact congrArg (fun α : L ⟶ L ↦ α.f q) e.inv_hom_id
      calc
        HomologicalComplex.ιTensorObj M L p q n h ≫
            ((HomologicalComplex.tensorHom (𝟙 M) e.inv ≫
              HomologicalComplex.tensorHom (𝟙 M) e.hom).f n)
          = (M.X p ◁ e.inv.f q) ≫
              (HomologicalComplex.ιTensorObj M K p q n h ≫
                (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n) := by
                  simpa [HomologicalComplex.comp_f, Category.assoc] using
                    congrArg
                      (fun k ↦ k ≫ (HomologicalComplex.tensorHom (𝟙 M) e.hom).f n)
                      hhom
        _ = (M.X p ◁ e.inv.f q) ≫
              ((M.X p ◁ e.hom.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h) := by
                rw [hinv]
        _ = (M.X p ◁ (e.inv.f q ≫ e.hom.f q)) ≫
              HomologicalComplex.ιTensorObj M L p q n h := by
                rw [← Category.assoc, ← whiskerLeft_comp]
        _ = HomologicalComplex.ιTensorObj M L p q n h := by
          simp [hq] }

/-- Helper for Lemma 21.17.8: fixed-left tensoring commutes with shifts in the right argument. -/
private noncomputable def tensorRightShiftTransportIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L K : CochainComplex (Mod(𝒪)) ℤ) (b : ℤ)
    [HomologicalComplex.HasTensor L (K⟦b⟧)]
    [HomologicalComplex.HasTensor L K] :
    HomologicalComplex.tensorObj L (K⟦b⟧) ≅
      (HomologicalComplex.tensorObj L K)⟦b⟧ := by
  -- Proof comment: use the owner bifunctor/shift comparison directly for the tensor bifunctor.
  simpa using
    (CochainComplex.mapBifunctorShift₂Iso L K (curriedTensor (Mod(𝒪))) b)

/-- Helper for Lemma 21.17.8: K-flatness transports across an isomorphism of cochain complexes. -/
private theorem isKFlatOfIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    {K L : CochainComplex (Mod(𝒪)) ℤ}
    (e : K ≅ L) (hK : K.IsKFlat) :
    L.IsKFlat := by
  -- Proof comment: rewrite the tensor test for `K` along the induced isomorphism on the right
  -- tensor factor.
  rw [CochainComplex.isKFlat_iff] at hK ⊢
  intro M _ hM
  have hTensorK : (HomologicalComplex.tensorObj M K).Acyclic := hK hM
  let eTensor :
      HomologicalComplex.tensorObj M K ≅ HomologicalComplex.tensorObj M L :=
    tensorRightIso (𝒪 := 𝒪) M e
  exact acyclic_of_iso (𝒪 := 𝒪) eTensor hTensorK

/-- Helper for Lemma 21.17.8: shifting a single complex by its own degree identifies it with the
degree-zero single complex. -/
private noncomputable def singleShiftToZeroIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (M : Mod(𝒪)) (n : ℤ) :
    (((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M)⟦n⟧) ≅
      ((single₀).obj M) :=
  ((CochainComplex.singleFunctors (Mod(𝒪))).shiftIso n 0 n (by simp)).app M

/-- Helper for Lemma 21.17.8: postcompose the universal tensor-descended map with a chosen
morphism. -/
@[reassoc] private theorem iTensorObjMapBifunctorDescAssoc
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (K L : CochainComplex (Mod(𝒪)) ℤ) (n : ℤ) {A B : Mod(𝒪)}
    (f : ∀ p q
      (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (Mod(𝒪))).obj (K.X p)).obj (L.X q) ⟶ A)
    (u : A ⟶ B) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (Mod(𝒪)))
          (c := ComplexShape.up ℤ) (A := A) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Proof comment: this is just the owner universal property `ι_mapBifunctorDesc` with one
  -- extra postcomposition.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (Mod(𝒪)))
        (c := ComplexShape.up ℤ) (A := A) (j := n) (f := f) p q h)

/-- Helper for Lemma 21.17.8: away from degree `0`, the degree-zero single complex contributes a
zero summand to the tensor totalization. -/
private theorem tensorSingleZeroOffDiagonalIsZero
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((curriedTensor (Mod(𝒪))).obj (L.X p)).obj (((single₀).obj M).X q)) := by
  -- Proof comment: the unique nonzero degree of the single complex is degree `0`, and left
  -- tensoring preserves zero objects.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (Mod(𝒪))).obj (L.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M q hq)

/-- Helper for Lemma 21.17.8: on the surviving degree-zero tensor summand, tensoring with
`M[0]` identifies with right tensoring by `M`. -/
private noncomputable def tensorSingleZeroDiagonalIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (n : ℤ) :
    ((curriedTensor (Mod(𝒪))).obj (L.X n)).obj (((single₀).obj M).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X n := by
  -- Proof comment: degreewise right tensoring only sees the degree-zero component of the single
  -- complex.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (Mod(𝒪))).obj (L.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M)

/-- Helper for Lemma 21.17.8: the forward degreewise comparison keeps only the unique diagonal
summand of `L ⊗ M[0]`. -/
private noncomputable def tensorSingleZeroComponentHom
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (n : ℤ) :
    (HomologicalComplex.tensorObj L ((single₀).obj M)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := L)
    (K₂ := (single₀).obj M)
    (F := curriedTensor (Mod(𝒪)))
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n)
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).hom
      · exact 0)

/-- Helper for Lemma 21.17.8: on the diagonal summand, the forward comparison is the expected
degreewise identification. -/
private theorem tensorSingleZeroComponentHomDiag
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n h ≫
        tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n =
      (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).hom := by
  let A : Mod(𝒪) :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n
  let f : ∀ p q
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (Mod(𝒪))).obj (L.X p)).obj (((single₀).obj M).X q) ⟶ A :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).hom
      · exact 0
  -- Proof comment: evaluate the descended tensor map on the unique surviving diagonal summand.
  simpa [tensorSingleZeroComponentHom, A, f] using
    (iTensorObjMapBifunctorDescAssoc (𝒪 := 𝒪) L ((single₀).obj M) n f (𝟙 A) n 0 h)

/-- Helper for Lemma 21.17.8: off the diagonal, the forward comparison map vanishes. -/
private theorem tensorSingleZeroComponentHomOffDiagonal
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj L ((single₀).obj M) p q n h ≫
        tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n = 0 := by
  let A : Mod(𝒪) :=
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n
  let f : ∀ p' q'
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (Mod(𝒪))).obj (L.X p')).obj (((single₀).obj M).X q') ⟶ A :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).hom
      · exact 0
  -- Proof comment: away from the diagonal the defining branch of the descended map is literally
  -- zero.
  simpa [tensorSingleZeroComponentHom, A, f, hq] using
    (iTensorObjMapBifunctorDescAssoc (𝒪 := 𝒪) L ((single₀).obj M) n f (𝟙 A) p q h)

/-- Helper for Lemma 21.17.8: the inverse degreewise comparison reinserts the surviving diagonal
summand into the tensor totalization. -/
private noncomputable def tensorSingleZeroComponentInv
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).X n ⟶
      (HomologicalComplex.tensorObj L ((single₀).obj M)).X n :=
  (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).inv ≫
    HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n
      (by simpa using (show n + 0 = n by simp))

/-- Helper for Lemma 21.17.8: in each total degree, tensoring with the degree-zero single complex
collapses to right tensoring by that sheaf module. -/
private noncomputable def tensorSingleZeroComponentIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (n : ℤ) :
    (HomologicalComplex.tensorObj L ((single₀).obj M)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X n :=
  { hom := tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n
    inv := tensorSingleZeroComponentInv (𝒪 := 𝒪) L M n
    hom_inv_id := by
      -- Proof comment: check the identity summandwise; only the diagonal summand survives.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        change
          ((HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n h ≫
              tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n) ≫
            tensorSingleZeroComponentInv (𝒪 := 𝒪) L M n) =
            HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n h ≫
              𝟙 ((HomologicalComplex.tensorObj L ((single₀).obj M)).X n)
        simpa [tensorSingleZeroComponentInv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensorSingleZeroComponentInv (𝒪 := 𝒪) L M n)
            (tensorSingleZeroComponentHomDiag (𝒪 := 𝒪) L M n h)
      · change
          ((HomologicalComplex.ιTensorObj L ((single₀).obj M) p q n h ≫
              tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n) ≫
            tensorSingleZeroComponentInv (𝒪 := 𝒪) L M n) =
            HomologicalComplex.ιTensorObj L ((single₀).obj M) p q n h ≫
              𝟙 ((HomologicalComplex.tensorObj L ((single₀).obj M)).X n)
        rw [tensorSingleZeroComponentHomOffDiagonal (𝒪 := 𝒪) L M n p q h hq]
        simp only [zero_comp, Category.comp_id]
        symm
        exact (tensorSingleZeroOffDiagonalIsZero (𝒪 := 𝒪) L M p q hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simp
      -- Proof comment: the inverse lands in the diagonal summand and cancels there immediately.
      change
        ((tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).inv ≫
            HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n h0) ≫
          tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n =
            𝟙 ((((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).X n)
      calc
        ((tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).inv ≫
            HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n h0) ≫
          tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n
            = (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).inv ≫
                (HomologicalComplex.ιTensorObj L ((single₀).obj M) n 0 n h0 ≫
                  tensorSingleZeroComponentHom (𝒪 := 𝒪) L M n) := by
                    simp [Category.assoc]
        _ = (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).inv ≫
              (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).hom := by
                simpa using
                  congrArg
                    (fun k ↦ (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M n).inv ≫ k)
                    (tensorSingleZeroComponentHomDiag (𝒪 := 𝒪) L M n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Lemma 21.17.8: the diagonal comparison is natural in the differential of `L`. -/
private theorem tensorSingleZeroDiagonalIsoHomNaturality
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L).d i j =
      (((curriedTensor (Mod(𝒪))).map (L.d i j)).app (((single₀).obj M).X 0)) ≫
        (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M j).hom := by
  -- Proof comment: this is the `singleObjXSelf` naturality square after applying the tensor
  -- functor.
  simpa [tensorSingleZeroDiagonalIso, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    CochainComplex.singleFunctor] using
    (((curriedTensor (Mod(𝒪))).map (L.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M).hom)

/-- Helper for Lemma 21.17.8: the inverse diagonal comparison satisfies the same naturality
square rewritten for the inverse map. -/
private theorem tensorSingleZeroDiagonalIsoInvNaturality
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M i).inv ≫
        (((curriedTensor (Mod(𝒪))).map (L.d i j)).app (((single₀).obj M).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).d i j ≫
        (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M j).inv := by
  apply (cancel_mono (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M j).hom).1
  simpa [Category.assoc] using
    calc
      (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M i).inv ≫
          (((curriedTensor (Mod(𝒪))).map (L.d i j)).app (((single₀).obj M).X 0)) ≫
          (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M j).hom
        = (tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M i).inv ≫
            ((tensorSingleZeroDiagonalIso (𝒪 := 𝒪) L M i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L).d i j) := by
            rw [tensorSingleZeroDiagonalIsoHomNaturality (𝒪 := 𝒪) L M i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L).d i j := by
            simp [Category.assoc]

/-- Helper for Lemma 21.17.8: the inverse degreewise comparison already respects the cochain
differential. -/
private theorem tensorSingleZeroComponentInvComm
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensorSingleZeroComponentInv (𝒪 := 𝒪) L M i ≫
        (HomologicalComplex.tensorObj L ((single₀).obj M)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).d i j ≫
        tensorSingleZeroComponentInv (𝒪 := 𝒪) L M j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Proof comment: in the total tensor differential, the vertical piece vanishes because the
  -- degree-zero single complex has zero outgoing differential.
  simp only [tensorSingleZeroComponentInv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.single_obj_d, Functor.map_zero, comp_zero, add_zero]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := L) (K₂ := (single₀).obj M) (F := curriedTensor (Mod(𝒪)))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0) (j := i + 1)
      (h' := by simpa using (show (i + 1) + 0 = i + 1 by simp))]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := L) (K₂ := (single₀).obj M) (F := curriedTensor (Mod(𝒪)))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simpa using (show i + (0 + 1) = i + 1 by simp))]
  have hsingle : (((single₀).obj M).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, zero_comp, smul_zero, comp_zero, add_zero]
  rw [show ComplexShape.ε₁
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by rfl,
    one_smul]
  rw [← Category.assoc]
  rw [tensorSingleZeroDiagonalIsoInvNaturality (𝒪 := 𝒪) L M i (i + 1)
      (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 21.17.8: tensoring a cochain complex with the degree-zero single complex
`M[0]` is canonically the same as applying `tensorRight M` degreewise. -/
private noncomputable def tensorSingleZeroComplexIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (M : Mod(𝒪)) :
    HomologicalComplex.tensorObj L ((single₀).obj M) ≅
      ((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L :=
  let eInv :
      (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) ≅
        HomologicalComplex.tensorObj L ((single₀).obj M) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (tensorSingleZeroComponentIso (𝒪 := 𝒪) L M n).symm)
      (fun i j hij ↦ by
        simpa using tensorSingleZeroComponentInvComm (𝒪 := 𝒪) L M i j hij)
  eInv.symm

/-- Helper for Lemma 21.17.8: tensoring with a degree-zero single flat sheaf-module complex is
exactly right tensoring by that flat module. -/
private theorem tensorSingleZeroAcyclicOfFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L : CochainComplex (Mod(𝒪)) ℤ) (hL : L.Acyclic) (M : Mod(𝒪))
    (hM : IsFlat 𝒪 M) :
    (HomologicalComplex.tensorObj L ((single₀).obj M)).Acyclic := by
  -- Proof comment: transport acyclicity across the explicit comparison between `L ⊗ M[0]` and
  -- the mapped complex obtained from right tensoring by `M`.
  have hRightTensor :
      (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic :=
    mapHomologicalComplex_acyclic_of_tensorRight_flat (𝒪 := 𝒪) L hL M hM
  exact acyclic_of_iso (𝒪 := 𝒪) (tensorSingleZeroComplexIso (𝒪 := 𝒪) L M).symm hRightTensor

/-- Helper for Lemma 21.17.8: a single cochain complex on a flat sheaf module is K-flat. -/
private theorem singleIsKFlatOfFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : Mod(𝒪)) (n : ℤ) (hM : IsFlat 𝒪 M) :
    ((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M).IsKFlat := by
  -- Proof comment: shift the single complex to degree `0`, use the degree-zero tensor
  -- identification, and then descend acyclicity from the shifted tensor complex.
  rw [CochainComplex.isKFlat_iff]
  intro L _ hL
  have hZero :
      (HomologicalComplex.tensorObj L ((single₀).obj M)).Acyclic :=
    tensorSingleZeroAcyclicOfFlat (𝒪 := 𝒪) L hL M hM
  let eSingle :
      (((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M)⟦n⟧) ≅
        ((single₀).obj M) :=
    singleShiftToZeroIso (𝒪 := 𝒪) M n
  let eTensorSingle :
      HomologicalComplex.tensorObj L
          (((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M)⟦n⟧) ≅
        HomologicalComplex.tensorObj L
          ((single₀).obj M) :=
    tensorRightIso (𝒪 := 𝒪) L eSingle
  have hShiftSource :
      (HomologicalComplex.tensorObj L
        (((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M)⟦n⟧)).Acyclic :=
    acyclic_of_iso (𝒪 := 𝒪) eTensorSingle.symm hZero
  have hTensorShifted :
      ((HomologicalComplex.tensorObj L
        ((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M))⟦n⟧).Acyclic :=
    acyclic_of_iso (𝒪 := 𝒪)
      (tensorRightShiftTransportIso (𝒪 := 𝒪) L
        ((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M) n)
      hShiftSource
  rw [HomologicalComplex.acyclic_iff] at hTensorShifted ⊢
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hZeroShift :
      IsZero
        (((HomologicalComplex.tensorObj L
          ((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M))⟦n⟧).homology (i - n)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hTensorShifted (i - n)
  exact hZeroShift.of_iso
    (((HomologicalComplex.homologyFunctor (Mod(𝒪)) (ComplexShape.up ℤ) (0 : ℤ)).shiftIso
      n (i - n) i (by omega)).app
      (HomologicalComplex.tensorObj L ((CochainComplex.singleFunctor (Mod(𝒪)) n).obj M))).symm

/-- Helper for Lemma 21.17.8: the single quotient term in the brutal-left stage sequence is
termwise flat as soon as the original strictly nonpositive complex is termwise flat. -/
private theorem shiftedBrutalLeftStageSingleTermwiseFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    [HasZeroObject (Mod(𝒪))]
    (Q : CochainComplex (Mod(𝒪)) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : IsTermwiseFlat Q) (m : ℕ) :
    IsTermwiseFlat (shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m) := by
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i = -((m + 1 : ℕ) : ℤ)
  · subst hi
    let eDiag :
        ((shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m).X
          (-((m + 1 : ℕ) : ℤ))) ≅
          Q.X (-((m + 1 : ℕ) : ℤ)) :=
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((m + 1 : ℕ) : ℤ))
        (Q.X (-((m + 1 : ℕ) : ℤ)))
    exact isFlatOfIso (𝒪 := 𝒪) eDiag.symm (hFlat.isFlat _)
  · have hzero :
        IsZero ((shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m).X i) := by
      simpa [shifted_brutal_left_stage_single] using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
          (-((m + 1 : ℕ) : ℤ)) (Q.X (-((m + 1 : ℕ) : ℤ))) i hi)
    -- Proof comment: away from the cutoff degree the single complex term is zero, and the zero
    -- sheaf module is flat.
    let _ : HasZeroObject (Mod(𝒪)) := by infer_instance
    let _ : Zero (Mod(𝒪)) := CategoryTheory.Limits.HasZeroObject.zero' (Mod(𝒪))
    exact isFlatOfIso (𝒪 := 𝒪) (hzero.isoZero).symm (isFlatZero (𝒪 := 𝒪))

/-- Helper for Lemma 21.17.8: the initial brutal-left stage is concentrated in degree `0`, hence
K-flat. -/
private theorem shiftedBrutalLeftStageZeroIsKFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (Q : CochainComplex (Mod(𝒪)) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : IsTermwiseFlat Q) :
    (shifted_brutal_left_stage (A := Mod(𝒪)) Q 0).IsKFlat := by
  let K₀ : CochainComplex (Mod(𝒪)) ℤ :=
    shifted_brutal_left_stage (A := Mod(𝒪)) Q 0
  letI : K₀.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    refine Q.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (0 : ℤ)) i ?_
    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi
  letI : K₀.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    by_cases h0i : (0 : ℤ) ≤ i
    · let e := shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q 0 h0i
      have hzero : IsZero (Q.X i) := by
        simpa using Q.isZero_of_isStrictlyLE 0 i hi
      exact hzero.of_iso e
    · refine Q.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (0 : ℤ)) i ?_
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge h0i
  let M₀ : Mod(𝒪) := Classical.choose (CochainComplex.exists_iso_single (K := K₀) 0)
  let e₀ : K₀ ≅ ((single₀).obj M₀) := by
    simpa using
      (Classical.choice (Classical.choose_spec (CochainComplex.exists_iso_single (K := K₀) 0)))
  let eX :
      K₀.X 0 ≅ M₀ :=
    (HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) 0).mapIso e₀ ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M₀
  have hK₀X₀ : IsFlat 𝒪 (K₀.X 0) := by
    let eQ :
        K₀.X 0 ≅ Q.X 0 :=
      shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q 0 (by simp)
    exact isFlatOfIso (𝒪 := 𝒪) eQ.symm (hFlat.isFlat 0)
  have hM₀ : IsFlat 𝒪 M₀ := by
    exact isFlatOfIso (𝒪 := 𝒪) eX hK₀X₀
  have hSingle : ((single₀).obj M₀).IsKFlat :=
    singleIsKFlatOfFlat (𝒪 := 𝒪) M₀ 0 hM₀
  exact isKFlatOfIso (𝒪 := 𝒪) e₀.symm hSingle

/-- Helper for Lemma 21.17.8: every finite brutal-left stage of a strictly nonpositive
termwise-flat complex is K-flat. -/
private theorem shiftedBrutalLeftStageIsKFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (Q : CochainComplex (Mod(𝒪)) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : IsTermwiseFlat Q) :
    ∀ m : ℕ, (shifted_brutal_left_stage (A := Mod(𝒪)) Q m).IsKFlat
  | 0 => by
      -- Proof comment: the initial brutal-left stage is concentrated in degree `0`.
      exact shiftedBrutalLeftStageZeroIsKFlat (𝒪 := 𝒪) Q hFlat
  | m + 1 => by
      let S : ShortComplex (CochainComplex (Mod(𝒪)) ℤ) :=
        shifted_brutal_left_stage_short_complex_sign_corrected
          (A := Mod(𝒪)) Q m
      have hS : S.ShortExact :=
        shifted_brutal_left_stage_short_exact_sign_corrected
          (A := Mod(𝒪)) Q m
      have hStage : S.X₁.IsKFlat := by
        change (shifted_brutal_left_stage (A := Mod(𝒪)) Q m).IsKFlat
        exact shiftedBrutalLeftStageIsKFlat Q hFlat m
      have hSingleFlat : IsTermwiseFlat S.X₃ := by
        change SheafOfModules.RingedSite.CochainComplex.IsTermwiseFlat
          (shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m)
        refine ⟨fun i ↦ ?_⟩
        by_cases hi : i = -((m + 1 : ℕ) : ℤ)
        · subst hi
          let eDiag :
              ((shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m).X
                (-((m + 1 : ℕ) : ℤ))) ≅
                Q.X (-((m + 1 : ℕ) : ℤ)) :=
            HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-((m + 1 : ℕ) : ℤ))
              (Q.X (-((m + 1 : ℕ) : ℤ)))
          exact isFlatOfIso (𝒪 := 𝒪) eDiag.symm (hFlat.isFlat _)
        · have hzero :
              IsZero ((shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m).X i) := by
            simpa [shifted_brutal_left_stage_single] using
              (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
                (-((m + 1 : ℕ) : ℤ)) (Q.X (-((m + 1 : ℕ) : ℤ))) i hi)
          let _ : HasZeroObject (Mod(𝒪)) := by infer_instance
          let _ : Zero (Mod(𝒪)) := CategoryTheory.Limits.HasZeroObject.zero' (Mod(𝒪))
          exact isFlatOfIso (𝒪 := 𝒪) (hzero.isoZero).symm (isFlatZero (𝒪 := 𝒪))
      have hSingle : S.X₃.IsKFlat := by
        change (shifted_brutal_left_stage_single (A := Mod(𝒪)) Q m).IsKFlat
        simpa [shifted_brutal_left_stage_single] using
          singleIsKFlatOfFlat (𝒪 := 𝒪)
            (Q.X (-((m + 1 : ℕ) : ℤ))) (-((m + 1 : ℕ) : ℤ))
            (hFlat.isFlat (-((m + 1 : ℕ) : ℤ)))
      have hMiddle : S.X₂.IsKFlat :=
        SheafOfModules.RingedSite.isKFlat_X₂
          (𝒪 := 𝒪) (S := S) hS hSingleFlat hStage hSingle
      change (shifted_brutal_left_stage (A := Mod(𝒪)) Q (m + 1)).IsKFlat
      simpa [S] using hMiddle

/-- Helper for Lemma 21.17.8: a strictly nonpositive termwise-flat complex is K-flat. -/
private theorem isKFlatOfStrictlyLEZeroOfTermwiseFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (Q : CochainComplex (Mod(𝒪)) ℤ) [Q.IsStrictlyLE 0]
    (hFlat : IsTermwiseFlat Q) :
    Q.IsKFlat := by
  let Q' : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ := Q
  let stage : ℕ → CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ :=
    shifted_brutal_left_stage Q'
  let step :
      ∀ n : ℕ, stage n ⟶ stage (n + 1) :=
    shifted_brutal_left_stage_step_sign_corrected Q'
  let F : ℕ ⥤ CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ :=
    Functor.ofSequence step
  let inclComp :
      (n : ℕ) → (i : ℤ) → (stage n).X i ⟶ Q'.X i :=
    fun n i ↦
      if hi : -((n : ℕ) : ℤ) ≤ i then
        (shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q n hi).hom
      else
        0
  have inclComm :
      ∀ (n : ℕ) {i j : ℤ}, (ComplexShape.up ℤ).Rel i j →
        inclComp n i ≫ Q.d i j =
          (shifted_brutal_left_stage (A := Mod(𝒪)) Q n).d i j ≫ inclComp n j := by
    intro n i j hij
    have hij' : i + 1 = j := by
      simpa [ComplexShape.up, eq_comm] using hij
    by_cases hi : -((n : ℕ) : ℤ) ≤ i
    · have hj : -((n : ℕ) : ℤ) ≤ j := by
        omega
      apply (cancel_epi (shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q n hi).inv).1
      rw [show inclComp n i =
          (shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q n hi).hom by
            simp [inclComp, hi]]
      rw [show inclComp n j =
          (shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q n hj).hom by
            simp [inclComp, hj]]
      repeat rw [Category.assoc]
      rw [Iso.inv_hom_id_assoc]
      exact (shifted_brutal_left_stage_d_via_x_iso (A := Mod(𝒪)) (K := Q) (n := n) hi hj).symm
    · by_cases hj : -((n : ℕ) : ℤ) ≤ j
      · have hi_lt : i < -((n : ℕ) : ℤ) := by
          omega
        have hzero : IsZero ((shifted_brutal_left_stage (A := Mod(𝒪)) Q n).X i) := by
          exact (shifted_brutal_left_stage (A := Mod(𝒪)) Q n).isZero_of_isStrictlyGE
            (-((n : ℕ) : ℤ)) i hi_lt
        rw [show inclComp n i = 0 by simp [inclComp, hi], zero_comp]
        rw [show inclComp n j =
            (shifted_brutal_left_stage_x_iso (A := Mod(𝒪)) Q n hj).hom by
              simp [inclComp, hj]]
        exact hzero.eq_of_src _ _
      · have hj_lt : j < -((n : ℕ) : ℤ) := by
          omega
        rw [show inclComp n i = 0 by simp [inclComp, hi], zero_comp]
        rw [show inclComp n j = 0 by simp [inclComp, hj], comp_zero]
  let incl :
      (n : ℕ) → stage n ⟶ Q' :=
    fun n ↦
      { f := inclComp n
        comm' := fun i j hij ↦ inclComm n hij }
  have stepCompIncl :
      ∀ n : ℕ,
        step n ≫ incl (n + 1) =
          incl n := by
    intro n
    ext i
    by_cases hi : -((n : ℕ) : ℤ) ≤ i
    · have hi' : -((n + 1 : ℕ) : ℤ) ≤ i := by
        omega
      rw [HomologicalComplex.comp_f]
      simp [incl, inclComp, hi, hi', Category.assoc]
    · rw [HomologicalComplex.comp_f]
      simp [incl, inclComp, hi]
  let c : Cocone F :=
    { pt := Q
      ι := NatTrans.ofSequence
        (fun n ↦ incl n)
        (fun n ↦ by
          simpa [F] using stepCompIncl n) }
  have eventualStageLE : ∀ i : ℤ, -((Int.toNat (-i) : ℕ) : ℤ) ≤ i := by
    intro i
    by_cases hi : 0 ≤ i
    · rw [Int.toNat_of_nonpos (by omega)]
      omega
    · rw [Int.toNat_of_nonneg (by omega)]
      omega
  have evalIsColimit :
      ∀ i : ℤ, IsColimit ((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i).mapCocone c) := by
    intro i
    let n : ℕ := Int.toNat (-i)
    have hn : -((n : ℕ) : ℤ) ≤ i := eventualStageLE i
    let cEval : Cocone (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) :=
      (HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i).mapCocone c
    letI : IsIso (cEval.ι.app n) := by
      change IsIso ((incl n).f i)
      simp [incl, inclComp, hn]
    refine IsEssentiallyConstantFilteredCocone.isColimit ?_
    refine ⟨n, ⟨(asIso (cEval.ι.app n)).inv, ?_⟩, ?_⟩
    · simp
    · intro j
      let k := max n j
      have hk : -((k : ℕ) : ℤ) ≤ i := by
        dsimp [k]
        omega
      letI : IsIso (cEval.ι.app k) := by
        change IsIso ((incl k).f i)
        simp [incl, inclComp, hk]
      refine ⟨k, homOfLE (Nat.le_max_left _ _), homOfLE (Nat.le_max_right _ _), ?_⟩
      apply (cancel_mono (cEval.ι.app k)).1
      rw [Category.assoc]
      have hjk :
          (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i).map
              (homOfLE (Nat.le_max_right n j)) ≫
            cEval.ι.app k =
              cEval.ι.app j := by
        simpa [cEval, k] using cEval.w (homOfLE (Nat.le_max_right n j))
      have hnk :
          (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i).map
              (homOfLE (Nat.le_max_left n j)) ≫
            cEval.ι.app k =
              cEval.ι.app n := by
        simpa [cEval, k] using cEval.w (homOfLE (Nat.le_max_left n j))
      rw [hjk, Category.assoc, hnk, Iso.inv_hom_id_assoc]
  let _ : HasColimit F := inferInstance
  have hColim : (colimit F).IsKFlat := by
    -- Proof comment: every finite brutal-left stage is K-flat, so Lemma 21.17.9 applies to `F`.
    exact SheafOfModules.RingedSite.sequentialColimit_isKFlat
      (𝒪 := 𝒪) F
      (fun n ↦ by
        simpa [F, stage] using shiftedBrutalLeftStageIsKFlat (𝒪 := 𝒪) Q hFlat n)
  let e : colimit F ≅ Q :=
    ((HomologicalComplex.isColimitOfEval (F := F) (s := c) evalIsColimit).coconePointUniqueUpToIso
      (colimit.isColimit F)).symm
  -- Proof comment: the brutal-left tower has colimit `Q`, so K-flatness transports from that
  -- colimit object back to `Q`.
  exact isKFlatOfIso (𝒪 := 𝒪) e hColim

/-- Helper for Lemma 21.17.8: after shifting the bounded-above flat complex to cutoff `0`, the
remaining source-faithful step is to show tensoring any acyclic test complex stays acyclic. -/
private theorem acyclicTensorOfAcyclicOfStrictlyLEZeroOfTermwiseFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))] [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (L Q : CochainComplex (Mod(𝒪)) ℤ)
    (hL : L.Acyclic) [Q.IsStrictlyLE 0]
    (hFlat : IsTermwiseFlat Q) :
    (HomologicalComplex.tensorObj L Q).Acyclic := by
  -- Route correction: replace the earlier spectral-sequence stub with the finite brutal-left
  -- filtration and sequential-colimit K-flat argument on `Q`.
  have hQKFlat : Q.IsKFlat :=
    isKFlatOfStrictlyLEZeroOfTermwiseFlat (𝒪 := 𝒪) Q hFlat
  exact CochainComplex.acyclic_tensorObj_of_isKFlat hQKFlat hL

-- Proof sketch: let `ℒ` be an acyclic complex of `𝒪`-modules. Write `ℒ` as the
-- termwise filtered colimit of its bounded-above truncations `τ≤m ℒ`, so the total tensor
-- product with `K` is the corresponding filtered colimit of the total tensors with these
-- truncations. It is therefore enough to treat bounded-above acyclic `ℒ`. For such `ℒ`, apply the
-- homology spectral sequence of the double complex `ℒ ⊗ K`; the `E₁`-page is
-- `H^p(ℒ ⊗ K^q)`, which vanishes because each term `K^q` is flat and `ℒ` is acyclic. Hence the
-- total tensor product is acyclic, so `K` is K-flat.
--
-- The site hypotheses `[HasWeakSheafify J AddCommGrpCat.{max u v}]` and
-- `[J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]` only supply ambient exactness and tensor
-- infrastructure on `Mod(𝒪)`; they are proof data rather than source-facing inputs of the bounded
-- above flat criterion.
omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Lemma 21.17.8: a bounded above termwise-flat cochain complex of `𝒪`-modules on a
ringed site `(C, 𝒪)` is K-flat, expressed in the canonical owners
`CochainComplex.IsTermwiseFlat` and `K.IsKFlat`. -/
@[stacks 06YQ]
theorem isKFlat_of_boundedAbove_of_flat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))] [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (K : CochainComplex (Mod(𝒪)) ℤ)
    (hbounded : CochainComplex.minus (Mod(𝒪)) K)
    (hFlat : IsTermwiseFlat K) :
    K.IsKFlat := by
  -- Route correction: normalize the bounded-above complex by a shift to a strictly nonpositive
  -- model `Q := K⟦b⟧`; the first remaining blocker is the tensor-acyclicity statement for that
  -- shifted model.
  rw [CochainComplex.isKFlat_iff]
  intro L _ hL
  obtain ⟨b, hLE⟩ := (CochainComplex.minus_iff (Mod(𝒪)) K).1 hbounded
  let Q : CochainComplex (Mod(𝒪)) ℤ := K⟦b⟧
  have hQLE : Q.IsStrictlyLE 0 := by
    letI : K.IsStrictlyLE b := hLE
    simpa [Q] using
      CochainComplex.isStrictlyLE_shift (K := K) b b 0 (by simp)
  letI : Q.IsStrictlyLE 0 := hQLE
  have hQFlat : IsTermwiseFlat Q :=
    isTermwiseFlatShift (𝒪 := 𝒪) K hFlat b
  have hTensorShift :
      (HomologicalComplex.tensorObj L Q).Acyclic :=
    acyclicTensorOfAcyclicOfStrictlyLEZeroOfTermwiseFlat
      (𝒪 := 𝒪) L Q hL hQFlat
  have hTensorShifted :
      ((HomologicalComplex.tensorObj L K)⟦b⟧).Acyclic :=
    acyclic_of_iso (𝒪 := 𝒪)
      (tensorRightShiftTransportIso (𝒪 := 𝒪) L K b)
      (by simpa [Q] using hTensorShift)
  -- Proof comment: once the shifted tensor complex is acyclic, descend along the shift
  -- comparison to recover acyclicity of `L ⊗ K`.
  rw [HomologicalComplex.acyclic_iff] at hTensorShifted ⊢
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hZeroShift : IsZero (((HomologicalComplex.tensorObj L K)⟦b⟧).homology (i - b)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hTensorShifted (i - b)
  exact hZeroShift.of_iso
    (((HomologicalComplex.homologyFunctor (Mod(𝒪)) (ComplexShape.up ℤ) (0 : ℤ)).shiftIso
      b (i - b) i (by omega)).app (HomologicalComplex.tensorObj L K)).symm

end SheafOfModules.RingedSite
