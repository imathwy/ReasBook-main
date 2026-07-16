import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.stacks_project.Chap12.Lemma_12_7_2
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap18.«18_19_2_1»
import StacksProject_2024.stacks_project.Chap18.Remark_18_19_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero
open scoped PresheafOfModules.Monoidal

noncomputable section

universe u

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Helper for Lemma 18.28.8: in an abelian setting, preserving monomorphisms together with
finite colimits upgrades a functor to an exact functor. -/
private theorem exactOfPreservesMonomorphismsAndFiniteColimits
    {A : Type*} {B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B)
    [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    (hMono : F.PreservesMonomorphisms) :
    exactFunctor A B F := by
  let _ : F.PreservesMonomorphisms := hMono
  let _ : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  -- Proof comment: in an abelian category, homology preservation recovers finite-limit
  -- preservation, so exactness reduces to the formal finite-colimit half.
  exact
    (CategoryTheory.exactFunctor_iff F).2
      ⟨F.preservesFiniteLimits_of_preservesHomology, inferInstance⟩

/-- Helper for Lemma 18.28.8: the localized structure module `\mathcal O_U` on `C/U`, regarded
as a module over the restricted ring presheaf. -/
private abbrev localizedStructureModule
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules ((Over.forget U).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.unit ((Over.forget U).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat))

/-- Helper for Lemma 18.28.8: the presheaf lower-shriek `j_{U!}\mathcal O_U`, obtained by
extending the localized structure module by zero from `C/U` back to `C`. -/
private abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pullback
      (𝟙 ((Over.forget U).op ⋙ (𝒪 ⋙ forget₂ CommRingCat RingCat)))).obj
    (localizedStructureModule 𝒪 U)

/-- Helper for Lemma 18.28.8: the presheaf `ℱ` restricted to the slice category `C/U` via the
extension-by-zero adjunction. -/
private abbrev localizedPushforward
    (U : C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    PresheafOfModules ((Over.forget U).op ⋙ ringPresheaf 𝒪) :=
  (PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ ringPresheaf 𝒪))).obj ℱ

/-- Helper for Lemma 18.28.8: sections of the restricted presheaf module on `C/U` are computed by
evaluating at the terminal object `U ⟶ U`. -/
private noncomputable def localizedSectionsEquivEvaluation
    (U : C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    (localizedPushforward (𝒪 := 𝒪) U ℱ).sections ≃
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (localizedPushforward (𝒪 := 𝒪) U ℱ).sectionsMk
      (fun X ↦ (localizedPushforward (𝒪 := 𝒪) U ℱ).map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun X Y f ↦ by
        -- Each component is the restriction of the terminal value along the unique map to `U`.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A section over the slice site is determined by its values on the unique terminal maps.
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Evaluating the reconstructed section at the terminal object recovers the original value.
    change
      (localizedPushforward (𝒪 := 𝒪) U ℱ).map
          ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (localizedPushforward (𝒪 := 𝒪) U ℱ).congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.28.8: morphisms from `j_{U!}\mathcal O_U` into a presheaf module are the
same as sections over `U`. -/
private noncomputable def localizedStructureModuleExtensionByZero_homEquiv
    (U : C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    (localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) ≃
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op U)).obj ℱ :=
  (((PresheafOfModules.pullbackPushforwardAdjunction
      (𝟙 ((Over.forget U).op ⋙ (ringPresheaf 𝒪)))).homEquiv
      (localizedStructureModule 𝒪 U) ℱ).trans
    (PresheafOfModules.unitHomEquiv (localizedPushforward (𝒪 := 𝒪) U ℱ))).trans
    (localizedSectionsEquivEvaluation (𝒪 := 𝒪) U ℱ)

/-- Helper for Lemma 18.28.8: the presheaf lower-shriek Hom/evaluation equivalence is natural in
the target module. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivNaturality
    (U : C) {ℱ 𝒢 : PresheafOfModules (ringPresheaf 𝒪)}
    (β : localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) U 𝒢 (β ≫ α) =
      ((PresheafOfModules.evaluation (ringPresheaf 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) U ℱ β) := by
  -- The owner equivalence is assembled from target-functorial constructions, so this is
  -- definitional.
  rfl

/-- Helper for Lemma 18.28.8: morphisms out of a coproduct of presheaf lower-shriek modules are
exactly families of chosen sections. -/
private noncomputable def localizedStructureModuleExtensionByZeroCoproductHomEquiv
    {I : Type u} (U : I → C) (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    ((∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ) ≃
      (∀ i : I, (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op (U i))).obj ℱ) where
  toFun α i :=
    localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ
      (Sigma.ι (fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫ α)
  invFun s :=
    Sigma.desc
      (fun i : I ↦
        (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ).symm (s i))
  left_inv α := by
    -- A morphism out of the coproduct is determined by its restrictions to the summands.
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply
      (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ)
      (Sigma.ι (fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫ α)
  right_inv s := by
    -- Evaluating the reconstructed morphism on each summand recovers the prescribed section.
    funext i
    change
      localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ
        (Sigma.ι (fun k : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U k)) i ≫
          Sigma.desc
            (fun k : I ↦
              (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U k) ℱ).symm
                (s k))) = s i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ)
      (s i)

/-- Helper for Lemma 18.28.8: evaluating one presheaf lower-shriek at `V` gives a coproduct of
copies of `\mathcal O(V)`. -/
private noncomputable abbrev localizedStructureModuleExtensionByZeroObjIsoCoproduct
    (U V : C) :
    ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V)) ≅
      (∐ fun _φ : V ⟶ U ↦ ModuleCat.of (𝒪.obj (op V)) (𝒪.obj (op V))) := by
  -- Proof comment: specialize the extension-by-zero fiber formula to the unit module on `C/U`.
  simpa [localizedStructureModuleExtensionByZero, localizedStructureModule] using
    (presheafLocalizedExtensionByZero_objIsoSigma
      (𝒪 := 𝒪 ⋙ forget₂ CommRingCat RingCat)
      (U := U) (𝒢 := localizedStructureModule 𝒪 U) V)

/-- Helper for Lemma 18.28.8: each section module of a presheaf lower-shriek is flat. -/
private theorem localizedStructureModuleExtensionByZeroObjFlat
    (U V : C) :
    Module.Flat (𝒪.obj (op V)) ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V)) := by
  classical
  let R := 𝒪.obj (op V)
  let Z : (V ⟶ U) → ModuleCat R := fun _ ↦ ModuleCat.of R R
  let eCoproduct :
      ((localizedStructureModuleExtensionByZero 𝒪 U).obj (op V)) ≅ ∐ Z :=
    localizedStructureModuleExtensionByZeroObjIsoCoproduct (𝒪 := 𝒪) U V
  let eDirectSum : (∐ Z) ≅ ModuleCat.of R (DirectSum (V ⟶ U) fun _ ↦ R) :=
    ModuleCat.coprodIsoDirectSum (R := R) Z
  letI : ∀ φ : V ⟶ U, Module.Flat R (R : Type u) := fun _ ↦ Module.Flat.self
  letI : Module.Flat R (DirectSum (V ⟶ U) fun _ ↦ R) := Module.Flat.directSum
  -- Proof comment: the evaluated lower-shriek is a direct sum of free rank-one modules.
  exact Module.Flat.of_linearEquiv ((eCoproduct ≪≫ eDirectSum).toLinearEquiv)

/-- Helper for Lemma 18.28.8: the specific coproduct source in part `(1)` is a flat presheaf. -/
private theorem localizedStructureModuleExtensionByZeroCoproductObjFlat
    {I : Type u} (U : I → C) (V : C) :
    Module.Flat (𝒪.obj (op V))
      ((∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)).obj (op V)) := by
  classical
  let R := 𝒪.obj (op V)
  let F : I → PresheafOfModules (ringPresheaf 𝒪) :=
    fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)
  let G : I → ModuleCat R := fun i ↦ (F i).obj (op V)
  let eEval :
      ((∐ F).obj (op V)) ≅ colimit
        ((Discrete.functor F) ⋙ PresheafOfModules.evaluation (ringPresheaf 𝒪) (op V)) :=
    preservesColimitIso
      (PresheafOfModules.evaluation (ringPresheaf 𝒪) (op V))
      (Discrete.functor F)
  let eDiagram :
      ((Discrete.functor F) ⋙ PresheafOfModules.evaluation (ringPresheaf 𝒪) (op V)) ≅
        Discrete.functor G :=
    NatIso.ofComponents (fun i ↦ Iso.refl _) (fun {i j} f ↦ by
      cases i
      cases j
      cases Discrete.eq_of_hom f
      simp [F, G])
  let eDirectSum :
      (∐ G) ≅ ModuleCat.of R (DirectSum I fun i ↦ G i) :=
    ModuleCat.coprodIsoDirectSum (R := R) G
  letI : ∀ i : I, Module.Flat R (G i) :=
    fun i ↦ localizedStructureModuleExtensionByZeroObjFlat (𝒪 := 𝒪) (U i) V
  letI : Module.Flat R (DirectSum I fun i ↦ G i) := Module.Flat.directSum
  -- Proof comment: evaluation preserves the coproduct, and the evaluated diagram is literally the
  -- discrete family of section modules indexed by `I`.
  let eColim :
      colimit ((Discrete.functor F) ⋙ PresheafOfModules.evaluation (ringPresheaf 𝒪) (op V)) ≅
        ∐ G :=
    HasColimit.isoOfNatIso eDiagram
  exact Module.Flat.of_linearEquiv ((eEval ≪≫ eColim ≪≫ eDirectSum).toLinearEquiv)

/-- Helper for Lemma 18.28.8: tensoring with the coproduct source from part `(1)` preserves
monomorphisms because its sections are flat modules. -/
private theorem localizedStructureModuleExtensionByZeroCoproduct_tensorPreservesMonomorphisms
    {I : Type u} (U : I → C) :
    (CategoryTheory.MonoidalCategory.tensorRight
      (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))).PreservesMonomorphisms := by
  refine ⟨fun {M N} α _ ↦ ?_⟩
  -- Proof comment: monomorphisms of presheaves of modules are checked sectionwise, and tensoring
  -- a sectionwise monomorphism with a flat section module stays injective.
  refine PresheafOfModules.mono_of_injective ?_
  intro X
  have hαinj :
      Function.Injective (ModuleCat.Hom.hom (α.app X)) :=
    PresheafOfModules.injective_of_mono α X
  letI :
      Module.Flat (𝒪.obj X)
        ((∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)).obj X) := by
    simpa using localizedStructureModuleExtensionByZeroCoproductObjFlat (𝒪 := 𝒪) U (unop X)
  simpa using
    Module.Flat.rTensor_preserves_injective_linearMap
      (R := 𝒪.obj X)
      (M := (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)).obj X)
      (f := ModuleCat.Hom.hom (α.app X))
      hαinj

/-- Helper for Lemma 18.28.8: the specific coproduct source in part `(1)` is a flat presheaf. -/
private theorem localizedStructureModuleExtensionByZeroCoproduct_isFlat
    {I : Type u} (U : I → C) :
    IsFlat (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) := by
  let F := CategoryTheory.MonoidalCategory.tensorRight
    (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
  have hMono : F.PreservesMonomorphisms :=
    localizedStructureModuleExtensionByZeroCoproduct_tensorPreservesMonomorphisms (𝒪 := 𝒪) U
  let _ : F.Additive :=
    CategoryTheory.functor_additive_of_leftExact_or_rightExact (F := F)
      (.inr ((CategoryTheory.rightExactFunctor_iff F).2 inferInstance))
  -- Proof comment: tensoring on the right is formally right exact, and the objectwise flatness of
  -- the chosen coproduct source shows that it also preserves monomorphisms.
  exact ⟨exactOfPreservesMonomorphismsAndFiniteColimits F hMono⟩

-- Proof sketch: for each pair `(U, s)` with `U : C` and `s ∈ ℱ(U)`, the adjunction defining
-- `j_{U!}` gives a morphism `j_{U!}\mathcal O_U ⟶ ℱ` sending `1` to `s`. Taking the coproduct over
-- all such pairs yields a morphism whose components generate every section objectwise, hence an
-- epimorphism.
/-- Lemma 18.28.8 (1): any presheaf of `\mathcal O`-modules is the quotient of a direct sum of
lower-shriek modules `j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ), Epi φ := by
  let I : Type u := Σ U : C, ℱ.obj (op U)
  let U : I → C := fun i ↦ i.1
  let φ : (∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ :=
    (localizedStructureModuleExtensionByZeroCoproductHomEquiv (𝒪 := 𝒪) U ℱ).symm
      (fun i ↦ i.2)
  refine ⟨I, U, φ, ?_⟩
  refine ⟨?_⟩
  intro 𝒢 α β hαβ
  -- Compare the two composites on the summand indexed by the section being tested.
  ext V s
  let i : I := ⟨V.unop, s⟩
  have hcomp := congrArg
    (fun ψ ↦ (localizedStructureModuleExtensionByZeroCoproductHomEquiv (𝒪 := 𝒪) U 𝒢) ψ)
    hαβ
  have hi := congrFun hcomp i
  have hi' :
      localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ) ≫ α) =
        localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ) ≫ β) := by
    simpa only [localizedStructureModuleExtensionByZeroCoproductHomEquiv] using hi
  have hφi :
      localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) ℱ
          (Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ) = s := by
    let hφfam := Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZeroCoproductHomEquiv (𝒪 := 𝒪) U ℱ)
      (fun j : I ↦ j.2)
    have hφi' := congrFun hφfam i
    simpa [I, U, i, φ, localizedStructureModuleExtensionByZeroCoproductHomEquiv] using hφi'
  have hleft :
      localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ) ≫ α) =
        ((PresheafOfModules.evaluation (ringPresheaf 𝒪) (op (U i))).map α) s := by
    rw [localizedStructureModuleExtensionByZeroHomEquivNaturality
      (𝒪 := 𝒪) (U := U i)
      (β := Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ)
      (α := α)]
    rw [hφi]
  have hright :
      localizedStructureModuleExtensionByZero_homEquiv (𝒪 := 𝒪) (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ) ≫ β) =
        ((PresheafOfModules.evaluation (ringPresheaf 𝒪) (op (U i))).map β) s := by
    rw [localizedStructureModuleExtensionByZeroHomEquivNaturality
      (𝒪 := 𝒪) (U := U i)
      (β := Sigma.ι (fun j : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ φ)
      (α := β)]
    rw [hφi]
  rw [hleft, hright] at hi'
  simpa [I, U, i] using hi'

-- Proof sketch: apply part `(1)` to obtain an epimorphism from a coproduct of the modules
-- `j_{U_i!}\mathcal O_{U_i}`. Each summand is flat by Lemma `18.28.7 (1)`, and the coproduct is
-- flat by Lemma `18.28.5 (2)`, giving a flat source surjecting onto `ℱ`.
/-- Lemma 18.28.8 (2): any presheaf of `\mathcal O`-modules is the quotient of a flat presheaf of
`\mathcal O`-modules. -/
theorem exists_epi_from_flat
    (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) :
    ∃ (𝒢 : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))
      (_h𝒢 : IsFlat 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := by
  rcases exists_epi_from_coproduct_localizedStructureModuleExtensionByZero (𝒪 := 𝒪) ℱ with
    ⟨I, U, φ, hφ⟩
  refine ⟨∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i), ?_, φ, hφ⟩
  -- Route correction: avoid the broken general coproduct-flatness import and prove flatness only
  -- for the specific coproduct source already constructed in part `(1)`.
  exact localizedStructureModuleExtensionByZeroCoproduct_isFlat (𝒪 := 𝒪) U

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪
local notation "PModS(" 𝒪 ")" => PresheafOfModules (𝒪.1 ⋙ forget₂ CommRingCat RingCat)

/-- Helper for Lemma 18.28.8: exactness is stable under composition of functors in the sheaf
module setting. -/
private theorem exactFunctorComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both
  -- properties compose formally.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  let _ : CategoryTheory.Limits.PreservesFiniteLimits G := hG.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 18.28.8: exactness transports across a natural isomorphism of functors in
the sheaf module setting. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B}
    (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the functor
  -- isomorphism and repackage the result as exactness.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : CategoryTheory.Limits.PreservesFiniteLimits F := hF.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

/-- Helper for Lemma 18.28.8: finite colimits descend along a reflective presentation. -/
private theorem preservesFiniteColimitsOfReflectiveComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    [CategoryTheory.Limits.HasFiniteColimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G)] :
    CategoryTheory.Limits.PreservesFiniteColimits G := by
  -- Proof comment: pull a finite diagram in `B` back along the reflective right adjoint,
  -- compute its colimit in `A`, and transport that colimit through `F`.
  refine ⟨?_⟩
  intro K _ _
  refine ⟨?_⟩
  intro L
  let P := L ⋙ R
  let e : L ≅ P ⋙ F :=
    Functor.isoWhiskerLeft L (asIso adj.counit).symm
  have hPF : CategoryTheory.Limits.PreservesColimit (P ⋙ F) G := by
    refine CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
      (CategoryTheory.Limits.isColimitOfPreserves F (CategoryTheory.Limits.colimit.isColimit P))
      ?_
    change CategoryTheory.Limits.IsColimit
      (CategoryTheory.Functor.mapCocone (F ⋙ G) (CategoryTheory.Limits.colimit.cocone P))
    exact CategoryTheory.Limits.isColimitOfPreserves
      (F ⋙ G) (CategoryTheory.Limits.colimit.isColimit P)
  exact CategoryTheory.Limits.preservesColimit_of_iso_diagram G e.symm

/-- Helper for Lemma 18.28.8: finite limits descend along a reflective presentation. -/
private theorem preservesFiniteLimitsOfReflectiveComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    [CategoryTheory.Limits.HasFiniteLimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G)] :
    CategoryTheory.Limits.PreservesFiniteLimits G := by
  -- Proof comment: the same reflective-localization argument applies to finite limits.
  refine ⟨?_⟩
  intro K _ _
  refine ⟨?_⟩
  intro L
  let P := L ⋙ R
  let e : L ≅ P ⋙ F :=
    Functor.isoWhiskerLeft L (asIso adj.counit).symm
  have hPF : CategoryTheory.Limits.PreservesLimit (P ⋙ F) G := by
    refine CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (CategoryTheory.Limits.isLimitOfPreserves F (CategoryTheory.Limits.limit.isLimit P))
      ?_
    change CategoryTheory.Limits.IsLimit
      (CategoryTheory.Functor.mapCone (F ⋙ G) (CategoryTheory.Limits.limit.cone P))
    exact CategoryTheory.Limits.isLimitOfPreserves
      (F ⋙ G) (CategoryTheory.Limits.limit.isLimit P)
  exact CategoryTheory.Limits.preservesLimit_of_iso_diagram G e.symm

/-- Helper for Lemma 18.28.8: exactness descends from the essential image of a reflective
presentation. -/
private theorem exactFunctorOfReflectiveComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    [CategoryTheory.Limits.HasFiniteLimits A]
    [CategoryTheory.Limits.HasFiniteColimits A]
    (F : A ⥤ B) (R : B ⥤ A) (adj : F ⊣ R) (G : B ⥤ D)
    [IsIso adj.counit]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ F)]
    [CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ F)]
    (h : exactFunctor A D (F ⋙ G)) :
    exactFunctor B D G := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and each half
  -- descends through the reflective localization.
  rw [CategoryTheory.exactFunctor_iff] at h ⊢
  constructor
  · let _ : CategoryTheory.Limits.PreservesFiniteLimits (F ⋙ G) := h.1
    exact preservesFiniteLimitsOfReflectiveComp F R adj G
  · let _ : CategoryTheory.Limits.PreservesFiniteColimits (F ⋙ G) := h.2
    exact preservesFiniteColimitsOfReflectiveComp F R adj G

/-- Helper for Lemma 18.28.8: fixed-owner module sheafification commutes with right tensoring. -/
private noncomputable def moduleSheafificationTensorRightIso
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : PModS(𝒪)) :
    CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification 𝒪 ≅
      moduleSheafification 𝒪 ⋙
        CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ) :=
  -- TODO: produce the fixed-owner tensor/sheafification comparison from a stable exported owner,
  -- either a canonical `Functor.Monoidal` instance or a dedicated comparison iso for
  -- `moduleSheafification 𝒪`.
  sorry

/-
The helper below does not use the additive-sheaf composition instance directly; omit it to keep
the theorem-local section-variable set minimal.
-/
omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Helper for Lemma 18.28.8: exactness of tensoring by a sheafified module descends from the
essential image of fixed-owner sheafification. -/
private theorem tensorRightExactOfSheafificationImage
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : PModS(𝒪))
    (hComposite :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (moduleSheafification 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ))) :
    exactFunctor
      (Mod(𝒪))
      (Mod(𝒪))
      (CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ)) := by
  let R := SheafOfModules.forget (ringSheaf J 𝒪)
  let S := moduleSheafification 𝒪
  let T := CategoryTheory.MonoidalCategory.tensorRight (S.obj ℱ)
  let adj : S ⊣ R :=
    PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf J 𝒪).obj)
  let _ : IsIso adj.counit := by
    infer_instance
  let hSExact := (CategoryTheory.exactFunctor_iff S).1 ((ExactFunctor.of S).property)
  let _ : CategoryTheory.Limits.PreservesFiniteLimits (R ⋙ S) := by
    exact CategoryTheory.Limits.preservesFiniteLimits_of_natIso (asIso adj.counit).symm
  let _ : CategoryTheory.Limits.PreservesFiniteColimits (R ⋙ S) := by
    exact CategoryTheory.Limits.preservesFiniteColimits_of_natIso (asIso adj.counit).symm
  let _ : CategoryTheory.Limits.PreservesFiniteLimits S := hSExact.1
  let _ : CategoryTheory.Limits.PreservesFiniteColimits S := hSExact.2
  -- Proof comment: the counit identifies every sheaf module with a sheafification image, so
  -- exactness of the composite through sheafification descends to exactness of `tensorRight`.
  exact exactFunctorOfReflectiveComp S R adj T hComposite

omit [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] in
/-- Helper for Lemma 18.28.8: a flat presheaf over the fixed ring sheaf stays flat after
fixed-owner sheafification. -/
private theorem sheafificationIsFlatOfFlatPresheaf
    [MonoidalCategory (Mod(𝒪))]
    (ℱ : PModS(𝒪))
    (hℱ : PresheafOfModules.IsFlat ℱ) :
    IsFlat 𝒪 ((moduleSheafification 𝒪).obj ℱ) := by
  refine ⟨?_⟩
  let hTensor :
      exactFunctor
        (PModS(𝒪))
        (PModS(𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ) :=
    PresheafOfModules.IsFlat.exact_tensor (ℱ := ℱ)
  let hSheafification :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (moduleSheafification 𝒪) :=
    (ExactFunctor.of (moduleSheafification 𝒪)).property
  let hCompositePresheaf :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (CategoryTheory.MonoidalCategory.tensorRight ℱ ⋙ moduleSheafification 𝒪) :=
    exactFunctorComp hTensor hSheafification
  let hCompositeSheaf :
      exactFunctor
        (PModS(𝒪))
        (Mod(𝒪))
        (moduleSheafification 𝒪 ⋙
          CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj ℱ)) :=
    exactFunctorOfNatIso
      (moduleSheafificationTensorRightIso (J := J) (𝒪 := 𝒪) ℱ)
      hCompositePresheaf
  -- Proof comment: once the fixed-owner tensor comparison is available, reflective descent along
  -- the sheafification counit upgrades exactness of presheaf tensoring to exactness of tensoring
  -- by the sheafified module.
  exact tensorRightExactOfSheafificationImage (J := J) (𝒪 := 𝒪) ℱ hCompositeSheaf

/-- Helper for Lemma 18.28.8: the sheaf lower shriek is the sheafification of the corresponding
presheaf lower shriek. -/
private noncomputable abbrev localizedStructureModuleExtensionByZeroSheafificationIso
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    j![𝒪, U] ≅
      (moduleSheafification 𝒪).obj
        (PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪.1 U) := by
  -- Proof comment: `SheafOfModules.pullbackIso` compares the sheaf pullback defining `j!` with
  -- sheafification of the corresponding presheaf pullback.
  simpa [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero,
    PresheafOfModules.localizedStructureModuleExtensionByZero,
    PresheafOfModules.localizedStructureModule, moduleSheafification] using
    (SheafOfModules.pullbackIso
      (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))).app
      (SheafOfModules.unit
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))

/-- Helper for Lemma 18.28.8: sheafification carries the presheaf coproduct of localized
extension-by-zero modules to the corresponding sheaf coproduct. -/
private noncomputable def localizedStructureModuleExtensionByZeroCoproductSheafificationIso
    {I : Type u} (U : I → C) :
    (moduleSheafification 𝒪).obj
      (∐ fun i : I ↦ PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪.1 (U i)) ≅
        ∐ fun i : I ↦ j![𝒪, (U i)] := by
  let F : I → PresheafOfModules (ringSheaf J 𝒪).obj :=
    fun i ↦
      show PresheafOfModules (ringSheaf J 𝒪).obj from
        PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪.1 (U i)
  let S := moduleSheafification 𝒪
  let G : I → Mod(𝒪) := fun i ↦ S.obj (F i)
  let H : I → Mod(𝒪) := fun i ↦ j![𝒪, (U i)]
  let eMap :
      S.obj (∐ F) ≅ colimit ((Discrete.functor F) ⋙ S) :=
    preservesColimitIso S (Discrete.functor F)
  let eDiagram :
      ((Discrete.functor F) ⋙ S) ≅ Discrete.functor G :=
    NatIso.ofComponents (fun i ↦ Iso.refl _) (fun {i j} f ↦ by
      cases i
      cases j
      cases Discrete.eq_of_hom f
      simp [F, G])
  let eColim :
      colimit ((Discrete.functor F) ⋙ S) ≅ ∐ G :=
    HasColimit.isoOfNatIso eDiagram
  let eSummands :
      Discrete.functor G ≅ Discrete.functor H :=
    NatIso.ofComponents
      (fun i ↦
        (localizedStructureModuleExtensionByZeroSheafificationIso
          (J := J) (𝒪 := 𝒪) (U (Discrete.as i))).symm)
      (fun {i j} f ↦ by
        cases i
        cases j
        cases Discrete.eq_of_hom f
        simp [G, H])
  let eCoproduct : (∐ G) ≅ ∐ H :=
    HasColimit.isoOfNatIso eSummands
  -- Proof comment: sheafification preserves the discrete coproduct, then the summandwise lower-
  -- shriek comparison identifies the resulting coproduct with the source-facing sheaf coproduct.
  exact eMap ≪≫ eColim ≪≫ eCoproduct

/-- Helper for Lemma 18.28.8: the sheaf lower-shriek Hom/evaluation equivalence is natural in the
target module sheaf. -/
private theorem localizedStructureModuleExtensionByZeroHomEquivNaturality
    (U : C) {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (β : j![𝒪, U] ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
  -- The owner equivalence is defined by target-functorial constructions.
  rfl

/-- Helper for Lemma 18.28.8: morphisms out of a coproduct of sheaf lower-shriek modules are
exactly families of chosen sections. -/
private noncomputable def localizedStructureModuleExtensionByZeroCoproductHomEquiv
    {I : Type u} (U : I → C) (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ((∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ) ≃
      (∀ i : I, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).obj ℱ) where
  toFun α i :=
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
      (Sigma.ι (fun i : I ↦ j![𝒪, (U i)]) i ≫ α)
  invFun s :=
    Sigma.desc
      (fun i : I ↦
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ).symm (s i))
  left_inv α := by
    -- A coproduct morphism is determined by its restrictions to the summands.
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.symm_apply_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ)
      (Sigma.ι (fun i : I ↦ j![𝒪, (U i)]) i ≫ α)
  right_inv s := by
    -- Evaluating the reconstructed morphism on each summand recovers the prescribed section.
    funext i
    change
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
        (Sigma.ι (fun k : I ↦ j![𝒪, (U k)]) i ≫
          Sigma.desc
            (fun k : I ↦
              (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U k) ℱ).symm
                (s k))) = s i
    rw [Limits.Sigma.ι_desc]
    exact Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ)
      (s i)

-- Proof sketch: repeat the presheaf argument in the sheaf category, or apply the presheaf result
-- and then sheafify. For each local section over `U`, adjunction produces a map
-- `j_{U!}\mathcal O_U ⟶ ℱ`; the induced coproduct map is epimorphic.
/-- Lemma 18.28.8 (3): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of rings, then
any sheaf of `\mathcal O`-modules is the quotient of a direct sum of lower-shriek modules
`j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
    (ℱ : SheafOfModules (ringSheaf J 𝒪)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ), Epi φ := by
  let I : Type u := Σ U : C, (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ
  let U : I → C := fun i ↦ i.1
  let φ : (∐ fun i : I ↦ j![𝒪, (U i)]) ⟶ ℱ :=
    (localizedStructureModuleExtensionByZeroCoproductHomEquiv (J := J) (𝒪 := 𝒪) U ℱ).symm
      (fun i ↦ i.2)
  refine ⟨I, U, φ, ?_⟩
  refine ⟨?_⟩
  intro 𝒢 α β hαβ
  -- Compare the two composites on the summand indexed by the tested local section.
  ext V s
  let i : I := ⟨V.unop, s⟩
  have hcomp := congrArg
    (fun ψ ↦
      (localizedStructureModuleExtensionByZeroCoproductHomEquiv (J := J) (𝒪 := 𝒪) U 𝒢) ψ)
    hαβ
  have hi := congrFun hcomp i
  have hi' :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ α) =
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ β) := by
    simpa [localizedStructureModuleExtensionByZeroCoproductHomEquiv] using hi
  have hφi :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) ℱ
          (Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) = s := by
    let hφfam := Equiv.apply_symm_apply
      (localizedStructureModuleExtensionByZeroCoproductHomEquiv (J := J) (𝒪 := 𝒪) U ℱ)
      (fun j : I ↦ j.2)
    have hφi' := congrFun hφfam i
    simpa [I, U, i, φ, localizedStructureModuleExtensionByZeroCoproductHomEquiv] using hφi'
  have hleft :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ α) =
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).map α) s := by
    rw [localizedStructureModuleExtensionByZeroHomEquivNaturality
      (J := J) (𝒪 := 𝒪) (U := U i)
      (β := Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) (α := α)]
    rw [hφi]
  have hright :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) 𝒢
          ((Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) ≫ β) =
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).map β) s := by
    rw [localizedStructureModuleExtensionByZeroHomEquivNaturality
      (J := J) (𝒪 := 𝒪) (U := U i)
      (β := Sigma.ι (fun j : I ↦ j![𝒪, (U j)]) i ≫ φ) (α := β)]
    rw [hφi]
  rw [hleft, hright] at hi'
  simpa [I, U, i] using hi'

/-- Helper for Lemma 18.28.8: the coproduct of lower-shriek sheaves is flat because each summand
is flat and direct sums preserve flatness in the sheaf category. -/
private theorem localizedStructureModuleExtensionByZeroCoproduct_isFlat
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    {I : Type u} (U : I → C) :
    IsFlat 𝒪 (∐ fun i : I ↦ j![𝒪, (U i)]) := by
  -- Route correction: stay inside the sheaf-module category and reuse the earlier flatness
  -- theorems instead of importing the currently broken upstream flatness files.
  let F : PresheafOfModules (ringSheaf J 𝒪).obj :=
    show PresheafOfModules (ringSheaf J 𝒪).obj from
      (∐ fun i : I ↦ PresheafOfModules.localizedStructureModuleExtensionByZero 𝒪.1 (U i))
  have hPresheafFlat : PresheafOfModules.IsFlat F :=
    show PresheafOfModules.IsFlat F from
      PresheafOfModules.localizedStructureModuleExtensionByZeroCoproduct_isFlat (𝒪 := 𝒪.1) U
  have hSheafifiedFlat : IsFlat 𝒪 ((moduleSheafification 𝒪).obj F) :=
    sheafificationIsFlatOfFlatPresheaf (J := J) (𝒪 := 𝒪) F hPresheafFlat
  let e :
      (moduleSheafification 𝒪).obj F ≅ ∐ fun i : I ↦ j![𝒪, (U i)] :=
    localizedStructureModuleExtensionByZeroCoproductSheafificationIso (J := J) (𝒪 := 𝒪) U
  let eTensor :
      CategoryTheory.MonoidalCategory.tensorRight ((moduleSheafification 𝒪).obj F) ≅
        CategoryTheory.MonoidalCategory.tensorRight (∐ fun i : I ↦ j![𝒪, (U i)]) :=
    (CategoryTheory.MonoidalCategory.tensoringRight (Mod(𝒪))).mapIso e
  -- Proof comment: the presheaf coproduct source is already flat in part `(2)`; fixed-owner
  -- sheafification preserves that flatness, and the coproduct comparison identifies the
  -- sheafified object with the sheaf coproduct appearing in part `(4)`.
  exact ⟨exactFunctorOfNatIso eTensor hSheafifiedFlat.exact_tensor⟩

-- Proof sketch: combine part `(3)` with Lemma `18.28.7 (2)` for flatness of each
-- `j_{U_i!}\mathcal O_{U_i}`, then use direct sums of flat sheaves to obtain a flat sheaf
-- surjecting onto `ℱ`.
/-- Lemma 18.28.8 (4): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of rings, then
any sheaf of `\mathcal O`-modules is the quotient of a flat sheaf of `\mathcal O`-modules. -/
theorem exists_epi_from_flat
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (ℱ : SheafOfModules.{u, u, u, u} (ringSheaf J 𝒪)) :
    ∃ (𝒢 : SheafOfModules.{u, u, u, u} (ringSheaf J 𝒪))
      (_h𝒢 : IsFlat 𝒪 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := by
  rcases
      exists_epi_from_coproduct_localizedStructureModuleExtensionByZero
        (J := J) (𝒪 := 𝒪) ℱ with
    ⟨I, U, φ, hφ⟩
  have hflat : IsFlat 𝒪 (∐ fun i : I ↦ j![𝒪, (U i)]) :=
    localizedStructureModuleExtensionByZeroCoproduct_isFlat (J := J) (𝒪 := 𝒪) U
  -- Proof comment: part `(3)` already provides the epi from a coproduct of lower-shriek sheaves,
  -- and the imported Chapter 18 flatness theorems make that same source flat.
  exact ⟨∐ fun i : I ↦ j![𝒪, (U i)], hflat, φ, hφ⟩

end SheafOfModules.RingedSite
