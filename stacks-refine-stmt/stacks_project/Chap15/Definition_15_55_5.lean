import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Module.CharacterModule

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ModuleCat

universe u v

variable (R : Type u)

/-!
Domain-style sampling:
- primary domain: character modules and the free-forget adjunction on `ModuleCat R`;
- sampled owner API:
  `CharacterModule.dual`,
  `ModuleCat.free`,
  `ModuleCat.adj`,
  `Adjunction.counit`;
- owner abstraction:
  `source-facing`: the arbitrary-ring character-module functor;
  `core/canonical`: `CharacterModule.dual` on the commutative side and the counit
    `(ModuleCat.adj R).counit` of the free-forget adjunction;
  `bridge/view`: the opposite-ring linearization of `CharacterModule.dual`. The textbook
    assignment `M ↦ (F(M) → M)` is only the Arrow-valued view of the counit, so the file should
    recall `(ModuleCat.adj R).counit` directly rather than keep a parallel wrapper functor.
- primitive versus derived:
  the primitive data are only the ambient module and the canonical owners above. The
  free-presentation viewpoint is derived from the free-module counit, not a second primitive owner
  abstraction.
-/

postfix:max "^∨" => CharacterModule

section CharacterModuleGeneral

variable [Ring R]

namespace CharacterModule

instance moduleOpposite
    (M : Type v) [AddCommGroup M] [Module R M] :
    Module Rᵐᵒᵖ M^∨ :=
  AddMonoidHom.instDomMulActModule

@[simp] theorem op_smul_apply
    {M : Type v} [AddCommGroup M] [Module R M]
    (r : Rᵐᵒᵖ) (χ : M^∨) (m : M) :
    (r • χ) m = χ (MulOpposite.unop r • m) :=
  DomMulAct.smul_addMonoidHom_apply r χ m

private instance doubleModule
    {M : Type v} [AddCommGroup M] [Module R M] :
    Module R ((M^∨)^∨) :=
  Module.compHom ((M^∨)^∨) (RingEquiv.opOp R).toRingHom

/-- The canonical evaluation map from a module to its double character module. -/
noncomputable def eval
    {M : Type v} [AddCommGroup M] [Module R M] : M →ₗ[R] (M^∨)^∨ :=
  { toFun := fun m ↦
      { toFun := fun χ ↦ χ m
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    map_add' := by
      intro m n
      ext χ
      exact χ.map_add m n
    map_smul' := by
      intro r m
      ext χ
      change χ (r • m) = ((MulOpposite.op r : Rᵐᵒᵖ) • χ) m
      simp [op_smul_apply] }

/-- The double-character evaluation map evaluates a character at the chosen module element. -/
@[simp] theorem eval_apply
    {M : Type v} [AddCommGroup M] [Module R M] (m : M) (χ : M^∨) :
    ((eval R) m) χ = χ m := rfl

end CharacterModule

/-- Definition 15.55.5: for an arbitrary ring `R`, the character-module construction is the
contravariant functor `M ↦ M^∨` from left `R`-modules to left `Rᵐᵒᵖ`-modules. -/
noncomputable def CharacterModule.functor : (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ where
  obj M := ModuleCat.of Rᵐᵒᵖ M.unop^∨
  map {X Y} f :=
    let f' := f.unop.hom
    ModuleCat.ofHom
      { toFun := fun χ ↦ CharacterModule.dual (f'.restrictScalars ℤ) χ
        map_add' := by
          intro χ ψ
          rfl
        map_smul' := by
          intro r χ
          ext m
          change χ (MulOpposite.unop r • f' m) = χ (f' (MulOpposite.unop r • m))
          rw [f'.map_smul] }
  map_id M := by
    ext χ m
    rfl
  map_comp f g := by
    ext χ m
    rfl

instance : (CharacterModule.functor R).PreservesZeroMorphisms where
  map_zero {X Y} := by
    ext χ
    change CharacterModule.dual ((0 : Y.unop ⟶ X.unop).hom.restrictScalars ℤ) χ = 0
    apply CharacterModule.ext
    intro m
    change
      (AddMonoidHom.comp χ (LinearMap.toAddMonoidHom (0 : Y.unop →ₗ[ℤ] X.unop))) m =
        (0 : Y.unop →+ AddCircle (1 : ℚ)) m
    simp

end CharacterModuleGeneral

section FreeModulePresentation

variable [Ring R]

/- Definition 15.55.5: the textbook assignment `M ↦ (F(M) → M)` is the counit of the
free-forget adjunction on `ModuleCat R`. The Arrow-valued functor is derived packaging of this
canonical natural transformation, so the file recalls the counit directly. -/
#check (ModuleCat.adj R).counit

end FreeModulePresentation
