import Mathlib
import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGMod" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic search note: `lean_leansearch` returned category-theoretic preservation patterns such
-- as `CategoryTheory.IsGrothendieckAbelian.hasColimits` and
-- `ModuleCat.FilteredColimits.forget_preservesFilteredColimits`. The Chapter 24 differential
-- graded owner stores tensor-action morphisms rather than sectionwise bilinear maps, so the
-- source's category `\mathrm{Mod}(\mathcal A)` is formalized here by the matching morphism-based
-- graded-module owner `UnderlyingGradedModule 𝒜`.

namespace UnderlyingGradedModule

/-- A graded `\mathcal A`-module in the morphism-based Chapter 24 style: a `\mathbf Z`-graded
family of `\mathcal O`-module sheaves with degreewise action morphisms by the underlying graded
algebra of `\mathcal A`, but without a differential. -/
structure Module (𝒜 : DGAO) where
  /-- The degree-`n` term of the underlying graded module. -/
  obj : ℤ → ModO
  /-- The degreewise right action `M^n \otimes A^m \to M^{n + m}`. -/
  smul : ∀ n m : ℤ, obj n ⊗ 𝒜.toComplex.X m ⟶ obj (n + m)
  /-- Associativity of the graded action. -/
  smul_assoc :
    ∀ n m k : ℤ,
      (α_ (obj n) (𝒜.toComplex.X m) (𝒜.toComplex.X k)).hom ≫
          (obj n ◁ 𝒜.mul m k) ≫
          smul n (m + k) =
        (smul n m ▷ 𝒜.toComplex.X k) ≫
          smul (n + m) k ≫
          eqToHom (congrArg obj (Int.add_assoc n m k))
  /-- The degree-zero unit acts by the identity. -/
  one_smul :
    ∀ n : ℤ,
      (obj n ◁ unitIsoTensorUnit.hom) ≫
          (ρ_ (obj n)).hom =
        (obj n ◁ 𝒜.one) ≫
          smul n 0 ≫
          eqToHom (congrArg obj (add_zero n))

/-- The root owner for graded `\mathcal A`-modules underlying differential graded modules. -/
abbrev moduleCategory (𝒜 : DGAO) := Module 𝒜

/-- The source-facing category `moduleCategory 𝒜` is the bundled type of graded
`\mathcal A`-modules in this morphism-based formalization. -/
theorem moduleCategory_def (𝒜 : DGAO) :
    moduleCategory 𝒜 = Module 𝒜 := sorry

/-- A morphism of graded `\mathcal A`-modules is a degreewise family of maps compatible with the
graded action. -/
structure Hom {𝒜 : DGAO} (M N : Module 𝒜) where
  /-- The degreewise maps `M^n \to N^n`. -/
  hom : ∀ n : ℤ, M.obj n ⟶ N.obj n
  /-- Compatibility with the graded `\mathcal A`-action. -/
  comm :
    ∀ n m : ℤ,
      M.smul n m ≫ hom (n + m) =
        ((hom n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m

/-- A morphism of graded `\mathcal A`-modules can be evaluated degreewise. -/
theorem hom_apply {𝒜 : DGAO} {M N : Module 𝒜} (f : Hom M N) (n : ℤ) :
    f.hom n = f.hom n := sorry

/-- The canonical category structure on morphism-based graded `\mathcal A`-modules. -/
instance instCategory (𝒜 : DGAO) : Category (Module 𝒜) where
  Hom M N := Hom M N
  id M :=
    { hom := fun n ↦ 𝟙 (M.obj n)
      comm := sorry }
  comp f g :=
    { hom := fun n ↦ f.hom n ≫ g.hom n
      comm := sorry }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end UnderlyingGradedModule

namespace DifferentialGradedModule

/-- Forgetting the differential on a differential graded `\mathcal A`-module yields its
underlying graded `\mathcal A`-module. -/
noncomputable def forgetToGradedObj {𝒜 : DGAO} (M : DGMod 𝒜) :
    UnderlyingGradedModule.Module 𝒜 where
  obj := M.toComplex.X
  smul := M.smul
  smul_assoc := M.smul_assoc
  one_smul := M.one_smul

/-- The degree-`n` term of `forgetToGradedObj M` is the `n`th term of the underlying cochain
complex of `M`. -/
theorem forgetToGradedObj_obj {𝒜 : DGAO} (M : DGMod 𝒜) (n : ℤ) :
    (forgetToGradedObj M).obj n = M.toComplex.X n := sorry

/-- Forgetting the differential on a morphism of differential graded modules keeps the degreewise
graded-module maps. -/
noncomputable def forgetToGradedMap {𝒜 : DGAO} {M N : DGMod 𝒜} (f : M ⟶ N) :
    UnderlyingGradedModule.Hom (forgetToGradedObj M) (forgetToGradedObj N) where
  hom := f.toCochainMap.f
  comm := f.comm

/-- The degree-`n` component of `forgetToGradedMap f` is the `n`th component of the underlying
cochain map. -/
theorem forgetToGradedMap_hom {𝒜 : DGAO} {M N : DGMod 𝒜} (f : M ⟶ N) (n : ℤ) :
    (forgetToGradedMap f).hom n = f.toCochainMap.f n := sorry

/-- Identity morphisms are preserved by the forgetful functor to graded modules. -/
theorem forgetToGraded_map_id (𝒜 : DGAO) :
    ∀ M : DGMod 𝒜, forgetToGradedMap (𝟙 M) = 𝟙 (forgetToGradedObj M) := sorry

/-- Composition is preserved by the forgetful functor to graded modules. -/
theorem forgetToGraded_map_comp (𝒜 : DGAO) :
    ∀ {M N P : DGMod 𝒜} (f : M ⟶ N) (g : N ⟶ P),
      forgetToGradedMap (f ≫ g) =
        (UnderlyingGradedModule.instCategory 𝒜).comp (forgetToGradedMap f) (forgetToGradedMap g) :=
  sorry

/-- The forgetful functor from differential graded `\mathcal A`-modules to the underlying graded
`\mathcal A`-module category. -/
noncomputable def forgetToGraded (𝒜 : DGAO) :
    moduleCategory 𝒜 ⥤ UnderlyingGradedModule.moduleCategory 𝒜 where
  obj M := forgetToGradedObj M
  map f := forgetToGradedMap f
  map_id := forgetToGraded_map_id 𝒜
  map_comp := forgetToGraded_map_comp 𝒜

/-- The forgetful functor sends a differential graded module to its underlying graded module. -/
theorem forgetToGraded_obj_obj (𝒜 : DGAO) (M : moduleCategory 𝒜) (n : ℤ) :
    ((forgetToGraded 𝒜).obj M).obj n = M.toComplex.X n := sorry

/-- Lemma 24.13.2 (1): the category `\mathrm{Mod}(\mathcal A, d)` of differential graded
`\mathcal A`-modules is abelian. -/
instance moduleCategoryAbelian (𝒜 : DGAO) : Abelian (moduleCategory 𝒜) := sorry

/-- Lemma 24.13.2 (2): the category `\mathrm{Mod}(\mathcal A, d)` has arbitrary direct sums,
formalized as arbitrary coproducts. -/
instance moduleCategoryHasCoproducts (𝒜 : DGAO) : HasCoproducts (moduleCategory 𝒜) := sorry

/-- Lemma 24.13.2 (3): the category `\mathrm{Mod}(\mathcal A, d)` has arbitrary colimits. -/
instance moduleCategoryHasColimits (𝒜 : DGAO) : HasColimits (moduleCategory 𝒜) := sorry

/-- Lemma 24.13.2 (4): filtered colimits in `\mathrm{Mod}(\mathcal A, d)` are exact, formalized
by the Grothendieck axiom `AB5`. -/
instance moduleCategoryAB5 (𝒜 : DGAO) : AB5 (moduleCategory 𝒜) := sorry

/-- Lemma 24.13.2 (5): the category `\mathrm{Mod}(\mathcal A, d)` has arbitrary products. -/
instance moduleCategoryHasProducts (𝒜 : DGAO) : HasProducts (moduleCategory 𝒜) := sorry

/-- Lemma 24.13.2 (6): the category `\mathrm{Mod}(\mathcal A, d)` has arbitrary limits. -/
instance moduleCategoryHasLimits (𝒜 : DGAO) : HasLimits (moduleCategory 𝒜) := sorry

/-- Lemma 24.13.2 (7): the forgetful functor from differential graded `\mathcal A`-modules to
graded `\mathcal A`-modules preserves all limits. -/
instance forgetToGradedPreservesLimits (𝒜 : DGAO) :
    PreservesLimits (forgetToGraded 𝒜) := sorry

/-- Lemma 24.13.2 (8): the forgetful functor from differential graded `\mathcal A`-modules to
graded `\mathcal A`-modules preserves all colimits. -/
instance forgetToGradedPreservesColimits (𝒜 : DGAO) :
    PreservesColimits (forgetToGraded 𝒜) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
