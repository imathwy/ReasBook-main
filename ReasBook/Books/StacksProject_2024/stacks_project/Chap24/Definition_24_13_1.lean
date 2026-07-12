import Mathlib
import StacksProject_2024.Chap24.Definition_24_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
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
local notation "CpxO" => CochainComplex ModO ℤ

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _

/-- Definition 24.13.1 (1): a differential graded `\mathcal A`-module on the ringed site
`(\mathcal C, \mathcal O)` is a cochain complex of `\mathcal O`-modules endowed with degreewise
right multiplication maps by `\mathcal A` satisfying associativity, the unit law, and the
Leibniz rule. -/
@[stacks 0FRI]
structure DifferentialGradedModule (𝒜 : DGAO) where
  /-- The underlying cochain complex of `\mathcal O`-modules. -/
  toComplex : CpxO
  /-- The degreewise right action `\mathcal M^n \otimes \mathcal A^m \to
  \mathcal M^{n + m}`. -/
  smul : ∀ n m : ℤ, toComplex.X n ⊗ 𝒜.toComplex.X m ⟶ toComplex.X (n + m)
  /-- Compatibility of the action with the multiplication on `\mathcal A`. -/
  smul_assoc :
    ∀ n m k : ℤ,
      (α_ (toComplex.X n) (𝒜.toComplex.X m) (𝒜.toComplex.X k)).hom ≫
          (toComplex.X n ◁ 𝒜.mul m k) ≫
          smul n (m + k) =
        (smul n m ▷ 𝒜.toComplex.X k) ≫
          smul (n + m) k ≫
          eqToHom (congrArg toComplex.X (Int.add_assoc n m k))
  /-- The unit section of `\mathcal A^0` acts by the identity on each degree of `\mathcal M`. -/
  one_smul :
    ∀ n : ℤ,
      (toComplex.X n ◁ unitIsoTensorUnit.hom) ≫
          (ρ_ (toComplex.X n)).hom =
        (toComplex.X n ◁ 𝒜.one) ≫
          smul n 0 ≫
          eqToHom (congrArg toComplex.X (add_zero n))
  /-- Compatibility of the differential on `\mathcal M` with the differential on `\mathcal A`. -/
  d_smul :
    ∀ n m : ℤ,
      smul n m ≫ toComplex.d (n + m) (n + m + 1) =
        ((toComplex.d n (n + 1)) ▷ 𝒜.toComplex.X m) ≫
          smul (n + 1) m ≫
          eqToHom
            (congrArg toComplex.X
              (differentialGradedAlgebra_leftLeibniz_index n m)) +
        n.negOnePow •
          ((toComplex.X n ◁ 𝒜.toComplex.d m (m + 1)) ≫
            smul n (m + 1) ≫
            eqToHom
              (congrArg toComplex.X
                (differentialGradedAlgebra_rightLeibniz_index n m)))

namespace DifferentialGradedModule

/- Source-facing notation: the Stacks Project writes the category of differential graded
`\mathcal A`-modules as `\mathrm{Mod}(\mathcal A, d)`. This scoped notation exposes the canonical
owner `DifferentialGradedModule 𝒜`. -/
scoped[SheafOfModules.RingedSite.DifferentialGradedModule] notation:max
    "Mod(" 𝒜:arg ", " "d" ")" =>
  DifferentialGradedModule 𝒜

end DifferentialGradedModule

open scoped SheafOfModules.RingedSite.DifferentialGradedModule

/-- The underlying cochain complex of a bundled differential graded module. -/
instance instCoeOutDifferentialGradedModule (𝒜 : DGAO) :
    CoeOut (Mod(𝒜, d)) CpxO where
  coe ℳ := ℳ.toComplex

namespace DifferentialGradedModule

/-- A differential graded module can be evaluated degreewise on its underlying cochain complex. -/
instance instCoeFun {𝒜 : DGAO} :
    CoeFun (Mod(𝒜, d)) (fun _ ↦ ℤ → ModO) where
  coe ℳ := ℳ.toComplex.X

/-- The degree-`n` term of the underlying cochain complex of a differential graded module is its
degree-`n` component. -/
@[simp] theorem coe_apply
    {𝒜 : DGAO} (ℳ : Mod(𝒜, d)) (n : ℤ) :
    ℳ n = ℳ.toComplex.X n :=
  rfl

/-- The underlying cochain complex of a differential graded module evaluates degreewise to the
same `\mathcal O`-module sheaf. -/
@[simp] theorem toComplex_X
    {𝒜 : DGAO} (ℳ : Mod(𝒜, d)) (n : ℤ) :
    ℳ.toComplex.X n = ℳ n :=
  rfl

/-- Definition 24.13.1 (2): a homomorphism of differential graded `\mathcal A`-modules is a
morphism of the underlying cochain complexes that is compatible with the `\mathcal A`-action. -/
@[ext] structure Hom
    {𝒜 : DGAO}
    (ℳ N : Mod(𝒜, d)) where
  /-- The underlying morphism of cochain complexes of `\mathcal O`-modules. -/
  toCochainMap : ℳ.toComplex ⟶ N.toComplex
  /-- Compatibility with the right `\mathcal A`-module structures. -/
  comm :
    ∀ n m : ℤ,
      ℳ.smul n m ≫ toCochainMap.f (n + m) =
        ((toCochainMap.f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m

/-- The underlying morphism of cochain complexes of a differential graded module homomorphism. -/
instance instCoeOutHom {𝒜 : DGAO} (ℳ N : Mod(𝒜, d)) :
    CoeOut (Hom ℳ N) (ℳ.toComplex ⟶ N.toComplex) where
  coe f := f.toCochainMap

/-- A differential graded module homomorphism can be applied directly to its degreewise
components. -/
instance instCoeFunHom {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} :
    CoeFun (Hom ℳ N) (fun _ ↦ ∀ n : ℤ, ℳ n ⟶ N n) where
  coe f := f.toCochainMap.f

/-- Coercion of a differential graded module homomorphism recovers its degreewise component. -/
@[simp] theorem hom_coe_apply
    {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} (f : Hom ℳ N) (n : ℤ) :
    f n = f.toCochainMap.f n :=
  rfl

/-- The degree-`n` component of the underlying cochain map of a differential graded module
homomorphism is the degree-`n` component of the homomorphism itself. -/
@[simp] theorem toCochainMap_f
    {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} (f : Hom ℳ N) (n : ℤ) :
    f.toCochainMap.f n = f n :=
  rfl

/-- Two differential graded module homomorphisms are equal when their degreewise components
agree. -/
@[ext] theorem hom_ext
    {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} (f g : Hom ℳ N)
    (h : ∀ n : ℤ, f n = g n) : f = g := by
  cases f with
  | mk toCochainMapf commf =>
      cases g with
      | mk toCochainMapg commg =>
          change ∀ n : ℤ, toCochainMapf.f n = toCochainMapg.f n at h
          have hmap : toCochainMapf = toCochainMapg := by
            apply HomologicalComplex.hom_f_injective
            funext n
            exact h n
          subst hmap
          have hcomm : commf = commg := Subsingleton.elim _ _
          subst hcomm
          rfl

/-- The underlying cochain map determines a differential graded module homomorphism. -/
theorem toCochainMap_injective
    {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} :
    Function.Injective (fun f : Hom ℳ N ↦ f.toCochainMap) := by
  intro f g h
  apply hom_ext f g
  intro n
  change f.toCochainMap.f n = g.toCochainMap.f n
  exact congrArg (fun k : ℳ.toComplex ⟶ N.toComplex ↦ k.f n) h

namespace Hom

/-- The identity homomorphism of a differential graded module. -/
def id {𝒜 : DGAO} (ℳ : Mod(𝒜, d)) : Hom ℳ ℳ where
  toCochainMap := 𝟙 ℳ.toComplex
  comm n m := by
    simp only [HomologicalComplex.id_f, Category.comp_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp]

/-- The composite of differential graded module homomorphisms. -/
def comp {𝒜 : DGAO} {ℳ N P : Mod(𝒜, d)} (f : Hom ℳ N) (g : Hom N P) : Hom ℳ P where
  toCochainMap := f.toCochainMap ≫ g.toCochainMap
  comm n m := by
    calc
      ℳ.smul n m ≫ (f.toCochainMap ≫ g.toCochainMap).f (n + m)
          = (ℳ.smul n m ≫ f.toCochainMap.f (n + m)) ≫
              g.toCochainMap.f (n + m) := by
            simp only [HomologicalComplex.comp_f, Category.assoc]
      _ = (((f.toCochainMap.f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m) ≫
              g.toCochainMap.f (n + m) := by
            rw [f.comm n m]
      _ = (f.toCochainMap.f n) ▷ 𝒜.toComplex.X m ≫
            (N.smul n m ≫ g.toCochainMap.f (n + m)) := by
            simp only [Category.assoc]
      _ = (f.toCochainMap.f n) ▷ 𝒜.toComplex.X m ≫
            ((g.toCochainMap.f n) ▷ 𝒜.toComplex.X m ≫ P.smul n m) := by
            rw [g.comm n m]
      _ = ((f.toCochainMap.f n ≫ g.toCochainMap.f n) ▷ 𝒜.toComplex.X m) ≫ P.smul n m := by
            rw [← MonoidalCategory.comp_whiskerRight_assoc]
      _ = ((f.toCochainMap ≫ g.toCochainMap).f n ▷ 𝒜.toComplex.X m) ≫ P.smul n m := by
            rw [HomologicalComplex.comp_f]

/-- The underlying cochain map of the identity differential graded module homomorphism is the
identity. -/
@[simp] theorem id_toCochainMap {𝒜 : DGAO} (ℳ : Mod(𝒜, d)) :
    (id ℳ).toCochainMap = 𝟙 ℳ.toComplex :=
  rfl

/-- The degree-`n` component of the identity differential graded module homomorphism is the
identity on `\mathcal M^n`. -/
@[simp] theorem id_apply {𝒜 : DGAO} (ℳ : Mod(𝒜, d)) (n : ℤ) :
    id ℳ n = 𝟙 (ℳ n) :=
  rfl

/-- The underlying cochain map of a composite differential graded module homomorphism is the
composite of the underlying cochain maps. -/
@[simp] theorem comp_toCochainMap {𝒜 : DGAO} {ℳ N P : Mod(𝒜, d)} (f : Hom ℳ N) (g : Hom N P) :
    (comp f g).toCochainMap = f.toCochainMap ≫ g.toCochainMap :=
  rfl

/-- The degree-`n` component of a composite differential graded module homomorphism is the
composite of the degree-`n` components. -/
@[simp] theorem comp_apply
    {𝒜 : DGAO} {ℳ N P : Mod(𝒜, d)} (f : Hom ℳ N) (g : Hom N P) (n : ℤ) :
    comp f g n = f n ≫ g n :=
  rfl

end Hom

/-- Identity and composition of compatible cochain maps make differential graded
`\mathcal A`-modules into a category. -/
instance instCategory (𝒜 : DGAO) :
    Category (Mod(𝒜, d)) where
  Hom ℳ N := DifferentialGradedModule.Hom ℳ N
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro ℳ N f
    cases f
    rfl
  comp_id := by
    intro ℳ N f
    cases f
    rfl
  assoc := by
    intro ℳ N P Q f g h
    cases f
    cases g
    cases h
    rfl

/-- Definition 24.13.1 (3): the category of differential graded `\mathcal A`-modules, i.e. the
source-facing owner for the textbook notation `\mathrm{Mod}(\mathcal A, d)`. -/
@[stacks 0FRI]
abbrev moduleCategory (𝒜 : DGAO) := Mod(𝒜, d)

/-- The source-facing owner `moduleCategory 𝒜` is the bundled type `Mod(𝒜, d)` of differential
graded `\mathcal A`-modules. -/
@[simp] theorem moduleCategory_def (𝒜 : DGAO) :
    moduleCategory 𝒜 = Mod(𝒜, d) :=
  rfl

/-- Forgetting the differential graded module structure remembers only the underlying cochain
complex of `\mathcal O`-modules. -/
def forgetToComplex (𝒜 : DGAO) : Mod(𝒜, d) ⥤ CpxO where
  obj ℳ := ℳ.toComplex
  map f := f.toCochainMap
  map_id := Hom.id_toCochainMap
  map_comp := Hom.comp_toCochainMap

/-- The object part of `forgetToComplex` recovers the underlying cochain complex. -/
@[simp] theorem forgetToComplex_obj {𝒜 : DGAO} (ℳ : Mod(𝒜, d)) :
    (forgetToComplex 𝒜).obj ℳ = ℳ.toComplex :=
  rfl

/-- The morphism part of `forgetToComplex` recovers the underlying cochain map. -/
@[simp] theorem forgetToComplex_map
    {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} (f : ℳ ⟶ N) :
    (forgetToComplex 𝒜).map f = f.toCochainMap :=
  rfl

/-- The degree-`n` component of the image of a differential graded module map under
`forgetToComplex` is the degree-`n` component of the original map. -/
@[simp] theorem forgetToComplex_map_f
    {𝒜 : DGAO} {ℳ N : Mod(𝒜, d)} (f : ℳ ⟶ N) (n : ℤ) :
    ((forgetToComplex 𝒜).map f).f n = f.toCochainMap.f n :=
  rfl

/-- Forgetting to the underlying cochain complex is faithful. -/
instance forgetToComplex_faithful (𝒜 : DGAO) :
    Functor.Faithful (forgetToComplex 𝒜) where
  map_injective := by
    intro X Y f g h
    exact toCochainMap_injective h

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
