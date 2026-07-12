import StacksProject_2024.Chap24.Definition_24_13_1

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
local notation "DGMod" => @SheafOfModules.RingedSite.DifferentialGradedModule C _ J _ 𝒪 _

/-- Definition 24.17.1 (1): a differential graded `(\mathcal A, \mathcal B)`-bimodule on a
ringed site `(\mathcal C, \mathcal O)` is a right differential graded `\mathcal B`-module
together with a degreewise left `\mathcal A`-action satisfying the usual associativity,
commutation, unit, and Leibniz compatibilities. -/
@[stacks 0FRQ]
structure DifferentialGradedBimodule (𝒜 𝒝 : DGAO) where
  /-- The underlying right differential graded `\mathcal B`-module. -/
  toRightModule : DGMod 𝒝
  /-- The degreewise left action `\mathcal A^n \otimes \mathcal M^m \to \mathcal M^{n + m}`. -/
  leftMul (n m : ℤ) :
    𝒜.toComplex.X n ⊗ toRightModule.toComplex.X m ⟶ toRightModule.toComplex.X (n + m)
  /-- Compatibility of the left action with multiplication on `\mathcal A`. -/
  left_assoc :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (𝒜.toComplex.X j) (toRightModule.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ leftMul j k) ≫
          leftMul i (j + k) =
        (𝒜.mul i j ▷ toRightModule.toComplex.X k) ≫
          leftMul (i + j) k ≫
          eqToHom (congrArg toRightModule.toComplex.X (Int.add_assoc i j k))
  /-- Commutation of the left `\mathcal A`-action with the given right `\mathcal B`-action. -/
  middle_assoc :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (toRightModule.toComplex.X j) (𝒝.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ toRightModule.smul j k) ≫
          leftMul i (j + k) =
        (leftMul i j ▷ 𝒝.toComplex.X k) ≫
          toRightModule.smul (i + j) k ≫
          eqToHom (congrArg toRightModule.toComplex.X (Int.add_assoc i j k))
  /-- The unit section of `\mathcal A^0` acts by the identity. -/
  one_left :
    ∀ n : ℤ,
      (unitIsoTensorUnit.hom ▷ toRightModule.toComplex.X n) ≫
          (λ_ (toRightModule.toComplex.X n)).hom =
        (𝒜.one ▷ toRightModule.toComplex.X n) ≫
          leftMul 0 n ≫
          eqToHom (congrArg toRightModule.toComplex.X (zero_add n))
  /-- Compatibility of the differential with the left action. -/
  d_leftMul :
    ∀ n m : ℤ,
      leftMul n m ≫ toRightModule.toComplex.d (n + m) (n + m + 1) =
        ((𝒜.toComplex.d n (n + 1)) ▷ toRightModule.toComplex.X m) ≫
          leftMul (n + 1) m ≫
          eqToHom
            (congrArg toRightModule.toComplex.X
              (differentialGradedAlgebra_leftLeibniz_index n m)) +
        n.negOnePow •
          ((𝒜.toComplex.X n ◁ toRightModule.toComplex.d m (m + 1)) ≫
            leftMul n (m + 1) ≫
            eqToHom
              (congrArg toRightModule.toComplex.X
                (differentialGradedAlgebra_rightLeibniz_index n m)))

namespace DifferentialGradedBimodule

/- Source-facing notation: the Stacks Project writes the category of differential graded
`(\mathcal A, \mathcal B)`-bimodules as `\mathrm{Mod}(\mathcal A, \mathcal B, d)`. This scoped
notation exposes the canonical owner `DifferentialGradedBimodule 𝒜 𝒝`. -/
scoped[SheafOfModules.RingedSite.DifferentialGradedBimodule] notation:max
    "Mod(" 𝒜:arg ", " 𝒝:arg ", " "d" ")" =>
  DifferentialGradedBimodule 𝒜 𝒝

end DifferentialGradedBimodule

open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

namespace DifferentialGradedBimodule

/-- The underlying differential graded `\mathcal B`-module of a bimodule. -/
instance instCoeOutRightModule (𝒜 𝒝 : DGAO) :
    CoeOut (Mod(𝒜, 𝒝, d)) (DGMod 𝒝) where
  coe M := M.toRightModule

/-- The underlying cochain complex of a differential graded bimodule. -/
abbrev toComplex {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) : CpxO :=
  M.toRightModule.toComplex

/-- A differential graded bimodule carries its underlying cochain complex. -/
instance instCoeOutComplex (𝒜 𝒝 : DGAO) :
    CoeOut (Mod(𝒜, 𝒝, d)) CpxO where
  coe M := M.toComplex

/-- A differential graded bimodule can be evaluated degreewise as a family of `\mathcal
O`-modules. -/
instance instCoeFun (𝒜 𝒝 : DGAO) :
    CoeFun (Mod(𝒜, 𝒝, d)) (fun _ ↦ ℤ → ModO) where
  coe M := M.toComplex.X

/-- The degree-`n` term of the underlying cochain complex of a differential graded bimodule is
its degree-`n` component. -/
@[simp] theorem toComplex_X {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) (n : ℤ) :
    M.toComplex.X n = M n :=
  rfl

/-- Coercion of a differential graded bimodule recovers its degree-`n` component. -/
@[simp] theorem coe_apply {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) (n : ℤ) :
    M n = M.toComplex.X n :=
  rfl

/-- Definition 24.17.1 (2): a homomorphism of differential graded
`(\mathcal A, \mathcal B)`-bimodules is a homomorphism of the underlying right differential
graded `\mathcal B`-modules that is compatible with the left `\mathcal A`-action. -/
@[ext] structure Hom {𝒜 𝒝 : DGAO} (M N : Mod(𝒜, 𝒝, d)) where
  /-- The underlying homomorphism of right differential graded `\mathcal B`-modules. -/
  toRightHom : DifferentialGradedModule.Hom M.toRightModule N.toRightModule
  /-- Compatibility with the left `\mathcal A`-action. -/
  comm_leftMul :
    ∀ n m : ℤ,
      M.leftMul n m ≫ toRightHom (n + m) =
        (𝒜.toComplex.X n ◁ toRightHom m) ≫ N.leftMul n m

namespace Hom

/-- The identity homomorphism of a differential graded bimodule. -/
def id {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) : Hom M M where
  toRightHom := DifferentialGradedModule.Hom.id M.toRightModule
  comm_leftMul n m := by
    simp only [DifferentialGradedModule.Hom.id_toCochainMap, HomologicalComplex.id_f,
      MonoidalCategory.whiskerLeft_id, Category.comp_id, Category.id_comp]

/-- The composite of differential graded bimodule homomorphisms. -/
def comp {𝒜 𝒝 : DGAO} {M N P : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) : Hom M P where
  toRightHom := DifferentialGradedModule.Hom.comp f.toRightHom g.toRightHom
  comm_leftMul n m := by
    calc
      M.leftMul n m ≫ (f.toRightHom.toCochainMap ≫ g.toRightHom.toCochainMap).f (n + m)
          = (M.leftMul n m ≫ f.toRightHom (n + m)) ≫ g.toRightHom (n + m) := by
            rw [HomologicalComplex.comp_f, Category.assoc]
      _ = ((𝒜.toComplex.X n ◁ f.toRightHom m) ≫ N.leftMul n m) ≫ g.toRightHom (n + m) := by
            rw [f.comm_leftMul]
      _ = (𝒜.toComplex.X n ◁ f.toRightHom m) ≫ (N.leftMul n m ≫ g.toRightHom (n + m)) := by
            rw [Category.assoc]
      _ = (𝒜.toComplex.X n ◁ f.toRightHom m) ≫
            ((𝒜.toComplex.X n ◁ g.toRightHom m) ≫ P.leftMul n m) := by
            rw [g.comm_leftMul]
      _ = ((𝒜.toComplex.X n ◁ f.toRightHom m) ≫ (𝒜.toComplex.X n ◁ g.toRightHom m)) ≫
          P.leftMul n m := by
            rw [Category.assoc]
      _ = (𝒜.toComplex.X n ◁ (f.toRightHom m ≫ g.toRightHom m)) ≫ P.leftMul n m := by
            rw [← MonoidalCategory.whiskerLeft_comp]
      _ = (𝒜.toComplex.X n ◁
            (f.toRightHom.toCochainMap ≫ g.toRightHom.toCochainMap).f m) ≫
          P.leftMul n m := by
            rw [HomologicalComplex.comp_f]

/-- The underlying right-module homomorphism of the identity bimodule map is the identity. -/
@[simp] theorem id_toRightHom {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) :
    (id M).toRightHom = DifferentialGradedModule.Hom.id M.toRightModule :=
  rfl

/-- The underlying right-module homomorphism of a composite is the composite of the
underlying right-module homomorphisms. -/
@[simp] theorem comp_toRightHom {𝒜 𝒝 : DGAO} {M N P : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) :
    (comp f g).toRightHom = DifferentialGradedModule.Hom.comp f.toRightHom g.toRightHom :=
  rfl

end Hom

/-- A bimodule homomorphism carries its underlying right-module homomorphism. -/
instance instCoeOutHom {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)} :
    CoeOut (Hom M N) (DifferentialGradedModule.Hom M.toRightModule N.toRightModule) where
  coe f := f.toRightHom

/-- A bimodule homomorphism can be evaluated degreewise on the underlying cochain complexes. -/
instance instCoeFunHom {𝒜 𝒝 : DGAO} (M N : Mod(𝒜, 𝒝, d)) :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M n ⟶ N n) where
  coe f := f.toRightHom

/-- Coercion of a bimodule homomorphism recovers its degree-`n` component. -/
@[simp] theorem hom_coe_apply {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (n : ℤ) :
    f n = f.toRightHom n :=
  rfl

/-- Two differential graded bimodule homomorphisms are equal when their degreewise components
agree. -/
@[ext] theorem hom_ext
    {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)} (f g : Hom M N)
    (h : ∀ n : ℤ, f n = g n) : f = g := by
  cases f with
  | mk toRightHomf comm_leftMulf =>
      cases g with
      | mk toRightHomg comm_leftMulg =>
          have hhom : toRightHomf = toRightHomg := by
            apply DifferentialGradedModule.hom_ext
            intro n
            change toRightHomf n = toRightHomg n
            exact h n
          subst hhom
          have hcomm_leftMul : comm_leftMulf = comm_leftMulg := Subsingleton.elim _ _
          subst hcomm_leftMul
          rfl

/-- The underlying right-module homomorphism determines a differential graded bimodule
homomorphism. -/
theorem toRightHom_injective
    {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)} :
    Function.Injective
      (fun f : Hom M N ↦
        (f.toRightHom :
          DifferentialGradedModule.Hom M.toRightModule N.toRightModule)) := by
  intro f g h
  apply hom_ext f g
  intro n
  exact
    congrArg
      (fun k : DifferentialGradedModule.Hom M.toRightModule N.toRightModule ↦ k n) h

/-- The degree-`n` component of the identity bimodule homomorphism is the identity. -/
@[simp] theorem id_hom {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) (n : ℤ) :
    Hom.id M n = 𝟙 (M n) :=
  rfl

/-- The degree-`n` component of a composite bimodule homomorphism is the composite of the
degree-`n` components. -/
@[simp] theorem comp_hom {𝒜 𝒝 : DGAO} {M N P : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) (n : ℤ) :
    Hom.comp f g n = f n ≫ g n :=
  rfl

/-- Identity and composition of compatible right-module maps give differential graded bimodules
their canonical category structure. -/
instance instCategory (𝒜 𝒝 : DGAO) :
    Category (Mod(𝒜, 𝒝, d)) where
  Hom M N := Hom M N
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro M N f
    cases f
    rfl
  comp_id := by
    intro M N f
    cases f
    rfl
  assoc := by
    intro M N P Q f g h
    cases f
    cases g
    cases h
    rfl

/-- Definition 24.17.1 (3): the category of differential graded `(\mathcal A, \mathcal B)`-
bimodules, i.e. the source-facing owner for the textbook notation
`\mathrm{Mod}(\mathcal A, \mathcal B, d)`. -/
@[stacks 0FRQ]
abbrev bimoduleCategory (𝒜 𝒝 : DGAO) := Mod(𝒜, 𝒝, d)

/-- The source-facing category `bimoduleCategory 𝒜 𝒝` is the bundled type of differential
graded `(\mathcal A, \mathcal B)`-bimodules. -/
@[simp] theorem bimoduleCategory_def (𝒜 𝒝 : DGAO) :
    bimoduleCategory 𝒜 𝒝 = Mod(𝒜, 𝒝, d) :=
  rfl

/-- Forgetting a differential graded `(\mathcal A, \mathcal B)`-bimodule remembers its
underlying right differential graded `\mathcal B`-module. -/
def forgetToRightModule (𝒜 𝒝 : DGAO) : Mod(𝒜, 𝒝, d) ⥤ DGMod 𝒝 where
  obj M := M.toRightModule
  map f := f.toRightHom
  map_id := Hom.id_toRightHom
  map_comp := Hom.comp_toRightHom

/-- Forgetting a differential graded bimodule to the right-module level recovers its underlying
right differential graded module. -/
@[simp] theorem forgetToRightModule_obj {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) :
    (forgetToRightModule 𝒜 𝒝).obj M = M.toRightModule :=
  rfl

/-- Forgetting a differential graded bimodule homomorphism to the right-module level recovers
its underlying right-module homomorphism. -/
@[simp] theorem forgetToRightModule_map
    {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)} (f : M ⟶ N) :
    (forgetToRightModule 𝒜 𝒝).map f = f.toRightHom :=
  rfl

/-- Forgetting to the underlying right differential graded module is faithful. -/
instance forgetToRightModule_faithful (𝒜 𝒝 : DGAO) :
    Functor.Faithful (forgetToRightModule 𝒜 𝒝) where
  map_injective := by
    intro M N f g h
    exact toRightHom_injective h

/-- Forgetting a differential graded `(\mathcal A, \mathcal B)`-bimodule all the way to its
underlying cochain complex of `\mathcal O`-modules factors through the canonical forgetful
functor from right differential graded `\mathcal B`-modules. -/
abbrev forgetToComplex (𝒜 𝒝 : DGAO) : Mod(𝒜, 𝒝, d) ⥤ CpxO :=
  forgetToRightModule 𝒜 𝒝 ⋙ DifferentialGradedModule.forgetToComplex 𝒝

/-- The bimodule-to-complex forgetful functor is definitionally the composite of the bimodule-to-
right-module forgetful functor and the canonical right-module-to-complex forgetful functor. -/
theorem forgetToComplex_def (𝒜 𝒝 : DGAO) :
    forgetToComplex 𝒜 𝒝 =
      forgetToRightModule 𝒜 𝒝 ⋙ DifferentialGradedModule.forgetToComplex 𝒝 :=
  rfl

/-- The underlying cochain complex of a differential graded bimodule agrees with the object
part of `forgetToComplex`. -/
@[simp] theorem forgetToComplex_obj {𝒜 𝒝 : DGAO} (M : Mod(𝒜, 𝒝, d)) :
    (forgetToComplex 𝒜 𝒝).obj M = M.toComplex :=
  rfl

/-- The underlying cochain map of a differential graded bimodule homomorphism agrees with the
morphism part of `forgetToComplex`. -/
@[simp] theorem forgetToComplex_map
    {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)} (f : M ⟶ N) :
    (forgetToComplex 𝒜 𝒝).map f = f.toRightHom.toCochainMap :=
  rfl

/-- The degree-`n` component of the image of a differential graded bimodule homomorphism under
`forgetToComplex` is the degree-`n` component of the original map. -/
@[simp] theorem forgetToComplex_map_f
    {𝒜 𝒝 : DGAO} {M N : Mod(𝒜, 𝒝, d)} (f : M ⟶ N) (n : ℤ) :
    ((forgetToComplex 𝒜 𝒝).map f).f n = f.toRightHom n :=
  rfl

/-- Forgetting to the underlying cochain complex is faithful. -/
instance forgetToComplex_faithful (𝒜 𝒝 : DGAO) :
    Functor.Faithful (forgetToComplex 𝒜 𝒝) where
  map_injective := by
    intro M N f g h
    exact toRightHom_injective (DifferentialGradedModule.toCochainMap_injective h)

end DifferentialGradedBimodule

end

end SheafOfModules.RingedSite
