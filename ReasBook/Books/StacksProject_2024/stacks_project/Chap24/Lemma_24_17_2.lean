import Mathlib
import StacksProject_2024.Chap24.Definition_24_17_1

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

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _

open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

/-- Differential graded `(\mathcal A, \mathcal B)`-bimodule structures on the fixed right
`\mathcal B`-module `\mathcal N`. This is the source-facing fiber of the forgetful map from
bimodules to right modules that Lemma 24.17.2 compares with the endomorphism-picture action data.
-/
abbrev DifferentialGradedBimodule.WithFixedRightModule
    (𝒜 𝒝 : DGAO) (N : Mod(𝒝, d)) :=
  {M : Mod(𝒜, 𝒝, d) // M.toRightModule = N}

namespace DifferentialGradedBimodule.WithFixedRightModule

/-- The fixed-right-module fiber carries its underlying differential graded
`(\mathcal A, \mathcal B)`-bimodule. -/
instance instCoeOutBimodule {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} :
    CoeOut (DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) (Mod(𝒜, 𝒝, d)) where
  coe Mfix := Mfix.1

/-- The underlying bimodule in the fixed-right-module fiber has right module `\mathcal N`. -/
@[simp] theorem coe_toRightModule
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)}
    (Mfix : DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) :
    (Mfix : Mod(𝒜, 𝒝, d)).toRightModule = N :=
  Mfix.2

/-- The left action of a fixed-right-module bimodule structure, viewed directly on the fixed
right module `\mathcal N`. -/
abbrev leftMul
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)}
    (Mfix : DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) (n m : ℤ) :
    𝒜.toComplex.X n ⊗ N.toComplex.X m ⟶ N.toComplex.X (n + m) := by
  rcases Mfix with ⟨M, hM⟩
  cases hM
  exact M.leftMul n m

end DifferentialGradedBimodule.WithFixedRightModule

/-- A homomorphism of differential graded `\mathcal O`-algebras from `\mathcal A` to the
right-`\mathcal B`-linear endomorphism differential graded algebra
`\mathcal{H}\!\mathit{om}^{dg}_{\mathcal B}(\mathcal N, \mathcal N)`, recorded by the induced
degreewise action maps on `\mathcal N`. -/
@[ext]
structure RightLinearEndomorphismDGAHom (𝒜 𝒝 : DGAO) (N : Mod(𝒝, d)) where
  /-- The degreewise action map `\mathcal A^n \otimes \mathcal N^m \to \mathcal N^{n + m}`. -/
  map (n m : ℤ) :
    𝒜.toComplex.X n ⊗ N.toComplex.X m ⟶ N.toComplex.X (n + m)
  /-- Multiplication in `\mathcal A` is sent to composition in the endomorphism DGA. -/
  map_mul :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (𝒜.toComplex.X j) (N.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ map j k) ≫
          map i (j + k) =
        (𝒜.mul i j ▷ N.toComplex.X k) ≫
          map (i + j) k ≫
          eqToHom (congrArg N.toComplex.X (Int.add_assoc i j k))
  /-- The resulting endomorphisms are right `\mathcal B`-linear. -/
  comm_rightMul :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (N.toComplex.X j) (𝒝.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ N.smul j k) ≫
          map i (j + k) =
        (map i j ▷ 𝒝.toComplex.X k) ≫
          N.smul (i + j) k ≫
          eqToHom (congrArg N.toComplex.X (Int.add_assoc i j k))
  /-- The unit of `\mathcal A^0` is sent to the identity endomorphism. -/
  map_one :
    ∀ n : ℤ,
      (unitIsoTensorUnit.hom ▷ N.toComplex.X n) ≫
          (λ_ (N.toComplex.X n)).hom =
        (𝒜.one ▷ N.toComplex.X n) ≫
          map 0 n ≫
          eqToHom (congrArg N.toComplex.X (zero_add n))
  /-- The differential on `\mathcal A` is sent to the differential on the internal Hom complex. -/
  comm_d :
    ∀ n m : ℤ,
      map n m ≫ N.toComplex.d (n + m) (n + m + 1) =
        ((𝒜.toComplex.d n (n + 1)) ▷ N.toComplex.X m) ≫
          map (n + 1) m ≫
          eqToHom
            (congrArg N.toComplex.X
              (differentialGradedAlgebra_leftLeibniz_index n m)) +
        n.negOnePow •
          ((𝒜.toComplex.X n ◁ N.toComplex.d m (m + 1)) ≫
            map n (m + 1) ≫
            eqToHom
              (congrArg N.toComplex.X
                (differentialGradedAlgebra_rightLeibniz_index n m)))

namespace RightLinearEndomorphismDGAHom

/-- A right-`\mathcal B`-linear endomorphism-DGA map can be applied directly to its degreewise
action morphisms. -/
instance instCoeFun {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} :
    CoeFun (RightLinearEndomorphismDGAHom 𝒜 𝒝 N) (fun _ ↦ ∀ n m : ℤ,
      𝒜.toComplex.X n ⊗ N.toComplex.X m ⟶ N.toComplex.X (n + m)) where
  coe τ := τ.map

/-- Coercion of a right-`\mathcal B`-linear endomorphism-DGA map recovers its degreewise action
map. -/
@[simp] theorem coe_apply
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N)
    (n m : ℤ) :
    τ n m = τ.map n m :=
  rfl

/-- A right-`\mathcal B`-linear endomorphism-DGA map packages canonically into a differential
graded `(\mathcal A, \mathcal B)`-bimodule whose underlying right module is `\mathcal N`. -/
def toDifferentialGradedBimodule
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N) :
    Mod(𝒜, 𝒝, d) where
  toRightModule := N
  leftMul := τ.map
  left_assoc := τ.map_mul
  middle_assoc := τ.comm_rightMul
  one_left := τ.map_one
  d_leftMul := τ.comm_d

/-- Packaging a right-`\mathcal B`-linear endomorphism-DGA map into a bimodule preserves the
given right module. -/
@[simp] theorem toDifferentialGradedBimodule_toRightModule
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N) :
    τ.toDifferentialGradedBimodule.toRightModule = N :=
  rfl

/-- Packaging a right-`\mathcal B`-linear endomorphism-DGA map into a bimodule preserves the
given left action map. -/
@[simp] theorem toDifferentialGradedBimodule_leftMul
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N)
    (n m : ℤ) :
    τ.toDifferentialGradedBimodule.leftMul n m = τ.map n m :=
  rfl

end RightLinearEndomorphismDGAHom

namespace DifferentialGradedBimodule.WithFixedRightModule

/-- A differential graded `(\mathcal A, \mathcal B)`-bimodule structure on the fixed right
`\mathcal B`-module `\mathcal N` determines the corresponding right-`\mathcal B`-linear
endomorphism-DGA map by its left action. -/
def toRightLinearEndomorphismDGAHom
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)}
    (Mfix : DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) :
    RightLinearEndomorphismDGAHom 𝒜 𝒝 N := by
  rcases Mfix with ⟨M, hM⟩
  cases hM
  exact
    { map := M.leftMul
      map_mul := M.left_assoc
      comm_rightMul := M.middle_assoc
      map_one := M.one_left
      comm_d := M.d_leftMul }

/-- The source-facing fixed-right-module owner packages the endomorphism-picture action data back
into a differential graded `(\mathcal A, \mathcal B)`-bimodule structure on `\mathcal N`. -/
def ofRightLinearEndomorphismDGAHom
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N) :
    DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N :=
  ⟨τ.toDifferentialGradedBimodule, rfl⟩

/-- Recovering the endomorphism-picture action from a fixed-right-module bimodule structure is
definitionally given by its left action maps. -/
@[simp] theorem toRightLinearEndomorphismDGAHom_apply
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)}
    (Mfix : DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) (n m : ℤ) :
    Mfix.toRightLinearEndomorphismDGAHom n m = Mfix.leftMul n m := by
  cases Mfix with
  | mk M h =>
      cases h
      rfl

/-- Packaging right-`\mathcal B`-linear endomorphism action data into the fixed-right-module
owner preserves the underlying bimodule. -/
@[simp] theorem ofRightLinearEndomorphismDGAHom_coe
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N) :
    ((ofRightLinearEndomorphismDGAHom τ :
        DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) : Mod(𝒜, 𝒝, d)) =
      τ.toDifferentialGradedBimodule :=
  rfl

/-- Packaging right-`\mathcal B`-linear endomorphism action data into the fixed-right-module
owner preserves the resulting left action. -/
@[simp] theorem ofRightLinearEndomorphismDGAHom_leftMul
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N)
    (n m : ℤ) :
    (ofRightLinearEndomorphismDGAHom τ).leftMul n m = τ.map n m :=
  rfl

/-- Lemma 24.17.2: for a ringed site `(\mathcal C, \mathcal O)`, sheaves of differential graded
`\mathcal O`-algebras `\mathcal A` and `\mathcal B`, and a right differential graded
`\mathcal B`-module `\mathcal N`, giving a differential graded `(\mathcal A, \mathcal B)`-
bimodule structure on `\mathcal N` compatible with the fixed right `\mathcal B`-module structure
is equivalent to giving the corresponding right-`\mathcal B`-linear endomorphism-DGA map out of
`\mathcal A`, written in degreewise action-map form. This is the source-facing bridge from the
chapter bimodule owner with fixed right module to the endomorphism-picture formulation. -/
@[stacks 0FRR]
def equivRightLinearEndomorphismDGAHom
    (𝒜 𝒝 : DGAO) (N : Mod(𝒝, d)) :
    DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N ≃
      RightLinearEndomorphismDGAHom 𝒜 𝒝 N :=
  { toFun := toRightLinearEndomorphismDGAHom
    invFun := ofRightLinearEndomorphismDGAHom
    left_inv := by
      intro Mfix
      apply Subtype.ext
      cases Mfix with
      | mk M h =>
          cases h
          cases M
          rfl
    right_inv := by
      intro τ
      cases τ
      rfl }

/-- Applying the bridge of Lemma 24.17.2 is definitionally the recovery of the right-`\mathcal
B`-linear endomorphism-DGA map from the bimodule left action. -/
@[simp] theorem equivRightLinearEndomorphismDGAHom_apply
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)}
    (Mfix : DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N) :
    equivRightLinearEndomorphismDGAHom 𝒜 𝒝 N Mfix =
      Mfix.toRightLinearEndomorphismDGAHom :=
  rfl

/-- Applying the inverse bridge of Lemma 24.17.2 is definitionally the packaging of the
right-`\mathcal B`-linear endomorphism-DGA map into the chapter bimodule owner. -/
@[simp] theorem equivRightLinearEndomorphismDGAHom_symm_apply
    {𝒜 𝒝 : DGAO} {N : Mod(𝒝, d)} (τ : RightLinearEndomorphismDGAHom 𝒜 𝒝 N) :
    (equivRightLinearEndomorphismDGAHom 𝒜 𝒝 N).symm τ =
      ofRightLinearEndomorphismDGAHom τ :=
  rfl

/-- The source-facing map from fixed-right-module bimodule structures to right-`\mathcal
B`-linear endomorphism-DGA maps is bijective. -/
theorem toRightLinearEndomorphismDGAHom_bijective
    (𝒜 𝒝 : DGAO) (N : Mod(𝒝, d)) :
    Function.Bijective
      (fun Mfix : DifferentialGradedBimodule.WithFixedRightModule 𝒜 𝒝 N ↦
        Mfix.toRightLinearEndomorphismDGAHom) := by
  simpa using (equivRightLinearEndomorphismDGAHom 𝒜 𝒝 N).bijective

end DifferentialGradedBimodule.WithFixedRightModule

end

end SheafOfModules.RingedSite
