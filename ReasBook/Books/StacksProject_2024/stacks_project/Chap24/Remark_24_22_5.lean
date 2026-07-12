import StacksProject_2024.Chap24.Definition_24_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/-- The source-facing pair of degree-`0` and degree-`-1` module-valued global sections appearing
in Remark 24.22.5. -/
def ConeIdentityPair
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} (ℳ : Mod(𝒜, d)) :=
  (unitModule J 𝒪 ⟶ ℳ 0) ×
    (unitModule J 𝒪 ⟶ ℳ (-1))

/-- The compatibility relation `x = \mathrm d(y)` on the section pairs of Remark 24.22.5. -/
def ConeIdentityPair.Compatible
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (p : ConeIdentityPair ℳ) : Prop :=
  p.1 = p.2 ≫ ℳ.toComplex.d (-1) 0

/-- The source-facing subtype of pairs satisfying the compatibility relation from Remark 24.22.5. -/
def CompatibleConeIdentityPair
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} (ℳ : Mod(𝒜, d)) :=
  {p : ConeIdentityPair ℳ // ConeIdentityPair.Compatible p}

/-- For an explicit pair `(x, y)`, compatibility is exactly the equation
 `x = y ≫ d^{-1,0}`. -/
@[simp] theorem ConeIdentityPair.compatible_mk
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (x : unitModule J 𝒪 ⟶ ℳ 0)
    (y : unitModule J 𝒪 ⟶ ℳ (-1)) :
    ConeIdentityPair.Compatible (x, y) ↔ x = y ≫ ℳ.toComplex.d (-1) 0 :=
  Iff.rfl

end

section

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasFiniteBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

open DifferentialGradedModule

namespace DifferentialGradedAlgebra

/-- A differential graded algebra acts on itself on the right, giving the canonical object of
`Mod(\mathcal A, d)` used in the cone-on-the-identity construction. -/
noncomputable def selfModule
    (𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)) : Mod(𝒜, d) where
  toComplex := 𝒜.toComplex
  smul := 𝒜.mul
  smul_assoc := 𝒜.mul_assoc
  one_smul := 𝒜.mul_one
  d_smul := 𝒜.d_mul

/-- The cone on the identity of the canonical right `\mathcal A`-module `\mathcal A`. This is
the source-facing object `C(\mathrm{id}_{\mathcal A})` in Remark 24.22.5. -/
noncomputable def coneIdentity
    (𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)) : Mod(𝒜, d) :=
  cone (𝟙 𝒜.selfModule)

/-- The canonical map `\mathcal O \to C(\mathrm{id}_{\mathcal A})^0` corresponding to the
generator `(1, 0)` of `\mathcal A^0 \oplus \mathcal A^1`. -/
noncomputable def coneIdentityDegreeZeroUnit
    (𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)) :
    unitModule J 𝒪 ⟶ 𝒜.coneIdentity 0 :=
  𝒜.one ≫ biprod.inl ≫
    eqToHom
      (cone_X (𝟙 𝒜.selfModule) 0).symm

/-- The canonical map `\mathcal O \to C(\mathrm{id}_{\mathcal A})^{-1}` corresponding to the
generator `(0, 1)` of `\mathcal A^{-1} \oplus \mathcal A^0`. -/
noncomputable def coneIdentityDegreeNegOneUnit
    (𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)) :
    unitModule J 𝒪 ⟶ 𝒜.coneIdentity (-1) :=
  𝒜.one ≫ biprod.inr ≫
    eqToHom
      (cone_X (𝟙 𝒜.selfModule) (-1)).symm

end DifferentialGradedAlgebra

open DifferentialGradedAlgebra

namespace DifferentialGradedModule.Hom

/-- The explicit pair-map from morphisms `C(\mathrm{id}_{\mathcal A}) \to \mathcal M` to the
degree-`0` and degree-`-1` module-valued global sections of `\mathcal M`, formalized on a ringed
site as morphisms out of `unitModule J 𝒪`. -/
noncomputable def coneIdentityPair
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (f : 𝒜.coneIdentity ⟶ ℳ) : ConeIdentityPair ℳ :=
  (𝒜.coneIdentityDegreeZeroUnit ≫ f.toCochainMap.f 0,
    𝒜.coneIdentityDegreeNegOneUnit ≫ f.toCochainMap.f (-1))

/-- The degree-`0` component of the pair associated to a cone morphism is obtained by evaluating
the morphism on the canonical degree-`0` unit section of `C(\mathrm{id}_{\mathcal A})`. -/
@[simp] theorem coneIdentityPair_degreeZero
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (f : 𝒜.coneIdentity ⟶ ℳ) :
    (coneIdentityPair f).1 =
      𝒜.coneIdentityDegreeZeroUnit ≫ f.toCochainMap.f 0 :=
  rfl

/-- The degree-`-1` component of the pair associated to a cone morphism is obtained by
evaluating the morphism on the canonical degree-`-1` unit section of
`C(\mathrm{id}_{\mathcal A})`. -/
@[simp] theorem coneIdentityPair_degreeNegOne
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (f : 𝒜.coneIdentity ⟶ ℳ) :
    (coneIdentityPair f).2 =
      𝒜.coneIdentityDegreeNegOneUnit ≫ f.toCochainMap.f (-1) :=
  rfl

/-- Remark 24.22.5 (1): the explicit pair extracted from a morphism
`C(\mathrm{id}_{\mathcal A}) \to \mathcal M` by evaluating on the canonical unit-section
generators of `C(\mathrm{id}_{\mathcal A})^0` and `C(\mathrm{id}_{\mathcal A})^{-1}` satisfies
the relation `x = \mathrm d(y)`. On the current ringed-site owner, the global sections
`Γ(\mathcal C,-)` are formalized as morphisms out of `unitModule J 𝒪`. -/
theorem coneIdentityPair_compatible
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (f : 𝒜.coneIdentity ⟶ ℳ) :
    ConeIdentityPair.Compatible (coneIdentityPair f) := sorry

/-- The canonical compatible pair attached to a morphism
`C(\mathrm{id}_{\mathcal A}) \to \mathcal M`. -/
noncomputable def compatibleConeIdentityPair
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (f : 𝒜.coneIdentity ⟶ ℳ) :
    CompatibleConeIdentityPair ℳ :=
  ⟨coneIdentityPair f, coneIdentityPair_compatible f⟩

/-- Forgetting the compatibility proof from the canonical subtype-valued map recovers the explicit
pair of degree-`0` and degree-`-1` sections. -/
@[simp] theorem compatibleConeIdentityPair_val
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (f : 𝒜.coneIdentity ⟶ ℳ) :
    (compatibleConeIdentityPair f).1 = coneIdentityPair f :=
  rfl

end DifferentialGradedModule.Hom

open DifferentialGradedModule.Hom

/-- Remark 24.22.5 (2): every compatible pair `(x, y)` of degree-`0` and degree-`-1`
module-valued global sections of `\mathcal M` comes from a unique morphism
`C(\mathrm{id}_{\mathcal A}) \to \mathcal M`. -/
theorem CompatibleConeIdentityPair.existsUnique_hom
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (p : CompatibleConeIdentityPair ℳ) :
    ∃! f : 𝒜.coneIdentity ⟶ ℳ,
      compatibleConeIdentityPair f = p := sorry

/-- Bridge/view: the unique-existence statement for compatible pairs can be called with an
explicit pair together with a proof of the source relation `x = \mathrm d(y)`. -/
theorem ConeIdentityPair.existsUnique_hom
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (p : ConeIdentityPair ℳ) (hp : ConeIdentityPair.Compatible p) :
    ∃! f : 𝒜.coneIdentity ⟶ ℳ,
      coneIdentityPair f = p := sorry

/-- A pair of degree-`0` and degree-`-1` unit sections of `\mathcal M` comes from a unique
morphism `C(\mathrm{id}_{\mathcal A}) \to \mathcal M` exactly when it satisfies the source
relation `x = \mathrm d(y)`. -/
theorem ConeIdentityPair.existsUnique_hom_iff_compatible
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)}
    (p : ConeIdentityPair ℳ) :
    (∃! f : 𝒜.coneIdentity ⟶ ℳ,
      coneIdentityPair f = p) ↔
      ConeIdentityPair.Compatible p := sorry

namespace DifferentialGradedModule.Hom

/-- Remark 24.22.5 packaged as the canonical bijection between morphisms
`C(\mathrm{id}_{\mathcal A}) ⟶ \mathcal M` and compatible degree-`0`/degree-`-1` pairs. -/
theorem coneIdentityPair_bijective
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {ℳ : Mod(𝒜, d)} :
    Function.Bijective
      (fun f : 𝒜.coneIdentity ⟶ ℳ ↦ compatibleConeIdentityPair f) := sorry

end DifferentialGradedModule.Hom

end

end SheafOfModules.RingedSite
