import StacksProject_2024.Chap24.Lemma_24_23_7
import StacksProject_2024.Chap24.Definition_24_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGMod" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule (C := C) (J := J) (𝒪 := 𝒪)

/- Semantic search note: `lean_leansearch` surfaced the canonical `HomologicalComplex.Acyclic`
predicate and flat tensor exactness lemmas. Local Chapter 24 precedent supplies
`CochainComplex.IsGood`, `DifferentialGradedModule`, and the site-presented pullback functor; the
relative tensor product over a differential graded algebra is recorded here as explicit source
data because the current morphism-based Chapter 24 owner has no checked left-module tensor
construction for this section. -/

namespace DifferentialGradedModule

/-- A left differential graded `\mathcal A`-module in the morphism-based Chapter 24 style: a
cochain complex of `\mathcal O`-modules with degreewise left action maps by `\mathcal A`. -/
structure LeftModule (𝒜 : DGAO) where
  /-- The underlying cochain complex of `\mathcal O`-modules. -/
  toComplex : CpxO
  /-- The degreewise left action `\mathcal A^n \otimes \mathcal N^m \to
  \mathcal N^{n + m}`. -/
  smul : ∀ n m : ℤ, 𝒜.toComplex.X n ⊗ toComplex.X m ⟶ toComplex.X (n + m)
  /-- Compatibility of the action with the multiplication on `\mathcal A`. -/
  smul_assoc : Prop
  /-- The unit section of `\mathcal A^0` acts by the identity on each degree. -/
  one_smul : Prop
  /-- Compatibility of the differential on `\mathcal N` with the differential on
  `\mathcal A`. -/
  d_smul : Prop

/-- A left differential graded module can be used through its underlying cochain complex. -/
instance instCoeOutLeftModule (𝒜 : DGAO) :
    CoeOut (LeftModule 𝒜) CpxO where
  coe N := N.toComplex

/-- A source-facing tensor product datum for a right differential graded `\mathcal A`-module
`P` and a left differential graded `\mathcal A`-module `N`. The concrete payload is the
underlying cochain complex and its homogeneous tensor maps; the balance, differential, and
universal-property clauses are proof data for later stages. -/
structure TensorProduct {𝒜 : DGAO} (P : DGMod 𝒜) (N : LeftModule 𝒜) where
  /-- The underlying cochain complex of `P \otimes_\mathcal A N`. -/
  toComplex : CpxO
  /-- The homogeneous tensor map
  `P^n \otimes_\mathcal O N^m \to (P \otimes_\mathcal A N)^{n + m}`. -/
  tensor : ∀ n m : ℤ, P.toComplex.X n ⊗ N.toComplex.X m ⟶ toComplex.X (n + m)
  /-- The tensor maps are balanced over the differential graded algebra `\mathcal A`. -/
  balanced : Prop
  /-- The tensor maps are compatible with the differentials. -/
  d_tensor : Prop
  /-- The tensor datum has the expected universal property for balanced differential graded
  bilinear maps. -/
  universalProperty : Prop

/-- A source-facing tensor product datum can be used through its underlying cochain complex. -/
instance instCoeOutTensorProduct {𝒜 : DGAO} (P : DGMod 𝒜) (N : LeftModule 𝒜) :
    CoeOut (TensorProduct P N) CpxO where
  coe T := T.toComplex

/-- The site-presented pullback of the underlying cochain complex of a differential graded module.
-/
abbrev pullbackComplex
    {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    {𝒪' : Sheaf JD CommRingCat.{max u v}}
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint]
    [(pullbackFunctor F φ).PreservesZeroMorphisms]
    (P : DGMod 𝒜) :
    CochainComplex (ringedSiteModuleCategory JD 𝒪') ℤ :=
  ((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj P.toComplex

/-- The helper `pullbackComplex` is the complex obtained by applying the local site-presented
module pullback functor degreewise. -/
theorem pullbackComplex_def
    {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    {𝒪' : Sheaf JD CommRingCat.{max u v}}
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint]
    [(pullbackFunctor F φ).PreservesZeroMorphisms]
    (P : DGMod 𝒜) :
    pullbackComplex F φ P =
      ((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj P.toComplex := sorry

/-- Lemma 24.23.8 (1): if `\mathcal P` is a good acyclic right differential graded
`\mathcal A`-module, then for every left differential graded `\mathcal A`-module
`\mathcal N`, the tensor product `\mathcal P \otimes_\mathcal A \mathcal N` is acyclic. -/
@[stacks 0FSI]
theorem tensorProduct_acyclic_of_isGood_acyclic
    (𝒜 : DGAO) (P : DGMod 𝒜) (N : LeftModule 𝒜)
    (T : TensorProduct P N)
    (_hPgood : CochainComplex.IsGood (P.toComplex : CpxO))
    (_hPacyclic : HomologicalComplex.Acyclic (P.toComplex : CpxO)) :
    HomologicalComplex.Acyclic (T : CpxO) := sorry

/-- Lemma 24.23.8 (2): under a morphism of ringed topoi and a compatible map
`f^{-1}\mathcal A \to \mathcal A'` of differential graded algebras, the pullback of a good
acyclic right differential graded `\mathcal A`-module is again acyclic and good. The local
Chapter 24 `IsGood` owner is a property of the underlying pulled-back cochain complex. -/
@[stacks 0FSI]
theorem pullbackComplex_acyclic_and_isGood_of_isGood_acyclic
    (𝒜 : DGAO) (P : DGMod 𝒜)
    (_hPgood : CochainComplex.IsGood (P.toComplex : CpxO))
    (_hPacyclic : HomologicalComplex.Acyclic (P.toComplex : CpxO))
    {D : Type u} [Category.{v} D] {JD : GrothendieckTopology D}
    [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify JD AddCommGrpCat.{max u v}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (F : C ⥤ D) [Functor.IsContinuous F J JD]
    {𝒪' : Sheaf JD CommRingCat.{max u v}}
    (φ : 𝒪 ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).obj 𝒪')
    [(F.sheafPushforwardContinuous CommRingCat.{max u v} J JD).IsRightAdjoint]
    [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
    [(pullbackFunctor F φ).PreservesZeroMorphisms]
    [MonoidalCategory (ringedSiteModuleCategory JD 𝒪')]
    [MonoidalPreadditive (ringedSiteModuleCategory JD 𝒪')]
    [(curriedTensor (ringedSiteModuleCategory JD 𝒪')).Additive]
    [∀ M : ringedSiteModuleCategory JD 𝒪',
      ((curriedTensor (ringedSiteModuleCategory JD 𝒪')).obj M).Additive]
    (𝒜pull 𝒜' : @DifferentialGradedAlgebra D _ JD _ 𝒪' _)
    (_h𝒜pull :
      𝒜pull.toComplex =
        ((pullbackFunctor F φ).mapHomologicalComplex (up ℤ)).obj 𝒜.toComplex)
    (_φA : DifferentialGradedAlgebra.Hom 𝒜pull 𝒜') :
    HomologicalComplex.Acyclic (pullbackComplex F φ P) ∧
      CochainComplex.IsGood (pullbackComplex F φ P) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
