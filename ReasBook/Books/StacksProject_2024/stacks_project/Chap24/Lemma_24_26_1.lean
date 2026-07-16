import StacksProject_2024.stacks_project.Chap24.Lemma_24_26_1_Additive

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _
local notation "ModX" => ringedSiteModuleCategory J 𝒪
variable [Abelian ModX]
variable [CategoryWithHomology ModX]

local notation "H0ModX" =>
  HomologicalComplex.homologyFunctor ModX (up ℤ) 0
local notation "H0KModX" =>
  HomotopyCategory.homologyFunctor ModX (up ℤ) 0

private theorem dgHom_add_comm {𝒜 : DGAO} {M N : DGModA 𝒜}
    (f g : DifferentialGradedModule.Hom M N) (n m : ℤ) :
    M.smul n m ≫ (f.toCochainMap + g.toCochainMap).f (n + m) =
      (((f.toCochainMap + g.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_add, Preadditive.add_comp, f.comm n m, g.comm n m]

private theorem dgHom_neg_comm {𝒜 : DGAO} {M N : DGModA 𝒜}
    (f : DifferentialGradedModule.Hom M N) (n m : ℤ) :
    M.smul n m ≫ (-f.toCochainMap).f (n + m) =
      (((-f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_neg, Preadditive.neg_comp] using congrArg (-·) (f.comm n m)

private theorem dgHom_sub_comm {𝒜 : DGAO} {M N : DGModA 𝒜}
    (f g : DifferentialGradedModule.Hom M N) (n m : ℤ) :
    M.smul n m ≫ (f.toCochainMap - g.toCochainMap).f (n + m) =
      (((f.toCochainMap - g.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [sub_eq_add_neg] using dgHom_add_comm f (-g) n m

private theorem dgHom_nsmul_comm {𝒜 : DGAO} {M N : DGModA 𝒜}
    (k : ℕ) (f : DifferentialGradedModule.Hom M N) (n m : ℤ) :
    M.smul n m ≫ (k • f.toCochainMap).f (n + m) =
      (((k • f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_nsmul, Preadditive.nsmul_comp, f.comm n m]

private theorem dgHom_zsmul_comm {𝒜 : DGAO} {M N : DGModA 𝒜}
    (k : ℤ) (f : DifferentialGradedModule.Hom M N) (n m : ℤ) :
    M.smul n m ≫ (k • f.toCochainMap).f (n + m) =
      (((k • f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_zsmul, Preadditive.zsmul_comp, f.comm n m]

private instance dgHom_add {𝒜 : DGAO} (M N : DGModA 𝒜) :
    Add (DifferentialGradedModule.Hom M N) where
  add f g :=
    { toCochainMap := f.toCochainMap + g.toCochainMap
      comm := dgHom_add_comm f g }

private instance dgHom_neg {𝒜 : DGAO} (M N : DGModA 𝒜) :
    Neg (DifferentialGradedModule.Hom M N) where
  neg f :=
    { toCochainMap := -f.toCochainMap
      comm := dgHom_neg_comm f }

private instance dgHom_sub {𝒜 : DGAO} (M N : DGModA 𝒜) :
    Sub (DifferentialGradedModule.Hom M N) where
  sub f g :=
    { toCochainMap := f.toCochainMap - g.toCochainMap
      comm := dgHom_sub_comm f g }

private instance dgHom_smulNat {𝒜 : DGAO} (M N : DGModA 𝒜) :
    SMul ℕ (DifferentialGradedModule.Hom M N) where
  smul k f :=
    { toCochainMap := k • f.toCochainMap
      comm := dgHom_nsmul_comm k f }

private instance dgHom_smulInt {𝒜 : DGAO} (M N : DGModA 𝒜) :
    SMul ℤ (DifferentialGradedModule.Hom M N) where
  smul k f :=
    { toCochainMap := k • f.toCochainMap
      comm := dgHom_zsmul_comm k f }

private theorem dgHom_add_toCochainMap {𝒜 : DGAO} {M N : DGModA 𝒜}
    (f g : DifferentialGradedModule.Hom M N) :
    (f + g).toCochainMap =
      (f.toCochainMap + g.toCochainMap : M.toComplex ⟶ N.toComplex) :=
  rfl

private instance dgHom_addCommGroup {𝒜 : DGAO} (M N : DGModA 𝒜) :
    AddCommGroup (DifferentialGradedModule.Hom M N) :=
  Function.Injective.addCommGroup
    (fun f : DifferentialGradedModule.Hom M N ↦
      (f.toCochainMap : M.toComplex ⟶ N.toComplex))
    DifferentialGradedModule.toCochainMap_injective
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

private instance dgModA_preadditive (𝒜 : DGAO) : Preadditive (DGModA 𝒜) where
  homGroup M N := dgHom_addCommGroup M N
  add_comp M N P f g h := by
    apply DifferentialGradedModule.toCochainMap_injective
    change (f.toCochainMap + g.toCochainMap) ≫ h.toCochainMap =
      f.toCochainMap ≫ h.toCochainMap + g.toCochainMap ≫ h.toCochainMap
    exact Preadditive.add_comp M.toComplex N.toComplex P.toComplex _ _ _
  comp_add M N P f g h := by
    apply DifferentialGradedModule.toCochainMap_injective
    change f.toCochainMap ≫ (g.toCochainMap + h.toCochainMap) =
      f.toCochainMap ≫ g.toCochainMap + f.toCochainMap ≫ h.toCochainMap
    exact Preadditive.comp_add M.toComplex N.toComplex P.toComplex _ _ _

private instance dgForgetToComplex_additive (𝒜 : DGAO) :
    (DifferentialGradedModule.forgetToComplex 𝒜).Additive where
  map_add := by
    intro M N f g
    simpa using dgHom_add_toCochainMap f g

private abbrev hZeroComplexFunctor (𝒜 : DGAO) : DGModA 𝒜 ⥤ ModX :=
  DifferentialGradedModule.forgetToComplex 𝒜 ⋙ H0ModX

-- Semantic search note: the chapter-local owner `K(\mathrm{Mod}(\mathcal A, d))` is
-- `HomotopyCategory (DGModA 𝒜) (up ℤ)`, and the source-facing functor below is the canonical
-- homotopy-category lift of the Section 24.13 degree-zero homology functor on differential
-- graded modules.

namespace DifferentialGradedAlgebra

variable (𝒜 : DGAO)
variable [CategoryWithHomology (DGModA 𝒜)]

/-- The degree-zero homology functor on cochain complexes of differential graded
`\mathcal A`-modules, viewed on the homotopy category. -/
abbrev hZeroHomotopyFunctor :
    HomotopyCategory (DGModA 𝒜) (up ℤ) ⥤ ModX :=
  (hZeroComplexFunctor 𝒜).mapHomotopyCategory (up ℤ) ⋙ H0KModX

/-- Unfolding `hZeroHomotopyFunctor` gives the canonical composite of the homotopy-category lift
of the degree-zero homology functor on differential graded `\mathcal A`-modules with the
degree-zero homology functor on the homotopy category of cochain complexes of
`\mathcal O`-modules. -/
theorem hZeroHomotopyFunctor_def :
    hZeroHomotopyFunctor 𝒜 =
      (hZeroComplexFunctor 𝒜).mapHomotopyCategory (up ℤ) ⋙ H0KModX :=
  rfl

/-- Lemma 24.26.1: the degree-zero homology functor
`H^0 : K(\mathrm{Mod}(\mathcal A, d)) \to \mathrm{Mod}(\mathcal O)` is homological. -/
@[stacks 0FT2]
instance hZeroHomotopyFunctor_isHomological :
    (hZeroHomotopyFunctor 𝒜).IsHomological := by
  infer_instance

end DifferentialGradedAlgebra

end

end SheafOfModules.RingedSite
