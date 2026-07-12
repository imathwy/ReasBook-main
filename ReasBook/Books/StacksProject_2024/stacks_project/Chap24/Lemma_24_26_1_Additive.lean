import StacksProject_2024.Chap24.Definition_24_13_1

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
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

namespace DifferentialGradedModule

section Additive

variable {𝒜 : DGAO}
local notation "DHomA" => @DifferentialGradedModule.Hom C _ J _ 𝒪 _ 𝒜

private theorem add_comm {M N : DGModA 𝒜}
    (f g : DHomA M N) (n m : ℤ) :
    M.smul n m ≫ (f.toCochainMap + g.toCochainMap).f (n + m) =
      (((f.toCochainMap + g.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_add, Preadditive.add_comp, f.comm n m, g.comm n m]

private theorem neg_comm {M N : DGModA 𝒜}
    (f : DHomA M N) (n m : ℤ) :
    M.smul n m ≫ (-f.toCochainMap).f (n + m) =
      (((-f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_neg, Preadditive.neg_comp] using congrArg (-·) (f.comm n m)

private theorem sub_comm {M N : DGModA 𝒜}
    (f g : DHomA M N) (n m : ℤ) :
    M.smul n m ≫ (f.toCochainMap - g.toCochainMap).f (n + m) =
      (((f.toCochainMap - g.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [sub_eq_add_neg] using add_comm f (-g) n m

private theorem nsmul_comm {M N : DGModA 𝒜}
    (k : ℕ) (f : DHomA M N) (n m : ℤ) :
    M.smul n m ≫ (k • f.toCochainMap).f (n + m) =
      (((k • f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_nsmul, Preadditive.nsmul_comp, f.comm n m]

private theorem zsmul_comm {M N : DGModA 𝒜}
    (k : ℤ) (f : DHomA M N) (n m : ℤ) :
    M.smul n m ≫ (k • f.toCochainMap).f (n + m) =
      (((k • f.toCochainMap).f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m := by
  simpa [Preadditive.comp_zsmul, Preadditive.zsmul_comp, f.comm n m]

instance instAddHom (M N : DGModA 𝒜) : Add (DHomA M N) where
  add f g :=
    ({ toCochainMap := f.toCochainMap + g.toCochainMap
       comm := add_comm f g } : DHomA M N)

instance instNegHom (M N : DGModA 𝒜) : Neg (DHomA M N) where
  neg f :=
    ({ toCochainMap := -f.toCochainMap
       comm := neg_comm f } : DHomA M N)

instance instSubHom (M N : DGModA 𝒜) : Sub (DHomA M N) where
  sub f g :=
    ({ toCochainMap := f.toCochainMap - g.toCochainMap
       comm := sub_comm f g } : DHomA M N)

instance instSMulNatHom (M N : DGModA 𝒜) : SMul ℕ (DHomA M N) where
  smul k f :=
    ({ toCochainMap := k • f.toCochainMap
       comm := nsmul_comm k f } : DHomA M N)

instance instSMulIntHom (M N : DGModA 𝒜) : SMul ℤ (DHomA M N) where
  smul k f :=
    ({ toCochainMap := k • f.toCochainMap
       comm := zsmul_comm k f } : DHomA M N)

@[simp] theorem add_toCochainMap
    {M N : DGModA 𝒜} (f g : DHomA M N) :
    (f + g).toCochainMap =
      (f.toCochainMap + g.toCochainMap : M.toComplex ⟶ N.toComplex) :=
  rfl

instance instAddCommGroupHom (M N : DGModA 𝒜) :
    AddCommGroup (DHomA M N) :=
  Function.Injective.addCommGroup
    (fun f : DHomA M N ↦
      (f.toCochainMap : M.toComplex ⟶ N.toComplex))
    toCochainMap_injective
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

instance instPreadditive :
    Preadditive (@DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _ 𝒜) where
  homGroup M N := by
    change AddCommGroup (DHomA M N)
    infer_instance
  add_comp M N P f g h := by
    apply toCochainMap_injective
    change (f.toCochainMap + g.toCochainMap) ≫ h.toCochainMap =
      f.toCochainMap ≫ h.toCochainMap + g.toCochainMap ≫ h.toCochainMap
    exact Preadditive.add_comp M.toComplex N.toComplex P.toComplex _ _ _
  comp_add M N P f g h := by
    apply toCochainMap_injective
    change f.toCochainMap ≫ (g.toCochainMap + h.toCochainMap) =
      f.toCochainMap ≫ g.toCochainMap + f.toCochainMap ≫ h.toCochainMap
    exact Preadditive.comp_add M.toComplex N.toComplex P.toComplex _ _ _

end Additive

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
