import Mathlib
import StacksProject_2024.Chap13.Lemma_13_30_1
import StacksProject_2024.Chap18.Definition_18_32_1.UnitIsoTensorUnit
import StacksProject_2024.Chap21.«21_18_0_1»
import StacksProject_2024.Chap24.Definition_24_12_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (F : C ⥤ D) [Functor.IsContinuous F JC JD]
variable {𝒪' : Sheaf JC CommRingCat.{max u v}} {𝒪 : Sheaf JD CommRingCat.{max u v}}
variable (φ : 𝒪' ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).obj 𝒪)
variable [(F.sheafPushforwardContinuous CommRingCat.{max u v} JC JD).IsRightAdjoint]
variable [(SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).IsRightAdjoint]
variable [MonoidalCategory (ringedSiteModuleCategory JC 𝒪')]
variable [MonoidalCategory (ringedSiteModuleCategory JD 𝒪)]
variable [Functor.LaxMonoidal (SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ))]
variable [Functor.Monoidal (pullbackFunctor F φ)]

-- Semantic search note: `lean_leansearch` recalled
-- `SheafOfModules.pullbackPushforwardAdjunction`; the owner/API choice here was then checked
-- against the local site-presented pullback bridge `Chap21/21_18_0_1.lean`, the graded
-- predecessor `Chap24/Remark_24_3_2.lean`, and the Chapter 24 differential graded algebra owner
-- `Chap24/Definition_24_12_1.lean`.

local notation "DGAlgC" => @DifferentialGradedAlgebra C _ JC _ 𝒪' _
local notation "DGAlgD" => @DifferentialGradedAlgebra D _ JD _ 𝒪 _
local notation "complexAdj" =>
  CategoryTheory.Adjunction.mapHomologicalComplex
    (SheafOfModules.pullbackPushforwardAdjunction (ringedSiteUnderlyingStructureMap F φ))
    (ComplexShape.up ℤ)

/-- The site-presented module pushforward functor used in Remark 24.12.2 is additive. -/
local instance pushforwardAdditive :
    (SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).Additive := sorry

/-- The site-presented module pullback functor used in Remark 24.12.2 is additive. -/
local instance pullbackFunctorAdditive :
    (pullbackFunctor F φ).Additive := sorry

/-- Remark 24.12.2 (1): for the site-presented morphism of ringed topoi determined by `φ`, the
pushforward of a differential graded `\mathcal O`-algebra is obtained by pushing forward the
underlying cochain complex and transporting the multiplication and unit through the lax monoidal
structure on module pushforward. -/
noncomputable abbrev pushforwardDifferentialGradedAlgebra
    (𝒜 : DGAlgD) : DGAlgC where
  toComplex :=
    ((SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj 𝒜.toComplex
  mul n m :=
    Functor.LaxMonoidal.μ
        (SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ))
        (𝒜.toComplex.X n) (𝒜.toComplex.X m) ≫
      (SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).map (𝒜.mul n m)
  one :=
    (@unitIsoTensorUnit C _ JC _ 𝒪' _).hom ≫
      Functor.LaxMonoidal.ε (SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)) ≫
        (SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).map
          ((@unitIsoTensorUnit D _ JD _ 𝒪 _).inv ≫ 𝒜.one)
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  d_mul := sorry

/-- The underlying cochain complex of `pushforwardDifferentialGradedAlgebra` is the pushed-forward
cochain complex. -/
theorem pushforwardDifferentialGradedAlgebra_toComplex
    (𝒜 : DGAlgD) :
    (pushforwardDifferentialGradedAlgebra F φ 𝒜).toComplex =
      ((SheafOfModules.pushforward (ringedSiteUnderlyingStructureMap F φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj 𝒜.toComplex := sorry

/-- Remark 24.12.2 (2): for the same site-presented morphism, the pullback of a differential
graded `\mathcal O'`-algebra is obtained by pulling back the underlying cochain complex and
transporting multiplication and the unit through the monoidal structure on module pullback. -/
noncomputable abbrev pullbackDifferentialGradedAlgebra
    (ℬ : DGAlgC) : DGAlgD where
  toComplex := ((pullbackFunctor F φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℬ.toComplex
  mul n m :=
    (Functor.Monoidal.μIso (pullbackFunctor F φ) (ℬ.toComplex.X n) (ℬ.toComplex.X m)).hom ≫
      (pullbackFunctor F φ).map (ℬ.mul n m)
  one :=
    (@unitIsoTensorUnit D _ JD _ 𝒪 _).hom ≫
      (Functor.Monoidal.εIso (pullbackFunctor F φ)).hom ≫
        (pullbackFunctor F φ).map
          ((@unitIsoTensorUnit C _ JC _ 𝒪' _).inv ≫ ℬ.one)
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  d_mul := sorry

/-- The underlying cochain complex of `pullbackDifferentialGradedAlgebra` is the pulled-back
cochain complex. -/
theorem pullbackDifferentialGradedAlgebra_toComplex
    (ℬ : DGAlgC) :
    (pullbackDifferentialGradedAlgebra F φ ℬ).toComplex =
      ((pullbackFunctor F φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℬ.toComplex := sorry

/-- The adjoint transpose of a differential graded algebra morphism out of the pullback preserves
the unit. -/
private theorem toPushforwardDifferentialGradedAlgebraHom_comm_one
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜) :
    ℬ.one ≫ (((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex) g.hom).f 0 =
      (pushforwardDifferentialGradedAlgebra F φ 𝒜).one := sorry

/-- The adjoint transpose of a differential graded algebra morphism out of the pullback preserves
the multiplication. -/
private theorem toPushforwardDifferentialGradedAlgebraHom_comm_mul
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜) :
    ∀ n m : ℤ,
      ℬ.mul n m ≫ (((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex) g.hom).f (n + m) =
        ((((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex) g.hom).f n ▷ ℬ.toComplex.X m) ≫
          ((pushforwardDifferentialGradedAlgebra F φ 𝒜).toComplex.X n ◁
              (((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex) g.hom).f m) ≫
            (pushforwardDifferentialGradedAlgebra F φ 𝒜).mul n m := sorry

/-- The adjoint transpose of a differential graded algebra morphism into the pushforward preserves
the unit. -/
private theorem ofPushforwardDifferentialGradedAlgebraHom_comm_one
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom ℬ
      (pushforwardDifferentialGradedAlgebra F φ 𝒜)) :
    (pullbackDifferentialGradedAlgebra F φ ℬ).one ≫
        ((((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex).symm g.hom).f 0) =
      𝒜.one := sorry

/-- The adjoint transpose of a differential graded algebra morphism into the pushforward preserves
the multiplication. -/
private theorem ofPushforwardDifferentialGradedAlgebraHom_comm_mul
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom ℬ
      (pushforwardDifferentialGradedAlgebra F φ 𝒜)) :
    ∀ n m : ℤ,
      (pullbackDifferentialGradedAlgebra F φ ℬ).mul n m ≫
          ((((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex).symm g.hom).f (n + m)) =
        (((((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex).symm g.hom).f n) ▷
            (pullbackDifferentialGradedAlgebra F φ ℬ).toComplex.X m) ≫
          (𝒜.toComplex.X n ◁
              ((((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex).symm g.hom).f m)) ≫
            𝒜.mul n m := sorry

/-- The forward map in Remark 24.12.2 (3), obtained by transposing the underlying cochain map
across the pullback/pushforward adjunction on complexes. -/
private noncomputable def toPushforwardDifferentialGradedAlgebraHom
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜) :
    DifferentialGradedAlgebra.Hom ℬ
      (pushforwardDifferentialGradedAlgebra F φ 𝒜) where
  hom := ((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex) g.hom
  comm_one := toPushforwardDifferentialGradedAlgebraHom_comm_one F φ ℬ 𝒜 g
  comm_mul := toPushforwardDifferentialGradedAlgebraHom_comm_mul F φ ℬ 𝒜 g

/-- The inverse map in Remark 24.12.2 (3), obtained by transposing the underlying cochain map
back across the pullback/pushforward adjunction on complexes. -/
private noncomputable def ofPushforwardDifferentialGradedAlgebraHom
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom ℬ
      (pushforwardDifferentialGradedAlgebra F φ 𝒜)) :
    DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜 where
  hom := ((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex).symm g.hom
  comm_one := ofPushforwardDifferentialGradedAlgebraHom_comm_one F φ ℬ 𝒜 g
  comm_mul := ofPushforwardDifferentialGradedAlgebraHom_comm_mul F φ ℬ 𝒜 g

/-- The two adjoint-transpose constructions on differential graded algebra homomorphisms are
inverse on maps out of the pullback. -/
private theorem toPushforwardDifferentialGradedAlgebraHom_left_inv
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜) :
    ofPushforwardDifferentialGradedAlgebraHom F φ ℬ 𝒜
      (toPushforwardDifferentialGradedAlgebraHom F φ ℬ 𝒜 g) = g := sorry

/-- The two adjoint-transpose constructions on differential graded algebra homomorphisms are
inverse on maps into the pushforward. -/
private theorem toPushforwardDifferentialGradedAlgebraHom_right_inv
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom ℬ
      (pushforwardDifferentialGradedAlgebra F φ 𝒜)) :
    toPushforwardDifferentialGradedAlgebraHom F φ ℬ 𝒜
      (ofPushforwardDifferentialGradedAlgebraHom F φ ℬ 𝒜 g) = g := sorry

/-- Remark 24.12.2 (3): homomorphisms of differential graded algebras from the pullback of `ℬ`
to `𝒜` are in canonical bijection with homomorphisms from `ℬ` to the pushforward of `𝒜`. This is
the differential graded algebra form of the usual pullback/pushforward adjunction on module
sheaves. -/
noncomputable def pullbackPushforwardDifferentialGradedAlgebraHomEquiv
    (ℬ : DGAlgC) (𝒜 : DGAlgD) :
    DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜 ≃
      DifferentialGradedAlgebra.Hom ℬ
        (pushforwardDifferentialGradedAlgebra F φ 𝒜) where
  toFun := toPushforwardDifferentialGradedAlgebraHom F φ ℬ 𝒜
  invFun := ofPushforwardDifferentialGradedAlgebraHom F φ ℬ 𝒜
  left_inv g := toPushforwardDifferentialGradedAlgebraHom_left_inv F φ ℬ 𝒜 g
  right_inv g := toPushforwardDifferentialGradedAlgebraHom_right_inv F φ ℬ 𝒜 g

/-- Applying `pullbackPushforwardDifferentialGradedAlgebraHomEquiv` sends the underlying cochain
map to its adjoint transpose on complexes. -/
theorem pullbackPushforwardDifferentialGradedAlgebraHomEquiv_apply_hom
    (ℬ : DGAlgC) (𝒜 : DGAlgD)
    (g : DifferentialGradedAlgebra.Hom
      (pullbackDifferentialGradedAlgebra F φ ℬ) 𝒜) :
    (pullbackPushforwardDifferentialGradedAlgebraHomEquiv F φ ℬ 𝒜 g).hom =
      ((complexAdj).homEquiv ℬ.toComplex 𝒜.toComplex) g.hom := sorry

end

end SheafOfModules.RingedSite
