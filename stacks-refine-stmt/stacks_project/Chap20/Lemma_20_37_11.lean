import Mathlib

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The family of objects underlying a sequential inverse system in a category. -/
abbrev inverseSystemFamily (Ksys : ℕᵒᵖ ⥤ D) : ℕ → D :=
  fun n ↦ Ksys.obj (op n)

/-- The Milnor difference endomorphism of the product `∏ K_n` attached to a sequential inverse
system. -/
def derivedLimitDifferenceMap (Ksys : ℕᵒᵖ ⥤ D)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n -
      Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map ((homOfLE (Nat.le_succ n)).op)

/-- An object `K` is a derived limit of a sequential inverse system `Ksys` if it fits into the
standard Milnor distinguished triangle. -/
def IsDerivedLimit (Ksys : ℕᵒᵖ ⥤ D) (K : D) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang D

end

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) :=
  inferInstance

/-- The category `Mod(\mathcal O_X)` carries the standard derived-category structure. -/
local instance ringedSpaceModuleCatHasDerivedCategory :
    HasDerivedCategory (ringedSpaceModuleCat X) :=
  HasDerivedCategory.standard (ringedSpaceModuleCat X)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

/-- The inverse system `n ↦ H^q(K_n)` of cohomology sheaves attached to a sequential inverse
system in `D(\mathcal O_X)`. -/
abbrev ringedSpaceCohomologySheafTower
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    ℕᵒᵖ ⥤ Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  Ksys ⋙
    DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q ⋙
      SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)

/-- The inverse system `n ↦ H^0(U, H^q(K_n))` of sections of the cohomology sheaves over a fixed
open subset `U`. -/
abbrev ringedSpaceCohomologySheafSectionsTower
    (U : Opens X.carrier)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ringedSpaceCohomologySheafTower X Ksys q ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- A model for `R^1 \!\varprojlim_n H^0(U, H^q(K_n))`, given by the cokernel of the Milnor
difference map on the tower `n ↦ H^0(U, H^q(K_n))`. -/
abbrev ringedSpaceCohomologySheafSectionsR1LimitTerm
    (U : Opens X.carrier)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    AddCommGrpCat.{u} :=
  cokernel (derivedLimitDifferenceMap (ringedSpaceCohomologySheafSectionsTower X U Ksys q))

-- Proof sketch: on each basis open `U ∈ ℬ`, the vanishing hypothesis kills the higher
-- cohomology of every cohomology sheaf `H^q(K_n)`, so one identifies `H^q(U, K_n)` with the
-- sections `H^0(U, H^q(K_n))`. The Milnor short exact sequence for the tower `RΓ(U, K_n)`,
-- together with the assumed vanishing of `R^1 \!\varprojlim` for these degree-zero sections,
-- identifies `H^q(U, K)` with the inverse limit of the sections of `H^q(K_n)` over `U`. Since
-- every open admits a covering by members of `ℬ`, these basiswise identifications sheafify to
-- the claimed isomorphism of cohomology sheaves.
/-- Lemma 20.37.11: let `(X, \mathcal O_X)` be a ringed space, let `(K_n)` be an inverse system
in `D(\mathcal O_X)`, and let `K = R\!\varprojlim_n K_n` be a chosen derived limit. Assume every
open subset of `X` admits a covering by members of `ℬ`, that for every `U ∈ ℬ`, every `n`, every
`q : \mathbf Z`, and every `p > 0` one has `H^p(U, H^q(K_n)) = 0`, and that for every `U ∈ ℬ`
and `q : \mathbf Z` the inverse system `n ↦ H^0(U, H^q(K_n))` has vanishing
`R^1 \!\varprojlim`. Then for each `q : \mathbf Z`, the cohomology sheaf
`H^q(R\!\varprojlim_n K_n)` is isomorphic to `\varprojlim_n H^q(K_n)`. -/
theorem derivedLimit_cohomologySheaf_isomorphic_limit_of_basiswise_acyclicity
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X))
    (K : DerivedCategory (ringedSpaceModuleCat X))
    (hK : IsDerivedLimit Ksys K)
    (ℬ : Set (Opens X.carrier))
    (hcover :
      ∀ V : Opens X.carrier,
        ∃ ι : Type u, ∃ 𝒰 : ι → Opens X.carrier, iSup 𝒰 = V ∧ ∀ i, 𝒰 i ∈ ℬ)
    (hacyclic :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ ℬ →
        ∀ n : ℕ, ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero ((ringedSpaceCohomologySheaf X (Ksys.obj (op n)) q).H' p U))
    (hR1lim :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ ℬ →
        ∀ q : ℤ,
          IsZero (ringedSpaceCohomologySheafSectionsR1LimitTerm X U Ksys q))
    (q : ℤ) :
    IsIsomorphic
      (ringedSpaceCohomologySheaf X K q)
      (limit (ringedSpaceCohomologySheafTower X Ksys q)) := sorry

end

end AlgebraicGeometry.RingedSpace
