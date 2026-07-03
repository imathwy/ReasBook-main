import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_37_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)
variable [IsGrothendieckAbelian (RingedSpace.Modules X)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance sheafModulesAbelian : Abelian (RingedSpace.Modules X) := inferInstance

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
local instance sheafModulesHasDerivedCategory : HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

-- Proof sketch: apply Lemma `19.13.6` to the additive sections functor `\Gamma(U,-)` on
-- `\mathcal O_X`-modules, using the canonical owner
-- `derivedSectionsAtOpenToAbelian X U`.
/-- Lemma 20.37.1 (1): for a ringed space `X` and an open subset `U ⊆ X`, the derived sections
functor `R\Gamma(U,-)` on `D(\mathcal O_X)` sends a sequential derived inverse limit to the
derived inverse limit of the stagewise derived sections. -/
theorem derivedSectionsOverOpen_preservesDerivedLimit
    {Ksys : ℕᵒᵖ ⥤ ringedSpaceModuleDerived X}
    {K : ringedSpaceModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ derivedSectionsAtOpenToAbelian X U)
      ((derivedSectionsAtOpenToAbelian X U).obj K) := sorry

-- Proof sketch: first apply part `(1)` to identify `R\Gamma(U, K)` as a derived limit of the
-- tower `n ↦ R\Gamma(U, K_n)`, then apply the Milnor short exact sequence
-- `derivedLimit_cohomology_shortExact` in `D(\operatorname{Ab})`.
/-- Lemma 20.37.1 (2): for a ringed space `X`, an open subset `U ⊆ X`, a sequential inverse
system `(K_n)` in `D(\mathcal O_X)`, a chosen derived limit `K = R\!\varprojlim K_n`, and
`m : ℤ`, the groups `H^m(U, K)` fit into the short exact sequence
`0 \to R^1 \!\varprojlim H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim H^m(U, K_n) \to 0`.
Here the left term is canonically realized as the owner
`((Ksys ⋙ derivedSectionsAtOpenToAbelian X U) ⋙
  DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).firstDerivedLimit`. -/
theorem derivedSectionsOverOpen_cohomology_shortExact
    (Ksys : ℕᵒᵖ ⥤ ringedSpaceModuleDerived X)
    (K : ringedSpaceModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ derivedSectionsAtOpenToAbelian X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
            ((derivedSectionsAtOpenToAbelian X U).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
            ((derivedSectionsAtOpenToAbelian X U).obj K) ⟶
          limit
            ((Ksys ⋙ derivedSectionsAtOpenToAbelian X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Limits
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory

section

variable {D : Type u} [Category D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The family of objects underlying a sequential inverse system in a category. -/
abbrev inverseSystemFamily (Ksys : ℕᵒᵖ ⥤ D) : ℕ → D :=
  fun n ↦ Ksys.obj (Opposite.op n)

/-- The Milnor difference endomorphism of the product of a sequential inverse system. -/
def derivedLimitDifferenceMap (Ksys : ℕᵒᵖ ⥤ D)
    [HasProduct (inverseSystemFamily Ksys)] :
    ∏ᶜ inverseSystemFamily Ksys ⟶ ∏ᶜ inverseSystemFamily Ksys :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily Ksys) n -
      Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
        Ksys.map ((homOfLE (Nat.le_succ n)).op)

/-- An object is a derived limit of a sequential inverse system if it fits into the standard
Milnor distinguished triangle built from the product and the difference map `1 - shift`. -/
def IsDerivedLimit (Ksys : ℕᵒᵖ ⥤ D) (K : D) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang D

end

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

section

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms used to construct the derived category of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The cochain-level direct image functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforward f).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))

/-- The derived direct-image functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforwardToDerived f).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (ModuleQis X)

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory (RingedSpace.Modules X)) n)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory (RingedSpace.Modules Y)) n)]
variable [(modulePushforward f).Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

-- Proof sketch: the usual derived pullback `Lf^*` is left adjoint to `Rf_*`, so `Rf_*` is a
-- right adjoint and therefore preserves all small limits.
/-- The derived pushforward functor is a right adjoint. -/
theorem moduleDerivedPushforward_isRightAdjoint :
    (moduleDerivedPushforward f).IsRightAdjoint := sorry

-- Proof sketch: choose the Milnor triangle defining `R lim K_n`, apply the exact functor
-- `Rf_*`, and use that `Rf_*` preserves products because it is a right adjoint. The resulting
-- triangle is again the defining Milnor triangle, now for the inverse system obtained by applying
-- `Rf_*` termwise.
/-- Lemma 20.37.2: if `K` is a derived limit of an inverse system `Ksys` in `D(\mathcal O_X)`,
then `Rf_* K` is a derived limit of the termwise direct-image system. Equivalently, the derived
pushforward functor `Rf_*` commutes with derived limits. -/
theorem moduleDerivedPushforward_preservesDerivedLimits
    {Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X)}
    {K : DerivedCategory (RingedSpace.Modules X)}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ moduleDerivedPushforward f) ((moduleDerivedPushforward f).obj K) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_37_3 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- The category of `\mathcal O_X`-modules on a ringed space is abelian. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) :=
  inferInstance

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
local instance ringedSpaceModuleCatHasDerivedCategory :
    HasDerivedCategory (ringedSpaceModuleCat X) :=
  HasDerivedCategory.standard (ringedSpaceModuleCat X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor :
    ringedSpaceModuleCat X ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X)) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    DerivedCategory (ringedSpaceModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor X U)

/-- A model for `R^1 \!\varprojlim H^q(U, K_n)`, given by the cokernel of the Milnor difference
map on the tower `n ↦ H^q(U, K_n)`. -/
abbrev firstDerivedLimitCohomologyAtOpen
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    AddCommGrpCat.{u} :=
  cokernel
    (derivedLimitDifferenceMap
      (Ksys ⋙ moduleSectionsAsAbelianDerived X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q))

-- Proof sketch: identify `\underline{\mathcal H}^m(U)` with the value at `U` of the objectwise
-- cohomology presheaf from Lemma `20.32.3`, then apply the Milnor short exact sequence
-- from Lemma `20.37.1` to the tower `Ksys`.
/-- Remark 20.37.3: for a ringed space `(X, \mathcal O_X)`, an open subset `U ⊆ X`, a
sequential inverse system `(K_n)` in `D(\mathcal O_X)`, a chosen derived limit
`K = R\!\varprojlim K_n`, and `m : ℤ`, the presheaf values
`\underline{\mathcal H}^m(U) = H^m(U, K)` fit into the short exact sequence
`0 \to R^1 \!\varprojlim \underline{\mathcal H}^{m - 1}_n(U) \to \underline{\mathcal H}^m(U) \to
\varprojlim \underline{\mathcal H}^m_n(U) \to 0`. Here
`ringedSpaceObjectwiseCohomologyPresheaf X K m` models the presheaf
`U \mapsto \underline{\mathcal H}^m(U)`, and the left term is modeled by
`firstDerivedLimitCohomologyAtOpen X U Ksys (m - 1)`. -/
theorem objectwiseCohomologyPresheaf_value_shortExact
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X))
    (K : DerivedCategory (ringedSpaceModuleCat X))
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        firstDerivedLimitCohomologyAtOpen X U Ksys (m - 1) ⟶
          (ringedSpaceObjectwiseCohomologyPresheaf X K m).obj (op U))
      (π :
        (ringedSpaceObjectwiseCohomologyPresheaf X K m).obj (op U) ⟶
          limit
            (Ksys ⋙ moduleSectionsAsAbelianDerived X U ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-- The structure sheaf of a ringed space, regarded as a sheaf with values in `RingCat`. -/
/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
variable [IsGrothendieckAbelian.{v} (Modules X)]
variable [CategoryWithHomology (Modules X)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory (Modules X)) n)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance sheafModulesAbelian : Abelian (Modules X) := inferInstance

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
local instance sheafModulesHasDerivedCategory : HasDerivedCategory (Modules X) :=
  HasDerivedCategory.standard (Modules X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor
    (U : Opens X.carrier) :
    Modules X ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor U).Additive] :
    DerivedCategory (Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor U)

/-- The degree-`m` cohomology group `H^m(U, K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev moduleCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor U).Additive]
    (K : DerivedCategory (Modules X)) (m : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
    ((moduleSectionsAsAbelianDerived U).obj K)

/-- The inverse system `n ↦ \mathcal F_n(U)` of underlying abelian groups over a fixed open set
`U`. -/
abbrev moduleUnderlyingSectionsTowerAtOpen
    (ℱ : ℕᵒᵖ ⥤ Modules X) (U : Opens X.carrier) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ℱ ⋙ SheafOfModules.toSheaf (ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The Milnor cokernel model for `R^1 \!\varprojlim_n \mathcal F_n(U)` on the underlying
abelian groups of sections. -/
abbrev moduleUnderlyingSectionsFirstDerivedLimitAtOpen
    (ℱ : ℕᵒᵖ ⥤ Modules X) (U : Opens X.carrier) :
    AddCommGrpCat.{u} :=
  cokernel (derivedLimitDifferenceMap (moduleUnderlyingSectionsTowerAtOpen ℱ U))

variable (ℱ : ℕᵒᵖ ⥤ Modules X) (ℬ : Set (Opens X.carrier))

variable
  (hcover :
    ∀ U : Opens X.carrier,
      ∃ ι : Type u, ∃ 𝒰 : ι → Opens X.carrier, iSup 𝒰 = U ∧ ∀ i, 𝒰 i ∈ ℬ)
  (hacyclic :
    ∀ (U : Opens X.carrier), U ∈ ℬ →
      ∀ (n p : ℕ), 0 < p →
        IsZero
          (moduleCohomologyAtOpen U
            ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj
              (ℱ.obj (op n)))
            (p : ℤ)))
  (hR1 :
    ∀ (U : Opens X.carrier), U ∈ ℬ →
      IsZero (moduleUnderlyingSectionsFirstDerivedLimitAtOpen ℱ U))

-- Proof sketch: apply the openwise Milnor short exact sequence from `20.37.3.1` to the tower
-- `\mathcal F_n[0]`. On each `U ∈ ℬ`, positive stagewise cohomology vanishes by `hacyclic`, while
-- the `R^1 \!\varprojlim` term for sections vanishes by `hR1`, so the objectwise cohomology of the
-- derived limit is concentrated in degree `0` with degree-zero part equal to the ordinary inverse
-- limit presheaf. Since every open is covered by members of `ℬ`, sheafification gives the same
-- statement for cohomology sheaves, hence the derived limit is represented by `lim ℱ` in degree
-- zero.
/-- Lemma 20.37.4 (1): if every open subset of `X` is covered by opens in `ℬ`, if
`H^p(U, \mathcal F_n) = 0` for every `U ∈ ℬ`, every `n`, and every `p > 0`, and if the inverse
system of sections `\mathcal F_n(U)` has vanishing `R^1 \!\varprojlim` for every `U ∈ ℬ`, then
the ordinary inverse limit sheaf `\varprojlim_n \mathcal F_n` computes the derived inverse limit
of the tower `(\mathcal F_n)`. -/
theorem single_limit_isDerivedLimit_of_basis_acyclicity :
    IsDerivedLimit
      (ℱ ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ))
      ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj (limit ℱ)) := sorry

-- Proof sketch: apply the Milnor short exact sequence from `20.37.3.1` to the degree-zero tower
-- `\mathcal F_n[0]` and to the derived limit identified in part `(1)` with `(\varprojlim_n
-- \mathcal F_n)[0]`. For `U ∈ ℬ` and `p > 0`, the right term `\varprojlim_n H^p(U,\mathcal F_n)`
-- vanishes by `hacyclic`, and the left `R^1 \!\varprojlim` term vanishes by `hR1` when `p = 1`
-- and by the stagewise vanishing in degree `p - 1` when `p > 1`. Hence `H^p(U, \varprojlim_n
-- \mathcal F_n) = 0`.
/-- Lemma 20.37.4 (2): under the same hypotheses, the inverse limit sheaf
`\varprojlim_n \mathcal F_n` has vanishing higher cohomology on every open set `U ∈ ℬ`; that is,
`H^p(U, \varprojlim_n \mathcal F_n) = 0` for all `p > 0`. -/
theorem higherCohomologyAtBasisOpen_isZero_of_basis_acyclicity
    (U : Opens X.carrier) (hU : U ∈ ℬ) (p : ℕ) (hp : 0 < p) :
    IsZero
      (moduleCohomologyAtOpen U
        ((DerivedCategory.singleFunctor (Modules X) (0 : ℤ)).obj (limit ℱ))
        (p : ℤ)) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [IsGrothendieckAbelian.{v} (RingedSpace.Modules X)]

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
private abbrev moduleSectionsAsAbelianFunctor
    (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
private abbrev moduleSectionsAsAbelianDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor X U)

/-- The degree-`m` cohomology group `H^m(U, K)` of a derived `\mathcal O_X`-module `K`. -/
private abbrev moduleCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (K : DerivedCategory (RingedSpace.Modules X)) (m : ℤ) : AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
    ((moduleSectionsAsAbelianDerived X U).obj K)

/-- The sequential inverse system `n ↦ H^m(U, K_n)` attached to a tower in
`D(\mathcal O_X)`. -/
private abbrev moduleCohomologyTowerAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X)) (m : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Ksys ⋙ moduleSectionsAsAbelianDerived X U) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} m

/-- A model for `R^1 \!\varprojlim H^q(U, K_n)`, given by the cokernel of the Milnor difference
map on the tower `n ↦ H^q(U, K_n)`. -/
private abbrev firstDerivedLimitCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X)) (q : ℤ) :
    AddCommGrpCat.{u} :=
  cokernel (derivedLimitDifferenceMap (moduleCohomologyTowerAtOpen X U Ksys q))

/-- The transition map `H^m(U, K_n) → H^m(U, K_i)` for `i ≤ n` in the tower of objectwise
cohomology groups attached to a sequential inverse system in `D(\mathcal O_X)`. -/
private abbrev moduleCohomologyToEventualStageAtOpen
    (U : Opens X.carrier)
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (m : ℤ) (i n : ℕ) (hin : i ≤ n) :
    moduleCohomologyAtOpen X U (Ksys.obj (op n)) m ⟶
      moduleCohomologyAtOpen X U (Ksys.obj (op i)) m :=
  (moduleCohomologyTowerAtOpen X U Ksys m).map ((homOfLE hin).op)

/-- The map on cohomology sheaves induced by a morphism in `D(\mathcal O_X)`. -/
private abbrev cohomologySheafMap
    {K L : DerivedCategory (RingedSpace.Modules X)} (m : ℤ) (c : K ⟶ L) :
    ringedSpaceCohomologySheaf X K m ⟶ ringedSpaceCohomologySheaf X L m :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).map
    ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) m).map c)

/-- The induced map on stalks of degree-`m` cohomology sheaves. -/
private abbrev cohomologySheafStalkMap
    (x : X) {K L : DerivedCategory (RingedSpace.Modules X)} (m : ℤ) (c : K ⟶ L) :
    TopCat.Presheaf.stalk (ringedSpaceCohomologySheaf X K m).1 x ⟶
      TopCat.Presheaf.stalk (ringedSpaceCohomologySheaf X L m).1 x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (cohomologySheafMap X m c).1

/-- A morphism `c : K ⟶ K_n` is the canonical comparison from a chosen derived limit `K` to the
`n`th stage if it comes from the Milnor product map defining that derived limit. -/
private def IsDerivedLimitStageComparison
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (K : DerivedCategory (RingedSpace.Modules X)) (n : ℕ) (c : K ⟶ Ksys.obj (op n)) : Prop :=
  ∃ _ : HasProduct (inverseSystemFamily Ksys),
    ∃ (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
      (δ : ∏ᶜ inverseSystemFamily Ksys ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ ∈ distTriang
          (DerivedCategory (RingedSpace.Modules X)) ∧
        c = ι ≫ Pi.π (inverseSystemFamily Ksys) n

/-- A neighborhood `U ⊆ W` of `x` satisfies the local Milnor vanishing and eventual injectivity
hypotheses appearing in the stalkwise Milnor criterion. -/
private class LocalMilnorNeighborhoodCondition
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (x : X) (m : ℤ) (nx : ℕ) (W U : Opens X.carrier) : Prop where
  /-- The chosen neighborhood still contains the point `x`. -/
  mem : x ∈ U
  /-- The chosen neighborhood is contained in the ambient neighborhood `W`. -/
  le : U ≤ W
  /-- The local `R^1 \!\varprojlim` term vanishes on the chosen neighborhood. -/
  r1_vanish :
    IsZero (firstDerivedLimitCohomologyAtOpen X U Ksys (m - 1))
  /-- The transition maps into stage `n(x)` are monomorphisms on the chosen neighborhood. -/
  transition_mono :
    ∀ n : ℕ, ∀ hn : nx ≤ n,
      Mono (moduleCohomologyToEventualStageAtOpen X U Ksys m nx n hn)

-- Proof sketch: represent a germ in the stalk of `H^m(K)` by a section over an open neighborhood
-- coming from the cofinal neighborhood system in the hypotheses. Using the sheafification
-- description of cohomology sheaves from Lemma `20.32.3`, shrink so that its image in the stage
-- `n(x)` stalk is already zero on that neighborhood. Then apply the Milnor short exact sequence
-- from `20.37.3.1`: the local `R^1 lim` term vanishes, and the local transition maps into stage
-- `n(x)` are injective, forcing the representing section itself to vanish.
/-- Lemma 20.37.5: let `(X, \mathcal O_X)` be a ringed space, let `(K_n)` be a sequential inverse
system in `D(\mathcal O_X)`, let `x ∈ X`, and let `m ∈ \mathbf Z`. Assume there is an index
`n(x)` such that every open neighborhood of `x` contains a smaller open neighborhood `U` with
`R^1 \!\varprojlim_n H^{m-1}(U, K_n) = 0` and such that the transition maps
`H^m(U, K_n) → H^m(U, K_{n(x)})` are injective for all `n ≥ n(x)`. Then the induced map on
stalks `H^m(R \!\varprojlim_n K_n)_x → H^m(K_{n(x)})_x`, formalized using a chosen compatible
comparison morphism `c : K ⟶ K_{n(x)}`, is injective. -/
theorem cohomologyStalkMap_injective_to_eventual_stage_of_local_milnor_conditions
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (RingedSpace.Modules X))
    (K : DerivedCategory (RingedSpace.Modules X))
    (x : X) (m : ℤ) (nx : ℕ)
    (c : K ⟶ Ksys.obj (op nx))
    (hc : IsDerivedLimitStageComparison X Ksys K nx c)
    (hlocal :
      ∀ (W : Opens X.carrier), x ∈ W →
        ∃ U : Opens X.carrier,
          LocalMilnorNeighborhoodCondition X Ksys x m nx W U) :
    Function.Injective (cohomologySheafStalkMap X x m c) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- A derived `\mathcal O_X`-module has eventually vanishing local cohomology of its cohomology
sheaves near each point if, after shrinking inside any neighborhood of `x`, one gets a uniform
bound in each total degree beyond which the groups `H^p(U, H^{m-p}(E))` vanish. -/
def EventualCohomologySheafVanishingNear
    (E : DerivedCategory (ringedSpaceModuleCat X)) : Prop :=
  ∀ x : X, ∃ px : ℤ → ℤ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
            IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U)

-- Proof sketch: this is just the defining neighborhood-shrinking form of
-- `EventualCohomologySheafVanishingNear`.
/-- The local vanishing hypothesis can be used on any chosen neighborhood of a point. -/
theorem EventualCohomologySheafVanishingNear.exists_shrunk_open
    {E : DerivedCategory (ringedSpaceModuleCat X)}
    (hE : EventualCohomologySheafVanishingNear X E)
    (x : X) :
    ∃ px : ℤ → ℤ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
              IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U) := sorry

-- Proof sketch: for each degree `m` and point `x`, choose `n(x)` from the local bounds in the
-- hypothesis so that the truncation triangles of Remark `13.12.4` force eventual stability of
-- the maps on `H^{m-1}(U,-)` and `H^m(U,-)` over a cofinal system of neighborhoods of `x`.
-- Lemma `20.37.5` then gives injectivity on stalks of the map
-- `H^m(L)_x → H^m(\tau_{\ge -n(x)}E)_x`; since `H^m(E) → H^m(\tau_{\ge -n(x)}E)` is an
-- isomorphism for `n(x) ≥ -m`, the induced stalk map `H^m(E)_x → H^m(L)_x` is bijective. Thus
-- every cohomology sheaf map induced by `c` is an isomorphism, so `c` is an isomorphism in the
-- derived category.
/-- Lemma 20.37.6: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume that for every point `x ∈ X` there is a function `p(x,-) : \mathbf Z → \mathbf Z` such
that, after shrinking inside any neighborhood of `x`, one has
`H^p(U, H^{m-p}(E)) = 0` for all `p > p(x,m)`. Then any compatible comparison morphism
`E ⟶ R\!\varprojlim_n \tau_{\ge -n}E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem isIso_of_truncationDerivedLimitComparison_of_eventualCohomologySheafVanishingNear
    (E : DerivedCategory (ringedSpaceModuleCat X))
    {L : DerivedCategory (ringedSpaceModuleCat X)} (c : E ⟶ L)
    (hc : CategoryTheory.IsTruncationDerivedLimitComparison E L c)
    (hE : EventualCohomologySheafVanishingNear X E) :
    IsIso c := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_7 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- Sheaves of `\mathcal O_X`-modules form an abelian category. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) := inferInstance

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(E)` of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf
    (E : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj E)

/-- The stage `τ_{\ge -n} E` in the canonical truncation tower of a derived `\mathcal O_X`-module
`E`. -/
noncomputable abbrev derivedTruncationGEStage
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    DerivedCategory (ringedSpaceModuleCat X) :=
  Q.obj ((Q.objPreimage E).truncGE (-((n : ℕ) : ℤ)))

/-- The transition map `τ_{\ge -(n + 1)} E ⟶ τ_{\ge -n} E` in the truncation tower of `E`. -/
noncomputable abbrev derivedTruncationGEStep
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    derivedTruncationGEStage X E (n + 1) ⟶ derivedTruncationGEStage X E n :=
  let E' := Q.objPreimage E
  let a : ℤ := -(((n + 1 : ℕ)) : ℤ)
  let b : ℤ := -((n : ℕ) : ℤ)
  let hab : a ≤ b :=
    neg_le_neg (show ((n : ℕ) : ℤ) ≤ (((n + 1 : ℕ)) : ℤ) from
      Int.ofNat_le.mpr (Nat.le_succ n))
  letI : (E'.truncGE b).IsStrictlyGE a :=
    (E'.truncGE b).isStrictlyGE_of_ge a b hab
  Q.map (CochainComplex.truncGEMap (E'.πTruncGE b) a) ≫
    inv (Q.map ((E'.truncGE b).πTruncGE a))

/-- The inverse system `n ↦ τ_{\ge -n} E` in `D(\mathcal O_X)`. -/
noncomputable abbrev derivedTruncationGETower
    (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X) :=
  Functor.ofOpSequence (derivedTruncationGEStep X E)

/-- The family of objects underlying the truncation tower of `E`. -/
abbrev derivedTruncationGETowerFamily
    (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕ → DerivedCategory (ringedSpaceModuleCat X) :=
  fun n ↦ (derivedTruncationGETower X E).obj (Opposite.op n)

/-- The Milnor difference map `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))` for the truncation tower of
`E`. -/
def derivedTruncationGETowerDifferenceMap
    (E : DerivedCategory (ringedSpaceModuleCat X))
    [HasProduct (derivedTruncationGETowerFamily X E)] :
    ∏ᶜ derivedTruncationGETowerFamily X E ⟶ ∏ᶜ derivedTruncationGETowerFamily X E :=
  Pi.lift fun n ↦
    Pi.π (derivedTruncationGETowerFamily X E) n -
      Pi.π (derivedTruncationGETowerFamily X E) (n + 1) ≫
        (derivedTruncationGETower X E).map ((homOfLE (Nat.le_succ n)).op)

/-- The canonical map `E ⟶ τ_{\ge -n} E` obtained from truncating a chosen cochain-complex
representative of `E`. -/
noncomputable abbrev derivedTruncationGEToStage
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    E ⟶ derivedTruncationGEStage X E n :=
  (Q.objObjPreimageIso E).inv ≫
    Q.map ((Q.objPreimage E).πTruncGE (-((n : ℕ) : ℤ)))

/-- A morphism `c : E ⟶ L` is a compatible comparison from `E` to a chosen derived limit of the
truncation tower `(\tau_{\ge -n} E)_n` if `L` sits in the Milnor triangle and the stage
projections recover the canonical maps `E ⟶ τ_{\ge -n} E`. -/
def IsTruncationDerivedLimitComparison
    (E L : DerivedCategory (ringedSpaceModuleCat X)) (c : E ⟶ L) : Prop :=
  ∃ _ : HasProduct (derivedTruncationGETowerFamily X E),
    ∃ (ι : L ⟶ ∏ᶜ derivedTruncationGETowerFamily X E)
      (δ : ∏ᶜ derivedTruncationGETowerFamily X E ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedTruncationGETowerDifferenceMap X E) δ ∈
          distTriang (DerivedCategory (ringedSpaceModuleCat X)) ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (derivedTruncationGETowerFamily X E) n =
          derivedTruncationGEToStage X E n

/-- A derived `\mathcal O_X`-module has locally uniform vanishing of higher cohomology for its
negative cohomology sheaves if, near each point `x`, there is one bound `d_x` that annihilates
`H^p(U, H^q(E))` for all `q < 0` on some neighborhood basis of `x`. -/
def LocallyUniformNegativeCohomologySheafVanishing
    (E : DerivedCategory (ringedSpaceModuleCat X)) : Prop :=
  ∀ x : X, ∃ d : ℕ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ q : ℤ, q < 0 →
            ∀ p : ℕ, d < p →
              IsZero ((ringedSpaceCohomologySheaf X E q).H' p U)

-- Proof sketch: this is immediate by unfolding
-- `LocallyUniformNegativeCohomologySheafVanishing`; the hypothesis already says that for each
-- point `x` and each neighborhood `W` of `x`, one may shrink to such a `U`.
/-- The local uniform vanishing hypothesis can be applied after shrinking inside any prescribed
open neighborhood of a point. -/
theorem LocallyUniformNegativeCohomologySheafVanishing.exists_shrunk_open
    {E : DerivedCategory (ringedSpaceModuleCat X)}
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E) :
    ∀ x : X, ∃ d : ℕ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ q : ℤ, q < 0 →
              ∀ p : ℕ, d < p →
                IsZero ((ringedSpaceCohomologySheaf X E q).H' p U) := sorry

-- Proof sketch: convert the source hypothesis to
-- the eventual-vanishing criterion of Lemma `20.37.6` by choosing the bound
-- `p(x,m) = d_x + max (0, m)`. Then apply the previous lemma in the source development to deduce
-- that the canonical comparison map from `E` to the derived inverse limit of its truncation tower
-- is an isomorphism.
/-- Lemma 20.37.7: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume that for every `x ∈ X` there exist an integer `d_x ≥ 0` and a fundamental system of open
neighborhoods of `x` such that `H^p(U, H^q(E)) = 0` for all members `U` of that system, all
`p > d_x`, and all `q < 0`. Then any compatible comparison map
`E ⟶ R\!\varprojlim_n \tau_{\ge -n} E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem isIso_of_truncationDerivedLimitComparison_of_locallyUniformNegativeCohomologySheafVanishing
    (E : DerivedCategory (ringedSpaceModuleCat X))
    {L : DerivedCategory (ringedSpaceModuleCat X)} (c : E ⟶ L)
    (hc : IsTruncationDerivedLimitComparison X E L c)
    (hE : LocallyUniformNegativeCohomologySheafVanishing X E) :
    IsIso c := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_8 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry
open DerivedCategory

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology X)
    (CategoryTheory.forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of modules on a ringed space `X`. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf (X : RingedSpace.{u})
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

/-- The stage `τ_{\ge -n} E` in the canonical lower truncation tower of a derived
`\mathcal O_X`-module `E`. -/
noncomputable abbrev derivedTruncationGEStage
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    DerivedCategory (ringedSpaceModuleCat X) :=
  Q.obj ((Q.objPreimage E).truncGE (-((n : ℕ) : ℤ)))

/-- The transition morphism `τ_{\ge -(n + 1)} E ⟶ τ_{\ge -n} E` in the truncation tower. -/
noncomputable abbrev derivedTruncationGEStep
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    derivedTruncationGEStage E (n + 1) ⟶ derivedTruncationGEStage E n :=
  let E' := Q.objPreimage E
  let a : ℤ := -(((n + 1 : ℕ)) : ℤ)
  let b : ℤ := -((n : ℕ) : ℤ)
  let hab : a ≤ b :=
    neg_le_neg (show ((n : ℕ) : ℤ) ≤ (((n + 1 : ℕ)) : ℤ) from
      Int.ofNat_le.mpr (Nat.le_succ n))
  letI : (E'.truncGE b).IsStrictlyGE a :=
    (E'.truncGE b).isStrictlyGE_of_ge a b hab
  Q.map (CochainComplex.truncGEMap (E'.πTruncGE b) a) ≫
    inv (Q.map ((E'.truncGE b).πTruncGE a))

/-- The inverse system `n ↦ τ_{\ge -n} E` in the derived category of `\mathcal O_X`-modules. -/
noncomputable abbrev derivedTruncationGETower
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X) :=
  Functor.ofOpSequence (derivedTruncationGEStep E)

/-- The underlying family of objects of the truncation tower of `E`. -/
abbrev derivedTruncationGETowerFamily
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕ → DerivedCategory (ringedSpaceModuleCat X) :=
  fun n ↦ (derivedTruncationGETower E).obj (Opposite.op n)

/-- The Milnor difference map on the product of the truncation tower of `E`. -/
def derivedTruncationGETowerDifferenceMap
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X))
    [HasProduct (derivedTruncationGETowerFamily E)] :
    ∏ᶜ derivedTruncationGETowerFamily E ⟶ ∏ᶜ derivedTruncationGETowerFamily E :=
  Pi.lift fun n ↦
    Pi.π (derivedTruncationGETowerFamily E) n -
      Pi.π (derivedTruncationGETowerFamily E) (n + 1) ≫
        (derivedTruncationGETower E).map ((homOfLE (Nat.le_succ n)).op)

/-- The canonical morphism `E ⟶ τ_{\ge -n} E` obtained from truncating a chosen cochain-complex
representative of `E`. -/
noncomputable abbrev derivedTruncationGEToStage
    {X : RingedSpace.{u}} (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    E ⟶ derivedTruncationGEStage E n :=
  (Q.objObjPreimageIso E).inv ≫
    Q.map ((Q.objPreimage E).πTruncGE (-((n : ℕ) : ℤ)))

/-- A morphism `c : E ⟶ L` is a compatible comparison from `E` to a chosen derived limit of its
truncation tower if `L` fits into the Milnor triangle and the projections to each truncation stage
recover the canonical truncation maps. -/
def IsTruncationDerivedLimitComparison
    {X : RingedSpace.{u}}
    (E L : DerivedCategory (ringedSpaceModuleCat X)) (c : E ⟶ L) : Prop :=
  ∃ _ : HasProduct (derivedTruncationGETowerFamily E),
    ∃ (ι : L ⟶ ∏ᶜ derivedTruncationGETowerFamily E)
      (δ : ∏ᶜ derivedTruncationGETowerFamily E ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedTruncationGETowerDifferenceMap E) δ ∈
          distTriang (DerivedCategory (ringedSpaceModuleCat X)) ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (derivedTruncationGETowerFamily E) n =
          derivedTruncationGEToStage E n

/-- A derived `\mathcal O_X`-module has eventually vanishing local cohomology of its cohomology
sheaves near each point if, after shrinking inside any neighborhood of the point, one gets a
uniform bound in each total degree beyond which the groups `H^p(U, H^{m-p}(E))` vanish. -/
def EventualCohomologySheafVanishingNear
    {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (E : DerivedCategory (ringedSpaceModuleCat X)) : Prop :=
  ∀ x : X, ∃ px : ℤ → ℤ,
    ∀ W : Opens X.carrier, x ∈ W →
      ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
            IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U)

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

section UniformBasisVanishing

variable (E : DerivedCategory (ringedSpaceModuleCat X))
variable (cohomologyBound : ℤ → ℤ) (𝓑 : Set (Opens X.carrier))
variable
  (hcover :
    ∀ W : Opens X.carrier, ∃ ι : Type u, ∃ U : ι → Opens X.carrier,
      (∀ i, U i ∈ 𝓑) ∧ iSup U = W)
variable
  (hvanish :
    ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
      ∀ m : ℤ, ∀ p : ℕ, cohomologyBound m < (p : ℤ) →
        IsZero ((ringedSpaceCohomologySheaf X E (m - (p : ℤ))).H' p U))

-- Proof sketch: fix a point `x` and a neighborhood `W`. Choose a covering of `W` by opens in
-- `𝓑`, then pick one member containing `x`. The same global function `cohomologyBound` serves as
-- the local bound `p(x,-)`, and the given vanishing hypothesis on members of `𝓑` is exactly the
-- neighborhood condition required in `EventualCohomologySheafVanishingNear`.
/-- A uniform vanishing bound on a basis-like family of opens implies the pointwise shrinking
condition `EventualCohomologySheafVanishingNear`. -/
theorem eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing :
    EventualCohomologySheafVanishingNear E := sorry

variable {L : DerivedCategory (ringedSpaceModuleCat X)} (c : E ⟶ L)
variable (hc : IsTruncationDerivedLimitComparison E L c)

-- Proof sketch: first use
-- `eventualCohomologySheafVanishingNear_of_uniform_basis_vanishing` to convert the global
-- basis-wise vanishing assumption into the local hypothesis of Lemma `20.37.6`. Then apply the
-- local-to-global truncation comparison criterion for a compatible map to the derived limit of the
-- truncation tower.
/-- Lemma 20.37.8: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume there exist a function `p(-) : \mathbf Z → \mathbf Z` and a set `\mathcal B` of opens of
`X` such that every open subset of `X` admits a covering by members of `\mathcal B`, and
`H^p(U, H^{m-p}(E)) = 0` for `p > p(m)` and `U ∈ \mathcal B`. Then any compatible comparison
morphism `E ⟶ R\!\varprojlim_n τ_{\ge -n} E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem isIso_of_truncationDerivedLimitComparison_of_uniform_basis_vanishing :
    IsIso c := sorry

end UniformBasisVanishing

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_9 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- Sheaves of `\mathcal O_X`-modules form an abelian category. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) := inferInstance

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(E)` of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf
    (E : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj E)

/-- The stage `τ_{\ge -n} E` in the canonical truncation tower of a derived `\mathcal O_X`-module
`E`. -/
noncomputable abbrev derivedTruncationGEStage
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    DerivedCategory (ringedSpaceModuleCat X) :=
  Q.obj ((Q.objPreimage E).truncGE (-((n : ℕ) : ℤ)))

/-- The transition map `τ_{\ge -(n + 1)} E ⟶ τ_{\ge -n} E` in the truncation tower of `E`. -/
noncomputable abbrev derivedTruncationGEStep
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    derivedTruncationGEStage X E (n + 1) ⟶ derivedTruncationGEStage X E n :=
  let E' := Q.objPreimage E
  let a : ℤ := -(((n + 1 : ℕ)) : ℤ)
  let b : ℤ := -((n : ℕ) : ℤ)
  let hab : a ≤ b :=
    neg_le_neg (show ((n : ℕ) : ℤ) ≤ (((n + 1 : ℕ)) : ℤ) from
      Int.ofNat_le.mpr (Nat.le_succ n))
  letI : (E'.truncGE b).IsStrictlyGE a :=
    (E'.truncGE b).isStrictlyGE_of_ge a b hab
  Q.map (CochainComplex.truncGEMap (E'.πTruncGE b) a) ≫
    inv (Q.map ((E'.truncGE b).πTruncGE a))

/-- The inverse system `n ↦ τ_{\ge -n} E` in `D(\mathcal O_X)`. -/
noncomputable abbrev derivedTruncationGETower
    (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X) :=
  Functor.ofOpSequence (derivedTruncationGEStep X E)

/-- The family of objects underlying the truncation tower of `E`. -/
abbrev derivedTruncationGETowerFamily
    (E : DerivedCategory (ringedSpaceModuleCat X)) :
    ℕ → DerivedCategory (ringedSpaceModuleCat X) :=
  fun n ↦ (derivedTruncationGETower X E).obj (Opposite.op n)

/-- The Milnor difference map `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))` for the truncation tower of
`E`. -/
def derivedTruncationGETowerDifferenceMap
    (E : DerivedCategory (ringedSpaceModuleCat X))
    [HasProduct (derivedTruncationGETowerFamily X E)] :
    ∏ᶜ derivedTruncationGETowerFamily X E ⟶ ∏ᶜ derivedTruncationGETowerFamily X E :=
  Pi.lift fun n ↦
    Pi.π (derivedTruncationGETowerFamily X E) n -
      Pi.π (derivedTruncationGETowerFamily X E) (n + 1) ≫
        (derivedTruncationGETower X E).map ((homOfLE (Nat.le_succ n)).op)

/-- The canonical map `E ⟶ τ_{\ge -n} E` obtained from truncating a chosen cochain-complex
representative of `E`. -/
noncomputable abbrev derivedTruncationGEToStage
    (E : DerivedCategory (ringedSpaceModuleCat X)) (n : ℕ) :
    E ⟶ derivedTruncationGEStage X E n :=
  (Q.objObjPreimageIso E).inv ≫
    Q.map ((Q.objPreimage E).πTruncGE (-((n : ℕ) : ℤ)))

/-- A morphism `c : E ⟶ L` is a compatible comparison from `E` to a chosen derived limit of the
truncation tower `(\tau_{\ge -n} E)_n` if `L` sits in the Milnor triangle and the stage
projections recover the canonical maps `E ⟶ τ_{\ge -n} E`. -/
def IsTruncationDerivedLimitComparison
    (E L : DerivedCategory (ringedSpaceModuleCat X)) (c : E ⟶ L) : Prop :=
  ∃ _ : HasProduct (derivedTruncationGETowerFamily X E),
    ∃ (ι : L ⟶ ∏ᶜ derivedTruncationGETowerFamily X E)
      (δ : ∏ᶜ derivedTruncationGETowerFamily X E ⟶ L⟦(1 : ℤ)⟧),
      Triangle.mk ι (derivedTruncationGETowerDifferenceMap X E) δ ∈
          distTriang (DerivedCategory (ringedSpaceModuleCat X)) ∧
        ∀ n : ℕ, c ≫ ι ≫ Pi.π (derivedTruncationGETowerFamily X E) n =
          derivedTruncationGEToStage X E n

-- Proof sketch: apply Lemma `20.37.7` with the constant local bound `d_x = d` for every point
-- `x ∈ X`. Since `𝓑` is a topological basis, each neighborhood `W` of `x` contains some
-- `U ∈ 𝓑` with `x ∈ U ⊆ W`, and the assumed vanishing on basis opens supplies the required local
-- vanishing hypothesis for the negative cohomology sheaves of `E`.
/-- Lemma 20.37.9: let `(X, \mathcal O_X)` be a ringed space and let `E ∈ D(\mathcal O_X)`.
Assume there exist an integer `d ≥ 0` and a basis `\mathcal B` for the topology of `X` such
that `H^p(U, H^q(E)) = 0` for `U ∈ \mathcal B`, `p > d`, and `q < 0`. Then any compatible
comparison morphism formalizing the canonical map
`E \to R\!\varprojlim_n \tau_{\ge -n} E` from Remark `13.34.5` is an isomorphism in
`D(\mathcal O_X)`. -/
theorem truncationComparison_isIso_of_basiswise_negative_cohomologySheaf_vanishing
    (E : DerivedCategory (ringedSpaceModuleCat X))
    {K : DerivedCategory (ringedSpaceModuleCat X)}
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison X E K c)
    (𝓑 : Set (Opens X.carrier))
    (h𝓑 : Opens.IsBasis 𝓑)
    (d : ℕ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, d < p →
          ∀ q : ℤ, q < 0 →
            IsZero ((ringedSpaceCohomologySheaf X E q).H' p U)) :
    IsIso c := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_10 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev ringedSpaceModuleCat (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) :=
  inferInstance

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor
    (U : Opens X.carrier) :
    ringedSpaceModuleCat X ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The cochain-level functor underlying derived sections over `U`. -/
abbrev moduleSectionsAsAbelianToDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    CochainComplex (ringedSpaceModuleCat X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

-- Proof sketch: the category `Mod(\mathcal O_X)` is Grothendieck abelian, so K-injective
-- resolutions compute right derived functors. Applying this to the additive sections functor
-- `\Gamma(U,-)` produces the total right derived functor defining `R\Gamma(U,-)`.
/-- The cochain-level sections functor over `U` admits a total right derived functor. -/
theorem moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    (moduleSectionsAsAbelianToDerived X U).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (ringedSpaceModuleCat X) (ComplexShape.up ℤ)) := sorry

attribute [local instance] moduleSectionsAsAbelianToDerived_hasRightDerivedFunctor

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    DerivedCategory (ringedSpaceModuleCat X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (moduleSectionsAsAbelianToDerived X U).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ringedSpaceModuleCat X) (ComplexShape.up ℤ))

/-- The degree-`m` cohomology group `H^m(U, K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev moduleCohomologyAtOpen
    (U : Opens X.carrier)
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (K : DerivedCategory (ringedSpaceModuleCat X)) (m : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
    ((moduleSectionsAsAbelianDerived X U).obj K)

/-- The underlying abelian sheaf of the degree-`q` cohomology sheaf `H^q(K)` of a derived
`\mathcal O_X`-module. -/
abbrev ringedSpaceCohomologySheaf
    (K : DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (ringedSpaceRingCatSheaf X)).obj
    ((DerivedCategory.homologyFunctor (ringedSpaceModuleCat X) q).obj K)

-- Proof sketch: apply Lemma `20.37.9` with `d = 0` to identify `K` with the derived limit of its
-- truncation tower. For `U ∈ ℬ`, use the Milnor short exact sequence from `20.37.3.1` for that
-- tower. Example `20.29.3` computes the cohomology of each bounded-below truncation
-- `τ_{\ge -n} K` from its cohomology sheaves, and the hypothesis forces the resulting spectral
-- sequence to degenerate at `E₂`, giving `H^q(U, τ_{\ge -n} K) = H^0(U, H^q(τ_{\ge -n} K))`.
-- Once `n > -q`, these groups stabilize to `H^0(U, H^q(K))`, so the `R^1 \!\varprojlim` term
-- vanishes and the limit term is canonically `H^0(U, H^q(K))`.
/-- Lemma 20.37.10: let `(X, \mathcal O_X)` be a ringed space, let `K ∈ D(\mathcal O_X)`, and
let `ℬ` be a set of opens such that every open subset of `X` admits a covering by members of
`ℬ`. If for every `U ∈ ℬ`, every `q : ℤ`, and every `p > 0` one has
`H^p(U, H^q(K)) = 0`, then for every `U ∈ ℬ` and every `q : ℤ` the hypercohomology group
`H^q(U, K)` is canonically isomorphic to the degree-zero cohomology
`H^0(U, H^q(K))` of the cohomology sheaf. -/
theorem cohomologyOverBasisOpen_iso_zeroDegreeCohomologySheafSections
    (K : DerivedCategory (ringedSpaceModuleCat X))
    (ℬ : Set (Opens X.carrier))
    (hcover :
      ∀ V : Opens X.carrier,
        ∃ ι : Type u, ∃ 𝒰 : ι → Opens X.carrier, iSup 𝒰 = V ∧ ∀ i, 𝒰 i ∈ ℬ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ ℬ →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ, IsZero ((ringedSpaceCohomologySheaf X K q).H' p U))
    (U : Opens X.carrier) (hU : U ∈ ℬ) (q : ℤ) :
    IsIsomorphic
      (moduleCohomologyAtOpen X U K q)
      ((ringedSpaceCohomologySheaf X K q).H' 0 U) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_37_11 (from Chap20) -/
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
