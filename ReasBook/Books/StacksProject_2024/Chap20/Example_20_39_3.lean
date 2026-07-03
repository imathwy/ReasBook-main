import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.Chap20.Lemma_20_39_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable {A : Type u} [CommRing A]

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of `\mathcal O_X`-modules on a ringed space. -/
/-- The global-sections ring `Γ(X, \mathcal O_X)`. -/
abbrev globalSectionsRing (X : RingedSpace.{u}) : CommRingCat :=
  X.presheaf.obj (op (⊤ : Opens X.carrier))

/-- The underlying `RingCat`-valued presheaf of the structure sheaf. -/
private abbrev structureSheafPresheaf (X : RingedSpace.{u}) :=
  (ringCatSheaf X).obj

/-- The top open subset of a ringed space. -/
abbrev topOpen (X : RingedSpace.{u}) : Opens X.carrier :=
  ⊤

/-- Restriction of a global section of `\mathcal O_X` to an open subset. -/
abbrev ringGlobalSectionRestrict
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (U : Opens X.carrier) :
    (structureSheafPresheaf X).obj (op U) :=
  (((structureSheafPresheaf X).map
      (homOfLE (show U ≤ topOpen X from by intro x hx; trivial)).op).hom f :
    (structureSheafPresheaf X).obj (op U))

/-- The objectwise action of a global section on the sections of an `\mathcal O_X`-module. -/
abbrev ringGlobalSectionMulAppFun
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (F : Modules X)
    (U : (Opens X.carrier)ᵒᵖ) :
    F.val.obj U → F.val.obj U :=
  fun s ↦
    let r : (structureSheafPresheaf X).obj U := ringGlobalSectionRestrict f (unop U)
    let s' : F.val.obj U := s
    show F.val.obj U from r • s'

-- Proof sketch: after evaluating on `U`, this is ordinary distributivity of scalar multiplication
-- by the restricted section `f|_U`.
/-- Multiplication by a global section preserves addition on every open set. -/
theorem ringGlobalSectionMulAppFun_map_add
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (F : Modules X)
    (U : (Opens X.carrier)ᵒᵖ) (s t : F.val.obj U) :
    ringGlobalSectionMulAppFun f F U (s + t) =
      ringGlobalSectionMulAppFun f F U s + ringGlobalSectionMulAppFun f F U t := sorry

-- Proof sketch: the section ring on `U` acts linearly on `F(U)`, so multiplication by `f|_U`
-- commutes with scalar multiplication.
/-- Multiplication by a global section is linear over the ring of sections on every open set. -/
theorem ringGlobalSectionMulAppFun_map_smul
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (F : Modules X)
    (U : (Opens X.carrier)ᵒᵖ) (a : (structureSheafPresheaf X).obj U) (s : F.val.obj U) :
    ringGlobalSectionMulAppFun f F U (a • s) =
      a • ringGlobalSectionMulAppFun f F U s := sorry

/-- Multiplication by a global section as an endomorphism of the section module over `U`. -/
abbrev ringGlobalSectionMulApp
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (F : Modules X)
    (U : (Opens X.carrier)ᵒᵖ) :
    F.val.obj U ⟶ F.val.obj U :=
  let M : ModuleCat ((structureSheafPresheaf X).obj U) := F.val.obj U
  let linearMap : M →ₗ[(structureSheafPresheaf X).obj U] M :=
    { toFun := ringGlobalSectionMulAppFun f F U
      map_add' := ringGlobalSectionMulAppFun_map_add f F U
      map_smul' := ringGlobalSectionMulAppFun_map_smul f F U }
  show M ⟶ M from (ModuleCat.homEquiv).symm linearMap

-- Proof sketch: the restriction maps of `F` are linear over the structure-sheaf restriction maps,
-- so multiplication by `f` commutes with restriction.
/-- Multiplication by a global section is natural with respect to restriction. -/
theorem ringGlobalSectionMul_naturality
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (F : Modules X)
    {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) :
    F.val.map i ≫
      (ModuleCat.restrictScalars (((structureSheafPresheaf X).map i).hom)).map
        (ringGlobalSectionMulApp f F V) =
    ringGlobalSectionMulApp f F U ≫ F.val.map i := sorry

/-- Multiplication by a global section as an endomorphism of an `\mathcal O_X`-module. -/
abbrev ringGlobalSectionMul
    {X : RingedSpace.{u}} (f : globalSectionsRing X) (F : Modules X) :
    F ⟶ F where
  val.app U := ringGlobalSectionMulApp f F U
  val.naturality i := ringGlobalSectionMul_naturality f F i

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on a ringed space. -/
abbrev sheafModulesDerived (X : RingedSpace.{u}) :=
  DerivedCategory (Modules X)

/-- The derived category `D(Γ(X,\mathcal O_X))` of modules over the global-sections ring. -/
abbrev globalSectionsDerived (X : RingedSpace.{u}) :=
  DerivedCategory (ModuleCat.{u} (globalSectionsRing X))

/-- The degree-zero embedding of `\mathcal O_X`-modules into `D(\mathcal O_X)`. -/
abbrev sheafModulesSingleZeroFunctor (X : RingedSpace.{u}) :
    Modules X ⥤ sheafModulesDerived X :=
  DerivedCategory.singleFunctor (Modules X) (0 : ℤ)

/-- The degree-`p` homology functor on `D(Γ(X,\mathcal O_X))`. -/
abbrev globalSectionsHomologyFunctor (X : RingedSpace.{u}) (p : ℤ) :
    globalSectionsDerived X ⥤ ModuleCat.{u} (globalSectionsRing X) :=
  DerivedCategory.homologyFunctor (ModuleCat.{u} (globalSectionsRing X)) p

/-- A packaged exact comparison diagram of the shape used for principal completion. -/
structure PrincipalCompletionComparisonDiagram
    (g : globalSectionsRing X) (K : globalSectionsDerived X) (p : ℤ) where
  /-- The usual `g`-adic completion of `H^p(K)`. -/
  completedCohomology : ModuleCat.{u} (globalSectionsRing X)
  /-- The inverse limit `\varprojlim_n H^p(K_n)`. -/
  inverseLimitCohomology : ModuleCat.{u} (globalSectionsRing X)
  /-- The Tate module term `T_g(H^{p+1}(K))`. -/
  tateModule : ModuleCat.{u} (globalSectionsRing X)
  /-- The degree-zero cohomology of the derived completion of `H^p(K)`. -/
  derivedCompletionH0 : ModuleCat.{u} (globalSectionsRing X)
  /-- The degree-`p` cohomology of the completed derived object. -/
  completedDerivedCohomology : ModuleCat.{u} (globalSectionsRing X)
  /-- The `R^1 \!\varprojlim` term coming from the `g`-power torsion tower. -/
  torsionR1Lim : ModuleCat.{u} (globalSectionsRing X)
  /-- The `R^1 \!\varprojlim` term coming from the completion tower. -/
  towerR1Lim : ModuleCat.{u} (globalSectionsRing X)
  /-- The left map in the top short exact row. -/
  topRowLeft : completedCohomology ⟶ inverseLimitCohomology
  /-- The right map in the top short exact row. -/
  topRowRight : inverseLimitCohomology ⟶ tateModule
  /-- The left map in the middle short exact row. -/
  middleRowLeft : derivedCompletionH0 ⟶ completedDerivedCohomology
  /-- The right map in the middle short exact row. -/
  middleRowRight : completedDerivedCohomology ⟶ tateModule
  /-- The top map in the left short exact column. -/
  leftColumnTop : completedCohomology ⟶ derivedCompletionH0
  /-- The bottom map in the left short exact column. -/
  leftColumnBottom : derivedCompletionH0 ⟶ torsionR1Lim
  /-- The top map in the middle short exact column. -/
  middleColumnTop : inverseLimitCohomology ⟶ completedDerivedCohomology
  /-- The bottom map in the middle short exact column. -/
  middleColumnBottom : completedDerivedCohomology ⟶ towerR1Lim
  /-- The bottom horizontal comparison is an isomorphism of the two `R^1 \!\varprojlim` terms. -/
  bottomIso : torsionR1Lim ≅ towerR1Lim
  /-- The top row is a complex. -/
  topRowZero : topRowLeft ≫ topRowRight = 0
  /-- The middle row is a complex. -/
  middleRowZero : middleRowLeft ≫ middleRowRight = 0
  /-- The left column is a complex. -/
  leftColumnZero : leftColumnTop ≫ leftColumnBottom = 0
  /-- The middle column is a complex. -/
  middleColumnZero : middleColumnTop ≫ middleColumnBottom = 0
  /-- The top row is short exact. -/
  topRowShortExact : (ShortComplex.mk topRowLeft topRowRight topRowZero).ShortExact
  /-- The middle row is short exact. -/
  middleRowShortExact : (ShortComplex.mk middleRowLeft middleRowRight middleRowZero).ShortExact
  /-- The left column is short exact. -/
  leftColumnShortExact : (ShortComplex.mk leftColumnTop leftColumnBottom leftColumnZero).ShortExact
  /-- The middle column is short exact. -/
  middleColumnShortExact :
      (ShortComplex.mk middleColumnTop middleColumnBottom middleColumnZero).ShortExact
  /-- The upper-left square commutes. -/
  upperLeftComm : topRowLeft ≫ middleColumnTop = leftColumnTop ≫ middleRowLeft
  /-- The upper-right square commutes. -/
  upperRightComm : topRowRight = middleColumnTop ≫ middleRowRight
  /-- The lower-left square commutes after identifying the two bottom `R^1 \!\varprojlim` terms. -/
  lowerLeftComm : middleRowLeft ≫ middleColumnBottom = leftColumnBottom ≫ bottomIso.hom

/-- The inverse system
`n ↦ H^p(R\Gamma(X,\mathcal F / g^(n+1)\mathcal F))` attached to the quotient tower. -/
abbrev ringGlobalSectionPowerCokernelCohomologyTower
    (RGamma : sheafModulesDerived X ⥤ globalSectionsDerived X)
    (g : globalSectionsRing X) (F : Modules X) (p : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} (globalSectionsRing X) :=
  endomorphismPowerCokernelTower (ringGlobalSectionMul g F) ⋙ RGamma ⋙
    globalSectionsHomologyFunctor X p

/-- The inverse limit `\varprojlim_n H^p(X,\mathcal F / g^(n+1)\mathcal F)`. -/
abbrev ringGlobalSectionPowerCokernelCohomologyLimit
    (RGamma : sheafModulesDerived X ⥤ globalSectionsDerived X)
    (g : globalSectionsRing X) (F : Modules X) (p : ℤ) :
    ModuleCat.{u} (globalSectionsRing X) :=
  limit (ringGlobalSectionPowerCokernelCohomologyTower RGamma g F p)

/-- The standard Milnor cokernel model for
`R^1 \!\varprojlim_n H^p(X,\mathcal F / g^(n+1)\mathcal F)`. -/
abbrev ringGlobalSectionPowerCokernelCohomologyR1Lim
    (RGamma : sheafModulesDerived X ⥤ globalSectionsDerived X)
    (g : globalSectionsRing X) (F : Modules X) (p : ℤ) :
    ModuleCat.{u} (globalSectionsRing X) :=
  let T := ringGlobalSectionPowerCokernelCohomologyTower RGamma g F p
  cokernel <|
    Pi.lift fun n ↦
      Pi.π (fun k ↦ T.obj (op k)) n -
        Pi.π (fun k ↦ T.obj (op k)) (n + 1) ≫
          T.map ((homOfLE (Nat.le_succ n)).op)

-- Proof sketch: apply the principal completion comparison to the chosen derived global-sections
-- functor `RGamma` and to the object `\mathcal F[0]`. The stabilization hypothesis identifies the
-- completion tower with the quotient tower `(\mathcal F / g^(n+1)\mathcal F)_n`, so the upper
-- middle term and the lower `R^1 \!\varprojlim` term can be expressed using that quotient tower.
/-- Example 20.39.3: let `(X,\mathcal O_X)` be a ringed space, let `A → Γ(X,\mathcal O_X)` be a
ring map, let `f ∈ A`, and let `\mathcal F` be an `\mathcal O_X`-module. Assume there is `c`
such that `\mathcal F[f^c] = \mathcal F[f^n]` for all `n ≥ c`. Then for every `p : \mathbf Z`
there is a completion comparison diagram for `R\Gamma(X,\mathcal F)` whose upper-middle term
identifies with `\varprojlim_n H^p(X,\mathcal F / f^(n+1)\mathcal F)` and whose lower
`R^1 \!\varprojlim` term identifies with
`R^1 \!\varprojlim_n H^{p-1}(X,\mathcal F / f^(n+1)\mathcal F)`. The `n ↦ n + 1` indexing is the
standard project convention for the quotient tower. -/
theorem module_principalCompletion_has_quotient_comparison_diagram
    (RGamma : sheafModulesDerived X ⥤ globalSectionsDerived X)
    (α : A →+* globalSectionsRing X) (f : A) (F : Modules X)
    (hstable : endomorphismPowerKernelStabilizes (ringGlobalSectionMul (α f) F)) (p : ℤ) :
    ∃ D : PrincipalCompletionComparisonDiagram
        (α f) (RGamma.obj ((sheafModulesSingleZeroFunctor X).obj F)) p,
      Nonempty
        (D.inverseLimitCohomology ≅
          ringGlobalSectionPowerCokernelCohomologyLimit RGamma (α f) F p) ∧
      Nonempty
        (D.towerR1Lim ≅
          ringGlobalSectionPowerCokernelCohomologyR1Lim RGamma (α f) F (p - 1)) := sorry

end

end AlgebraicGeometry.RingedSpace
