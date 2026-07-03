import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Geometry.RingedSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_39_1 (from Chap20) -/
noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable {ΓX : Type u} [CommRing ΓX]
variable {A : Type u} [CommRing A]
variable {DSh : Type u} [Category DSh]

/-- A packaged commutative diagram with exact rows and columns of the shape appearing in the
completion comparison for derived global sections. The object parameters are the usual completion,
the inverse limit of the cohomology of the completion tower, the Tate module term, the degree-zero
cohomology of the derived completion of the cohomology module, the cohomology of the completed
derived global sections object, and the two `R^1 lim` terms. -/
structure PrincipalCompletionComparisonDiagram
    (f : ΓX) (K : DerivedCategory (ModuleCat ΓX)) (p : ℤ) where
  /-- The usual `f`-adic completion of `H^p(K)`. -/
  completedCohomology : ModuleCat.{u} ΓX
  /-- The inverse limit `lim_n H^p(K_n)`. -/
  inverseLimitCohomology : ModuleCat.{u} ΓX
  /-- The `f`-adic Tate module `T_f(H^{p + 1}(K))`. -/
  tateModule : ModuleCat.{u} ΓX
  /-- The degree-zero cohomology of the derived completion of `H^p(K)`. -/
  derivedCompletionH0 : ModuleCat.{u} ΓX
  /-- The degree-`p` cohomology of the completed derived object. -/
  completedDerivedCohomology : ModuleCat.{u} ΓX
  /-- The `R^1 lim` term coming from the `f`-power torsion tower of `H^p(K)`. -/
  torsionR1Lim : ModuleCat.{u} ΓX
  /-- The `R^1 lim` term coming from the completion tower `K_n`. -/
  towerR1Lim : ModuleCat.{u} ΓX
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
  /-- The bottom horizontal comparison is an isomorphism between the two `R^1 lim` terms. -/
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
  /-- The lower-left square commutes after identifying the two `R^1 lim` terms. -/
  lowerLeftComm : middleRowLeft ≫ middleColumnBottom = leftColumnBottom ≫ bottomIso.hom

-- Proof sketch: apply the principal completion comparison on the derived global-sections side to
-- `RΓ(X, E)` and to the image of `f` under `A → Γ(X, \mathcal O_X)`. This is the formal
-- translation of the Stacks Project argument reducing the sheaf statement to the algebraic
-- completion diagram for derived global sections.
/-- Lemma 20.39.1: let `(X, \mathcal O_X)` be a ringed space, let `A → Γ(X, \mathcal O_X)` be a
ring map, let `f ∈ A`, and let `E ∈ D(\mathcal O_X)`. Formalized on the derived-global-sections
side, for every `p : ℤ` there is a canonical commutative diagram with exact rows and columns whose
top row is
`0 → \widehat{H^p(X, E)} → \varprojlim_n H^p(X, E_n) → T_f(H^{p + 1}(X, E)) → 0`
and whose middle row is
`0 → H^0(H^p(X, E)^∧) → H^p(X, E^∧) → T_f(H^{p + 1}(X, E)) → 0`. -/
theorem derivedGlobalSections_principalCompletion_has_comparison_diagram
    (RGamma : DSh ⥤ DerivedCategory (ModuleCat ΓX))
    (α : A →+* ΓX) (f : A) (E : DSh) (p : ℤ) :
    Nonempty (PrincipalCompletionComparisonDiagram (α f) (RGamma.obj E) p) := sorry

-- Proof sketch: the hypothesis identifies the derived global sections of the completed object with
-- the chosen derived completion object. Applying degree-`p` homology yields the comparison of
-- cohomology modules.
/-- If the derived global sections of a completed object are identified with a chosen derived
completion object, then their degree-`p` cohomology modules are canonically isomorphic. -/
theorem derivedGlobalSections_completion_cohomology_iso
    (RGamma : DSh ⥤ DerivedCategory (ModuleCat ΓX))
    (EHat : DSh)
    (completedRGamma : DerivedCategory (ModuleCat ΓX)) (p : ℤ)
    (hEHat : IsIsomorphic (RGamma.obj EHat) completedRGamma) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (ModuleCat ΓX) p).obj (RGamma.obj EHat))
      ((DerivedCategory.homologyFunctor (ModuleCat ΓX) p).obj completedRGamma) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_39_2 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {M : 𝒜}

local notation "D𝒜" => DerivedCategory 𝒜
local notation "single0" => DerivedCategory.singleFunctor 𝒜 (0 : ℤ)
local notation "singleComplex0" => CochainComplex.singleFunctor 𝒜 (0 : ℤ)

/- Domain-style sampling for Lemma 20.39.2:
- primary domain: sequential pro-object comparisons in `D(𝒜)` between the cokernel tower of the
  powers of an endomorphism and the corresponding two-term mapping-cone tower;
- sampled owner declarations:
  `SequentialProObjectMorphismRep`,
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `Functor.ofOpSequence`,
  `exists_pro_isomorphism_derived_completion_koszul_powers_to_power_quotients`;
- best owner abstraction: the source-facing towers should remain explicit sequential inverse
  systems, while the pro-comparison itself should live directly in
  `SequentialProObjectMorphismRep ...` together with its owner morphism `r.toProObjectHom`;
- primitive data: the stage objects `cokernel (f ^ (n + 1))` and
  `mappingCone ((singleComplex0).map (f ^ (n + 1)))`, their transition morphisms, and the
  stabilization predicate on the kernel subobjects of the powers of `f`;
- derived API: the existence of a shift-by-`c` representative whose induced morphism in the
  sequential pro-category is an isomorphism.

Source/core/bridge triage:
- `source-facing`: `endomorphismPowerCokernelTower`, `endomorphismPowerTwoTermTower`, and
  `endomorphismPowerKernelStabilizes`;
- `core/canonical`: `SequentialProObjectMorphismRep ...` and `.toProObjectHom`;
- `bridge/view`: the explicit stagewise cokernel and mapping-cone models used to assemble the
  sequential towers. -/

/-- The degree-zero derived object represented by `\operatorname{Coker}(f^(n+1))`. -/
abbrev endomorphismPowerCokernelStage (f : End M) (n : ℕ) : D𝒜 :=
  (single0).obj (cokernel (f ^ (n + 1) : M ⟶ M))

/-- The two-term cochain complex `M \xrightarrow{f^(n+1)} M`, modeled as the mapping cone of
`f^(n+1)` placed in degree `0`. -/
abbrev endomorphismPowerTwoTermComplex (f : End M) (n : ℕ) : CochainComplex 𝒜 ℤ :=
  CochainComplex.mappingCone ((singleComplex0).map (f ^ (n + 1) : M ⟶ M))

/-- The derived object represented by the two-term complex `M \xrightarrow{f^(n+1)} M`. -/
abbrev endomorphismPowerTwoTermStage (f : End M) (n : ℕ) : D𝒜 :=
  DerivedCategory.Q.obj (endomorphismPowerTwoTermComplex f n)

-- Proof sketch: `f^(n + 2)` factors through `f^(n + 1)`, so the cokernel projection of
-- `f^(n + 1)` annihilates `f^(n + 2)`.
/-- The defining factorization condition for the transition map
`coker(f^(n+2)) ⟶ coker(f^(n+1))`. -/
theorem endomorphismPowerCokernelTransition_condition (f : End M) (n : ℕ) :
    (f ^ (n + 2) : M ⟶ M) ≫ cokernel.π (f ^ (n + 1) : M ⟶ M) = 0 := sorry

/-- The transition morphism `coker(f^(n+2)) ⟶ coker(f^(n+1))` in the cokernel tower. -/
abbrev endomorphismPowerCokernelTransition (f : End M) (n : ℕ) :
    endomorphismPowerCokernelStage f (n + 1) ⟶ endomorphismPowerCokernelStage f n :=
  (single0).map <|
    cokernel.desc (f ^ (n + 2) : M ⟶ M) (cokernel.π (f ^ (n + 1) : M ⟶ M))
      (endomorphismPowerCokernelTransition_condition f n)

-- Proof sketch: the square defining the transition between the two-term complexes commutes
-- because `f^(n + 2) = f ≫ f^(n + 1)` as endomorphisms of `M`.
/-- The commutative square used to define the transition
`(M \xrightarrow{f^(n+2)} M) ⟶ (M \xrightarrow{f^(n+1)} M)`. -/
theorem endomorphismPowerTwoTermTransition_comm (f : End M) (n : ℕ) :
    CommSq
      ((singleComplex0).map (f ^ (n + 2) : M ⟶ M))
      ((singleComplex0).map (f : M ⟶ M))
      (𝟙 ((singleComplex0).obj M))
      ((singleComplex0).map (f ^ (n + 1) : M ⟶ M)) := sorry

/-- The transition morphism
`(M \xrightarrow{f^(n+2)} M) ⟶ (M \xrightarrow{f^(n+1)} M)` in the two-term tower. -/
abbrev endomorphismPowerTwoTermTransition (f : End M) (n : ℕ) :
    endomorphismPowerTwoTermStage f (n + 1) ⟶ endomorphismPowerTwoTermStage f n :=
  DerivedCategory.Q.map <|
    CochainComplex.mappingCone.map
      ((singleComplex0).map (f ^ (n + 2) : M ⟶ M))
      ((singleComplex0).map (f ^ (n + 1) : M ⟶ M))
      ((singleComplex0).map (f : M ⟶ M))
      (𝟙 ((singleComplex0).obj M))
      (endomorphismPowerTwoTermTransition_comm f n).w

/-- The inverse system whose `n`th stage is `\operatorname{Coker}(f^(n+1))` in
`D(\mathcal A)`. -/
abbrev endomorphismPowerCokernelTower (f : End M) : ℕᵒᵖ ⥤ D𝒜 :=
  Functor.ofOpSequence (endomorphismPowerCokernelTransition f)

/-- The inverse system whose `n`th stage is the two-term complex
`M \xrightarrow{f^(n+1)} M` in `D(\mathcal A)`. -/
abbrev endomorphismPowerTwoTermTower (f : End M) : ℕᵒᵖ ⥤ D𝒜 :=
  Functor.ofOpSequence (endomorphismPowerTwoTermTransition f)

/-- The stabilization condition `\ker(f^c) = \ker(f^n)` for all `n ≥ c`, expressed as eventual
constancy of the kernel subobjects of the powers of `f`. -/
def endomorphismPowerKernelStabilizes (f : End M) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, c ≤ n →
    kernelSubobject (f ^ n : M ⟶ M) = kernelSubobject (f ^ c : M ⟶ M)

-- Proof sketch: choose a stage `c` from which the kernels of the powers of `f` stabilize. The
-- evident map from the two-term tower to the cokernel tower has identity reindexing. In the
-- opposite direction, use the quotient `M / \ker(f^c)` and the diagrams
-- `M / \ker(f^c) \xrightarrow{f^(n+c+1)} M` mapping down to `M \xrightarrow{f^(n+1)} M`; once
-- the kernels stabilize, the top horizontal map is monic and the resulting two-term complex is
-- quasi-isomorphic to `\operatorname{Coker}(f^(n+c+1))`, giving a shift-by-`c` inverse system
-- map which is inverse up to common refinement.
/-- Lemma 20.39.2: let `\mathcal A` be an abelian category, let `f : M ⟶ M` be an endomorphism,
and suppose the kernels `\ker(f^n)` stabilize. Then the inverse systems
`(M \xrightarrow{f^(n+1)} M)_n` and `(\operatorname{Coker}(f^(n+1)))_n` are pro-isomorphic in
`D(\mathcal A)`. In the project's canonical sequential pro-object API this is recorded by a
shifted representative whose induced pro-object morphism is an isomorphism, using the standard
chapter convention that stage `n` corresponds to the exponent `n + 1`. -/
theorem exists_cokernel_to_endomorphismPowerTwoTerm_shiftedProIsomorphism
    (f : End M)
    (hstable : endomorphismPowerKernelStabilizes f) :
    ∃ c : ℕ,
      ∃ r :
        SequentialProObjectMorphismRep
          (endomorphismPowerCokernelTower f)
          (endomorphismPowerTwoTermTower f),
        (∀ n : ℕ, r.reindex n = n + c) ∧ IsIso r.toProObjectHom := sorry

end

end CategoryTheory

/-! ### Example_20_39_3 (from Chap20) -/
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
