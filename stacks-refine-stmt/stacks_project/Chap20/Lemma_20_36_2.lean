import Mathlib
import stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The underlying `RingCat`-valued presheaf of the structure sheaf of a ringed space. -/
private abbrev structureSheafPresheaf (X : RingedSpace.{u}) :=
  (RingedSpace.ringCatSheaf X).obj

/-- The top open subset of a ringed space. -/
abbrev topOpen (X : RingedSpace.{u}) : Opens X.carrier :=
  ⟨Set.univ, isOpen_univ⟩

/-- The restriction of a global section `f ∈ Γ(X, \mathcal O_X)` to an open subset `U`. -/
abbrev ringGlobalSectionRestrict {X : RingedSpace.{u}} (f : globalSectionsRing X)
    (U : Opens X.carrier) :
    (structureSheafPresheaf X).obj (op U) :=
  (((structureSheafPresheaf X).map
      (homOfLE (show U ≤ topOpen X from by intro x hx; trivial)).op).hom f :
    (structureSheafPresheaf X).obj (op U))

/-- The objectwise action of a global section `f` on the sections of an `\mathcal O_X`-module. -/
abbrev ringGlobalSectionMulAppFun {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : (RingedSpace.Modules X)) (U : (Opens X.carrier)ᵒᵖ) :
    ℱ.val.obj U → ℱ.val.obj U :=
  fun s ↦
    let r : (structureSheafPresheaf X).obj U := ringGlobalSectionRestrict f (unop U)
    let s' : ℱ.val.obj U := s
    show ℱ.val.obj U from r • s'

-- Proof sketch: after evaluating on `U`, this is ordinary distributivity of scalar
-- multiplication by the restricted section `f|_U`.
/-- Multiplication by a global section preserves addition on every open set. -/
theorem ringGlobalSectionMulAppFun_map_add {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : (RingedSpace.Modules X)) (U : (Opens X.carrier)ᵒᵖ)
    (s t : ℱ.val.obj U) :
    ringGlobalSectionMulAppFun f ℱ U (s + t) =
      ringGlobalSectionMulAppFun f ℱ U s + ringGlobalSectionMulAppFun f ℱ U t := sorry

-- Proof sketch: the section ring on `U` acts linearly on `ℱ(U)`, so multiplication by `f|_U`
-- commutes with scalar multiplication.
/-- Multiplication by a global section is linear over the ring of sections on every open set. -/
theorem ringGlobalSectionMulAppFun_map_smul {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : (RingedSpace.Modules X)) (U : (Opens X.carrier)ᵒᵖ)
    (a : (structureSheafPresheaf X).obj U) (s : ℱ.val.obj U) :
    ringGlobalSectionMulAppFun f ℱ U (a • s) =
      a • ringGlobalSectionMulAppFun f ℱ U s := sorry

/-- Multiplication by `f` as an endomorphism of the module of sections over `U`. -/
abbrev ringGlobalSectionMulApp {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : (RingedSpace.Modules X)) (U : (Opens X.carrier)ᵒᵖ) :
    ℱ.val.obj U ⟶ ℱ.val.obj U :=
  let M : ModuleCat ((structureSheafPresheaf X).obj U) := ℱ.val.obj U
  let linearMap : M →ₗ[(structureSheafPresheaf X).obj U] M :=
    { toFun := ringGlobalSectionMulAppFun f ℱ U
      map_add' := ringGlobalSectionMulAppFun_map_add f ℱ U
      map_smul' := ringGlobalSectionMulAppFun_map_smul f ℱ U }
  show M ⟶ M from (ModuleCat.homEquiv).symm linearMap

-- Proof sketch: the restriction maps of `ℱ` are linear over the structure-sheaf restriction
-- maps, so multiplication by `f` commutes with restriction.
/-- Multiplication by a global section is natural with respect to restriction maps. -/
theorem ringGlobalSectionMul_naturality {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : (RingedSpace.Modules X)) {U V : (Opens X.carrier)ᵒᵖ}
    (i : U ⟶ V) :
    ℱ.val.map i ≫
      (ModuleCat.restrictScalars (((structureSheafPresheaf X).map i).hom)).map
        (ringGlobalSectionMulApp f ℱ V) =
    ringGlobalSectionMulApp f ℱ U ≫ ℱ.val.map i := sorry

/-- Multiplication by `f` as an endomorphism of an `\mathcal O_X`-module. -/
abbrev ringGlobalSectionMul {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : (RingedSpace.Modules X)) : ℱ ⟶ ℱ where
  val.app U := ringGlobalSectionMulApp f ℱ U
  val.naturality i := ringGlobalSectionMul_naturality f ℱ i

/-- The transition morphism `\mathcal F_{n + 1} \to \mathcal F_n` in a sequential inverse system
of `\mathcal O_X`-modules. -/
abbrev inverseSystemStep {X : RingedSpace.{u}}
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) (n : ℕ) :
    ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op n) :=
  ℱ.map (homOfLE (Nat.le_succ n)).op

/-- The comparison morphism `\mathcal F_n \to \mathcal F_1` for a stage `n ≥ 1` of a sequential
inverse system of `\mathcal O_X`-modules. -/
abbrev inverseSystemToFirst {X : RingedSpace.{u}}
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) (n : ℕ) (hn : 1 ≤ n) :
    ℱ.obj (op n) ⟶ ℱ.obj (op 1) :=
  ℱ.map (homOfLE hn).op

/-- Condition `(1)` of Lemma `20.36.1` for a tower of `\mathcal O_X`-modules and a global
section `f ∈ Γ(X, \mathcal O_X)`. -/
def ringStepShortExactCondition {X : RingedSpace.{u}}
    (f : globalSectionsRing X) (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π := inverseSystemToFirst ℱ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    ∃ (ι : ℱ.obj (op n) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        inverseSystemStep ℱ n ≫ ι = ringGlobalSectionMul f (ℱ.obj (op (n + 1)))

/-- The degree-`p` global cohomology functor on `\mathcal O_X`-modules, valued in modules over
`Γ(X, \mathcal O_X)`. -/
abbrev moduleGlobalCohomologyFunctor (X : RingedSpace.{u}) (p : ℤ) :
    (RingedSpace.Modules X) ⥤ ModuleCat (globalSectionsRing X) :=
  DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ) ⋙
    moduleDerivedGlobalSections X ⋙
      DerivedCategory.homologyFunctor (ModuleCat (globalSectionsRing X)) p

/-- The degree-`p` global cohomology module `H^p(X, \mathcal F)` of an `\mathcal O_X`-module. -/
abbrev moduleGlobalCohomology (X : RingedSpace.{u}) (p : ℤ) (ℱ : (RingedSpace.Modules X)) :
    ModuleCat (globalSectionsRing X) :=
  (moduleGlobalCohomologyFunctor X p).obj ℱ

/-- The inverse system `n ↦ H^p(X, \mathcal F_n)` attached to a tower of `\mathcal O_X`-modules.
-/
abbrev moduleGlobalCohomologyTower {X : RingedSpace.{u}} (p : ℤ)
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) :
    ℕᵒᵖ ⥤ ModuleCat (globalSectionsRing X) :=
  ℱ ⋙ moduleGlobalCohomologyFunctor X p

/-- The inverse limit `\varprojlim_n H^p(X, \mathcal F_n)` of the cohomology tower. -/
abbrev moduleGlobalCohomologyLimit {X : RingedSpace.{u}} (p : ℤ)
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) :
    ModuleCat (globalSectionsRing X) :=
  limit (moduleGlobalCohomologyTower p ℱ)

/-- The limit topology on `\varprojlim_n H^p(X, \mathcal F_n)` induced from the discrete stage
cohomology modules. -/
abbrev moduleGlobalCohomologyLimitTopology {X : RingedSpace.{u}} (p : ℤ)
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) :
    TopologicalSpace ↥(moduleGlobalCohomologyLimit p ℱ) :=
  let _ : (n : ℕ) → TopologicalSpace ↥((moduleGlobalCohomologyTower p ℱ).obj (op n)) :=
    fun _ ↦ ⊥
  TopologicalSpace.induced
    (fun x : ↥(moduleGlobalCohomologyLimit p ℱ) ↦
      fun n : ℕ ↦
        (((limit.π (moduleGlobalCohomologyTower p ℱ) (op n)).hom x) :
          (moduleGlobalCohomologyTower p ℱ).obj (op n)))
    inferInstance

section

variable {X : RingedSpace.{u}}

-- Proof sketch: for fixed `c ≥ 1`, the stepwise short exact sequences from
-- `ringStepShortExactCondition f ℱ` iterate to short exact sequences
-- `0 → \mathcal F_{n-c} \xrightarrow{f^c} \mathcal F_n → \mathcal F_c → 0` for `n ≥ c`.
-- Passing to the corresponding long exact cohomology sequences and then to the inverse limit
-- identifies the kernel of `H^p → H^p(X,\mathcal F_c)` with the image of multiplication by `f^c`.
/-- Lemma 20.36.2 (1): if the tower `(\mathcal F_n)` satisfies condition `(1)` of
Lemma `20.36.1` and `H^p = \varprojlim_n H^p(X, \mathcal F_n)`, then for every `c ≥ 1` the
submodule `f^c H^p` is the kernel of the projection `H^p → H^p(X, \mathcal F_c)`. In this
formalization `f^c H^p` is represented by the action of the `c`th power of the principal ideal
generated by `f`. -/
theorem cohomologyLimit_pow_eq_kernel_projection
    (f : globalSectionsRing X)
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X))
    (hℱ : ringStepShortExactCondition f ℱ)
    (p : ℕ) (c : ℕ) (hc : 1 ≤ c) :
    (Ideal.span ({f} : Set (globalSectionsRing X)) ^ c) •
        (⊤ : Submodule (globalSectionsRing X) (moduleGlobalCohomologyLimit (p : ℤ) ℱ)) =
      LinearMap.ker
        ((limit.π (moduleGlobalCohomologyTower (p : ℤ) ℱ) (op c)).hom) := sorry

-- Proof sketch: by part `(1)`, the neighborhoods of `0` in the inverse-limit topology are exactly
-- the kernels of the projections to `H^p(X,\mathcal F_c)`, hence exactly the powers of the
-- principal ideal generated by `f`. This matches the defining neighborhood basis of the
-- `f`-adic topology.
/-- Lemma 20.36.2 (2): under the same hypotheses, the limit topology on
`H^p = \varprojlim_n H^p(X, \mathcal F_n)` is the `f`-adic topology. -/
theorem cohomologyLimitTopology_eq_adic_of_stepShortExactCondition
    (f : globalSectionsRing X)
    (ℱ : ℕᵒᵖ ⥤ (RingedSpace.Modules X))
    (hℱ : ringStepShortExactCondition f ℱ)
    (p : ℕ) :
    moduleGlobalCohomologyLimitTopology (p : ℤ) ℱ =
      Ideal.adicModuleTopology
        (Ideal.span ({f} : Set (globalSectionsRing X)))
        ↥(moduleGlobalCohomologyLimit (p : ℤ) ℱ) := sorry

end

end AlgebraicGeometry.RingedSpace
