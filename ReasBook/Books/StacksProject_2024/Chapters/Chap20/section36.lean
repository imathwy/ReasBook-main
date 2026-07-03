import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_36_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "ModX" => SheafOfModules.{u} (RingedSpace.ringCatSheaf X)
local notation "TowerX" => ℕᵒᵖ ⥤ ModX

/-- An `\mathcal O_X`-module is `f`-divisible if multiplication by `f` is an epimorphism. -/
def IsDivisibleByGlobalSection
    (f : StructureSheafGlobalSection X) (ℱ : ModX) : Prop :=
  Epi (globalSectionMul f ℱ)

/-- The transition morphism `\mathcal F_{n + 1} \to \mathcal F_n` in a sequential inverse system
of `\mathcal O_X`-modules. -/
abbrev inverseSystemStep
    (ℱ : TowerX) (n : ℕ) :
    ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op n) :=
  ℱ.map (homOfLE (Nat.le_succ n)).op

/-- The comparison morphism `\mathcal F_n \to \mathcal F_1` for a stage `n ≥ 1` of a sequential
inverse system of `\mathcal O_X`-modules. -/
abbrev inverseSystemToFirst
    (ℱ : TowerX) (n : ℕ) (hn : 1 ≤ n) :
    ℱ.obj (op n) ⟶ ℱ.obj (op 1) :=
  ℱ.map (homOfLE hn).op

/-- Condition (1) from Lemma 20.36.1: for every `n ≥ 1`, multiplication by `f` on
`\mathcal F_{n + 1}` factors through `\mathcal F_{n + 1} \to \mathcal F_n` and gives a short
exact sequence `0 → \mathcal F_n → \mathcal F_{n + 1} → \mathcal F_1 → 0`. -/
def stepShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π := inverseSystemToFirst ℱ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    let σ := inverseSystemStep ℱ n
    ∃ (ι : ℱ.obj (op n) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        σ ≫ ι = globalSectionMul f (ℱ.obj (op (n + 1)))

/-- Condition (2) from Lemma 20.36.1: for every `n ≥ 1`, multiplication by `f^n` on
`\mathcal F_{n + 1}` factors through `\mathcal F_{n + 1} \to \mathcal F_1` and gives a short
exact sequence `0 → \mathcal F_1 → \mathcal F_{n + 1} → \mathcal F_n → 0`. -/
def powerShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π := inverseSystemStep ℱ n
    let σ := inverseSystemToFirst ℱ (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    ∃ (ι : ℱ.obj (op 1) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        σ ≫ ι =
          globalSectionMulPow f (ℱ.obj (op (n + 1))) n

/-- Condition (3) from Lemma 20.36.1: the inverse system is obtained from the kernels
`\mathcal G[f^n]` of powers of multiplication by `f` on an `f`-divisible module `\mathcal G`. -/
def divisibleKernelTowerCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) : Prop :=
  ∃ 𝒢 : ModX,
    IsDivisibleByGlobalSection f 𝒢 ∧
      ∀ n : ℕ, ∀ _ : 1 ≤ n,
        Nonempty (ℱ.obj (op n) ≅ kernel (globalSectionMulPow f 𝒢 n))

-- Proof sketch: starting from an `f`-torsion free module `\mathcal F`, apply the standard short
-- exact sequences `0 → \mathcal F/f\mathcal F → \mathcal F/f^{n + 1}\mathcal F →
-- \mathcal F/f^n\mathcal F → 0`, pass to the colimit model of the quotient tower, and identify
-- the resulting divisible module whose `f^n`-torsion recovers the original stages.
/-- Lemma 20.36.1 (1): if the inverse system is given by quotients
`\mathcal F / f^n \mathcal F` of an `f`-torsion free module, then it is also given by the kernels
`\mathcal G[f^n]` inside an `f`-divisible module `\mathcal G`. -/
theorem torsionFreeQuotientTowerCondition_implies_divisibleKernelTowerCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) :
    torsionFreeQuotientTowerCondition f ℱ →
      divisibleKernelTowerCondition f ℱ := sorry

-- Proof sketch: for `3 → 2`, use the inclusions `\mathcal G[f] \subset \mathcal G[f^{n + 1}]`
-- inside an `f`-divisible module and identify the quotient with `\mathcal G[f^n]`; for `2 → 3`,
-- form the filtered colimit of the tower and show that multiplication by `f` on the colimit is
-- surjective, with kernels equal to the prescribed stages.
/-- Lemma 20.36.1 (2): the inverse system comes from the kernels `\mathcal G[f^n]` of an
`f`-divisible module if and only if the powers `f^n` factor through
`\mathcal F_{n + 1} \to \mathcal F_1` to yield short exact sequences
`0 → \mathcal F_1 → \mathcal F_{n + 1} → \mathcal F_n → 0`. -/
theorem divisibleKernelTowerCondition_iff_powerShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) :
    divisibleKernelTowerCondition f ℱ ↔
      powerShortExactCondition f ℱ := sorry

-- Proof sketch: in one direction, compose the factorization through `\mathcal F_{n + 1} →
-- \mathcal F_1` with the standard exact sequence from condition (2) to recover the factorization
-- through `\mathcal F_{n + 1} → \mathcal F_n`; in the other direction, iterate the stepwise
-- factorization from condition (1) to identify the factorization of `f^n`.
/-- Lemma 20.36.1 (3): the power-factorization short exact sequences from condition (2) are
equivalent to the stepwise factorization short exact sequences from condition (1). -/
theorem powerShortExactCondition_iff_stepShortExactCondition
    (f : StructureSheafGlobalSection X) (ℱ : TowerX) :
    powerShortExactCondition f ℱ ↔
      stepShortExactCondition f ℱ := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_36_2 (from Chap20) -/
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

/-! ### Lemma_20_36_3 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- Scalar multiplication by `f` on the sections of a sheaf of `A`-modules over an open set. -/
abbrev topologicalSpaceModuleScalarMulAppFun
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) :
    ℱ.obj.obj U → ℱ.obj.obj U :=
  fun s ↦ f • s

-- Proof sketch: on each open set this is ordinary distributivity of scalar multiplication by `f`
-- in the `A`-module of sections.
/-- Scalar multiplication by `f` preserves addition on every open set. -/
theorem topologicalSpaceModuleScalarMulAppFun_map_add
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) (s t : ℱ.obj.obj U) :
    topologicalSpaceModuleScalarMulAppFun f ℱ U (s + t) =
      topologicalSpaceModuleScalarMulAppFun f ℱ U s +
        topologicalSpaceModuleScalarMulAppFun f ℱ U t := sorry

-- Proof sketch: because `A` is commutative, multiplication by the fixed scalar `f` is
-- `A`-linear on every module of sections `ℱ(U)`.
/-- Scalar multiplication by `f` is `A`-linear on the sections over every open set. -/
theorem topologicalSpaceModuleScalarMulAppFun_map_smul
    (f a : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) (s : ℱ.obj.obj U) :
    topologicalSpaceModuleScalarMulAppFun f ℱ U (a • s) =
      a • topologicalSpaceModuleScalarMulAppFun f ℱ U s := sorry

/-- Scalar multiplication by `f` as an endomorphism of the module of sections over an open set. -/
abbrev topologicalSpaceModuleScalarMulApp
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) :
    ℱ.obj.obj U ⟶ ℱ.obj.obj U :=
  let M : ModuleCat A := ℱ.obj.obj U
  let linearMap : M →ₗ[A] M :=
    { toFun := topologicalSpaceModuleScalarMulAppFun f ℱ U
      map_add' := fun s t ↦ topologicalSpaceModuleScalarMulAppFun_map_add f ℱ U s t
      map_smul' := fun a s ↦ topologicalSpaceModuleScalarMulAppFun_map_smul f a ℱ U s }
  show M ⟶ M from (ModuleCat.homEquiv).symm linearMap

-- Proof sketch: the restriction maps of a sheaf of `A`-modules are `A`-linear, hence they
-- commute with multiplication by the fixed scalar `f`.
/-- Scalar multiplication by `f` is natural with respect to restriction maps. -/
theorem topologicalSpaceModuleScalarMul_naturality
    (f : A) (ℱ : ModSheaf) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ℱ.obj.map i ≫ topologicalSpaceModuleScalarMulApp f ℱ V =
      topologicalSpaceModuleScalarMulApp f ℱ U ≫ ℱ.obj.map i := sorry

/-- Multiplication by `f` as an endomorphism of a sheaf of `A`-modules. -/
abbrev topologicalSpaceModuleScalarMul
    (f : A) (ℱ : ModSheaf) : ℱ ⟶ ℱ where
  hom.app U := topologicalSpaceModuleScalarMulApp f ℱ U
  hom.naturality := fun {_ _} i ↦ topologicalSpaceModuleScalarMul_naturality f ℱ i

/-- The transition morphism `\mathcal F_{n + 1} \to \mathcal F_n` in a sequential inverse system
of sheaves of `A`-modules. -/
abbrev topologicalSpaceModuleInverseSystemStep
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (n : ℕ) :
    ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op n) :=
  ℱ.map (homOfLE (Nat.le_succ n)).op

/-- The comparison morphism `\mathcal F_n \to \mathcal F_1` for a stage `n ≥ 1` of a sequential
inverse system of sheaves of `A`-modules. -/
abbrev topologicalSpaceModuleInverseSystemToFirst
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (n : ℕ) (hn : 1 ≤ n) :
    ℱ.obj (op n) ⟶ ℱ.obj (op 1) :=
  ℱ.map (homOfLE hn).op

/-- Condition `(1)` of Lemma `20.36.1` for a sequential inverse system of sheaves of `A`-modules
with respect to the scalar `f : A`. -/
def topologicalSpaceModuleStepShortExactCondition
    (f : A) (ℱ : ℕᵒᵖ ⥤ ModSheaf) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π :=
      topologicalSpaceModuleInverseSystemToFirst ℱ (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n))
    ∃ (ι : ℱ.obj (op n) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        topologicalSpaceModuleInverseSystemStep ℱ n ≫ ι =
          topologicalSpaceModuleScalarMul f (ℱ.obj (op (n + 1)))

/-- Global sections of sheaves of `A`-modules on `X`. -/
abbrev topologicalSpaceModuleGlobalSectionsFunctor : ModSheaf ⥤ ModuleCat A :=
  Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat A)

/-- The inverse system `n ↦ Γ(X, \mathcal F_n)` attached to a sequential inverse system of sheaves
of `A`-modules on `X`. -/
abbrev topologicalSpaceModuleGlobalSectionsTower
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) : ℕᵒᵖ ⥤ ModuleCat A :=
  ℱ ⋙ topologicalSpaceModuleGlobalSectionsFunctor

/-- The inverse limit `M = \varprojlim_n Γ(X, \mathcal F_n)`. -/
abbrev topologicalSpaceModuleGlobalSectionsLimit
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) : ModuleCat A :=
  limit (topologicalSpaceModuleGlobalSectionsTower ℱ)

-- Proof sketch: the stepwise short exact condition identifies the kernel of the projection
-- `M → Γ(X,\mathcal F_1)` with `fM`, so `M / fM` is a subquotient of `Γ(X,\mathcal F_1)`. Since
-- `A` is Noetherian and `Γ(X,\mathcal F_1)` is finite, the quotient `M / fM` is finite. The
-- completion hypothesis and Lemma `10.96.12` then promote finite generation of `M / fM` to finite
-- generation of the complete separated module `M`.
/-- Lemma 20.36.3 (1): if `A` is Noetherian and complete with respect to the principal ideal
`(f)`, if `Γ(X, \mathcal F_1)` is a finite `A`-module, and if the inverse system
`(\mathcal F_n)_n` satisfies condition `(1)` of Lemma `20.36.1`, then
`M = \varprojlim_n Γ(X, \mathcal F_n)` is a finite `A`-module. -/
theorem topologicalSpaceModuleGlobalSectionsLimit_finite_of_stepShortExactCondition
    (f : A) (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    [IsNoetherianRing A]
    [IsAdicComplete (Ideal.span ({f} : Set A)) A]
    (hΓ₁finite :
      Module.Finite A (topologicalSpaceModuleGlobalSectionsFunctor.obj (ℱ.obj (op 1))))
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) :
    Module.Finite A (topologicalSpaceModuleGlobalSectionsLimit ℱ) := sorry

-- Proof sketch: if `s = (s_n)` lies in the inverse limit and `f • s = 0`, then condition `(1)`
-- shows that each `s_{n + 1}` maps to zero in `\mathcal F_n`, hence already vanishes in the tower.
-- Therefore every component of `s` is zero, so multiplication by `f` on `M` is injective.
/-- Lemma 20.36.3 (2): under condition `(1)` of Lemma `20.36.1`, multiplication by `f` on
`M = \varprojlim_n Γ(X, \mathcal F_n)` is injective; equivalently, `f` is a nonzerodivisor on
`M`. -/
theorem topologicalSpaceModuleGlobalSectionsLimit_isSMulRegular_of_stepShortExactCondition
    (f : A) (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) :
    IsSMulRegular (topologicalSpaceModuleGlobalSectionsLimit ℱ) f := sorry

-- Proof sketch: apply condition `(1)` to the tower of global sections. The kernel of the
-- projection `M → Γ(X,\mathcal F_1)` is exactly the principal submodule `fM`; the textbook
-- identification `M / fM = \operatorname{Im}(M → Γ(X,\mathcal F_1))` then follows from the first
-- isomorphism theorem.
/-- Lemma 20.36.3 (3): under condition `(1)` of Lemma `20.36.1`, the kernel of the projection
`M = \varprojlim_n Γ(X, \mathcal F_n) → Γ(X, \mathcal F_1)` is exactly `fM`. Equivalently,
`M / fM` identifies with the image of `M` in `Γ(X, \mathcal F_1)`. -/
theorem topologicalSpaceModuleGlobalSectionsLimit_projection_ker_eq_principalSubmodule_of_stepShortExactCondition
    (f : A) (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) :
    LinearMap.ker ((limit.π (topologicalSpaceModuleGlobalSectionsTower ℱ) (op 1)).hom) =
      ((Ideal.span ({f} : Set A)) •
        (⊤ : Submodule A (topologicalSpaceModuleGlobalSectionsLimit ℱ))) := sorry

end

end CategoryTheory

/-! ### Lemma_20_36_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.SequentialInverseSystem

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The inverse system `n ↦ H^p(X, \mathcal F_n)` attached to a sequential inverse system of
`\mathcal O_X`-modules. -/
abbrev moduleCohomologyTower
    (X : RingedSpace.{u}) [HasInjectiveResolutions (SheafOfModules (RingedSpace.ringCatSheaf X))]
    (ℱ : ℕᵒᵖ ⥤ SheafOfModules (RingedSpace.ringCatSheaf X)) (p : ℕ) :
    SequentialInverseSystem (ModuleCat (globalSectionsRing X)) :=
  ℱ ⋙ (moduleGlobalSectionsFunctor X).rightDerived p

-- Proof sketch: use the short exact sequences from `stepShortExactCondition` to identify the
-- cohomology tower with the middle term in the standard short exact sequence relating the
-- principal-power quotient tower of `H^p(X, \mathcal F_1)` and the principal-power torsion tower
-- of `H^{p + 1}(X, \mathcal F_1)`. Finite length or finite generation over the Noetherian ring
-- `Γ(X, \mathcal O_X)` gives the required Mittag-Leffler control on the torsion tower, and then
-- Remark `15.94.7` transfers it to the cohomology tower.
/-- Lemma 20.36.4: if the inverse system `(\mathcal F_n)_n` of `\mathcal O_X`-modules satisfies
condition `(1)` of Lemma `20.36.1` with respect to a global section `f`, and if
`H^{p + 1}(X, \mathcal F_1)` is either of finite length over `Γ(X, \mathcal O_X)` or finite over
the Noetherian ring `Γ(X, \mathcal O_X)`, then the inverse system
`n ↦ H^p(X, \mathcal F_n)` is Mittag-Leffler. -/
theorem moduleCohomologyTower_isMittagLeffler_of_stepShortExactCondition_of_finiteLength_or_finite
    (f : StructureSheafGlobalSection X)
    (ℱ : ℕᵒᵖ ⥤ SheafOfModules (RingedSpace.ringCatSheaf X))
    (p : ℕ)
    [HasInjectiveResolutions (SheafOfModules (RingedSpace.ringCatSheaf X))]
    (hstep : stepShortExactCondition f ℱ)
    (hHp1 :
      IsFiniteLength (globalSectionsRing X)
          (moduleCohomology X (p + 1) (ℱ.obj (op 1))) ∨
        (IsNoetherianRing (globalSectionsRing X) ∧
          Module.Finite (globalSectionsRing X)
            (moduleCohomology X (p + 1) (ℱ.obj (op 1))))) :
    IsMittagLeffler (moduleCohomologyTower X ℱ p) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_36_5 (from Chap20) -/
open CategoryTheory
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- Scalar multiplication by `f` on the sections of a sheaf of `A`-modules over an open set. -/
abbrev topologicalSpaceModuleScalarMulAppFun
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) :
    ℱ.obj.obj U → ℱ.obj.obj U :=
  fun s ↦ f • s

-- Proof sketch: on each open set this is ordinary distributivity of scalar multiplication by `f`
-- in the `A`-module of sections.
/-- Scalar multiplication by `f` preserves addition on every open set. -/
theorem topologicalSpaceModuleScalarMulAppFun_map_add
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) (s t : ℱ.obj.obj U) :
    topologicalSpaceModuleScalarMulAppFun f ℱ U (s + t) =
      topologicalSpaceModuleScalarMulAppFun f ℱ U s +
        topologicalSpaceModuleScalarMulAppFun f ℱ U t := sorry

-- Proof sketch: because `A` is commutative, multiplication by the fixed scalar `f` is
-- `A`-linear on every module of sections `ℱ(U)`.
/-- Scalar multiplication by `f` is `A`-linear on the sections over every open set. -/
theorem topologicalSpaceModuleScalarMulAppFun_map_smul
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) (a : A) (s : ℱ.obj.obj U) :
    topologicalSpaceModuleScalarMulAppFun f ℱ U (a • s) =
      a • topologicalSpaceModuleScalarMulAppFun f ℱ U s := sorry

/-- Scalar multiplication by `f` as an endomorphism of the module of sections over an open set. -/
abbrev topologicalSpaceModuleScalarMulApp
    (f : A) (ℱ : ModSheaf) (U : (Opens X)ᵒᵖ) :
    ℱ.obj.obj U ⟶ ℱ.obj.obj U :=
  let M : ModuleCat A := ℱ.obj.obj U
  let linearMap : M →ₗ[A] M :=
    { toFun := topologicalSpaceModuleScalarMulAppFun f ℱ U
      map_add' := topologicalSpaceModuleScalarMulAppFun_map_add f ℱ U
      map_smul' := topologicalSpaceModuleScalarMulAppFun_map_smul f ℱ U }
  show M ⟶ M from (ModuleCat.homEquiv).symm linearMap

-- Proof sketch: the restriction maps of a sheaf of `A`-modules are `A`-linear, hence they
-- commute with multiplication by the fixed scalar `f`.
/-- Scalar multiplication by `f` is natural with respect to restriction maps. -/
theorem topologicalSpaceModuleScalarMul_naturality
    (f : A) (ℱ : ModSheaf) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ℱ.obj.map i ≫ topologicalSpaceModuleScalarMulApp f ℱ V =
      topologicalSpaceModuleScalarMulApp f ℱ U ≫ ℱ.obj.map i := sorry

/-- Scalar multiplication by `f` as an endomorphism of a sheaf of `A`-modules. -/
abbrev topologicalSpaceModuleScalarMul
    (f : A) (ℱ : ModSheaf) : ℱ ⟶ ℱ :=
  ObjectProperty.homMk
    { app := fun U ↦ topologicalSpaceModuleScalarMulApp f ℱ U
      naturality := fun {_ _} i ↦ topologicalSpaceModuleScalarMul_naturality f ℱ i }

/-- The transition morphism `\mathcal F_{n + 1} \to \mathcal F_n` in a sequential inverse system
of sheaves of `A`-modules. -/
abbrev topologicalSpaceModuleInverseSystemStep
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (n : ℕ) :
    ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op n) :=
  ℱ.map (homOfLE (Nat.le_succ n)).op

/-- The comparison morphism `\mathcal F_n \to \mathcal F_1` for a stage `n ≥ 1` of a sequential
inverse system of sheaves of `A`-modules. -/
abbrev topologicalSpaceModuleInverseSystemToFirst
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (n : ℕ) (hn : 1 ≤ n) :
    ℱ.obj (op n) ⟶ ℱ.obj (op 1) :=
  ℱ.map (homOfLE hn).op

/-- The stepwise short exactness condition from Lemma `20.36.1` for a tower of sheaves of
`A`-modules and an element `f ∈ A`. -/
def topologicalSpacePrincipalIdealStepShortExactCondition
    (f : A) (ℱ : ℕᵒᵖ ⥤ ModSheaf) : Prop :=
  ∀ n : ℕ, ∀ _ : 1 ≤ n,
    let π := topologicalSpaceModuleInverseSystemToFirst ℱ (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
    ∃ (ι : ℱ.obj (op n) ⟶ ℱ.obj (op (n + 1))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        topologicalSpaceModuleInverseSystemStep ℱ n ≫ ι =
          topologicalSpaceModuleScalarMul f (ℱ.obj (op (n + 1)))

/-- The degree-`p` cohomology group `H^p(X, \mathcal F_n)` of the `n`th stage of a sheaf tower. -/
abbrev topologicalSpaceModuleCohomologyStage
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (p n : ℕ) : AddCommGrpCat :=
  (topologicalSpaceModuleCohomologyFunctor p).obj (ℱ.obj (op n))

/-- The comparison map `H^p(X, \mathcal F_n) \to H^p(X, \mathcal F_1)` in a sequential
cohomology tower. -/
abbrev topologicalSpaceModuleCohomologyToFirst
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (p n : ℕ) (hn : 1 ≤ n) :
    topologicalSpaceModuleCohomologyStage ℱ p n ⟶
      topologicalSpaceModuleCohomologyStage ℱ p 1 :=
  (topologicalSpaceModuleCohomologyTower ℱ p).map (homOfLE hn).op

/-- The intersection of the images of the degree-`q` cohomology maps into stage `1`, written
using chosen `A`-linear realizations of those maps. -/
def topologicalSpaceModuleCohomologyToFirstImageIntersection
    (ℱ : ℕᵒᵖ ⥤ ModSheaf) (q : ℕ)
    [∀ n : ℕ, Module A (topologicalSpaceModuleCohomologyStage ℱ q n)]
    (toFirstLinear : ∀ n : ℕ, 1 ≤ n →
      topologicalSpaceModuleCohomologyStage ℱ q n →ₗ[A]
        topologicalSpaceModuleCohomologyStage ℱ q 1) :
    Submodule A (topologicalSpaceModuleCohomologyStage ℱ q 1) :=
  sInf {N : Submodule A (topologicalSpaceModuleCohomologyStage ℱ q 1) |
    ∃ n : ℕ, ∃ hn : 1 ≤ n, N = LinearMap.range (toFirstLinear n hn)}

-- Proof sketch: apply the criterion of Lemma `20.35.2` to the principal ideal `(f)`. Under the
-- stepwise short exactness hypothesis, the ideal-power tower `(f)^n \mathcal F_{m + 1}` is
-- identified with the shifted tower `\mathcal F_{m + 1 - n}`, so the eventual ranges `N_n` are
-- controlled by the images of `H^{p + 1}(X, \mathcal F_m) → H^{p + 1}(X, \mathcal F_1)`. The
-- finite-length or Noetherian finite-intersection hypothesis then yields the required ACC input,
-- and Lemma `20.35.2` gives the Mittag-Leffler property.
/-- Lemma 20.36.5: let `A` be a ring, let `f ∈ A`, let `X` be a topological space, and let
`(\mathcal F_n)_n` be a sequential inverse system of sheaves of `A`-modules on `X`. Assume the
stepwise short exactness condition `(1)` from Lemma `20.36.1`. Also assume that the degree
`p + 1` cohomology maps into `H^{p + 1}(X, \mathcal F_1)` admit chosen `A`-linear models
`toFirstLinear`, compatible with the actual cohomology transition maps, and that either some
image `\operatorname{Im}(H^{p + 1}(X, \mathcal F_m) \to H^{p + 1}(X, \mathcal F_1))` has finite
length as an `A`-module or `A` is Noetherian and the intersection of these images is a finite
`A`-module. Then the inverse system `n ↦ H^p(X, \mathcal F_n)` satisfies the Mittag-Leffler
condition. -/
lemma topologicalSpace_moduleCohomologyTower_isMittagLeffler_of_principalIdeal_stepShortExactCondition_of_imageFiniteLength_or_intersectionFinite
    (f : A)
    (ℱ : ℕᵒᵖ ⥤ ModSheaf)
    (p : ℕ)
    (hstep : topologicalSpacePrincipalIdealStepShortExactCondition f ℱ)
    [∀ n : ℕ, Module A (topologicalSpaceModuleCohomologyStage ℱ (p + 1) n)]
    (toFirstLinear : ∀ n : ℕ, 1 ≤ n →
      topologicalSpaceModuleCohomologyStage ℱ (p + 1) n →ₗ[A]
        topologicalSpaceModuleCohomologyStage ℱ (p + 1) 1)
    (htoFirstLinear : ∀ n : ℕ, ∀ hn : 1 ≤ n,
      (toFirstLinear n hn).toAddMonoidHom =
        (topologicalSpaceModuleCohomologyToFirst ℱ (p + 1) n hn).hom)
    (hfinite :
      (∃ m : ℕ, ∃ hm : 1 ≤ m,
        IsFiniteLength A (ModuleCat.of A ↥(LinearMap.range (toFirstLinear m hm)))) ∨
      (IsNoetherianRing A ∧
        Module.Finite A
          (ModuleCat.of A ↥(topologicalSpaceModuleCohomologyToFirstImageIntersection
            ℱ (p + 1) toFirstLinear)))) :
    ((topologicalSpaceModuleCohomologyTower ℱ p) ⋙
      forget AddCommGrpCat).IsMittagLeffler := sorry

end

end CategoryTheory

/-! ### Remark_20_36_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.SequentialInverseSystem

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- A global section of the structure sheaf determines an element of the global-sections ring
`Γ(X, \mathcal O_X)` by evaluation on the top open subset. -/
abbrev globalSectionAsRingElement
    (f : StructureSheafGlobalSection X) : globalSectionsRing X :=
  show globalSectionsRing X from globalSectionRestrict f (op (⊤ : Opens X.carrier))

-- Proof sketch: unfold `globalSectionAsRingElement`; it is the value of `f` on the top open.
/-- Evaluating a global section on the top open recovers the corresponding element of
`Γ(X, \mathcal O_X)`. -/
theorem globalSectionAsRingElement_def
    (f : StructureSheafGlobalSection X) :
    globalSectionAsRingElement f =
      (show globalSectionsRing X from globalSectionRestrict f (op (⊤ : Opens X.carrier))) :=
  rfl

/-- The standard Milnor cokernel model for `R^1 \!\varprojlim` of a sequential inverse system of
modules. -/
abbrev sequentialModuleR1Lim {A : Type u} [CommRing A]
    (M : SequentialInverseSystem (ModuleCat A)) : ModuleCat A :=
  cokernel <|
    Pi.lift fun n ↦
      Pi.π (fun k ↦ M.obj (op k)) n -
        Pi.π (fun k ↦ M.obj (op k)) (n + 1) ≫ M.map ((homOfLE (Nat.le_succ n)).op)

-- Proof sketch: unfold `sequentialModuleR1Lim`; it is defined as the cokernel of the Milnor
-- difference map on the product of the stages of `M`.
/-- The Milnor model for `R^1 \!\varprojlim M_n` is the cokernel of the usual difference map on
`∏_n M_n`. -/
theorem sequentialModuleR1Lim_def {A : Type u} [CommRing A]
    (M : SequentialInverseSystem (ModuleCat A)) :
    sequentialModuleR1Lim M =
      cokernel
        (Pi.lift fun n ↦
          Pi.π (fun k ↦ M.obj (op k)) n -
            Pi.π (fun k ↦ M.obj (op k)) (n + 1) ≫ M.map ((homOfLE (Nat.le_succ n)).op)) :=
  rfl

section

variable (f : StructureSheafGlobalSection X) (ℱ : (RingedSpace.Modules X))
variable (quotTower : ℕᵒᵖ ⥤ (RingedSpace.Modules X)) (p : ℕ)

local notation "f₀" => globalSectionAsRingElement f
local notation "Hp" => moduleGlobalCohomology X (p : ℤ) ℱ
local notation "Hp1" => moduleGlobalCohomology X (((p + 1 : ℕ) : ℤ)) ℱ
local notation "Qsys" => principalPowerQuotientTower f₀ Hp
local notation "Bsys" => moduleGlobalCohomologyTower (p : ℤ) quotTower
local notation "Tsys" => principalPowerTorsionTower f₀ Hp1

-- Proof sketch: apply the long exact cohomology sequence to the short exact sequences
-- `0 → \mathcal F/f^n\mathcal F → \mathcal F/f^(n+1)\mathcal F → H^{p+1}(X,\mathcal F)[f^(n+1)]`
-- furnished by the `f`-torsion-free quotient-tower condition, and assemble the resulting maps
-- functorially in `n`.
/-- Remark 20.36.6 (1): if `quotTower` models the quotient tower
`n ↦ \mathcal F / f^(n+1)\mathcal F` of an `f`-torsion-free `\mathcal O_X`-module `\mathcal F`,
then for every `p` there is a short exact sequence of inverse systems
`0 → (H^p(X,\mathcal F)/f^(n+1)H^p(X,\mathcal F))_n →
 (H^p(X,\mathcal F/f^(n+1)\mathcal F))_n →
 (H^{p+1}(X,\mathcal F)[f^(n+1)])_n → 0`.
This is the source tower reindexed from powers `f^n` with `n ≥ 1` to powers `f^(n+1)` with
`n : ℕ`. -/
theorem exists_cohomology_shortExact_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    ∃ (ι : Qsys ⟶ Bsys) (π : Bsys ⟶ Tsys) (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

-- Proof sketch: each transition map in the quotient tower
-- `H^p(X,\mathcal F)/f^(n+2)H^p(X,\mathcal F) → H^p(X,\mathcal F)/f^(n+1)H^p(X,\mathcal F)` is
-- surjective, so the images into any fixed stage stabilize immediately.
/-- Remark 20.36.6 (2): the inverse system
`n ↦ H^p(X,\mathcal F)/f^(n+1)H^p(X,\mathcal F)` is Mittag-Leffler. Equivalently, the source
inverse system `{H^p(X,\mathcal F)/f^nH^p(X,\mathcal F)}` is Mittag-Leffler after the same
reindexing shift. -/
theorem cohomology_principalPowerQuotientTower_isMittagLeffler :
    IsMittagLeffler Qsys := by
  simpa using principalPowerQuotientTower_isMittagLeffler f₀ Hp

-- Proof sketch: combine the short exact sequence of inverse systems from part `(1)` with the
-- Mittag-Leffler property from part `(2)`, then apply inverse-limit exactness for sequential
-- systems to obtain the short exact sequence on limits.
/-- Remark 20.36.6 (3): under the same quotient-tower hypothesis, there is a short exact sequence
`0 → \widehat{H^p(X,\mathcal F)} → \varprojlim_n H^p(X,\mathcal F/f^(n+1)\mathcal F) →
 T_f(H^{p+1}(X,\mathcal F)) → 0`,
where the left term is the usual `f`-adic completion, modeled by the inverse limit of the quotient
tower, and the right term is the principal Tate module, modeled by the inverse limit of the
torsion tower. -/
theorem exists_cohomology_completion_shortExact_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    ∃ (ι : limit Qsys ⟶ limit Bsys)
      (π : limit Bsys ⟶ limit Tsys)
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

-- Proof sketch: use the six-term exact sequence for derived inverse limits on the short exact
-- system from part `(1)`. The left quotient tower is Mittag-Leffler by part `(2)`, so its
-- `R^1 \!\varprojlim` term vanishes and the remaining two `R^1 \!\varprojlim` terms identify.
/-- Remark 20.36.6 (4): under the same quotient-tower hypothesis, the standard Milnor models for
`R^1 \!\varprojlim_n H^p(X,\mathcal F/f^(n+1)\mathcal F)` and
`R^1 \!\varprojlim_n H^{p+1}(X,\mathcal F)[f^(n+1)]` are canonically isomorphic. -/
theorem cohomologyTower_R1Lim_iso_torsion_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    IsIsomorphic (sequentialModuleR1Lim Bsys) (sequentialModuleR1Lim Tsys) := sorry

-- Proof sketch: apply Remark `15.94.7` to the short exact sequence of cohomology towers from part
-- `(1)`. Since the left quotient tower is Mittag-Leffler by part `(2)`, the middle tower is
-- Mittag-Leffler exactly when the right torsion tower is.
/-- Remark 20.36.6 (5): under the same quotient-tower hypothesis, the inverse system
`n ↦ H^{p+1}(X,\mathcal F)[f^(n+1)]` is Mittag-Leffler if and only if the inverse system
`n ↦ H^p(X,\mathcal F/f^(n+1)\mathcal F)` is Mittag-Leffler. -/
theorem cohomologyTower_isMittagLeffler_iff_torsion_of_torsionFreeQuotientTower
    (hquot : torsionFreeQuotientTowerCondition f quotTower) :
    IsMittagLeffler Bsys ↔ IsMittagLeffler Tsys := by
  rcases exists_cohomology_shortExact_of_torsionFreeQuotientTower f ℱ quotTower p hquot with
    ⟨ι, π, h, hShort⟩
  simpa using
    principalPower_shortExact_middle_isMittagLeffler_iff_torsion f₀ Hp Hp1 Bsys ι π h hShort

end

end AlgebraicGeometry.RingedSpace
