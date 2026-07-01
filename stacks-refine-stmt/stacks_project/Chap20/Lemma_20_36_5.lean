import Mathlib
import stacks_project.Chap20.Lemma_20_35_1

-- Declarations for this item will be appended below by the statement pipeline.

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
