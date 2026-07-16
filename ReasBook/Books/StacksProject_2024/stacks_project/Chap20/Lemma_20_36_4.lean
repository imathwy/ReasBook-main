import StacksProject_2024.stacks_project.Chap20.SiteModuleCohomologyTower
import StacksProject_2024.stacks_project.Chap20.Lemma_20_36_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-- Internal shorthand for the canonical scalar endomorphism of a sheaf of `A`-modules. -/
private abbrev sheafScalarEndomorphism
    (a : A) (ℱ : ModSheaf) : ℱ ⟶ ℱ :=
  a • 𝟙 ℱ

/-- A morphism of sheaves of `A`-modules commutes with the canonical scalar endomorphisms. -/
private theorem sheafScalarEndomorphism_comm
    (a : A) {ℱ 𝒢 : ModSheaf} (φ : ℱ ⟶ 𝒢) :
    sheafScalarEndomorphism a ℱ ≫ φ =
      φ ≫ sheafScalarEndomorphism a 𝒢 := by
  simp [sheafScalarEndomorphism, CategoryTheory.Linear.smul_comp,
    CategoryTheory.Linear.comp_smul]

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (forget₂ (ModuleCat A) AddCommGrpCat)]

private abbrev topologicalSpaceModuleCohomologySMul
    (p : ℕ) (ℱ : ModSheaf) (a : A) :
    ((siteModuleCohomologyFunctor p).obj ℱ) →
      ((siteModuleCohomologyFunctor p).obj ℱ) :=
  ((siteModuleCohomologyFunctor p).map
    (sheafScalarEndomorphism a ℱ)).hom

private instance sheafCompose_moduleToAdd_additive :
    (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat A) AddCommGrpCat)).Additive := by
  constructor
  intro ℱ 𝒢 φ ψ
  apply (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map_injective
  ext U x
  rfl

private instance siteModuleCohomologyFunctorAdditive (p : ℕ) :
    (sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat A) AddCommGrpCat) ⋙
      Sheaf.cohomologyFunctor (Opens.grothendieckTopology X) p).Additive :=
  by
    infer_instance

private instance topologicalSpaceModuleCohomologySMulInst
    (p : ℕ) (ℱ : ModSheaf) :
    SMul A ((siteModuleCohomologyFunctor p).obj ℱ) where
  smul := topologicalSpaceModuleCohomologySMul p ℱ

/-- The degree-`p` cohomology of a sheaf of `A`-modules carries its canonical `A`-module
structure induced by scalar endomorphisms of the sheaf. -/
instance siteModuleCohomologyModule
    (p : ℕ) (ℱ : ModSheaf) :
    Module A ((siteModuleCohomologyFunctor p).obj ℱ) :=
  Module.ofMinimalAxioms
    (by
      intro a x y
      simpa [topologicalSpaceModuleCohomologySMul] using
        (((siteModuleCohomologyFunctor p).map (sheafScalarEndomorphism a ℱ)).hom.map_add x y))
    (by
      intro a b x
      have hmapAdd :
          (siteModuleCohomologyFunctor p).map ((a + b) • 𝟙 ℱ) =
            (siteModuleCohomologyFunctor p).map (a • 𝟙 ℱ) +
              (siteModuleCohomologyFunctor p).map (b • 𝟙 ℱ) := by
        simpa [add_smul] using
          (Functor.map_add (siteModuleCohomologyFunctor p) :
            (siteModuleCohomologyFunctor p).map ((a • 𝟙 ℱ) + (b • 𝟙 ℱ)) =
              (siteModuleCohomologyFunctor p).map (a • 𝟙 ℱ) +
                (siteModuleCohomologyFunctor p).map (b • 𝟙 ℱ))
      simpa [topologicalSpaceModuleCohomologySMul, sheafScalarEndomorphism, smul_add] using
        ConcreteCategory.congr_hom hmapAdd x)
    (by
      intro a b x
      change AddCommGrpCat.Hom.hom
          ((siteModuleCohomologyFunctor p).map (((a * b) : A) • 𝟙 ℱ)) x =
        AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map (a • 𝟙 ℱ))
          (AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map (b • 𝟙 ℱ)) x)
      simpa [sheafScalarEndomorphism, mul_smul] using
        congrArg (fun ψ ↦ AddCommGrpCat.Hom.hom ψ x)
          ((siteModuleCohomologyFunctor p).map_comp (b • 𝟙 ℱ) (a • 𝟙 ℱ)))
    (by
      intro x
      have hmapOne :
          (siteModuleCohomologyFunctor p).map ((1 : A) • 𝟙 ℱ) =
            𝟙 ((siteModuleCohomologyFunctor p).obj ℱ) := by
        simp [one_smul]
      change AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map ((1 : A) • 𝟙 ℱ)) x = x
      rw [hmapOne]
      rfl)

/-- The degree-`p` cohomology map induced by a morphism of sheaves of `A`-modules is canonically
`A`-linear. -/
abbrev siteModuleCohomologyMapLinear
    (p : ℕ) {ℱ 𝒢 : ModSheaf} (φ : ℱ ⟶ 𝒢) :
    ((siteModuleCohomologyFunctor p).obj ℱ) →ₗ[A]
      ((siteModuleCohomologyFunctor p).obj 𝒢) :=
  { toFun := ((siteModuleCohomologyFunctor p).map φ).hom
    map_add' := ((siteModuleCohomologyFunctor p).map φ).hom.map_add
    map_smul' := by
      intro a x
      change AddCommGrpCat.Hom.hom
          (((siteModuleCohomologyFunctor p).map (sheafScalarEndomorphism a _)) ≫
            (siteModuleCohomologyFunctor p).map φ) x =
        AddCommGrpCat.Hom.hom
          (((siteModuleCohomologyFunctor p).map φ) ≫
            (siteModuleCohomologyFunctor p).map (sheafScalarEndomorphism a _)) x
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun ψ ↦ AddCommGrpCat.Hom.hom ψ x) <|
        congrArg ((siteModuleCohomologyFunctor p).map) (sheafScalarEndomorphism_comm a φ) }

@[simp] theorem siteModuleCohomologyMapLinear_apply
    (p : ℕ) {ℱ 𝒢 : ModSheaf} (φ : ℱ ⟶ 𝒢) (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    siteModuleCohomologyMapLinear p φ x =
      ((siteModuleCohomologyFunctor p).map φ).hom x :=
  rfl

/-- The degree-`p` cohomology of sheaves of `A`-modules, viewed as a functor to `ModuleCat A`
using the canonical module structure on each cohomology group. -/
abbrev siteModuleCohomologyModuleFunctor (p : ℕ) :
    ModSheaf ⥤ ModuleCat A where
  obj ℱ := ModuleCat.of A ((siteModuleCohomologyFunctor p).obj ℱ)
  map φ := ModuleCat.ofHom (siteModuleCohomologyMapLinear p φ)
  map_id ℱ := by
    ext x
    change AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map (𝟙 ℱ)) x = x
    rw [Functor.map_id]
    rfl
  map_comp φ ψ := by
    ext x
    change AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map (φ ≫ ψ)) x =
      AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map ψ)
        (AddCommGrpCat.Hom.hom ((siteModuleCohomologyFunctor p).map φ) x)
    rw [Functor.map_comp]
    rfl

@[simp] theorem siteModuleCohomologyModuleFunctor_map_apply
    (p : ℕ) {ℱ 𝒢 : ModSheaf} (φ : ℱ ⟶ 𝒢) (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    ((siteModuleCohomologyModuleFunctor p).map φ).hom x =
      ((siteModuleCohomologyFunctor p).map φ).hom x :=
  rfl

/-- The sequential inverse system `n ↦ H^p(X, ℱ_n)` viewed in `ModuleCat A` via the canonical
`A`-module structures on the stagewise cohomology groups. -/
abbrev siteModuleCohomologyModuleTower
    (ℱ : SequentialInverseSystem ModSheaf) (p : ℕ) :
    SequentialInverseSystem (ModuleCat A) :=
  ℱ ⋙ siteModuleCohomologyModuleFunctor p

/-- The degree-`p` cohomology transition map in a sequential inverse system of sheaves of
`A`-modules, viewed as the canonical `A`-linear map on the site cohomology tower
`siteModuleCohomologyTower ℱ p`. -/
abbrev siteModuleCohomologyTransitionMapLinear
    (ℱ : SequentialInverseSystem ModSheaf) (p : ℕ) {i j : ℕ} (hij : i ≤ j) :
    ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op j))) →ₗ[A]
      ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op i))) :=
  siteModuleCohomologyMapLinear p (ℱ.transitionMap hij)

@[simp] theorem siteModuleCohomologyModuleTower_transitionMap_apply
    (ℱ : SequentialInverseSystem ModSheaf) (p : ℕ) {i j : ℕ} (hij : i ≤ j)
    (x : (siteModuleCohomologyFunctor p).obj (ℱ.obj (op j))) :
    ((siteModuleCohomologyModuleTower ℱ p).transitionMap hij).hom x =
      ((siteModuleCohomologyTower ℱ p).transitionMap hij).hom x :=
  rfl

@[simp] theorem siteModuleCohomologyTransitionMapLinear_apply
    (ℱ : SequentialInverseSystem ModSheaf) (p : ℕ) {i j : ℕ} (hij : i ≤ j)
    (x : (siteModuleCohomologyFunctor p).obj (ℱ.obj (op j))) :
    siteModuleCohomologyTransitionMapLinear ℱ p hij x =
      ((siteModuleCohomologyTower ℱ p).transitionMap hij).hom x :=
  siteModuleCohomologyModuleTower_transitionMap_apply ℱ p hij x

-- Proof sketch: the stepwise short exactness hypothesis is the source-facing condition `(1)` of
-- Lemma `20.36.1`. Together with the finite-length or Noetherian-finite hypothesis on
-- `H^(p + 1)(X, ℱ₁)`, the preceding subsection identifies the degree-`p` cohomology tower
-- with a tower satisfying the standard Mittag-Leffler criterion.
/-- Lemma 20.36.4: let `A` be a ring, let `f ∈ A`, let `X` be a topological space, and let
`(ℱₙ)ₙ` be a sequential inverse system of sheaves of `A`-modules on `X`. Assume condition `(1)`
of Lemma `20.36.1` for `X`, `f`, and `(ℱₙ)ₙ`. If `H^(p + 1)(X, ℱ₁)` is either of finite length
as an `A`-module or finite over the Noetherian ring `A`, then the tail inverse system of
`A`-modules `Mₙ = H^p(X, ℱ_{n + 1})`, formalized by
`(siteModuleCohomologyModuleTower ℱ p).shift 1`, satisfies the Mittag-Leffler condition. -/
@[stacks 0BLC]
theorem topologicalSpaceModuleCohomologyTower_isMittagLeffler_of_stepShortExactCondition_of_finiteLength_or_finite
    (f : A)
    (ℱ : SequentialInverseSystem ModSheaf)
    (p : ℕ)
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ)
    (hHp1 :
      IsFiniteLength A ((siteModuleCohomologyFunctor (p + 1)).obj (ℱ.obj (op 1))) ∨
        (IsNoetherianRing A ∧
          Module.Finite A ((siteModuleCohomologyFunctor (p + 1)).obj (ℱ.obj (op 1))))) :
    ((siteModuleCohomologyModuleTower ℱ p).shift 1).IsMittagLeffler := sorry

end

end CategoryTheory
