import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
