import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open scoped PrincipalIdeal

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)
local notation "ΓMod" => Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat A)

/- Domain-style sampling for 20.36.3:
- primary domain: inverse systems of sheaves of `A`-modules on a topological space and the induced
  inverse system of global sections;
- sampled owner declarations:
  `Sheaf.Γ`,
  `Limits.limit`,
  `Limits.limit.π`,
  `SequentialInverseSystem.transitionMap`,
  `f • 𝟙 _` for scalar endomorphisms in `Sheaf (Opens.grothendieckTopology X) (ModuleCat A)`;
- best owner abstraction: the canonical inverse-limit object of global sections
  `lim (ℱ ⋙ Sheaf.Γ ...)`, together with its projection to stage `1`, and the canonical scalar
  action on sheaf endomorphisms;
- primitive data: the scalar `f : A`, the sequential inverse system `ℱ`, and the stepwise short
  exactness condition;
- derived API: finiteness, regularity, and kernel-identification statements for
  `limit (ℱ ⋙ ΓMod)`.

Source/core/bridge triage:
- `source-facing`: `topologicalSpaceModuleStepShortExactCondition` and the three numbered lemma
  consequences about the inverse limit of global sections;
- `core/canonical`: `Sheaf.Γ`, `Limits.limit`, and `Limits.limit.π`;
- `bridge/view`: the composed tower `ℱ ⋙ ΓMod`.

The previous file exposed the composed tower itself as a public `abbrev` even though it adds no
mathematical content beyond the canonical owners above. The refined file keeps the same
mathematics, treats the tower only as an internal view, and exposes the source-facing limit object
`M = lim (ℱ ⋙ Sheaf.Γ ...)` and its stage-`1` projection as the reusable public API.
-/

/-- Condition `(1)` of Lemma `20.36.1` for a sequential inverse system of sheaves of `A`-modules
with respect to the scalar `f : A`. -/
def topologicalSpaceModuleStepShortExactCondition
    (f : A) (ℱ : SequentialInverseSystem ModSheaf) : Prop :=
  ∀ n : ℕ,
    let π := ℱ.stepMap (n + 1)
    ∃ (ι : ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op (n + 2))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        ℱ.stepMap (n + 1) ≫ ι = f • 𝟙 (ℱ.obj (op (n + 2)))

namespace topologicalSpaceModuleStepShortExactCondition

/-- Under condition `(1)` of Lemma `20.36.1`, the short exact row at each positive stage of the
tower is available directly with the source indexing `n + 1`. -/
theorem exists_succ
    {f : A} {ℱ : SequentialInverseSystem ModSheaf}
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) (n : ℕ) :
    let π := ℱ.stepMap (n + 1)
    ∃ (ι : ℱ.obj (op (n + 1)) ⟶ ℱ.obj (op (n + 2))) (hιπ : ι ≫ π = 0),
      (ShortComplex.mk ι π hιπ).ShortExact ∧
        ℱ.stepMap (n + 1) ≫ ι = f • 𝟙 (ℱ.obj (op (n + 2))) :=
  hstep n

end topologicalSpaceModuleStepShortExactCondition

/-- The inverse limit `M = lim (ℱ ⋙ ΓMod)` of the global sections of a sequential inverse system of
sheaves of `A`-modules on `X`. -/
abbrev topologicalSpaceModuleGlobalSectionsLimit
    (ℱ : SequentialInverseSystem ModSheaf) : ModuleCat A :=
  limit (ℱ ⋙ ΓMod)

/-- The canonical projection `M → Γ(X, ℱ₁)` from the inverse limit of global sections to stage
`1`. -/
abbrev topologicalSpaceModuleGlobalSectionsLimitProjection
    (ℱ : SequentialInverseSystem ModSheaf) :
    topologicalSpaceModuleGlobalSectionsLimit ℱ →ₗ[A] ((ΓMod).obj (ℱ.obj (op 1))) :=
  (limit.π (ℱ ⋙ ΓMod) (op 1)).hom

@[simp] theorem topologicalSpaceModuleGlobalSectionsLimitProjection_apply
    (ℱ : SequentialInverseSystem ModSheaf) (x : topologicalSpaceModuleGlobalSectionsLimit ℱ) :
    topologicalSpaceModuleGlobalSectionsLimitProjection ℱ x =
      ((limit.π (ℱ ⋙ ΓMod) (op 1)).hom) x :=
  rfl

-- Proof sketch: the stepwise short exact condition identifies the kernel of the projection
-- `M → Γ(X, ℱ₁)` with `fM`, so `M / fM` is a subquotient of `Γ(X, ℱ₁)`. Since
-- `A` is Noetherian and `Γ(X, ℱ₁)` is finite, the quotient `M / fM` is finite. The
-- completion hypothesis and Lemma `10.96.12` then promote finite generation of `M / fM` to finite
-- generation of the complete separated module `M`.
/-- Lemma 20.36.3 (1): if `A` is Noetherian and complete with respect to the principal ideal
`(f)`, if `Γ(X, ℱ₁)` is a finite `A`-module, and if the inverse system `(ℱₙ)ₙ` satisfies
condition `(1)` of Lemma `20.36.1`, then
`M = lim (ℱ ⋙ ΓMod)` is a finite `A`-module. -/
@[stacks 0BLB]
theorem topologicalSpaceModuleGlobalSectionsLimit_finite_of_stepShortExactCondition
    (f : A) (ℱ : SequentialInverseSystem ModSheaf)
    [IsNoetherianRing A]
    [IsAdicComplete ((f) : Ideal A) A]
    (hΓ₁finite : Module.Finite A ((ΓMod).obj (ℱ.obj (op 1))))
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) :
    Module.Finite A (topologicalSpaceModuleGlobalSectionsLimit ℱ) := sorry

-- Proof sketch: if `s = (s_n)` lies in the inverse limit and `f • s = 0`, then condition `(1)`
-- shows that each `s_{n + 1}` maps to zero in `ℱₙ`, hence already vanishes in the tower.
-- Therefore every component of `s` is zero, so multiplication by `f` on `M` is injective.
/-- Lemma 20.36.3 (2): under condition `(1)` of Lemma `20.36.1`, multiplication by `f` on
`M = lim (ℱ ⋙ ΓMod)` is injective; equivalently, `f` is a nonzerodivisor on
`M`. -/
@[stacks 0BLB]
theorem topologicalSpaceModuleGlobalSectionsLimit_isSMulRegular_of_stepShortExactCondition
    (f : A) (ℱ : SequentialInverseSystem ModSheaf)
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) :
    IsSMulRegular (topologicalSpaceModuleGlobalSectionsLimit ℱ) f := sorry

-- Proof sketch: apply condition `(1)` to the tower of global sections. The kernel of the
-- projection `M → Γ(X, ℱ₁)` is exactly the principal submodule `fM`; the textbook
-- identification `M / fM = im (M → Γ(X, ℱ₁))` then follows from the first
-- isomorphism theorem.
/-- Lemma 20.36.3 (3): under condition `(1)` of Lemma `20.36.1`, the kernel of the projection
`M = lim (ℱ ⋙ ΓMod) → Γ(X, ℱ₁)` is exactly `fM`. Equivalently,
`M / fM` identifies with the image of `M` in `Γ(X, ℱ₁)`. -/
@[stacks 0BLB]
theorem topologicalSpaceModuleGlobalSectionsLimit_projection_ker_eq_principalSubmodule_of_stepShortExactCondition
    (f : A) (ℱ : SequentialInverseSystem ModSheaf)
    (hstep : topologicalSpaceModuleStepShortExactCondition f ℱ) :
    LinearMap.ker (topologicalSpaceModuleGlobalSectionsLimitProjection ℱ) =
      (((f) : Ideal A) •
        (⊤ : Submodule A (topologicalSpaceModuleGlobalSectionsLimit ℱ))) := sorry

end

end CategoryTheory
