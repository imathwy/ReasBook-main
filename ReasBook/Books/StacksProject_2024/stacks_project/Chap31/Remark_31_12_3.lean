import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

variable (k : Type u) [Field k]

local notation "Kt" => Polynomial k
local notation "t" => (X : Kt)

/- Domain-style sampling for Remark 31.12.3:
- primary domain: affine module-theoretic reflexivity over the explicit semigroup ring
  `k[t^3, t^4, t^5]`, together with the relative evaluation map into a fixed module;
- sampled owner declarations:
  `Module.IsReflexive`,
  `LinearMap.applyₗ`,
  `Ideal.span`,
  `Algebra.adjoin`;
- semantic recall hit:
  `lean_leansearch` returned `LinearMap.applyₗ`, the canonical owner of the evaluation map
  `M → Hom_R(Hom_R(M, C), C)` into a fixed codomain module `C`;
- source/core/bridge triage:
  `source-facing`: the explicit affine example `R = k[t^3, t^4, t^5]` and the ideal
    `ω = (t^3, t^4)`, used as the module-level avatar of the dualizing sheaf in the source remark;
  `core/canonical`: `Module.IsReflexive` for the ordinary notion and `LinearMap.applyₗ` for the
    relative evaluation map into `ω`;
  `bridge/view`: the explicit companion theorem spelling out how `LinearMap.applyₗ` acts on
    `ω`.

The current Lean environment does not provide dualizing-complex infrastructure for coherent sheaves
on schemes, so this file formalizes the source remark at the affine module level with explicit
ring and ideal data rather than introducing fake scheme-side placeholder APIs.
-/

/-- The affine semigroup ring `k[t^3, t^4, t^5]` as a `k`-subalgebra of `k[t]`. -/
def threeFourFiveSemigroupRing : Subalgebra k Kt :=
  Algebra.adjoin k ({ t ^ 3, t ^ 4, t ^ 5 } : Set Kt)

namespace ThreeFourFiveSemigroupRing

local notation "S" => threeFourFiveSemigroupRing k
local notation "R" => ↥S

/-- The subtype element of `R` represented by `t^3`. -/
private def generatorThree :
    R :=
  ⟨t ^ 3, Algebra.subset_adjoin (by simp)⟩

/-- The subtype element of `R` represented by `t^4`. -/
private def generatorFour :
    R :=
  ⟨t ^ 4, Algebra.subset_adjoin (by simp)⟩

/-- The ideal `(t^3, t^4)` inside `k[t^3, t^4, t^5]`. -/
def omega : Ideal R :=
  Ideal.span
    ({ generatorThree k, generatorFour k } : Set R)

local notation "ω" => omega k

local instance : Module R R :=
  Semiring.toModule

local instance : Module R ω :=
  SMulMemClass.toModule ω

local instance : Module R (ω →ₗ[R] ω) :=
  LinearMap.module

/-- The canonical evaluation map `Hom_R(ω, ω) → Hom_R(ω, ω)` at a fixed element of `ω`. -/
abbrev selfEval : (ω →ₗ[R] ω) →ₗ[R] ω →ₗ[R] ω :=
  LinearMap.applyₗ' (R := R) (S := R) (M := ω) (M₂ := ω)

/-- The relative evaluation map into `ω` is the canonical `LinearMap.applyₗ` evaluation map. -/
theorem selfEval_apply
    (φ : ω →ₗ[R] ω) (m : ω) :
    selfEval (k := k) φ m = φ m :=
  rfl

/-- Remark 31.12.3 (1): for the affine example `X = Spec(k[t^3, t^4, t^5])`, the module-level
avatar `ω = (t^3, t^4)` of the dualizing sheaf is not reflexive in the ordinary sense based on
`Hom_R(-, R)`. -/
theorem omega_not_isReflexive :
    ¬ Module.IsReflexive R ω := sorry

/-- Remark 31.12.3 (2): for the same affine example, the canonical evaluation map
`ω → Hom_R(Hom_R(ω, ω), ω)` is bijective, expressing reflexivity with respect to the dualizing
module rather than with respect to the structure sheaf. -/
theorem selfEval_bijective :
    Function.Bijective (selfEval (k := k)) := sorry

end ThreeFourFiveSemigroupRing
