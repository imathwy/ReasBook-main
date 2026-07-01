import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16

noncomputable section

open scoped BigOperators Rockafellar

universe u v w u' v' w'

attribute [local instance] Classical.propDecidable

namespace Bifunction

section

variable {𝕜 : Type w}
variable {X : Type u} {XStar : Type u'}
variable {Y₀ : Type v} {Y₀Star : Type v'}
variable {ι : Type*} {Y : ι → Type w} {YStar : ι → Type w'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Fintype ι]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [HasPairing X XStar 𝕜]
variable [AddCommGroup Y₀] [Module 𝕜 Y₀]
variable [AddCommGroup Y₀Star] [Module 𝕜 Y₀Star] [HasPairing Y₀ Y₀Star 𝕜]
variable [∀ i, AddCommGroup (Y i)] [∀ i, Module 𝕜 (Y i)]
variable [∀ i, AddCommGroup (YStar i)] [∀ i, Module 𝕜 (YStar i)]
variable [∀ i, HasPairing (Y i) (YStar i) 𝕜]

local notation "U" => (ι → 𝕜) × (Y₀ × ((i : ι) → Y i))
local notation "UStar" => (ι → 𝕜) × (Y₀Star × ((i : ι) → YStar i))

private def intermediateProgramConstraint
    (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a : ∀ i : ι, Y i)
    (aStar : ι → XStar) (α : ι → 𝕜)
    (w : U) :
    ι → X → WithBotTop 𝕜 :=
  fun i x ↦
    h i (A i x + a i - w.2.2 i) + ((⟪x, aStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) + α i

private def intermediateProgramBound
    (w : U) : ι → WithBotTop 𝕜 :=
  fun i ↦ w.1 i

/-- The multiplier block `𝕜^ι`, encoded as `ι → 𝕜`, carries the canonical coordinate pairing
used by the intermediate-program adjoint owner. -/
local instance instHasPairingIntermediateProgramMultiplier :
    HasPairing (ι → 𝕜) (ι → 𝕜) 𝕜 :=
  instHasPairingOfHasLinearPairing

/-- The family of perturbation shifts pairs with its dual family by summing the coordinate
pairings. -/
local instance instHasPairingIntermediateProgramShiftFamily :
    HasPairing ((i : ι) → Y i) ((i : ι) → YStar i) 𝕜 where
  pairing p pStar := ∑ i, ⟪p i, pStar i⟫ₚ

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.24 computes the adjoint value of the intermediate-program
  bifunction `H`, where each objective/constraint branch is represented as a closed proper convex
  function after an affine change of variables.
- `core/canonical`: the existing owner for adjoint values is `Bifunction.adjoint`, so the
  source object `H_{x⋆}⋆(w⋆)` is stated directly on that owner rather than through a parallel
  surrogate package.
- `bridge/view`: the primal and dual feasibility conditions are exposed as source-facing feasible
  set owners, and the explicit dual objective is recorded directly on the actual dual
  perturbation-parameter type.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- the canonical dual zero-slice owner `((adjoint XStar UStar F)₀)` from
  `Definition_6_30_16`;
- `convexInequalitySolutionSet` and `mem_convexInequalitySolutionSet` from
  `Chap04.Text_21_0_1`;
- `convexInequalitySolutionSetOn` from `Chap04.Text_21_0_1`, which shows the chapter's
  finite-subsystem owner layer for the same kind of feasible set;
- `convexConjugate` and the notation `f⋆` from `Chap03.Defn_12_2`;
- `HasPairing`-based evaluations `⟪·, ·⟫ₚ` on all primal/dual blocks;
- `indicatorFunction` and the notation `δ[𝕜](· | ·)` from `Chap01.Defintion_4_8_1`;
- the generic ordered-scalar Chapter 6 owner layer in `Theorem_6_30_20`.

Primitive data vs derived API:
- primitive source data: the affine representation data
  `(h₀, h, A₀, A, a₀, a, a₀⋆, a⋆, α₀, α)` and the dual affine maps `(A₀⋆, A⋆)`;
- primitive Chapter 21 owner inputs: `intermediateProgramConstraint` and
  `intermediateProgramBound`, which feed the canonical all-weak feasible-set owner
  `convexInequalitySolutionSet`;
- source-facing owner: `intermediateProgramBifunction`;
- core/canonical dual owner: `adjoint` applied to `intermediateProgramBifunction`;
- bridge/view owners: `intermediateProgramDualObjective` and
  `intermediateProgramDualFeasibleSet`;
- main derived API: the explicit adjoint formula in indicator form, together with its source
  case-split companion and the zero-slice specialization through the canonical owner `(·)₀`.

Layer target: `source-facing`, while keeping the dual-space part on the intrinsic pairing-dual
layer and the primal feasibility side on the Chapter 21 feasible-set owner rather than a local
wrapper or raw `if` guards.
-/

/-- The intermediate-program bifunction `H` attached to an affine representation of the objective
and constraint functions. It is the affine objective branch plus the indicator of the feasible
slice cut out by the shifted threshold constraints, expressed directly on the Chapter 21
feasible-set owner. -/
def intermediateProgramBifunction
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜) :
    U → X → WithBotTop 𝕜 :=
  fun w x ↦
    h₀ (A₀ x + a₀ - w.2.1) + ((⟪x, a₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) + α₀ +
      δ[𝕜](x |
        convexInequalitySolutionSet
          (fun _ : ι ↦ .le)
          (intermediateProgramConstraint h A a aStar α w)
          (intermediateProgramBound w))

/-- Evaluating the intermediate-program bifunction gives the affine objective branch plus the
indicator of the source feasible slice. -/
@[simp] theorem intermediateProgramBifunction_apply
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜)
    (w : U) (x : X) :
    intermediateProgramBifunction h₀ h A₀ A a₀ a a₀Star aStar α₀ α w x =
      h₀ (A₀ x + a₀ - w.2.1) + ((⟪x, a₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) + α₀ +
        δ[𝕜](x |
          convexInequalitySolutionSet
            (fun _ : ι ↦ .le)
            (intermediateProgramConstraint h A a aStar α w)
            (intermediateProgramBound w)) :=
  rfl

-- Proof sketch: rewrite `intermediateProgramBifunction` by the indicator owner, then split on
-- membership in the Chapter 21 feasible set
-- `convexInequalitySolutionSet (fun _ : ι ↦ .le)
--    (intermediateProgramConstraint h A a aStar α w) (intermediateProgramBound w)`.
/-- Evaluating the intermediate-program bifunction also yields the textbook two-branch source
formula for `H_w(x)`. -/
theorem intermediateProgramBifunction_apply_eq_ite
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜)
    (w : U) (x : X) :
    intermediateProgramBifunction h₀ h A₀ A a₀ a a₀Star aStar α₀ α w x =
      if
          ∀ i : ι,
            h i (A i x + a i - w.2.2 i) + ((⟪x, aStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) + α i ≤ w.1 i then
        h₀ (A₀ x + a₀ - w.2.1) + ((⟪x, a₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) + α₀
      else
        ⊤ := sorry

/-- The explicit dual objective appearing in the dual program of the intermediate program, viewed
as a function on the dual perturbation-parameter space. -/
def intermediateProgramDualObjective
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (α₀ : 𝕜) (α : ι → 𝕜) :
    UStar →
      WithBotTop 𝕜 :=
  fun wStar ↦
    let uStar := wStar.1
    let p₀Star := wStar.2.1
    let pStar := wStar.2.2
    (α₀ : WithBotTop 𝕜) + ((⟪a₀, p₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) - (h₀⋆ p₀Star) +
      ∑ i : ι,
        ((((α i) * (uStar i) : 𝕜) : WithBotTop 𝕜) +
            ((⟪a i, pStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) -
          ((fun q : Y i ↦ ((uStar i : 𝕜) : WithBotTop 𝕜) * h i q)⋆ (pStar i)))

/-- Evaluating the dual-objective owner at `(u⋆, p₀⋆, p⋆)` gives the explicit finite-sum formula
from the source. -/
@[simp] theorem intermediateProgramDualObjective_apply
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (α₀ : 𝕜) (α : ι → 𝕜)
    (uStar : ι → 𝕜) (p₀Star : Y₀Star)
    (pStar : ∀ i : ι, YStar i) :
    intermediateProgramDualObjective h₀ h a₀ a α₀ α (uStar, (p₀Star, pStar)) =
      (α₀ : WithBotTop 𝕜) + ((⟪a₀, p₀Star⟫ₚ : 𝕜) : WithBotTop 𝕜) - (h₀⋆ p₀Star) +
        ∑ i : ι,
          ((((α i) * (uStar i) : 𝕜) : WithBotTop 𝕜) +
              ((⟪a i, pStar i⟫ₚ : 𝕜) : WithBotTop 𝕜) -
            ((fun q : Y i ↦ ((uStar i : 𝕜) : WithBotTop 𝕜) * h i q)⋆ (pStar i))) :=
  rfl

/-- The dual feasible set for the explicit dual program attached to the intermediate program. -/
def intermediateProgramDualFeasibleSet
    (A₀Star : Y₀Star →ₗ[𝕜] XStar) (AStar : ∀ i : ι, YStar i →ₗ[𝕜] XStar)
    (a₀Star : XStar) (aStar : ι → XStar) (xStar : XStar) :
    Set UStar :=
  {wStar |
    0 ≤ wStar.1 ∧
      a₀Star + A₀Star wStar.2.1 +
          ∑ i, ((wStar.1 i) • aStar i + AStar i (wStar.2.2 i)) = xStar}

/-- Membership in the dual feasible set is the source nonnegativity and adjoint-balance
condition. -/
@[simp] theorem mem_intermediateProgramDualFeasibleSet
    (A₀Star : Y₀Star →ₗ[𝕜] XStar) (AStar : ∀ i : ι, YStar i →ₗ[𝕜] XStar)
    (a₀Star : XStar) (aStar : ι → XStar) (xStar : XStar)
    (wStar : UStar) :
    wStar ∈ intermediateProgramDualFeasibleSet A₀Star AStar a₀Star aStar xStar ↔
      0 ≤ wStar.1 ∧
        a₀Star + A₀Star wStar.2.1 +
            ∑ i, ((wStar.1 i) • aStar i + AStar i (wStar.2.2 i)) = xStar :=
  Iff.rfl

section TheoremSurface

variable
    (h₀ : Y₀ → WithBotTop 𝕜) (h : ∀ i : ι, Y i → WithBotTop 𝕜)
    (A₀ : X →ₗ[𝕜] Y₀) (A : ∀ i : ι, X →ₗ[𝕜] Y i)
    (A₀Star : Y₀Star →ₗ[𝕜] XStar) (AStar : ∀ i : ι, YStar i →ₗ[𝕜] XStar)
    (a₀ : Y₀) (a : ∀ i : ι, Y i)
    (a₀Star : XStar) (aStar : ι → XStar)
    (α₀ : 𝕜) (α : ι → 𝕜)

local notation "H" => intermediateProgramBifunction h₀ h A₀ A a₀ a a₀Star aStar α₀ α
local notation "dualObjective" => intermediateProgramDualObjective h₀ h a₀ a α₀ α
local notation "dualFeasibleSet" => intermediateProgramDualFeasibleSet A₀Star AStar a₀Star aStar

-- Proof sketch: expand the canonical adjoint owner of
-- `H`. Minimizing first over the threshold variables forces
-- `u⋆ ≥ 0`; then substitute `q₀ = A₀ x + a₀ - p₀` and `qᵢ = Aᵢ x + aᵢ - pᵢ`, separate the
-- `x`-term from the `q`-terms, and identify the remaining infima with the relevant conjugate
-- values. The surviving feasibility condition is exactly
-- `dualFeasibleSet xStar`.
/-- Theorem 6.30.24: for the intermediate-program bifunction `H` coming from affine
representations `h₀(A₀ x + a₀) + ⟪x, a₀⋆⟫ₚ + α₀` and
`hᵢ(Aᵢ x + aᵢ) + ⟪x, aᵢ⋆⟫ₚ + αᵢ`, the adjoint value `H_{x⋆}⋆(w⋆)` is the negative of the
explicit dual objective minus the indicator of the dual feasible set. -/
theorem adjointFunction_intermediateProgramBifunction_apply
    (hA₀ :
      ∀ x : X, ∀ p₀Star : Y₀Star, ⟪A₀ x, p₀Star⟫ₚ = ⟪x, A₀Star p₀Star⟫ₚ)
    (hA :
      ∀ i : ι, ∀ x : X, ∀ pStar : YStar i, ⟪A i x, pStar⟫ₚ = ⟪x, AStar i pStar⟫ₚ)
    (xStar : XStar)
    (wStar : UStar) :
    H⋆ xStar wStar =
      -(dualObjective wStar) -
        δ[𝕜](wStar | dualFeasibleSet xStar) := sorry

-- Proof sketch: rewrite `adjointFunction_intermediateProgramBifunction_apply` by splitting on
-- membership in `dualFeasibleSet xStar`.
/-- Source case-split form of Theorem 6.30.24: the adjoint value is the negative of the explicit
dual objective on the dual feasible set, and `-∞` off that set. -/
theorem adjointFunction_intermediateProgramBifunction_apply_eq_ite
    (hA₀ :
      ∀ x : X, ∀ p₀Star : Y₀Star, ⟪A₀ x, p₀Star⟫ₚ = ⟪x, A₀Star p₀Star⟫ₚ)
    (hA :
      ∀ i : ι, ∀ x : X, ∀ pStar : YStar i, ⟪A i x, pStar⟫ₚ = ⟪x, AStar i pStar⟫ₚ)
    (xStar : XStar)
    (wStar : UStar) :
    H⋆ xStar wStar =
      if wStar ∈ dualFeasibleSet xStar then
        -(dualObjective wStar)
      else
        ⊥ := sorry

-- Proof sketch: specialize
-- `adjointFunction_intermediateProgramBifunction_apply_eq_ite` to `x⋆ = 0`. This is the zero
-- slice of the canonical adjoint owner defining the dual
-- program, so the surviving branch is exactly the explicit dual maximand under the source
-- feasibility constraints.
/-- The zero-slice specialization of the adjoint formula describes the dual program `(R⋆)`: the
dual data are feasible exactly when `u⋆ ≥ 0` and
`a₀⋆ + A₀⋆ p₀⋆ + ∑ᵢ (uᵢ⋆ aᵢ⋆ + Aᵢ⋆ pᵢ⋆) = 0`, and on that feasible set the dual program
maximizes `intermediateProgramDualObjective`, expressed on the theorem surface by the canonical
zero-slice owner of the adjoint bifunction. -/
theorem objective_adjointFunction_intermediateProgramBifunction_apply_eq_ite
    (hA₀ :
      ∀ x : X, ∀ p₀Star : Y₀Star, ⟪A₀ x, p₀Star⟫ₚ = ⟪x, A₀Star p₀Star⟫ₚ)
    (hA :
      ∀ i : ι, ∀ x : X, ∀ pStar : YStar i, ⟪A i x, pStar⟫ₚ = ⟪x, AStar i pStar⟫ₚ)
    (wStar : UStar) :
    (((H⋆ : XStar → UStar → WithBotTop 𝕜)₀) wStar) =
      if wStar ∈ dualFeasibleSet (0 : XStar) then
        -(dualObjective wStar)
      else
        ⊥ := sorry

end TheoremSurface

end

end Bifunction
