import Mathlib
import Nesterov.Chap03.Definition_3_9
import Nesterov.Chap07.Definition_7_7
import Nesterov.Chap07.Definition_7_84

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped SupportFunction

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Lemma 7.1 lies in the finite-range support-function / pullback-seminorm domain.

Sampled owner declarations:
- `ξ[Q]` and `supportFunction_apply` from `Chap03/Definition_3_9`
- `Seminorm.comp` and `normSeminorm` for canonical pullback seminorms
- `LinearMap.pi` and `EuclideanSpace.equiv` for the canonical finite row map into
  `EuclideanSpace ℝ (Fin m)`
- `SatisfiesAsphericityCondition` from `Chap07/Definition_7_7`
- `Seminorm.IsNorm` from `Chap02/Definition_2_5`, recalled in `Chap07/Definition_7_84`

Best owner abstraction:
- source-facing: the Chapter 3 support function `ξ[Set.range a]` and the Euclidean pullback
  seminorm attached to the finite row family `a`
- core/canonical: `ξ[Set.range a]`, `Seminorm.comp`, `LinearMap.pi`, and `EuclideanSpace.equiv`
- bridge/view: the concrete `sSup` and `sqrt` evaluation formulas below

Primitive data:
- a finite family `a : Fin m → E`

Derived API kept here:
- the finite-range evaluation of the support function
- the coordinate formula for the canonical pullback seminorm
- the norm / asphericity statement of Lemma 7.1

This refinement removes the previous public convenience owners
`polyhedralMaxFunction`, `rowInnerMap`, and `rowInnerSeminorm`. The public surface is stated
directly with the established Chapter 3 support-function owner and the canonical pullback-seminorm
construction instead of parallel wrapper names.
-/

section

variable (a : Fin m → E)

/-- Evaluating the Chapter 3 support-function owner on the finite set `Set.range a` recovers the
supremum of the finitely many inner products `⟪aᵢ, x⟫`. -/
theorem supportFunction_range_toReal_eq_sSup_inner (x : E) :
    (ξ[Set.range a] x).toReal = sSup (Set.range fun i : Fin m ↦ inner ℝ (a i) x) := sorry

-- Proof sketch: rewrite the pullback seminorm as the Euclidean norm of the finite row map
-- `((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
--   (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap)` applied to `x`, then expand the
-- Euclidean norm coordinatewise.
/-- The canonical Euclidean pullback seminorm attached to `a` evaluates to the square root of the
summed squared inner products `∑ i ⟪aᵢ, x⟫²`. -/
theorem pullbackSeminorm_eq_sqrt_sum_inner_sq (x : E) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))
    p x =
      Real.sqrt (∑ i : Fin m, (inner ℝ (a i) x) ^ 2) := sorry

-- Proof sketch: prove definiteness of the pullback seminorm from the spanning hypothesis
-- `span ℝ (range a) = ⊤`, identify
-- `∂ (fun x ↦ (ξ[Set.range a] x).toReal) (0)` with
-- `convexHull ℝ (Set.range fun i ↦ (InnerProductSpace.toDual ℝ E) (a i))`, and then derive the
-- two `Definition_7_7` dual-ball inclusions using the convex-combination estimate and the
-- zero-sum estimate from the textbook proof.
/-- Lemma 7.1: if the family `a` has full row rank, encoded by
`Submodule.span ℝ (Set.range a) = ⊤`, has at least two elements, and satisfies `∑ i, a i = 0`,
then the canonical pullback seminorm
`x ↦ (∑ i ⟪aᵢ, x⟫²)^(1/2)` is a norm and the subdifferential at `0` of the Chapter 3 support
function `x ↦ (ξ[Set.range a] x).toReal` satisfies the asphericity condition with `γ₁ = 1` and
`γ₀ = 1 / √(m (m - 1))`. -/
theorem supportFunction_range_toReal_norm_and_asphericity
    (hm : 2 ≤ m) (hfull_row_rank : Submodule.span ℝ (Set.range a) = ⊤)
    (hzero_sum : ∑ i : Fin m, a i = 0) :
    let p : Seminorm ℝ E :=
      Seminorm.comp
        (normSeminorm ℝ (EuclideanSpace ℝ (Fin m)))
        (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
          (LinearMap.pi fun i ↦ (innerSL ℝ (a i)).toLinearMap))
    Seminorm.IsNorm p ∧
      SatisfiesAsphericityCondition
        (fun x ↦ (ξ[Set.range a] x).toReal)
        p
        (1 / Real.sqrt ((m : ℝ) * (m - 1 : ℝ))) 1 := sorry

end
