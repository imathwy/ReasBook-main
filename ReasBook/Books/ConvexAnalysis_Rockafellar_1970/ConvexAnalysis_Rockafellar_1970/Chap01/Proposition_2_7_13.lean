import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_11

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {R : Type w} [Mul R] [Zero R] [Preorder R] [PosMulMono R]
variable {M : Type u} {N : Type v}
variable [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.7.13 states that the barrier cone is a convex cone.
- `core/canonical`: the source-facing owner is the set-level barrier predicate
  `barr[R](C)`.
- `bridge/view`: the closure properties are proved directly from the membership bridge
  `mem_barrier_iff_exists_bound`, so the proposition works directly at the source-facing
  set-owner layer.
- Primitive data vs derived API: boundedness witnesses in `R` are primitive owner data; cone and
  convex closure are derived by transporting those witnesses through positive scaling and convex
  combinations.
-/

/-- Proposition 2.7.13, set-level cone form: the barrier cone is a cone. -/
theorem barrierCone_isCone (C : Set M) :
    Set.IsCone R (barr[R](C) : Set N) := by
  refine (Set.isCone_iff_forall_pos_smul_subset (K := (barr[R](C) : Set N))).2 ?_
  intro c hc xStar hxStar
  rcases Set.mem_smul_set.mp hxStar with ⟨yStar, hyStar, rfl⟩
  rw [mem_barrier_iff_exists_bound] at hyStar ⊢
  rcases hyStar with ⟨β, hβ⟩
  refine ⟨c * β, ?_⟩
  intro x hxC
  rw [pairing_smul_right]
  exact mul_le_mul_of_nonneg_left (hβ x hxC) (le_of_lt hc)

end

section

universe u v w

variable {R : Type w} [Semiring R] [PartialOrder R] [PosMulMono R] [AddLeftMono R]
variable {M : Type u} {N : Type v}
variable [AddCommMonoid N] [SMul R N]
variable [HasPairing M N R]
variable [HasPairingSMulRight M N R]
variable [HasPairingAddRight M N R]

open scoped Rockafellar

/-- Proposition 2.7.13, set-level convexity form: the barrier cone is convex. -/
theorem barrierCone_convex (C : Set M) :
    Convex R (barr[R](C) : Set N) := by
  refine convex_iff_add_mem.2 ?_
  intro xStar hxStar yStar hyStar a b ha hb hab
  rw [mem_barrier_iff_exists_bound] at hxStar hyStar ⊢
  rcases hxStar with ⟨βx, hβx⟩
  rcases hyStar with ⟨βy, hβy⟩
  refine ⟨a * βx + b * βy, ?_⟩
  intro x hxC
  have hxle : (⟪x, xStar⟫ₚ : R) ≤ βx := hβx x hxC
  have hyle : (⟪x, yStar⟫ₚ : R) ≤ βy := hβy x hxC
  have hpair :
      (⟪x, a • xStar + b • yStar⟫ₚ : R) =
        a * (⟪x, xStar⟫ₚ : R) + b * (⟪x, yStar⟫ₚ : R) := by
    calc
      (⟪x, a • xStar + b • yStar⟫ₚ : R)
          = (⟪x, a • xStar⟫ₚ : R) + (⟪x, b • yStar⟫ₚ : R) := by
              exact HasPairingAddRight.pairing_add_right x (a • xStar) (b • yStar)
      _ = a * (⟪x, xStar⟫ₚ : R) + b * (⟪x, yStar⟫ₚ : R) := by
            rw [pairing_smul_right, pairing_smul_right]
  refine hpair ▸ add_le_add ?_ ?_
  · exact mul_le_mul_of_nonneg_left hxle ha
  · exact mul_le_mul_of_nonneg_left hyle hb

/-- Proposition 2.7.13 in canonical source-facing owner form: the barrier cone is a convex cone. -/
theorem barrierCone_isConvexCone (C : Set M) :
    Set.IsConvexCone R (barr[R](C) : Set N) :=
  ⟨barrierCone_isCone C, barrierCone_convex C⟩

end
