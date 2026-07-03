import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_22_2_3 (from Chap04) -/
open scoped Rockafellar

section PairingOwner

variable {E : Type*} {Y : Type*} {R : Type*}
variable [AddGroup R] [Preorder R] [AddLeftMono R]
variable [AddGroup Y]
variable [HasPairing E Y R] [HasPairingNegRight E Y R] [HasPairingAddRight E Y R]

/-- Two-inequality weak-system owner used in Text 22.2.3:
`⟪x, -a⟫ₚ ≤ 0` and `⟪x, -b⟫ₚ ≤ 0`. -/
def twoConstraintSystem (R : Type*) [AddGroup R] [Preorder R] [AddLeftMono R]
    [HasPairing E Y R] [HasPairingNegRight E Y R] (a b : Y) : Set E :=
  (LinearConstraintRelation.leFeasible
    (X := E)
    (fun i : Bool ↦ if i then -b else -a)
    (fun _ : Bool ↦ (0 : R)))

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.2.3 states that two weak inequalities `⟪x, -a⟫ₚ ≤ 0`,
  `⟪x, -b⟫ₚ ≤ 0` imply `0 ≤ ⟪x, a + b⟫ₚ`.
- `core/canonical`: consequence is owner inclusion from the indexed weak feasible-set owner
  `LinearConstraintRelation.leFeasible` into the target half-space owner `closedHalfSpaceGE`.
- `bridge/view`: the Euclidean coordinate specialization (`R²`, `ξ₁`, `ξ₂`) appears below as a
  direct bridge theorem.

Domain-style sampling used here:
- `LinearConstraintRelation.leFeasible`;
- `is_linear_inequality_consequence_leFeasible_iff`;
- `closedHalfSpaceLE` / `closedHalfSpaceGE` with membership lemmas;
- pairing compatibility owners `HasPairingNegRight` and `HasPairingAddRight`.

Primitive data vs derived API:
- primitive data: two right-side vectors `a`, `b` and zero right-hand side;
- owner abstraction: `twoConstraintSystem R a b ⊆ closedHalfSpaceGE (a + b) 0`;
- derived bridge/view API: coordinatewise `R²` statement.

Layer target: `core/canonical` at the pairing owner layer.
-/

private theorem twoConstraintSystem_implies_nonpositive_neg_pairing_sum
    (a b : Y) (x : E)
    (hx : ∀ i : Bool, (⟪x, (if i then -b else -a)⟫ₚ : R) ≤ (0 : R)) :
    (⟪x, -(a + b)⟫ₚ : R) ≤ (0 : R) := by
  have ha : (0 : R) ≤ (⟪x, a⟫ₚ : R) := by
    simpa [HasPairingNegRight.pairing_neg_right] using hx false
  have hb : (0 : R) ≤ (⟪x, b⟫ₚ : R) := by
    simpa [HasPairingNegRight.pairing_neg_right] using hx true
  have hab : (0 : R) ≤ (⟪x, a⟫ₚ : R) + (⟪x, b⟫ₚ : R) := add_nonneg ha hb
  have hpair :
      (⟪x, -(a + b)⟫ₚ : R) = -((⟪x, a⟫ₚ : R) + (⟪x, b⟫ₚ : R)) := by
    calc
      (⟪x, -(a + b)⟫ₚ : R) = -((⟪x, a + b⟫ₚ : R)) := by
        simpa using (HasPairingNegRight.pairing_neg_right (x := x) (y := (a + b)))
      _ = -((⟪x, a⟫ₚ : R) + (⟪x, b⟫ₚ : R)) := by
        rw [HasPairingAddRight.pairing_add_right x a b]
  rw [hpair]
  exact neg_nonpos.mpr hab

-- Proof sketch: use `is_linear_inequality_consequence_leFeasible_iff` with target
-- `⟪x, -(a + b)⟫ₚ ≤ 0` to obtain owner inclusion into `closedHalfSpaceLE (-(a+b)) 0`, then
-- rewrite that owner back to `closedHalfSpaceGE (a + b) 0` via `pairing_neg_right`.
/-- Text 22.2.3, canonical owner form: the feasible set of the two weak inequalities
`⟪x, -a⟫ₚ ≤ 0`, `⟪x, -b⟫ₚ ≤ 0` is contained in the half-space `0 ≤ ⟪x, a + b⟫ₚ`. -/
theorem twoConstraintSystem_subset_sumNonnegativeHalfSpace
    (a b : Y) :
    twoConstraintSystem R a b ⊆
      (closedHalfSpaceGE (a + b) (0 : R) : Set E) := by
  have hsubsetLE :
      twoConstraintSystem R a b ⊆
        (closedHalfSpaceLE (-(a + b)) (0 : R) : Set E) :=
    (is_linear_inequality_consequence_leFeasible_iff
      (-(a + b)) (0 : R)
      (fun i : Bool ↦ if i then -b else -a)
      (fun _ : Bool ↦ (0 : R))).2
      (twoConstraintSystem_implies_nonpositive_neg_pairing_sum (a := a) (b := b))
  intro x hx
  have hxLE : (⟪x, -(a + b)⟫ₚ : R) ≤ (0 : R) := mem_closedHalfSpaceLE_iff.mp (hsubsetLE hx)
  have hxGE : (0 : R) ≤ (⟪x, a + b⟫ₚ : R) := by
    have hneg_pair : (⟪x, -(a + b)⟫ₚ : R) = -((⟪x, a + b⟫ₚ : R)) := by
      simpa using (HasPairingNegRight.pairing_neg_right (x := x) (y := a + b))
    rw [hneg_pair] at hxLE
    exact neg_nonpos.mp hxLE
  exact mem_closedHalfSpaceGE_iff.mpr hxGE

end PairingOwner

section EuclideanBridge

open scoped RealInnerProductSpace

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "e₁" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e₂" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

def coordinateNonnegativeSystem : Set R2 :=
  (LinearConstraintRelation.leFeasible
    (X := R2)
    (fun i : Bool ↦ if i then -e₂ else -e₁)
    (fun _ : Bool ↦ (0 : ℝ)))

def sumNonnegativeHalfSpace : Set R2 :=
  (closedHalfSpaceGE (e₁ + e₂) (0 : ℝ) : Set R2)

private theorem inner_e₁ (x : R2) : ⟪x, e₁⟫ = x 0 := by
  simpa using EuclideanSpace.inner_single_right (0 : Fin 2) (1 : ℝ) x

private theorem inner_e₂ (x : R2) : ⟪x, e₂⟫ = x 1 := by
  simpa using EuclideanSpace.inner_single_right (1 : Fin 2) (1 : ℝ) x

/-- Text 22.2.3, Euclidean bridge form: the feasible set of `ξ₁ ≥ 0`, `ξ₂ ≥ 0` is contained in
the half-space for `ξ₁ + ξ₂ ≥ 0`. -/
theorem coordinateNonnegativeSystem_subset_sumNonnegativeHalfSpace :
    coordinateNonnegativeSystem ⊆ sumNonnegativeHalfSpace := by
  simpa [coordinateNonnegativeSystem, sumNonnegativeHalfSpace, twoConstraintSystem] using
    (twoConstraintSystem_subset_sumNonnegativeHalfSpace
      (a := e₁) (b := e₂))

/-- Coordinate companion view of Text 22.2.3: every point of `R²` whose coordinates are
nonnegative satisfies `ξ₁ + ξ₂ ≥ 0`. -/
theorem nonnegative_coordinate_sum_of_coordinatewise_nonnegative
    (x : R2) (hx : ∀ i : Fin 2, (0 : ℝ) ≤ x i) :
    (0 : ℝ) ≤ x 0 + x 1 := by
  have hx_mem : x ∈ coordinateNonnegativeSystem := by
    rw [coordinateNonnegativeSystem, LinearConstraintRelation.mem_leFeasible]
    intro i
    cases i with
    | false =>
        have hx0' : (0 : ℝ) ≤ ⟪x, e₁⟫ := by
          simpa [inner_e₁ x] using (hx 0)
        simpa [inner_neg_right] using (neg_nonpos.mpr hx0')
    | true =>
        have hx1' : (0 : ℝ) ≤ ⟪x, e₂⟫ := by
          simpa [inner_e₂ x] using (hx 1)
        simpa [inner_neg_right] using (neg_nonpos.mpr hx1')
  have hsum_mem := coordinateNonnegativeSystem_subset_sumNonnegativeHalfSpace hx_mem
  have hsum : (0 : ℝ) ≤ ⟪x, e₁ + e₂⟫ := mem_closedHalfSpaceGE_iff.mp hsum_mem
  simpa [inner_add_right, inner_e₁ x, inner_e₂ x] using hsum

end EuclideanBridge
