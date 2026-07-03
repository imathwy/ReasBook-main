import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_17_2_12 (from Chap04) -/
section

open scoped BigOperators Rockafellar

variable {X Y : Type*}
  {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup X] [Module R X]
  [AddCommMonoid Y] [Module R Y]
  [HasPairing X Y R]
  [HasPairingAddRight X Y R]
  [HasPairingSMulRight X Y R]

local notation "YStar" => Y × R
local notation "solutionSet[" SStar "]" =>
  linearInequalitySolutionSet (E := X) (SStar : Set YStar)
local notation "halfSpace[" yStar ", " μStar "]" =>
  (closedHalfSpaceLE yStar μStar : Set X)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.2.12 rewrites the containing-half-space condition from
  Theorem 17.2.11 as containment of the intersection of a finite subsystem of at most
  `Module.finrank R X` half-spaces coming from points of `S*`.
- `core/canonical`: the owner abstractions are `linearInequalitySolutionSet SStar`,
  `linearInequalitySolutionSet s`, `closedHalfSpaceLE`, and the upstream owner
  theorems `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate` and
  `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination`.
- `bridge/view`: the corollary keeps the same half-space containment from Theorem 17.2.11 and
  replaces the finite conic-combination certificate on a selected finite set `s` by the induced
  finite subsystem `linearInequalitySolutionSet s`, whose source-facing
  presentation is the intersection of the corresponding selected half-spaces.

Domain-style sampling used here:
- `linearInequalitySolutionSet` from `Chap04.Definition_17_2_4`;
- `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate` from
  `Chap04.Theorem_17_2_11`;
- `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination` from
  `Chap04.Theorem_17_2_11`;
- `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `linear_constraint_solution_set` from `Chap01.Corollary_2_1_2`, through the owner
  `linearInequalitySolutionSet`.

Primitive data vs derived API:
- primitive source-facing data: the inequality family `SStar`, the target half-space
  `closedHalfSpaceLE yStar μStar`, and the selected finite subsystem `s`;
- derived API: the subsystem containment extracted from the finite nonnegative certificate already
  provided canonically by
  `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination`.

Layer target: `bridge/view`.
-/

-- Proof sketch: for `(→)`, apply the companion theorem
-- `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination` from Theorem 17.2.11
-- to obtain a finite subset `s ⊆ SStar` of size at most `Module.finrank R X` together with a
-- finite nonnegative certificate on `s`. That certificate implies that every point of
-- `linearInequalitySolutionSet s` satisfies the target inequality. For `(←)`, every point of
-- `linearInequalitySolutionSet SStar` satisfies each inequality in `s` because `s ⊆ SStar`, so
-- the assumed subsystem containment yields the target
-- containment.

omit [AddCommGroup X] [Module R X] in
private theorem subsystem_subset_closedHalfSpaceLE_of_conicCombination
    {s : Finset YStar} {yStar : Y} {μStar : R} {weights : {y // y ∈ s} → R}
    (hnonneg : ∀ y, 0 ≤ weights y)
    (hvector : yStar = s.attach.sum (fun y ↦ weights y • (y : YStar).1))
    (hscalar : s.attach.sum (fun y ↦ weights y * (y : YStar).2) ≤ μStar) :
    solutionSet[s] ⊆ halfSpace[yStar, μStar] := by
  intro x hx
  rw [mem_closedHalfSpaceLE_iff]
  have hx_points : ∀ y : {z // z ∈ s}, ⟪x, (y : YStar).1⟫ₚ ≤ (y : YStar).2 := fun y ↦
    (mem_linearInequalitySolutionSet_iff.mp hx) y y.2
  have hsum :
      s.attach.sum (fun y ↦ weights y * ⟪x, (y : YStar).1⟫ₚ) ≤
        s.attach.sum (fun y ↦ weights y * (y : YStar).2) := by
    exact Finset.sum_le_sum fun y _ ↦
      mul_le_mul_of_nonneg_left (hx_points y) (hnonneg y)
  have hpair_sum :
      (⟪x, s.attach.sum (fun y ↦ weights y • (y : YStar).1)⟫ₚ : R) =
        s.attach.sum (fun y ↦ weights y * ⟪x, (y : YStar).1⟫ₚ) := by
    classical
    induction s.attach using Finset.induction_on with
    | empty =>
        simpa using (pairing_smul_right (x := x) (c := (0 : R)) (y := (0 : Y)))
    | @insert y t hy ht =>
        simp [Finset.sum_insert, hy, HasPairingAddRight.pairing_add_right, pairing_smul_right, ht]
  have hyStar_eq :
      (⟪x, yStar⟫ₚ : R) = s.attach.sum (fun y ↦ weights y * ⟪x, (y : YStar).1⟫ₚ) := by
    calc
      (⟪x, yStar⟫ₚ : R) = (⟪x, s.attach.sum (fun y ↦ weights y • (y : YStar).1)⟫ₚ : R) := by
        rw [hvector]
      _ = s.attach.sum (fun y ↦ weights y * ⟪x, (y : YStar).1⟫ₚ) := hpair_sum
  calc
    (⟪x, yStar⟫ₚ : R) = s.attach.sum (fun y ↦ weights y * ⟪x, (y : YStar).1⟫ₚ) := hyStar_eq
    _ ≤ s.attach.sum (fun y ↦ weights y * (y : YStar).2) := hsum
    _ ≤ μStar := hscalar

/-- Corollary 17.2.12: under the hypotheses of Theorem 17.2.11, the containment of
`linearInequalitySolutionSet SStar` in `closedHalfSpaceLE yStar μStar` is equivalent to the
existence of a finite subsystem `s : Finset (Y × R)` of at most `Module.finrank R X` inequalities
drawn from `SStar` whose induced owner set, equivalently the intersection of the corresponding
half-spaces, is contained in `closedHalfSpaceLE yStar μStar`. -/
theorem dualCaratheodory_subset_closedHalfSpaceLE_iff_exists_n_halfspaces_intersection_subset
    -- These ambient assumptions are local to this bridge theorem and enter only through
    -- `IsClosed`/`Bornology.IsBounded` hypotheses and Theorem 17.2.11.
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      ∃ s : Finset YStar, s.card ≤ Module.finrank R X ∧
        (∀ y ∈ s, y ∈ SStar) ∧
          solutionSet[s] ⊆ halfSpace[yStar, μStar] := by
  constructor
  · intro hsubset
    rcases
      (subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination
        hSStar_closed hSStar_bounded hfull yStar μStar).mp hsubset with
      ⟨s, hcard, hs, weights, hnonneg, hvector, hscalar⟩
    refine ⟨s, hcard, hs, ?_⟩
    exact
      subsystem_subset_closedHalfSpaceLE_of_conicCombination
        hnonneg hvector hscalar
  · rintro ⟨s, -, hs, hsubset⟩ x hx
    exact hsubset <| by
      rw [mem_linearInequalitySolutionSet_iff] at hx ⊢
      intro y hy
      exact hx y (hs y hy)

end
