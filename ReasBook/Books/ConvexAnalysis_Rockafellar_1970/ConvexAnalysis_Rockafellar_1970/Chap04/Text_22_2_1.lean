import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

section BridgeLayer

variable {E : Type*} {Y : Type*} {R : Type*}
variable [LE R] [HasPairing E Y R]
variable {m : ℕ}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 22.2.1 isolates the weak subsystem indexed by `i = k + 1, …, m` and keeps
  the same Farkas alternative on that block.
- `core/canonical`: the feasibility owner is the chapter weak-inequality owner
  `linearInequalitySolutionSet`, and the block index is intrinsically the subtype
  `{i : Fin m // k ≤ i.1}`.
- `bridge/view`: the textbook blockwise pointwise feasibility clause is recovered directly from
  owner membership on the indexed range system.

Domain-style sampling used here:
- `linearInequalitySolutionSet` and `mem_linearInequalitySolutionSet_range_iff` from
  `Chap04.Definition_17_2_4`.

Primitive data vs derived API:
- primitive inputs: a finite coefficient family `a : Fin m → Y`, right-hand side `α : Fin m → R`,
  and cut index `k`;
- owner object:
  `linearInequalitySolutionSet (Set.range (fun i : {i : Fin m // k ≤ i.1} ↦ (a i, α i)))`;
- derived API: the textbook blockwise pointwise inequality view.

Layer target: keep this bridge at the primitive pairing/order owner layer.
-/

/-- The second-block owner weak-system set is nonempty exactly when the displayed subsystem has a
solution. -/
theorem second_block_linearInequalitySolutionSet_nonempty_iff
    (k : ℕ) (a : Fin m → Y) (α : Fin m → R) :
    (linearInequalitySolutionSet
      (Set.range fun i : {i : Fin m // k ≤ i.1} ↦ (a i, α i)) : Set E).Nonempty ↔
      ∃ x : E, ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_linearInequalitySolutionSet_range_iff] at hx
    intro i hi
    exact hx ⟨i, hi⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_linearInequalitySolutionSet_range_iff]
    intro i
    exact hx i i.2

end BridgeLayer

section FarkasAlternative

variable {E : Type*} {Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {m : ℕ}

/-!
Ambient-layer note for this file:
- `second_block_linearInequalitySolutionSet_nonempty_iff` above lives at the primitive pairing
  layer `[LE R] [HasPairing E Y R]`.
- The three Farkas-alternative theorems below are imported specializations of the pairing-owner
  form in `Chap04.Theorem_22_1`; they therefore inherit its ambient assumptions.
-/

/-- Text 22.2.1 in owner form: for the weak subsystem `⟪x, aᵢ⟫ₚ ≤ αᵢ` on the intrinsic block
`{i : Fin m // k ≤ i.1}`, exactly one of the two Farkas alternatives holds. -/
theorem
    xor_second_block_solutionSet_nonempty_or_weak_linear_inequality_farkas_certificate
    (k : ℕ) (a : Fin m → Y) (α : Fin m → ℝ) :
    Xor'
      (linearInequalitySolutionSet
        (Set.range fun i : {i : Fin m // k ≤ i.1} ↦ (a i, α i)) : Set E).Nonempty
      (∃ w : {i : Fin m // k ≤ i.1} → ℝ,
        (∀ i : {i : Fin m // k ≤ i.1}, 0 ≤ w i) ∧
          (∀ x : E,
            (∑ i : {i : Fin m // k ≤ i.1}, w i * (⟪x, a i⟫ₚ : ℝ)) = 0) ∧
            (∑ i : {i : Fin m // k ≤ i.1}, w i * α i) < 0) := by
  simpa [Set.Nonempty, mem_linearInequalitySolutionSet_range_iff] using
    (xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate
      (E := E) (Y := Y)
      (I := {i : Fin m // k ≤ i.1})
      (a := fun i : {i : Fin m // k ≤ i.1} ↦ a i)
      (α := fun i : {i : Fin m // k ≤ i.1} ↦ α i))

/-- Text 22.2.1 pointwise form: for the weak subsystem `⟪x, aᵢ⟫ₚ ≤ αᵢ` indexed by
`i = k + 1, …, m`, exactly one of the following holds: either the subsystem has a solution `x ∈ E`,
or there is a nonnegative multiplier family on the intrinsic second-block index type
`{i : Fin m // k ≤ i.1}` whose weighted pairing sums vanish pointwise and whose weighted constants
sum to a negative number. -/
theorem xor_exists_second_block_feasible_point_or_weak_linear_inequality_farkas_certificate
    (k : ℕ) (a : Fin m → Y) (α : Fin m → ℝ) :
    Xor'
      (∃ x : E,
        ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i)
      (∃ w : {i : Fin m // k ≤ i.1} → ℝ,
        (∀ i : {i : Fin m // k ≤ i.1}, 0 ≤ w i) ∧
          (∀ x : E,
            (∑ i : {i : Fin m // k ≤ i.1}, w i * (⟪x, a i⟫ₚ : ℝ)) = 0) ∧
            (∑ i : {i : Fin m // k ≤ i.1}, w i * α i) < 0) := by
  let pOwner : Prop :=
    (linearInequalitySolutionSet
      (Set.range fun i : {i : Fin m // k ≤ i.1} ↦ (a i, α i)) : Set E).Nonempty
  let pPointwise : Prop :=
    ∃ x : E, ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i
  let q : Prop :=
    ∃ w : {i : Fin m // k ≤ i.1} → ℝ,
      (∀ i : {i : Fin m // k ≤ i.1}, 0 ≤ w i) ∧
        (∀ x : E,
          (∑ i : {i : Fin m // k ≤ i.1}, w i * (⟪x, a i⟫ₚ : ℝ)) = 0) ∧
          (∑ i : {i : Fin m // k ≤ i.1}, w i * α i) < 0
  have hOwner : Xor' pOwner q := by
    simpa [pOwner, q] using
      xor_second_block_solutionSet_nonempty_or_weak_linear_inequality_farkas_certificate
        (E := E) (Y := Y) k a α
  have hPointwise : pOwner ↔ pPointwise := by
    simpa [pOwner, pPointwise] using
      (second_block_linearInequalitySolutionSet_nonempty_iff
        (E := E) (Y := Y) (R := ℝ) k a α)
  have hnotiff : ¬ (pPointwise ↔ q) := by
    intro hiff
    have hOwner_iff : pOwner ↔ q := hPointwise.trans hiff
    exact ((xor_iff_not_iff _ _).1 hOwner) hOwner_iff
  exact (xor_iff_not_iff _ _).2 hnotiff

/-- The second weak block is infeasible exactly when it admits a nonnegative Farkas certificate
with vanishing weighted pairing sums and strictly negative weighted scalar sum. -/
theorem not_exists_second_block_feasible_point_iff_exists_weak_linear_inequality_farkas_certificate
    (k : ℕ) (a : Fin m → Y) (α : Fin m → ℝ) :
    (¬ ∃ x : E,
      ∀ i : Fin m, k ≤ i.1 → ⟪x, a i⟫ₚ ≤ α i) ↔
      ∃ w : {i : Fin m // k ≤ i.1} → ℝ,
        (∀ i : {i : Fin m // k ≤ i.1}, 0 ≤ w i) ∧
          (∀ x : E,
            (∑ i : {i : Fin m // k ≤ i.1}, w i * (⟪x, a i⟫ₚ : ℝ)) = 0) ∧
            (∑ i : {i : Fin m // k ≤ i.1}, w i * α i) < 0 := by
  exact
    (xor_iff_not_iff').mp
      (xor_exists_second_block_feasible_point_or_weak_linear_inequality_farkas_certificate
        (E := E) (Y := Y) k a α)

end FarkasAlternative
