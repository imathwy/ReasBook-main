import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_12_0_1 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X Y : Type*}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]

variable [HasLinearPairing (X × 𝕜) (Y × 𝕜) 𝕜]

local notation "P" => X × 𝕜
local notation "D" => Y × 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Text 12.0.1 says that every closed half-space in coordinates `(x, μ)` is
  exactly one of the three textbook types from Definition 12.1: vertical, upper, or lower.
  In Lean this remains source-facing as a classification theorem on subsets of `X × 𝕜`.
- `core/canonical`: the owner abstraction for “closed half-space” is already Chapter 1’s
  predicate `IsClosedHalfSpace` on `Set P`, where `P = X × 𝕜`.
- `bridge/view`: the sign-of-`μStar` theorem is only a companion presentation lemma for a chosen
  normal form `closedHalfSpaceLE (yStar, μStar) α`; the main public theorem should bridge
  the owner predicate `IsClosedHalfSpace` to the Chapter 12 classification predicate
  `Set.IsVerticalUpperLowerClosedHalfSpace`.

Domain-style sampling used here:
- `IsClosedHalfSpace`;
- `Set.closedHalfSpaceLE_isClosedHalfSpace`;
- `closedHalfSpaceLE`;
- `Set.IsVerticalClosedHalfSpace`;
- `Set.IsUpperClosedHalfSpace`;
- `Set.IsLowerClosedHalfSpace`;
- the chapter predicate `Set.IsVerticalUpperLowerClosedHalfSpace`.

Primitive data vs derived API:
- primitive data: the Chapter 1 owner predicate `IsClosedHalfSpace` on `Set P`;
- derived API: the source-facing Chapter 12 trichotomy and the sign-based companion view for a
  chosen coordinate presentation of the normal.
-/

-- Proof sketch: classify according to the sign of `μStar`. If `μStar = 0`, the nontrivial-owner
-- hypothesis is already the vertical witness. If `μStar < 0`, divide the
-- defining inequality by `μStar` to rewrite the owner half-space as an upper half-space; if
-- `0 < μStar`, the same algebra yields a lower half-space. The three sign cases are pairwise
-- disjoint, so this gives the textbook classification directly on the owner
-- `closedHalfSpaceLE (yStar, μStar) α`.
/-- Text 12.0.1, stated on the pairing owner layer `P = X × 𝕜`, `D = Y × 𝕜`: every closed
half-space cut out by a nontrivial pairing linear functional inequality
`⟪(x, μ), bStar⟫ₚ ≤ α` falls into exactly one of the three textbook sign cases, according to the
sign of the scalar coordinate `bStar.2`. -/
theorem closedHalfSpaceLE_sign_cases
    (bStar : D) (α : 𝕜)
    (hflip : (HasLinearPairing.pairingLinear.flip bStar : P →ₗ[𝕜] 𝕜) ≠ 0) :
    (bStar.2 = 0 ∧
        verticalClosedHalfSpace[Y] (closedHalfSpaceLE bStar α : Set P)) ∨
      (bStar.2 < 0 ∧
        upperClosedHalfSpace[Y] (closedHalfSpaceLE bStar α : Set P)) ∨
      (0 < bStar.2 ∧
        lowerClosedHalfSpace[Y] (closedHalfSpaceLE bStar α : Set P)) := by
  rcases bStar with ⟨b, μ⟩
  by_cases hμ0 : μ = 0
  · refine Or.inl ⟨hμ0, ?_⟩
    refine ⟨b, α, ?_, ?_⟩
    · simpa [hμ0] using hflip
    · simp [hμ0]
  · rcases lt_or_gt_of_ne hμ0 with hμneg | hμpos
    · let c : 𝕜 := -μ⁻¹
      have hc_pos : 0 < c := by
        have hcinv_neg : μ⁻¹ < 0 := (inv_lt_zero).2 hμneg
        exact (neg_pos).2 hcinv_neg
      have hc_ne : c ≠ 0 := ne_of_gt hc_pos
      have hflipc :
          (HasLinearPairing.pairingLinear.flip (c • (((b : Y), μ) : D)) : P →ₗ[𝕜] 𝕜) ≠
            0 := by
        rw [show HasLinearPairing.pairingLinear.flip (c • (((b : Y), μ) : D)) =
            c • HasLinearPairing.pairingLinear.flip (((b : Y), μ) : D) by
            simpa using
              (HasLinearPairing.pairingLinear.flip.map_smul c (((b : Y), μ) : D))]
        exact smul_ne_zero hc_ne hflip
      have hcsnd : (c • (((b : Y), μ) : D) : D).2 = (-1 : 𝕜) := by
        have hμne : μ ≠ 0 := ne_of_lt hμneg
        simp [c, hμne]
      have hceq :
          (c • (((b : Y), μ) : D) : D) =
            ((((c • (((b : Y), μ) : D) : D).1 : Y), (-1 : 𝕜)) : D) := by
        ext
        · rfl
        · exact hcsnd
      have hflipc' :
          (HasLinearPairing.pairingLinear.flip
              ((((c • (((b : Y), μ) : D) : D).1 : Y), (-1 : 𝕜)) : D) : P →ₗ[𝕜] 𝕜) ≠
            0 := by
        rw [← hceq]
        exact hflipc
      have hscale :
          (closedHalfSpaceLE (((b : Y), μ) : D) α : Set P) =
            closedHalfSpaceLE (c • (((b : Y), μ) : D)) (c * α) := by
        ext x
        constructor
        · intro hx
          have hx_le : ⟪x, (((b : Y), μ) : D)⟫ₚ ≤ α := mem_closedHalfSpaceLE_iff.mp hx
          have hx_mul : c * ⟪x, (((b : Y), μ) : D)⟫ₚ ≤ c * α :=
            mul_le_mul_of_nonneg_left hx_le (le_of_lt hc_pos)
          have hx_pair : ⟪x, c • (((b : Y), μ) : D)⟫ₚ = c * ⟪x, (((b : Y), μ) : D)⟫ₚ := by
            simpa [smul_eq_mul] using
              (map_smul (HasLinearPairing.pairingLinear x) c (((b : Y), μ) : D))
          have hx_scaled : ⟪x, c • (((b : Y), μ) : D)⟫ₚ ≤ c * α := by
            calc
              ⟪x, c • (((b : Y), μ) : D)⟫ₚ = c * ⟪x, (((b : Y), μ) : D)⟫ₚ := hx_pair
              _ ≤ c * α := hx_mul
          exact mem_closedHalfSpaceLE_iff.mpr hx_scaled
        · intro hx
          have hx_le : ⟪x, c • (((b : Y), μ) : D)⟫ₚ ≤ c * α := mem_closedHalfSpaceLE_iff.mp hx
          have hx_pair : ⟪x, c • (((b : Y), μ) : D)⟫ₚ = c * ⟪x, (((b : Y), μ) : D)⟫ₚ := by
            simpa [smul_eq_mul] using
              (map_smul (HasLinearPairing.pairingLinear x) c (((b : Y), μ) : D))
          have hx_mul : c * ⟪x, (((b : Y), μ) : D)⟫ₚ ≤ c * α := by
            exact hx_pair.symm ▸ hx_le
          exact mem_closedHalfSpaceLE_iff.mpr (le_of_mul_le_mul_left hx_mul hc_pos)
      refine Or.inr <| Or.inl ⟨hμneg, ?_⟩
      refine ⟨(c • (((b : Y), μ) : D)).1, c * α, hflipc', ?_⟩
      calc
        (closedHalfSpaceLE (((b : Y), μ) : D) α : Set P) =
            closedHalfSpaceLE (c • (((b : Y), μ) : D)) (c * α) := hscale
        _ = closedHalfSpaceLE
              ((((c • (((b : Y), μ) : D) : D).1 : Y), (-1 : 𝕜)) : D) (c * α) := by
            rw [← hceq]
    · let c : 𝕜 := -μ⁻¹
      have hc_neg : c < 0 := neg_neg_of_pos ((inv_pos).2 hμpos)
      have hc_ne : c ≠ 0 := ne_of_lt hc_neg
      have hflipc :
          (HasLinearPairing.pairingLinear.flip (c • (((b : Y), μ) : D)) : P →ₗ[𝕜] 𝕜) ≠
            0 := by
        rw [show HasLinearPairing.pairingLinear.flip (c • (((b : Y), μ) : D)) =
            c • HasLinearPairing.pairingLinear.flip (((b : Y), μ) : D) by
            simpa using
              (HasLinearPairing.pairingLinear.flip.map_smul c (((b : Y), μ) : D))]
        exact smul_ne_zero hc_ne hflip
      have hcsnd : (c • (((b : Y), μ) : D) : D).2 = (-1 : 𝕜) := by
        have hμne : μ ≠ 0 := ne_of_gt hμpos
        simp [c, hμne]
      have hceq :
          (c • (((b : Y), μ) : D) : D) =
            ((((c • (((b : Y), μ) : D) : D).1 : Y), (-1 : 𝕜)) : D) := by
        ext
        · rfl
        · exact hcsnd
      have hflipc' :
          (HasLinearPairing.pairingLinear.flip
              ((((c • (((b : Y), μ) : D) : D).1 : Y), (-1 : 𝕜)) : D) : P →ₗ[𝕜] 𝕜) ≠
            0 := by
        rw [← hceq]
        exact hflipc
      have hscale :
          (closedHalfSpaceLE (((b : Y), μ) : D) α : Set P) =
            closedHalfSpaceGE (c • (((b : Y), μ) : D)) (c * α) := by
        ext x
        constructor
        · intro hx
          have hx_le : ⟪x, (((b : Y), μ) : D)⟫ₚ ≤ α := mem_closedHalfSpaceLE_iff.mp hx
          have hx_mul : c * α ≤ c * ⟪x, (((b : Y), μ) : D)⟫ₚ :=
            mul_le_mul_of_nonpos_left hx_le (le_of_lt hc_neg)
          have hx_pair : ⟪x, c • (((b : Y), μ) : D)⟫ₚ = c * ⟪x, (((b : Y), μ) : D)⟫ₚ := by
            simpa [smul_eq_mul] using
              (map_smul (HasLinearPairing.pairingLinear x) c (((b : Y), μ) : D))
          have hx_scaled : c * α ≤ ⟪x, c • (((b : Y), μ) : D)⟫ₚ := by
            calc
              c * α ≤ c * ⟪x, (((b : Y), μ) : D)⟫ₚ := hx_mul
              _ = ⟪x, c • (((b : Y), μ) : D)⟫ₚ := hx_pair.symm
          exact mem_closedHalfSpaceGE_iff.mpr hx_scaled
        · intro hx
          have hx_ge : c * α ≤ ⟪x, c • (((b : Y), μ) : D)⟫ₚ := mem_closedHalfSpaceGE_iff.mp hx
          have hx_pair : ⟪x, c • (((b : Y), μ) : D)⟫ₚ = c * ⟪x, (((b : Y), μ) : D)⟫ₚ := by
            simpa [smul_eq_mul] using
              (map_smul (HasLinearPairing.pairingLinear x) c (((b : Y), μ) : D))
          have hx_mul : c * α ≤ c * ⟪x, (((b : Y), μ) : D)⟫ₚ := by
            exact hx_pair ▸ hx_ge
          have hx_neg : -(c * ⟪x, (((b : Y), μ) : D)⟫ₚ) ≤ -(c * α) := neg_le_neg hx_mul
          have hx_posmul : (-c) * ⟪x, (((b : Y), μ) : D)⟫ₚ ≤ (-c) * α := by
            simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using hx_neg
          have hc_pos : 0 < -c := (neg_pos).2 hc_neg
          exact mem_closedHalfSpaceLE_iff.mpr (le_of_mul_le_mul_left hx_posmul hc_pos)
      refine Or.inr <| Or.inr ⟨hμpos, ?_⟩
      refine ⟨(c • (((b : Y), μ) : D)).1, c * α, hflipc', ?_⟩
      calc
        (closedHalfSpaceLE (((b : Y), μ) : D) α : Set P) =
            closedHalfSpaceGE (c • (((b : Y), μ) : D)) (c * α) := hscale
        _ = closedHalfSpaceGE
              ((((c • (((b : Y), μ) : D) : D).1 : Y), (-1 : 𝕜)) : D) (c * α) := by
            rw [← hceq]

/-- Text 12.0.1, owner-facing form for a fixed coordinate presentation: the half-space cut out by
`⟪(x, μ), bStar⟫ₚ ≤ α` is one of the three Chapter 12 types. The companion theorem
`closedHalfSpaceLE_sign_cases` retains the sign witness selecting the branch. -/
theorem closedHalfSpaceLE_isVerticalUpperLowerClosedHalfSpace
    (bStar : D) (α : 𝕜)
    (hflip : (HasLinearPairing.pairingLinear.flip bStar : P →ₗ[𝕜] 𝕜) ≠ 0) :
    verticalUpperLowerClosedHalfSpace[Y] (closedHalfSpaceLE bStar α : Set P) := by
  simpa using
    (closedHalfSpaceLE_sign_cases bStar α hflip).elim
      (fun h ↦ Or.inl h.2)
      (fun h ↦ Or.inr <| h.elim (fun h' ↦ Or.inl h'.2) (fun h' ↦ Or.inr h'.2))

private theorem closedHalfSpaceGE_eq_closedHalfSpaceLE_neg (b : D) (β : 𝕜) :
    (closedHalfSpaceGE b β : Set P) = closedHalfSpaceLE (((-1 : 𝕜) • b) : D) (-β) := by
  ext x
  constructor
  · intro hx
    have hx_ge : β ≤ ⟪x, b⟫ₚ := mem_closedHalfSpaceGE_iff.mp hx
    have hx_le : ⟪x, (((-1 : 𝕜) • b) : D)⟫ₚ ≤ -β := by
      simpa using (neg_le_neg hx_ge)
    exact mem_closedHalfSpaceLE_iff.mpr hx_le
  · intro hx
    have hx_le : ⟪x, (((-1 : 𝕜) • b) : D)⟫ₚ ≤ -β := mem_closedHalfSpaceLE_iff.mp hx
    have hx_ge : β ≤ ⟪x, b⟫ₚ := by
      exact neg_le_neg_iff.mp (by simpa using hx_le)
    exact mem_closedHalfSpaceGE_iff.mpr hx_ge

/-- Text 12.0.1, owner-facing form for a fixed right-oriented coordinate presentation: the
half-space cut out by `α ≤ ⟪(x, μ), bStar⟫ₚ` is one of the three Chapter 12 types. -/
theorem closedHalfSpaceGE_isVerticalUpperLowerClosedHalfSpace
    (bStar : D) (α : 𝕜)
    (hflip : (HasLinearPairing.pairingLinear.flip bStar : P →ₗ[𝕜] 𝕜) ≠ 0) :
    verticalUpperLowerClosedHalfSpace[Y] (closedHalfSpaceGE bStar α : Set P) := by
  have hle :
      verticalUpperLowerClosedHalfSpace[Y]
        (closedHalfSpaceLE (((-1 : 𝕜) • bStar) : D) (-α) : Set P) :=
    closedHalfSpaceLE_isVerticalUpperLowerClosedHalfSpace
      (((-1 : 𝕜) • bStar) : D) (-α) (by simpa using hflip)
  simpa [closedHalfSpaceGE_eq_closedHalfSpaceLE_neg] using hle

namespace Set

-- Proof sketch: unpack the Chapter 1 owner witness for `s`; in the `LE` branch apply the
-- left-oriented constructor bridge above, and in the `GE` branch apply the right-oriented bridge.
/-- Text 12.0.1 in owner form: every closed half-space in `P = X × 𝕜`, expressed canonically
through the Chapter 1 predicate `IsClosedHalfSpace`, is one of the three Chapter 12 types. The
sign-based coordinate presentation remains available as the companion theorem
`closedHalfSpaceLE_sign_cases`. -/
theorem IsClosedHalfSpace.isVerticalUpperLowerClosedHalfSpace {s : Set P}
    (hs : closedHalfSpace[D,𝕜] s) :
    verticalUpperLowerClosedHalfSpace[Y] s := by
  rcases hs with ⟨bStar, α, hflip, hsdef⟩
  rcases hsdef with rfl | rfl
  · exact closedHalfSpaceLE_isVerticalUpperLowerClosedHalfSpace bStar α hflip
  · exact closedHalfSpaceGE_isVerticalUpperLowerClosedHalfSpace bStar α hflip

/-- Text 12.0.1 at the canonical owner layer: for subsets of `P = X × 𝕜`, Chapter 1 closed
half-spaces are exactly the Chapter 12 vertical/upper/lower closed half-spaces. -/
theorem IsClosedHalfSpace.iff_verticalUpperLowerClosedHalfSpace {s : Set P} :
    (closedHalfSpace[D,𝕜] s) ↔ (verticalUpperLowerClosedHalfSpace[Y] s) := by
  constructor
  · exact IsClosedHalfSpace.isVerticalUpperLowerClosedHalfSpace
  · intro hs
    exact hs.isClosedHalfSpace

end Set

end
