import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open Metric
open scoped Pointwise Rockafellar

section

variable {P : Type*} [PseudoMetricSpace P]

/-- The witness-set neighborhood `{x | ∃ y ∈ C, dist x y ≤ ε}` is exactly the union of the
closed balls of radius `ε` centered at points of `C`. -/
theorem points_within_distance_le_eq_iUnion_closedBall (C : Set P) (ε : ℝ) :
    {x : P | ∃ y ∈ C, dist x y ≤ ε} = ⋃ y ∈ C, closedBall y ε := by
  ext x
  simp [mem_closedBall]

end

section

variable {E : Type*} [PseudoMetricSpace E] [AddGroup E] [IsIsometricVAdd E E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.6 identifies the radius-`ε` neighborhood of a set `C` with a
  pointwise-set sum.
- `core/canonical`: before introducing any normed-space-specific bridge, the intrinsic owner level
  is metric witness neighborhoods and translated closed balls:
  `{x | ∃ y ∈ C, dist x y ≤ ε} = C +ᵥ closedBall 0 ε`.
- `bridge/view`: in real normed spaces, Text 6.5 upgrades `closedBall 0 ε` to `ε • B`,
  giving the textbook `C + ε • B` surface.
- `bridge/view` sampled but not adopted as the main owner: `Metric.cthickening ε C` and the
  compact/proper-space bridges `Metric.IsCompact.cthickening_eq_biUnion_closedBall` and
  `Metric.cthickening_eq_biUnion_closedBall`. They describe closed thickenings via
  infimum distance, which is stronger than the source-facing existential witness set when the
  nearest point need not be attained.
- Primitive data vs derived API: the primitive data are the set `C`, radius `ε`, and the additive
  action/translation structure; `C + closedBall 0 ε` and `C + ε • B` are derived additive views.
- Domain-style sampling: `closedBall_eq_vadd_closedBall_zero` and `Metric.mem_closedBall`.
- Layer target: expose the intrinsic owner theorem
  `points_within_distance_le_eq_vadd_closedBall_zero` first, then derive additive surfaces.
-/

/-- Intrinsic owner theorem for Text 6.6: the union of radius-`ε` closed balls centered at points
of `C` is exactly the additive-action translate `C +ᵥ closedBall 0 ε`. -/
theorem iUnion_closedBall_eq_vadd_closedBall_zero (C : Set E) (ε : ℝ) :
    (⋃ y ∈ C, closedBall y ε) = C +ᵥ closedBall (0 : E) ε := by
  calc
    (⋃ y ∈ C, closedBall y ε) = ⋃ y ∈ C, y +ᵥ closedBall (0 : E) ε := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion₂.mp hx with ⟨y, hyC, hxBall⟩
        have hxVadd : x ∈ y +ᵥ closedBall (0 : E) ε := by
          rw [← closedBall_eq_vadd_closedBall_zero (a := y) (ε := ε)]
          exact hxBall
        exact Set.mem_iUnion₂.mpr ⟨y, hyC, hxVadd⟩
      · intro hx
        rcases Set.mem_iUnion₂.mp hx with ⟨y, hyC, hxVadd⟩
        have hxBall : x ∈ closedBall y ε := by
          rw [← closedBall_eq_vadd_closedBall_zero (a := y) (ε := ε)] at hxVadd
          exact hxVadd
        exact Set.mem_iUnion₂.mpr ⟨y, hyC, hxBall⟩
    _ = Set.image2 (fun y z : E ↦ y +ᵥ z) C (closedBall (0 : E) ε) := by
      simpa using
        (Set.iUnion_image_left
          (f := fun y z : E ↦ y +ᵥ z)
          (s := C) (t := closedBall (0 : E) ε))
    _ = C +ᵥ closedBall (0 : E) ε := by
      simp

/-- Additive bridge for Text 6.6: rewriting the intrinsic `+ᵥ` owner gives the pointwise-set sum
surface `C + closedBall 0 ε`. -/
theorem iUnion_closedBall_eq_add_closedBall_zero (C : Set E) (ε : ℝ) :
    (⋃ y ∈ C, closedBall y ε) = C + closedBall (0 : E) ε := by
  simpa [vadd_eq_add] using iUnion_closedBall_eq_vadd_closedBall_zero (C := C) ε

/-- Intrinsic Text 6.6 statement: points within distance `ε` from `C` form
`C +ᵥ closedBall 0 ε`. -/
theorem points_within_distance_le_eq_vadd_closedBall_zero (C : Set E) (ε : ℝ) :
    {x : E | ∃ y ∈ C, dist x y ≤ ε} = C +ᵥ closedBall (0 : E) ε := by
  calc
    {x : E | ∃ y ∈ C, dist x y ≤ ε} = ⋃ y ∈ C, closedBall y ε := by
      simpa using points_within_distance_le_eq_iUnion_closedBall (C := C) ε
    _ = C +ᵥ closedBall (0 : E) ε := by
      simpa using iUnion_closedBall_eq_vadd_closedBall_zero (C := C) ε

/-- Additive bridge for Text 6.6: points within distance `ε` from `C` form
`C + closedBall 0 ε`. -/
theorem points_within_distance_le_eq_add_closedBall_zero (C : Set E) (ε : ℝ) :
    {x : E | ∃ y ∈ C, dist x y ≤ ε} = C + closedBall (0 : E) ε := by
  simpa [vadd_eq_add] using points_within_distance_le_eq_vadd_closedBall_zero (C := C) ε

end

section

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
the union of closed balls centered at points of `C` with radius `‖u‖` is `C + u • B`,
with invertibility carried intrinsically by the unit `u : 𝕜ˣ`. -/
theorem iUnion_closedBall_norm_eq_add_smul_unitClosedBall_unit
    (C : Set E) (u : 𝕜ˣ) :
    (⋃ y ∈ C, closedBall y ‖(u : 𝕜)‖) = C + (u : 𝕜) • B := by
  calc
    (⋃ y ∈ C, closedBall y ‖(u : 𝕜)‖) = C + closedBall (0 : E) ‖(u : 𝕜)‖ := by
      simpa using iUnion_closedBall_eq_add_closedBall_zero (C := C) ‖(u : 𝕜)‖
    _ = C + (u : 𝕜) • B := by
      have hball : closedBall (0 : E) ‖(u : 𝕜)‖ = (u : 𝕜) • B := by
        simpa using
          (closedBall_eq_add_smul_unitClosedBall_unit (a := (0 : E)) (u := u))
      simp [hball]

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
the union of closed balls centered at points of `C` with radius `‖c‖` is `C + c • B`. -/
theorem iUnion_closedBall_norm_eq_add_smul_unitClosedBall_of_ne_zero
    (C : Set E) (c : 𝕜) (hc : c ≠ 0) :
    (⋃ y ∈ C, closedBall y ‖c‖) = C + c • B := by
  let u : 𝕜ˣ := ⟨c, c⁻¹, by simp [hc], by simp [hc]⟩
  simpa [u] using iUnion_closedBall_norm_eq_add_smul_unitClosedBall_unit (C := C) u

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
points lying within distance at most `‖u‖` of `C` are exactly `C + u • B`,
with invertibility carried intrinsically by the unit `u : 𝕜ˣ`. -/
theorem points_within_distance_le_norm_eq_add_smul_unitClosedBall_unit
    (C : Set E) (u : 𝕜ˣ) :
    {x : E | ∃ y ∈ C, dist x y ≤ ‖(u : 𝕜)‖} = C + (u : 𝕜) • B := by
  calc
    {x : E | ∃ y ∈ C, dist x y ≤ ‖(u : 𝕜)‖} = ⋃ y ∈ C, closedBall y ‖(u : 𝕜)‖ := by
      simpa using points_within_distance_le_eq_iUnion_closedBall (C := C) ‖(u : 𝕜)‖
    _ = C + (u : 𝕜) • B := by
      simpa using iUnion_closedBall_norm_eq_add_smul_unitClosedBall_unit (C := C) u

/-- Text 6.6 (canonical scalar-generic owner, nonzero radius witness):
points lying within distance at most `‖c‖` of `C` are exactly `C + c • B`. -/
theorem points_within_distance_le_norm_eq_add_smul_unitClosedBall_of_ne_zero
    (C : Set E) (c : 𝕜) (hc : c ≠ 0) :
    {x : E | ∃ y ∈ C, dist x y ≤ ‖c‖} = C + c • B := by
  let u : 𝕜ˣ := ⟨c, c⁻¹, by simp [hc], by simp [hc]⟩
  simpa [u] using points_within_distance_le_norm_eq_add_smul_unitClosedBall_unit (C := C) u

/-- Text 6.6 (canonical scalar-generic owner):
the union of closed balls centered at points of `C` with radius `‖c‖` is exactly `C + c • B`;
the endpoint `c = 0` uses `T1Space`. -/
theorem iUnion_closedBall_norm_eq_add_smul_unitClosedBall
    [T1Space E] (C : Set E) (c : 𝕜) :
    (⋃ y ∈ C, closedBall y ‖c‖) = C + c • B := by
  by_cases hc : c = 0
  · subst hc
    ext x
    simp [Metric.closedBall_zero']
  · exact iUnion_closedBall_norm_eq_add_smul_unitClosedBall_of_ne_zero (C := C) c hc

/-- Text 6.6 (canonical scalar-generic owner):
points lying within distance at most `‖c‖` of `C` are exactly `C + c • B`;
the endpoint `c = 0` uses `T1Space`. -/
theorem points_within_distance_le_norm_eq_add_smul_unitClosedBall
    [T1Space E] (C : Set E) (c : 𝕜) :
    {x : E | ∃ y ∈ C, dist x y ≤ ‖c‖} = C + c • B := by
  calc
    {x : E | ∃ y ∈ C, dist x y ≤ ‖c‖} = ⋃ y ∈ C, closedBall y ‖c‖ := by
      simpa using points_within_distance_le_eq_iUnion_closedBall (C := C) ‖c‖
    _ = C + c • B := by
      simpa using iUnion_closedBall_norm_eq_add_smul_unitClosedBall (C := C) c

end
