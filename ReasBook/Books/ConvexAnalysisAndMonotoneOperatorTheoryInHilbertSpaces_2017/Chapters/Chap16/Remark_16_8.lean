import Mathlib
import BauschkeLean.Chap06.Example_6_39
import BauschkeLean.Chap06.Proposition_6_44
import BauschkeLean.Chap09.Remark_9_37
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Example_16_13

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped EuclideanSpace InnerProductSpace Pointwise

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "B" => Metric.closedBall (0 : ℝ²) 1
local notation "x₀" => (!₂[(1 : ℝ), 0] : ℝ²)

/-- Helper for Remark 16 8: a vector in `ℝ²` is determined by its two coordinates. -/
private theorem euclideanSpace_fin2_eq (x : ℝ²) : x = !₂[x 0, x 1] := by
  -- Reduce equality in `EuclideanSpace ℝ (Fin 2)` to the two coordinate identities.
  ext i
  fin_cases i <;> simp

/-- Helper for Remark 16 8: the squared norm in `ℝ²` is the sum of the coordinate squares. -/
private theorem norm_sq_eq_coord_sq_sum (x : ℝ²) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  -- Rewrite `x` by its two coordinates and use the standard Euclidean norm formula.
  rw [euclideanSpace_fin2_eq x]
  norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- Helper for Remark 16 8: the boundary point `x₀ = (1,0)` has norm `1`. -/
private theorem x₀_norm_eq_one : ‖x₀‖ = 1 := by
  -- Square the norm first, then solve the resulting scalar identity.
  have hsq : ‖x₀‖ ^ 2 = 1 := by
    rw [norm_sq_eq_coord_sq_sum x₀]
    norm_num
  have hnonneg : 0 ≤ ‖x₀‖ := norm_nonneg x₀
  nlinarith

/-- Helper for Remark 16 8: the boundary point `x₀ = (1,0)` lies in the closed unit ball. -/
private theorem x₀_mem_closedUnitBall : x₀ ∈ B := by
  -- Membership in the closed ball centered at `0` is exactly the norm bound `‖x₀‖ ≤ 1`.
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa using (show ‖x₀‖ ≤ 1 by rw [x₀_norm_eq_one])

/-- Helper for Remark 16 8: the closed unit ball is nonempty. -/
private theorem closedUnitBall_nonempty : Set.Nonempty B := by
  -- The distinguished boundary point already witnesses nonemptiness.
  exact ⟨x₀, x₀_mem_closedUnitBall⟩

/-- Helper for Remark 16 8: the nonnegative ray through `(1,0)` is the horizontal nonnegative
half-line. -/
private theorem nonnegative_ray_through_x₀_eq :
    Set.Ici (0 : ℝ) • ({x₀} : Set ℝ²) = {u : ℝ² | 0 ≤ u 0 ∧ u 1 = 0} := by
  ext u
  constructor
  · rintro ⟨a, ha, y, hy, rfl⟩
    have hyx : y = x₀ := by
      simpa using hy
    subst hyx
    constructor
    · simpa using ha
    · simp
  · rintro ⟨hu0, hu1⟩
    -- Rebuild the vector as its first coordinate times `(1,0)`.
    refine ⟨u 0, hu0, x₀, ?_, ?_⟩
    · simp
    · ext i
      fin_cases i
      · simp
      · simp [hu1]

/-- Helper for Remark 16 8: the first coordinate slice through `x₀` is the scalar multiple
`(t,0) = t • (1,0)`. -/
private theorem first_coordinate_slice_eq_smul (t : ℝ) :
    coordinateSliceEuclidean x₀ 0 t = t • x₀ := by
  -- Compare both vectors on the two coordinates.
  ext i
  fin_cases i <;> simp

/-- Helper for Remark 16 8: the first slice meets the closed unit ball exactly on `[-1,1]`. -/
private theorem first_slice_mem_closedUnitBall_iff (t : ℝ) :
    coordinateSliceEuclidean x₀ 0 t ∈ B ↔ t ∈ Metric.closedBall (0 : ℝ) 1 := by
  -- Rewrite the slice as `t • x₀`, so the Euclidean membership test becomes `‖t‖ ≤ 1`.
  calc
    coordinateSliceEuclidean x₀ 0 t ∈ B ↔ dist (coordinateSliceEuclidean x₀ 0 t) 0 ≤ 1 := by
      rw [Metric.mem_closedBall]
    _ ↔ ‖coordinateSliceEuclidean x₀ 0 t‖ ≤ 1 := by
      simp [dist_eq_norm]
    _ ↔ ‖t‖ ≤ 1 := by
      rw [first_coordinate_slice_eq_smul, norm_smul, x₀_norm_eq_one, mul_one]
    _ ↔ t ∈ Metric.closedBall (0 : ℝ) 1 := by
      simp [Metric.mem_closedBall, dist_eq_norm]

/-- Helper for Remark 16 8: the sliced indicator along the first coordinate is the indicator of
the real closed unit ball. -/
private theorem indicator_first_coordinate_slice_eq_indicator_closedBall :
    ((ι[B]) ∘ coordinateSliceEuclidean x₀ 0) = ι[Metric.closedBall (0 : ℝ) 1] := by
  funext t
  apply Subtype.ext
  -- The two indicator functions agree because the two membership tests are equivalent.
  by_cases ht : t ∈ Metric.closedBall (0 : ℝ) 1
  · have hs : coordinateSliceEuclidean x₀ 0 t ∈ B :=
      (first_slice_mem_closedUnitBall_iff t).2 ht
    simp [Function.comp_apply, indicator_apply, hs, ht]
  · have hs : coordinateSliceEuclidean x₀ 0 t ∉ B := by
      simpa [first_slice_mem_closedUnitBall_iff t] using ht
    simp [Function.comp_apply, indicator_apply, hs, ht]

/-- Helper for Remark 16 8: the nonnegative ray through `1` is exactly `ℝ₊`. -/
private theorem nonnegative_ray_singleton_one_eq_Ici :
    Set.Ici (0 : ℝ) • ({(1 : ℝ)} : Set ℝ) = Set.Ici (0 : ℝ) := by
  ext u
  constructor
  · rintro ⟨a, ha, y, hy, rfl⟩
    have hy1 : y = 1 := by
      simpa using hy
    subst hy1
    simpa using ha
  · intro hu
    -- Realize `u` as the nonnegative scalar `u` times the singleton generator `1`.
    refine ⟨u, hu, 1, ?_, ?_⟩
    · simp
    · simp

/-- Helper for Remark 16 8: the second coordinate slice through `x₀` is `(1,t)`. -/
private theorem second_coordinate_slice_eq (t : ℝ) :
    coordinateSliceEuclidean x₀ 1 t = !₂[(1 : ℝ), t] := by
  -- Compare both vectors on the two coordinates.
  ext i
  fin_cases i <;> simp

/-- Helper for Remark 16 8: the second slice meets the closed unit ball only at `t = 0`. -/
private theorem second_slice_mem_closedUnitBall_iff (t : ℝ) :
    coordinateSliceEuclidean x₀ 1 t ∈ B ↔ t = 0 := by
  -- Rewrite the slice as `(1,t)` and solve the resulting scalar inequality `1 + t^2 ≤ 1`.
  rw [Metric.mem_closedBall, dist_eq_norm, second_coordinate_slice_eq]
  constructor
  · intro ht
    have hnorm : ‖(!₂[(1 : ℝ), t] : ℝ²)‖ ≤ 1 := by
      simpa using ht
    have hsq : ‖(!₂[(1 : ℝ), t] : ℝ²)‖ ^ 2 ≤ 1 := by
      nlinarith [hnorm, norm_nonneg (!₂[(1 : ℝ), t] : ℝ²)]
    rw [norm_sq_eq_coord_sq_sum (!₂[(1 : ℝ), t] : ℝ²)] at hsq
    have hsq' : 1 + t ^ 2 ≤ 1 := by
      simpa using hsq
    nlinarith [sq_nonneg t]
  · intro ht
    subst ht
    have hx_norm : ‖(!₂[(1 : ℝ), (0 : ℝ)] : ℝ²)‖ = 1 := by
      simpa using x₀_norm_eq_one
    have hx_le : ‖(!₂[(1 : ℝ), (0 : ℝ)] : ℝ²)‖ ≤ 1 := by
      rw [hx_norm]
    simpa using hx_le

/-- Helper for Remark 16 8: the sliced indicator along the second coordinate is the indicator of
the singleton `{0}`. -/
private theorem indicator_second_coordinate_slice_eq_indicator_singleton :
    ((ι[B]) ∘ coordinateSliceEuclidean x₀ 1) = ι[({0} : Set ℝ)] := by
  funext t
  apply Subtype.ext
  -- The slice lies in the closed ball exactly when the varied coordinate vanishes.
  by_cases ht : t = 0
  · have hs : coordinateSliceEuclidean x₀ 1 t ∈ B :=
      (second_slice_mem_closedUnitBall_iff t).2 ht
    have hsingleton : t ∈ ({0} : Set ℝ) := by
      simpa [Set.mem_singleton_iff] using ht
    simp [Function.comp_apply, indicator_apply, hs, hsingleton]
  · have hs : coordinateSliceEuclidean x₀ 1 t ∉ B := by
      simpa [second_slice_mem_closedUnitBall_iff t] using ht
    have hsingleton : t ∉ ({0} : Set ℝ) := by
      simpa [Set.mem_singleton_iff] using ht
    simp [Function.comp_apply, indicator_apply, hs, hsingleton]

/-- Helper for Remark 16 8: subtracting the singleton `{0}` leaves a set unchanged. -/
private theorem sub_singleton_zero_eq_self {H : Type*} [AddGroup H] (S : Set H) :
    S - ({0} : Set H) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst hz0
    simpa using hy
  · intro hx
    -- Use the trivial decomposition `x = x - 0`.
    refine ⟨x, hx, 0, ?_, ?_⟩
    · simp
    · simp

-- Proof sketch: Example 16.13 rewrites the subdifferential of `ι[B]` as the normal cone of `B`,
-- and Example 6.39 identifies that normal cone at the boundary point `x₀ = (1,0)` with the
-- nonnegative ray through `x₀`, i.e. `ℝ₊ × {0}`.
/-- The subdifferential of the closed-unit-ball indicator at the boundary point `(1,0)` is
`ℝ₊ × {0}`. -/
theorem subdifferential_indicator_closedUnitBall_boundary_eq :
    (∂ ι[B]) x₀ =
      {u : ℝ² | 0 ≤ u 0 ∧ u 1 = 0} := by
  have hsubd :
      ∂ ι[B] = N[B] :=
    subdifferential_setIndicator_eq_normalCone B closedUnitBall_nonempty
  -- Compute the indicator subdifferential through the normal cone and then identify the ray.
  calc
    (∂ ι[B]) x₀ = N[B] x₀ := by
      simpa using congrFun hsubd x₀
    _ = Set.Ici (0 : ℝ) • ({x₀} : Set ℝ²) := by
      simpa using normalCone_closedUnitBall_eq_nonnegative_ray_of_norm_eq_one
        (x := x₀) x₀_norm_eq_one
    _ = {u : ℝ² | 0 ≤ u 0 ∧ u 1 = 0} := nonnegative_ray_through_x₀_eq

-- Proof sketch: the slice `coordinateSliceEuclidean x₀ 0 : t ↦ (t,0)` pulls `ι[B]` back to the
-- indicator of the interval `[-1,1]`; at the endpoint `1`, its subdifferential is `ℝ₊`.
/-- The first coordinate slice through `(1,0)` has subdifferential `ℝ₊` at the boundary point
`1`. -/
theorem subdifferential_indicator_closedUnitBall_firstCoordinateSlice_eq :
    (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ 0)) (1 : ℝ) = Set.Ici (0 : ℝ) := by
  have hnonempty : (Metric.closedBall (0 : ℝ) 1).Nonempty := by
    refine ⟨0, ?_⟩
    simp [Metric.mem_closedBall]
  have hsubd :
      ∂ ι[Metric.closedBall (0 : ℝ) 1] = N[Metric.closedBall (0 : ℝ) 1] :=
    subdifferential_setIndicator_eq_normalCone (Metric.closedBall (0 : ℝ) 1) hnonempty
  have hone_norm : ‖(1 : ℝ)‖ = 1 := by
    norm_num
  -- First rewrite the sliced indicator as the real closed-ball indicator,
  -- then compute its normal cone.
  calc
    (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ 0)) (1 : ℝ) =
        (∂ ι[Metric.closedBall (0 : ℝ) 1]) (1 : ℝ) := by
      rw [indicator_first_coordinate_slice_eq_indicator_closedBall]
    _ = N[Metric.closedBall (0 : ℝ) 1] (1 : ℝ) := by
      simpa using congrFun hsubd (1 : ℝ)
    _ = Set.Ici (0 : ℝ) • ({(1 : ℝ)} : Set ℝ) := by
      simpa using normalCone_closedUnitBall_eq_nonnegative_ray_of_norm_eq_one
        (x := (1 : ℝ)) hone_norm
    _ = Set.Ici (0 : ℝ) := nonnegative_ray_singleton_one_eq_Ici

-- Proof sketch: the slice `coordinateSliceEuclidean x₀ 1 : t ↦ (1,t)` pulls `ι[B]` back to the
-- indicator of `{0}`, whose subdifferential at `0` is all of `ℝ`.
/-- The second coordinate slice through `(1,0)` has full subdifferential at `0`. -/
theorem subdifferential_indicator_closedUnitBall_secondCoordinateSlice_eq :
    (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ 1)) (0 : ℝ) = (Set.univ : Set ℝ) := by
  have hzero_mem : (0 : ℝ) ∈ ({0} : Set ℝ) := by
    simp
  have hsubd :
      ∂ ι[({0} : Set ℝ)] = N[({0} : Set ℝ)] :=
    subdifferential_setIndicator_eq_normalCone ({0} : Set ℝ) ⟨0, hzero_mem⟩
  -- Collapse the second slice to the singleton indicator and evaluate its normal cone explicitly.
  calc
    (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ 1)) (0 : ℝ) =
        (∂ ι[({0} : Set ℝ)]) (0 : ℝ) := by
      rw [indicator_second_coordinate_slice_eq_indicator_singleton]
    _ = N[({0} : Set ℝ)] (0 : ℝ) := by
      simpa using congrFun hsubd (0 : ℝ)
    _ = ({0} : Set ℝ)ᵒ⊖ := by
      rw [Set.normalCone_eq_polarCone_translate_of_mem hzero_mem, sub_singleton_zero_eq_self]
    _ = (Set.univ : Set ℝ) := Set.polarCone_singleton_zero_eq_univ

-- Proof sketch: the two one-dimensional slice computations identify the coordinatewise owner from
-- Proposition 16.7 with `ℝ₊ × ℝ = {u | 0 ≤ u 0}`.
/-- At `(1,0)`, the coordinatewise slice subdifferentials from Proposition 16.7 identify with
`ℝ₊ × ℝ`. -/
theorem coordinatewise_subdifferential_indicator_closedUnitBall_boundary_eq :
    {u : ℝ² |
        ∀ i, u i ∈ (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ i)) (x₀ i)} =
      {u : ℝ² | 0 ≤ u 0} := by
  ext u
  constructor
  · intro hu
    have h0 := hu 0
    -- The coordinate `0` condition is exactly the first-slice subdifferential computation.
    simpa [subdifferential_indicator_closedUnitBall_firstCoordinateSlice_eq] using h0
  · intro hu i
    -- Split the two coordinates and plug in the previously computed one-dimensional slices.
    fin_cases i
    · simpa [subdifferential_indicator_closedUnitBall_firstCoordinateSlice_eq] using hu
    · simp [subdifferential_indicator_closedUnitBall_secondCoordinateSlice_eq]

-- Proof sketch: Proposition 16.7 gives the ambient inclusion into the coordinatewise slice
-- subdifferentials. The companion equality above rewrites that right-hand side as `ℝ₊ × ℝ`, while
-- `subdifferential_indicator_closedUnitBall_boundary_eq` identifies the left-hand side with the
-- smaller ray `ℝ₊ × {0}`.
/-- Remark 16 8: for the indicator of the closed unit ball in the canonical Euclidean model of
`ℝ²`, the coordinatewise subdifferential inclusion from Proposition 16.7 is strict at `(1,0)`. -/
theorem indicator_closedUnitBall_strict_subset_coordinatewise_subdifferential :
    (∂ ι[B]) x₀ ⊂
      {u : ℝ² |
        ∀ i, u i ∈ (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ i)) (x₀ i)} := by
  -- After identifying both sides explicitly,
  -- strictness is witnessed by the vertical vector `(0,1)`.
  rw [subdifferential_indicator_closedUnitBall_boundary_eq,
    coordinatewise_subdifferential_indicator_closedUnitBall_boundary_eq]
  refine Set.ssubset_iff_subset_ne.mpr ?_
  constructor
  · intro u hu
    exact hu.1
  · intro hEq
    have hwCoord : (!₂[(0 : ℝ), 1] : ℝ²) ∈ {u : ℝ² | 0 ≤ u 0} := by
      norm_num
    have hwTrue : (!₂[(0 : ℝ), 1] : ℝ²) ∈ {u : ℝ² | 0 ≤ u 0 ∧ u 1 = 0} := by
      rw [hEq]
      exact hwCoord
    norm_num at hwTrue

end

end ERealFunction
