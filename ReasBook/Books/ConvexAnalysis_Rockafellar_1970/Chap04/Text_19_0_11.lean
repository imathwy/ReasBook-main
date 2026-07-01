import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_13
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

section

variable {ι : Type*} [Finite ι]
variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜]

local noncomputable instance : Fintype ι := Fintype.ofFinite ι

local notation "E" => ι → 𝕜
local notation "l1Gauge" => (coordinateL1Gauge ι : E → WithTopBot 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Text 19.0.11 is the finite-coordinate example asserting that the coordinate
  `ℓ¹` gauge is polyhedral convex.
  `coordinateL1Gauge ι` from `Chap03.Text_15_0_13` and the finite sign-vector half-space
  presentation of its epigraph.
- `core/canonical`: the Chapter 19 owner predicate is `Function.HasPolyhedralEpigraph`.
- `bridge/view`: the epigraph is presented as the intersection of the finitely many half-spaces
  indexed by sign choices `ε : ι → Bool`; no extra wrapper owner is needed.

Domain-style sampling used here:
- `coordinateL1Gauge` from `Chap03.Text_15_0_13`;
- `Set.isPolyhedral_setOf_forall_linear_le` from `Chap04.Text_19_0_1`;
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Set.IsPolyhedral` from `Chap01.Definition_2_1_2`.

Primitive data vs derived API:
- primitive owner: the function `coordinateL1Gauge ι`;
- derived API: the polyhedral-epigraph predicate on that owner;
- bridge data: the private sign-indexed linear forms cutting out `epi (coordinateL1Gauge ι)`.

Layer target: `source-facing`, with the public statement kept directly on the canonical owner
`coordinateL1Gauge` rather than on a parallel local coordinate-sum wrapper.
-/

private def coordinateL1EpigraphLinearMap (ε : ι → Bool) : (E × 𝕜) →ₗ[𝕜] 𝕜 :=
  (∑ i, if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
      else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) -
    LinearMap.snd 𝕜 E 𝕜

omit [LinearOrder 𝕜] in
@[simp] private theorem coordinateL1EpigraphLinearMap_apply (ε : ι → Bool) (p : E × 𝕜) :
    coordinateL1EpigraphLinearMap ε p =
      (∑ i, if ε i then p.1 i else -p.1 i) - p.2 := by
  rw [coordinateL1EpigraphLinearMap, LinearMap.sub_apply, LinearMap.snd_apply]
  have hsumApply :
      (∑ i, if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
          else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) p =
        ∑ i,
          (if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
            else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) p := by
    simp [LinearMap.sum_apply]
  rw [hsumApply]
  have hsum :
      ∑ i,
          (if ε i then (LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜)
            else -((LinearMap.proj i).comp (LinearMap.fst 𝕜 E 𝕜))) p =
        ∑ i, if ε i then p.1 i else -p.1 i := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hε : ε i
    · simp [hε, LinearMap.comp_apply, LinearMap.fst_apply]
    · simp [hε, LinearMap.comp_apply, LinearMap.fst_apply]
  rw [hsum]

private theorem sum_abs_le_iff_forall_signs_le (x : E) (t : 𝕜) :
    (∑ i, |x i|) ≤ t ↔ ∀ ε : ι → Bool, ∑ i, (if ε i then x i else -x i) ≤ t := by
  constructor
  · intro h ε
    calc
      ∑ i, (if ε i then x i else -x i) ≤ ∑ i, |x i| := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        by_cases hε : ε i
        · simp [hε, le_abs_self]
        · simp [hε, neg_le_abs]
      _ ≤ t := h
  · intro h
    let ε : ι → Bool := fun i ↦ decide (0 ≤ x i)
    have hε : ∑ i, (if ε i then x i else -x i) ≤ t := h ε
    have hEq : ∑ i, (if ε i then x i else -x i) = ∑ i, |x i| := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hx : 0 ≤ x i
      · simp [ε, hx, abs_of_nonneg hx]
      · simp [ε, hx, abs_of_neg (lt_of_not_ge hx)]
    simpa [hEq] using hε

private theorem epi_coordinateL1Gauge_eq_setOf_forall_signLinearMap :
    epi l1Gauge =
      {p : E × 𝕜 |
        ∀ ε : ι → Bool, coordinateL1EpigraphLinearMap ε p ≤ 0} := by
  ext p
  rw [mem_epi_iff]
  change ((((∑ i, |p.1 i|) : 𝕜) : WithTopBot 𝕜) ≤ ((p.2 : 𝕜) : WithTopBot 𝕜)) ↔ _
  rw [WithBotTop.coe_le_coe]
  constructor
  · intro hp ε
    rw [coordinateL1EpigraphLinearMap_apply]
    exact sub_nonpos.mpr ((sum_abs_le_iff_forall_signs_le p.1 p.2).1 hp ε)
  · intro hp
    refine (sum_abs_le_iff_forall_signs_le p.1 p.2).2 fun ε ↦ ?_
    exact sub_nonpos.mp <| by simpa [coordinateL1EpigraphLinearMap_apply] using hp ε

/-- Text 19.0.11, owner form: on any finite ordered-ring coordinate space, the coordinate `ℓ¹`
gauge has polyhedral epigraph. Specializing `𝕜 = ℝ` and `ι = Fin n` recovers the textbook
`R^n` statement. -/
theorem coordinateL1Gauge_hasPolyhedralEpigraph :
    (l1Gauge).HasPolyhedralEpigraph := by
  change (epi l1Gauge).IsPolyhedral 𝕜
  rw [epi_coordinateL1Gauge_eq_setOf_forall_signLinearMap]
  simpa using
    (Set.isPolyhedral_setOf_forall_linear_le (I := ι → Bool)
      coordinateL1EpigraphLinearMap
      (fun _ ↦ (0 : 𝕜)))

end
