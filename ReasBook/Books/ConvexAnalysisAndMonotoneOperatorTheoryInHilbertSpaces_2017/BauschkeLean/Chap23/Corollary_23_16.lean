import BauschkeLean.Chap04.Proposition_4_4
import BauschkeLean.Chap04.Text_4_21_1
import BauschkeLean.Chap23.Theorem_23_15

-- Semantic recall: the relevant owner abstractions are the Chapter 23 extension theorem
-- `exists_firmlyNonexpansive_extension_range_subset_closure_convexHull_range`, the Chapter 4
-- reflected-map characterization of firm nonexpansiveness, and the metric projection onto the
-- closed convex hull of the original range.

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 23.16 is the Kirszbraun--Valentine extension statement for a
  nonexpansive map on a subset.
- `core/canonical`: the chapter's owner extension theorem is
  `exists_firmlyNonexpansive_extension_range_subset_closure_convexHull_range`.
 - `bridge/view`: the midpoint map `x ↦ (x + T x) / 2`, its reflector `2S - Id`, and the metric
  projection onto `closedConvexHull ℝ (Set.range T)` bridge the source-facing nonexpansive map to
  the firmly nonexpansive extension owner. -/

/-- Corollary 23.16 (Kirszbraun--Valentine): if `D` is a nonempty subset of a real Hilbert space
and `T : D → H` is nonexpansive, then there exists a nonexpansive extension `Ttilde : H → H`
such that `Ttilde` agrees with `T` on `D`, written as `∀ x : D, Ttilde x = T x`, and
`Set.range Ttilde ⊆ closure (convexHull ℝ (Set.range T))`. -/
theorem exists_nonexpansive_extension_range_subset_closure_convexHull_range
    (D : Set H) (hD : D.Nonempty) (T : D → H) (hT : LipschitzWith 1 T) :
    ∃ Ttilde : H → H,
      LipschitzWith 1 Ttilde ∧
      (∀ x : D, Ttilde x = T x) ∧
      Set.range Ttilde ⊆ closure (convexHull ℝ (Set.range T)) := by
  let S : D → H := fun x ↦ (1 / 2 : ℝ) • ((x : H) + T x)
  have hS : FirmlyNonexpansiveOn D S := by
    refine (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D S).1 ?_
    intro x y
    have hxy : ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
      simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y
    simpa [S, reflectedMap, two_smul, smul_add, smul_smul, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm]
      using hxy
  obtain ⟨Stilde, hStilde, hStilde_eq, _⟩ :=
    exists_firmlyNonexpansive_extension_range_subset_closure_convexHull_range D hD S hS
  let R : H → H := fun x ↦ (2 : ℝ) • Stilde x - x
  have hR : LipschitzWith 1 R := by
    have hR_pair :
        ∀ x y : Set.univ,
          ‖reflectedMap (Set.univ : Set H) (fun z : Set.univ ↦ Stilde z) x -
              reflectedMap (Set.univ : Set H) (fun z : Set.univ ↦ Stilde z) y‖ ≤
            ‖(x : H) - y‖ :=
      (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn
        (Set.univ : Set H) (fun z : Set.univ ↦ Stilde z)).2 <| by
          simpa [FirmlyNonexpansive] using hStilde
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa [R, reflectedMap, Subtype.dist_eq, dist_eq_norm, one_mul] using
      hR_pair ⟨x, by simp⟩ ⟨y, by simp⟩
  let C : Set H := closedConvexHull ℝ (Set.range T)
  have hC_nonempty : C.Nonempty := by
    rcases hD with ⟨x, hx⟩
    refine ⟨T ⟨x, hx⟩, ?_⟩
    exact subset_closedConvexHull ⟨⟨x, hx⟩, rfl⟩
  have hC_closed : IsClosed C := by
    simpa [C] using (isClosed_closedConvexHull : IsClosed (closedConvexHull ℝ (Set.range T)))
  have hC_convex : Convex ℝ C := by
    simpa [C] using (convex_closedConvexHull : Convex ℝ (closedConvexHull ℝ (Set.range T)))
  let P : H → H :=
    projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
  have hP_firm : FirmlyNonexpansive P :=
    firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hP : LipschitzWith 1 P := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    have hxy : ‖P x - P y‖ ^ (2 : ℕ) ≤ inner ℝ (P x - P y) (x - y) :=
      (firmlyNonexpansive_iff_norm_sq_le_inner.1 hP_firm) x y
    have hinner : inner ℝ (P x - P y) (x - y) ≤ ‖P x - P y‖ * ‖x - y‖ :=
      real_inner_le_norm _ _
    have hnorm : ‖P x - P y‖ ≤ ‖x - y‖ := by
      nlinarith [hxy, hinner, norm_nonneg (P x - P y), norm_nonneg (x - y)]
    simpa [dist_eq_norm] using hnorm
  have hP_eq_self {x : H} (hx : x ∈ C) : P x = x := by
    have hxproj : x = P x := by
      exact
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mpr <| by
            refine ⟨hx, ?_⟩
            intro y hy
            simp
    simpa using hxproj.symm
  let Ttilde : H → H := P ∘ R
  refine ⟨Ttilde, ?_, ?_, ?_⟩
  · simpa [Ttilde, Function.comp] using hP.comp hR
  · intro x
    have hRx : R x = T x := by
      calc
        R x = (2 : ℝ) • Stilde x - x := rfl
        _ = (2 : ℝ) • S x - x := by rw [hStilde_eq x]
        _ = T x := by
              simp [S, smul_add, smul_smul, sub_eq_add_neg, add_assoc]
    have hTx_mem : T x ∈ C := by
      exact subset_closedConvexHull ⟨x, rfl⟩
    simpa [Ttilde, Function.comp, hRx] using hP_eq_self hTx_mem
  · rintro y ⟨x, rfl⟩
    have : P (R x) ∈ C := projectionPoint_mem C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (R x)
    simpa [Ttilde, Function.comp, C, closedConvexHull_eq_closure_convexHull] using this

end SetValuedOperator
