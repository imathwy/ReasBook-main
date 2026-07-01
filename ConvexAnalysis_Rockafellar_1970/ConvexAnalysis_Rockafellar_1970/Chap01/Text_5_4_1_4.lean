import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Eorder.Add
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

attribute [local instance] Classical.propDecidable

section

variable {E : Type*} [SeminormedAddCommGroup E]

open Metric

scoped[Rockafellar] notation "d(" x ", " C ")" => Metric.infEDist x C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.1.4 specializes infimal convolution to the Euclidean norm and the
  `0/+∞` indicator of a set `C`, obtaining the distance-to-set function.
- `core/canonical`: the owner abstractions are the chapter operation `infimal_convolution` from
  `Text_5_4_0`, the chapter indicator owner `indicator` from `Defintion_4_8_1`, and the
  canonical distance owner `Metric.infEDist` viewed through the chapter notation `d(·, C)`.
- `bridge/view`: `d(·, C)` is notation for the canonical owner `Metric.infEDist`; this concrete
  owner is defined locally here because the dedicated distance file is currently unavailable as a
  compiled dependency.
- Primitive data vs derived API: the primitive inputs are the set `C` and the point `x`; the
  distance identity is the derived theorem.

Domain-style sampling used here:
- the chapter owner declaration `infimal_convolution`;
- the chapter owner declaration `indicator`;
- the chapter distance owner notation `d(·, C)` with its bridge to `Metric.infEDist`;
- the `dist`-bridge theorem `distanceToSet_eq_iInf_dist`;
- the canonical norm-metric bridge `dist_eq_norm`.

The source phrases the statement for a convex set `C`, but the identity itself depends on neither
convexity nor nonemptiness, so those hypotheses are removed as mathematically redundant.
- Ambient minimization: although the source states the formula on `ℝ^n`, the canonical owners used
  in the statement and proof already live on any seminormed additive commutative group, so the
  public theorem is stated at that intrinsic level rather than on a fixed coordinate model.
-/

/-- Helper for Text 5.4.1.4: the chapter distance owner is the subtype-indexed infimum of the
pointwise distances, viewed in `EReal`. -/
theorem infEDist_eq_iInf_dist_withTopBot {C : Set E} (x : E) :
    (d(x, C) : EReal) = ⨅ z : C, (dist x z : EReal) := by
  have hE' :
      (d(x, C) : EReal) = ⨅ z : C, (dist x z : EReal) := by
    -- Rewrite the edistance owner as a subtype-indexed infimum before coercing it to `EReal`.
    rw [Metric.infEDist, iInf_subtype']
    let f : C → ENNReal := fun z ↦ edist x z
    have hmono : Monotone ((↑) : ENNReal → EReal) :=
      EReal.coe_ennreal_strictMono.monotone
    -- Move the coercion through the infimum and then rewrite each edistance term via `dist`.
    have hmap :
        ((⨅ z, f z : ENNReal) : EReal) = ⨅ z, ((f z : ENNReal) : EReal) :=
      hmono.map_iInf_of_continuousAt continuous_coe_ennreal_ereal.continuousAt rfl
    calc
      ((⨅ z, f z : ENNReal) : EReal) = ⨅ z : C, ((f z : ENNReal) : EReal) := hmap
      _ = ⨅ z : C, (dist x z : EReal) := by
        exact iInf_congr fun z : C ↦
          (show ((f z : ENNReal) : EReal) = (dist x z : EReal) from by
            simpa [f, dist_edist] using (EReal.coe_ennreal_toReal (edist_ne_top x (z : E))).symm)
  exact hE'

/-- Helper for Text 5.4.1.4: outside the set, the indicator term is `⊤` when viewed in `EReal`. -/
theorem indicator_of_notMem_toEReal {C : Set E} {z : E} (hz : z ∉ C) :
    (show EReal from (δ[ℝ](z | C))) = (⊤ : EReal) := by
  -- Transport the indicator's off-set branch to the `EReal` codomain used in this file.
  simpa [indicator_def, hz]

/-- Helper for Text 5.4.1.4: restricting the indicator branch turns the ambient infimum into the
subtype infimum over the feasible shifts. -/
theorem indicator_shift_iInf_eq_subtype_iInf {C : Set E} (x : E) :
    (⨅ y : E, ((‖y‖ : ℝ) : EReal) + (show EReal from (δ[ℝ](x - y | C)))) =
      ⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : EReal) := by
  -- Split on whether the indicator is finite and collapse the `+∞` branch.
  calc
    (⨅ y : E, ((‖y‖ : ℝ) : EReal) + (show EReal from (δ[ℝ](x - y | C)))) =
        ⨅ y : E, if x - y ∈ C then ((‖y‖ : ℝ) : EReal) else (⊤ : EReal) := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : x - y ∈ C
          · -- On feasible shifts, the indicator vanishes and the branch keeps the norm term.
            rw [if_pos hy, indicator_of_mem (α := ℝ) (C := C) hy]
            exact add_zero (((‖y‖ : ℝ) : EReal))
          · -- Outside the feasible set, the indicator becomes `⊤`, which absorbs finite addition.
            rw [if_neg hy]
            rw [indicator_of_notMem_toEReal (C := C) (z := x - y) hy]
            simp
    _ = ⨅ y : E, ⨅ (_ : x - y ∈ C), (((‖y‖ : ℝ) : EReal)) := by
          refine iInf_congr fun y ↦ ?_
          by_cases hy : x - y ∈ C
          · simp [hy]
          · simp [hy]
    _ = ⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : EReal) := by
          rw [iInf_subtype']

/-- Helper for Text 5.4.1.4: subtracting a feasible shift from `x` lands in the target set. -/
theorem sub_mem_equiv_set_member_toFun_mem {C : Set E} (x : E)
    (y : {y : E // x - y ∈ C}) :
    x - (y : E) ∈ C :=
  y.property

/-- Helper for Text 5.4.1.4: subtracting a point of `C` from `x` produces a feasible shift. -/
theorem sub_mem_equiv_set_member_inv_mem {C : Set E} (x : E) (z : C) :
    x - (z : E) ∈ {y : E | x - y ∈ C} := by
  -- Rewrite the double subtraction so the goal becomes the stored membership proof of `z`.
  simp [sub_sub_cancel, z.property]

/-- Helper for Text 5.4.1.4: applying the subtraction reindexing twice recovers a feasible shift. -/
theorem sub_mem_equiv_set_member_left_inv_val {C : Set E} (x : E)
    (y : {y : E // x - y ∈ C}) :
    x - (x - (y : E)) = (y : E) := by
  -- Cancel the two subtractions to recover the original shift variable.
  simp [sub_sub_cancel]

/-- Helper for Text 5.4.1.4: applying the inverse subtraction reindexing twice recovers a point
of `C`. -/
theorem sub_mem_equiv_set_member_right_inv_val {C : Set E} (x : E) (z : C) :
    x - (x - (z : E)) = (z : E) := by
  -- The same cancellation now shows the reindexed point of `C` is unchanged.
  simp [sub_sub_cancel]

/-- Helper for Text 5.4.1.4: subtraction identifies the feasible shifts with the set itself. -/
def sub_mem_equiv_set_member {C : Set E} (x : E) : {y : E // x - y ∈ C} ≃ C :=
  { toFun := fun y ↦ ⟨x - y, y.property⟩
    invFun := fun z ↦ ⟨x - z, sub_mem_equiv_set_member_inv_mem (C := C) x z⟩
    left_inv := fun y ↦ Subtype.ext (sub_mem_equiv_set_member_left_inv_val (C := C) x y)
    right_inv := fun z ↦ Subtype.ext (sub_mem_equiv_set_member_right_inv_val (C := C) x z) }

/-- Helper for Text 5.4.1.4: after reindexing by subtraction, the constrained norm infimum is the
set-indexed distance infimum. -/
theorem subtype_iInf_norm_eq_set_iInf_dist {C : Set E} (x : E) :
    (⨅ y : {y : E // x - y ∈ C}, ((‖(y : E)‖ : ℝ) : EReal)) =
      ⨅ z : C, (dist x z : EReal) := by
  let e : {y : E // x - y ∈ C} ≃ C := sub_mem_equiv_set_member (C := C) x
  -- Reindex the subtype infimum by the subtraction equivalence.
  refine Equiv.iInf_congr e ?_
  intro y
  -- The reindexed norm is exactly the distance `dist x z`.
  show (dist x (e y) : EReal) = ((‖(y : E)‖ : ℝ) : EReal)
  simp [e, sub_mem_equiv_set_member]

-- Proof sketch: rewrite the infimal convolution with the inline `0/+∞` indicator as the infimum
-- of the norms `‖x - z‖` over `z ∈ C`. Then identify that subtype-indexed infimum directly with
-- the Chapter 1 `dist`-bridge theorem `distanceToSet_eq_iInf_dist`, keeping the theorem surface
-- on the chapter codomain owner `EReal`.
/-- Owner-facing form of Text 5.4.1.4: taking `f` to be the norm and `g` to be the `0/+∞`
indicator of a set `C`, the infimal convolution `f □ g` is exactly the chapter distance function
`x ↦ d(x, C)`.
The source states this on `ℝ^n`, but the canonical chapter statement is valid on any
seminormed additive commutative group. The source's convexity and nonemptiness assumptions on
`C` are redundant for this identity and are omitted. -/
theorem infimal_convolution_norm_indicator_eq_distanceToSet
    {C : Set E} :
    ((fun y : E ↦ ((‖y‖ : ℝ) : EReal)) □
      (fun z ↦ (show EReal from (δ[ℝ](z | C))))) =
      fun x ↦ (d(x, C) : EReal) := by
  funext x
  -- Rewrite the infimal convolution into the textbook one-parameter infimum.
  rw [infimal_convolution_apply]
  -- Restrict the ambient infimum to the feasible shifts where the indicator is zero.
  rw [indicator_shift_iInf_eq_subtype_iInf (C := C) (x := x)]
  -- Reindex the feasible shifts by points of `C` and rewrite norms as distances.
  rw [subtype_iInf_norm_eq_set_iInf_dist (C := C) (x := x)]
  -- Identify the resulting infimum with the canonical distance owner.
  exact (infEDist_eq_iInf_dist_withTopBot (C := C) x).symm

end
