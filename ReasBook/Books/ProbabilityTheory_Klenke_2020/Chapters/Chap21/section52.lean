import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_52 (from Items/Chap21) -/
open Set
open scoped Topology ENNReal

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/-- Definition 21.52 (1): the first-variation path `t ↦ V_t^1(G)` of a continuous real-valued
path on `[0, ∞)` is the canonical signed-variation path `variationOnFromTo G univ 0`. -/
def variationProcess (G : PathSpace) : NNReal → ℝ :=
  variationOnFromTo G univ 0

/-- Evaluating `variationProcess G` at time `t` gives the total variation of `G` on `[0, t]`. -/
theorem variationProcess_eq_toReal_eVariationOn_Icc (G : PathSpace) (t : NNReal) :
    variationProcess G t = (eVariationOn G (Icc 0 t)).toReal := sorry

/-- Definition 21.52 (2): for paths on `[0, ∞)`, the source condition "locally finite variation"
is exactly the canonical owner property `LocallyBoundedVariationOn G univ`. -/
theorem locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero (G : PathSpace) :
    LocallyBoundedVariationOn G univ ↔ ∀ t : NNReal, BoundedVariationOn G (Icc 0 t) := sorry

/- Definition 21.52 (2): the owner property is `LocallyBoundedVariationOn G univ`; continuity of
`variationProcess G` is derived API. -/
/-- For a continuous path of locally bounded variation, the variation process is continuous. -/
theorem _root_.LocallyBoundedVariationOn.continuous_variationProcess {G : PathSpace}
    (hG : LocallyBoundedVariationOn G univ) :
    Continuous (variationProcess G) := sorry

-- Proof sketch: the zero path has zero variation on every interval, so the finiteness condition
-- is immediate.
private theorem locallyBoundedVariationOn_univ_zero :
    LocallyBoundedVariationOn (0 : PathSpace) univ := sorry

-- Proof sketch: total variation is subadditive on each interval, giving local finite variation
-- for `G + H`.
private theorem locallyBoundedVariationOn_univ_add {G H : PathSpace}
    (hG : LocallyBoundedVariationOn G univ) (hH : LocallyBoundedVariationOn H univ) :
    LocallyBoundedVariationOn (G + H) univ := sorry

-- Proof sketch: variation scales by `|c|` on each interval, so scalar multiplication preserves
-- local finite variation.
private theorem locallyBoundedVariationOn_univ_smul (c : ℝ) {G : PathSpace}
    (hG : LocallyBoundedVariationOn G univ) :
    LocallyBoundedVariationOn (c • G) univ := sorry

/-- Definition 21.52 (3): `continuousVariationSubmodule` is the textbook vector space `𝒞_v` of
continuous real-valued paths on `[0, ∞)` whose variation process is continuous. -/
def continuousVariationSubmodule : Submodule ℝ PathSpace where
  carrier := {G | LocallyBoundedVariationOn G univ}
  zero_mem' := locallyBoundedVariationOn_univ_zero
  add_mem' := locallyBoundedVariationOn_univ_add
  smul_mem' := locallyBoundedVariationOn_univ_smul

-- Proof sketch: unfold `continuousVariationSubmodule`; membership in its carrier is exactly the
-- predicate used to define the submodule.
/-- A path belongs to `continuousVariationSubmodule` exactly when it has locally bounded
variation on `[0, ∞)`. -/
theorem mem_continuousVariationSubmodule_iff (G : PathSpace) :
    G ∈ continuousVariationSubmodule ↔ LocallyBoundedVariationOn G univ :=
  Iff.rfl
