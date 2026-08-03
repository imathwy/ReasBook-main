import BauschkeLean.Chap01.Text_1_0_8
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap20.Example_20_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set
open SetValuedOperator

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The standard monotonicity predicate on set-valued operators in the ambient Hilbert space. -/
abbrev operatorMonotone (A : SetValuedOperator H H) : Prop :=
  ∀ ⦃x u y v : H⦄, u ∈ A x → v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.49 works with a single-valued operator along a closed convex
  subset `C`, and the local source-facing notion is Rockafellar hemicontinuity along segments in
  `C`.
- `core/canonical`: the owner abstractions are the singleton-valued restriction operator
  `Function.toSetValuedOperatorOn`, the normal cone owner `N[C]`, and order-theoretic maximality
  for the monotonicity predicate on set-valued operators.
- `bridge/view`: `Function.IsHemicontinuousOn` is the minimal source-facing bridge for the
  subset-based segment condition, and the continuity-on-convex-set lemma is the canonical bridge
  from `ContinuousOn` to that source-facing condition.
- semantic recall: `lean_leansearch` returned continuity/inner-product lemmas such as
  `ContinuousOn.inner`, but no existing subset-based hemicontinuity owner matching this item.

Primitive data: an ambient map `A : H → H` whose restriction to `C` gives the singleton-valued
operator `A.toSetValuedOperatorOn C`.
Derived API: the continuity-on-convex-set bridge and the maximal-monotonicity theorem for
`A.toSetValuedOperatorOn C + N[C]`. -/

/-- The singleton-valued set-valued operator associated with `A` on `C`, taking value `{A x}` on
`C` and `∅` off `C`. -/
noncomputable def toSetValuedOperatorOn (A : H → H) (C : Set H) : SetValuedOperator H H := by
  classical
  exact fun x ↦ if hx : x ∈ C then ({A x} : Set H) else ∅

/-- A single-valued operator is hemicontinuous on `C` when every scalar slice along the segment
from `x` to `y` is right-continuous at `0`. -/
def IsHemicontinuousOn (A : H → H) (C : Set H) : Prop :=
  ∀ x y : C, ∀ z : H,
    ContinuousWithinAt (fun α : ℝ ↦ ⟪z, A (AffineMap.lineMap (x : H) y α)⟫_ℝ) (Set.Ioi 0) 0

/-- Helper for Proposition 20.49: near `0` from the right, the segment `AffineMap.lineMap x y α`
stays inside the convex set `C`. -/
private lemma eventually_lineMap_mem_of_convex {C : Set H} (hC_convex : Convex ℝ C)
    (x y : C) :
    ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), AffineMap.lineMap (x : H) y α ∈ C := by
  -- Right-near `0`, both `α > 0` and `α < 1`, so convexity keeps the segment point in `C`.
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with α hα_pos hα_lt
  exact hC_convex.lineMap_mem x.2 y.2 ⟨hα_pos.le, hα_lt.le⟩

-- Proof sketch: a convex set contains the whole segment between `x` and `y`, so continuity of
-- `A` on `C` makes the scalar slice `α ↦ ⟪z, A ((1 - α) • x + α • y)⟫` continuous on
-- `Set.Icc 0 1`; restricting that continuity to the right-neighborhood `Set.Ioi 0` at `0` gives
-- Rockafellar hemicontinuity on `C`.
/-- Continuity on a convex set implies Rockafellar hemicontinuity on that set. -/
theorem _root_.ContinuousOn.isHemicontinuousOn {A : H → H} {C : Set H}
    (hA : ContinuousOn A C) (hC_convex : Convex ℝ C) :
    A.IsHemicontinuousOn C := by
  intro x y z
  -- Compose the continuity of `A` on `C` with the segment map; convexity supplies the local
  -- domain condition for the composition theorem.
  let ℓ : ℝ → H := fun α ↦ AffineMap.lineMap (x : H) (y : H) α
  have hline :
      ContinuousWithinAt ℓ (Set.Ioi 0) 0 := by
    simpa [ℓ] using
      (AffineMap.lineMap_continuous : Continuous (AffineMap.lineMap (x : H) (y : H))).continuousWithinAt
  have hpreimage :
      ℓ ⁻¹' C ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    simpa [ℓ, Set.preimage] using eventually_lineMap_mem_of_convex hC_convex x y
  have hcomp :
      ContinuousWithinAt (A ∘ ℓ) (Set.Ioi 0) 0 := by
    have hAx : ContinuousWithinAt A C (ℓ 0) := by
      simpa [ℓ, AffineMap.lineMap_apply_zero] using hA (x : H) x.2
    exact hAx.comp_of_preimage_mem_nhdsWithin hline hpreimage
  -- Pairing with the fixed vector `z` preserves continuity of the scalar slice.
  simpa [ℓ, Function.comp] using (continuousWithinAt_const.inner hcomp)

section

variable [CompleteSpace H]

/-- Helper for Proposition 20.49: if `c + γ d` is nonnegative for every `γ ≥ 0`, then the slope
`d` is nonnegative. -/
private lemma nonneg_of_forall_nonneg_mul_add_nonneg {c d : ℝ}
    (h : ∀ γ ≥ 0, 0 ≤ c + γ * d) : 0 ≤ d := by
  by_contra hd
  have hd_neg : d < 0 := lt_of_not_ge hd
  let γ : ℝ := |c| / (-d) + 1
  have hγ_pos : 0 < γ := by
    have hdiv_nonneg : 0 ≤ |c| / (-d) := by
      have hden_pos : 0 < -d := by
        linarith
      exact div_nonneg (abs_nonneg c) hden_pos.le
    dsimp [γ]
    linarith
  have hγ_nonneg : 0 ≤ γ := hγ_pos.le
  have hγ := h γ hγ_nonneg
  have hγd : γ * d = d - |c| := by
    have hd_ne : d ≠ 0 := by
      linarith
    dsimp [γ]
    calc
      (|c| / -d + 1) * d = (|c| / -d) * d + d := by ring
      _ = |c| * (d / -d) + d := by ring
      _ = |c| * (-1 : ℝ) + d := by
            have hdiv : d / -d = (-1 : ℝ) := by
              field_simp [hd_ne]
            rw [hdiv]
      _ = d - |c| := by ring
  have hc_abs : c - |c| ≤ 0 := sub_nonpos.mpr (le_abs_self c)
  linarith

/-- Helper for Proposition 20.49: the normal cone at a point of `C` is closed under
nonnegative scaling. -/
private lemma smul_mem_normalCone_of_nonneg {C : Set H} {x u : H} (hx : x ∈ C)
    (hu : u ∈ N[C] x) {γ : ℝ} (hγ : 0 ≤ γ) :
    γ • u ∈ N[C] x := by
  -- Rewrite normal-cone membership to the pointwise variational inequality and scale it.
  rw [Set.normalCone_of_mem hx] at hu ⊢
  refine (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := γ • u) (p := x)).2 ?_
  intro y hy
  have hu' := (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := u) (p := x)).1 hu y hy
  simpa [real_inner_smul_right] using mul_nonpos_of_nonneg_of_nonpos hγ hu'

/-- Helper for Proposition 20.49: the zero vector always belongs to the normal cone at a point of
`C`. -/
private lemma zero_mem_normalCone {C : Set H} {x : H} (hx : x ∈ C) :
    (0 : H) ∈ N[C] x := by
  -- The defining variational inequality is trivial for the zero vector.
  rw [Set.normalCone_of_mem hx]
  refine (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := (0 : H)) (p := x)).2 ?_
  intro y hy
  simp

/-- Helper for Proposition 20.49: a point monotonically related to
`gra (A.toSetValuedOperatorOn C + N[C])` must already lie in `C`. -/
private lemma mem_set_of_mintyRelated_add_normalCone {C : Set H}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (A : H → H) {z w : H}
    (hrel : ∀ ⦃x v : H⦄, v ∈ (A.toSetValuedOperatorOn C + N[C]) x →
      0 ≤ ⟪z - x, w - v⟫_ℝ) :
    z ∈ C := by
  let hNCmax : Maximal operatorMonotone (N[C]) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hzero_rel : ∀ ⦃x u : H⦄, u ∈ N[C] x → 0 ≤ ⟪z - x, (0 : H) - u⟫_ℝ := by
    intro x u hu
    have hx : x ∈ C := by
      by_contra hx
      simpa [Set.normalCone_of_not_mem hx] using hu
    have hscaled :
        ∀ γ : ℝ, γ ≥ 0 → 0 ≤ ⟪z - x, w - (A x + γ • u)⟫_ℝ := by
      intro (γ : ℝ) hγ
      have hAx : A x ∈ A.toSetValuedOperatorOn C x := by
        simp [toSetValuedOperatorOn, hx]
      have hγu : γ • u ∈ N[C] x :=
        smul_mem_normalCone_of_nonneg (C := C) hx hu (γ := γ) hγ
      exact hrel (Set.mem_add.2 ⟨A x, hAx, γ • u, hγu, by simp⟩)
    have hu_nonneg : 0 ≤ ⟪x - z, u⟫_ℝ := by
      apply nonneg_of_forall_nonneg_mul_add_nonneg
      intro (γ : ℝ) hγ
      have hγineq := hscaled γ hγ
      have hsplit :
          ⟪z - x, w - (A x + γ • u)⟫_ℝ =
            ⟪x - z, A x - w⟫_ℝ + γ * ⟪x - z, u⟫_ℝ := by
        have hsum_eq : w - (A x + γ • u) = (w - A x) - γ • u := by
          abel_nf
        have hpair₁ : ⟪z - x, w - A x⟫_ℝ = ⟪x - z, A x - w⟫_ℝ := by
          have hzx : z - x = -(x - z) := by
            abel_nf
          have hwA : w - A x = -(A x - w) := by
            abel_nf
          rw [hzx, hwA, inner_neg_left, inner_neg_right]
          simp
        have hpair₂ : ⟪z - x, u⟫_ℝ = -⟪x - z, u⟫_ℝ := by
          have hzx : z - x = -(x - z) := by
            abel_nf
          rw [hzx, inner_neg_left]
        calc
          ⟪z - x, w - (A x + γ • u)⟫_ℝ
              = ⟪z - x, (w - A x) - γ • u⟫_ℝ := by rw [hsum_eq]
          _ = ⟪z - x, w - A x⟫_ℝ - ⟪z - x, γ • u⟫_ℝ := by
                rw [inner_sub_right]
          _ = ⟪z - x, w - A x⟫_ℝ - γ * ⟪z - x, u⟫_ℝ := by
                rw [real_inner_smul_right]
          _ = ⟪x - z, A x - w⟫_ℝ + γ * ⟪x - z, u⟫_ℝ := by
                rw [hpair₁, hpair₂]
                ring
      simpa [hsplit] using hγineq
    have hzu : ⟪z - x, u⟫_ℝ = -⟪x - z, u⟫_ℝ := by
      have hzx : z - x = -(x - z) := by
        abel_nf
      rw [hzx, inner_neg_left]
    have hzu_nonpos : ⟪z - x, u⟫_ℝ ≤ 0 := by
      rw [hzu]
      linarith
    simpa [sub_eq_add_neg, inner_neg_right] using neg_nonneg.mpr hzu_nonpos
  have hz_zero : (0 : H) ∈ N[C] z := by
    exact (SetValuedOperator.Maximal.mem_iff hNCmax z 0).2 fun {_x _u} hu ↦ hzero_rel hu
  by_contra hz
  simpa [Set.normalCone_of_not_mem hz] using hz_zero

/-- Helper for Proposition 20.49: the Minty relation along the segment from `z` to `x` passes to
the limit `α ↓ 0` and yields the endpoint variational inequality. -/
private lemma limitPairing_nonneg_of_mintyRelated_add_normalCone {C : Set H}
    (hC_convex : Convex ℝ C) (A : H → H) (hA_hemi : A.IsHemicontinuousOn C)
    {z w : H} (hz : z ∈ C)
    (hrel : ∀ ⦃x v : H⦄, v ∈ (A.toSetValuedOperatorOn C + N[C]) x →
      0 ≤ ⟪z - x, w - v⟫_ℝ) :
    ∀ x ∈ C, 0 ≤ ⟪x - z, A z - w⟫_ℝ := by
  intro x hx
  let zC : C := ⟨z, hz⟩
  let xC : C := ⟨x, hx⟩
  let s : ℝ → H := fun α ↦ AffineMap.lineMap z x α
  have hEventually :
      ∀ᶠ α : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 ≤ ⟪x - z, A (s α) - w⟫_ℝ := by
    -- For small positive `α`, the segment point `s α` lies in `C`, so the Minty relation may be
    -- tested there with the normal-cone vector `0`.
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with α hα_pos hα_lt
    have hs_mem : s α ∈ C := by
      exact hC_convex.lineMap_mem hz hx ⟨hα_pos.le, hα_lt.le⟩
    have hzero : (0 : H) ∈ N[C] (s α) :=
      zero_mem_normalCone hs_mem
    have hgraph :
        A (s α) ∈ (A.toSetValuedOperatorOn C + N[C]) (s α) := by
      refine Set.mem_add.2 ⟨A (s α), ?_, 0, hzero, by simp⟩
      simp [toSetValuedOperatorOn, hs_mem]
    have hαineq : 0 ≤ ⟪z - s α, w - A (s α)⟫_ℝ := hrel hgraph
    have hrewrite :
        ⟪z - s α, w - A (s α)⟫_ℝ = α * ⟪x - z, A (s α) - w⟫_ℝ := by
      have hzsub : z - s α = α • (z - x) := by
        calc
          z - s α = -(α • (x - z)) := by
              dsimp [s]
              rw [AffineMap.lineMap_apply_module']
              abel_nf
          _ = α • (z - x) := by
              have hzx : z - x = -(x - z) := by
                abel_nf
              rw [hzx, smul_neg]
      have hpair :
          ⟪z - x, w - A (s α)⟫_ℝ = ⟪x - z, A (s α) - w⟫_ℝ := by
        have hzx : z - x = -(x - z) := by
          abel_nf
        have hAw : w - A (s α) = -(A (s α) - w) := by
          abel_nf
        rw [hzx, hAw, inner_neg_left, inner_neg_right]
        simp
      calc
        ⟪z - s α, w - A (s α)⟫_ℝ
            = ⟪α • (z - x), w - A (s α)⟫_ℝ := by rw [hzsub]
        _ = α * ⟪z - x, w - A (s α)⟫_ℝ := by rw [real_inner_smul_left]
        _ = α * ⟪x - z, A (s α) - w⟫_ℝ := by rw [hpair]
    have hmul_nonneg : 0 ≤ α * ⟪x - z, A (s α) - w⟫_ℝ := by
      simpa [hrewrite] using hαineq
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul_nonneg) hα_pos
  have hslice :
      ContinuousWithinAt (fun α : ℝ ↦ ⟪x - z, A (s α)⟫_ℝ) (Set.Ioi 0) 0 :=
    hA_hemi zC xC (x - z)
  have hlimit :
      Filter.Tendsto (fun α : ℝ ↦ ⟪x - z, A (s α) - w⟫_ℝ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ⟪x - z, A z - w⟫_ℝ) := by
    -- Subtract the constant pairing with `w` from the hemicontinuous scalar slice.
    simpa [ContinuousWithinAt, s, inner_sub_right, AffineMap.lineMap_apply_zero] using
      (hslice.sub continuousWithinAt_const)
  exact ge_of_tendsto hlimit hEventually

/-- Helper for Proposition 20.49: pointwise endpoint inequalities imply residual membership in the
normal cone. -/
private lemma neg_mem_normalCone_of_forall_inner_nonneg {C : Set H} {z r : H}
    (hz : z ∈ C) (hineq : ∀ x ∈ C, 0 ≤ ⟪x - z, r⟫_ℝ) :
    -r ∈ N[C] z := by
  -- Rewrite normal-cone membership to the pointwise characterization and negate the pairing.
  rw [Set.normalCone_of_mem hz]
  refine (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := -r) (p := z)).2 ?_
  intro x hx
  have hxineq := hineq x hx
  simpa [inner_neg_right] using neg_nonpos.mpr hxineq

-- Proof sketch: use the maximal-monotonicity criterion from Definition 20.20. A graph point
-- monotonically related to `gra (A.toSetValuedOperatorOn C + N[C])` first lies over `C` by maximal
-- monotonicity of `N[C]` (Example 20.26); then apply the monotonicity hypothesis on `C` and let
-- the segment parameter tend to `0` via hemicontinuity to show that the residual vector belongs to
-- `N[C]`, hence the point already lies in the graph of the sum.
/-- Proposition 20.49: if `C` is a nonempty closed convex subset of a real Hilbert space and `A`
is monotone and hemicontinuous on `C` in Rockafellar's sense, then the sum of the restricted
singleton-valued operator `A.toSetValuedOperatorOn C` with the normal cone operator `N[C]` is
maximally monotone. -/
theorem ofFunction_add_normalCone_isMaximallyMonotone_of_monotoneOn_hemicontinuousOn
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (A : H → H) (hA_mono : operatorMonotone (A.toSetValuedOperatorOn C))
    (hA_hemi : A.IsHemicontinuousOn C) :
    Maximal operatorMonotone (A.toSetValuedOperatorOn C + N[C]) := by
  change Maximal SetValuedOperator.IsMonotone (A.toSetValuedOperatorOn C + N[C])
  rw [SetValuedOperator.maximal_iff_mem_iff]
  let hNCmax : Maximal operatorMonotone (N[C]) :=
    Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed hC_convex
  have hNC_mono : operatorMonotone (N[C]) := hNCmax.1
  have hsum_mono : operatorMonotone (A.toSetValuedOperatorOn C + N[C]) := by
    -- Decompose both graph points of the sum and add the monotonicity inequalities of the two
    -- summands.
    intro x u y v hu hv
    rcases Set.mem_add.mp hu with ⟨ux, hux, nx, hnx, rfl⟩
    rcases Set.mem_add.mp hv with ⟨uy, huy, ny, hny, rfl⟩
    have hA : 0 ≤ ⟪x - y, ux - uy⟫_ℝ := hA_mono hux huy
    have hN : 0 ≤ ⟪x - y, nx - ny⟫_ℝ := hNC_mono hnx hny
    have hsum :
        0 ≤ ⟪x - y, ux - uy⟫_ℝ + ⟪x - y, nx - ny⟫_ℝ := add_nonneg hA hN
    have hdecomp : (ux + nx) - (uy + ny) = (ux - uy) + (nx - ny) := by
      abel_nf
    simpa [hdecomp, inner_add_right] using hsum
  intro z w
  constructor
  · intro hw x v hv
    exact hsum_mono hw hv
  · intro hrel
    -- First force the test point into `C` using maximality of the normal cone.
    have hz : z ∈ C :=
      mem_set_of_mintyRelated_add_normalCone hC_nonempty hC_closed hC_convex A hrel
    -- Then pass the Minty relation to the limit along segments issued from `z`.
    have hineq : ∀ x ∈ C, 0 ≤ ⟪x - z, A z - w⟫_ℝ :=
      limitPairing_nonneg_of_mintyRelated_add_normalCone hC_convex A hA_hemi hz hrel
    have hresidual : w - A z ∈ N[C] z := by
      have hnormal : -(A z - w) ∈ N[C] z :=
        neg_mem_normalCone_of_forall_inner_nonneg hz hineq
      simpa using hnormal
    -- Finally rebuild the graph witness `(A z, w - A z)` for the sum operator at `z`.
    refine Set.mem_add.2 ⟨A z, ?_, w - A z, hresidual, ?_⟩
    · simp [toSetValuedOperatorOn, hz]
    · abel_nf

end

end Function
