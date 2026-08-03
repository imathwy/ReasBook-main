import BauschkeLean.Chap06.Proposition_6_47
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap15.Definition_15_24_1
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap17.Corollary_17_42
import BauschkeLean.Chap27.Corollary_27_3

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator

noncomputable section

universe u

namespace ERealFunction

section AbstractConstrainedMinimizationProblems

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Semantic recall note: `lean_leansearch` only surfaced generic projection lemmas here. The
-- verified project-facing owners for this item are Corollary 27.3 together with the Chapter 16
-- bridge `subdifferential_setIndicator_eq_normalCone` and the Chapter 12 indicator/projection API.

/- Source/core/bridge triage:
- `source-facing`: Proposition 27.8 is the optimality system for minimizing `f` over a closed
  convex constraint set `C`.
- `core/canonical`: the reusable owners are Corollary 27.3 for the pointwise sum
  `f + ι[C]` and Example 16.13's identification `∂ ι[C] = N[C]`.
- `bridge/view`: `SetConstraintRegularity` packages the book's three regularity alternatives and
  `SetConstraintRegularity.toPointwiseAddRegularity` converts them to the Chapter 27 owner.
-/

/-- The three source regularity alternatives in Proposition 27.8 for the constrained problem
`minimize f(x)` over `x ∈ C`. -/
inductive SetConstraintRegularity
    (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) : Prop where
  | zero_mem_sri
      (hsri : (0 : H) ∈ sri (C - effectiveDomain f)) :
      SetConstraintRegularity f C
  | finiteDimensional_polyhedral_ri
      (hfin : FiniteDimensional ℝ H)
      (hpolyC : C.IsPolyhedral)
      (hri : (C ∩ ri (effectiveDomain f)).Nonempty) :
      SetConstraintRegularity f C
  | finiteDimensional_polyhedral_function
      (hfin : FiniteDimensional ℝ H)
      (hpolyC : C.IsPolyhedral)
      (hpolyf : Polyhedral f.asEReal)
      (hfeas : (C ∩ effectiveDomain f).Nonempty) :
      SetConstraintRegularity f C

/-- Helper for Proposition 27.8: the product of a polyhedral set with the nonnegative half-line
is polyhedral. -/
private theorem Set.IsPolyhedral.prodIciZero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : C.IsPolyhedral) :
    (C ×ˢ Set.Ici (0 : ℝ)).IsPolyhedral := by
  classical
  -- Repackage the new vertical constraint `0 ≤ r` as one extra closed half-space.
  rcases hC with ⟨t, hCeq⟩
  refine ⟨
    t.image (fun p : (E →L[ℝ] ℝ) × ℝ ↦ (p.1.comp (ContinuousLinearMap.fst ℝ E ℝ), p.2)) ∪
      {(-ContinuousLinearMap.snd ℝ E ℝ, (0 : ℝ))},
    ?_⟩
  ext q
  rcases q with ⟨x, r⟩
  rw [hCeq]
  simp only [mem_prod, mem_iInter, Prod.forall, mem_Ici, Finset.union_singleton,
    Finset.mem_insert, Finset.mem_image, Prod.exists, iInter_iInter_eq_or_left,
    iInter_exists, mem_inter_iff, and_imp, Prod.mk.injEq]
  constructor
  · rintro ⟨hxt, hr⟩
    refine ⟨?_, ?_⟩
    · simpa [Set.mem_closedHalfspace_iff] using hr
    intro a b i i₁ hi hcomp hb
    subst hcomp hb
    exact hxt i i₁ hi
  · rintro ⟨hr, hprod⟩
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hprod _ _ a b hab rfl rfl
    · simpa [Set.mem_closedHalfspace_iff] using hr

/-- Helper for Proposition 27.8: the indicator of a polyhedral constraint set is a polyhedral
extended-real-valued function. -/
private theorem indicatorAsEReal_polyhedral_of_isPolyhedral
    {C : Set H} (hC_polyhedral : C.IsPolyhedral) :
    Polyhedral (ι[C]).asEReal := by
  -- Rewrite the epigraph as `C × ℝ≥0` and reuse the product description.
  rw [polyhedral_iff]
  have hprod : (C ×ˢ Set.Ici (0 : ℝ)).IsPolyhedral :=
    Set.IsPolyhedral.prodIciZero hC_polyhedral
  have hepigraph :
      epigraph (ι[C]).asEReal = C ×ˢ Set.Ici (0 : ℝ) := by
    ext p
    rcases p with ⟨x, t⟩
    rw [mem_epigraph_iff]
    by_cases hx : x ∈ C
    · simp [ERealFunction.indicator, hx]
    · simp [ERealFunction.indicator, hx]
  simpa [hepigraph] using hprod

/-- Helper for Proposition 27.8: the scaled proximity operator of the indicator of a nonempty
closed convex set is its metric projection. -/
private theorem scaledProxIndicator_eq_projectionPoint_of_nonempty_isClosed_convex
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (γ : PosReal) :
    Prox[γ, ι[C], indicator_mem_gammaZero_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex] =
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) := by
  -- Collapse the harmless positive scaling `γ • ι[C]` back to `ι[C]`.
  have hsmul_indicator : γ • ι[C] = ι[C] := by
    funext y
    apply Subtype.ext
    by_cases hy : y ∈ C
    · simp [ERealFunction.indicator, hy]
    · have htop :
        (((γ : ℝ) : EReal) * ⊤) = ⊤ :=
          EReal.coe_mul_top_of_pos γ.2
      simpa [ERealFunction.indicator, hy] using htop
  change Prox[γ • ι[C], smul_mem_gammaZero (ι[C])
      (indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) γ] =
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
  ext x
  -- The unscaled indicator proximity operator is exactly the projector.
  simpa [hsmul_indicator] using
    congrArg (fun T : H → H ↦ T x) <|
      proximityOperator_indicator_eq_projectionPoint_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex

/-- Helper for Proposition 27.8: reversing both a difference and the second vector leaves the real
inner product unchanged. -/
private theorem inner_sub_neg_right_eq_inner_sub {x y u : H} :
    ⟪y - x, -u⟫_ℝ = ⟪x - y, u⟫_ℝ := by
  -- Both signs cancel after rewriting `y - x = -(x - y)`.
  have hsub : y - x = -(x - y) := by
    abel
  calc
    ⟪y - x, -u⟫_ℝ = -⟪y - x, u⟫_ℝ := by rw [inner_neg_right]
    _ = -(-⟪x - y, u⟫_ℝ) := by rw [hsub, inner_neg_left]
    _ = ⟪x - y, u⟫_ℝ := by ring

/-- The regularity hypotheses in Proposition 27.8 imply that the constraint set is nonempty. -/
theorem SetConstraintRegularity.nonempty
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hregular : SetConstraintRegularity f C) :
    C.Nonempty := by
  -- Each regularity branch contains an explicit feasible-point witness for `C`.
  cases hregular with
  | zero_mem_sri hsri =>
      rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
      rcases Set.mem_sub.mp hzero with ⟨x, hxC, y, hy, hxy⟩
      exact ⟨x, hxC⟩
  | finiteDimensional_polyhedral_ri _ _ hri =>
      rcases hri with ⟨x, hxC, _⟩
      exact ⟨x, hxC⟩
  | finiteDimensional_polyhedral_function _ _ _ hfeas =>
      rcases hfeas with ⟨x, hxC, _⟩
      exact ⟨x, hxC⟩

/-- A helper for Proposition 27.8: Corollary 27.3 is applied to the indicator of `C`, and this
theorem converts the source regularity alternatives into the Chapter 27 pointwise-sum regularity
owner. -/
theorem SetConstraintRegularity.toPointwiseAddRegularity
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hregular : SetConstraintRegularity f C) :
    PointwiseAddRegularity f (ι[C]) := by
  -- Match each source regularity branch with the corresponding Chapter 27 constructor.
  cases hregular with
  | zero_mem_sri hsri =>
      refine PointwiseAddRegularity.zero_mem_sri ?_
      simpa [effectiveDomain_indicator] using hsri
  | finiteDimensional_polyhedral_ri hfin hpolyC hri =>
      refine PointwiseAddRegularity.finiteDimensional_polyhedral_g
        hfin (indicatorAsEReal_polyhedral_of_isPolyhedral hpolyC) ?_
      simpa [effectiveDomain_indicator] using hri
  | finiteDimensional_polyhedral_function hfin hpolyC hpolyf hfeas =>
      refine PointwiseAddRegularity.finiteDimensional_polyhedral_fg
        hfin hpolyf (indicatorAsEReal_polyhedral_of_isPolyhedral hpolyC) ?_
      simpa [effectiveDomain_indicator, Set.inter_comm] using hfeas

/-- Proposition 27.8 (1): if `C` is a closed convex subset of `H`, if `f ∈ Γ₀(H)`, and if one
of the three source regularity alternatives holds, then `xbar` solves `minimize f(x)` over
`x ∈ C` if and only if `xbar ∈ zer (N_C + ∂ f)`. -/
theorem mem_argminOn_iff_mem_zeros_normalCone_add_subdifferential_of_regularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hregular : SetConstraintRegularity f C) {xbar : H} :
    xbar ∈ Argmin[C] f.asEReal ↔
      xbar ∈ ((N[C]) + (∂ f)).zeros := by
  let hC_nonempty : C.Nonempty := hregular.nonempty
  have hindicator : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hregular' : PointwiseAddRegularity f (ι[C]) :=
    hregular.toPointwiseAddRegularity
  have hbot : ∀ x ∉ C, (f x : EReal) ≠ ⊥ := by
    intro x hx
    exact ne_of_gt (f x).2
  have hargmin :
      xbar ∈ Argmin (f.asEReal + (ι[C]).asEReal) ↔
        xbar ∈ ((∂ f) + (∂ ι[C])).zeros := by
    -- Corollary 27.3 handles the unconstrained sum `f + ι[C]`.
    simpa using
      (mem_argmin_add_iff_mem_zeros_subdifferential_add_of_regularity
        (f := f) (g := ι[C]) hf hindicator hregular' (xbar := xbar))
  rw [argminOn_eq_inter_argmin_add_indicator f.asEReal C hbot]
  constructor
  · rintro ⟨hxC, hxarg⟩
    have hxzero :
        xbar ∈ ((∂ f) + (∂ ι[C])).zeros :=
      hargmin.mp hxarg
    rw [SetValuedOperator.mem_zeros_iff] at hxzero ⊢
    change 0 ∈ (∂ f) xbar + (∂ ι[C]) xbar at hxzero
    change 0 ∈ N[C] xbar + (∂ f) xbar
    rw [subdifferential_setIndicator_eq_normalCone C hC_nonempty] at hxzero
    rw [Set.mem_add] at hxzero ⊢
    rcases hxzero with ⟨u, hu, v, hv, huv⟩
    have hsum : v + u = 0 := by
      simpa [add_comm] using huv
    exact ⟨v, hv, u, hu, hsum⟩
  · intro hxzero
    have hxzero' :
        xbar ∈ ((∂ f) + (∂ ι[C])).zeros := by
      rw [SetValuedOperator.mem_zeros_iff] at hxzero ⊢
      change 0 ∈ N[C] xbar + (∂ f) xbar at hxzero
      change 0 ∈ (∂ f) xbar + (∂ ι[C]) xbar
      rw [subdifferential_setIndicator_eq_normalCone C hC_nonempty]
      rw [Set.mem_add] at hxzero ⊢
      rcases hxzero with ⟨u, hu, v, hv, huv⟩
      have hsum : v + u = 0 := by
        simpa [add_comm] using huv
      exact ⟨v, hv, u, hu, hsum⟩
    have hxarg : xbar ∈ Argmin (f.asEReal + (ι[C]).asEReal) :=
      hargmin.mpr hxzero'
    have hxC : xbar ∈ C := by
      by_contra hxC
      rw [SetValuedOperator.mem_zeros_iff] at hxzero
      change 0 ∈ N[C] xbar + (∂ f) xbar at hxzero
      rw [Set.normalCone_of_not_mem hxC, Set.mem_add] at hxzero
      simpa using hxzero
    exact ⟨hxC, hxarg⟩

section ClosedConvexConstraintSet

variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Proposition 27.8 (2): for a nonempty closed convex set `C`, the zero-set condition
`xbar ∈ zer (N_C + ∂ f)` is equivalent to `xbar` lying in the image under `Prox_{γ f}` of the
fixed points of `(2 P_C - Id) ∘ (2 Prox_{γ f} - Id)`. -/
theorem mem_zeros_normalCone_add_subdifferential_iff_mem_scaledProx_image_fixedPoints
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (γ : PosReal) {xbar : H} :
    xbar ∈ ((N[C]) + (∂ f)).zeros ↔
      xbar ∈ Prox[γ, f, hf] '' Function.fixedPoints
        ((fun x : H ↦ (2 : ℝ) • P x - x) ∘
          fun x : H ↦ (2 : ℝ) • Prox[γ, f, hf] x - x) := by
  have hindicator : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  -- Corollary 27.3 already has the right reflected-composition form once `f := ι[C]`.
  simpa [scaledProxIndicator_eq_projectionPoint_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex γ,
    subdifferential_setIndicator_eq_normalCone C hC_nonempty] using
    (mem_zeros_subdifferential_add_iff_mem_scaledProx_image_fixedPoints_reflectedProximity
      (f := ι[C]) (g := f) hindicator hf γ (xbar := xbar))

end ClosedConvexConstraintSet

/-- Proposition 27.8 (3): `xbar ∈ zer (N_C + ∂ f)` is equivalent to the existence of
`u ∈ N_C(xbar)` such that `-u ∈ ∂ f(xbar)`. -/
theorem mem_zeros_normalCone_add_subdifferential_iff_exists_mem_normalCone_neg
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xbar : H} :
    xbar ∈ ((N[C]) + (∂ f)).zeros ↔
      ∃ u : H, u ∈ N[C] xbar ∧ -u ∈ (∂ f) xbar := by
  -- Unfold the zero-set condition into a pointwise Minkowski-sum witness.
  rw [SetValuedOperator.mem_zeros_iff]
  change 0 ∈ N[C] xbar + (∂ f) xbar ↔
    ∃ u : H, u ∈ N[C] xbar ∧ -u ∈ (∂ f) xbar
  rw [Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hv' : v = -u := by
      simpa using eq_neg_of_add_eq_zero_right huv
    have hneg : -u ∈ (∂ f) xbar := by
      simpa [hv'] using hv
    exact ⟨u, hu, hneg⟩
  · rintro ⟨u, hu, hneg⟩
    have hsum : u + -u = 0 := by
      simp
    exact ⟨u, hu, -u, hneg, hsum⟩

/-- Proposition 27.8 (4): `xbar ∈ zer (N_C + ∂ f)` is equivalent to the existence of
`u ∈ ∂ f(xbar)` such that `-u ∈ N_C(xbar)`. -/
theorem mem_zeros_normalCone_add_subdifferential_iff_exists_mem_subdifferential_neg
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xbar : H} :
    xbar ∈ ((N[C]) + (∂ f)).zeros ↔
      ∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[C] xbar := by
  -- The same zero-set witness can be read with the subgradient as the chosen summand.
  rw [SetValuedOperator.mem_zeros_iff]
  change 0 ∈ N[C] xbar + (∂ f) xbar ↔
    ∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[C] xbar
  rw [Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = -v := by
      simpa using eq_neg_of_add_eq_zero_left huv
    have hneg : -v ∈ N[C] xbar := by
      simpa [hu'] using hu
    exact ⟨v, hv, hneg⟩
  · rintro ⟨u, hu, hneg⟩
    have hsum : -u + u = 0 := by
      simp
    exact ⟨-u, hneg, u, hu, hsum⟩

/-- Proposition 27.8 (5): the witness condition
`∃ u ∈ ∂ f(xbar), -u ∈ N_C(xbar)` is equivalent to the source variational inequality
on `C`. -/
theorem exists_mem_subdifferential_neg_iff_mem_and_forall_inner_le_zero
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xbar : H} :
    (∃ u ∈ (∂ f) xbar, -u ∈ N[C] xbar) ↔
      xbar ∈ C ∧
        ∃ u ∈ (∂ f) xbar, ∀ y ∈ C, ⟪xbar - y, u⟫_ℝ ≤ 0 := by
  constructor
  · rintro ⟨u, hu, hneg⟩
    by_cases hx : xbar ∈ C
    · rw [Set.normalCone_of_mem hx] at hneg
      have hineq :
          ∀ y ∈ C, ⟪y - xbar, -u⟫_ℝ ≤ 0 :=
        (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := -u) (p := xbar)).1 hneg
      refine ⟨hx, u, hu, ?_⟩
      intro y hy
      rw [← inner_sub_neg_right_eq_inner_sub (x := xbar) (y := y) (u := u)]
      exact hineq y hy
    · rw [Set.normalCone_of_not_mem hx] at hneg
      simp at hneg
  · rintro ⟨hx, u, hu, hineq⟩
    rw [Set.normalCone_of_mem hx]
    refine ⟨u, hu, ?_⟩
    -- Rewrite the source variational inequality into the normal-cone owner.
    exact (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := -u) (p := xbar)).2
      (fun y hy ↦ by
        rw [inner_sub_neg_right_eq_inner_sub (x := xbar) (y := y) (u := u)]
        exact hineq y hy)

/-- Proposition 27.8 (6): if `xbar` lies in `interior (effectiveDomain f)` and the finite real
representative of `f` has Gâteaux gradient `gradf` at `xbar`, then
`xbar ∈ zer (N_C + ∂ f)` is equivalent to `-gradf ∈ N_C(xbar)`. -/
theorem
    mem_zeros_normalCone_add_subdifferential_iff_neg_gradient_mem_normalCone_of_gateauxDerivative
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} {xbar gradf : H}
    (hxbar : xbar ∈ interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeAt
        (fun y ↦ (f y : EReal).toReal) (InnerProductSpace.toDualMap ℝ H gradf) xbar) :
    xbar ∈ ((N[C]) + (∂ f)).zeros ↔
      -gradf ∈ N[C] xbar := by
  -- Collapse the subdifferential fiber to the singleton `{gradf}`.
  have hsub : (∂ f) xbar = ({gradf} : Set H) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt_of_mem_interior_effectiveDomain
      hf hxbar hgrad
  rw [mem_zeros_normalCone_add_subdifferential_iff_exists_mem_subdifferential_neg]
  constructor
  · rintro ⟨u, hu, hneg⟩
    rw [hsub, Set.mem_singleton_iff] at hu
    simpa [hu] using hneg
  · intro hneg
    have hgrad_mem : gradf ∈ (∂ f) xbar := by
      simpa [hsub]
    exact ⟨gradf, hgrad_mem, hneg⟩

/-- Helper for Proposition 27.8: once the subdifferential fiber at `xbar` is explicitly the
singleton `{gradf}`, the zero-set condition identifies with `-gradf ∈ N_C(xbar)`. -/
theorem mem_zeros_normalCone_add_subdifferential_iff_neg_gradient_mem_normalCone
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xbar gradf : H}
    (hsub : (∂ f) xbar = ({gradf} : Set H)) :
    xbar ∈ ((N[C]) + (∂ f)).zeros ↔
      -gradf ∈ N[C] xbar := by
  rw [mem_zeros_normalCone_add_subdifferential_iff_exists_mem_subdifferential_neg]
  constructor
  · rintro ⟨u, hu, hneg⟩
    rw [hsub, Set.mem_singleton_iff] at hu
    simpa [hu] using hneg
  · intro hneg
    have hgrad_mem : gradf ∈ (∂ f) xbar := by
      simpa [hsub]
    exact ⟨gradf, hgrad_mem, hneg⟩

/-- Proposition 27.8 (7): the normal-cone condition `-gradf ∈ N_C(xbar)` is equivalent to the
source variational inequality `xbar ∈ C` and
`∀ y ∈ C, ⟪xbar - y, gradf⟫ ≤ 0`. -/
theorem neg_gradient_mem_normalCone_iff_mem_and_forall_inner_gradient_le_zero
    {C : Set H} {xbar gradf : H} :
    -gradf ∈ N[C] xbar ↔
      xbar ∈ C ∧ ∀ y ∈ C, ⟪xbar - y, gradf⟫_ℝ ≤ 0 := by
  constructor
  · intro hneg
    by_cases hx : xbar ∈ C
    · rw [Set.normalCone_of_mem hx] at hneg
      have hineq :
          ∀ y ∈ C, ⟪y - xbar, -gradf⟫_ℝ ≤ 0 :=
        (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := -gradf) (p := xbar)).1 hneg
      refine ⟨hx, ?_⟩
      intro y hy
      rw [← inner_sub_neg_right_eq_inner_sub (x := xbar) (y := y) (u := gradf)]
      exact hineq y hy
    · rw [Set.normalCone_of_not_mem hx] at hneg
      simp at hneg
  · rintro ⟨hx, hineq⟩
    rw [Set.normalCone_of_mem hx]
    -- Package the pointwise inequalities back into the normal-cone support bound.
    exact (innerSupremumOn_sub_singleton_le_zero_iff (C := C) (u := -gradf) (p := xbar)).2
      (fun y hy ↦ by
        rw [inner_sub_neg_right_eq_inner_sub (x := xbar) (y := y) (u := gradf)]
        exact hineq y hy)

section ClosedConvexConstraintSet

variable {C : Set H}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

/-- Proposition 27.8 (8): the normal-cone condition `-gradf ∈ N_C(xbar)` is equivalent to the
projection fixed-point identity `xbar = P_C (xbar - γ gradf)`. -/
theorem neg_gradient_mem_normalCone_iff_eq_projectionPoint
    (γ : PosReal) {xbar gradf : H} :
    -gradf ∈ N[C] xbar ↔
      xbar = P (xbar - (γ : ℝ) • gradf) := by
  have hscaled_iff :
      (γ : ℝ) • (-gradf) ∈ N[C] xbar ↔ -gradf ∈ N[C] xbar := by
    constructor
    · intro hscaled
      have hscaled_neg : -((γ : ℝ) • gradf) ∈ N[C] xbar := by
        simpa [smul_neg] using hscaled
      have hscaled_vi :
          xbar ∈ C ∧ ∀ y ∈ C, ⟪xbar - y, (γ : ℝ) • gradf⟫_ℝ ≤ 0 := by
        simpa [smul_neg] using
          (neg_gradient_mem_normalCone_iff_mem_and_forall_inner_gradient_le_zero
            (C := C) (xbar := xbar) (gradf := (γ : ℝ) • gradf)).1 hscaled_neg
      rcases hscaled_vi with ⟨hx, hineq⟩
      refine (neg_gradient_mem_normalCone_iff_mem_and_forall_inner_gradient_le_zero
        (C := C) (xbar := xbar) (gradf := gradf)).2 ?_
      refine ⟨hx, ?_⟩
      intro y hy
      have hy_scaled :
          (γ : ℝ) * ⟪xbar - y, gradf⟫_ℝ ≤ 0 := by
        simpa [real_inner_smul_right] using hineq y hy
      nlinarith [γ.2, hy_scaled]
    · intro hneg
      have hvi :
          xbar ∈ C ∧ ∀ y ∈ C, ⟪xbar - y, gradf⟫_ℝ ≤ 0 :=
        (neg_gradient_mem_normalCone_iff_mem_and_forall_inner_gradient_le_zero
          (C := C) (xbar := xbar) (gradf := gradf)).1 hneg
      rcases hvi with ⟨hx, hineq⟩
      have hscaled_vi :
          xbar ∈ C ∧ ∀ y ∈ C, ⟪xbar - y, (γ : ℝ) • gradf⟫_ℝ ≤ 0 := by
        refine ⟨hx, ?_⟩
        intro y hy
        have hy0 : ⟪xbar - y, gradf⟫_ℝ ≤ 0 :=
          hineq y hy
        have hy_scaled :
            (γ : ℝ) * ⟪xbar - y, gradf⟫_ℝ ≤ 0 := by
          nlinarith [γ.2, hy0]
        simpa [real_inner_smul_right] using hy_scaled
      simpa [smul_neg] using
        (neg_gradient_mem_normalCone_iff_mem_and_forall_inner_gradient_le_zero
          (C := C) (xbar := xbar) (gradf := (γ : ℝ) • gradf)).2 hscaled_vi
  constructor
  · intro hneg
    have hscaled : (γ : ℝ) • (-gradf) ∈ N[C] xbar :=
      hscaled_iff.mpr hneg
    -- Proposition 6.47 turns the normal-cone residual into the projection identity.
    exact
      (eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex
        (x := xbar - (γ : ℝ) • gradf) (p := xbar)).2
        (by
          simpa [sub_eq_add_neg, smul_neg] using hscaled)
  · intro hproj
    have hscaled :
        (xbar - (γ : ℝ) • gradf) - xbar ∈ N[C] xbar :=
      (eq_projectionPoint_iff_sub_mem_normalCone_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex
        (x := xbar - (γ : ℝ) • gradf) (p := xbar)).1 hproj
    have hscaled' : (γ : ℝ) • (-gradf) ∈ N[C] xbar := by
      simpa [sub_eq_add_neg, smul_neg] using hscaled
    exact hscaled_iff.mp hscaled'

end ClosedConvexConstraintSet

end AbstractConstrainedMinimizationProblems

end ERealFunction
