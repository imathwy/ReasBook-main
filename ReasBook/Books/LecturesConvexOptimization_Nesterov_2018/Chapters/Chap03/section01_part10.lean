import Mathlib
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_1_24 (from Chap03) -/
noncomputable section

open scoped ConstrainedArgmin
open scoped TangentCone
open scoped WithTopConvexAnalysis
open scoped NormalCone
open scoped Topology

universe u

/- Theorem 3.1.24 lies in the chapter's constrained convex minimization / normal-cone domain.

Mandatory domain-style sampling before refinement:
- `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the owner API
  for feasible minimizers on a set, with textbook notation `argmin[Q] f`;
- `subdifferential` and `mem_subdifferential_iff` in `Definition_3_1_5`, the owner API for
  pointwise subdifferentials;
- `normalCone` and `mem_normalCone_iff` in `Definition_3_22`, the chapter owner API for textbook
  normal cones;
- `subgradient_inner_sub_nonneg_of_isMinOn` in `Theorem_3_1_5_6`, the intrinsic subgradient
  inequality at a constrained minimizer.

Best owner abstraction:
- the minimizer set owner `argmin[Q] f`;
- the pointwise owners `gStar ∈ ∂ (fun x ↦ (f x : WithTop ℝ))(xStar)` and `gStar ∈ N[Q] xStar`.

Primitive data:
- a feasible set `Q`;
- a convex objective `f`;
- a feasible point `xStar`;
- a candidate certificate `gStar`.

Derived API:
- the source-facing constrained-optimality criterion in normal-cone form;
- its textbook pairing reformulation via `mem_normalCone_iff`.

Source/core/bridge triage:
- source-facing: Theorem 3.1.24's constrained minimizer criterion;
- core/canonical: `argmin[Q] f`, `subdifferential`, and `normalCone`;
- bridge/view: the pairing reformulation through `mem_normalCone_iff`.

The later common-normal-cone/common-subdifferential propagation layer belongs downstream in
`Theorem_3_29`. This file stays focused on the normal-cone optimality criterion itself, while
using the chapter owner notation `argmin[Q] f` directly on the public theorem surface. The
textbook item lives on `ℝⁿ`, so the ambient layer here is the corresponding finite-dimensional
real inner-product-space owner rather than an unnecessarily more general complete-space wrapper.
-/

section NormalConeOwner

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Helper for Theorem 3.1.24: the subdifferential of a real-valued convex function at a point is
closed in the subgradient variable. -/
lemma isClosed_subdifferential_coe_real_at
    {f : V → ℝ} (xStar : V) :
    IsClosed (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) : Set V) := by
  let H : V → Set V := fun y ↦ {g : V | f xStar + inner ℝ g (y - xStar) ≤ f y}
  have hclosedH : ∀ y : V, IsClosed (H y) := by
    intro y
    refine isClosed_le ?_ continuous_const
    -- Each support inequality cuts out a closed half-space in the subgradient variable.
    have hcont : Continuous fun g : V ↦ f xStar + inner ℝ g (y - xStar) := by
      continuity
    simpa [H] using hcont
  have hrepr :
      (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) : Set V) = ⋂ y : V, H y := by
    -- Rewrite subdifferential membership as the family of affine support inequalities.
    ext g
    rw [mem_subdifferential_coe_real_iff]
    simp [H, ge_iff_le]
  rw [hrepr]
  exact isClosed_iInter hclosedH

/-- Helper for Theorem 3.1.24: the real-valued subdifferential is convex in the subgradient
variable. -/
lemma convex_subdifferential_coe_real_at
    {f : V → ℝ} (xStar : V) :
    Convex ℝ (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) := by
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rw [mem_subdifferential_coe_real_iff] at hg₁ hg₂ ⊢
  intro y
  have h₁ := hg₁ y
  have h₂ := hg₂ y
  -- Convex combinations preserve the affine lower-support inequalities.
  have hcombo :
      a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar)) ≤ f y := by
    have ha' := mul_le_mul_of_nonneg_left h₁ ha
    have hb' := mul_le_mul_of_nonneg_left h₂ hb
    calc
      a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar))
          ≤ a * f y + b * f y := add_le_add ha' hb'
      _ = f y := by
            rw [← add_mul, hab, one_mul]
  calc
    f y ≥ a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar)) := by
      exact hcombo
    _ = f xStar + inner ℝ (a • g₁ + b • g₂) (y - xStar) := by
      calc
        a * (f xStar + inner ℝ g₁ (y - xStar)) + b * (f xStar + inner ℝ g₂ (y - xStar))
            = (a + b) * f xStar + (a * inner ℝ g₁ (y - xStar) + b * inner ℝ g₂ (y - xStar)) := by
                ring
        _ = f xStar + (a * inner ℝ g₁ (y - xStar) + b * inner ℝ g₂ (y - xStar)) := by
              rw [hab]
              ring
        _ = f xStar + inner ℝ (a • g₁ + b • g₂) (y - xStar) := by
              simp [inner_add_left, inner_smul_left]

/-- Helper for Theorem 3.1.24: at an interior point of the effective domain, the real-valued
subdifferential is compact and convex. -/
lemma subdifferential_compact_convex_at
    [FiniteDimensional ℝ V]
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f) (xStar : V) :
    IsCompact (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) ∧
      Convex ℝ (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) := by
  let lift : V → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hf_withTop : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hxInt : xStar ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hbounded : Bornology.IsBounded (∂ lift(xStar)) :=
    (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
      hf_withTop hxInt).2
  have hclosed : IsClosed (∂ lift(xStar) : Set V) :=
    isClosed_subdifferential_coe_real_at (f := f) xStar
  have hconv : Convex ℝ (∂ lift(xStar)) := by
    -- Real-valued subgradients stay convex under affine interpolation.
    simpa [lift] using convex_subdifferential_coe_real_at (f := f) xStar
  exact ⟨Metric.isCompact_of_isClosed_isBounded hclosed hbounded, hconv⟩

/-- Helper for Theorem 3.1.24: a point of the pointed cone hull of `Q - xStar` is a nonnegative
multiple of one feasible displacement from `xStar`. -/
lemma exists_nonneg_smul_vsub_of_mem_pointedConeHull
    {Q : Set V} (hQ_convex : Convex ℝ Q) {xStar p : V} (hxStar : xStar ∈ Q)
    (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V))) :
    ∃ r : ℝ, 0 ≤ r ∧ ∃ x ∈ Q, p = r • (x - xStar) := by
  let S : Set V := Q -ᵥ ({xStar} : Set V)
  have hS_convex : Convex ℝ S := by
    -- Translating a convex set by `-xStar` preserves convexity.
    simpa [S, Set.vsub_singleton, vsub_eq_sub] using
      hQ_convex.sub (convex_singleton xStar)
  have hxSingleton : xStar ∈ ({xStar} : Set V) := by
    simp
  have hz : xStar -ᵥ xStar = (0 : V) := by
    simp [vsub_eq_sub]
  have hS_zero : (0 : V) ∈ S := by
    -- The zero displacement belongs to the displacement set because `xStar ∈ Q`.
    exact ⟨xStar, hxStar, xStar, hxSingleton, hz⟩
  have hconvexHull_pointed : (ConvexCone.hull ℝ S).Pointed :=
    ConvexCone.subset_hull hS_zero
  have hpointedHull_eq_convexHull : (PointedCone.hull ℝ S : Set V) = ConvexCone.hull ℝ S := by
    -- For a convex set containing `0`, the pointed hull agrees with the convex cone hull.
    ext v
    constructor
    · intro hv
      let C : PointedCone ℝ V := (ConvexCone.hull ℝ S).toPointedCone hconvexHull_pointed
      have hspan : PointedCone.hull ℝ S ≤ C := by
        refine Submodule.span_le.2 ?_
        intro y hy
        exact ConvexCone.subset_hull hy
      exact hspan hv
    · intro hv
      have hconvexHull_le : ConvexCone.hull ℝ S ≤ (PointedCone.hull ℝ S : ConvexCone ℝ V) := by
        exact ConvexCone.hull_min fun y hy ↦ PointedCone.subset_hull hy
      exact hconvexHull_le hv
  have hpS : p ∈ (PointedCone.hull ℝ S : Set V) := by
    simpa [S] using hp
  have hp' : p ∈ ConvexCone.hull ℝ S := by
    rwa [hpointedHull_eq_convexHull] at hpS
  rcases (ConvexCone.mem_hull_of_convex hS_convex).mp hp' with ⟨r, hr, y, hy, rfl⟩
  have hy' : y ∈ (fun z ↦ z - xStar) '' Q := by
    simpa [S, Set.vsub_singleton] using hy
  rcases hy' with ⟨x, hx, rfl⟩
  exact ⟨r, hr.le, x, hx, rfl⟩

/-- Helper for Theorem 3.1.24: the compact subdifferential admits a closest point to the normal
cone, and together with the projection of that point onto the cone one gets the two standard
variational inequalities for the closest pair. -/
lemma exists_closest_subgradient_normalCone_pair
    [FiniteDimensional ℝ V] [CompleteSpace V]
    {Q : Set V} {f : V → ℝ} {xStar : V}
    (hf_conv : ConvexOn ℝ Set.univ f) :
    ∃ g1Star ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
      ∃ g2Star ∈ N[Q] xStar,
        (∀ g1 ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
            inner ℝ (g2Star - g1Star) (g1 - g1Star) ≤ 0) ∧
          (∀ g2 ∈ N[Q] xStar,
            inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) := by
  let S : Set V := ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)
  let N : Set V := N[Q] xStar
  let lift : V → WithTop ℝ := fun x ↦ (f x : WithTop ℝ)
  have hf_withTop : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hxInt : xStar ∈ interior (dom lift) := by
    simp [lift, withTopEffectiveDomain]
  have hS_nonempty : S.Nonempty := by
    -- Interior points of a real-valued convex function admit at least one subgradient.
    simpa [S, lift] using
      (subdifferential_nonempty_and_isBounded_of_convexOn_effectiveDomain_of_mem_interior
        hf_withTop hxInt).1
  have hS_compact : IsCompact S := by
    -- The compactness package lets us minimize the distance to the normal cone on the
    -- subdifferential.
    simpa [S] using (subdifferential_compact_convex_at (V := V) hf_conv xStar).1
  have hS_convex : Convex ℝ S := by
    simpa [S] using (subdifferential_compact_convex_at (V := V) hf_conv xStar).2
  have hinf_cont : ContinuousOn (fun g : V ↦ Metric.infDist g N) S := by
    simpa [N] using (Metric.continuous_infDist_pt N).continuousOn
  rcases hS_compact.exists_isMinOn hS_nonempty hinf_cont with ⟨g1Star, hg1Star, hg1Min⟩
  have hzero_mem : (0 : V) ∈ N := by
    -- The normal cone is a cone, so it always contains the zero vector.
    change (0 : V) ∈ N[Q] xStar
    rw [mem_normalCone_iff]
    intro x hx
    simp
  have hN_nonempty : N.Nonempty := ⟨0, hzero_mem⟩
  have hN_closed : IsClosed N := by
    simpa [N] using (N[Q] xStar : ProperCone ℝ V).isClosed
  have hN_convex : Convex ℝ N := by
    simpa [N] using (N[Q] xStar : ProperCone ℝ V).convex
  rcases exists_unique_projection_point_of_nonempty_closed_convex
      N hN_nonempty hN_closed hN_convex g1Star with ⟨g2Star, hprojN, _⟩
  have hprojS : IsProjectionPointOn S g2Star g1Star := by
    -- Minimizing `infDist · N` on `S` turns `g1Star` into a projection of `g2Star` onto `S`.
    refine (IsProjectionPointOn.iff_isMinOn).2 ?_
    refine ⟨hg1Star, ?_⟩
    rw [isMinOn_iff]
    intro g1 hg1
    have hdist_le : dist g2Star g1Star ≤ dist g2Star g1 := by
      calc
        dist g2Star g1Star = Metric.infDist g1Star N := by
          simpa [dist_comm] using hprojN.2
        _ ≤ Metric.infDist g1 N := (isMinOn_iff.mp hg1Min) g1 hg1
        _ ≤ dist g1 g2Star := Metric.infDist_le_dist_of_mem hprojN.1
        _ = dist g2Star g1 := by rw [dist_comm]
    simpa [dist_eq_norm, norm_sub_rev] using hdist_le
  refine ⟨g1Star, hg1Star, g2Star, hprojN.1, ?_, ?_⟩
  · intro g1 hg1
    -- The projection inequality on the subdifferential gives the first closest-pair inequality.
    have hineq : 0 ≤ inner ℝ (g1Star - g2Star) (g1 - g1Star) :=
      hprojS.inner_sub_nonneg hS_convex hg1
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonpos.mpr hineq
  · intro g2 hg2
    -- The projection inequality on the normal cone gives the second closest-pair inequality.
    have hineq : 0 ≤ inner ℝ (g2Star - g1Star) (g2 - g2Star) :=
      hprojN.inner_sub_nonneg hN_convex hg2
    simpa [sub_eq_add_neg, inner_add_left, inner_neg_left] using neg_nonpos.mpr hineq

/-- Helper for Theorem 3.1.24: the normal-cone projection inequalities force the projection point
to be orthogonal to the gap vector `g2Star - g1Star`. -/
lemma normal_projection_gap_pairing_eq_zero
    [CompleteSpace V]
    {Q : Set V} {xStar g1Star g2Star : V}
    (hg2Star : g2Star ∈ N[Q] xStar)
    (hproj :
      ∀ g2 ∈ N[Q] xStar, inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) :
    inner ℝ g2Star (g2Star - g1Star) = 0 := by
  have hzero_mem : (0 : V) ∈ N[Q] xStar := by
    rw [mem_normalCone_iff]
    intro x hx
    simp
  have htwo_mem : (2 : ℝ) • g2Star ∈ N[Q] xStar := by
    rw [mem_normalCone_iff]
    intro x hx
    have hnormal := mem_normalCone_iff.mp hg2Star x hx
    simpa [inner_smul_left] using mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num) hnormal
  have hzero := hproj 0 hzero_mem
  have htwo := hproj ((2 : ℝ) • g2Star) htwo_mem
  have hzero' : ‖g2Star‖ ^ (2 : ℕ) ≤ inner ℝ g1Star g2Star := by
    simpa [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
      real_inner_comm, real_inner_self_eq_norm_sq] using hzero
  have htwo_simple : inner ℝ (g1Star - g2Star) g2Star ≤ 0 := by
    simpa [two_smul, sub_eq_add_neg] using htwo
  have htwo' : inner ℝ g1Star g2Star ≤ ‖g2Star‖ ^ (2 : ℕ) := by
    have htwo'':
        inner ℝ g1Star g2Star - ‖g2Star‖ ^ (2 : ℕ) ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_comm,
        real_inner_self_eq_norm_sq] using htwo_simple
    linarith
  have hEq : inner ℝ g1Star g2Star = ‖g2Star‖ ^ (2 : ℕ) := le_antisymm htwo' hzero'
  calc
    inner ℝ g2Star (g2Star - g1Star) = ‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star := by
      calc
        inner ℝ g2Star (g2Star - g1Star) = inner ℝ g2Star g2Star - inner ℝ g2Star g1Star := by
          rw [inner_sub_right]
        _ = ‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star := by
          rw [real_inner_self_eq_norm_sq, real_inner_comm]
    _ = 0 := by linarith

/-- Helper for Theorem 3.1.24: the gap vector of the closest pair belongs to the tangent cone. -/
lemma closest_pair_direction_mem_tangentCone
    [CompleteSpace V]
    {Q : Set V} (hQ_convex : Convex ℝ Q) {xStar g1Star g2Star : V}
    (hxStar : xStar ∈ Q) (hg2Star : g2Star ∈ N[Q] xStar)
    (hproj :
      ∀ g2 ∈ N[Q] xStar, inner ℝ (g1Star - g2Star) (g2 - g2Star) ≤ 0) :
    g2Star - g1Star ∈ 𝒯[Q] xStar := by
  have hzeroPair :
      inner ℝ g2Star (g2Star - g1Star) = 0 :=
    normal_projection_gap_pairing_eq_zero hg2Star hproj
  rw [mem_tangentCone_iff hQ_convex hxStar]
  intro g hg
  have hineq := hproj g hg
  have hEq : inner ℝ g1Star g2Star = ‖g2Star‖ ^ (2 : ℕ) := by
    have hzeroPair' : inner ℝ g2Star g2Star - inner ℝ g2Star g1Star = 0 := by
      simpa [sub_eq_add_neg, inner_add_right] using hzeroPair
    have hzeroPair'' : ‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star = 0 := by
      simpa [real_inner_self_eq_norm_sq, real_inner_comm] using hzeroPair'
    linarith
  have hbasic : inner ℝ g1Star g ≤ inner ℝ g2Star g := by
    have hineq' :
        inner ℝ g1Star g - inner ℝ g2Star g +
          (‖g2Star‖ ^ (2 : ℕ) - inner ℝ g1Star g2Star) ≤ 0 := by
      simpa [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
        real_inner_self_eq_norm_sq, real_inner_comm, add_assoc, add_left_comm, add_comm] using hineq
    linarith
  calc
    0 ≤ inner ℝ g2Star g - inner ℝ g1Star g := sub_nonneg.mpr hbasic
    _ = inner ℝ g (g2Star - g1Star) := by
          rw [inner_sub_right, real_inner_comm g g2Star, real_inner_comm g g1Star]

/-- Helper for Theorem 3.1.24: the convex directional derivative is nonnegative on every feasible
displacement from a constrained minimizer. -/
lemma directionalDerivativeReal_nonneg_on_feasible_displacement_of_mem_argmin
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) (hxArgmin : xStar ∈ argmin[Q] f)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))))
    {x : V} (hx : x ∈ Q) :
    0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (x - xStar) := by
  let lift : V → WithTop ℝ := fun z ↦ (f z : WithTop ℝ)
  have hf_withTop : ConvexOn ℝ (dom lift) (withTopRealPart lift) := by
    simpa [lift, withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hxMin : IsMinOn f Q xStar := (mem_constrainedArgmin_iff.mp hxArgmin).2
  have hlt : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have hquot_nonneg :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ (withTopRealPart lift (xStar + α • (x - xStar)) - withTopRealPart lift xStar) / α := by
    -- Along the feasible segment from `xStar` to `x`, every forward secant quotient is
    -- nonnegative because `xStar` minimizes `f` on `Q`.
    filter_upwards [self_mem_nhdsWithin, hlt] with α hαpos hαlt
    have hseg : xStar + α • (x - xStar) ∈ segment ℝ xStar x := by
      rw [segment_eq_image']
      exact ⟨α, ⟨le_of_lt hαpos, le_of_lt hαlt⟩, rfl⟩
    have hfeas : xStar + α • (x - xStar) ∈ Q := hQ_convex.segment_subset hxStar hx hseg
    have hmin_ineq : f xStar ≤ f (xStar + α • (x - xStar)) := (isMinOn_iff.mp hxMin) _ hfeas
    have hsub : 0 ≤ f (xStar + α • (x - xStar)) - f xStar := by
      linarith
    simpa [lift, withTopRealPart] using div_nonneg hsub hαpos.le
  have hzero : Filter.Tendsto (fun _ : ℝ ↦ 0) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds
  have hsecant :=
    tendsto_directionalSecantQuotient_of_mem_interior hf_withTop hxInt (x - xStar)
  -- Passing to the limit preserves the secant-quotient lower bound at `0`.
  exact le_of_tendsto_of_tendsto hzero hsecant hquot_nonneg

/-- Helper for Theorem 3.1.24: the convex directional derivative is nonnegative on the pointed
cone hull generated by feasible displacements. -/
lemma directionalDerivativeReal_nonneg_on_pointedConeHull_of_mem_argmin
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) (hxArgmin : xStar ∈ argmin[Q] f)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))))
    {p : V} (hp : p ∈ PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V))) :
    0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt p := by
  rcases exists_nonneg_smul_vsub_of_mem_pointedConeHull hQ_convex hxStar hp with
    ⟨r, hr, x, hx, rfl⟩
  have hdisp :
      0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
        hxInt (x - xStar) :=
    directionalDerivativeReal_nonneg_on_feasible_displacement_of_mem_argmin
      hQ_convex hf_conv hxStar hxArgmin hxInt hx
  have hf_withTop :
      ConvexOn ℝ (dom (fun z : V ↦ (f z : WithTop ℝ)))
        (withTopRealPart (fun z : V ↦ (f z : WithTop ℝ))) := by
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hzero :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (0 : V) = 0 := by
    -- The zero direction has zero directional derivative by uniqueness against the constant slice.
    have howner :
        HasDirectionalDerivAt (withTopToEReal ∘ fun z : V ↦ (f z : WithTop ℝ))
          xStar (0 : V)
          (convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (0 : V)) :=
      convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf_withTop hxInt 0
    have hconst :
        HasDirectionalDerivAt (withTopToEReal ∘ fun z : V ↦ (f z : WithTop ℝ))
          xStar (0 : V) 0 :=
      HasDirectionalDerivAt.zero
        (f := withTopToEReal ∘ fun z : V ↦ (f z : WithTop ℝ))
        (x := xStar)
        (mem_dom_withTopToEReal_comp_of_mem_dom (interior_subset hxInt))
    exact HasDirectionalDerivAt.unique howner hconst
  have hscale :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (r • (x - xStar)) =
        r * convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (x - xStar) := by
    -- Positive homogeneity transports the feasible-displacement estimate to the whole cone hull.
    by_cases hr0 : r = 0
    · subst hr0
      simp [hzero]
    · have hr_pos : 0 < r := lt_of_le_of_ne hr (by simpa [eq_comm] using hr0)
      rw [convexDirectionalDerivativeReal_apply, convexDirectionalDerivativeReal_apply]
      rw [convexDirectionalDerivative_smul
        (f := fun z : V ↦ (f z : WithTop ℝ))
        (hx := interior_subset hxInt) hr_pos (x - xStar)]
      simp [EReal.toReal_mul]
  rw [hscale]
  exact mul_nonneg hr hdisp

/-- Helper for Theorem 3.1.24: the convex directional derivative is nonnegative on the whole
tangent cone at a constrained minimizer. -/
lemma directionalDerivativeReal_nonneg_on_tangentCone_of_mem_argmin
    [FiniteDimensional ℝ V] [CompleteSpace V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) (hxArgmin : xStar ∈ argmin[Q] f)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))))
    {p : V} (hp : p ∈ 𝒯[Q] xStar) :
    0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt p := by
  let dderiv : V → ℝ :=
    convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt
  let C : Set V := {q : V | 0 ≤ dderiv q}
  have hf_withTop :
      ConvexOn ℝ (dom (fun z : V ↦ (f z : WithTop ℝ)))
        (withTopRealPart (fun z : V ↦ (f z : WithTop ℝ))) := by
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hcont : Continuous dderiv := by
    -- The whole-space convex directional derivative is continuous on all directions.
    rw [← continuousOn_univ]
    simpa [dderiv] using
      (convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior
        (f := fun z : V ↦ (f z : WithTop ℝ)) hf_withTop hxInt).continuousOn_interior
  have hclosed : IsClosed C := by
    simpa [C] using isClosed_Ici.preimage hcont
  have hsubset :
      (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V)) : Set V) ⊆ C := by
    -- The pointed-cone-hull lemma provides the dense generating cone of tangent directions.
    intro q hq
    exact directionalDerivativeReal_nonneg_on_pointedConeHull_of_mem_argmin
      hQ_convex hf_conv hxStar hxArgmin hxInt hq
  have hp' : p ∈ closure (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V)) : Set V) := by
    -- Lemma 3.1.18 identifies the tangent cone with the closure of the pointed feasible hull.
    rw [posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton Q hQ_convex xStar hxStar] at hp
    simpa using hp
  have hclosure :
      closure (PointedCone.hull ℝ (Q -ᵥ ({xStar} : Set V)) : Set V) ⊆ C := by
    exact hclosed.closure_subset_iff.2 hsubset
  exact hclosure hp'

/-- Helper for Theorem 3.1.24: the subgradient-side variational inequality forces the directional
derivative along the closest-pair gap to be strictly negative. -/
lemma closest_pair_directionalDerivative_lt_zero
    [FiniteDimensional ℝ V]
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar g1Star g2Star : V}
    (hdisj :
      Disjoint (∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)) ({g2Star} : Set V))
    (hg1Star : g1Star ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar))
    (hproj :
      ∀ g1 ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
        inner ℝ (g2Star - g1Star) (g1 - g1Star) ≤ 0)
    (hzeroPair : inner ℝ g2Star (g2Star - g1Star) = 0)
    (hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ)))) :
    convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt (g2Star - g1Star) < 0 := by
  let pStar : V := g2Star - g1Star
  have hf_withTop :
      ConvexOn ℝ (dom (fun z : V ↦ (f z : WithTop ℝ)))
        (withTopRealPart (fun z : V ↦ (f z : WithTop ℝ))) := by
    simpa [withTopEffectiveDomain, withTopRealPart] using hf_conv
  have hmax :=
    convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior
      (f := fun z : V ↦ (f z : WithTop ℝ)) hf_withTop hxInt pStar
  have hupper :
      ∀ g ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar),
        inner ℝ g pStar ≤ inner ℝ g1Star pStar := by
    intro g hg
    have hineq : inner ℝ g pStar - inner ℝ g1Star pStar ≤ 0 := by
      calc
        inner ℝ g pStar - inner ℝ g1Star pStar
            = inner ℝ pStar g - inner ℝ pStar g1Star := by
                rw [real_inner_comm g pStar, real_inner_comm g1Star pStar]
        _ = inner ℝ pStar (g - g1Star) := by
              rw [inner_sub_right]
        _ ≤ 0 := hproj g hg
    exact sub_nonpos.mp hineq
  have hmemImage :
      inner ℝ g1Star pStar ∈
        (fun g : V ↦ inner ℝ g pStar) '' ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) := by
    exact ⟨g1Star, hg1Star, rfl⟩
  have hle_max :
      inner ℝ g1Star pStar ≤
        convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt pStar :=
    hmax.2 hmemImage
  have hge_max :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt pStar ≤
        inner ℝ g1Star pStar := by
    rcases hmax.1 with ⟨g, hg, hgEq⟩
    rw [← hgEq]
    exact hupper g hg
  have hvalue :
      convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ)) hxInt pStar =
        inner ℝ g1Star pStar := by
    exact le_antisymm hge_max hle_max
  have hg2_not_mem :
      g2Star ∉ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) := by
    rw [Set.disjoint_singleton_right] at hdisj
    exact hdisj
  have hneq : g1Star ≠ g2Star := by
    intro hEq
    apply hg2_not_mem
    simpa [hEq] using hg1Star
  have hp_nonzero : pStar ≠ 0 := by
    exact sub_ne_zero.mpr hneq.symm
  have hp_norm_sq_pos : 0 < ‖pStar‖ ^ (2 : ℕ) := by
    positivity
  have hpair :
      inner ℝ g1Star pStar = -‖pStar‖ ^ (2 : ℕ) := by
    calc
      inner ℝ g1Star pStar = inner ℝ (g2Star - pStar) pStar := by
        simp [pStar, sub_eq_add_neg, add_left_comm]
      _ = inner ℝ g2Star pStar - inner ℝ pStar pStar := by
        rw [inner_sub_left]
      _ = -‖pStar‖ ^ (2 : ℕ) := by
        simp [pStar, hzeroPair]
  rw [hvalue, hpair]
  linarith

/-- Theorem 3.1.24, owner-level normal-cone form: a feasible point `xStar ∈ Q` belongs to the
optimal set `X* = argmin_{x ∈ Q} f(x)` if and only if some subgradient at `xStar` lies in the
normal cone of `Q` at `xStar`. -/
theorem mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          gStar ∈ N[Q] xStar := by
  constructor
  · intro hxArgmin
    by_contra hno
    let S : Set V := ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar)
    have hxInt : xStar ∈ interior (dom (fun z : V ↦ (f z : WithTop ℝ))) := by
      simp [withTopEffectiveDomain]
    have hnone :
        ∀ g : V, g ∈ S → g ∉ N[Q] xStar := by
      intro g hgS hgN
      exact hno ⟨g, hgS, hgN⟩
    rcases exists_closest_subgradient_normalCone_pair (V := V) (Q := Q) (f := f) (xStar := xStar)
        hf_conv with ⟨g1Star, hg1Star, g2Star, hg2Star, hprojS, hprojN⟩
    have hg2_not_mem : g2Star ∉ S := by
      intro hg2S
      exact hno ⟨g2Star, hg2S, hg2Star⟩
    have hdisj_singleton : Disjoint S ({g2Star} : Set V) := by
      rw [Set.disjoint_singleton_right]
      exact hg2_not_mem
    have htan : g2Star - g1Star ∈ 𝒯[Q] xStar :=
      closest_pair_direction_mem_tangentCone hQ_convex hxStar hg2Star hprojN
    have hnonneg :
        0 ≤ convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (g2Star - g1Star) :=
      directionalDerivativeReal_nonneg_on_tangentCone_of_mem_argmin
        hQ_convex hf_conv hxStar hxArgmin hxInt htan
    have hzeroPair :
        inner ℝ g2Star (g2Star - g1Star) = 0 :=
      normal_projection_gap_pairing_eq_zero hg2Star hprojN
    have hlt :
        convexDirectionalDerivativeReal (fun z : V ↦ (f z : WithTop ℝ))
          hxInt (g2Star - g1Star) < 0 :=
      closest_pair_directionalDerivative_lt_zero
        hf_conv hdisj_singleton hg1Star hprojS hzeroPair hxInt
    linarith
  · rintro ⟨gStar, hgStar_sub, hgStar_normal⟩
    rw [mem_constrainedArgmin_iff]
    refine ⟨hxStar, isMinOn_iff.mpr ?_⟩
    intro x hx
    have hsubgrad := mem_subdifferential_coe_real_iff.mp hgStar_sub x
    have hnormal := mem_normalCone_iff.mp hgStar_normal x hx
    linarith

end NormalConeOwner

section PairingBridge

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem 3.1.24: a feasible point `xStar ∈ Q` belongs to the optimal set
`X* = argmin_{x ∈ Q} f(x)` if and only if there exists a subgradient `gStar ∈ ∂f(xStar)` such
that `⟪gStar, x - xStar⟫ ≥ 0` for every `x ∈ Q`. -/
-- Proof sketch: rewrite the canonical normal-cone owner statement through
-- the normal-cone pairing condition.
theorem mem_constrainedArgmin_iff_exists_subgradient_nonneg_pairing
    [FiniteDimensional ℝ V]
    {Q : Set V} (hQ_convex : Convex ℝ Q)
    {f : V → ℝ} (hf_conv : ConvexOn ℝ Set.univ f)
    {xStar : V} (hxStar : xStar ∈ Q) :
    xStar ∈ argmin[Q] f ↔
      ∃ gStar : V,
        gStar ∈ ∂ (fun x : V ↦ (f x : WithTop ℝ))(xStar) ∧
          ∀ x ∈ Q, 0 ≤ inner ℝ gStar (x - xStar) := by
  -- Rewrite the canonical owner statement through the normal-cone membership criterion.
  rw [mem_constrainedArgmin_iff_exists_subgradient_mem_normalCone hQ_convex hf_conv hxStar]
  constructor
  · rintro ⟨gStar, hgStar, hgNormal⟩
    exact ⟨gStar, hgStar, mem_normalCone_iff.mp hgNormal⟩
  · rintro ⟨gStar, hgStar, hpair⟩
    exact ⟨gStar, hgStar, mem_normalCone_iff.mpr hpair⟩

end PairingBridge

end

/-! ### Theorem_3_1_25 (from Chap03) -/
noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis WithTopConvexAnalysis

universe u v

/- Theorem 3.1.25 lies in the chapter's partial-infimal-projection / subdifferential-transfer
domain.

Sampled owner-style declarations:
- `partialInfProjection` in `Theorem_3_1_2_3`, the canonical `EReal` owner for fiberwise infima;
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the canonical convexity
  theorem for `WithTop` objectives on that owner;
- `ClosedConvexOn.convexOn_withTopRealPart` in `Definition_3_1_1_5`, the chapter bridge from a
  closed-convex owner to the primitive convexity input `ConvexOn ℝ (dom φ) (withTopRealPart φ)`;
- `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for minimizer sets on a feasible set;
- `subdifferential` with notation `∂ f(x)` and `subdifferentialWithin` in `Definition_3_1_5` and
  `Theorem_3_44`, the chapter owners for ambient and relative subgradients.

Best owner abstraction:
- core/canonical: `partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)`, together with
  `ConvexOn ℝ (dom φ) (withTopRealPart φ)`, `argmin[Q₂] (fun y ↦ φ (x, y))`, the ambient
  subdifferential of the intrinsic `WithLp 2 (X × Y)` lift of `φ`, and `subdifferentialWithin`;
- bridge/view: the finite real part
  `extendedRealRealPart (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))`.

Primitive data:
- the fiber constraint `Q₂`;
- the product objective `φ : X × Y → WithTop ℝ`;
- a convex set `Q₁` on which the infimal projection is known to be finite.

Derived API:
- the convexity and subgradient-transfer theorems below for the finite real part of the canonical
  owner.

Source/core/bridge triage:
- source-facing: Theorem 3.1.25's real-valued partial value function and its subgradient
  consequence;
- core/canonical: `ConvexOn ℝ (dom φ) (withTopRealPart φ)`, `partialInfProjection`, `argmin`,
  `∂`, and `subdifferentialWithin`;
- bridge/view: `ClosedConvexOn.convexOn_withTopRealPart` and `extendedRealRealPart` applied to the
  owner `partialInfProjection`.

The previous file rebuilt local owners for the effective domain, closed convexity, fiberwise
argmin, ambient subdifferential, and relative subdifferential. Those notions are already owned
upstream, and the remaining one-off real-valued wrapper around `partialInfProjection` was also
redundant. This refinement deletes that wrapper and keeps the canonical owner expression directly
on the public theorem surface.
-/

section Convexity

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

variable {Q₁ : Set X} {Q₂ : Set Y} {φ : X × Y → WithTop ℝ}

/-- Theorem 3.1.25 (1): if `φ : X × Y → (-∞, +∞]` is convex on its effective domain and the
canonical infimal projection over `Q₂` is finite on `Q₁`, then its finite real part is convex on
`Q₁`. -/
-- Proof sketch: apply `partialInfProjection_convexOn_of_convexWithTop` to the convex feasible set
-- `Set.univ ×ˢ Q₂`, and then restrict the resulting owner `ConvexOn` statement from
-- `dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))` to the convex subset `Q₁`.
theorem partialInfProjection_realPart_convexOn_of_convexWithTop
    (hφ : ConvexOn ℝ (dom φ) (withTopRealPart φ))
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hfinite :
      Q₁ ⊆ dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) :
    ConvexOn ℝ Q₁
      (extendedRealRealPart (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) := by
  let ψ : X → EReal := partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)
  -- The owner convexity theorem already gives convexity on the finite-value domain of `ψ`.
  have hψ_convex : ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ) :=
    partialInfProjection_convexOn_of_convexWithTop
      (Q := Set.univ ×ˢ Q₂)
      (φ := φ)
      (convex_univ.prod hQ₂_convex) hφ
  -- Restrict the owner convexity statement from `dom ψ` to the prescribed finite subset `Q₁`.
  refine ⟨hQ₁_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  exact hψ_convex.2 (hfinite hx) (hfinite hy) ha hb hab

end Convexity

/-
Theorem 3.1.25 (2) is a direct subgradient-transfer statement. Its primitive data are the
finiteness of the projected value function on `Q₁`, the fiberwise argmin set, and the ambient
subgradient/variational-inequality hypotheses. The closed-convex and convex-set assumptions from
part (1) are derived proof context rather than part of this theorem's owner-level interface.
-/
section Subgradient

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

variable {Q₁ : Set X} {Q₂ : Set Y} {φ : X × Y → WithTop ℝ}

local notation "Z" => WithLp 2 (X × Y)
local notation "toZ" => WithLp.toLp 2

/-- Helper for Theorem 3.1.25: a fiber minimizer realizes the canonical partial-infimal-projection
value on that fiber. -/
lemma partialInfProjection_eq_value_of_mem_argmin
    {x : X} {yx : Y}
    (hyx : yx ∈ argmin[Q₂] (fun y ↦ φ (x, y))) :
    partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ) x =
      withTopToEReal (φ (x, yx)) := by
  let ψ : X → EReal := partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)
  let S : Set EReal :=
    (withTopToEReal ∘ φ) '' {z : X × Y | z ∈ Set.univ ×ˢ Q₂ ∧ z.1 = x}
  rcases mem_constrainedArgmin_iff.mp hyx with ⟨hyxQ, hyxMin⟩
  have hS_nonempty : S.Nonempty := by
    refine ⟨withTopToEReal (φ (x, yx)), ⟨(x, yx), ?_, rfl⟩⟩
    exact ⟨⟨by simp, hyxQ⟩, rfl⟩
  -- Every feasible fiber value lies above the value attained at the minimizing point `yx`.
  have hS_lower : ∀ b ∈ S, withTopToEReal (φ (x, yx)) ≤ b := by
    intro b hb
    rcases hb with ⟨⟨x', y'⟩, hz, rfl⟩
    rcases hz with ⟨hz, hx'⟩
    have hx'' : x' = x := by simpa using hx'
    subst x'
    have hy'Q : y' ∈ Q₂ := hz.2
    have hmin : φ (x, yx) ≤ φ (x, y') := hyxMin hy'Q
    exact
      (show Monotone (fun t : WithTop ℝ ↦ withTopToEReal t) from WithBot.coe_mono) hmin
  have hS_bddBelow : BddBelow S := ⟨withTopToEReal (φ (x, yx)), hS_lower⟩
  have hψ_upper : ψ x ≤ withTopToEReal (φ (x, yx)) := by
    have hmem : withTopToEReal (φ (x, yx)) ∈ S := by
      refine ⟨(x, yx), ?_, rfl⟩
      exact ⟨⟨by simp, hyxQ⟩, rfl⟩
    simpa [ψ, S, partialInfProjection_eq_sInf] using csInf_le hS_bddBelow hmem
  have hψ_lower : withTopToEReal (φ (x, yx)) ≤ ψ x := by
    simpa [ψ, S, partialInfProjection_eq_sInf] using le_csInf hS_nonempty hS_lower
  exact le_antisymm hψ_upper hψ_lower

/-- Helper for Theorem 3.1.25: the ambient product-space subgradient inequality together with the
variational inequality in the second variable yields the fiberwise lower bound used in the
projected subgradient proof. -/
lemma fiber_lower_bound_of_subgradient_and_variational_inequality
    {x x₁ : X} {yx y₁ : Y} {gx : X} {gy : Y}
    (hyx_dom : (x, yx) ∈ dom φ)
    (hy₁ : y₁ ∈ Q₂) (hy₁_dom : (x₁, y₁) ∈ dom φ)
    (hg :
      toZ (gx, gy) ∈
        ∂ (fun z : Z ↦ φ (z.fst, z.snd))((toZ (x, yx))))
    (hvar : ∀ ⦃y : Y⦄, y ∈ Q₂ → inner ℝ gy (y - yx) ≥ 0) :
    withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) ≤ withTopRealPart φ (x₁, y₁) := by
  have hyx_domZ : toZ (x, yx) ∈ dom (fun z : Z ↦ φ (z.fst, z.snd)) := by
    simpa using hyx_dom
  have hy₁_domZ : toZ (x₁, y₁) ∈ dom (fun z : Z ↦ φ (z.fst, z.snd)) := by
    simpa using hy₁_dom
  -- Rewrite the ambient subgradient inequality at the finite target point into ordinary real
  -- coordinates.
  have hsupport_withTop :=
    (mem_subdifferential_iff.mp hg).2 hy₁_domZ
  have hsupport :
      withTopRealPart φ (x₁, y₁) ≥
        withTopRealPart φ (x, yx) +
          inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) := by
    have hsupport_withTop' :
        φ (x₁, y₁) ≥
          φ (x, yx) +
            (inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : WithTop ℝ) := by
      simpa using hsupport_withTop
    have hyx_value :
        φ (x, yx) = ((withTopRealPart φ (x, yx) : ℝ) : WithTop ℝ) := by
      simpa using (coe_withTopRealPart (f := φ) hyx_dom).symm
    have hsupport_realTop :
        φ (x₁, y₁) ≥
          ((withTopRealPart φ (x, yx) +
              inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) := by
      calc
        φ (x₁, y₁) ≥
            φ (x, yx) +
              (inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : WithTop ℝ) :=
          hsupport_withTop'
        _ = (((withTopRealPart φ (x, yx) : ℝ) : WithTop ℝ) +
              (inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : WithTop ℝ)) := by
            rw [hyx_value]
        _ = ((withTopRealPart φ (x, yx) +
              inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) := by
            rw [WithTop.coe_add]
    have hy₁_value :
        φ (x₁, y₁) = ((withTopRealPart φ (x₁, y₁) : ℝ) : WithTop ℝ) := by
      simpa using (coe_withTopRealPart (f := φ) hy₁_dom).symm
    have hsupport_realTop' :
        ((withTopRealPart φ (x₁, y₁) : ℝ) : WithTop ℝ) ≥
          ((withTopRealPart φ (x, yx) +
              inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) := by
      calc
        ((withTopRealPart φ (x₁, y₁) : ℝ) : WithTop ℝ) = φ (x₁, y₁) := by
          rw [hy₁_value]
        _ ≥ ((withTopRealPart φ (x, yx) +
            inner ℝ (toZ (gx, gy)) (toZ (x₁, y₁) - toZ (x, yx)) : ℝ) : WithTop ℝ) :=
          hsupport_realTop
    exact_mod_cast hsupport_realTop'
  have hsupport' :
      withTopRealPart φ (x₁, y₁) ≥
        withTopRealPart φ (x, yx) +
          inner ℝ gx (x₁ - x) +
            inner ℝ gy (y₁ - yx) := by
    simpa [WithLp.prod_inner_apply, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
      hsupport
  -- The variational inequality says the second-coordinate contribution is nonnegative.
  have hgy_nonneg : 0 ≤ inner ℝ gy (y₁ - yx) := hvar hy₁
  linarith

/-- Theorem 3.1.25 (2): if `yₓ` minimizes the fiber objective `y ↦ φ (x, y)` on `Q₂`, and if an
ambient subgradient of the intrinsic product-space lift of `φ` at `(x, yₓ)` has components
`(gₓ, g_y)` and satisfies the variational inequality `⟪g_y, y - yₓ⟫ ≥ 0` on `Q₂`, then `gₓ`
belongs to the relative subdifferential of the finite real part of the canonical partial
infimal projection on `Q₁` at `x`. -/
-- Proof sketch: for `x₁ ∈ Q₁`, combine the subgradient inequality for
-- `WithLp.toLp 2 (gₓ, g_y) ∈
-- ∂ (fun z : Z ↦ φ (z.fst, z.snd))((WithLp.toLp 2 (x, yₓ)))` with an almost
-- minimizing fiber point over `x₁`; the
-- variational inequality for `g_y` removes the second-coordinate contribution, and the remaining
-- first-coordinate inequality is exactly the defining condition for
-- `∂[Q₁] (extendedRealRealPart
--   (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) (x)`.
theorem mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient
    (hfinite :
      Q₁ ⊆ dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)))
    {x : X} (hx : x ∈ Q₁)
    {yx : Y} (hyx : yx ∈ argmin[Q₂] (fun y ↦ φ (x, y)))
    {gx : X} {gy : Y}
    (hg :
      WithLp.toLp 2 (gx, gy) ∈
        ∂ (fun z : Z ↦ φ (z.fst, z.snd))((WithLp.toLp 2 (x, yx))))
    (hvar : ∀ ⦃y : Y⦄, y ∈ Q₂ → inner ℝ gy (y - yx) ≥ 0) :
    gx ∈ ∂[Q₁]
      (extendedRealRealPart (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) (x) :=
      by
  let ψ : X → EReal := partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)
  change gx ∈ ∂[Q₁] (extendedRealRealPart ψ) (x)
  have hxψ : x ∈ dom ψ := hfinite hx
  rcases mem_constrainedArgmin_iff.mp hyx with ⟨hyxQ, _⟩
  -- The minimizing fiber point `yx` realizes the projected value at `x`.
  have hψx : ψ x = withTopToEReal (φ (x, yx)) :=
    partialInfProjection_eq_value_of_mem_argmin (Q₂ := Q₂) (φ := φ) hyx
  have hyx_dom : (x, yx) ∈ dom φ := by
    by_contra hyx_dom
    rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hyx_dom
    have htop : φ (x, yx) = ⊤ := by
      simpa using hyx_dom
    have hψ_top : ψ x = ⊤ := by
      rw [hψx, htop, withTopToEReal]
      rfl
    exact (mem_extendedRealEffectiveDomain_iff.mp hxψ).1 hψ_top
  have hψx_real : extendedRealRealPart ψ x = withTopRealPart φ (x, yx) := by
    apply EReal.coe_injective
    rw [coe_extendedRealRealPart hxψ, hψx]
    simpa [withTopToEReal] using
      (congrArg withTopToEReal (coe_withTopRealPart (f := φ) hyx_dom)).symm
  rw [mem_subdifferentialWithin_iff]
  refine ⟨hx, ?_⟩
  intro x₁ hx₁
  have hx₁ψ : x₁ ∈ dom ψ := hfinite hx₁
  let S : Set EReal :=
    (withTopToEReal ∘ φ) '' {z : X × Y | z ∈ Set.univ ×ˢ Q₂ ∧ z.1 = x₁}
  -- The same feasible minimizer witness `yx ∈ Q₂` makes every fiber set nonempty.
  have hS_nonempty : S.Nonempty := by
    refine ⟨withTopToEReal (φ (x₁, yx)), ⟨(x₁, yx), ?_, rfl⟩⟩
    exact ⟨⟨by simp, hyxQ⟩, rfl⟩
  -- Every fiber value lies above the affine lower support term determined by `gx`.
  have hS_lower :
      ∀ b ∈ S,
        (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤ b := by
    intro b hb
    rcases hb with ⟨⟨x', y'⟩, hz, rfl⟩
    rcases hz with ⟨hz, hx'⟩
    have hx'' : x' = x₁ := by simpa using hx'
    subst x'
    by_cases hy'_dom : (x₁, y') ∈ dom φ
    · have hzQ : y' ∈ Q₂ := hz.2
      have hreal :
          withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) ≤ withTopRealPart φ (x₁, y') := by
        simpa using
          fiber_lower_bound_of_subgradient_and_variational_inequality
            (Q₂ := Q₂) (φ := φ)
            (hyx_dom := hyx_dom) (hy₁ := hzQ) (hy₁_dom := hy'_dom)
            (hg := hg) (hvar := hvar)
      have hzValue :
          ((withTopRealPart φ (x₁, y') : ℝ) : EReal) = withTopToEReal (φ (x₁, y')) := by
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart (f := φ) hy'_dom)
      change (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤
        withTopToEReal (φ (x₁, y'))
      rw [← hzValue]
      exact_mod_cast hreal
    · rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hy'_dom
      have htop : φ (x₁, y') = ⊤ := by
        simpa using hy'_dom
      change (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤
        withTopToEReal (φ (x₁, y'))
      rw [htop, withTopToEReal]
      exact le_top
  have hψx₁_lower :
      (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤ ψ x₁ := by
    simpa [ψ, S, partialInfProjection_eq_sInf] using le_csInf hS_nonempty hS_lower
  -- Convert the `EReal` lower bound back to the real-valued owner surface at the finite point `x₁`.
  have hsupport :
      withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) ≤ extendedRealRealPart ψ x₁ := by
    have hE :
        (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤
          ((extendedRealRealPart ψ x₁ : ℝ) : EReal) := by
      calc
        (((withTopRealPart φ (x, yx) + inner ℝ gx (x₁ - x) : ℝ) : EReal)) ≤ ψ x₁ := hψx₁_lower
        _ = ((extendedRealRealPart ψ x₁ : ℝ) : EReal) := by
            symm
            exact coe_extendedRealRealPart hx₁ψ
    exact_mod_cast hE
  rw [hψx_real]
  simpa [add_comm, add_left_comm, add_assoc] using hsupport

/-- A candidate-set repackaging of Theorem 3.1.25 (2): every first-coordinate component arising
from a minimizing fiber point, an ambient subgradient there, and the corresponding variational
inequality on `Q₂` lies in the relative subdifferential of the finite real part of the canonical
partial infimal projection on `Q₁` at `x`. This is a derived bridge, not the main source-facing
theorem. -/
theorem partialInfProjectionSubgradientCandidates_subset_subdifferentialWithin
    (hfinite :
      Q₁ ⊆ dom (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ)))
    {x : X} (hx : x ∈ Q₁) :
    {gx : X | ∃ yx : Y, yx ∈ argmin[Q₂] (fun y ↦ φ (x, y)) ∧
        ∃ gy : Y, WithLp.toLp 2 (gx, gy) ∈
            ∂ (fun z : Z ↦ φ (z.fst, z.snd))((WithLp.toLp 2 (x, yx))) ∧
          ∀ ⦃y : Y⦄, y ∈ Q₂ → inner ℝ gy (y - yx) ≥ 0} ⊆
      ∂[Q₁]
        (extendedRealRealPart
          (partialInfProjection (Set.univ ×ˢ Q₂) (withTopToEReal ∘ φ))) (x) := by
  intro gx hgx
  rcases hgx with ⟨yx, hyx, gy, hgy, hvar⟩
  exact mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient
    hfinite hx hyx hgy hvar

end Subgradient

end

/-! ### Theorem_3_1_26 (from Chap03) -/
noncomputable section

open scoped Gradient EuclideanOrthant

universe u

variable {E : Type u}
variable {m : ℕ}

/- Theorem 3.1.26 lies in the convex inequality-constrained first-order optimality domain.

Sampled owner-style declarations:
- `LagrangianProblem.feasibleSet` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, the project owner for finite families of `≤ 0` constraints on a
  feasible subtype;
- `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible` and
  `LagrangianProblem.slaterCondition_iff` in `Chap01/Definition_1_10_9`, the canonical owner and
  bridge for strict feasibility;
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the owner for nonnegative
  multiplier vectors in `ℝ^m`;
- `gradient` / `∇` and `DifferentiableAt.hasGradientAt` in `Chap01/Definition_1_4_7`, the
  canonical owner and bridge for gradients of differentiable real-valued functions on a real
  inner-product space;
- `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Chap02/Theorem_2_29`, the
  chapter owner for constrained first-order optimality from explicit `HasGradientAt` data on a
  convex set.

Best owner abstraction:
- source-facing: the KKT optimality theorem below, because the textbook item is stated on an
  ambient set `Q ⊆ E` rather than on a pre-packaged problem structure;
- core/canonical: `LagrangianProblem`,
  `problem.toFunctionalConstraintsMinimizationProblem.StrictlyFeasible`,
  `nonnegativeOrthant m`, `gradient`, `DifferentiableAt`, `HasGradientAt`, and
  `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt`;
- bridge/view: the ambient feasible-set predicate `inequalityConstrainedFeasibleSet`.

Primitive data:
- the ambient feasible set `Q`;
- the objective `f0`;
- the finite inequality family `fi`;
- the candidate point `xStar`;
- the multiplier vector `lam : Λ`;
- the strict-feasibility certificate `∃ x ∈ Q, ∀ i : Fin m, fi i x < 0`;
- differentiability of `f0` and the constraint family `fi` at `xStar`.

Derived API:
- `inequalityConstrainedFeasibleSet`;
- `mem_inequalityConstrainedFeasibleSet_iff`;
- the KKT optimality equivalence.

The earlier version fixed the ambient space to `EuclideanSpace ℝ (Fin n)` even though the public
surface only uses real inner-product-space structure. The refined file keeps the source-facing KKT
surface, reuses the Chapter 1 orthant owner for multiplier nonnegativity, and lowers the ambient
space to the weakest canonical layer used by the statements. The theorem now takes the
source-faithful strict-feasibility hypothesis directly instead of exporting a parallel set-based
Slater wrapper, and the main theorem exposes the KKT certificate directly through the canonical
gradients `∇ f0 xStar` and `∇ (fi i) xStar` instead of a one-off certificate wrapper. -/

/-- The feasible set of the inequality-constrained problem on the ambient set `Q` consists of the
points of `Q` satisfying every scalar constraint `fᵢ(x) ≤ 0`. -/
def inequalityConstrainedFeasibleSet
    (Q : Set E) (fi : Fin m → E → ℝ) : Set E :=
  {x | x ∈ Q ∧ ∀ i : Fin m, fi i x ≤ 0}

/-- Membership in `inequalityConstrainedFeasibleSet Q fi` means belonging to `Q` and satisfying
all scalar inequality constraints. -/
-- Proof sketch: unfold `inequalityConstrainedFeasibleSet`; membership in the set-builder is
-- definitionally the conjunction of `x ∈ Q` and `fi i x ≤ 0` for every constraint index `i`.
theorem mem_inequalityConstrainedFeasibleSet_iff
    {Q : Set E} {fi : Fin m → E → ℝ} {x : E} :
    x ∈ inequalityConstrainedFeasibleSet Q fi ↔
      x ∈ Q ∧ ∀ i : Fin m, fi i x ≤ 0 :=
  Iff.rfl

section

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-- Theorem 3.1.26: (Karush--Kuhn--Tucker) under convexity, pointwise differentiability at
`xStar`, and a strict-feasibility point for the constraints, a point `xStar` is an optimal
solution of the
inequality-constrained problem `min {f₀(x) | x ∈ Q, fᵢ(x) ≤ 0 for all i}` if and only if there is
a nonnegative multiplier vector such that `xStar` is primal feasible, the canonical gradients
`∇ f0 xStar` and `∇ (fi i) xStar` yield the Lagrangian variational inequality on `Q`, and the
coordinates obey complementary slackness at `xStar`. -/
-- Proof sketch: rewrite the problem as minimizing `f₀` on
-- `inequalityConstrainedFeasibleSet Q fi`. The forward direction comes from the convex
-- first-order optimality condition together with the max/subdifferential description of the active
-- inequality constraints under the Chapter 1 Slater condition for the restricted subtype problem,
-- which yields a multiplier vector. For the reverse direction, use the `ConvexOn` hypotheses on
-- `f₀` and `fᵢ`, the variational inequality, and
-- complementary slackness to recover the optimality inequality against every feasible point.
theorem isMinOn_iff_exists_karush_kuhn_tucker_multiplier
    {Q : Set E} {f0 : E → ℝ} {fi : Fin m → E → ℝ}
    (hf0_conv : ConvexOn ℝ Q f0)
    (hfi_conv : ∀ i : Fin m, ConvexOn ℝ Q (fi i))
    {xStar : E}
    (hf0_diff : DifferentiableAt ℝ f0 xStar)
    (hfi_diff : ∀ i : Fin m, DifferentiableAt ℝ (fi i) xStar)
    (hSlater : ∃ x ∈ Q, ∀ i : Fin m, fi i x < 0) :
    IsMinOn f0 (inequalityConstrainedFeasibleSet Q fi) xStar ↔
      ∃ lam : Λ,
        xStar ∈ inequalityConstrainedFeasibleSet Q fi ∧
          lam ∈ ℝ₊^m ∧
            (∀ x : E, x ∈ Q →
              0 ≤
                inner ℝ
                  (∇ f0 xStar + ∑ i : Fin m, (lam i) • ∇ (fi i) xStar)
                  (x - xStar)) ∧
              ∀ i : Fin m, lam i * fi i xStar = 0 := sorry

end

end

/-! ### Theorem_3_1_27 (from Chap03) -/
noncomputable section

open scoped Topology
open scoped NormalCone
open scoped WithTopConvexAnalysis

universe u v

variable {E : Type u} {Λ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ] [FiniteDimensional ℝ Λ]

/- Theorem 3.1.27 lies in the chapter's equality-constrained extended-valued convex-optimality
domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on finite-dimensional real inner-product spaces
  with linear equality constraints.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owners for
  extended-valued subgradients;
- `normalCone`, the notation `N[Q] x`, and `mem_normalCone_iff` in `Definition_3_22`, the chapter
  owner API for textbook normal cones;
- `constrainedSublevelSet` in `Definition_3_3`, the chapter owner for constrained sublevel sets;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the chapter owner for the feasible
  set cut out by `x ∈ Q` and `A x = b`.

Best owner abstraction:
- the source-facing theorem stated directly on the chapter owners
  `ConvexOn ℝ (dom f) (withTopRealPart f)`, `∂ f(xStar)`, `N[Q] xStar`,
  `constrainedSublevelSet`, and `linearEqualityFeasibleSet`.

Primitive data:
- a closed convex feasible set `Q`;
- an extended-real-valued objective `f`;
- a linear map `A` and right-hand side `b`;
- a Slater point `xBar` with a feasible ball `Metric.ball xBar ε ⊆ Q`.

Derived API:
- the feasibility conclusion `A xStar = b`;
- an owner-level subgradient witness `gStar ∈ ∂ f(xStar)`;
- the owner-level normal-cone condition `gStar - A.adjoint yStar ∈ N[Q] xStar`;
- the quantitative Slater-radius bound on `‖A.adjoint yStar‖`.

Source/core/bridge triage:
- source-facing: the quantitative equality-constrained optimality theorem;
- core/canonical: `dom`, `withTopRealPart`, `∂`, `N[Q] xStar`,
  `constrainedSublevelSet`, and `linearEqualityFeasibleSet`;
- bridge/view: matrix / transpose and relative-subgradient reformulations in downstream files.

The previous version rebuilt local copies of the effective domain, finite real part, convexity
predicate, subgradient predicate, subdifferential, and constrained sublevel set, then repackaged
the resulting theorem witnesses in a one-off certificate structure. Those notions are already
owned earlier in the chapter, so this refinement deletes the duplicate wheel layer and the local
wrapper, and states the theorem directly on the canonical chapter surface. The normal-cone
component is kept on the owner abstraction `N[Q] xStar`, with the raw pairing inequality treated
as the companion view supplied by `mem_normalCone_iff` rather than as the main public statement.
-/

/-- Theorem 3.1.27: for a convex function on a closed convex set
`Q ⊆ interior (dom f)` with bounded constrained sublevel sets, under the equality Slater
condition `A xBar = b` and `Metric.ball xBar ε ⊆ Q`, a point `xStar` minimizes
`withTopRealPart f` over `{x ∈ Q | A x = b}` if and only if
`xStar ∈ linearEqualityFeasibleSet Q A b` and there exist a multiplier `yStar` and a subgradient
`gStar ∈ ∂ f(xStar)` such that `gStar - A.adjoint yStar ∈ N[Q] xStar`; moreover the certificate
can be chosen so that `‖A.adjoint yStar‖ ≤
(sSup (withTopRealPart f '' Metric.ball xBar ε) - sInf (withTopRealPart f '' Q)) / ε`.
-/
-- Proof sketch: for the reverse implication, combine the subgradient inequality for
-- `gStar ∈ ∂ f(xStar)` with the normal-cone inequality supplied by `mem_normalCone_iff`, and use
-- `A x = A xStar = b` on feasible points to cancel the multiplier term. For the forward
-- implication, minimize the penalized function `x ↦ f x + K ‖b - A x‖` on `Q`, apply first-order
-- optimality on `Q`, decompose a subgradient of the penalty through the adjoint `A.adjoint`, and
-- use the Slater ball of radius `ε` to derive the bound on `‖A.adjoint yStar‖` after dividing
-- the value gap by `ε`.
theorem isMinOn_linearEqualityFeasibleSet_iff_exists_subgradient_multiplier_with_bound
    {Q : Set E} {f : E → WithTop ℝ}
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hQ_subset_interior : Q ⊆ interior (dom f))
    (hlevel_bounded : ∀ α : ℝ, Bornology.IsBounded (constrainedSublevelSet Q f α))
    {A : E →ₗ[ℝ] Λ} {b : Λ} {xBar : E} {ε : ℝ}
    (hbar : A xBar = b) (hε : 0 < ε) (hball : Metric.ball xBar ε ⊆ Q) {xStar : E} :
    IsMinOn (withTopRealPart f) (linearEqualityFeasibleSet Q A b) xStar ↔
      xStar ∈ linearEqualityFeasibleSet Q A b ∧
        ∃ yStar : Λ, ∃ gStar ∈ ∂ f(xStar),
          gStar - A.adjoint yStar ∈ N[Q] xStar ∧
            ‖A.adjoint yStar‖ ≤
              (sSup (withTopRealPart f '' Metric.ball xBar ε) -
                  sInf (withTopRealPart f '' Q)) / ε := sorry

end

/-! ### Theorem_3_1_28 (from Chap03) -/
/- Theorem 3.1.28 is recall-only in the chapter's affine-fiber value-function /
multiplier-subgradient domain.

Mandatory domain-style sampling before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for effective domains and
  finite real parts of `WithTop ℝ`-valued objectives;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  ambient extended-valued subgradients;
- `linearEqualityFeasibleSet` in `LinearEqualityFeasibleSet`, the primitive affine-fiber owner;
- `affinePartialInfProjection_realPart_convexOn` and
  `mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality` in
  `Theorem_3_35`, the canonical owner-level affine-fiber convexity and multiplier-subgradient
  declarations.

Best owner abstraction:
- core/canonical: the two owner declarations in `Theorem_3_35`, stated directly on the chapter's
  affine-fiber `partialInfProjection` surface;
- bridge/view: this numbered recall surface.

Primitive data:
- none in this file; the affine-fiber owner data already live upstream.

Derived API:
- this numbered recall surface.

Source/core/bridge triage:
- source-facing: Theorem 3.1.28's convexity and multiplier-subgradient clauses for a linearly
  constrained value function;
- core/canonical: the owner declarations in `Theorem_3_35`;
- bridge/view: this recall surface.

The previous file kept a second public `WithTop ℝ` value-function owner together with parallel
theorem wrappers around the affine-fiber owner already developed in `Theorem_3_35`. That local
surface was not the chapter owner abstraction: the canonical construction already lives on
`partialInfProjection`, with `linearEqualityFeasibleSet` as the primitive affine-fiber data and
the per-multiplier relative-subdifferential theorem already stated upstream. This file therefore
reuses those owner declarations directly instead of maintaining a second value-function API. -/

/- Theorem 3.1.28 (1): the affine-fiber projected value function is convex on its finite-value
domain under the standard convexity hypotheses on `f` and `Q`. -/
recall affinePartialInfProjection_realPart_convexOn

/- Theorem 3.1.28 (2): a feasible primal point together with a primal subgradient satisfying the
affine variational inequality yields a relative subgradient of the canonical affine-fiber
projected value function. -/
recall mem_subdifferentialWithin_affinePartialInfProjection_of_variational_inequality

/-! ### Theorem_3_1_29 (from Chap03) -/
noncomputable section

universe u v

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommMonoid U] [Module ℝ U]

/- This item lies in the chapter's parametric minimax / saddle-value domain.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/PointwiseSupremumOn`, the chapter owner for faithful upper
  envelopes of a kernel;
- `ClosedConvexOn` in `Chap03/Definition_3_1_1_5`, the chapter owner for primal slice geometry;
- `IsSaddlePointOn` in `Mathlib/Order/SaddlePoint`, the canonical owner for saddle inequalities;
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer` in
  `Chap03/Lemma_3_22`, the nearby minimax owner theorem behind the present unique-minimizer
  consequence.

Best owner abstraction:
- source-facing: the minimax equality between the attained primal minimum and attained dual
  maximum;
- core/canonical: `IsSaddlePointOn`, `pointwiseSupremumOn`, `IsMinOn`, `IsMaxOn`, and `IsLeast`;
- bridge/view: the chosen minimizer family `x`, which realizes the diagonal values.

Primitive data:
- the feasible sets `P` and `S`;
- the kernel `Ψ`;
- the real-valued upper objective `f`, bridged to `pointwiseSupremumOn` on `P`;
- the closed-convexity of the primal slices and the concavity of the dual slices;
- the chosen slice minimizers `x u` on `P` and their uniqueness;
- an attained maximizer `uStar ∈ S` of the lower-value function
  `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`.

Derived API:
- the actual minimax equality for the primal and dual value sets;
- the canonical saddle predicate at `(x uStar, uStar)`;
- the primal-minimizer and value companions derived from that saddle relation.
-/

section

variable {P : Set X} {S : Set U} {Ψ : X → U → ℝ} {f : X → ℝ}
variable (x : U → X)
variable {uStar : U}

/-- Theorem 3.1.29: if every primal slice `x ↦ Ψ x u` with `u ∈ S` attains the unique minimizer
`x u` on `P`, and if the lower-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` attains its
maximum on `S`, then the primal minimum of `f` on `P` equals the dual maximum of that lower-value
function on `S`. -/
-- Proof sketch: first use the unique-minimizer hypothesis together with Theorem 3.1.4 and
-- Lemma 3.1.22 to show that `(x uStar, uStar)` is a saddle point of `Ψ` on `P × S`. The saddle
-- inequalities imply that `x uStar` minimizes `f` on `P` and that
-- `f (x uStar) = sInf ((fun x ↦ Ψ x uStar) '' P)`. Finally combine that identity with the
-- maximizing property `huStar_max` to identify the primal infimum `sInf (f '' P)` with the dual
-- supremum `sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S)`.
theorem minimax_eq_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    sInf (f '' P) = sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := sorry

/-- The distinguished pair `(x uStar, uStar)` is a saddle point of `Ψ` on `P × S` under the
unique-slice-minimizer and dual-maximizer hypotheses. -/
-- Proof sketch: apply Theorem 3.1.4 to each closed-convex slice `x ↦ Ψ x u` to recover bounded
-- sublevel sets from uniqueness of `x u`. Then Lemma 3.1.22 applied at `uStar` forces the two
-- inequalities `Ψ (x uStar) u ≤ Ψ (x uStar) uStar ≤ Ψ x uStar` for all `u ∈ S` and `x ∈ P`,
-- which is exactly the saddle relation.
theorem isSaddlePointOn_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsSaddlePointOn P S Ψ (x uStar) uStar := sorry

/-- Companion consequence of Theorem 3.1.29: the distinguished primal point `x uStar` minimizes
the real-valued upper objective `f` on `P`. -/
-- Proof sketch: combine the saddle inequalities at `(x uStar, uStar)` with the bridge
-- `hf_eq` identifying `f` on `P` with the faithful upper envelope `pointwiseSupremumOn S Ψ`.
-- This gives `f (x uStar) ≤ f x` for every feasible `x`.
theorem isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsMinOn f P (x uStar) := sorry

/-- Companion value identity from Theorem 3.1.29. -/
-- Proof sketch: once `x uStar` is known to minimize `f` on `P`, the right-hand saddle inequality
-- identifies its objective value with the slice minimum
-- `sInf ((fun x ↦ Ψ x uStar) '' P)`.
theorem objective_eq_valueFunction_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    f (x uStar) = sInf ((fun x ↦ Ψ x uStar) '' P) := sorry

/-- Order-theoretic companion of Theorem 3.1.29: the upper-envelope value attained at `x uStar`
is the least element of the feasible value image. -/
-- Proof sketch: reformulate `isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max`
-- as the statement that `f (x uStar)` is a lower bound on `f '' P`, and use `hx_mem huStar` to
-- record that the bound is itself attained in the image.
theorem primal_min_isLeast_of_unique_slice_argmin_and_attained_dual_max
    (hΨ_closedConvex :
      ∀ ⦃u : U⦄, u ∈ S → ClosedConvexOn P (fun x ↦ (Ψ x u : WithTop ℝ)))
    (hΨ_concave : ∀ ⦃x : X⦄, x ∈ P → ConcaveOn ℝ S (fun v ↦ Ψ x v))
    (hf_eq :
      ∀ ⦃x : X⦄, x ∈ P →
        (f x : WithTop ℝ) = pointwiseSupremumOn S (fun x' u ↦ (Ψ x' u : WithTop ℝ)) x)
    (hx_mem : ∀ ⦃u : U⦄, u ∈ S → x u ∈ P)
    (hx_min : ∀ ⦃u : U⦄, u ∈ S → IsMinOn (fun p ↦ Ψ p u) P (x u))
    (hx_unique : ∀ ⦃u : U⦄, u ∈ S → ∀ p : X, IsMinOn (fun q ↦ Ψ q u) P p → p = x u)
    (huStar : uStar ∈ S)
    (huStar_max : IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar) :
    IsLeast (f '' P) (f (x uStar)) := by
  refine ⟨⟨x uStar, hx_mem huStar, rfl⟩, ?_⟩
  rintro _ ⟨p, hpP, rfl⟩
  have hmin : IsMinOn f P (x uStar) :=
    isMinOn_objective_of_unique_slice_argmin_and_attained_dual_max
      x hΨ_closedConvex hΨ_concave hf_eq hx_mem hx_min hx_unique huStar huStar_max
  exact hmin hpP

end

end
