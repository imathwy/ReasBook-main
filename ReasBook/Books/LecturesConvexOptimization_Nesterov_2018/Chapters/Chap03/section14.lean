import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_14 (from Chap03) -/
/- Definition 3.14 is a recall-only specialization in the chapter's positive-part domain.

Primary domain:
- positive-part operations in ordered additive algebra.

Relevant owner-style declarations sampled before refinement:
- `posPart`
- `posPart_def`
- `posPart_eq_ite`

Best owner abstraction:
- the canonical owner `posPart`, specialized to `ℝ`

Primitive data:
- none beyond the real input variable; the owner map already exists upstream

Derived API:
- the specialization `ℝ → ℝ`
- the pointwise bridge `x⁺ = max x 0`

Source/core/bridge triage:
- source-facing: the textbook real function `x ↦ (x)_+`
- core/canonical: `posPart`
- bridge/view: `posPart_def` specialized to `ℝ`

`Definition_3_1_5_2` already recalls the positive-part owner together with its canonical formulas.
This file therefore deletes the duplicate wrapper `realPosPart` and its parallel bridge theorem,
and keeps Definition 3.14 as the direct real specialization of the existing owner. -/

/- Definition 3.14: the textbook real positive-part function `x ↦ (x)_+` is the real
specialization of the canonical owner `posPart`. -/
#check ((·⁺) : ℝ → ℝ)

/- Pointwise, the real specialization is `x ↦ max x 0`. -/
#check (posPart_def : ∀ x : ℝ, x⁺ = max x 0)

/-! ### Lemma_3_14 (from Chap03) -/
noncomputable section

open Set
open scoped WithTopConvexAnalysis

universe u v

variable {ι : Type u} {X : Type v}

/- Lemma 3.14 [Chapter3_2.json:8] lies in the chapter's subset-indexed pointwise-supremum and
constrained-subdifferential calculus for `WithTop ℝ`-valued functions on real vector spaces.

Sampled owner declarations:
- `pointwiseSupremumOn`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn.pointwise_sSup`
- `constrainedSubdifferential`

Best owner abstraction:
- core/canonical: the upper-envelope owner `pointwiseSupremumOn`, its effective-domain view
  `pointwiseSupremumOnEffectiveDomain`, the closed-convex owner theorem
  `ClosedConvexOn.pointwise_sSup`, and the constrained-subdifferential owner `∂[Q] f(x)`;
- source-facing: the active-index surface `activePointwiseSupremumOnIndices`;
- bridge/view: the active-index membership theorem
  `mem_activePointwiseSupremumOnIndices_iff`.

The textbook lemma splits canonically into two independent clauses: closed-convex stability of the
pointwise supremum, and the active-slice convex-hull inclusion for constrained subdifferentials.
This file keeps that source-faithful split. It recalls the closed-convex clause from the owner
theorem and proves the active-slice inclusion locally, so the numbered item no longer depends on
the upstream source-facing placeholder theorem from `Lemma_3_1_14`. -/

/-- Helper for Lemma 3.14 [Chapter3_2.json:8]: the active parameter set `I(x)` for the
subset-indexed pointwise supremum over `Δ`. -/
def activePointwiseSupremumOnIndices
    (Δ : Set ι) (φ : X → ι → WithTop ℝ) (x : X) : Set ι :=
  {y | y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x}

/-- Helper for Lemma 3.14 [Chapter3_2.json:8]: membership in the active-index set means that the
chosen parameter belongs to `Δ` and attains the pointwise supremum at `x`. -/
@[simp]
theorem mem_activePointwiseSupremumOnIndices_iff
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι} :
    y ∈ activePointwiseSupremumOnIndices Δ φ x ↔
      y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x :=
  Iff.rfl

/-- Helper for Lemma 3.14 [Chapter3_2.json:8]: every admissible slice value lies below the
pointwise supremum. -/
lemma slice_le_pointwiseSupremumOn
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι}
    (hy : y ∈ Δ) :
    φ x y ≤ pointwiseSupremumOn Δ φ x := by
  -- The chosen slice contributes one element to the supremum-defining image set.
  rw [pointwiseSupremumOn_apply]
  refine le_csSup ?_ ?_
  · exact ⟨⊤, fun _ _ ↦ le_top⟩
  · exact ⟨y, hy, rfl⟩

/- Lemma 3.14 [Chapter3_2.json:8] (1): if `Δ` is nonempty and every slice `x ↦ φ(x, y)` with
`y ∈ Δ` is closed and convex on `Q`, then the pointwise supremum is closed and convex on its
effective domain `pointwiseSupremumOnEffectiveDomain Q Δ φ`. -/
recall ClosedConvexOn.pointwise_sSup
    [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ}
    (hΔ : Δ.Nonempty)
    (hφ : ∀ y ∈ Δ, ClosedConvexOn Q (fun x ↦ φ x y)) :
    ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q Δ φ) (pointwiseSupremumOn Δ φ)

variable {E : Type v} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 3.14 [Chapter3_2.json:8]: an active slice subgradient is a constrained
subgradient of the pointwise supremum on the effective domain. -/
lemma mem_constrainedSubdifferential_pointwiseSupremumOn_of_mem_active
    {Q : Set E} {Δ : Set ι} {φ : E → ι → WithTop ℝ} {x : E} {y : ι} {g : E}
    (hx : x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ)
    (hy : y ∈ activePointwiseSupremumOnIndices Δ φ x)
    (hg : g ∈ ∂[Q] (fun z ↦ φ z y) (x)) :
    g ∈ ∂[pointwiseSupremumOnEffectiveDomain Q Δ φ] (pointwiseSupremumOn Δ φ) (x) := by
  -- Route correction: instead of recalling the upstream source-facing theorem, prove the active
  -- slice transfer directly from the defining support inequalities.
  rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hx) with ⟨hxQ, hxdom⟩
  rcases (mem_activePointwiseSupremumOnIndices_iff.mp hy) with ⟨hyΔ, hyactive⟩
  rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨_, _, hsubgrad⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hx, hxdom, ?_⟩
  intro z hz
  rcases (mem_pointwiseSupremumOnEffectiveDomain_iff.mp hz) with ⟨hzQ, _⟩
  -- Compare the active slice with the whole supremum, then rewrite the base-point value by
  -- activity of `y`.
  calc
    pointwiseSupremumOn Δ φ z ≥ φ z y := slice_le_pointwiseSupremumOn hyΔ
    _ ≥ φ x y + ↑(inner ℝ g (z - x)) := hsubgrad hzQ
    _ = pointwiseSupremumOn Δ φ x + ↑(inner ℝ g (z - x)) := by rw [hyactive]

/-- Helper for Lemma 3.14 [Chapter3_2.json:8]: every constrained subdifferential is convex in the
subgradient variable. -/
lemma convex_constrainedSubdifferential
    {Q : Set E} {f : E → WithTop ℝ} {x : E} :
    Convex ℝ (∂[Q] f(x)) := by
  rw [convex_iff_add_mem]
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  rcases (mem_constrainedSubdifferential_iff.mp hg₁) with ⟨hxQ, hxdom, hg₁'⟩
  rcases (mem_constrainedSubdifferential_iff.mp hg₂) with ⟨_, _, hg₂'⟩
  rw [mem_constrainedSubdifferential_iff]
  refine ⟨hxQ, hxdom, ?_⟩
  intro y hyQ
  by_cases hyf : y ∈ dom f
  · -- On the effective domain both endpoint inequalities are real, so a convex combination of
    -- the slopes still satisfies the same support bound.
    have hg₁_withTop :
        (((withTopRealPart f x + inner ℝ g₁ (y - x) : ℝ) : WithTop ℝ) ≤ f y) := by
      rw [WithTop.coe_add, coe_withTopRealPart hxdom]
      exact hg₁' hyQ
    have hg₂_withTop :
        (((withTopRealPart f x + inner ℝ g₂ (y - x) : ℝ) : WithTop ℝ) ≤ f y) := by
      rw [WithTop.coe_add, coe_withTopRealPart hxdom]
      exact hg₂' hyQ
    have hg₁_real :
        withTopRealPart f x + inner ℝ g₁ (y - x) ≤ withTopRealPart f y :=
      (le_withTopRealPart_iff hyf).mpr hg₁_withTop
    have hg₂_real :
        withTopRealPart f x + inner ℝ g₂ (y - x) ≤ withTopRealPart f y :=
      (le_withTopRealPart_iff hyf).mpr hg₂_withTop
    have hslope₁ :
        inner ℝ g₁ (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
      linarith
    have hslope₂ :
        inner ℝ g₂ (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
      linarith
    have hcombo_real :
        withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) ≤ withTopRealPart f y := by
      rw [inner_add_left]
      have hsmul₁ :
          inner ℝ (a • g₁) (y - x) = a * inner ℝ g₁ (y - x) := by
        simpa using (inner_smul_left g₁ (y - x) a)
      have hsmul₂ :
          inner ℝ (b • g₂) (y - x) = b * inner ℝ g₂ (y - x) := by
        simpa using (inner_smul_left g₂ (y - x) b)
      rw [hsmul₁, hsmul₂]
      have hslope_combo :
          a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x) ≤
            withTopRealPart f y - withTopRealPart f x := by
        let d : ℝ := withTopRealPart f y - withTopRealPart f x
        have hmul₁ :
            a * inner ℝ g₁ (y - x) ≤ a * d :=
          mul_le_mul_of_nonneg_left hslope₁ ha
        have hmul₂ :
            b * inner ℝ g₂ (y - x) ≤ b * d :=
          mul_le_mul_of_nonneg_left hslope₂ hb
        calc
          a * inner ℝ g₁ (y - x) + b * inner ℝ g₂ (y - x)
              ≤ a * d + b * d :=
            add_le_add hmul₁ hmul₂
          _ = (a + b) * d := by ring_nf
          _ = d := by rw [hab, one_mul]
          _ = withTopRealPart f y - withTopRealPart f x := rfl
      linarith
    have hcombo_withTop :
        (((withTopRealPart f x + inner ℝ (a • g₁ + b • g₂) (y - x) : ℝ) : WithTop ℝ) ≤ f y) :=
      (le_withTopRealPart_iff hyf).mp hcombo_real
    rw [WithTop.coe_add, coe_withTopRealPart hxdom] at hcombo_withTop
    exact hcombo_withTop
  · -- Outside the effective domain the value of `f` is `⊤`, so the support inequality is trivial.
    have htop : f y = ⊤ := by
      rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hyf
      exact not_ne_iff.mp hyf
    simp [htop]

/-- Lemma 3.14 [Chapter3_2.json:8] (2): for every
`x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ`, the constrained subdifferential of the pointwise
supremum contains the convex hull of the constrained subdifferentials of the active slices
`y ∈ activePointwiseSupremumOnIndices Δ φ x`. -/
-- Proof sketch: each active-slice subgradient is already a constrained subgradient of the
-- supremum by the support-inequality comparison, and then `convexHull_min` upgrades that union
-- inclusion to the convex hull because the target constrained subdifferential is convex.
theorem convexHull_activePointwiseSupremumOnSubdifferentials_subset
    {Q : Set E} {Δ : Set ι} {φ : E → ι → WithTop ℝ} {x : E}
    (hx : x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ) :
    convexHull ℝ
        (⋃ y ∈ activePointwiseSupremumOnIndices Δ φ x,
          ∂[Q] (fun z ↦ φ z y) (x)) ⊆
      ∂[pointwiseSupremumOnEffectiveDomain Q Δ φ] (pointwiseSupremumOn Δ φ) (x) := by
  -- First place each active-slice subgradient inside the target subdifferential.
  refine convexHull_min ?_ (convex_constrainedSubdifferential (Q := pointwiseSupremumOnEffectiveDomain Q Δ φ)
    (f := pointwiseSupremumOn Δ φ) (x := x))
  intro g hg
  rcases mem_iUnion.mp hg with ⟨y, hg⟩
  rcases mem_iUnion.mp hg with ⟨hy, hg⟩
  exact mem_constrainedSubdifferential_pointwiseSupremumOn_of_mem_active hx hy hg

end

/-! ### Proposition_3_14 (from Chap03) -/
noncomputable section

open Set
open scoped BigOperators Pointwise RealInnerProductSpace WithTopConvexAnalysis

universe u v

variable {ι : Type u} {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Proposition 3.14 lies in the chapter's convex-subdifferential / finite absolute-inner-sum
domain.

The source-faithful route is:
1. rewrite `y ↦ ∑ i ∈ s, |⟪a i, y⟫|` as the finite supremum over all sign patterns;
2. identify each signed slice as a linear functional with singleton subdifferential;
3. compute the convex hull of the active signed sums as the fixed positive/negative base plus the
   zero-coordinate segment sum.

This file keeps that route explicit. The remaining blocker is not the mathematical skeleton but the
attach-indexed finite-sum normalization needed to pass from active sign patterns to the displayed
surface formula. -/

/-- Helper for Proposition 3.14: a sign choice on the finite index family `s`. -/
abbrev SignPattern (s : Finset ι) :=
  s → Bool

/-- Helper for Proposition 3.14: the signed vector sum attached to a sign pattern. -/
abbrev signedVectorSum (s : Finset ι) (a : ι → V) (σ : SignPattern s) : V :=
  ∑ i : s, if σ i then a i.1 else -a i.1

/-- Helper for Proposition 3.14: the linear slice corresponding to a sign pattern. -/
abbrev signedSlice (s : Finset ι) (a : ι → V) (σ : SignPattern s) (y : V) : ℝ :=
  ∑ i : s, if σ i then ⟪a i.1, y⟫ else -⟪a i.1, y⟫

/-- Helper for Proposition 3.14: each signed scalar term is bounded above by the corresponding
absolute value. -/
lemma signed_term_le_abs (b : Bool) (t : ℝ) :
    (if b then t else -t) ≤ |t| := by
  by_cases hb : b
  · simp [hb, le_abs_self]
  · simp [hb, neg_le_abs]

/-- Helper for Proposition 3.14: a signed slice is the inner product against its signed vector
sum. -/
lemma signedSlice_eq_inner_signedVectorSum
    (s : Finset ι) (a : ι → V) (σ : SignPattern s) :
    signedSlice s a σ = fun y ↦ inner ℝ (signedVectorSum s a σ) y := by
  funext y
  -- Repackage the finite signed sum as one linear functional.
  rw [signedSlice, signedVectorSum, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hσ : σ i
  · simp [hσ]
  · simp [hσ, inner_neg_left]

/-- Helper for Proposition 3.14: a sum over the subtype `s` can be rewritten as a surface sum over
`s` by extending the summand with `0` off the finite set. -/
lemma sum_subtype_eq_sum_surface
    [DecidableEq ι] {W : Type*} [AddCommMonoid W]
    (s : Finset ι) (F : s → W) :
    (∑ i : s, F i) = ∑ j ∈ s, if h : j ∈ s then F ⟨j, h⟩ else 0 := by
  -- Normalize the subtype sum through `s.attach`, then collapse the attach proof.
  rw [Finset.univ_eq_attach]
  simpa using
    (Finset.sum_attach (s := s)
      (f := fun j ↦ if h : j ∈ s then F ⟨j, h⟩ else 0))

/-- Helper for Proposition 3.14: the signed vector sum has a surface-sum presentation over `s`. -/
lemma signed_sum_eq_surface_sum
    [DecidableEq ι] (s : Finset ι) (a : ι → V) (σ : SignPattern s) :
    signedVectorSum s a σ =
      ∑ j ∈ s, if h : j ∈ s then if σ ⟨j, h⟩ then a j else -a j else 0 := by
  -- Specialize the generic subtype-to-surface bridge to the signed vector summand.
  simpa [signedVectorSum] using
    (sum_subtype_eq_sum_surface
      (s := s) (F := fun i ↦ if σ i then a i.1 else -a i.1))

/-- Helper for Proposition 3.14: the signed slice has a surface-sum presentation over `s`. -/
lemma signed_slice_eq_surface_sum
    [DecidableEq ι] (s : Finset ι) (a : ι → V) (σ : SignPattern s) (y : V) :
    signedSlice s a σ y =
      ∑ j ∈ s, if h : j ∈ s then if σ ⟨j, h⟩ then ⟪a j, y⟫ else -⟪a j, y⟫ else 0 := by
  -- The same normalization works for the scalar signed slice.
  simpa [signedSlice] using
    (sum_subtype_eq_sum_surface
      (s := s) (F := fun i ↦ if σ i then ⟪a i.1, y⟫ else -⟪a i.1, y⟫))

/-- Helper for Proposition 3.14: the absolute-value subtype sum equals the usual surface sum over
`s`. -/
lemma subtype_abs_inner_sum_eq_surface_sum
    (s : Finset ι) (a : ι → V) (y : V) :
    (∑ i : s, |⟪a i.1, y⟫|) = ∑ i ∈ s, |⟪a i, y⟫| := by
  -- Rewrite the subtype sum through `s.attach`, where the summand depends only on the ambient
  -- index and no longer on the membership proof.
  rw [Finset.univ_eq_attach]
  simpa using (Finset.sum_attach (s := s) (f := fun i ↦ |⟪a i, y⟫|))

/-- Helper for Proposition 3.14: the sign-pattern supremum route does produce the original
absolute-value sum. -/
lemma sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns
    (s : Finset ι) (a : ι → V) :
    pointwiseSupremumOn (Set.univ : Set (SignPattern s))
        (fun y σ ↦ (signedSlice s a σ y : WithTop ℝ)) =
      fun y ↦ (((∑ i ∈ s, |⟪a i, y⟫|) : ℝ) : WithTop ℝ) := by
  classical
  let _ : Fintype (SignPattern s) := inferInstance
  let _ : Nonempty (SignPattern s) := ⟨fun _ ↦ false⟩
  funext y
  -- Evaluate the finite supremum at `y` and bound it termwise by the absolute-value sum.
  rw [pointwiseSupremumOn_univ_eq_sup' (ι := SignPattern s)]
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le Finset.univ_nonempty
        (fun σ : SignPattern s ↦ (signedSlice s a σ y : WithTop ℝ)) ?_
    intro σ hσ
    have hreal : signedSlice s a σ y ≤ ∑ i : s, |⟪a i.1, y⟫| := by
      -- Each signed term is bounded above by the corresponding absolute value.
      rw [signedSlice]
      refine Finset.sum_le_sum ?_
      intro i hi
      exact signed_term_le_abs (σ i) ⟪a i.1, y⟫
    rw [subtype_abs_inner_sum_eq_surface_sum] at hreal
    exact show ((signedSlice s a σ y : ℝ) : WithTop ℝ) ≤
        (((∑ i ∈ s, |⟪a i, y⟫| : ℝ) : ℝ) : WithTop ℝ) from by
      exact_mod_cast hreal
  · let σ0 : SignPattern s := fun i ↦ decide (0 ≤ ⟪a i.1, y⟫)
    have hreal : signedSlice s a σ0 y = ∑ i : s, |⟪a i.1, y⟫| := by
      -- Choose the maximizing sign pattern given by the sign of each inner product.
      rw [signedSlice]
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hnonneg : 0 ≤ ⟪a i.1, y⟫
      · simp [σ0, hnonneg, abs_of_nonneg]
      · have hneg : ⟪a i.1, y⟫ < 0 := lt_of_not_ge hnonneg
        simp [σ0, hnonneg, abs_of_neg hneg]
    have hsurf :
        (signedSlice s a σ0 y : WithTop ℝ) =
          (((∑ i ∈ s, |⟪a i, y⟫| : ℝ) : ℝ) : WithTop ℝ) := by
      -- The maximizing subtype sum is the displayed surface sum.
      rw [hreal, subtype_abs_inner_sum_eq_surface_sum]
    rw [← hsurf]
    exact Finset.le_sup'
      (s := (Finset.univ : Finset (SignPattern s)))
      (f := fun σ : SignPattern s ↦ (signedSlice s a σ y : WithTop ℝ))
      (by simp [σ0])

/-- Helper for Proposition 3.14: a linear inner-product functional has singleton
subdifferential given by its coefficient vector. -/
lemma subdifferential_inner_eq_singleton (v x : V) :
    ∂ (fun y ↦ ((inner ℝ v y) : ℝ))(x) = {v} := by
  ext g
  rw [Set.mem_singleton_iff, mem_subdifferential_coe_real_iff]
  constructor
  · intro hg
    -- Test the subgradient inequality in the direction `g - v` to force the norm gap to vanish.
    have hz := hg (x + (g - v))
    have hineq : inner ℝ g (g - v) ≤ inner ℝ v (g - v) := by
      have hrewrite :
          inner ℝ v (x + (g - v)) = inner ℝ v x + inner ℝ v (g - v) := by
        rw [inner_add_right]
      have hsub : x + (g - v) - x = g - v := by
        abel_nf
      rw [hrewrite, hsub] at hz
      linarith
    have hnonpos : ‖g - v‖ ^ (2 : ℕ) ≤ 0 := by
      have hpair : inner ℝ (g - v) (g - v) ≤ 0 := by
        calc
          inner ℝ (g - v) (g - v) = inner ℝ g (g - v) - inner ℝ v (g - v) := by
            rw [inner_sub_left]
          _ ≤ 0 := sub_nonpos.mpr hineq
      simpa [real_inner_self_eq_norm_sq] using hpair
    have hzeroNorm : ‖g - v‖ = 0 := by
      nlinarith [sq_nonneg ‖g - v‖, hnonpos]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzeroNorm)
  · intro hg
    subst hg
    intro y
    -- For the true coefficient vector, the affine support inequality is an equality.
    have hy : y = x + (y - x) := by
      abel_nf
    have hsub : x + (y - x) - x = y - x := by
      abel_nf
    rw [hy, inner_add_right, hsub]

/-- Helper for Proposition 3.14: every signed slice has singleton subdifferential given by its
signed vector sum. -/
lemma subdifferential_signed_inner_slice_eq_singleton
    (s : Finset ι) (a : ι → V) (σ : SignPattern s) (x : V) :
    ∂ (fun y ↦ (signedSlice s a σ y : WithTop ℝ))(x) =
      {signedVectorSum s a σ} := by
  -- Rewrite the slice to the canonical linear form and apply the singleton computation.
  rw [signedSlice_eq_inner_signedVectorSum]
  simpa using subdifferential_inner_eq_singleton (signedVectorSum s a σ) x

/-- Helper for Proposition 3.14: equality in the scalar signed-term bound forces the expected sign
choice away from the zero case. -/
lemma signed_term_eq_abs_iff_sign_choice (b : Bool) (t : ℝ) :
    (if b then t else -t) = |t| ↔
      (0 < t → b = true) ∧ (t < 0 → b = false) := by
  constructor
  · intro h
    constructor
    · intro ht
      by_cases hb : b = true
      · exact hb
      · have hb' : b = false := by
          cases b <;> simp at hb ⊢
        have : -t = t := by simpa [hb', abs_of_pos ht] using h
        linarith
    · intro ht
      by_cases hb : b = true
      · have : t = -t := by simpa [hb, abs_of_neg ht] using h
        linarith
      · have hb' : b = false := by
          cases b <;> simp at hb ⊢
        exact hb'
  · rintro ⟨hpos, hneg⟩
    by_cases ht_pos : 0 < t
    · have hb : b = true := hpos ht_pos
      simp [hb, abs_of_pos ht_pos]
    · by_cases ht_neg : t < 0
      · have hb : b = false := hneg ht_neg
        simp [hb, abs_of_neg ht_neg]
      · have ht_zero : t = 0 := by linarith
        simp [ht_zero]

/-- Helper for Proposition 3.14: a finite Minkowski sum of symmetric two-point sets is exactly the
set of the corresponding signed surface sums. -/
lemma mem_sum_pairs_iff_exists_signed_sum
    (s : Finset ι) (a : ι → V) (z : V) :
    z ∈ s.sum (fun i ↦ ({-a i, a i} : Set V)) ↔
      ∃ ε : ι → Bool, z = ∑ i ∈ s, if ε i then a i else -a i := by
  classical
  induction s using Finset.induction_on generalizing z with
  | empty =>
      constructor
      · intro hz
        -- The empty Minkowski sum is `{0}`, so any witness sign function works.
        refine ⟨fun _ ↦ false, ?_⟩
        simpa using hz
      · rintro ⟨ε, hz⟩
        simp [hz]
  | @insert i s hi ih =>
      constructor
      · intro hz
        -- Peel off the `i`-th two-point contribution and apply the induction hypothesis.
        rw [Finset.sum_insert hi, Set.mem_add] at hz
        rcases hz with ⟨u, hu, w, hw, rfl⟩
        rcases (ih w).1 hw with ⟨ε, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · let ε' : ι → Bool := Function.update ε i false
          have hs :
              (∑ j ∈ s, if ε' j then a j else -a j) =
                ∑ j ∈ s, if ε j then a j else -a j := by
            -- Off the inserted index, the updated sign function agrees with `ε`.
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              intro hji
              exact hi (by simpa [hji] using hj)
            simp [ε', hji]
          refine ⟨ε', ?_⟩
          rw [Finset.sum_insert hi, hs]
          simp [ε']
        · let ε' : ι → Bool := Function.update ε i true
          have hs :
              (∑ j ∈ s, if ε' j then a j else -a j) =
                ∑ j ∈ s, if ε j then a j else -a j := by
            -- The same update argument handles the positive sign choice.
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              intro hji
              exact hi (by simpa [hji] using hj)
            simp [ε', hji]
          refine ⟨ε', ?_⟩
          rw [Finset.sum_insert hi, hs]
          simp [ε']
      · rintro ⟨ε, rfl⟩
        -- Rebuild the Minkowski-sum witness from the current sign at `i` and the inductive tail.
        rw [Finset.sum_insert hi]
        refine Set.mem_add.2 ?_
        have hzsum :
            ((if ε i then a i else -a i) + ∑ j ∈ s, if ε j then a j else -a j) =
              ∑ j ∈ insert i s, if ε j then a j else -a j := by
          rw [Finset.sum_insert hi]
        refine ⟨if ε i then a i else -a i, ?_, ∑ j ∈ s, if ε j then a j else -a j, ?_, hzsum⟩
        · by_cases hε : ε i
          · simp [hε]
          · simp [hε]
        · exact (ih _).2 ⟨ε, rfl⟩

/-- Helper for Proposition 3.14: the signed-gap sum vanishes exactly when every coordinatewise
gap vanishes. -/
lemma surface_signed_gap_sum_eq_zero_iff
    (s : Finset ι) (a : ι → V) (x : V) (σ : SignPattern s) :
    (∑ i : s, (|⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫))) = 0 ↔
      ∀ i : s, |⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫) = 0 := by
  let gap : s → ℝ := fun i ↦ |⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫)
  have hnonneg : ∀ i ∈ (Finset.univ : Finset s), 0 ≤ gap i := by
    intro i hi
    dsimp [gap]
    exact sub_nonneg.mpr (signed_term_le_abs (σ i) ⟪a i.1, x⟫)
  -- The whole sum can be zero only if every nonnegative coordinate gap is zero.
  simpa [gap] using
    (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset s)) hnonneg)

/-- Helper for Proposition 3.14: once the positive and negative signs are fixed, the signed
surface sum splits into the positive base, the negative base, and the remaining zero-part
contribution. -/
lemma signed_surface_sum_decomposition
    (s : Finset ι) (a : ι → V) (x : V) (ε : ι → Bool)
    (hpos : ∀ i ∈ s, 0 < ⟪a i, x⟫ → ε i = true)
    (hneg : ∀ i ∈ s, ⟪a i, x⟫ < 0 → ε i = false) :
    ∑ i ∈ s, (if ε i then a i else -a i) =
      (s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
        (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a +
          Finset.sum (s.filter (fun i ↦ ⟪a i, x⟫ = 0)) (fun i ↦ if ε i then a i else -a i) := by
  classical
  let pos : ι → Prop := fun i ↦ 0 < ⟪a i, x⟫
  let neg : ι → Prop := fun i ↦ ⟪a i, x⟫ < 0
  let term : ι → V := fun i ↦ if ε i then a i else -a i
  have hsplitPos :=
    (Finset.sum_filter_add_sum_filter_not s pos term).symm
  have hsplitNeg :=
    (Finset.sum_filter_add_sum_filter_not (s.filter fun i ↦ ¬ pos i) neg term).symm
  have hposSum : Finset.sum (s.filter pos) term = Finset.sum (s.filter pos) a := by
    -- On the positive coordinates the sign is forced to be `true`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hipos : 0 < ⟪a i, x⟫ := (Finset.mem_filter.mp hi).2
    have hε : ε i = true := hpos i his hipos
    simp [term, hε]
  have hnegFilter :
      (s.filter (fun i ↦ ¬ pos i)).filter neg = s.filter neg := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hi₁, hneg'⟩
      rw [Finset.mem_filter] at hi₁
      rcases hi₁ with ⟨his, hnotPos⟩
      rw [Finset.mem_filter]
      exact ⟨his, hneg'⟩
    · intro hi
      rw [Finset.mem_filter] at hi ⊢
      rcases hi with ⟨his, hneg'⟩
      refine ⟨?_, hneg'⟩
      rw [Finset.mem_filter]
      refine ⟨his, ?_⟩
      linarith
  have hnegSum :
      Finset.sum ((s.filter (fun i ↦ ¬ pos i)).filter neg) term = -(Finset.sum (s.filter neg) a) := by
    rw [hnegFilter]
    calc
      Finset.sum (s.filter neg) term = Finset.sum (s.filter neg) (fun i ↦ -a i) := by
        -- On the negative coordinates the sign is forced to be `false`.
        refine Finset.sum_congr rfl ?_
        intro i hi
        have his : i ∈ s := (Finset.mem_filter.mp hi).1
        have hneg' : ⟪a i, x⟫ < 0 := (Finset.mem_filter.mp hi).2
        have hε : ε i = false := hneg i his hneg'
        simp [term, hε]
      _ = -(Finset.sum (s.filter neg) a) := by
        simp
  have hzeroFilter :
      (s.filter (fun i ↦ ¬ pos i)).filter (fun i ↦ ¬ neg i) =
        s.filter (fun i ↦ ⟪a i, x⟫ = 0) := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hi₁, hnotNeg⟩
      rw [Finset.mem_filter] at hi₁
      rcases hi₁ with ⟨his, hnotPos⟩
      rw [Finset.mem_filter]
      exact ⟨his, by linarith⟩
    · intro hi
      rw [Finset.mem_filter] at hi ⊢
      rcases hi with ⟨his, hzero⟩
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨his, ?_⟩
        linarith [hzero]
      · linarith [hzero]
  -- Split the surface sum into positive, negative, and zero branches before simplifying each
  -- branch separately.
  calc
    Finset.sum s term
        = Finset.sum (s.filter pos) term + Finset.sum (s.filter fun i ↦ ¬ pos i) term := by
            simpa [pos, term] using hsplitPos
    _ = Finset.sum (s.filter pos) term +
          (Finset.sum ((s.filter (fun i ↦ ¬ pos i)).filter neg) term +
            Finset.sum ((s.filter (fun i ↦ ¬ pos i)).filter (fun i ↦ ¬ neg i)) term) := by
          rw [hsplitNeg]
    _ = Finset.sum (s.filter pos) a +
          (-(Finset.sum (s.filter neg) a) +
            Finset.sum (s.filter fun i ↦ ⟪a i, x⟫ = 0) term) := by
          rw [hposSum, hnegSum, hzeroFilter]
    _ = (s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
          (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a +
            Finset.sum (s.filter (fun i ↦ ⟪a i, x⟫ = 0)) (fun i ↦ if ε i then a i else -a i) := by
          simp [pos, neg, term, sub_eq_add_neg, add_assoc]

/-- Helper for Proposition 3.14: an active sign pattern fixes the positive and negative
coordinates, while the zero coordinates remain free. -/
lemma mem_active_sign_pattern_iff
    (s : Finset ι) (a : ι → V) (x : V) (σ : SignPattern s) :
    σ ∈ activePointwiseSupremumOnIndices
          (Set.univ : Set (SignPattern s))
          (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
          x ↔
      (∀ i : s, 0 < ⟪a i.1, x⟫ → σ i = true) ∧
        (∀ i : s, ⟪a i.1, x⟫ < 0 → σ i = false) := by
  rw [mem_activePointwiseSupremumOnIndices_univ_iff,
    sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns]
  constructor
  · intro hσ
    have hsurfaceTop :
        ((signedSlice s a σ x : ℝ) : WithTop ℝ) =
          ((((∑ i ∈ s, |⟪a i, x⟫|) : ℝ) : ℝ) : WithTop ℝ) := by
      simpa using hσ
    have hsurface : signedSlice s a σ x = ∑ i ∈ s, |⟪a i, x⟫| := by
      exact_mod_cast hsurfaceTop
    have hsubtype : signedSlice s a σ x = ∑ i : s, |⟪a i.1, x⟫| := by
      rw [← subtype_abs_inner_sum_eq_surface_sum] at hsurface
      exact hsurface
    have hgapSum :
        (∑ i : s, (|⟪a i.1, x⟫| - (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫))) = 0 := by
      -- Activity means the total signed slice reaches the total absolute-value bound.
      have hsubtype' := hsubtype
      unfold signedSlice at hsubtype'
      rw [Finset.sum_sub_distrib, ← hsubtype']
      simp
    have hgap := (surface_signed_gap_sum_eq_zero_iff s a x σ).1 hgapSum
    constructor
    · intro i hiPos
      have hterm : (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫) = |⟪a i.1, x⟫| := by
        linarith [hgap i]
      exact ((signed_term_eq_abs_iff_sign_choice (σ i) ⟪a i.1, x⟫).1 hterm).1 hiPos
    · intro i hiNeg
      have hterm : (if σ i then ⟪a i.1, x⟫ else -⟪a i.1, x⟫) = |⟪a i.1, x⟫| := by
        linarith [hgap i]
      exact ((signed_term_eq_abs_iff_sign_choice (σ i) ⟪a i.1, x⟫).1 hterm).2 hiNeg
  · rintro ⟨hpos, hneg⟩
    have hsubtype : signedSlice s a σ x = ∑ i : s, |⟪a i.1, x⟫| := by
      -- The sign constraints force equality in each scalar bound.
      rw [signedSlice]
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact (signed_term_eq_abs_iff_sign_choice (σ i) ⟪a i.1, x⟫).2
        ⟨hpos i, hneg i⟩
    have hsurface : signedSlice s a σ x = ∑ i ∈ s, |⟪a i, x⟫| := by
      rw [hsubtype, subtype_abs_inner_sum_eq_surface_sum]
    simpa using congrArg (fun t : ℝ ↦ ((t : ℝ) : WithTop ℝ)) hsurface

/-- Helper for Proposition 3.14: the active signed sums equal the fixed positive-minus-negative
base translated by the zero-coordinate sign choices. -/
lemma active_signed_sums_eq_base_add_zero_pairs
    (s : Finset ι) (a : ι → V) (x : V) :
    {g | ∃ σ : SignPattern s,
        σ ∈ activePointwiseSupremumOnIndices
              (Set.univ : Set (SignPattern s))
              (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
              x ∧
          g = signedVectorSum s a σ} =
      ({(s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
          (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a} : Set V) +
        (s.filter fun i ↦ ⟪a i, x⟫ = 0).sum (fun i ↦ ({-a i, a i} : Set V)) := by
  classical
  let base : V :=
    (s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
      (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a
  let zeroSet : Finset ι := s.filter fun i ↦ ⟪a i, x⟫ = 0
  ext g
  constructor
  · rintro ⟨σ, hσactive, rfl⟩
    rcases (mem_active_sign_pattern_iff s a x σ).1 hσactive with ⟨hpos, hneg⟩
    let εσ : ι → Bool := fun i ↦ if h : i ∈ s then σ ⟨i, h⟩ else false
    have hsurface :
        signedVectorSum s a σ = ∑ i ∈ s, if εσ i then a i else -a i := by
      -- Extend the subtype sign pattern to an ambient surface sign choice.
      rw [signed_sum_eq_surface_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [εσ, hi]
    have hdecomp :=
      signed_surface_sum_decomposition s a x εσ
        (by
          intro i hi hiPos
          simpa [εσ, hi] using hpos ⟨i, hi⟩ hiPos)
        (by
          intro i hi hiNeg
          simpa [εσ, hi] using hneg ⟨i, hi⟩ hiNeg)
    have hzeroMem :
        (∑ i ∈ zeroSet, if εσ i then a i else -a i) ∈
          zeroSet.sum (fun i ↦ ({-a i, a i} : Set V)) := by
      exact (mem_sum_pairs_iff_exists_signed_sum
        (s := zeroSet) (a := a)
        (z := ∑ i ∈ zeroSet, if εσ i then a i else -a i)).2 ⟨εσ, rfl⟩
    have hsigned :
        signedVectorSum s a σ = base + ∑ i ∈ zeroSet, if εσ i then a i else -a i := by
      calc
        signedVectorSum s a σ = ∑ i ∈ s, if εσ i then a i else -a i := hsurface
        _ = base + ∑ i ∈ zeroSet, if εσ i then a i else -a i := by
          simpa [base, zeroSet, sub_eq_add_neg, add_assoc] using hdecomp
    refine Set.mem_add.2 ?_
    refine ⟨base, by simp [base], ∑ i ∈ zeroSet, if εσ i then a i else -a i, hzeroMem, ?_⟩
    exact hsigned.symm
  · intro hg
    rcases Set.mem_add.1 hg with ⟨b, hb, z, hz, hsum⟩
    have hb' : b = base := by
      simpa [base] using hb
    subst hb'
    rcases (mem_sum_pairs_iff_exists_signed_sum (s := zeroSet) (a := a) (z := z)).1 hz with
      ⟨ε0, hz0⟩
    let ε : ι → Bool := fun i ↦
      if hposi : 0 < ⟪a i, x⟫ then true else if hnegi : ⟪a i, x⟫ < 0 then false else ε0 i
    let σ : SignPattern s := fun i ↦ ε i.1
    have hσactive :
        σ ∈ activePointwiseSupremumOnIndices
              (Set.univ : Set (SignPattern s))
              (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
              x := by
      rw [mem_active_sign_pattern_iff]
      constructor
      · intro i hiPos
        -- Positive coordinates are forced to the positive sign.
        simp [σ, ε, hiPos]
      · intro i hiNeg
        -- Negative coordinates are forced to the negative sign.
        have hnotPos : ¬ 0 < ⟪a i.1, x⟫ := by
          linarith
        simp [σ, ε, hnotPos, hiNeg]
    have hsurface :
        signedVectorSum s a σ = ∑ i ∈ s, if ε i then a i else -a i := by
      -- The subtype sign pattern and the ambient sign choice agree on `s`.
      rw [signed_sum_eq_surface_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [σ, ε, hi]
    have hdecomp :=
      signed_surface_sum_decomposition s a x ε
        (by
          intro i hi hiPos
          simp [ε, hiPos])
        (by
          intro i hi hiNeg
          have hnotPos : ¬ 0 < ⟪a i, x⟫ := by
            linarith
          simp [ε, hnotPos, hiNeg])
    have hzeroSum :
        (∑ i ∈ zeroSet, if ε i then a i else -a i) = z := by
      rw [hz0]
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hzero : ⟪a i, x⟫ = 0 := (Finset.mem_filter.mp hi).2
      have hnotPos : ¬ 0 < ⟪a i, x⟫ := by
        linarith
      have hnotNeg : ¬ ⟪a i, x⟫ < 0 := by
        linarith
      simp [ε, hnotPos, hnotNeg]
    have hsigned : signedVectorSum s a σ = base + z := by
      calc
        signedVectorSum s a σ = ∑ i ∈ s, if ε i then a i else -a i := hsurface
        _ = base + ∑ i ∈ zeroSet, if ε i then a i else -a i := by
          simpa [base, zeroSet, sub_eq_add_neg, add_assoc] using hdecomp
        _ = base + z := by rw [hzeroSum]
    refine ⟨σ, hσactive, ?_⟩
    exact (hsigned.trans hsum).symm

/-- Helper for Proposition 3.14: each signed slice is a closed convex function. -/
lemma signed_slice_closedConvexFunction
    (s : Finset ι) (a : ι → V) (σ : SignPattern s) :
    ClosedConvexFunction (fun y ↦ (signedSlice s a σ y : WithTop ℝ)) := by
  -- Rewrite the slice to a linear functional and package convexity plus continuity.
  rw [signedSlice_eq_inner_signedVectorSum]
  apply closedConvexFunction_coe_of_convexOn_continuous
  · let L : V →ₗ[ℝ] ℝ :=
      { toFun := fun y ↦ inner ℝ (signedVectorSum s a σ) y
        map_add' := by
          intro y z
          rw [inner_add_right]
        map_smul' := by
          intro c y
          simpa [smul_eq_mul] using
            (inner_smul_right (signedVectorSum s a σ) y c) }
    -- Linear functionals are convex on the whole space.
    simpa using L.convexOn convex_univ
  · -- The inner-product pairing is continuous in its second argument.
    simpa using (continuous_const.inner continuous_id)

/-- Proposition 3.14: for `f(x) = ∑_{i ∈ s} |⟪aᵢ, x⟫|`, the subdifferential at `x` is the signed
sum of the active vectors with positive and negative inner products, translated by the Minkowski
sum of the symmetric line segments `[-aᵢ, aᵢ] = segment ℝ (-aᵢ) aᵢ` over the zero inner-product
indices. -/
-- Proof sketch: rewrite the function as the supremum over sign patterns, apply the finite
-- pointwise-supremum subdifferential theorem, rewrite each active slice subdifferential to a
-- singleton signed sum, and then replace the convex hull of active signed sums by the displayed
-- positive/negative base plus zero-index segment sum.
theorem subdifferential_sum_abs_inner_eq_signed_sum_add_zero_segments
    (s : Finset ι) (a : ι → V) (x : V) :
    ∂ (fun y ↦ ((∑ i ∈ s, |⟪a i, y⟫|) : ℝ))(x) =
      ({(s.filter fun i ↦ 0 < ⟪a i, x⟫).sum a -
          (s.filter fun i ↦ ⟪a i, x⟫ < 0).sum a} : Set V) +
        (s.filter fun i ↦ ⟪a i, x⟫ = 0).sum (fun i ↦ segment ℝ (-a i) (a i)) := by
  -- Route correction: the source proof runs through the finite sign-pattern supremum, not through
  -- the earlier support-function theorem with nonnegative multipliers.
  classical
  let _ : Fintype (SignPattern s) := inferInstance
  let _ : Finite (SignPattern s) := by infer_instance
  let _ : Nonempty (SignPattern s) := ⟨fun _ ↦ false⟩
  have hx :
      x ∈ interior
        (dom
          (pointwiseSupremumOn
            (Set.univ : Set (SignPattern s))
            (fun y σ ↦ (signedSlice s a σ y : WithTop ℝ)))) := by
    -- The sign-pattern supremum is the everywhere-finite absolute-value sum.
    rw [sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns]
    have hdom :
        dom (fun y : V ↦ ∑ i ∈ s, (↑|⟪a i, y⟫| : WithTop ℝ)) = (Set.univ : Set V) := by
      ext y
      simp
    simp [hdom]
  have hmain :=
    subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
      (ι := SignPattern s)
      (φ := fun y σ ↦ (signedSlice s a σ y : WithTop ℝ))
      (fun σ ↦ signed_slice_closedConvexFunction s a σ) hx
  have hactiveSet :
      {g | ∃ σ : SignPattern s,
          σ ∈ activePointwiseSupremumOnIndices
                (Set.univ : Set (SignPattern s))
                (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
                x ∧
            g ∈ ∂ (fun y ↦ (signedSlice s a σ y : WithTop ℝ))(x)} =
        {g | ∃ σ : SignPattern s,
            σ ∈ activePointwiseSupremumOnIndices
                  (Set.univ : Set (SignPattern s))
                  (fun y τ ↦ (signedSlice s a τ y : WithTop ℝ))
                  x ∧
              g = signedVectorSum s a σ} := by
    ext g
    constructor
    · rintro ⟨σ, hσ, hg⟩
      rw [subdifferential_signed_inner_slice_eq_singleton] at hg
      exact ⟨σ, hσ, Set.mem_singleton_iff.mp hg⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨σ, hσ, ?_⟩
      rw [subdifferential_signed_inner_slice_eq_singleton]
      simp
  -- Replace the finite supremum by the absolute-value sum, then compute the active hull.
  rw [← sum_abs_inner_eq_pointwiseSupremumOn_sign_patterns (s := s) (a := a)]
  rw [hmain, hactiveSet, active_signed_sums_eq_base_add_zero_pairs, convexHull_add,
    convexHull_singleton, convexHull_sum]
  simp [convexHull_pair]

end

/-! ### Theorem_3_14 (from Chap03) -/
/- Theorem 3.14 lies in the chapter's convex directional-derivative domain.

Sampled owner-style declarations:
- `HasDirectionalDerivAt` in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_3_1`, the source-facing owner for one-sided directional
  derivatives of extended-real-valued functions;
- `exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain` in
  `LecturesConvexOptimization_Nesterov_2018.Chap03.Theorem_3_1_12`, the canonical secant-slope existence theorem for convex
  `WithTop ℝ`-valued functions at interior points;
- `ConvexOn.slope_mono` and `bddBelow_slope_lt_of_mem_interior` in mathlib
  `Mathlib/Analysis/Convex/Deriv.lean`, the one-variable slope monotonicity and interior-point
  boundedness lemmas underlying the owner theorem.

Best owner abstraction:
- source-facing: Theorem 3.14's one-sided directional-slope limit statement at an interior point
  of the effective domain;
- core/canonical: the stronger chapter theorem
  `exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain`;
- bridge/view: the `EReal`-valued limit presentation obtained by coercing the owner theorem's
  finite real limit.

Primitive data:
- a convexity witness
  `hf : ConvexOn ℝ {y : E | f y < ⊤} (fun y ↦ (f y).untopD 0)`;
- an interior point `hx : x ∈ interior {y : E | f y < ⊤}`.

Derived API:
- the eventual finiteness of the ray `α ↦ x + α • p`, already bundled in the owner theorem;
- the finite real right limit of the secant slopes, also bundled in the owner theorem;
- the weaker `EReal`-valued limit form stated by the textbook item.

The previous file reintroduced a second public theorem name for a weaker consequence of the
already-canonical chapter theorem in `Theorem_3_1_12`. Since the stronger owner theorem is the
correct reusable API and there are no direct downstream uses of the duplicate local name, this file
now recalls the owner theorem directly instead of preserving a parallel wrapper.
-/

recall exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
