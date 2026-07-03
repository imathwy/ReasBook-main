import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_17 (from Chap03) -/
universe u v

open Set

section

variable {α : Type u} {β : Type v}
variable (𝒮 : α → Set β) (X : Set α) (y : β)

/-- Definition 3.17 (Intersection of images of a set-valued mapping): the common-value set of
all images `𝒮 x` with `x ∈ X`. -/
def intersectionOfImages : Set β :=
  ⋂ x ∈ X, 𝒮 x

/-- Helper for Definition 3.17: membership in the intersection of images means belonging to every
image indexed by `X`. -/
theorem mem_intersectionOfImages_iff :
    y ∈ intersectionOfImages 𝒮 X ↔ ∀ x ∈ X, y ∈ 𝒮 x := by
  -- Unfold the source-facing definition to reach the canonical bounded intersection.
  unfold intersectionOfImages
  -- The generic membership rule for bounded intersections is exactly the desired expansion.
  exact
    (Set.mem_iInter₂ : y ∈ (⋂ x ∈ X, 𝒮 x : Set β) ↔ ∀ x ∈ X, y ∈ 𝒮 x)

end

/-! ### Lemma_3_17 (from Chap03) -/
open scoped BigOperators Gradient Pointwise WithTopConvexAnalysis

noncomputable section

universe u

variable {m : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "Y" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.17 lies in the constrained convex-composition / relative-subdifferential domain.

Sampled owner-style declarations:
- `vectorMap` in `Lemma_3_1_16`
- mathlib `Monotone` and `HasGradientAt` on `Fin m → ℝ`
- `constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum` in `Lemma_3_1_17`
- the real-valued constrained-subdifferential notation `∂[Q] f(x)` and bridge
  `subdifferentialWithin` in `Theorem_3_44`

Best owner abstractions:
- source-facing: Lemma 3.17's real-valued relative-subdifferential chain rule
- core/canonical: `vectorMap` together with
  `constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum`
- bridge/view: the chapter's real-valued relative-subdifferential surface `∂[Q] f(x)`, implemented
  through `subdifferentialWithin`

Primitive data:
- a convex feasible set `Q`
- a coordinate family `fs : Fin m → E → ℝ`
- a convex coordinatewise-monotone outer function `F : Y → ℝ`

Derived API:
- convexity of `F ∘ vectorMap fs` on `Q`
- the real-valued chain-rule equality and its subset corollary on `∂[Q] f(x)`

Source/core/bridge triage:
- source-facing: Lemma 3.17's chain-rule statement for real-valued relative subdifferentials
- core/canonical: the constrained-subdifferential owner theorem in `Lemma_3_1_17`
- bridge/view: this file's `∂[Q] f(x)` reformulation of that owner theorem

This file therefore deletes the exact-interface duplicate wrapper theorem and keeps only the
real-valued bridge to the canonical owner surface `∂[Q] f(x)`, plus the one genuine local
subset corollary.
-/

/- Upstream owner theorem reused below:
`convexOn_comp_coordinatewiseMonotone` from `Lemma_3_1_17`. -/

recall convexOn_comp_coordinatewiseMonotone

section

variable {Q : Set E} {fs : Fin m → E → ℝ} {F : Y → ℝ}
variable (hF_convex : ConvexOn ℝ Set.univ F)
variable (hQ_convex : Convex ℝ Q)
variable (hfs_convex : ∀ i, ConvexOn ℝ Q (fs i))
variable (hF_mono : Monotone (F ∘ (EuclideanSpace.equiv (Fin m) ℝ).symm))

/-- Lemma 3.17 (2): under the same hypotheses, the real-valued relative subdifferential
`∂[Q] (F ∘ vectorMap fs) (x)` equals the weighted sum of the coordinate relative
subdifferentials `∑ i, g i • ∂[Q] (fs i) (x)` for a gradient witness
`HasGradientAt F g (vectorMap fs x)`. -/
theorem subdifferentialWithin_comp_coordinatewiseMonotone_eq_weighted_sum
    {x : E} (_hx : x ∈ interior Q) {g : Y}
    (_hF_grad : HasGradientAt F g (vectorMap fs x)) :
    ∂[Q] (F ∘ vectorMap fs) (x) =
      ∑ i,
        (g i) • ∂[Q] (fs i) (x) :=
  let _ : Decidable (x ∈ interior Q) := Classical.decPred (fun y : E ↦ y ∈ interior Q) x
  if hx' : x ∈ interior Q then
    constrainedSubdifferential_comp_coordinatewiseMonotone_eq_weighted_sum
      hQ_convex hF_convex hfs_convex hF_mono hx' _hF_grad
  else
    False.elim (hx' _hx)

/-- Lemma 3.17 (1): at each interior point `x ∈ interior Q`, the weighted sum of the coordinate
relative subdifferentials `∂[Q] (fs i) (x)`, with weights given by the coordinates of
the gradient witness `g`, is contained in
`∂[Q] (F ∘ vectorMap fs) (x)`. -/
theorem weighted_sum_subdifferentialWithin_subset_comp_coordinatewiseMonotone
    {x : E} (_hx : x ∈ interior Q) {g : Y}
    (_hF_grad : HasGradientAt F g (vectorMap fs x)) :
    (∑ i,
        (g i) • ∂[Q] (fs i) (x)) ⊆
      ∂[Q] (F ∘ vectorMap fs) (x) :=
  let _ : Decidable (x ∈ interior Q) := Classical.decPred (fun y : E ↦ y ∈ interior Q) x
  if hx' : x ∈ interior Q then
    fun g hg ↦
      (subdifferentialWithin_comp_coordinatewiseMonotone_eq_weighted_sum
        hF_convex hQ_convex hfs_convex hF_mono hx' _hF_grad).symm ▸ hg
  else
    False.elim (hx' _hx)

end

end

/-! ### Proposition_3_17 (from Chap03) -/
noncomputable section

open scoped BigOperators Pointwise WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

/- Proposition 3.17 lies in the chapter's Euclidean `ℓ₁`-subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`;
- `EuclideanSpace.l1Seminorm` in `Definition_3_7`, the project owner for the coordinate `ℓ₁`
  seminorm on `ℝⁿ`;
- `EuclideanSpace.linftyClosedBall` in `Chap01/Definition_1_3_2`, the source-facing `ℓ∞` unit-ball
  owner;
- `subdifferential_sum_abs_inner_eq_signed_sum_add_zero_segments` in `Proposition_3_14`, the
  chapter owner theorem for finite absolute-inner sums.

Best owner abstraction:
- the Chapter 3 subdifferential owner specialized through
  `subdifferential_sum_abs_inner_eq_signed_sum_add_zero_segments` to the standard basis.

Primitive data:
- the ambient dimension `n`;
- the point `x : E`.

Derived API:
- the signed-basis plus zero-segment description of `∂ ‖·‖₁ (x)`;
- the coordinatewise sign specification;
- the origin specialization to the closed `ℓ∞` unit ball.

Source/core/bridge triage:
- source-facing: Proposition 3.17's `ℓ₁`-subdifferential formulas on `ℝⁿ`;
- core/canonical: `subdifferential` together with Proposition 3.14's finite absolute-inner-sum
  owner theorem;
- bridge/view: the explicit `WithTop` lift
  `fun y ↦ ((EuclideanSpace.l1Seminorm n) y : WithTop ℝ)`, the coordinatewise sign conditions, and
  the origin specialization.

The previous version rebuilt three public filtered-index helpers for positive, negative, and zero
coordinates. Those finsets are only proof/view data for the `Finset.univ` specialization of
Proposition 3.14, so this file now reuses that owner theorem directly and keeps only theorem-level
views. -/

private theorem inner_standardBasis (x : E) (i : Fin n) :
    inner ℝ (e[i]) x = x i := by
  simpa using (EuclideanSpace.inner_single_left i (1 : ℝ) x)

/-- Proposition 3.17: the subdifferential of the `ℓ₁`-norm on `ℝⁿ` is the signed sum of the
active standard basis vectors, translated by the Minkowski sum of the symmetric line segments
`[-e_i, e_i] = segment ℝ (-e_i) e_i` over the zero coordinates. -/
-- Proof sketch: specialize Proposition 3.14 to the standard basis family
-- `i ↦ EuclideanSpace.single i 1`. The identity
-- `EuclideanSpace.l1Seminorm n y = ∑ i, |⟪e_i, y⟫|` is the coordinate `ℓ₁` formula together with
-- the Euclidean basis inner-product evaluation.
theorem subdifferential_l1Seminorm_eq_signedBasis_add_segmentSum
    (x : E) :
    ∂ (fun y : E ↦ ((EuclideanSpace.l1Seminorm n) y : WithTop ℝ))(x) =
      ({(Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
          (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])} : Set E) +
        (Finset.univ.filter fun i ↦ x i = 0).sum (fun i ↦ segment ℝ (-e[i]) e[i]) := by
  have hl1 :
      (fun y : E ↦ ((EuclideanSpace.l1Seminorm n) y : WithTop ℝ)) =
        fun y : E ↦ ((∑ i, |y i| : ℝ) : WithTop ℝ) := by
    funext y
    rw [EuclideanSpace.l1Seminorm_apply]
    simp [Real.norm_eq_abs]
  calc
    ∂ (fun y : E ↦ ((EuclideanSpace.l1Seminorm n) y : WithTop ℝ))(x)
        = ∂ (fun y : E ↦ ((∑ i, |y i| : ℝ) : WithTop ℝ))(x) := by
          rw [hl1]
    _ = ({(Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
            (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])} : Set E) +
          (Finset.univ.filter fun i ↦ x i = 0).sum (fun i ↦ segment ℝ (-e[i]) e[i]) := by
        simpa [inner_standardBasis] using
          subdifferential_sum_abs_inner_eq_signed_sum_add_zero_segments Finset.univ (fun i ↦ e[i]) x

/-- Helper for Proposition 3.17: evaluating the conditional standard basis term at a coordinate
reduces to a Kronecker-delta test. -/
-- Proof sketch: split on whether the source and target coordinates agree, then on whether the
-- predicate includes the source basis vector.
private lemma coord_apply (p : Fin n → Prop) [DecidablePred p] (a j : Fin n) :
    ((if p a then e[a] else 0 : E) j) = if a = j then (if p j then 1 else 0) else 0 := by
  by_cases haj : a = j
  · by_cases hpj : p j
    · simp [haj, hpj]
    · simp [haj, hpj]
  · by_cases hpa : p a
    · simp [hpa, haj]
    · simp [hpa, haj]

/-- Helper for Proposition 3.17: the coordinate of a filtered sum of standard basis vectors is the
indicator of the filter predicate. -/
-- Proof sketch: rewrite the filtered sum as an unrestricted sum of conditional basis vectors,
-- evaluate coordinatewise, and collapse the resulting Kronecker-delta sum.
private lemma filtered_standard_basis_sum_apply (p : Fin n → Prop) [DecidablePred p] (j : Fin n) :
    ((Finset.univ.filter p).sum (fun i ↦ e[i])) j = if p j then 1 else 0 := by
  rw [Finset.sum_filter]
  calc
    ((∑ a : Fin n, if p a then e[a] else 0 : E) j) =
        ∑ a : Fin n, ((if p a then e[a] else 0 : E) j) := by
          simpa using (Finset.sum_apply j Finset.univ (fun a : Fin n ↦ if p a then e[a] else 0))
    _ = ∑ a : Fin n, (if a = j then (if p j then 1 else 0) else 0) := by
          simp_rw [coord_apply]
    _ = if p j then 1 else 0 := by
          rw [Finset.sum_ite_eq']
          simp

/-- Helper for Proposition 3.17: a vector lies in the segment `[-e[i], e[i]]` exactly when it is a
scalar multiple of `e[i]` with coefficient in `[-1, 1]`. -/
-- Proof sketch: rewrite the segment as the line-map image of `[0, 1]`, then convert between the
-- line-map parameter `t` and the coefficient `2t - 1`.
private lemma mem_standard_basis_segment_iff (i : Fin n) (v : E) :
    v ∈ segment ℝ (-e[i]) e[i] ↔ ∃ a : ℝ, a ∈ Set.Icc (-1) 1 ∧ v = a • e[i] := by
  constructor
  · intro hv
    rw [segment_eq_image_lineMap] at hv
    rcases hv with ⟨t, ht, rfl⟩
    refine ⟨2 * t - 1, ?_, ?_⟩
    · rcases ht with ⟨ht0, ht1⟩
      constructor <;> linarith
    · rw [AffineMap.lineMap_apply_module]
      ext j
      by_cases hji : j = i
      · subst hji
        simp
        ring_nf
      · simp [hji]
  · rintro ⟨a, ha, rfl⟩
    rw [segment_eq_image_lineMap]
    refine ⟨(a + 1) / 2, ?_, ?_⟩
    · rcases ha with ⟨ha0, ha1⟩
      constructor <;> linarith
    · rw [AffineMap.lineMap_apply_module]
      ext j
      by_cases hji : j = i
      · subst hji
        simp
        ring_nf
      · simp [hji]

/-- Helper for Proposition 3.17: the Minkowski sum of the segments `[-e[i], e[i]]` over a finite
set of indices is exactly the coordinate box supported on that set. -/
-- Proof sketch: induct on the finite index set. The forward step reads a Minkowski-sum element as
-- one segment contribution plus a smaller supported box; the reverse step peels off the current
-- coordinate and reconstructs the remainder.
private lemma mem_standard_basis_segment_sum_iff (s : Finset (Fin n)) (v : E) :
    v ∈ s.sum (fun i ↦ segment ℝ (-e[i]) e[i]) ↔
      ∀ i : Fin n, (i ∈ s → v i ∈ Set.Icc (-1 : ℝ) 1) ∧ (i ∉ s → v i = 0) := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty =>
      simp
      constructor
      · intro hv i
        simp [hv]
      · intro hv
        ext i
        exact hv i
  | @insert i s hi ih =>
      constructor
      · intro hv
        rw [Finset.sum_insert hi, Set.mem_add] at hv
        rcases hv with ⟨u, hu, w, hw, huv⟩
        rcases (mem_standard_basis_segment_iff i u).1 hu with ⟨a, ha, hua⟩
        have hw' := (ih w).1 hw
        intro j
        constructor
        · intro hj
          -- On the inserted coordinate we keep the new segment coefficient; elsewhere we inherit
          -- the box constraint from the smaller sum.
          have hcoord : v j = u j + w j := by
            simpa [Pi.add_apply] using congrArg (fun z : E ↦ z j) huv.symm
          by_cases hji : j = i
          · have hjs : j ∉ s := by simpa [hji] using hi
            have hwj : w j = 0 := (hw' j).2 hjs
            rw [hua] at hcoord
            simpa [hcoord, hwj, hji] using ha
          · have hjs : j ∈ s := by
              rw [Finset.mem_insert] at hj
              exact hj.resolve_left hji
            have hwj : w j ∈ Set.Icc (-1 : ℝ) 1 := (hw' j).1 hjs
            rw [hua] at hcoord
            simpa [hcoord, hji] using hwj
        · intro hj
          -- Off the support, both the new segment term and the inductive remainder vanish.
          have hcoord : v j = u j + w j := by
            simpa [Pi.add_apply] using congrArg (fun z : E ↦ z j) huv.symm
          have hji : j ≠ i := by
            intro hji
            apply hj
            simp [hji, hi]
          have hjs : j ∉ s := by
            intro hjs
            apply hj
            simp [hjs, hji]
          have hwj : w j = 0 := (hw' j).2 hjs
          rw [hua] at hcoord
          simpa [hcoord, hji, hwj]
      · intro hv
        rw [Finset.sum_insert hi]
        let u : E := (v i) • e[i]
        let w : E := v - u
        -- Extract the current coordinate into a single segment term.
        have hu_mem : u ∈ segment ℝ (-e[i]) e[i] := by
          refine (mem_standard_basis_segment_iff i u).2 ?_
          refine ⟨v i, (hv i).1 (by simp), ?_⟩
          dsimp [u]
        -- The remaining coordinates stay inside the smaller supported box.
        have hw_mem : w ∈ s.sum (fun i ↦ segment ℝ (-e[i]) e[i]) := by
          refine (ih w).2 ?_
          intro j
          constructor
          · intro hjs
            have hji : j ≠ i := by
              intro hji
              apply hi
              simpa [hji] using hjs
            have hwj : w j = v j := by
              dsimp [w, u]
              simp [hji]
            simpa [hwj] using (hv j).1 (by simp [hjs])
          · intro hjs
            by_cases hji : j = i
            · subst hji
              dsimp [w, u]
              simp
            · have hj_insert : j ∉ insert i s := by simp [hjs, hji]
              have hvj : v j = 0 := (hv j).2 hj_insert
              dsimp [w, u]
              simp [hji, hvj]
        refine Set.mem_add.2 ?_
        refine ⟨u, hu_mem, w, hw_mem, ?_⟩
        ext j
        by_cases hji : j = i
        · subst hji
          dsimp [w, u]
          simp
        · dsimp [w, u]
          simp [hji]

/-- Helper for Proposition 3.17: the signed translation vector has coordinate `1` on positive
entries of `x`, coordinate `-1` on negative entries, and coordinate `0` on zero entries. -/
-- Proof sketch: compute each filtered basis sum coordinate as an indicator, then subtract the
-- positive and negative indicators.
private lemma signed_basis_translation_apply (x : E) (j : Fin n) :
    (0 < x j →
      (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
          (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) j = 1) ∧
    (x j < 0 →
      (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
          (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) j = -1) ∧
    (x j = 0 →
      (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
          (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) j = 0) := by
  constructor
  · intro hj
    -- Positive coordinates contribute `+e[j]` and never `-e[j]`.
    have hcoord :
        (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
            (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) j =
          (if 0 < x j then 1 else 0) - (if x j < 0 then 1 else 0) := by
      simp [filtered_standard_basis_sum_apply]
    simpa [hcoord, hj, not_lt.mpr hj.le]
  constructor
  · intro hj
    -- Negative coordinates contribute `-e[j]` and never `+e[j]`.
    have hcoord :
        (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
            (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) j =
          (if 0 < x j then 1 else 0) - (if x j < 0 then 1 else 0) := by
      simp [filtered_standard_basis_sum_apply]
    simpa [hcoord, hj, not_lt.mpr hj.le]
  · intro hj
    -- Zero coordinates are absent from both signed sums.
    have hcoord :
        (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
            (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) j =
          (if 0 < x j then 1 else 0) - (if x j < 0 then 1 else 0) := by
      simp [filtered_standard_basis_sum_apply]
    simpa [hcoord, hj]

/-- Proposition 3.17: the subdifferential of the `ℓ₁`-norm on `ℝⁿ` consists exactly of the
vectors whose positive coordinates are `1`, whose negative coordinates are `-1`, and whose zero
coordinates lie in `[-1, 1]`. This is the coordinatewise view of
`subdifferential_l1Seminorm_eq_signedBasis_add_segmentSum`. -/
-- Proof sketch: unravel membership in the signed-basis-plus-segment description coordinate by
-- coordinate. The basis sums fix coordinates with `x i > 0` and `x i < 0`, while the segment
-- factors contribute exactly the interval condition `g i ∈ [-1, 1]` on the zero coordinates.
theorem subdifferential_l1Seminorm_eq_coordinatewise
    (x : E) :
    ∂ (fun y : E ↦ ((EuclideanSpace.l1Seminorm n) y : WithTop ℝ))(x) =
      {g | ∀ i : Fin n,
        (0 < x i → g i = 1) ∧
          (x i < 0 → g i = -1) ∧
          (x i = 0 → g i ∈ Set.Icc (-1 : ℝ) 1)} := by
  ext g
  constructor
  · intro hg
    rw [subdifferential_l1Seminorm_eq_signedBasis_add_segmentSum, Set.mem_add] at hg
    rcases hg with ⟨u, hu, w, hw, huw⟩
    rcases Set.mem_singleton_iff.1 hu with rfl
    have hw' := (mem_standard_basis_segment_sum_iff _ w).1 hw
    intro i
    constructor
    · intro hpos
      -- On positive coordinates the segment sum vanishes, so only the signed translation remains.
      have hwi : w i = 0 := (hw' i).2 (by simp [hpos.ne'])
      have hcoord : g i =
          (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
              (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) i + w i := by
        simpa [Pi.add_apply] using congrArg (fun z : E ↦ z i) huw.symm
      have htrans :
          (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
              (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) i = 1 :=
        (signed_basis_translation_apply x i).1 hpos
      simpa [hcoord, htrans, hwi]
    constructor
    · intro hneg
      -- On negative coordinates the segment sum again vanishes, leaving the `-e[i]` contribution.
      have hwi : w i = 0 := (hw' i).2 (by simp [ne_of_lt hneg])
      have hcoord : g i =
          (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
              (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) i + w i := by
        simpa [Pi.add_apply] using congrArg (fun z : E ↦ z i) huw.symm
      have htrans :
          (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
              (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) i = -1 :=
        (signed_basis_translation_apply x i).2.1 hneg
      simpa [hcoord, htrans, hwi]
    · intro hzero
      -- On zero coordinates the translation vanishes, so membership comes from the segment box.
      have hwi : w i ∈ Set.Icc (-1 : ℝ) 1 := (hw' i).1 (by simp [hzero])
      have hcoord : g i =
          (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
              (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) i + w i := by
        simpa [Pi.add_apply] using congrArg (fun z : E ↦ z i) huw.symm
      have htrans :
          (((Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
              (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])) : E) i = 0 :=
        (signed_basis_translation_apply x i).2.2 hzero
      simpa [hcoord, htrans] using hwi
  · intro hg
    rw [subdifferential_l1Seminorm_eq_signedBasis_add_segmentSum, Set.mem_add]
    let u : E :=
      (Finset.univ.filter fun i ↦ 0 < x i).sum (fun i ↦ e[i]) -
        (Finset.univ.filter fun i ↦ x i < 0).sum (fun i ↦ e[i])
    let w : E := g - u
    have hu_mem : (u : E) ∈ ({u} : Set E) := by
      simp
    have hw_mem : w ∈ (Finset.univ.filter fun i ↦ x i = 0).sum (fun i ↦ segment ℝ (-e[i]) e[i]) := by
      refine (mem_standard_basis_segment_sum_iff _ w).2 ?_
      intro i
      constructor
      · intro hi
        -- On zero coordinates the signed translation vanishes, so `w i = g i` stays in `[-1,1]`.
        have hxi : x i = 0 := by simpa using hi
        have hui : u i = 0 := (signed_basis_translation_apply x i).2.2 hxi
        have hwi : w i = g i := by
          dsimp [w]
          simp [hui]
        simpa [hwi] using (hg i).2.2 hxi
      · intro hi
        -- Off the zero set, `w i` vanishes because both `g i` and the signed translation match.
        have hxi : x i ≠ 0 := by
          intro hxi
          apply hi
          simpa [hxi]
        rcases lt_trichotomy (x i) 0 with hneg | hzero | hpos
        · have hgi : g i = -1 := (hg i).2.1 hneg
          have hui : u i = -1 := (signed_basis_translation_apply x i).2.1 hneg
          dsimp [w]
          simp [hgi, hui]
        · exfalso
          exact hxi hzero
        · have hgi : g i = 1 := (hg i).1 hpos
          have hui : u i = 1 := (signed_basis_translation_apply x i).1 hpos
          dsimp [w]
          simp [hgi, hui]
    refine ⟨u, hu_mem, w, hw_mem, ?_⟩
    -- The decomposition `g = u + w` is the canonical singleton-plus-box presentation.
    ext i
    dsimp [w]
    simp [u]

/-- At the origin, the subdifferential of the `ℓ₁`-norm is the closed `ℓ∞`-unit ball. -/
-- Proof sketch: specialize the coordinatewise description to `x = 0`. All coordinates fall in the
-- zero case, so the subdifferential becomes the set of vectors with `g i ∈ [-1, 1]` for every
-- coordinate `i`, i.e. the source-facing owner `EuclideanSpace.linftyClosedBall 1`.
theorem subdifferential_l1Seminorm_at_zero_eq_linftyClosedUnitBall :
    ∂ (fun y : E ↦ ((EuclideanSpace.l1Seminorm n) y : WithTop ℝ))((0 : E)) =
      EuclideanSpace.linftyClosedBall 1 := by
  ext g
  constructor
  · intro hg
    rw [subdifferential_l1Seminorm_eq_coordinatewise (x := (0 : E)), Set.mem_setOf_eq] at hg
    rw [mem_linftyClosedBall_iff, linftyNorm_eq_sup]
    have hsup : Finset.univ.sup (fun i : Fin n ↦ ‖g i‖₊) ≤ 1 := by
      refine Finset.sup_le_iff.2 ?_
      intro i hi
      have hgi : g i ∈ Set.Icc (-1 : ℝ) 1 := (hg i).2.2 rfl
      have habs : |g i| ≤ 1 := abs_le.2 hgi
      have hnorm : ‖g i‖ ≤ (1 : ℝ) := by
        simpa [Real.norm_eq_abs] using habs
      exact_mod_cast hnorm
    exact_mod_cast hsup
  · intro hg
    rw [subdifferential_l1Seminorm_eq_coordinatewise (x := (0 : E)), Set.mem_setOf_eq]
    intro i
    constructor
    · intro hpos
      simpa using hpos.false
    constructor
    · intro hneg
      simpa using hneg.false
    · intro _
      rw [mem_linftyClosedBall_iff, linftyNorm_eq_sup] at hg
      have hg' : Finset.univ.sup (fun j : Fin n ↦ ‖g j‖₊) ≤ 1 := by
        exact_mod_cast hg
      have hcoord : ‖g i‖₊ ≤ Finset.univ.sup (fun j : Fin n ↦ ‖g j‖₊) := by
        exact Finset.le_sup (s := Finset.univ) (f := fun j : Fin n ↦ ‖g j‖₊) (by simp)
      have hle : ‖g i‖₊ ≤ 1 := le_trans hcoord hg'
      have hnorm : ‖g i‖ ≤ (1 : ℝ) := by
        exact_mod_cast hle
      have habs : |g i| ≤ 1 := by
        simpa [Real.norm_eq_abs] using hnorm
      exact abs_le.1 habs

end

/-! ### Theorem_3_17 (from Chap03) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped ConvexAnalysis SupportFunction

/- Theorem 3.17 lies in the chapter's support-function comparison domain.

Primary domain:
- support functions of closed convex subsets of a real Hilbert space.

Relevant sampled owner declarations:
- `supportFunction` in `Definition_3_9`, the chapter owner for `ξ[Q]`;
- `extendedRealEffectiveDomain` / `dom` in `Definition_3_1_1_2`, the owner of the finite-value
  domain of an `EReal`-valued function;
- `supportFunction_apply` in `Definition_3_9`, the evaluation bridge for `ξ[Q]`;
- mathlib `geometric_hahn_banach_closed_point`, the strict point-versus-closed-convex separation
  theorem whose dual functional is converted to a vector normal by Riesz representation.

Best owner abstraction:
- the pair `ξ[Q]` and `dom ξ[Q]`.

Primitive data:
- the sets `Q₁`, `Q₂`.

Derived API:
- the support-function comparison theorem `subset_of_supportFunction_le_on_domain`;
- the equality criterion `supportFunction_eq_on_common_domain_implies_eq`.

Source/core/bridge triage:
- source-facing: the textbook comparison and equality criteria for closed convex sets via support
  functions;
- core/canonical: the owner constructions `supportFunction` and `dom`;
- bridge/view: these two theorems, which express the source comparison statements directly in that
  owner language instead of introducing a parallel local wrapper.

The textbook states these results on `ℝⁿ`. The comparison theorems themselves still live directly
on the owner pair `ξ[Q]`, `dom ξ[Q]`, but their intrinsic ambient layer is a real Hilbert space:
the proof needs a separating continuous linear functional to be represented by a vector normal in
the same space. This completeness requirement is therefore mathematical owner data here, not mere
proof scaffolding. -/

/-- Theorem 3.17 (1): if `Q₂` is a nonempty closed convex subset of a real Hilbert space and
the support function of `Q₁` is bounded above by that of `Q₂` at every vector in `dom ξ[Q₂]`,
then `Q₁ ⊆ Q₂`. -/
-- Proof sketch: if `Q₁ = ∅`, the conclusion is immediate. Otherwise argue by contradiction. For
-- `x₀ ∈ Q₁ \\ Q₂`, use the separation theorem for the point `x₀` and the nonempty closed convex
-- set `Q₂` to produce a vector `g` with `supportFunction Q₂ g` finite and
-- `supportFunction Q₂ g < supportFunction Q₁ g`, contradicting the assumed pointwise inequality
-- on `dom ξ[Q₂]`.
theorem subset_of_supportFunction_le_on_domain
    (Q₁ Q₂ : Set E) (hQ₂_nonempty : Q₂.Nonempty)
    (hQ₂_closed : IsClosed Q₂) (hQ₂_convex : Convex ℝ Q₂)
    (hξ : ∀ g ∈ dom ξ[Q₂], ξ[Q₁] g ≤ ξ[Q₂] g) :
    Q₁ ⊆ Q₂ := by
  intro x hxQ₁
  by_contra hxQ₂
  obtain ⟨f, u, hQ₂_lt, hux⟩ :=
    geometric_hahn_banach_closed_point hQ₂_convex hQ₂_closed hxQ₂
  let g : E := (InnerProductSpace.toDual ℝ E).symm f
  have hQ₂_lt' : ∀ y ∈ Q₂, inner ℝ y g < u := by
    intro y hy
    have : inner ℝ g y < u := by
      simpa [g] using hQ₂_lt y hy
    simpa [real_inner_comm] using this
  have hux' : u < inner ℝ x g := by
    have : u < inner ℝ g x := by
      simpa [g] using hux
    simpa [real_inner_comm] using this
  have hξQ₂_le : ξ[Q₂] g ≤ (u : EReal) := by
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    change ((inner ℝ y g : ℝ) : EReal) ≤ (u : EReal)
    exact_mod_cast (hQ₂_lt' y hy).le
  have hg_dom : g ∈ dom ξ[Q₂] := by
    rw [mem_extendedRealEffectiveDomain_iff]
    constructor
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top u) hξQ₂_le
    · intro hbot
      rcases hQ₂_nonempty with ⟨y, hy⟩
      have hy_le : ((inner ℝ y g : ℝ) : EReal) ≤ ξ[Q₂] g := by
        rw [supportFunction_apply]
        exact le_sSup ⟨y, hy, rfl⟩
      have hy_le_bot : ((inner ℝ y g : ℝ) : EReal) ≤ (⊥ : EReal) := by
        rw [hbot] at hy_le
        exact hy_le
      exact (not_le_of_gt (EReal.bot_lt_coe _)) hy_le_bot
  have hu_lt : (u : EReal) < ξ[Q₁] g := by
    have hx_le : ((inner ℝ x g : ℝ) : EReal) ≤ ξ[Q₁] g := by
      rw [supportFunction_apply]
      exact le_sSup ⟨x, hxQ₁, rfl⟩
    have huxE : (u : EReal) < ((inner ℝ x g : ℝ) : EReal) := by
      exact_mod_cast hux'
    exact huxE.trans_le hx_le
  exact (not_le_of_gt hu_lt) ((hξ g hg_dom).trans hξQ₂_le)

/-- Theorem 3.17 (2): if two closed convex sets in a real Hilbert space have the same
effective domain for their support functions and those support functions agree on that common
domain, then the sets are equal. -/
-- Proof sketch: equality of effective domains rules out the mixed empty/nonempty case for `Q₁`
-- and `Q₂`. If both sets are empty, the conclusion is immediate. Otherwise the common domain is
-- nonempty, so both sets are nonempty; apply `subset_of_supportFunction_le_on_domain` in both
-- directions. The domain equality transports the equality hypothesis from one set to the other,
-- giving both inclusions and hence equality.
theorem supportFunction_eq_on_common_domain_implies_eq
    (Q₁ Q₂ : Set E) (hQ₁_closed : IsClosed Q₁) (hQ₂_closed : IsClosed Q₂)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₂_convex : Convex ℝ Q₂)
    (hdom : dom ξ[Q₁] = dom ξ[Q₂])
    (hξ : Set.EqOn ξ[Q₁] ξ[Q₂] (dom ξ[Q₁])) :
    Q₁ = Q₂ := by
  have hdom_empty : dom ξ[(∅ : Set E)] = (∅ : Set E) := by
    ext g
    rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
    simp
  by_cases hQ₁_nonempty : Q₁.Nonempty
  · have hQ₂_nonempty : Q₂.Nonempty := by
      by_contra hQ₂_nonempty
      have hQ₂_empty : Q₂ = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ₂_nonempty
      have hzero_mem : (0 : E) ∈ dom ξ[Q₁] := by
        rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
        constructor <;> simp [hQ₁_nonempty]
      have : (0 : E) ∈ dom ξ[Q₂] := by
        simpa [hdom] using hzero_mem
      simp [hQ₂_empty] at this
    apply Set.Subset.antisymm
    · exact
        subset_of_supportFunction_le_on_domain Q₁ Q₂ hQ₂_nonempty hQ₂_closed hQ₂_convex
          fun g hg ↦ by
            have hg' : g ∈ dom ξ[Q₁] := by
              simpa [hdom] using hg
            exact (hξ hg').le
    · exact
        subset_of_supportFunction_le_on_domain Q₂ Q₁ hQ₁_nonempty hQ₁_closed hQ₁_convex
          fun g hg ↦ (hξ hg).symm.le
  · have hQ₁_empty : Q₁ = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ₁_nonempty
    have hQ₂_empty : Q₂ = ∅ := by
      by_cases hQ₂_nonempty : Q₂.Nonempty
      · have hdomQ₂_empty : dom ξ[Q₂] = (∅ : Set E) := by
          calc
            dom ξ[Q₂] = dom ξ[Q₁] := hdom.symm
            _ = dom ξ[(∅ : Set E)] := by simp [hQ₁_empty]
            _ = ∅ := hdom_empty
        have hzero_mem : (0 : E) ∈ dom ξ[Q₂] := by
          rw [mem_extendedRealEffectiveDomain_iff, supportFunction_apply]
          constructor <;> simp [hQ₂_nonempty]
        simp [hdomQ₂_empty] at hzero_mem
      · exact Set.not_nonempty_iff_eq_empty.mp hQ₂_nonempty
    simp [hQ₁_empty, hQ₂_empty]

end
