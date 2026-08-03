import Mathlib
import BauschkeLean.Chap12.Definition_12_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace ERealFunction

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E]
variable {p : ENNReal}

/-- The latent group lasso decomposition space consists of families whose `k`-th component is
supported in the coordinate group `groups k`. -/
def latentGroupLassoDecompositionSpace (E : Type*) [NormedAddCommGroup E] (p : ENNReal)
    (groups : κ → Set ι) :=
  {x : κ → PiLp p (fun _ : ι ↦ E) // ∀ k, Function.support (x k) ⊆ groups k}

namespace latentGroupLassoDecompositionSpace

/-- The latent group lasso synthesis map sends an admissible family `(x_k)` to the sum
`∑ k, x_k`. -/
noncomputable def synthesis (E : Type*) [NormedAddCommGroup E] (p : ENNReal)
    (groups : κ → Set ι) : latentGroupLassoDecompositionSpace E p groups → PiLp p (fun _ : ι ↦ E) :=
  fun x ↦ ∑ k, x.1 k

end latentGroupLassoDecompositionSpace

open latentGroupLassoDecompositionSpace

/- The primitive decomposition space and synthesis map make sense for every `p : ENNReal`. The
source-facing penalties of Example 12.35 use the textbook `ℓ^p` regime `1 ≤ p < ∞`. -/

/-- The textbook exponent range for Example 12.35: `1 ≤ p < ∞`. -/
abbrev TextbookExponent := Subtype fun p : ENNReal ↦ 1 ≤ p ∧ p ≠ ⊤

namespace latentGroupLassoDecompositionSpace

/-- The latent group lasso decomposition cost is the sum of the `p`-norms of the components of an
admissible decomposition, in the textbook exponent range `1 ≤ p < ∞`. -/
noncomputable def cost (E : Type*) [NormedAddCommGroup E]
    (p : TextbookExponent) (groups : κ → Set ι) :
    latentGroupLassoDecompositionSpace E p.1 groups → ℝ :=
  fun x ↦ ∑ k, ‖x.1 k‖

end latentGroupLassoDecompositionSpace

/-- Example 12 35: on a finite coordinate `ℓ^p` space with `1 ≤ p < ∞`, the latent group lasso
penalty is the infimal postcomposition of the source-facing real-valued cost
`x ↦ ∑ k, ‖x_k‖_p` by the synthesis map `(x_k) ↦ ∑ k, x_k`. The textbook `ℝ^N` case is
recovered by taking `ι = Fin N` and `E = ℝ`. The nonemptiness and covering hypotheses on the
groups enter later analytic properties, not this defining infimal-postcomposition construction. -/
noncomputable def latentGroupLassoPenalty
    (p : TextbookExponent)
    (groups : κ → Set ι) : PiLp p.1 (fun _ : ι ↦ E) → EReal :=
  synthesis E p.1 groups ▷ (cost E p groups).toEReal

/- Example 12.35: the textbook latent group lasso penalty `‖·‖_{gl}` with parameters `p` and
`groups` is written `‖y‖_gl[p,groups]`. -/
notation "‖" y "‖_gl[" p "," groups "]" => latentGroupLassoPenalty p groups y

/-- Evaluating the latent group lasso penalty at `y` gives the infimum of the sums of the
component norms over all admissible decompositions whose synthesis is `y`. -/
theorem latentGroupLassoPenalty_apply
    (p : TextbookExponent)
    (groups : κ → Set ι) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    ‖y‖_gl[p,groups] =
      sInf ((cost E p groups).toEReal.asEReal '' (synthesis E p.1 groups ⁻¹' {y})) := by
  simpa [latentGroupLassoPenalty] using
    infimalPostcomposition_apply (synthesis E p.1 groups) (cost E p groups).toEReal y

/-- The `k`-th block of `y` supported on `groups k`, obtained by zeroing out the other
coordinates. -/
noncomputable def groupLassoBlock
    (p : TextbookExponent) (groups : κ → Set ι)
    (k : κ) : PiLp p.1 (fun _ : ι ↦ E) → PiLp p.1 (fun _ : ι ↦ E) :=
  fun y ↦
    let _ : DecidablePred fun i : ι ↦ i ∈ groups k := Classical.decPred _
    WithLp.toLp p.1 ((groups k).indicator y)

/-- The blockwise sum of `p`-norms associated with the family `groups`; when the groups are
pairwise disjoint, this is the ordinary group lasso penalty. -/
noncomputable def groupLassoPenalty
    (p : TextbookExponent) (groups : κ → Set ι) :
    PiLp p.1 (fun _ : ι ↦ E) → ℝ :=
  fun y ↦ ∑ k, ‖groupLassoBlock p groups k y‖

section

variable {ι κ : Type*}
variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for Example 12 35: the `k`-th block agrees with `y` on the coordinates belonging to
`groups k`. -/
private lemma groupLassoBlock_apply_of_mem
    (p : TextbookExponent) (groups : κ → Set ι)
    (k : κ) (y : PiLp p.1 (fun _ : ι ↦ E)) {i : ι} (hi : i ∈ groups k) :
    groupLassoBlock p groups k y i = y i := by
  classical
  -- Unfold the block and evaluate the indicator on the in-group branch.
  simp [groupLassoBlock, hi]

/-- Helper for Example 12 35: the `k`-th block vanishes outside `groups k`. -/
private lemma groupLassoBlock_apply_of_not_mem
    (p : TextbookExponent) (groups : κ → Set ι)
    (k : κ) (y : PiLp p.1 (fun _ : ι ↦ E)) {i : ι} (hi : i ∉ groups k) :
    groupLassoBlock p groups k y i = 0 := by
  classical
  -- Unfold the block and evaluate the indicator on the out-of-group branch.
  simp [groupLassoBlock, hi]

/-- Helper for Example 12 35: each canonical block is supported in its designated coordinate
group. -/
private lemma groupLassoBlock_support_subset
    (p : TextbookExponent) (groups : κ → Set ι)
    (k : κ) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    Function.support (groupLassoBlock p groups k y) ⊆ groups k := by
  classical
  -- Outside `groups k`, the block is identically zero, so those coordinates leave the support.
  refine Function.support_subset_iff'.2 ?_
  intro i hi
  exact groupLassoBlock_apply_of_not_mem p groups k y hi

/-- Helper for Example 12 35: the family of canonical blocks is an admissible latent
decomposition. -/
private lemma canonical_groupLassoDecomposition_property
    (p : TextbookExponent) (groups : κ → Set ι)
    (y : PiLp p.1 (fun _ : ι ↦ E)) :
    ∀ k, Function.support (groupLassoBlock p groups k y) ⊆ groups k := by
  -- The admissibility condition is exactly the support statement for each block.
  intro k
  exact groupLassoBlock_support_subset p groups k y

/-- Helper for Example 12 35: the canonical block truncations assemble into a latent group lasso
decomposition. -/
private noncomputable def canonicalGroupLassoDecomposition
    (p : TextbookExponent) (groups : κ → Set ι)
    (y : PiLp p.1 (fun _ : ι ↦ E)) :
    latentGroupLassoDecompositionSpace E p.1 groups :=
  ⟨fun k ↦ groupLassoBlock p groups k y, canonical_groupLassoDecomposition_property p groups y⟩

/-- Helper for Example 12 35: a supported decomposition component vanishes outside its coordinate
group. -/
private lemma decomposition_component_eq_zero_of_not_mem
    (p : TextbookExponent) (groups : κ → Set ι)
    {x : latentGroupLassoDecompositionSpace E p.1 groups}
    (k : κ) {i : ι} (hi : i ∉ groups k) :
    x.1 k i = 0 := by
  -- Convert the support inclusion from the subtype field into a pointwise vanishing statement.
  exact Function.support_subset_iff'.1 (x.2 k) i hi

end

section

variable {ι κ : Type*} [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for Example 12 35: under the disjoint cover hypotheses, the canonical block
decomposition synthesizes back to `y`. -/
private lemma synthesis_groupLassoBlock_eq
    (p : TextbookExponent) (groups : κ → Set ι)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (groups i) (groups j))
    (hcover : (⋃ k, groups k) = Set.univ) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    synthesis E p.1 groups (canonicalGroupLassoDecomposition (E := E) p groups y) = y := by
  classical
  ext i
  have hiUnion : i ∈ ⋃ k, groups k := by
    simp [hcover]
  rcases Set.mem_iUnion.1 hiUnion with ⟨k, hk⟩
  -- Collapse the blockwise sum to the unique group containing `i`.
  calc
    synthesis E p.1 groups (canonicalGroupLassoDecomposition (E := E) p groups y) i
        = ∑ j, groupLassoBlock p groups j y i := by
          simp [canonicalGroupLassoDecomposition, latentGroupLassoDecompositionSpace.synthesis]
    _ = groupLassoBlock p groups k y i := by
      rw [Fintype.sum_eq_single k]
      intro j hj
      have hij : i ∉ groups j := by
        intro hij
        exact (Set.disjoint_left.1 (hdisjoint hj)) hij hk
      exact groupLassoBlock_apply_of_not_mem p groups j y hij
    _ = y i := groupLassoBlock_apply_of_mem p groups k y hk

/-- Helper for Example 12 35: the canonical block decomposition lies in the synthesis fiber over
`y`. -/
private lemma canonicalGroupLassoDecomposition_mem_fiber
    (p : TextbookExponent) (groups : κ → Set ι)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (groups i) (groups j))
    (hcover : (⋃ k, groups k) = Set.univ) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    canonicalGroupLassoDecomposition (E := E) p groups y ∈
      synthesis E p.1 groups ⁻¹' {y} := by
  -- Membership in the fiber is exactly the synthesized equality.
  simp [synthesis_groupLassoBlock_eq, hdisjoint, hcover]

/-- Helper for Example 12 35: every decomposition in the synthesis fiber agrees with the canonical
block truncation coordinatewise. -/
private lemma eq_groupLassoBlock_of_mem_fiber
    (p : TextbookExponent) (groups : κ → Set ι)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (groups i) (groups j))
    {y : PiLp p.1 (fun _ : ι ↦ E)}
    {x : latentGroupLassoDecompositionSpace E p.1 groups}
    (hx : x ∈ synthesis E p.1 groups ⁻¹' {y}) (k : κ) :
    x.1 k = groupLassoBlock p groups k y := by
  classical
  have hsynth : synthesis E p.1 groups x = y := by
    simpa using hx
  ext i
  by_cases hi : i ∈ groups k
  · -- On `groups k`, all other components vanish, so the synthesis identity isolates component `k`.
    have hsum :
        ∑ j, x.1 j i = y i := by
      simpa [latentGroupLassoDecompositionSpace.synthesis] using congrArg (fun z ↦ z i) hsynth
    rw [Fintype.sum_eq_single k] at hsum
    · calc
        x.1 k i = y i := hsum
        _ = groupLassoBlock p groups k y i := (groupLassoBlock_apply_of_mem p groups k y hi).symm
    · intro j hj
      have hij : i ∉ groups j := by
        intro hij
        exact (Set.disjoint_left.1 (hdisjoint hj.symm)) hi hij
      exact decomposition_component_eq_zero_of_not_mem p groups j hij
  · -- Outside `groups k`, both the admissible component and the canonical block are zero.
    rw [decomposition_component_eq_zero_of_not_mem p groups k hi]
    exact (groupLassoBlock_apply_of_not_mem p groups k y hi).symm

end

/-- Helper for Example 12 35: every point of the synthesis fiber has the same decomposition cost,
namely the ordinary group lasso value. -/
private lemma cost_eq_groupLassoPenalty_of_mem_fiber
    (p : TextbookExponent) (groups : κ → Set ι)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (groups i) (groups j))
    {y : PiLp p.1 (fun _ : ι ↦ E)}
    {x : latentGroupLassoDecompositionSpace E p.1 groups}
    (hx : x ∈ synthesis E p.1 groups ⁻¹' {y}) :
    cost E p groups x = groupLassoPenalty p groups y := by
  -- Replace each admissible component by the canonical block determined by the fiber identity.
  unfold latentGroupLassoDecompositionSpace.cost groupLassoPenalty
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [eq_groupLassoBlock_of_mem_fiber p groups hdisjoint hx k]

/-- If the coordinate groups are pairwise disjoint and cover all coordinates, then the latent group
lasso penalty reduces to the ordinary group lasso penalty. -/
theorem latentGroupLassoPenalty_eq_groupLassoPenalty_of_pairwiseDisjoint
    (p : TextbookExponent) (groups : κ → Set ι)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (groups i) (groups j))
    (hcover : (⋃ k, groups k) = Set.univ) (y : PiLp p.1 (fun _ : ι ↦ E)) :
    ‖y‖_gl[p,groups] = (groupLassoPenalty p groups y : ℝ) :=
  by
    let fiber := synthesis E p.1 groups ⁻¹' {y}
    have hz :
        canonicalGroupLassoDecomposition (E := E) p groups y ∈ fiber := by
      -- The canonical decomposition belongs to the fiber because its synthesis is exactly `y`.
      simpa [fiber] using
        canonicalGroupLassoDecomposition_mem_fiber (E := E) p groups hdisjoint hcover y
    have himage :
        (fun x : latentGroupLassoDecompositionSpace E p.1 groups ↦
          ((cost E p groups x : ℝ) : EReal)) '' fiber =
          {((groupLassoPenalty p groups y : ℝ) : EReal)} := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        -- Every fiber point has the same cost, so the image collapses to a singleton.
        have hcost :
            cost E p groups x = groupLassoPenalty p groups y :=
          cost_eq_groupLassoPenalty_of_mem_fiber p groups hdisjoint hx
        simp [hcost]
      · intro ha
        -- The canonical decomposition realizes that singleton value on the fiber.
        refine ⟨canonicalGroupLassoDecomposition (E := E) p groups y, hz, ?_⟩
        have hcost :
            cost E p groups (canonicalGroupLassoDecomposition (E := E) p groups y) =
              groupLassoPenalty p groups y :=
          cost_eq_groupLassoPenalty_of_mem_fiber p groups hdisjoint hz
        simpa [hcost] using ha.symm
    -- Rewrite the infimal postcomposition as the infimum of a singleton image.
    calc
      ‖y‖_gl[p,groups]
          = sInf (((fun x : latentGroupLassoDecompositionSpace E p.1 groups ↦
                ((cost E p groups x : ℝ) : EReal)) '' fiber)) := by
              simpa [fiber, Function.asEReal_apply, Function.toEReal_apply] using
                latentGroupLassoPenalty_apply (E := E) p groups y
      _ = ((groupLassoPenalty p groups y : ℝ) : EReal) := by
        rw [himage]
        simp

end ERealFunction
