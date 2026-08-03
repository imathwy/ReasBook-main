import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix

-- Semantic recall note: this file keeps the source-facing mixed-space split owners from
-- Theorem 5.10, while exposing them as thin bridges to the canonical Chapter 5 split-hull owner
-- on the flattened ambient space `ℝ^(nI + nC)`.

section Theorem510

variable {nI nC : ℕ}

/-- The mixed split hull `P^(π, π₀)` is the convex hull of the two split branches cut out by the
integer-block split data `(π, π₀)` on `P ⊆ ℝ^I × ℝ^C`. -/
def mixed_split_hull
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) : Set (MixedRealPoint nI nC) :=
  convexHull ℝ
    ({xy : MixedRealPoint nI nC |
        xy ∈ P ∧ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1 ≤ (π0 : ℝ)} ∪
      {xy : MixedRealPoint nI nC |
        xy ∈ P ∧ (π0 : ℝ) + 1 ≤ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1})

private lemma isLinearMap_appendEquiv :
    IsLinearMap ℝ
      (Fin.appendEquiv nI nC : MixedRealPoint nI nC → Fin (nI + nC) → ℝ) := by
  refine ⟨?_, ?_⟩
  · intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

private lemma appendEquiv_image_convexHull
    (S : Set (MixedRealPoint nI nC)) :
    (Fin.appendEquiv nI nC : MixedRealPoint nI nC → Fin (nI + nC) → ℝ) '' convexHull ℝ S =
      convexHull ℝ
        ((Fin.appendEquiv nI nC : MixedRealPoint nI nC → Fin (nI + nC) → ℝ) '' S) := by
  simpa using isLinearMap_appendEquiv.image_convexHull S

private theorem appendEquiv_image_mixed_split_branch_lower
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    Fin.appendEquiv nI nC ''
        {xy : MixedRealPoint nI nC |
          xy ∈ P ∧ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1 ≤ (π0 : ℝ)} =
      split_branch_lower
        (Fin.appendEquiv nI nC '' P)
        (Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))) π0 := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    refine (mem_split_branch_lower_iff).2 ?_
    refine ⟨⟨xy, hxy.1, rfl⟩, ?_⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using hxy.2
  · intro hu
    rcases (mem_split_branch_lower_iff).1 hu with ⟨huP, huπ⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    refine ⟨xy, ⟨hxyP, ?_⟩, rfl⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using huπ

private theorem appendEquiv_image_mixed_split_branch_upper
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    Fin.appendEquiv nI nC ''
        {xy : MixedRealPoint nI nC |
          xy ∈ P ∧ (π0 : ℝ) + 1 ≤ (fun i : Fin nI ↦ (π i : ℝ)) ⬝ᵥ xy.1} =
      split_branch_upper
        (Fin.appendEquiv nI nC '' P)
        (Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))) π0 := by
  ext u
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    refine (mem_split_branch_upper_iff).2 ?_
    refine ⟨⟨xy, hxy.1, rfl⟩, ?_⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using hxy.2
  · intro hu
    rcases (mem_split_branch_upper_iff).1 hu with ⟨huP, huπ⟩
    rcases huP with ⟨xy, hxyP, rfl⟩
    refine ⟨xy, ⟨hxyP, ?_⟩, rfl⟩
    simpa [split_dot, dotProduct, Fin.sum_univ_add] using huπ

/-- Flattening by `Fin.appendEquiv` turns the mixed split hull into the canonical Chapter 5 split
hull cut out by the supported coefficient vector `Fin.append π 0` on `ℝ^(nI + nC)`. -/
theorem appendEquiv_image_mixed_split_hull
    (P : Set (MixedRealPoint nI nC))
    (π : Fin nI → ℤ)
    (π0 : ℤ) :
    Fin.appendEquiv nI nC '' mixed_split_hull P π π0 =
      split_hull
        (Fin.appendEquiv nI nC '' P)
        (Fin.append π (fun _ : Fin nC ↦ (0 : ℤ))) π0 := by
  rw [mixed_split_hull, split_hull, appendEquiv_image_convexHull, Set.image_union,
    appendEquiv_image_mixed_split_branch_lower, appendEquiv_image_mixed_split_branch_upper]

/-- The mixed split closure `P^split` is the intersection of `P^(π, π₀)` over all nonzero
integral split vectors on the integer block and all integral right-hand sides. -/
def mixed_split_closure
    (P : Set (MixedRealPoint nI nC)) : Set (MixedRealPoint nI nC) :=
  ⋂ π : {π : Fin nI → ℤ // π ≠ 0}, ⋂ π0 : ℤ, mixed_split_hull P π.1 π0

/-- Membership in `mixed_split_closure P` means belonging to every mixed split hull
`P^(π, π₀)` defined by nonzero integral split data on the integer block. -/
theorem mem_mixed_split_closure_iff
    (P : Set (MixedRealPoint nI nC))
    (xy : MixedRealPoint nI nC) :
    xy ∈ mixed_split_closure P ↔
      ∀ π : {π : Fin nI → ℤ // π ≠ 0}, ∀ π0 : ℤ, xy ∈ mixed_split_hull P π.1 π0 := by
  simp [mixed_split_closure]

/-- Theorem 5.10 (Cook et al. [90]). Let `P ⊆ ℝ^I × ℝ^C` be a rational polyhedron and let
`S := P ∩ (ℤ^I × ℝ^C)`. Then the mixed split closure `P^split` is a rational polyhedron. -/
theorem mixed_split_closure_is_rational_mixed_polyhedron
    (P : Set (MixedRealPoint nI nC))
    (hP : is_rational_mixed_polyhedron P) :
    is_rational_mixed_polyhedron (mixed_split_closure P) := sorry

end Theorem510
