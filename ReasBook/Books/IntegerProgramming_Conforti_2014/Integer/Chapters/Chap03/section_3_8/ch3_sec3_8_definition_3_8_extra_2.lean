import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped BigOperators Matrix

/-- The strong-dual functional associated with a coefficient vector is the corresponding coordinate
dot product. -/
noncomputable def dotProductStrongDual {n : ℕ} (c : Fin n → ℝ) :
    StrongDual ℝ (Fin n → ℝ) :=
  ∑ i, c i • ContinuousLinearMap.proj i

/-- `dotProductStrongDual c` evaluates as `c ⬝ᵥ x`. -/
lemma dotProductStrongDual_apply {n : ℕ} (c x : Fin n → ℝ) :
    dotProductStrongDual c x = c ⬝ᵥ x := by
  simp [dotProductStrongDual, dotProduct]

/-- Every strong-dual functional on `Fin n → ℝ` is represented by a dot product with some
coefficient vector. -/
lemma strongDual_eq_dotProduct_fin {n : ℕ} (l : StrongDual ℝ (Fin n → ℝ)) :
    ∃ c : Fin n → ℝ, ∀ x : Fin n → ℝ, l x = c ⬝ᵥ x := by
  let c : Fin n → ℝ := fun i ↦ l (Pi.single i 1)
  refine ⟨c, ?_⟩
  intro x
  have hx : x = ∑ i, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  calc
    l x = l (∑ i, x i • Pi.single i 1) := congrArg l hx
    _ = ∑ i, l (x i • Pi.single i 1) := by rw [map_sum]
    _ = ∑ i, x i * l (Pi.single i 1) := by simp
    _ = ∑ i, l (Pi.single i 1) * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_comm]
    _ = c ⬝ᵥ x := by
      simp [c, dotProduct]

/-- The hyperplane cut out by the equation `c ⬝ᵥ x = δ`. -/
def linear_hyperplane {n : ℕ} (c : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {x | c ⬝ᵥ x = δ}

/-- Membership in `linear_hyperplane c δ` is the equation `c ⬝ᵥ x = δ`. -/
theorem mem_linear_hyperplane_iff {n : ℕ} {c x : Fin n → ℝ} {δ : ℝ} :
    x ∈ linear_hyperplane c δ ↔ c ⬝ᵥ x = δ := by
  rfl

/-- The set cut out from `P` by the equality case of the inequality `c ⬝ᵥ x ≤ δ`. -/
def face_set {n : ℕ} (P : Set (Fin n → ℝ)) (c : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  P ∩ linear_hyperplane c δ

/-- Membership in `face_set P c δ` means lying in `P` and satisfying `c ⬝ᵥ x = δ`. -/
theorem mem_face_set_iff {n : ℕ} {P : Set (Fin n → ℝ)} {c x : Fin n → ℝ} {δ : ℝ} :
    x ∈ face_set P c δ ↔ x ∈ P ∧ c ⬝ᵥ x = δ := by
  simp [face_set, linear_hyperplane]

/-- If the valid inequality `c ⬝ᵥ x ≤ δ` is attained at some point of `P`, then its equality set on
`P` is the maximizer set of the corresponding strong-dual functional. -/
lemma face_set_eq_toExposed_of_mem {n : ℕ} {P : Set (Fin n → ℝ)} {c x₀ : Fin n → ℝ} {δ : ℝ}
    (h_valid : is_valid_inequality P c δ) (hx₀ : x₀ ∈ face_set P c δ) :
    face_set P c δ = (dotProductStrongDual c).toExposed P := by
  have hx₀P : x₀ ∈ P := (mem_face_set_iff.1 hx₀).1
  have hx₀_eq : dotProductStrongDual c x₀ = δ := by
    simpa [dotProductStrongDual_apply] using (mem_face_set_iff.1 hx₀).2
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, fun y hyP ↦ ?_⟩
    calc
      dotProductStrongDual c y = c ⬝ᵥ y := dotProductStrongDual_apply c y
      _ ≤ δ := h_valid hyP
      _ = dotProductStrongDual c x := by
        simpa [dotProductStrongDual_apply] using hxEq.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hx₀_le : dotProductStrongDual c x₀ ≤ dotProductStrongDual c x := hx.2 x₀ hx₀P
    have hx_le : dotProductStrongDual c x ≤ dotProductStrongDual c x₀ := by
      simpa [dotProductStrongDual_apply, hx₀_eq] using h_valid hx.1
    have hx_eq : dotProductStrongDual c x = dotProductStrongDual c x₀ :=
      le_antisymm hx_le hx₀_le
    simpa [dotProductStrongDual_apply, hx₀_eq] using hx_eq

/- Helper lemmas for the exposed-face characterization. -/

/-- Helper for Definition 3.8-extra-2: if a strong-dual functional is represented by the dot
product with `c` and attains its maximum at `x₀`, then its exposed set is the equality face cut out
by `c ⬝ᵥ x = c ⬝ᵥ x₀`. -/
lemma toExposed_eq_face_set_of_mem {n : ℕ} {P : Set (Fin n → ℝ)} {l : StrongDual ℝ (Fin n → ℝ)}
    {c x₀ : Fin n → ℝ} (hrep : ∀ x : Fin n → ℝ, l x = c ⬝ᵥ x) (hx₀ : x₀ ∈ l.toExposed P) :
    l.toExposed P = face_set P c (c ⬝ᵥ x₀) := by
  -- First record the valid inequality coming from maximality of `x₀`.
  have h_valid : is_valid_inequality P c (c ⬝ᵥ x₀) := by
    intro x hxP
    calc
      c ⬝ᵥ x = l x := by rw [hrep x]
      _ ≤ l x₀ := hx₀.2 x hxP
      _ = c ⬝ᵥ x₀ := hrep x₀
  -- Then identify the equality slice with the maximizer set of the dot-product functional.
  have hx₀_face : x₀ ∈ face_set P c (c ⬝ᵥ x₀) := by
    exact (mem_face_set_iff).2 ⟨hx₀.1, rfl⟩
  have hl : l = dotProductStrongDual c := by
    ext x
    rw [hrep x, dotProductStrongDual_apply]
  calc
    l.toExposed P = (dotProductStrongDual c).toExposed P := by rw [hl]
    _ = face_set P c (c ⬝ᵥ x₀) := by
      symm
      exact face_set_eq_toExposed_of_mem h_valid hx₀_face

namespace IsExposed

/-- Helper for Definition 3.8-extra-2: a nonempty exposed subset of `P` is the equality face of one
valid inequality. -/
lemma exists_eq_face_set_of_nonempty {n : ℕ} {P F : Set (Fin n → ℝ)}
    (hF_face : IsExposed ℝ P F) (hF_nonempty : F.Nonempty) :
    ∃ c : Fin n → ℝ, ∃ δ : ℝ, is_valid_inequality P c δ ∧ F = face_set P c δ := by
  obtain ⟨x₀, hx₀F⟩ := hF_nonempty
  obtain ⟨l, rfl⟩ := hF_face ⟨x₀, hx₀F⟩
  -- Translate the exposing functional into coordinate dot-product form.
  obtain ⟨c, hc⟩ := strongDual_eq_dotProduct_fin l
  refine ⟨c, c ⬝ᵥ x₀, ?_, ?_⟩
  · -- Maximality of `x₀` turns the representation into a valid inequality on `P`.
    intro x hxP
    calc
      c ⬝ᵥ x = l x := by rw [← hc x]
      _ ≤ l x₀ := hx₀F.2 x hxP
      _ = c ⬝ᵥ x₀ := hc x₀
  · -- The exposed set is exactly the equality slice where the maximum is attained.
    exact toExposed_eq_face_set_of_mem hc hx₀F

end IsExposed

/-- Helper for Definition 3.8-extra-2: every equality face cut out by a valid inequality is
exposed. -/
lemma isExposed_face_set_of_valid_inequality {n : ℕ} {P : Set (Fin n → ℝ)} {c : Fin n → ℝ}
    {δ : ℝ} (h_valid : is_valid_inequality P c δ) :
    IsExposed ℝ P (face_set P c δ) := by
  by_cases h_face_nonempty : (face_set P c δ).Nonempty
  · obtain ⟨x₀, hx₀_face⟩ := h_face_nonempty
    -- A nonempty equality face is the maximizer set of the defining functional.
    rw [face_set_eq_toExposed_of_mem h_valid hx₀_face]
    exact ContinuousLinearMap.toExposed.isExposed
  · -- If the equality face is empty, it is exposed by convention.
    rw [Set.not_nonempty_iff_eq_empty.mp h_face_nonempty]
    exact isExposed_empty

/- Definition 3.8-extra-2 (1). Faces of `P` are expressed by mathlib's canonical exposed-set owner
`IsExposed ℝ P`. -/

/-- Definition 3.8-extra-2. On `Fin n → ℝ`, an exposed face is exactly either `∅` or the equality
set on `P` of a valid inequality `c ⬝ᵥ x ≤ δ`. -/
theorem isExposed_iff_eq_empty_or_eq_face_set {n : ℕ} {P F : Set (Fin n → ℝ)} :
    IsExposed ℝ P F ↔
      F = ∅ ∨ ∃ c : Fin n → ℝ, ∃ δ : ℝ, is_valid_inequality P c δ ∧ F = face_set P c δ := by
  constructor
  · intro hF
    by_cases hF_nonempty : F.Nonempty
    · -- In the nonempty case, unpack the exposing functional into one valid equality face.
      right
      exact hF.exists_eq_face_set_of_nonempty hF_nonempty
    · -- Otherwise the exposed set is empty.
      left
      exact Set.not_nonempty_iff_eq_empty.mp hF_nonempty
  · rintro (rfl | ⟨c, δ, h_valid, rfl⟩)
    · -- The empty set is exposed by convention.
      exact isExposed_empty
    · -- Every valid equality face is exposed.
      exact isExposed_face_set_of_valid_inequality h_valid

/-- Definition 3.8-extra-2 (2). A hyperplane is supporting for `P` if it is defined by a nonzero
valid inequality whose associated face on `P` is nonempty. -/
def is_supporting_hyperplane {n : ℕ} (P H : Set (Fin n → ℝ)) : Prop :=
  ∃ c : Fin n → ℝ, ∃ δ : ℝ,
    c ≠ 0 ∧ is_valid_inequality P c δ ∧ (face_set P c δ).Nonempty ∧ H = linear_hyperplane c δ

/-- `is_supporting_hyperplane` unfolds to the existence of a nonzero valid defining inequality with
nonempty equality face. -/
theorem is_supporting_hyperplane_iff {n : ℕ} {P H : Set (Fin n → ℝ)} :
    is_supporting_hyperplane P H ↔
      ∃ c : Fin n → ℝ, ∃ δ : ℝ,
        c ≠ 0 ∧ is_valid_inequality P c δ ∧ (face_set P c δ).Nonempty ∧
          H = linear_hyperplane c δ := by
  rfl

/-- Definition 3.8-extra-2 (3). A proper face of `P` is a nonempty exposed face properly contained
in `P`. -/
def is_proper_face {n : ℕ} (P F : Set (Fin n → ℝ)) : Prop :=
  IsExposed ℝ P F ∧ F.Nonempty ∧ F ⊂ P

/-- `is_proper_face` unfolds to being a nonempty exposed face properly contained in `P`. -/
theorem is_proper_face_iff {n : ℕ} {P F : Set (Fin n → ℝ)} :
    is_proper_face P F ↔ IsExposed ℝ P F ∧ F.Nonempty ∧ F ⊂ P := by
  rfl
