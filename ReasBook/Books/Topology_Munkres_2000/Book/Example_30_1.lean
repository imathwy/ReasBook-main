module

public import Topology_Munkres_2000.Book.Exercise_13_8.RationalIntervals

public section

namespace Real

/-- The full products of rational-endpoint open intervals in `ι → ℝ`. -/
def rationalOpenProducts (ι : Type u) : Set (Set (ι → ℝ)) :=
  {s | ∃ U : ι → Set ℝ,
    (∀ i, U i ∈ rationalOpenIntervals) ∧ s = (Set.univ : Set ι).pi U}

/-- Membership in `Real.rationalOpenProducts` is witnessed coordinatewise by rational intervals. -/
theorem mem_rationalOpenProducts {ι : Type u} (s : Set (ι → ℝ)) :
    s ∈ rationalOpenProducts ι ↔
      ∃ U : ι → Set ℝ,
        (∀ i, U i ∈ rationalOpenIntervals) ∧ s = (Set.univ : Set ι).pi U := Iff.rfl

/-- Helper for Example 30.1: finite-coordinate pi sets from a countable family form a
countable family. -/
lemma finiteCoordinatePiSets_countable {ι : Type u} {α : Type v} [Countable ι]
    (B : Set (Set α)) (hB : B.Countable) :
    {s : Set (ι → α) | ∃ (U : ι → Set α) (F : Finset ι),
      (∀ i ∈ F, U i ∈ B) ∧ s = (F : Set ι).pi U}.Countable := by
  classical
  let encode : (Σ F : Finset ι, F → B) → Set (ι → α) := fun p =>
    (p.1 : Set ι).pi fun i => if hi : i ∈ p.1 then p.2 ⟨i, hi⟩ else Set.univ
  letI : Countable B := hB.to_subtype
  -- Encode each cylinder by its finite support and its constrained coordinate sets.
  refine (Set.countable_range encode).mono ?_
  rintro s ⟨U, F, hU, rfl⟩
  let V : F → B := fun i => ⟨U i, hU i i.property⟩
  refine ⟨⟨F, V⟩, ?_⟩
  -- Values outside `F` do not affect the finite-coordinate pi set.
  ext x
  simp only [encode, Set.mem_pi, Finset.mem_coe]
  constructor
  · intro hx i hi
    simpa only [dif_pos hi, V] using hx i hi
  · intro hx i hi
    simpa only [dif_pos hi, V] using hx i hi

/-- Example 30.1: For a finite index type, the family `Real.rationalOpenProducts` is countable. -/
theorem rationalOpenProducts_countable (ι : Type u) [Finite ι] :
    (rationalOpenProducts ι).Countable := by
  classical
  -- Regard a full product as a finite-coordinate product supported on all indices.
  refine (finiteCoordinatePiSets_countable rationalOpenIntervals
    rationalOpenIntervals_countable).mono ?_
  rintro s ⟨U, hU, rfl⟩
  let F : Finset ι := Set.Finite.toFinset Set.finite_univ
  refine ⟨U, F, ?_, ?_⟩
  · intro i hi
    exact hU i
  · congr
    ext i
    simp [F]

/-- Helper for Example 30.1: a point of a finite rational cylinder lies in a full rational
product contained in that cylinder. -/
lemma exists_rationalOpenProduct_subset_finitePi {ι : Type u} [Finite ι]
    (F : Finset ι) (U : ι → Set ℝ) (hU : ∀ i ∈ F, U i ∈ rationalOpenIntervals)
    (x : ι → ℝ) (hx : x ∈ (F : Set ι).pi U) :
    ∃ s ∈ rationalOpenProducts ι, x ∈ s ∧ s ⊆ (F : Set ι).pi U := by
  classical
  let W : ι → Set ℝ := fun i => if i ∈ F then U i else Set.univ
  have hWOpen : ∀ i, IsOpen (W i) := by
    intro i
    by_cases hi : i ∈ F
    · simpa [W, hi] using rationalOpenIntervals_isTopologicalBasis.isOpen (hU i hi)
    · simp [W, hi]
  have hxW : ∀ i, x i ∈ W i := by
    intro i
    by_cases hi : i ∈ F
    · simpa [W, hi] using hx i hi
    · simp [W, hi]
  choose V hVB hxV hVW using fun i =>
    rationalOpenIntervals_isTopologicalBasis.exists_subset_of_mem_open (hxW i) (hWOpen i)
  -- Assemble the coordinatewise refinements into one full rational product.
  refine ⟨Set.univ.pi V, ⟨V, hVB, rfl⟩, ?_, ?_⟩
  · intro i hi
    exact hxV i
  · intro y hy i hi
    have hiF : i ∈ F := hi
    have hyV : y i ∈ V i := hy i (Set.mem_univ i)
    simpa [W, hiF] using hVW i hyV

/-- Companion for Example 30.1: For a finite index type, `Real.rationalOpenProducts` is a
topological basis of `ι → ℝ`. -/
theorem rationalOpenProducts_isTopologicalBasis (ι : Type u) [Finite ι] :
    TopologicalSpace.IsTopologicalBasis (rationalOpenProducts ι) := by
  let hPi := isTopologicalBasis_pi (fun _ : ι ↦ rationalOpenIntervals_isTopologicalBasis)
  -- Refine the canonical finite-coordinate product basis by full rational products.
  refine hPi.isTopologicalBasis_of_exists_subset ?_ ?_
  · rintro s ⟨U, hU, rfl⟩
    exact isOpen_set_pi Set.finite_univ fun i _ =>
      rationalOpenIntervals_isTopologicalBasis.isOpen (hU i)
  · rintro s ⟨U, F, hU, rfl⟩ x hx
    exact exists_rationalOpenProduct_subset_finitePi F U hU x hx

/-- The finite-coordinate cylinders with rational-endpoint interval constraints in `ι → ℝ`. -/
def rationalOpenCylinders (ι : Type u) : Set (Set (ι → ℝ)) :=
  {s | ∃ (U : ι → Set ℝ) (F : Finset ι),
    (∀ i ∈ F, U i ∈ rationalOpenIntervals) ∧ s = (F : Set ι).pi U}

/-- Membership in `Real.rationalOpenCylinders` is witnessed by finitely many constrained
coordinates. -/
theorem mem_rationalOpenCylinders {ι : Type u} (s : Set (ι → ℝ)) :
    s ∈ rationalOpenCylinders ι ↔
      ∃ (U : ι → Set ℝ) (F : Finset ι),
        (∀ i ∈ F, U i ∈ rationalOpenIntervals) ∧ s = (F : Set ι).pi U := Iff.rfl

/-- Companion for Example 30.1: For a countable index type, the family
`Real.rationalOpenCylinders` is countable. -/
theorem rationalOpenCylinders_countable (ι : Type u) [Countable ι] :
    (rationalOpenCylinders ι).Countable := by
  -- The definition is exactly the generic finite-coordinate construction.
  exact finiteCoordinatePiSets_countable rationalOpenIntervals rationalOpenIntervals_countable

/-- Companion for Example 30.1: The family `Real.rationalOpenCylinders` is a topological basis
of `ι → ℝ`. -/
theorem rationalOpenCylinders_isTopologicalBasis (ι : Type u) :
    TopologicalSpace.IsTopologicalBasis (rationalOpenCylinders ι) :=
  isTopologicalBasis_pi (fun _ ↦ rationalOpenIntervals_isTopologicalBasis)

end Real
