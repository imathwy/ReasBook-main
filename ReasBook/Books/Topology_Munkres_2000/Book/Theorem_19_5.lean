module

public import Topology_Munkres_2000.Book.Theorem_19_1.Basis
public import Mathlib.Topology.NhdsWithin

universe u v

open scoped Topology

public section

namespace Pi

/-- Helper for Theorem 19.5: membership in a box restricting one coordinate is
membership in the selected coordinate set. -/
private lemma mem_coordinateBox_iff {ι : Type u} {X : ι → Type v}
    [DecidableEq ι] (i : ι) (U : Set (X i)) (x : (j : ι) → X j) :
    x ∈ Set.pi Set.univ (Function.update (fun _ ↦ Set.univ) i U) ↔ x i ∈ U := by
  -- Read the selected coordinate from membership in the whole box.
  constructor
  · intro hx
    have hxi := hx i (Set.mem_univ i)
    simpa only [Function.update_self] using hxi
  · intro hxi j hj
    -- At the selected coordinate use the hypothesis; elsewhere the factor is `univ`.
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hxi
    · simp only [Function.update_of_ne hji, Set.mem_univ]

/-- Helper for Theorem 19.5: a box restricting one coordinate to an open set
belongs to the box basis. -/
private lemma coordinateBox_mem_boxBasis {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] [DecidableEq ι]
    (i : ι) (U : Set (X i)) (hU : IsOpen U) :
    Set.pi Set.univ (Function.update (fun _ ↦ Set.univ) i U) ∈ boxBasis X := by
  -- Present the coordinate box by its open coordinate factors.
  refine (mem_boxBasis _).mpr ⟨Function.update (fun _ ↦ Set.univ) i U, ?_, rfl⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hU
  · simpa only [Function.update_of_ne hji] using
      (isOpen_univ : IsOpen (Set.univ : Set (X j)))

/-- Helper for Theorem 19.5: an open box containing a point whose constrained
coordinates lie in the corresponding closures meets the Cartesian product. -/
private lemma boxIntersectsPiOfCoordinatewiseClosure {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] {I : Set ι}
    {A U : (i : ι) → Set (X i)} {x : (i : ι) → X i}
    (hU : ∀ i, IsOpen (U i)) (hxU : x ∈ Set.pi Set.univ U)
    (hxA : ∀ i ∈ I, x i ∈ closure (A i)) :
    (Set.pi Set.univ U ∩ Set.pi I A).Nonempty := by
  classical
  -- Choose a point in `U i ∩ A i` on constrained coordinates and retain `x i` elsewhere.
  have hExists : ∀ i, ∃ y : X i, y ∈ U i ∧ (i ∈ I → y ∈ A i) := by
    intro i
    by_cases hi : i ∈ I
    · have hMeet : (U i ∩ A i).Nonempty :=
        (mem_closure_iff.mp (hxA i hi)) (U i) (hU i) (hxU i (Set.mem_univ i))
      obtain ⟨y, hyU, hyA⟩ := hMeet
      exact ⟨y, hyU, fun _ ↦ hyA⟩
    · exact ⟨x i, hxU i (Set.mem_univ i), fun hi' ↦ (hi hi').elim⟩
  choose y hyU hyA using hExists
  -- Assemble the coordinate choices into the required point of the intersection.
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    exact hyU i
  · intro i hi
    exact hyA i hi

/-- Theorem 19.5: membership in the box-topology closure of a Cartesian product is
coordinatewise membership in the corresponding closures. -/
theorem mem_closure_pi_box {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] {I : Set ι}
    {A : (i : ι) → Set (X i)} {x : (i : ι) → X i} :
    x ∈ closure[boxTopologicalSpace X] (Set.pi I A) ↔
      ∀ i ∈ I, x i ∈ closure (A i) := by
  -- Use the open boxes from Theorem 19.1 as the closure-testing basis.
  classical
  letI : TopologicalSpace ((i : ι) → X i) := boxTopologicalSpace X
  have hBasis := (isTopologicalBasis_boxBasis :
    (boxTopologicalSpace X).IsTopologicalBasis (boxBasis X))
  rw [hBasis.mem_closure_iff]
  constructor
  · intro hx i hi
    -- Test the product closure against a box restricting only coordinate `i`.
    apply mem_closure_iff.mpr
    intro U hU hxi
    have hBox := coordinateBox_mem_boxBasis i U hU
    have hxBox := (mem_coordinateBox_iff i U x).mpr hxi
    obtain ⟨y, hyBox, hyA⟩ := hx _ hBox hxBox
    exact ⟨y i, (mem_coordinateBox_iff i U y).mp hyBox, hyA i hi⟩
  · intro hx B hB hxB
    -- An arbitrary basis box meets the product by choosing a point coordinatewise.
    obtain ⟨U, hU, rfl⟩ := (mem_boxBasis B).mp hB
    exact boxIntersectsPiOfCoordinatewiseClosure hU hxB hx

/-- Helper for Theorem 19.5: the box-topology closure of a Cartesian product is
the product of the coordinatewise closures. -/
theorem closure_pi_set_box {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (I : Set ι) (A : (i : ι) → Set (X i)) :
    closure[boxTopologicalSpace X] (Set.pi I A) = Set.pi I (fun i ↦ closure (A i)) := by
  -- Extensionality reduces the equality to the coordinatewise membership theorem.
  ext x
  exact mem_closure_pi_box

end Pi

/- Theorem 19.5 (1): For the product topology, the Cartesian product of the
coordinatewise closures equals the closure of the Cartesian product. -/
#check closure_pi_set Set.univ

/- Theorem 19.5 (2): For the box topology, the Cartesian product of the
coordinatewise closures equals the closure of the Cartesian product. -/
#check Pi.closure_pi_set_box Set.univ
