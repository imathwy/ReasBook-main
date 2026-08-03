module

public import Mathlib.Topology.Connected.Basic

public section

open Set

universe u v

/-- The subspace of a product whose coordinates outside `K` equal the fixed point `a`. -/
def coordinateSubspace {J : Type u} {X : J → Type v} (a : (j : J) → X j)
    (K : Set J) : Set ((j : J) → X j) :=
  {x | ∀ j, j ∉ K → x j = a j}

/-- Membership in `coordinateSubspace a K` means agreeing with `a` outside `K`. -/
theorem mem_coordinateSubspace {J : Type u} {X : J → Type v}
    (a x : (j : J) → X j) (K : Set J) :
    x ∈ coordinateSubspace a K ↔ ∀ j, j ∉ K → x j = a j := by
  rfl

/-- Helper for Exercise 23.10: a coordinate subspace is the product of full
factors on `K` and singleton factors outside `K`. -/
lemma coordinateSubspace_eq_univ_pi {J : Type u} {X : J → Type v}
    (a : (j : J) → X j) (K : Set J) :
    coordinateSubspace a K =
      Set.univ.pi (fun j ↦ {z | j ∈ K ∨ z = a j}) := by
  -- Compare the two descriptions coordinate by coordinate.
  ext x
  simp only [mem_coordinateSubspace, mem_pi, mem_univ, true_implies, mem_setOf_eq]
  constructor
  · intro hx j
    by_cases hj : j ∈ K
    · exact Or.inl hj
    · exact Or.inr (hx j hj)
  · intro hx j hj
    exact (hx j).resolve_left hj

/-- Exercise 23.10 (a): if `K` is finite and every factor is connected, then
the subspace whose coordinates outside `K` are fixed at `a` is connected. -/
theorem isConnected_coordinateSubspace {J : Type u} {X : J → Type v}
    [(j : J) → TopologicalSpace (X j)] [∀ j, ConnectedSpace (X j)]
    (a : (j : J) → X j) (K : Set J) (hK : K.Finite) :
    IsConnected (coordinateSubspace a K) := by
  -- Rewrite the subspace as a product of connected coordinate sets.
  rw [coordinateSubspace_eq_univ_pi, isConnected_univ_pi]
  intro j
  by_cases hj : j ∈ K
  · have hfactor : {z : X j | j ∈ K ∨ z = a j} = Set.univ := by
      ext z
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact Or.inl hj
    rw [hfactor]
    exact isConnected_univ
  · have hfactor : {z : X j | j ∈ K ∨ z = a j} = {a j} := by
      ext z
      simp only [mem_setOf_eq, mem_singleton_iff]
      exact or_iff_right hj
    rw [hfactor]
    exact isConnected_singleton

/-- The union `Y` of the finite-coordinate subspaces based at `a`. -/
def finiteCoordinateUnion {J : Type u} {X : J → Type v} (a : (j : J) → X j) :
    Set ((j : J) → X j) :=
  ⋃ K : {K : Set J // K.Finite}, coordinateSubspace a K

/-- Membership in `finiteCoordinateUnion a` is equivalent to differing from
`a` at only finitely many coordinates. -/
theorem mem_finiteCoordinateUnion_iff {J : Type u} {X : J → Type v}
    (a x : (j : J) → X j) :
    x ∈ finiteCoordinateUnion a ↔ {j | x j ≠ a j}.Finite := by
  simp only [finiteCoordinateUnion, mem_iUnion, Subtype.exists, mem_coordinateSubspace]
  constructor
  · rintro ⟨K, hK, hx⟩
    exact hK.subset fun j hj ↦ by
      contrapose! hj
      simpa using hx j hj
  · intro h
    exact ⟨{j | x j ≠ a j}, h, fun _ hj ↦ not_ne_iff.mp hj⟩

/-- Exercise 23.10 (b): the union of all finite-coordinate subspaces based at
`a` is connected. -/
theorem isConnected_finiteCoordinateUnion {J : Type u} {X : J → Type v}
    [(j : J) → TopologicalSpace (X j)] [∀ j, ConnectedSpace (X j)]
    (a : (j : J) → X j) :
    IsConnected (finiteCoordinateUnion a) := by
  -- The basepoint belongs to every finite-coordinate subspace.
  have hcommon : (⋂ K : {K : Set J // K.Finite}, coordinateSubspace a K).Nonempty := by
    refine ⟨a, ?_⟩
    simp only [mem_iInter, mem_coordinateSubspace]
    intro K j hj
    trivial
  -- A union of preconnected sets with a common point is preconnected.
  refine ⟨?_, ?_⟩
  · refine ⟨a, ?_⟩
    rw [mem_finiteCoordinateUnion_iff]
    simpa only [ne_eq, not_true_eq_false, setOf_false] using (Set.finite_empty : (∅ : Set J).Finite)
  · rw [finiteCoordinateUnion]
    exact isPreconnected_iUnion hcommon fun K ↦
      (isConnected_coordinateSubspace a K K.property).isPreconnected

/-- The union of all finite-coordinate subspaces based at `a` is dense in the
product space. -/
theorem dense_finiteCoordinateUnion {J : Type u} {X : J → Type v}
    [(j : J) → TopologicalSpace (X j)] (a : (j : J) → X j) :
    Dense (finiteCoordinateUnion a) := by
  classical
  -- Every nonempty open set contains a finite-coordinate modification of `a`.
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨I, u, hxu, hpiU⟩ := isOpen_pi_iff.mp hU x hxU
  let y : (j : J) → X j := fun j ↦ if j ∈ I then x j else a j
  have hyPi : y ∈ (I : Set J).pi u := by
    intro j hj
    simp only [y, Finset.mem_coe.mp hj, if_pos]
    exact (hxu j (Finset.mem_coe.mp hj)).2
  have hyU : y ∈ U := hpiU hyPi
  have hyFinite : {j | y j ≠ a j}.Finite := by
    refine I.finite_toSet.subset ?_
    intro j hj
    by_contra hjI
    have hjI' : j ∉ I := by
      simpa only [Finset.mem_coe] using hjI
    have hyj : y j = a j := by
      simp [y, hjI']
    exact hj hyj
  refine ⟨y, hyU, ?_⟩
  exact (mem_finiteCoordinateUnion_iff a y).2 hyFinite

/-- Exercise 23.10 (c): the product space is the closure of the union of all
finite-coordinate subspaces based at `a`. -/
theorem closure_finiteCoordinateUnion {J : Type u} {X : J → Type v}
    [(j : J) → TopologicalSpace (X j)] (a : (j : J) → X j) :
    closure (finiteCoordinateUnion a) = Set.univ :=
  (dense_finiteCoordinateUnion a).closure_eq

variable {J : Type u} {X : J → Type v}
  [(j : J) → TopologicalSpace (X j)] [∀ j, ConnectedSpace (X j)]

/- Exercise 23.10 (c), conclusion: the product of connected spaces is connected. -/
#check (inferInstance : ConnectedSpace ((j : J) → X j))
