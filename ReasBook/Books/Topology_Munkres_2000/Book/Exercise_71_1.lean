module

public import Topology_Munkres_2000.Book.Exercise_71_1.CircleUnion
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Coherent

public section

universe u

namespace Topology.IsCircleUnion

/-- Helper for Exercise 71.1: a finite closed cover by Hausdorff subspaces with
subsingleton pairwise intersections has Hausdorff union. -/
private lemma t2Space_of_finite_closed_cover_of_subsingleton_inter
    {X : Type u} {ι : Type*} [TopologicalSpace X] [Finite ι]
    (F : ι → Set X) [∀ i, T2Space (F i)]
    (h_closed : ∀ i, IsClosed (F i)) (h_cover : ⋃ i, F i = Set.univ)
    (h_inter : ∀ {i j}, i ≠ j → (F i ∩ F j).Subsingleton) :
    T2Space X := by
  classical
  -- Each rectangle contributes a closed equality locus to the ambient diagonal.
  have h_piece_closed (i j : ι) :
      IsClosed ((Prod.map ((↑) : F i → X) ((↑) : F j → X)) ''
        {z : F i × F j | (z.1 : X) = z.2}) := by
    have h_embedding : Topology.IsClosedEmbedding
        (Prod.map ((↑) : F i → X) ((↑) : F j → X)) :=
      (h_closed i).isClosedEmbedding_subtypeVal.prodMap
        (h_closed j).isClosedEmbedding_subtypeVal
    rw [← h_embedding.isClosed_iff_image_isClosed]
    by_cases hij : i = j
    · subst j
      have h_equal_piece :
          {z : F i × F i | (z.1 : X) = z.2} = Set.diagonal (F i) := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_diagonal_iff, Subtype.ext_iff]
      rw [h_equal_piece]
      exact isClosed_diagonal
    · have h_subsingleton :
          {z : F i × F j | (z.1 : X) = z.2}.Subsingleton := by
        intro a ha b hb
        have ha_inter : (a.1 : X) ∈ F i ∩ F j :=
          ⟨a.1.property, ha ▸ a.2.property⟩
        have hb_inter : (b.1 : X) ∈ F i ∩ F j :=
          ⟨b.1.property, hb ▸ b.2.property⟩
        have hab : (a.1 : X) = b.1 := h_inter hij ha_inter hb_inter
        apply Prod.ext
        · exact Subtype.ext hab
        · exact Subtype.ext (ha.symm.trans (hab.trans hb))
      exact h_subsingleton.isClosed
  -- The cover writes the full diagonal as the finite union of those loci.
  have h_diagonal : Set.diagonal X = ⋃ q : ι × ι,
      (Prod.map ((↑) : F q.1 → X) ((↑) : F q.2 → X)) ''
        {z : F q.1 × F q.2 | (z.1 : X) = z.2} := by
    ext z
    constructor
    · intro hz
      have hz_eq : z.1 = z.2 := Set.mem_diagonal_iff.mp hz
      have hz_first : z.1 ∈ ⋃ i, F i := by
        rw [h_cover]
        exact Set.mem_univ z.1
      have hz_second : z.2 ∈ ⋃ i, F i := by
        rw [h_cover]
        exact Set.mem_univ z.2
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz_first
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz_second
      refine Set.mem_iUnion.mpr ⟨(i, j), ?_⟩
      exact ⟨(⟨z.1, hzi⟩, ⟨z.2, hzj⟩), hz_eq, rfl⟩
    · intro hz
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
      obtain ⟨w, hw, rfl⟩ := hq
      exact Set.mem_diagonal_iff.mpr hw
  rw [t2_iff_isClosed_diagonal, h_diagonal]
  exact isClosed_iUnion_of_finite fun q ↦ h_piece_closed q.1 q.2

/-- Helper for Exercise 71.1: a topology is coherent with any finite closed cover. -/
private lemma isCoherentWith_of_finite_closed_cover
    {X : Type u} {ι : Type*} [TopologicalSpace X] [Finite ι]
    (F : ι → Set X) (h_closed : ∀ i, IsClosed (F i))
    (h_cover : ⋃ i, F i = Set.univ) :
    Topology.IsCoherentWith (Set.range F) := by
  -- Reassemble a set from its closed restrictions to the finitely many pieces.
  refine Topology.IsCoherentWith.of_isClosed fun C hC ↦ ?_
  have h_inter_closed (i : ι) : IsClosed (F i ∩ C) := by
    exact (h_closed i).inter_preimage_val_iff.mp (hC (F i) ⟨i, rfl⟩)
  have h_union : C = ⋃ i, F i ∩ C := by
    ext x
    constructor
    · intro hx
      have hx_cover : x ∈ ⋃ i, F i := by
        rw [h_cover]
        exact Set.mem_univ x
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx_cover
      exact Set.mem_iUnion.mpr ⟨i, hxi, hx⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact hxi.2
  rw [h_union]
  exact isClosed_iUnion_of_finite h_inter_closed

/-- Helper for Exercise 71.1: coherence forces every component circle to be closed. -/
private lemma isClosed_of_isCoherentWith
    {X : Type u} [TopologicalSpace X] {ι : Type*}
    (S : ι → Set X) (p : X) [IsCircleUnion S p]
    (h_coherent : Topology.IsCoherentWith (Set.range S)) (i : ι) :
    IsClosed (S i) := by
  classical
  -- On its own component the restriction is universal; on every other one it is finite.
  refine h_coherent.isClosed_iff.mpr fun s hs ↦ ?_
  obtain ⟨j, rfl⟩ := hs
  letI : T2Space (S j) :=
    (Classical.choice (IsCircleUnion.homeomorphic_circle (S := S) (p := p) j)).symm.t2Space
  by_cases hij : i = j
  · subst j
    have h_preimage : ((↑) : S i → X) ⁻¹' S i = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact x.property
    rw [h_preimage]
    exact isClosed_univ
  · have h_subsingleton : ((↑) : S j → X) ⁻¹' S i |>.Subsingleton := by
      intro x hx y hy
      have hx_inter : (x : X) ∈ S i ∩ S j := ⟨hx, x.property⟩
      have hy_inter : (y : X) ∈ S i ∩ S j := ⟨hy, y.property⟩
      have hx_p : (x : X) = p := by
        have hx_singleton : (x : X) ∈ ({p} : Set X) :=
          (Set.ext_iff.mp (IsCircleUnion.inter_eq (S := S) (p := p) hij) x).mp hx_inter
        exact Set.mem_singleton_iff.mp hx_singleton
      have hy_p : (y : X) = p := by
        have hy_singleton : (y : X) ∈ ({p} : Set X) :=
          (Set.ext_iff.mp (IsCircleUnion.inter_eq (S := S) (p := p) hij) y).mp hy_inter
        exact Set.mem_singleton_iff.mp hy_singleton
      exact Subtype.ext (hx_p.trans hy_p.symm)
    exact h_subsingleton.finite.isClosed

/-- Exercise 71.1 (1). A space covered by finitely many circles meeting pairwise exactly
at one common point is Hausdorff if and only if every circle is closed. -/
theorem t2Space_iff_isClosed {X : Type u} [TopologicalSpace X] {n : ℕ}
    (S : Fin n → Set X) (p : X) [IsCircleUnion S p] :
    T2Space X ↔ ∀ i, IsClosed (S i) := by
  constructor
  · intro hT2 i
    letI : T2Space X := hT2
    obtain ⟨e⟩ := IsCircleUnion.homeomorphic_circle (S := S) (p := p) i
    -- Compactness transfers from `Circle`, and compact subsets of a Hausdorff space are closed.
    exact (isCompact_iff_compactSpace.mpr e.symm.compactSpace).isClosed
  · intro h_closed
    classical
    letI : ∀ i, T2Space (S i) := fun i ↦
      (Classical.choice
        (IsCircleUnion.homeomorphic_circle (S := S) (p := p) i)).symm.t2Space
    -- The singleton intersection law supplies the off-diagonal closed pieces.
    have h_inter : ∀ {i j}, i ≠ j → (S i ∩ S j).Subsingleton := by
      intro i j hij
      rw [IsCircleUnion.inter_eq (S := S) (p := p) hij]
      exact Set.subsingleton_singleton
    exact t2Space_of_finite_closed_cover_of_subsingleton_inter S h_closed
      (IsCircleUnion.covers (S := S) (p := p)) h_inter

/-- Exercise 71.1 (2). A space covered by finitely many circles meeting pairwise exactly
at one common point is Hausdorff if and only if its topology is coherent with them. -/
theorem t2Space_iff_isCoherentWith {X : Type u} [TopologicalSpace X] {n : ℕ}
    (S : Fin n → Set X) (p : X) [IsCircleUnion S p] :
    T2Space X ↔ Topology.IsCoherentWith (Set.range S) := by
  constructor
  · intro hT2
    have h_closed := (t2Space_iff_isClosed S p).mp hT2
    -- The finite closed cover now generates the ambient topology coherently.
    exact isCoherentWith_of_finite_closed_cover S h_closed
      (IsCircleUnion.covers (S := S) (p := p))
  · intro h_coherent
    -- Coherence closes each circle, reducing the converse to part (1).
    exact (t2Space_iff_isClosed S p).mpr
      (isClosed_of_isCoherentWith S p h_coherent)

noncomputable section

namespace NonHausdorffCircleWedge

/-- Helper for Exercise 71.1: a circle with a second copy of every point except `1`. -/
inductive Space : Type u where
  | left : Circle → Space
  | right : {z : Circle // z ≠ 1} → Space

/-- Helper for Exercise 71.1: the doubled circle projects to its underlying circle. -/
def projection : Space → Circle
  | .left z => z
  | .right z => z

/-- Helper for Exercise 71.1: the doubled circle carries the topology induced by its projection. -/
instance instTopologicalSpaceSpace : TopologicalSpace Space :=
  TopologicalSpace.induced projection inferInstance

/-- Helper for Exercise 71.1: the common basepoint of the two component circles. -/
def origin : Space := .left 1

/-- Helper for Exercise 71.1: the two circles in the doubled-circle model. -/
def component (i : Fin 2) : Set Space :=
  if i = 0 then Set.range Space.left else {origin} ∪ Set.range Space.right

/-- Helper for Exercise 71.1: the first model component is the full left copy. -/
lemma component_zero : component 0 = Set.range Space.left := by
  -- Evaluation at the first index selects the left range.
  unfold component
  rfl

/-- Helper for Exercise 71.1: the second model component is the origin plus the right copy. -/
lemma component_one : component 1 = {origin} ∪ Set.range Space.right := by
  -- Evaluation at the second index selects the origin and punctured right range.
  unfold component
  rfl

/-- Helper for Exercise 71.1: every point in the left copy belongs to the first component. -/
lemma left_mem_component (z : Circle) : Space.left z ∈ component 0 := by
  -- Unfolding the zeroth component leaves exactly the range of `Space.left`.
  simp only [component, if_pos, Set.mem_range]
  exact ⟨z, rfl⟩

/-- Helper for Exercise 71.1: the common origin belongs to the second component. -/
lemma origin_mem_component : origin ∈ component 1 := by
  -- The origin is the distinguished singleton summand of the second component.
  rw [component_one]
  exact Or.inl rfl

/-- Helper for Exercise 71.1: every point in the punctured right copy belongs to
the second component. -/
lemma right_mem_component (z : {z : Circle // z ≠ 1}) :
    Space.right z ∈ component 1 := by
  -- The punctured right copy is the range summand of the second component.
  rw [component_one]
  exact Or.inr ⟨z, rfl⟩

/-- Helper for Exercise 71.1: projection restricted to either component. -/
def componentProjection (i : Fin 2) : component i → Circle :=
  fun x ↦ projection x

/-- Helper for Exercise 71.1: each restricted component projection induces its topology. -/
lemma componentProjection_isInducing (i : Fin 2) :
    Topology.IsInducing (componentProjection i) := by
  -- Inducing maps remain inducing after restriction to a subtype.
  unfold componentProjection
  exact (Topology.IsInducing.induced projection).comp Topology.IsInducing.subtypeVal

/-- Helper for Exercise 71.1: each restricted component projection is bijective. -/
lemma componentProjection_bijective (i : Fin 2) :
    Function.Bijective (componentProjection i) := by
  fin_cases i
  · constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [component] at hx hy
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      simp only [componentProjection, projection] at hxy
      exact Subtype.ext (congrArg Space.left hxy)
    · intro z
      have hmem : Space.left z ∈ component 0 := left_mem_component z
      have hprojection : componentProjection 0 ⟨Space.left z, hmem⟩ = z := by
        simp only [componentProjection, projection]
      exact ⟨⟨Space.left z, hmem⟩, hprojection⟩
  · constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [component] at hx hy
      rcases hx with rfl | ⟨z, rfl⟩
      · rcases hy with rfl | ⟨w, rfl⟩
        · have hcircle : (1 : Circle) = 1 := Eq.refl 1
          exact Subtype.ext (congrArg Space.left hcircle)
        · simp only [componentProjection, projection, origin] at hxy
          exact False.elim (w.property hxy.symm)
      · rcases hy with rfl | ⟨w, rfl⟩
        · simp only [componentProjection, projection, origin] at hxy
          exact False.elim (z.property hxy)
        · simp only [componentProjection, projection] at hxy
          exact Subtype.ext (congrArg Space.right (Subtype.ext hxy))
    · intro z
      by_cases hz : z = 1
      · subst z
        have hmem : origin ∈ component 1 := origin_mem_component
        have hprojection : componentProjection 1 ⟨origin, hmem⟩ = 1 := by
          simp only [componentProjection, origin, projection]
        exact ⟨⟨origin, hmem⟩, hprojection⟩
      · let z' : {w : Circle // w ≠ 1} := ⟨z, hz⟩
        have hmem : Space.right z' ∈ component 1 := right_mem_component z'
        have hprojection : componentProjection 1 ⟨Space.right z', hmem⟩ = z := by
          simp only [componentProjection, projection, z']
        exact ⟨⟨Space.right z', hmem⟩, hprojection⟩

/-- Helper for Exercise 71.1: each component of the model is homeomorphic to `Circle`. -/
lemma componentHomeomorphicCircle (i : Fin 2) : Nonempty (component i ≃ₜ Circle) := by
  -- Bijectivity and the inducing property promote the restricted projection to a homeomorphism.
  let e : component i ≃ Circle :=
    Equiv.ofBijective (componentProjection i) (componentProjection_bijective i)
  have he : Topology.IsInducing e := by
    have he_fun : (e : component i → Circle) = componentProjection i := by
      rfl
    rw [he_fun]
    exact componentProjection_isInducing i
  exact ⟨e.toHomeomorphOfIsInducing he⟩

/-- Helper for Exercise 71.1: the two model components cover the doubled circle. -/
lemma components_cover : ⋃ i, component i = Set.univ := by
  -- Every constructor lands in its corresponding component.
  ext x
  constructor
  · intro hx
    exact Set.mem_univ x
  · intro hx
    cases x with
    | left z => exact Set.mem_iUnion.mpr ⟨0, left_mem_component z⟩
    | right z => exact Set.mem_iUnion.mpr ⟨1, right_mem_component z⟩

/-- Helper for Exercise 71.1: the two model components meet only at their common origin. -/
lemma components_inter : Pairwise (fun i j ↦ component i ∩ component j = {origin}) := by
  -- There are only two ordered distinct pairs, and constructor disjointness resolves both.
  intro i j hij
  fin_cases i
  · fin_cases j
    · exact False.elim (hij rfl)
    · ext x
      cases x with
      | left z => simp [component, origin]
      | right z => simp [component, origin]
  · fin_cases j
    · ext x
      cases x with
      | left z => simp [component, origin]
      | right z => simp [component, origin]
    · exact False.elim (hij rfl)

/-- Helper for Exercise 71.1: the doubled-circle model is a circle union. -/
lemma isCircleUnion : Topology.IsCircleUnion component origin := by
  -- Combine the cover, component homeomorphisms, and singleton intersection calculation.
  exact Topology.IsCircleUnion.of components_cover componentHomeomorphicCircle components_inter

/-- Helper for Exercise 71.1: the doubled-circle model is not Hausdorff. -/
lemma notT2Space : ¬ T2Space Space := by
  intro hT2
  letI : T2Space Space := hT2
  let z : {w : Circle // w ≠ 1} := ⟨-1, Circle.neg_ne_self 1⟩
  have hprojection : projection (Space.left (-1)) = projection (Space.right z) := by
    simp only [projection, z]
  -- Hausdorffness would make the inducing projection injective, contradicting the doubled point.
  have hfalse := (Topology.IsInducing.induced projection).injective hprojection
  exact Space.noConfusion hfalse

end NonHausdorffCircleWedge

end

/-- Exercise 71.1 (3). There is a non-Hausdorff space covered by two circles that meet
exactly at one common point. -/
theorem exists_not_t2Space :
    ∃ (X : TopCat) (S : Fin 2 → Set X) (p : X),
      IsCircleUnion S p ∧ ¬ T2Space X := by
  -- Package the explicit doubled-circle model as a topological category object.
  exact ⟨TopCat.of NonHausdorffCircleWedge.Space,
    NonHausdorffCircleWedge.component, NonHausdorffCircleWedge.origin,
    NonHausdorffCircleWedge.isCircleUnion, NonHausdorffCircleWedge.notT2Space⟩

end Topology.IsCircleUnion
