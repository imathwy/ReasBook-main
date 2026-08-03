module

public import Topology_Munkres_2000.Book.Example_50_6.LinearGraph
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Topology.LocallyFinite

public section

universe u v

namespace FiniteLinearGraph

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Example 50.7: the endpoint vertex set of a finite linear graph is finite. -/
lemma vertexSet_finite (G : FiniteLinearGraph.{u, v} X) : G.vertexSet.Finite := by
  -- Each edge contributes two endpoints, and only finitely many edges occur.
  letI : Finite G.Edge := G.edgeFinite
  rw [G.vertexSet_def]
  exact Set.finite_iUnion fun i ↦ Set.toFinite {G.edge i 0, G.edge i 1}

end FiniteLinearGraph

/-- Helper for Example 50.7: at most four distinct points on the cubic moment curve are
affinely independent. -/
lemma momentCurve_affineIndependent_of_card_le_four
    {n : ℕ} (t : Fin n → ℝ) (ht : Function.Injective t) (hcard : n ≤ 4) :
    AffineIndependent ℝ
      (fun i ↦ (EuclideanSpace.equiv (Fin 3) ℝ).symm ![t i, (t i) ^ 2, (t i) ^ 3]) := by
  -- An affine dependence gives the first `n` power-sum equations.
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hweighted i
  have hlinear : ∑ j, w j •
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![t j, (t j) ^ 2, (t j) ^ 3] = 0 := by
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hweighted
    simpa using hweighted
  have hpowers : ∀ k : Fin n, ∑ j, w j * t j ^ (k : ℕ) = 0 := by
    intro k
    have hk : (k : ℕ) < 4 := lt_of_lt_of_le k.isLt hcard
    interval_cases hkval : (k : ℕ)
    · simpa [hkval] using hsum
    · simpa [hkval] using congrArg (fun x ↦ (EuclideanSpace.equiv (Fin 3) ℝ x) 0) hlinear
    · simpa [hkval] using congrArg (fun x ↦ (EuclideanSpace.equiv (Fin 3) ℝ x) 1) hlinear
    · simpa [hkval] using congrArg (fun x ↦ (EuclideanSpace.equiv (Fin 3) ℝ x) 2) hlinear
  -- Vandermonde invertibility forces every coefficient to vanish.
  have hw : w = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht hpowers
  exact congrFun hw i

namespace FiniteLinearGraph

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Example 50.7: the vertices admit an injective placement in Euclidean
three-space whose subfamilies of at most four vertices are affinely independent. -/
lemma exists_vertexMap_generalPosition (G : FiniteLinearGraph.{u, v} X) :
    ∃ z : X → EuclideanSpace ℝ (Fin 3), Set.InjOn z G.vertexSet ∧
      ∀ s : Finset X, (s : Set X) ⊆ G.vertexSet → s.card ≤ 4 →
        AffineIndependent ℝ (fun x : s ↦ z x) := by
  classical
  -- Enumerate the finite vertex subtype and place it on the moment curve.
  letI : Fintype G.vertexSet := G.vertexSet_finite.fintype
  let e := Fintype.equivFin G.vertexSet
  let p : G.vertexSet → EuclideanSpace ℝ (Fin 3) := fun x ↦
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![((e x : ℕ) : ℝ), ((e x : ℕ) : ℝ) ^ 2, ((e x : ℕ) : ℝ) ^ 3]
  let z : X → EuclideanSpace ℝ (Fin 3) := Subtype.val.extend p 0
  refine ⟨z, ?_, ?_⟩
  · -- On vertices, the extension is exactly the injective moment-curve placement.
    intro x hx y hy hxy
    have hxz : z x = p ⟨x, hx⟩ := Subtype.val_injective.extend_apply p 0 ⟨x, hx⟩
    have hyz : z y = p ⟨y, hy⟩ := Subtype.val_injective.extend_apply p 0 ⟨y, hy⟩
    have hp : p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
      exact hxz.symm.trans (hxy.trans hyz)
    have hparam : ((e ⟨x, hx⟩ : ℕ) : ℝ) = ((e ⟨y, hy⟩ : ℕ) : ℝ) := by
      simpa [p] using congrArg (fun q ↦ (EuclideanSpace.equiv (Fin 3) ℝ q) 0) hp
    have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Fin.ext
      exact_mod_cast hparam
    exact congrArg Subtype.val (e.injective heq)
  · intro s hs hcard
    -- Reindex the chosen vertices by their distinct finite parameters.
    let es : s ≃ Fin s.card := s.equivFin
    let t : Fin s.card → ℝ := fun i ↦
      ((e ⟨(es.symm i : X), hs (es.symm i).property⟩ : ℕ) : ℝ)
    have ht : Function.Injective t := by
      intro i j hij
      have heij : e ⟨(es.symm i : X), hs (es.symm i).property⟩ =
          e ⟨(es.symm j : X), hs (es.symm j).property⟩ := by
        dsimp [t] at hij
        apply Fin.ext
        exact_mod_cast hij
      have hvertex : (⟨(es.symm i : X), hs (es.symm i).property⟩ : G.vertexSet) =
          (⟨(es.symm j : X), hs (es.symm j).property⟩ : G.vertexSet) := e.injective heij
      exact es.symm.injective (Subtype.ext (congrArg (fun x : G.vertexSet ↦ (x : X)) hvertex))
    have hmoment := momentCurve_affineIndependent_of_card_le_four t ht hcard
    -- The extension computation identifies this family with the moment-curve family.
    have hfamily : (fun x : s ↦ z x) =
        (fun i ↦
          (EuclideanSpace.equiv (Fin 3) ℝ).symm ![t i, (t i) ^ 2, (t i) ^ 3]) ∘ es := by
      funext x
      have hxz : z x = p ⟨(x : X), hs x.property⟩ :=
        Subtype.val_injective.extend_apply p 0 ⟨(x : X), hs x.property⟩
      rw [hxz]
      simp [t, p]
    rw [hfamily]
    exact (affineIndependent_equiv es).mpr hmoment

end FiniteLinearGraph

namespace FiniteLinearGraph

variable {X : Type u} [TopologicalSpace X]

/-- Helper for Example 50.7: an edge-set point belongs to the range of its edge
parameterization. -/
lemma edgeSetPoint_mem_range (G : FiniteLinearGraph.{u, v} X) (i : G.Edge)
    (x : G.edgeSet i) : (x : X) ∈ Set.range (G.edge i) := by
  exact x.property

/-- Helper for Example 50.7: every parameterized edge point belongs to its edge set. -/
lemma edgePoint_mem_edgeSet (G : FiniteLinearGraph.{u, v} X) (i : G.Edge)
    (t : unitInterval) : G.edge i t ∈ G.edgeSet i := by
  simp [G.edgeSet_def]

variable [T2Space X]

/-- Helper for Example 50.7: affine line maps on the edges glue to a continuous map on the
finite linear graph. -/
lemma exists_continuous_edgewiseLineMap (G : FiniteLinearGraph.{u, v} X)
    (z : X → EuclideanSpace ℝ (Fin 3)) :
    ∃ f : X → EuclideanSpace ℝ (Fin 3), Continuous f ∧
      ∀ i t, f (G.edge i t) =
        AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)) (t : ℝ) := by
  classical
  letI : Finite G.Edge := G.edgeFinite
  let φ : ∀ i, G.edgeSet i → EuclideanSpace ℝ (Fin 3) := fun i x ↦
    AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1))
      ((G.edgeEmbedding i).toHomeomorph.symm
        ⟨x, G.edgeSetPoint_mem_range i x⟩ : ℝ)
  have hφ_spec (i : G.Edge) (t : unitInterval) :
      φ i ⟨G.edge i t, G.edgePoint_mem_edgeSet i t⟩ =
        AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)) (t : ℝ) := by
    -- The inverse of the embedding homeomorphism recovers the edge parameter.
    have htparam := (G.edgeEmbedding i).toHomeomorph_symm_apply t
    exact congrArg (AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)))
      (congrArg Subtype.val htparam)
  have hφ_vertex (i : G.Edge) (x : X) (hx : x ∈ G.edgeSet i)
      (hend : x = G.edge i 0 ∨ x = G.edge i 1) : φ i ⟨x, hx⟩ = z x := by
    -- At either endpoint, the affine line map agrees with the assigned vertex position.
    obtain rfl | rfl := hend
    · simpa using hφ_spec i 0
    · simpa using hφ_spec i 1
  have hcompat : ∀ (i j : G.Edge) (x : X) (hxi : x ∈ G.edgeSet i)
      (hxj : x ∈ G.edgeSet j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    by_cases hij : i = j
    · subst j
      rfl
    · have hend := G.inter_subset_endpoints hij ⟨hxi, hxj⟩
      exact (hφ_vertex i x hxi hend.1).trans (hφ_vertex j x hxj hend.2).symm
  let f : X → EuclideanSpace ℝ (Fin 3) :=
    Set.liftCover G.edgeSet φ hcompat G.iUnion_edgeSet
  refine ⟨f, ?_, ?_⟩
  · -- Continuity follows from the finite closed cover by compact edge images.
    refine (locallyFinite_of_finite G.edgeSet).continuous G.iUnion_edgeSet ?_ ?_
    · intro i
      exact (isCompact_range (G.edgeEmbedding i).continuous).isClosed
    · intro i
      have hφ_cont : Continuous (φ i) := by
        exact
          (AffineMap.lineMap
            (z (G.edge i 0)) (z (G.edge i 1))).continuous_of_finiteDimensional.comp
          (continuous_subtype_val.comp (G.edgeEmbedding i).toHomeomorph.symm.continuous)
      rw [continuousOn_iff_continuous_restrict]
      have hrestrict : (G.edgeSet i).restrict f = φ i := by
        funext x
        exact Set.liftCover_coe (hS := G.iUnion_edgeSet) x
      rw [hrestrict]
      exact hφ_cont
  · intro i t
    -- The lift-cover computation rule exposes the intended affine edge formula.
    have hmem : G.edge i t ∈ G.edgeSet i := G.edgePoint_mem_edgeSet i t
    have hlift : f (G.edge i t) = φ i ⟨G.edge i t, hmem⟩ :=
      Set.liftCover_of_mem hmem
    rw [hlift]
    exact hφ_spec i t

/-- Helper for Example 50.7: the convex hulls of two coordinate endpoint pairs intersect in
the convex hull of their common coordinate endpoints. -/
lemma endpointConvexHulls_inter
    {X : Type u} [TopologicalSpace X] [DecidableEq X]
    (G : FiniteLinearGraph.{u, v} X) {z : X → EuclideanSpace ℝ (Fin 3)}
    (hz_inj : Set.InjOn z G.vertexSet)
    (hz_gp : ∀ s : Finset X, (s : Set X) ⊆ G.vertexSet → s.card ≤ 4 →
      AffineIndependent ℝ (fun x : s ↦ z x)) (i j : G.Edge) :
    convexHull ℝ
        ((Finset.image z
          (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1}) : Finset X) : Finset _) :
          Set (EuclideanSpace ℝ (Fin 3))) =
      convexHull ℝ ((Finset.image z ({G.edge i 0, G.edge i 1} : Finset X) : Finset _) : Set _) ∩
        convexHull ℝ
          ((Finset.image z ({G.edge j 0, G.edge j 1} : Finset X) : Finset _) : Set _) := by
  classical
  let endpoints : Finset X := {G.edge i 0, G.edge i 1} ∪ {G.edge j 0, G.edge j 1}
  have hendpoints : (endpoints : Set X) ⊆ G.vertexSet := by
    -- Every member of the endpoint union is one of the four displayed vertices.
    intro x hx
    simp only [endpoints, Finset.mem_coe, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl) | rfl | rfl
    · exact G.endpoint_mem_vertexSet i 0 (Or.inl rfl)
    · exact G.endpoint_mem_vertexSet i 1 (Or.inr rfl)
    · exact G.endpoint_mem_vertexSet j 0 (Or.inl rfl)
    · exact G.endpoint_mem_vertexSet j 1 (Or.inr rfl)
  have hcard : endpoints.card ≤ 4 := by
    -- A union of two endpoint pairs contains at most four points.
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_le_two Finset.card_le_two)
  have hsource : AffineIndependent ℝ (fun x : endpoints ↦ z x) :=
    hz_gp endpoints hendpoints hcard
  have hinj : Set.InjOn z (endpoints : Set X) := hz_inj.mono hendpoints
  have hrange : Set.range (fun x : endpoints ↦ z x) =
      ((endpoints.image z : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) := by
    -- The range of the restricted coordinate map is its finset image.
    ext y
    simp only [Set.mem_range, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : Set.range (fun x : endpoints ↦ z x) ≃
      ((endpoints.image z : Finset _) : Set (EuclideanSpace ℝ (Fin 3))) :=
    Equiv.setCongr hrange
  have himage : AffineIndependent ℝ
      ((↑) : ↥(endpoints.image z) → EuclideanSpace ℝ (Fin 3)) := by
    -- Reindex the range subtype along the equality with the coordinate finset image.
    have hcomp : (fun x : Set.range (fun x : endpoints ↦ z x) ↦
        (x : EuclideanSpace ℝ (Fin 3))) =
        ((fun x : ↥(endpoints.image z) ↦ (x : EuclideanSpace ℝ (Fin 3))) ∘ e) := by
      funext x
      rfl
    apply (affineIndependent_equiv e).mp
    rw [← hcomp]
    exact hsource.range
  have himage_inter :
      Finset.image z (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1}) : Finset X) =
        Finset.image z ({G.edge i 0, G.edge i 1} : Finset X) ∩
          Finset.image z ({G.edge j 0, G.edge j 1} : Finset X) := by
    have hinjUnion : Set.InjOn z
        ((({G.edge i 0, G.edge i 1} : Finset X) : Set X) ∪
          (({G.edge j 0, G.edge j 1} : Finset X) : Set X)) := by
      simpa only [endpoints, Finset.coe_union] using hinj
    exact Finset.image_inter_of_injOn _ _ hinjUnion
  have hi_subset : Finset.image z ({G.edge i 0, G.edge i 1} : Finset X) ⊆ endpoints.image z := by
    exact Finset.image_mono z Finset.subset_union_left
  have hj_subset : Finset.image z ({G.edge j 0, G.edge j 1} : Finset X) ⊆ endpoints.image z := by
    exact Finset.image_mono z Finset.subset_union_right
  -- Apply the simplex intersection theorem in the normalized coordinate finset.
  rw [himage_inter]
  simpa only [Finset.coe_inter] using himage.convexHull_inter hi_subset hj_subset

/-- Helper for Example 50.7: an edge point whose coordinate is an endpoint coordinate is
that endpoint. -/
lemma edgePoint_eq_endpoint_of_image_eq
    {X : Type u} [TopologicalSpace X] (G : FiniteLinearGraph.{u, v} X)
    {z f : X → EuclideanSpace ℝ (Fin 3)}
    (hz_inj : Set.InjOn z G.vertexSet)
    (hf : ∀ i t, f (G.edge i t) =
      AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)) (t : ℝ))
    (i : G.Edge) (t : unitInterval) (p : X)
    (hp : p = G.edge i 0 ∨ p = G.edge i 1) (himage : f (G.edge i t) = z p) :
    G.edge i t = p := by
  have hedge : G.edge i 0 ≠ G.edge i 1 := by
    -- The stored edge parameterization separates the two unit-interval endpoints.
    intro h
    exact zero_ne_one ((G.edgeEmbedding i).injective h)
  have hz_ne : z (G.edge i 0) ≠ z (G.edge i 1) := by
    -- General-position coordinates remain distinct on the two source endpoints.
    intro h
    exact hedge (hz_inj (G.endpoint_mem_vertexSet i 0 (Or.inl rfl))
      (G.endpoint_mem_vertexSet i 1 (Or.inr rfl)) h)
  rcases hp with rfl | rfl
  · -- Equality with the left endpoint forces parameter zero.
    have ht : (t : ℝ) = 0 := (AffineMap.lineMap_injective ℝ hz_ne) (by
      rw [← hf i t, himage]
      exact (AffineMap.lineMap_apply_zero _ _).symm)
    exact congrArg (G.edge i) (Subtype.ext ht)
  · -- Equality with the right endpoint forces parameter one.
    have ht : (t : ℝ) = 1 := (AffineMap.lineMap_injective ℝ hz_ne) (by
      rw [← hf i t, himage]
      exact (AffineMap.lineMap_apply_one _ _).symm)
    exact congrArg (G.edge i) (Subtype.ext ht)

/-- Helper for Example 50.7: an edgewise affine map from a general-position vertex placement
is injective. -/
lemma edgewiseLineMap_injective
    {X : Type u} [TopologicalSpace X] (G : FiniteLinearGraph.{u, v} X)
    {z f : X → EuclideanSpace ℝ (Fin 3)}
    (hz_inj : Set.InjOn z G.vertexSet)
    (hz_gp : ∀ s : Finset X, (s : Set X) ⊆ G.vertexSet → s.card ≤ 4 →
      AffineIndependent ℝ (fun x : s ↦ z x))
    (hf : ∀ i t, f (G.edge i t) =
      AffineMap.lineMap (z (G.edge i 0)) (z (G.edge i 1)) (t : ℝ)) :
    Function.Injective f := by
  classical
  intro x y hxy
  -- Choose edge parameters for the two source points from the edge cover.
  have hxcover : x ∈ ⋃ i, G.edgeSet i := by
    rw [G.iUnion_edgeSet]
    exact Set.mem_univ x
  have hycover : y ∈ ⋃ i, G.edgeSet i := by
    rw [G.iUnion_edgeSet]
    exact Set.mem_univ y
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hycover
  obtain ⟨t, rfl⟩ := hi
  obtain ⟨s, rfl⟩ := hj
  by_cases hij : i = j
  · -- On one edge, the affine line map and the edge parameterization are injective.
    subst j
    have hedge : G.edge i 0 ≠ G.edge i 1 := by
      intro h
      exact zero_ne_one ((G.edgeEmbedding i).injective h)
    have hz_ne : z (G.edge i 0) ≠ z (G.edge i 1) := by
      intro h
      exact hedge (hz_inj (G.endpoint_mem_vertexSet i 0 (Or.inl rfl))
        (G.endpoint_mem_vertexSet i 1 (Or.inr rfl)) h)
    have hts : (t : ℝ) = (s : ℝ) := (AffineMap.lineMap_injective ℝ hz_ne) (by
      rw [← hf i t, ← hf i s]
      exact hxy)
    exact congrArg (G.edge i) (Subtype.ext hts)
  · -- Distinct edge images can meet only at their unique common endpoint.
    have hleft : f (G.edge i t) ∈
        convexHull ℝ
          ((Finset.image z ({G.edge i 0, G.edge i 1} : Finset X) : Finset _) : Set _) := by
      rw [hf]
      simpa only [Finset.coe_image, Finset.coe_pair, Set.image_insert_eq,
        Set.image_singleton, convexHull_pair] using
        lineMap_mem_segment ℝ (z (G.edge i 0)) (z (G.edge i 1)) t.property
    have hright : f (G.edge i t) ∈
        convexHull ℝ
          ((Finset.image z ({G.edge j 0, G.edge j 1} : Finset X) : Finset _) : Set _) := by
      rw [hxy, hf]
      simpa only [Finset.coe_image, Finset.coe_pair, Set.image_insert_eq,
        Set.image_singleton, convexHull_pair] using
        lineMap_mem_segment ℝ (z (G.edge j 0)) (z (G.edge j 1)) s.property
    have hcommonHull : f (G.edge i t) ∈ convexHull ℝ
        ((Finset.image z
          (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1}) : Finset X) : Finset _) :
          Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [G.endpointConvexHulls_inter hz_inj hz_gp i j]
      exact ⟨hleft, hright⟩
    have hsourceSubsingleton :
        (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1} : Finset X) :
          Set X).Subsingleton := by
      -- Common endpoints form a subset of the subsingleton intersection of the edge images.
      intro p hp q hq
      apply G.inter_subsingleton hij
      · constructor
        · obtain hp0 | hp1 := by
            simpa only [Finset.mem_insert, Finset.mem_singleton] using
              (Finset.mem_inter.mp hp).1
          · exact ⟨0, hp0.symm⟩
          · exact ⟨1, hp1.symm⟩
        · obtain hp0 | hp1 := by
            simpa only [Finset.mem_insert, Finset.mem_singleton] using
              (Finset.mem_inter.mp hp).2
          · exact ⟨0, hp0.symm⟩
          · exact ⟨1, hp1.symm⟩
      · constructor
        · obtain hq0 | hq1 := by
            simpa only [Finset.mem_insert, Finset.mem_singleton] using
              (Finset.mem_inter.mp hq).1
          · exact ⟨0, hq0.symm⟩
          · exact ⟨1, hq1.symm⟩
        · obtain hq0 | hq1 := by
            simpa only [Finset.mem_insert, Finset.mem_singleton] using
              (Finset.mem_inter.mp hq).2
          · exact ⟨0, hq0.symm⟩
          · exact ⟨1, hq1.symm⟩
    have hcoordinateSubsingleton :
        (((Finset.image z
          (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1}) : Finset X) : Finset _) :
          Set (EuclideanSpace ℝ (Fin 3)))).Subsingleton := by
      simpa only [Finset.coe_image] using hsourceSubsingleton.image z
    have hconvexHull_eq : convexHull ℝ
        ((Finset.image z
          (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1}) : Finset X) : Finset _) :
          Set (EuclideanSpace ℝ (Fin 3))) =
        ((Finset.image z
          (({G.edge i 0, G.edge i 1} ∩ {G.edge j 0, G.edge j 1}) : Finset X) : Finset _) :
          Set (EuclideanSpace ℝ (Fin 3))) := by
      -- A subsingleton set is convex, so taking its convex hull changes nothing.
      apply Set.Subset.antisymm
      · exact convexHull_min subset_rfl hcoordinateSubsingleton.convex
      · exact subset_convexHull ℝ _
    rw [hconvexHull_eq] at hcommonHull
    obtain ⟨p, hp, hzp⟩ := Finset.mem_image.mp hcommonHull
    have hp_i : p = G.edge i 0 ∨ p = G.edge i 1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using (Finset.mem_inter.mp hp).1
    have hp_j : p = G.edge j 0 ∨ p = G.edge j 1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using (Finset.mem_inter.mp hp).2
    have hxp : G.edge i t = p :=
      G.edgePoint_eq_endpoint_of_image_eq hz_inj hf i t p hp_i (hzp ▸ rfl)
    have hyp : G.edge j s = p :=
      G.edgePoint_eq_endpoint_of_image_eq hz_inj hf j s p hp_j (by
        rw [← hxy]
        exact hzp.symm)
    exact hxp.trans hyp.symm

/-- Example 50.7. Every finite linear graph embeds in `EuclideanSpace ℝ (Fin 3)`. -/
theorem exists_isEmbedding_euclideanThree
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (G : FiniteLinearGraph.{u, v} X) :
    ∃ f : X → EuclideanSpace ℝ (Fin 3), Topology.IsEmbedding f := by
  classical
  -- Choose general-position vertex coordinates and glue the corresponding affine edge maps.
  obtain ⟨z, hz_inj, hz_gp⟩ := G.exists_vertexMap_generalPosition
  obtain ⟨f, hcont, hf⟩ := G.exists_continuous_edgewiseLineMap z
  have hinj : Function.Injective f := G.edgewiseLineMap_injective hz_inj hz_gp hf
  -- The finitely many compact edge images make the graph compact.
  letI : Finite G.Edge := G.edgeFinite
  have hcompact : IsCompact (Set.univ : Set X) := by
    rw [← G.iUnion_edgeSet]
    exact isCompact_iUnion fun i ↦ isCompact_range (G.edgeEmbedding i).continuous
  letI : CompactSpace X := isCompact_univ_iff.mp hcompact
  -- A continuous injection from a compact space to Euclidean space is an embedding.
  exact ⟨f, (hcont.isClosedEmbedding hinj).isEmbedding⟩

end FiniteLinearGraph
