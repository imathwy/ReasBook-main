module

public import Topology_Munkres_2000.Book.Definition_50_7.GeneralPosition
public import Mathlib.Analysis.Convex.Combination

public section

open Set

/-- The five vertices used for the straight-line drawing of the complete graph on five
vertices: the origin, the three standard basis vectors, and the all-ones vector in `ℝ³`. -/
noncomputable def kFivePosition : Fin 5 → EuclideanSpace ℝ (Fin 3) :=
  Fin.cases 0
    (Fin.cases (EuclideanSpace.single 0 1)
      (Fin.cases (EuclideanSpace.single 1 1)
        (Fin.cases (EuclideanSpace.single 2 1)
          (fun _ : Fin 1 ↦ EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 +
            EuclideanSpace.single 2 1))))

/-- Helper for Exercise 50.4: every affine relation among the five specified points has
coefficients determined by its coefficient at the all-ones point. -/
lemma kFivePosition_affineRelation_normalForm (w : Fin 5 → ℝ)
    (hsum : ∑ i, w i = 0) (hlinear : ∑ i, w i • kFivePosition i = 0) :
    w = ![2 * w 4, -w 4, -w 4, -w 4, w 4] := by
  -- Reading the vector relation coordinatewise determines the three middle weights.
  have hcoordinate₀ :=
    congrArg (fun x ↦ (EuclideanSpace.equiv (Fin 3) ℝ x) 0) hlinear
  have hcoordinate₁ :=
    congrArg (fun x ↦ (EuclideanSpace.equiv (Fin 3) ℝ x) 1) hlinear
  have hcoordinate₂ :=
    congrArg (fun x ↦ (EuclideanSpace.equiv (Fin 3) ℝ x) 2) hlinear
  simp [kFivePosition, Fin.sum_univ_succ] at hcoordinate₀ hcoordinate₁ hcoordinate₂
  -- The zero-sum condition then determines the remaining origin coefficient.
  simp [Fin.sum_univ_succ] at hsum
  funext i
  fin_cases i <;> simp <;> linarith

/-- Helper for Exercise 50.4: restricting the five specified points to at most four
indices gives an affinely independent family. -/
lemma kFivePosition_restrict_affineIndependent (s : Finset (Fin 5)) (hs : s.card ≤ 4) :
    AffineIndependent ℝ (fun i : s ↦ kFivePosition i) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hsum hweighted
  -- Extend a relation on the chosen subfamily by zero to all five indices.
  let w' : Fin 5 → ℝ := fun i ↦ if hi : i ∈ s then w ⟨i, hi⟩ else 0
  have hlinear : ∑ i : s, w i • kFivePosition i = 0 := by
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hweighted
    simpa using hweighted
  have hsum' : ∑ i, w' i = 0 := by
    calc
      ∑ i, w' i = ∑ i ∈ s, w' i := by
        symm
        exact Finset.sum_subset (Finset.subset_univ s) (by
          intro i _ hi
          simp [w', hi])
      _ = ∑ i : s, w i := by
        rw [← Finset.sum_attach]
        simp [w']
      _ = 0 := hsum
  have hlinear' : ∑ i, w' i • kFivePosition i = 0 := by
    calc
      ∑ i, w' i • kFivePosition i = ∑ i ∈ s, w' i • kFivePosition i := by
        symm
        exact Finset.sum_subset (Finset.subset_univ s) (by
          intro i _ hi
          simp [w', hi])
      _ = ∑ i : s, w i • kFivePosition i := by
        rw [← Finset.sum_attach]
        simp [w']
      _ = 0 := hlinear
  have hnormal := kFivePosition_affineRelation_normalForm w' hsum' hlinear'
  -- Since at least one index is omitted, the normal form's common parameter vanishes.
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, i ∉ s := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hs_univ : s = Finset.univ := Finset.eq_univ_of_forall h
    rw [hs_univ] at hs
    norm_num at hs
  have hi_zero : w' i = 0 := by
    simp [w', hi]
  have hw_four : w' 4 = 0 := by
    rw [hnormal] at hi_zero
    fin_cases i <;> simp at hi_zero ⊢ <;> linarith
  have hw'_zero : w' = 0 := by
    rw [hnormal, hw_four]
    funext i
    fin_cases i <;> simp
  -- Every original coefficient is therefore zero.
  intro j
  have hw'_eq : w' j = w j := by
    simp [w', j.property]
  rw [← hw'_eq, hw'_zero]
  rfl

/-- Helper for Exercise 50.4: bounded affine independence of indexed subfamilies implies
general position of the family's range. -/
lemma range_inGeneralPosition_of_boundedAffineIndependent
    {ι : Type*} {N : ℕ} (z : ι → EuclideanSpace ℝ (Fin N))
    (haff : ∀ t : Finset ι, t.card ≤ N + 1 →
      AffineIndependent ℝ (fun i : t ↦ z i)) :
    (range z).InGeneralPosition := by
  classical
  rw [inGeneralPosition_iff]
  intro s hs hcard
  -- Choose one source index for each distinct point in the finite target subset.
  let preimage : s → ι := fun p ↦ (hs p.property).choose
  have preimage_spec (p : s) : z (preimage p) = p :=
    (hs p.property).choose_spec
  have preimage_injective : Function.Injective preimage := by
    intro p q hpq
    apply Subtype.ext
    calc
      (p : EuclideanSpace ℝ (Fin N)) = z (preimage p) := (preimage_spec p).symm
      _ = z (preimage q) := congrArg z hpq
      _ = (q : EuclideanSpace ℝ (Fin N)) := preimage_spec q
  let preimageEmbedding : s ↪ ι := ⟨preimage, preimage_injective⟩
  let t : Finset ι := Finset.univ.map preimageEmbedding
  have ht_card : t.card = s.card := by
    simp [t]
  have ht_bound : t.card ≤ N + 1 := ht_card.trans_le hcard
  have preimage_mem (p : s) : preimageEmbedding p ∈ t := by
    unfold t
    exact Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩
  let intoT : s → t := fun p ↦ ⟨preimageEmbedding p, preimage_mem p⟩
  have intoT_injective : Function.Injective intoT := by
    intro p q hpq
    exact preimageEmbedding.injective (congrArg Subtype.val hpq)
  let intoTEmbedding : s ↪ t := ⟨intoT, intoT_injective⟩
  have intoTEmbedding_val (p : s) : (intoTEmbedding p).1 = preimage p := by
    rfl
  -- Pull independence back along the embedding formed by the chosen preimages.
  have hpulled := (haff t ht_bound).comp_embedding intoTEmbedding
  convert hpulled using 1
  apply funext
  intro p
  rw [Function.comp_apply, intoTEmbedding_val]
  exact (preimage_spec p).symm

/-- Exercise 50.4 (1): The five specified points in `ℝ³` are in general position. -/
theorem kFivePosition_inGeneralPosition :
    (range kFivePosition).InGeneralPosition := by
  -- Transfer the verified bound on indexed subfamilies to finite subsets of the range.
  apply range_inGeneralPosition_of_boundedAffineIndependent kFivePosition
  intro s hs
  have hs_four : s.card ≤ 4 := by
    omega
  exact kFivePosition_restrict_affineIndependent s hs_four

/-- Every subfamily of at most four of the five specified points is affinely independent. -/
theorem kFivePosition_affineIndependent (s : Finset (Fin 5)) (hs : s.card ≤ 4) :
    AffineIndependent ℝ (fun i : s ↦ kFivePosition i) := by
  -- This is exactly the restricted-family conclusion proved from the relation normal form.
  exact kFivePosition_restrict_affineIndependent s hs

/-- Helper for Exercise 50.4: affine independence of a finset-indexed restriction passes
to the coercion family of its image finset. -/
lemma finsetImage_affineIndependent
    {k V P ι : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    [DecidableEq P] (s : Finset ι) (z : ι → P)
    (hsource : AffineIndependent k (fun i : s ↦ z i)) :
    AffineIndependent k ((↑) : ↥(s.image z) → P) := by
  -- Identify the range of the restricted family with the coerced image finset.
  have hrange : range (fun i : s ↦ z i) = ((s.image z : Finset P) : Set P) := by
    ext y
    simp only [mem_range, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : range (fun i : s ↦ z i) ≃ ((s.image z : Finset P) : Set P) :=
    Equiv.setCongr hrange
  have hcomp : (fun x : range (fun i : s ↦ z i) ↦ (x : P)) =
      ((fun x : ↥(s.image z) ↦ (x : P)) ∘ e) := by
    funext x
    rfl
  -- Reindex the independent range family along this set equivalence.
  apply (affineIndependent_equiv e).mp
  rw [← hcomp]
  exact hsource.range

/-- Exercise 50.4 (2): Regarding two-element finsets as the edges of
`SimpleGraph.completeGraph (Fin 5)`, their straight segments meet exactly along the convex
hull of their shared endpoints. -/
theorem kFivePosition_edge_inter (e₁ e₂ : Finset (Fin 5))
    (he₁ : e₁.card = 2) (he₂ : e₂.card = 2) :
    convexHull ℝ (kFivePosition '' (e₁ : Set (Fin 5))) ∩
        convexHull ℝ (kFivePosition '' (e₂ : Set (Fin 5))) =
      convexHull ℝ (kFivePosition '' (e₁ ∩ e₂ : Set (Fin 5))) := by
  classical
  let endpoints : Finset (Fin 5) := e₁ ∪ e₂
  have hsum_card : e₁.card + e₂.card = 4 := by
    omega
  have hcard : endpoints.card ≤ 4 := by
    calc
      endpoints.card ≤ e₁.card + e₂.card := Finset.card_union_le _ _
      _ = 4 := hsum_card
  -- The endpoint union is an affinely independent simplex containing both edges.
  have hsource : AffineIndependent ℝ (fun i : endpoints ↦ kFivePosition i) :=
    kFivePosition_restrict_affineIndependent endpoints hcard
  have himage : AffineIndependent ℝ
      ((↑) : ↥(endpoints.image kFivePosition) → EuclideanSpace ℝ (Fin 3)) :=
    finsetImage_affineIndependent endpoints kFivePosition hsource
  have hinj : Set.InjOn kFivePosition (endpoints : Set (Fin 5)) := by
    intro x hx y hy hxy
    have hsubtype : (⟨x, hx⟩ : endpoints) = ⟨y, hy⟩ :=
      hsource.injective hxy
    exact congrArg Subtype.val hsubtype
  have himage_inter :
      Finset.image kFivePosition (e₁ ∩ e₂) =
        Finset.image kFivePosition e₁ ∩ Finset.image kFivePosition e₂ := by
    have hinj_union : Set.InjOn kFivePosition
        (((e₁ : Set (Fin 5)) ∪ (e₂ : Set (Fin 5)))) := by
      simpa only [endpoints, Finset.coe_union] using hinj
    exact Finset.image_inter_of_injOn e₁ e₂ hinj_union
  have he₁_subset : e₁.image kFivePosition ⊆ endpoints.image kFivePosition :=
    Finset.image_mono kFivePosition Finset.subset_union_left
  have he₂_subset : e₂.image kFivePosition ⊆ endpoints.image kFivePosition :=
    Finset.image_mono kFivePosition Finset.subset_union_right
  have hfinset :
      convexHull ℝ ((Finset.image kFivePosition (e₁ ∩ e₂) : Finset _) :
          Set (EuclideanSpace ℝ (Fin 3))) =
        convexHull ℝ ((Finset.image kFivePosition e₁ : Finset _) : Set _) ∩
          convexHull ℝ ((Finset.image kFivePosition e₂ : Finset _) : Set _) := by
    -- The simplex intersection theorem computes the overlap inside the endpoint union.
    rw [himage_inter]
    simpa only [Finset.coe_inter] using himage.convexHull_inter he₁_subset he₂_subset
  -- Translate the finset computation back to the source-facing set-image formulation.
  symm
  simpa only [Finset.coe_image, Finset.coe_inter] using hfinset
