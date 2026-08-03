module

public import Topology_Munkres_2000.Book.Definition_50_7.GeneralPosition
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos

public section

namespace Lemma50_4

open MeasureTheory

/-- Helper for Lemma 50.4: at most `N` points in `N`-dimensional Euclidean
space have proper affine span. -/
lemma affineSpan_image_finset_ne_top_of_card_le
    {ι : Type*} {N : ℕ} (z : ι → EuclideanSpace ℝ (Fin N))
    (u : Finset ι) (hu : u.card ≤ N) :
    affineSpan ℝ (u.image z : Set (EuclideanSpace ℝ (Fin N))) ≠ ⊤ := by
  classical
  -- The empty family has empty affine span, so it cannot fill Euclidean space.
  by_cases hzero : u.card = 0
  · have hu_empty : u = ∅ := Finset.card_eq_zero.mp hzero
    simp [hu_empty]
  · obtain ⟨n, hn⟩ : ∃ n, u.card = n + 1 := by
      exact ⟨u.card - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hzero)).symm⟩
    -- A nonempty family spans at most one fewer vector dimensions than points.
    intro htop
    have hrank_le : Module.finrank ℝ
        (vectorSpan ℝ (u.image z : Set (EuclideanSpace ℝ (Fin N)))) ≤ n :=
      finrank_vectorSpan_image_finset_le ℝ z u hn
    have hvector_top :
        vectorSpan ℝ (u.image z : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
      rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
    have hN_le_n : N ≤ n := by
      rw [hvector_top, finrank_top, finrank_euclideanSpace_fin] at hrank_le
      exact hrank_le
    omega

/-- Helper for Lemma 50.4: every positive-radius ball contains a point outside
the affine spans of all small subfamilies of a fixed finite family. -/
lemma exists_mem_ball_avoiding_small_affineSpans
    {ι : Type*} {N : ℕ} (z : ι → EuclideanSpace ℝ (Fin N))
    (s : Finset ι) (c : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ Metric.ball c ε, ∀ u : Finset ι, u ⊆ s → u.card ≤ N →
      p ∉ affineSpan ℝ (u.image z : Set (EuclideanSpace ℝ (Fin N))) := by
  classical
  let candidates := s.powerset.filter fun u ↦ u.card ≤ N
  let forbidden : Set (EuclideanSpace ℝ (Fin N)) :=
    ⋃ u : {u // u ∈ candidates},
      (affineSpan ℝ (u.1.image z : Set (EuclideanSpace ℝ (Fin N))) : Set _)
  let μ : Measure (EuclideanSpace ℝ (Fin N)) :=
    (Module.finBasis ℝ (EuclideanSpace ℝ (Fin N))).addHaar
  -- Proper candidate spans are Haar-null, hence so is their finite union.
  have hforbidden_zero : μ forbidden = 0 := by
    unfold forbidden
    apply measure_iUnion_null
    intro u
    exact Measure.addHaar_affineSubspace μ _
      (affineSpan_image_finset_ne_top_of_card_le z u.1
        (Finset.mem_filter.mp u.2).2)
  -- A positive-measure ball cannot be contained in the null forbidden union.
  have hnot_subset : ¬ Metric.ball c ε ⊆ forbidden := by
    intro hsubset
    have hmono : μ (Metric.ball c ε) ≤ μ forbidden := measure_mono hsubset
    rw [hforbidden_zero] at hmono
    exact (not_lt_of_ge hmono) (Metric.measure_ball_pos μ c hε)
  obtain ⟨p, hp_ball, hp_forbidden⟩ := Set.not_subset.mp hnot_subset
  refine ⟨p, hp_ball, ?_⟩
  intro u hus hcard hp_span
  -- Register the small subfamily as a candidate before entering the union.
  have hu_candidate : u ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hus, hcard⟩
  let candidate : {u // u ∈ candidates} := ⟨u, hu_candidate⟩
  apply hp_forbidden
  exact Set.mem_iUnion.mpr ⟨candidate, hp_span⟩

open scoped Classical in
/-- Helper for Lemma 50.4: adjoining a fresh updated point outside the old
affine span preserves affine independence on the enlarged finset. -/
lemma affineIndependent_insert_update
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : ι → E} {s : Finset ι} {i : ι} {p : E}
    (hi : i ∉ s)
    (hs : AffineIndependent ℝ (fun j : {j // j ∈ s} ↦ z j.1))
    (hp : p ∉ affineSpan ℝ (Set.image z (s : Set ι))) :
    AffineIndependent ℝ
      (fun j : {j // j ∈ insert i s} ↦ Function.update z i p j.1) := by
  classical
  let inserted : {j // j ∈ insert i s} := ⟨i, Finset.mem_insert_self i s⟩
  -- Build the equivalence between old indices and all enlarged indices except
  -- the freshly inserted one, keeping its proof fields separate from the term.
  have oldToFun_ne (j : {j // j ∈ s}) :
      (⟨j.1, Finset.mem_insert_of_mem j.2⟩ : {j // j ∈ insert i s}) ≠ inserted := by
    intro h
    have hji : j.1 = i := congrArg Subtype.val h
    exact hi (hji ▸ j.2)
  let oldToFun : {j // j ∈ s} →
      {j : {j // j ∈ insert i s} // j ≠ inserted} :=
    fun j ↦ ⟨⟨j.1, Finset.mem_insert_of_mem j.2⟩, oldToFun_ne j⟩
  have oldInvFun_mem (j : {j : {j // j ∈ insert i s} // j ≠ inserted}) :
      j.1.1 ∈ s := by
    have hj := Finset.mem_insert.mp j.1.2
    exact hj.resolve_left fun h ↦ j.2 (Subtype.ext h)
  let oldInvFun : {j : {j // j ∈ insert i s} // j ≠ inserted} → {j // j ∈ s} :=
    fun j ↦ ⟨j.1.1, oldInvFun_mem j⟩
  have old_leftInverse : Function.LeftInverse oldInvFun oldToFun := by
    intro j
    apply Subtype.ext
    rfl
  have old_rightInverse : Function.RightInverse oldInvFun oldToFun := by
    intro j
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let oldEquiv : {j // j ∈ s} ≃
      {j : {j // j ∈ insert i s} // j ≠ inserted} :=
    ⟨oldToFun, oldInvFun, old_leftInverse, old_rightInverse⟩
  let family : {j // j ∈ insert i s} → E :=
    fun j ↦ Function.update z i p j.1
  -- Transport old affine independence across the equivalence of old indices.
  have hold : AffineIndependent ℝ
      (fun j : {j : {j // j ∈ insert i s} // j ≠ inserted} ↦ family j.1) := by
    rw [← affineIndependent_equiv oldEquiv]
    convert hs using 1
    ext j
    simp only [Function.comp_apply, family, oldEquiv, oldToFun]
    apply Function.update_of_ne
    intro hji
    exact hi (hji.symm ▸ j.2)
  have himage : family '' {j | j ≠ inserted} = Set.image z (s : Set ι) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj_old : j.1 ∈ s := by
        have hj_insert := Finset.mem_insert.mp j.2
        exact hj_insert.resolve_left fun h ↦ hj (Subtype.ext h)
      refine ⟨j.1, hj_old, ?_⟩
      unfold family
      rw [Function.update_of_ne]
      exact fun h ↦ hi (h ▸ hj_old)
    · rintro ⟨j, hjs, rfl⟩
      let j' : {j // j ∈ insert i s} := ⟨j, Finset.mem_insert_of_mem hjs⟩
      have hj'_ne : j' ≠ inserted := by
        intro h
        have hji : j = i := congrArg Subtype.val h
        exact hi (hji ▸ hjs)
      refine ⟨j', hj'_ne, ?_⟩
      unfold family
      rw [Function.update_of_ne]
      exact fun h ↦ hi (h ▸ hjs)
  -- The standard all-but-one extension theorem now adjoins the new point.
  apply AffineIndependent.affineIndependent_of_notMem_span hold
  rw [himage]
  simpa [family, inserted] using hp

/-- Helper for Lemma 50.4: a finite Euclidean family admits a pointwise small
perturbation whose subfamilies of size at most the ambient dimension plus one
are affinely independent. -/
lemma existsNearbyBoundedAffineIndependentFamily
    {ι : Type*} [Finite ι] {N : ℕ}
    (v : ι → EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ι → EuclideanSpace ℝ (Fin N),
      (∀ i, dist (z i) (v i) < ε) ∧
      ∀ t : Finset ι, t.card ≤ N + 1 →
        AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1) := by
  letI := Fintype.ofFinite ι
  classical
  -- Induct over processed indices while retaining closeness and affine
  -- independence for every sufficiently small processed subfamily.
  have invariant : ∀ s : Finset ι,
      ∃ z : ι → EuclideanSpace ℝ (Fin N),
        (∀ i ∈ s, dist (z i) (v i) < ε) ∧
        ∀ t : Finset ι, t ⊆ s → t.card ≤ N + 1 →
          AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨v, ?_, ?_⟩
        · intro i hi
          exact (Finset.notMem_empty i hi).elim
        · intro t ht _
          have ht_empty : t = ∅ := Finset.subset_empty.mp ht
          subst t
          exact affineIndependent_of_subsingleton ℝ _
    | @insert i s hi ih =>
        obtain ⟨z, hz_close, hz_independent⟩ := ih
        obtain ⟨p, hp_ball, hp_avoid⟩ :=
          exists_mem_ball_avoiding_small_affineSpans z s (v i) hε
        let z' : ι → EuclideanSpace ℝ (Fin N) := Function.update z i p
        refine ⟨z', ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · simpa [z'] using Metric.mem_ball.mp hp_ball
          · have hji : j ≠ i := fun h ↦ hi (h ▸ hjs)
            simpa [z', Function.update_of_ne hji] using hz_close j hjs
        · intro t ht hcard
          by_cases hit : i ∈ t
          · let u := t.erase i
            have hu_subset : u ⊆ s := by
              intro j hju
              have hjt : j ∈ t := Finset.mem_of_mem_erase hju
              have hji : j ≠ i := Finset.ne_of_mem_erase hju
              exact (Finset.mem_insert.mp (ht hjt)).resolve_left hji
            have hu_card_add_one : u.card + 1 = t.card :=
              Finset.card_erase_add_one hit
            have hu_card : u.card ≤ N := by omega
            have hu_card_succ : u.card ≤ N + 1 := by omega
            have hu_independent := hz_independent u hu_subset hu_card_succ
            have hp_span : p ∉ affineSpan ℝ (Set.image z (u : Set ι)) := by
              simpa only [Finset.coe_image] using hp_avoid u hu_subset hu_card
            have hinsert := affineIndependent_insert_update
              (Finset.notMem_erase i t) hu_independent hp_span
            have ht_eq : insert i u = t := Finset.insert_erase hit
            rw [← ht_eq]
            simpa [z', u] using hinsert
          · have ht_subset : t ⊆ s := by
              intro j hjt
              exact (Finset.mem_insert.mp (ht hjt)).resolve_left fun h ↦ hit (h ▸ hjt)
            have ht_independent := hz_independent t ht_subset hcard
            convert ht_independent using 1
            ext j
            simp only [z']
            rw [Function.update_of_ne]
            exact fun h ↦ hit (h ▸ j.2)
  obtain ⟨z, hz_close, hz_independent⟩ := invariant Finset.univ
  refine ⟨z, ?_, ?_⟩
  · intro i
    exact hz_close i (Finset.mem_univ i)
  · intro t hcard
    exact hz_independent t (Finset.subset_univ t) hcard

/-- Helper for Lemma 50.4: bounded affine independence of indexed subfamilies
implies general position of the family's range. -/
lemma inGeneralPosition_range_of_boundedAffineIndependent
    {ι : Type*} {N : ℕ} (z : ι → EuclideanSpace ℝ (Fin N))
    (haff : ∀ t : Finset ι, t.card ≤ N + 1 →
      AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1)) :
    (Set.range z).InGeneralPosition := by
  classical
  rw [Set.inGeneralPosition_iff]
  intro s hs hcard
  -- Choose one source index for each distinct point of the finite target set.
  let preimage : s → ι := fun p ↦ (hs p.2).choose
  have preimage_spec (p : s) : z (preimage p) = p :=
    (hs p.2).choose_spec
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
  let intoT : s → {i // i ∈ t} :=
    fun p ↦ ⟨preimageEmbedding p, preimage_mem p⟩
  have intoT_injective : Function.Injective intoT := by
    intro p q hpq
    exact preimageEmbedding.injective (congrArg Subtype.val hpq)
  let intoTEmbedding : s ↪ {i // i ∈ t} := ⟨intoT, intoT_injective⟩
  have intoTEmbedding_val (p : s) : (intoTEmbedding p).1 = preimage p := by
    rfl
  -- Pull affine independence back along the chosen-preimage embedding.
  have hpulled := (haff t ht_bound).comp_embedding intoTEmbedding
  convert hpulled using 1
  apply funext
  intro p
  rw [Function.comp_apply, intoTEmbedding_val]
  exact (preimage_spec p).symm

end Lemma50_4

/-- Lemma 50.4. Given a family of points in `EuclideanSpace ℝ (Fin N)` indexed by a
finite type and `0 < δ`, there is a pointwise `δ`-close family whose range is in general
position. -/
theorem existsGeneralPositionNear {N : ℕ} {ι : Type*} [Finite ι]
    (x : ι → EuclideanSpace ℝ (Fin N)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : ι → EuclideanSpace ℝ (Fin N),
      (Set.range y).InGeneralPosition ∧ ∀ i, dist (x i) (y i) < δ := by
  -- First perturb the indexed family while controlling every small subfamily.
  obtain ⟨y, hy_close, hy_independent⟩ :=
    Lemma50_4.existsNearbyBoundedAffineIndependentFamily x hδ
  refine ⟨y, Lemma50_4.inGeneralPosition_range_of_boundedAffineIndependent
    y hy_independent, ?_⟩
  -- Reverse the helper's distance orientation to match the textbook statement.
  intro i
  simpa only [dist_comm] using hy_close i
