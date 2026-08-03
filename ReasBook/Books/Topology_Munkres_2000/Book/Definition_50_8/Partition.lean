module

public import Topology_Munkres_2000.Book.Corollary_50_3
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Exercise_36_4.Shrinking
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.UrysohnsLemma

public section

open Set TopologicalSpace

universe u

/-- Helper for Definition 50.8: the frontier of a finite union is contained in the union of
the individual frontiers. -/
lemma frontier_biUnion_finset_subset
    {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (U : ι → Set X) :
    frontier (⋃ i ∈ s, U i) ⊆ ⋃ i ∈ s, frontier (U i) := by
  -- Add one set at a time and use the binary frontier inclusion.
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.set_biUnion_insert]
      exact (frontier_union_subset (U i) (⋃ j ∈ s, U j)).trans <|
        (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right).trans
          (Set.union_subset_union_right _ ih)

/-- Helper for Definition 50.8: an order-bounded open refinement of a compact metrizable
space can be represented by finitely many indexed opens together with a closure-controlled
shrinking and explicit parents in the original cover. -/
lemma existsFiniteIndexedShrinkingRefinement
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) (𝒜 : Set (Set X))
    (h𝒜open : ∀ U ∈ 𝒜, IsOpen U) (h𝒜cover : ⋃₀ 𝒜 = Set.univ) :
    ∃ (ι : Type u) (_ : Finite ι) (B C : ι → Opens X) (p : ι → 𝒜),
      IsOpenCover B ∧ IsOpenCover C ∧
        (Set.range (fun i ↦ (B i : Set X))).HasOrderLE (n + 1) ∧
        Function.Injective (fun i ↦ (B i : Set X)) ∧
        (∀ i, (B i : Set X) ⊆ p i) ∧
        ∀ i, closure (C i : Set X) ⊆ B i := by
  classical
  -- First obtain an order-bounded open refinement, then retain a finite subcover.
  obtain ⟨ℬ, hℬrefines, hℬcover, hℬorder⟩ :=
    (hasCoveringDimensionLE_iff_pointwise X n).mp h 𝒜 h𝒜open h𝒜cover
  have hℬopen : ∀ U ∈ ℬ, IsOpen U :=
    (isOpenRefinement_iff.mp hℬrefines).2
  have hsubcover : Set.univ ⊆ ⋃ U : ℬ, U.1 := by
    intro x _
    have hx : x ∈ ⋃₀ ℬ := hℬcover.symm ▸ Set.mem_univ x
    rw [Set.mem_sUnion] at hx
    obtain ⟨U, hUℬ, hxU⟩ := hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hUℬ⟩, hxU⟩
  obtain ⟨t, htcover⟩ := isCompact_univ.elim_finite_subcover
    (fun U : ℬ ↦ U.1) (fun U ↦ hℬopen U.1 U.2) hsubcover
  -- Index by the selected refinement members, preserving their membership proofs.
  let ι := {U : ℬ // U ∈ t}
  letI : Finite ι := Finite.of_fintype ι
  let B : ι → Opens X := fun i ↦ ⟨i.1.1, hℬopen i.1.1 i.1.2⟩
  have hBcover : IsOpenCover B := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ U ∈ t, U.1 := htcover (Set.mem_univ x)
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨U, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hUt, hxU⟩ := hx
    exact ⟨⟨U, hUt⟩, hxU⟩
  have hBorder : Set.range (fun i ↦ (B i : Set X)) |>.HasOrderLE (n + 1) := by
    -- Passing to a finite subfamily can only decrease point multiplicity.
    rw [Set.hasOrderLE_iff]
    intro x
    apply (Set.encard_le_encard ?_).trans (hℬorder x)
    rintro U ⟨⟨i, rfl⟩, hxU⟩
    exact ⟨i.1.2, hxU⟩
  -- Choose an original-cover parent for each retained refinement member.
  have hparent (i : ι) : ∃ A : 𝒜, (B i : Set X) ⊆ A := by
    obtain ⟨A, hA𝒜, hBA⟩ := hℬrefines.subset_of_mem i.1.2
    exact ⟨⟨A, hA𝒜⟩, hBA⟩
  choose p hp using hparent
  -- Normality provides an indexed shrinking whose closures remain in the selected opens.
  have hBfinite : PointFinite (fun i ↦ (B i : Set X)) := by
    rw [pointFinite_iff]
    intro x
    exact Set.toFinite _
  obtain ⟨C, hCcover, hCclosure⟩ := hBcover.exists_shrinking hBfinite
  have hBinjective : Function.Injective (fun i ↦ (B i : Set X)) := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact hij
  exact ⟨ι, inferInstance, B, C, p, hBcover, hCcover, hBorder, hBinjective, hp, hCclosure⟩

/-- Helper for Definition 50.8: a real-valued map has a buffered fine zero cover of order
`q` when one finite open family has order at most `q` throughout a neighborhood of its zero
fiber and all of its members have diameter less than `δ`. -/
def HasBufferedFineZeroCover {X : Type*} [PseudoMetricSpace X]
    (f : C(X, ℝ)) (q : ℕ) (δ : ℝ) : Prop :=
  ∃ ε > 0, ∃ 𝒰 : Set (Set X),
    𝒰.Finite ∧
      (∀ U ∈ 𝒰, IsOpen U) ∧
      (∀ x, |f x| < ε → x ∈ ⋃₀ 𝒰) ∧
      (∀ x, |f x| < ε → Set.encard {U ∈ 𝒰 | x ∈ U} ≤ q) ∧
      ∀ U ∈ 𝒰, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ

/-- Helper for Definition 50.8: buffered fine zero covers persist under sufficiently small
uniform perturbations of the real-valued map. -/
lemma isOpen_setOf_hasBufferedFineZeroCover
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] (q : ℕ) (δ : ℝ) :
    IsOpen {f : C(X, ℝ) | HasBufferedFineZeroCover f q δ} := by
  rw [isOpen_iff_mem_nhds]
  intro f hf
  obtain ⟨ε, hε, 𝒰, h𝒰finite, h𝒰open, h𝒰cover, h𝒰order, h𝒰diameter⟩ := hf
  apply Filter.mem_of_superset (Metric.ball_mem_nhds f (half_pos hε))
  intro g hg
  refine ⟨ε / 2, half_pos hε, 𝒰, h𝒰finite, h𝒰open, ?_, ?_, h𝒰diameter⟩
  · intro x hx
    apply h𝒰cover x
    have hdist : dist (g x) (f x) < ε / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hg)
    have hdistAbs : |f x - g x| < ε / 2 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist
    calc
      |f x| ≤ |f x - g x| + |g x| := by
        nth_rw 1 [← sub_add_cancel (f x) (g x)]
        exact abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdistAbs hx
      _ = ε := by ring
  · intro x hx
    apply h𝒰order x
    have hdist : dist (g x) (f x) < ε / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hg)
    have hdistAbs : |f x - g x| < ε / 2 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hdist
    calc
      |f x| ≤ |f x - g x| + |g x| := by
        nth_rw 1 [← sub_add_cancel (f x) (g x)]
        exact abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdistAbs hx
      _ = ε := by ring

/-- Helper for Definition 50.8: a convex weighted average remains uniformly close to a point
when every vertex carrying nonzero weight is uniformly close to that point. -/
lemma dist_weightedSum_lt
    {ι : Type*} [Fintype ι] (w z : ι → ℝ) (p : ℝ) {r : ℝ}
    (hw_nonnegative : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hz : ∀ i, w i ≠ 0 → dist (z i) p < r) :
    dist (∑ i, w i * z i) p < r := by
  classical
  have hpositive : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have hzero : ∀ i, w i = 0 := fun i ↦ (h i).antisymm (hw_nonnegative i)
    simp only [hzero, Finset.sum_const_zero] at hw_sum
    norm_num at hw_sum
  rw [Real.dist_eq]
  have hrewrite : (∑ i, w i * z i) - p = ∑ i, w i * (z i - p) := by
    calc
      (∑ i, w i * z i) - p = (∑ i, w i * z i) - (∑ i, w i) * p := by
        rw [hw_sum, one_mul]
      _ = ∑ i, (w i * z i - w i * p) := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = ∑ i, w i * (z i - p) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hrewrite]
  refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
  calc
    ∑ i, |w i * (z i - p)| < ∑ i, w i * r := by
      apply Finset.sum_lt_sum
      · intro i _
        by_cases hi : w i = 0
        · simp only [hi, zero_mul, abs_zero, le_refl]
        · rw [abs_mul, abs_of_nonneg (hw_nonnegative i)]
          have hvertex : |z i - p| ≤ r := by
            simpa only [Real.dist_eq] using (hz i hi).le
          exact mul_le_mul_of_nonneg_left
            hvertex (hw_nonnegative i)
      · obtain ⟨i, hi⟩ := hpositive
        refine ⟨i, Finset.mem_univ i, ?_⟩
        rw [abs_mul, abs_of_nonneg hi.le]
        have hvertex : |z i - p| < r := by
          simpa only [Real.dist_eq] using hz i (ne_of_gt hi)
        exact mul_lt_mul_of_pos_left
          hvertex hi
    _ = r := by rw [← Finset.sum_mul, hw_sum, one_mul]

/-- Helper for Definition 50.8: a sufficiently small weighted sum of nonzero real vertices has
an active vertex of each sign. -/
lemma exists_active_vertices_of_bothSigns
    {ι : Type*} [Fintype ι] (w z : ι → ℝ) {ε : ℝ}
    (hw_nonnegative : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hε : 0 < ε) (hz : ∀ i, ε ≤ |z i|)
    (hsmall : |∑ i, w i * z i| < ε) :
    (∃ i, 0 < z i ∧ w i ≠ 0) ∧ (∃ i, z i < 0 ∧ w i ≠ 0) := by
  classical
  constructor
  · by_contra h
    push Not at h
    have hupper : ∑ i, w i * z i ≤ -ε := by
      calc
        ∑ i, w i * z i ≤ ∑ i, w i * (-ε) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hwi : w i = 0
          · simp only [hwi, zero_mul, le_refl]
          · have hzinonzero : z i ≠ 0 := abs_pos.mp (hε.trans_le (hz i))
            have hnotpositive : ¬ 0 < z i := fun hpositive ↦ hwi (h i hpositive)
            have hzi : z i < 0 := lt_of_le_of_ne (not_lt.mp hnotpositive) hzinonzero
            have hzle : z i ≤ -ε := by
              have hbound := hz i
              rw [abs_of_neg hzi] at hbound
              linarith
            exact mul_le_mul_of_nonneg_left hzle (hw_nonnegative i)
        _ = -ε := by rw [← Finset.sum_mul, hw_sum, one_mul]
    exact (not_lt_of_ge hupper) (abs_lt.mp hsmall).1
  · by_contra h
    push Not at h
    have hlower : ε ≤ ∑ i, w i * z i := by
      calc
        ε = ∑ i, w i * ε := by rw [← Finset.sum_mul, hw_sum, one_mul]
        _ ≤ ∑ i, w i * z i := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hwi : w i = 0
          · simp only [hwi, zero_mul, le_refl]
          · have hzinonzero : z i ≠ 0 := abs_pos.mp (hε.trans_le (hz i))
            have hnotnegative : ¬ z i < 0 := fun hnegative ↦ hwi (h i hnegative)
            have hzi : 0 < z i :=
              lt_of_le_of_ne (not_lt.mp hnotnegative) hzinonzero.symm
            have hbound := hz i
            rw [abs_of_pos hzi] at hbound
            exact mul_le_mul_of_nonneg_left hbound (hw_nonnegative i)
    exact (not_lt_of_ge hlower) (abs_lt.mp hsmall).2

/-- Helper for Definition 50.8: maps with a buffered fine zero cover of order `n` are dense
when the compact metric domain has covering dimension at most `n`. -/
lemma dense_setOf_hasBufferedFineZeroCover
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {δ : ℝ} (hδ : 0 < δ) :
    Dense {f : C(X, ℝ) | HasBufferedFineZeroCover f n δ} := by
  rw [Metric.dense_iff]
  intro f r hr
  classical
  let neighborhood : X → Set X := fun x ↦
    Metric.ball x (δ / 2) ∩ f ⁻¹' Metric.ball (f x) (r / 4)
  let 𝒜 : Set (Set X) := Set.range neighborhood
  have h𝒜open : ∀ U ∈ 𝒜, IsOpen U := by
    rintro U ⟨x, rfl⟩
    exact Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage f.continuous)
  have h𝒜cover : ⋃₀ 𝒜 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_sUnion.mpr
    refine ⟨neighborhood x, ⟨x, rfl⟩, ?_⟩
    have hrquarter : 0 < r / 4 := by positivity
    exact ⟨Metric.mem_ball_self (half_pos hδ), Metric.mem_ball_self hrquarter⟩
  obtain ⟨ι, hιfinite, B, _, p, hBcover, _, hBorder, hBinjective, hBp, _⟩ :=
    existsFiniteIndexedShrinkingRefinement h 𝒜 h𝒜open h𝒜cover
  letI : Finite ι := hιfinite
  letI : Fintype ι := Fintype.ofFinite ι
  have hιnonempty : Nonempty ι := by
    have hx : Classical.choice (inferInstance : Nonempty X) ∈ ⋃ i, (B i : Set X) :=
      hBcover.iSup_set_eq_univ.symm ▸ Set.mem_univ _
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact ⟨i⟩
  let i₀ : ι := Classical.choice hιnonempty
  have hcenter (i : ι) : ∃ c : X, (p i : Set X) = neighborhood c := by
    obtain ⟨c, hc⟩ : ∃ c, neighborhood c = (p i : Set X) := by
      simpa only [𝒜, Set.mem_range] using (p i).2
    exact ⟨c, hc.symm⟩
  choose c hc using hcenter
  let z : ι → ℝ := fun i ↦ if f (c i) = 0 then r / 4 else f (c i)
  have hznonzero : ∀ i, z i ≠ 0 := by
    intro i
    simp only [z]
    split_ifs with hi
    · have hfour : (4 : ℝ) ≠ 0 := by norm_num
      exact div_ne_zero (ne_of_gt hr) hfour
    · exact hi
  have hzcenter : ∀ i, dist (z i) (f (c i)) < r / 2 := by
    intro i
    simp only [z]
    split_ifs with hi
    · rw [hi, Real.dist_eq]
      simp only [sub_zero, abs_div, abs_of_pos hr]
      norm_num
      linarith
    · rw [dist_self]
      linarith
  have hBcoverSet : (Set.univ : Set X) ⊆ ⋃ i, (B i : Set X) := by
    intro x _
    have hx : x ∈ ⋃ i, (B i : Set X) :=
      hBcover.iSup_set_eq_univ.symm ▸ Set.mem_univ x
    exact hx
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i ↦ (B i : Set X)) (fun i ↦ (B i).2) hBcoverSet
  let g : C(X, ℝ) :=
    ⟨fun x ↦ ∑ i, ρ i x * z i,
      continuous_finsetSum _ fun i _ ↦ (ρ i).continuous.mul continuous_const⟩
  have hg_apply : ∀ x, g x = ∑ i, ρ i x * z i := fun _ ↦ rfl
  have hzpoint : ∀ i x, ρ i x ≠ 0 → dist (z i) (f x) < r := by
    intro i x hix
    have hxB : x ∈ B i := hρ i (subset_tsupport (ρ i) hix)
    have hxparent : x ∈ neighborhood (c i) := hc i ▸ hBp i hxB
    have hcxf : dist (f (c i)) (f x) < r / 4 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hxparent.2
    have hsum : dist (z i) (f (c i)) + dist (f (c i)) (f x) < r := by
      linarith [hzcenter i]
    exact lt_of_le_of_lt (dist_triangle (z i) (f (c i)) (f x)) hsum
  have hgclose : dist g f < r := by
    apply ContinuousMap.dist_lt_of_nonempty
    intro x
    rw [hg_apply]
    apply dist_weightedSum_lt (fun i ↦ ρ i x) z (f x)
    · exact fun i ↦ ρ.nonneg i x
    · simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    · exact fun i hi ↦ hzpoint i x hi
  let ε : ℝ := Finset.univ.inf' ⟨i₀, Finset.mem_univ i₀⟩ fun i ↦ |z i|
  have hεpositive : 0 < ε := by
    rw [Finset.lt_inf'_iff]
    intro i _
    exact abs_pos.mpr (hznonzero i)
  have hεle : ∀ i, ε ≤ |z i| := by
    intro i
    exact Finset.inf'_le (fun j ↦ |z j|) (Finset.mem_univ i)
  let P : Set ι := {i | 0 < z i}
  let 𝒰 : Set (Set X) := (fun i ↦ (B i : Set X)) '' P
  have h𝒰finite : 𝒰.Finite := (Set.toFinite P).image _
  have h𝒰open : ∀ U ∈ 𝒰, IsOpen U := by
    rintro U ⟨i, _, rfl⟩
    exact (B i).2
  have hsigns : ∀ x, |g x| < ε →
      (∃ i, 0 < z i ∧ ρ i x ≠ 0) ∧ (∃ i, z i < 0 ∧ ρ i x ≠ 0) := by
    intro x hx
    rw [hg_apply] at hx
    apply exists_active_vertices_of_bothSigns (fun i ↦ ρ i x) z
    · exact fun i ↦ ρ.nonneg i x
    · simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    · exact hεpositive
    · exact hεle
    · exact hx
  have h𝒰cover : ∀ x, |g x| < ε → x ∈ ⋃₀ 𝒰 := by
    intro x hx
    obtain ⟨i, hiz, hiρ⟩ := (hsigns x hx).1
    exact Set.mem_sUnion.mpr ⟨(B i : Set X), ⟨i, hiz, rfl⟩,
      hρ i (subset_tsupport (ρ i) hiρ)⟩
  have h𝒰order : ∀ x, |g x| < ε → Set.encard {U ∈ 𝒰 | x ∈ U} ≤ n := by
    intro x hx
    obtain ⟨j, hjz, hjρ⟩ := (hsigns x hx).2
    let S : Set (Set X) := {U ∈ 𝒰 | x ∈ U}
    let T : Set (Set X) := {U ∈ Set.range (fun i ↦ (B i : Set X)) | x ∈ U}
    have hST : S ⊆ T := by
      rintro U ⟨⟨i, _, rfl⟩, hxi⟩
      exact ⟨⟨i, rfl⟩, hxi⟩
    have hjT : (B j : Set X) ∈ T :=
      ⟨⟨j, rfl⟩, hρ j (subset_tsupport (ρ j) hjρ)⟩
    have hjS : (B j : Set X) ∉ S := by
      rintro ⟨⟨i, hiz, hBi⟩, _⟩
      have hji : j = i := hBinjective hBi.symm
      rw [← hji] at hiz
      exact (not_lt_of_ge hjz.le) hiz
    have hproper : S ⊂ T := Set.ssubset_iff_subset_ne.mpr
      ⟨hST, fun hEq ↦ hjS (hEq ▸ hjT)⟩
    have hlt : Set.encard S < Set.encard T :=
      (h𝒰finite.subset fun U hU ↦ hU.1).encard_lt_encard hproper
    have hlt' : Set.encard S < (n + 1 : ℕ) :=
      hlt.trans_le (Set.hasOrderLE_iff.mp hBorder x)
    have hltSucc : Set.encard S < (n : ℕ∞) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hlt'
    exact (ENat.lt_add_one_iff (ENat.coe_ne_top n)).mp hltSucc
  have h𝒰diameter : ∀ U ∈ 𝒰, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ := by
    rintro U ⟨i, _, rfl⟩ x hx y hy
    have hxc : dist x (c i) < δ / 2 := Metric.mem_ball.mp (hc i ▸ hBp i hx).1
    have hcy : dist (c i) y < δ / 2 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp (hc i ▸ hBp i hy).1
    have hsum : dist x (c i) + dist (c i) y < δ := by linarith
    exact lt_of_le_of_lt (dist_triangle x (c i) y) hsum
  exact ⟨g, Metric.mem_ball.mpr hgclose,
    ε, hεpositive, 𝒰, h𝒰finite, h𝒰open, h𝒰cover, h𝒰order, h𝒰diameter⟩

/-- Helper for Definition 50.8: buffered fine zero covers at every metric scale give the
corresponding covering-dimension bound on every closed subset of the zero fiber. -/
lemma hasCoveringDimensionLE_closedSubset_zeroFiber
    {X : Type u} [MetricSpace X] [CompactSpace X] {f : C(X, ℝ)} {L : Set X} {q : ℕ}
    (hLclosed : IsClosed L) (hLzero : L ⊆ {x | f x = 0})
    (hfine : ∀ k : ℕ,
      HasBufferedFineZeroCover f (q + 1) (1 / (k + 1 : ℝ))) :
    HasCoveringDimensionLE L q := by
  intro 𝒜 h𝒜open h𝒜cover
  classical
  let ambient : Set (Set X) :=
    {U | IsOpen U ∧ (Subtype.val : L → X) ⁻¹' U ∈ 𝒜}
  have hambientOpen : ∀ U ∈ ambient, IsOpen U := fun U hU ↦ hU.1
  have hambientCover : L ⊆ ⋃₀ ambient := by
    intro x hxL
    let z : L := ⟨x, hxL⟩
    have hz : z ∈ ⋃₀ 𝒜 := h𝒜cover.symm ▸ Set.mem_univ z
    obtain ⟨A, hA𝒜, hzA⟩ := Set.mem_sUnion.mp hz
    obtain ⟨U, hUopen, hUtrace⟩ := isOpen_induced_iff.mp (h𝒜open A hA𝒜)
    refine Set.mem_sUnion.mpr ⟨U, ⟨hUopen, ?_⟩, ?_⟩
    · simpa only [hUtrace] using hA𝒜
    · have hzU : z ∈ (Subtype.val : L → X) ⁻¹' U := by
        rw [hUtrace]
        exact hzA
      exact hzU
  obtain ⟨δ, hδ, hLebesgue⟩ :=
    lebesgue_number_lemma_of_metric_sUnion hLclosed.isCompact hambientOpen hambientCover
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨ε, hε, 𝒰, _, h𝒰open, h𝒰cover, h𝒰order, h𝒰diameter⟩ := hfine k
  let ℬ : Set (Set L) :=
    {V | V.Nonempty ∧ ∃ U ∈ 𝒰, V = (Subtype.val : L → X) ⁻¹' U}
  refine ⟨ℬ, ?_, ?_, ?_⟩
  · rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · intro V hV
      obtain ⟨⟨z, hzV⟩, U, hU𝒰, hV⟩ := hV
      obtain ⟨O, hOambient, hzO⟩ := hLebesgue z.1 z.2
      have hzU : z.1 ∈ U := (Set.ext_iff.mp hV z).mp hzV
      refine ⟨(Subtype.val : L → X) ⁻¹' O, hOambient.2, ?_⟩
      rw [hV]
      intro y hy
      apply hzO
      apply Metric.mem_ball.mpr
      simpa only [dist_comm] using (h𝒰diameter U hU𝒰 z.1 hzU y.1 hy).trans hk
    · intro V hV
      obtain ⟨_, U, hU𝒰, rfl⟩ := hV
      exact (h𝒰open U hU𝒰).preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro z
    have hzsmall : |f z.1| < ε := by
      rw [hLzero z.2]
      simpa using hε
    obtain ⟨U, hU𝒰, hzU⟩ := Set.mem_sUnion.mp (h𝒰cover z.1 hzsmall)
    exact Set.mem_sUnion.mpr
      ⟨(Subtype.val : L → X) ⁻¹' U, ⟨⟨z, hzU⟩, U, hU𝒰, rfl⟩, hzU⟩
  · rw [Set.hasOrderLE_iff]
    intro z
    let pullback : Set X → Set L := fun U ↦ (Subtype.val : L → X) ⁻¹' U
    have hincident : {V ∈ ℬ | z ∈ V} ⊆
        pullback '' {U ∈ 𝒰 | z.1 ∈ U} := by
      intro V hV
      obtain ⟨⟨_, U, hU𝒰, hV⟩, hzV⟩ := hV
      have hzU : z.1 ∈ U := (Set.ext_iff.mp hV z).mp hzV
      exact ⟨U, ⟨hU𝒰, hzU⟩, hV.symm⟩
    calc
      Set.encard {V ∈ ℬ | z ∈ V}
          ≤ Set.encard (pullback '' {U ∈ 𝒰 | z.1 ∈ U}) := Set.encard_mono hincident
      _ ≤ Set.encard {U ∈ 𝒰 | z.1 ∈ U} := Set.encard_image_le pullback _
      _ ≤ q + 1 := by
        have hzsmall : |f z.1| < ε := by
          rw [hLzero z.2]
          simpa only [abs_zero] using hε
        exact h𝒰order z.1 hzsmall

/-- Helper for Definition 50.8: a compact metric space of covering dimension at most `n`
admits a real separator whose zero fiber has buffered fine covers of order `n` at every scale. -/
lemma exists_zeroFiberSeparator_with_fineCovers
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {K F : Set X}
    (hK : IsClosed K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ f : C(X, ℝ),
      (∀ x ∈ K, f x < 0) ∧ (∀ x ∈ F, 0 < f x) ∧
        ∀ k : ℕ, HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ)) := by
  have hopen : ∀ k : ℕ,
      IsOpen {f : C(X, ℝ) | HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ))} :=
    fun k ↦ isOpen_setOf_hasBufferedFineZeroCover n (1 / (k + 1 : ℝ))
  have hdense : ∀ k : ℕ,
      Dense {f : C(X, ℝ) | HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ))} := by
    intro k
    have hscale : 0 < 1 / (k + 1 : ℝ) := by positivity
    exact dense_setOf_hasBufferedFineZeroCover h hscale
  have hgeneric : Dense (⋂ k : ℕ,
      {f : C(X, ℝ) | HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ))}) :=
    BaireSpace.baire_property _ hopen hdense
  obtain ⟨u, huK, huF, _⟩ := exists_continuous_zero_one_of_isClosed hK hF hKF
  let f₀ : C(X, ℝ) := (ContinuousMap.const X 2) * u - ContinuousMap.const X 1
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hballNonempty : (Metric.ball f₀ (1 / 2 : ℝ)).Nonempty :=
    ⟨f₀, Metric.mem_ball_self hhalf⟩
  obtain ⟨f, hfine, hfclose⟩ :=
    hgeneric.exists_mem_open Metric.isOpen_ball hballNonempty
  refine ⟨f, ?_, ?_, Set.mem_iInter.mp hfine⟩
  · intro x hxK
    have hpoint : dist (f x) (f₀ x) < (1 / 2 : ℝ) :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hfclose)
    have hux : u x = 0 := huK hxK
    have hf₀ : f₀ x = -1 := by norm_num [f₀, hux]
    rw [hf₀, Real.dist_eq] at hpoint
    have := (abs_lt.mp hpoint).2
    linarith
  · intro x hxF
    have hpoint : dist (f x) (f₀ x) < (1 / 2 : ℝ) :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hfclose)
    have hux : u x = 1 := huF hxF
    have hf₀ : f₀ x = 1 := by norm_num [f₀, hux]
    rw [hf₀, Real.dist_eq] at hpoint
    have := (abs_lt.mp hpoint).1
    linarith

/-- Helper for Definition 50.8: a covering-dimension bound gives a controlled open partition
between two disjoint closed subsets of a compact metrizable space. -/
lemma existsOpenPartition_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {K F : Set X} (hK : IsClosed K) (hF : IsClosed F)
    (hKF : Disjoint K F) :
    ∃ V : Set X,
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Fᶜ ∧
        HasCoveringDimensionLT ↥(frontier V) n := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      refine ⟨∅, isOpen_empty, ?_, by simp, ?_⟩
      · intro x _
        exact isEmptyElim x
      · cases n with
        | zero =>
            exact Set.isEmpty_coe_sort.mpr frontier_empty
        | succ q =>
            exact hasCoveringDimensionLE_of_isEmpty
              (Set.isEmpty_coe_sort.mpr frontier_empty) q
  | inr hX =>
      letI : Nonempty X := hX
      letI : MetricSpace X := metrizableSpaceMetric X
      obtain ⟨f, hfK, hfF, hfine⟩ :=
        exists_zeroFiberSeparator_with_fineCovers h hK hF hKF
      let V : Set X := {x | f x < 0}
      have hVopen : IsOpen V := isOpen_lt f.continuous continuous_const
      have hKV : K ⊆ V := fun x hx ↦ hfK x hx
      have hVclosure : closure V ⊆ Fᶜ := by
        have hclosed : IsClosed {x | f x ≤ 0} :=
          isClosed_le f.continuous continuous_const
        have hsubset : V ⊆ {x | f x ≤ 0} := by
          intro x hx
          change f x < 0 at hx
          exact hx.le
        intro x hxclosure hxF
        have hfx : f x ≤ 0 := closure_minimal hsubset hclosed hxclosure
        exact (not_lt_of_ge hfx) (hfF x hxF)
      have hfrontierZero : frontier V ⊆ {x | f x = 0} := by
        exact frontier_lt_subset_eq f.continuous continuous_const
      refine ⟨V, hVopen, hKV, hVclosure, ?_⟩
      cases n with
      | zero =>
          constructor
          rintro ⟨x, hxfrontier⟩
          obtain ⟨ε, hε, 𝒰, _, _, h𝒰cover, h𝒰order, _⟩ := hfine 0
          have hxsmall : |f x| < ε := by
            rw [hfrontierZero hxfrontier]
            simpa using hε
          obtain ⟨U, hU𝒰, hxU⟩ := Set.mem_sUnion.mp (h𝒰cover x hxsmall)
          have hone : (1 : ℕ∞) ≤ Set.encard {W ∈ 𝒰 | x ∈ W} :=
            Set.one_le_encard_iff_nonempty.mpr ⟨U, hU𝒰, hxU⟩
          have hzero : Set.encard {W ∈ 𝒰 | x ∈ W} ≤ (0 : ℕ) :=
            h𝒰order x hxsmall
          have hnotOneZero : ¬ (1 : ℕ∞) ≤ 0 := by norm_num
          exact hnotOneZero (hone.trans hzero)
      | succ q =>
          exact hasCoveringDimensionLE_closedSubset_zeroFiber isClosed_frontier
            hfrontierZero hfine
