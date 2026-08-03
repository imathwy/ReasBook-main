module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Example_50_3
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Set.Card.Arithmetic

public section

open scoped CoveringDimension

open Set

/-- Helper for Theorem 50.6: the fractional translation used for one phase of the
Euclidean grid. -/
private noncomputable def euclideanCoverPhaseShift (N : ℕ) (c : Fin (N + 1)) : ℝ :=
  (c : ℝ) / (N + 1)

/-- Helper for Theorem 50.6: an open box in one translated Euclidean grid. -/
private def shiftedEuclideanBox (N : ℕ) (a : ℝ) (c : Fin (N + 1))
    (p : Fin N → ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)) ⁻¹' Set.pi Set.univ
    (fun i ↦ Ioo
      (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)))

/-- Helper for Theorem 50.6: the family of all boxes in one translated grid. -/
private def shiftedEuclideanBoxFamily (N : ℕ) (a : ℝ) (c : Fin (N + 1)) :
    Set (Set (EuclideanSpace ℝ (Fin N))) :=
  Set.range (shiftedEuclideanBox N a c)

/-- Helper for Theorem 50.6: membership in a shifted Euclidean box is coordinatewise
membership in its defining intervals. -/
private lemma mem_shiftedEuclideanBox_iff {N : ℕ} {a : ℝ} {c : Fin (N + 1)}
    {p : Fin N → ℤ} {x : EuclideanSpace ℝ (Fin N)} :
    x ∈ shiftedEuclideanBox N a c p ↔
      ∀ i, x i ∈ Ioo
        (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
        (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)) := by
  -- Unfold the box once, exposing the stable coordinatewise interface used below.
  simp only [shiftedEuclideanBox, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rfl

/-- Helper for Theorem 50.6: a real coordinate lies on the boundary grid of at most
one of the `N + 1` phases. -/
private lemma euclideanGridBoundary_phase_unique {N : ℕ} {a x : ℝ} (ha : 0 < a)
    {c d : Fin (N + 1)}
    (hc : ∃ n : ℤ, x = a * ((n : ℝ) + euclideanCoverPhaseShift N c))
    (hd : ∃ n : ℤ, x = a * ((n : ℝ) + euclideanCoverPhaseShift N d)) :
    c = d := by
  -- Cancel the mesh and clear the common denominator of the two phase shifts.
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm⟩ := hd
  have hscaled : (n : ℝ) + euclideanCoverPhaseShift N c =
      (m : ℝ) + euclideanCoverPhaseShift N d := by
    nlinarith
  have hdenomPos : 0 < (N : ℝ) + 1 := by
    positivity
  have hdenom : ((N + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hc0 : 0 ≤ euclideanCoverPhaseShift N c := by
    dsimp [euclideanCoverPhaseShift]
    positivity
  have hc1 : euclideanCoverPhaseShift N c < 1 := by
    rw [euclideanCoverPhaseShift, div_lt_one hdenomPos]
    exact_mod_cast c.isLt
  have hd0 : 0 ≤ euclideanCoverPhaseShift N d := by
    dsimp [euclideanCoverPhaseShift]
    positivity
  have hd1 : euclideanCoverPhaseShift N d < 1 := by
    rw [euclideanCoverPhaseShift, div_lt_one hdenomPos]
    exact_mod_cast d.isLt
  have hcFloor : ⌊euclideanCoverPhaseShift N c⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨hc0, hc1⟩
  have hdFloor : ⌊euclideanCoverPhaseShift N d⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨hd0, hd1⟩
  have hnFloor : ⌊(n : ℝ) + euclideanCoverPhaseShift N c⌋ = n := by
    rw [Int.floor_intCast_add, hcFloor, add_zero]
  have hmFloor : ⌊(m : ℝ) + euclideanCoverPhaseShift N d⌋ = m := by
    rw [Int.floor_intCast_add, hdFloor, add_zero]
  have hnm : n = m := by
    rw [← hnFloor, ← hmFloor]
    exact congrArg Int.floor hscaled
  have hshift : euclideanCoverPhaseShift N c = euclideanCoverPhaseShift N d := by
    rw [hnm] at hscaled
    linarith
  have hcast : (c : ℝ) = d := by
    dsimp [euclideanCoverPhaseShift] at hshift
    field_simp [hdenom] at hshift
    linarith
  apply Fin.ext
  exact_mod_cast hcast

/-- Helper for Theorem 50.6: among `N + 1` translated grids, one phase avoids the
boundary grid in all `N` coordinates. -/
private lemma exists_phase_avoiding_euclideanGridBoundaries {N : ℕ} {a : ℝ}
    (ha : 0 < a) (x : EuclideanSpace ℝ (Fin N)) :
    ∃ c : Fin (N + 1), ∀ i : Fin N,
      ¬ ∃ n : ℤ, x i = a * ((n : ℝ) + euclideanCoverPhaseShift N c) := by
  -- Each coordinate forbids at most one phase, so their union cannot exhaust `N + 1` phases.
  classical
  let bad : Fin N → Set (Fin (N + 1)) := fun i ↦
    {c | ∃ n : ℤ, x i = a * ((n : ℝ) + euclideanCoverPhaseShift N c)}
  have hbad (i : Fin N) : Set.encard (bad i) ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro c d hc hd
    exact euclideanGridBoundary_phase_unique ha hc hd
  by_contra hnone
  have hall : (Set.univ : Set (Fin (N + 1))) ⊆ ⋃ i, bad i := by
    intro c _
    by_contra hc
    apply hnone
    refine ⟨c, ?_⟩
    intro i hi
    exact hc (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hcard : ((N + 1 : ℕ) : ℕ∞) ≤ N := by
    calc
      ((N + 1 : ℕ) : ℕ∞) = Set.encard (Set.univ : Set (Fin (N + 1))) := by simp
      _ ≤ Set.encard (⋃ i, bad i) := Set.encard_le_encard hall
      _ ≤ ∑ i, Set.encard (bad i) := Set.encard_iUnion_le_of_fintype bad
      _ ≤ ∑ _i : Fin N, (1 : ℕ∞) := Finset.sum_le_sum fun i _ ↦ hbad i
      _ = N := by simp
  have hcardNat : N + 1 ≤ N := by
    exact_mod_cast hcard
  omega

/-- Helper for Theorem 50.6: avoiding every coordinate boundary selects a containing
shifted Euclidean box. -/
private lemma mem_shiftedEuclideanBox_of_phaseAvoidance {N : ℕ} {a : ℝ}
    (ha : 0 < a) (x : EuclideanSpace ℝ (Fin N)) (c : Fin (N + 1))
    (havoid : ∀ i : Fin N,
      ¬ ∃ n : ℤ, x i = a * ((n : ℝ) + euclideanCoverPhaseShift N c)) :
    x ∈ shiftedEuclideanBox N a c
      (fun i ↦ ⌊x i / a - euclideanCoverPhaseShift N c⌋) := by
  -- Floor bounds locate every coordinate strictly between consecutive grid hyperplanes.
  rw [mem_shiftedEuclideanBox_iff]
  intro i
  have hfloor := Int.floor_le (x i / a - euclideanCoverPhaseShift N c)
  have hstrict : (⌊x i / a - euclideanCoverPhaseShift N c⌋ : ℝ) <
      x i / a - euclideanCoverPhaseShift N c := by
    apply lt_of_le_of_ne hfloor
    intro heq
    apply havoid i
    refine ⟨⌊x i / a - euclideanCoverPhaseShift N c⌋, ?_⟩
    field_simp [ha.ne'] at heq ⊢
    nlinarith
  have hupp := Int.lt_floor_add_one (x i / a - euclideanCoverPhaseShift N c)
  constructor
  · field_simp [ha.ne'] at hstrict hupp ⊢
    nlinarith
  · field_simp [ha.ne'] at hstrict hupp ⊢
    nlinarith

/-- Helper for Theorem 50.6: two overlapping coordinate intervals in one translated
grid have the same integer index. -/
private lemma shiftedEuclideanInterval_index_unique {N : ℕ} {a z : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) {n m : ℤ}
    (hn : z ∈ Ioo
      (a * ((n : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((n : ℝ) + 1 + euclideanCoverPhaseShift N c)))
    (hm : z ∈ Ioo
      (a * ((m : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((m : ℝ) + 1 + euclideanCoverPhaseShift N c))) :
    n = m := by
  -- Cross the lower endpoint of each interval with the other interval's upper endpoint.
  have hnm : (n : ℝ) < m + 1 := by
    nlinarith [hn.1, hm.2]
  have hmn : (m : ℝ) < n + 1 := by
    nlinarith [hm.1, hn.2]
  have hnmInt : n < m + 1 := by
    exact_mod_cast hnm
  have hmnInt : m < n + 1 := by
    exact_mod_cast hmn
  omega

/-- Helper for Theorem 50.6: boxes in one translated grid are pointwise unique. -/
private lemma shiftedEuclideanBoxFamily_pointwiseUnique {N : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin N))
    {V W : Set (EuclideanSpace ℝ (Fin N))}
    (hV : V ∈ shiftedEuclideanBoxFamily N a c)
    (hW : W ∈ shiftedEuclideanBoxFamily N a c)
    (hxV : x ∈ V) (hxW : x ∈ W) : V = W := by
  -- Recover both integer index functions and compare them coordinate by coordinate.
  obtain ⟨p, rfl⟩ := hV
  obtain ⟨q, rfl⟩ := hW
  rw [mem_shiftedEuclideanBox_iff] at hxV hxW
  have hpq : p = q := by
    funext i
    exact shiftedEuclideanInterval_index_unique ha c (hxV i) (hxW i)
  rw [hpq]

/-- Helper for Theorem 50.6: every shifted Euclidean box is open. -/
private lemma shiftedEuclideanBox_isOpen {N : ℕ} (a : ℝ) (c : Fin (N + 1))
    (p : Fin N → ℤ) : IsOpen (shiftedEuclideanBox N a c p) := by
  -- The box is the homeomorphic preimage of a finite product of open intervals.
  have hopen : IsOpen (Set.pi Set.univ (fun i : Fin N ↦ Ioo
      (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)))) := by
    apply isOpen_set_pi Set.finite_univ
    intro i _
    exact isOpen_Ioo
  exact hopen.preimage (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).continuous

/-- Helper for Theorem 50.6: the distance between two points of one shifted box is at
most `Real.sqrt N * a`. -/
private lemma shiftedEuclideanBox_dist_le {N : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) (p : Fin N → ℤ)
    {x y : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ shiftedEuclideanBox N a c p)
    (hy : y ∈ shiftedEuclideanBox N a c p) :
    dist x y ≤ Real.sqrt N * a := by
  -- Bound each squared coordinate distance by `a²`, then sum over the `N` coordinates.
  rw [mem_shiftedEuclideanBox_iff] at hx hy
  have hcoord (i : Fin N) : dist (x i) (y i) < a := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · nlinarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
    · nlinarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ (N : ℝ) * a ^ 2 := by
    calc
      ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin N, a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [dist_nonneg (x := x i) (y := y i), hcoord i]
      _ = (N : ℝ) * a ^ 2 := by simp
  have hNnonneg : 0 ≤ (N : ℝ) := by
    positivity
  rw [EuclideanSpace.dist_eq]
  calc
    Real.sqrt (∑ i, dist (x i) (y i) ^ 2)
        ≤ Real.sqrt ((N : ℝ) * a ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt N * Real.sqrt (a ^ 2) := by
      rw [Real.sqrt_mul hNnonneg]
    _ = Real.sqrt N * a := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]

/-- Helper for Theorem 50.6: every shifted Euclidean box is bounded and has diameter
at most `Real.sqrt N * a`. -/
private lemma shiftedEuclideanBox_isBounded_diam {N : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) (p : Fin N → ℤ) :
    Bornology.IsBounded (shiftedEuclideanBox N a c p) ∧
      Metric.diam (shiftedEuclideanBox N a c p) ≤ Real.sqrt N * a := by
  -- Reuse the pairwise distance estimate for both boundedness and diameter.
  constructor
  · rw [Metric.isBounded_iff]
    exact ⟨Real.sqrt N * a, fun x hx y hy ↦ shiftedEuclideanBox_dist_le ha c p hx hy⟩
  · apply Metric.diam_le_of_forall_dist_le (mul_nonneg (Real.sqrt_nonneg _) ha.le)
    intro x hx y hy
    exact shiftedEuclideanBox_dist_le ha c p hx hy

/-- Helper for Theorem 50.6: there is a uniformly fine open cover of `N`-dimensional
Euclidean space with pointwise order at most `N + 1`. -/
private lemma exists_euclideanOpenCover_order {N : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ∃ 𝒸 : Set (Set (EuclideanSpace ℝ (Fin N))),
      (∀ V ∈ 𝒸, IsOpen V) ∧ ⋃₀ 𝒸 = Set.univ ∧ 𝒸.HasOrderLE (N + 1) ∧
        ∀ V ∈ 𝒸, Bornology.IsBounded V ∧ Metric.diam V < ε := by
  -- Use `N + 1` translated grids with mesh small enough for the Euclidean diameter bound.
  classical
  let a : ℝ := ε / (Real.sqrt N + 1)
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hdenom : 0 < Real.sqrt (N : ℝ) + 1 := by linarith
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hε hdenom
  have haε : Real.sqrt N * a < ε := by
    dsimp [a]
    rw [← mul_div_assoc, div_lt_iff₀ hdenom]
    nlinarith
  let 𝒸 : Set (Set (EuclideanSpace ℝ (Fin N))) :=
    ⋃ c : Fin (N + 1), shiftedEuclideanBoxFamily N a c
  refine ⟨𝒸, ?_, ?_, ?_, ?_⟩
  · -- Every cover member is an open box from one phase.
    intro V hV
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV
    obtain ⟨p, rfl⟩ := hc
    exact shiftedEuclideanBox_isOpen a c p
  · -- Phase avoidance and coordinatewise floors place every point in a cover member.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨c, hc⟩ := exists_phase_avoiding_euclideanGridBoundaries ha x
    let p : Fin N → ℤ := fun i ↦ ⌊x i / a - euclideanCoverPhaseShift N c⌋
    have hxp : x ∈ shiftedEuclideanBox N a c p :=
      mem_shiftedEuclideanBox_of_phaseAvoidance ha x c hc
    rw [Set.mem_sUnion]
    exact ⟨shiftedEuclideanBox N a c p,
      Set.mem_iUnion.2 ⟨c, ⟨p, rfl⟩⟩, hxp⟩
  · -- Split the members through a point by phase; each phase contributes at most one box.
    rw [Set.hasOrderLE_iff]
    intro x
    let throughPhase : Fin (N + 1) → Set (Set (EuclideanSpace ℝ (Fin N))) :=
      fun c ↦ {V ∈ shiftedEuclideanBoxFamily N a c | x ∈ V}
    have hsub : {V ∈ 𝒸 | x ∈ V} ⊆ ⋃ c, throughPhase c := by
      intro V hV
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV.1
      exact Set.mem_iUnion.2 ⟨c, ⟨hc, hV.2⟩⟩
    have hphase (c : Fin (N + 1)) : Set.encard (throughPhase c) ≤ 1 := by
      rw [Set.encard_le_one_iff]
      intro V W hV hW
      exact shiftedEuclideanBoxFamily_pointwiseUnique ha c x hV.1 hW.1 hV.2 hW.2
    calc
      Set.encard {V ∈ 𝒸 | x ∈ V}
          ≤ Set.encard (⋃ c, throughPhase c) := Set.encard_le_encard hsub
      _ ≤ ∑ c, Set.encard (throughPhase c) :=
        Set.encard_iUnion_le_of_fintype throughPhase
      _ ≤ ∑ _c : Fin (N + 1), (1 : ℕ∞) :=
        Finset.sum_le_sum fun c _ ↦ hphase c
      _ = N + 1 := by simp
  · -- The chosen mesh turns the box diameter estimate into strict `ε`-smallness.
    intro V hV
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV
    obtain ⟨p, rfl⟩ := hc
    have hspec := shiftedEuclideanBox_isBounded_diam ha c p
    exact ⟨hspec.1, hspec.2.trans_lt haε⟩

/-- Helper for Theorem 50.6: restricting a uniformly fine Euclidean cover to a
subtype gives a nonempty uniformly fine cover of the same order. -/
lemma exists_subtypeEuclideanCover_order {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (ε : ℝ) (hε : 0 < ε) :
    ∃ ℬ : Set (Set X),
      (∀ B ∈ ℬ, IsOpen B) ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (N + 1) ∧
        ∀ B ∈ ℬ, B.Nonempty ∧ Bornology.IsBounded B ∧ Metric.diam B < ε := by
  -- Pull the ambient cover back along the subtype inclusion and discard empty members.
  obtain ⟨𝒸, h𝒸open, h𝒸cover, h𝒸order, h𝒸small⟩ :=
    exists_euclideanOpenCover_order ε hε
  let pullback : Set (Set X) :=
    ((fun V : Set (EuclideanSpace ℝ (Fin N)) ↦
      ((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) '' 𝒸)
  let ℬ : Set (Set X) := {B ∈ pullback | B.Nonempty}
  refine ⟨ℬ, ?_, ?_, ?_, ?_⟩
  · -- Openness is preserved by the continuous subtype inclusion.
    intro B hB
    obtain ⟨V, hV𝒸, rfl⟩ := hB.1
    exact (h𝒸open V hV𝒸).preimage continuous_subtype_val
  · -- Ambient coverage supplies a nonempty pullback member through each subtype point.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    have hx : (x : EuclideanSpace ℝ (Fin N)) ∈ ⋃₀ 𝒸 := by
      rw [h𝒸cover]
      exact Set.mem_univ _
    rw [Set.mem_sUnion] at hx
    obtain ⟨V, hV𝒸, hxV⟩ := hx
    let B : Set X := ((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V
    have hxB : x ∈ B := hxV
    have hBpullback : B ∈ pullback := ⟨V, hV𝒸, rfl⟩
    exact ⟨B, ⟨hBpullback, ⟨x, hxB⟩⟩, hxB⟩
  · -- Filtering out empty members cannot increase point multiplicity.
    rw [Set.hasOrderLE_iff]
    intro x
    have hpullbackOrder : pullback.HasOrderLE (N + 1) := by
      exact preimageFamily_hasOrderLE
        ((↑) : X → EuclideanSpace ℝ (Fin N)) 𝒸 (N + 1) h𝒸order
    calc
      Set.encard {B ∈ ℬ | x ∈ B} ≤ Set.encard {B ∈ pullback | x ∈ B} := by
        apply Set.encard_le_encard
        intro B hB
        exact ⟨hB.1.1, hB.2⟩
      _ ≤ N + 1 := (Set.hasOrderLE_iff.mp hpullbackOrder) x
  · -- The subtype inclusion is an isometry, so boundedness and diameter bounds descend.
    intro B hB
    have hBpullback : B ∈ pullback := hB.1
    obtain ⟨V, hV𝒸, rfl⟩ := hBpullback
    have hVsmall := h𝒸small V hV𝒸
    have himage :
        ((↑) : X → EuclideanSpace ℝ (Fin N)) ''
            (((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) ⊆ V :=
      Set.image_preimage_subset _ _
    have hBbounded : Bornology.IsBounded
        (((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) := by
      apply isometry_subtype_coe.antilipschitz.isBounded_preimage
      exact hVsmall.1
    have hdiamImage :
        Metric.diam (((↑) : X → EuclideanSpace ℝ (Fin N)) ''
          (((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V)) =
            Metric.diam (((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) :=
      isometry_subtype_coe.diam_image _
    have hdiamLe :
        Metric.diam (((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) ≤
          Metric.diam V := by
      rw [← hdiamImage]
      exact Metric.diam_mono himage hVsmall.1
    exact ⟨hB.2, hBbounded, hdiamLe.trans_lt hVsmall.2⟩

/-- Every compact subspace of `EuclideanSpace ℝ (Fin N)` has covering-dimension
bound `N`. -/
theorem compactSubset_euclideanSpace_hasCoveringDimensionLE {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X) :
    HasCoveringDimensionLE X N := by
  -- Choose a Lebesgue number, then refine by the uniformly fine order-`N + 1` cover.
  intro 𝒜 h𝒜open h𝒜cover
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨δ, hδ⟩ := lebesgueNumberLemma 𝒜 h𝒜open h𝒜cover
  obtain ⟨ℬ, hℬopen, hℬcover, hℬorder, hℬsmall⟩ :=
    exists_subtypeEuclideanCover_order X δ hδ.pos
  refine ⟨ℬ, smallDiameterOpenCover_isOpenRefinement hδ hℬopen hℬsmall,
    hℬcover, ?_⟩
  simpa using hℬorder

/-- Theorem 50.6. Every compact subspace of `EuclideanSpace ℝ (Fin N)` has
covering dimension at most `N`. -/
theorem compactSubset_euclideanSpace_coveringDimension_le {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X) :
    dim X ≤ N := by
  -- Translate the proved cover-refinement bound into the numerical dimension inequality.
  rw [coveringDimension_le_iff]
  exact compactSubset_euclideanSpace_hasCoveringDimensionLE X hX
