module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Lemma_27_5
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.ShrinkingLemma

public section

open Set

universe u v

/-- Helper for Theorem 50.3: preimages of a family do not increase its pointwise order. -/
private lemma preimageFamily_hasOrderLE {Y : Type u} {Z : Type v}
    (f : Y → Z) (Ccover : Set (Set Z)) (n : ℕ) (hCcover : Ccover.HasOrderLE n) :
    ((fun V : Set Z ↦ f ⁻¹' V) '' Ccover).HasOrderLE n := by
  -- Compare the sets containing a point with the image of the corresponding source family.
  rw [Set.hasOrderLE_iff] at hCcover ⊢
  intro y
  let source : Set (Set Z) := {V ∈ Ccover | f y ∈ V}
  let pullback : (Set Z) → Set Y := fun V ↦ f ⁻¹' V
  have hsub : {B ∈ pullback '' Ccover | y ∈ B} ⊆ pullback '' source := by
    intro B hB
    obtain ⟨V, hVCcover, rfl⟩ := hB.1
    exact ⟨V, ⟨hVCcover, hB.2⟩, rfl⟩
  calc
    Set.encard {B ∈ pullback '' Ccover | y ∈ B}
        ≤ Set.encard (pullback '' source) := Set.encard_le_encard hsub
    _ ≤ Set.encard source := Set.encard_image_le pullback source
    _ ≤ n := hCcover (f y)
/-- Helper for Theorem 50.3: a nonempty bounded open cover finer than a Lebesgue
number is an open refinement of the original cover. -/
private lemma smallDiameterOpenCoverIsOpenRefinement
    {Y : Type u} [PseudoMetricSpace Y] {Acover Bcover : Set (Set Y)} {δ : ℝ}
    (hδ : IsLebesgueNumber Acover δ) (hBcoveropen : ∀ B ∈ Bcover, IsOpen B)
    (hBcoversmall : ∀ B ∈ Bcover,
      B.Nonempty ∧ Bornology.IsBounded B ∧ Metric.diam B < δ) :
    IsOpenRefinement Bcover Acover := by
  -- The Lebesgue-number property supplies the containing original member.
  rw [isOpenRefinement_iff]
  constructor
  · rw [isRefinement_iff]
    intro B hB
    exact hδ.exists_superset (hBcoversmall B hB).1 (hBcoversmall B hB).2.1 (hBcoversmall B hB).2.2
  · exact hBcoveropen
/-- Helper for Theorem 50.3: the fractional translation used for one phase of the
Euclidean grid. -/
private noncomputable def euclideanCoverPhaseShift (N : ℕ) (c : Fin (N + 1)) : ℝ :=
  (c : ℝ) / (N + 1)

/-- Helper for Theorem 50.3: an open box in one translated Euclidean grid. -/
private def shiftedEuclideanBox (N : ℕ) (a : ℝ) (c : Fin (N + 1))
    (p : Fin N → ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)) ⁻¹' Set.pi Set.univ
    (fun i ↦ Ioo
      (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)))

/-- Helper for Theorem 50.3: the family of all boxes in one translated grid. -/
private def shiftedEuclideanBoxFamily (N : ℕ) (a : ℝ) (c : Fin (N + 1)) :
    Set (Set (EuclideanSpace ℝ (Fin N))) :=
  Set.range (shiftedEuclideanBox N a c)

/-- Helper for Theorem 50.3: membership in a shifted Euclidean box is coordinatewise
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

/-- Helper for Theorem 50.3: a real coordinate lies on the boundary grid of at most
one of the `N + 1` phases. -/
private lemma euclideanGridBoundaryPhaseUnique {N : ℕ} {a x : ℝ} (ha : 0 < a)
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

/-- Helper for Theorem 50.3: among `N + 1` translated grids, one phase avoids the
boundary grid in all `N` coordinates. -/
private lemma existsPhaseAvoidingEuclideanGridBoundaries {N : ℕ} {a : ℝ}
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
    exact euclideanGridBoundaryPhaseUnique ha hc hd
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

/-- Helper for Theorem 50.3: avoiding every coordinate boundary selects a containing
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

/-- Helper for Theorem 50.3: two overlapping coordinate intervals in one translated
grid have the same integer index. -/
private lemma shiftedEuclideanIntervalIndexUnique {N : ℕ} {a z : ℝ} (ha : 0 < a)
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

/-- Helper for Theorem 50.3: boxes in one translated grid are pointwise unique. -/
private lemma shiftedEuclideanBoxFamilyPointwiseUnique {N : ℕ} {a : ℝ} (ha : 0 < a)
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
    exact shiftedEuclideanIntervalIndexUnique ha c (hxV i) (hxW i)
  rw [hpq]

/-- Helper for Theorem 50.3: every shifted Euclidean box is open. -/
private lemma isOpen_shiftedEuclideanBox {N : ℕ} (a : ℝ) (c : Fin (N + 1))
    (p : Fin N → ℤ) : IsOpen (shiftedEuclideanBox N a c p) := by
  -- The box is the homeomorphic preimage of a finite product of open intervals.
  have hopen : IsOpen (Set.pi Set.univ (fun i : Fin N ↦ Ioo
      (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)))) := by
    apply isOpen_set_pi Set.finite_univ
    intro i _
    exact isOpen_Ioo
  exact hopen.preimage (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).continuous

/-- Helper for Theorem 50.3: the distance between two points of one shifted box is at
most `Real.sqrt N * a`. -/
private lemma dist_le_of_mem_shiftedEuclideanBox {N : ℕ} {a : ℝ} (ha : 0 < a)
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

/-- Helper for Theorem 50.3: every shifted Euclidean box is bounded and has diameter
at most `Real.sqrt N * a`. -/
private lemma isBounded_shiftedEuclideanBox_and_diam_le {N : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) (p : Fin N → ℤ) :
    Bornology.IsBounded (shiftedEuclideanBox N a c p) ∧
      Metric.diam (shiftedEuclideanBox N a c p) ≤ Real.sqrt N * a := by
  -- Reuse the pairwise distance estimate for both boundedness and diameter.
  constructor
  · rw [Metric.isBounded_iff]
    exact ⟨Real.sqrt N * a, fun x hx y hy ↦ dist_le_of_mem_shiftedEuclideanBox ha c p hx hy⟩
  · apply Metric.diam_le_of_forall_dist_le (mul_nonneg (Real.sqrt_nonneg _) ha.le)
    intro x hx y hy
    exact dist_le_of_mem_shiftedEuclideanBox ha c p hx hy

/-- Helper for Theorem 50.3: there is a uniformly fine open cover of `N`-dimensional
Euclidean space with pointwise order at most `N + 1`. -/
private lemma existsEuclideanOpenCoverOfOrder {N : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ∃ Ccover : Set (Set (EuclideanSpace ℝ (Fin N))),
      (∀ V ∈ Ccover, IsOpen V) ∧ ⋃₀ Ccover = Set.univ ∧ Ccover.HasOrderLE (N + 1) ∧
        ∀ V ∈ Ccover, Bornology.IsBounded V ∧ Metric.diam V < ε := by
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
  let Ccover : Set (Set (EuclideanSpace ℝ (Fin N))) :=
    ⋃ c : Fin (N + 1), shiftedEuclideanBoxFamily N a c
  refine ⟨Ccover, ?_, ?_, ?_, ?_⟩
  · -- Every cover member is an open box from one phase.
    intro V hV
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV
    obtain ⟨p, rfl⟩ := hc
    exact isOpen_shiftedEuclideanBox a c p
  · -- Phase avoidance and coordinatewise floors place every point in a cover member.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨c, hc⟩ := existsPhaseAvoidingEuclideanGridBoundaries ha x
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
    have hsub : {V ∈ Ccover | x ∈ V} ⊆ ⋃ c, throughPhase c := by
      intro V hV
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV.1
      exact Set.mem_iUnion.2 ⟨c, ⟨hc, hV.2⟩⟩
    have hphase (c : Fin (N + 1)) : Set.encard (throughPhase c) ≤ 1 := by
      rw [Set.encard_le_one_iff]
      intro V W hV hW
      exact shiftedEuclideanBoxFamilyPointwiseUnique ha c x hV.1 hW.1 hV.2 hW.2
    calc
      Set.encard {V ∈ Ccover | x ∈ V}
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
    have hspec := isBounded_shiftedEuclideanBox_and_diam_le ha c p
    exact ⟨hspec.1, hspec.2.trans_lt haε⟩

/-- Helper for Theorem 50.3: restricting a uniformly fine Euclidean cover to a
subtype gives a nonempty uniformly fine cover of the same order. -/
private lemma existsFineSubtypeEuclideanOpenCover {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (ε : ℝ) (hε : 0 < ε) :
    ∃ Bcover : Set (Set X),
      (∀ B ∈ Bcover, IsOpen B) ∧ ⋃₀ Bcover = Set.univ ∧ Bcover.HasOrderLE (N + 1) ∧
        ∀ B ∈ Bcover, B.Nonempty ∧ Bornology.IsBounded B ∧ Metric.diam B < ε := by
  -- Pull the ambient cover back along the subtype inclusion and discard empty members.
  obtain ⟨Ccover, hCcoveropen, hCcovercover, hCcoverorder, hCcoversmall⟩ :=
    existsEuclideanOpenCoverOfOrder ε hε
  let pullback : Set (Set X) :=
    ((fun V : Set (EuclideanSpace ℝ (Fin N)) ↦
      ((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) '' Ccover)
  let Bcover : Set (Set X) := {B ∈ pullback | B.Nonempty}
  refine ⟨Bcover, ?_, ?_, ?_, ?_⟩
  · -- Openness is preserved by the continuous subtype inclusion.
    intro B hB
    obtain ⟨V, hVCcover, rfl⟩ := hB.1
    exact (hCcoveropen V hVCcover).preimage continuous_subtype_val
  · -- Ambient coverage supplies a nonempty pullback member through each subtype point.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    have hx : (x : EuclideanSpace ℝ (Fin N)) ∈ ⋃₀ Ccover := by
      rw [hCcovercover]
      exact Set.mem_univ _
    rw [Set.mem_sUnion] at hx
    obtain ⟨V, hVCcover, hxV⟩ := hx
    let B : Set X := ((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V
    have hxB : x ∈ B := hxV
    have hBpullback : B ∈ pullback := ⟨V, hVCcover, rfl⟩
    exact ⟨B, ⟨hBpullback, ⟨x, hxB⟩⟩, hxB⟩
  · -- Filtering out empty members cannot increase point multiplicity.
    rw [Set.hasOrderLE_iff]
    intro x
    have hpullbackOrder : pullback.HasOrderLE (N + 1) := by
      exact preimageFamily_hasOrderLE
        ((↑) : X → EuclideanSpace ℝ (Fin N)) Ccover (N + 1) hCcoverorder
    calc
      Set.encard {B ∈ Bcover | x ∈ B} ≤ Set.encard {B ∈ pullback | x ∈ B} := by
        apply Set.encard_le_encard
        intro B hB
        exact ⟨hB.1.1, hB.2⟩
      _ ≤ N + 1 := (Set.hasOrderLE_iff.mp hpullbackOrder) x
  · -- The subtype inclusion is an isometry, so boundedness and diameter bounds descend.
    intro B hB
    have hBpullback : B ∈ pullback := hB.1
    obtain ⟨V, hVCcover, rfl⟩ := hBpullback
    have hVsmall := hCcoversmall V hVCcover
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

/-- Helper for Theorem 50.3: every compact subspace of
`EuclideanSpace ℝ (Fin N)` has covering-dimension bound `N`. -/
private lemma compactSubsetEuclideanHasCoveringDimensionLE {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X) :
    HasCoveringDimensionLE X N := by
  -- Choose a Lebesgue number, then refine by the uniformly fine order-`N + 1` cover.
  intro Acover hAcoveropen hAcovercover
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨δ, hδ⟩ := lebesgueNumberLemma Acover hAcoveropen hAcovercover
  obtain ⟨Bcover, hBcoveropen, hBcovercover, hBcoverorder, hBcoversmall⟩ :=
    existsFineSubtypeEuclideanOpenCover X δ hδ.pos
  refine ⟨Bcover, smallDiameterOpenCoverIsOpenRefinement hδ hBcoveropen hBcoversmall,
    hBcovercover, ?_⟩
  simpa using hBcoverorder
/-- Helper for Theorem 50.3: covering-dimension bounds are preserved by homeomorphisms. -/
private lemma homeomorphPreservesCoveringDimensionLE
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {n : ℕ} (h : HasCoveringDimensionLE X n) :
    HasCoveringDimensionLE Y n := by
  -- Pull an arbitrary cover back to the source and push the controlled refinement forward.
  rw [hasCoveringDimensionLE_iff_pointwise] at h ⊢
  intro Acover hAcoveropen hAcovercover
  let Acover' : Set (Set X) := (fun U : Set Y ↦ e ⁻¹' U) '' Acover
  have hAcover'open : ∀ U ∈ Acover', IsOpen U := by
    rintro U ⟨A, hA, rfl⟩
    exact (hAcoveropen A hA).preimage e.continuous
  have hAcover'cover : ⋃₀ Acover' = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e x ∈ ⋃₀ Acover := hAcovercover.symm ▸ Set.mem_univ (e x)
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨A, hA, hxA⟩ := hx
    exact ⟨e ⁻¹' A, ⟨A, hA, rfl⟩, hxA⟩
  obtain ⟨Bcover, hBcoverrefines, hBcovercover, hBcoverorder⟩ :=
    h Acover' hAcover'open hAcover'cover
  let Bcover' : Set (Set Y) := (fun B : Set X ↦ e '' B) '' Bcover
  refine ⟨Bcover', ?_, ?_, ?_⟩
  · -- Images of the pulled-back parents give an open refinement of the original cover.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨B, hB, rfl⟩
      obtain ⟨A', hA', hBA⟩ := hBcoverrefines.subset_of_mem hB
      obtain ⟨A, hA, rfl⟩ := hA'
      refine ⟨A, hA, ?_⟩
      rintro y ⟨x, hxB, rfl⟩
      exact hBA hxB
    · rintro V ⟨B, hB, rfl⟩
      exact e.isOpen_image.mpr (hBcoverrefines.isOpen_of_mem hB)
  · -- Surjectivity of the homeomorphism transports the covering property.
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.symm y ∈ ⋃₀ Bcover := hBcovercover.symm ▸ Set.mem_univ (e.symm y)
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨B, hB, hyB⟩ := hy
    exact ⟨e '' B, ⟨B, hB, rfl⟩, ⟨e.symm y, hyB, e.apply_symm_apply y⟩⟩
  · -- Containing members correspond bijectively, so point multiplicity is unchanged.
    intro y
    let S : Set (Set X) := {B ∈ Bcover | e.symm y ∈ B}
    have hmembers : {V ∈ Bcover' | y ∈ V} = (fun B : Set X ↦ e '' B) '' S := by
      ext V
      constructor
      · rintro ⟨⟨B, hB, rfl⟩, hyB⟩
        obtain ⟨x, hxB, hxy⟩ := hyB
        have hx : x = e.symm y := by
          simpa using congrArg e.symm hxy
        exact ⟨B, ⟨hB, hx ▸ hxB⟩, rfl⟩
      · rintro ⟨B, ⟨hB, hyB⟩, rfl⟩
        exact ⟨⟨B, hB, rfl⟩, ⟨e.symm y, hyB, e.apply_symm_apply y⟩⟩
    rw [hmembers, e.injective.image_injective.encard_image]
    exact hBcoverorder (e.symm y)
/-- Helper for Theorem 50.3: an open cover can be refined with controlled order on
a closed subspace whose covering dimension is bounded. -/
private lemma existsOpenRefinementOrderLEOnClosed
    {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hYclosed : IsClosed Y) (hYdim : HasCoveringDimensionLE Y n)
    (Acover : Set (Set X)) (hAopen : ∀ A ∈ Acover, IsOpen A)
    (hAcover : ⋃₀ Acover = Set.univ) :
    ∃ Bcover : Set (Set X),
      IsOpenRefinement Bcover Acover ∧ ⋃₀ Bcover = Set.univ ∧
        ∀ y : Y, Set.encard {B ∈ Bcover | y.1 ∈ B} ≤ (n + 1 : ℕ) := by
  classical
  -- First refine the trace of the original cover on the closed subspace.
  let traceCover : Set (Set Y) :=
    (fun A : Set X ↦ ((↑) : Y → X) ⁻¹' A) '' Acover
  have htraceOpen : ∀ A ∈ traceCover, IsOpen A := by
    rintro A ⟨U, hU, rfl⟩
    exact (hAopen U hU).preimage continuous_subtype_val
  have htraceCover : ⋃₀ traceCover = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have hy : y.1 ∈ ⋃₀ Acover := hAcover.symm ▸ Set.mem_univ y.1
    rw [Set.mem_sUnion] at hy ⊢
    obtain ⟨A, hA, hyA⟩ := hy
    exact ⟨((↑) : Y → X) ⁻¹' A, ⟨A, hA, rfl⟩, hyA⟩
  obtain ⟨traceRefinement, hrefines, hrefinementCover, hrefinementOrder⟩ :=
    hYdim traceCover htraceOpen htraceCover
  -- Choose one ambient open representative and one original parent for each trace member.
  have hparentExists (B : traceRefinement) :
      ∃ A : Acover, (B.1 : Set Y) ⊆ ((↑) : Y → X) ⁻¹' (A.1 : Set X) := by
    obtain ⟨T, hT, hBT⟩ := hrefines.subset_of_mem B.2
    obtain ⟨A, hA, rfl⟩ := hT
    exact ⟨⟨A, hA⟩, hBT⟩
  choose parent hparent using hparentExists
  have hambientExists (B : traceRefinement) :
      ∃ U : Set X, IsOpen U ∧ ((↑) : Y → X) ⁻¹' U = (B.1 : Set Y) := by
    exact isOpen_induced_iff.mp (hrefines.isOpen_of_mem B.2)
  choose ambient hambientOpen hambientTrace using hambientExists
  let extended : traceRefinement → Set X :=
    fun B ↦ ambient B ∩ (parent B : Set X)
  let outside : Acover → Set X := fun A ↦ (A : Set X) \ Y
  let Bcover : Set (Set X) := Set.range (Sum.elim extended outside)
  refine ⟨Bcover, ?_, ?_, ?_⟩
  · -- Intersecting with the chosen parent preserves both openness and refinement.
    rw [isOpenRefinement_iff, isRefinement_iff]
    constructor
    · rintro V ⟨j, rfl⟩
      cases j with
      | inl B =>
          exact ⟨parent B, (parent B).2, Set.inter_subset_right⟩
      | inr A =>
          exact ⟨A, A.2, Set.sdiff_subset⟩
    · rintro V ⟨j, rfl⟩
      cases j with
      | inl B =>
          exact (hambientOpen B).inter (hAopen (parent B) (parent B).2)
      | inr A =>
          exact (hAopen A A.2).sdiff hYclosed
  · -- Trace members cover `Y`; the original members with `Y` removed cover its complement.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    by_cases hxY : x ∈ Y
    · let y : Y := ⟨x, hxY⟩
      have hy : y ∈ ⋃₀ traceRefinement :=
        hrefinementCover.symm ▸ Set.mem_univ y
      rw [Set.mem_sUnion] at hy
      obtain ⟨B, hB, hyB⟩ := hy
      let j : traceRefinement := ⟨B, hB⟩
      have hyAmbient : x ∈ ambient j := by
        have : y ∈ ((↑) : Y → X) ⁻¹' ambient j := by
          rw [hambientTrace j]
          exact hyB
        exact this
      have hyParent : x ∈ (parent j : Set X) := hparent j hyB
      exact ⟨extended j, ⟨Sum.inl j, rfl⟩, hyAmbient, hyParent⟩
    · have hx : x ∈ ⋃₀ Acover := hAcover.symm ▸ Set.mem_univ x
      rw [Set.mem_sUnion] at hx
      obtain ⟨A, hA, hxA⟩ := hx
      let j : Acover := ⟨A, hA⟩
      exact ⟨outside j, ⟨Sum.inr j, rfl⟩, hxA, hxY⟩
  · -- At a point of `Y`, outside members disappear and each remaining member has one trace.
    intro y
    let source : Set traceRefinement := {B | y ∈ (B.1 : Set Y)}
    have hsub : {V ∈ Bcover | y.1 ∈ V} ⊆ extended '' source := by
      intro V hV
      obtain ⟨j, rfl⟩ := hV.1
      cases j with
      | inl B =>
          have hyTrace : y ∈ (B.1 : Set Y) := by
            rw [← hambientTrace B]
            exact hV.2.1
          exact ⟨B, hyTrace, rfl⟩
      | inr A =>
          exact (hV.2.2 y.2).elim
    have hsourceImage :
        ((fun B : traceRefinement ↦ (B.1 : Set Y)) '' source) =
          {B ∈ traceRefinement | y ∈ B} := by
      ext B
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j.2, hj⟩
      · intro hB
        exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩
    calc
      Set.encard {V ∈ Bcover | y.1 ∈ V}
          ≤ Set.encard (extended '' source) := Set.encard_le_encard hsub
      _ ≤ Set.encard source := Set.encard_image_le extended source
      _ = Set.encard {B ∈ traceRefinement | y ∈ B} := by
        rw [← hsourceImage, Subtype.val_injective.encard_image]
      _ ≤ n + 1 := (Set.hasOrderLE_iff.mp hrefinementOrder) y

/-- Helper for Theorem 50.3: two closed subspaces covering a space transmit a
common covering-dimension bound to the ambient space. -/
private lemma hasCoveringDimensionLE_of_closed_union
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (hYclosed : IsClosed Y) (hZclosed : IsClosed Z)
    (hcover : Y ∪ Z = Set.univ)
    (hYdim : HasCoveringDimensionLE Y n)
    (hZdim : HasCoveringDimensionLE Z n) :
    HasCoveringDimensionLE X n := by
  classical
  intro Acover hAopen hAcover
  -- Successively control multiplicity on `Y` and `Z` while retaining refinement.
  obtain ⟨Bcover, hBrefines, hBcover, hBorderY⟩ :=
    existsOpenRefinementOrderLEOnClosed hYclosed hYdim Acover hAopen hAcover
  obtain ⟨Ccover, hCrefines, hCcover, hCorderZ⟩ :=
    existsOpenRefinementOrderLEOnClosed hZclosed hZdim Bcover
      (fun B hB ↦ hBrefines.isOpen_of_mem hB) hBcover
  have hparentExists (C : Ccover) :
      ∃ B : Bcover, (C.1 : Set X) ⊆ (B.1 : Set X) := by
    obtain ⟨B, hB, hCB⟩ := hCrefines.subset_of_mem C.2
    exact ⟨⟨B, hB⟩, hCB⟩
  choose parent hparent using hparentExists
  -- Amalgamate all second-stage members having the same first-stage parent.
  let consolidated : Bcover → Set X := fun B ↦
    ⋃ C : {C : Ccover // parent C = B}, (C.1.1 : Set X)
  let Dcover : Set (Set X) := Set.range consolidated
  have hDrefinesB : IsRefinement Dcover Bcover := by
    rw [isRefinement_iff]
    rintro D ⟨B, rfl⟩
    refine ⟨B, B.2, ?_⟩
    intro x hx
    obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hx
    rw [← C.2]
    exact hparent C.1 hxC
  have hDopen : ∀ D ∈ Dcover, IsOpen D := by
    rintro D ⟨B, rfl⟩
    apply isOpen_iUnion
    intro C
    exact hCrefines.isOpen_of_mem C.1.2
  refine ⟨Dcover, ?_, ?_, ?_⟩
  · -- Amalgamation remains an open refinement of the original cover.
    rw [isOpenRefinement_iff]
    exact ⟨hDrefinesB.trans hBrefines.toIsRefinement, hDopen⟩
  · -- Every second-stage member lies in the amalgam indexed by its parent.
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃₀ Ccover := hCcover.symm ▸ Set.mem_univ x
    rw [Set.mem_sUnion] at hx ⊢
    obtain ⟨C, hC, hxC⟩ := hx
    let j : Ccover := ⟨C, hC⟩
    have hxConsolidated : x ∈ consolidated (parent j) := by
      rw [Set.mem_iUnion]
      exact ⟨⟨j, rfl⟩, hxC⟩
    exact ⟨consolidated (parent j), ⟨parent j, rfl⟩, hxConsolidated⟩
  · -- On `Y` use first-stage parents; on `Z` use second-stage witnesses.
    rw [Set.hasOrderLE_iff]
    intro x
    have hxYZ : x ∈ Y ∪ Z := hcover.symm ▸ Set.mem_univ x
    rcases hxYZ with hxY | hxZ
    · let y : Y := ⟨x, hxY⟩
      let source : Set Bcover := {B | x ∈ (B.1 : Set X)}
      have hsub : {D ∈ Dcover | x ∈ D} ⊆ consolidated '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        have hxB : x ∈ (B.1 : Set X) := by
          rw [← C.2]
          exact hparent C.1 hxC
        exact ⟨B, hxB, rfl⟩
      have hsourceImage :
          ((fun B : Bcover ↦ (B.1 : Set X)) '' source) =
            {B ∈ Bcover | x ∈ B} := by
        ext B
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.2, hj⟩
        · intro hB
          exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩
      calc
        Set.encard {D ∈ Dcover | x ∈ D}
            ≤ Set.encard (consolidated '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le consolidated source
        _ = Set.encard {B ∈ Bcover | x ∈ B} := by
          rw [← hsourceImage, Subtype.val_injective.encard_image]
        _ ≤ n + 1 := hBorderY y
    · let z : Z := ⟨x, hxZ⟩
      let source : Set Ccover := {C | x ∈ (C.1 : Set X)}
      let amalgamate : Ccover → Set X := fun C ↦ consolidated (parent C)
      have hsub : {D ∈ Dcover | x ∈ D} ⊆ amalgamate '' source := by
        intro D hD
        obtain ⟨B, rfl⟩ := hD.1
        obtain ⟨C, hxC⟩ := Set.mem_iUnion.mp hD.2
        refine ⟨C.1, hxC, ?_⟩
        exact congrArg consolidated C.2
      have hsourceImage :
          ((fun C : Ccover ↦ (C.1 : Set X)) '' source) =
            {C ∈ Ccover | x ∈ C} := by
        ext C
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.2, hj⟩
        · intro hC
          exact ⟨⟨C, hC.1⟩, hC.2, rfl⟩
      calc
        Set.encard {D ∈ Dcover | x ∈ D}
            ≤ Set.encard (amalgamate '' source) := Set.encard_le_encard hsub
        _ ≤ Set.encard source := Set.encard_image_le amalgamate source
        _ = Set.encard {C ∈ Ccover | x ∈ C} := by
          rw [← hsourceImage, Subtype.val_injective.encard_image]
        _ ≤ n + 1 := hCorderZ z

/-- Helper for Theorem 50.3: a union of two closed subspaces inherits a common
covering-dimension bound. -/
private lemma hasCoveringDimensionLE_closedUnion
    {X : Type u} [TopologicalSpace X] {S T : Set X} {n : ℕ}
    (hSclosed : IsClosed S) (hTclosed : IsClosed T)
    (hSdim : HasCoveringDimensionLE S n)
    (hTdim : HasCoveringDimensionLE T n) :
    HasCoveringDimensionLE (S ∪ T : Set X) n := by
  let W : Set X := S ∪ T
  let SW : Set W := ((↑) : W → X) ⁻¹' S
  let TW : Set W := ((↑) : W → X) ⁻¹' T
  have hSWclosed : IsClosed SW := hSclosed.preimage continuous_subtype_val
  have hTWclosed : IsClosed TW := hTclosed.preimage continuous_subtype_val
  have hSWcover : SW ∪ TW = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    rcases w.2 with hwS | hwT
    · exact Or.inl hwS
    · exact Or.inr hwT
  -- Each pulled-back piece is homeomorphic to the corresponding original subtype.
  let hSW : S ⊆ W := Set.subset_union_left
  let incS : S → W := Set.inclusion hSW
  let fS : S → SW := fun s ↦ ⟨incS s, s.2⟩
  have hfS : Topology.IsEmbedding fS :=
    (Topology.IsEmbedding.inclusion hSW).codRestrict SW fun s ↦ s.2
  have hfSsurj : Function.Surjective fS := by
    intro w
    refine ⟨⟨w.1.1, w.2⟩, ?_⟩
    exact Subtype.ext (Subtype.ext rfl)
  have hSWdim : HasCoveringDimensionLE SW n :=
    homeomorphPreservesCoveringDimensionLE
      (hfS.toHomeomorphOfSurjective hfSsurj) hSdim
  let hTW : T ⊆ W := Set.subset_union_right
  let incT : T → W := Set.inclusion hTW
  let fT : T → TW := fun t ↦ ⟨incT t, t.2⟩
  have hfT : Topology.IsEmbedding fT :=
    (Topology.IsEmbedding.inclusion hTW).codRestrict TW fun t ↦ t.2
  have hfTsurj : Function.Surjective fT := by
    intro w
    refine ⟨⟨w.1.1, w.2⟩, ?_⟩
    exact Subtype.ext (Subtype.ext rfl)
  have hTWdim : HasCoveringDimensionLE TW n :=
    homeomorphPreservesCoveringDimensionLE
      (hfT.toHomeomorphOfSurjective hfTsurj) hTdim
  exact hasCoveringDimensionLE_of_closed_union
    hSWclosed hTWclosed hSWcover hSWdim hTWdim

/-- Helper for Theorem 50.3: a finite closed cover whose members have a common
covering-dimension bound transmits that bound to the ambient space. -/
private lemma hasCoveringDimensionLE_of_finiteClosedCover
    {X : Type u} [TopologicalSpace X] {ι : Type v} [Finite ι] {n : ℕ}
    (Y : ι → Set X) (hclosed : ∀ i, IsClosed (Y i))
    (hcover : (⋃ i, Y i) = Set.univ)
    (hdim : ∀ i, HasCoveringDimensionLE (Y i) n) :
    HasCoveringDimensionLE X n := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- Inductively adjoin one closed member, using the two-piece theorem at each step.
  have hfinite : ∀ s : Finset ι,
      HasCoveringDimensionLE (⋃ i ∈ s, Y i) n := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        apply hasCoveringDimensionLE_of_isEmpty
        constructor
        intro x
        simpa using x.2
    | @insert i s hi ih =>
        rw [Finset.set_biUnion_insert]
        exact hasCoveringDimensionLE_closedUnion
          (hclosed i) (isClosed_biUnion_finset fun j _ ↦ hclosed j) (hdim i) ih
  have hall := hfinite Finset.univ
  have hunion : (⋃ i ∈ (Finset.univ : Finset ι), Y i) = Set.univ := by
    simpa using hcover
  rw [hunion] at hall
  exact homeomorphPreservesCoveringDimensionLE (Homeomorph.Set.univ X) hall

/-- Helper for Theorem 50.3: a compact subset of a Euclidean-charted locally compact
Hausdorff space is an exact finite union of compact closed sets lying in chart sources. -/
private lemma existsFiniteClosedChartCover {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [LocallyCompactSpace M] (K : Set M) (hK : IsCompact K) :
    ∃ (t : Finset M) (C : t → Set M), K = ⋃ i, C i ∧
      (∀ i, IsClosed (C i)) ∧ (∀ i, IsCompact (C i)) ∧
      ∀ i, C i ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source := by
  classical
  -- First reduce the full family of chart sources to a finite cover of `K`.
  have h_chart_open : ∀ x : M,
      IsOpen (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x
    exact (chartAt (EuclideanSpace ℝ (Fin m)) x).open_source
  have h_chart_cover :
      K ⊆ ⋃ x : M, (chartAt (EuclideanSpace ℝ (Fin m)) x).source := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source (EuclideanSpace ℝ (Fin m)) x⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin m)) x).source)
    h_chart_open h_chart_cover
  let U : t → Set M := fun i ↦ (chartAt (EuclideanSpace ℝ (Fin m)) i.1).source
  have hKU : K ⊆ ⋃ i, U i := by
    intro x hx
    have hx_cover := ht hx
    simp only [Set.mem_iUnion] at hx_cover ⊢
    obtain ⟨i, hi, hxi⟩ := hx_cover
    exact ⟨⟨i, hi⟩, hxi⟩
  -- Shrink that finite cover to compact closed sets still contained in their charts.
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    exact (chartAt (EuclideanSpace ℝ (Fin m)) i.1).open_source
  have hU_pointFinite : ∀ x ∈ K, {i | x ∈ U i}.Finite := by
    intro _ _
    exact Set.toFinite _
  obtain ⟨V, hKV, hV_closed, hV_subset, hV_compact⟩ :=
    exists_subset_iUnion_compact_subset_t2space (u := U) hK hU_open hU_pointFinite hKU
  let C : t → Set M := fun i ↦ K ∩ V i
  refine ⟨t, C, ?_, ?_, ?_, ?_⟩
  · -- Intersecting with `K` changes containment into an exact union equality.
    ext x
    constructor
    · intro hxK
      have hxV := hKV hxK
      rw [Set.mem_iUnion] at hxV ⊢
      obtain ⟨i, hxi⟩ := hxV
      exact ⟨i, hxK, hxi⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨i, hxi⟩ := hx
      exact hxi.1
  · intro i
    exact hK.isClosed.inter (hV_closed i)
  · intro i
    exact (hV_compact i).inter_left hK.isClosed
  · intro i _ hxi
    exact hV_subset i hxi.2

/-- Helper for Theorem 50.3: a compact set contained in one chart source has covering
dimension at most the dimension of the Euclidean model. -/
private lemma compactSubsetChartSourceHasCoveringDimensionLE {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    (K : Set M) (hK : IsCompact K) (x : M)
    (hK_source : K ⊆ (chartAt (EuclideanSpace ℝ (Fin m)) x).source) :
    HasCoveringDimensionLE K m := by
  -- The chart sends the compact set to a compact subset of the Euclidean model.
  have h_image_compact :
      IsCompact ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) :=
    hK.image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin m)) x).continuousOn.mono hK_source)
  have h_image_eq :
      (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K =
        (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K := by
    rfl
  let restrictedChart :
      K ≃ₜ (chartAt (EuclideanSpace ℝ (Fin m)) x) '' K :=
    (chartAt (EuclideanSpace ℝ (Fin m)) x).homeomorphOfImageSubsetSource
      hK_source h_image_eq
  -- Apply the Euclidean bound and transport it back through the restricted chart.
  have h_image_dimension :
      HasCoveringDimensionLE
        ((chartAt (EuclideanSpace ℝ (Fin m)) x) '' K) m :=
    compactSubsetEuclideanHasCoveringDimensionLE _ h_image_compact
  exact homeomorphPreservesCoveringDimensionLE restrictedChart.symm h_image_dimension
/-- Theorem 50.3. The covering dimension of a compact `m`-manifold is at most `m`. -/
theorem compactManifold_coveringDimension_le {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [TopologicalManifold m M] [CompactSpace M] :
    HasCoveringDimensionLE M m := by
  -- Manifold charts supply local compactness, so compactness yields a finite closed chart cover.
  letI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) M
  obtain ⟨t, C, hCunion, hCclosed, hCcompact, hCsource⟩ :=
    existsFiniteClosedChartCover (m := m) (Set.univ : Set M)
      CompactSpace.isCompact_univ
  -- Restricted charts transport the Euclidean bound to every closed chart piece.
  have hCdim : ∀ i, HasCoveringDimensionLE (C i) m := by
    intro i
    exact compactSubsetChartSourceHasCoveringDimensionLE
      (C i) (hCcompact i) i.1 (hCsource i)
  -- The finite closed-cover theorem assembles the local bounds without increasing order.
  apply hasCoveringDimensionLE_of_finiteClosedCover C hCclosed
  · exact hCunion.symm
  · exact hCdim
