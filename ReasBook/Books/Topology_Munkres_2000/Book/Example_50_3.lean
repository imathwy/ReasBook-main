module

public import Topology_Munkres_2000.Book.Definition_50_3.CoveringDimension
public import Topology_Munkres_2000.Book.Definition_20_1
public import Topology_Munkres_2000.Book.Lemma_27_5
public import Mathlib.Topology.MetricSpace.Isometry

public section

open scoped CoveringDimension

open Set

universe u v

/-- Helper for Example 50.3: preimages of a family do not increase its pointwise order. -/
lemma preimageFamily_hasOrderLE {Y : Type u} {Z : Type v}
    (f : Y → Z) (𝒞 : Set (Set Z)) (n : ℕ) (h𝒞 : 𝒞.HasOrderLE n) :
    ((fun V : Set Z ↦ f ⁻¹' V) '' 𝒞).HasOrderLE n := by
  -- Compare the sets containing a point with the image of the corresponding source family.
  rw [Set.hasOrderLE_iff] at h𝒞 ⊢
  intro y
  let source : Set (Set Z) := {V ∈ 𝒞 | f y ∈ V}
  let pullback : (Set Z) → Set Y := fun V ↦ f ⁻¹' V
  have hsub : {B ∈ pullback '' 𝒞 | y ∈ B} ⊆ pullback '' source := by
    intro B hB
    obtain ⟨V, hV𝒞, rfl⟩ := hB.1
    exact ⟨V, ⟨hV𝒞, hB.2⟩, rfl⟩
  calc
    Set.encard {B ∈ pullback '' 𝒞 | y ∈ B}
        ≤ Set.encard (pullback '' source) := Set.encard_le_encard hsub
    _ ≤ Set.encard source := Set.encard_image_le pullback source
    _ ≤ n := h𝒞 (f y)

/-- Helper for Example 50.3: the three translations used for the square grids. -/
noncomputable def planeCoverPhaseShift (c : Fin 3) : ℝ :=
  (c : ℝ) / 3

/-- Helper for Example 50.3: an open square in a translated grid of mesh `a`. -/
def shiftedOpenSquare (a : ℝ) (c : Fin 3) (p : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Ioo (a * ((p.1 : ℝ) + planeCoverPhaseShift c))
      (a * ((p.1 : ℝ) + 1 + planeCoverPhaseShift c)) ×ˢ
    Ioo (a * ((p.2 : ℝ) + planeCoverPhaseShift c))
      (a * ((p.2 : ℝ) + 1 + planeCoverPhaseShift c))

/-- Helper for Example 50.3: the family of all squares in one translated grid. -/
def shiftedSquareFamily (a : ℝ) (c : Fin 3) : Set (Set (ℝ × ℝ)) :=
  Set.range (shiftedOpenSquare a c)

/-- Helper for Example 50.3: a real coordinate lies on the boundary grid of at most one phase. -/
lemma gridBoundary_phase_unique {a x : ℝ} (ha : 0 < a) {c d : Fin 3}
    (hc : ∃ n : ℤ, x = a * ((n : ℝ) + planeCoverPhaseShift c))
    (hd : ∃ n : ℤ, x = a * ((n : ℝ) + planeCoverPhaseShift d)) :
    c = d := by
  -- Cancel the positive mesh, then rule out distinct thirds by integer arithmetic.
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm⟩ := hd
  have hscaled : (n : ℝ) + planeCoverPhaseShift c =
      (m : ℝ) + planeCoverPhaseShift d := by
    nlinarith
  have hscaled' : (3 * n : ℝ) + c = 3 * m + d := by
    dsimp [planeCoverPhaseShift] at hscaled
    nlinarith
  have hinteger : 3 * n + c.val = 3 * m + d.val := by
    exact_mod_cast hscaled'
  apply Fin.ext
  omega

/-- Helper for Example 50.3: one phase avoids the boundary grids of two coordinates. -/
lemma exists_phase_avoiding_gridBoundaries {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    ∃ c : Fin 3,
      (¬ ∃ n : ℤ, x = a * ((n : ℝ) + planeCoverPhaseShift c)) ∧
        ¬ ∃ n : ℤ, y = a * ((n : ℝ) + planeCoverPhaseShift c) := by
  -- If all three phases failed, two failures would concern the same coordinate,
  -- contradicting uniqueness of that coordinate's boundary phase.
  by_contra hnone
  have hfail (c : Fin 3) :
      (∃ n : ℤ, x = a * ((n : ℝ) + planeCoverPhaseShift c)) ∨
        ∃ n : ℤ, y = a * ((n : ℝ) + planeCoverPhaseShift c) := by
    by_contra h
    apply hnone
    refine ⟨c, ?_, ?_⟩
    · intro hx
      exact h (Or.inl hx)
    · intro hy
      exact h (Or.inr hy)
  obtain hx0 | hy0 := hfail (0 : Fin 3)
  · obtain hx1 | hy1 := hfail (1 : Fin 3)
    · have h01 : (0 : Fin 3) = 1 := gridBoundary_phase_unique ha hx0 hx1
      norm_num at h01
    · obtain hx2 | hy2 := hfail (2 : Fin 3)
      · have h02 : (0 : Fin 3) = 2 := gridBoundary_phase_unique ha hx0 hx2
        omega
      · have h12 : (1 : Fin 3) = 2 := gridBoundary_phase_unique ha hy1 hy2
        omega
  · obtain hx1 | hy1 := hfail (1 : Fin 3)
    · obtain hx2 | hy2 := hfail (2 : Fin 3)
      · have h12 : (1 : Fin 3) = 2 := gridBoundary_phase_unique ha hx1 hx2
        omega
      · have h02 : (0 : Fin 3) = 2 := gridBoundary_phase_unique ha hy0 hy2
        omega
    · have h01 : (0 : Fin 3) = 1 := gridBoundary_phase_unique ha hy0 hy1
      norm_num at h01

/-- Helper for Example 50.3: avoiding a phase boundary selects a containing shifted square. -/
lemma mem_shiftedOpenSquare_of_phaseAvoidance {a x y : ℝ} (ha : 0 < a) (c : Fin 3)
    (hx : ¬ ∃ n : ℤ, x = a * ((n : ℝ) + planeCoverPhaseShift c))
    (hy : ¬ ∃ n : ℤ, y = a * ((n : ℝ) + planeCoverPhaseShift c)) :
    (x, y) ∈ shiftedOpenSquare a c
      (⌊x / a - planeCoverPhaseShift c⌋, ⌊y / a - planeCoverPhaseShift c⌋) := by
  -- Floor bounds become strict lower bounds because the chosen phase avoids equality.
  simp only [shiftedOpenSquare, Set.mem_prod, Set.mem_Ioo]
  constructor
  · have hfloor := Int.floor_le (x / a - planeCoverPhaseShift c)
    have hstrict : (⌊x / a - planeCoverPhaseShift c⌋ : ℝ) <
        x / a - planeCoverPhaseShift c := by
      apply lt_of_le_of_ne hfloor
      intro heq
      apply hx
      refine ⟨⌊x / a - planeCoverPhaseShift c⌋, ?_⟩
      field_simp [ha.ne'] at heq ⊢
      nlinarith
    have hupp := Int.lt_floor_add_one (x / a - planeCoverPhaseShift c)
    constructor <;> field_simp [ha.ne'] at hstrict hupp ⊢ <;> nlinarith
  · have hfloor := Int.floor_le (y / a - planeCoverPhaseShift c)
    have hstrict : (⌊y / a - planeCoverPhaseShift c⌋ : ℝ) <
        y / a - planeCoverPhaseShift c := by
      apply lt_of_le_of_ne hfloor
      intro heq
      apply hy
      refine ⟨⌊y / a - planeCoverPhaseShift c⌋, ?_⟩
      field_simp [ha.ne'] at heq ⊢
      nlinarith
    have hupp := Int.lt_floor_add_one (y / a - planeCoverPhaseShift c)
    constructor <;> field_simp [ha.ne'] at hstrict hupp ⊢ <;> nlinarith

/-- Helper for Example 50.3: two overlapping intervals in one shifted grid have the same index. -/
lemma shiftedOpenInterval_index_unique {a z : ℝ} (ha : 0 < a) (c : Fin 3) {n m : ℤ}
    (hn : z ∈ Ioo (a * ((n : ℝ) + planeCoverPhaseShift c))
      (a * ((n : ℝ) + 1 + planeCoverPhaseShift c)))
    (hm : z ∈ Ioo (a * ((m : ℝ) + planeCoverPhaseShift c))
      (a * ((m : ℝ) + 1 + planeCoverPhaseShift c))) :
    n = m := by
  -- Cross the lower bound from each interval with the upper bound from the other.
  have hnm : (n : ℝ) < m + 1 := by
    nlinarith [hn.1, hm.2]
  have hmn : (m : ℝ) < n + 1 := by
    nlinarith [hm.1, hn.2]
  have hnmInt : n < m + 1 := by
    exact_mod_cast hnm
  have hmnInt : m < n + 1 := by
    exact_mod_cast hmn
  omega

/-- Helper for Example 50.3: squares in a fixed translated grid are pointwise unique. -/
lemma shiftedSquareFamily_pointwiseUnique {a : ℝ} (ha : 0 < a) (c : Fin 3)
    (z : ℝ × ℝ) {V W : Set (ℝ × ℝ)}
    (hV : V ∈ shiftedSquareFamily a c) (hW : W ∈ shiftedSquareFamily a c)
    (hzV : z ∈ V) (hzW : z ∈ W) :
    V = W := by
  -- Recover both grid indices and compare their coordinate intervals separately.
  obtain ⟨p, rfl⟩ := hV
  obtain ⟨q, rfl⟩ := hW
  simp only [shiftedOpenSquare, Set.mem_prod] at hzV hzW
  have hpq1 : p.1 = q.1 := shiftedOpenInterval_index_unique ha c hzV.1 hzW.1
  have hpq2 : p.2 = q.2 := shiftedOpenInterval_index_unique ha c hzV.2 hzW.2
  have hpq : p = q := Prod.ext hpq1 hpq2
  rw [hpq]

/-- Helper for Example 50.3: the union of three pointwise-unique families has order at
most three. -/
lemma threePointwiseUniqueFamilies_hasOrderLE {Y : Type u}
    (𝒞₀ 𝒞₁ 𝒞₂ : Set (Set Y))
    (hunique : ∀ i : Fin 3, ∀ y : Y, ∀ V ∈ ![𝒞₀, 𝒞₁, 𝒞₂] i,
      ∀ W ∈ ![𝒞₀, 𝒞₁, 𝒞₂] i, y ∈ V → y ∈ W → V = W) :
    (𝒞₀ ∪ 𝒞₁ ∪ 𝒞₂).HasOrderLE 3 := by
  -- Split the members containing a point by phase; each part has cardinality at most one.
  rw [Set.hasOrderLE_iff]
  intro y
  let S0 : Set (Set Y) := {V ∈ 𝒞₀ | y ∈ V}
  let S1 : Set (Set Y) := {V ∈ 𝒞₁ | y ∈ V}
  let S2 : Set (Set Y) := {V ∈ 𝒞₂ | y ∈ V}
  have hsub : {V ∈ 𝒞₀ ∪ 𝒞₁ ∪ 𝒞₂ | y ∈ V} ⊆ S0 ∪ S1 ∪ S2 := by
    intro V hV
    rcases hV.1 with (hV0 | hV1) | hV2
    · exact Or.inl (Or.inl ⟨hV0, hV.2⟩)
    · exact Or.inl (Or.inr ⟨hV1, hV.2⟩)
    · exact Or.inr ⟨hV2, hV.2⟩
  have hS0 : Set.encard S0 ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro V W hV hW
    exact hunique 0 y V hV.1 W hW.1 hV.2 hW.2
  have hS1 : Set.encard S1 ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro V W hV hW
    exact hunique 1 y V hV.1 W hW.1 hV.2 hW.2
  have hS2 : Set.encard S2 ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro V W hV hW
    exact hunique 2 y V hV.1 W hW.1 hV.2 hW.2
  calc
    Set.encard {V ∈ 𝒞₀ ∪ 𝒞₁ ∪ 𝒞₂ | y ∈ V}
        ≤ Set.encard (S0 ∪ S1 ∪ S2) := Set.encard_le_encard hsub
    _ ≤ Set.encard (S0 ∪ S1) + Set.encard S2 := Set.encard_union_le _ _
    _ ≤ (Set.encard S0 + Set.encard S1) + Set.encard S2 := by
      gcongr
      exact Set.encard_union_le _ _
    _ ≤ (1 + 1) + 1 := add_le_add (add_le_add hS0 hS1) hS2
    _ = 3 := by norm_num

/-- Helper for Example 50.3: each shifted square is open, bounded, and has diameter at
most its mesh. -/
lemma shiftedOpenSquare_isOpen_isBounded_diam {a : ℝ} (ha : 0 < a) (c : Fin 3)
    (p : ℤ × ℤ) :
    IsOpen (shiftedOpenSquare a c p) ∧
      Bornology.IsBounded (shiftedOpenSquare a c p) ∧
        Metric.diam (shiftedOpenSquare a c p) ≤ a := by
  -- Openness and boundedness are inherited from the two interval factors.
  constructor
  · exact isOpen_Ioo.prod isOpen_Ioo
  constructor
  · exact (Metric.isBounded_Ioo _ _).prod (Metric.isBounded_Ioo _ _)
  · -- Coordinate differences are below the mesh, hence so is the product sup distance.
    apply Metric.diam_le_of_forall_dist_le ha.le
    intro x hx y hy
    simp only [shiftedOpenSquare, Set.mem_prod, Set.mem_Ioo] at hx hy
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    apply max_le
    · rw [abs_le]
      constructor <;> nlinarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
    · rw [abs_le]
      constructor <;> nlinarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]

/-- Helper for Example 50.3: a uniformly fine open cover of the Euclidean plane exists
with pointwise order at most three. -/
lemma exists_planeOpenCover_orderThree (ε : ℝ) (hε : 0 < ε) :
    ∃ 𝒞 : Set (Set (ℝ × ℝ)),
      (∀ V ∈ 𝒞, IsOpen V) ∧ ⋃₀ 𝒞 = Set.univ ∧ 𝒞.HasOrderLE 3 ∧
        ∀ V ∈ 𝒞, Bornology.IsBounded V ∧ Metric.diam V < ε := by
  -- Route correction: three diagonally shifted square grids avoid the edge-neighborhood
  -- construction while preserving the source proof's three disjoint levels.
  let a : ℝ := ε / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have haε : a < ε := by
    dsimp [a]
    linarith
  let 𝒞₀ := shiftedSquareFamily a (0 : Fin 3)
  let 𝒞₁ := shiftedSquareFamily a (1 : Fin 3)
  let 𝒞₂ := shiftedSquareFamily a (2 : Fin 3)
  refine ⟨𝒞₀ ∪ 𝒞₁ ∪ 𝒞₂, ?_, ?_, ?_, ?_⟩
  · -- Every member is an open product of two open intervals.
    intro V hV
    rcases hV with (hV | hV) | hV
    · obtain ⟨p, rfl⟩ := hV
      exact (shiftedOpenSquare_isOpen_isBounded_diam ha 0 p).1
    · obtain ⟨p, rfl⟩ := hV
      exact (shiftedOpenSquare_isOpen_isBounded_diam ha 1 p).1
    · obtain ⟨p, rfl⟩ := hV
      exact (shiftedOpenSquare_isOpen_isBounded_diam ha 2 p).1
  · -- Boundary avoidance supplies a square from one of the three phases through each point.
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨c, hcx, hcy⟩ := exists_phase_avoiding_gridBoundaries ha z.1 z.2
    let p : ℤ × ℤ :=
      (⌊z.1 / a - planeCoverPhaseShift c⌋, ⌊z.2 / a - planeCoverPhaseShift c⌋)
    have hzp : z ∈ shiftedOpenSquare a c p := by
      exact mem_shiftedOpenSquare_of_phaseAvoidance ha c hcx hcy
    have hc : c = 0 ∨ c = 1 ∨ c = 2 := by
      have hcval := c.isLt
      omega
    rw [Set.mem_sUnion]
    rcases hc with rfl | rfl | rfl
    · exact ⟨shiftedOpenSquare a 0 p, Or.inl (Or.inl ⟨p, rfl⟩), hzp⟩
    · exact ⟨shiftedOpenSquare a 1 p, Or.inl (Or.inr ⟨p, rfl⟩), hzp⟩
    · exact ⟨shiftedOpenSquare a 2 p, Or.inr ⟨p, rfl⟩, hzp⟩
  · -- Pointwise uniqueness inside each phase gives the global order-three bound.
    apply threePointwiseUniqueFamilies_hasOrderLE 𝒞₀ 𝒞₁ 𝒞₂
    intro i z V hV W hW hzV hzW
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have hival := i.isLt
      omega
    rcases hi with rfl | rfl | rfl
    · exact shiftedSquareFamily_pointwiseUnique ha 0 z hV hW hzV hzW
    · exact shiftedSquareFamily_pointwiseUnique ha 1 z hV hW hzV hzW
    · exact shiftedSquareFamily_pointwiseUnique ha 2 z hV hW hzV hzW
  · -- The diameter bound by `a` is strict relative to `ε`.
    intro V hV
    rcases hV with (hV | hV) | hV
    · obtain ⟨p, rfl⟩ := hV
      have hspec := shiftedOpenSquare_isOpen_isBounded_diam ha 0 p
      exact ⟨hspec.2.1, hspec.2.2.trans_lt haε⟩
    · obtain ⟨p, rfl⟩ := hV
      have hspec := shiftedOpenSquare_isOpen_isBounded_diam ha 1 p
      exact ⟨hspec.2.1, hspec.2.2.trans_lt haε⟩
    · obtain ⟨p, rfl⟩ := hV
      have hspec := shiftedOpenSquare_isOpen_isBounded_diam ha 2 p
      exact ⟨hspec.2.1, hspec.2.2.trans_lt haε⟩

/-- Helper for Example 50.3: restricting a uniformly fine order-three plane cover to a
subtype gives a nonempty uniformly fine order-three open cover. -/
lemma exists_subtypePlaneCover_orderThree
    (X : Set (ℝ × ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ ℬ : Set (Set X),
      (∀ B ∈ ℬ, IsOpen B) ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE 3 ∧
        ∀ B ∈ ℬ, B.Nonempty ∧ Bornology.IsBounded B ∧ Metric.diam B < ε := by
  -- Pull back the ambient cover and discard exactly the empty members.
  obtain ⟨𝒞, h𝒞open, h𝒞cover, h𝒞order, h𝒞small⟩ :=
    exists_planeOpenCover_orderThree ε hε
  let pullback : Set (Set X) := ((fun V : Set (ℝ × ℝ) ↦ ((↑) : X → ℝ × ℝ) ⁻¹' V) '' 𝒞)
  let ℬ : Set (Set X) := {B ∈ pullback | B.Nonempty}
  refine ⟨ℬ, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨V, hV𝒞, rfl⟩ := hB.1
    exact (h𝒞open V hV𝒞).preimage continuous_subtype_val
  · -- Every subtype point lies in a nonempty pullback member supplied by ambient coverage.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    have hx : (x : ℝ × ℝ) ∈ ⋃₀ 𝒞 := by
      rw [h𝒞cover]
      exact Set.mem_univ _
    rw [Set.mem_sUnion] at hx
    obtain ⟨V, hV𝒞, hxV⟩ := hx
    let B : Set X := ((↑) : X → ℝ × ℝ) ⁻¹' V
    have hxB : x ∈ B := hxV
    have hBpullback : B ∈ pullback := ⟨V, hV𝒞, rfl⟩
    exact ⟨B, ⟨hBpullback, ⟨x, hxB⟩⟩, hxB⟩
  · -- Filtering to nonempty members can only decrease point multiplicity.
    rw [Set.hasOrderLE_iff]
    intro x
    have hpullbackOrder : pullback.HasOrderLE 3 := by
      exact preimageFamily_hasOrderLE ((↑) : X → ℝ × ℝ) 𝒞 3 h𝒞order
    calc
      Set.encard {B ∈ ℬ | x ∈ B} ≤ Set.encard {B ∈ pullback | x ∈ B} := by
        apply Set.encard_le_encard
        intro B hB
        exact ⟨hB.1.1, hB.2⟩
      _ ≤ 3 := (Set.hasOrderLE_iff.mp hpullbackOrder) x
  · intro B hB
    have hBpullback : B ∈ pullback := hB.1
    obtain ⟨V, hV𝒞, rfl⟩ := hBpullback
    have hVsmall := h𝒞small V hV𝒞
    have himage : ((↑) : X → ℝ × ℝ) '' (((↑) : X → ℝ × ℝ) ⁻¹' V) ⊆ V :=
      Set.image_preimage_subset _ _
    have hBbounded : Bornology.IsBounded (((↑) : X → ℝ × ℝ) ⁻¹' V) := by
      apply isometry_subtype_coe.antilipschitz.isBounded_preimage
      exact hVsmall.1
    have hdiam_image :
        Metric.diam (((↑) : X → ℝ × ℝ) '' (((↑) : X → ℝ × ℝ) ⁻¹' V)) =
          Metric.diam (((↑) : X → ℝ × ℝ) ⁻¹' V) :=
      isometry_subtype_coe.diam_image _
    have hdiam_le :
        Metric.diam (((↑) : X → ℝ × ℝ) ⁻¹' V) ≤ Metric.diam V := by
      rw [← hdiam_image]
      exact Metric.diam_mono himage hVsmall.1
    exact ⟨hB.2, hBbounded, hdiam_le.trans_lt hVsmall.2⟩

/-- Helper for Example 50.3: a nonempty bounded open cover finer than a Lebesgue
number is an open refinement of the original cover. -/
lemma smallDiameterOpenCover_isOpenRefinement
    {Y : Type u} [PseudoMetricSpace Y] {𝒜 ℬ : Set (Set Y)} {δ : ℝ}
    (hδ : IsLebesgueNumber 𝒜 δ) (hℬopen : ∀ B ∈ ℬ, IsOpen B)
    (hℬsmall : ∀ B ∈ ℬ,
      B.Nonempty ∧ Bornology.IsBounded B ∧ Metric.diam B < δ) :
    IsOpenRefinement ℬ 𝒜 := by
  -- The Lebesgue-number property supplies the containing original member.
  rw [isOpenRefinement_iff]
  constructor
  · rw [isRefinement_iff]
    intro B hB
    exact hδ.exists_superset (hℬsmall B hB).1 (hℬsmall B hB).2.1 (hℬsmall B hB).2.2
  · exact hℬopen

/-- Example 50.3. Every compact subspace of the Euclidean plane has covering
dimension at most two. -/
theorem compactSubset_euclideanPlane_coveringDimension_le_two
    (X : Set (ℝ × ℝ)) (hX : IsCompact X) :
    dim X ≤ 2 := by
  -- Use the open-cover characterization and choose a Lebesgue number on the compact subtype.
  refine (coveringDimension_le_iff X 2).2 ?_
  intro 𝒜 h𝒜open h𝒜cover
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨δ, hδ⟩ := lebesgueNumberLemma 𝒜 h𝒜open h𝒜cover
  obtain ⟨ℬ, hℬopen, hℬcover, hℬorder, hℬsmall⟩ :=
    exists_subtypePlaneCover_orderThree X δ hδ.pos
  -- The fine order-three cover refines the original cover by the Lebesgue-number property.
  refine ⟨ℬ, smallDiameterOpenCover_isOpenRefinement hδ hℬopen hℬsmall, hℬcover, ?_⟩
  simpa using hℬorder
