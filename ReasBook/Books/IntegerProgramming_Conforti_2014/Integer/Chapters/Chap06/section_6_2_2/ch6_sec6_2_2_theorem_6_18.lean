import Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open Set
open scoped IntegerVectorNotation

section Theorem618

variable {p : ℕ}

/-- Helper for Theorem 6.18: a full-dimensional maximal lattice-free set has nonempty interior. -/
lemma maximalLatticeFreeInteriorNonempty
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    (interior K).Nonempty := by
  -- Full dimensionality upgrades convexity to nonempty interior.
  exact
    (Convex.interior_nonempty_iff_affineSpan_eq_top
      (is_maximal_lattice_free.convex hK)).2 hfull

/-- Helper for Theorem 6.18: every lineality direction is automatically a recession direction. -/
lemma mem_recessionCone_of_mem_linealitySpace
    {K : Set (Fin p → ℝ)}
    {r : Fin p → ℝ}
    (hr : r ∈ linealitySpace K) :
    r ∈ recessionCone K := by
  -- The lineality condition allows translation by every scalar, hence by every nonnegative scalar.
  rw [mem_linealitySpace_iff] at hr
  rw [mem_recessionCone_iff]
  intro x hx a ha
  exact hr hx a

/-- Helper for Theorem 6.18: translating an interior point along a recession direction stays in
the interior. -/
lemma recessionDirectionPreservesInterior
    {K : Set (Fin p → ℝ)}
    {x₀ r : Fin p → ℝ}
    (hx₀ : x₀ ∈ interior K)
    (hr : r ∈ recessionCone K)
    {a : ℝ}
    (ha : 0 ≤ a) :
    x₀ + a • r ∈ interior K := by
  -- Translate an open neighborhood of `x₀` by the recession step.
  rw [mem_interior_iff_mem_nhds] at hx₀ ⊢
  rcases mem_nhds_iff.mp hx₀ with ⟨s, hsK, hsOpen, hx₀s⟩
  have hsImageOpen : IsOpen ((fun x : Fin p → ℝ ↦ x + a • r) '' s) := by
    exact (Homeomorph.addRight (a • r)).isOpenMap _ hsOpen
  have hsImageSubset : ((fun x : Fin p → ℝ ↦ x + a • r) '' s) ⊆ K := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (mem_recessionCone_iff.mp hr) (hsK hx) a ha
  have hx₀Image : x₀ + a • r ∈ (fun x : Fin p → ℝ ↦ x + a • r) '' s := by
    exact ⟨x₀, hx₀s, rfl⟩
  exact Filter.mem_of_superset (hsImageOpen.mem_nhds hx₀Image) hsImageSubset

/-- Helper for Theorem 6.18: if a recession direction is not in the lineality space, then some
point of `K` leaves `K` after a positive backward step along that direction. -/
lemma existsBackwardEscapeOf_mem_recessionCone_of_not_mem_linealitySpace
    {K : Set (Fin p → ℝ)}
    {r : Fin p → ℝ}
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K) :
    ∃ y ∈ K, ∃ t : ℝ, 0 < t ∧ y - t • r ∉ K := by
  -- Negating the lineality condition yields a violating translate; recession forces it to be a
  -- negative translate, which we rewrite as a positive backward step.
  rw [mem_linealitySpace_iff] at hnot
  push Not at hnot
  rcases hnot with ⟨y, hyK, a, hya⟩
  have ha_not_nonneg : ¬ 0 ≤ a := by
    intro ha
    exact hya ((mem_recessionCone_iff.mp hr) hyK a ha)
  have hneg : 0 < -a := neg_pos.mpr (lt_of_not_ge ha_not_nonneg)
  refine ⟨y, hyK, -a, hneg, ?_⟩
  simpa [sub_eq_add_neg, neg_smul] using hya

/-- Helper for Theorem 6.18: a full-dimensional maximal lattice-free set is closed. -/
lemma maximalLatticeFree_isClosed
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    IsClosed K := by
  -- Compare `K` with its closure; maximality forces equality once the closure stays lattice-free.
  have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
  have hinterior : (interior K).Nonempty := maximalLatticeFreeInteriorNonempty hfull hK
  have hclosureFree : is_lattice_free (closure K) := by
    -- The convex full-dimensional hypothesis identifies the interiors of `K` and `closure K`.
    rw [is_lattice_free_iff]
    intro z
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior hinterior]
    exact (is_lattice_free_iff.mp (is_maximal_lattice_free.lattice_free hK)) z
  have hclosure_eq : closure K = K :=
    is_maximal_lattice_free.eq_of_subset hK subset_closure hconv.closure hclosureFree
  exact closure_eq_iff_isClosed.mp hclosure_eq

/-- Helper for Theorem 6.18: after moving slightly toward an interior point, a backward escape
may be arranged to start inside `interior K`. -/
lemma existsInteriorBackwardEscape
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K)
    {r : Fin p → ℝ}
    (hr : r ∈ recessionCone K)
    (hnot : r ∉ linealitySpace K) :
    ∃ x ∈ interior K, ∃ t : ℝ, 0 < t ∧ x - t • r ∉ K := by
  have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
  have hclosed : IsClosed K := maximalLatticeFree_isClosed hfull hK
  rcases maximalLatticeFreeInteriorNonempty hfull hK with ⟨x₀, hx₀⟩
  rcases existsBackwardEscapeOf_mem_recessionCone_of_not_mem_linealitySpace hr hnot with
    ⟨y, hyK, t, ht, hyOut⟩
  let z : Fin p → ℝ := y - t • r
  have hzOut : z ∉ K := hyOut
  let φ : ℝ → Fin p → ℝ := fun s ↦ (1 - s) • z + s • x₀
  have hφ_cont : Continuous φ := by
    continuity
  have hpreimage :
      φ ⁻¹' Kᶜ ∈ nhds (0 : ℝ) := by
    -- The complement of the closed set `K` is open, so points on the affine path stay outside
    -- for all sufficiently small positive parameters.
    have hzMem : z ∈ Kᶜ := hzOut
    have hφ0 : φ 0 ∈ Kᶜ := by
      simpa [φ, z] using hzMem
    exact hφ_cont.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hφ0)
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨ε, hεpos, hεsubset⟩
  let s : ℝ := min (ε / 2) (1 / 2)
  have hsPos : 0 < s := by
    dsimp [s]
    refine lt_min ?_ (by norm_num)
    linarith
  have hsLtOne : s < 1 := by
    have hsLe : s ≤ 1 / 2 := by
      dsimp [s]
      exact min_le_right _ _
    linarith
  have hsLtEps : s < ε := by
    have hsLe : s ≤ ε / 2 := by
      dsimp [s]
      exact min_le_left _ _
    linarith
  have hsBall : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hsPos.le]
    exact hsLtEps
  have hφsOut : φ s ∉ K := by
    have hsMem : s ∈ φ ⁻¹' Kᶜ := hεsubset hsBall
    simpa [Set.mem_preimage, φ] using hsMem
  have hxInterior : (1 - s) • y + s • x₀ ∈ interior K := by
    -- A positive convex combination of a point in `K` and an interior point lies in `interior K`.
    exact hconv.combo_self_interior_mem_interior hyK hx₀ (sub_nonneg.mpr hsLtOne.le) hsPos
      (sub_add_cancel 1 s)
  refine ⟨(1 - s) • y + s • x₀, hxInterior, (1 - s) * t, ?_, ?_⟩
  · -- The new escape parameter stays positive because `s ∈ (0,1)`.
    exact mul_pos (sub_pos.mpr hsLtOne) ht
  · -- Rewriting the translated point onto the affine path reduces the claim to `hφsOut`.
    simpa [φ, z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, sub_smul, smul_add,
      mul_smul] using hφsOut

/-- Helper for Theorem 6.18: a backward ray from an interior point to an outside point crosses the
frontier in between. -/
lemma backwardRayFrontierPoint
    {K : Set (Fin p → ℝ)}
    (hclosed : IsClosed K)
    {x r : Fin p → ℝ}
    (hx : x ∈ interior K)
    {t : ℝ}
    (ht : 0 < t)
    (hout : x - t • r ∉ K) :
    ∃ τ ∈ Ioo (0 : ℝ) t, x - τ • r ∈ frontier K := by
  let φ : ℝ → Fin p → ℝ := fun s ↦ x - s • r
  have hφ_cont : Continuous φ := by
    continuity
  let U : Set ℝ := φ ⁻¹' interior K
  let V : Set ℝ := φ ⁻¹' Kᶜ
  have hU_open : IsOpen U := by
    -- The interior branch is open because `φ` is continuous.
    dsimp [U]
    exact hφ_cont.isOpen_preimage _ isOpen_interior
  have hV_open : IsOpen V := by
    -- The complement branch is open because `K` is closed.
    dsimp [V]
    exact hφ_cont.isOpen_preimage _ hclosed.isOpen_compl
  have h0U : (0 : ℝ) ∈ U := by
    -- The ray starts in `interior K`.
    simpa [U, φ]
  have htV : t ∈ V := by
    -- The chosen escape time lands outside `K`.
    simpa [V, φ] using hout
  have hnot_cover : ¬ Icc (0 : ℝ) t ⊆ U ∪ V := by
    intro hcover
    -- If the whole interval split into the inside and outside branches, preconnectedness would
    -- force a point lying in both, contradicting `interior K ⊆ K`.
    have hpre := isPreconnected_Icc U V hU_open hV_open hcover
      ⟨0, left_mem_Icc.mpr ht.le, h0U⟩ ⟨t, right_mem_Icc.mpr ht.le, htV⟩
    rcases hpre with ⟨s, hsIcc, hsUV⟩
    exact hsUV.2 (interior_subset hsUV.1)
  rcases not_subset.mp hnot_cover with ⟨τ, hτIcc, hτnot⟩
  have hτ_not_interior : φ τ ∉ interior K := by
    -- The witness `τ` was chosen outside the interior branch.
    intro hmem
    exact hτnot (Or.inl (by simpa [U] using hmem))
  have hτ_mem : φ τ ∈ K := by
    -- The same witness also avoids the outside branch, so it still belongs to `K`.
    by_contra hmem
    exact hτnot (Or.inr (by simpa [V] using hmem))
  have hτ_ne_zero : τ ≠ 0 := by
    -- The endpoint `0` belongs to the inside branch, so `τ` cannot equal it.
    intro hτ0
    have : τ ∈ U := by
      simpa [hτ0] using h0U
    exact hτnot (Or.inl this)
  have hτ_ne_t : τ ≠ t := by
    -- The endpoint `t` belongs to the outside branch, so `τ` cannot equal it either.
    intro hτt
    have : τ ∈ V := by
      simpa [hτt] using htV
    exact hτnot (Or.inr this)
  refine ⟨τ, ⟨lt_of_le_of_ne hτIcc.1 (Ne.symm hτ_ne_zero),
    lt_of_le_of_ne hτIcc.2 hτ_ne_t⟩, ?_⟩
  -- Membership in the frontier is exactly the combination of `φ τ ∈ K` and `φ τ ∉ interior K`.
  exact (mem_frontier_iff_notMem_interior hτ_mem).2 hτ_not_interior

/-- Helper for Theorem 6.18: along a convex backward escape ray, there is a last parameter that
still lies in `K`, and every later parameter up to the escape time is already outside. -/
lemma backwardRayFirstExit
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    {x r : Fin p → ℝ}
    (hx : x ∈ interior K)
    {t : ℝ}
    (ht : 0 < t)
    (hout : x - t • r ∉ K) :
    ∃ τ ∈ Ioo (0 : ℝ) t, x - τ • r ∈ frontier K ∧
      (∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K) ∧
      (∀ s ∈ Ioc τ t, x - s • r ∉ K) := by
  let φ : ℝ → Fin p → ℝ := fun s ↦ x - s • r
  let S : Set ℝ := Icc (0 : ℝ) t ∩ φ ⁻¹' K
  have hφ_cont : Continuous φ := by
    continuity
  have hS_closed : IsClosed S := by
    -- The feasible scalar set is the intersection of a compact interval with the closed preimage.
    dsimp [S]
    exact isClosed_Icc.inter (hclosed.preimage hφ_cont)
  have hS_nonempty : S.Nonempty := by
    -- The interior start point gives the initial feasible parameter `0`.
    refine ⟨0, ?_⟩
    constructor
    · exact left_mem_Icc.mpr ht.le
    · simpa [φ] using interior_subset hx
  have hS_bdd : BddAbove S := by
    refine ⟨t, ?_⟩
    intro s hs
    exact hs.1.2
  let τ : ℝ := sSup S
  have hτ_mem : τ ∈ S := hS_closed.csSup_mem hS_nonempty hS_bdd
  have hτ_nonneg : 0 ≤ τ := hτ_mem.1.1
  have hτ_le_t : τ ≤ t := hτ_mem.1.2
  have hτ_mem_K : φ τ ∈ K := hτ_mem.2
  have hτ_lt_t : τ < t := by
    -- If the supremum reached `t`, then the outside endpoint would still lie in `K`.
    by_contra hτ_ge_t
    have hτ_eq_t : τ = t := le_antisymm hτ_le_t (le_of_not_gt hτ_ge_t)
    exact hout (by simpa [φ, hτ_eq_t] using hτ_mem_K)
  have hτ_not_interior : φ τ ∉ interior K := by
    intro hτ_int
    -- A small interval of interior points after `τ` would contradict the supremum property.
    have hpre :
        φ ⁻¹' interior K ∈ nhds τ := by
      exact hφ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hτ_int)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hball⟩
    let d : ℝ := min (ε / 2) ((t - τ) / 2)
    have hd_pos : 0 < d := by
      dsimp [d]
      refine lt_min ?_ ?_
      · linarith
      · linarith
    have hd_lt_eps : d < ε := by
      have hd_le : d ≤ ε / 2 := by
        dsimp [d]
        exact min_le_left _ _
      linarith
    have hd_lt_gap : d < t - τ := by
      have hd_le : d ≤ (t - τ) / 2 := by
        dsimp [d]
        exact min_le_right _ _
      linarith
    let σ : ℝ := τ + d
    have hσ_lt_t : σ < t := by
      dsimp [σ]
      linarith
    have hσ_mem_ball : σ ∈ Metric.ball τ ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hσ_sub : σ - τ = d := by
        dsimp [σ]
        ring
      calc
        |σ - τ| = d := by rw [hσ_sub, abs_of_pos hd_pos]
        _ < ε := hd_lt_eps
    have hσ_mem_interior : φ σ ∈ interior K := by
      have hσ_pre : σ ∈ φ ⁻¹' interior K := hball hσ_mem_ball
      simpa [Set.mem_preimage] using hσ_pre
    have hσ_nonneg : 0 ≤ σ := by
      dsimp [σ]
      linarith
    have hσ_mem_S : σ ∈ S := by
      constructor
      · exact ⟨hσ_nonneg, hσ_lt_t.le⟩
      · simpa [Set.mem_preimage] using interior_subset hσ_mem_interior
    have hσ_le_τ : σ ≤ τ := le_csSup hS_bdd hσ_mem_S
    dsimp [σ] at hσ_le_τ
    linarith
  have hτ_pos : 0 < τ := by
    -- If the exit parameter were `0`, the starting interior point would already be on the frontier.
    by_contra hτ_nonpos
    have hτ_eq_zero : τ = 0 := le_antisymm (le_of_not_gt hτ_nonpos) hτ_nonneg
    exact hτ_not_interior (by simpa [φ, hτ_eq_zero] using hx)
  have hτ_frontier : φ τ ∈ frontier K := by
    -- The first-exit point lies in `K` but no longer in its interior.
    exact (mem_frontier_iff_notMem_interior hτ_mem_K).2 hτ_not_interior
  have hinside :
      ∀ s ∈ Icc (0 : ℝ) τ, φ s ∈ K := by
    intro s hs
    -- Convexity keeps the whole initial segment from `x` to the first-exit point inside `K`.
    have hxK : x ∈ K := interior_subset hx
    have hs_div_nonneg : 0 ≤ s / τ := by
      exact div_nonneg hs.1 hτ_pos.le
    have hs_div_le_one : s / τ ≤ 1 := by
      have hs_div_self : s / τ ≤ τ / τ := by
        exact div_le_div_of_nonneg_right hs.2 hτ_pos.le
      simpa [ne_of_gt hτ_pos] using hs_div_self
    have hleft_nonneg : 0 ≤ 1 - s / τ := sub_nonneg.mpr hs_div_le_one
    have hsum : (1 - s / τ) + (s / τ) = 1 := by ring
    have hcombo :
        (1 - s / τ) • x + (s / τ) • φ τ ∈ K := by
      exact hconv hxK hτ_mem_K hleft_nonneg hs_div_nonneg hsum
    have hφ_eq : φ s = (1 - s / τ) • x + (s / τ) • φ τ := by
      ext i
      have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
      change x i - s * r i = (1 - s / τ) * x i + (s / τ) * (x i - τ * r i)
      field_simp [hτ_ne]
      ring
    simpa [hφ_eq] using hcombo
  have houtside :
      ∀ s ∈ Ioc τ t, φ s ∉ K := by
    intro s hs hsK
    -- Any later scalar in `K` would violate the maximality of `τ` as the last feasible time.
    have hs_mem_S : s ∈ S := by
      constructor
      · exact ⟨le_trans hτ_pos.le hs.1.le, hs.2⟩
      · exact hsK
    have hs_le : s ≤ τ := le_csSup hS_bdd hs_mem_S
    exact (not_lt_of_ge hs_le) hs.1
  refine ⟨τ, ⟨hτ_pos, hτ_lt_t⟩, ?_, ?_, ?_⟩
  · simpa [φ] using hτ_frontier
  · intro s hs
    simpa [φ] using hinside s hs
  · intro s hs
    simpa [φ] using houtside s hs

/-- Helper for Theorem 6.18: Hahn-Banach separates a closed convex set from a point outside it. -/
lemma separatingFunctionalAtOutsideRayPoint
    {K : Set (Fin p → ℝ)}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    {y : Fin p → ℝ}
    (hyK : y ∉ K) :
    ∃ f : (Fin p → ℝ) →L[ℝ] ℝ, ∃ c : ℝ,
      (∀ z ∈ K, f z ≤ c) ∧ c < f y := by
  -- Package the separation theorem in the exact shape needed for the later cap construction.
  obtain ⟨f, c, hsep, hysep⟩ :=
    geometric_hahn_banach_closed_point (s := K) (x := y) hconv hclosed hyK
  exact ⟨f, c, fun z hz ↦ le_of_lt (hsep z hz), hysep⟩

/-- Helper for Theorem 6.18: the coordinate strip between two consecutive integers around `a`
contains exactly the points whose `i`-th coordinate stays in that open unit interval. -/
def coordinateUnitStrip (i : Fin p) (a : ℝ) : Set (Fin p → ℝ) :=
  {u | (Int.floor a : ℝ) < u i ∧ u i < (Int.floor a : ℝ) + 1}

/-- Helper for Theorem 6.18: a coordinate unit strip is open. -/
lemma isOpen_coordinateUnitStrip
    (i : Fin p)
    (a : ℝ) :
    IsOpen (coordinateUnitStrip i a) := by
  -- The strip is cut out by two strict coordinate inequalities.
  dsimp [coordinateUnitStrip]
  exact
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

/-- Helper for Theorem 6.18: a coordinate unit strip is convex. -/
lemma convex_coordinateUnitStrip
    (i : Fin p)
    (a : ℝ) :
    Convex ℝ (coordinateUnitStrip i a) := by
  -- Convex combinations preserve the two strict coordinate bounds.
  intro x hx y hy α β hα hβ hαβ
  dsimp [coordinateUnitStrip] at hx hy ⊢
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2, hα, hβ, hαβ]

/-- Helper for Theorem 6.18: a coordinate unit strip is disjoint from the embedded integer
lattice. -/
lemma coordinateUnitStrip_disjoint_integerVectors
    (i : Fin p)
    (a : ℝ) :
    Disjoint (coordinateUnitStrip i a) (ℤ^p) := by
  -- Any integer vector has an integral `i`-th coordinate, but the strip keeps that coordinate
  -- strictly between two consecutive integers.
  rw [disjoint_left]
  intro u hu huint
  rw [mem_integerVectors_iff_forall] at huint
  rcases huint i with ⟨z, hz⟩
  have hlower : (Int.floor a : ℝ) < (z : ℝ) := by
    simpa [hz] using hu.1
  have hupper : (z : ℝ) < (Int.floor a : ℝ) + 1 := by
    simpa [hz] using hu.2
  have hsucc : Int.floor a + 1 ≤ z := Int.add_one_le_iff.mpr (by exact_mod_cast hlower)
  have hsucc_real : ((Int.floor a : ℝ) + 1) ≤ (z : ℝ) := by
    exact_mod_cast hsucc
  exact (not_le_of_gt hupper) hsucc_real

/-- Helper for Theorem 6.18: the first-exit point can be pushed slightly farther along the
backward ray to an outside point lying in an open convex coordinate strip disjoint from `ℤ^p`. -/
lemma existsOutsideRayPointWithCoordinateSlab
    {K : Set (Fin p → ℝ)}
    {x r : Fin p → ℝ}
    {t τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) t)
    (houtside : ∀ s ∈ Ioc τ t, x - s • r ∉ K)
    (hnot : r ∉ linealitySpace K) :
    ∃ i : Fin p, ∃ δ : ℝ, ∃ y : Fin p → ℝ, ∃ U : Set (Fin p → ℝ),
      0 < δ ∧ τ + δ < t ∧ y = x - (τ + δ) • r ∧ y ∉ K ∧
        IsOpen U ∧ Convex ℝ U ∧ y ∈ U ∧ Disjoint U (ℤ^p) := by
  -- Route correction: the arithmetic bridge is now an explicit coordinate strip, so the remaining
  -- theorem-local blocker is only the exposed-face localization step.
  have hr_ne_zero : r ≠ 0 := by
    intro hr0
    apply hnot
    simpa [hr0] using (zero_mem_linealitySpace : (0 : Fin p → ℝ) ∈ linealitySpace K)
  have hcoord : ∃ i : Fin p, r i ≠ 0 := by
    classical
    by_contra hcoord
    push_neg at hcoord
    apply hr_ne_zero
    ext i
    exact hcoord i
  rcases hcoord with ⟨i, hri⟩
  let b : Fin p → ℝ := x - τ • r
  by_cases hbi_int : b i ∈ Set.range (Int.cast : ℤ → ℝ)
  · rcases hbi_int with ⟨m, hm⟩
    let δ : ℝ := min ((t - τ) / 2) (1 / (2 * |r i|))
    let y : Fin p → ℝ := x - (τ + δ) • r
    let U : Set (Fin p → ℝ) := coordinateUnitStrip i (y i)
    have hδ_pos : 0 < δ := by
      -- The two candidate step sizes are both positive.
      dsimp [δ]
      refine lt_min ?_ ?_
      · linarith [hτ.2]
      · have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
        positivity
    have hτδ_lt_t : τ + δ < t := by
      -- Choosing `δ ≤ (t - τ) / 2` keeps the new point strictly before `t`.
      have hδ_le : δ ≤ (t - τ) / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      linarith
    have hy_out : y ∉ K := by
      -- The first-exit data already says every later parameter stays outside.
      apply houtside (τ + δ)
      exact ⟨by linarith, hτδ_lt_t.le⟩
    have hdelta_mul_abs_lt_one : |δ * r i| < 1 := by
      -- The second branch of the minimum bounds the coordinate shift by `1 / 2`.
      have hδ_le : δ ≤ 1 / (2 * |r i|) := by
        dsimp [δ]
        exact min_le_right _ _
      have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
      have hδ_nonneg : 0 ≤ δ := hδ_pos.le
      have hmul_le_half : |δ * r i| ≤ 1 / 2 := by
        calc
          |δ * r i| = δ * |r i| := by
            rw [abs_mul, abs_of_nonneg hδ_nonneg]
          _ ≤ (1 / (2 * |r i|)) * |r i| := by
            gcongr
          _ = 1 / 2 := by
            field_simp [ne_of_gt hri_abs_pos]
      linarith
    have hyi_not_int : y i ∉ Set.range (Int.cast : ℤ → ℝ) := by
      intro hyi_int
      rcases hyi_int with ⟨n, hn⟩
      have hyi_eq : y i = (m : ℝ) - δ * r i := by
        dsimp [y, b]
        rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, hm]
        ring
      have hshift_ne : δ * r i ≠ 0 := mul_ne_zero (ne_of_gt hδ_pos) hri
      have hshift_sign : 0 < δ * r i ∨ δ * r i < 0 := lt_or_gt_of_ne hshift_ne
      cases hshift_sign with
      | inl hshift_pos =>
          have hshift_lt_one : δ * r i < 1 := by
            exact (abs_lt.mp hdelta_mul_abs_lt_one).2
          have hy_upper : (n : ℝ) < (m : ℝ) := by
            linarith [hyi_eq, hn, hshift_pos]
          have hy_lower : (m : ℝ) - 1 < (n : ℝ) := by
            linarith [hyi_eq, hn, hshift_lt_one]
          have hm_le_n : m ≤ n := by
            exact Int.add_one_le_iff.mpr (by exact_mod_cast hy_lower)
          have hn_lt_m : n < m := by
            exact_mod_cast hy_upper
          exact (not_le_of_gt hn_lt_m) hm_le_n
      | inr hshift_neg =>
          have hneg_lt_shift : -1 < δ * r i := by
            exact (abs_lt.mp hdelta_mul_abs_lt_one).1
          have hy_lower : (m : ℝ) < (n : ℝ) := by
            linarith [hyi_eq, hn, hshift_neg]
          have hy_upper : (n : ℝ) < (m : ℝ) + 1 := by
            linarith [hyi_eq, hn, hneg_lt_shift]
          have hm_succ_le_n : m + 1 ≤ n := by
            exact Int.add_one_le_iff.mpr (by exact_mod_cast hy_lower)
          have hn_lt_succ : n < m + 1 := by
            exact_mod_cast hy_upper
          exact (not_le_of_gt hn_lt_succ) hm_succ_le_n
    have hy_mem : y ∈ U := by
      -- Once the chosen coordinate of `y` is nonintegral, it lies in its own unit strip.
      dsimp [U, coordinateUnitStrip]
      constructor
      · simpa using (Int.floor_lt_self_iff.2 hyi_not_int)
      · exact Int.lt_floor_add_one (y i)
    refine ⟨i, δ, y, U, hδ_pos, hτδ_lt_t, rfl, hy_out, ?_, ?_, hy_mem, ?_⟩
    · simpa [U] using isOpen_coordinateUnitStrip i (y i)
    · simpa [U] using convex_coordinateUnitStrip i (y i)
    · simpa [U] using coordinateUnitStrip_disjoint_integerVectors i (y i)
  · let gap : ℝ := min (b i - (Int.floor (b i) : ℝ)) (((Int.floor (b i) : ℝ) + 1) - b i)
    let δ : ℝ := min ((t - τ) / 2) (gap / (2 * |r i|))
    let y : Fin p → ℝ := x - (τ + δ) • r
    let U : Set (Fin p → ℝ) := coordinateUnitStrip i (y i)
    have hgap_pos : 0 < gap := by
      -- Nonintegrality of `b i` gives positive distance to both neighboring integers.
      dsimp [gap]
      refine lt_min ?_ ?_
      · have hfloor_lt : (Int.floor (b i) : ℝ) < b i := by
          simpa using (Int.floor_lt_self_iff.2 hbi_int)
        linarith
      · have hupper : b i < (Int.floor (b i) : ℝ) + 1 := Int.lt_floor_add_one (b i)
        linarith
    have hδ_pos : 0 < δ := by
      -- The time window and the coordinate gap both allow a positive step.
      dsimp [δ]
      refine lt_min ?_ ?_
      · linarith [hτ.2]
      · have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
        positivity
    have hτδ_lt_t : τ + δ < t := by
      -- Choosing `δ ≤ (t - τ) / 2` again keeps the new point before `t`.
      have hδ_le : δ ≤ (t - τ) / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      linarith
    have hy_out : y ∉ K := by
      -- The pushed point still lies past the first exit.
      apply houtside (τ + δ)
      exact ⟨by linarith, hτδ_lt_t.le⟩
    have hdelta_mul_abs_lt_gap : |δ * r i| < gap := by
      -- The second branch of the minimum bounds the coordinate shift by `gap / 2`.
      have hδ_le : δ ≤ gap / (2 * |r i|) := by
        dsimp [δ]
        exact min_le_right _ _
      have hri_abs_pos : 0 < |r i| := abs_pos.mpr hri
      have hδ_nonneg : 0 ≤ δ := hδ_pos.le
      have hmul_le_half : |δ * r i| ≤ gap / 2 := by
        calc
          |δ * r i| = δ * |r i| := by
            rw [abs_mul, abs_of_nonneg hδ_nonneg]
          _ ≤ (gap / (2 * |r i|)) * |r i| := by
            gcongr
          _ = gap / 2 := by
            field_simp [ne_of_gt hri_abs_pos]
      linarith
    have hyi_not_int : y i ∉ Set.range (Int.cast : ℤ → ℝ) := by
      intro hyi_int
      rcases hyi_int with ⟨n, hn⟩
      have hyi_eq : y i = b i - δ * r i := by
        dsimp [y, b]
        rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply]
        ring
      have hshift_upper : δ * r i < gap := (abs_lt.mp hdelta_mul_abs_lt_gap).2
      have hshift_lower : -gap < δ * r i := (abs_lt.mp hdelta_mul_abs_lt_gap).1
      have hgap_left : gap ≤ b i - (Int.floor (b i) : ℝ) := by
        dsimp [gap]
        exact min_le_left _ _
      have hgap_right : gap ≤ ((Int.floor (b i) : ℝ) + 1) - b i := by
        dsimp [gap]
        exact min_le_right _ _
      have hy_lower : (Int.floor (b i) : ℝ) < (n : ℝ) := by
        have : δ * r i < b i - (Int.floor (b i) : ℝ) :=
          lt_of_lt_of_le hshift_upper hgap_left
        linarith [hyi_eq, hn]
      have hy_upper : (n : ℝ) < (Int.floor (b i) : ℝ) + 1 := by
        have : -(((Int.floor (b i) : ℝ) + 1) - b i) < δ * r i :=
          lt_of_le_of_lt (by linarith [hgap_right]) hshift_lower
        linarith [hyi_eq, hn]
      have hsucc : Int.floor (b i) + 1 ≤ n := Int.add_one_le_iff.mpr (by exact_mod_cast hy_lower)
      have hsucc_real : ((Int.floor (b i) : ℝ) + 1) ≤ (n : ℝ) := by
        exact_mod_cast hsucc
      exact (not_le_of_gt hy_upper) hsucc_real
    have hy_mem : y ∈ U := by
      -- The chosen outside point sits in the strip determined by its own nonintegral coordinate.
      dsimp [U, coordinateUnitStrip]
      constructor
      · simpa using (Int.floor_lt_self_iff.2 hyi_not_int)
      · exact Int.lt_floor_add_one (y i)
    refine ⟨i, δ, y, U, hδ_pos, hτδ_lt_t, rfl, hy_out, ?_, ?_, hy_mem, ?_⟩
    · simpa [U] using isOpen_coordinateUnitStrip i (y i)
    · simpa [U] using convex_coordinateUnitStrip i (y i)
    · simpa [U] using coordinateUnitStrip_disjoint_integerVectors i (y i)

/-- Theorem 6.18 (1) (Lovász [261]). Let `K ⊆ ℝ^p` be full-dimensional. Then `K` is a maximal
lattice-free convex set if and only if `K` is a polyhedron, its interior contains no point of the
embedded lattice `ℤ^p`, and every facet of `K` contains an integer point in its relative
interior. -/
theorem maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤) :
    is_maximal_lattice_free K ↔
      is_polyhedron K ∧
        is_lattice_free K ∧
          ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
            ∃ z : Fin p → ℤ, (Int.cast ∘ z) ∈ intrinsicInterior ℝ F := by
  constructor
  · intro hK
    -- Route correction: the source proof only treats the bounded case, so the forward implication
    -- must first pass through the recession/lineality reduction before replaying the box-and-
    -- separation argument on a bounded factor.
    -- TODO: prove that maximal lattice-free sets reduce to a bounded factor after splitting off
    -- `linealitySpace K`, then transport the bounded-case polyhedron statement back to `K`.
    have hpoly : is_polyhedron K := sorry
    -- TODO: after the same bounded-factor reduction, transport the bounded-case facet lattice-point
    -- statement back through the lineality split.
    have hfacets :
        ∀ F : Set (Fin p → ℝ), IsFacetOf K F →
          ∃ z : Fin p → ℤ, (Int.cast ∘ z) ∈ intrinsicInterior ℝ F := sorry
    exact ⟨hpoly, ⟨is_maximal_lattice_free.lattice_free hK, hfacets⟩⟩
  · rintro ⟨hpoly, hfree, hfacets⟩
    -- Route correction: maximality should come from a facet-crossing contradiction, not from the
    -- bounded forward-direction argument.
    -- TODO: given a strict convex lattice-free enlargement `L ⊋ K`, use polyhedral structure to
    -- find a crossed facet of `K`, then show the lattice point from `hfacets` in that facet's
    -- `intrinsicInterior` becomes an interior lattice point of `L`, contradicting `hfree`.
    sorry

/-- Theorem 6.18 (2). Let `K ⊆ ℝ^p` be full-dimensional. If `K` is a maximal lattice-free convex
set, then its recession cone equals its lineality space. -/
theorem recessionCone_eq_linealitySpace_of_is_maximal_lattice_free
    {K : Set (Fin p → ℝ)}
    (hfull : affineSpan ℝ K = ⊤)
    (hK : is_maximal_lattice_free K) :
    recessionCone K = linealitySpace K := by
  ext r
  constructor
  · intro hr
    -- Route correction: this is the genuinely hard direction. It needs the structural lemma that a
    -- recession direction outside `linealitySpace K` yields a strict larger convex lattice-free
    -- set, contradicting maximality.
    by_contra hnot
    have hconv : Convex ℝ K := is_maximal_lattice_free.convex hK
    have hclosed : IsClosed K := maximalLatticeFree_isClosed hfull hK
    have hinteriorBack :
        ∃ x ∈ interior K, ∃ t : ℝ, 0 < t ∧ x - t • r ∉ K :=
      existsInteriorBackwardEscape hfull hK hr hnot
    rcases hinteriorBack with ⟨x, hx, t, ht, hout⟩
    have hfirstExit :
        ∃ τ ∈ Ioo (0 : ℝ) t, x - τ • r ∈ frontier K ∧
          (∀ s ∈ Icc (0 : ℝ) τ, x - s • r ∈ K) ∧
          (∀ s ∈ Ioc τ t, x - s • r ∉ K) :=
      backwardRayFirstExit hconv hclosed hx ht hout
    rcases hfirstExit with ⟨τ, hτ, hfrontier, hinside, houtside⟩
    let b : Fin p → ℝ := x - τ • r
    have hb_frontier : b ∈ frontier K := by
      simpa [b] using hfrontier
    have hslab :
        ∃ i : Fin p, ∃ δ : ℝ, ∃ y : Fin p → ℝ, ∃ U : Set (Fin p → ℝ),
          0 < δ ∧ τ + δ < t ∧ y = x - (τ + δ) • r ∧ y ∉ K ∧
            IsOpen U ∧ Convex ℝ U ∧ y ∈ U ∧ Disjoint U (ℤ^p) :=
      existsOutsideRayPointWithCoordinateSlab hτ houtside hnot
    rcases hslab with ⟨i, δ, y, U, hδpos, hτδlt, hydef, hyK, hUopen, hUconvex, hyU, hUdisj⟩
    have hsep :
        ∃ f : (Fin p → ℝ) →L[ℝ] ℝ, ∃ c : ℝ,
          (∀ z ∈ K, f z ≤ c) ∧ c < f y :=
      separatingFunctionalAtOutsideRayPoint hconv hclosed hyK
    rcases hsep with ⟨f, c, hsepK, hsepY⟩
    -- TODO: perturb `f` along the chosen coordinate `i` so that the exposed face
    -- `K ∩ {z | g z = d}` lies inside `U`, then enlarge `K` by the explicit pyramid over that
    -- face and use `hUdisj` to keep the new interior lattice-free.
    sorry
  · intro hr
    -- The reverse inclusion is the direct direction from the definitions.
    exact mem_recessionCone_of_mem_linealitySpace hr

end Theorem618
