import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap06.Proposition_6_16
import BauschkeLean.Chap08.Proposition_8_46
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_4
import BauschkeLean.Chap16.Proposition_16_35
import BauschkeLean.Chap16.Proposition_16_69

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

section ConvexInequalityConstraints

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {g : H → Set.Ioi (⊥ : EReal)} {x : H}

/-- Helper for Lemma 27.20: the translated support inequality defining `N[C] x` is equivalent to
the pointwise family `∀ y ∈ C, ⟪y - x, u⟫ ≤ 0`. -/
private lemma innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos
    {C : Set H} {u p : H} :
    innerSupremumOn (C - ({p} : Set H)) u ≤ 0 ↔
      ∀ y ∈ C, ⟪y - p, u⟫_ℝ ≤ 0 := by
  constructor
  · intro hsup
    have hsep :
        innerSupremumOn (C - ({p} : Set H)) u ≤ innerInfimumOn ({0} : Set H) u := by
      simpa using hsup
    have hinner :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set H)) ({0} : Set H) u).1 hsep
    intro y hy
    have hy_sub : y - p ∈ C - ({p} : Set H) := by
      exact ⟨y, hy, p, by simp, rfl⟩
    simpa using hinner (y - p) hy_sub 0 (by simp)
  · intro hinner
    have hsep :
        innerSupremumOn (C - ({p} : Set H)) u ≤ innerInfimumOn ({0} : Set H) u := by
      refine (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({p} : Set H)) ({0} : Set H) u).2 ?_
      intro v hv z hz
      have hz0 : z = 0 := by
        simpa using hz
      subst hz0
      rcases hv with ⟨y, hy, q, hq, hvq⟩
      have hq_eq : q = p := by
        simpa using hq
      have hv_eq : v = y - p := by
        simpa [hq_eq] using hvq.symm
      simpa [hv_eq] using hinner y hy
    simpa using hsep

/-- Helper for Lemma 27.20: at a point of `C`, normal-cone membership is the corresponding
pointwise family of nonpositive inner-product inequalities on `C`. -/
private lemma mem_normalCone_iff_forall_inner_nonpos
    {C : Set H} {x u : H} (hx : x ∈ C) :
    u ∈ N[C] x ↔ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
  -- Rewrite `N[C] x` to the translated support inequality and then use the pointwise bridge.
  rw [Set.normalCone_of_mem hx]
  exact innerSupremumOn_sub_singleton_le_zero_iff_forall_inner_nonpos

/-- Helper for Lemma 27.20: the boundary theorem's easy inclusion comes from monotonicity of
domain normals and the defining subgradient inequality. -/
private lemma
    domainNormalUnionSubdifferentialCone_subset_normalCone_nonpositiveSublevel_of_eq_zero
    (_hconv : ConvexOn g (effectiveDomain g)) (hx0 : (g x : EReal) = 0) :
    N[effectiveDomain g] x ∪ cone ((∂ g) x) ⊆ N[lowerLevelSet g 0] x := by
  have hx_level : x ∈ lowerLevelSet g 0 := by
    rw [mem_lowerLevelSet_iff]
    simpa [hx0]
  have hx_dom : x ∈ effectiveDomain g := by
    rw [mem_effectiveDomain_iff]
    simpa [hx0] using (EReal.zero_lt_top : (0 : EReal) < ⊤)
  have hlevel_subset_domain : lowerLevelSet g 0 ⊆ effectiveDomain g := by
    intro y hy
    exact mem_effectiveDomain_of_mem_lowerLevelSet_zero hy
  intro u hu
  rcases hu with hu_domain | hu_cone
  · -- Domain normals restrict immediately to the smaller sublevel set.
    refine (mem_normalCone_iff_forall_inner_nonpos hx_level).2 ?_
    have hdomain :=
      (mem_normalCone_iff_forall_inner_nonpos hx_dom).1 hu_domain
    intro y hy
    exact hdomain y (hlevel_subset_domain hy)
  · -- A positive multiple of a subgradient stays nonpositive on the `≤ 0` level set when `g x = 0`.
    rcases
        (mem_cone_iff_exists_pos_smul_mem (convex_subdifferential g x)).1 hu_cone with
      ⟨a, ha, ha_mem⟩
    rcases Set.mem_smul_set.mp ha_mem with ⟨w, hw, rfl⟩
    refine (mem_normalCone_iff_forall_inner_nonpos hx_level).2 ?_
    have hsubgrad := (mem_subdifferential_iff (f := g) (x := x) (u := w)).1 hw
    intro y hy
    have hy_level : (g y : EReal) ≤ 0 := by
      rw [mem_lowerLevelSet_iff] at hy
      exact hy
    have hinner_ereal : ((⟪y - x, w⟫_ℝ : ℝ) : EReal) ≤ 0 := by
      have hsub : ((⟪y - x, w⟫_ℝ : ℝ) : EReal) ≤ (g y : EReal) := by
        have hsub' : ((⟪y - x, w⟫_ℝ : ℝ) : EReal) + (g x : EReal) ≤ (g y : EReal) :=
          hsubgrad y
        rw [hx0, add_zero] at hsub'
        exact hsub'
      exact le_trans hsub hy_level
    have hinner : ⟪y - x, w⟫_ℝ ≤ 0 := by
      exact_mod_cast hinner_ereal
    have hscaled : ⟪y - x, a • w⟫_ℝ = a * ⟪y - x, w⟫_ℝ := by
      rw [real_inner_smul_right]
    rw [hscaled]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hinner

/-- Helper for Lemma 27.20: Proposition 16.35 projects a zero-height epigraph normal back to
either the effective-domain normal cone or the cone generated by the subdifferential. -/
private lemma mem_domainNormal_or_subdifferentialCone_of_mem_epigraphNormal_zeroHeight
    (hx0 : (g x : EReal) = 0) {u : H} {a : ℝ} (_ha : 0 ≤ a)
    (hpair : (u, -a) ∈ N[epigraph g.asEReal] (x, 0)) :
    u ∈ N[effectiveDomain g] x ∪ cone ((∂ g) x) := by
  have hx_dom : x ∈ effectiveDomain g := by
    rw [mem_effectiveDomain_iff]
    simpa [hx0] using (EReal.zero_lt_top : (0 : EReal) < ⊤)
  have hpair' : (u, -a) ∈ N[epigraph g.asEReal] (x, (g x : EReal).toReal) := by
    simpa [hx0] using hpair
  rw [normalCone_epigraph_eq_effectiveDomain_normal_zero_union_positive_subdifferential
    hx_dom] at hpair'
  rcases hpair' with hzero | hpos
  · -- The zero vertical slice is exactly the domain-normal branch.
    left
    exact hzero.1
  · -- The positive ray branch is precisely a cone point of the subdifferential fiber.
    right
    have hray := (mem_positive_ray_subdifferential_slice_iff g).1 hpos
    exact
      (mem_cone_iff_exists_pos_smul_mem (convex_subdifferential g x)).2
        ⟨a, hray.1, hray.2⟩

/-- Helper for Lemma 27.20: on `ℝ`, the inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul_local (a b : ℝ) :
    ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

/-- Helper for Lemma 27.20: in the product Hilbert space `E × ℝ`, the inner product splits into
the horizontal inner product plus the vertical scalar product. -/
private lemma inner_pair_eq_add_mul_local
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {y u : E} {η a : ℝ} :
    ⟪(y, η), (u, a)⟫_ℝ = ⟪y, u⟫_ℝ + η * a := by
  change ⟪y, u⟫_ℝ + ⟪η, a⟫_ℝ = ⟪y, u⟫_ℝ + η * a
  rw [real_inner_eq_mul_local]

/-- Helper for Lemma 27.20: the image of the epigraph under
`p ↦ (⟪p.1 - x, u⟫, p.2)` cannot meet the open quadrant `(0, ∞) × (-∞, 0)` because a negative
height already forces the base point into `lowerLevelSet g 0`, where `u` has nonpositive support.
-/
private lemma epigraphInnerHeightImage_disjoint_openQuadrant
    (hx0 : (g x : EReal) = 0) {u : H} (hu : u ∈ N[lowerLevelSet g 0] x) :
    Disjoint (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ))
      ((fun p : H × ℝ ↦ (⟪p.1 - x, u⟫_ℝ, p.2)) '' epigraph g.asEReal) := by
  have hx_level : x ∈ lowerLevelSet g 0 := by
    rw [mem_lowerLevelSet_iff]
    simpa [hx0]
  refine Set.disjoint_left.2 ?_
  intro q hq_quad hq_image
  rcases hq_quad with ⟨hq_fst, hq_snd⟩
  rcases hq_image with ⟨p, hp_epi, hp_map⟩
  rcases p with ⟨y, η⟩
  -- Read the image point through the epigraph inequality and the open-quadrant coordinates.
  have hη_lt : η < 0 := by
    have hq_snd_eq : q.2 = η := by
      simpa using congrArg Prod.snd hp_map.symm
    simpa [hq_snd_eq] using hq_snd
  have hy_inner_pos : 0 < ⟪y - x, u⟫_ℝ := by
    have hq_fst_eq : q.1 = ⟪y - x, u⟫_ℝ := by
      simpa using congrArg Prod.fst hp_map.symm
    simpa [hq_fst_eq] using hq_fst
  have hy_level : y ∈ lowerLevelSet g 0 := by
    rw [mem_lowerLevelSet_iff]
    have hgy_le : (g y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).1 hp_epi
    exact le_trans hgy_le (by exact_mod_cast (le_of_lt hη_lt))
  have hu_nonpos := (mem_normalCone_iff_forall_inner_nonpos hx_level).1 hu y hy_level
  exact (not_le_of_gt hy_inner_pos) hu_nonpos

/-- Helper for Lemma 27.20: a continuous linear functional on `ℝ²` is determined by its values on
the coordinate vectors `(1, 0)` and `(0, 1)`. -/
private lemma strongDual_apply_eq_coordinateForm
    (f : StrongDual ℝ (ℝ × ℝ)) :
    let A := f (1, 0)
    let B := f (0, 1)
    ∀ z : ℝ × ℝ, f z = z.1 * A + z.2 * B := by
  intro A B z
  rcases z with ⟨s, t⟩
  -- Decompose `(s, t)` along the standard basis and use linearity of `f`.
  have hz : (s, t) = s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hz, map_add, map_smul, map_smul]
  simp [A, B]

/-- Helper for Lemma 27.20: once the separator is normalized to be negative on the open quadrant
and nonnegative on `S`, its coordinate coefficients satisfy `A < 0 ≤ B`. -/
private lemma separatorCoefficients_openQuadrant
    {S : Set (ℝ × ℝ)} {f : StrongDual ℝ (ℝ × ℝ)}
    (hquad : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ), f q < 0)
    (hS : ∀ p ∈ S, 0 ≤ f p)
    (hneg : ∃ p ∈ S, p.2 < 0) :
    let A := f (1, 0)
    let B := f (0, 1)
    A < 0 ∧ 0 ≤ B ∧ ∀ z : ℝ × ℝ, f z = z.1 * A + z.2 * B := by
  intro A B
  have hcoord : ∀ z : ℝ × ℝ, f z = z.1 * A + z.2 * B := by
    simpa [A, B] using strongDual_apply_eq_coordinateForm f
  have hA_nonpos : A ≤ 0 := by
    by_contra hA_nonpos
    have hA_pos : 0 < A := lt_of_not_ge hA_nonpos
    let ε : ℝ := A / (2 * (|B| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_abs : ε * |B| < A / 2 := by
      have hlt : |B| < |B| + 1 := by linarith
      have hmul := mul_lt_mul_of_pos_left hlt hε_pos
      have hε_eval : ε * (|B| + 1) = A / 2 := by
        dsimp [ε]
        field_simp
      linarith
    have hε_mem : ((1 : ℝ), -ε) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ) := by
      constructor
      · norm_num
      ·
        have hneg : -ε < -0 := by exact neg_lt_neg hε_pos
        simpa using hneg
    have hquad_eval : f ((1 : ℝ), -ε) < 0 := hquad ((1 : ℝ), -ε) hε_mem
    have hε_bound : -(ε * |B|) ≤ -(ε * B) := by
      have hB_le : B ≤ |B| := le_abs_self B
      linarith [mul_le_mul_of_nonneg_left hB_le hε_pos.le]
    have hpos_eval : 0 < f ((1 : ℝ), -ε) := by
      rw [hcoord ((1 : ℝ), -ε)]
      linarith
    exact (not_lt_of_gt hpos_eval) hquad_eval
  have hB_nonneg : 0 ≤ B := by
    by_contra hB_nonneg
    have hB_neg : B < 0 := lt_of_not_ge hB_nonneg
    let ε : ℝ := (-B) / (2 * (|A| + 1))
    have hε_pos : 0 < ε := by
      dsimp [ε]
      exact div_pos (by linarith) (by positivity)
    have hε_abs : ε * |A| < (-B) / 2 := by
      have hlt : |A| < |A| + 1 := by linarith
      have hmul := mul_lt_mul_of_pos_left hlt hε_pos
      have hε_eval : ε * (|A| + 1) = (-B) / 2 := by
        dsimp [ε]
        field_simp
      linarith
    have hε_mem : (ε, (-1 : ℝ)) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ) := by
      constructor
      · exact hε_pos
      · norm_num
    have hquad_eval : f (ε, -1) < 0 := hquad (ε, -1) hε_mem
    have hA_lower : -|A| ≤ A := by simpa using neg_abs_le A
    have hε_lower : -(ε * |A|) ≤ ε * A := by
      simpa [neg_mul] using (mul_le_mul_of_nonneg_left hA_lower hε_pos.le)
    have hpos_eval : 0 < f (ε, -1) := by
      rw [hcoord (ε, -1)]
      linarith
    exact (not_lt_of_gt hpos_eval) hquad_eval
  have hA_ne : A ≠ 0 := by
    intro hA0
    rcases hneg with ⟨p, hpS, hp₂_neg⟩
    have hp_nonneg : 0 ≤ f p := hS p hpS
    rw [hcoord p, hA0] at hp_nonneg
    have hB_nonpos : B ≤ 0 := by
      by_contra hB_nonpos
      have hB_pos : 0 < B := lt_of_not_ge hB_nonpos
      have : p.2 * B < 0 := mul_neg_of_neg_of_pos hp₂_neg hB_pos
      linarith
    have hB0 : B = 0 := le_antisymm hB_nonpos hB_nonneg
    have hquad_eval : f (1, (-1 : ℝ)) < 0 := by
      refine hquad (1, -1) ?_
      constructor <;> norm_num
    rw [hcoord (1, -1), hA0, hB0] at hquad_eval
    linarith
  have hA_neg : A < 0 := lt_of_le_of_ne hA_nonpos hA_ne
  exact ⟨hA_neg, hB_nonneg, hcoord⟩

/-- Helper for Lemma 27.20: a convex subset of `ℝ²` through the origin, disjoint from the open
quadrant `(0, ∞) × (-∞, 0)` and containing a point of negative height, admits a nonnegative slope
bounding the first coordinate by the second. -/
private lemma exists_nonnegativeSlope_of_disjoint_epigraphInnerHeightImage
    {S : Set (ℝ × ℝ)} (hSconv : Convex ℝ S) (h0S : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hdisj : Disjoint (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) S)
    (hneg : ∃ p ∈ S, p.2 < 0) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ q ∈ S, q.1 ≤ a * q.2 := by
  have hquad_convex : Convex ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).prod (convex_Iio (0 : ℝ))
  have hquad_open : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) :=
    isOpen_Ioi.prod isOpen_Iio
  obtain ⟨f, c, hquad_lt, hS_ge⟩ :=
    geometric_hahn_banach_open hquad_convex hquad_open hSconv hdisj
  have hc_nonpos : c ≤ 0 := by
    have hzero_eval : f (0, 0) = 0 := by
      simpa only using map_zero f
    have hS_zero : c ≤ f (0, 0) := hS_ge (0, 0) h0S
    rw [hzero_eval] at hS_zero
    exact hS_zero
  have hc_nonneg : 0 ≤ c := by
    by_contra hc_neg
    have hc_lt : c < 0 := lt_of_not_ge hc_neg
    let m : ℝ := f ((1 : ℝ), (-1 : ℝ))
    by_cases hm_nonneg : 0 ≤ m
    · have hquad_eval : f (1, (-1 : ℝ)) < c := by
        refine hquad_lt (1, -1) ?_
        constructor <;> norm_num
      linarith
    · have hm_lt : m < 0 := lt_of_not_ge hm_nonneg
      let t : ℝ := c / (2 * m)
      have ht_pos : 0 < t := by
        dsimp [t]
        refine div_pos_of_neg_of_neg hc_lt ?_
        linarith
      have hquad_eval : f (t, -t) < c := by
        refine hquad_lt (t, -t) ?_
        constructor
        · exact ht_pos
        ·
          have hneg : -t < -0 := by exact neg_lt_neg ht_pos
          simpa using hneg
      have ht_eval : f (t, -t) = t * m := by
        have ht_repr : (t, -t) = t • ((1 : ℝ), (-1 : ℝ)) := by
          ext <;> simp [t]
        rw [ht_repr, map_smul]
        simp [m]
      have ht_half : t * m = c / 2 := by
        have htmul : t * (2 * m) = c := by
          have hden_ne : (2 : ℝ) * m ≠ 0 := mul_ne_zero two_ne_zero hm_lt.ne
          calc
            t * (2 * m) = (c / (2 * m)) * (2 * m) := by rfl
            _ = c := div_mul_cancel₀ _ hden_ne
        nlinarith [htmul]
      rw [ht_eval, ht_half] at hquad_eval
      linarith
  have hc_zero : c = 0 := le_antisymm hc_nonpos hc_nonneg
  have hquad0 : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ), f q < 0 := by
    intro q hq
    simpa [hc_zero] using hquad_lt q hq
  have hS0 : ∀ p ∈ S, 0 ≤ f p := by
    intro p hp
    simpa [hc_zero] using hS_ge p hp
  obtain ⟨A_neg, B_nonneg, hcoord⟩ :=
    separatorCoefficients_openQuadrant (f := f) hquad0 hS0 hneg
  let a : ℝ := (f (0, 1)) / (-(f (1, 0)))
  refine ⟨a, ?_, ?_⟩
  · -- The slope is the quotient of two nonnegative quantities.
    exact div_nonneg B_nonneg (by linarith [A_neg])
  · intro q hq
    have hq_nonneg : 0 ≤ f q := hS0 q hq
    have hA_pos : 0 < -(f (1, 0)) := by linarith [A_neg]
    have hmul :
        q.1 * (-(f (1, 0))) ≤ q.2 * f (0, 1) := by
      rw [hcoord q] at hq_nonneg
      linarith
    have hdiv : q.1 ≤ (q.2 * f (0, 1)) / (-(f (1, 0))) :=
      (le_div_iff₀ hA_pos).2 hmul
    calc
      q.1 ≤ (q.2 * f (0, 1)) / (-(f (1, 0))) := hdiv
      _ = a * q.2 := by
        dsimp [a]
        field_simp [hA_pos.ne']

-- Route correction: the remaining blocker is the `ℝ²` separation step lifting a lower-level-set
-- normal at height `0` to an epigraph normal at the graph point `(x, 0)`.
/-- Helper for Lemma 27.20: a normal to `lowerLevelSet g 0` at a boundary point `x` lifts to a
zero-height epigraph normal `(u, -a)` for some `a ≥ 0`. -/
private lemma mem_epigraphNormal_zeroHeight_of_mem_normalCone_nonpositiveSublevel
    (hconv : ConvexOn g (effectiveDomain g))
    (hneg : (strictLowerLevelSet g.asEReal 0).Nonempty)
    (hx0 : (g x : EReal) = 0) {u : H}
    (hu : u ∈ N[lowerLevelSet g 0] x) :
    ∃ a : ℝ, 0 ≤ a ∧ (u, -a) ∈ N[epigraph g.asEReal] (x, 0) := by
  let T : H × ℝ → ℝ × ℝ := fun p ↦ (⟪p.1 - x, u⟫_ℝ, p.2)
  let S : Set (ℝ × ℝ) := T '' epigraph g.asEReal
  let L : (H × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun p ↦ (⟪p.1, u⟫_ℝ, p.2)
      map_add' := by
        intro p q
        ext <;> simp [inner_add_left]
      map_smul' := by
        intro a p
        ext <;> simp [inner_smul_left, mul_comm] }
  have hS_eq :
      S = L '' ((fun p : H × ℝ ↦ p - (x, 0)) '' epigraph g.asEReal) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p - (x, 0), ⟨p, hp, rfl⟩, ?_⟩
      rcases p with ⟨y, η⟩
      simp [T, L, sub_eq_add_neg]
    · rintro ⟨r, ⟨p, hp, hp_eq⟩, hq⟩
      refine ⟨p, hp, ?_⟩
      rcases p with ⟨y, η⟩
      subst r
      simpa [T, L, sub_eq_add_neg] using hq
  have hSconv : Convex ℝ S := by
    have hEpiConv : Convex ℝ (epigraph g.asEReal) := hconv.convex_epigraph_asEReal
    have htranslated :
        Convex ℝ ((fun p : H × ℝ ↦ p - (x, 0)) '' epigraph g.asEReal) := by
      simpa [sub_eq_add_neg, add_comm] using hEpiConv.translate (-(x, (0 : ℝ)))
    rw [hS_eq]
    exact htranslated.linear_image L
  have hx_epi : (x, 0) ∈ epigraph g.asEReal := by
    -- The boundary condition `g x = 0` puts `(x, 0)` on the epigraph graph.
    rw [mem_epigraph_iff]
    simpa [hx0]
  have h0S : ((0 : ℝ), (0 : ℝ)) ∈ S := by
    refine ⟨(x, 0), hx_epi, ?_⟩
    simp [T]
  have hdisj :
      Disjoint (Set.Ioi (0 : ℝ) ×ˢ Set.Iio (0 : ℝ)) S := by
    simpa [S, T] using
      epigraphInnerHeightImage_disjoint_openQuadrant (g := g) (x := x) hx0 hu
  have hSneg : ∃ p ∈ S, p.2 < 0 := by
    rcases hneg with ⟨z, hz⟩
    have hz_lt : (g z : EReal) < 0 := by
      simpa [mem_strictLowerLevelSet_iff] using hz
    have hz_dom : z ∈ effectiveDomain g := by
      rw [mem_effectiveDomain_iff]
      exact lt_trans hz_lt EReal.zero_lt_top
    have hz_top : (g z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
    have hz_bot : (g z : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (g z : EReal) from (g z).2)
    have hz_epi : (z, (g z : EReal).toReal) ∈ epigraph g.asEReal := by
      rw [mem_epigraph_iff]
      simpa using (show (g z : EReal) ≤ (((g z : EReal).toReal : ℝ) : EReal) by
        rw [EReal.coe_toReal hz_top hz_bot])
    have hz_toReal_neg : (g z : EReal).toReal < 0 := by
      have hcast : ((((g z : EReal).toReal : ℝ) : EReal) < (0 : EReal)) := by
        simpa [EReal.coe_toReal hz_top hz_bot] using hz_lt
      exact_mod_cast hcast
    refine ⟨T (z, (g z : EReal).toReal), ⟨(z, (g z : EReal).toReal), hz_epi, rfl⟩, ?_⟩
    simpa [T] using hz_toReal_neg
  rcases
      exists_nonnegativeSlope_of_disjoint_epigraphInnerHeightImage hSconv h0S hdisj hSneg with
    ⟨a, ha, hslope⟩
  refine ⟨a, ha, ?_⟩
  -- The slope inequality on the image set rewrites exactly as the pointwise normal-cone test.
  refine (mem_normalCone_iff_forall_inner_nonpos (C := epigraph g.asEReal) (x := (x, 0)) hx_epi).2 ?_
  intro p hp
  rcases p with ⟨y, η⟩
  have hpS : T (y, η) ∈ S := ⟨(y, η), hp, rfl⟩
  have hslope' : ⟪y - x, u⟫_ℝ ≤ a * η := by
    simpa [T] using hslope (T (y, η)) hpS
  have hinner_pair :
      ⟪(y - x, η), (u, -a)⟫_ℝ = ⟪y - x, u⟫_ℝ - a * η := by
    calc
      ⟪(y - x, η), (u, -a)⟫_ℝ
          = ⟪y - x, u⟫_ℝ + η * (-a) := inner_pair_eq_add_mul_local
      _ = ⟪y - x, u⟫_ℝ - a * η := by ring
  have hnonpos : ⟪y - x, u⟫_ℝ - a * η ≤ 0 := by
    linarith
  have hnonpos_pair : ⟪(y - x, η), (u, -a)⟫_ℝ ≤ 0 := by
    rw [hinner_pair]
    exact hnonpos
  simpa using hnonpos_pair

/- Source/core/bridge triage:
- `source-facing`: Lemma 27.20 is the single-inequality normal-cone formula for the nonpositive
  sublevel set `lowerLevelSet g 0`, split into the boundary case `g x = 0` and the interior case
  `g x < 0`.
- `core/canonical`: the Chapter 16 owner abstraction is the epigraph normal-cone decomposition
  `normalCone_epigraph_eq_effectiveDomain_normal_zero_union_positive_subdifferential`, together
  with the indicator/normal-cone bridge `subdifferential_setIndicator_eq_normalCone`.
- `bridge/view`: this file keeps only the source-facing `≤ 0` specialization, but expressed through
  the project owner `lowerLevelSet`. The paired `cases` theorem is derived API assembled from the
  two clause-specific source-facing statements.

Primitive data: `g`, the convexity hypothesis `ConvexOn g (effectiveDomain g)`, the source
feasibility hypothesis `(strictLowerLevelSet g.asEReal 0).Nonempty`, and the boundary or interior
condition at the evaluation point `x`.
Derived API: membership of `x` in `lowerLevelSet g 0` is still a consequence of `g x = 0` or
`g x < 0`, but the source's strict negative feasibility hypothesis remains part of the public
interface.
-/

-- Semantic recall note: `lean_leansearch` only surfaced generic convex sublevel-set lemmas here.
-- The verified local owners for the source statement are the Chapter 16 epigraph normal-cone
-- owner, together with `effectiveDomain g`, `∂ g`, `N[C]`, and `cone`.

/-! The source-facing nonpositive-sublevel normal-cone formula is accompanied below by
boundary and interior branch theorems. -/
/-- Boundary clause for the nonpositive-sublevel normal-cone formula: let `g : H → ]-∞,+∞]`
be convex, assume `(strictLowerLevelSet g.asEReal 0).Nonempty`, and set `C = lowerLevelSet g 0`.
If `g x = 0`, then `N[C] x = N[effectiveDomain g] x ∪ cone ((∂ g) x)`. -/
theorem
    normalCone_nonpositiveSublevel_eq_domainNormal_union_subdifferentialCone_of_eq_zero
    (hconv : ConvexOn g (effectiveDomain g))
    (hneg : (strictLowerLevelSet g.asEReal 0).Nonempty)
    (hx0 : (g x : EReal) = 0) :
    N[lowerLevelSet g 0] x =
      N[effectiveDomain g] x ∪ cone ((∂ g) x) := by
  ext u
  constructor
  · intro hu
    -- Lift the lower-level normal to the epigraph, then project back with Proposition 16.35.
    have hlift :=
      mem_epigraphNormal_zeroHeight_of_mem_normalCone_nonpositiveSublevel
        (g := g) (x := x) (hconv := hconv) (hneg := hneg) (hx0 := hx0) hu
    rcases hlift with
      ⟨a, ha, hpair⟩
    exact
      mem_domainNormal_or_subdifferentialCone_of_mem_epigraphNormal_zeroHeight
        (g := g) (x := x) hx0 ha hpair
  · -- The reverse inclusion is the direct domain-normal/subgradient argument.
    intro hu
    exact
      domainNormalUnionSubdifferentialCone_subset_normalCone_nonpositiveSublevel_of_eq_zero
        (g := g) (x := x) hconv hx0 hu

/-- Interior clause for the nonpositive-sublevel normal-cone formula: let `g : H → ]-∞,+∞]`
be convex, assume `(strictLowerLevelSet g.asEReal 0).Nonempty`, and set `C = lowerLevelSet g 0`.
If `g x < 0`, then `N[C] x = N[effectiveDomain g] x`. -/
theorem
    normalCone_nonpositiveSublevel_eq_domainNormal_of_lt_zero
    (hconv : ConvexOn g (effectiveDomain g))
    (hneg : (strictLowerLevelSet g.asEReal 0).Nonempty)
    (hxneg : (g x : EReal) < 0) :
    N[lowerLevelSet g 0] x = N[effectiveDomain g] x := by
  have hx_level : x ∈ lowerLevelSet g 0 := by
    rw [mem_lowerLevelSet_iff]
    exact le_of_lt hxneg
  have hx_dom : x ∈ effectiveDomain g := by
    rw [mem_effectiveDomain_iff]
    exact lt_trans hxneg EReal.zero_lt_top
  have hlevel_subset_domain : lowerLevelSet g 0 ⊆ effectiveDomain g := by
    intro y hy
    exact mem_effectiveDomain_of_mem_lowerLevelSet_zero hy
  ext u
  constructor
  · intro hu
    -- Test the lower-level normal on a short segment from `x` toward an arbitrary domain point.
    refine (mem_normalCone_iff_forall_inner_nonpos hx_dom).2 ?_
    have hnormal :=
      (mem_normalCone_iff_forall_inner_nonpos hx_level).1 hu
    intro y hy
    let gx : ℝ := (g x : EReal).toReal
    let gy : ℝ := (g y : EReal).toReal
    let d : ℝ := |gy - gx| + 1
    let α : ℝ := min (1 / 2 : ℝ) ((-gx) / (2 * d))
    have hx_real_neg' : (g x : EReal).toReal < 0 := by
      have hx_top : (g x : EReal) ≠ ⊤ := ne_of_lt (lt_trans hxneg EReal.zero_lt_top)
      have hx_bot : (g x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
      have hcast : (((g x : EReal).toReal : ℝ) : EReal) < ((0 : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hx_top hx_bot] using hxneg
      exact_mod_cast hcast
    have hx_real_neg : gx < 0 := by
      simpa [gx] using hx_real_neg'
    have hd_pos : 0 < d := by
      dsimp [d]
      positivity
    have hratio_pos : 0 < (-gx) / (2 * d) := by
      have hneg_gx : 0 < -gx := by
        linarith
      positivity
    have hα0 : 0 < α := by
      exact lt_min (by norm_num) hratio_pos
    have hα_lt_half : α ≤ 1 / 2 := min_le_left _ _
    have hα1 : α < 1 := by
      linarith
    have hα_le_ratio : α ≤ (-gx) / (2 * d) := min_le_right _ _
    have htwo_d_pos : 0 < 2 * d := by
      positivity
    have hα_bound : α * (2 * d) ≤ -gx := by
      have hmul := mul_le_mul_of_nonneg_right hα_le_ratio htwo_d_pos.le
      calc
        α * (2 * d) ≤ ((-gx) / (2 * d)) * (2 * d) := hmul
        _ = -gx := by
          field_simp [htwo_d_pos.ne']
    have habs_lt : 2 * |gy - gx| < 2 * d := by
      dsimp [d]
      nlinarith [abs_nonneg (gy - gx)]
    have hmul_lt : α * (2 * |gy - gx|) < α * (2 * d) := by
      exact mul_lt_mul_of_pos_left habs_lt hα0
    have hα_abs : α * |gy - gx| < -gx / 2 := by
      have htmp : α * (2 * |gy - gx|) < -gx := lt_of_lt_of_le hmul_lt hα_bound
      nlinarith
    have hα_diff_le : α * (gy - gx) ≤ α * |gy - gx| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self (gy - gx)) hα0.le
    have hreal_lt0 : α * gy + (1 - α) * gx < 0 := by
      have hmid : gx + α * |gy - gx| < 0 := by
        linarith
      have hrewrite : α * gy + (1 - α) * gx = gx + α * (gy - gx) := by
        ring
      rw [hrewrite]
      have hle : gx + α * (gy - gx) ≤ gx + α * |gy - gx| := by
        linarith
      exact lt_of_le_of_lt hle hmid
    let z : H := α • y + (1 - α) • x
    have hz_mem : z ∈ lowerLevelSet g 0 := by
      have hx_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_dom)
      have hx_bot : (g x : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (g x : EReal) from (g x).2)
      have hy_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hy_bot : (g y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (g y : EReal) from (g y).2)
      have hconv_ineq :
          (g z : EReal) ≤
            (α : EReal) * (g y : EReal) + (1 - α : EReal) * (g x : EReal) := by
        simpa [z] using hconv.ineq hy hx_dom hα0 hα1
      have hy_coe : (g y : EReal) = (gy : EReal) := by
        simpa [gy] using (EReal.coe_toReal hy_top hy_bot).symm
      have hx_coe : (g x : EReal) = (gx : EReal) := by
        simpa [gx] using (EReal.coe_toReal hx_top hx_bot).symm
      have hsum :
          (α : EReal) * (g y : EReal) + (1 - α : EReal) * (g x : EReal) =
            ((α * (g y : EReal).toReal + (1 - α) * (g x : EReal).toReal : ℝ) : EReal) := by
        calc
          (α : EReal) * (g y : EReal) + (1 - α : EReal) * (g x : EReal)
              = (α : EReal) * (gy : EReal) + (1 - α : EReal) * (gx : EReal) := by
                  rw [hy_coe, hx_coe]
          _ = ((α * (g y : EReal).toReal + (1 - α) * (g x : EReal).toReal : ℝ) : EReal) := by
                simp [gx, gy, EReal.coe_mul, EReal.coe_add]
      have hrhs_neg :
          (α : EReal) * (g y : EReal) + (1 - α : EReal) * (g x : EReal) < 0 := by
        have hreal_lt0' :
            α * (g y : EReal).toReal + (1 - α) * (g x : EReal).toReal < 0 := by
          simpa [gx, gy] using hreal_lt0
        rw [hsum]
        exact_mod_cast hreal_lt0'
      rw [mem_lowerLevelSet_iff]
      exact le_of_lt (lt_of_le_of_lt hconv_ineq hrhs_neg)
    have hz_nonpos : ⟪z - x, u⟫_ℝ ≤ 0 := hnormal z hz_mem
    have hz_sub : z - x = α • (y - x) := by
      have hx_shift : (1 - α) • x - x = (-α) • x := by
        calc
          (1 - α) • x - x = (1 - α) • x + -x := by
            simp [sub_eq_add_neg]
          _ = (1 - α) • x + (-1 : ℝ) • x := by simp
          _ = ((1 - α) + -1) • x := by rw [← add_smul]
          _ = (-α) • x := by congr 1; ring
      dsimp [z]
      calc
        α • y + (1 - α) • x - x = α • y + ((1 - α) • x - x) := by
          simp [sub_eq_add_neg, add_assoc]
        _ = α • y + (-α) • x := by rw [hx_shift]
        _ = α • y - α • x := by simp [sub_eq_add_neg, neg_smul]
        _ = α • (y - x) := by
          rw [smul_sub]
    have hscaled : α * ⟪y - x, u⟫_ℝ ≤ 0 := by
      simpa [hz_sub, real_inner_smul_left] using hz_nonpos
    nlinarith [hscaled, hα0]
  · intro hu
    -- Restrict a domain normal to the smaller feasible set `lowerLevelSet g 0`.
    refine (mem_normalCone_iff_forall_inner_nonpos hx_level).2 ?_
    have hdomain :=
      (mem_normalCone_iff_forall_inner_nonpos hx_dom).1 hu
    intro y hy
    exact hdomain y (hlevel_subset_domain hy)

/-- Lemma 27.20: let `g : H → ]-∞,+∞]` be convex, assume
`(strictLowerLevelSet g.asEReal 0).Nonempty`, set `C = lowerLevelSet g 0`, and let `x ∈ C`.
Then
`N[C] x = if (g x : EReal) = 0 then N[effectiveDomain g] x ∪ cone ((∂ g) x)
  else N[effectiveDomain g] x`. -/
theorem normalCone_nonpositiveSublevel
    (hconv : ConvexOn g (effectiveDomain g))
    (hneg : (strictLowerLevelSet g.asEReal 0).Nonempty)
    (hx : x ∈ lowerLevelSet g 0) :
    N[lowerLevelSet g 0] x =
      if (g x : EReal) = 0 then
        N[effectiveDomain g] x ∪ cone ((∂ g) x)
      else
        N[effectiveDomain g] x := by
  have hx_le : (g x : EReal) ≤ 0 := by
    simpa [mem_lowerLevelSet_iff] using hx
  rcases eq_or_lt_of_le hx_le with hx0 | hxneg
  · -- The boundary clause is the previously established zero-value branch.
    rw [if_pos hx0]
    exact
      normalCone_nonpositiveSublevel_eq_domainNormal_union_subdifferentialCone_of_eq_zero
        hconv hneg hx0
  · -- The strict interior clause is the previously established negative-value branch.
    rw [if_neg hxneg.ne]
    exact normalCone_nonpositiveSublevel_eq_domainNormal_of_lt_zero hconv hneg hxneg

/-- Derived API bundling the boundary and interior clauses for the nonpositive sublevel set. -/
theorem normalCone_nonpositiveSublevel_cases
    (hconv : ConvexOn g (effectiveDomain g))
    (hneg : (strictLowerLevelSet g.asEReal 0).Nonempty) :
    (((g x : EReal) = 0 →
        N[lowerLevelSet g 0] x =
          N[effectiveDomain g] x ∪ cone ((∂ g) x)) ∧
      ((g x : EReal) < 0 →
        N[lowerLevelSet g 0] x = N[effectiveDomain g] x)) := by
  constructor
  · intro hx0
    exact
      normalCone_nonpositiveSublevel_eq_domainNormal_union_subdifferentialCone_of_eq_zero
        hconv hneg hx0
  · intro hxneg
    exact normalCone_nonpositiveSublevel_eq_domainNormal_of_lt_zero hconv hneg hxneg

end ConvexInequalityConstraints

end

end ERealFunction
