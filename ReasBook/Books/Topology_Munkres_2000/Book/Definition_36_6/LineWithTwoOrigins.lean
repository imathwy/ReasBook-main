module

public import Mathlib.Topology.Bases
public import Mathlib.Data.Real.Basic

public section

open Set

/-- The two distinguished origins of the line with two origins. -/
inductive LineWithTwoOrigins.Origin where
  | p
  | q
  deriving DecidableEq

namespace LineWithTwoOrigins.Origin

/-- The two origins have the canonical finite enumeration `{p, q}`. -/
instance instFintype : Fintype LineWithTwoOrigins.Origin where
  elems := {.p, .q}
  complete o := by cases o <;> simp

end LineWithTwoOrigins.Origin

/-- The line with two origins, consisting of nonzero real points and two origins. -/
inductive LineWithTwoOrigins where
  | point (x : ℝ) (hx : x ≠ 0)
  | origin (o : LineWithTwoOrigins.Origin)

namespace LineWithTwoOrigins

/-- The real coordinate, sending both origins to `0`. -/
def toReal : LineWithTwoOrigins → ℝ
  | point x _ => x
  | origin _ => 0

/-- The coordinate of a nonzero real point is its defining real number. -/
theorem toReal_point (x : ℝ) (hx : x ≠ 0) : toReal (point x hx) = x := by
  -- The coordinate map computes directly on the point constructor.
  rfl

/-- The coordinate of either distinguished origin is `0`. -/
theorem toReal_origin (o : Origin) : toReal (origin o) = 0 := by
  -- The coordinate map computes directly on the origin constructor.
  rfl

/-- The points whose nonzero real coordinate belongs to the open interval `(l, r)`. -/
def interval (l r : ℝ) : Set LineWithTwoOrigins :=
  {z | match z with
    | point x _ => x ∈ Ioo l r
    | origin _ => False}

/-- Membership of a nonzero real point in a transported open interval. -/
theorem point_mem_interval_iff {x l r : ℝ} (hx : x ≠ 0) :
    point x hx ∈ interval l r ↔ x ∈ Ioo l r := Iff.rfl

/-- Neither distinguished origin belongs to a transported open interval. -/
theorem origin_not_mem_interval (o : Origin) (l r : ℝ) :
    origin o ∉ interval l r := by simp [interval]

/-- The punctured symmetric interval about the selected origin, together with that origin. -/
def originNeighborhood (o : Origin) (a : ℝ) : Set LineWithTwoOrigins :=
  interval (-a) a ∪ {origin o}

/-- Membership in an origin neighborhood is interval membership or equality to the chosen origin. -/
theorem mem_originNeighborhood_iff {z : LineWithTwoOrigins} {o : Origin} {a : ℝ} :
    z ∈ originNeighborhood o a ↔ z ∈ interval (-a) a ∨ z = origin o := by
  -- Unfold the union while retaining the interval as the stable geometric interface.
  simp only [originNeighborhood, mem_union, mem_singleton_iff]

/-- Helper for Definition 36.6: transported intervals are monotone under inclusion of their
underlying real intervals. -/
private theorem interval_subset_interval {l r l' r' : ℝ}
    (h : Ioo l r ⊆ Ioo l' r') : interval l r ⊆ interval l' r' := by
  -- Point membership transports through `h`; origins occur in neither interval.
  intro z hz
  cases z with
  | point x hx =>
      exact (point_mem_interval_iff hx).2 (h ((point_mem_interval_iff hx).1 hz))
  | origin o =>
      exact (origin_not_mem_interval o l r hz).elim

/-- Helper for Definition 36.6: nested radii give nested neighborhoods of a fixed origin. -/
theorem originNeighborhood_mono {o : Origin} {a b : ℝ} (hab : a ≤ b) :
    originNeighborhood o a ⊆ originNeighborhood o b := by
  -- Preserve the selected origin and enlarge only the symmetric real interval.
  intro z hz
  rcases mem_originNeighborhood_iff.1 hz with hza | hzo
  · refine mem_originNeighborhood_iff.2 (Or.inl ?_)
    exact interval_subset_interval (Ioo_subset_Ioo (neg_le_neg hab) hab) hza
  · exact mem_originNeighborhood_iff.2 (Or.inr hzo)

/-- Helper for Definition 36.6: two real open intervals through a point distinct from `c`
have a smaller common open interval through that point which avoids `c`. -/
private theorem exists_Ioo_subset_inter_avoiding {x c l₁ r₁ l₂ r₂ : ℝ}
    (hxc : x ≠ c) (hx₁ : x ∈ Ioo l₁ r₁) (hx₂ : x ∈ Ioo l₂ r₂) :
    ∃ l r : ℝ, l < r ∧ x ∈ Ioo l r ∧ c ∉ Ioo l r ∧
      Ioo l r ⊆ Ioo l₁ r₁ ∩ Ioo l₂ r₂ := by
  -- Choose the new interval on the side of `c` containing `x`.
  rcases lt_or_gt_of_ne hxc with hxc | hcx
  · refine ⟨max l₁ l₂, min (min r₁ r₂) c, ?_, ?_, ?_, ?_⟩
    · exact (max_lt hx₁.1 hx₂.1).trans (lt_min (lt_min hx₁.2 hx₂.2) hxc)
    · exact ⟨max_lt hx₁.1 hx₂.1, lt_min (lt_min hx₁.2 hx₂.2) hxc⟩
    · intro hc
      exact (not_lt_of_ge (min_le_right (min r₁ r₂) c)) hc.2
    · intro y hy
      exact ⟨
        ⟨(le_max_left l₁ l₂).trans_lt hy.1,
          hy.2.trans_le ((min_le_left (min r₁ r₂) c).trans (min_le_left r₁ r₂))⟩,
        ⟨(le_max_right l₁ l₂).trans_lt hy.1,
          hy.2.trans_le ((min_le_left (min r₁ r₂) c).trans (min_le_right r₁ r₂))⟩⟩
  · refine ⟨max (max l₁ l₂) c, min r₁ r₂, ?_, ?_, ?_, ?_⟩
    · exact (max_lt (max_lt hx₁.1 hx₂.1) hcx).trans (lt_min hx₁.2 hx₂.2)
    · exact ⟨max_lt (max_lt hx₁.1 hx₂.1) hcx, lt_min hx₁.2 hx₂.2⟩
    · intro hc
      exact (not_lt_of_ge (le_max_right (max l₁ l₂) c)) hc.1
    · intro y hy
      exact ⟨
        ⟨(le_max_left l₁ l₂).trans (le_max_left (max l₁ l₂) c) |>.trans_lt hy.1,
          hy.2.trans_le (min_le_left r₁ r₂)⟩,
        ⟨(le_max_right l₁ l₂).trans (le_max_left (max l₁ l₂) c) |>.trans_lt hy.1,
          hy.2.trans_le (min_le_right r₁ r₂)⟩⟩

/-- The designated basis sets for the line with two origins. -/
def basis : Set (Set LineWithTwoOrigins) :=
  {s | (∃ l r : ℝ, l < r ∧ 0 ∉ Ioo l r ∧ s = interval l r) ∨
    ∃ o : Origin, ∃ a : ℝ, 0 < a ∧ s = originNeighborhood o a}

/-- A set belongs to the designated basis exactly when it is one of the two source families. -/
theorem mem_basis_iff {s : Set LineWithTwoOrigins} :
    s ∈ basis ↔
      (∃ l r : ℝ, l < r ∧ 0 ∉ Ioo l r ∧ s = interval l r) ∨
        ∃ o : Origin, ∃ a : ℝ, 0 < a ∧ s = originNeighborhood o a := Iff.rfl

/-- Helper for Definition 36.6: a real point lying in a basis set has a real open interval
around its coordinate whose transported interval is contained in that basis set. -/
private theorem exists_interval_subset_basis_at_point {s : Set LineWithTwoOrigins}
    {x : ℝ} {hx : x ≠ 0} (hs : s ∈ basis) (hxs : point x hx ∈ s) :
    ∃ l r : ℝ, x ∈ Ioo l r ∧ interval l r ⊆ s := by
  -- Separate the ordinary-interval and selected-origin-neighborhood source families.
  rcases mem_basis_iff.1 hs with ⟨l, r, _, _, rfl⟩ | ⟨o, a, _, rfl⟩
  · exact ⟨l, r, (point_mem_interval_iff hx).1 hxs, Subset.rfl⟩
  · rcases mem_originNeighborhood_iff.1 hxs with hxa | hxo
    · exact ⟨-a, a, (point_mem_interval_iff hx).1 hxa, subset_union_left⟩
    · exact (LineWithTwoOrigins.noConfusion hxo)

/-- Helper for Definition 36.6: a basis set containing an origin is a positive-radius
neighborhood of that same origin. -/
private theorem exists_originNeighborhood_eq_of_mem_basis {s : Set LineWithTwoOrigins}
    {o : Origin} (hs : s ∈ basis) (hos : origin o ∈ s) :
    ∃ a : ℝ, 0 < a ∧ s = originNeighborhood o a := by
  -- Ordinary intervals contain no origin, so only the neighborhood family remains.
  rcases mem_basis_iff.1 hs with ⟨l, r, _, _, hslr⟩ | ⟨o', a, ha, hsoa⟩
  · subst s
    exact (origin_not_mem_interval o l r hos).elim
  · subst s
    rcases mem_originNeighborhood_iff.1 hos with hoa | hoo
    · exact (origin_not_mem_interval o (-a) a hoa).elim
    · have ho : o = o' := LineWithTwoOrigins.origin.inj hoo
      subst o'
      exact ⟨a, ha, rfl⟩

/-- The topology on the line with two origins generated by its designated basis sets. -/
instance instTopologicalSpace : TopologicalSpace LineWithTwoOrigins :=
  TopologicalSpace.generateFrom basis

/-- The installed topology is generated by the designated basis sets. -/
theorem topology_eq_generateFrom :
    (inferInstance : TopologicalSpace LineWithTwoOrigins) =
      TopologicalSpace.generateFrom basis := rfl

/-- Helper for Definition 36.6: the designated basis sets cover the line with two origins. -/
theorem basis_sUnion_eq : ⋃₀ basis = Set.univ := by
  -- Every nonzero point lies in a sufficiently large selected-origin neighborhood, and each
  -- origin lies in its own radius-one neighborhood.
  refine sUnion_eq_univ_iff.2 fun z ↦ ?_
  cases z with
  | point x hx =>
      have hRadius : 0 < |x| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg x) zero_lt_one
      have hAbs : |x| < |x| + 1 := lt_add_of_pos_right |x| zero_lt_one
      have hInterval : point x hx ∈ interval (- (|x| + 1)) (|x| + 1) :=
        (point_mem_interval_iff hx).2 (abs_lt.1 hAbs)
      have hBasis : originNeighborhood .p (|x| + 1) ∈ basis :=
        mem_basis_iff.2 (Or.inr ⟨.p, |x| + 1, hRadius, rfl⟩)
      have hMem : point x hx ∈ originNeighborhood .p (|x| + 1) :=
        mem_originNeighborhood_iff.2 (Or.inl hInterval)
      exact ⟨originNeighborhood .p (|x| + 1), hBasis, hMem⟩
  | origin o =>
      have hOne : (0 : ℝ) < 1 := zero_lt_one
      have hBasis : originNeighborhood o 1 ∈ basis :=
        mem_basis_iff.2 (Or.inr ⟨o, 1, hOne, rfl⟩)
      have hMem : origin o ∈ originNeighborhood o 1 :=
        mem_originNeighborhood_iff.2 (Or.inr rfl)
      exact ⟨originNeighborhood o 1, hBasis, hMem⟩

/-- Helper for Definition 36.6: any common point of two designated basis sets has a
designated basis neighborhood contained in their intersection. -/
theorem basis_exists_subset_inter :
    ∀ s ∈ basis, ∀ t ∈ basis, ∀ z ∈ s ∩ t,
      ∃ u ∈ basis, z ∈ u ∧ u ⊆ s ∩ t := by
  -- Split according to the global coordinate invariant: nonzero real coordinates use a
  -- smaller avoiding interval, while an origin uses the minimum of two radii.
  intro s hs t ht z hz
  cases z with
  | point x hx =>
      obtain ⟨l₁, r₁, hx₁, hsub₁⟩ :=
        exists_interval_subset_basis_at_point hs hz.1
      obtain ⟨l₂, r₂, hx₂, hsub₂⟩ :=
        exists_interval_subset_basis_at_point ht hz.2
      obtain ⟨l, r, hlr, hxlr, hzero, hreal⟩ :=
        exists_Ioo_subset_inter_avoiding hx hx₁ hx₂
      have hBasis : interval l r ∈ basis :=
        mem_basis_iff.2 (Or.inl ⟨l, r, hlr, hzero, rfl⟩)
      have hMem : point x hx ∈ interval l r := (point_mem_interval_iff hx).2 hxlr
      have hReal₁ : Ioo l r ⊆ Ioo l₁ r₁ := fun y hy ↦ (hreal hy).1
      have hReal₂ : Ioo l r ⊆ Ioo l₂ r₂ := fun y hy ↦ (hreal hy).2
      have hInterval₁ : interval l r ⊆ interval l₁ r₁ := interval_subset_interval hReal₁
      have hInterval₂ : interval l r ⊆ interval l₂ r₂ := interval_subset_interval hReal₂
      have hSub : interval l r ⊆ s ∩ t := fun y hy ↦
        ⟨hsub₁ (hInterval₁ hy), hsub₂ (hInterval₂ hy)⟩
      exact ⟨interval l r, hBasis, hMem, hSub⟩
  | origin o =>
      obtain ⟨a, ha, hsEq⟩ := exists_originNeighborhood_eq_of_mem_basis hs hz.1
      obtain ⟨b, hb, htEq⟩ := exists_originNeighborhood_eq_of_mem_basis ht hz.2
      subst s
      subst t
      have hRadius : 0 < min a b := lt_min ha hb
      have hBasis : originNeighborhood o (min a b) ∈ basis :=
        mem_basis_iff.2 (Or.inr ⟨o, min a b, hRadius, rfl⟩)
      have hMem : origin o ∈ originNeighborhood o (min a b) :=
        mem_originNeighborhood_iff.2 (Or.inr rfl)
      have hSub : originNeighborhood o (min a b) ⊆
          originNeighborhood o a ∩ originNeighborhood o b := fun y hy ↦
        ⟨originNeighborhood_mono (min_le_left a b) hy,
          originNeighborhood_mono (min_le_right a b) hy⟩
      exact ⟨originNeighborhood o (min a b), hBasis, hMem, hSub⟩

end LineWithTwoOrigins
