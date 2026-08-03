module

public import Topology_Munkres_2000.Book.Definition_4_6
public import Mathlib.NumberTheory.Niven
public import Mathlib.Topology.Constructions

public section

namespace PositiveIntegerCollapse

/-- Two real numbers are related when they are equal or are both positive integers. -/
def rel (x y : ℝ) : Prop :=
  x = y ∨ (x ∈ ℤ₊ ∧ y ∈ ℤ₊)

/-- Collapsing the positive integers defines an equivalence relation on `ℝ`. -/
theorem rel_equivalence : Equivalence rel := by
  -- Equality supplies reflexivity, while the collapsed-set alternative is symmetric.
  refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
  · intro x y hxy
    rcases hxy with hxy | ⟨hx, hy⟩
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨hy, hx⟩
  · intro x y z hxy hyz
    -- If neither relation step is equality, all three points are positive integers.
    rcases hxy with hxy | ⟨hx, hy⟩
    · subst y
      exact hyz
    · rcases hyz with hyz | ⟨hy, hz⟩
      · subst z
        exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

/-- The setoid on `ℝ` that identifies all positive integers with one another. -/
def setoid : Setoid ℝ where
  r := rel
  iseqv := rel_equivalence

end PositiveIntegerCollapse

/-- The quotient of `ℝ` obtained by collapsing `ℤ₊` to one point. -/
abbrev PositiveIntegerCollapse := Quotient PositiveIntegerCollapse.setoid

namespace PositiveIntegerCollapse

/-- The canonical map from `ℝ` to the positive-integer collapse. -/
def map : ℝ → PositiveIntegerCollapse :=
  Quotient.mk setoid

/-- The common quotient point represented by the positive integer `1`. -/
def point : PositiveIntegerCollapse :=
  map 1

/-- A real number maps to the collapsed point exactly when it is a positive integer. -/
theorem map_eq_point_iff (x : ℝ) :
    map x = point ↔ x ∈ ℤ₊ := by
  -- Quotient equality is precisely the defining relation with the representative `1`.
  rw [show point = map 1 from rfl, show map x = map 1 ↔ rel x 1 from Quotient.eq]
  constructor
  · intro hx
    rcases hx with hx | ⟨hx, _⟩
    · subst x
      rw [Real.positiveIntegers_eq_range_pnatCast]
      refine ⟨⟨1, Nat.zero_lt_one⟩, ?_⟩
      norm_num
    · exact hx
  · intro hx
    right
    refine ⟨hx, ?_⟩
    rw [Real.positiveIntegers_eq_range_pnatCast]
    refine ⟨⟨1, Nat.zero_lt_one⟩, ?_⟩
    norm_num

/-- The canonical collapse map is a quotient map. -/
theorem map_isQuotientMap :
    Topology.IsQuotientMap map := by
  -- The topology on a quotient is defined so that its canonical projection is quotient.
  exact isQuotientMap_quotient_mk'

/-- The product of the collapse map with the identity map on `ℚ`. -/
def productMap : ℝ × ℚ → PositiveIntegerCollapse × ℚ :=
  Prod.map map (id : ℚ → ℚ)

/-- The irrational center height `cₙ = √2 / n`. -/
noncomputable def centerHeight (n : ℕ+) : ℝ :=
  Real.sqrt 2 / (n : ℝ)

/-- No rational number has the center height `cₙ`. -/
theorem centerHeight_ne_rat (n : ℕ+) (q : ℚ) :
    (q : ℝ) ≠ centerHeight n := by
  -- Dividing `√2` by a nonzero natural preserves irrationality.
  have hirr : Irrational (Real.sqrt 2 / (n : ℕ)) :=
    irrational_sqrt_two.div_natCast n.pos.ne'
  simpa [centerHeight] using (hirr.ne_rat q).symm

/-- Helper for Example 22.7: the center heights become arbitrarily small. -/
theorem exists_centerHeight_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ+, centerHeight n < δ := by
  -- Apply the Archimedean estimate to the reciprocal after scaling by `√2`.
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hδ hsqrt)
  refine ⟨k.succPNat, ?_⟩
  have hk' : 1 / ((k + 1 : ℕ) : ℝ) < δ / Real.sqrt 2 := by
    norm_num [Nat.cast_add, Nat.cast_one] at hk ⊢
    exact hk
  calc
    centerHeight k.succPNat = Real.sqrt 2 * (1 / ((k + 1 : ℕ) : ℝ)) := by
      simp [centerHeight, Nat.succPNat_coe, div_eq_mul_inv]
    _ < Real.sqrt 2 * (δ / Real.sqrt 2) := mul_lt_mul_of_pos_left hk' hsqrt
    _ = δ := by field_simp

/-- The open region between `x = n - 1/4` and `x = n + 1/4` lying above both
or below both diagonal lines through `(n, cₙ)`. -/
def witnessPiece (n : ℕ+) : Set (ℝ × ℚ) :=
  {z | |z.1 - (n : ℝ)| < (1 : ℝ) / 4 ∧
    |(z.2 : ℝ) - centerHeight n| > |z.1 - (n : ℝ)|}

/-- Every rational-height point on the vertical line through `n` belongs to
`witnessPiece n`. -/
theorem verticalFiber_mem_witnessPiece (n : ℕ+) (q : ℚ) :
    (((n : ℝ), q) : ℝ × ℚ) ∈ witnessPiece n := by
  -- At the center line the horizontal distance is zero, and irrationality makes the
  -- vertical distance strictly positive.
  unfold witnessPiece
  constructor
  · norm_num
  · rw [sub_self, abs_zero]
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (centerHeight_ne_rat n q)

/-- The union of the witness regions over all positive integers. -/
def witnessSet : Set (ℝ × ℚ) :=
  ⋃ n : ℕ+, witnessPiece n

/-- The witness set is open in `ℝ × ℚ`. -/
theorem isOpen_witnessSet :
    IsOpen witnessSet := by
  -- Each piece is the intersection of two strict inequalities of continuous functions.
  apply isOpen_iUnion
  intro n
  have horizontalContinuous : Continuous (fun z : ℝ × ℚ ↦ |z.1 - (n : ℝ)|) :=
    (continuous_fst.sub continuous_const).abs
  have verticalContinuous : Continuous (fun z : ℝ × ℚ ↦
      |(z.2 : ℝ) - centerHeight n|) :=
    ((Rat.continuous_coe_real.comp continuous_snd).sub continuous_const).abs
  exact (isOpen_lt horizontalContinuous continuous_const).inter
    (isOpen_lt horizontalContinuous verticalContinuous)

/-- The witness set is saturated with respect to `productMap`. -/
theorem witnessSet_saturated :
    productMap ⁻¹' (productMap '' witnessSet) = witnessSet := by
  -- Equality under the product map fixes the rational coordinate and either fixes the real
  -- coordinate or places both real coordinates in the collapsed positive-integer fiber.
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hq : w.2 = z.2 := by
      simpa [productMap] using congrArg (fun p ↦ p.2) hwz
    have hmap : map w.1 = map z.1 := by
      simpa [productMap] using congrArg (fun p ↦ p.1) hwz
    have hx : rel w.1 z.1 := Quotient.eq.mp hmap
    rcases hx with hx | ⟨_, hzpos⟩
    · cases Prod.ext hx hq
      exact hw
    · rw [Real.positiveIntegers_eq_range_pnatCast] at hzpos
      obtain ⟨n, hn⟩ := hzpos
      have hzpair : z = ((n : ℝ), z.2) := Prod.ext hn.symm rfl
      rw [hzpair]
      exact Set.mem_iUnion.2 ⟨n, verticalFiber_mem_witnessPiece n z.2⟩
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The image of the open saturated witness set is not open. -/
theorem not_isOpen_image_witnessSet :
    ¬ IsOpen (productMap '' witnessSet) := by
  -- An open image would contain a rectangular neighborhood of the collapsed point at height zero.
  intro hopen
  have hone : ((1 : ℝ), (0 : ℚ)) ∈ witnessSet := by
    have honePiece := verticalFiber_mem_witnessPiece (1 : ℕ+) 0
    unfold witnessSet
    simpa using Set.mem_iUnion.2 ⟨(1 : ℕ+), honePiece⟩
  have hpoint : (point, (0 : ℚ)) ∈ productMap '' witnessSet := by
    refine ⟨((1 : ℝ), (0 : ℚ)), hone, ?_⟩
    rfl
  obtain ⟨W, I, hW, hI, hpointW, hzeroI, hrectangle⟩ :=
    isOpen_prod_iff.mp hopen point 0 hpoint
  obtain ⟨δ, hδ, hballI⟩ := Metric.isOpen_iff.mp hI 0 hzeroI
  obtain ⟨n, hncenter⟩ := exists_centerHeight_lt (half_pos hδ)
  have hnW : map (n : ℝ) ∈ W := by
    have hmap : map (n : ℝ) = point := by
      rw [map_eq_point_iff, Real.positiveIntegers_eq_range_pnatCast]
      exact ⟨n, rfl⟩
    rwa [hmap]
  have hpreOpen : IsOpen (map ⁻¹' W) := map_isQuotientMap.continuous.isOpen_preimage W hW
  obtain ⟨ε, hε, hballW⟩ := Metric.isOpen_iff.mp hpreOpen (n : ℝ) hnW
  let d : ℝ := min (ε / 2) (min ((1 : ℝ) / 8) (δ / 2))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdε : d < ε := by
    have hdle : d ≤ ε / 2 := min_le_left _ _
    linarith
  have hdquarter : d < (1 : ℝ) / 4 := by
    have hdle : d ≤ (1 : ℝ) / 8 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hdδ : d ≤ δ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨q, hqlow, hqhigh⟩ :=
    exists_rat_btwn (show centerHeight n - d / 2 < centerHeight n + d / 2 by linarith)
  have hqclose : |(q : ℝ) - centerHeight n| < d := by
    rw [abs_lt]
    constructor <;> linarith
  have hqI : q ∈ I := by
    apply hballI
    rw [Metric.mem_ball]
    have hdist : dist q 0 = |(q : ℝ)| := by
      rw [← Rat.dist_cast, Real.dist_eq, Rat.cast_zero, sub_zero]
    rw [hdist]
    have hcenterNonneg : 0 ≤ centerHeight n := by
      unfold centerHeight
      positivity
    have hqupper : (q : ℝ) < δ := by linarith
    have hqlower : -δ < (q : ℝ) := by linarith
    exact (abs_lt).2 ⟨hqlower, hqupper⟩
  let x : ℝ := (n : ℝ) + d
  have hxW : map x ∈ W := by
    apply hballW
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [x]
    rw [add_sub_cancel_left, abs_of_pos hd]
    exact hdε
  have htargetImage : (map x, q) ∈ productMap '' witnessSet :=
    hrectangle ⟨hxW, hqI⟩
  have hxyWitness : (x, q) ∈ witnessSet := by
    rw [← witnessSet_saturated]
    simpa [productMap] using htargetImage
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxyWitness
  have hmn : m = n := by
    by_contra hne
    have hfar : ¬ |x - (m : ℝ)| < (1 : ℝ) / 4 := by
      rcases lt_or_gt_of_ne hne with hmn | hnm
      · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
        dsimp [x]
        rw [abs_of_nonneg]
        · linarith
        · linarith
      · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
        dsimp [x]
        rw [abs_of_nonpos]
        · linarith
        · linarith
    exact hfar hm.1
  subst m
  -- At the selected index, the rational point lies closer to the center height than its
  -- horizontal displacement, contradicting the defining diagonal-gap inequality.
  have hhorizontal : |x - (n : ℝ)| = d := by
    dsimp [x]
    rw [add_sub_cancel_left, abs_of_pos hd]
  change |x - (n : ℝ)| < (1 : ℝ) / 4 ∧
    |(q : ℝ) - centerHeight n| > |x - (n : ℝ)| at hm
  rw [hhorizontal] at hm
  linarith [hm.2, hqclose]

/-- The product of the collapse map with the identity map on `ℚ` is not a quotient map. -/
theorem not_isQuotientMap_productMap :
    ¬ Topology.IsQuotientMap productMap := by
  -- A quotient map would recognize openness from the open saturated preimage.
  intro hquot
  apply not_isOpen_image_witnessSet
  apply hquot.isOpen_preimage.mp
  rw [witnessSet_saturated]
  exact isOpen_witnessSet

/-- Example 22.7: The collapse map and the identity map on `ℚ` are quotient maps,
but their product is not a quotient map. -/
theorem quotientMaps_product_not_isQuotientMap :
    Topology.IsQuotientMap map ∧ Topology.IsQuotientMap (id : ℚ → ℚ) ∧
      ¬ Topology.IsQuotientMap productMap :=
  ⟨map_isQuotientMap, Topology.IsQuotientMap.id, not_isQuotientMap_productMap⟩

end PositiveIntegerCollapse


end
