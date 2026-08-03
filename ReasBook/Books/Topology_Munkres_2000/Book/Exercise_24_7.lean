module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.MonotoneContinuity

public section

open Set

noncomputable section

universe u v

/-- Part (a) of Exercise 24.7: A strictly order-preserving surjection between linearly
ordered spaces with their order topologies is a homeomorphism. -/
theorem strictMonoSurjective_isHomeomorph {X : Type u} {Y : Type v}
    [LinearOrder X] [LinearOrder Y] [TopologicalSpace X] [TopologicalSpace Y]
    [OrderTopology X] [OrderTopology Y] (f : X → Y) (hf : StrictMono f)
    (hsurj : Function.Surjective f) : IsHomeomorph f := by
  rw [← StrictMono.coe_orderIsoOfSurjective f hf hsurj]
  exact (hf.orderIsoOfSurjective f hsurj).toHomeomorph.isHomeomorph

/-- Part (b) of Exercise 24.7: A positive natural power is strictly order-preserving on
the nonnegative real numbers. -/
theorem nnrealPow_strictMono (n : ℕ+) :
    StrictMono (fun x : NNReal ↦ x ^ (n : ℕ)) :=
  (NNReal.powOrderIso (n : ℕ) n.ne_zero).strictMono

/-- Part (b) of Exercise 24.7: A positive natural power maps the nonnegative real
numbers onto themselves. -/
theorem nnrealPow_surjective (n : ℕ+) :
    Function.Surjective (fun x : NNReal ↦ x ^ (n : ℕ)) :=
  (NNReal.powOrderIso (n : ℕ) n.ne_zero).surjective

/-- The positive `n`th-root function on the nonnegative real numbers. -/
noncomputable def nnrealNthRoot (n : ℕ+) : NNReal → NNReal :=
  (NNReal.powOrderIso (n : ℕ) n.ne_zero).symm

/-- The inverse of the positive natural power map is given by the usual real-power formula. -/
theorem nnrealNthRoot_apply (n : ℕ+) (x : NNReal) :
    nnrealNthRoot n x = x ^ (((n : ℕ) : ℝ)⁻¹) := by
  apply (NNReal.powOrderIso (n : ℕ) n.ne_zero).injective
  change (nnrealNthRoot n x) ^ (n : ℕ) = (x ^ (((n : ℕ) : ℝ)⁻¹)) ^ (n : ℕ)
  rw [show (nnrealNthRoot n x) ^ (n : ℕ) = x from
    (NNReal.powOrderIso (n : ℕ) n.ne_zero).apply_symm_apply x]
  exact (NNReal.rpow_inv_natCast_pow x n.ne_zero).symm

/-- Part (b) of Exercise 24.7: Taking the positive `n`th root after raising to the
`n`th power returns the original nonnegative real number. -/
theorem nnrealNthRoot_leftInverse (n : ℕ+) :
    Function.LeftInverse (nnrealNthRoot n) (fun x : NNReal ↦ x ^ (n : ℕ)) :=
  (NNReal.powOrderIso (n : ℕ) n.ne_zero).left_inv

/-- Part (b) of Exercise 24.7: Raising the positive `n`th root to the `n`th power
returns the original nonnegative real number. -/
theorem nnrealNthRoot_rightInverse (n : ℕ+) :
    Function.RightInverse (nnrealNthRoot n) (fun x : NNReal ↦ x ^ (n : ℕ)) :=
  (NNReal.powOrderIso (n : ℕ) n.ne_zero).right_inv

/-- Part (b) of Exercise 24.7: The positive `n`th-root function is continuous on the
nonnegative real numbers. -/
theorem continuous_nnrealNthRoot (n : ℕ+) : Continuous (nnrealNthRoot n) :=
  (NNReal.powOrderIso (n : ℕ) n.ne_zero).symm.continuous

/-- The gapped real subspace `(-∞, -1) ∪ [0, ∞)` from Exercise 24.7. -/
def gapDomain : Set ℝ := Iio (-1 : ℝ) ∪ Ici 0

/-- The piecewise map from the gapped real subspace that adds `1` below `-1` and
fixes the nonnegative part. -/
def gapOrderMap (x : gapDomain) : ℝ :=
  if (x : ℝ) < -1 then (x : ℝ) + 1 else x

/-- Exercise 24.7 (7): The piecewise map from `(-∞, -1) ∪ [0, ∞)` to `ℝ` is
strictly order-preserving. -/
theorem gapOrderMap_strictMono : StrictMono gapOrderMap := by
  -- Separate the two components of the gapped domain and normalize each branch.
  intro x y hxy
  have hxyReal : (x : ℝ) < (y : ℝ) := hxy
  have hx : (x : ℝ) < -1 ∨ 0 ≤ (x : ℝ) := by
    simpa only [gapDomain, mem_union, mem_Iio, mem_Ici] using x.property
  have hy : (y : ℝ) < -1 ∨ 0 ≤ (y : ℝ) := by
    simpa only [gapDomain, mem_union, mem_Iio, mem_Ici] using y.property
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · simp only [gapOrderMap, if_pos hx, if_pos hy]
      linarith
    · have hyBranch : ¬ (y : ℝ) < -1 := by
        linarith
      simp only [gapOrderMap, if_pos hx, if_neg hyBranch]
      linarith
  · rcases hy with hy | hy
    · exfalso
      linarith [hxyReal]
    · have hxBranch : ¬ (x : ℝ) < -1 := by
        linarith
      have hyBranch : ¬ (y : ℝ) < -1 := by
        linarith
      simp only [gapOrderMap, if_neg hxBranch, if_neg hyBranch]
      exact hxyReal

/-- Exercise 24.7 (8): The piecewise map from `(-∞, -1) ∪ [0, ∞)` maps onto `ℝ`. -/
theorem gapOrderMap_surjective : Function.Surjective gapOrderMap := by
  -- Choose the inverse branch according to the sign of the target point.
  intro y
  by_cases hy : y < 0
  · have hnegative : y - 1 < -1 := by
      linarith
    have hmem : y - 1 ∈ gapDomain := by
      simp only [gapDomain, mem_union, mem_Iio, mem_Ici]
      exact Or.inl hnegative
    let x : gapDomain := ⟨y - 1, hmem⟩
    refine ⟨x, ?_⟩
    simp only [gapOrderMap, x, if_pos hnegative]
    ring
  · have hnonnegative : 0 ≤ y := le_of_not_gt hy
    have hmem : y ∈ gapDomain := by
      simp only [gapDomain, mem_union, mem_Iio, mem_Ici]
      exact Or.inr hnonnegative
    let x : gapDomain := ⟨y, hmem⟩
    have hbranch : ¬ (x : ℝ) < -1 := by
      dsimp only [x]
      linarith
    refine ⟨x, ?_⟩
    simp only [gapOrderMap, if_neg hbranch, x]

/-- Helper for Exercise 24.7: The nonnegative component of `gapDomain` is open in the
inherited topology. -/
lemma gapDomain_nonnegative_isOpen : IsOpen {x : gapDomain | 0 ≤ (x : ℝ)} := by
  -- Express the right component as an open-ray preimage in the subtype.
  have hset : {x : gapDomain | 0 ≤ (x : ℝ)} =
      (fun x : gapDomain ↦ (x : ℝ)) ⁻¹' Ioi (-1) := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, mem_Ioi]
    constructor
    · intro hx
      linarith
    · intro hx
      have hxDomain : (x : ℝ) < -1 ∨ 0 ≤ (x : ℝ) := by
        simpa only [gapDomain, mem_union, mem_Iio, mem_Ici] using x.property
      rcases hxDomain with hxDomain | hxDomain
      · linarith
      · exact hxDomain
  rw [hset]
  exact isOpen_Ioi.preimage continuous_subtype_val

/-- Helper for Exercise 24.7: The image of the nonnegative component under `gapOrderMap`
is the nonnegative ray. -/
lemma gapOrderMap_image_nonnegative :
    gapOrderMap '' {x : gapDomain | 0 ≤ (x : ℝ)} = Ici 0 := by
  -- On the right component the map is the identity, giving both inclusions directly.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxNonnegative : 0 ≤ (x : ℝ) := hx
    have hbranch : ¬ (x : ℝ) < -1 := by
      linarith
    simpa only [gapOrderMap, if_neg hbranch, mem_Ici] using hxNonnegative
  · intro hy
    have hmem : y ∈ gapDomain := by
      simp only [gapDomain, mem_union, mem_Iio, mem_Ici]
      exact Or.inr hy
    let x : gapDomain := ⟨y, hmem⟩
    have hx : 0 ≤ (x : ℝ) := by
      exact hy
    have hbranch : ¬ (x : ℝ) < -1 := by
      linarith
    refine ⟨x, hx, ?_⟩
    simp only [gapOrderMap, if_neg hbranch, x]

/-- Exercise 24.7 (9): With the inherited subspace topology, the piecewise map from
`(-∞, -1) ∪ [0, ∞)` to `ℝ` is not a homeomorphism. -/
theorem gapOrderMap_not_isHomeomorph : ¬ IsHomeomorph gapOrderMap := by
  -- An open map would send the open right component to the non-open ray `Ici 0`.
  intro hhomeomorph
  have hopen : IsOpen (Ici (0 : ℝ)) := by
    rw [← gapOrderMap_image_nonnegative]
    exact hhomeomorph.isOpenMap _ gapDomain_nonnegative_isOpen
  have hinterior : interior (Ici (0 : ℝ)) = Ici 0 := hopen.interior_eq
  rw [interior_Ici] at hinterior
  have hzero : (0 : ℝ) ∈ Ioi 0 := by
    rw [hinterior]
    exact self_mem_Ici
  have : (0 : ℝ) < 0 := by
    simpa only [mem_Ioi] using hzero
  exact (lt_irrefl 0) this

/-- Exercise 24.7 (10): The inherited topology on `(-∞, -1) ∪ [0, ∞)` is not its
order topology, explaining why the conclusion of part (a) does not apply. -/
theorem gapDomain_not_orderTopology : ¬ OrderTopology gapDomain := by
  -- Under an order topology, the earlier strict-monotone-surjection theorem gives a contradiction.
  intro horder
  letI : OrderTopology gapDomain := horder
  exact gapOrderMap_not_isHomeomorph
    (strictMonoSurjective_isHomeomorph gapOrderMap gapOrderMap_strictMono
      gapOrderMap_surjective)
