module

public import Topology_Munkres_2000.Book.Example_2_1.SquareMaps

public section

/-- Example 2.3 (1). The square map `ℝ → ℝ` is not injective. -/
theorem realSquare_notInjective :
    ¬ Function.Injective realSquare := by
  -- The opposite inputs `1` and `-1` have the same square.
  intro hinjective
  have hequal : realSquare (1 : ℝ) = realSquare (-1 : ℝ) := by
    norm_num [realSquare]
  have hopen := hinjective hequal
  norm_num at hopen

/-- Companion to Example 2.3: the square map `ℝ → ℝ` is not surjective. -/
theorem realSquare_notSurjective :
    ¬ Function.Surjective realSquare := by
  -- A hypothetical preimage of `-1` contradicts nonnegativity of squares.
  intro hsurjective
  obtain ⟨x, hx⟩ := hsurjective (-1 : ℝ)
  have hsquare : x ^ 2 = -1 := by
    simpa [realSquare] using hx
  linarith [sq_nonneg x]

/-- Companion to Example 2.3: restricting the square map to `NNReal` makes it injective. -/
theorem nnrealSquareToReal_injective :
    Function.Injective nnrealSquareToReal := by
  -- Equality of squares determines equal nonnegative real inputs.
  intro x y hxy
  have hsquares : (x : ℝ) ^ 2 = (y : ℝ) ^ 2 := by
    simpa only [nnrealSquareToReal_apply] using hxy
  apply NNReal.eq
  nlinarith [x.coe_nonneg, y.coe_nonneg]

/-- Companion to Example 2.3: the square map `NNReal → ℝ` is not surjective. -/
theorem nnrealSquareToReal_notSurjective :
    ¬ Function.Surjective nnrealSquareToReal := by
  -- The restricted domain still cannot produce the negative value `-1`.
  intro hsurjective
  obtain ⟨x, hx⟩ := hsurjective (-1 : ℝ)
  have hsquare : (x : ℝ) ^ 2 = -1 := by
    simpa only [nnrealSquareToReal_apply] using hx
  linarith [sq_nonneg (x : ℝ)]

/-- Companion to Example 2.3: the square map `ℝ → NNReal` is surjective. -/
theorem realSquareToNNReal_surjective :
    Function.Surjective realSquareToNNReal := by
  -- The nonnegative square root, viewed as a real number, is a preimage.
  intro y
  refine ⟨(NNReal.sqrt y : ℝ), ?_⟩
  apply NNReal.eq
  rw [realSquareToNNReal_coe, realSquare]
  -- Coercion preserves the square-root inverse identity.
  exact_mod_cast NNReal.sq_sqrt y

/-- Companion to Example 2.3: the square map `ℝ → NNReal` is not injective. -/
theorem realSquareToNNReal_notInjective :
    ¬ Function.Injective realSquareToNNReal := by
  -- Changing only the codomain preserves the collision at `1` and `-1`.
  intro hinjective
  have hequal : realSquareToNNReal (1 : ℝ) = realSquareToNNReal (-1 : ℝ) := by
    apply NNReal.eq
    simp only [realSquareToNNReal_coe, realSquare]
    norm_num
  have hopen := hinjective hequal
  norm_num at hopen

/- Example 2.3 (7). The square map `NNReal → NNReal` is the inverse order
isomorphism of `NNReal.sqrt`, and hence is bijective. -/
#check NNReal.sqrt.symm.bijective

/- Example 2.3 (8). The inverse identities for the square map and
`NNReal.sqrt`. -/
#check NNReal.sqrt_sq
#check NNReal.sq_sqrt
