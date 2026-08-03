import BauschkeLean.Chap03.Theorem_3_16_2
import BauschkeLean.Chap12.Corollary_12_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

noncomputable section

universe u v

-- Source/core/bridge triage:
-- - `source-facing`: the Cartesian product `directSumSet C` and Proposition 29.3's
--   coordinatewise projector on `lp K 2`
-- - `core/canonical`: the product predicate `Set.pi Set.univ C`
-- - `bridge/view`: Theorem 3.16.2's variational characterization of metric projections

section DirectSumSet

variable {I : Type v}
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]

/-- The Cartesian product `∏ᵢ Cᵢ` viewed as a subset of the finite Hilbert direct sum `lp K 2`. -/
def directSumSet (C : ∀ i, Set (K i)) : Set (lp K 2) :=
  {x | ∀ i, x i ∈ C i}

/-- Membership in `directSumSet C` is exactly coordinatewise membership in the family `C`. -/
@[simp] theorem mem_directSumSet_iff
    (C : ∀ i, Set (K i)) (x : lp K 2) :
    x ∈ directSumSet C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

/-- `directSumSet C` is the pullback of the canonical product set `Set.pi Set.univ C` along the
coercion `lp K 2 → ∀ i, K i`. -/
theorem directSumSet_eq_preimage_pi
    (C : ∀ i, Set (K i)) :
    directSumSet C =
      (fun x : lp K 2 ↦ (x : ∀ i, K i)) ⁻¹' Set.pi Set.univ C := by
  ext x
  simp [directSumSet, Set.pi]

/-- The Cartesian product `∏ᵢ Cᵢ` is nonempty when each factor `Cᵢ` is nonempty. -/
theorem directSumSet_nonempty
    [Finite I]
    (C : ∀ i, Set (K i))
    (hC_nonempty : ∀ i, (C i).Nonempty) :
    (directSumSet C).Nonempty := by
  classical
  choose x hx using hC_nonempty
  exact ⟨⟨x, Memℓp.all x⟩, hx⟩

/-- The Cartesian product `∏ᵢ Cᵢ` is closed in `lp K 2` when each factor `Cᵢ` is closed. -/
theorem directSumSet_isClosed
    (C : ∀ i, Set (K i))
    (hC_closed : ∀ i, IsClosed (C i)) :
    IsClosed (directSumSet C) := by
  have hclosed :
      IsClosed (⋂ i : I, {x : lp K 2 | x i ∈ C i}) := by
    refine isClosed_iInter fun i ↦ ?_
    have hcont : Continuous fun x : lp K 2 ↦ x i := by
      exact (continuous_apply i).comp lp.uniformContinuous_coe.continuous
    simpa using (hC_closed i).preimage hcont
  convert hclosed using 1
  ext x
  simp [directSumSet]

section Convex

variable [∀ i, InnerProductSpace ℝ (K i)]

/-- The Cartesian product `∏ᵢ Cᵢ` is convex in `lp K 2` when each factor `Cᵢ` is convex. -/
theorem directSumSet_convex
    (C : ∀ i, Set (K i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    Convex ℝ (directSumSet C) := by
  intro x hx y hy a b ha hb hab i
  simpa using hC_convex i (hx i) (hy i) ha hb hab

end Convex

end DirectSumSet

section IndicatorFamily

variable {I : Type v}
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]
variable [∀ i, InnerProductSpace ℝ (K i)]

/-- The coordinate indicators of a nonempty closed convex family `Cᵢ` belong to `Γ₀(K i)`. -/
theorem indicatorFamily_mem_gammaZero
    (C : ∀ i, Set (K i))
    (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    ∀ i, ι[C i] ∈ Γ₀(K i) :=
  fun i ↦ indicator_mem_gammaZero_of_nonempty_isClosed_convex
    (hC_nonempty i) (hC_closed i) (hC_convex i)

end IndicatorFamily

section DirectSumSetChebyshev

variable {I : Type v} [Finite I]
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]
variable [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The Cartesian product `directSumSet C` of a finite family of nonempty closed convex sets is
Chebyshev. -/
theorem directSumSet_isChebyshev
    (C : ∀ i, Set (K i))
    (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    IsChebyshev (directSumSet C) := by
  exact isChebyshev_of_nonempty_isClosed_convex
    (directSumSet_nonempty C hC_nonempty)
    (directSumSet_isClosed C hC_closed)
    (directSumSet_convex C hC_convex)

end DirectSumSetChebyshev

section Proposition293

variable {I : Type v} [Fintype I]
variable {K : I → Type u}
variable [∀ i, NormedAddCommGroup (K i)]
variable [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The coordinatewise metric projection onto a finite family of nonempty closed convex sets,
realized by projecting each coordinate separately. -/
abbrev coordinatewiseProjectionPoint
    (C : ∀ i, Set (K i))
    (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) :
    lp K 2 → lp K 2 :=
  fun x ↦ ⟨
    fun i ↦
      P[C i, isChebyshev_of_nonempty_isClosed_convex
        (hC_nonempty i) (hC_closed i) (hC_convex i)] (x i),
    Memℓp.all _
  ⟩

/-- Evaluating `coordinatewiseProjectionPoint C` at `i` returns the projection onto `Cᵢ`. -/
@[simp] theorem coordinatewiseProjectionPoint_apply
    (C : ∀ i, Set (K i))
    (hC_nonempty : ∀ i, (C i).Nonempty)
    (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i))
    (x : lp K 2) (i : I) :
    coordinatewiseProjectionPoint C hC_nonempty hC_closed hC_convex x i =
      P[C i, isChebyshev_of_nonempty_isClosed_convex
        (hC_nonempty i) (hC_closed i) (hC_convex i)] (x i) := by
  rfl

variable (C : ∀ i, Set (K i))
variable (hC_nonempty : ∀ i, (C i).Nonempty)
variable (hC_closed : ∀ i, IsClosed (C i))
variable (hC_convex : ∀ i, Convex ℝ (C i))

/-- Proposition 29.3: let `(K i)ᵢ` be a finite family of real Hilbert spaces, let `C i` be a
nonempty closed convex subset of `K i` for each `i`, and let `x : lp K 2`. Then the metric
projection onto the Cartesian product `∏ᵢ Cᵢ` acts coordinatewise:
`P[directSumSet C, directSumSet_isChebyshev C hC_nonempty hC_closed hC_convex] x =
  (P[Cᵢ] (xᵢ))ᵢ`. -/
theorem projectionPoint_directSumSet_eq_coordinatewiseProjectionPoint
    (x : lp K 2) :
    P[directSumSet C, directSumSet_isChebyshev C hC_nonempty hC_closed hC_convex] x =
      coordinatewiseProjectionPoint C hC_nonempty hC_closed hC_convex x := by
  let p := coordinatewiseProjectionPoint C hC_nonempty hC_closed hC_convex x
  have hp :
      p =
        P[directSumSet C, directSumSet_isChebyshev C hC_nonempty hC_closed hC_convex] x := by
    -- Verify the coordinatewise projector by the product-set variational inequality.
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (directSumSet_nonempty C hC_nonempty)
        (directSumSet_isClosed C hC_closed)
        (directSumSet_convex C hC_convex)).2 ?_
    constructor
    · intro i
      change
        P[C i, isChebyshev_of_nonempty_isClosed_convex
          (hC_nonempty i) (hC_closed i) (hC_convex i)] (x i) ∈ C i
      exact
        projectionPoint_mem
          (C i)
          (isChebyshev_of_nonempty_isClosed_convex
            (hC_nonempty i) (hC_closed i) (hC_convex i))
          (x i)
    · intro y hy
      have hyi : ∀ i, y i ∈ C i := by
        simpa [directSumSet] using hy
      have hcoord :
          ∀ i, ⟪y i - p i, x i - p i⟫_ℝ ≤ 0 := by
        intro i
        have hproj :=
          (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
            (hC_nonempty i) (hC_closed i) (hC_convex i)
            (x := x i)
            (p := p i)).mp <| by
              change
                P[C i, isChebyshev_of_nonempty_isClosed_convex
                  (hC_nonempty i) (hC_closed i) (hC_convex i)] (x i) =
                  P[C i, isChebyshev_of_nonempty_isClosed_convex
                    (hC_nonempty i) (hC_closed i) (hC_convex i)] (x i)
              rfl
        exact hproj.2 (y i) (hyi i)
      have hsum :
          ∑ i, ⟪y i - p i, x i - p i⟫_ℝ ≤ 0 := by
        exact Finset.sum_nonpos fun i _ ↦ hcoord i
      have hinner :
          ∑ i, ⟪y i - p i, x i - p i⟫_ℝ = ⟪y - p, x - p⟫_ℝ := by
        calc
          ∑ i, ⟪y i - p i, x i - p i⟫_ℝ
              = ∑ i, ⟪(lpPiLpₗᵢ K ℝ (y - p)) i, (lpPiLpₗᵢ K ℝ (x - p)) i⟫_ℝ := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simp [coe_lpPiLpₗᵢ]
          _ = ⟪lpPiLpₗᵢ K ℝ (y - p), lpPiLpₗᵢ K ℝ (x - p)⟫_ℝ := by
                rw [PiLp.inner_apply]
          _ = ⟪y - p, x - p⟫_ℝ := by
                simpa using (lpPiLpₗᵢ K ℝ).inner_map_map (y - p) (x - p)
      simpa [hinner] using hsum
  calc
    P[directSumSet C, directSumSet_isChebyshev C hC_nonempty hC_closed hC_convex] x = p :=
      hp.symm
    _ = coordinatewiseProjectionPoint C hC_nonempty hC_closed hC_convex x := rfl

end Proposition293

end
