

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_22 (from Items/Chap07) -/
open MeasureTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/- Corollary 7.22: the real `L²(μ)` space with its canonical inner product is a Hilbert space,
expressed directly by the canonical owner type `HilbertSpace ℝ (Lp ℝ 2 μ)` built from
`L2.innerProductSpace` and `MeasureTheory.Lp.instCompleteSpace`. -/
#check (HilbertSpace ℝ (Lp ℝ 2 μ))

end
