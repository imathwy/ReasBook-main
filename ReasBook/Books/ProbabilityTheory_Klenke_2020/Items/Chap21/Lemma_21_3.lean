import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped NNReal Topology

section RealLocalHolder

variable {I : Set ℝ} {f : I → ℝ} {γ γ' : Set.Ioc (0 : ℝ≥0) 1} {Cε : ℝ≥0} {ε T : ℝ}

-- Proof sketch: around each point, shrink a local `γ`-Hölder neighborhood to diameter at most
-- `1`, then use monotonicity of the power function on `[0,1]` to replace the exponent `γ` by the
-- smaller exponent `γ'`.
/-- Lemma 21.3 (1): if `f : I → ℝ` is locally Hölder-continuous of order `γ ∈ (0,1]`, then it is
also locally Hölder-continuous of every order `γ' ∈ (0, γ)`. -/
theorem locallyHolderWith_subexponent
    (hf : LocallyHolderWith γ f)
    (hγ'γ : (γ' : ℝ≥0) < γ) :
    LocallyHolderWith γ' f := sorry

-- Proof sketch: choose finitely many local Hölder neighborhoods from compactness, take a Lebesgue
-- number for this finite cover, and bound large distances by the sup norm on the compact domain.
/-- Lemma 21.3 (2): if `I` is compact and `f : I → ℝ` is locally Hölder-continuous of order
`γ ∈ (0,1]`, then `f` is globally Hölder-continuous on `I`. -/
theorem exists_holderWith_of_isCompact
    (hI : IsCompact I)
    (hf : LocallyHolderWith γ f) :
    ∃ C : ℝ≥0, HolderWith C γ f := sorry

-- Proof sketch: subdivide the segment between two points of the interval into
-- `⌈T / ε⌉` subsegments of length at most `ε`, apply the local small-scale Hölder estimate on
-- each subsegment, and sum the resulting bounds.
/-- Lemma 21.3 (3): for an interval `I` of length at most `T`, a small-scale Hölder estimate with
range `ε` upgrades to a global `γ`-Hölder estimate with constant
`Cε * ⌈T / ε⌉ ^ (1 - γ)`. -/
theorem holderWith_of_small_scale_on_interval
    (hI : Convex ℝ I)
    (hT : ∀ s t : I, dist s t ≤ T)
    (hε : 0 < ε)
    (hsmall :
      ∀ s t : I, dist s t ≤ ε → dist (f t) (f s) ≤ Cε * dist s t ^ (γ : ℝ)) :
    HolderWith (Cε * (Nat.ceil (T / ε) : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) γ f := sorry

end RealLocalHolder
