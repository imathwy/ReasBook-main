import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type u} {E : Type v} {F : Type w}

namespace Function

/-- Finite-height epigraph for an ordered codomain. -/
def positiveHomogeneityEpigraph [Preorder F] (f : E → F) : Set (E × F) :=
  {p : E × F | f p.1 ≤ p.2}

/-- The epigraph is a positive cone when it is closed under multiplication by positive scalars. -/
def IsPositiveCone [LT 𝕜] [Zero 𝕜] [SMul 𝕜 (E × F)] (S : Set (E × F)) : Prop :=
  ∀ c : 𝕜, 0 < c → ∀ p ∈ S, c • p ∈ S

/-- Remark 4.8.1, positive-homogeneity form: under the standard order-compatibility assumptions
for positive scalar multiplication on the codomain, positive homogeneity is equivalent to the
finite-height epigraph being a positive cone. -/
theorem positivelyHomogeneous_iff_epigraph_isPositiveCone
    [LT 𝕜] [Zero 𝕜] [SMul 𝕜 E] [SMul 𝕜 F] [SMul 𝕜 (E × F)] [Preorder F]
    (f : E → F)
    (hmono : ∀ {c : 𝕜}, 0 < c → ∀ {a b : F}, a ≤ b → c • a ≤ c • b)
    (hcancel : ∀ {c : 𝕜}, 0 < c → ∀ {a b : F}, c • a ≤ c • b → a ≤ b) :
    f.PositivelyHomogeneous 𝕜 ↔
      IsPositiveCone (𝕜 := 𝕜) (positiveHomogeneityEpigraph f) := by
  sorry

end Function

end
