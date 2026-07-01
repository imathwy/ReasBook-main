import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function

/-- Canonical owner for the convex minorants of `g`. -/
def convexMinorants (g : E → WithBotTop 𝕜) : Set (E → WithBotTop 𝕜) :=
  {h | h.IsConvex 𝕜 ∧ h ≤ g}

end Function
end

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.3 states that `f = conv(g)` is the greatest convex minorant of `g`,
  equivalently the greatest convex function majorized by `g`.
- `core/canonical`: the owner abstractions already present in this section are
  `conv(g)` from Text 5.5.1 and
  `Function.IsConvex : (E → WithBotTop 𝕜) → Prop` from Theorem 4.2.
- `bridge/view`: the order-theoretic phrase "greatest convex minorant of `g`" is most naturally
  expressed by `IsGreatest (Function.convexMinorants g) (conv(g))`.
- Primitive data vs derived API: the primitive input is `g`; convexity of `conv(g)` comes from
  Text 5.5.2, and maximality among convex minorants is the derived API here.
- Ambient minimization: the owner construction and convexity theorem already live on an arbitrary
  additive commutative `𝕜`-module `E`, so specializing back to `EuclideanSpace ℝ (Fin n)` would
  only reintroduce a concrete model layer with no mathematical role in this item.

Domain-style sampling used here:
- `conv`;
- `Function.IsConvex`;
- `Function.IsConvex.convex_epigraph`;
- `IsGreatest`.
- Layer target: `source-facing`; this file keeps the new greatest-minorant statement and reuses
  the earlier chapter owner declarations directly instead of redefining them locally.
-/

namespace Function

/-- Every convex minorant of `g` lies below `conv(g)`. -/
theorem le_conv_of_le
    {g h : E → WithBotTop 𝕜} (hh_convex : h.IsConvex 𝕜) (hh_le : h ≤ g) :
    h ≤ conv(g) := by
  have hsubset : epi g ⊆ epi h := by
    rintro ⟨x, μ⟩ hx
    rcases mem_epi_restrict_iff.mp hx with ⟨-, hxμ⟩
    exact mem_epi_restrict_iff.mpr ⟨by simp, (hh_le x).trans hxμ⟩
  have hh_epi : Convex 𝕜 (epi h) := by
    simpa [epi_univ_eq_setOf_le] using hh_convex.convex_epigraph
  rw [convexHull]
  exact le_verticalInfimum_of_subset_epi <|
    convexHull_min hsubset hh_epi

end Function

end

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

section NoBotOrder

variable [NoBotOrder 𝕜]

/-- `conv(g)` is a pointwise minorant of `g`. -/
theorem conv_le
    (g : E → WithBotTop 𝕜) :
    conv(g) ≤ g := by
  rw [convexHull]
  exact verticalInfimum_le_of_epi_subset (subset_convexHull 𝕜 (epi g))

/-- Order-theoretic maximality principle: if `conv(g)` is convex, then it is the greatest convex
minorant of `g`. -/
theorem isGreatest_conv_minorant_of_isConvex
    (g : E → WithBotTop 𝕜) (hconv : (conv(g)).IsConvex 𝕜) :
    IsGreatest (convexMinorants g) (conv(g)) := by
  refine ⟨⟨hconv, conv_le g⟩, ?_⟩
  intro h hh
  exact le_conv_of_le hh.1 hh.2

end NoBotOrder

end Function

end

section

variable {E : Type u} {𝕜 : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

-- Proof sketch: apply the primitive maximality theorem
-- `isGreatest_conv_minorant_of_isConvex` using the convexity bridge
-- `isConvex_conv g` from Text 5.5.2.
/-- Text 5.5.3: `conv(g)` is the greatest convex minorant of `g`, equivalently the
greatest convex function majorized by `g`. -/
theorem isGreatest_conv_minorant
    (g : E → WithBotTop 𝕜) :
    IsGreatest (convexMinorants g) (conv(g)) :=
  isGreatest_conv_minorant_of_isConvex g (isConvex_conv g)

end Function

end
