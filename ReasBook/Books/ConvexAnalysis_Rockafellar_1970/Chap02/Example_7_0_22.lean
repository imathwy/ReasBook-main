import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_7_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar
open Function

variable {𝕜 : Type*} {Y Z : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 7.0.22 fixes a finite convex function `f` on a product space
  `Y × Z`, defines the first-coordinate infimum
  `g(y) = inf_{z ∈ Z} f(y, z)`, and records the convexity and
  finiteness properties of `g` together with the consequence for lower bounds on first-coordinate
  fibers.
- `core/canonical`: the owner abstraction for taking infima along fibers is the intrinsic
  `Function.partialInfimum` from Text 5.7.2, together with the owner convexity predicate
  `Function.IsConvex` on `WithTopBot 𝕜`-valued functions.
- `bridge/view`: the textbook coordinate formula
  `g(ξ₁) = inf_{ξ₂} f(ξ₁, ξ₂)` is exactly `partialInfimum`.
  The equivalent linear-image view is given by specialization at the intrinsic product projection
  `LinearMap.fst 𝕜 Y Z : Y × Z →ₗ[𝕜] Y`.
  Rockafellar's statement that `g` is finite everywhere is rendered by the owner equality
  `dom(partialInfimum f.toWithTopBot) = Set.univ`, and "bounded below on a line
  parallel to the `ξ₂`-axis" is rendered by `BddBelow` of the corresponding fiber value set.
- Primitive data vs derived API: the primitive input is the finite-valued function `f`; the
  first-coordinate infimum is expressed directly by the intrinsic owner
  `Function.partialInfimum`, and the convexity/finiteness statements are companion API.
- Layer target: `source-facing` for the textbook consequences below, implemented directly through
  the intrinsic owner surface rather than through a duplicate local alias.

Domain-style sampling used here:
- `Function.partialInfimum_apply` from Text 5.7.2 as the
  intrinsic first-coordinate infimum owner formula;
- `Function.IsConvex.partialInfimum` from Text 5.7.2 as the owner convexity theorem;
- `Function.IsConvex.all_gt_bot_or_all_infinite` from
  Corollary 7.2.3
  as the owner dichotomy used in part (3).
-/

-- Proof sketch: apply Text 5.7.2 owner theorem `Function.IsConvex.partialInfimum`
-- to the canonical codomain lift `toWithTopBot f`.
/-- Example 7.0.22 (1): for a finite convex function `f` on `Y × Z`, the first-coordinate
infimum `g(y) = inf_{z ∈ Z} f(y, z)` is convex, in the canonical owner form
`(partialInfimum f.toWithTopBot).IsConvex 𝕜`. -/
theorem verticalLineInfimum_isConvex
    [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [DenselyOrdered 𝕜]
    [AddCommMonoid Y] [Module 𝕜 Y] [AddCommMonoid Z] [Module 𝕜 Z]
    (f : Y × Z → 𝕜) (hf : ConvexOn 𝕜 (Set.univ : Set (Y × Z)) f) :
    (partialInfimum f.toWithTopBot).IsConvex 𝕜 := by
  simpa using
    Function.IsConvex.partialInfimum (h := f.toWithTopBot)
      (Function.isConvex_coe_of_convexOn_univ hf)

-- Proof sketch: choose a witness `z₀ : Z` and evaluate the defining infimum at `z₀`. This gives
-- `partialInfimum f.toWithTopBot y ≤ f (y, z₀) < ⊤`, hence every `y` lies in
-- `dom(partialInfimum f.toWithTopBot)`.
/-- Example 7.0.22 (2): the first-coordinate infimum has effective domain all of `Y`, in canonical
owner form `dom(g) = Set.univ`. -/
theorem dom_verticalLineInfimum_eq_univ
    {α : Type*} [ConditionallyCompleteLattice α] [Nonempty Z]
    (f : Y × Z → α) :
    dom(partialInfimum f.toWithTopBot) = Set.univ := by
  rcases ‹Nonempty Z› with ⟨z₀⟩
  ext y
  simp only [mem_effectiveDomain, Set.mem_univ, iff_true]
  have hsInf_le : partialInfimum f.toWithTopBot y ≤ f (y, z₀) := by
    rw [partialInfimum_apply]
    exact sInf_le ⟨z₀, rfl⟩
  exact lt_of_le_of_lt hsInf_le (WithTop.coe_lt_top (f (y, z₀) : WithBot α))

-- Proof sketch: apply Corollary 7.2.3 to the convex `WithTopBot 𝕜`-valued function
-- `partialInfimum f.toWithTopBot`. Part (2) identifies its effective domain with all of
-- `Y`, so the alternative "all values are infinite" reduces to `g y = -∞` for every `y`.
/-- Example 7.0.22 (3): the first-coordinate infimum of a finite convex function on `Y × Z` is
either finite everywhere in owner form `⊥ < g(y) < ⊤`, or equal to `-∞` everywhere on `Y`. -/
theorem verticalLineInfimum_all_finite_or_all_eq_bot
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (f : Y × Z → 𝕜) (hf : ConvexOn 𝕜 (Set.univ : Set (Y × Z)) f) :
    (∀ y : Y, ⊥ < partialInfimum f.toWithTopBot y ∧ partialInfimum f.toWithTopBot y < ⊤) ∨
      (∀ y : Y, partialInfimum f.toWithTopBot y = ⊥) := by
  have hlt_top (y : Y) : partialInfimum f.toWithTopBot y < ⊤ := by
    have hy : y ∈ dom(partialInfimum f.toWithTopBot) := by
      simp [dom_verticalLineInfimum_eq_univ f]
    simpa [mem_effectiveDomain] using hy
  have hdom_open : IsRelativelyOpen 𝕜 dom(partialInfimum f.toWithTopBot) := by
    simpa [dom_verticalLineInfimum_eq_univ f] using
      (IsOpen.isRelativelyOpen isOpen_univ : IsRelativelyOpen 𝕜 (Set.univ : Set Y))
  rcases
      Function.IsConvex.all_gt_bot_or_all_infinite
        (verticalLineInfimum_isConvex f hf)
        hdom_open with
    hfinite | hinf
  · left
    intro y
    exact ⟨hfinite y, hlt_top y⟩
  · right
    intro y
    rcases hinf y with hbot | htop
    · exact hbot
    · exfalso
      have hlt : (⊤ : WithTopBot 𝕜) < ⊤ := by
        have hlt' := hlt_top y
        rwa [htop] at hlt'
      exact (lt_irrefl (⊤ : WithTopBot 𝕜)) hlt

-- Proof sketch: if one first-coordinate fiber value set is `BddBelow`, then the infimum on that
-- fiber is not `-∞`. By part (3), the first-coordinate infimum therefore cannot be identically
-- `-∞`, so it is
-- finite everywhere. Translating finiteness of the infimum back to the fibers yields `BddBelow`
-- for every first-coordinate fiber value set.
/-- Example 7.0.22 (4): if a finite convex function on `Y × Z` is bounded below on one
first-coordinate fiber, then the value set on every such fiber is `BddBelow`. -/
theorem bddBelow_range_verticalLine_of_bddBelow_range_one_verticalLine
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [AddCommMonoid Z] [Module 𝕜 Z]
    (f : Y × Z → 𝕜) (hf : ConvexOn 𝕜 (Set.univ : Set (Y × Z)) f) {y₀ : Y}
    (hline : BddBelow (Set.range fun z : Z ↦ f (y₀, z))) (y : Y) :
    BddBelow (Set.range fun z : Z ↦ f (y, z)) := by
  rcases verticalLineInfimum_all_finite_or_all_eq_bot f hf with hfinite | hall_bot
  · rcases hfinite y with ⟨hgt, hlt⟩
    have hne_top : partialInfimum f.toWithTopBot y ≠ ⊤ := hlt.ne
    have hne_bot : partialInfimum f.toWithTopBot y ≠ ⊥ := ne_of_gt hgt
    induction hr' : partialInfimum f.toWithTopBot y using WithTop.recTopCoe with
    | top => exact (hne_top hr').elim
    | coe q =>
        induction q using WithBot.recBotCoe with
        | bot => exact (hne_bot hr').elim
        | coe r =>
            refine ⟨r, ?_⟩
            rintro _ ⟨z, rfl⟩
            have hsInf_le : partialInfimum f.toWithTopBot y ≤ (f (y, z) : WithTopBot 𝕜) := by
              calc
                partialInfimum f.toWithTopBot y
                    = sInf (Set.range fun z : Z ↦ (f (y, z) : WithTopBot 𝕜)) := by
                      rw [partialInfimum_apply]
                _ ≤ (f (y, z) : WithTopBot 𝕜) := sInf_le ⟨z, rfl⟩
            exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp <| by
              calc
                (r : WithTopBot 𝕜) = partialInfimum f.toWithTopBot y := by
                  simpa using hr'.symm
                _ ≤ (f (y, z) : WithTopBot 𝕜) := hsInf_le)
  · rcases hline with ⟨a, ha⟩
    have hsInf_ge : (a : WithTopBot 𝕜) ≤ partialInfimum f.toWithTopBot y₀ := by
      rw [partialInfimum_apply]
      refine le_sInf ?_
      rintro _ ⟨z, rfl⟩
      exact show (a : WithTopBot 𝕜) ≤ (f (y₀, z) : WithTopBot 𝕜) by
        exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr (ha ⟨z, rfl⟩))
    exfalso
    have hge : (a : WithTopBot 𝕜) ≤ ⊥ := by
      rw [hall_bot y₀] at hsInf_ge
      exact hsInf_ge
    have hbot_lt : (⊥ : WithTopBot 𝕜) < a :=
      WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)
    exact (not_le_of_gt hbot_lt) hge

end
