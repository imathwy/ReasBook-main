import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_16
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_19

noncomputable section

open scoped Rockafellar

universe u v

namespace Bifunction

section

variable {𝕜 : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {Y : Type (max u v)} [Neg Y] [Zero Y]
variable [HasPairing E Y 𝕜]
variable {f g : E → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.13 is the Kuhn-Tucker existence criterion in the Fenchel
  perturbation setup for the translated value function `p(u) = inf_x (f x - g (x + u))`.
- `core/canonical`: the owner abstractions already present upstream are
  `Bifunction.IsKuhnTuckerVector`,
  `Bifunction.isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality`,
  `Bifunction.fenchelPerturbation`, `Bifunction.perturbationFunction`,
  `_root_.subdifferentialAt`, and `Function.directionalDerivativeAt`.
- `bridge/view`: dual attainment of the adjoint zero-slice objective at `p 0` and membership in
  `∂[Y]p(0)` are companion characterizations of `IsKuhnTuckerVector F uStar`.

Layer target: `source-facing`, centered on the pairing-level owner
`IsKuhnTuckerVector F uStar`.
-/

variable (𝕜)
local notation "F" => fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g
local notation "p" => perturbationFunction F
local notation "F⋆" => (adjoint Y Y F)
local notation "dualObjective" => ((F⋆)₀ : Y → WithBotTop 𝕜)
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set Y)

variable {𝕜}

-- Proof sketch: specialize the chapter owner `IsKuhnTuckerVector F uStar` to the identity-map
-- Fenchel perturbation and use the dual-value equality `hdual` to identify it with attainment of
-- the dual zero-slice objective at `p 0`.
/-- Owner-level set bridge for Lemma 31.0.13: under the dual-value identification, membership in
`KT(F)` is equivalent to attainment of the dual zero-slice objective at `p 0`. -/
theorem mem_kuhnTuckerVectorSet_iff_dualObjective_eq_perturbationFunction_zero
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥)
    (uStar : Y) :
    uStar ∈ KT(F) ↔ dualObjective uStar = p 0 := by
  sorry

/-- Owner-level bridge for Lemma 31.0.13: under the dual-value identification, the canonical
Kuhn-Tucker owner `IsKuhnTuckerVector F uStar` is equivalent to attainment of the dual zero-slice
objective at the primal value `p 0`. -/
theorem isKuhnTuckerVector_iff_dualObjective_eq_perturbationFunction_zero
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥)
    (uStar : Y) :
    IsKuhnTuckerVector F uStar ↔ dualObjective uStar = p 0 := by
  simpa [mem_kuhnTuckerVectorSet] using
    (mem_kuhnTuckerVectorSet_iff_dualObjective_eq_perturbationFunction_zero
      (𝕜 := 𝕜) (f := f) (g := g) hp_convex hdual hp0_dom hp0_ne_bot uStar)

end

section

variable {𝕜 : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [Neg Y] [Zero Y]
variable [HasPairing E Y 𝕜]
variable {f g : E → WithBotTop 𝕜}

variable (𝕜)
local notation "F" => fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g
local notation "p" => perturbationFunction F
local notation "F⋆" => (adjoint Y Y F)
local notation "dualObjective" => ((F⋆)₀ : Y → WithBotTop 𝕜)
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set Y)

variable {𝕜}

-- Proof sketch: combine the owner-to-dual-attainment bridge with the Chapter 23 pairing-level
-- subgradient characterization at `0`.
/-- Set-owner companion bridge for Lemma 31.0.13: membership in `KT(F)` is equivalent to
subgradient membership in `∂[Y]p(0)`. -/
theorem mem_kuhnTuckerVectorSet_iff_mem_subdifferentialAt_perturbationFunction_zero
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥)
    (uStar : Y) :
    uStar ∈ KT(F) ↔ uStar ∈ (∂[Y]p(0)) := by
  sorry

/-- Companion bridge for Lemma 31.0.13: a Kuhn-Tucker vector, rendered canonically as
`IsKuhnTuckerVector F uStar`, is equivalently a dual-side subgradient of the perturbation
function at `0`. -/
theorem isKuhnTuckerVector_iff_mem_subdifferentialAt_perturbationFunction_zero
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥)
    (uStar : Y) :
    IsKuhnTuckerVector F uStar ↔ uStar ∈ (∂[Y]p(0)) := by
  simpa [mem_kuhnTuckerVectorSet] using
    (mem_kuhnTuckerVectorSet_iff_mem_subdifferentialAt_perturbationFunction_zero
      (𝕜 := 𝕜) (f := f) (g := g) hp_convex hdual hp0_dom hp0_ne_bot uStar)

-- Proof sketch: compose the two previous owner-level bridges.
/-- Companion dual-attainment/subdifferential bridge for Lemma 31.0.13: under the dual-value
identification, a dual-side element attains the perturbation value `p 0` exactly when it belongs
to `∂[Y]p(0)`. -/
theorem dualObjective_eq_perturbationFunction_zero_iff_mem_subdifferentialAt
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥)
    (uStar : Y) :
    dualObjective uStar = p 0 ↔ uStar ∈ (∂[Y]p(0)) := by
  constructor
  · intro huStar
    exact
      (isKuhnTuckerVector_iff_mem_subdifferentialAt_perturbationFunction_zero
        hp_convex hdual hp0_dom hp0_ne_bot uStar).mp
      ((isKuhnTuckerVector_iff_dualObjective_eq_perturbationFunction_zero
        hp_convex hdual hp0_dom hp0_ne_bot uStar).mpr huStar)
  · intro huStar
    exact
      (isKuhnTuckerVector_iff_dualObjective_eq_perturbationFunction_zero
        hp_convex hdual hp0_dom hp0_ne_bot uStar).mp
      ((isKuhnTuckerVector_iff_mem_subdifferentialAt_perturbationFunction_zero
        hp_convex hdual hp0_dom hp0_ne_bot uStar).mpr huStar)

-- Proof sketch: apply the pointwise owner-to-subdifferential bridge and transport the witness
-- across the resulting equivalence.
/-- Owner-level nonemptiness bridge for Lemma 31.0.13: the Kuhn-Tucker owner set `KT(F)` is
nonempty exactly when the pairing-level subdifferential owner `∂[Y]p(0)` is nonempty. -/
theorem kuhnTuckerVectorSet_nonempty_iff_subdifferentialAt_perturbationFunction_nonempty
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥) :
    (KT(F)).Nonempty ↔
      (∂[Y]p(0)).Nonempty := by
  constructor
  · rintro ⟨uStar, huStar⟩
    exact ⟨uStar,
      (mem_kuhnTuckerVectorSet_iff_mem_subdifferentialAt_perturbationFunction_zero
        hp_convex hdual hp0_dom hp0_ne_bot uStar).mp huStar⟩
  · rintro ⟨uStar, huStar⟩
    exact ⟨uStar,
      (mem_kuhnTuckerVectorSet_iff_mem_subdifferentialAt_perturbationFunction_zero
        hp_convex hdual hp0_dom hp0_ne_bot uStar).mpr huStar⟩

/-- Source-phrasing bridge for Lemma 31.0.13: existence of a Kuhn-Tucker vector for the identity
Fenchel perturbation is equivalent to nonemptiness of `∂[Y]p(0)`. -/
theorem exists_kuhnTuckerVector_iff_subdifferentialAt_perturbationFunction_nonempty
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥) :
    (∃ uStar : Y, IsKuhnTuckerVector F uStar) ↔
      (∂[Y]p(0)).Nonempty := by
  simpa [Set.nonempty_def, mem_kuhnTuckerVectorSet] using
    (kuhnTuckerVectorSet_nonempty_iff_subdifferentialAt_perturbationFunction_nonempty
      (𝕜 := 𝕜) (f := f) (g := g) hp_convex hdual hp0_dom hp0_ne_bot)

/-- Owner-level nonemptiness/directional-derivative bridge for Lemma 31.0.13: under the dual-value
identification, `KT(F)` is nonempty exactly when all directional derivatives `p'(0; y)` are
strictly above `-∞`. -/
theorem kuhnTuckerVectorSet_nonempty_iff_forall_bot_lt_directionalDerivativeAt_perturbationFunction
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥) :
    (KT(F)).Nonempty ↔
      ∀ y : E, ⊥ < Function.directionalDerivativeAt p 0 y := by
  sorry

/-- Lemma 31.0.13, pairing-owner form: if the translated value function
`p := perturbationFunction
  (fenchelPerturbation (LinearMap.id : E →ₗ[𝕜] E) f g)` is convex, the
dual-value identity `⨆ uStar, dualObjective uStar = p 0` holds, and `p 0` is finite-valued, then
a Kuhn-Tucker vector exists if and only if every directional derivative `p'(0; y)` is strictly
above `-∞`. -/
theorem exists_kuhnTuckerVector_iff_forall_bot_lt_directionalDerivativeAt_perturbationFunction
    (hp_convex : ConvexOn 𝕜 (Set.univ : Set E) p)
    (hdual : (⨆ uStar : Y, dualObjective uStar) = p 0)
    (hp0_dom : (0 : E) ∈ dom p)
    (hp0_ne_bot : p 0 ≠ ⊥) :
    (∃ uStar : Y, IsKuhnTuckerVector F uStar) ↔
      ∀ y : E, ⊥ < Function.directionalDerivativeAt p 0 y := by
  simpa [Set.nonempty_def, mem_kuhnTuckerVectorSet] using
    (kuhnTuckerVectorSet_nonempty_iff_forall_bot_lt_directionalDerivativeAt_perturbationFunction
      (𝕜 := 𝕜) (f := f) (g := g) hp_convex hdual hp0_dom hp0_ne_bot)

end

end Bifunction
