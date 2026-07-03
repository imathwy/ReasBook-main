import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_31_0_13 (from Chap06) -/
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

/-! ### Lemma_31_0_14 (from Chap06) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

namespace Bifunction

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.14 upgrades Lemma 31.0.13 from existence to uniqueness of a
  Kuhn-Tucker functional for the identity-map Fenchel perturbation problem, and in the Euclidean
  bridge specialization identifies the unique vector representative as the gradient of the
  perturbation value function at `0`.
- `core/canonical`: the owner abstractions already present upstream are
  `Bifunction.perturbationFunction`, `Bifunction.adjoint` together with the zero-slice
  objective owner `(·)₀`, `Bifunction.IsStrictlyConsistent`, `Function.realBranch`,
  `_root_.subdifferentialAt`,
  `DifferentiableAt`, and the Euclidean bridge owner `Function.subdifferentialAt` with gradient
  notation `∇`.
- `bridge/view`: the source phrase “`p` is finite and differentiable at `0`” is expressed
  canonically as strict consistency `IsStrictlyConsistent F` together with differentiability of
  the real branch `p.realBranch`. The primary uniqueness theorem is stated on the intrinsic dual
  owner, with a separate Euclidean bridge theorem for vector-valued statements.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `_root_.subdifferentialAt` and `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `Bifunction.isKuhnTuckerVector_iff_mem_subdifferentialAt_perturbationFunction_zero` from
  `Lemma_31_0_13`;
- `Bifunction.isKuhnTuckerVector_iff_dualObjective_eq_perturbationFunction_zero` from
  `Lemma_31_0_13`;
- `Bifunction.dualObjective_eq_perturbationFunction_zero_iff_mem_subdifferentialAt` from
  `Lemma_31_0_13`;
- `Function.realBranch` from `Chap02/Theorem_10_4`, used on the theorem surface as `p.realBranch`;
- the Chapter 25 singleton-subdifferential versus differentiability bridge for `p.realBranch`;
- the Chapter 23 directional-derivative/gradient bridge for the same real branch.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, the perturbation owner
  `perturbationFunction (fenchelPerturbation (LinearMap.id : E →ₗ[ℝ] E) f g)` and the
  owner-level hypotheses actually used downstream here: convexity `p.IsConvex ℝ`,
  pointwise finiteness `p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤`, and the dual-value identification
  from Lemma 31.0.13;
- derived API: uniqueness of the Kuhn-Tucker functional in `StrongDual ℝ E`, plus the Euclidean
  bridge uniqueness of a Kuhn-Tucker vector and the source-facing gradient formula. Dual
  attainment at value `p 0` remains a companion bridge from `Lemma_31_0_13`, not the main owner
  surface. The theorem surface carries pointwise finiteness at `0` directly as primitive data
  (`p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤`), while strict consistency continues to provide the
  canonical local interior-domain owner `IsStrictlyConsistent F`; the dual objective stays the
  existing Chapter 6 owner `(F⋆)₀` through the short local surface `dualObjective`.

Layer target: `source-facing`, but phrased directly on the canonical perturbation-function owner
and the existing Chapter 23/25 differentiability and subdifferential owners, with the intrinsic
dual layer primary and the inner-product vector layer as bridge.
-/

variable (f g : E → WithBotTop ℝ)

local notation "F" => fenchelPerturbation (LinearMap.id : E →ₗ[ℝ] E) f g
local notation "p" => perturbationFunction F
local notation "F⋆" => adjoint (StrongDual ℝ E) (StrongDual ℝ E) F
local notation "dualObjective" => ((F⋆)₀ : StrongDual ℝ E → WithBotTop ℝ)
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set (StrongDual ℝ E))

-- Proof sketch: translate uniqueness of the canonical Kuhn-Tucker owner into singletonhood of the
-- dual-valued subdifferential owner of `p` at `0`, using only the convex/pointwise-finiteness/
-- value data actually consumed from Lemma 31.0.13; then apply the Chapter 25
-- singleton-subdifferential
-- versus differentiability correspondence to the finite real branch `p.realBranch`.
/-- Lemma 31.0.14, intrinsic-dual owner form: under the convex perturbation hypothesis, finite
value at `0`, and the dual-value identity, there exists a unique Kuhn-Tucker functional
exactly when the
perturbation function is finite and differentiable at `0`. In the owner language, local finiteness
at `0` is represented by strict consistency `IsStrictlyConsistent F`, and pointwise finiteness at
`0` is carried directly by the primitive hypothesis `p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤` for the
canonical real branch
`p.realBranch`. -/
theorem existsUnique_kuhnTuckerFunctional_iff_differentiableAt_perturbationFunction_zero
    [FiniteDimensional ℝ E]
    (hp_convex : ConvexOn ℝ (Set.univ : Set E) p)
    (hp0_finite : p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hdual : (⨆ xStar : StrongDual ℝ E, dualObjective xStar) = p 0) :
    (∃! xStar : StrongDual ℝ E, xStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := by
  sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f g : E → WithBotTop ℝ)

local notation "F" => fenchelPerturbation (LinearMap.id : E →ₗ[ℝ] E) f g
local notation "p" => perturbationFunction F
local notation "F⋆" => adjoint E E F
local notation "dualObjective" => ((F⋆)₀ : E → WithBotTop ℝ)
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set E)

/-- Lemma 31.0.14, Euclidean bridge form: uniqueness of a Kuhn-Tucker vector is equivalent to
strict consistency and differentiability of the real branch of the perturbation function at `0`.
This specializes the intrinsic dual-owner statement to the inner-product model owner. -/
theorem existsUnique_kuhnTuckerVector_iff_differentiableAt_perturbationFunction_zero
    [FiniteDimensional ℝ E]
    (hp_convex : ConvexOn ℝ (Set.univ : Set E) p)
    (hp0_finite : p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hdual : (⨆ xStar : E, dualObjective xStar) = p 0) :
    (∃! xStar : E, xStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := by
  sorry

-- Proof sketch: once the previous theorem yields uniqueness together with differentiability of the
-- finite branch, the unique supporting vector is the gradient of `p.realBranch` at `0`; the only
-- owner data needed on `p` are convexity, pointwise finiteness at `0`, and the dual-value
-- identity.
/-- In the differentiable case of Lemma 31.0.14, the unique Kuhn-Tucker vector is the gradient of
the real branch of the perturbation function at `0`. -/
theorem gradient_is_kuhnTuckerVector_of_differentiableAt_perturbationFunction_zero
    [CompleteSpace E]
    (hp_convex : ConvexOn ℝ (Set.univ : Set E) p)
    (hp0_finite : p 0 ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤)
    (hdual : (⨆ xStar : E, dualObjective xStar) = p 0)
    (hstrict : IsStrictlyConsistent F)
    (hdiff : DifferentiableAt ℝ p.realBranch 0) :
    (∇ p.realBranch 0) ∈ KT(F) := by
  sorry

end

end Bifunction

/-! ### Lemma_31_0_15 (from Chap06) -/
noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {𝕜 : Type v} {E : Type u} {U : Type w} {Y : Type (max u v)}
variable [Ring 𝕜] [TopologicalSpace 𝕜] [Preorder 𝕜]
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.15 records the extremality condition in Theorem 31.2 for the primal
  Fenchel objective `x ↦ f x - g (A x)`.
- `core/canonical`: the chapter owners already present upstream are
  `(fenchelPerturbation A f g)₀`, `minimumSet`, and Proposition 6.27.6's minimizer
  criteria at three canonical layers:
  pairing (`∂[Y]h(x)`), canonical continuous dual (`∂ h at x`), and Euclidean bridge
  (`∂ᵥh(x)`).
- `bridge/view`: the source phrase “attains its minimum at `x`” is already
  `IsMinOn ((fenchelPerturbation A f g)₀) Set.univ x` by the owner `minimumSet`, so this file
  only records specializations of the existing minimizer criteria to the Chapter 31 primal
  objective.

Domain-style sampling used here:
- `Bifunction.fenchelPerturbation` and `Bifunction.objective_fenchelPerturbation_apply` from
  `Lemma_31_0_6`;
- `minimumSet` from `Definition_6_27_3`;
- `mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing`,
- `mem_minimumSet_iff_zero_mem_subdifferentialAt` and
  `mem_minimumSet_iff_zero_mem_subdifferentialAt_vector` from `Proposition_6_27_6`.

Primitive data vs derived API:
- primitive source data: the linear map `A`, the functions `f` and `g`, and the point `x`;
- primitive owner object: `(fenchelPerturbation A f g)₀` together with the canonical
  minimizer owner `minimumSet`;
- derived source-facing view: `IsMinOn _ Set.univ _`, obtained from `minimumSet` by definition.

Layer target: `source-facing` reusable specializations on the canonical owners already present
upstream.
-/

variable (A : E →ₗ[𝕜] U) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)
variable (x : E)
local notation "F0" => (fenchelPerturbation A f g)₀

/- Lemma 31.0.15, pairing-owner form: Proposition 6.27.6 specialized to the primal Fenchel
objective, at the canonical owner layer `minimumSet`. -/
/-- Lemma 31.0.15, pairing-owner form: the primal Fenchel objective `F0` has `x` in its
minimum set exactly when `0` belongs to its pairing-valued subdifferential at `x`. -/
theorem mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_pairing :
    x ∈ minimumSet F0 ↔ (0 : Y) ∈ (∂[Y]F0(x)) := by
  exact mem_minimumSet_iff_zero_mem_subdifferentialAt_pairing

/- Source wording bridge: “attains its minimum at `x`” is `IsMinOn _ Set.univ _`,
definitionally equivalent to minimum-set membership. -/
/-- Source-phrasing bridge for Lemma 31.0.15 at the pairing owner layer: saying that `F0`
attains its minimum at `x` is equivalent to zero-subgradient membership at `x`. -/
theorem isMinOn_objective_fenchelPerturbation_univ_iff_zero_mem_subdifferentialAt_pairing :
    IsMinOn F0 Set.univ x ↔ (0 : Y) ∈ (∂[Y]F0(x)) := by
  change x ∈ minimumSet F0 ↔ (0 : Y) ∈ (∂[Y]F0(x))
  exact mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_pairing
    (A := A) (f := f) (g := g) (x := x)

end

section

variable {𝕜 : Type v} {E : Type u} {U : Type w}
variable [NormedField 𝕜] [Preorder 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [AddCommMonoid U] [Module 𝕜 U]

variable (A : E →ₗ[𝕜] U) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)
variable (x : E)
local notation "F0" => (fenchelPerturbation A f g)₀

/- Lemma 31.0.15, canonical-dual form: the same minimizer criterion expressed with the canonical
continuous-dual owner `∂ ((fenchelPerturbation A f g)₀) at x`. -/
/-- Lemma 31.0.15, canonical-dual form: for the primal Fenchel objective `F0`, membership of `x`
in `minimumSet F0` is equivalent to zero membership in the canonical continuous-dual
subdifferential at `x`. -/
theorem mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt :
    x ∈ minimumSet F0 ↔ (0 : StrongDual 𝕜 E) ∈ (∂ F0 at x) := by
  exact mem_minimumSet_iff_zero_mem_subdifferentialAt

/- Source wording bridge for the canonical-dual specialization. -/
/-- Source-phrasing bridge for Lemma 31.0.15 at the canonical-dual owner layer. -/
theorem isMinOn_objective_fenchelPerturbation_univ_iff_zero_mem_subdifferentialAt :
    IsMinOn F0 Set.univ x ↔ (0 : StrongDual 𝕜 E) ∈ (∂ F0 at x) := by
  change x ∈ minimumSet F0 ↔ (0 : StrongDual 𝕜 E) ∈ (∂ F0 at x)
  exact mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt
    (A := A) (f := f) (g := g) (x := x)

end

section

variable {𝕜 : Type v} {E : Type u} {U : Type w}
variable [RCLike 𝕜] [Preorder 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [AddCommMonoid U] [Module 𝕜 U]

variable (A : E →ₗ[𝕜] U) (f : E → WithBotTop 𝕜) (g : U → WithBotTop 𝕜)
variable (x : E)
local notation "F0" => (fenchelPerturbation A f g)₀

/- Euclidean bridge form of Lemma 31.0.15: the same source-facing specialization through the
vector notation `∂ᵥ((fenchelPerturbation A f g)₀)(x)`. -/
/-- Euclidean bridge form of Lemma 31.0.15: for the primal Fenchel objective `F0`, `x` is a
global minimizer exactly when `0` belongs to the vector-valued subdifferential at `x`. -/
theorem mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_vector :
    x ∈ minimumSet F0 ↔ (0 : E) ∈ (∂ᵥF0(x)) := by
  exact mem_minimumSet_iff_zero_mem_subdifferentialAt_vector

/- Source wording bridge for the Euclidean specialization. -/
/-- Source-phrasing bridge for Lemma 31.0.15 at the Euclidean vector owner layer. -/
theorem isMinOn_objective_fenchelPerturbation_univ_iff_zero_mem_subdifferentialAt_vector :
    IsMinOn F0 Set.univ x ↔ (0 : E) ∈ (∂ᵥF0(x)) := by
  change x ∈ minimumSet F0 ↔ (0 : E) ∈ (∂ᵥF0(x))
  exact mem_minimumSet_objective_fenchelPerturbation_iff_zero_mem_subdifferentialAt_vector
    (A := A) (f := f) (g := g) (x := x)

end

end Bifunction

/-! ### Lemma_31_0_16 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} {U : Type v}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

local instance instHasPairingSwapPrimalStrongDual :
    HasPairingSwap E (StrongDual 𝕜 E) 𝕜 where
  pairing_swap _ _ := rfl

/-!
Source/core/bridge triage for Lemma 31.0.16.

- `source-facing`: the homogeneous-program Kuhn-Tucker conditions for the support/indicator
  specialization are the two owner memberships on support and concave-indicator sides.
- `core/canonical`: the chapter/project owners are `normalCone`, `subdifferentialAt`,
  and `concaveSubdifferentialAt` on the intrinsic dual carrier `StrongDual`; this pass exposes
  the pointwise canonical theorem first, then a homogeneous-program specialization as a thin
  bridge.
- `bridge/view`: this file specializes the existing Chapter 23/6 owner bridges to the Chapter 31
  support/indicator data, without using the Euclidean `∂ᵥ` bridge or `A.adjoint`.

Domain-style sampling used here:
- `supportFunction` (`δᵛ(· | C)`) from `Chap01.Defintion_4_8_2`;
- `subdifferentialAt` (`∂[Y]`) from `Chap05.Definition_23_0_6`;
- `indicatorFunction_isClosedProperConvex_of_nonempty` from `Chap03.Text_12_3_6`;
- `convexConjugate_indicatorFunction_eq_supportFunction` from `Chap03.Text_13_1_4`;
- `_root_.subdifferentialGraph_convexConjugate_eq_inv` from `Chap05.Text_26_0_1`;
- `_root_.subdifferentialAt_indicatorFunction_eq_normalCone` from
  `Chap05.Example_23_0_7`;
- `_root_.mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg` from
  `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive core data: sets `C`, `D` and points `x`, `xStar`, `u`, `uStar`;
- derived source-facing bridge data: a map `A` and companion dual-side map `Astar` yielding
  `xStar = Astar uStar` and `u = A x`.

Layer target: `core/canonical`.

Scalar/ambient check:
- this declaration is expressed at the generic ordered-normed scalar layer required by the
  graph-inversion owner `_root_.subdifferentialGraph_convexConjugate_eq_inv` and the indicator/
  normal-cone bridges used below.
-/

/-- Pointwise canonical owner form behind Lemma 31.0.16: support/indicator Kuhn-Tucker
subgradient conditions are exactly paired normal-cone memberships, on intrinsic dual carriers. -/
theorem supportIndicator_kuhnTuckerConditions_iff_normalCone
    {C : Set E} {D : Set U}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    {x : E} {xStar : StrongDual 𝕜 E} {u : U} {uStar : StrongDual 𝕜 U} :
    x ∈ (∂[E] (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜)(xStar)) ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at u) ↔
      xStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](u | D) := by
  change x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) xStar E ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at u) ↔
      xStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](u | D)
  have hSupport :
      x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) xStar E ↔
        xStar ∈ N[𝕜](x | C) := by
    have hIndicatorClosed :
        Function.IsClosedProperConvex (𝕜 := 𝕜) (δ[𝕜](· | C) : E → WithTopBot 𝕜) :=
      indicatorFunction_isClosedProperConvex_of_nonempty hC_nonempty hC_closed hC_convex
    have hConjSupport :
        (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)) =
          (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) := by
      simpa using
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := E) (EStar := StrongDual 𝕜 E) (α := 𝕜) (C := C))
    have hGraph :
        _root_.subdifferentialGraph
            (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)) E =
          (_root_.subdifferentialGraph (δ[𝕜](· | C) : E → WithTopBot 𝕜)).inv :=
      _root_.subdifferentialGraph_convexConjugate_eq_inv
        (f := (δ[𝕜](· | C) : E → WithTopBot 𝕜)) hIndicatorClosed
    have hConjSub :
        x ∈ subdifferentialAt
          (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜))
          xStar E ↔
          xStar ∈ (∂ (δ[𝕜](· | C) : E → WithTopBot 𝕜) at x) := by
      change
        (xStar, x) ∈ _root_.subdifferentialGraph
            (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)) E ↔
          (x, xStar) ∈ _root_.subdifferentialGraph
            (δ[𝕜](· | C) : E → WithTopBot 𝕜)
      rw [hGraph]
      exact
        (SetRel.mem_inv
          (R := _root_.subdifferentialGraph (δ[𝕜](· | C) : E → WithTopBot 𝕜))
          (a := x) (b := xStar))
    calc
      x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) xStar E
          ↔ x ∈
            subdifferentialAt
              (((δ[𝕜](· | C) : E → WithTopBot 𝕜)⋆ : StrongDual 𝕜 E → WithTopBot 𝕜))
              xStar E := by
              rw [← hConjSupport]
      _ ↔ xStar ∈ (∂ (δ[𝕜](· | C) : E → WithTopBot 𝕜) at x) := hConjSub
      _ ↔ xStar ∈ N[𝕜](x | C) := by
            rw [_root_.subdifferentialAt_indicatorFunction_eq_normalCone]
  have hIndicator :
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at u) ↔
        -uStar ∈ N[𝕜](u | D) := by
    rw [_root_.mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg]
    have hneg_indicator :
        (-(fun z : U ↦ -(δ[𝕜](z | D)))) = (δ[𝕜](· | D) : U → WithTopBot 𝕜) := by
      funext z
      by_cases hz : z ∈ D <;> simp [indicator_def, hz]
    rw [hneg_indicator]
    rw [_root_.subdifferentialAt_indicatorFunction_eq_normalCone]
  exact hSupport.and hIndicator

/-- Lemma 31.0.16, homogeneous-program specialization: instantiate the pointwise canonical
owner theorem with `xStar = Astar uStar` and `u = A x`. -/
theorem homogeneousProgram_supportIndicator_kuhnTuckerConditions_iff_normalCone
    {A : E →L[𝕜] U} {Astar : StrongDual 𝕜 U → StrongDual 𝕜 E}
    {C : Set E} {D : Set U}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C)
    {x : E} {uStar : StrongDual 𝕜 U} :
    x ∈ (∂[E] (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜)(Astar uStar)) ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at A x) ↔
      Astar uStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](A x | D) := by
  change x ∈ subdifferentialAt (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) (Astar uStar) E ∧
      uStar ∈ (∂⁺ (fun z : U ↦ -(δ[𝕜](z | D))) at A x) ↔
      Astar uStar ∈ N[𝕜](x | C) ∧
        -uStar ∈ N[𝕜](A x | D)
  exact
    (supportIndicator_kuhnTuckerConditions_iff_normalCone
      (C := C) (D := D) hC_nonempty hC_closed hC_convex
      (x := x) (xStar := Astar uStar) (u := A x) (uStar := uStar))

end
