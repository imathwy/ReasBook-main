import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_1_1 (from Chap03) -/
open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Corollary 16.1.1 states that dilating a nonempty set by a nonnegative scalar
  scales its support function by the same scalar.
- `core/canonical`: the owner abstraction is the project support function `supportFunction`,
  together with pointwise set scaling. The generic owner theorem belongs with the existing
  support-function scaling API in `Text_13_1_3`.
- `bridge/view`: the textbook notation `δ*(x* | C)` is the chapter notation `δᵛ(xStar | C)`, and
  the pointwise textbook evaluation formula is the companion theorem
  `supportFunction_smul_set_of_nonempty_apply`.
- Primitive data vs derived API: primitive inputs are only `C`, its nonemptiness witness, and a
  scalar `c` with nonnegativity witness `0 ≤ c`; the owner equality and its pointwise
  specialization are
  derived API.

Domain-style sampling used here:
- `supportFunction` and `supportFunction_def`;
- the owner theorem `supportFunction_smul_set_of_pos`;
- the upstream owner extension `supportFunction_smul_set_of_nonempty`.

Layer target: `bridge/view`. This numbered file should be a direct recall layer, not a second
owner location for the same support-function scaling API.
-/

/- Corollary 16.1.1: for a nonempty set `C` and a nonnegative scalar `λ`, the support function of
the dilate `λ C` is `λ` times the support function of `C`. This is the canonical owner theorem
`supportFunction_smul_set_of_nonempty`, restated on the owner surface `supportFunction`. -/
recall supportFunction_smul_set_of_nonempty
  {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {X Y : Type*}
  [AddCommMonoid Y] [Module 𝕜 Y]
  [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜] [HasPairingZeroRight X Y 𝕜]
  (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) :
  (supportFunction (c • C) : X → WithTopBot 𝕜) =
    (c : WithTopBot 𝕜) • (supportFunction C : X → WithTopBot 𝕜)

/- Corollary 16.1.1 in pointwise form is the existing companion theorem
`supportFunction_smul_set_of_nonempty_apply`. -/
recall supportFunction_smul_set_of_nonempty_apply
  {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {X Y : Type*}
  [AddCommMonoid Y] [Module 𝕜 Y]
  [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜] [HasPairingZeroRight X Y 𝕜]
  (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) (xStar : X) :
  supportFunction (c • C) xStar = (c : WithTopBot 𝕜) * supportFunction C xStar

/-! ### Theorem_16_1 (from Chap03) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v w

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 16.1 records the two scalar-scaling identities for the Fenchel
  conjugate of a proper convex function: conjugation swaps left scalar multiplication with the
  chapter operation `rightScalarMul`.
- `core/canonical`: the owner declarations are `convexConjugate`, `ConvexOn 𝕜 Set.univ`,
  `Function.IsProper`, and `rightScalarMul`, with `Function.IsConvex` used only as a bridge alias.
- `bridge/view`: the textbook notation `λ f` is rendered by the canonical pointwise scalar action
  `((λ : WithTopBot 𝕜) • f)`, while `f λ` is rendered by the previously defined chapter operation
  `(λ •ʳ f)`.
- Primitive data vs derived API: `convexConjugate` and `rightScalarMul` are the owner
  operations; the two scalar-conjugacy identities below are derived source-facing API, not new
  primitive data.

Domain-style sampling used here:
- `convexConjugate` from `Defn_12_2`;
- `ConvexOn` / `convexOn_iff_convex_epigraph` from mathlib and `Theorem_4_2`;
- `Function.IsProper` from `Definition_4_6`;
- `rightScalarMul` from `Text_5_4_2`.

Ambient refinement:
- the two owner equalities themselves use only the ambient structure required by
  `convexConjugate` and `rightScalarMul`, namely an ordered scalar layer, scalar actions, and a
  raw pairing;
- the proper-convex source-facing recovery additionally uses the finite-dimensional properness
  theorem `Function.convexConjugate_isProper_iff_of_convexOn_univ` from `Theorem_12_2`.

Layer target: `source-facing`, split into the two atomic dual-scaling identities displayed in the
source theorem. The owner forms are stated on the codomain-general `WithTopBot 𝕜` layer, and
separate source-facing proper-convex bridges recover the textbook hypothesis block over the
chapter codomain `WithTopBot 𝕜`.
-/

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Ring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [SMul 𝕜 Y]
variable [HasPairing X Y 𝕜]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

variable (f : X → WithTopBot 𝕜) (lam : 𝕜≥0)

-- Proof sketch: for `λ > 0`, expand `convexConjugate` and factor the scalar `λ` out of the
-- Fenchel supremum, rewriting the result as the Chapter 5 formula for the right scalar multiple
-- of `f*`. For `λ = 0`, the only owner-side obstruction is the exceptional case
-- `convexConjugate f = ⊤`, because `rightScalarMul_zero_apply_eq_origin_indicator_of_ne_top`
-- applies directly to `f*`.
theorem convexConjugate_left_smul_eq_rightScalarMul
    (hconj_ne_top : f⋆ ≠ (⊤ : Y → WithTopBot 𝕜)) :
    ((lam : 𝕜) • f)⋆ = lam •ʳ f⋆ := sorry

/-- Properness bridge for Theorem 16.1 (1): if the conjugate is proper, then it is in particular
not identically `+∞`, so the owner-layer scaling identity applies directly. -/
theorem convexConjugate_left_smul_eq_rightScalarMul_of_conjugate_isProper
    (hconj_proper : (f⋆ : Y → WithTopBot 𝕜).IsProper) :
    ((lam : 𝕜) • f)⋆ = lam •ʳ f⋆ :=
  let hconj_ne_top : f⋆ ≠ (⊤ : Y → WithTopBot 𝕜) := by
    intro hconj_top
    rcases hconj_proper.nonempty_dom with ⟨y, hy⟩
    simp [hconj_top] at hy
  convexConjugate_left_smul_eq_rightScalarMul (f := f) (lam := lam) hconj_ne_top

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Ring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [SMul 𝕜 X]
variable [HasPairing X Y 𝕜]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

variable (f : X → WithTopBot 𝕜) (lam : 𝕜≥0)

-- Proof sketch: for `λ > 0`, rewrite `rightScalarMul` by the explicit rescaling
-- formula `x ↦ λ * f (λ⁻¹ • x)`, then change variables in the Fenchel supremum to obtain the
-- pointwise scalar multiple `λ • f*`. For `λ = 0`, the only obstruction is the exceptional case
-- `f = ⊤`; under `f ≠ ⊤`, the zero right scalar multiple is the origin indicator, whose
-- conjugate is the constant zero function `0 • f*`.
theorem convexConjugate_rightScalarMul_eq_left_smul
    (hf_ne_top : f ≠ ⊤) :
    (lam •ʳ f)⋆ = (lam : 𝕜) • f⋆ := sorry

/-- Properness bridge for Theorem 16.1 (2): in the owner layer, properness already supplies the
endpoint exclusion `f ≠ ⊤`, so no convexity hypothesis is needed. -/
theorem convexConjugate_rightScalarMul_eq_left_smul_of_isProper
    (hf_proper : f.IsProper) :
    (lam •ʳ f)⋆ = (lam : 𝕜) • f⋆ :=
  let h_ne_top : f ≠ ⊤ := by
    intro hf_top
    rcases hf_proper.nonempty_dom with ⟨x, hx⟩
    simp [hf_top] at hx
  convexConjugate_rightScalarMul_eq_left_smul (f := f) (lam := lam) h_ne_top

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [MulAction 𝕜 X]
variable [HasPairing X Y 𝕜]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

/-- Positive-scalar companion of Theorem 16.1 (2): when `λ > 0`, the conjugate of `f λ`
is the pointwise left scalar multiple `λ f*`, with no extra endpoint hypothesis because the
exceptional zero-scalar branch is absent. -/
theorem convexConjugate_rightScalarMul_eq_left_smul_of_pos
    (f : X → WithTopBot 𝕜) {lam : 𝕜} (hlam : 0 < lam) :
    ((⟨lam, hlam.le⟩ : 𝕜≥0) •ʳ f)⋆ = (lam : 𝕜) • f⋆ := by
  by_cases hf : f = ⊤
  · have htop :
      (((⟨lam, hlam.le⟩ : 𝕜≥0) •ʳ (⊤ : X → WithTopBot 𝕜)) : X → WithTopBot 𝕜) = ⊤ := by
      ext x
      simpa [WithBotTop.coe_mul_top_of_pos hlam] using
        (rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
          (f := (⊤ : X → WithTopBot 𝕜)) hlam x)
    rw [hf, htop, convexConjugate_top_eq_bot]
    ext y
    simp [Pi.smul_apply, WithBotTop.coe_mul_bot_of_pos hlam]
  · simpa using convexConjugate_rightScalarMul_eq_left_smul
      (f := f) (lam := ⟨lam, hlam.le⟩) hf

end

section

variable {E : Type u} {𝕜 : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

variable (f : E → WithTopBot 𝕜) (lam : 𝕜≥0)

-- Rockafellar states clause `(1)` for proper convex `f`. On theorem surfaces, this file treats
-- `ConvexOn 𝕜 Set.univ` as the canonical convexity owner and keeps `Function.IsConvex` only as an
-- explicit bridge.
/-- Theorem 16.1 (1) in canonical source-facing project form: for a proper convex function on
`Set.univ` and a nonnegative scalar `λ`, the conjugate of the pointwise left scalar multiple `λ f`
is the right
scalar multiple `f* λ`. -/
theorem convexConjugate_left_smul_eq_rightScalarMul_of_proper_convexOn_univ
    (hf_convex : ConvexOn 𝕜 (Set.univ : Set E) f) (hf_proper : f.IsProper) :
    ((lam : 𝕜) • f)⋆ = lam •ʳ f⋆ :=
  let hconj_proper : (f⋆ : E → WithTopBot 𝕜).IsProper :=
    (Function.convexConjugate_isProper_iff_of_convexOn_univ (hf := hf_convex)).2 hf_proper
  convexConjugate_left_smul_eq_rightScalarMul_of_conjugate_isProper
    (f := f) (lam := lam) hconj_proper

/-- Bridge form of Theorem 16.1 (1) through the chapter alias `Function.IsConvex`. -/
theorem convexConjugate_left_smul_eq_rightScalarMul_of_proper_convex
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    ((lam : 𝕜) • f)⋆ = lam •ʳ f⋆ := by
  have hf_convexOn : ConvexOn 𝕜 (Set.univ : Set E) f := by
    rw [convexOn_iff_convex_epigraph]
    simpa [Function.isConvex_iff_convex_epigraph, Set.mem_univ] using hf_convex
  exact convexConjugate_left_smul_eq_rightScalarMul_of_proper_convexOn_univ
    (f := f) (lam := lam) hf_convexOn hf_proper

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [Ring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [SMul 𝕜 X]
variable [HasPairing X Y 𝕜]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

variable (f : X → WithTopBot 𝕜) (lam : 𝕜≥0)

-- Rockafellar states clause `(2)` under the same proper-convex hypothesis block, but in the owner
-- API the convexity premise is unnecessary: properness alone already supplies `f ≠ ⊤`.
/-- Theorem 16.1 (2) in source-facing project form with minimal assumptions:
for a proper function `f` and a nonnegative scalar `λ`, the conjugate of the right scalar
multiple `f λ` is the pointwise left scalar multiple `λ f*`. -/
theorem convexConjugate_rightScalarMul_eq_left_smul_of_proper
    (hf_proper : f.IsProper) :
    (lam •ʳ f)⋆ = (lam : 𝕜) • f⋆ :=
  convexConjugate_rightScalarMul_eq_left_smul_of_isProper (f := f) (lam := lam) hf_proper

end

/-! ### Corollary_16_1_2 (from Chap03) -/
universe u v

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [CommSemiring 𝕜] [ConditionallyCompleteLattice 𝕜] [One 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.1.2 states that the polar of a positive dilate `λ C` is the
  inverse dilate `λ⁻¹ Cᵒ`.
- `core/canonical`: the owner abstractions are the chapter polar operator `Set.polar` and
  pointwise scalar multiplication of sets on a pairing space, best exposed through the
  invertible-scalar action `𝕜ˣ`.
- `bridge/view`: Rockafellar's notation `Cᵒ[𝕜]` is the chapter postfix notation for `Set.polar`,
  while positive-scalar source formulations are thin specializations via `Units.mk0`.

Domain-style sampling used here:
- `Set.polar`, `Set.mem_polar_iff_swap` from `Text_14_0_5`;
- the generic pointwise-set owner lemma `Set.mem_smul_set_iff_inv_smul_mem`.

Primitive data vs derived API:
- primitive inputs: a set `C : Set X` and an invertible scalar `α : 𝕜ˣ`;
- derived API: the polar-scaling equality and its positive-scalar specialization.

Layer target: `source-facing`, stated directly as an equality of polar sets.

Semantic note: this identity only uses invertibility of the scalar, not positivity, so the main
declaration is phrased on `𝕜ˣ`. The source's convexity and nonemptiness hypotheses are redundant
for this owner-level identity and are omitted from the public statement.
-/

-- Proof sketch: rewrite membership in `(α • C)ᵒ` and `α⁻¹ • Cᵒ` using
-- `Set.mem_polar_iff_swap` and
-- `Set.mem_smul_set_iff_inv_smul_mem`. The forward direction evaluates the polar inequality on
-- `α • y`; the reverse direction evaluates it on `α⁻¹ • x`. In both directions the scalar factors
-- cancel by the unit action, so the two membership conditions become equivalent pointwise.
/-- Corollary 16.1.2 at the pairing owner layer: for an invertible scalar `α : 𝕜ˣ`, the polar of
`α • C` is the inverse dilate `α⁻¹ • Cᵒ[𝕜]`. -/
theorem polar_smul_eq_inv_smul_polar
    (C : Set X) (α : 𝕜ˣ) :
    ((α • C)ᵒ[𝕜] : Set Y) = α⁻¹ • (Cᵒ[𝕜] : Set Y) := by
  ext yStar
  rw [Set.mem_polar_iff_swap, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_polar_iff_swap]
  constructor
  · intro hy x hx
    simpa [Units.smul_def, HasLinearPairing.pairing_eq_pairingLinear] using
      hy (α • x) ⟨x, hx, rfl⟩
  · intro hy x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx
    simpa [Units.smul_def, HasLinearPairing.pairing_eq_pairingLinear] using
      hy (α⁻¹ • x) hx

end

section

open scoped Pointwise Rockafellar

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

/-- Corollary 16.1.2, textbook specialization: for a positive scalar `λ`, the polar of the dilate
`λ C` is the inverse dilate `λ⁻¹ Cᵒ[𝕜]`. This is the source-facing view of
`polar_smul_eq_inv_smul_polar`. -/
theorem polar_pos_smul_eq_inv_smul_polar
    (C : Set X) (α : Set.Ioi (0 : 𝕜)) :
    (((α : 𝕜) • C)ᵒ[𝕜] : Set Y) = ((α : 𝕜)⁻¹) • (Cᵒ[𝕜] : Set Y) := by
  simpa [Units.smul_def, Units.val_inv_eq_inv_val] using
    polar_smul_eq_inv_smul_polar C (Units.mk0 (α : 𝕜) α.2.ne')

end
