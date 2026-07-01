import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_5_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section PairingSwapped

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 13.3 identifies the support function of `dom f` with the recession
  function of `f*`, and in the closed case identifies the support function of `dom f*` with the
  recession function of `f`.
- `core/canonical`: the owner abstractions already present in the project are `supportFunction`,
  `convexConjugate`, `Function.recessionFunction`, `Function.IsConvex`,
  `Function.IsProper`, and `Function.IsClosedProperConvex`, with the source-facing theorem surface
  written using the chapter notation `δᵛ(· | ·)` and the object-prefix predicates `f.IsConvex`
  and `f.IsProper`.
- `bridge/view`: for `WithTopBot 𝕜`-valued functions, Rockafellar's `dom f` is the chapter's
  established
  effective-domain set `dom(f) = {x : X | f x < ⊤}`, so `dom f*` is correspondingly `dom(f⋆)`.

Domain-style sampling used here:
- `supportFunction` from Definition 4.8.2;
- `Function.recessionFunction` from Corollary 8.5.1;
- `convexConjugate` from Definition 12.2;
- the closed-case biconjugacy theorem `Function.IsClosedProperConvex.biconjugate_eq`.

Primitive data vs derived API:
- primitive input: a function `f : X → WithTopBot 𝕜`;
- owner hypotheses: `f.IsConvex` and `f.IsProper` for clause (1);
- derived API: clause (2), obtained from clause (1) applied to `f⋆` together with closed proper
  convex biconjugacy.

Layer target: this item stays `source-facing`, with clause (1) stated on the swap-compatible
paired-space owner layer and clause (2) on the finite-dimensional continuous linear self-pairing
layer where the current biconjugacy dependency lives.

Codomain/scalar canonicalization note for this file:
- clause (1) is stated directly on the canonical codomain `WithTopBot 𝕜` at the pairing layer;
- clause (2) is stated on the finite-dimensional scalar-generic layer where the reused closed
  proper convex biconjugacy route is already available in this dependency chain.
-/
variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X] [HasPairing X Y 𝕜]
variable [AddCommMonoid Y] [HasPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜]
local instance : HasPairing X Y (WithTopBot 𝕜) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot 𝕜) := instHasPairingWithBotTop
variable (f : X → WithTopBot 𝕜)

-- Proof sketch: represent `f*` as the pointwise supremum of the affine functions
-- `xStar ↦ ⟪x, xStar⟫ - μ` coming from points `(x, μ)` of the epigraph of `f`. The recession
-- function of such an affine function is the linear map `xStar ↦ ⟪x, xStar⟫`, so the recession
-- function of `f*` is the pointwise supremum of those linear maps over `x ∈ dom(f)`. That
-- supremum is exactly `δᵛ(· | dom(f))`.
private theorem
    supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate_of_pairing_swap_core
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    δᵛ(· | dom(f)) = (f⋆)₀⁺ := by
  sorry

/-- Theorem 13.3 (1), pairing-owner form: on a swap-compatible dual pairing, the support function
of the effective domain `dom(f)` of a proper convex function `f` equals the recession function of
its Fenchel conjugate `f⋆`. -/
theorem supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    δᵛ(· | dom(f)) = (f⋆)₀⁺ := by
  simpa using
    supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate_of_pairing_swap_core
      hf_convex hf_proper

end PairingSwapped

section PairingFiniteDimensional

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithTopBot 𝕜) := instHasPairingWithBotTop
variable (f : E → WithTopBot 𝕜)

-- Proof sketch: apply clause (1) to `convexConjugate f`. Under the packaged closed proper convex
-- hypothesis `f.IsClosedProperConvex`, biconjugacy gives `f⋆⋆ = f`, so `δᵛ(· | dom(f⋆))`
-- identifies with `f0⁺`.
/-- Theorem 13.3 (2): if `f` is closed as well as proper convex, then the support function of
`dom(f⋆)` is the recession function `f₀⁺`. This clause is stated at the finite-dimensional
continuous linear self-pairing layer and uses closed proper convex biconjugacy. -/
theorem supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction
    (hf : f.IsClosedProperConvex) :
    δᵛ(· | dom(f⋆)) = f₀⁺ := by
  have hfirst :
      δᵛ(· | dom(f⋆)) = (f⋆⋆)₀⁺ := by
    simpa using
      supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
        (f := f⋆) hf.convexConjugate.convex hf.convexConjugate.proper
  have hbiconj : f⋆⋆ = f := by
    simpa using hf.biconjugate_eq
  have hrec : (f⋆⋆)₀⁺ = f₀⁺ := by
    simpa using congrArg Function.recessionFunction hbiconj
  exact hfirst.trans hrec

end PairingFiniteDimensional
