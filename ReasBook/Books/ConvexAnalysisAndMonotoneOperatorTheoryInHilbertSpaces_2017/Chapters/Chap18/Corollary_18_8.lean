import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap11.Definition_11_11
import BauschkeLean.Chap12.Definition_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfInfimalConvolutions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]

local notation:70 f " □ₑ " g =>
  ERealFunction.infimalConvolution (fun z ↦ (f z : EReal)) (fun z ↦ (g z : EReal))

/-- The finite real representative of an `Ioi (⊥ : EReal)`-valued function. -/
abbrev toRealRepresentative (f : H → Set.Ioi (⊥ : EReal)) : H → ℝ :=
  fun x ↦ (f x : EReal).toReal

/-- The finite real representative of the infimal convolution `f □ g`. -/
noncomputable abbrev infimalConvolutionToReal
    (f g : H → Set.Ioi (⊥ : EReal)) : H → ℝ :=
  fun x ↦ ((f □ₑ g) x).toReal

-- Semantic search note: `lean_leansearch` returned only generic convolution/calculus lemmas, so
-- this file keeps the source-facing Chapter 12/18 owner chain as the public statement surface.

/- Source/core/bridge triage:
- `source-facing`: Corollary 18.8 is the global differentiability consequence for the finite real
  representative of `f □ g` under the source hypotheses on `f`.
- `core/canonical`: the owner abstractions are `Supercoercive f.asEReal`, the Chapter 12 exactness
  and properness owners for `f □ g`, and the pointwise differentiability theorem from Proposition
  18.7.
- `bridge/view`: the source-facing finiteness hypothesis `hfin` is used only to place every
  `x : H` in `dom (f □ g)` through `dom_infimalConvolution`; the proof then routes entirely
  through the existing owner API. -/

-- Proof sketch: Proposition 12.14 gives that the infimal convolution is exact under the
-- supercoercive hypothesis and that the raw infimal convolution `f □ g` is proper and lies in
-- `Γ(H)`. Since `f` is finite everywhere, Proposition 12.6(ii) makes the effective domain of
-- `f □ g` all of `H`, so every `x : H` admits a minimizer `y` with
-- `(f □ g) x = f y + g (x - y)`. Apply the finite-dimensional Fréchet conclusion of Proposition
-- 18.7 pointwise, using the Fréchet differentiability of `f` at `y`, and conclude global
-- differentiability.
/-- Corollary 18.8: on a finite-dimensional real Hilbert space, if `f, g ∈ Γ₀(H)`, if `f` is
finite everywhere, supercoercive, and Fréchet differentiable on `H`, then the finite-valued
representative of `f □ g` is Fréchet differentiable on `H`. -/
theorem differentiable_infimalConvolution_toReal_of_mem_gammaZero_of_supercoercive_of_differentiable
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hfin : ∀ x : H, (f x : EReal) < ⊤)
    (hsuper : Supercoercive f.asEReal)
    (hdiff : Differentiable ℝ (toRealRepresentative f)) :
    Differentiable ℝ (infimalConvolutionToReal f g) := sorry

end DifferentiabilityOfInfimalConvolutions

end ERealFunction
