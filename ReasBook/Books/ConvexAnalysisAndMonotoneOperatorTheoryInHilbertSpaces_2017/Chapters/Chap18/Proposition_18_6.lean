import Mathlib
import BauschkeLean.Chap02.Definition_2_54
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap16.Proposition_16_61
import BauschkeLean.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfInfimalConvolutions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation:70 f " □ₑ " g =>
  ERealFunction.infimalConvolution (fun z ↦ (f z : EReal)) (fun z ↦ (g z : EReal))

omit [CompleteSpace H] in
/-- Helper for Proposition 18 6: domain membership of `∂ (f □ g)` together with exactness at `y`
produces a common subgradient of `f` at `y` and of `g` at `x - y`. -/
lemma mem_inter_subdifferential_of_mem_subdifferential_infimalConvolution_of_value_eq
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (x y : H) {u : H}
    (hu : u ∈ (∂ (f □ₑ g)) x)
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal)) :
    u ∈ (∂ f) y ∩ (∂ g) (x - y) := by
  have hsub :
      (∂ (f □ₑ g)) x = (∂ f) y ∩ (∂ g) (x - y) := by
    simpa using
      (subdifferential_infimalConvolution_eq_inter_of_value_eq
        (f := f) (g := g) (x := x) (y := y) hf hg hEq)
  rw [hsub] at hu
  exact hu

omit [CompleteSpace H] in
/-- Helper for Proposition 18 6: domain membership of `∂ (f □ g)` together with exactness at `y`
produces a common subgradient of `f` at `y` and of `g` at `x - y`. -/
lemma common_subgradient_nonempty_of_mem_dom_of_value_eq
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (x y : H)
    (hx : x ∈ SetValuedOperator.dom (∂ (f □ₑ g)))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal)) :
    ((∂ f) y ∩ (∂ g) (x - y)).Nonempty := by
  rw [SetValuedOperator.mem_dom_iff] at hx
  rcases hx with ⟨u, hu⟩
  exact ⟨u, mem_inter_subdifferential_of_mem_subdifferential_infimalConvolution_of_value_eq
    f g hf hg x y hu hEq⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 18 6: a nonempty subdifferential fiber of a `Γ₀(H)` function lies over
its effective domain. -/
lemma effectiveDomain_of_subdifferential_nonempty_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (y : H)
    (hy_sub : ((∂ f) y).Nonempty) :
    y ∈ effectiveDomain f := by
  have hy_dom : y ∈ SetValuedOperator.dom (∂ f) := by
    rcases hy_sub with ⟨u, hu⟩
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  exact subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero hf hy_dom

omit [CompleteSpace H] in
/-- Helper for Proposition 18 6: once the left subdifferential fiber is known to be the singleton
`{gradf}`, any common subgradient forces `gradf` to lie in the right fiber as well. -/
lemma gradf_mem_right_subdifferential_of_common_subgradient
    {f g : H → Set.Ioi (⊥ : EReal)} {x y gradf u : H}
    (hu : u ∈ (∂ f) y ∩ (∂ g) (x - y))
    (hleft : (∂ f) y = ({gradf} : Set H)) :
    gradf ∈ (∂ g) (x - y) := by
  rcases hu with ⟨hu_left, hu_right⟩
  -- The common subgradient must equal the unique element of the left singleton fiber.
  have hu_eq : u = gradf := by
    rw [hleft] at hu_left
    simpa using hu_left
  -- Rewriting along that equality transfers the right-fiber membership to `gradf`.
  simpa [hu_eq] using hu_right

-- Proof sketch: Proposition 16.61 rewrites the subdifferential of the exact infimal convolution at
-- `x` as `(∂ f) y ∩ (∂ g) (x - y)`. The Gâteaux derivative hypothesis identifies `(∂ f) y` with
-- the singleton `{gradf}` via Proposition 17.31 once exactness and domain membership of the
-- left-hand side place `y` in `effectiveDomain f`. Rewriting that domain membership as pointwise
-- nonemptiness makes the intersection nonempty, hence it must equal `{gradf}`.
/-- Proposition 18.6: if `x` belongs to the domain of the subdifferential of the infimal
convolution `f □ g`, the infimal convolution is exact at `x` with minimizer `y`, and `f` has
Gâteaux gradient `gradf` at `y`, then the subdifferential of `f □ g` at `x` is the singleton
`{gradf}`. -/
theorem subdifferential_infimalConvolution_eq_singleton_of_mem_dom_of_value_eq_of_gateauxDerivative
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (x y gradf : H)
    (hx : x ∈ SetValuedOperator.dom (∂ (f □ₑ g)))
    (hEq : (f □ₑ g) x = (f y : EReal) + (g (x - y) : EReal))
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) y) :
    (∂ (f □ₑ g)) x = ({gradf} : Set H) := by
  have _ : CompleteSpace H := inferInstance
  have hinter_nonempty :
      ((∂ f) y ∩ (∂ g) (x - y)).Nonempty :=
    common_subgradient_nonempty_of_mem_dom_of_value_eq f g hf hg x y hx hEq
  have hleft_nonempty : ((∂ f) y).Nonempty := by
    rcases hinter_nonempty with ⟨u, hu⟩
    exact ⟨u, hu.1⟩
  have hy_eff : y ∈ effectiveDomain f :=
    effectiveDomain_of_subdifferential_nonempty_of_mem_gammaZero f hf y hleft_nonempty
  have hleft : (∂ f) y = ({gradf} : Set H) :=
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt
      (f := f) (x := y) hy_eff gradf hgrad
  have hsub :
      (∂ (f □ₑ g)) x = (∂ f) y ∩ (∂ g) (x - y) := by
    simpa using
      (subdifferential_infimalConvolution_eq_inter_of_value_eq
        (f := f) (g := g) (x := x) (y := y) hf hg hEq)
  rcases hinter_nonempty with ⟨u, hu⟩
  have hgrad_right : gradf ∈ (∂ g) (x - y) :=
    gradf_mem_right_subdifferential_of_common_subgradient hu hleft
  have hsubset : ({gradf} : Set H) ⊆ (∂ g) (x - y) := by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    simpa [hv] using hgrad_right
  rw [hsub, hleft]
  exact Set.inter_eq_left.mpr hsubset

end DifferentiabilityOfInfimalConvolutions

end ERealFunction
