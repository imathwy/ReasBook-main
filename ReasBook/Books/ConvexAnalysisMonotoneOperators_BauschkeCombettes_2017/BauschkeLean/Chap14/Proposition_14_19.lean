import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.BauschkeLean.Chap13.Corollary_13_38

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section Conjugation

attribute [local instance] Classical.propDecidable

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use Corollary 13.38 to rewrite `h` as its Fenchel biconjugate, expand
-- the conjugate of the piecewise map
-- `x ↦ if x ∈ effectiveDomain g then g x - h x else +∞` as a supremum over the effective domain
-- of `g`, insert the
-- supremum formula for `h = h**`, interchange the two suprema, and identify the inner supremum as
-- `g* (u + v)`.
/-- Proposition 14.19: if `h ∈ Γ₀(H)`, then the Fenchel conjugate of the
piecewise function from `(14.23)`, equal to `g - h` on `effectiveDomain g` and `+∞` outside it,
satisfies
`(x ↦ if x ∈ effectiveDomain g then g x - h x else +∞)* u =
  sup_{v ∈ dom h*} (g* (u + v) - h* v)` for every `u`. -/
theorem conjugate_sub_on_effectiveDomain_eq_sSup_conjugate_add_sub_conjugate
    (g h : H → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(H)) (u : H) :
    (fun x ↦ if x ∈ effectiveDomain g then g.asEReal x - h.asEReal x else ⊤)∗ u =
      sSup
        ((fun v : H ↦
            g.asEReal∗ (u + v) - h.asEReal∗ v) ''
          dom (h.asEReal∗)) := sorry

end Conjugation

end ERealFunction
