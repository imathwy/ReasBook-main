import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_12_8 (from Chap12) -/
open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [AddGroup H]
variable (f g : H → Set.Ioi (⊥ : EReal))

-- Proof sketch: unpack membership in the pointwise sum of the two epigraphs, rewrite each
-- epigraph condition with `mem_epigraph_iff`, and compare the defining infimum of `f □ g` with the
-- single decomposition coming from the chosen summands.
/-- Proposition 12.8 (1): the pointwise sum of the real-height epigraphs of `f` and `g` is
contained in the real-height epigraph of their infimal convolution. -/
theorem add_epigraph_subset_epigraph_infimalConvolution :
    epigraph f.asEReal + epigraph g.asEReal ⊆
      epigraph (f □ g) := sorry

-- Proof sketch: one inclusion is Proposition 12.8 (1). For the reverse inclusion, take a point
-- of `epigraph (f □ g)`, use exactness to choose a minimizing decomposition `x = y + (x - y)`,
-- and place the two resulting summands in the epigraphs of `f` and `g`.
/-- Proposition 12.8 (2): if the infimal convolution is exact, then its real-height epigraph is
exactly the pointwise sum of the real-height epigraphs of `f` and `g`. -/
theorem epigraph_infimalConvolution_eq_add_epigraph_of_exact
    (hExact : infimalConvolution.Exact f g) :
    epigraph (f □ g) =
      epigraph f.asEReal + epigraph g.asEReal := sorry

end ERealFunction
