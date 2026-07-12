import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced
-- `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` and the affine-transition-limit API.
-- Local Chapter 32 precedent states the source-facing eventual-stage form for quasi-affineness
-- in Lemma `32.4.12`; this item records the corresponding eventual affine statement.

/-- Lemma 32.4.13: in Situation `32.4.5`, if the limit scheme
`S = \lim_i S_i` is affine, then after passing to some stage `i₀`, every later stage
`S_i` with `i ≥ i₀` is affine. -/
@[stacks 01Z6]
theorem exists_eventually_isAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    [IsAffine c.pt] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAffine (D.obj i) := sorry

end

end AlgebraicGeometry
