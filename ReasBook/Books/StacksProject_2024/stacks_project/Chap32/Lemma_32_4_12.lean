import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced
-- `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit` and
-- `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`; the source-facing statement below
-- keeps the stronger eventual-stage form stated in Lemma `32.4.12`.

/-- Lemma 32.4.12: in Situation `32.4.5`, if the limit scheme
`S = \lim_i S_i` is quasi-affine, then after passing to some stage `i₀`, every later stage
`S_i` with `i ≥ i₀` is quasi-affine. -/
@[stacks 01Z5]
theorem exists_eventually_isQuasiAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (hS : c.pt.IsQuasiAffine) :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → (D.obj i).IsQuasiAffine := sorry

end

end AlgebraicGeometry
