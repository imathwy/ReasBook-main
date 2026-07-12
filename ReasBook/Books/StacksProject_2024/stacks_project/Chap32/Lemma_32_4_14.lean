import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced the affine-transition limit API and the canonical
-- separatedness owners `IsSeparated` and `Scheme.IsSeparated`; local Lemmas `32.4.12` and
-- `32.4.13` use the same directed inverse-system owner for eventual stage properties.

/-- Lemma 32.4.14: in Situation `32.4.5`, if the limit scheme
`S = \lim_i S_i` is separated, then after passing to some stage `i₀`, every later stage
`S_i` with `i ≥ i₀` is separated. -/
@[stacks 086Q]
theorem exists_eventually_isSeparated_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    [c.pt.IsSeparated] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → (D.obj i).IsSeparated := sorry

end

end AlgebraicGeometry
