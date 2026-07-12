import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced `IsFinite`,
-- `IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`, `IsIntegralHom`, and
-- `LocallyOfFiniteType`. Local Chapter 32 precedent represents directed limits of schemes as
-- diagrams `D : OrderDual I ⥤ Scheme` with an explicit limit cone and structure morphisms over
-- the base. The Stacks source tag evidence is consistent with tag `09ZN`.

/-- Lemma 32.4.19: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of
schemes over `S` with affine transition morphisms. Assume `S` is quasi-compact and
quasi-separated, every `X_i` is quasi-compact and quasi-separated, the transition morphisms
`X_{i'} ⟶ X_i` are finite, every `X_i ⟶ S` is locally of finite type, and the limit morphism
`X ⟶ S` is integral. Then `X_i ⟶ S` is finite for all sufficiently large `i`. -/
@[stacks 09ZN]
theorem exists_eventually_isFinite_to_base_of_isLimit_isIntegralHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [CompactSpace ↥S] [QuasiSeparatedSpace ↥S]
    [∀ i : I, CompactSpace ↥(D.obj i)]
    [∀ i : I, QuasiSeparatedSpace ↥(D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [∀ {i i' : I} (hii' : i ≤ i'), IsFinite (D.map (homOfLE hii'))]
    [∀ i : I, LocallyOfFiniteType (σ i)]
    [IsIntegralHom σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsFinite (σ i) := sorry

end

end AlgebraicGeometry
