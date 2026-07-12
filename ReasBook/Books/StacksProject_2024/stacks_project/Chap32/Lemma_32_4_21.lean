import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsImmersion`, `IsClosedImmersion`, and `LocallyOfFiniteType`. Local Chapter 32 precedent,
-- especially Lemma 32.4.20, represents directed limits over a base by
-- `D : OrderDual I ⥤ Scheme`, a limit cone, and compatible structure morphisms to the base.
-- The Stacks source tag evidence is consistent with tag `0GIH`.

/-- Lemma 32.4.21: let `S` be a quasi-separated scheme, and let `X = lim_i X_i` be a directed
limit of schemes over `S` with affine transition morphisms. Assume every `X_i` is quasi-compact
and quasi-separated, the transition morphisms `X_{i'} ⟶ X_i` are closed immersions, every
`X_i ⟶ S` is locally of finite type, and the limit morphism `X ⟶ S` is an immersion. Then
`X_i ⟶ S` is an immersion for all sufficiently large `i`. -/
@[stacks 0GIH]
theorem exists_eventually_isImmersion_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [QuasiSeparatedSpace ↥S]
    [∀ i : I, CompactSpace ↥(D.obj i)]
    [∀ i : I, QuasiSeparatedSpace ↥(D.obj i)]
    [∀ i : I, LocallyOfFiniteType (σ i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
    [IsImmersion σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsImmersion (σ i) := sorry

end

end AlgebraicGeometry
