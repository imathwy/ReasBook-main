import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced the canonical `IsClosedImmersion`,
-- `LocallyOfFiniteType`, and affine-transition-limit API. Local Chapter 32 precedent, especially
-- Lemma 32.4.18, represents a directed limit of schemes over a base by a diagram
-- `D : OrderDual I ⥤ Scheme`, a limit cone, and explicit compatible structure morphisms to `S`.

/-- Lemma 32.4.20: let `S` be a quasi-compact quasi-separated scheme, and let
`X = lim_i X_i` be a directed limit of quasi-compact quasi-separated schemes over `S` with affine
transition morphisms. If the transition morphisms `X_{i'} ⟶ X_i` are closed immersions, each
`X_i ⟶ S` is locally of finite type, and the limit morphism `X ⟶ S` is a closed immersion, then
`X_i ⟶ S` is a closed immersion for all sufficiently large `i`. -/
@[stacks 0A0N]
theorem exists_eventually_isClosedImmersion_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [CompactSpace ↥S] [QuasiSeparatedSpace ↥S]
    [∀ i : I, CompactSpace ↥(D.obj i)]
    [∀ i : I, QuasiSeparatedSpace ↥(D.obj i)]
    [∀ i : I, LocallyOfFiniteType (σ i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
    [IsClosedImmersion σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsClosedImmersion (σ i) := sorry

end

end AlgebraicGeometry
