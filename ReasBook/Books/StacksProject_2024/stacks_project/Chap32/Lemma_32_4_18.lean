import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced the affine-transition-limit API, especially
-- `Scheme.exists_isAffine_of_isLimit`; local Chapter 32 precedent represents a directed limit of
-- schemes as `D : OrderDual I ⥤ Scheme` with a limit cone and affine transition morphisms.

/-- Lemma 32.4.18: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of schemes
over `S` with affine transition morphisms. If `S` and all `X_i` are quasi-compact and
quasi-separated, and the limit structure morphism `X ⟶ S` is affine, then the stage structure
morphisms `X_i ⟶ S` are affine for all sufficiently large `i`. -/
@[stacks 09ZM]
theorem exists_eventually_isAffineHom_to_base_of_isLimit
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
    [IsAffineHom σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAffineHom (σ i) := sorry

end

end AlgebraicGeometry
