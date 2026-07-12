import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism separatedness owner
-- `AlgebraicGeometry.IsSeparated`. Local Chapter 32 precedent represents directed limits over a
-- base by a diagram `D : OrderDual I ⥤ Scheme`, a limit cone, explicit structure morphisms
-- `σ i : D.obj i ⟶ S`, and compatibility with transition maps and cone projections. The Stacks
-- source tag evidence is consistent with tag `01ZH`.

/-- Lemma 32.4.17: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of schemes
over `S` with affine transition morphisms. Assume `S` is quasi-separated, every `X_i` is
quasi-compact and quasi-separated, and the limit structure morphism `X ⟶ S` is separated. Then
the stage structure morphisms `X_i ⟶ S` are separated for all sufficiently large `i`. -/
@[stacks 01ZH]
theorem exists_eventually_isSeparated_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [QuasiSeparatedSpace ↥S]
    [∀ i : I, CompactSpace ↥(D.obj i)]
    [∀ i : I, QuasiSeparatedSpace ↥(D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [IsSeparated σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsSeparated (σ i) := sorry

end

end AlgebraicGeometry
