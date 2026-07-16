import StacksProject_2024.stacks_project.Chap32.Lemma_32_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

-- Semantic recall: `lean_leansearch` confirmed `IsProper` as the canonical
-- scheme-morphism owner for properness. Local Chapter 32 precedent represents a directed
-- limit of schemes over a base by a diagram `D : OrderDual I ⥤ Scheme`, a limiting cone,
-- and compatible structure morphisms to the base. The Stacks source tag evidence is
-- consistent with tag `0EX1`.

/-- Lemma 32.13.4: let `S` be a scheme and let `X = lim_i X_i` be a directed limit of
schemes over `S` with affine transition morphisms. Let `Y ⟶ X` be a morphism over `S`.
If `Y ⟶ X` is proper, every `X_i` is quasi-compact and quasi-separated, and `Y` is
locally of finite type over `S`, then `Y ⟶ X_i` is proper for all sufficiently large
indices `i`. -/
@[stacks 0EX1]
theorem exists_eventually_isProper_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S Y : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsProper f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsProper (f ≫ c.π.app i) := sorry

end

end AlgebraicGeometry
