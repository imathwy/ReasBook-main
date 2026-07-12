import Mathlib

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsClosedImmersion`, `IsImmersion`, `LocallyOfFiniteType`, and
-- `LocallyOfFinitePresentation`. Local Chapter 32 precedent keeps the inverse-system owner as a
-- diagram `D : OrderDual I ⥤ Scheme` with a chosen limit cone `c`; to preserve the source's
-- "schemes over `S`" semantics without introducing a wrapper, the structure morphisms to `S` and
-- their compatibility with transitions and projections are kept explicit in each statement.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S Y : Scheme.{u}}

/-- Lemma 32.4.16 (1): let `S` be a scheme, let `X = lim_i X_i` be a directed limit of schemes
over `S` with affine transition morphisms, and let `f : Y ⟶ X` be a morphism over `S`. If `f` is
a closed immersion, every stage `X_i` is quasi-compact, and `Y ⟶ S` is locally of finite type,
then for all sufficiently large stages the composite `Y ⟶ X_i` is a closed immersion. -/
@[stacks 081B]
theorem exists_eventually_isClosedImmersion_to_stage
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [∀ i : I, CompactSpace ↥(D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsClosedImmersion f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsClosedImmersion (f ≫ c.π.app i') := sorry

/-- Lemma 32.4.16 (2): in the same inverse-limit situation over `S`, if `f : Y ⟶ X` is an
immersion, every stage `X_i` is quasi-separated, `Y ⟶ S` is locally of finite type, and `Y` is
quasi-compact, then for all sufficiently large stages the composite `Y ⟶ X_i` is an immersion. -/
@[stacks 081B]
theorem exists_eventually_isImmersion_to_stage
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [∀ i : I, QuasiSeparatedSpace ↥(D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [CompactSpace ↥Y]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsImmersion f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsImmersion (f ≫ c.π.app i') := sorry

/-- Lemma 32.4.16 (3): in the same inverse-limit situation over `S`, if `f : Y ⟶ X` is an
isomorphism, every stage `X_i` is quasi-compact and locally of finite type over `S`, the
transition morphisms `X_{i'} ⟶ X_i` are closed immersions, and `Y ⟶ S` is locally of finite
presentation, then for all sufficiently large stages the composite `Y ⟶ X_i` is an isomorphism. -/
@[stacks 081B]
theorem exists_eventually_isIso_to_stage
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (σ : ∀ i : I, D.obj i ⟶ S) (σlim : c.pt ⟶ S)
    (hσ : ∀ {i i' : I} (hii' : i ≤ i'), D.map (homOfLE hii') ≫ σ i = σ i')
    (hπ : ∀ i : I, c.π.app i ≫ σ i = σlim)
    [∀ i : I, CompactSpace ↥(D.obj i)]
    [∀ i : I, LocallyOfFiniteType (σ i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsIso f] [LocallyOfFinitePresentation g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsIso (f ≫ c.π.app i') := sorry

end

end AlgebraicGeometry
