import Mathlib
import StacksProject_2024.Chap32.Lemma_32_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ j, CompactSpace ↥(D.obj j)]
variable [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

-- Semantic recall: `lean_leansearch` only surfaced general affine-transition limit owners in
-- mathlib, while local Chapter 32 precedent provides the source-faithful base-change diagram in
-- `Lemma_32_2_3`; this item reuses that owner and records the eventual-emptiness conclusion as a
-- direct theorem on later stages.

/-- Lemma 32.4.9: in Situation 32.4.5, fix a stage `i` and a morphism `T ⟶ S_i` with `T`
quasi-compact. If the pullback `T ×_{S_i} S` along the limit projection is empty, then there is a
later stage `i₀ ≥ i` such that every further base change `T ×_{S_i} S_{i'}` with `i' ≥ i₀` is
empty. -/
@[stacks 05F3]
theorem exists_eventually_isEmpty_baseChange_to_stage
    (i : I) {T : Scheme.{u}} (t : T ⟶ D.obj i) [CompactSpace ↥T]
    (hempty : IsEmpty ↥(baseChangeConeOfDirectedAffineTransition D c i t).pt) :
    ∃ (i₀ : I) (hii₀ : i ≤ i₀), ∀ ⦃i' : I⦄, (hi₀i' : i₀ ≤ i') →
      IsEmpty ↥((baseChangeDiagramOfDirectedAffineTransition D i t).obj
        (Over.mk (homOfLE (show OrderDual.toDual i' ≤ OrderDual.toDual i from
          (show i ≤ i' from le_trans hii₀ hi₀i'))))) := sorry

end

end AlgebraicGeometry
