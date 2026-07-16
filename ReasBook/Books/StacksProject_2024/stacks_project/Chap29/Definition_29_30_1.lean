import StacksProject_2024.stacks_project.Chap10.Definition_10_136_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced nearby scheme-morphism owners such as
  `AlgebraicGeometry.LocallyOfFinitePresentation`, `AlgebraicGeometry.IsSmooth`, and
  `AlgebraicGeometry.IsEtale`;
- local verification against `Chap29/Definition_29_14_2.lean`, `Chap29/Lemma_29_30_5.lean`,
  `Chap29/Lemma_29_30_6.lean`, and `Chap29/Definition_29_34_1.lean` shows that the project owner
  for scheme-level syntomicity is `LocallyOfType RingHom.Syntomic`.
-/

/-- Definition 29.30.1 (1): a morphism `f : X ⟶ S` is syntomic at `x ∈ X` if `x` admits affine
source and target neighbourhoods on which the induced ring map is syntomic. -/
def SyntomicAt (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ V : S.affineOpens,
      ∃ e : U ≤ f ⁻¹ᵁ V,
        RingHom.Syntomic (f.appLE V U e).hom

/-- A `SyntomicAt` hypothesis can be used through its affine-neighborhood witness condition from
Definition 29.30.1. -/
theorem SyntomicAt.exists_affineNeighborhood
    {x : X} (hx : SyntomicAt f x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Syntomic (f.appLE V U e).hom := sorry

/-- Unfold `SyntomicAt` as the affine-neighborhood witness condition from Definition 29.30.1. -/
theorem syntomicAt_iff (x : X) :
    SyntomicAt f x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            RingHom.Syntomic (f.appLE V U e).hom := sorry

/-- Definition 29.30.1 (2): a morphism `f : X ⟶ S` is syntomic if it is syntomic at every point
of `X`. This is the scheme-level specialization of `LocallyOfType` to `RingHom.Syntomic`. -/
abbrev Syntomic : Prop :=
  LocallyOfType RingHom.Syntomic f

/-- A morphism is syntomic exactly when it is syntomic at every point of the source. -/
theorem syntomic_iff_forall_syntomicAt :
    Syntomic f ↔ ∀ x : X, SyntomicAt f x := sorry

/-- Definition 29.30.1 (3): for a morphism `f : X ⟶ Spec(k)`, saying that `X` is a local complete
intersection over `k` means exactly that `f` is syntomic. -/
abbrev IsLocalCompleteIntersectionOver
    (k : Type u) [Field k]
    {X : Scheme.{u}}
    (f : X ⟶ Scheme.Spec.obj (Opposite.op <| CommRingCat.of k)) : Prop :=
  Syntomic f

end AlgebraicGeometry
