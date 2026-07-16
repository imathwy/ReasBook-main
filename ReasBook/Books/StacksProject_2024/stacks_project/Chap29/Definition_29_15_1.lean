import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import StacksProject_2024.stacks_project.Chap29.Definition_29_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` returned the canonical scheme-morphism owner
  `AlgebraicGeometry.LocallyOfFiniteType`, its affine-open characterization
  `AlgebraicGeometry.locallyOfFiniteType_iff`, and the affine-chart theorem
  `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`;
- `Chap29/Definition_29_14_2.lean` supplies the source-style affine-neighborhood owner
  `LocallyOfType`;
- `Chap29/Lemma_29_15_5.lean` and `Chap29/Lemma_29_15_6.lean` already record scheme morphisms “of
  finite type” through the canonical pair `QuasiCompact` and `LocallyOfFiniteType`.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Definition 29.15.1 (1): the morphism `f : X ⟶ S` is of finite type at `x` if `x` admits an
affine open neighborhood mapping into an affine open neighborhood of `f x` such that the induced
ring map is of finite type. -/
class FiniteTypeAt (x : X) : Prop where
  property :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType

/-- Finite-type-at-a-point structures are proposition-valued. -/
instance instSubsingletonFiniteTypeAt (x : X) :
    Subsingleton (FiniteTypeAt f x) :=
  inferInstance

/-- Unfold `FiniteTypeAt` as the affine-neighborhood witness condition from the source definition.
-/
theorem finiteTypeAt_iff (x : X) :
    f.FiniteTypeAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType :=
  sorry

/-- Definition 29.15.1 (2): the morphism `f : X ⟶ S` is locally of finite type exactly when it is
of finite type at every point of `X`; this is the canonical mathlib owner
`LocallyOfFiniteType f`. -/
theorem locallyOfFiniteType_iff_forall_finiteTypeAt :
    LocallyOfFiniteType f ↔ ∀ x : X, f.FiniteTypeAt x := sorry

/-- The source-style affine-neighborhood owner for finite type agrees with the canonical owner
`LocallyOfFiniteType`. -/
theorem locallyOfFiniteType_iff_locallyOfType :
    LocallyOfFiniteType f ↔ LocallyOfType RingHom.FiniteType f := sorry

/-- Definition 29.15.1 (3): in scheme language, saying that `f` is of finite type is recorded by
the canonical pair of conditions that `f` is quasi-compact and locally of finite type. -/
class FiniteType : Prop extends QuasiCompact f, LocallyOfFiniteType f

/-- A finite type morphism is quasi-compact. -/
instance instQuasiCompactOfFiniteType [h : FiniteType f] :
    QuasiCompact f :=
  h.toQuasiCompact

/-- A finite type morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOfFiniteType [h : FiniteType f] :
    LocallyOfFiniteType f :=
  h.toLocallyOfFiniteType

/-- Finite-type structures are proposition-valued. -/
instance instSubsingletonFiniteType :
    Subsingleton (FiniteType f) :=
  inferInstance

/-- Unfold `FiniteType` into quasi-compactness and local finite type. -/
theorem finiteType_iff :
    FiniteType f ↔ QuasiCompact f ∧ LocallyOfFiniteType f := sorry

/-- Unfold the scheme-side finite-type condition into quasi-compactness together with the pointwise
finite-type-at condition. -/
theorem finiteType_iff_quasiCompact_and_forall_finiteTypeAt :
    FiniteType f ↔
      (QuasiCompact f ∧ ∀ x : X, f.FiniteTypeAt x) := sorry

end Scheme.Hom
end AlgebraicGeometry
