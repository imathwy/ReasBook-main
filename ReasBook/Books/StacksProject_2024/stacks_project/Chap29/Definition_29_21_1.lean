import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import StacksProject_2024.stacks_project.Chap29.Definition_29_14_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-morphism owner
  `AlgebraicGeometry.LocallyOfFinitePresentation` together with
  `AlgebraicGeometry.locallyOfFinitePresentation_iff`;
- `Chap29/Definition_29_14_2.lean` supplies the source-style affine-neighborhood owner
  `LocallyOfType`;
- `Chap29/Definition_29_15_1.lean` already fixes the Chapter 29 owner pattern for the analogous
  finite-type item: keep the pointwise source-facing predicate, bridge it to the generic
  affine-neighborhood owner, and record the global scheme-side notion through the canonical
  mathlib owner plus the qc/qs strengthening.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Definition 29.21.1 (1): a morphism `f : X ⟶ S` is of finite presentation at `x ∈ X` if `x`
admits affine source and target neighborhoods on which the induced ring map is of finite
presentation. -/
class FinitePresentationAt (x : X) : Prop where
  property :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation

/-- Finite-presentation-at-a-point structures are proposition-valued. -/
instance instSubsingletonFinitePresentationAt (x : X) :
    Subsingleton (f.FinitePresentationAt x) :=
  inferInstance

/-- A `FinitePresentationAt` hypothesis can be used through its affine-neighborhood witness
condition from Definition 29.21.1. -/
theorem FinitePresentationAt.exists_affineNeighborhood
    {x : X} (hx : f.FinitePresentationAt x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation :=
  hx.property

/-- Unfold `FinitePresentationAt` as the affine-neighborhood witness condition from the source
definition. -/
theorem finitePresentationAt_iff (x : X) :
    f.FinitePresentationAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation :=
  sorry

/-- Definition 29.21.1 (2): a morphism `f : X ⟶ S` is locally of finite presentation if and only
if it is of finite presentation at every point of `X`. -/
theorem locallyOfFinitePresentation_iff_forall_finitePresentationAt :
    LocallyOfFinitePresentation f ↔ ∀ x : X, f.FinitePresentationAt x := sorry

/-- The source-style affine-neighborhood owner for finite presentation agrees with the canonical
owner `LocallyOfFinitePresentation`. -/
theorem locallyOfFinitePresentation_iff_locallyOfType :
    LocallyOfFinitePresentation f ↔ LocallyOfType RingHom.FinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally (P := @LocallyOfFinitePresentation)]
  exact (AlgebraicGeometry.locallyOfType_iff_affineLocally
    RingHom.FinitePresentation f RingHom.finitePresentation_isLocal).symm

/-- Definition 29.21.1 (3): a morphism `f : X ⟶ S` is of finite presentation if it is locally of
finite presentation, quasi-compact, and quasi-separated. -/
class FinitePresentation : Prop extends
    LocallyOfFinitePresentation f,
    QuasiCompact f,
    QuasiSeparated f

/-- Finite-presentation structures are proposition-valued. -/
instance instSubsingletonFinitePresentation :
    Subsingleton (FinitePresentation f) :=
  inferInstance

/-- A morphism of finite presentation is locally of finite presentation. -/
instance instLocallyOfFinitePresentationOfFinitePresentation [h : FinitePresentation f] :
    LocallyOfFinitePresentation f :=
  h.toLocallyOfFinitePresentation

/-- A morphism of finite presentation is quasi-compact. -/
instance instQuasiCompactOfFinitePresentation [h : FinitePresentation f] :
    QuasiCompact f :=
  h.toQuasiCompact

/-- A morphism of finite presentation is quasi-separated. -/
instance instQuasiSeparatedOfFinitePresentation [h : FinitePresentation f] :
    QuasiSeparated f :=
  h.toQuasiSeparated

/-- Unfold `FinitePresentation` into local finite presentation, quasi-compactness, and
quasi-separatedness. -/
theorem finitePresentation_iff :
    FinitePresentation f ↔
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f := sorry

/-- Unfold the scheme-side finite-presentation condition into quasi-compactness,
quasi-separatedness, and the pointwise finite-presentation-at condition. -/
theorem finitePresentation_iff_quasiCompact_and_quasiSeparated_and_forall_finitePresentationAt :
    FinitePresentation f ↔
      (QuasiCompact f ∧ QuasiSeparated f ∧ ∀ x : X, f.FinitePresentationAt x) := sorry

end Scheme.Hom
end AlgebraicGeometry
