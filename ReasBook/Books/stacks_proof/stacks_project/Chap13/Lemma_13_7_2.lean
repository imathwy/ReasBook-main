import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Adjunction

section

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable {F : D ⥤ D'} {G : D' ⥤ D}
  [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]

/- Domain-style sampling for Lemma 13.7.2:
- primary domain: adjunctions between pretriangulated categories and equivalence criteria detected
  by the counit triangle;
- sampled owner declarations:
  `Adjunction.rightAdjointCommShift`,
  `Adjunction.commShift_of_leftAdjoint`,
  `Adjunction.isTriangulated_rightAdjoint`,
  `Adjunction.unit_isIso_of_L_fully_faithful`,
  `Adjunction.mem_essImage_of_counit_isIso`,
  `Functor.EssSurj`,
  `Adjunction.toEquivalence`,
  `Functor.IsEquivalence`,
  `Functor.kernel`,
  `Triangle.isZero₃_of_isIso₁`;
- source-facing layer: the Stacks lemma upgrading a fully faithful exact left adjoint to an
  equivalence when the right adjoint has zero kernel;
- core/canonical owners: `Functor.EssSurj` and `Functor.IsEquivalence` for the equivalence
  criterion, `CategoryTheory.Adjunction` for the exact right-adjoint data and the counit-to-
  essential-image bridge, `Functor.kernel` for the conservative hypothesis, and the canonical
  triangle owner theorem `Triangle.isZero₃_of_isIso₁` on the mapped counit triangle;
- bridge/view: derive exactness of `G` from exactness of `F` using the canonical adjunction
  owners from Lemma `13.7.1`, complete each counit component to a distinguished triangle, apply
  the triangulated right adjoint, use the triangle owner API to see the cone term is sent to zero,
  use `G.kernel ≤ IsZero` to identify the cone term itself as zero, and then pass from the counit
  isomorphism to the essential-image owner via `Adjunction.mem_essImage_of_counit_isIso`.

Primitive data are exactly the adjunction `adj`, exactness of the left adjoint `F`, and the
kernel hypothesis `hker`. The right-adjoint exactness data, the unit isomorphism from full
faithfulness of `F`, the counit-isomorphism test, essential surjectivity of `F`, and the
resulting equivalence are all derived API already owned by `Adjunction` or `Functor`, so this
file should keep only the source-facing theorem and the owner-level essential-surjectivity bridge.
-/

-- Proof sketch: by Lemma 13.7.1, encoded by `Adjunction.rightAdjointCommShift`,
-- `Adjunction.commShift_of_leftAdjoint`, and `Adjunction.isTriangulated_rightAdjoint`, the right
-- adjoint `G` is exact because the left adjoint `F` is exact. By Lemma 4.24.4, full faithfulness
-- of `F` makes the unit `𝟭 D ⟶ F ⋙ G` an isomorphism. For any `X : D'`, complete the counit map
-- `F.obj (G.obj X) ⟶ X` to a distinguished triangle and apply `G`. The first map in the resulting
-- triangle is an isomorphism, so the canonical triangle owner API shows the cone term is sent to
-- zero by `G`; the kernel hypothesis forces that cone term itself to be zero, hence the counit at
-- `X` is an isomorphism.
/-- If `F ⊣ G`, the left adjoint `F` is fully faithful, and `G` has zero kernel, then each counit
component of the adjunction is an isomorphism. This is the canonical bridge from the zero-kernel
hypothesis to the adjunction-owner counit criterion for essential image. -/
theorem isIso_counit_app_of_kernel_le_isZero
    (adj : F ⊣ G) (hker : G.kernel ≤ IsZero) (X : D') :
    IsIso (adj.counit.app X) := by
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  letI := adj.isTriangulated_rightAdjoint
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adj.counit.app X)
  let T : Triangle D' := .mk (adj.counit.app X) g h
  let GT : Triangle D := G.mapTriangle.obj T
  have hGT : GT ∈ distTriang D := by
    simpa [GT, T] using G.map_distinguished T hT
  have hGZ : IsZero (G.obj Z) := by
    exact Triangle.isZero₃_of_isIso₁ GT hGT <| by
      simpa [GT, T] using
        (show IsIso (G.map (adj.counit.app X)) by infer_instance)
  have hZ : IsZero Z := hker Z hGZ
  simpa [T] using (Triangle.isZero₃_iff_isIso₁ T hT).1 hZ

/-- If `F ⊣ G`, the left adjoint `F` is fully faithful, and `G` has zero kernel, then `F` is
essentially surjective. This is the owner-level bridge from the kernel hypothesis on `G` to the
canonical equivalence owner data for `F`. -/
theorem essSurj_of_kernel_le_isZero
    (adj : F ⊣ G) (hker : G.kernel ≤ IsZero) :
    F.EssSurj := by
  refine ⟨fun X ↦ ?_⟩
  letI : IsIso (adj.counit.app X) := isIso_counit_app_of_kernel_le_isZero adj hker X
  exact adj.mem_essImage_of_counit_isIso X

/-- Lemma 13.7.2 in adjunction-owner form: if the left adjoint `F` is fully faithful, the right
adjoint `G` has zero kernel, formalized as `G.kernel ≤ IsZero`, then an exact fully faithful left
adjoint `F` is an equivalence of categories. The public bridge lands first in the canonical owner
`F.EssSurj`, and the equivalence then follows from the standard owner fields `Faithful`, `Full`,
and `EssSurj`. -/
@[stacks 09J1]
theorem isEquivalence_of_fullyFaithful_of_kernel_le_isZero
    (adj : F ⊣ G) (hker : G.kernel ≤ IsZero) :
    F.IsEquivalence := by
  letI : F.EssSurj := essSurj_of_kernel_le_isZero adj hker
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

end

end Adjunction
end CategoryTheory
