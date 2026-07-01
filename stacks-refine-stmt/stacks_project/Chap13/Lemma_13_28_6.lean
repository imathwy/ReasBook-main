import Mathlib
import stacks_project.Chap13.Definition_13_28_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂ v₃ u₃

set_option checkBinderAnnotations false

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.28.6:
- primary domain: pretriangulated Grothendieck groups and exact-functor functoriality/bilinear
  pairings;
- sampled owner declarations:
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.TriangulatedK0.of`,
  `CategoryTheory.TriangulatedK0.lift`,
  `CategoryTheory.TriangulatedK0.map`,
  `CategoryTheory.TriangulatedK0.map_of`;
- source-facing layer: Lemma 13.28.6 is the bilinear `K₀` pairing induced by a bifunctor that is
  triangulated in each variable;
- core/canonical owner: `CategoryTheory.TriangulatedK0.tensorBilinear`;
- bridge/view: partial evaluation at a class is identified with the upstream one-variable owner
  `CategoryTheory.TriangulatedK0.map`; the source-facing class-evaluation formula is then derived
  directly from that owner.

Primitive data are only the bifunctor and its exactness in each variable. The one-variable `K₀`
map is already owned upstream by `CategoryTheory.TriangulatedK0.map` from
`Definition_13_28_1`, so this file should reuse that owner and keep only the genuinely bilinear
quotient descent.
-/

namespace TriangulatedK0

section TensorK0

variable {D₁ : Type u₁} [Category.{v₁} D₁] [Preadditive D₁] [HasZeroObject D₁] [HasShift D₁ ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D₁ n)] [Pretriangulated D₁]
variable {D₂ : Type u₂} [Category.{v₂} D₂] [Preadditive D₂] [HasZeroObject D₂] [HasShift D₂ ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D₂ n)] [Pretriangulated D₂]
variable {D₃ : Type u₃} [Category.{v₃} D₃] [Preadditive D₃] [HasZeroObject D₃] [HasShift D₃ ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D₃ n)] [Pretriangulated D₃]

variable (tensor : D₁ ⥤ D₂ ⥤ D₃)
variable [∀ X : D₁, (tensor.obj X).CommShift ℤ]
variable [∀ X : D₁, (tensor.obj X).IsTriangulated]
variable [∀ X : D₂, (tensor.flip.obj X).CommShift ℤ]
variable [∀ X : D₂, (tensor.flip.obj X).IsTriangulated]

-- Proof sketch: for a distinguished triangle in `D₁`, evaluate the corresponding element of the
-- raw map at an arbitrary class `[X']` in `K₀(D₂)`. The result is the distinguished-triangle
-- relation in `K₀(D₃)` coming from the exact functor `- ⊗ X'`.
/-- The distinguished-triangle relations in `D₁` lie in the kernel of the raw tensor pairing. -/
private theorem relations_le_ker_tensor :
    relations D₁ ≤ (FreeAbelianGroup.lift fun X ↦ map (tensor.obj X)).ker := by
  rw [relations, AddSubgroup.closure_le]
  rintro _ ⟨T, rfl⟩
  rcases T with ⟨T, hT⟩
  change
    (FreeAbelianGroup.lift fun X ↦ map (tensor.obj X))
        (FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ - FreeAbelianGroup.of T.obj₃) = 0
  apply AddMonoidHom.ext
  intro a
  induction a using QuotientAddGroup.induction_on with
  | H z =>
      change
        ((FreeAbelianGroup.lift fun X ↦ map (tensor.obj X))
            (FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ -
              FreeAbelianGroup.of T.obj₃))
          (QuotientAddGroup.mk' (relations D₂) z) = 0
      induction z using FreeAbelianGroup.induction_on with
      | zero =>
          simp
      | of X =>
          change
            map (tensor.obj T.obj₂) (of X) - map (tensor.obj T.obj₁) (of X) -
              map (tensor.obj T.obj₃) (of X) = 0
          rw [map_of, map_of, map_of]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            sub_eq_zero.mpr
              (of_distinguished
                ((tensor.flip.obj X).mapTriangle.obj T)
                ((tensor.flip.obj X).map_distinguished T hT))
      | neg X hX =>
          change
            map (tensor.obj T.obj₂) (-of X) - map (tensor.obj T.obj₁) (-of X) -
              map (tensor.obj T.obj₃) (-of X) = 0
          rw [map_neg, map_neg, map_neg]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hX
      | add x y hx hy =>
          rw [(QuotientAddGroup.mk' (relations D₂)).map_add, map_add]
          rw [hx, hy]
          simp

/-- Lemma 13.28.6: a bifunctor `⊗ : D × D' ⥤ D''` that is triangulated in each variable induces
the bilinear map on zeroth K-groups sending `([X], [X'])` to `[X ⊗ X']`. -/
def tensorBilinear : TriangulatedK0 D₁ →+ TriangulatedK0 D₂ →+ TriangulatedK0 D₃ :=
  lift (fun X ↦ map (tensor.obj X)) (relations_le_ker_tensor tensor)

/-- Fixing the left class in the bilinear pairing recovers the exact-functoriality map induced by
`tensor.obj X`. -/
@[simp] theorem tensorBilinear_of (X : D₁) :
    tensorBilinear tensor (of X) = map (tensor.obj X) := by
  simpa [tensorBilinear] using
    lift_of (fun Y ↦ map (tensor.obj Y)) (relations_le_ker_tensor tensor) X

/-- The bilinear pairing induced by `tensor` sends the classes of `X` and `X'` to the class of
`X ⊗ X'`. -/
@[simp] theorem tensorBilinear_of_of (X : D₁) (X' : D₂) :
    tensorBilinear tensor (of X) (of X') = of ((tensor.obj X).obj X') := by
  rw [tensorBilinear_of, map_of]

/-- Fixing the right class in the bilinear pairing recovers the exact-functoriality map induced by
`tensor.flip.obj X'`. -/
@[simp] theorem flip_tensorBilinear_of (X' : D₂) :
    AddMonoidHom.flip (tensorBilinear tensor) (of X') = map (tensor.flip.obj X') := by
  ext X
  simpa using tensorBilinear_of_of tensor X X'

end TensorK0

end TriangulatedK0

end CategoryTheory
