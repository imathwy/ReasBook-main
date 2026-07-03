import Mathlib
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_3_1 (from Chap13) -/
namespace CategoryTheory.Pretriangulated

/- Domain-style sampling for Definition 13.3.1:
- primary domain: triangles in a category with shift, together with morphisms between such
  triangles;
- sampled core/canonical declarations:
  `Triangle`,
  `Triangle.mk`,
  `TriangleMorphism`,
  `Triangle.homMk`;
- primary owner abstraction: `Triangle`;
- companion morphism owner: `TriangleMorphism`;
- primitive data: the triangle object itself and, separately, the triple of component morphisms
  with the three commutative-square conditions for a morphism of triangles;
- derived API: `Triangle.mk` and `Triangle.homMk`, along with the induced category structure on
  triangles;
- source/core/bridge triage:
  `source-facing`: triangles `X ⟶ Y ⟶ Z ⟶ X[1]` and morphisms between them;
  `core/canonical`: `Triangle` and `TriangleMorphism`;
  `bridge/view`: the constructor API `Triangle.mk`/`Triangle.homMk` and later distinguished-triangle
    structure built on top of these owners.

Definition 13.3.1 is therefore a pure recall of the existing canonical owners, not a place for a
parallel local triangle or triangle-morphism wrapper. -/

/- Definition 13.3.1: the basic object `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is the canonical owner `Triangle`. -/
recall Triangle

/- Companion check: the source-facing display `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is built by the canonical
constructor `Triangle.mk`, so no parallel local triangle package is needed. -/
#check Triangle.mk

/- Companion recall: a morphism between such triangles is the canonical owner
`TriangleMorphism`. -/
recall TriangleMorphism

/- Companion check: the commutative-diagram data for a morphism of triangles is assembled by the
canonical constructor `Triangle.homMk`, so the file should not keep a duplicate local morphism
wrapper. -/
#check Triangle.homMk

end CategoryTheory.Pretriangulated

/-! ### Definition_13_3_2 (from Chap13) -/
namespace CategoryTheory

/- Domain-style sampling:
- primary domain: triangulated categories, organized around distinguished triangles and the
  octahedron axiom;
- relevant upstream owner declarations in this domain:
  `Pretriangulated`,
  `Pretriangulated.distinguishedTriangles`,
  `IsTriangulated`,
  `IsTriangulated.mk'`;
- source/core/bridge triage:
  `source-facing`: the Stacks definition of a triangulated category via distinguished triangles
    satisfying TR1--TR4;
  `core/canonical`: `Pretriangulated` for the distinguished-triangle data with TR1--TR3, and
    `IsTriangulated` for adding TR4;
  `bridge/view`: `distTriang` as the induced distinguished-triangle owner and
    `IsTriangulated.mk'` as the canonical constructor used downstream to verify TR4.

Primitive data is the pretriangulated structure; the octahedron axiom is derived as the extra
owner proposition `IsTriangulated`. Definition 13.3.2 is therefore a pure recall of the existing
canonical owners, not a place for any local wrapper or duplicate predicate.
-/

/- Definition 13.3.2: in mathlib, the choice of distinguished triangles together with
axioms TR1, TR2, and TR3 is packaged by `Pretriangulated`, and a
triangulated category is obtained by adding the octahedron axiom TR4, formalized by the
canonical class `IsTriangulated`. -/
recall IsTriangulated

/- Companion recall: the pre-triangulated part of the definition, namely the distinguished
triangles satisfying TR1, TR2, and TR3, is formalized by the canonical class
`Pretriangulated`. -/
recall Pretriangulated

end CategoryTheory

/-! ### Definition_13_3_3 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasShift C ℤ] [HasShift D ℤ]

/- Domain-style sampling for Definition 13.3.3:
- primary domain: triangulated functors between categories with shift by `ℤ`;
- sampled core/canonical declarations:
  `Functor.CommShift`,
  `Functor.IsTriangulated`,
  `Functor.mapTriangle`,
  `Functor.mapTriangleCompIso`;
- best owner abstraction: exactness is owned canonically by the pair of functor-level structures
  `[F.CommShift ℤ]` and `[F.IsTriangulated]`, with `Functor.IsTriangulated` carrying the actual
  distinguished-triangle preservation property and `Functor.CommShift ℤ` as the primitive
  shift-compatibility data it depends on;
- primitive data: a functor `F : C ⥤ D` together with the shift-commuting structure
  `[F.CommShift ℤ]`;
- derived API: `F.mapTriangle`, the induced exactness/additivity instances, and the composition
  compatibility supplied upstream by `mapTriangleCompIso` and the standard composite instances;
- source/core/bridge triage:
  `source-facing`: the Stacks notion of an exact functor between pretriangulated categories;
  `core/canonical`: `Functor.CommShift` and `Functor.IsTriangulated`;
  `bridge/view`: the induced functor on triangles and the composition/isomorphism API built from
    those owners.

Definition 13.3.3 is therefore a pure recall of the canonical owner declarations, not a place
for a local wrapper predicate or duplicate exact-functor structure. -/

/- The primitive shift-compatibility data in the definition of an exact functor is the canonical
`Functor.CommShift ℤ` structure. -/
recall Functor.CommShift

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ]

/- Definition 13.3.3: once the shift-commuting data is fixed, the exactness condition for a
functor between pre-triangulated categories is the canonical predicate
`Functor.IsTriangulated`. -/
recall Functor.IsTriangulated

end

end CategoryTheory

/-! ### Definition_13_3_4 (from Chap13) -/
universe v u

namespace CategoryTheory.ObjectProperty

open Limits

/- Domain-style sampling for Definition 13.3.4:
- primary domain: triangulated subcategories of a pretriangulated category, expressed as object
  properties stable under the canonical triangulated operations;
- sampled core/canonical declarations:
  `ObjectProperty.IsTriangulated`,
  `Pretriangulated P.FullSubcategory`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: `ObjectProperty.IsTriangulated P`;
- primitive data: only the object property `P : ObjectProperty C`;
- derived API: the induced pretriangulated structure on `P.FullSubcategory`, and, when the ambient
  category is triangulated, the induced triangulated structure on `P.FullSubcategory`;
- source/core/bridge triage:
  `source-facing`: the textbook notion of a pretriangulated subcategory of `C`;
  `core/canonical`: `ObjectProperty.IsTriangulated`;
  `bridge/view`: the full-subcategory realizations `Pretriangulated P.FullSubcategory` and
    `IsTriangulated P.FullSubcategory`.

No parallel local wrapper is needed: the source notion is already owned canonically by
`ObjectProperty.IsTriangulated`. -/

/- Definition 13.3.4: a pre-triangulated subcategory of a pre-triangulated category `C` is
formalized by the canonical owner predicate `ObjectProperty.IsTriangulated` on an object property
`P : ObjectProperty C`. -/
recall IsTriangulated

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  [P.IsTriangulated]

/- Companion recall: a triangulated object property induces the canonical pretriangulated
structure on the full subcategory `P.FullSubcategory`. -/
#check (inferInstance : Pretriangulated P.FullSubcategory)

/-- A triangulated object property in a preadditive pretriangulated category is closed under
binary coproducts. This is the binary-coproduct companion to the existing binary-product owner
instance from mathlib's triangulated-subcategory API. -/
instance [P.IsClosedUnderIsomorphisms] : P.IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let X₁ := p.diag.obj (.mk .left)
    let X₂ := p.diag.obj (.mk .right)
    let B : BinaryCofan X₁ X₂ := BinaryCofan.mk (p.ι.app (.mk .left)) (p.ι.app (.mk .right))
    have hB : IsColimit B := by
      let hp := ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm p.cocone).2 p.isColimit)
      simpa [B, BinaryCofan.inl, BinaryCofan.inr] using
        (IsColimit.ofIsoColimit hp (isoBinaryCofanMk _))
    have e : X ≅ X₁ ⨿ X₂ := by
      simpa [B] using hB.coconePointUniqueUpToIso (coprodIsCoprod X₁ X₂)
    let _ : HasBinaryBiproduct X₁ X₂ := HasBinaryBiproduct.of_hasBinaryCoproduct X₁ X₂
    exact P.prop_of_iso e.symm <|
      P.prop_of_iso (biprodIso X₁ X₂) <|
        P.prop_prod X₁ X₂
          (by simpa [X₁] using p.prop_diag_obj (.mk .left))
          (by simpa [X₂] using p.prop_diag_obj (.mk .right))

/-- A triangulated object property in a preadditive pretriangulated category is closed under
finite coproducts. This is the finite-coproduct companion to the binary-coproduct bridge above. -/
instance [P.IsClosedUnderIsomorphisms] : P.IsClosedUnderFiniteCoproducts := by
  let _ : P.IsClosedUnderBinaryCoproducts := inferInstance
  exact IsClosedUnderFiniteCoproducts.mk'

variable [IsTriangulated C]

/- Companion recall: if the ambient category is triangulated, the induced full subcategory is
triangulated in the usual sense. -/
#check (inferInstance : IsTriangulated P.FullSubcategory)

end

end CategoryTheory.ObjectProperty

/-! ### Definition_13_3_5 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]

/- Domain-style sampling for Definition 13.3.5:
- primary domain: homological functors from pretriangulated categories to abelian categories, and
  the contravariant/cohomological view obtained by passing to opposites;
- sampled core/canonical declarations:
  `Functor.IsHomological`,
  `Functor.map_distinguished_exact`,
  `Functor.rightOp`;
- best owner abstraction: `Functor.IsHomological`;
- primitive data: only the functor itself; homologicality/cohomologicality is a property, not
  additional packaged data;
- derived API: exactness on distinguished triangles, shift-sequence long exact sequences, and the
  contravariant cohomological view via `H.rightOp`, together with the generic bridge instance
  turning `[H.IsHomological]` into `[H.rightOp.IsHomological]`;
- source/core/bridge triage:
`source-facing`: the Stacks notion of a cohomological contravariant functor `H : Dᵒᵖ ⥤ A`;
  `core/canonical`: `Functor.IsHomological`;
  `bridge/view`: the passage from `H` to `H.rightOp : D ⥤ Aᵒᵖ`.

No local `IsCohomological` wrapper is needed here: the source notion is exactly the canonical
homological owner applied to the opposite-valued functor. -/

/- Definition 13.3.5 first recalls the covariant owner: the Stacks notion of a homological
functor `H : D ⥤ A` is the canonical predicate `Functor.IsHomological`. In this setting, the
exactness on distinguished triangles is primitive for the owner, and additivity is derived from
that owner rather than extra packaged data. -/
recall Functor.IsHomological

/- Companion recall: the defining exactness statement for the canonical owner is exposed by
`Functor.map_distinguished_exact`. -/
#check Functor.map_distinguished_exact

/- Companion recall: the contravariant source-facing functor `H : Dᵒᵖ ⥤ A` is converted to the
opposite-valued covariant functor by the canonical bridge `Functor.rightOp`. -/
variable (H : Dᵒᵖ ⥤ A) in
#check H.rightOp

/- Definition 13.3.5: for a contravariant functor `H : Dᵒᵖ ⥤ A`, the Stacks condition
"cohomological" is exactly the canonical homologicality condition on the opposite-valued
functor `H.rightOp : D ⥤ Aᵒᵖ`. -/
variable (H : Dᵒᵖ ⥤ A) in
#check H.rightOp.IsHomological

namespace Functor

open Pretriangulated.Opposite

/- Companion bridge: if `H : Dᵒᵖ ⥤ A` is homological on the opposite category, then its
opposite-valued covariant view `H.rightOp : D ⥤ Aᵒᵖ` is homological. This keeps the cohomological
source-facing reading attached to the canonical owner rather than to a separate local wrapper. -/
instance (H : Dᵒᵖ ⥤ A) [H.IsHomological] : H.rightOp.IsHomological := by
  refine ⟨fun T hT ↦ ?_⟩
  change (((Pretriangulated.shortComplexOfDistTriangle T hT).op.map H).op).Exact
  exact (H.map_distinguished_op_exact T hT).op

end Functor

end CategoryTheory

/-! ### Definition_13_3_6 (from Chap13) -/
namespace CategoryTheory

open Limits
open CategoryTheory.Pretriangulated

universe vA uA vD uD

variable {A : Type uA} {D : Type uD} [Category.{vA} A] [Abelian A]
  [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

section

/- Domain-style sampling for Definition 13.3.6:
- primary domain: short exact sequences in an abelian category mapped to distinguished triangles in
  a pretriangulated category;
- inspected nearby canonical declarations in this domain:
  `ShortComplex.ShortExact`,
  `Triangle.mk`,
  `distTriang`,
  `Functor.IsHomological`;
- best owner abstraction: there is no upstream owner for this source-facing notion, so the file
  itself must own `DeltaFunctor`;
- primitive data: the inherited functor, the connecting morphism for each short exact sequence,
  additivity of that functor, the connecting morphism for each short exact sequence,
  distinguishedness of the induced triangle, and naturality for morphisms of short exact
  sequences;
- derived API: the inherited functor projections `obj` and `map`, and the associated triangle
  attached to a short exact sequence;
- source/core/bridge triage:
  `source-facing`: `DeltaFunctor`;
  `core/canonical`: the canonical triangle and short-exact-sequence owners `Triangle.mk`,
    `distTriang`, and `ShortComplex.ShortExact`;
  `bridge/view`: `Functor.IsHomological` on the target side, used later to extract long exact
    sequences from the distinguished triangles carried by a `DeltaFunctor`.

The owner only needs the pretriangulated distinguished-triangle structure on `D`; the stronger
`IsTriangulated D` hypothesis is not primitive data for this definition. The associated triangle
is derived API from the owner, not a second packaged notion. -/

/-- Definition 13.3.6: A `δ`-functor from an abelian category `A` to a pretriangulated category
`D` consists of an additive functor `A ⥤ D` together with a connecting morphism for every short
exact sequence in `A`, such that the associated triangle is distinguished and these connecting
morphisms are natural in morphisms of short exact sequences. -/
structure DeltaFunctor (A : Type uA) [Category.{vA} A] [Abelian A]
    (D : Type uD) [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] extends A ⥤ D where
  /-- The underlying functor of a `δ`-functor is additive. -/
  additive : toFunctor.Additive
  /-- The connecting morphism attached to a short exact sequence in `A`. -/
  δ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    obj S.X₃ ⟶ (obj S.X₁)⟦(1 : ℤ)⟧
  /-- The triangle obtained from a short exact sequence by the `δ`-functor is distinguished. -/
  map_distinguished ⦃S : ShortComplex A⦄ (hS : S.ShortExact) :
    Triangle.mk (map S.f) (map S.g) (δ hS) ∈ distTriang D
  /-- The connecting morphisms commute with morphisms of short exact sequences. -/
  δ_naturality ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T) :
    CommSq (map φ.τ₃) (δ hS) (δ hT) ((map φ.τ₁)⟦(1 : ℤ)⟧')

namespace DeltaFunctor

variable (F : DeltaFunctor A D)

instance : F.toFunctor.Additive := F.additive

/-- The triangle attached by a `δ`-functor to a short exact sequence. -/
def triangle {S : ShortComplex A} (hS : S.ShortExact) : Triangle D :=
  Triangle.mk (F.map S.f) (F.map S.g) (F.δ hS)

/-- A morphism of short exact sequences induces a morphism between the attached triangles. -/
@[simps]
def triangleMap {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    F.triangle hS ⟶ F.triangle hT :=
  Triangle.homMk _ _ (F.map φ.τ₁) (F.map φ.τ₂) (F.map φ.τ₃)
    (by
      simpa only [Functor.map_comp] using
        congrArg (fun f ↦ F.map f) φ.comm₁₂.symm)
    (by
      simpa only [Functor.map_comp] using
        congrArg (fun g ↦ F.map g) φ.comm₂₃.symm)
    (by
      simpa [triangle] using (F.δ_naturality hS hT φ).w.symm)

/-- The triangle attached to a short exact sequence by a `δ`-functor is distinguished. -/
theorem triangle_distinguished {S : ShortComplex A} (hS : S.ShortExact) :
    F.triangle hS ∈ distTriang D :=
  F.map_distinguished hS

end DeltaFunctor

end

end CategoryTheory
