import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_4_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Pretriangulated

universe v u

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/- Domain-style sampling:
- primary domain: distinguished triangles in pretriangulated categories;
- sampled canonical declarations:
  `Pretriangulated.distinguishedTriangles`,
  `comp_distTriang_mor_zero₁₂`,
  `comp_distTriang_mor_zero₂₃`,
  `comp_distTriang_mor_zero₃₁`;
- best owner abstraction: the canonical owner declaration is
  `Pretriangulated.distinguishedTriangles`, with project-facing notation `distTriang C`, so the
  owner-level hypothesis is `hT : T ∈ distTriang C`;
- primitive data: a triangle `T` together with the owner-level hypothesis `hT : T ∈ distTriang C`;
- derived API: the three vanishing composites of consecutive morphisms in a distinguished triangle;
- source/core/bridge triage:
  `source-facing`: Stacks Lemma 13.4.1, asserting that the three consecutive composites in a
    distinguished triangle vanish;
  `core/canonical`: the owner `Pretriangulated.distinguishedTriangles`, surfaced as `distTriang C`,
    and the three canonical vanishing theorems above;
  `bridge/view`: none needed, because the textbook statements already coincide with the canonical
    owner-level API.

Primitive data already lives upstream in `Pretriangulated`, so this file should expose the owner
directly and recall the three canonical consequences rather than introducing any parallel local
lemma wrappers.
-/

/- The owner for Lemma 13.4.1 is the canonical distinguished-triangle predicate `distTriang`. -/
#check (distTriang C)

/- Lemma 13.4.1 (1): if `(X, Y, Z, f, g, h)` is a distinguished triangle in a pretriangulated
category, then `g ∘ f = 0`. This is exactly the canonical theorem
`comp_distTriang_mor_zero₁₂`. -/
recall comp_distTriang_mor_zero₁₂

/- Lemma 13.4.1 (2): if `(X, Y, Z, f, g, h)` is a distinguished triangle in a pretriangulated
category, then `h ∘ g = 0`. This is exactly the canonical theorem
`comp_distTriang_mor_zero₂₃`. -/
recall comp_distTriang_mor_zero₂₃

/- Lemma 13.4.1 (3): if `(X, Y, Z, f, g, h)` is a distinguished triangle in a pretriangulated
category, then `f[1] ∘ h = 0`, which in Lean is the vanishing
`T.mor₃ ≫ T.mor₁⟦1⟧' = 0`. This is exactly the canonical theorem
`comp_distTriang_mor_zero₃₁`. -/
recall comp_distTriang_mor_zero₃₁

end

/-! ### Lemma_13_4_2 (from Chap13) -/
universe v u

namespace CategoryTheory

open Limits Opposite
open scoped Pretriangulated.Opposite

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.2:
- primary domain: represented Hom functors on a pretriangulated category and their
  homological/cohomological exactness;
- sampled declarations:
  `Functor.IsHomological`,
  `preadditiveCoyoneda.obj`,
  `preadditiveYoneda.obj`,
  `Functor.rightOp`;
- best owner abstraction: `Functor.IsHomological`;
- primitive data: only the represented functor itself;
- derived API: the homologicality instances of `preadditiveCoyoneda.obj (op W)` and
  `(preadditiveYoneda.obj W).rightOp`;
- source/core/bridge triage:
  `source-facing`: the contravariant cohomological statement for `preadditiveYoneda.obj W`;
  `core/canonical`: the mathlib `Functor.IsHomological` instances on the represented Hom functors;
  `bridge/view`: the chapter-level generic instance on `Functor.rightOp`, applied to
    `preadditiveYoneda.obj W`.

Both parts of the lemma are therefore direct recall items: the covariant case from mathlib's
represented-Hom owner instance, and the contravariant case from the chapter's generic
`Functor.rightOp` bridge to the same owner. -/

variable (W : D)

/- Lemma 13.4.2 (1): for any object `W` of a pretriangulated category, the covariant Hom functor
`Hom_D(W,-)`, represented by `preadditiveCoyoneda.obj (op W)`, is homological. This is exactly the
canonical instance in `CategoryTheory.Triangulated.Yoneda`. -/
#synth (preadditiveCoyoneda.obj (op W)).IsHomological

/- Lemma 13.4.2 (2): for any object `W` of a pretriangulated category, the contravariant Hom
functor `Hom_D(-,W)`, represented by `preadditiveYoneda.obj W`, is cohomological; equivalently,
its opposite-valued functor is homological. This is likewise already inferable from the canonical
owner infrastructure. -/
#synth (preadditiveYoneda.obj W).rightOp.IsHomological

end CategoryTheory

/-! ### Lemma_13_4_3 (from Chap13) -/
namespace CategoryTheory
namespace Pretriangulated

/- Domain-style sampling:
- primary domain: morphisms of distinguished triangles in a pretriangulated category and the
  triangle-level two-out-of-three isomorphism principle;
- sampled upstream owner declarations:
  `Triangle`,
  `TriangleMorphism`,
  `isIso₂_of_isIso₁₃`,
  `isIso₃_of_isIso₁₂`,
  `isIso₁_of_isIso₂₃`;
- best owner abstraction:
  `source-facing`: the three Stacks clauses asserting that in a morphism of distinguished
    triangles, any two isomorphic components force the third to be an isomorphism;
  `core/canonical`: the owner lemmas `isIso₂_of_isIso₁₃`, `isIso₃_of_isIso₁₂`, and
    `isIso₁_of_isIso₂₃` in `CategoryTheory.Pretriangulated`;
  `bridge/view`: none, because the source statements already coincide with the canonical
    owner-level theorems.

Primitive data are only the triangle morphism and the distinguishedness assumptions on its source
and target triangles. The isomorphism conclusion for the remaining component is derived API from
the canonical owner lemmas, so this file should remain a pure recall file with no parallel local
wrapper declarations.
-/

/- Lemma 13.4.3 (1): for a morphism of distinguished triangles in a pre-triangulated category, if
the first and third components are isomorphisms, then the second component is an isomorphism.
This is exactly the canonical theorem `isIso₂_of_isIso₁₃`. -/
recall isIso₂_of_isIso₁₃

/- Lemma 13.4.3 (2): for a morphism of distinguished triangles in a pre-triangulated category, if
the first and second components are isomorphisms, then the third component is an isomorphism.
This is exactly the canonical theorem `isIso₃_of_isIso₁₂`. -/
recall isIso₃_of_isIso₁₂

/- Lemma 13.4.3 (3): for a morphism of distinguished triangles in a pre-triangulated category, if
the second and third components are isomorphisms, then the first component is an isomorphism.
This is exactly the canonical theorem `isIso₁_of_isIso₂₃`. -/
recall isIso₁_of_isIso₂₃

end Pretriangulated
end CategoryTheory

/-! ### Remark_13_4_4 (from Chap13) -/
universe v u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Opposite

namespace CategoryTheory
namespace Pretriangulated

variable {D : Type u} [Category.{v} D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

/- Domain-style sampling for Remark 13.4.4:
- primary domain: exactness properties of shifted covariant and contravariant Hom-sequences
  attached to triangles, together with the triangle-level two-out-of-three isomorphism principle;
- sampled upstream owner declarations:
  `Triangle.shiftFunctor`,
  `Triangle.rotate`,
  `Triangle.yoneda_exact₂`,
  `Triangle.yoneda_exact₃`,
  `Triangle.coyoneda_exact₁`,
  `Triangle.coyoneda_exact₂`,
  `Triangle.coyoneda_exact₃`,
  `Pretriangulated.preadditiveYoneda_map_distinguished`,
  `Pretriangulated.isIso₂_of_isIso₁₃`,
  `triangleOpEquivalence`;
- best owner abstraction:
  `source-facing`: the Stacks notion of a special triangle, as a property of a single triangle;
  `core/canonical`: the owner `Triangle D`, together with its shift, rotation, and opposite
    equivalence APIs;
  `bridge/view`: co-speciality is the opposite-category reformulation of speciality via
    `triangleOpEquivalence`, and distinguished triangles imply speciality via
    `Triangle.shift_distinguished` and the owner exactness lemmas.

Primitive data vs derived API:
- primitive data: for a source-facing special triangle, the exactness of the three shifted
  Hom-map pairs for `Hom_D(W,-)`;
- derived API: the factorization lemmas `coyoneda_exact₁/₂/₃`, the zero-composite companion lemmas
  `zero₁₂/₂₃/₃₁`, the distinguished-triangle bridge instances, the thin opposite-category
  co-special view giving `yoneda_exact₁/₂/₃`, and the two-out-of-three isomorphism consequences.
-/

namespace Triangle

/-- Remark 13.4.4: a triangle is special when, for every object `W`, the long covariant Hom
sequence `Hom_D(W,-)` attached to every shifted triangle `T⟦n⟧` is exact. Here this is recorded by
the three exact shifted Hom-map pairs attached to `T⟦n⟧`; the successive zero composites are
derived below from `Function.Exact.comp_eq_zero`. -/
class IsSpecial (T : Triangle D) : Prop where
  exact₂ (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₁))
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₂))
  exact₃ (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₂))
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₃))
  exact₁ (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T⟦n⟧ : Triangle D).mor₃))
      ((preadditiveCoyoneda.obj (op W)).map (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧'))

namespace IsSpecial

variable {T : Triangle D}

/-- Helper for Remark 13.4.4: if `e : T ≅ T'` is a triangle isomorphism, then the first
commutative square can be rewritten using the inverse components. -/
lemma comm₁_inv {T' : Triangle D} (e : T ≅ T') :
    inv e.hom.hom₁ ≫ T.mor₁ = T'.mor₁ ≫ inv e.hom.hom₂ := by
  -- Postcompose the first commutative square with the inverse second component and simplify.
  simpa [Category.assoc] using
    congrArg (fun k => inv e.hom.hom₁ ≫ k ≫ inv e.hom.hom₂) e.hom.comm₁

/-- Helper for Remark 13.4.4: if `e : T ≅ T'` is a triangle isomorphism, then the second
commutative square can be rewritten using the inverse components. -/
lemma comm₂_inv {T' : Triangle D} (e : T ≅ T') :
    inv e.hom.hom₂ ≫ T.mor₂ = T'.mor₂ ≫ inv e.hom.hom₃ := by
  -- Postcompose the second commutative square with the inverse third component and simplify.
  simpa [Category.assoc] using
    congrArg (fun k => inv e.hom.hom₂ ≫ k ≫ inv e.hom.hom₃) e.hom.comm₂

/-- Helper for Remark 13.4.4: if `e : T ≅ T'` is a triangle isomorphism, then the third
commutative square can be rewritten using the inverse shifted first component. -/
lemma comm₃_inv {T' : Triangle D} (e : T ≅ T') :
    inv e.hom.hom₃ ≫ T.mor₃ = T'.mor₃ ≫ inv (e.hom.hom₁⟦(1 : ℤ)⟧') := by
  -- Postcompose the third commutative square with the inverse shifted first component.
  simpa [Category.assoc] using
    congrArg (fun k => inv e.hom.hom₃ ≫ k ≫ inv (e.hom.hom₁⟦(1 : ℤ)⟧')) e.hom.comm₃

/-- Helper for Remark 13.4.4: postcomposition with an isomorphism has the obvious left inverse on
covariant Hom groups. -/
lemma hom_add_equiv_left_inv {X Y : D} (W : D) (i : X ≅ Y) (f : W ⟶ X) :
    (f ≫ i.hom) ≫ i.inv = f := by
  -- Cancel the inverse pair inside the postcomposition expression.
  simp [Category.assoc]

/-- Helper for Remark 13.4.4: postcomposition with an isomorphism has the obvious right inverse on
covariant Hom groups. -/
lemma hom_add_equiv_right_inv {X Y : D} (W : D) (i : X ≅ Y) (g : W ⟶ Y) :
    (g ≫ i.inv) ≫ i.hom = g := by
  -- Cancel the inverse pair inside the postcomposition expression.
  simp [Category.assoc]

/-- Helper for Remark 13.4.4: postcomposition with an isomorphism is additive on covariant Hom
groups. -/
lemma hom_add_equiv_map_add {X Y : D} (W : D) (i : X ≅ Y) (f g : W ⟶ X) :
    (f + g) ≫ i.hom = f ≫ i.hom + g ≫ i.hom := by
  -- Functorial postcomposition respects the additive structure on morphisms.
  simp

/-- Helper for Remark 13.4.4: postcomposition with an isomorphism gives an additive equivalence on
covariant Hom groups. -/
noncomputable def hom_add_equiv {X Y : D} (W : D) (i : X ≅ Y) :
    (W ⟶ X) ≃+ (W ⟶ Y) :=
  { toFun := fun f => f ≫ i.hom
    invFun := fun g => g ≫ i.inv
    left_inv := hom_add_equiv_left_inv W i
    right_inv := hom_add_equiv_right_inv W i
    map_add' := hom_add_equiv_map_add W i }

/-- Helper for Remark 13.4.4: the covariant Yoneda map of a morphism, viewed as an
`AddMonoidHom` between the underlying Hom groups. -/
abbrev coyoneda_map_add_hom {X Y : D} (W : D) (f : X ⟶ Y) :
    ((preadditiveCoyoneda.obj (op W)).obj X) →+ ((preadditiveCoyoneda.obj (op W)).obj Y) :=
  ((preadditiveCoyoneda.obj (op W)).map f).hom

/-- Helper for Remark 13.4.4: evaluating the covariant Yoneda map of an isomorphism agrees with
ordinary postcomposition on Hom groups. -/
lemma coyoneda_map_hom_add_equiv_apply {X Y : D} (W : D) (i : X ≅ Y) (f : W ⟶ X) :
    ((preadditiveCoyoneda.obj (op W)).map i.hom) f = hom_add_equiv W i f :=
  rfl

/-- Helper for Remark 13.4.4: the covariant Hom-group equivalences induced by isomorphisms
identify the Yoneda maps attached to a commutative square. -/
lemma coyoneda_hom_add_equiv_naturality {X X' Y Y' : D} (W : D) (α : X' ≅ X) (β : Y' ≅ Y)
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (h : α.hom ≫ f = f' ≫ β.hom) :
    AddMonoidHom.comp (coyoneda_map_add_hom W f) (hom_add_equiv W α).toAddMonoidHom =
      AddMonoidHom.comp (hom_add_equiv W β).toAddMonoidHom (coyoneda_map_add_hom W f') := by
  -- Move the ladder-square verification to the AddMonoidHom level before applying exactness
  -- transport, so the exactness theorem can consume the commutative square directly.
  ext x
  change (((x : W ⟶ X') ≫ α.hom) ≫ f) = (((x : W ⟶ X') ≫ f') ≫ β.hom)
  simpa [Category.assoc] using congrArg (fun k => x ≫ k) h

/-- Helper for Remark 13.4.4: shifting the inverse first commutative square of a triangle
isomorphism yields the corresponding square for the shifted first morphisms. -/
lemma comm₁_inv_shift {T' : Triangle D} (e : T ≅ T') :
    inv (e.hom.hom₁⟦(1 : ℤ)⟧') ≫ (T.mor₁⟦(1 : ℤ)⟧') =
      (T'.mor₁⟦(1 : ℤ)⟧') ≫ inv (e.hom.hom₂⟦(1 : ℤ)⟧') := by
  -- Shift the inverse square from `comm₁_inv` and normalize inverses under the shift functor.
  simpa using congrArg (fun k => k⟦(1 : ℤ)⟧') (comm₁_inv e)

/-- Helper for Remark 13.4.4: exactness of the first covariant Hom-map pair transports across a
triangle isomorphism. -/
lemma exact₂_transport_of_iso {T T' : Triangle D} (e : T ≅ T') (W : D)
    (H :
      Function.Exact
        ((preadditiveCoyoneda.obj (op W)).map T.mor₁)
        ((preadditiveCoyoneda.obj (op W)).map T.mor₂)) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T'.mor₁)
      ((preadditiveCoyoneda.obj (op W)).map T'.mor₂) := by
  let i₁ : T'.obj₁ ≅ T.obj₁ := (Triangle.π₁.mapIso e).symm
  let i₂ : T'.obj₂ ≅ T.obj₂ := (Triangle.π₂.mapIso e).symm
  let i₃ : T'.obj₃ ≅ T.obj₃ := (Triangle.π₃.mapIso e).symm
  let e₁ : (W ⟶ T'.obj₁) ≃+ (W ⟶ T.obj₁) := hom_add_equiv W i₁
  let e₂ : (W ⟶ T'.obj₂) ≃+ (W ⟶ T.obj₂) := hom_add_equiv W i₂
  let e₃ : (W ⟶ T'.obj₃) ≃+ (W ⟶ T.obj₃) := hom_add_equiv W i₃
  -- Transport exactness across the inverse ladder built from the triangle isomorphism.
  simpa [coyoneda_map_add_hom] using
    (Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
      (f₁₂ := coyoneda_map_add_hom W T'.mor₁) (f₂₃ := coyoneda_map_add_hom W T'.mor₂)
      (g₁₂ := coyoneda_map_add_hom W T.mor₁) (g₂₃ := coyoneda_map_add_hom W T.mor₂)
      (comm₁₂ := coyoneda_hom_add_equiv_naturality W i₁ i₂ (by simpa [i₁, i₂] using comm₁_inv e))
      (comm₂₃ := coyoneda_hom_add_equiv_naturality W i₂ i₃ (by simpa [i₂, i₃] using comm₂_inv e))
      (H := by simpa [coyoneda_map_add_hom] using H))

/-- Helper for Remark 13.4.4: exactness of the second covariant Hom-map pair transports across a
triangle isomorphism. -/
lemma exact₃_transport_of_iso {T T' : Triangle D} (e : T ≅ T') (W : D)
    (H :
      Function.Exact
        ((preadditiveCoyoneda.obj (op W)).map T.mor₂)
        ((preadditiveCoyoneda.obj (op W)).map T.mor₃)) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T'.mor₂)
      ((preadditiveCoyoneda.obj (op W)).map T'.mor₃) := by
  let i₂ : T'.obj₂ ≅ T.obj₂ := (Triangle.π₂.mapIso e).symm
  let i₃ : T'.obj₃ ≅ T.obj₃ := (Triangle.π₃.mapIso e).symm
  let i₁s : T'.obj₁⟦(1 : ℤ)⟧ ≅ T.obj₁⟦(1 : ℤ)⟧ := asIso (inv (e.hom.hom₁⟦(1 : ℤ)⟧'))
  let e₁ : (W ⟶ T'.obj₂) ≃+ (W ⟶ T.obj₂) := hom_add_equiv W i₂
  let e₂ : (W ⟶ T'.obj₃) ≃+ (W ⟶ T.obj₃) := hom_add_equiv W i₃
  let e₃ : (W ⟶ T'.obj₁⟦(1 : ℤ)⟧) ≃+ (W ⟶ T.obj₁⟦(1 : ℤ)⟧) := hom_add_equiv W i₁s
  -- Transport exactness across the inverse ladder for the second pair.
  simpa [coyoneda_map_add_hom] using
    (Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
      (f₁₂ := coyoneda_map_add_hom W T'.mor₂) (f₂₃ := coyoneda_map_add_hom W T'.mor₃)
      (g₁₂ := coyoneda_map_add_hom W T.mor₂) (g₂₃ := coyoneda_map_add_hom W T.mor₃)
      (comm₁₂ := coyoneda_hom_add_equiv_naturality W i₂ i₃ (by simpa [i₂, i₃] using comm₂_inv e))
      (comm₂₃ := coyoneda_hom_add_equiv_naturality W i₃ i₁s
        (by simpa [i₃, i₁s] using comm₃_inv e))
      (H := by simpa [coyoneda_map_add_hom] using H))

/-- Helper for Remark 13.4.4: exactness of the third covariant Hom-map pair transports across a
triangle isomorphism. -/
lemma exact₁_transport_of_iso {T T' : Triangle D} (e : T ≅ T') (W : D)
    (H :
      Function.Exact
        ((preadditiveCoyoneda.obj (op W)).map T.mor₃)
        ((preadditiveCoyoneda.obj (op W)).map (T.mor₁⟦(1 : ℤ)⟧'))) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T'.mor₃)
      ((preadditiveCoyoneda.obj (op W)).map (T'.mor₁⟦(1 : ℤ)⟧')) := by
  let i₃ : T'.obj₃ ≅ T.obj₃ := (Triangle.π₃.mapIso e).symm
  let i₁s : T'.obj₁⟦(1 : ℤ)⟧ ≅ T.obj₁⟦(1 : ℤ)⟧ := asIso (inv (e.hom.hom₁⟦(1 : ℤ)⟧'))
  let i₂s : T'.obj₂⟦(1 : ℤ)⟧ ≅ T.obj₂⟦(1 : ℤ)⟧ := asIso (inv (e.hom.hom₂⟦(1 : ℤ)⟧'))
  let e₁ : (W ⟶ T'.obj₃) ≃+ (W ⟶ T.obj₃) := hom_add_equiv W i₃
  let e₂ : (W ⟶ T'.obj₁⟦(1 : ℤ)⟧) ≃+ (W ⟶ T.obj₁⟦(1 : ℤ)⟧) := hom_add_equiv W i₁s
  let e₃ : (W ⟶ T'.obj₂⟦(1 : ℤ)⟧) ≃+ (W ⟶ T.obj₂⟦(1 : ℤ)⟧) := hom_add_equiv W i₂s
  -- Transport exactness across the inverse ladder for the third pair.
  simpa [coyoneda_map_add_hom] using
    (Function.Exact.of_ladder_addEquiv_of_exact' (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
      (f₁₂ := coyoneda_map_add_hom W T'.mor₃)
      (f₂₃ := coyoneda_map_add_hom W (T'.mor₁⟦(1 : ℤ)⟧'))
      (g₁₂ := coyoneda_map_add_hom W T.mor₃)
      (g₂₃ := coyoneda_map_add_hom W (T.mor₁⟦(1 : ℤ)⟧'))
      (comm₁₂ := coyoneda_hom_add_equiv_naturality W i₃ i₁s
        (by simpa [i₃, i₁s] using comm₃_inv e))
      (comm₂₃ := coyoneda_hom_add_equiv_naturality W i₁s i₂s
        (by simpa [i₁s, i₂s] using comm₁_inv_shift e))
      (H := by simpa [coyoneda_map_add_hom] using H))

lemma zero₁₂ (hT : IsSpecial T) (n : ℤ) :
    ((T⟦n⟧ : Triangle D).mor₁) ≫ (T⟦n⟧ : Triangle D).mor₂ = 0 := by
  -- Evaluate the exactness zero-composite on the identity to recover the triangle composite.
  let S : Triangle D := T⟦n⟧
  have h := congrFun ((hT.exact₂ n S.obj₁).comp_eq_zero) (𝟙 S.obj₁)
  -- Normalize the functorial action to ordinary postcomposition.
  change (𝟙 S.obj₁ ≫ S.mor₁) ≫ S.mor₂ = 0 at h
  simpa [S] using h

lemma zero₂₃ (hT : IsSpecial T) (n : ℤ) :
    ((T⟦n⟧ : Triangle D).mor₂) ≫ (T⟦n⟧ : Triangle D).mor₃ = 0 := by
  -- Evaluate the exactness zero-composite on the identity to recover the triangle composite.
  let S : Triangle D := T⟦n⟧
  have h := congrFun ((hT.exact₃ n S.obj₂).comp_eq_zero) (𝟙 S.obj₂)
  -- Normalize the functorial action to ordinary postcomposition.
  change (𝟙 S.obj₂ ≫ S.mor₂) ≫ S.mor₃ = 0 at h
  simpa [S] using h

lemma zero₃₁ (hT : IsSpecial T) (n : ℤ) :
    ((T⟦n⟧ : Triangle D).mor₃) ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = 0 := by
  -- Evaluate the exactness zero-composite on the identity to recover the triangle composite.
  let S : Triangle D := T⟦n⟧
  have h := congrFun ((hT.exact₁ n S.obj₃).comp_eq_zero) (𝟙 S.obj₃)
  -- Normalize the functorial action to ordinary postcomposition.
  change (𝟙 S.obj₃ ≫ S.mor₃) ≫ (S.mor₁⟦(1 : ℤ)⟧') = 0 at h
  simpa [S] using h

theorem of_iso {T' : Triangle D} (e : T ≅ T') (hT : IsSpecial T) :
    IsSpecial T' := by
  -- Route correction: transport the three exactness fields one by one across the shifted triangle
  -- isomorphisms, so the fixed-shift Hom-level ladders carry the whole proof.
  refine
    { exact₂ := ?_
      exact₃ := ?_
      exact₁ := ?_ }
  · intro n W
    -- Transport the first exact pair across the shifted triangle isomorphism.
    exact exact₂_transport_of_iso ((Triangle.shiftFunctor D n).mapIso e) W (hT.exact₂ n W)
  · intro n W
    -- Transport the second exact pair across the shifted triangle isomorphism.
    exact exact₃_transport_of_iso ((Triangle.shiftFunctor D n).mapIso e) W (hT.exact₃ n W)
  · intro n W
    -- Transport the third exact pair across the shifted triangle isomorphism.
    exact exact₁_transport_of_iso ((Triangle.shiftFunctor D n).mapIso e) W (hT.exact₁ n W)

/-- Helper for Remark 13.4.4: the `n = 0` exactness field transports to the unshifted first
covariant Hom-map pair of `T`. -/
lemma exact₂_unshifted (hT : IsSpecial T) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T.mor₁)
      ((preadditiveCoyoneda.obj (op W)).map T.mor₂) := by
  -- Remove the formal shift by transporting exactness across the zero-shift isomorphism.
  simpa using exact₂_transport_of_iso ((Triangle.shiftFunctorZero D).app T) W (hT.exact₂ 0 W)

/-- Helper for Remark 13.4.4: the `n = 0` exactness field transports to the unshifted second
covariant Hom-map pair of `T`. -/
lemma exact₃_unshifted (hT : IsSpecial T) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T.mor₂)
      ((preadditiveCoyoneda.obj (op W)).map T.mor₃) := by
  -- Remove the formal shift by transporting exactness across the zero-shift isomorphism.
  simpa using exact₃_transport_of_iso ((Triangle.shiftFunctorZero D).app T) W (hT.exact₃ 0 W)

/-- Helper for Remark 13.4.4: the `n = 0` exactness field transports to the unshifted third
covariant Hom-map pair of `T`. -/
lemma exact₁_unshifted (hT : IsSpecial T) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map T.mor₃)
      ((preadditiveCoyoneda.obj (op W)).map (T.mor₁⟦(1 : ℤ)⟧')) := by
  -- Remove the formal shift by transporting exactness across the zero-shift isomorphism.
  simpa using exact₁_transport_of_iso ((Triangle.shiftFunctorZero D).app T) W (hT.exact₁ 0 W)

/-- Helper for Remark 13.4.4: the unshifted first covariant Hom-map pair gives the expected
factorization through `T.mor₁`. -/
lemma coyoneda_exact₂_unshifted (hT : IsSpecial T) (W : D)
    {f : W ⟶ T.obj₂} (hf : f ≫ T.mor₂ = 0) :
    ∃ g : W ⟶ T.obj₁, f = g ≫ T.mor₁ := by
  obtain ⟨g, hg⟩ := (exact₂_unshifted hT W f).1 hf
  exact ⟨g, by simpa using hg.symm⟩

/-- Helper for Remark 13.4.4: the unshifted second covariant Hom-map pair gives the expected
factorization through `T.mor₂`. -/
lemma coyoneda_exact₃_unshifted (hT : IsSpecial T) (W : D)
    {f : W ⟶ T.obj₃} (hf : f ≫ T.mor₃ = 0) :
    ∃ g : W ⟶ T.obj₂, f = g ≫ T.mor₂ := by
  obtain ⟨g, hg⟩ := (exact₃_unshifted hT W f).1 hf
  exact ⟨g, by simpa using hg.symm⟩

/-- Helper for Remark 13.4.4: the unshifted first two morphisms of a special triangle compose to
zero. -/
lemma zero₁₂_unshifted (hT : IsSpecial T) :
    T.mor₁ ≫ T.mor₂ = 0 := by
  -- Evaluate the transported unshifted exactness on the identity.
  have h := congrFun ((exact₂_unshifted hT T.obj₁).comp_eq_zero) (𝟙 T.obj₁)
  change (𝟙 T.obj₁ ≫ T.mor₁) ≫ T.mor₂ = 0 at h
  simpa using h

/-- Helper for Remark 13.4.4: the unshifted second and third morphisms of a special triangle
compose to zero. -/
lemma zero₂₃_unshifted (hT : IsSpecial T) :
    T.mor₂ ≫ T.mor₃ = 0 := by
  -- Evaluate the transported unshifted exactness on the identity.
  have h := congrFun ((exact₃_unshifted hT T.obj₂).comp_eq_zero) (𝟙 T.obj₂)
  change (𝟙 T.obj₂ ≫ T.mor₂) ≫ T.mor₃ = 0 at h
  simpa using h

section

instance instShift (n : ℤ) [IsSpecial T] : IsSpecial (T⟦n⟧ : Triangle D) := by
  refine
    { exact₂ := ?_
      exact₃ := ?_
      exact₁ := ?_ }
  · intro m W
    let e : (T⟦n + m⟧ : Triangle D) ≅ (((T⟦n⟧ : Triangle D)⟦m⟧) : Triangle D) :=
      (Triangle.shiftFunctorAdd' D n m (n + m) rfl).app T
    -- Reindex the first exact pair through the canonical shift-add isomorphism.
    exact exact₂_transport_of_iso e W ((inferInstance : IsSpecial T).exact₂ (n + m) W)
  · intro m W
    let e : (T⟦n + m⟧ : Triangle D) ≅ (((T⟦n⟧ : Triangle D)⟦m⟧) : Triangle D) :=
      (Triangle.shiftFunctorAdd' D n m (n + m) rfl).app T
    -- Reindex the second exact pair through the canonical shift-add isomorphism.
    exact exact₃_transport_of_iso e W ((inferInstance : IsSpecial T).exact₃ (n + m) W)
  · intro m W
    let e : (T⟦n + m⟧ : Triangle D) ≅ (((T⟦n⟧ : Triangle D)⟦m⟧) : Triangle D) :=
      (Triangle.shiftFunctorAdd' D n m (n + m) rfl).app T
    -- Reindex the third exact pair through the canonical shift-add isomorphism.
    exact exact₁_transport_of_iso e W ((inferInstance : IsSpecial T).exact₁ (n + m) W)

/-- Helper for Remark 13.4.4: exactness is preserved when the left additive map is negated. -/
lemma exact_of_neg_left {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {f : A →+ B} {g : B →+ C} (h : Function.Exact f g) :
    Function.Exact (-f) g := by
  -- The kernel condition is unchanged, and every factorization through `f` can be rewritten
  -- through `-f` by negating the witness in the source.
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := (h y).1 hy
    refine ⟨-x, ?_⟩
    simp
  · rintro ⟨x, rfl⟩
    simpa using congrFun h.comp_eq_zero (-x)

/-- Helper for Remark 13.4.4: exactness is preserved when the right additive map is negated. -/
lemma exact_of_neg_right {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {f : A →+ B} {g : B →+ C} (h : Function.Exact f g) :
    Function.Exact f (-g) := by
  -- Negating the target map does not change its kernel, so the same exactness witnesses work.
  intro y
  constructor
  · intro hy
    exact (h y).1 (by simpa using hy)
  · rintro ⟨x, rfl⟩
    simpa using congrFun h.comp_eq_zero x

/-- Helper for Remark 13.4.4: the `exact₁` field of `T.rotate` is the shifted `exact₂` field of
`T`, after identifying the rotated third map with the negative of the shifted first map. -/
lemma rotate_exact₁_from_shift_exact₂ [IsSpecial T] (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T.rotate⟦n⟧ : Triangle D).mor₃))
      ((preadditiveCoyoneda.obj (op W)).map (((T.rotate⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧')) := by
  -- TODO: transport the shifted `exact₂` ladder of `T` at degree `n + 1` across the
  -- `shiftFunctorComm` comparison between `X⟦1⟧⟦n⟧` and `X⟦n⟧⟦1⟧`, then apply
  -- `exact_of_neg_left`.
  sorry

end

instance instRotate [IsSpecial T] : IsSpecial T.rotate := by
  -- TODO: exactness of the rotated first two pairs still needs explicit `shiftFunctorComm`
  -- transport on the Hom ladders; the third pair is `rotate_exact₁_from_shift_exact₂`.
  sorry

noncomputable instance instInvRotate [IsSpecial T] : IsSpecial T.invRotate := by
  -- TODO: once `instRotate` is available, transport specialness back along
  -- `invRotateIsoRotateRotateShiftFunctorNegOne`.
  sorry

lemma coyoneda_exact₂ (hT : IsSpecial T) (n : ℤ) (W : D)
    {f : W ⟶ (T⟦n⟧ : Triangle D).obj₂} (hf : f ≫ (T⟦n⟧ : Triangle D).mor₂ = 0) :
    ∃ g : W ⟶ (T⟦n⟧ : Triangle D).obj₁, f = g ≫ (T⟦n⟧ : Triangle D).mor₁ := by
  obtain ⟨g, hg⟩ := (hT.exact₂ n W f).1 hf
  exact ⟨g, by simpa using hg.symm⟩

lemma coyoneda_exact₃ (hT : IsSpecial T) (n : ℤ) (W : D)
    {f : W ⟶ (T⟦n⟧ : Triangle D).obj₃} (hf : f ≫ (T⟦n⟧ : Triangle D).mor₃ = 0) :
    ∃ g : W ⟶ (T⟦n⟧ : Triangle D).obj₂, f = g ≫ (T⟦n⟧ : Triangle D).mor₂ := by
  obtain ⟨g, hg⟩ := (hT.exact₃ n W f).1 hf
  exact ⟨g, by simpa using hg.symm⟩

lemma coyoneda_exact₁ (hT : IsSpecial T) (n : ℤ) (W : D)
    {f : W ⟶ (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧}
    (hf : f ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = 0) :
    ∃ g : W ⟶ (T⟦n⟧ : Triangle D).obj₃, f = g ≫ (T⟦n⟧ : Triangle D).mor₃ := by
  obtain ⟨g, hg⟩ := (hT.exact₁ n W f).1 hf
  exact ⟨g, by simpa using hg.symm⟩

end IsSpecial

/-- Remark 13.4.4: a triangle is co-special precisely when its canonical opposite-category view
is special. As a bridge/view notion, this keeps only the contravariant exactness and rotation API
needed later in the chapter, rather than mirroring the full `IsSpecial` helper surface. -/
noncomputable abbrev IsCoSpecial (T : Triangle D) : Prop :=
  IsSpecial ((triangleOpEquivalence D).functor.obj (op T))

/-- Helper for Remark 13.4.4: applying `triangleOpEquivalence` to a shifted triangle agrees with
shifting the opposite-category image of the triangle. -/
noncomputable def triangleOpEquivalence_functor_obj_shift_iso (T : Triangle D) (n : ℤ) :
    ((triangleOpEquivalence D).functor.obj (op (T⟦n⟧ : Triangle D))) ≅
      (((triangleOpEquivalence D).functor.obj (op T))⟦n⟧ : Triangle Dᵒᵖ) := by
  -- TODO: specialize the opposite-functor compatibility of shifts to rewrite the opposite view
  -- of `T⟦n⟧` as the shift of the opposite view of `T`.
  sorry

namespace IsCoSpecial

variable {T : Triangle D}

instance instRotate [IsCoSpecial T] : IsCoSpecial T.rotate := by
  -- TODO: transport the opposite-category view of `T.rotate` to the inverse rotation of the
  -- opposite triangle, then reuse `Triangle.IsSpecial.instInvRotate`.
  sorry

noncomputable instance instInvRotate [IsCoSpecial T] : IsCoSpecial T.invRotate := by
  -- TODO: transport the opposite-category view of `T.invRotate` to the rotation of the opposite
  -- triangle, then reuse `Triangle.IsSpecial.instRotate`.
  sorry

lemma yoneda_exact₂ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₂ ⟶ W} (hf : (T⟦n⟧ : Triangle D).mor₁ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₃ ⟶ W, f = (T⟦n⟧ : Triangle D).mor₂ ≫ g := by
  -- TODO: identify the opposite-category shift of `triangleOpEquivalence.obj (op T)` with the
  -- opposite view of `T⟦n⟧`, apply `coyoneda_exact₂` there, and unop the factorization.
  sorry

lemma yoneda_exact₃ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₃ ⟶ W} (hf : (T⟦n⟧ : Triangle D).mor₂ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧ ⟶ W, f = (T⟦n⟧ : Triangle D).mor₃ ≫ g := by
  -- TODO: identify the opposite-category shift of `triangleOpEquivalence.obj (op T)` with the
  -- opposite view of `T⟦n⟧`, apply `coyoneda_exact₃` there, and unop the factorization.
  sorry

lemma yoneda_exact₁ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧ ⟶ W} (hf : (T⟦n⟧ : Triangle D).mor₃ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₂⟦(1 : ℤ)⟧ ⟶ W,
      f = (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') ≫ g := by
  -- TODO: identify the opposite-category shift of `triangleOpEquivalence.obj (op T)` with the
  -- opposite view of `T⟦n⟧`, apply `coyoneda_exact₁` there, and unop the factorization.
  sorry

end IsCoSpecial

end Triangle

-- Proof sketch: repeat the proof of `Pretriangulated.isIso₂_of_isIso₁₃`, replacing the
-- distinguished-triangle exactness input by the `coyoneda_exact₂` and `coyoneda_exact₃` fields of
-- the special-triangle assumptions on `T` and `T'`.
/-- In a morphism of special triangles, if the first and third components are isomorphisms, then
the second component is an isomorphism. -/
theorem isIso₂_of_isIso₁₃_of_isSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsSpecial T) (hT' : Triangle.IsSpecial T') (h₁ : IsIso φ.hom₁)
    (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₂ := by
  letI : Triangle.IsSpecial T := hT
  letI : Triangle.IsSpecial T' := hT'
  letI : IsIso φ.hom₁ := h₁
  letI : IsIso φ.hom₃ := h₃
  have : Mono φ.hom₂ := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A f hf
    -- Recover the first factorization from the covariant exactness of `T`.
    obtain ⟨g, rfl⟩ : ∃ g : A ⟶ T.obj₁, f = g ≫ T.mor₁ := by
      exact Triangle.IsSpecial.coyoneda_exact₂_unshifted hT A (by
        rw [← cancel_mono φ.hom₃, Category.assoc, φ.comm₂, reassoc_of% hf, zero_comp, zero_comp])
    -- Use exactness on `T'.invRotate` to lift the comparison one step further.
    obtain ⟨h, hh⟩ : ∃ h : A ⟶ T'.invRotate.obj₁, g ≫ φ.hom₁ = h ≫ T'.invRotate.mor₁ := by
      exact Triangle.IsSpecial.coyoneda_exact₂_unshifted
        (inferInstance : Triangle.IsSpecial T'.invRotate) A (by
          have hzero : g ≫ T.mor₁ ≫ φ.hom₂ = 0 := by
            simpa [Category.assoc] using hf
          have hcomm : g ≫ T.mor₁ ≫ φ.hom₂ = g ≫ φ.hom₁ ≫ T'.mor₁ := by
            simpa [Category.assoc] using congrArg (fun m => g ≫ m) φ.comm₁
          dsimp [invRotate]
          simpa [Category.assoc] using (hcomm ▸ hzero))
    obtain ⟨k, rfl⟩ : ∃ k : A ⟶ T.invRotate.obj₁, k ≫ T.invRotate.mor₁ = g := by
      letI : IsIso ((shiftFunctor D (-1)).map φ.hom₃) :=
        Functor.map_isIso (shiftFunctor D (-1)) φ.hom₃
      refine ⟨h ≫ inv ((shiftFunctor D (-1)).map φ.hom₃), ?_⟩
      have eq := ((invRotate D).map φ).comm₁
      dsimp only [invRotate] at eq
      rw [← cancel_mono φ.hom₁, Category.assoc, Category.assoc, eq, IsIso.inv_hom_id_assoc, hh]
    calc
      (k ≫ T.invRotate.mor₁) ≫ T.mor₁ = k ≫ (T.invRotate.mor₁ ≫ T.mor₁) := by
        simp [Category.assoc]
      _ = k ≫ 0 := by
        have hz : T.invRotate.mor₁ ≫ T.mor₁ = 0 := by
          simpa [invRotate] using
            Triangle.IsSpecial.zero₁₂_unshifted (inferInstance : Triangle.IsSpecial T.invRotate)
        rw [hz]
      _ = 0 := by simp
  refine isIso_of_yoneda_map_bijective _ (fun A => ⟨?_, ?_⟩)
  · intro f₁ f₂ h
    simpa only [← cancel_mono φ.hom₂] using h
  · intro y₂
    have hx₃ : ∃ x₃ : A ⟶ T.obj₃, x₃ ≫ φ.hom₃ = y₂ ≫ T'.mor₂ := by
      refine ⟨y₂ ≫ T'.mor₂ ≫ inv φ.hom₃, ?_⟩
      simp [Category.assoc]
    obtain ⟨x₃, hx₃⟩ := hx₃
    have hx₃_zero : x₃ ≫ T.mor₃ = 0 := by
      rw [← cancel_mono (φ.hom₁⟦(1 : ℤ)⟧'), Category.assoc, zero_comp, φ.comm₃,
        reassoc_of% hx₃]
      simpa [Category.assoc] using
        congrArg (fun m => y₂ ≫ m) (Triangle.IsSpecial.zero₂₃_unshifted hT')
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : A ⟶ T.obj₂, x₃ = x₂ ≫ T.mor₂ := by
      exact Triangle.IsSpecial.coyoneda_exact₃_unshifted hT A hx₃_zero
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : A ⟶ T'.obj₁, y₂ - x₂ ≫ φ.hom₂ = y₁ ≫ T'.mor₁ := by
      exact Triangle.IsSpecial.coyoneda_exact₂_unshifted hT' A (by
        rw [Preadditive.sub_comp, Category.assoc, ← φ.comm₂, ← reassoc_of% hx₂, hx₃, sub_self])
    have hx₁ : ∃ x₁ : A ⟶ T.obj₁, x₁ ≫ φ.hom₁ = y₁ := by
      exact ⟨y₁ ≫ inv φ.hom₁, by simp⟩
    obtain ⟨x₁, hx₁⟩ := hx₁
    refine ⟨x₂ + x₁ ≫ T.mor₁, ?_⟩
    dsimp
    rw [Preadditive.add_comp, Category.assoc, φ.comm₁, reassoc_of% hx₁, ← hy₁, add_sub_cancel]

-- Proof sketch: apply the preceding special-triangle two-out-of-three statement to the rotated
-- morphism of triangles.
/-- In a morphism of special triangles, if the first and second components are isomorphisms, then
the third component is an isomorphism. -/
theorem isIso₃_of_isIso₁₂_of_isSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsSpecial T) (hT' : Triangle.IsSpecial T') (h₁ : IsIso φ.hom₁)
    (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ := by
  letI : Triangle.IsSpecial T := hT
  letI : Triangle.IsSpecial T' := hT'
  letI : IsIso φ.hom₁ := h₁
  letI : IsIso φ.hom₂ := h₂
  simpa [rotate] using
    isIso₂_of_isIso₁₃_of_isSpecial ((rotate D).map φ)
      (by simpa using (inferInstance : Triangle.IsSpecial T.rotate))
      (by simpa using (inferInstance : Triangle.IsSpecial T'.rotate))
      (by dsimp [rotate]; infer_instance)
      (by dsimp [rotate]; infer_instance)

-- Proof sketch: apply the preceding special-triangle two-out-of-three statement to the inverse
-- rotation of the morphism of triangles.
/-- In a morphism of special triangles, if the second and third components are isomorphisms, then
the first component is an isomorphism. -/
theorem isIso₁_of_isIso₂₃_of_isSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsSpecial T) (hT' : Triangle.IsSpecial T') (h₂ : IsIso φ.hom₂)
    (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₁ := by
  letI : Triangle.IsSpecial T := hT
  letI : Triangle.IsSpecial T' := hT'
  letI : IsIso φ.hom₂ := h₂
  letI : IsIso φ.hom₃ := h₃
  simpa [invRotate] using
    isIso₂_of_isIso₁₃_of_isSpecial ((invRotate D).map φ)
      (by simpa using (inferInstance : Triangle.IsSpecial T.invRotate))
      (by simpa using (inferInstance : Triangle.IsSpecial T'.invRotate))
      (by dsimp [invRotate]; infer_instance)
      (by dsimp [invRotate]; infer_instance)

-- Proof sketch: pass to the opposite-category view and apply the special-triangle
-- two-out-of-three theorem there, rewriting the resulting source-facing conclusion back in terms
-- of `yoneda_exact₂` and `yoneda_exact₃`.
/-- In a morphism of co-special triangles, if the first and third components are isomorphisms, then
the second component is an isomorphism. -/
theorem isIso₂_of_isIso₁₃_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsCoSpecial T) (hT' : Triangle.IsCoSpecial T') (h₁ : IsIso φ.hom₁)
    (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₂ := by
  -- TODO: pass to the opposite-category morphism given by `triangleOpEquivalence`, apply the
  -- special-triangle theorem there, and rewrite the resulting `IsIso` statement back to `φ.hom₂`.
  sorry

-- Proof sketch: reduce to the co-special version of the first theorem after rotating the morphism
-- of triangles.
/-- In a morphism of co-special triangles, if the first and second components are isomorphisms,
then the third component is an isomorphism. -/
theorem isIso₃_of_isIso₁₂_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsCoSpecial T) (hT' : Triangle.IsCoSpecial T') (h₁ : IsIso φ.hom₁)
    (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ := by
  letI : Triangle.IsCoSpecial T := hT
  letI : Triangle.IsCoSpecial T' := hT'
  letI : IsIso φ.hom₁ := h₁
  letI : IsIso φ.hom₂ := h₂
  simpa [rotate] using
    isIso₂_of_isIso₁₃_of_isCoSpecial ((rotate D).map φ)
      (by simpa using (inferInstance : Triangle.IsCoSpecial T.rotate))
      (by simpa using (inferInstance : Triangle.IsCoSpecial T'.rotate))
      (by dsimp [rotate]; infer_instance)
      (by dsimp [rotate]; infer_instance)

-- Proof sketch: reduce to the co-special version of the first theorem after inverse-rotating the
-- morphism of triangles.
/-- In a morphism of co-special triangles, if the second and third components are isomorphisms,
then the first component is an isomorphism. -/
theorem isIso₁_of_isIso₂₃_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsCoSpecial T) (hT' : Triangle.IsCoSpecial T') (h₂ : IsIso φ.hom₂)
    (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₁ := by
  letI : Triangle.IsCoSpecial T := hT
  letI : Triangle.IsCoSpecial T' := hT'
  letI : IsIso φ.hom₂ := h₂
  letI : IsIso φ.hom₃ := h₃
  simpa [invRotate] using
    isIso₂_of_isIso₁₃_of_isCoSpecial ((invRotate D).map φ)
      (by simpa using (inferInstance : Triangle.IsCoSpecial T.invRotate))
      (by simpa using (inferInstance : Triangle.IsCoSpecial T'.invRotate))
      (by dsimp [invRotate]; infer_instance)
      (by dsimp [invRotate]; infer_instance)

section

variable [HasZeroObject D] [Pretriangulated D]

-- Proof sketch: apply the distinguished-triangle exactness lemmas `Triangle.coyoneda_exact₁`,
-- `Triangle.coyoneda_exact₂`, and `Triangle.coyoneda_exact₃` to each shifted triangle
-- `T⟦n⟧`, using `Triangle.shift_distinguished` to transport distinguishedness along shifts.
/-- Every distinguished triangle is special. -/
instance instIsSpecialOfMemDistTriang (T : Triangle D) (hT : T ∈ distTriang D) :
    Triangle.IsSpecial T where
  exact₂ n W := by
    -- Shift distinguishedness to the relevant triangle and use the standard exactness factorization.
    let hshift : (T⟦n⟧ : Triangle D) ∈ distTriang D := Triangle.shift_distinguished T hT n
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext f
      -- Normalize the functorial action to ordinary postcomposition.
      change (f ≫ (T⟦n⟧ : Triangle D).mor₁) ≫ (T⟦n⟧ : Triangle D).mor₂ = 0
      calc
        (f ≫ (T⟦n⟧ : Triangle D).mor₁) ≫ (T⟦n⟧ : Triangle D).mor₂ = f ≫ 0 := by
          simpa [Category.assoc] using
            congrArg (fun k => f ≫ k) (comp_distTriang_mor_zero₁₂ (T := (T⟦n⟧ : Triangle D)) hshift)
        _ = 0 := by simpa using (comp_zero (f := f) (Z := (T⟦n⟧ : Triangle D).obj₃))
    · intro f hf
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ (T := (T⟦n⟧ : Triangle D)) hshift f hf
      exact ⟨g, hg.symm⟩
  exact₃ n W := by
    -- Shift distinguishedness to the relevant triangle and use the standard exactness factorization.
    let hshift : (T⟦n⟧ : Triangle D) ∈ distTriang D := Triangle.shift_distinguished T hT n
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext f
      -- Normalize the functorial action to ordinary postcomposition.
      change (f ≫ (T⟦n⟧ : Triangle D).mor₂) ≫ (T⟦n⟧ : Triangle D).mor₃ = 0
      calc
        (f ≫ (T⟦n⟧ : Triangle D).mor₂) ≫ (T⟦n⟧ : Triangle D).mor₃ = f ≫ 0 := by
          simpa [Category.assoc] using
            congrArg (fun k => f ≫ k) (comp_distTriang_mor_zero₂₃ (T := (T⟦n⟧ : Triangle D)) hshift)
        _ = 0 := by simpa using (comp_zero (f := f) (Z := (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧))
    · intro f hf
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ (T := (T⟦n⟧ : Triangle D)) hshift f hf
      exact ⟨g, hg.symm⟩
  exact₁ n W := by
    -- Shift distinguishedness to the relevant triangle and use the standard exactness factorization.
    let hshift : (T⟦n⟧ : Triangle D) ∈ distTriang D := Triangle.shift_distinguished T hT n
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext f
      -- Normalize the functorial action to ordinary postcomposition.
      change (f ≫ (T⟦n⟧ : Triangle D).mor₃) ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = 0
      calc
        (f ≫ (T⟦n⟧ : Triangle D).mor₃) ≫ (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') = f ≫ 0 := by
          simpa [Category.assoc] using
            congrArg (fun k => f ≫ k) (comp_distTriang_mor_zero₃₁ (T := (T⟦n⟧ : Triangle D)) hshift)
        _ = 0 := by simpa using (comp_zero (f := f) (Z := (T⟦n⟧ : Triangle D).obj₂⟦(1 : ℤ)⟧))
    · intro f hf
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ (T := (T⟦n⟧ : Triangle D)) hshift f hf
      exact ⟨g, hg.symm⟩

-- Proof sketch: transport distinguishedness to the canonical opposite-category view with
-- `op_distinguished`, then invoke the distinguished-triangle instance for `Triangle.IsSpecial`.
/-- Every distinguished triangle is co-special. -/
instance instIsCoSpecialOfMemDistTriang (T : Triangle D) (hT : T ∈ distTriang D) :
    Triangle.IsCoSpecial T := by
  simpa [Triangle.IsCoSpecial] using
    (instIsSpecialOfMemDistTriang ((triangleOpEquivalence D).functor.obj (op T))
      (op_distinguished T hT))

end

end Pretriangulated
end CategoryTheory

/-! ### Lemma_13_4_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.5:
- primary domain: distinguished triangles in a pretriangulated category and the exactness of the
  covariant and contravariant Hom sequences attached to them;
- sampled core/canonical declarations:
  `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`,
  `comp_distTriang_mor_zero₁₂`;
- best owner abstraction: the canonical owner is a distinguished triangle `T ∈ distTriang D`,
  together with the exactness API on the `mor₁`-`mor₂` segment;
- primitive data: the distinguished triangle `T` and the exactness-relevant vanishing conditions
  `φ.hom₁ = 0` and `φ'.hom₃ = 0` on two triangle endomorphisms;
- derived API: the textbook `(0,b,0)` and `(0,b',0)` formulation is an immediate corollary of the
  owner-level exactness statement below, so it should not remain as a second packaged public
  theorem;
- source/core/bridge triage:
  `source-facing`: the Stacks-project vanishing statement for the textbook composite `bb'`;
  `core/canonical`: the distinguished-triangle exactness lemmas above;
  `bridge/view`: the textbook `(0,b,0)`/`(0,b',0)` reformulation, obtained immediately by
    instantiating the owner-level theorem, so no second wrapper theorem is kept.
-/

-- Proof sketch: use `φ'.comm₂` and `φ.comm₁` together with `hφ'₃` and `hφ₁` to factor
-- `φ'.hom₂` through `T.mor₁` and `φ.hom₂` through `T.mor₂` via `Triangle.coyoneda_exact₂`
-- and `Triangle.yoneda_exact₂`; then the middle composite vanishes by
-- `comp_distTriang_mor_zero₁₂`.
/-- Lemma 13.4.5: for endomorphisms `φ` and `φ'` of a distinguished triangle, the composite
`φ'.hom₂ ≫ φ.hom₂` vanishes as soon as `φ.hom₁ = 0` and `φ'.hom₃ = 0`. -/
theorem endomorphism_hom₂_comp_eq_zero {T : Triangle D}
    (hT : T ∈ distTriang D) (φ φ' : End T) (hφ₁ : φ.hom₁ = 0) (hφ'₃ : φ'.hom₃ = 0) :
    φ'.hom₂ ≫ φ.hom₂ = 0 := by
  obtain ⟨g', hg'⟩ := T.coyoneda_exact₂ hT φ'.hom₂ (by
    rw [← φ'.comm₂, hφ'₃, comp_zero])
  obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT φ.hom₂ (by
    rw [φ.comm₁, hφ₁, zero_comp])
  calc
    φ'.hom₂ ≫ φ.hom₂ = (g' ≫ T.mor₁) ≫ (T.mor₂ ≫ g) := by rw [hg', hg]
    _ = g' ≫ (T.mor₁ ≫ T.mor₂) ≫ g := by simp [Category.assoc]
    _ = 0 := by rw [comp_distTriang_mor_zero₁₂ _ hT, zero_comp, comp_zero]

end

/-! ### Lemma_13_4_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.6:
- primary domain: distinguished triangles and their endomorphisms in a pretriangulated category,
  together with idempotent endomorphisms of the outer terms;
- sampled owner declarations:
  `Triangle`,
  `TriangleMorphism`,
  `complete_distinguished_triangle_morphism₂`,
  `endomorphism_hom₂_comp_eq_zero`;
- best owner abstraction: triangle endomorphisms `T ⟶ T`, with outer endomorphisms expressed on the
  canonical owner `End`;
- primitive data: a distinguished triangle `T`, idempotent endomorphisms `a : End T.obj₁` and
  `c : End T.obj₃`, and the commutative square `CommSq T.mor₃ c (a⟦(1 : ℤ)⟧') T.mor₃`;
- derived API: a chosen completion of the outer square to a triangle endomorphism and the
  exactness-based vanishing statement of Lemma `13.4.5`, which forces the correction term on the
  middle object to square to zero;
- source/core/bridge triage:
  `source-facing`: existence of a triangle endomorphism with prescribed outer idempotents and
    idempotent middle component;
  `core/canonical`: `Triangle`, `TriangleMorphism`, and the distinguished-triangle completion API;
  `bridge/view`: the exactness lemma `endomorphism_hom₂_comp_eq_zero` used to correct a chosen
    middle component to an idempotent one.
-/

-- Proof sketch: use `complete_distinguished_triangle_morphism₂` to choose a triangle
-- endomorphism `φ : End T` with outer components `a` and `c`. Then `δ := φ * φ - φ` has zero
-- first and third components, so Lemma 13.4.5 forces `(δ.hom₂)^2 = 0`. Correct `φ` by the
-- polynomial `3x^2 - 2x^3` on `End T`; the outer components remain `a` and `c` because those are
-- idempotent, and the middle component becomes idempotent by the resulting quartic relation.
/-- Lemma 13.4.6: if `T` is a distinguished triangle in a pretriangulated category and
idempotent endomorphisms `a` of `T.obj₁` and `c` of `T.obj₃` commute with the third morphism of
`T`, then there exists a triangle endomorphism of `T` with outer components `a` and `c` whose
middle component is idempotent. -/
theorem exists_idempotent_triangle_endomorphism_of_outer_idempotents {T : Triangle D}
    (hT : T ∈ distTriang D) (a : End T.obj₁) (c : End T.obj₃)
    (hcomm : CommSq T.mor₃ c (a⟦(1 : ℤ)⟧') T.mor₃) (ha : a ≫ a = a) (hc : c ≫ c = c) :
    ∃ φ : End T, φ.hom₁ = a ∧ φ.hom₃ = c ∧ φ.hom₂ ≫ φ.hom₂ = φ.hom₂ := by
  obtain ⟨b₀, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ T T hT hT a c hcomm.w
  let b : End T.obj₂ := b₀
  let φ : End T := Triangle.homMk _ _ a b c hb₁ hb₂ hcomm.w
  let δ : End T := φ * φ - φ
  have ha' : a * a = a := by
    simpa [End.mul_def] using ha
  have hc' : c * c = c := by
    simpa [End.mul_def] using hc
  have hδ₁ : δ.hom₁ = 0 := by
    change a * a - a = 0
    exact sub_eq_zero.mpr ha'
  have hδ₃ : δ.hom₃ = 0 := by
    change c * c - c = 0
    exact sub_eq_zero.mpr hc'
  have hδ₂_nil := endomorphism_hom₂_comp_eq_zero hT δ δ hδ₁ hδ₃
  have hnil : (b * b - b) * (b * b - b) = 0 := by
    simpa [δ, φ, End.mul_def, Category.assoc] using hδ₂_nil
  have hfour : b * (b * (b * b)) = (2 : ℤ) • (b * (b * b)) - b * b := by
    calc
      b * (b * (b * b)) =
          ((b * b - b) * (b * b - b)) + ((2 : ℤ) • (b * (b * b)) - b * b) := by
            noncomm_ring
      _ = (2 : ℤ) • (b * (b * b)) - b * b := by
        rw [hnil]
        abel
  let ψ : End T := (3 : ℤ) • (φ * φ) - (2 : ℤ) • (φ * φ * φ)
  have hψ₁ : ψ.hom₁ = a := by
    change (3 : ℤ) • (a * a) - (2 : ℤ) • (a * a * a) = a
    rw [ha', ha']
    abel
  have hψ₃ : ψ.hom₃ = c := by
    change (3 : ℤ) • (c * c) - (2 : ℤ) • (c * c * c) = c
    rw [hc', hc']
    abel
  have hψ₂ : ψ.hom₂ ≫ ψ.hom₂ = ψ.hom₂ := by
    change ((3 : ℤ) • (b * b) - (2 : ℤ) • (b * b * b)) *
        ((3 : ℤ) • (b * b) - (2 : ℤ) • (b * b * b)) =
      (3 : ℤ) • (b * b) - (2 : ℤ) • (b * b * b)
    noncomm_ring [hfour]
  exact ⟨ψ, hψ₁, hψ₃, hψ₂⟩

end

/-! ### Lemma_13_4_7 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

/- Domain-style sampling:
- primary domain: pretriangulated categories, organized around distinguished triangles and the
  TR1/TR3 comparison data attached to a fixed morphism;
- sampled owner declarations:
  `Pretriangulated.distinguished_cocone_triangle`,
  `Pretriangulated.isoTriangleOfIso₁₂`,
  `Pretriangulated.exists_iso_of_arrow_iso`,
  `distTriang`;
- best owner abstraction: the existence part of Lemma 13.4.7 is exactly the canonical owner
  `distinguished_cocone_triangle`, while the comparison between two distinguished cones on the
  same morphism is derived directly from the canonical owner theorem
  `exists_iso_of_arrow_iso` by specializing to the identity arrow isomorphism on `f`;
- primitive data: a morphism `f : X ⟶ Y`, and for the comparison statement two distinguished
  triangles of the form `Triangle.mk f _ _`;
- derived API: the source-facing uniqueness statement, whose witness is obtained from
  `exists_iso_of_arrow_iso` and has identity first two components.

Source/core/bridge triage:
- `source-facing`: existence of a distinguished triangle on `f`, and the comparison between two
  such distinguished triangles;
- `core/canonical`: `distinguished_cocone_triangle`, `exists_iso_of_arrow_iso`, and `distTriang`;
- `bridge/view`: the identity-arrow specialization of `exists_iso_of_arrow_iso` for
  `Triangle.mk f g h` and `Triangle.mk f g' h'`.

The file should therefore recall the canonical owner for the existence statement and keep only the
source-facing uniqueness theorem as derived API.
-/

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Lemma 13.4.7 (existence): this is exactly the canonical owner theorem
`Pretriangulated.distinguished_cocone_triangle`. -/
recall distinguished_cocone_triangle

/-- Lemma 13.4.7: any two distinguished triangles with the same first morphism are isomorphic by
a triangle isomorphism whose first two components are identities. -/
theorem exists_distinguished_triangle_unique_up_to_iso {X Y Z Z' : D} {f : X ⟶ Y}
    {g : Y ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧} {g' : Y ⟶ Z'} {h' : Z' ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang D) (hT' : Triangle.mk f g' h' ∈ distTriang D) :
    ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h', e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y := by
  simpa using
    (exists_iso_of_arrow_iso _ _ hT hT' (Arrow.isoMk (Iso.refl X) (Iso.refl Y) (by simp)))

end CategoryTheory

/-! ### Lemma_13_4_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.8:
- primary domain: morphisms between distinguished triangles in a pretriangulated category, together
  with the exact Hom sequences attached to a distinguished triangle;
- sampled owner declarations:
  `Triangle.hom_ext`,
  `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`,
  `Triangle.coyoneda_exact₁`;
- best owner abstraction: the category `Triangle D`, so parallel triangle morphisms should use the
  canonical hom type `T ⟶ T'`; the five vanishing alternatives remain source-facing hypotheses on
  the theorem surface rather than a separate packaged owner;
- primitive data: two distinguished triangles `T` and `T'`, together with parallel morphisms
  `φ ψ : T ⟶ T'`;
- derived API: the uniqueness of the middle component under one of the five textbook
  Hom-vanishing alternatives.

Source/core/bridge triage:
- `source-facing`: the five textbook Hom-vanishing alternatives ensuring uniqueness of the middle
  component;
- `core/canonical`: the triangle category owner `Triangle D` and the exactness lemmas for the
  represented Hom functors of a distinguished triangle;
- `bridge/view`: the comparison of two parallel morphisms with fixed outer components, together
  with the owner-level corollary `φ = ψ` obtained from `Triangle.hom_ext`. -/

variable {T T' : Triangle D} {φ ψ : T ⟶ T'}

-- Proof sketch: subtract `ψ` from `φ`, use the equality of third components and the exactness of
-- `Hom(T.obj₂,-)` on `T'` to factor the difference of the middle components through `T'.mor₁`,
-- and then use the subsingleton hypothesis on `T.obj₂ ⟶ T'.obj₁` to force that factor to vanish.
/-- Companion to Lemma 13.4.8, case `(1)`: if `Hom(T.obj₂,T'.obj₁)` is subsingleton, then two
parallel morphisms of distinguished triangles with the same third component have the same middle
component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₂_obj₁
    (hT' : T' ∈ distTriang D) (h₃ : φ.hom₃ = ψ.hom₃)
    (h21 : Subsingleton (T.obj₂ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

-- Proof sketch: subtract `ψ` from `φ` and use the equality of first components together with the
-- exactness of `Hom(-,T'.obj₂)` on `T` to factor the difference of the middle components through
-- `T.mor₂`; the vanishing of `T.obj₃ ⟶ T'.obj₂` forces that factor to be zero.
/-- Companion to Lemma 13.4.8, case `(2)`: if `Hom(T.obj₃,T'.obj₂)` is subsingleton, then the
middle component of a morphism of distinguished triangles is determined by the first component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₂
    (hT : T ∈ distTriang D) (h₁ : φ.hom₁ = ψ.hom₁)
    (h32 : Subsingleton (T.obj₃ ⟶ T'.obj₂)) :
    φ.hom₂ = ψ.hom₂ := sorry

-- Proof sketch: from the difference morphism `(0,b,0)`, exactness gives a factorization through
-- both `T.mor₁` and `T'.mor₁`; the subsingleton hypotheses on
-- `Hom(T.obj₁,T'.obj₁)` and `Hom(T.obj₃,T'.obj₁)` force the factor maps, hence `b`, to vanish.
/-- Companion to Lemma 13.4.8, case `(3)`: if both `Hom(T.obj₁,T'.obj₁)` and `Hom(T.obj₃,T'.obj₁)`
are subsingleton, then the middle component is determined by the third component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₁_obj₁_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₃ : φ.hom₃ = ψ.hom₃)
    (h11 : Subsingleton (T.obj₁ ⟶ T'.obj₁)) (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

-- Proof sketch: this is dual to case `(3)`, now using the exactness segment around the third
-- components together with the subsingleton hypotheses on `Hom(T.obj₃,T'.obj₁)` and
-- `Hom(T.obj₃,T'.obj₃)`.
/-- Companion to Lemma 13.4.8, case `(4)`: if both `Hom(T.obj₃,T'.obj₁)` and
`Hom(T.obj₃,T'.obj₃)` are subsingleton, then the middle component is determined by the first
component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₁_and_obj₃_obj₃
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁)
    (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) (h33 : Subsingleton (T.obj₃ ⟶ T'.obj₃)) :
    φ.hom₂ = ψ.hom₂ := sorry

-- Proof sketch: use the shifted exactness segment ending in `T'.obj₁⟦1⟧` together with the
-- unshifted exactness through `T'.obj₁`; the subsingleton hypotheses on
-- `Hom(T.obj₁⟦1⟧,T'.obj₃)` and `Hom(T.obj₃,T'.obj₁)` force the relevant factors to vanish.
/-- Companion to Lemma 13.4.8, case `(5)`: if both `Hom(T.obj₁⟦1⟧,T'.obj₃)` and
`Hom(T.obj₃,T'.obj₁)` are subsingleton, then the middle component is unique. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_shift_obj₁_obj₃_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (h13 : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃))
    (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Lemma 13.4.8: for a morphism between distinguished triangles in a pretriangulated category,
the middle component is uniquely determined by the outer components whenever one of the five
listed Hom-vanishing conditions holds. -/
-- Proof sketch: subtract two triangle morphisms with the same first and third components to
-- reduce to a triangle morphism `(0,b,0)`. Then use the exactness statements of Lemma 13.4.2 for
-- the covariant or contravariant Hom functors, together with the stated vanishing hypotheses, to
-- force `b = 0` in each of the five cases.
theorem triangleMorphism_hom₂_eq_of_hom_vanishing
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hvan :
      Subsingleton (T.obj₂ ⟶ T'.obj₁) ∨
        Subsingleton (T.obj₃ ⟶ T'.obj₂) ∨
          (Subsingleton (T.obj₁ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₁)) ∨
            (Subsingleton (T.obj₃ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₃)) ∨
              (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) ∧
                Subsingleton (T.obj₃ ⟶ T'.obj₁))) :
    φ.hom₂ = ψ.hom₂ := by
  rcases hvan with h21 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₂_obj₁ hT' h₃ h21
  rcases hvan with h32 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₂ hT h₁ h32
  rcases hvan with h11 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₁_obj₁_and_obj₃_obj₁
      hT hT' h₃ h11.1 h11.2
  rcases hvan with h33 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₁_and_obj₃_obj₃
      hT hT' h₁ h33.1 h33.2
  exact triangleMorphism_hom₂_eq_of_subsingleton_hom_shift_obj₁_obj₃_and_obj₃_obj₁
    hT hT' h₁ h₃ hvan.1 hvan.2

/-- Owner-level corollary of Lemma 13.4.8: under any of the five Hom-vanishing alternatives, a
parallel morphism of distinguished triangles is determined by its first and third components. -/
theorem triangleMorphism_eq_of_outer_eq_of_hom_vanishing
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hvan :
      Subsingleton (T.obj₂ ⟶ T'.obj₁) ∨
        Subsingleton (T.obj₃ ⟶ T'.obj₂) ∨
          (Subsingleton (T.obj₁ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₁)) ∨
            (Subsingleton (T.obj₃ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₃)) ∨
              (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) ∧
                Subsingleton (T.obj₃ ⟶ T'.obj₁))) :
    φ = ψ :=
  Triangle.hom_ext φ ψ h₁
    (triangleMorphism_hom₂_eq_of_hom_vanishing hT hT' h₁ h₃ hvan) h₃

end

/-! ### Lemma_13_4_9 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ZeroObject

/-
Domain-style sampling:
- primary domain: distinguished triangles in a pretriangulated category, specialized to the cone
  on a fixed morphism `f : X ⟶ Y`;
- sampled owner declarations:
  `Pretriangulated.Triangle.isZero₃_iff_isIso₁`,
  `Pretriangulated.Triangle.distinguished_iff_of_isZero₃`;
- best owner abstraction: the canonical owner is `Triangle` equipped with the distinguished-triangle
  predicate `distTriang`; the book statement here is a source-facing bridge built from the owner
  characterization of an isomorphism by the distinguished zero cone;
- primitive data: a single morphism `f : X ⟶ Y`;
- derived API: the zero-object criterion for an arbitrary distinguished triangle `Triangle.mk f g h`
  on `f`.

Source/core/bridge triage:
- `source-facing`: the textbook criterion phrased for a fixed morphism `f`;
- `core/canonical`: `Triangle.isZero₃_iff_isIso₁` and
  `Triangle.distinguished_iff_of_isZero₃`;
- `bridge/view`: specialize those canonical owners to triangles of the form `Triangle.mk f g h`.
-/

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

-- Proof sketch: `Triangle.isZero₃_iff_isIso₁` is the owner equivalence for any distinguished
-- triangle on `f`, and `Triangle.distinguished_iff_of_isZero₃` specializes it to the zero cone
-- `Triangle.mk f 0 0`.
/- Lemma 13.4.9, source-facing clause `(1) ↔ (3)`: a morphism `f : X ⟶ Y` is an isomorphism
if and only if every distinguished triangle `Triangle.mk f g h` on `f` has zero third object. -/
set_option linter.unusedVariables false in
theorem isIso_iff_isZero_obj₃_of_distinguished_triangle {X Y : D} (f : X ⟶ Y) :
    IsIso f ↔
      ∀ ⦃Z : D⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
        (hT : Triangle.mk f g h ∈ distTriang D), IsZero Z := by
  constructor
  · intro hf Z g h hT
    simpa using (Triangle.isZero₃_of_isIso₁ (Triangle.mk f g h) hT hf)
  · intro hzero
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hzero hT)

/-- Lemma 13.4.9, source-facing clause `(1) ↔ (2)`: for a morphism `f : X ⟶ Y` in a
pretriangulated category, `f` is an isomorphism if and only if the zero cone
`Triangle.mk f 0 0` is distinguished. -/
theorem isIso_iff_zero_cone_triangle_distinguished {X Y : D} (f : X ⟶ Y) :
    IsIso f ↔ Triangle.mk f (0 : Y ⟶ 0) 0 ∈ distTriang D := by
  simpa using
    (Triangle.distinguished_iff_of_isZero₃
      (Triangle.mk f (0 : Y ⟶ 0) 0) (isZero_zero D)).symm

end CategoryTheory

/-! ### Lemma_13_4_10 (from Chap13) -/
noncomputable section

universe v u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]

/- Domain-style sampling for Lemma 13.4.10:
- primary domain: distinguished triangles in a pretriangulated category and their behavior under
  binary direct sums/products;
- sampled core/canonical declarations:
  `CategoryTheory.productTriangle`,
  `CategoryTheory.Pretriangulated.productTriangle_distinguished`,
  `CategoryTheory.Pretriangulated.distinguished_iff_of_iso`,
  `CategoryTheory.Limits.pairFunction`;
- best owner abstraction: the canonical owner for the forward implication is the generic
  `productTriangle` of a family of triangles, specialized here to the binary family
  `Limits.pairFunction T₁ T₂`; the source-facing direct sum of two triangles should therefore be
  treated as a bridge/view to that owner rather than as an isolated local product API, and this
  bridge itself lives already in the additive-plus-shift layer before distinguished triangles enter;
- primitive-vs-derived split:
  primitive data are the two triangles `T₁`, `T₂` and their source-facing direct-sum triangle;
  derived API is the comparison with the canonical product owner and the distinguishedness
  consequences obtained from `productTriangle_distinguished`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the direct sum of two triangles is distinguished iff
  both summands are distinguished;
- `core/canonical`: `productTriangle` in the basic triangle layer and
  `productTriangle_distinguished` in the pretriangulated layer;
- `bridge/view`: the source-facing direct-sum triangle `T₁ ⊞ T₂` and its comparison theorem with
  the binary `productTriangle` owner. -/

section

variable [HasBinaryBiproducts D]

namespace Triangle

/-- Internal bridge from a binary biproduct to the generic product over the walking pair. -/
private def biprodIsoPairProduct (X Y : D) : X ⊞ Y ≅ ∏ᶜ pairFunction X Y := by
  let fan : Fan (pairFunction X Y) :=
    Fan.mk (X ⊞ Y) (fun j ↦ WalkingPair.casesOn j biprod.fst biprod.snd)
  let hfan : IsLimit fan := by
    refine mkFanLimit _ (fun s ↦ biprod.lift (s.proj WalkingPair.left) (s.proj WalkingPair.right))
      ?_ ?_
    · intro s j
      cases j <;> simp [fan]
    · intro s m hm
      apply BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y)
      · simpa [fan] using hm WalkingPair.left
      · simpa [fan] using hm WalkingPair.right
  exact (limit.isoLimitCone ⟨fan, hfan⟩).symm

/-- The biproduct of two triangles, formed by taking the biproduct of each object and the direct
sum of each structure morphism. -/
abbrev biprod (T₁ T₂ : Triangle D) : Triangle D :=
  Triangle.mk
    (biprod.map T₁.mor₁ T₂.mor₁)
    (biprod.map T₁.mor₂ T₂.mor₂)
    (biprod.map T₁.mor₃ T₂.mor₃ ≫
      Functor.biprodComparison' (shiftFunctor D (1 : ℤ)) T₁.obj₁ T₂.obj₁)

infixl:70 " ⊞ " => biprod

/-- The canonical comparison isomorphism from the source-facing binary biproduct triangle to the
canonical binary `productTriangle` on the family `(T₁, T₂)`. -/
def biprodIsoProductTrianglePair (T₁ T₂ : Triangle D) :
    T₁ ⊞ T₂ ≅ productTriangle (pairFunction T₁ T₂) := by
  let e₁ : (T₁ ⊞ T₂).obj₁ ≅ (productTriangle (pairFunction T₁ T₂)).obj₁ :=
    (biprodIsoPairProduct T₁.obj₁ T₂.obj₁) ≪≫
      Pi.mapIso (fun j ↦ by cases j <;> exact Iso.refl _)
  let e₂ : (T₁ ⊞ T₂).obj₂ ≅ (productTriangle (pairFunction T₁ T₂)).obj₂ :=
    (biprodIsoPairProduct T₁.obj₂ T₂.obj₂) ≪≫
      Pi.mapIso (fun j ↦ by cases j <;> exact Iso.refl _)
  let e₃ : (T₁ ⊞ T₂).obj₃ ≅ (productTriangle (pairFunction T₁ T₂)).obj₃ :=
    (biprodIsoPairProduct T₁.obj₃ T₂.obj₃) ≪≫
      Pi.mapIso (fun j ↦ by cases j <;> exact Iso.refl _)
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  · sorry
  · sorry
  · sorry

end Triangle

end

section

variable [Pretriangulated D]

-- Proof sketch: identify each binary biproduct object with the corresponding binary product via
-- the universal property of the exact binary product fan on each component; the resulting
-- comparison isomorphism is `Triangle.biprodIsoProductTrianglePair`.
/-- Companion to `Triangle.biprodIsoProductTrianglePair`: the source-facing direct-sum triangle is
distinguished exactly when the canonical binary `productTriangle` on the pair `(T₁, T₂)` is
distinguished. -/
theorem triangle_biprod_distinguished_iff_productTriangle_pair {T₁ T₂ : Triangle D} :
    (T₁ ⊞ T₂) ∈ distTriang D ↔
      productTriangle (pairFunction T₁ T₂) ∈ distTriang D := by
  simpa using distinguished_iff_of_iso (Triangle.biprodIsoProductTrianglePair T₁ T₂)

-- Proof sketch: for the forward direction, complete `T₁.mor₁ ⊞ T₂.mor₁` to a distinguished
-- triangle using TR1, extend the summand inclusions by TR3, and apply Remark 13.4.4 to show the
-- induced map from `T₁ ⊞ T₂` is an isomorphism. For the reverse direction, first
-- pass to the canonical owner `productTriangle (pairFunction T₁ T₂)` via the bridge theorem
-- above and then apply `productTriangle_distinguished`; for the forward direction, view each
-- summand triangle as a direct summand of the distinguished biproduct triangle and apply the same
-- special-triangle two-out-of-three argument.
/-- Lemma 13.4.10: for triangles `T₁` and `T₂` in a pretriangulated category, the direct-sum
triangle `(X ⊕ X', Y ⊕ Y', Z ⊕ Z', f ⊕ f', g ⊕ g', h ⊕ h')` is distinguished if and only if both
summand triangles are distinguished. -/
theorem triangle_biprod_distinguished_iff {T₁ T₂ : Triangle D} :
    (T₁ ⊞ T₂) ∈ distTriang D ↔ T₁ ∈ distTriang D ∧ T₂ ∈ distTriang D := by
  constructor
  · intro h
    sorry
  · rintro ⟨h₁, h₂⟩
    rw [triangle_biprod_distinguished_iff_productTriangle_pair]
    exact productTriangle_distinguished (pairFunction T₁ T₂) <| by
      intro j
      cases j <;> assumption

end

end CategoryTheory

/-! ### Lemma_13_4_11 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling:
- primary domain: distinguished triangles in pretriangulated categories, split epimorphisms, and
  the canonical binary biproduct attached to a split distinguished triangle;
- sampled owner declarations:
  `Triangle.mor₃_eq_zero_iff_epi₂`,
  `Triangle.epi₂`,
  `CategoryTheory.isSplitEpi_of_epi`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- best owner abstraction: `IsSplitEpi T.mor₂` is the canonical owner for the existence of a right
  inverse to `T.mor₂`, and `exists_iso_binaryBiproduct_of_distTriang` is the canonical owner for
  the induced biproduct splitting of the triangle;
- primitive data: a distinguished triangle `T`, its distinguishedness proof `hT`, and either the
  vanishing hypothesis `T.mor₃ = 0` or an explicit right inverse `s` to `T.mor₂`;
-- derived API: the chosen section supplied by `IsSplitEpi T.mor₂` and the induced map
-- `biprod.desc T.mor₁ s`.

Source/core/bridge triage:
- `source-facing`: the statement that a right inverse to `T.mor₂` produces a biproduct splitting;
- `core/canonical`: `IsSplitEpi T.mor₂` and
  `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
-- `bridge/view`: the `IsIso` statement for `biprod.desc T.mor₁ s`.
-/

-- Proof sketch: `T.mor₃ = 0` makes `T.mor₂` epi by `Triangle.epi₂`; pretriangulated categories
-- are split-epi categories, so the canonical owner `IsSplitEpi T.mor₂` follows from the ambient
-- `SplitEpiCategory` instance.
/-- Lemma 13.4.11 (1): if the third morphism of a distinguished triangle is zero, then the second
morphism is split epic. -/
theorem isSplitEpi_mor₂_of_distinguished_mor₃_eq_zero {T : Triangle D}
    (hT : T ∈ distTriang D) (hzero : T.mor₃ = 0) :
    IsSplitEpi T.mor₂ := by
  letI : Epi T.mor₂ := T.epi₂ hT hzero
  exact isSplitEpi_of_epi T.mor₂

-- Proof sketch: a right inverse `s` to `T.mor₂` forces `T.mor₃ = 0` because
-- `T.mor₂` is then split epic, hence epic, so the third morphism vanishes. The exactness
-- criterion `coyoneda_exact₂` then supplies the complementary projection needed to package the
-- given section `s` into the biproduct datum `binaryBiproductData`, whose universal isomorphism
-- identifies `biprod.desc T.mor₁ s` as an inverse.
/-- Lemma 13.4.11 (2): if `s : Z ⟶ Y` is a right inverse to the second morphism in a
distinguished triangle `(X, Y, Z, f, g, h)`, then the induced map `X ⊞ Z ⟶ Y` with components
`f` and `s` is an isomorphism. -/
theorem isIso_biprod_desc_of_distinguished_right_inverse {T : Triangle D}
    (hT : T ∈ distTriang D) (s : T.obj₃ ⟶ T.obj₂) (hs : s ≫ T.mor₂ = 𝟙 T.obj₃) :
    IsIso (biprod.desc T.mor₁ s) := by
  have hzero : T.mor₃ = 0 := by
    haveI : IsSplitEpi T.mor₂ := IsSplitEpi.mk' { section_ := s, id := hs }
    exact Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi T.mor₂)
  obtain ⟨fst, hfst⟩ := T.coyoneda_exact₂ hT (𝟙 T.obj₂ - T.mor₂ ≫ s) (by simp [hs])
  have htotal : fst ≫ T.mor₁ + T.mor₂ ≫ s = 𝟙 T.obj₂ := by
    rw [← hfst, sub_add_cancel]
  let d := binaryBiproductData T hT hzero s hs fst htotal
  let e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃ := biprod.uniqueUpToIso _ _ d.isBilimit
  have hdesc : biprod.desc T.mor₁ s = e.inv := by
    apply biprod.hom_ext'
    · simp [e, d]
    · simp [e, d]
  rw [hdesc]
  infer_instance

/- Lemma 13.4.11 (3): for any objects `X'` and `Z'` of a pre-triangulated category, the standard
split triangle `(X', X' ⊞ Z', Z', (1,0), (0,1), 0)` is distinguished. This is exactly the
canonical theorem `CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`. -/
recall CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished

end CategoryTheory
