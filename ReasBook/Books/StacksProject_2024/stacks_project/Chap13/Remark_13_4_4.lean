import Mathlib
import Mathlib.CategoryTheory.Triangulated.Yoneda

-- Declarations for this item will be appended below by the statement pipeline.

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

/-- Helper for Remark 13.4.4: after shifting and rotating, the first morphism is definitionally the
shift of the original second morphism. -/
lemma rotate_shift_iso_mor₁ (T : Triangle D) (n : ℤ) :
    ((Triangle.shiftFunctor D n).obj T.rotate).mor₁ =
      ((Triangle.shiftFunctor D n).obj T).rotate.mor₁ := by
  -- The first edge is unchanged by the rotate/shift comparison once both sides are unfolded.
  rfl

/-- Helper for Remark 13.4.4: after shifting and rotating, the second square of
`rotate_shift_iso` is exactly the unit-scalar compatibility for composition. -/
lemma rotate_shift_iso_mor₂ (T : Triangle D) (n : ℤ) :
    ((Triangle.shiftFunctor D n).obj T.rotate).mor₂ ≫ (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁ =
      ((Triangle.shiftFunctor D n).obj T).rotate.mor₂ := by
  -- Unfold the shifted rotate once, then move the sign unit through the composite.
  dsimp [Triangle.rotate, Triangle.shiftFunctor]
  let f :
      (CategoryTheory.shiftFunctor D n).obj T.obj₃ ⟶
        ((CategoryTheory.shiftFunctor D (1 : ℤ) ⋙ CategoryTheory.shiftFunctor D n).obj T.obj₁) :=
    (CategoryTheory.shiftFunctor D n).map T.mor₃
  let g :
      ((CategoryTheory.shiftFunctor D (1 : ℤ) ⋙ CategoryTheory.shiftFunctor D n).obj T.obj₁) ⟶
        ((CategoryTheory.shiftFunctor D n ⋙ CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁) :=
    (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁
  refine (CategoryTheory.Linear.units_smul_comp (R := ℤ) n.negOnePow f g).trans ?_
  -- The target side is the same composite after unfolding the local names `f` and `g`.
  rfl

/-- Helper for Remark 13.4.4: the third square of `rotate_shift_iso` reduces to the naturality of
`shiftFunctorComm`, after applying the sign unit and negation once to the basic commutation square.
-/
lemma rotate_shift_iso_mor₃_scaled_naturality (T : Triangle D) (n : ℤ) :
    -(n.negOnePow •
        ((CategoryTheory.shiftFunctor D n).map ((CategoryTheory.shiftFunctor D (1 : ℤ)).map T.mor₁) ≫
          (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₂)) =
      -(n.negOnePow •
        ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁ ≫
          (CategoryTheory.shiftFunctor D (1 : ℤ)).map
            ((CategoryTheory.shiftFunctor D n).map T.mor₁))) := by
  -- Apply the sign unit and negation to the basic `shiftFunctorComm` naturality square once.
  let A := (CategoryTheory.shiftFunctor D n).map
    ((CategoryTheory.shiftFunctor D (1 : ℤ)).map T.mor₁)
  let c₁ := (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁
  let c₂ := (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₂
  let B := (CategoryTheory.shiftFunctor D (1 : ℤ)).map
    ((CategoryTheory.shiftFunctor D n).map T.mor₁)
  -- Repackage the commutation square in the exact scaled-and-negated form needed downstream.
  change -(n.negOnePow • (A ≫ c₂)) = -(n.negOnePow • (c₁ ≫ B))
  exact congrArg (fun k => - (n.negOnePow • k))
    (by simpa [A, B, c₁, c₂] using (shiftFunctorComm D (1 : ℤ) n).hom.naturality T.mor₁)

/-- Helper for Remark 13.4.4: the third `Triangle.isoMk` square for the rotate/shift comparison
is exactly the scaled naturality identity for `shiftFunctorComm` in the target shape. -/
lemma rotate_shift_iso_mor₃_left_normalized (T : Triangle D) (n : ℤ) :
    ((Triangle.shiftFunctor D n).obj T.rotate).mor₃ ≫
        (CategoryTheory.shiftFunctor D (1 : ℤ)).map
          (𝟙 (((Triangle.shiftFunctor D n).obj T.rotate).obj₁)) =
      -(n.negOnePow •
        ((CategoryTheory.shiftFunctor D n).map ((CategoryTheory.shiftFunctor D (1 : ℤ)).map T.mor₁) ≫
          (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₂)) := by
  -- Unfold the shifted rotate once and remove the identity postcomposition on the codomain.
  dsimp [Triangle.rotate, Triangle.shiftFunctor]
  let A :=
    (CategoryTheory.shiftFunctor D n).map ((CategoryTheory.shiftFunctor D (1 : ℤ)).map T.mor₁)
  let c := (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₂
  -- After unfolding, the left side is just a unit multiple of a negated composite.
  simpa [A, c, Preadditive.neg_comp] using
    (smul_neg n.negOnePow (A ≫ c))

/-- Helper for Remark 13.4.4: the target side of the third `Triangle.isoMk` square is the same
scaled-and-negated composite after unfolding the rotated shifted triangle. -/
lemma rotate_shift_iso_mor₃_right_normalized (T : Triangle D) (n : ℤ) :
    (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁ ≫
        ((Triangle.shiftFunctor D n).obj T).rotate.mor₃ =
      -(n.negOnePow •
        ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁ ≫
          (CategoryTheory.shiftFunctor D (1 : ℤ)).map
            ((CategoryTheory.shiftFunctor D n).map T.mor₁))) := by
  -- TODO: normalize the right side by first rewriting `((Triangle.shiftFunctor D n).obj T).rotate.mor₃`
  -- to `-((shiftFunctor D 1).map (n.negOnePow • ...))`, then use a directed
  -- `Functor.map_units_smul` followed by the postcomposition scalar rule in a form compatible
  -- with the leading negation.
  sorry

/-- Helper for Remark 13.4.4: the third `Triangle.isoMk` square for the rotate/shift comparison
is exactly the scaled naturality identity for `shiftFunctorComm` in the target shape. -/
lemma rotate_shift_iso_mor₃_exact (T : Triangle D) (n : ℤ) :
    ((Triangle.shiftFunctor D n).obj T.rotate).mor₃ ≫
        (CategoryTheory.shiftFunctor D (1 : ℤ)).map
          (𝟙 (((Triangle.shiftFunctor D n).obj T.rotate).obj₁)) =
      (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁ ≫
        ((Triangle.shiftFunctor D n).obj T).rotate.mor₃ := by
  -- Normalize both sides to the same scaled-and-negated naturality square before applying the
  -- dedicated commutation lemma.
  have hLeft := rotate_shift_iso_mor₃_left_normalized T n
  have hNat := rotate_shift_iso_mor₃_scaled_naturality T n
  have hRight := rotate_shift_iso_mor₃_right_normalized T n
  exact hLeft.trans (hNat.trans hRight.symm)

/-- Helper for Remark 13.4.4: shifting a rotated triangle agrees with rotating the shifted
triangle, up to the canonical `shiftFunctorComm` comparison on the third object. -/
noncomputable def rotate_shift_iso (T : Triangle D) (n : ℤ) :
    (T.rotate⟦n⟧ : Triangle D) ≅ ((T⟦n⟧ : Triangle D).rotate) := by
  -- Route correction: the first two squares are the formal objectwise identities coming from the
  -- definitions of `rotate` and `Triangle.shiftFunctor`; the only remaining work is the final
  -- normalization from `rotate_shift_iso_mor₃_scaled_naturality` to the exact `Triangle.isoMk`
  -- third-square shape.
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((shiftFunctorComm D (1 : ℤ) n).app T.obj₁) ?_ ?_ ?_
  · simpa using rotate_shift_iso_mor₁ T n
  · simpa using rotate_shift_iso_mor₂ T n
  · simpa using rotate_shift_iso_mor₃_exact T n

/-- Helper for Remark 13.4.4: the `exact₁` field of `T.rotate` is the shifted `exact₂` field of
`T`, after identifying the rotated third map with the negative of the shifted first map. -/
lemma rotate_exact₁_from_shift_exact₂ [IsSpecial T] (n : ℤ) (W : D) :
    Function.Exact
      ((preadditiveCoyoneda.obj (op W)).map ((T.rotate⟦n⟧ : Triangle D).mor₃))
      ((preadditiveCoyoneda.obj (op W)).map (((T.rotate⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧')) := by
  -- TODO: first convert `exact₂ 1 W` for `S := T⟦n⟧` into exactness of the positive pair
  -- `(coyoneda_map_add_hom W (S.mor₁⟦1⟧'), coyoneda_map_add_hom W (S.mor₂⟦1⟧'))` by an
  -- additive-hom level normalization of covariant Yoneda on negative morphisms, then apply
  -- `exact_of_neg_left` and transport the resulting unshifted exactness of `S.rotate` across
  -- `rotate_shift_iso T n`.
  sorry

end

instance instRotate [IsSpecial T] : IsSpecial T.rotate := by
  -- TODO: for each `n`, let `S := T⟦n⟧`, transport the unshifted exactness fields of `S.rotate`
  -- back across `rotate_shift_iso T n`, and use `rotate_exact₁_from_shift_exact₂` for the third
  -- field once the sign-normalization bridge there is completed.
  sorry

noncomputable instance instInvRotate [IsSpecial T] : IsSpecial T.invRotate := by
  let e := (invRotateIsoRotateRotateShiftFunctorNegOne D).app T
  -- Transport specialness back from the explicit `rotate ∘ rotate ∘ shift(-1)` model of
  -- `invRotate`.
  exact IsSpecial.of_iso e.symm (inferInstance : IsSpecial (((T.rotate).rotate⟦(-1 : ℤ)⟧ : Triangle D)))

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
noncomputable abbrev triangleOpEquivalence_functor_obj_shift_iso (T : Triangle D) (n : ℤ) :
    ((triangleOpEquivalence D).functor.obj (op (T⟦n⟧ : Triangle D))) ≅
      (((triangleOpEquivalence D).functor.obj (op T))⟦n⟧ : Triangle Dᵒᵖ) :=
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
      -- Reuse the shifted image of the third isomorphism to solve the inverse-rotation lift.
      have hmap : IsIso ((shiftFunctor D (-1)).map φ.hom₃) := by
        infer_instance
      letI : IsIso ((shiftFunctor D (-1)).map φ.hom₃) := hmap
      let e₃ : (shiftFunctor D (-1)).obj T.obj₃ ≅ (shiftFunctor D (-1)).obj T'.obj₃ :=
        asIso ((shiftFunctor D (-1)).map φ.hom₃)
      refine ⟨h ≫ e₃.inv, ?_⟩
      have eq := ((invRotate D).map φ).comm₁
      dsimp only [invRotate] at eq
      apply (cancel_mono φ.hom₁).1
      have hrewrite : ((h ≫ e₃.inv) ≫ T.invRotate.mor₁) ≫ φ.hom₁ = h ≫ T'.invRotate.mor₁ := by
        calc
          ((h ≫ e₃.inv) ≫ T.invRotate.mor₁) ≫ φ.hom₁ =
              h ≫ e₃.inv ≫ (T.invRotate.mor₁ ≫ φ.hom₁) := by
                simp [Category.assoc]
          _ = h ≫ e₃.inv ≫ (((shiftFunctor D (-1)).map φ.hom₃) ≫ T'.invRotate.mor₁) := by
                simpa [Category.assoc] using congrArg (fun m => h ≫ e₃.inv ≫ m) eq
          _ = h ≫ e₃.inv ≫ e₃.hom ≫ T'.invRotate.mor₁ := by
                rfl
          _ = h ≫ T'.invRotate.mor₁ := by
                simp [Category.assoc]
      exact hrewrite.trans hh.symm
    calc
      (k ≫ T.invRotate.mor₁) ≫ T.mor₁ = k ≫ (T.invRotate.mor₁ ≫ T.mor₁) := by
        simp [Category.assoc]
      _ = k ≫ 0 := by
        have hz : T.invRotate.mor₁ ≫ T.mor₁ = 0 := by
          simpa [invRotate] using
            Triangle.IsSpecial.zero₁₂_unshifted (inferInstance : Triangle.IsSpecial T.invRotate)
        rw [hz]
      _ = 0 := by
        -- The final composite vanishes because postcomposition with the zero morphism is zero.
        simpa using (comp_zero (f := k))
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
  -- Pass to the opposite-category morphism, where co-speciality is exactly speciality.
  let ψ := (triangleOpEquivalence D).functor.map (op φ)
  letI : IsIso ψ.hom₁ := by
    -- The first component of `ψ` is the opposite of `φ.hom₃`.
    dsimp [ψ]
    infer_instance
  letI : IsIso ψ.hom₃ := by
    -- The third component of `ψ` is the opposite of `φ.hom₁`.
    dsimp [ψ]
    infer_instance
  have hψ : IsIso ψ.hom₂ :=
    isIso₂_of_isIso₁₃_of_isSpecial ψ hT' hT inferInstance inferInstance
  -- Re-express the middle component as `φ.hom₂.op` before reflecting the isomorphism back.
  dsimp [ψ] at hψ
  letI : IsIso φ.hom₂.op := hψ
  -- Reflect the isomorphism statement back from the opposite morphism.
  exact isIso_of_op φ.hom₂

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
