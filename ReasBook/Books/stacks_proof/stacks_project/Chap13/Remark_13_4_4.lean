import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
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

/-- Remark 13.4.4 (1): a triangle is special when, for every object `W`, the long covariant Hom
sequence `Hom_D(W,-)` attached to every shifted triangle `T⟦n⟧` is exact. Here this is recorded by
the three exact shifted Hom-map pairs attached to `T⟦n⟧`; the successive zero composites are
derived below from `Function.Exact.comp_eq_zero`. -/
@[stacks 09WA]
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

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: if `e : T ≅ T'` is a triangle isomorphism, then the first
commutative square can be rewritten using the inverse components. -/
lemma comm₁_inv {T' : Triangle D} (e : T ≅ T') :
    inv e.hom.hom₁ ≫ T.mor₁ = T'.mor₁ ≫ inv e.hom.hom₂ := by
  -- Postcompose the first commutative square with the inverse second component and simplify.
  simpa [Category.assoc] using
    congrArg (fun k ↦ inv e.hom.hom₁ ≫ k ≫ inv e.hom.hom₂) e.hom.comm₁

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: if `e : T ≅ T'` is a triangle isomorphism, then the second
commutative square can be rewritten using the inverse components. -/
lemma comm₂_inv {T' : Triangle D} (e : T ≅ T') :
    inv e.hom.hom₂ ≫ T.mor₂ = T'.mor₂ ≫ inv e.hom.hom₃ := by
  -- Postcompose the second commutative square with the inverse third component and simplify.
  simpa [Category.assoc] using
    congrArg (fun k ↦ inv e.hom.hom₂ ≫ k ≫ inv e.hom.hom₃) e.hom.comm₂

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: if `e : T ≅ T'` is a triangle isomorphism, then the third
commutative square can be rewritten using the inverse shifted first component. -/
lemma comm₃_inv {T' : Triangle D} (e : T ≅ T') :
    inv e.hom.hom₃ ≫ T.mor₃ = T'.mor₃ ≫ inv (e.hom.hom₁⟦(1 : ℤ)⟧') := by
  -- Postcompose the third commutative square with the inverse shifted first component.
  simpa [Category.assoc] using
    congrArg (fun k ↦ inv e.hom.hom₃ ≫ k ≫ inv (e.hom.hom₁⟦(1 : ℤ)⟧')) e.hom.comm₃

omit [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: postcomposition with an isomorphism has the obvious left inverse on
covariant Hom groups. -/
lemma hom_add_equiv_left_inv {X Y : D} (W : D) (i : X ≅ Y) (f : W ⟶ X) :
    (f ≫ i.hom) ≫ i.inv = f := by
  -- Cancel the inverse pair inside the postcomposition expression.
  simp [Category.assoc]

omit [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: postcomposition with an isomorphism has the obvious right inverse on
covariant Hom groups. -/
lemma hom_add_equiv_right_inv {X Y : D} (W : D) (i : X ≅ Y) (g : W ⟶ Y) :
    (g ≫ i.inv) ≫ i.hom = g := by
  -- Cancel the inverse pair inside the postcomposition expression.
  simp [Category.assoc]

omit [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  { toFun := fun f ↦ f ≫ i.hom
    invFun := fun g ↦ g ≫ i.inv
    left_inv := hom_add_equiv_left_inv W i
    right_inv := hom_add_equiv_right_inv W i
    map_add' := hom_add_equiv_map_add W i }

/-- Helper for Remark 13.4.4: the covariant Yoneda map of a morphism, viewed as an
`AddMonoidHom` between the underlying Hom groups. -/
abbrev coyoneda_map_add_hom {X Y : D} (W : D) (f : X ⟶ Y) :
    ((preadditiveCoyoneda.obj (op W)).obj X) →+ ((preadditiveCoyoneda.obj (op W)).obj Y) :=
  ((preadditiveCoyoneda.obj (op W)).map f).hom

omit [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: evaluating the covariant Yoneda map of an isomorphism agrees with
ordinary postcomposition on Hom groups. -/
lemma coyoneda_map_hom_add_equiv_apply {X Y : D} (W : D) (i : X ≅ Y) (f : W ⟶ X) :
    ((preadditiveCoyoneda.obj (op W)).map i.hom) f = hom_add_equiv W i f :=
  rfl

omit [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: negating the covariant Yoneda map is the same as mapping the
negated morphism. -/
lemma coyoneda_map_neg {X Y : D} (W : D) (f : X ⟶ Y) :
    ((preadditiveCoyoneda.obj (op W)).map (-f)) =
      -((preadditiveCoyoneda.obj (op W)).map f) := by
  -- Both sides are the same pointwise postcomposition map after moving the negation through the
  -- covariant Hom functor.
  ext g
  change g ≫ (-f) = -(g ≫ f)
  simp [Preadditive.comp_neg]

omit [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the underlying additive hom of the covariant Yoneda map of `-f` is
the negation of the underlying additive hom of the map of `f`. -/
lemma coyoneda_map_hom_neg {X Y : D} (W : D) (f : X ⟶ Y) :
    (((preadditiveCoyoneda.obj (op W)).map (-f)).hom) =
      -(((preadditiveCoyoneda.obj (op W)).map f).hom) := by
  -- Project the morphism-level negation identity to the underlying additive hom.
  simpa using congrArg (fun k ↦ k.hom) (coyoneda_map_neg W f)

omit [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  simpa [Category.assoc] using congrArg (fun k ↦ x ≫ k) h

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: shifting the inverse first commutative square of a triangle
isomorphism yields the corresponding square for the shifted first morphisms. -/
lemma comm₁_inv_shift {T' : Triangle D} (e : T ≅ T') :
    inv (e.hom.hom₁⟦(1 : ℤ)⟧') ≫ (T.mor₁⟦(1 : ℤ)⟧') =
      (T'.mor₁⟦(1 : ℤ)⟧') ≫ inv (e.hom.hom₂⟦(1 : ℤ)⟧') := by
  -- Shift the inverse square from `comm₁_inv` and normalize inverses under the shift functor.
  simpa using congrArg (fun k ↦ k⟦(1 : ℤ)⟧') (comm₁_inv e)

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  -- Transport exactness backward along the Hom-group equivalences induced by the inverse
  -- triangle isomorphism, so the ladder theorem can reuse the given exact pair verbatim.
  apply Function.Exact.of_ladder_addEquiv_of_exact'
      (hom_add_equiv W (asIso e.hom.hom₁).symm)
      (hom_add_equiv W (asIso e.hom.hom₂).symm)
      (hom_add_equiv W (asIso e.hom.hom₃).symm)
  · -- The first square is exactly the inverse-oriented first triangle square on covariant Hom.
    simpa [coyoneda_map_add_hom] using
      coyoneda_hom_add_equiv_naturality W (asIso e.hom.hom₁).symm (asIso e.hom.hom₂).symm
        (comm₁_inv e)
  · -- The second square is exactly the inverse-oriented second triangle square on covariant Hom.
    simpa [coyoneda_map_add_hom] using
      coyoneda_hom_add_equiv_naturality W (asIso e.hom.hom₂).symm (asIso e.hom.hom₃).symm
        (comm₂_inv e)
  · exact H

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  -- Transport exactness backward along the Hom-group equivalences induced by the inverse
  -- triangle isomorphism, matching the exact pair `T.mor₂, T.mor₃`.
  apply Function.Exact.of_ladder_addEquiv_of_exact'
      (hom_add_equiv W (asIso e.hom.hom₂).symm)
      (hom_add_equiv W (asIso e.hom.hom₃).symm)
      (hom_add_equiv W (asIso (e.hom.hom₁⟦(1 : ℤ)⟧')).symm)
  · -- The first square is the inverse-oriented second triangle square on covariant Hom.
    simpa [coyoneda_map_add_hom] using
      coyoneda_hom_add_equiv_naturality W (asIso e.hom.hom₂).symm (asIso e.hom.hom₃).symm
        (comm₂_inv e)
  · -- The second square is the inverse-oriented third triangle square on covariant Hom.
    simpa [coyoneda_map_add_hom] using
      coyoneda_hom_add_equiv_naturality W (asIso e.hom.hom₃).symm
        (asIso (e.hom.hom₁⟦(1 : ℤ)⟧')).symm (comm₃_inv e)
  · exact H

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  -- Transport exactness backward along the inverse-oriented third square and its shifted first
  -- square, so the ladder theorem sees the exact pair `T.mor₃, T.mor₁⟦1⟧'`.
  apply Function.Exact.of_ladder_addEquiv_of_exact'
      (hom_add_equiv W (asIso e.hom.hom₃).symm)
      (hom_add_equiv W (asIso (e.hom.hom₁⟦(1 : ℤ)⟧')).symm)
      (hom_add_equiv W (asIso (e.hom.hom₂⟦(1 : ℤ)⟧')).symm)
  · -- The first square is the inverse-oriented third triangle square on covariant Hom.
    simpa [coyoneda_map_add_hom] using
      coyoneda_hom_add_equiv_naturality W (asIso e.hom.hom₃).symm
        (asIso (e.hom.hom₁⟦(1 : ℤ)⟧')).symm (comm₃_inv e)
  · -- The second square is the shifted inverse-oriented first triangle square on covariant Hom.
    simpa [coyoneda_map_add_hom] using
      coyoneda_hom_add_equiv_naturality W (asIso (e.hom.hom₁⟦(1 : ℤ)⟧')).symm
        (asIso (e.hom.hom₂⟦(1 : ℤ)⟧')).symm (comm₁_inv_shift e)
  · exact H

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

omit [HasShift D ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: postcomposition with a negated unit multiple can be normalized in a
single preadditive rewrite step. -/
lemma comp_neg_units_smul {A B C : D} (c : A ⟶ B) (u : ℤˣ) (g : B ⟶ C) :
    c ≫ (-(u • g)) = -(u • (c ≫ g)) := by
  -- Move the negation and the unit scalar through postcomposition once, so later proofs stay in
  -- the same normal form.
  rw [Preadditive.comp_neg, CategoryTheory.Linear.comp_units_smul]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after shifting and rotating, the first morphism is definitionally the
shift of the original second morphism. -/
lemma rotate_shift_iso_mor₁ (T : Triangle D) (n : ℤ) :
    ((Triangle.shiftFunctor D n).obj T.rotate).mor₁ =
      ((Triangle.shiftFunctor D n).obj T).rotate.mor₁ := by
  -- The first edge is unchanged by the rotate/shift comparison once both sides are unfolded.
  rfl

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  refine (CategoryTheory.Linear.units_smul_comp n.negOnePow f g).trans ?_
  -- The target side is the same composite after unfolding the local names `f` and `g`.
  rfl

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
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
  exact congrArg (fun k ↦ - (n.negOnePow • k))
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
  -- Unfold the rotated shifted triangle once, then use the dedicated normalization lemma to keep
  -- the postcomposition in the canonical `-(u • (c ≫ g))` form.
  dsimp [Triangle.rotate, Triangle.shiftFunctor]
  simpa [Functor.map_units_smul] using
    (comp_neg_units_smul
      ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁)
      n.negOnePow
      ((CategoryTheory.shiftFunctor D (1 : ℤ)).map
        ((CategoryTheory.shiftFunctor D n).map T.mor₁)))

/-- Helper for Remark 13.4.4: the shifted second exact pair of `S` can be normalized to the
rotated left-map shape by keeping the left additive negation explicit and removing the single
right-hand negation. -/
lemma rotateShiftCoyonedaExactPair (S : Triangle D) [IsSpecial S] (W : D) :
    Function.Exact
      (-((preadditiveCoyoneda.obj (op W)).map (S.mor₁⟦(1 : ℤ)⟧')))
      ((preadditiveCoyoneda.obj (op W)).map ((S.rotate.mor₁)⟦(1 : ℤ)⟧')) := by
  have hShift :
      Function.Exact
        ((preadditiveCoyoneda.obj (op W)).map ((S⟦(1 : ℤ)⟧ : Triangle D).mor₁))
        ((preadditiveCoyoneda.obj (op W)).map ((S⟦(1 : ℤ)⟧ : Triangle D).mor₂)) :=
    (inferInstance : IsSpecial S).exact₂ 1 W
  -- Normalize the shifted exact pair to the rotated one before transporting exactness.
  have hShift' :
      Function.Exact
        (-((preadditiveCoyoneda.obj (op W)).map (S.mor₁⟦(1 : ℤ)⟧')))
        (-((preadditiveCoyoneda.obj (op W)).map (S.mor₂⟦(1 : ℤ)⟧'))) := by
    simpa [Triangle.shiftFunctor, coyoneda_map_neg] using hShift
  -- The rotated exact pair keeps the left negation but drops the right one.
  change Function.Exact
    (-((preadditiveCoyoneda.obj (op W)).map (S.mor₁⟦(1 : ℤ)⟧')))
    ((preadditiveCoyoneda.obj (op W)).map (S.mor₂⟦(1 : ℤ)⟧'))
  convert exact_of_neg_right hShift' using 1
  ext g
  change g ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map S.mor₂ =
    -(- (g ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map S.mor₂))
  simp
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
  let S : Triangle D := (T⟦n⟧ : Triangle D)
  have hRotate :
      Function.Exact
        ((preadditiveCoyoneda.obj (op W)).map S.rotate.mor₃)
        ((preadditiveCoyoneda.obj (op W)).map (S.rotate.mor₁⟦(1 : ℤ)⟧')) :=
    by
      -- Convert the normalized additive left map back to the literal rotated morphism.
      simpa [Triangle.rotate, coyoneda_map_neg, Preadditive.comp_neg, Preadditive.neg_comp] using
        rotateShiftCoyonedaExactPair S W
  -- Transport the rotated exact pair back along the canonical rotate/shift comparison.
  exact exact₁_transport_of_iso (rotate_shift_iso T n).symm W hRotate

end

instance instRotate [IsSpecial T] : IsSpecial T.rotate := by
  refine
    { exact₂ := ?_
      exact₃ := ?_
      exact₁ := ?_ }
  · intro n W
    let S : Triangle D := (T⟦n⟧ : Triangle D)
    let hS : IsSpecial S := inferInstance
    have hRotate :
        Function.Exact
          ((preadditiveCoyoneda.obj (op W)).map S.rotate.mor₁)
          ((preadditiveCoyoneda.obj (op W)).map S.rotate.mor₂) := by
      -- The first exact pair of `S.rotate` is just the unshifted second exact pair of `S`.
      simpa [Triangle.rotate] using exact₃_unshifted hS W
    -- Transport the exact pair from the rotated shifted triangle back to `T.rotate⟦n⟧`.
    exact exact₂_transport_of_iso (rotate_shift_iso T n).symm W hRotate
  · intro n W
    let S : Triangle D := (T⟦n⟧ : Triangle D)
    let hS : IsSpecial S := inferInstance
    have hRotate :
        Function.Exact
          ((preadditiveCoyoneda.obj (op W)).map S.rotate.mor₂)
          ((preadditiveCoyoneda.obj (op W)).map S.rotate.mor₃) := by
      -- The second exact pair of `S.rotate` is the unshifted third exact pair of `S`, with the
      -- right map negated once by the rotation formula.
      simpa [Triangle.rotate, coyoneda_map_neg] using
        exact_of_neg_right (exact₁_unshifted hS W)
    -- Transport the exact pair from the rotated shifted triangle back to `T.rotate⟦n⟧`.
    exact exact₃_transport_of_iso (rotate_shift_iso T n).symm W hRotate
  · intro n W
    -- The third exact pair of `T.rotate⟦n⟧` was isolated above from the shifted second exact pair
    -- of `T`, so the final field is now a direct reuse of that helper.
    exact rotate_exact₁_from_shift_exact₂ n W

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

/-- Remark 13.4.4 (2): a triangle is co-special precisely when its canonical opposite-category view
is special. As a bridge/view notion, this keeps only the contravariant exactness and rotation API
needed later in the chapter, rather than mirroring the full `IsSpecial` helper surface. -/
@[stacks 09WA]
noncomputable abbrev IsCoSpecial (T : Triangle D) : Prop :=
  IsSpecial ((triangleOpEquivalence D).functor.obj (op T))

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: transporting an opposite morphism across the inverse-oriented
`shiftFunctorOpIso` reduces to the basic opposite-shift naturality square. -/
lemma shiftFunctorOpIso_inv_app_map (n : ℤ) {X Y : D} (f : X ⟶ Y) :
    ((CategoryTheory.shiftFunctor D n).map f).op ≫
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X)) =
    ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op := by
  -- Rewrite the opposite shifted map through `shiftFunctorOpIso`, then cancel the iso pair once.
  let eX := (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).app (op X)
  let eY := (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).app (op Y)
  have hMap :
      (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op =
        eY.hom ≫ ((CategoryTheory.shiftFunctor D n).map f).op ≫ eX.inv := by
    -- This is the owner naturality formula for `shiftFunctorOpIso`, specialized to `f.op`.
    simpa [eX, eY] using
      (shiftFunctor_op_map f.op (-n) n (neg_add_cancel n))
  rw [hMap]
  -- After the rewrite, the inverse and hom of the same iso cancel immediately.
  exact (eY.inv_hom_id_assoc (((CategoryTheory.shiftFunctor D n).map f).op ≫ eX.inv)).symm

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the scaled shifted map also transports across the inverse-oriented
`shiftFunctorOpIso`, with the scalar kept on the left for the opposite-shift target shape. -/
lemma shiftFunctorOpIso_inv_app_map_scaled (n : ℤ) {X Y : D} (f : X ⟶ Y) :
    (n.negOnePow • (CategoryTheory.shiftFunctor D n).map f).op ≫
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X)) =
    (n.negOnePow • (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op := by
  -- Move the scalar to the composite, transport the unscaled map, then put the scalar back on
  -- the left factor to match the shifted-triangle normal form.
  calc
    (n.negOnePow • (CategoryTheory.shiftFunctor D n).map f).op ≫
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X)) =
      (n.negOnePow • ((CategoryTheory.shiftFunctor D n).map f).op) ≫
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X)) := by
          rfl
    _ =
      n.negOnePow •
        (((CategoryTheory.shiftFunctor D n).map f).op ≫
          ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X))) := by
          rw [CategoryTheory.Linear.units_smul_comp]
    _ =
      n.negOnePow •
        (((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op) := by
          exact congrArg (fun k ↦ n.negOnePow • k) (shiftFunctorOpIso_inv_app_map n f)
    _ =
      (n.negOnePow • (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op := by
          rw [CategoryTheory.Linear.units_smul_comp]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the scaled opposite-shift transport can be rewritten with the
scalar on the shifted target map, matching the normal form used by `Triangle.shiftFunctor`. -/
lemma shiftFunctorOpIso_inv_app_map_scaled_right (n : ℤ) {X Y : D} (f : X ⟶ Y) :
    (n.negOnePow • (CategoryTheory.shiftFunctor D n).map f).op ≫
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X)) =
    ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
      ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op) := by
  -- Normalize the scalar from the comparison isomorphism to the shifted target map once, so the
  -- resulting equality matches the owner `Triangle.shiftFunctor` morphism spelling.
  calc
    (n.negOnePow • (CategoryTheory.shiftFunctor D n).map f).op ≫
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op X)) =
      (n.negOnePow • (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op := by
          simpa using shiftFunctorOpIso_inv_app_map_scaled n f
    _ =
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
        (n.negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op) := by
          rw [CategoryTheory.Linear.units_smul_comp, CategoryTheory.Linear.comp_units_smul]
    _ =
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op Y)) ≫
        ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map f.op) := by
          simp [Int.negOnePow_neg]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after transporting the shifted `T.mor₃` term, the remaining
functor image splits into the mapped comparison morphism followed by the mapped shifted tail. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_split
    (T : Triangle D) (n : ℤ) :
    (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
          ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op)) =
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op) := by
  -- Split the mapped composite once so the remaining bridge can compare only the first factors.
  rw [← Functor.map_comp]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: applying the extra shift functor preserves the normalized
scalar-right transport of `T.mor₃` across `shiftFunctorOpIso`. -/
lemma shiftFunctor_map_shiftFunctorOpIso_inv_app_map_scaled_right
    (T : Triangle D) (n : ℤ) :
    (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃).op ≫
          (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) =
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
          ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op)) := by
  -- Apply the scalar-right transport once under the outer shift functor so later rewrites only
  -- have to handle the counit/comparison prefix.
  exact congrArg ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map)
    (shiftFunctorOpIso_inv_app_map_scaled_right n T.mor₃)

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the op of the shifted third-map tail reverses the two factors once,
so later proofs can keep the comparison morphism on the left. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_op
    (T : Triangle D) (n : ℤ) :
    (n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃ ≫
        (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op =
      ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
        (n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃).op := by
  -- This is the standard reversal of composition under `op`.
  apply Quiver.Hom.unop_inj
  simp [unop_comp]
  rfl

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after opening the op-composite on the shifted third-map tail, the
extra shift functor can be reassociated so the comparison morphism appears as a separate prefix. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_reassociate
    (T : Triangle D) (n : ℤ) :
    (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃ ≫
            (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op) ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) =
    (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃).op ≫
          (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) := by
  -- Move the outer functor across the op-composite once, then keep the transported tail in the
  -- same normal form used by the scalar-right comparison helper.
  rw [← Functor.map_comp, triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_op,
    Category.assoc, Functor.map_comp]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: whiskering the reassociated shifted third-map tail by the owner
counit term preserves the exact normal form used by the closing `comm₃` proof. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_reassociate_prefix
    (T : Triangle D) (n : ℤ) :
    ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃ ≫
              (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op)) ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) =
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃).op ≫
              (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) := by
  -- Attach the fixed counit prefix after the tail has already been reassociated, so the closing
  -- theorem only consumes a named equality instead of rebuilding the whiskering.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
            (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫ k)
      (triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_reassociate T n)

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the combined counit/comparison prefix in the third square of
`triangleOpEquivalence_functor_obj_shift_iso_comm₃` collapses to the inverse
`shiftFunctorOpIso` comparison followed by the `-n`-shifted counit term. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix_reassociate
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
              (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) =
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          (((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
            (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
              (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) := by
  -- Package the two mapped comparison factors into one composite so the remaining blocker can be
  -- stated directly in the naturality shape expected by the owner counit API.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
            (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫ k)
      (Functor.map_comp (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ))
        ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
          (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)))).symm

/-- Helper for Remark 13.4.4: the combined counit/comparison prefix in the third square of
`triangleOpEquivalence_functor_obj_shift_iso_comm₃` collapses to the inverse
`shiftFunctorOpIso` comparison followed by the `-n`-shifted counit term. -/
noncomputable instance shiftFunctorCommShift (n : ℤ) :
    (CategoryTheory.shiftFunctor D n).CommShift ℤ where
  commShiftIso a := (shiftFunctorComm D n a).symm
  commShiftIso_zero := by
    -- Compare the zero-shift commutation through the canonical `shiftFunctorComm D n 0` formula.
    have h :
        shiftFunctorComm D n (0 : ℤ) =
          (Functor.CommShift.isoZero (CategoryTheory.shiftFunctor D n) ℤ).symm := by
      ext X
      simpa using
        (@shiftFunctorComm_zero_hom_app D ℤ _ _ _ X n)
    simpa using congrArg Iso.symm h
  commShiftIso_add a b := by
    -- Compare inverse components so the coherence statement is exactly the standard
    -- `shiftFunctorComm` compatibility with `shiftFunctorAdd`.
    have h :
        shiftFunctorComm D n (a + b) =
          (Functor.CommShift.isoAdd
            ((shiftFunctorComm D n a).symm) ((shiftFunctorComm D n b).symm)).symm := by
      ext X
      -- Postcompose the basic coherence square by the inverse `shiftFunctorAdd` and cancel the
      -- resulting mapped iso pair, so the target is exactly the inverse component of
      -- `CommShift.isoAdd`.
      have hcancel :
          (shiftFunctorComm D n (a + b)).hom.app X =
            (shiftFunctorComm D n (a + b)).hom.app X ≫
              (CategoryTheory.shiftFunctor D n).map ((shiftFunctorAdd D a b).hom.app X) ≫
                (CategoryTheory.shiftFunctor D n).map ((shiftFunctorAdd D a b).inv.app X) := by
        have hmap :
            (CategoryTheory.shiftFunctor D n).map ((shiftFunctorAdd D a b).hom.app X) ≫
              (CategoryTheory.shiftFunctor D n).map ((shiftFunctorAdd D a b).inv.app X) = 𝟙 _ := by
          rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
        simpa [Category.assoc] using
          (congrArg
            (fun k ↦ (shiftFunctorComm D n (a + b)).hom.app X ≫ k) hmap).symm
      exact hcancel.trans <| by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              k ≫ (CategoryTheory.shiftFunctor D n).map ((shiftFunctorAdd D a b).inv.app X))
            (shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app n a b X)
    simpa using congrArg Iso.symm h

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the chosen `CommShift` structure on `shiftFunctor D n` uses the
canonical `shiftFunctorComm D 1 n` comparison on components after swapping the shift indices. -/
lemma shiftFunctorCommIso_one_hom_app
    (T : Triangle D) (n : ℤ) :
    ((CategoryTheory.shiftFunctor D n).commShiftIso (1 : ℤ)).hom.app T.obj₁ =
      (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁ := by
  -- The local `CommShift` instance uses `(shiftFunctorComm D n 1).symm`, whose components are the
  -- same as `shiftFunctorComm D 1 n` by the symmetry of `shiftFunctorComm`.
  change (shiftFunctorComm D n (1 : ℤ)).inv.app T.obj₁ =
    (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁
  simpa using
    congrArg
      (fun η ↦ η.app T.obj₁)
      (congrArg Iso.hom (shiftFunctorComm_symm D n (1 : ℤ)))

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the chosen `CommShift` structure on `shiftFunctor D n` also uses
the public `shiftFunctorComm D 1 n` comparison on the once-shifted object. -/
lemma shiftFunctorCommIso_one_hom_app_shifted
    (T : Triangle D) (n : ℤ) :
    ((CategoryTheory.shiftFunctor D n).commShiftIso (1 : ℤ)).hom.app
        ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁) =
      (shiftFunctorComm D (1 : ℤ) n).hom.app
        ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁) := by
  -- The same symmetry comparison works pointwise on the shifted object.
  change (shiftFunctorComm D n (1 : ℤ)).inv.app
      ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁) =
    (shiftFunctorComm D (1 : ℤ) n).hom.app
      ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)
  simpa using
    congrArg
      (fun η ↦ η.app ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))
      (congrArg Iso.hom (shiftFunctorComm_symm D n (1 : ℤ)))

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the combined counit/comparison prefix in the third square of
`triangleOpEquivalence_functor_obj_shift_iso_comm₃` collapses to the inverse
`shiftFunctorOpIso` comparison followed by the `-n`-shifted counit term. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_raw
    (T : Triangle D) (n : ℤ) :
    ((CategoryTheory.shiftFunctor D n).map
        ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)).unop).op =
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
            (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (Functor.commShiftIso (CategoryTheory.shiftFunctor D n).op (1 : ℤ)).inv.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) := by
  letI : (CategoryTheory.shiftFunctor D n).CommShift ℤ := shiftFunctorCommShift n
  -- Specialize the owner counit-transport theorem once; only the final `F.op.commShiftIso`
  -- factor remains to be converted to the file's explicit `shiftFunctorOpIso` spelling.
  simpa [Category.assoc, shiftFunctorCommIso_one_hom_app] using
    congrArg Quiver.Hom.op
      (Functor.map_opShiftFunctorEquivalence_counitIso_inv_app_unop
        (CategoryTheory.shiftFunctor D n) (op T.obj₁) (1 : ℤ))

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the source object spelling in the raw shifted-counit transport is
definitionally the expected `op T.obj₁`. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_source_obj
    (T : Triangle D) :
    ((𝟭 Dᵒᵖ).obj (op T.obj₁)) = op T.obj₁ := rfl

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the target object spelling in the raw shifted-counit transport is
definitionally the expected shifted opposite object. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_target_obj
    (T : Triangle D) :
    (((opShiftFunctorEquivalence D (1 : ℤ)).inverse ⋙
        (opShiftFunctorEquivalence D (1 : ℤ)).functor).obj (op T.obj₁)) =
      ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).obj
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) := rfl

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the combined counit/comparison prefix in the third square of
`triangleOpEquivalence_functor_obj_shift_iso_comm₃` collapses to the inverse
`shiftFunctorOpIso` comparison followed by the `-n`-shifted counit term. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_naturality
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
        (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((CategoryTheory.shiftFunctor D (1 : ℤ)).map
          ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁)).unop).op =
    (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
        ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁)) := by
  let e := (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁)
  -- This is the raw counit naturality square for the inverse `shiftFunctorOpIso` component, kept
  -- before any endpoint-object normalization so later transport lemmas can consume it directly.
  simpa [e, Category.assoc] using
    (opShiftFunctorEquivalence_counitIso_inv_naturality (1 : ℤ) e).symm

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the raw shifted-counit transport can be reassociated so the counit
term and the first comparison map form a single prefix before the final owner `CommShift`
boundary. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_raw_reassociate
    (T : Triangle D) (n : ℤ) :
    ((CategoryTheory.shiftFunctor D n).map
        ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)).unop).op =
      ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op) ≫
        (Functor.commShiftIso (CategoryTheory.shiftFunctor D n).op (1 : ℤ)).inv.app
          (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) := by
  -- This is the existing raw shifted-counit transport with the prefix reassociated once.
  simpa [Category.assoc] using
    (triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_raw T n)

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the direct source object of the shifted `shiftFunctorOpIso.inv`
term is definitionally the `1`-shift of the `n`-shifted object. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_direct_source_obj
    (T : Triangle D) (n : ℤ) :
    op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj
      (unop ((CategoryTheory.shiftFunctor D n).op.obj (op T.obj₁)))) =
      op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj
        ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) := rfl

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the direct target object of the shifted `shiftFunctorOpIso.inv`
term is definitionally the `1`-shift of the unop of the `-n`-shifted opposite object. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_direct_target_obj
    (T : Triangle D) (n : ℤ) :
    op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj
      (unop ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁)))) =
    op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj
        (unop ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁)))) := rfl

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the hidden source object in the owner counit naturality theorem is
definitionally the explicit `shiftFunctor/op/unop` spelling used below. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_hidden_source_obj
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).functor.obj
        ((opShiftFunctorEquivalence D (1 : ℤ)).inverse.obj
          ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁))) =
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).obj
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj
          (unop ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁))))) := rfl

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the forward and backward transports attached to the hidden-source
object identification cancel before any remaining counit whisker. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_hidden_source_cancel
    (T : Triangle D) (n : ℤ) {Z : Dᵒᵖ}
    (f :
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).obj
          (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj
            (unop ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁))))) ⟶
        Z) :
    eqToHom (triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_hidden_source_obj T n).symm ≫
        (eqToHom (triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_hidden_source_obj T n) ≫
          f) =
      f := by
  -- The hidden-source object bridge is only an identity transport, so the two casts cancel.
  simp

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the hidden opposite commutation factor that appears when the
owner reassociated counit naturality theorem is instantiated is the inverse of the public
`shiftFunctorComm Dᵒᵖ (1) (-n)` component after swapping the shift indices. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_hiddenWhisker_symm
    (T : Triangle D) (n : ℤ) :
    (shiftFunctorComm Dᵒᵖ (-n) (1 : ℤ)).hom.app (op T.obj₁) =
      (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).inv.app (op T.obj₁) := by
  -- The two whiskers differ only by the standard symmetry of `shiftFunctorComm`.
  simpa using
    (congrArg
      (fun η ↦ η.hom.app (op T.obj₁))
      (shiftFunctorComm_symm Dᵒᵖ (1 : ℤ) (-n))).symm

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after shifting the object once, the opposite commutation factor
still swaps `(-n)` and `1` by the standard symmetry of `shiftFunctorComm`. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_hiddenWhisker_symm_shifted
    (T : Triangle D) (n : ℤ) :
    (shiftFunctorComm Dᵒᵖ (-n) (1 : ℤ)).hom.app
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) =
      (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).inv.app
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) := by
  -- The shifted object uses the same `shiftFunctorComm` symmetry as the unshifted one.
  simpa using
    (congrArg
      (fun η ↦ η.hom.app (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)))
      (shiftFunctorComm_symm Dᵒᵖ (1 : ℤ) (-n))).symm

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the reassociated owner counit naturality theorem can be specialized
to the inverse `shiftFunctorOpIso` component while leaving the final whisker arbitrary. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_naturality_assoc
    (T : Triangle D) (n : ℤ) {Z : Dᵒᵖ}
    (h :
      (opShiftFunctorEquivalence D (1 : ℤ)).functor.obj
        ((opShiftFunctorEquivalence D (1 : ℤ)).inverse.obj
          ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁))) ⟶ Z) :
    (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁)) ≫
          h =
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((CategoryTheory.shiftFunctor D (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
              (op T.obj₁)).unop).op ≫
          h := by
  let e := (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁)
  -- Keep the owner reassociated naturality theorem available with an arbitrary whisker, so the
  -- remaining work is isolated to identifying the exact hidden postcomposition term.
  simpa [e, Category.assoc] using
    (opShiftFunctorEquivalence_counitIso_inv_naturality_assoc (C := D) (n := (1 : ℤ)) e h)

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the hidden-owner whisker in the reassociated counit transport is the
owner `CommShift` component of `(shiftFunctor D n).op`, not the public
`shiftFunctorComm Dᵒᵖ (-n) 1` spelling. -/
noncomputable abbrev triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_ownerWhisker
    (T : Triangle D) (n : ℤ) :
    ((CategoryTheory.shiftFunctor D n).op ⋙ CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).obj
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ⟶
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ) ⋙ (CategoryTheory.shiftFunctor D n).op).obj
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) :=
  letI : (CategoryTheory.shiftFunctor D n).CommShift ℤ := shiftFunctorCommShift n
  (Functor.commShiftIso (CategoryTheory.shiftFunctor D n).op (1 : ℤ)).inv.app
    (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: unfolding the owner whisker only exposes the local
`Functor.commShiftIso` component used in the raw counit transport theorem. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_ownerWhisker_def
    (T : Triangle D) (n : ℤ) :
    triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_ownerWhisker T n =
      (by
        letI : (CategoryTheory.shiftFunctor D n).CommShift ℤ := shiftFunctorCommShift n
        exact
          (Functor.commShiftIso (CategoryTheory.shiftFunctor D n).op (1 : ℤ)).inv.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) := by
  -- The owner whisker is just a named abbreviation for the exact `CommShift` endpoint.
  rfl

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the public inverse shifted whisker is the same morphism as the
shifted hidden whisker once the standard `shiftFunctorComm` symmetry is applied. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_publicInv_shifted
    (T : Triangle D) (n : ℤ) :
    (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).inv.app
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) =
      (shiftFunctorComm Dᵒᵖ (-n) (1 : ℤ)).hom.app
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) := by
  -- This is exactly the shifted symmetry comparison already isolated above, just read in the
  -- public inverse-whisker direction needed by the remaining counit blocker.
  simpa using
    (triangleOpEquivalence_functor_obj_shift_iso_comm₃_hiddenWhisker_symm_shifted T n).symm

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the combined counit/comparison prefix in the third square of
`triangleOpEquivalence_functor_obj_shift_iso_comm₃` collapses to the inverse
`shiftFunctorOpIso` comparison followed by the `-n`-shifted counit term. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_whiskered
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
              (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) =
      (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
          ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
      (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app
          (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) := by
  let e := (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁)
  let w :
      (opShiftFunctorEquivalence D (1 : ℤ)).functor.obj
          ((opShiftFunctorEquivalence D (1 : ℤ)).inverse.obj
            ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj (op T.obj₁))) ⟶
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).obj
          ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) :=
    eqToHom (triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_hidden_source_obj T n).symm ≫
      triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_ownerWhisker T n
  have hnat :=
    triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_naturality_assoc
      (T := T) (n := n) (Z := (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).obj
        ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).obj
          (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)))) w
  -- Route correction: the remaining gap is the explicit hidden-source whisker matching needed to
  -- turn `hnat` into the exact public `shiftFunctorComm` spelling consumed below.
  simpa [e, w, Category.assoc,
    triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_ownerWhisker_def,
    triangleOpEquivalence_functor_obj_shift_iso_comm₃_publicInv_shifted] using hnat.symm

omit [Preadditive D] [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the combined counit/comparison prefix in the third square of
`triangleOpEquivalence_functor_obj_shift_iso_comm₃` collapses to the inverse
`shiftFunctorOpIso` comparison followed by the `-n`-shifted counit term. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          (((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
            (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
              (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) =
      (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
          ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
      (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app
          (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) := by
  -- Route correction: replay the owner `TriangleOpEquivalence.counitIso` third-square rewrite
  -- order on the fixed counit/comparison prefix instead of transporting the bare counit term.
  -- Consume the still-missing owner bridge on the split prefix, then fold the two mapped factors
  -- back into the original composite shape.
  rw [Functor.map_comp]
  exact triangleOpEquivalence_functor_obj_shift_iso_comm₃_counit_whiskered T n

/-- Helper for Remark 13.4.4: whiskering the collapsed counit/comparison prefix by the shifted
`T.mor₃` tail preserves the exact normal form used in the final `comm₃` assembly. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix_tail
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
              (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
              ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op) =
      (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
            ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
          (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
              ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op) := by
  -- Collapse the prefix first, then reattach the unchanged shifted tail on the right.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        k ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op))
      (triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix T n)

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after the tail reassociation, whiskering by the fixed counit prefix
also preserves the scalar-right `shiftFunctorOpIso` transport step. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_whisker_scaled_transport
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃).op ≫
              (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) =
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
                (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
              ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op)) := by
  -- Reattach the fixed counit-and-commutation prefix only after the scalar-right transport has
  -- been normalized under the outer shift functor.
  exact congrArg
    (fun k ↦
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
        k)
    (shiftFunctor_map_shiftFunctorOpIso_inv_app_map_scaled_right T n)

/-- Helper for Remark 13.4.4: after the prefix collapse, the shifted `T.mor₃` tail can be moved
across `shiftFunctorComm` in one named transport step. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_shiftFunctorComm
    (T : Triangle D) (n : ℤ) :
    (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app
        (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op) =
      ((-n).negOnePow •
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
          ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)) ≫
        (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app (op T.obj₃) := by
  -- This is the single `shiftFunctorComm` naturality square, normalized once in the scalar-right
  -- spelling used by the shifted triangle API.
  simpa [Functor.map_units_smul, Category.assoc,
    CategoryTheory.Linear.comp_units_smul, CategoryTheory.Linear.units_smul_comp] using
    ((shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.naturality T.mor₃.op).symm

/-- Helper for Remark 13.4.4: after the prefix collapse, the shifted `T.mor₃` tail can be moved
across `shiftFunctorComm` in one named transport step. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_shiftFunctorComm_tail
    (T : Triangle D) (n : ℤ) :
    (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
            ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
          (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app
            (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op) =
      (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
            ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
          (((-n).negOnePow •
              (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
                ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)) ≫
            (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app (op T.obj₃)) := by
  -- Postcompose the named transport with the fixed prefix instead of rebuilding it in the closing
  -- theorem.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
            ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
          k)
      (triangleOpEquivalence_functor_obj_shift_iso_comm₃_shiftFunctorComm T n)

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after the `shiftFunctorComm` transport, the explicit composite folds
back into the single `(-n)`-shifted tail used by `Triangle.shiftFunctor`. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_fold_tail
    (T : Triangle D) (n : ℤ) :
    (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
            ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁)) ≫
          (((-n).negOnePow •
              (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
                ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)) ≫
            (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app (op T.obj₃)) =
      (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        ((-n).negOnePow •
          (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
              ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁) ≫
                (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op) ≫
            (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app (op T.obj₃)) := by
  -- Fold the explicit mapped composite back into the owner `Triangle.shiftFunctor` tail spelling.
  let p := (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁)
  let a :=
    (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
      ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁))
  let b :=
    (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
      ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)
  let c := (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app (op T.obj₃)
  have hab :
      a ≫ b =
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
          ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op) := by
    -- Fold the two mapped factors back into a single mapped composite once.
    simpa [a, b] using
      (Functor.map_comp (CategoryTheory.shiftFunctor Dᵒᵖ (-n))
        ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁))
        ((CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)).symm
  -- Reassociate once, move the scalar across the first composition, and then fold the map.
  calc
    p ≫ a ≫ (((-n).negOnePow • b) ≫ c) =
        p ≫ (((-n).negOnePow • (a ≫ b)) ≫ c) := by
          have hInner :
              a ≫ ((-n).negOnePow • b) = (-n).negOnePow • (a ≫ b) := by
            exact CategoryTheory.Linear.comp_units_smul a (-n).negOnePow b
          simpa [Category.assoc] using
            congrArg (fun k ↦ p ≫ (k ≫ c)) hInner
    _ =
      p ≫ (((-n).negOnePow •
          (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
              ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁) ≫
                (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)) ≫ c) := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ p ≫ (((-n).negOnePow • k) ≫ c)) hab
    _ =
      p ≫ ((-n).negOnePow •
        ((CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
            ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁) ≫
              (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)) ≫ c) := by
      let m :=
        (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
          ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op)
      have hPost : (((-n).negOnePow • m) ≫ c) = (-n).negOnePow • (m ≫ c) :=
        CategoryTheory.Linear.units_smul_comp (-n).negOnePow m c
      simpa [m, Category.assoc] using congrArg (fun k ↦ p ≫ k) hPost

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: the initial opposite-tail reassociation and the scalar-right
`shiftFunctorOpIso` transport can be consumed as one named step before the counit prefix is
collapsed. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_transport
    (T : Triangle D) (n : ℤ) :
    ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₃ ≫
              (shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op)) ≫
      (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
        ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃)) =
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
                (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
              ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op)) := by
  -- First separate the fixed left whisker from the shifted tail, then normalize the scalar-right
  -- `shiftFunctorOpIso` transport under that fixed prefix.
  exact
    (triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_reassociate_prefix T n).trans
      (triangleOpEquivalence_functor_obj_shift_iso_comm₃_whisker_scaled_transport T n)

/-- Helper for Remark 13.4.4: once the shifted tail is transported, the remaining counit-prefix
collapse, `shiftFunctorComm` move, and fold-back to the canonical shifted triangle tail can be
assembled without revisiting the earlier op-tail transport. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix_folded_tail
    (T : Triangle D) (n : ℤ) :
    (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
          (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
            ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
                (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
              ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op)) =
      (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) ≫
        ((-n).negOnePow •
          (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map
              ((opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app (op T.obj₁) ≫
                (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map T.mor₃.op) ≫
            (shiftFunctorComm Dᵒᵖ (1 : ℤ) (-n)).hom.app (op T.obj₃)) := by
  -- Split the mapped tail once, then assemble the remaining prefix collapse, transport, and
  -- fold-back as a flat transitivity chain.
  have hSplit :
      (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
            (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
              ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
                  (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁)) ≫
                ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op)) =
        (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
            (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
          (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
                ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app
                    (op ((CategoryTheory.shiftFunctor D (1 : ℤ)).obj T.obj₁))) ≫
              (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
                ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₃.op) := by
    -- Separate the two mapped factors before invoking the already-proved prefix and tail helpers.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (opShiftFunctorEquivalence D (1 : ℤ)).counitIso.inv.app
              (op ((CategoryTheory.shiftFunctor D n).obj T.obj₁)) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map ((shiftFunctorComm D (1 : ℤ) n).hom.app T.obj₁).op ≫
            k)
        (triangleOpEquivalence_functor_obj_shift_iso_comm₃_split T n)
  exact
    hSplit.trans
      ((triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix_tail T n).trans
        ((triangleOpEquivalence_functor_obj_shift_iso_comm₃_shiftFunctorComm_tail T n).trans
          (triangleOpEquivalence_functor_obj_shift_iso_comm₃_fold_tail T n)))

/-- Helper for Remark 13.4.4: the third `Triangle.isoMk` square for
`triangleOpEquivalence_functor_obj_shift_iso` is exactly the counit/shift normalization from the
owner opposite-category equivalence, followed by the scalar-right shift transport for `T.mor₃`. -/
lemma triangleOpEquivalence_functor_obj_shift_iso_comm₃ (T : Triangle D) (n : ℤ) :
    ((triangleOpEquivalence D).functor.obj (op (T⟦n⟧ : Triangle D))).mor₃ ≫
        (CategoryTheory.shiftFunctor Dᵒᵖ (1 : ℤ)).map
          ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).symm.app (op T.obj₃)).hom =
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).symm.app (op T.obj₁)).hom ≫
        ((((triangleOpEquivalence D).functor.obj (op T))⟦(-n : ℤ)⟧) : Triangle Dᵒᵖ).mor₃ := by
  -- Route correction: keep the owner `TriangleOpEquivalence.counitIso` rewrite order, but consume
  -- the op-tail transport and the remaining prefix-collapse/fold steps through two named helpers,
  -- so the closing theorem only assembles already-normalized boundaries.
  dsimp [triangleOpEquivalence, TriangleOpEquivalence.functor, Triangle.shiftFunctor]
  exact
    (triangleOpEquivalence_functor_obj_shift_iso_comm₃_tail_transport T n).trans
      (triangleOpEquivalence_functor_obj_shift_iso_comm₃_prefix_folded_tail T n)

/-- Helper for Remark 13.4.4: applying `triangleOpEquivalence` to a shifted triangle agrees with
shifting the opposite-category image by `-n`. -/
noncomputable abbrev triangleOpEquivalence_functor_obj_shift_iso (T : Triangle D) (n : ℤ) :
    ((triangleOpEquivalence D).functor.obj (op (T⟦n⟧ : Triangle D))) ≅
      ((((triangleOpEquivalence D).functor.obj (op T))⟦(-n : ℤ)⟧) : Triangle Dᵒᵖ) := by
  -- The first two squares are the scalar-right transport lemmas for `T.mor₂` and `T.mor₁`,
  -- and the third square is the dedicated counit/shift normalization proved just above.
  refine Triangle.isoMk _ _
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).symm.app (op T.obj₃))
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).symm.app (op T.obj₂))
      ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).symm.app (op T.obj₁)) ?_ ?_ ?_
  · dsimp [triangleOpEquivalence, TriangleOpEquivalence.functor, Triangle.shiftFunctor]
    calc
      (n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₂).op ≫
          (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₂) =
        n.negOnePow •
          ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₂.op) := by
            simpa using shiftFunctorOpIso_inv_app_map_scaled_right n T.mor₂
      _ =
        (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃) ≫
          (n.negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₂.op) := by
            rw [← CategoryTheory.Linear.comp_units_smul]
      _ =
        (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₃) ≫
          ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₂.op) := by
            simp [Int.negOnePow_neg]
  · dsimp [triangleOpEquivalence, TriangleOpEquivalence.functor, Triangle.shiftFunctor]
    calc
      (n.negOnePow • (CategoryTheory.shiftFunctor D n).map T.mor₁).op ≫
          (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₁) =
        n.negOnePow •
          ((shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₂) ≫
            (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₁.op) := by
            simpa using shiftFunctorOpIso_inv_app_map_scaled_right n T.mor₁
      _ =
        (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₂) ≫
          (n.negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₁.op) := by
            rw [← CategoryTheory.Linear.comp_units_smul]
      _ =
        (shiftFunctorOpIso D (-n) n (neg_add_cancel n)).inv.app (op T.obj₂) ≫
          ((-n).negOnePow • (CategoryTheory.shiftFunctor Dᵒᵖ (-n)).map T.mor₁.op) := by
            simp [Int.negOnePow_neg]
  · simpa using triangleOpEquivalence_functor_obj_shift_iso_comm₃ T n

/-- Helper for Remark 13.4.4: applying `triangleOpEquivalence` to a rotated triangle agrees with
inverse-rotating the opposite-category image. -/
noncomputable abbrev triangleOpEquivalence_functor_obj_rotate_iso (T : Triangle D) :
    ((triangleOpEquivalence D).functor.obj (op T.rotate)) ≅
      (((triangleOpEquivalence D).functor.obj (op T)).invRotate) := by
  let S : Triangle Dᵒᵖ := (triangleOpEquivalence D).functor.obj (op T)
  let e₀ : S ≅ (triangleOpEquivalence D).functor.obj (op T.rotate.invRotate) := by
    -- Route correction: express `T` as `T.rotate.invRotate` before using the already packaged
    -- inverse-rotation transport, so the remaining work is just functorial composition.
    exact ((triangleOpEquivalence D).functor.mapIso (rotCompInvRot.app T).op).symm
  let e₁ :
      ((triangleOpEquivalence D).functor.obj (op T.rotate.invRotate)) ≅
        (((triangleOpEquivalence D).functor.obj (op T.rotate)).rotate) := by
    let S' : Triangle Dᵒᵖ := (triangleOpEquivalence D).functor.obj (op T.rotate)
    let r :
        (unop ((triangleOpEquivalence D).inverse.obj S'.rotate)).rotate ≅
          unop ((triangleOpEquivalence D).inverse.obj S') :=
      rotateTriangleOpEquivalenceInverseObjRotateUnopIso S'
    let u : unop ((triangleOpEquivalence D).inverse.obj S') ≅ T.rotate :=
      ((triangleOpEquivalence D).unitIso.app (op T.rotate)).unop
    let e' :
        (unop ((triangleOpEquivalence D).inverse.obj S'.rotate)).rotate ≅ T.rotate := r ≪≫ u
    let A' : Triangle D := unop ((triangleOpEquivalence D).inverse.obj S'.rotate)
    let aIso' : A' ≅ T.rotate.invRotate := by
      -- Package the inverse-rotation transport once for the rotated triangle.
      exact (rotCompInvRot.app A') ≪≫ (Pretriangulated.invRotate D).mapIso e'
    let c' :
        ((triangleOpEquivalence D).inverse ⋙ (triangleOpEquivalence D).functor).obj S'.rotate ≅
          S'.rotate :=
      (triangleOpEquivalence D).counitIso.app S'.rotate
    -- This is the inverse-rotation bridge specialized to `T.rotate`, kept local to avoid a
    -- later-declaration dependency in the file.
    simpa [A', S'] using
      (((triangleOpEquivalence D).functor.mapIso aIso'.op) ≪≫ c')
  let e : S ≅ (((triangleOpEquivalence D).functor.obj (op T.rotate)).rotate) := e₀ ≪≫ e₁
  let A : Triangle Dᵒᵖ := (triangleOpEquivalence D).functor.obj (op T.rotate)
  -- Convert the rotation comparison into the desired inverse-rotation comparison in one step.
  simpa [A, S] using
    ((rotCompInvRot.app A) ≪≫ (Pretriangulated.invRotate Dᵒᵖ).mapIso e.symm)

/-- Helper for Remark 13.4.4: applying `triangleOpEquivalence` to an inverse-rotated triangle
agrees with rotating the opposite-category image. -/
noncomputable abbrev triangleOpEquivalence_functor_obj_invRotate_iso (T : Triangle D) :
    ((triangleOpEquivalence D).functor.obj (op T.invRotate)) ≅
      (((triangleOpEquivalence D).functor.obj (op T)).rotate) := by
  let S : Triangle Dᵒᵖ := (triangleOpEquivalence D).functor.obj (op T)
  let r :
      (unop ((triangleOpEquivalence D).inverse.obj S.rotate)).rotate ≅
        unop ((triangleOpEquivalence D).inverse.obj S) :=
    rotateTriangleOpEquivalenceInverseObjRotateUnopIso S
  let u : unop ((triangleOpEquivalence D).inverse.obj S) ≅ T :=
    ((triangleOpEquivalence D).unitIso.app (op T)).unop
  let e : (unop ((triangleOpEquivalence D).inverse.obj S.rotate)).rotate ≅ T := r ≪≫ u
  let A : Triangle D := unop ((triangleOpEquivalence D).inverse.obj S.rotate)
  let aIso : A ≅ T.invRotate := by
    -- Move from the rotated inverse-side comparison to the canonical inverse-rotation target.
    exact (rotCompInvRot.app A) ≪≫ (Pretriangulated.invRotate D).mapIso e
  let c :
      ((triangleOpEquivalence D).inverse ⋙ (triangleOpEquivalence D).functor).obj S.rotate ≅
        S.rotate :=
    (triangleOpEquivalence D).counitIso.app S.rotate
  -- Transport the inverse-side comparison back across the equivalence, then identify the counit.
  simpa [A, S] using
    (((triangleOpEquivalence D).functor.mapIso aIso.op) ≪≫ c)

namespace IsCoSpecial

variable {T : Triangle D}

/-- Helper for Remark 13.4.4: co-speciality is preserved by shifts after transporting the
opposite-category view along the corrected shift bridge. -/
instance instShift (n : ℤ) [IsCoSpecial T] : IsCoSpecial (T⟦n⟧ : Triangle D) := by
  -- Transport speciality from the opposite image of `T` to the opposite image of `T⟦n⟧`.
  let e := triangleOpEquivalence_functor_obj_shift_iso T n
  simpa [Triangle.IsCoSpecial] using Triangle.IsSpecial.of_iso
    e.symm
    (inferInstance : Triangle.IsSpecial
      ((((triangleOpEquivalence D).functor.obj (op T))⟦(-n : ℤ)⟧) : Triangle Dᵒᵖ))

instance instRotate [IsCoSpecial T] : IsCoSpecial T.rotate := by
  -- Transport the opposite image of `T.rotate` to the inverse rotation of the already special
  -- opposite image of `T`.
  let e := triangleOpEquivalence_functor_obj_rotate_iso T
  simpa [Triangle.IsCoSpecial] using Triangle.IsSpecial.of_iso
    e.symm
    (inferInstance : Triangle.IsSpecial
      (((triangleOpEquivalence D).functor.obj (op T)).invRotate))

noncomputable instance instInvRotate [IsCoSpecial T] : IsCoSpecial T.invRotate := by
  -- Transport the opposite image of `T.invRotate` to the rotation of the already special
  -- opposite image of `T`.
  let e := triangleOpEquivalence_functor_obj_invRotate_iso T
  simpa [Triangle.IsCoSpecial] using Triangle.IsSpecial.of_iso
    e.symm
    (inferInstance : Triangle.IsSpecial
      (((triangleOpEquivalence D).functor.obj (op T)).rotate))

/-- Helper for Remark 13.4.4: the unshifted contravariant exactness at `obj₂` is the opposite-side
unshifted covariant exactness for the canonical opposite triangle. -/
lemma yoneda_exact₂_unshifted (hT : IsCoSpecial T) (W : D)
    {f : T.obj₂ ⟶ W} (hf : T.mor₁ ≫ f = 0) :
    ∃ g : T.obj₃ ⟶ W, f = T.mor₂ ≫ g := by
  let S : Triangle Dᵒᵖ := (triangleOpEquivalence D).functor.obj (op T)
  have hS : Triangle.IsSpecial S := by
    simpa [Triangle.IsCoSpecial, S] using hT
  -- Apply the covariant exactness statement in `Dᵒᵖ`, keeping the witness there until the end.
  obtain ⟨g, hg⟩ := Triangle.IsSpecial.coyoneda_exact₂_unshifted hS (op W) (by
    simpa [S] using congrArg Quiver.Hom.op hf)
  -- Unop the witness and the factorization once to recover the source-facing statement.
  exact ⟨g.unop, by simpa [S] using congrArg Quiver.Hom.unop hg⟩

lemma yoneda_exact₂ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₂ ⟶ W} (hf : (T⟦n⟧ : Triangle D).mor₁ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₃ ⟶ W, f = (T⟦n⟧ : Triangle D).mor₂ ≫ g := by
  letI : IsCoSpecial T := hT
  let S : Triangle D := (T⟦n⟧ : Triangle D)
  have hS : IsCoSpecial S := by
    simpa [S] using (show IsCoSpecial (T⟦n⟧ : Triangle D) from inferInstance)
  letI : IsCoSpecial S := hS
  -- Reuse the unshifted contravariant exactness on the shifted triangle.
  exact yoneda_exact₂_unshifted hS W hf

lemma yoneda_exact₃ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₃ ⟶ W} (hf : (T⟦n⟧ : Triangle D).mor₂ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧ ⟶ W, f = (T⟦n⟧ : Triangle D).mor₃ ≫ g := by
  letI : IsCoSpecial T := hT
  let S : Triangle D := (T⟦n⟧ : Triangle D)
  have hS : IsCoSpecial S := by
    simpa [S] using (show IsCoSpecial (T⟦n⟧ : Triangle D) from inferInstance)
  letI : IsCoSpecial S := hS
  letI : IsCoSpecial S.rotate := inferInstance
  let hRotate : IsCoSpecial S.rotate := inferInstance
  -- Apply the unshifted `obj₂` exactness to the rotated shifted triangle; its middle map is
  -- exactly `S.mor₃`, so the witness can be reused unchanged.
  obtain ⟨g, hg⟩ := yoneda_exact₂_unshifted hRotate W hf
  refine ⟨g, ?_⟩
  -- Unfold the single rotation once to recover the source-facing third map.
  simpa [S, Triangle.rotate] using hg

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Helper for Remark 13.4.4: after rotating a triangle twice, the middle morphism is the
negated shifted first morphism of the original triangle. -/
lemma rotateRotateMor₂_eq_neg_shiftMor₁ (S : Triangle D) :
    (S.rotate.rotate).mor₂ = -((S.mor₁)⟦(1 : ℤ)⟧') := by
  -- Two rotations turn the middle map into the negated shifted first map by definition.
  simp [Triangle.rotate]

lemma yoneda_exact₁ (hT : IsCoSpecial T) (n : ℤ) (W : D)
    {f : (T⟦n⟧ : Triangle D).obj₁⟦(1 : ℤ)⟧ ⟶ W} (hf : (T⟦n⟧ : Triangle D).mor₃ ≫ f = 0) :
    ∃ g : (T⟦n⟧ : Triangle D).obj₂⟦(1 : ℤ)⟧ ⟶ W,
      f = (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') ≫ g := by
  letI : IsCoSpecial T := hT
  let S : Triangle D := (T⟦n⟧ : Triangle D)
  have hS : IsCoSpecial S := by
    simpa [S] using (show IsCoSpecial (T⟦n⟧ : Triangle D) from inferInstance)
  letI : IsCoSpecial S := hS
  letI : IsCoSpecial S.rotate := inferInstance
  letI : IsCoSpecial S.rotate.rotate := inferInstance
  let hRotateRotate : IsCoSpecial S.rotate.rotate := inferInstance
  -- Route correction: apply the unshifted `obj₂` exactness to the twice-rotated shifted triangle,
  -- where `hf` is already the kernel condition on `mor₁`, then absorb the single minus sign in
  -- `mor₂` by negating the witness once.
  obtain ⟨g, hg⟩ := yoneda_exact₂_unshifted hRotateRotate W hf
  refine ⟨-g, ?_⟩
  -- Rewrite the twice-rotated middle morphism through the dedicated double-rotation helper, then
  -- move the minus to the witness side so the source-facing morphism spelling reappears.
  calc
    f = (-((S.mor₁)⟦(1 : ℤ)⟧')) ≫ g := by
          simpa [rotateRotateMor₂_eq_neg_shiftMor₁ S] using hg
    _ = ((S.mor₁)⟦(1 : ℤ)⟧') ≫ (-g) := by
          -- Compare both sides with the common normal form `-(((S.mor₁)⟦1⟧') ≫ g)`.
          have hLeft :
              (-((S.mor₁)⟦(1 : ℤ)⟧')) ≫ g = -((((S.mor₁)⟦(1 : ℤ)⟧')) ≫ g) := by
            simpa using (Preadditive.neg_comp ((S.mor₁)⟦(1 : ℤ)⟧') g)
          have hRight :
              ((S.mor₁)⟦(1 : ℤ)⟧') ≫ (-g) = -((((S.mor₁)⟦(1 : ℤ)⟧')) ≫ g) := by
            show ((S.mor₁)⟦(1 : ℤ)⟧') ≫ (-g) = -((((S.mor₁)⟦(1 : ℤ)⟧')) ≫ g)
            exact Preadditive.comp_neg ((S.mor₁)⟦(1 : ℤ)⟧') g
          exact hLeft.trans hRight.symm
    _ = (((T⟦n⟧ : Triangle D).mor₁)⟦(1 : ℤ)⟧') ≫ (-g) := by
          rfl

end IsCoSpecial

end Triangle

-- Proof sketch: repeat the proof of `Pretriangulated.isIso₂_of_isIso₁₃`, replacing the
-- distinguished-triangle exactness input by the `coyoneda_exact₂` and `coyoneda_exact₃` fields of
-- the special-triangle assumptions on `T` and `T'`.
/-- Remark 13.4.4 (3): in a morphism of special triangles, if the first and third components are
isomorphisms, then the second component is an isomorphism. -/
@[stacks 09WA]
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
            simpa [Category.assoc] using congrArg (fun m ↦ g ≫ m) φ.comm₁
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
                simpa [Category.assoc] using congrArg (fun m ↦ h ≫ e₃.inv ≫ m) eq
          _ = h ≫ e₃.inv ≫ e₃.hom ≫ T'.invRotate.mor₁ := by
                rfl
          _ = h ≫ T'.invRotate.mor₁ := by
                simp
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
        simpa using (comp_zero : k ≫ (0 : T.invRotate.obj₁ ⟶ T.obj₂) = 0)
  refine isIso_of_yoneda_map_bijective _ (fun A ↦ ⟨?_, ?_⟩)
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
        congrArg (fun m ↦ y₂ ≫ m) (Triangle.IsSpecial.zero₂₃_unshifted hT')
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
/-- Remark 13.4.4 (4): in a morphism of special triangles, if the first and second components are
isomorphisms, then the third component is an isomorphism. -/
@[stacks 09WA]
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
/-- Remark 13.4.4 (5): in a morphism of special triangles, if the second and third components are
isomorphisms, then the first component is an isomorphism. -/
@[stacks 09WA]
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
/-- Remark 13.4.4 (6): in a morphism of co-special triangles, if the first and third components are
isomorphisms, then the second component is an isomorphism. -/
@[stacks 09WA]
theorem isIso₂_of_isIso₁₃_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsCoSpecial T) (hT' : Triangle.IsCoSpecial T') (h₁ : IsIso φ.hom₁)
    (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₂ := by
  -- Pass to the opposite-category morphism, where co-speciality is exactly speciality.
  let ψ := (triangleOpEquivalence D).functor.map (op φ)
  letI : IsIso φ.hom₁ := h₁
  letI : IsIso φ.hom₃ := h₃
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
/-- Remark 13.4.4 (7): in a morphism of co-special triangles, if the first and second components
are isomorphisms, then the third component is an isomorphism. -/
@[stacks 09WA]
theorem isIso₃_of_isIso₁₂_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsCoSpecial T) (hT' : Triangle.IsCoSpecial T') (h₁ : IsIso φ.hom₁)
    (h₂ : IsIso φ.hom₂) :
    IsIso φ.hom₃ := by
  let ψ := (triangleOpEquivalence D).functor.map (op φ)
  letI : IsIso φ.hom₁ := h₁
  letI : IsIso φ.hom₂ := h₂
  letI : IsIso ψ.hom₂ := by
    -- The middle component of `ψ` is the opposite of `φ.hom₂`.
    dsimp [ψ]
    infer_instance
  letI : IsIso ψ.hom₃ := by
    -- The third component of `ψ` is the opposite of `φ.hom₁`.
    dsimp [ψ]
    infer_instance
  have hψ : IsIso ψ.hom₁ :=
    isIso₁_of_isIso₂₃_of_isSpecial ψ hT' hT inferInstance inferInstance
  -- Re-express the first component as `φ.hom₃.op` before reflecting the isomorphism back.
  dsimp [ψ] at hψ
  letI : IsIso φ.hom₃.op := hψ
  exact isIso_of_op φ.hom₃

-- Proof sketch: reduce to the co-special version of the first theorem after inverse-rotating the
-- morphism of triangles.
/-- Remark 13.4.4 (8): in a morphism of co-special triangles, if the second and third components
are isomorphisms, then the first component is an isomorphism. -/
@[stacks 09WA]
theorem isIso₁_of_isIso₂₃_of_isCoSpecial {T T' : Triangle D} (φ : T ⟶ T')
    (hT : Triangle.IsCoSpecial T) (hT' : Triangle.IsCoSpecial T') (h₂ : IsIso φ.hom₂)
    (h₃ : IsIso φ.hom₃) :
    IsIso φ.hom₁ := by
  let ψ := (triangleOpEquivalence D).functor.map (op φ)
  letI : IsIso φ.hom₂ := h₂
  letI : IsIso φ.hom₃ := h₃
  letI : IsIso ψ.hom₁ := by
    -- The first component of `ψ` is the opposite of `φ.hom₃`.
    dsimp [ψ]
    infer_instance
  letI : IsIso ψ.hom₂ := by
    -- The second component of `ψ` is the opposite of `φ.hom₂`.
    dsimp [ψ]
    infer_instance
  have hψ : IsIso ψ.hom₃ :=
    isIso₃_of_isIso₁₂_of_isSpecial ψ hT' hT inferInstance inferInstance
  -- Re-express the third component as `φ.hom₁.op` before reflecting the isomorphism back.
  dsimp [ψ] at hψ
  letI : IsIso φ.hom₁.op := hψ
  exact isIso_of_op φ.hom₁

section

variable [HasZeroObject D] [Pretriangulated D]

-- Proof sketch: apply the distinguished-triangle exactness lemmas `Triangle.coyoneda_exact₁`,
-- `Triangle.coyoneda_exact₂`, and `Triangle.coyoneda_exact₃` to each shifted triangle
-- `T⟦n⟧`, using `Triangle.shift_distinguished` to transport distinguishedness along shifts.
/-- Remark 13.4.4 (9): every distinguished triangle is special. -/
@[stacks 09WA]
instance instIsSpecialOfMemDistTriang (T : Triangle D) (hT : T ∈ distTriang D) :
    Triangle.IsSpecial T where
  exact₂ n W := by
    -- Shift distinguishedness to the relevant triangle and use the standard exactness factorization.
    let S : Triangle D := (T⟦n⟧ : Triangle D)
    let hshift : S ∈ distTriang D := Triangle.shift_distinguished T hT n
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext f
      -- Normalize the functorial action to ordinary postcomposition.
      change (f ≫ S.mor₁) ≫ S.mor₂ = 0
      calc
        (f ≫ S.mor₁) ≫ S.mor₂ = f ≫ 0 := by
          simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (comp_distTriang_mor_zero₁₂ S hshift)
        _ = 0 := by
          simpa using (comp_zero : f ≫ (0 : S.obj₁ ⟶ S.obj₃) = 0)
    · intro f hf
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ S hshift f hf
      exact ⟨g, hg.symm⟩
  exact₃ n W := by
    -- Shift distinguishedness to the relevant triangle and use the standard exactness factorization.
    let S : Triangle D := (T⟦n⟧ : Triangle D)
    let hshift : S ∈ distTriang D := Triangle.shift_distinguished T hT n
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext f
      -- Normalize the functorial action to ordinary postcomposition.
      change (f ≫ S.mor₂) ≫ S.mor₃ = 0
      calc
        (f ≫ S.mor₂) ≫ S.mor₃ = f ≫ 0 := by
          simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (comp_distTriang_mor_zero₂₃ S hshift)
        _ = 0 := by
          simpa using (comp_zero : f ≫ (0 : S.obj₂ ⟶ S.obj₁⟦(1 : ℤ)⟧) = 0)
    · intro f hf
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ S hshift f hf
      exact ⟨g, hg.symm⟩
  exact₁ n W := by
    -- Shift distinguishedness to the relevant triangle and use the standard exactness factorization.
    let S : Triangle D := (T⟦n⟧ : Triangle D)
    let hshift : S ∈ distTriang D := Triangle.shift_distinguished T hT n
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · ext f
      -- Normalize the functorial action to ordinary postcomposition.
      change (f ≫ S.mor₃) ≫ (S.mor₁⟦(1 : ℤ)⟧') = 0
      calc
        (f ≫ S.mor₃) ≫ (S.mor₁⟦(1 : ℤ)⟧') = f ≫ 0 := by
          simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (comp_distTriang_mor_zero₃₁ S hshift)
        _ = 0 := by
          simpa using (comp_zero : f ≫ (0 : S.obj₃ ⟶ S.obj₂⟦(1 : ℤ)⟧) = 0)
    · intro f hf
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ S hshift f hf
      exact ⟨g, hg.symm⟩

-- Proof sketch: transport distinguishedness to the canonical opposite-category view with
-- `op_distinguished`, then invoke the distinguished-triangle instance for `Triangle.IsSpecial`.
/-- Remark 13.4.4 (10): every distinguished triangle is co-special. -/
@[stacks 09WA]
instance instIsCoSpecialOfMemDistTriang (T : Triangle D) (hT : T ∈ distTriang D) :
    Triangle.IsCoSpecial T := by
  simpa [Triangle.IsCoSpecial] using
    (instIsSpecialOfMemDistTriang ((triangleOpEquivalence D).functor.obj (op T))
      (op_distinguished T hT))

end

end Pretriangulated
end CategoryTheory
