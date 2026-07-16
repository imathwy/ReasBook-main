import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_32_5
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_1
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_6
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_7
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uX uY

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{v, uX} C}
variable {Y : BasedCategory.{v, uY} C}

/- Domain-style sampling for Lemma 4.35.16:
- primary domain: factorization of a morphism of categories fibred in groupoids through the
  explicit `2`-fibre product with the identity of the target;
- sampled owner-level declarations:
  `FibredInGroupoidsOver.twoFibreProduct`,
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductRightProjection`,
  `ExplicitTwoFibreProductHom.ext`,
  `BasedFunctor.IsEquivalenceOverBase.mkPrime`;
- best owner abstraction: the source-facing factorization object is the explicit `2`-fibre
  product specialized to `(F, id Y)` because that specialization is definable without fibredness
  assumptions and is stable across the heterogeneous universes of `X` and `Y`; the fibred-in-
  groupoids closure should therefore reuse the existing explicit-pullback theorem directly rather
  than rebuilding a parallel bundled owner specialization inside this file.

Primitive-vs-derived split:
- primitive data: only the based functor `F : X ⥤ᵇ Y`;
- derived API: the factorization object `X ×_{F,Y,\mathrm{id}} Y`, the canonical source map
  `x ↦ (x, F(x), 𝟙)`, the target projection, the fibred-in-groupoids specialization of the
  pullback projection theorem, and the equivalence-over-base upgrade from the underlying
  categorical equivalence.

Source/core/bridge triage:
- `source-facing`: `fibredInGroupoidsFactorizationFromSource` and the numbered specializations in
  Lemma 4.35.16;
- `core/canonical`: `explicitTwoFibreProduct`, `explicitTwoFibreProductRightProjection`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`, and
  `BasedFunctor.IsEquivalenceOverBase`;
- `bridge/view`: the specialization of the generic explicit `2`-fibre product to `(F, id Y)`,
  together with the left-projection quasi-inverse data used in the over-base equivalence proof. -/

/-- The textbook factorization object `X' = X ×_{F,Y,\mathrm{id}} Y`, realized by the canonical
explicit `2`-fibre-product model from Lemma 4.35.7. -/
abbrev fibredInGroupoidsFactorization
    (F : X ⥤ᵇ Y) :
    BasedCategory C :=
  explicitTwoFibreProduct F (BasedFunctor.id Y)

-- Proof sketch: for each `x : X`, the comma object `(x, F(x), 𝟙_{F(x)})` has invertible
-- comparison arrow lying over the identity of `X.p.obj x`, so it belongs to the defining full
-- subcategory of the explicit `2`-fibre-product model.
/-- The canonical object `(x, F(x), id)` in the explicit factorization. -/
private abbrev fibredInGroupoidsFactorizationFromSourceObj
    (F : X ⥤ᵇ Y) (x : X.obj) :
    (fibredInGroupoidsFactorization F).obj :=
  { U := X.p.obj x
    obj :=
      { fst := ⟨x, rfl⟩
        snd := ⟨F.obj x, F.w_obj x⟩
        iso := Iso.refl _ } }

/-- The morphism of source objects induced by a morphism in `X`. -/
private def fibredInGroupoidsFactorizationFromSourceMap
    (F : X ⥤ᵇ Y) {x x' : X.obj} (a : x ⟶ x') :
    fibredInGroupoidsFactorizationFromSourceObj F x ⟶
      fibredInGroupoidsFactorizationFromSourceObj F x' where
  base := X.p.map a
  a := a
  a_over := by infer_instance
  b := F.map a
  b_over := by infer_instance
  comm := by
    change CommSq (F.map a) (𝟙 (F.obj x)) (𝟙 (F.obj x')) (F.map a)
    simp

/-- The source functor into the explicit factorization satisfies the identity law. -/
private theorem fibredInGroupoidsFactorizationFromSource_map_id
    (F : X ⥤ᵇ Y) (x : X.obj) :
    fibredInGroupoidsFactorizationFromSourceMap F (𝟙 x) =
      𝟙 (fibredInGroupoidsFactorizationFromSourceObj F x) := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · have hb :
        (((𝟙 (fibredInGroupoidsFactorizationFromSourceObj F x)) :
            fibredInGroupoidsFactorizationFromSourceObj F x ⟶
              fibredInGroupoidsFactorizationFromSourceObj F x)).b =
          𝟙 (F.obj x) := rfl
    have hmap := F.toFunctor.map_id x
    dsimp [fibredInGroupoidsFactorizationFromSourceMap] at hmap ⊢
    simp [hb] at hmap ⊢

-- Proof sketch: the left component is `a ≫ b` and the right component is `F.map (a ≫ b)`, which
-- agrees with `F.map a ≫ F.map b` by functoriality of `F`.
/-- The source functor into the explicit factorization satisfies the composition law. -/
private theorem fibredInGroupoidsFactorizationFromSource_map_comp
    (F : X ⥤ᵇ Y) {x y z : X.obj} (a : x ⟶ y) (b : y ⟶ z) :
    fibredInGroupoidsFactorizationFromSourceMap F (a ≫ b) =
      fibredInGroupoidsFactorizationFromSourceMap F a ≫
        fibredInGroupoidsFactorizationFromSourceMap F b := by
  apply ExplicitTwoFibreProductHom.ext
  · rfl
  · change F.map (a ≫ b) = F.map a ≫ F.map b
    simp

private def fibredInGroupoidsFactorizationFromSourceFunctor
    (F : X ⥤ᵇ Y) :
    X.obj ⥤ (fibredInGroupoidsFactorization F).obj where
  obj := fibredInGroupoidsFactorizationFromSourceObj F
  map := fun a ↦ fibredInGroupoidsFactorizationFromSourceMap F a
  map_id := fibredInGroupoidsFactorizationFromSource_map_id F
  map_comp := fun a b ↦ fibredInGroupoidsFactorizationFromSource_map_comp F a b

private theorem fibredInGroupoidsFactorizationFromSourceFunctor_comm
    (F : X ⥤ᵇ Y) :
    fibredInGroupoidsFactorizationFromSourceFunctor F ⋙
        (fibredInGroupoidsFactorization F).p =
      X.p := by
  rfl

/-- The canonical map `X ⟶ X'` given by `x ↦ (x, F(x), id)`. -/
abbrev fibredInGroupoidsFactorizationFromSource
    (F : X ⥤ᵇ Y) :
    X ⥤ᵇ fibredInGroupoidsFactorization F :=
  { toFunctor :=
      fibredInGroupoidsFactorizationFromSourceFunctor F
    w := fibredInGroupoidsFactorizationFromSourceFunctor_comm F }

/-- The projection `X' ⟶ Y` from the explicit factorization, forgetting the `X`-component. -/
abbrev fibredInGroupoidsFactorizationToTarget
    (F : X ⥤ᵇ Y) :
    fibredInGroupoidsFactorization F ⥤ᵇ Y :=
  explicitTwoFibreProductRightProjection F (BasedFunctor.id Y)

section

variable [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

-- Proof sketch: the factorization projection is the explicit `2`-fibre-product projection to
-- `C`, so one proves fibredness over `C` by lifting morphisms in `X` and transporting across the
-- vertical isomorphism in the `Y`-component.
/-- Lemma 4.35.16 (1): the explicit factorization object `X' = X ×_{F, Y, id} Y` is fibred in
groupoids over `C`. -/
theorem fibredInGroupoidsFactorization_isFibredInGroupoids
    (F : X ⥤ᵇ Y) :
    IsFibredInGroupoids (fibredInGroupoidsFactorization F).p := by
  simpa [fibredInGroupoidsFactorization] using
    explicitTwoFibreProductProjection_isFibredInGroupoids F (BasedFunctor.id Y)

end

-- Proof sketch: the canonical map `X ⟶ X ×_{F,Y,\mathrm{id}} Y` is an equivalence of categories,
-- with quasi-inverse given by the left projection of the explicit `2`-fibre product.
/-- The canonical comparison `X ⟶ X'` is an equivalence of categories. -/
theorem fibredInGroupoidsFactorizationFromSource_isEquivalence
    (F : X ⥤ᵇ Y) :
    (fibredInGroupoidsFactorizationFromSource F).IsEquivalence := sorry

-- Proof sketch: specialize the explicit `2`-fibre-product owner to `(F, 𝟭 Y)` and use the left
-- projection `(x, y, f) ↦ x` as a based quasi-inverse. The unit is the tautological identity on
-- `X`, while the counit at `(x, y, f)` is induced by the stored comparison isomorphism
-- `f : F(x) ≅ y`, so no fibred-in-groupoids hypotheses on `X` or `Y` are needed.
/-- Lemma 4.35.16 (2): the canonical map `X ⟶ X'` is an equivalence over the base category `C`. -/
theorem fibredInGroupoidsFactorizationFromSource_isEquivalenceOverBase
    (F : X ⥤ᵇ Y) :
    (fibredInGroupoidsFactorizationFromSource F).IsEquivalenceOverBase := by
  sorry

-- Proof sketch: the target projection from the explicit `2`-fibre-product model is the right
-- projection `(x, y, f) ↦ y`; the textbook argument shows it satisfies the fibred-in-groupoids
-- lifting and uniqueness conditions over `Y`.
-- Proof sketch: forgetting the `Y`-component after inserting `(x, F(x), id)` recovers the
-- original functor `F` by construction.
/-- Lemma 4.35.16 (3): the explicit factorization maps compose to the original functor `F`. -/
theorem fibredInGroupoidsFactorization_comp
    (F : X ⥤ᵇ Y) :
    BasedFunctor.comp
        (fibredInGroupoidsFactorizationFromSource F)
        (fibredInGroupoidsFactorizationToTarget F) =
      F :=
  rfl

section

variable [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p]

-- Proof sketch: the target projection from the explicit `2`-fibre-product model is the right
-- projection `(x, y, f) ↦ y`; the textbook argument shows it satisfies the fibred-in-groupoids
-- lifting and uniqueness conditions over `Y`, using the `Y`-side fibred-in-groupoids structure
-- over `C` to produce the needed comparison isomorphism over the identity.
/-- Lemma 4.35.16 (4): the projection `X' ⟶ Y` is fibred in groupoids over `Y`. -/
theorem fibredInGroupoidsFactorizationToTarget_isFibredInGroupoids
    (F : X ⥤ᵇ Y) :
    IsFibredInGroupoids (fibredInGroupoidsFactorizationToTarget F).toFunctor := sorry

end

end CategoryTheory
