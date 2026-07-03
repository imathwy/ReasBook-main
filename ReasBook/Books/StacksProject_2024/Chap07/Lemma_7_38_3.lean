import Mathlib
import StacksProject_2024.Chap07.Lemma_7_11_2
import StacksProject_2024.Chap07.Lemma_7_12_4
import StacksProject_2024.Chap07.Lemma_7_38_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 7.38.3: the fixed `ULift` functor used to compare small and large
type-valued sheaves. -/
private abbrev uliftTypeFunctor : Type w' ⥤ Type (max u v w') :=
  CategoryTheory.uliftFunctor.{max u v, w'}

/-- Helper for Lemma 7.38.3: the fiber functor of the universe-enlarged copy of a point. -/
private def uliftPointFiberFunctor
    (q : Point.{w'} J) : C ⥤ Type (max u v w') :=
  { obj := fun X ↦ ULift.{max u v, w'} (q.fiber.obj X)
    map := fun {X Y} f x ↦ ULift.up (q.fiber.map f x.down) }

/-- Helper for Lemma 7.38.3: adding or removing `ULift` on the fibers does not change the
covering-lift condition of a sieve. -/
private lemma point_cover_lift_ulift_iff
    (q : Point.{w'} J) {U : C} (S : Sieve U) :
    (∀ x : ULift.{max u v, w'} (q.fiber.obj U),
      ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} (q.fiber.obj Y)),
        ULift.up (q.fiber.map g y.down) = x) ↔
      (∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) := by
  constructor
  · intro h x
    -- Remove the `ULift` wrapper from a lifted witness.
    obtain ⟨Y, g, hg, y, hy⟩ := h (ULift.up.{max u v, w'} x)
    refine ⟨Y, g, hg, y.down, ?_⟩
    simpa using congrArg (ULift.down : ULift.{max u v, w'} (q.fiber.obj U) → q.fiber.obj U) hy
  · intro h x
    -- Conversely, lift any witness for `q` to a witness for the `ULift`-wrapped fibers.
    obtain ⟨Y, g, hg, y, hy⟩ := h x.down
    refine ⟨Y, g, hg, ULift.up.{max u v, w'} y, ?_⟩
    cases x
    simpa using
      congrArg (ULift.up.{max u v, w'} : q.fiber.obj U → ULift.{max u v, w'} (q.fiber.obj U)) hy

/-- Helper for Lemma 7.38.3: composing a small type-valued sheaf with the relevant `ULift`
functor still yields a sheaf in the large universe used by the statement. -/
private instance uliftFunctor_hasSheafCompose_type :
    J.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u v, w'} :
        Type w' ⥤ Type (max u v w')) where
  isSheaf P hP := by
    -- Rewrite the sheaf condition into the type-valued form where `ULift` preserves sheaves.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := J)
      ((isSheaf_iff_isSheaf_of_type J P).1 hP)

/-- Helper for Lemma 7.38.3: the larger `ULift` target universe still admits sheafification. -/
private instance hasSheafify_ulift_type :
    HasSheafify J (Type (max u v w')) := by
  -- The larger universe is large enough to index the cover multiequalizers used by sheafification.
  letI : ∀ X : C, Small.{max u v w', max u v} (J.Cover X)ᵒᵖ := by infer_instance
  infer_instance

/- Layering for Lemma 7.38.3:
- primary domain: conservative families of points of a site and their detection of equality of
  sections through point fibers;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `isConservativePointFamily_iff`,
  `JointlyFaithful.jointlyReflectsIsomorphisms`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook criterion that distinct local sections are separated by some germ
    at a point of the family;
  `core/canonical`: `(ofObj p).IsConservativeFamilyOfPoints`;
  `bridge/view`: the indexed-family recall `isConservativePointFamily_iff`, together with the
    sheafified-representable Yoneda equivalence used to compare sections with morphisms out of
    `h[U]^#[J]`.
- primitive data: only the indexed family of points `p`;
- derived API here: the source-facing separation criterion.

The owner abstraction remains `(ofObj p).IsConservativeFamilyOfPoints`; this file should stay a
thin source-facing bridge, not a second owner for conservative point families.
-/

-- Proof sketch: for the forward implication, if two sections have the same germ at every point of
-- the family, apply conservativity to the corresponding morphisms `h[U]^#[J] ⟶ ℱ`, using
-- `uliftSheafifiedRepresentableHomEquiv` to pass between sections and sheaf morphisms and the
-- canonical point-fiber comparison for sheafified representables. For the converse, use the
-- separation hypothesis to show the stalk family is jointly faithful on sheaves of sets; then the
-- generic owner theorem `JointlyFaithful.jointlyReflectsIsomorphisms`, combined with
-- `isConservativePointFamily_iff`, upgrades that joint faithfulness to conservativity.
/-- Helper for Lemma 7.38.3: the canonical generator of the point fiber of `uliftYoneda.obj U`. -/
private noncomputable abbrev point_uliftYoneda_generator
    (q : Point.{w'} J) (U : C) :
    q.fiber.obj U →
      q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) :=
  fun x ↦
    q.toPresheafFiber U x (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
      (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
        ULift.up (𝟙 U))

/-- Helper for Lemma 7.38.3: the explicit descent map from the fiber of `uliftYoneda.obj U` back
to the point fiber over `U`. -/
private lemma point_uliftYoneda_extract_naturality
    (q : Point.{w'} J) (U : C) {X Y : C} (f : X ⟶ Y) (x : q.fiber.obj X) :
    (CategoryTheory.uliftYoneda.{max u v w'}.obj U).map f.op ≫
      (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ↦
        ULift.up (q.fiber.map (ULift.down z) x)) =
    (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op Y) ↦
      ULift.up (q.fiber.map (ULift.down z) (q.fiber.map f x))) := by
  -- The representable transition map acts by precomposition, so both sides are the same by
  -- functoriality of the point fiber.
  funext z
  simp [CategoryTheory.uliftYoneda]

/-- Helper for Lemma 7.38.3: the extractor family satisfies the compatibility hypothesis needed
for `presheafFiberDesc`. -/
private lemma point_uliftYoneda_extract_compatible
    (q : Point.{w'} J) (U : C) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : q.fiber.obj X),
      (CategoryTheory.uliftYoneda.{max u v w'}.obj U).map f.op ≫
        (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ↦
          ULift.up (q.fiber.map (ULift.down z) x)) =
      (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op Y) ↦
        ULift.up (q.fiber.map (ULift.down z) (q.fiber.map f x))) := by
  intro X Y f x
  exact point_uliftYoneda_extract_naturality (q := q) U f x

/-- Helper for Lemma 7.38.3: the fiber of `uliftYoneda.obj U` at a point maps back to the lifted
fiber over `U`. -/
private noncomputable def point_uliftYoneda_extract
    (q : Point.{w'} J) (U : C) :
    q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) ⟶
      ULift (q.fiber.obj U) :=
  q.presheafFiberDesc
    (fun X x ↦
      fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ↦
        ULift.up (q.fiber.map (ULift.down z) x))
    (point_uliftYoneda_extract_compatible (q := q) U)

/-- Helper for Lemma 7.38.3: the extractor on the fiber of `uliftYoneda.obj U` evaluates a
canonical generator by composing the represented morphism in the point fiber. -/
private lemma point_uliftYoneda_extract_toPresheafFiber
    (q : Point.{w'} J) (U X : C) (x : q.fiber.obj X)
    (z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X)) :
    point_uliftYoneda_extract (q := q) U
        (q.toPresheafFiber X x (CategoryTheory.uliftYoneda.{max u v w'}.obj U) z) =
      ULift.up (q.fiber.map (ULift.down z) x) := by
  let φ :
      ∀ (X : C) (_ : q.fiber.obj X),
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ⟶
          ULift (q.fiber.obj U) :=
    fun X x z ↦ ULift.up (q.fiber.map (ULift.down z) x)
  -- Evaluate the universal descent map on the canonical colimit generator.
  have h := congr_fun
    (q.toPresheafFiber_presheafFiberDesc φ
      (point_uliftYoneda_extract_compatible (q := q) U) X x) z
  simpa [point_uliftYoneda_extract, φ] using h

/-- Helper for Lemma 7.38.3: the generators coming from `x ∈ u(U)` are already surjective on the
fiber of `uliftYoneda.obj U`. -/
private lemma point_uliftYoneda_generator_surjective
    (q : Point.{w'} J) (U : C) :
    Function.Surjective (point_uliftYoneda_generator (q := q) U) := by
  intro p
  refine ⟨ULift.down (point_uliftYoneda_extract (q := q) U p), ?_⟩
  let φ :
      q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) ⟶
        q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) :=
    fun p ↦
      point_uliftYoneda_generator (q := q) U
        (ULift.down (point_uliftYoneda_extract (q := q) U p))
  have hφ : φ = 𝟙 _ := by
    -- The extractor followed by the generator fixes each colimit generator, so it is the identity.
    apply q.presheafFiber_hom_ext
    intro X x
    ext z
    have hz :=
      point_uliftYoneda_extract_toPresheafFiber (q := q) U X x z
    have hw := congr_fun
      (q.toPresheafFiber_w (ULift.down z) x
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
      (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
        ULift.up (𝟙 U))
    have hw' :
        q.toPresheafFiber X x (CategoryTheory.uliftYoneda.{max u v w'}.obj U) z =
          q.toPresheafFiber U (q.fiber.map (ULift.down z) x)
            (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
            (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
              ULift.up (𝟙 U)) := by
      simpa [CategoryTheory.uliftYoneda] using hw
    simpa [φ, point_uliftYoneda_generator, hz] using hw'.symm
  simpa [φ] using congr_fun hφ p

/-- Helper for Lemma 7.38.3: a point-fiber element determines the corresponding stalk element of
`h_U^#` at the point. -/
noncomputable def point_sheafifiedRepresentable_stalkElem
    [HasWeakSheafify J (Type (max u v w'))]
    (q : Point.{w'} J) (U : C) (x : q.fiber.obj U) :
    q.sheafFiber.obj (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U) :=
  q.presheafFiber.map
      (CategoryTheory.toSheafify J
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
    (point_uliftYoneda_generator (q := q) U x)

/-- Helper for Lemma 7.38.3: every stalk element of `h_U^#` at a point comes from some
`x ∈ u(U)`. -/
lemma point_sheafifiedRepresentable_stalkElem_surjective
    [HasWeakSheafify J (Type (max u v w'))]
    (q : Point.{w'} J) (U : C) :
    Function.Surjective (point_sheafifiedRepresentable_stalkElem (q := q) U) := by
  -- Route correction: instead of forcing a universe-mismatched stalk/fiber isomorphism, use the
  -- explicit `toSheafify` map and the concrete inverse on the `uliftYoneda` fiber.
  let hbij :
      Function.Bijective
        (q.presheafFiber.map
          (CategoryTheory.toSheafify J
            (CategoryTheory.uliftYoneda.{max u v w'}.obj U))) := by
    exact
      (isIso_iff_bijective
        (q.presheafFiber.map
          (CategoryTheory.toSheafify J
            (CategoryTheory.uliftYoneda.{max u v w'}.obj U)))).1 (by infer_instance)
  intro p
  obtain ⟨y, rfl⟩ := hbij.surjective p
  obtain ⟨x, rfl⟩ := point_uliftYoneda_generator_surjective (q := q) U y
  exact ⟨x, rfl⟩

/-- Helper for Lemma 7.38.3: evaluating a morphism out of `h_U^#` on the canonical stalk element
coming from `x` recovers the corresponding germ. -/
private lemma sheafifiedRepresentable_stalk_map_apply
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : Point.{w'} J) (U : C)
    (α : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U ⟶ ℱ)
    (x : q.fiber.obj U) :
    (q.sheafFiber.map α)
        (point_sheafifiedRepresentable_stalkElem (q := q) U x) =
      q.toPresheafFiber U x ℱ.obj
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
  -- Expand the canonical stalk element through `toSheafify`, then use naturality of
  -- `toPresheafFiber` for the adjunct presheaf morphism `uliftYoneda.obj U ⟶ ℱ.obj`.
  simpa [point_sheafifiedRepresentable_stalkElem,
    CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv] using
    (q.toPresheafFiber_naturality_apply
      (CategoryTheory.toSheafify J
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U) ≫ α.hom)
      U x
      (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
        ULift.up (𝟙 U)))

/-- Helper for Lemma 7.38.3: evaluating two morphisms out of `h_U^#` at the canonical stalk
element from `x` agrees exactly when the corresponding germs agree. -/
lemma sheafifiedRepresentable_stalk_map_eq_iff
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : Point.{w'} J) (U : C)
    (α β : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U ⟶ ℱ)
    (x : q.fiber.obj U) :
    (q.sheafFiber.map α)
        (point_sheafifiedRepresentable_stalkElem (q := q) U x) =
      (q.sheafFiber.map β)
        (point_sheafifiedRepresentable_stalkElem (q := q) U x) ↔
      q.toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
        q.toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U β) := by
  -- Rewrite both sides by the explicit stalk-evaluation formula for the canonical generator.
  constructor
  · intro h
    simpa [sheafifiedRepresentable_stalk_map_apply (q := q) U α x,
      sheafifiedRepresentable_stalk_map_apply (q := q) U β x] using h
  · intro h
    simpa [sheafifiedRepresentable_stalk_map_apply (q := q) U α x,
      sheafifiedRepresentable_stalk_map_apply (q := q) U β x] using h

/-- Helper for Lemma 7.38.3: equality of all germs over `U` forces equality of the induced maps on
the stalk of `h_U^#` at the point. -/
lemma sheafifiedRepresentable_stalk_map_ext_of_pointwise_germ_eq
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : Point.{w'} J) (U : C)
    (α β : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U ⟶ ℱ)
    (hαβ :
      ∀ x : q.fiber.obj U,
        q.toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
          q.toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U β)) :
    q.sheafFiber.map α = q.sheafFiber.map β := by
  -- The canonical generators `x ∈ u(U)` are already surjective on the stalk of `h_U^#`, so it
  -- suffices to compare the two stalk maps on those generators.
  ext p
  obtain ⟨x, rfl⟩ := point_sheafifiedRepresentable_stalkElem_surjective (q := q) U p
  exact (sheafifiedRepresentable_stalk_map_eq_iff (q := q) U α β x).2 (hαβ x)

/-- Helper for Lemma 7.38.3: conservativity of the small family already gives joint faithfulness
of the corresponding stalk functors on small set-valued sheaves. -/
private lemma small_stalkFamily_jointlyFaithful_small_type
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] :
    JointlyFaithful
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type w') ⥤ Type w')) := by
  refine ⟨?_⟩
  intro ℱ 𝒢 φ ψ hφ
  -- Reindex the owner theorem `hp.jointlyFaithful (Type w')` back along `ofObj p`.
  exact (hp.jointlyFaithful (Type w')).map_injective fun Φ ↦ by
    rcases Φ with ⟨q, hq⟩
    rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
    exact hφ i

/-- Helper for Lemma 7.38.3: on small set-valued sheaves, equality on every stalk of the family
forces equality of morphisms. -/
private lemma sheaf_hom_ext_of_stalkwise_small_type
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C]
    {ℱ 𝒢 : Sheaf J (Type w')} {φ ψ : ℱ ⟶ 𝒢}
    (hφ : ∀ i, (p i).sheafFiber.map φ = (p i).sheafFiber.map ψ) :
    φ = ψ := by
  -- Apply the small-target joint faithfulness established just above.
  exact (small_stalkFamily_jointlyFaithful_small_type (p := p) hp).map_injective hφ

/-- Helper for Lemma 7.38.3: if the family separates unequal sections, then the associated stalk
functors on sheaves of sets are jointly faithful. -/
lemma stalkFamily_jointlyFaithful_of_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    JointlyFaithful
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type (max u v w')) ⥤ Type (max u v w'))) := by
  refine ⟨?_⟩
  intro ℱ 𝒢 φ ψ hφ
  -- Compare morphisms sectionwise; any unequal section values would be separated by some stalk.
  ext U s
  by_contra hs
  obtain ⟨i, x, hx⟩ := hsep U.unop ((φ.hom.app U) s) ((ψ.hom.app U) s) hs
  let a : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w',u,v} J U.unop ⟶ ℱ :=
    (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
      J ℱ U.unop).symm s
  have hi :
      ((p i).sheafFiber.map φ)
          (((p i).sheafFiber.map a)
            (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x)) =
        ((p i).sheafFiber.map ψ)
          (((p i).sheafFiber.map a)
            (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x)) := by
    exact congr_fun (hφ i)
      (((p i).sheafFiber.map a)
        (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x))
  have hi' :
      ((p i).sheafFiber.map (a ≫ φ))
          (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x) =
        ((p i).sheafFiber.map (a ≫ ψ))
          (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x) := by
    simpa [Functor.map_comp, Category.assoc] using hi
  have hcompφ :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ φ) = φ.hom.app U s := by
    have ha :
        CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a = s := by
      simpa [a] using
        (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J ℱ U.unop).apply_symm_apply s
    calc
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ φ) =
        φ.hom.app U
          (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a) := by
              simpa using
                (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{w',u,v}
                  J a φ)
      _ = φ.hom.app U s := by rw [ha]
  have hcompψ :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ ψ) = ψ.hom.app U s := by
    have ha :
        CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a = s := by
      simpa [a] using
        (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J ℱ U.unop).apply_symm_apply s
    calc
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ ψ) =
        ψ.hom.app U
          (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a) := by
              simpa using
                (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{w',u,v}
                  J a ψ)
      _ = ψ.hom.app U s := by rw [ha]
  exact hx <| by
    simpa [hcompφ, hcompψ] using
      (sheafifiedRepresentable_stalk_map_eq_iff (q := p i) U.unop (a ≫ φ) (a ≫ ψ) x).1 hi'

/-- Helper for Lemma 7.38.3: the section-separation hypothesis upgrades the large stalk family to a
jointly-reflecting family for isomorphisms of set-valued sheaves. -/
lemma stalkFamily_jointlyReflectsIsomorphisms_of_separating_sections_large
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    JointlyReflectIsomorphisms
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type (max u v w')) ⥤ Type (max u v w'))) := by
  -- Once the large stalk family is jointly faithful, the balanced category of sheaves upgrades
  -- that to joint reflection of isomorphisms.
  exact CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms
    (stalkFamily_jointlyFaithful_of_separating_sections (p := p) hsep)

/-- Helper for Lemma 7.38.3: for type-valued presheaves, equality of two germs in a point fiber
is witnessed after pulling back along some arrow landing at the chosen point element. -/
private lemma point_fiber_eq_iff_of_type
    (q : Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (X : C) (x : q.fiber.obj X) (z₁ z₂ : P.obj (op X)) :
    q.toPresheafFiber X x P z₁ = q.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : q.fiber.obj Y), q.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  constructor
  · intro h
    -- Equality in the filtered colimit comes from some later stage of the category of elements.
    obtain ⟨j, f, hf⟩ :=
      (Limits.Types.FilteredColimit.isColimit_eq_iff'
        (ht := q.isColimitPresheafFiberCocone P) (i := op ⟨X, x⟩) z₁ z₂).1 h
    exact ⟨j.unop.1, f.unop.val, j.unop.2, f.unop.property, hf⟩
  · rintro ⟨Y, f, y, hy, hEq⟩
    -- Conversely, any common refinement in the category of elements identifies the two germs.
    exact (Limits.Types.FilteredColimit.isColimit_eq_iff'
      (ht := q.isColimitPresheafFiberCocone P) (i := op ⟨X, x⟩) z₁ z₂).2
      ⟨op ⟨Y, y⟩, op (CategoryOfElements.homMk ⟨Y, y⟩ ⟨X, x⟩ f hy), hEq⟩

/-- Helper for Lemma 7.38.3: equality of the germs of two sections at a chosen point element
produces a lift of that point element through the equalizer sieve of the two sections. -/
private lemma pointwise_germ_eq_gives_equalizer_lift
    (q : Point.{w'} J) {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U)) {x : q.fiber.obj U}
    (hx : q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s') :
    ∃ (Y : C) (g : Y ⟶ U) (_ : Presheaf.equalizerSieve (F := ℱ.obj) s s' g) (y : q.fiber.obj Y),
      q.fiber.map g y = x := by
  -- Read equality in the filtered colimit as equality after pulling back to a common stage.
  obtain ⟨Y, g, y, hy, hEq⟩ :=
    (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').1 hx
  refine ⟨Y, g, hEq, y, hy⟩

/-- Helper for Lemma 7.38.3: equality of two lifted germs is equivalent to equality of the
original germs before applying `ULift`. -/
private lemma point_ulift_presheafFiber_eq_iff
    (q : Point.{w'} J) {ℱ : Sheaf J (Type w')} (U : C) (x : q.fiber.obj U)
    (s s' : ℱ.obj.obj (op U)) :
    q.toPresheafFiber U x
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj
        (show
          (((sheafCompose J
            (CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
            from ULift.up.{max u v, w'} s) =
      q.toPresheafFiber U x
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj
        (show
          (((sheafCompose J
            (CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
            from ULift.up.{max u v, w'} s') ↔
      q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s' := by
  constructor
  · intro h
    -- The lifted equality is witnessed after pullback at some stage; drop `ULift` there.
    obtain ⟨Y, f, y, hy, hEq⟩ :=
      (point_fiber_eq_iff_of_type
        (q := q)
        (P := ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj)
        U x _ _).1 h
    exact (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').2
      ⟨Y, f, y, hy, by simpa [CategoryTheory.uliftFunctor_map] using hEq⟩
  · intro h
    -- Any witness for the original equality also witnesses the lifted equality after `ULift`.
    obtain ⟨Y, f, y, hy, hEq⟩ :=
      (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').1 h
    exact (point_fiber_eq_iff_of_type
      (q := q)
      (P := ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u v, w'} :
          Type w' ⥤ Type (max u v w'))).obj ℱ).obj)
      U x _ _).2
      ⟨Y, f, y, hy, by simpa [CategoryTheory.uliftFunctor_map] using hEq⟩

/-- Helper for Lemma 7.38.3: the large separating-sections hypothesis immediately yields the same
separation property for small type-valued sheaves. -/
lemma small_separating_sections_of_large
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
      s ≠ s' →
        ∃ i : ι, ∃ x : (p i).fiber.obj U,
          (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s' := by
  intro ℱ U s s' hs
  -- Apply the large hypothesis to the `ULift`-whiskered sheaf and then remove `ULift` from the
  -- resulting germ inequality.
  obtain ⟨i, x, hx⟩ :=
    hsep
      (ℱ := (sheafCompose J
        (CategoryTheory.uliftFunctor.{max u v, w'} :
          Type w' ⥤ Type (max u v w'))).obj ℱ)
      U
      (show
        (((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
          from ULift.up.{max u v, w'} s)
      (show
        (((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
          from ULift.up.{max u v, w'} s') <| by
        intro hEq
        exact hs <| by simpa using hEq
  refine ⟨i, x, ?_⟩
  intro hEq
  apply hx
  exact (point_ulift_presheafFiber_eq_iff (q := p i) U x s s').2 hEq

/-- Helper for Lemma 7.38.3: once unequal sections are separated by some germ, stalkwise
isomorphisms force a morphism of small set-valued sheaves to be mono. -/
private lemma sheaf_mono_of_stalkwise_isIso_of_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s')
    {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ)) :
    Mono φ := by
  rw [← Sheaf.isLocallyInjective_iff_mono]
  rw [Sheaf.isLocallyInjective_iff_injective]
  intro U s s' hs
  by_contra hss
  obtain ⟨i, x, hx⟩ := hsep U.unop s s' hss
  have hEq :
      ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
        ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s') := by
    -- Naturality converts equality of sections after `φ` into equality of their germs.
    have hLeft :
        ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
          (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s) := by
      simpa using congrFun ((p i).toPresheafFiber_naturality φ.hom U.unop x) s
    have hMid :
        (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s) =
          (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s') := by
      simpa using congrArg ((p i).toPresheafFiber U.unop x 𝒢.obj) hs
    have hRight :
        (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s') =
          ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s') := by
      symm
      simpa using congrFun ((p i).toPresheafFiber_naturality φ.hom U.unop x) s'
    exact hLeft.trans (hMid.trans hRight)
  have hinj : Function.Injective ((p i).sheafFiber.map φ) := by
    exact (isIso_iff_bijective ((p i).sheafFiber.map φ)).1 (hφ i) |>.injective
  exact hx (hinj hEq)

/-- Helper for Lemma 7.38.3: if all stalk maps of `φ` are isomorphisms, then the same is true for
the stalk maps of the pushout coprojection `pushout.inl φ φ`. -/
lemma sheafFiber_map_pushoutInl_isIso_of_stalkwise_isIso
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢) [HasPushout φ φ]
    (hφ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ)) :
    ∀ i : ι, IsIso ((p i).sheafFiber.map (pushout.inl φ φ)) := by
  intro i
  -- Map the actual pushout cocone of `φ` through the stalk functor.
  let _ : PreservesColimit (span φ φ) (p i).sheafFiber := by
    infer_instance
  let hc := isColimitOfHasPushoutOfPreservesColimit ((p i).sheafFiber) φ φ
  -- Since the mapped stalk map is an isomorphism, it is in particular an epimorphism.
  let _ : IsIso ((p i).sheafFiber.map φ) := hφ i
  have hEpi : Epi ((p i).sheafFiber.map φ) := by
    infer_instance
  -- The universal pushout criterion identifies this epi with invertibility of `pushout.inl`.
  exact (epi_iff_isIso_inl hc).1 hEpi

/-- Helper for Lemma 7.38.3: if all stalk maps of `φ` are isomorphisms, then the same is true for
the stalk maps of its pushout codiagonal. -/
lemma stalkwise_isIso_codiagonal_of_stalkwise_isIso
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢) [HasPushout φ φ]
    (hφ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ)) :
    ∀ i : ι, IsIso ((p i).sheafFiber.map (pushout.codiagonal φ)) := by
  intro i
  -- First make the mapped coprojection invertible by the mapped pushout cocone criterion.
  let _ : IsIso ((p i).sheafFiber.map (pushout.inl φ φ)) :=
    sheafFiber_map_pushoutInl_isIso_of_stalkwise_isIso (p := p) (φ := φ) hφ i
  have hcomp :
      (p i).sheafFiber.map (pushout.inl φ φ) ≫
          (p i).sheafFiber.map (pushout.codiagonal φ) =
        𝟙 _ := by
    -- The codiagonal is a right inverse to `pushout.inl`, and this identity survives under any
    -- functor.
    calc
      (p i).sheafFiber.map (pushout.inl φ φ) ≫
          (p i).sheafFiber.map (pushout.codiagonal φ) =
        (p i).sheafFiber.map (pushout.inl φ φ ≫ pushout.codiagonal φ) := by
          rw [Functor.map_comp]
      _ = (p i).sheafFiber.map (𝟙 _) := by
        rw [pushout.inl_codiagonal]
      _ = 𝟙 _ := by
        simp
  have hcod :
      (p i).sheafFiber.map (pushout.codiagonal φ) =
        inv ((p i).sheafFiber.map (pushout.inl φ φ)) := by
    -- An isomorphism is determined by its right inverse, so the mapped codiagonal is the inverse
    -- of the mapped coprojection.
    calc
      (p i).sheafFiber.map (pushout.codiagonal φ) =
          𝟙 _ ≫ (p i).sheafFiber.map (pushout.codiagonal φ) := by
            simp
      _ = inv ((p i).sheafFiber.map (pushout.inl φ φ)) ≫
            ((p i).sheafFiber.map (pushout.inl φ φ) ≫
              (p i).sheafFiber.map (pushout.codiagonal φ)) := by
            simp
      _ = inv ((p i).sheafFiber.map (pushout.inl φ φ)) := by
            simp [hcomp]
  rw [hcod]
  infer_instance

/-- Helper for Lemma 7.38.3: the image sieve of the canonical universe-lifted sieve inclusion at
the identity section is the original sieve. -/
private lemma imageSieve_uliftFunctorInclusion_id
    {U : C} (S : Sieve U) :
    Presheaf.imageSieve S.uliftFunctorInclusion
        (show (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op U) from
          ULift.up (𝟙 U)) =
      S := by
  -- Unpack the image-sieve definition: the lifted generator at the identity sees exactly the
  -- original arrows of `S`.
  ext V g
  constructor
  · rintro ⟨t, ht⟩
    change ULift.up t.down.1 = ULift.up (g ≫ 𝟙 U) at ht
    have ht' : t.down.1 = g := by
      simpa using congrArg ULift.down ht
    simpa [ht'] using t.down.2
  · intro hg
    refine ⟨ULift.up ⟨g, by simpa using hg⟩, ?_⟩
    change ULift.up g = ULift.up (g ≫ 𝟙 U)
    simp

/-- Helper for Lemma 7.38.3: every element of a type-valued point fiber is represented by some
section at some stage of the filtered colimit. -/
private lemma point_presheafFiber_jointly_surjective_of_type
    (q : Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (p : q.presheafFiber.obj P) :
    ∃ (X : C) (x : q.fiber.obj X) (z : P.obj (op X)),
      q.toPresheafFiber X x P z = p := by
  -- Unpack the concrete colimit defining the point fiber in `Type`.
  obtain ⟨⟨X, x⟩, z, h⟩ :=
    Types.jointly_surjective_of_isColimit (q.isColimitPresheafFiberCocone P) p
  exact ⟨X, x, z, h⟩

/-- Helper for Lemma 7.38.3: two elements of a type-valued point fiber can be represented at a
common stage of the filtered colimit. -/
private lemma point_presheafFiber_jointly_surjective₂_of_type
    (q : Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (p₁ p₂ : q.presheafFiber.obj P) :
    ∃ (X : C) (x : q.fiber.obj X) (z₁ z₂ : P.obj (op X)),
      q.toPresheafFiber X x P z₁ = p₁ ∧ q.toPresheafFiber X x P z₂ = p₂ := by
  -- Use the filtered-colimit description to choose simultaneous representatives.
  obtain ⟨⟨X, x⟩, z₁, z₂, h₁, h₂⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (q.isColimitPresheafFiberCocone P) p₁ p₂
  exact ⟨X, x, z₁, z₂, h₁, h₂⟩

/-- Helper for Lemma 7.38.3: if every point of `u(U)` lifts through a sieve `S`, then the map on
point fibers induced by `S.uliftFunctorInclusion` is surjective. -/
private lemma point_uliftFunctorInclusion_presheafFiber_surjective_of_lifts
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Surjective
      (q.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)) := by
  intro p
  -- First reduce the target fiber element to the canonical generator coming from some `x ∈ u(U)`.
  obtain ⟨x, rfl⟩ := point_uliftYoneda_generator_surjective (q := q) U p
  obtain ⟨Y, g, hg, y, hy⟩ := hlift x
  refine ⟨q.toPresheafFiber Y y (Sieve.uliftFunctor.{max u v w'} S)
      (ULift.up ⟨g, hg⟩), ?_⟩
  -- Naturality computes the image of the lifted arrow under the sieve inclusion.
  have hη :
      q.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)
          (q.toPresheafFiber Y y (Sieve.uliftFunctor.{max u v w'} S)
            (ULift.up ⟨g, hg⟩)) =
        q.toPresheafFiber Y y (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
          (ULift.up g) := by
    simpa using
      congrFun
        (q.toPresheafFiber_naturality
          (Sieve.uliftFunctorInclusion.{max u v w'} S) Y y)
        (ULift.up ⟨g, hg⟩)
  -- The represented arrow `g` lands at the chosen element `x`, so this is exactly the canonical
  -- generator at `x`.
  have hgerm :
      q.toPresheafFiber Y y (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
          (ULift.up g) =
        point_uliftYoneda_generator (q := q) U x := by
    have hw :=
      congrFun
        (q.toPresheafFiber_w g y
          (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
        (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
          ULift.up (𝟙 U))
    simpa [point_uliftYoneda_generator, CategoryTheory.uliftYoneda, hy] using hw
  exact hη.trans hgerm

/-- Helper for Lemma 7.38.3: the universe-lifted inclusion of a sieve is objectwise injective. -/
private lemma uliftFunctorInclusion_app_injective
    {U : C} (S : Sieve U) (X : Cᵒᵖ) :
    Function.Injective ((Sieve.uliftFunctorInclusion.{max u v w'} S).app X) := by
  intro a b h
  cases a with
  | up a =>
    cases b with
    | up b =>
      -- Forget the outer `ULift`; the inclusion only remembers the underlying arrow of the sieve.
      have hab : a.1 = b.1 := by
        simpa using congrArg ULift.down h
      have hab' : a = b := Subtype.ext hab
      subst hab'
      rfl

/-- Helper for Lemma 7.38.3: pointwise lift witnesses through `S` make the induced map on point
fibers bijective. -/
private lemma point_uliftFunctorInclusion_presheafFiber_bijective_of_lifts
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    [LocallySmall.{w'} C]
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Bijective
      (q.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)) := by
  let _ : Presheaf.IsLocallyInjective J (Sieve.uliftFunctorInclusion.{max u v w'} S) :=
    -- Local injectivity is immediate because the lifted sieve inclusion is objectwise injective.
    Presheaf.isLocallyInjective_of_injective J
      (Sieve.uliftFunctorInclusion.{max u v w'} S)
      (uliftFunctorInclusion_app_injective (S := S))
  constructor
  · -- Once local injectivity is available, the owner theorem upgrades it to injectivity on fibers.
    exact q.toPresheafFiber_map_injective (Sieve.uliftFunctorInclusion.{max u v w'} S)
  · -- Surjectivity is the concrete part: every generator `x ∈ u(U)` already lifts through `S`.
    exact point_uliftFunctorInclusion_presheafFiber_surjective_of_lifts (q := q) S hlift

/-- Helper for Lemma 7.38.3: the image sieve of the lifted sieve inclusion on the section
represented by `g` is the pullback of the original sieve along `g`. -/
private lemma imageSieve_uliftFunctorInclusion_eq_pullback
    {U : C} (S : Sieve U) {V : C} (g : V ⟶ U) :
    Presheaf.imageSieve S.uliftFunctorInclusion
        (show (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op V) from ULift.up g) =
      S.pullback g := by
  let s : (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op U) := ULift.up (𝟙 U)
  have hpull := Presheaf.pullback_imageSieve S.uliftFunctorInclusion s g
  rw [imageSieve_uliftFunctorInclusion_id (S := S)] at hpull
  have hmap :
      Presheaf.imageSieve S.uliftFunctorInclusion
          (show (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op V) from ULift.up g) =
      Presheaf.imageSieve S.uliftFunctorInclusion
          ((CategoryTheory.uliftYoneda.obj.{max u v w'} U).map g.op s) := by
    ext W h
    simp [Presheaf.imageSieve, s]
  exact hmap.trans hpull.symm

/-- Helper for Lemma 7.38.3: the image sieve of the small shrink-functor inclusion at the
identity section is exactly the original sieve. -/
private lemma imageSieve_shrinkFunctor_ι_id
    [LocallySmall.{w'} C] {U : C} (S : Sieve U) :
    Presheaf.imageSieve (Sieve.shrinkFunctor.{w'} S).ι
        (show (shrinkYoneda.{w'}.obj U).obj (op U) from
          shrinkYonedaObjObjEquiv.symm (𝟙 U)) =
      S := by
  -- Unpack the image-sieve definition: the shrink-functor generator at the identity sees exactly
  -- the arrows already lying in `S`.
  ext V g
  constructor
  · rintro ⟨t, ht⟩
    have ht' :
        t.1 = shrinkYonedaObjObjEquiv.symm g := by
      calc
        t.1 = ((Sieve.shrinkFunctor.{w'} S).ι.app (op V)) t := rfl
        _ =
            (shrinkYoneda.{w'}.obj U).map g.op
              (show (shrinkYoneda.{w'}.obj U).obj (op U) from
                shrinkYonedaObjObjEquiv.symm (𝟙 U)) := ht
        _ = shrinkYonedaObjObjEquiv.symm g := by
            simpa using shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 U)
    have htg : shrinkYonedaObjObjEquiv t.1 = g := by
      simpa using congrArg shrinkYonedaObjObjEquiv ht'
    simpa [htg] using (show S (shrinkYonedaObjObjEquiv t.1) from t.2)
  · intro hg
    refine ⟨⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩, ?_⟩
    simpa using (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 U)).symm

/-- Helper for Lemma 7.38.3: if every point of `u(U)` lifts through a sieve `S`, then the map on
point fibers induced by `S.shrinkFunctor.ι` is surjective. -/
private lemma point_shrinkFunctor_presheafFiber_surjective_of_lifts
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Surjective
      (q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  intro p
  obtain ⟨x, rfl⟩ := (q.shrinkYonedaCompPresheafFiberIso.app U).toEquiv.symm.surjective p
  obtain ⟨Y, g, hg, y, hy⟩ := hlift x
  refine ⟨q.toPresheafFiber Y y (Sieve.shrinkFunctor.{w'} S).toFunctor
      ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩, ?_⟩
  -- Compute the image of the chosen representative under the sieve inclusion.
  have hmap :
      q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι
          (q.toPresheafFiber Y y (Sieve.shrinkFunctor.{w'} S).toFunctor
            ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩) =
        q.toPresheafFiber Y y (shrinkYoneda.{w'}.obj U)
          (shrinkYonedaObjObjEquiv.symm g) := by
    simpa using
      congrFun
        (q.toPresheafFiber_naturality ((Sieve.shrinkFunctor.{w'} S).ι) Y y)
        ⟨shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩
  have hshrink :
      q.toPresheafFiber Y y (shrinkYoneda.{w'}.obj U)
          (shrinkYonedaObjObjEquiv.symm g) =
        (q.shrinkYonedaCompPresheafFiberIso.app U).toEquiv.symm (q.fiber.map g y) := by
    calc
      q.toPresheafFiber Y y (shrinkYoneda.{w'}.obj U)
          (shrinkYonedaObjObjEquiv.symm g) =
        q.presheafFiber.map (shrinkYoneda.{w'}.map g)
          ((q.shrinkYonedaCompPresheafFiberIso.app Y).toEquiv.symm y) := by
            simpa using
              (q.presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
                (f := g) (x := y)).symm
      _ = (q.shrinkYonedaCompPresheafFiberIso.app U).toEquiv.symm (q.fiber.map g y) := by
            simpa using (congrFun (q.shrinkYonedaCompPresheafFiberIso.inv.naturality g) y).symm
  exact hmap.trans (hshrink.trans (by rw [hy]))

/-- Helper for Lemma 7.38.3: the small shrink-functor inclusion is objectwise injective. -/
private lemma shrinkFunctor_ι_app_injective
    [LocallySmall.{w'} C] {U : C} (S : Sieve U) (X : Cᵒᵖ) :
    Function.Injective ((Sieve.shrinkFunctor.{w'} S).ι.app X) := by
  intro a b h
  exact Subtype.ext h

/-- Helper for Lemma 7.38.3: pointwise lift witnesses through `S` make the induced map on point
fibers of `S.shrinkFunctor.ι` bijective. -/
private lemma point_shrinkFunctor_presheafFiber_bijective_of_lifts
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) :
    Function.Bijective
      (q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  let _ : Presheaf.IsLocallyInjective J (Sieve.shrinkFunctor.{w'} S).ι :=
    -- Local injectivity is immediate because `S.shrinkFunctor.ι` is objectwise injective.
    Presheaf.isLocallyInjective_of_injective J
      (Sieve.shrinkFunctor.{w'} S).ι
      (shrinkFunctor_ι_app_injective (S := S))
  constructor
  · -- Local injectivity upgrades objectwise injectivity to injectivity on the point fiber.
    exact q.toPresheafFiber_map_injective (Sieve.shrinkFunctor.{w'} S).ι
  · -- Surjectivity comes from lifting every generator `x ∈ u(U)` through the sieve.
    exact point_shrinkFunctor_presheafFiber_surjective_of_lifts (q := q) (S := S) hlift

/-- Helper for Lemma 7.38.3: lifted witness packages descend to surjectivity on the point fiber
of the small shrink-functor inclusion. -/
private lemma point_shrinkFunctor_presheafFiber_surjective_of_ulift_lifts
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {U : C} (S : Sieve U)
    (hlift :
      ∀ x : ULift.{max u v, w'} (q.fiber.obj U),
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} (q.fiber.obj Y)),
          ULift.up (q.fiber.map g y.down) = x) :
    Function.Surjective
      (q.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  -- First remove the `ULift` wrapper from the witness package, then apply the small shrink-fiber
  -- surjectivity lemma.
  refine point_shrinkFunctor_presheafFiber_surjective_of_lifts (q := q) (S := S) ?_
  exact (point_cover_lift_ulift_iff (q := q) (U := U) S).1 hlift

/-- Helper for Lemma 7.38.3: the `ULift`-based shrink-functor surjectivity package reindexes from
the original family index type to the owner full subcategory. -/
private lemma shrinkFunctor_surjective_fullSubcategory_of_ulift_lifts
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J) {U : C} (S : Sieve U)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj U)),
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    ∀ Φ : (ofObj p).FullSubcategory,
      Function.Surjective
        (Φ.obj.presheafFiber.map (Sieve.shrinkFunctor.{w'} S).ι) := by
  intro Φ
  rcases Φ with ⟨q, hq⟩
  -- Reindex the owner theorem's point back to one of the original `p i`.
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  exact point_shrinkFunctor_presheafFiber_surjective_of_ulift_lifts
    (q := p i) (S := S) (hS i)

/-- Helper for Lemma 7.38.3: the `ULift`-based lift package reindexes from the original family
index type to bijectivity of the universe-lifted sieve inclusion on the owner full subcategory. -/
private lemma uliftFunctorInclusion_bijective_fullSubcategory_of_ulift_lifts
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J) {U : C} (S : Sieve U)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj U)),
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    ∀ Φ : (ofObj p).FullSubcategory,
      Function.Bijective
        (Φ.obj.presheafFiber.map (Sieve.uliftFunctorInclusion.{max u v w'} S)) := by
  intro Φ
  rcases Φ with ⟨q, hq⟩
  -- Reindex the owner theorem's point back to one of the original `p i`.
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  -- Remove the `ULift` wrapper from the given witness package, then apply the pointwise
  -- bijectivity lemma for `S.uliftFunctorInclusion`.
  refine point_uliftFunctorInclusion_presheafFiber_bijective_of_lifts
    (q := p i) (S := S) ?_
  exact (point_cover_lift_ulift_iff (q := p i) (U := U) S).1 (hS i)

/-- Helper for Lemma 7.38.3: pointwise equality of germs along a family of points makes the
equalizer sieve act surjectively on each corresponding point fiber of `shrinkYoneda`. -/
private lemma pointwise_germ_eq_shrinkFunctor_surjective
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ i,
      Function.Surjective
        ((p i).presheafFiber.map
          (Sieve.shrinkFunctor.{w'} (Presheaf.equalizerSieve (F := ℱ.obj) s s')).ι) := by
  intro i
  -- Every `x ∈ u_i(U)` lifts through the equalizer sieve, so the induced map on the point fiber
  -- of `shrinkYoneda` is surjective.
  refine point_shrinkFunctor_presheafFiber_surjective_of_lifts
    (q := p i) (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') ?_
  intro x
  obtain ⟨Y, g, hg, y, hy⟩ :=
    pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x)
  exact ⟨Y, g, hg, y, hy⟩

/-- Helper for Lemma 7.38.3: reindex the pointwise surjectivity package from `i : ι` to the
owner theorem's full subcategory `(ofObj p).FullSubcategory`. -/
private lemma pointwise_germ_eq_shrinkFunctor_surjective_fullSubcategory
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ Φ : (ofObj p).FullSubcategory,
      Function.Surjective
        (Φ.obj.presheafFiber.map
          (Sieve.shrinkFunctor.{w'} (Presheaf.equalizerSieve (F := ℱ.obj) s s')).ι) := by
  intro Φ
  rcases Φ with ⟨q, hq⟩
  -- Reindex the owner theorem's object `q` back to one of the original points `p i`.
  rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
  exact pointwise_germ_eq_shrinkFunctor_surjective (p := p) U s s' hss i

/-- Helper for Lemma 7.38.3: pointwise equality of germs makes the equalizer sieve act
bijectively on each corresponding point fiber of `shrinkYoneda`. -/
private lemma pointwise_germ_eq_shrinkFunctor_bijective
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ i,
      Function.Bijective
        ((p i).presheafFiber.map
          (Sieve.shrinkFunctor.{w'} (Presheaf.equalizerSieve (F := ℱ.obj) s s')).ι) := by
  intro i
  -- The equalizer-lift witnesses already built above give the full bijectivity package.
  refine point_shrinkFunctor_presheafFiber_bijective_of_lifts
    (q := p i) (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') ?_
  intro x
  exact pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x)

/-- Helper for Lemma 7.38.3: stalkwise isomorphisms on a small set-valued sheaf morphism stay
stalkwise isomorphisms after composing with the relevant `ULift` functor. -/
private lemma point_sheafFiber_ulift_map_isIso
    [LocallySmall.{w'} C]
    (q : Point.{w'} J) {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢)
    (hφ : IsIso (q.sheafFiber.map φ)) :
    IsIso
      (q.sheafFiber.map
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).map φ)) := by
  let Fup :
      Sheaf J (Type w') ⥤ Sheaf J (Type (max u v w')) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u v, w'} :
        Type w' ⥤ Type (max u v w'))
  let ψ : q.sheafFiber.obj ℱ ⟶ q.sheafFiber.obj 𝒢 := q.sheafFiber.map φ
  let ψup : q.sheafFiber.obj (Fup.obj ℱ) ⟶ q.sheafFiber.obj (Fup.obj 𝒢) :=
    q.sheafFiber.map (Fup.map φ)
  have hψ : Function.Bijective ψ := (isIso_iff_bijective ψ).1 hφ
  refine (isIso_iff_bijective ψup).2 ?_
  constructor
  · intro a₁ a₂ hEq
    -- Represent both source stalk elements on a common stage of the filtered colimit.
    obtain ⟨X, x, z₁, z₂, rfl, rfl⟩ :=
      point_presheafFiber_jointly_surjective₂_of_type
        (q := q) (P := (Fup.obj ℱ).obj) a₁ a₂
    rcases z₁ with ⟨s₁⟩
    rcases z₂ with ⟨s₂⟩
    have hmap₁ :
        ψup (q.toPresheafFiber X x (Fup.obj ℱ).obj (ULift.up s₁)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₁)) := by
      -- Naturality computes the lifted stalk map on a chosen representative.
      simpa [Fup, ψup, CategoryTheory.uliftFunctor_map] using
        congrFun (q.toPresheafFiber_naturality (Fup.map φ).hom X x) (ULift.up s₁)
    have hmap₂ :
        ψup (q.toPresheafFiber X x (Fup.obj ℱ).obj (ULift.up s₂)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₂)) := by
      -- The same computation holds for the second representative.
      simpa [Fup, ψup, CategoryTheory.uliftFunctor_map] using
        congrFun (q.toPresheafFiber_naturality (Fup.map φ).hom X x) (ULift.up s₂)
    have hEqUp :
        q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₁)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op X)) s₂)) := by
      exact hmap₁.symm.trans (hEq.trans hmap₂)
    have hEqSmallMapped :
        q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₁) =
          q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₂) :=
      (point_ulift_presheafFiber_eq_iff (q := q) X x _ _).1 hEqUp
    have hsmall₁ :
        ψ (q.toPresheafFiber X x ℱ.obj s₁) =
          q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₁) := by
      -- Compare the original stalk map with the germ of the image section.
      simpa [ψ] using congrFun (q.toPresheafFiber_naturality φ.hom X x) s₁
    have hsmall₂ :
        ψ (q.toPresheafFiber X x ℱ.obj s₂) =
          q.toPresheafFiber X x 𝒢.obj ((φ.hom.app (op X)) s₂) := by
      -- The same comparison for the second section.
      simpa [ψ] using congrFun (q.toPresheafFiber_naturality φ.hom X x) s₂
    have hEqSmall :
        q.toPresheafFiber X x ℱ.obj s₁ =
          q.toPresheafFiber X x ℱ.obj s₂ := by
      -- Injectivity of the original stalk map identifies the two source germs.
      exact hψ.injective (hsmall₁.trans (hEqSmallMapped.trans hsmall₂.symm))
    exact (point_ulift_presheafFiber_eq_iff (q := q) X x s₁ s₂).2 hEqSmall
  · intro b
    -- Represent the target stalk element by an actual section of the lifted target sheaf.
    obtain ⟨X, x, z, rfl⟩ :=
      point_presheafFiber_jointly_surjective_of_type
        (q := q) (P := (Fup.obj 𝒢).obj) b
    rcases z with ⟨t⟩
    obtain ⟨a, ha⟩ := hψ.surjective (q.toPresheafFiber X x 𝒢.obj t)
    obtain ⟨Y, y, s, hs⟩ :=
      point_presheafFiber_jointly_surjective_of_type (q := q) (P := ℱ.obj) a
    refine ⟨q.toPresheafFiber Y y (Fup.obj ℱ).obj (ULift.up s), ?_⟩
    have hsmall :
        q.toPresheafFiber Y y 𝒢.obj ((φ.hom.app (op Y)) s) =
          q.toPresheafFiber X x 𝒢.obj t := by
      have hmapSmall :
          ψ a = q.toPresheafFiber Y y 𝒢.obj ((φ.hom.app (op Y)) s) := by
        -- Rewrite the chosen preimage `a` by its representing germ and compute the stalk map.
        rw [← hs]
        simpa [ψ] using congrFun (q.toPresheafFiber_naturality φ.hom Y y) s
      exact hmapSmall.symm.trans ha
    have hlarge :
        q.toPresheafFiber Y y (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op Y)) s)) =
          q.toPresheafFiber X x (Fup.obj 𝒢).obj (ULift.up t) := by
      obtain ⟨Z, f, g, hfg⟩ :=
        (Limits.Types.FilteredColimit.isColimit_eq_iff
          (ht := q.isColimitPresheafFiberCocone 𝒢.obj)
          (i := op ⟨Y, y⟩) (j := op ⟨X, x⟩)
          (xi := (φ.hom.app (op Y)) s) (xj := t)).1 hsmall
      exact
        (Limits.Types.FilteredColimit.isColimit_eq_iff
          (ht := q.isColimitPresheafFiberCocone (Fup.obj 𝒢).obj)
          (i := op ⟨Y, y⟩) (j := op ⟨X, x⟩)
          (xi := ULift.up ((φ.hom.app (op Y)) s)) (xj := ULift.up t)).2
          ⟨Z, f, g, by
            simpa [Fup, CategoryTheory.uliftFunctor_map] using hfg⟩
    have hmap :
        ψup (q.toPresheafFiber Y y (Fup.obj ℱ).obj (ULift.up s)) =
          q.toPresheafFiber Y y (Fup.obj 𝒢).obj
            (ULift.up ((φ.hom.app (op Y)) s)) := by
      -- Naturality computes the lifted stalk map on the chosen preimage representative.
      simpa [Fup, ψup, CategoryTheory.uliftFunctor_map] using
        congrFun (q.toPresheafFiber_naturality (Fup.map φ).hom Y y) (ULift.up s)
    exact hmap.trans hlarge

/-- Helper for Lemma 7.38.3: pointwise equality of germs makes the lifted equalizer-sieve
inclusion bijective on every point fiber. -/
private lemma pointwise_germ_eq_uliftFunctorInclusion_presheafFiber_bijective
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ i,
      Function.Bijective
        ((p i).presheafFiber.map
          (Sieve.uliftFunctorInclusion.{max u v w'}
            (Presheaf.equalizerSieve (F := ℱ.obj) s s'))) := by
  intro i
  -- Each point-fiber generator already lifts through the equalizer sieve, so the induced map is
  -- bijective by the earlier point-fiber lifting package.
  refine point_uliftFunctorInclusion_presheafFiber_bijective_of_lifts
    (q := p i) (S := Presheaf.equalizerSieve (F := ℱ.obj) s s') ?_
  intro x
  exact pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x)

/-- Helper for Lemma 7.38.3: bijectivity on a point fiber upgrades to an isomorphism on the
corresponding stalk map after sheafification. -/
private lemma point_sheafify_map_isIso_of_presheafFiber_bijective
    [HasWeakSheafify J (Type (max u v w'))]
    (q : Point.{w'} J) {P Q : Cᵒᵖ ⥤ Type (max u v w')} (η : P ⟶ Q)
    (hη : Function.Bijective (q.presheafFiber.map η)) :
    IsIso (q.sheafFiber.map ((presheafToSheaf J (Type (max u v w'))).map η)) := by
  -- Conjugate the stalk map across the canonical identification between presheaf fibers and the
  -- fibers of the sheafification.
  let _ : IsIso (q.presheafFiber.map η) := (isIso_iff_bijective _).2 hη
  exact
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (q.presheafToSheafCompSheafFiberIso (Type (max u v w')))).app
          (Arrow.mk η))).2
      (inferInstanceAs (IsIso (q.presheafFiber.map η)))

/-- Helper for Lemma 7.38.3: the concrete `Plus` map is locally injective in the ambient large
type universe. -/
private theorem toPlus_isLocallyInjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallyInjective J (J.toPlus P) := by
  -- The concrete `Plus` quotient identifies two representatives only after passing to a common
  -- covering sieve, so that covering sieve witnesses local injectivity directly.
  letI : Presheaf.IsLocallyInjective J (J.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      open GrothendieckTopology.Plus in
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, h₁, h₂, eq⟩ := h
      exact J.superset_covering (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.38.3: the concrete `Plus` map is locally surjective in the ambient large
type universe. -/
private theorem toPlus_isLocallySurjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallySurjective J (J.toPlus P) := by
  -- Every `Plus` section is represented on some covering sieve, and that representative gives
  -- the desired local preimage.
  letI : Presheaf.IsLocallySurjective J (J.toPlus P) := {
    imageSieve_mem := by
      intro X x
      open GrothendieckTopology.Plus in
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine J.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. } }
  infer_instance

/-- Helper for Lemma 7.38.3: the concrete `plus-plus` model of sheafification is locally
injective in the ambient large type universe. -/
private theorem concrete_toSheafify_isLocallyInjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallyInjective J (J.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective J (J.toPlus P) :=
    toPlus_isLocallyInjective_type (J := J) P
  letI : Presheaf.IsLocallyInjective J (J.toPlus (J.plusObj P)) :=
    toPlus_isLocallyInjective_type (J := J) (J.plusObj P)
  -- The concrete sheafification unit is the composite of the two concrete `Plus` maps.
  change Presheaf.IsLocallyInjective J (J.toPlus P ≫ J.plusMap (J.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.38.3: the concrete `plus-plus` model of sheafification is locally
surjective in the ambient large type universe. -/
private theorem concrete_toSheafify_isLocallySurjective_type
    [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ (Type (max u v w'))]
    [∀ P' : Cᵒᵖ ⥤ Type (max u v w'), ∀ X : C, ∀ S : J.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type (max u v w')))]
    (P : Cᵒᵖ ⥤ Type (max u v w')) :
    Presheaf.IsLocallySurjective J (J.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective J (J.toPlus P) :=
    toPlus_isLocallySurjective_type (J := J) P
  letI : Presheaf.IsLocallySurjective J (J.toPlus (J.plusObj P)) :=
    toPlus_isLocallySurjective_type (J := J) (J.plusObj P)
  -- The same concrete factorization reduces surjectivity to the two `Plus` steps.
  change Presheaf.IsLocallySurjective J (J.toPlus P ≫ J.plusMap (J.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.38.3: in the ambient large `Type` universe used for the sheafified
representable, `J.W` still agrees with local bijectivity. -/
private theorem large_type_WEqualsLocallyBijective
    [HasWeakSheafify J (Type (max u v w'))] :
    J.WEqualsLocallyBijective (Type (max u v w')) := by
  let T := Type (max u v w')
  let _ :
      ∀ P : Cᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective J (J.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallyInjective_type (J := J) (P := P ⋙ forget T)
    -- Rewrite the abstract large-universe unit as the concrete one followed by comparison
    -- isomorphisms that preserve local injectivity.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify J T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso J (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Cᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective J (J.toSheafify (P ⋙ forget T)) :=
      concrete_toSheafify_isLocallySurjective_type (J := J) (P := P ⋙ forget T)
    -- The same large-universe comparison transports local surjectivity to the abstract unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify J T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso J (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' (J := J) (A := T)

/-- Helper for Lemma 7.38.3: once the lifted sieve inclusion lies in `J.W`, local surjectivity at
the lifted identity section shows that the original sieve is covering. -/
private lemma covering_of_W_uliftFunctorInclusion
    [HasWeakSheafify J (Type (max u v w'))]
    {U : C} (S : Sieve U)
    (hW :
      J.W
        (Sieve.uliftFunctorInclusion.{max u v w'} S :
          Sieve.uliftFunctor.{max u v w'} S ⟶
            CategoryTheory.uliftYoneda.obj.{max u v w'} U)) :
    S ∈ J U := by
  let _ : J.WEqualsLocallyBijective (Type (max u v w')) :=
    large_type_WEqualsLocallyBijective (J := J)
  let f :
      Sieve.uliftFunctor.{max u v w'} S ⟶
        CategoryTheory.uliftYoneda.obj.{max u v w'} U :=
    Sieve.uliftFunctorInclusion.{max u v w'} S
  have hSurj : Presheaf.IsLocallySurjective J f := hW.isLocallySurjective
  let s : (CategoryTheory.uliftYoneda.obj.{max u v w'} U).obj (op U) := ULift.up (𝟙 U)
  -- Evaluate local surjectivity on the lifted identity section and identify its image sieve.
  have hmem : Presheaf.imageSieve f s ∈ J U := hSurj.imageSieve_mem s
  rw [imageSieve_uliftFunctorInclusion_eq_pullback (S := S) (𝟙 U), Sieve.pullback_id] at hmem
  exact hmem

/-- Helper for Lemma 7.38.3: if every lifted point-fiber element lifts through a sieve, that
forces the sieve to be covering by the conservative-family `W`-criterion. -/
private lemma covering_of_ulift_family_lifts_core
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj X)),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    S ∈ J X := by
  -- TODO: the remaining source-faithful step is to turn the reindexed point-fiber bijectivity
  -- package into a covering proof for `S`. The small `shrinkFunctor` route still needs a
  -- canonical `HasSheafify J (Type w')` / `J.WEqualsLocallyBijective (Type w')` bridge, while
  -- the large `hp.W_iff` route is blocked because the owner theorem only accepts concrete
  -- categories whose carrier lives in the point universe `w'`, so it cannot consume
  -- `Type (max u v w')` directly.
  sorry

/-- Helper for Lemma 7.38.3: pointwise equality of germs along a conservative family makes the
equalizer sieve of the two sections covering. -/
private lemma covering_equalizerSieve_of_pointwise_germ_eq
    [LocallySmall.{w'} C]
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U))
    (hss :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj s =
          (p i).toPresheafFiber U x ℱ.obj s') :
    Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U := by
  let S : Sieve U := Presheaf.equalizerSieve (F := ℱ.obj) s s'
  -- Keep the source proof's controlling object fixed: prove the equalizer sieve is covering from
  -- the pointwise germ equalities and the conservative family.
  exact covering_of_ulift_family_lifts_core (p := p) hp (S := S) <| by
    intro i x
    obtain ⟨Y, g, hg, y, hy⟩ :=
      pointwise_germ_eq_gives_equalizer_lift (q := p i) U s s' (hx := hss i x.down)
    refine ⟨Y, g, hg, ULift.up.{max u v, w'} y, ?_⟩
    cases x
    simpa using
      congrArg (ULift.up.{max u v, w'} : (p i).fiber.obj U → ULift.{max u v, w'} ((p i).fiber.obj U)) hy

/-- Helper for Lemma 7.38.3: a covering equalizer sieve forces two sections of a sheaf to agree. -/
private lemma sections_eq_of_covering_equalizerSieve
    {ℱ : Sheaf J (Type (max u v w'))} (U : C) (s s' : ℱ.obj.obj (op U))
    (hcover : Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U) :
    s = s' := by
  -- Use separatedness of the sheaf on the covering equalizer sieve.
  exact (((isSheaf_iff_isSheaf_of_type J ℱ.obj).1 ℱ.property).isSeparated _ hcover).ext
    (fun _ _ hf ↦ hf)

/-- Helper for Lemma 7.38.3: pointwise equality of germs along the family identifies the induced
stalk maps on `h_U^#` at every point of the family. -/
private lemma sheafifiedRepresentable_stalkwise_eq_of_pointwise_germ_eq
    {ι : Type w} (p : ι → Point.{w'} J)
    [LocallySmall.{w'} C]
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
          (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U β)) :
    ∀ i, (p i).sheafFiber.map α = (p i).sheafFiber.map β := by
  intro i
  -- Apply the single-point stalk extensionality lemma pointwise across the family.
  exact sheafifiedRepresentable_stalk_map_ext_of_pointwise_germ_eq
    (q := p i) U α β (hαβ i)

/-- Helper for Lemma 7.38.3: after applying `ULift` to the fibers of a point, covering witnesses
for a sieve are still produced by the original point axiom. -/
private lemma ulift_cover_lift_of_point
    (q : Point.{w'} J) {X : C} (S : Sieve X) (hS : S ∈ J X)
    (x : ULift.{max u v, w'} (q.fiber.obj X)) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : S f) (y : ULift.{max u v, w'} (q.fiber.obj Y)),
      ULift.up (q.fiber.map f y.down) = x := by
  -- This is exactly the forward direction of the previously established `ULift` cover-lift
  -- equivalence, applied to the original point axiom.
  exact (point_cover_lift_ulift_iff (q := q) (U := X) S).2
    (q.jointly_surjective S hS) x

/-- Helper for Lemma 7.38.3: the original and `ULift`-enlarged fibers of a point have equivalent
categories of elements. -/
private noncomputable def ulift_point_elements_equivalence
    (q : Point.{w'} J) :
    q.fiber.Elements ≌ (uliftPointFiberFunctor q).Elements where
  functor :=
    { obj := fun x ↦ ⟨x.1, ULift.up x.2⟩
      map := fun {X Y} f ↦
        CategoryOfElements.homMk _ _ f.1 (by
          -- The forward map keeps the base morphism and lifts only the element component.
          rcases X with ⟨X, x⟩
          rcases Y with ⟨Y, y⟩
          rcases f with ⟨f, hf⟩
          simpa [uliftPointFiberFunctor] using
            congrArg (ULift.up : q.fiber.obj Y → ULift.{max u v, w'} (q.fiber.obj Y)) hf) }
  inverse :=
    { obj := fun x ↦ ⟨x.1, x.2.down⟩
      map := fun {X Y} f ↦
        CategoryOfElements.homMk _ _ f.1 (by
          -- The inverse map keeps the base morphism and removes the `ULift` wrapper.
          rcases X with ⟨X, x⟩
          rcases Y with ⟨Y, y⟩
          rcases f with ⟨f, hf⟩
          simpa [uliftPointFiberFunctor] using
            congrArg (ULift.down : ULift.{max u v, w'} (q.fiber.obj Y) → q.fiber.obj Y) hf) }
  unitIso :=
    NatIso.ofComponents
      (fun x ↦
        CategoryOfElements.isoMk _ _ (Iso.refl _) (by
          -- Route correction: use the explicit `ULift` fiber isomorphism rather than reducing
          -- sigma objects in `Functor.Elements` by hand.
          simp))
      (fun f ↦ by
        -- Morphisms in the category of elements are determined by their base arrow.
        apply CategoryOfElements.ext
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun x ↦
        CategoryOfElements.isoMk _ _ (Iso.refl _) (by
          -- The `ULift` wrapper is removed objectwise, so the element component is unchanged.
          simpa [uliftPointFiberFunctor] using ULift.up_down x.2))
      (fun f ↦ by
        -- Again, the objectwise `ULift` comparison leaves the underlying arrow unchanged.
        apply CategoryOfElements.ext
        simp)
  functor_unitIso_comp x := by
    -- The triangle identity is objectwise reflexive on the underlying base arrow.
    apply CategoryOfElements.ext
    simp

/-- Helper for Lemma 7.38.3: the enlarged point inherits cofilteredness from the original point by
transporting across the explicit equivalence of element categories. -/
private lemma ulift_point_isCofiltered
    (q : Point.{w'} J) :
    IsCofiltered (uliftPointFiberFunctor q).Elements := by
  -- Transfer the global cofilteredness invariant across the explicit `ULift` equivalence.
  exact IsCofiltered.of_equivalence (ulift_point_elements_equivalence (q := q))

/-- Helper for Lemma 7.38.3: the enlarged point still has an initially small category of elements,
again via the explicit `ULift` equivalence. -/
private lemma ulift_point_initiallySmall
    (q : Point.{w'} J) :
    InitiallySmall.{max u v w'} (uliftPointFiberFunctor q).Elements := by
  -- Transfer the existing small indexing category for `q` along the explicit equivalence functor.
  letI : EssentiallySmall.{max u v w'} q.fiber.Elements :=
    CategoryTheory.essentiallySmallSelf (C := q.fiber.Elements)
  letI : InitiallySmall.{max u v w'} q.fiber.Elements :=
    CategoryTheory.initiallySmall_of_essentiallySmall (J := q.fiber.Elements)
  exact initiallySmall_of_initial_of_initiallySmall
    (ulift_point_elements_equivalence (q := q)).functor

/-- Helper for Lemma 7.38.3: the enlarged point satisfies the covering-lift axiom because the
original point does and the `ULift` bookkeeping is explicit. -/
private lemma ulift_point_jointly_surjective
    (q : Point.{w'} J) {X : C} (S : Sieve X) (hS : S ∈ J X)
    (x : (uliftPointFiberFunctor q).obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : S f) (y : (uliftPointFiberFunctor q).obj Y),
      (uliftPointFiberFunctor q).map f y = x := by
  -- Reuse the original point axiom and then rewrite the transported fiber map into its canonical
  -- `ULift` form.
  obtain ⟨Y, f, hf, y, hy⟩ := ulift_cover_lift_of_point (q := q) S hS x
  refine ⟨Y, f, hf, y, ?_⟩
  simpa [uliftTypeFunctor, CategoryTheory.uliftFunctor_map] using hy

/-- Helper for Lemma 7.38.3: enlarge a point to the ambient universe by `ULift` on all fibers. -/
private noncomputable def ulift_point
    (q : Point.{w'} J) : Point.{max u v w'} J :=
  { fiber := uliftPointFiberFunctor q
    isCofiltered := ulift_point_isCofiltered (q := q)
    initiallySmall := ulift_point_initiallySmall (q := q)
    jointly_surjective := ulift_point_jointly_surjective (q := q) }

/-- Helper for Lemma 7.38.3: the family-wise `ULift` lifting package immediately descends to the
ordinary point fibers. -/
private lemma family_point_cover_lift_of_ulift
    {ι : Type w} (p : ι → Point.{w'} J) {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj X)),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    ∀ i (x : (p i).fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : (p i).fiber.obj Y),
        (p i).fiber.map g y = x := by
  intro i
  -- Remove the auxiliary `ULift` wrapper pointwise, using the single-point equivalence already
  -- proved earlier in the file.
  exact (point_cover_lift_ulift_iff (q := p i) (U := X) S).1 (hS i)

/-- Helper for Lemma 7.38.3: lifted point-fiber witnesses for an arbitrary sieve already reflect
covering because the original family reflects coverings for sieves of arrows. -/
private lemma covering_of_ulift_family_lifts
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] {X : C} (S : Sieve X)
    (hS :
      ∀ i (x : ULift.{max u v, w'} ((p i).fiber.obj X)),
        ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : ULift.{max u v, w'} ((p i).fiber.obj Y)),
          ULift.up ((p i).fiber.map g y.down) = x) :
    S ∈ J X := by
  exact covering_of_ulift_family_lifts_core (p := p) hp (S := S) hS

/-- Helper for Lemma 7.38.3: if the original family is conservative, then the `ULift`-enlarged
family is conservative in the ambient point universe. -/
private lemma ulift_point_family_conservative
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] :
    (ofObj (fun i => ulift_point (p i))).IsConservativeFamilyOfPoints := by
  -- Route correction: use the owner constructor `mk'` directly and reflect covering of an
  -- arbitrary sieve via the explicit `ofArrows` reduction proved just above.
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' ?_
  intro X S hS
  exact covering_of_ulift_family_lifts (p := p) hp S (fun i x ↦
    hS ⟨ulift_point (p i), ofObj_apply (fun i ↦ ulift_point (p i)) i⟩ x)

/-- Helper for Lemma 7.38.3: the original point and its `ULift` enlargement induce canonically
isomorphic fiber functors on large type-valued presheaves. -/
private lemma ulift_point_presheafFiberHom_compatible
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : (ulift_point q).fiber.obj X),
      P.map f.op ≫ q.toPresheafFiber X x.down P =
        q.toPresheafFiber Y ((ulift_point q).fiber.map f x).down P := by
  intro X Y f x
  -- Remove the lifted point fiber back to the original point fiber before using `toPresheafFiber_w`.
  simpa [ulift_point, uliftPointFiberFunctor] using
    (q.toPresheafFiber_w (P := P) f x.down)

/-- Helper for Lemma 7.38.3: the forward comparison map on presheaf fibers removes the `ULift`
wrapper from point-fiber generators. -/
private noncomputable def ulift_point_presheafFiberHom
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    (ulift_point q).presheafFiber.obj P ⟶ q.presheafFiber.obj P :=
  (ulift_point q).presheafFiberDesc
    (fun X x ↦ q.toPresheafFiber X x.down P)
    (ulift_point_presheafFiberHom_compatible (q := q) P)

/-- Helper for Lemma 7.38.3: the forward comparison map evaluates on a lifted generator by simply
forgetting `ULift`. -/
private lemma ulift_point_toPresheafFiber_presheafFiberHom
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) (X : C)
    (x : (ulift_point q).fiber.obj X) :
    (ulift_point q).toPresheafFiber X x P ≫ ulift_point_presheafFiberHom (q := q) P =
      q.toPresheafFiber X x.down P := by
  -- Evaluate the descent map on the canonical colimit generator for the lifted point.
  simpa [ulift_point_presheafFiberHom] using
    ((ulift_point q).toPresheafFiber_presheafFiberDesc
      (fun X x ↦ q.toPresheafFiber X x.down P)
      (ulift_point_presheafFiberHom_compatible (q := q) P) X x)

/-- Helper for Lemma 7.38.3: the reverse comparison from the original presheaf fiber to the
lifted one is compatible with pullback along arrows. -/
private lemma ulift_point_presheafFiberInv_compatible
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : q.fiber.obj X),
      P.map f.op ≫ (ulift_point q).toPresheafFiber X (ULift.up x) P =
        (ulift_point q).toPresheafFiber Y (ULift.up (q.fiber.map f x)) P := by
  intro X Y f x
  -- The lifted point applies `ULift.up` after the original fiber map, so the compatibility is
  -- exactly `toPresheafFiber_w` for `ulift_point q`.
  simpa [ulift_point, uliftPointFiberFunctor] using
    ((ulift_point q).toPresheafFiber_w (P := P) f (ULift.up x))

/-- Helper for Lemma 7.38.3: the reverse comparison map on presheaf fibers adds the `ULift`
wrapper back to point-fiber generators. -/
private noncomputable def ulift_point_presheafFiberInv
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    q.presheafFiber.obj P ⟶ (ulift_point q).presheafFiber.obj P :=
  q.presheafFiberDesc
    (fun X x ↦ (ulift_point q).toPresheafFiber X (ULift.up x) P)
    (ulift_point_presheafFiberInv_compatible (q := q) P)

/-- Helper for Lemma 7.38.3: the reverse comparison map evaluates on an original generator by
reintroducing `ULift`. -/
private lemma point_toPresheafFiber_presheafFiberInv
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) (X : C) (x : q.fiber.obj X) :
    q.toPresheafFiber X x P ≫ ulift_point_presheafFiberInv (q := q) P =
      (ulift_point q).toPresheafFiber X (ULift.up x) P := by
  -- Evaluate the descent map on the canonical colimit generator for the original point.
  simpa [ulift_point_presheafFiberInv] using
    (q.toPresheafFiber_presheafFiberDesc
      (fun X x ↦ (ulift_point q).toPresheafFiber X (ULift.up x) P)
      (ulift_point_presheafFiberInv_compatible (q := q) P) X x)

/-- Helper for Lemma 7.38.3: the forward and reverse comparison maps on a presheaf fiber are
inverse after testing on lifted generators. -/
private lemma ulift_point_presheafFiberHom_inv
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ulift_point_presheafFiberHom (q := q) P ≫ ulift_point_presheafFiberInv (q := q) P = 𝟙 _ := by
  -- The comparison is determined on colimit generators, where `ULift.up` then `ULift.down`
  -- returns the original lifted element.
  apply (ulift_point q).presheafFiber_hom_ext
  intro X x
  repeat rw [← Category.assoc]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  rw [point_toPresheafFiber_presheafFiberInv]
  cases x
  rfl

/-- Helper for Lemma 7.38.3: the reverse and forward comparison maps on a presheaf fiber are
inverse after testing on original generators. -/
private lemma ulift_point_presheafFiberInv_hom
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    ulift_point_presheafFiberInv (q := q) P ≫ ulift_point_presheafFiberHom (q := q) P = 𝟙 _ := by
  -- The same generator test removes `ULift` immediately after it was introduced.
  apply q.presheafFiber_hom_ext
  intro X x
  repeat rw [← Category.assoc]
  rw [point_toPresheafFiber_presheafFiberInv]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  rfl

/-- Helper for Lemma 7.38.3: the componentwise presheaf-fiber comparison is natural in the
presheaf argument. -/
private lemma ulift_point_presheafFiberObjIso_hom_naturality
    (q : Point.{w'} J) {P Q : Cᵒᵖ ⥤ Type (max u v w')} (f : P ⟶ Q) :
    (ulift_point q).presheafFiber.map f ≫
        ulift_point_presheafFiberHom (q := q) Q =
      ulift_point_presheafFiberHom (q := q) P ≫ q.presheafFiber.map f := by
  -- Compare both composites on lifted generators and reduce to naturality of the original point
  -- fiber maps.
  apply (ulift_point q).presheafFiber_hom_ext
  intro X x
  rw [← Category.assoc, ← Category.assoc]
  rw [(ulift_point q).toPresheafFiber_naturality f X x]
  rw [Category.assoc]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  rw [ulift_point_toPresheafFiber_presheafFiberHom]
  simpa [ulift_point, uliftPointFiberFunctor] using
    (q.toPresheafFiber_naturality f X x.down).symm

/-- Helper for Lemma 7.38.3: for a fixed presheaf, the original point and its `ULift`
enlargement have canonically isomorphic fibers. -/
private noncomputable def ulift_point_presheafFiberObjIso
    (q : Point.{w'} J) (P : Cᵒᵖ ⥤ Type (max u v w')) :
    (ulift_point q).presheafFiber.obj P ≅ q.presheafFiber.obj P :=
  { hom := ulift_point_presheafFiberHom (q := q) P
    inv := ulift_point_presheafFiberInv (q := q) P
    hom_inv_id := ulift_point_presheafFiberHom_inv (q := q) P
    inv_hom_id := ulift_point_presheafFiberInv_hom (q := q) P }

/-- Helper for Lemma 7.38.3: the objectwise comparison isomorphisms assemble naturally into a
presheaf-fiber isomorphism. -/
private lemma ulift_point_presheafFiberObjIso_naturality
    (q : Point.{w'} J) {P Q : Cᵒᵖ ⥤ Type (max u v w')} (f : P ⟶ Q) :
    (ulift_point q).presheafFiber.map f ≫
        (ulift_point_presheafFiberObjIso (q := q) Q).hom =
      (ulift_point_presheafFiberObjIso (q := q) P).hom ≫ q.presheafFiber.map f := by
  -- This is the generatorwise naturality already proved for the underlying forward comparison.
  simpa [ulift_point_presheafFiberObjIso] using
    (ulift_point_presheafFiberObjIso_hom_naturality (q := q) f)

/-- Helper for Lemma 7.38.3: the original point and its `ULift` enlargement induce canonically
isomorphic fiber functors on large type-valued presheaves. -/
private noncomputable def ulift_point_presheafFiberIso
    (q : Point.{w'} J) :
    ((ulift_point q).presheafFiber :
      (Cᵒᵖ ⥤ Type (max u v w')) ⥤ Type (max u v w')) ≅ q.presheafFiber :=
  NatIso.ofComponents
    (ulift_point_presheafFiberObjIso (q := q))
    (ulift_point_presheafFiberObjIso_naturality (q := q))

/-- Helper for Lemma 7.38.3: equality of sheaf-fiber maps for the `ULift`-enlarged point should
be equivalent to equality for the original point. -/
private lemma ulift_point_sheafFiber_map_eq_iff
    (q : Point.{w'} J)
    {ℱ 𝒢 : Sheaf J (Type (max u v w'))} {φ ψ : ℱ ⟶ 𝒢} :
    (ulift_point q).sheafFiber.map φ = (ulift_point q).sheafFiber.map ψ ↔
      q.sheafFiber.map φ = q.sheafFiber.map ψ := by
  let e : (ulift_point q).sheafFiber ≅ q.sheafFiber :=
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type (max u v w')))
      (ulift_point_presheafFiberIso (q := q))
  constructor
  · intro h
    ext z
    obtain ⟨z', rfl⟩ := ((e.app ℱ).toEquiv).surjective z
    have hz :
        e.hom.app 𝒢 ((ulift_point q).sheafFiber.map φ z') =
          e.hom.app 𝒢 ((ulift_point q).sheafFiber.map ψ z') := by
      simpa using congrArg (e.hom.app 𝒢) (congrFun h z')
    -- Transport equality across the comparison isomorphism by naturality of the comparison map.
    exact (NatTrans.naturality_apply e.hom φ z').symm.trans <|
      hz.trans (NatTrans.naturality_apply e.hom ψ z')
  · intro h
    ext z
    obtain ⟨z', rfl⟩ := ((e.symm.app ℱ).toEquiv).surjective z
    have hz :
        e.inv.app 𝒢 (q.sheafFiber.map φ z') =
          e.inv.app 𝒢 (q.sheafFiber.map ψ z') := by
      simpa using congrArg (e.inv.app 𝒢) (congrFun h z')
    -- The inverse comparison map transports equality in the reverse direction.
    exact (NatTrans.naturality_apply e.inv φ z').symm.trans <|
      hz.trans (NatTrans.naturality_apply e.inv ψ z')

/-- Helper for Lemma 7.38.3: the conservative family should be jointly faithful on large
type-valued sheaves once the small-to-large universe bridge is supplied. -/
private lemma sheaf_hom_ext_of_stalkwise_large_type
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C]
    {ℱ 𝒢 : Sheaf J (Type (max u v w'))} {φ ψ : ℱ ⟶ 𝒢}
    (hφ : ∀ i, (p i).sheafFiber.map φ = (p i).sheafFiber.map ψ) :
    φ = ψ := by
  letI : LocallySmall.{max u v w'} C := by infer_instance
  let p' : ι → Point.{max u v w'} J := fun i ↦ ulift_point (p i)
  have hp' : (ofObj p').IsConservativeFamilyOfPoints :=
    ulift_point_family_conservative (p := p) hp
  have hφ' : ∀ i, (p' i).sheafFiber.map φ = (p' i).sheafFiber.map ψ := by
    intro i
    -- Transport the original stalkwise equality to the lifted family through the comparison iso.
    exact (ulift_point_sheafFiber_map_eq_iff (q := p i)).2 (hφ i)
  -- Apply Lemma 7.38.2 to the lifted conservative family, which lives in the ambient universe.
  exact sheaf_hom_ext_of_stalkwise (p := p') hp' hφ'

/-- Helper for Lemma 7.38.3: distinct maps out of `h_U^#` are detected on the stalk of some
point in a conservative family. -/
private lemma stalkwise_ne_of_ne_sheafifiedRepresentable_hom
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ : α ≠ β) :
    ∃ i, (p i).sheafFiber.map α ≠ (p i).sheafFiber.map β := by
  classical
  by_contra hstalk
  push Not at hstalk
  -- If every stalk map were equal, joint faithfulness of the conservative family would force
  -- `α = β`.
  exact hαβ <|
    sheaf_hom_ext_of_stalkwise_large_type (p := p) hp hstalk

/-- Helper for Lemma 7.38.3: a stalk-level difference between two maps out of `h_U^#` comes from
some actual point-fiber element `x ∈ u_i(U)` separating the corresponding germs. -/
private lemma exists_point_separating_germ_of_ne_sheafifiedRepresentable_hom
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C]
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ : α ≠ β) :
    ∃ i, ∃ x : (p i).fiber.obj U,
      (p i).toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) ≠
        (p i).toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U β) := by
  classical
  obtain ⟨i, hi⟩ :=
    stalkwise_ne_of_ne_sheafifiedRepresentable_hom (p := p) hp U α β hαβ
  have hz :
      ∃ z,
        (p i).sheafFiber.map α z ≠
          (p i).sheafFiber.map β z := by
    by_contra hz
    push Not at hz
    exact hi <| by
      funext z
      exact hz z
  obtain ⟨z, hz⟩ := hz
  obtain ⟨x, rfl⟩ := point_sheafifiedRepresentable_stalkElem_surjective (q := p i) U z
  refine ⟨i, x, ?_⟩
  -- Unwind the chosen stalk generator back to the germ of the corresponding section at `x`.
  intro hEq
  exact hz <|
    (sheafifiedRepresentable_stalk_map_eq_iff (q := p i) U α β x).2 hEq

/-- Helper for Lemma 7.38.3: pointwise equality of germs forces equality of the two associated
morphisms out of `h_U^#`. -/
private lemma sheafifiedRepresentable_hom_eq_of_pointwise_germ_eq
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C]
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (α β :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{max u v w', u, v}
        J U ⟶ ℱ)
    (hαβ :
      ∀ i (x : (p i).fiber.obj U),
        (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
        (p i).toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U β)) :
    α = β := by
  let eU := J.uliftSheafifiedRepresentableHomEquiv ℱ U
  let s : ℱ.obj.obj (op U) := eU α
  let s' : ℱ.obj.obj (op U) := eU β
  -- Route correction: follow the source proof and make the equalizer sieve covering from
  -- pointwise germ equality, then use sheaf separatedness on that covering.
  have hcover :
      Presheaf.equalizerSieve (F := ℱ.obj) s s' ∈ J U := by
    simpa [s, s'] using
      covering_equalizerSieve_of_pointwise_germ_eq (p := p) hp U s s'
        (by simpa [s, s'] using hαβ)
  have hs : s = s' :=
    sections_eq_of_covering_equalizerSieve (ℱ := ℱ) U s s' hcover
  exact eU.injective <| by simpa [s, s'] using hs

/-- Helper for Lemma 7.38.3: the large separating-sections criterion implies conservativity for the
original small family of point stalk functors. -/
lemma small_conservative_of_large_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    [LocallySmall.{w'} C]
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ ⦃ℱ 𝒢 : Sheaf J (Type w')⦄ (φ : ℱ ⟶ 𝒢),
      (∀ i : ι, IsIso ((p i).sheafFiber.map φ)) → IsIso φ := by
  intro ℱ 𝒢 φ hφ
  let Fup : Sheaf J (Type w') ⥤ Sheaf J (Type (max u v w')) :=
    sheafCompose J
      (CategoryTheory.uliftFunctor.{max u v, w'} :
        Type w' ⥤ Type (max u v w'))
  have hFup :
      ∀ i : ι, IsIso ((p i).sheafFiber.map (Fup.map φ)) := by
    intro i
    let _ : IsIso ((p i).sheafFiber.map φ) := hφ i
    exact
      ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso
          ((p i).sheafFiberCompIso
            (CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w')))).app (Arrow.mk φ))).2
        (inferInstanceAs
          (IsIso
            ((CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w')).map ((p i).sheafFiber.map φ))))
  let _ : ∀ i : ι, IsIso ((p i).sheafFiber.map (Fup.map φ)) := hFup
  let _ : IsIso (Fup.map φ) :=
    (stalkFamily_jointlyReflectsIsomorphisms_of_separating_sections_large
      (p := p) hsep).isIso (Fup.map φ)
  -- Reflect the lifted isomorphism back through the `ULift`-whiskering functor on sheaves.
  exact isIso_of_reflects_iso φ Fup

/-- Lemma 7.38.3: a family of points of a site is conservative if and only if every pair of
distinct local sections of a set-valued sheaf is separated by their germs at some point of one of
the fibers `u_i(U)`.

The source statement is set-valued in the point universe. The previous theorem used
`Sheaf J (Type (max u v w'))`, which forced a non-source universe bridge from conservative
`Point.{w'} J` data to large-valued sheaves and made the proof circular. -/
theorem isConservativePointFamily_iff_exists_point_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J) [LocallySmall.{w'} C] :
    (ofObj p).IsConservativeFamilyOfPoints ↔
      ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s' := by
  constructor
  · intro hp
    -- Source route: compare the two maps `h_U^# ⟶ ℱ` corresponding to `s` and `s'`; if every
    -- point has equal germs, the equalizer sieve is covering by conservativity, hence the two
    -- sheaf sections are equal.
    sorry
  · intro hsep
    -- Source route: convert the section-separation criterion into the owner criterion that every
    -- sheaf morphism inducing isomorphisms on all point stalks is itself an isomorphism.
    sorry

end GrothendieckTopology

end CategoryTheory
