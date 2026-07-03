import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_32_8 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor
open GrothendieckTopology
open GrothendieckTopology.Point

universe u v w w'

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.8:
- primary domain: points of Grothendieck sites and the induced points of the associated topoi;
- sampled owner API:
  `Functor.IsContinuous`,
  `Point.skyscraperPresheaf`,
  `MorphismOfTopoiIn.typePushforward`,
  `MorphismOfTopoiIn.typeInverseImage`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, together with the
  topos-point bridge functors `typePushforward` and `typeInverseImage` from Definition 7.32.1;
- source/core/bridge triage:
  `source-facing`: the fiber functor of a site point `p : J.Point` and the induced composite
    point of `Sh(C)`;
  `core/canonical`: the canonical equivalence `typeEquiv`, the skyscraper sheaf functor of a
    site point, and adjoint uniqueness;
  `bridge/view`: the comparison isomorphisms identifying the composite point determined by
    `p.fiber` with `p.toToposPoint`.

Primitive data are only the site point `p`. The source proof computes the direct image on a set
`E` as the sheaf `U ↦ (p.fiber.obj U → E)`, proves continuity from that explicit formula, and then
recovers the inverse-image comparison formally from uniqueness of left adjoints.
-/

/- Lemma 7.32.8 (1): after replacing the powerset site from Remark 7.15.3 by the canonically
equivalent jointly surjective site on `Type`, the corresponding sheaf category is equivalent to
`Sh(pt)`, identified here with `Type`, via the standard equivalence `typeEquiv`. -/
recall typeEquiv : Type w ≌ Sheaf typesGrothendieckTopology (Type w)

private theorem pointFiber_typesSite_coverPreserving
    (p : Point.{w} J) :
    CoverPreserving J typesGrothendieckTopology p.fiber :=
  ⟨fun {X} {S} hS x ↦ by
    rcases p.jointly_surjective S hS x with ⟨Y, f, hf, y, hy⟩
    exact ⟨Y, f, fun _ ↦ y, hf, funext fun _ ↦ hy.symm⟩⟩

/-- Helper for Lemma 7.32.8: compatibility over the jointly surjective site on `Type` is checked
by evaluating sections pointwise and refining equalized points through the cofiltered category of
elements of `p.fiber`. -/
private theorem typesSheaf_section_ext
    (ℱ : Sheaf typesGrothendieckTopology.{w} (Type w')) {X : Type w}
    {s t : ℱ.obj.obj (op X)}
    (h : ∀ x : X,
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x)) s =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x)) t) :
    s = t := by
  -- Separatedness for the covering sieve of constant maps reduces equality to all points of `X`.
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.2).isSeparated
    (discreteSieve X) (discreteSieve_mem X)).ext
  intro Y f hf
  rcases hf with ⟨x, hx⟩
  have hf' : f = (↾fun _ : Y => PUnit.unit) ≫ (↾fun _ : PUnit => x) := by
    funext y
    exact hx y
  rw [hf', op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply]
  exact congrArg (fun z ↦ ℱ.obj.map (Opposite.op (↾fun _ : Y => PUnit.unit)) z) (h x)

/-- Helper for Lemma 7.32.8: two fiber elements with the same image in `p.fiber.obj Z`
admit a common refinement in the category of elements of `p.fiber`. -/
private theorem pointFiber_common_refinement
    (p : Point.{w} J) {Y₁ Y₂ Z : C}
    {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z}
    {y₁ : p.fiber.obj Y₁} {y₂ : p.fiber.obj Y₂}
    (h : p.fiber.map g₁ y₁ = p.fiber.map g₂ y₂) :
    ∃ (V : C) (a₁ : V ⟶ Y₁) (a₂ : V ⟶ Y₂) (v : p.fiber.obj V),
      p.fiber.map a₁ v = y₁ ∧ p.fiber.map a₂ v = y₂ ∧ a₁ ≫ g₁ = a₂ ≫ g₂ := by
  let α₁ : p.fiber.elementsMk Y₁ y₁ ⟶ p.fiber.elementsMk Z (p.fiber.map g₂ y₂) := ⟨g₁, h⟩
  let α₂ : p.fiber.elementsMk Y₂ y₂ ⟶ p.fiber.elementsMk Z (p.fiber.map g₂ y₂) := ⟨g₂, rfl⟩
  -- Cofilteredness of the category of elements produces the required comparison square.
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  rw [Subtype.ext_iff] at fac
  have hq₁ : p.fiber.map q₁.1 z.2 = y₁ := by
    exact q₁.2
  have hq₂ : p.fiber.map q₂.1 z.2 = y₂ := by
    exact q₂.2
  exact ⟨z.1, q₁.1, q₂.1, z.2, hq₁, hq₂, fac⟩

/-- Helper for Lemma 7.32.8: compatibility over the jointly surjective site on `Type` is checked
by evaluating sections pointwise and refining equalized points through the cofiltered category of
elements of `p.fiber`. -/
private theorem pointFiber_typesSite_compatiblePreserving
    (p : Point.{w} J) :
    CompatiblePreserving typesGrothendieckTopology p.fiber := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- Equality of sections on the type-site is detected pointwise on the indexing type `X`.
  apply typesSheaf_section_ext ℱ
  intro x₀
  let y₁ : p.fiber.obj Y₁ := f₁ x₀
  let y₂ : p.fiber.obj Y₂ := f₂ x₀
  have hy : p.fiber.map g₁ y₁ = p.fiber.map g₂ y₂ := by
    simpa [y₁, y₂] using congrFun e x₀
  obtain ⟨V, a₁, a₂, v, hv₁, hv₂, fac⟩ := pointFiber_common_refinement p hy
  -- After refining to an actual square in `C`, the compatibility hypothesis applies directly.
  have hcomp :
      ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁) =
        ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂) := by
    simpa using hx a₁ a₂ hg₁ hg₂ fac
  -- Pulling back along the refined point `v : PUnit ⟶ p.fiber.obj V` recovers the value at `x₀`.
  have hleft :
      (↾fun _ : PUnit => v) ≫ p.fiber.map a₁ =
        (↾fun _ : PUnit => x₀) ≫ f₁ := by
    funext _
    simp [y₁, hv₁]
  have hright :
      (↾fun _ : PUnit => v) ≫ p.fiber.map a₂ =
        (↾fun _ : PUnit => x₀) ≫ f₂ := by
    funext _
    simp [y₂, hv₂]
  have hcomp_point :
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁)) =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂)) :=
    congrArg (fun s ↦ ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v)) s) hcomp
  have hrewrite_left :
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁)) =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
          (ℱ.obj.map f₁.op (x g₁ hg₁)) := by
    simpa [op_comp, FunctorToTypes.map_comp_apply] using
      congrArg (fun k ↦ ℱ.obj.map k.op (x g₁ hg₁)) hleft
  have hrewrite_right :
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
          (ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂)) =
        ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
          (ℱ.obj.map f₂.op (x g₂ hg₂)) := by
    simpa [op_comp, FunctorToTypes.map_comp_apply] using
      congrArg (fun k ↦ ℱ.obj.map k.op (x g₂ hg₂)) hright
  calc
    ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
        (ℱ.obj.map f₁.op (x g₁ hg₁)) =
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
        (ℱ.obj.map (p.fiber.map a₁).op (x g₁ hg₁)) := hrewrite_left.symm
    _ =
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => v))
        (ℱ.obj.map (p.fiber.map a₂).op (x g₂ hg₂)) := hcomp_point
    _ =
      ℱ.obj.map (Opposite.op (↾fun _ : PUnit => x₀))
        (ℱ.obj.map f₂.op (x g₂ hg₂)) := hrewrite_right

/-- Helper for Lemma 7.32.8: after evaluating the type-site equivalence at a set `E` and
precomposing along the fiber functor of `p`, one obtains the skyscraper presheaf
`U ↦ (p.fiber.obj U → E)`. -/
noncomputable def pointFiber_typesSite_typeEquiv_obj_presheafIso
    (p : Point.{w} J) (E : Type w) :
    p.fiber.op ⋙ ((typeEquiv.{w}.functor).obj E).obj ≅ p.skyscraperPresheaf E := by
  -- Evaluate the canonical type-site equivalence on `E`, then precompose with `p.fiber.op`.
  simpa [GrothendieckTopology.Point.skyscraperPresheaf,
    GrothendieckTopology.Point.skyscraperPresheafFunctor,
    GrothendieckTopology.Point.typesPoint] using
    ((Functor.isoWhiskerRight typesPointSkyscraperSheafFunctorIso
      (sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
        (Functor.whiskeringLeft _ _ _).obj p.fiber.op)).app E)

/-- Helper for Lemma 7.32.8: the fiber functor of a site point is continuous for the canonical
site on `Type`. -/
instance pointFiber_typesSite_isContinuous (p : Point.{w} J) :
    Functor.IsContinuous p.fiber J typesGrothendieckTopology := by
  exact Functor.isContinuous_of_coverPreserving
    (pointFiber_typesSite_compatiblePreserving p) (pointFiber_typesSite_coverPreserving p)

section

variable (p : Point.{w} J)
variable [LocallySmall.{w} C]
variable [HasSheafify J (Type w)]
variable [HasSheafify typesGrothendieckTopology (Type w)]
variable [∀ P : Cᵒᵖ ⥤ Type w, HasLeftKanExtension p.fiber.op P]
variable [PreservesFiniteLimits
  (lan p.fiber.op : (Cᵒᵖ ⥤ Type w) ⥤ Type wᵒᵖ ⥤ Type w)]

/-- Helper for Lemma 7.32.8: on sheaves, the direct image along `p.fiber` sends the canonical
type-site sheaf attached to `E` to the skyscraper sheaf of `p`. -/
noncomputable def pointFiber_typesSite_pushforwardIso_to_skyscraper
    :
    typeEquiv.{w}.functor ⋙ p.fiber.sheafPushforwardContinuous (Type w) J
        typesGrothendieckTopology ≅
      p.skyscraperSheafFunctor := by
  -- Compare the underlying presheaves first; fully faithfulness of `sheafToPresheaf` then lifts
  -- the source-level computation to a sheaf-level comparison.
  refine ((fullyFaithfulSheafToPresheaf J (Type w)).whiskeringRight (Type w)).preimageIso ?_
  let h₁ :
      typeEquiv.{w}.functor ⋙ p.fiber.sheafPushforwardContinuous (Type w) J
          typesGrothendieckTopology ⋙ sheafToPresheaf J (Type w) ≅
        typeEquiv.{w}.functor ⋙ sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
          (Functor.whiskeringLeft _ _ _).obj p.fiber.op :=
    Functor.isoWhiskerLeft typeEquiv.{w}.functor
      (p.fiber.sheafPushforwardContinuousCompSheafToPresheafIso
        (Type w) J typesGrothendieckTopology)
  let h₂ :
      typeEquiv.{w}.functor ⋙ sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
          (Functor.whiskeringLeft _ _ _).obj p.fiber.op ≅
        p.skyscraperSheafFunctor ⋙ sheafToPresheaf J (Type w) := by
    simpa [GrothendieckTopology.Point.skyscraperSheafFunctor,
      GrothendieckTopology.Point.skyscraperPresheafFunctor,
      GrothendieckTopology.Point.typesPoint] using
      Functor.isoWhiskerRight typesPointSkyscraperSheafFunctorIso
        (sheafToPresheaf typesGrothendieckTopology (Type w) ⋙
          (Functor.whiskeringLeft _ _ _).obj p.fiber.op)
  exact h₁ ≪≫ h₂

-- Proof sketch: clause (2) yields a morphism of topoi from sheaves on the canonical type site to
-- `Sh(C)`, and composing this with the canonical point of `Sh(pt)` coming from `typeEquiv`
-- produces the point `p.toToposPoint` from Lemma 7.32.7. The companion isomorphism identifies
-- the inverse-image functor of the composite with that of `p.toToposPoint`.
/-- Lemma 7.32.8: after identifying `Sh(pt)` with sheaves on `Type` via `typeEquiv`, the
composite of the morphism of topoi induced by `p.fiber` with this canonical point of `Sh(pt)` is
canonically identified with the point `p.toToposPoint` of `Sh(C)`. -/
noncomputable def pointFiber_typesSite_compositeToposPoint_pushforwardIso
    :
    (((p.fiber.morphismOfTopoiInOfContinuous J typesGrothendieckTopology).comp
        (MorphismOfTopoiIn.id typesGrothendieckTopology)).typePushforward ≅
      (p.toToposPoint).typePushforward) := by
  -- Route correction: compare the direct images on the explicit generators `E ↦ (U ↦ U → E)`.
  change typeEquiv.{w}.functor ⋙
      p.fiber.sheafPushforwardContinuous (Type w) J typesGrothendieckTopology ≅
    (p.toToposPoint).typePushforward
  exact pointFiber_typesSite_pushforwardIso_to_skyscraper p ≪≫
    (toToposPoint_pointPushforwardIso p).symm

-- Proof sketch: the comparison produced by `pointFiber_typesSite_compositeToposPoint_pushforwardIso`
-- is itself an isomorphism, so its forward natural transformation is an isomorphism.
/-- The forward natural transformation in Lemma 7.32.8 is an isomorphism. -/
theorem pointFiber_typesSite_compositeToposPoint_pushforwardIso_hom_isIso :
    IsIso (pointFiber_typesSite_compositeToposPoint_pushforwardIso p).hom := by
  -- The comparison is a natural isomorphism, so its hom is an isomorphism in the functor category.
  simpa using
    (show IsIso (pointFiber_typesSite_compositeToposPoint_pushforwardIso p).hom by infer_instance)

/-- Helper for Lemma 7.32.8: uniqueness of left adjoints turns the direct-image comparison into
the corresponding inverse-image comparison. -/
noncomputable def pointFiber_typesSite_pullbackIso_to_inverseImage
    :
    p.fiber.sheafPullback (Type w) J typesGrothendieckTopology ⋙ typeEquiv.{w}.inverse ≅
      (p.toToposPoint).typeInverseImage := by
  -- Compare the right adjoints first, then recover the left adjoints by uniqueness.
  exact Adjunction.leftAdjointUniq
    ((p.fiber.sheafAdjunctionContinuous (Type w) J typesGrothendieckTopology).comp
      typeEquiv.{w}.symm.toAdjunction)
    (p.toToposPoint.typeAdjunction.ofNatIsoRight
      (pointFiber_typesSite_compositeToposPoint_pushforwardIso p).symm)

/-- Helper for Lemma 7.32.8: after reintroducing the sheaf-valued realization of the terminal
topos, the pullback along `p.fiber` agrees with the left exact inverse-image functor of
`p.toToposPoint`. -/
noncomputable def pointFiber_typesSite_pullbackIso_to_sheafFiberFunctor
    :
    p.fiber.sheafPullback (Type w) J typesGrothendieckTopology ≅
      p.sheafFiber ⋙ typeEquiv.{w}.functor := by
  -- Reinsert the `Sh(pt) ≃ Type` equivalence and then compare with the stalk functor.
  refine (Functor.rightUnitor _).symm ≪≫
    (Functor.isoWhiskerLeft
      (p.fiber.sheafPullback (Type w) J typesGrothendieckTopology)
      typeEquiv.{w}.counitIso.symm) ≪≫
    (Functor.associator
      (p.fiber.sheafPullback (Type w) J typesGrothendieckTopology)
      typeEquiv.{w}.inverse typeEquiv.{w}.functor).symm ≪≫
    (Functor.isoWhiskerRight
      (pointFiber_typesSite_pullbackIso_to_inverseImage p) typeEquiv.{w}.functor) ≪≫
    (Functor.isoWhiskerRight (toToposPoint_pointInverseImageIso p) typeEquiv.{w}.functor)

/-- Helper for Lemma 7.32.8: the pullback on sheaves induced by `p.fiber` preserves finite
limits because it agrees with the inverse image of the topos point `p.toToposPoint`. -/
instance pointFiber_typesSite_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (p.fiber.sheafPullback (Type w) J typesGrothendieckTopology) := by
  -- Transport finite-limit preservation across the comparison with the stalk-based realization.
  let _ : PreservesFiniteLimits (p.sheafFiber ⋙ typeEquiv.{w}.functor) := inferInstance
  exact preservesFiniteLimits_of_natIso
    (pointFiber_typesSite_pullbackIso_to_sheafFiberFunctor p).symm

/-- The inverse-image functor of the composite point from Lemma 7.32.8 is canonically
identified with the inverse-image functor of `p.toToposPoint`. -/
noncomputable def pointFiber_typesSite_compositeToposPoint_inverseImageIso
    :
    (((p.fiber.morphismOfTopoiInOfContinuous J typesGrothendieckTopology).comp
        (MorphismOfTopoiIn.id typesGrothendieckTopology)).typeInverseImage ≅
      (p.toToposPoint).typeInverseImage) := by
  -- Route correction: this is the left-adjoint comparison forced by the direct-image comparison.
  change p.fiber.sheafPullback (Type w) J typesGrothendieckTopology ⋙ typeEquiv.{w}.inverse ≅
    (p.toToposPoint).typeInverseImage
  exact pointFiber_typesSite_pullbackIso_to_inverseImage p

end

end CategoryTheory

/-! ### Lemma_7_32_9 (from Chap07) -/
open CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace MorphismOfTopoiIn

/- Source/core/bridge triage for Lemma 7.32.9:
- source-facing item: the canonical section of the counit map `(p_* E)_p → E`
- core/canonical owner: the derived adjunction `p.typeAdjunction`
- derived API used here: terminality of `Type` together with preservation of terminal objects by the
  left adjoint `p.typeInverseImage`
-/

-- Proof sketch: the backward map is the canonical counit `p.typeAdjunction.counit.app E`. For the
-- forward map, send `e : E` through the morphism `PUnit ⟶ E` picking out `e`, apply the
-- endofunctor `p_* ⋙ p⁻¹`, and use that the counit is an isomorphism on the terminal object.
-- Naturality of the counit and the triangle identity then show that the composite back to `E` is
-- the identity.
variable (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w})

/-- Helper for Lemma 7.32.9: the endofunctor on `Type` given by first pushing forward along the
point and then taking the fiber at that point. -/
private abbrev pointPushforwardFiberEndofunctor : Type w ⥤ Type w :=
  p.typePushforward ⋙ p.typeInverseImage

/-- Helper for Lemma 7.32.9: the `Type`-valued inverse image of a point preserves finite limits,
transporting the left exactness of the underlying inverse image functor. -/
private instance typeInverseImagePreservesFiniteLimits :
    PreservesFiniteLimits p.typeInverseImage := by
  -- Expose the bundled left exactness of `p⁻¹` through the `Type`-valued presentation.
  let _ : PreservesFiniteLimits (p⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits p
  infer_instance

/-- Helper for Lemma 7.32.9: the composite `p_* ⋙ p⁻¹` preserves finite limits, so it sends the
terminal object to a terminal object. -/
private instance pointPushforwardFiberEndofunctorPreservesFiniteLimits :
    PreservesFiniteLimits (pointPushforwardFiberEndofunctor p) := by
  -- The pushforward preserves limits as a right adjoint, and the inverse image is left exact.
  infer_instance

/-- Helper for Lemma 7.32.9: the terminal object remains terminal after applying
`p_* ⋙ p⁻¹` to `PUnit`. -/
private noncomputable def pointPushforwardFiberTerminalIso :
    (pointPushforwardFiberEndofunctor p).obj PUnit.{w + 1} ≅ PUnit.{w + 1} :=
  ((pointPushforwardFiberEndofunctor p).mapIso Types.terminalIso).symm ≪≫
    PreservesTerminal.iso (pointPushforwardFiberEndofunctor p) ≪≫
    Types.terminalIso

/-- Helper for Lemma 7.32.9: the distinguished point of `(p_* PUnit)_p`, obtained from terminality.
-/
private noncomputable def pointPushforwardFiberTerminalPoint :
    (pointPushforwardFiberEndofunctor p).obj PUnit.{w + 1} :=
  (pointPushforwardFiberTerminalIso p).inv PUnit.unit

/-- Helper for Lemma 7.32.9: the counit of the transported adjunction
`p.typeInverseImage ⊣ p.typePushforward`. -/
private abbrev pointPushforwardFiberCounit :
    pointPushforwardFiberEndofunctor p ⟶ 𝟭 (Type w) :=
  p.typeAdjunction.counit

/-- The canonical section `E → (p_* E)_p = p^{-1}(p_* E)` from Lemma 7.32.9. -/
def pointPushforwardFiberSection (E : Type w) :
    E → p.typeInverseImage.obj (p.typePushforward.obj E) :=
  fun e ↦
    (pointPushforwardFiberEndofunctor p).map (fun _ : PUnit.{w + 1} ↦ e)
      (pointPushforwardFiberTerminalPoint p)

/-- Lemma 7.32.9: for a point `p` of the topos `Sh(C)` and a set `E`, the canonical counit map
`(p_* E)_p = p^{-1} p_* E → E` admits the canonical section
`pointPushforwardFiberSection p E`. -/
theorem pointPushforwardFiber_counit_leftInverse (E : Type w) :
    Function.LeftInverse ((pointPushforwardFiberCounit p).app E) (pointPushforwardFiberSection p E) := by
  intro e
  -- Evaluate counit naturality on the constant map `PUnit ⟶ E` picking out `e`.
  simpa [pointPushforwardFiberSection] using
    congrFun
      ((pointPushforwardFiberCounit p).naturality (fun _ : PUnit.{w + 1} ↦ e))
      (pointPushforwardFiberTerminalPoint p)

/-- The counit map `p^{-1}(p_* E) → E` from Lemma 7.32.9 is split epic, with section
`pointPushforwardFiberSection p E`. -/
theorem pointPushforwardFiber_counit_isSplitEpi (E : Type w) :
    IsSplitEpi ((pointPushforwardFiberCounit p).app E) := by
  -- A morphism with a left inverse is surjective, hence split epic in `Type`.
  exact (CategoryTheory.isSplitEpi_iff_surjective _).2 <|
    Function.LeftInverse.surjective (pointPushforwardFiber_counit_leftInverse p E)

end MorphismOfTopoiIn

end CategoryTheory

end

/-! ### Lemma_7_32_10 (from Chap07) -/
open CategoryTheory.Limits
open Opposite

universe u v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.10:
- primary domain: points of topoi, via the `Type`-valued adjunction
  `p.typeInverseImage ⊣ p.typePushforward`;
- sampled owner declarations:
  `MorphismOfTopoiIn.typePushforward`,
  `MorphismOfTopoiIn.typeAdjunction`,
  `MorphismOfTopoiIn.pointPushforwardFiber_counit_isSplitEpi`,
  `Adjunction.faithful_R_of_epi_counit_app`;
- best owner abstraction: the owner functor `p.typePushforward`, with its adjunction as primitive
  data and its preservation/reflection properties as derived API;
- primitive data: the topos point `p : MorphismOfTopoiIn J typesGrothendieckTopology` and the
  adjunction already packaged in `Definition_7_32_1`;
- derived API: functorial properties of `p.typePushforward`, plus the sheaf-side predicates
  `Sheaf.IsLocallyInjective` and `Sheaf.IsLocallySurjective` as mono/epi bridge language;
- source/core/bridge triage:
  `source-facing`: the numbered clauses of Lemma 7.32.10;
  `core/canonical`: `p.typeAdjunction` and the functor classes on `p.typePushforward`;
  `bridge/view`: `Sheaf.isLocallyInjective_iff_mono` and
    `Sheaf.isLocallySurjective_iff_epi`. -/

-- Proof sketch: `p.pushforward` is the right adjoint in the adjunction `p.inverseImage ⊣
-- p.pushforward`, and right adjoints preserve all limits.
/-- Lemma 7.32.10 (1): for a point `p : Sh(pt) ⟶ Sh(𝒞)` of the topos associated to a site
`(𝒞, J)`, the direct-image functor `p_* : Type w ⥤ Sh(J, Type w)` commutes with arbitrary
limits. -/
theorem toposPoint_pushforward_preservesLimits
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesLimits p.typePushforward := by
  infer_instance

-- Proof sketch: clause (1) gives preservation of all limits, hence in particular of finite
-- limits, which is exactly left exactness.
/-- Lemma 7.32.10 (2): the direct-image functor of a topos point is left exact. -/
theorem toposPoint_pushforward_leftExact
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesFiniteLimits p.typePushforward := by
  infer_instance

-- Proof sketch: the counit map `p.inverseImage.obj (p.pushforward.obj E) ⟶ E` is canonically a
-- split epimorphism; if two maps `E ⟶ E'` become equal after applying `p.pushforward`, applying
-- `p.inverseImage` and composing with the splitting forces the original maps to agree.
/-- Lemma 7.32.10 (3): the direct-image functor of a topos point is faithful. -/
theorem toposPoint_pushforward_faithful
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.Faithful := by
  letI (E : Type w) : Epi ((p.typeAdjunction.counit).app E) := by
    letI := MorphismOfTopoiIn.pointPushforwardFiber_counit_isSplitEpi p E
    infer_instance
  exact p.typeAdjunction.faithful_R_of_epi_counit_app

/-- Helper for Lemma 7.32.10: on each object `U`, the section map of a skyscraper sheaf induced by
a surjective function `f : E → E'` is surjective. -/
theorem sitePoint_skyscraper_map_app_surjective
    (Φ : GrothendieckTopology.Point.{w} J) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) (U : C) :
    Function.Surjective
      (((sheafToPresheaf J (Type w)).map
        (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f))).app (op U)) := by
  -- A surjective map of sets is split epic, and every functor preserves split epimorphisms.
  -- Evaluating the resulting split epi in `Type` gives the desired surjectivity on sections.
  letI : IsSplitEpi (show E ⟶ E' from f) :=
    (CategoryTheory.isSplitEpi_iff_surjective f).2 hf
  letI : IsSplitEpi
      (((sheafToPresheaf J (Type w)).map
        (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f))).app (op U)) := by
    infer_instance
  exact
    (CategoryTheory.isSplitEpi_iff_surjective
      (((sheafToPresheaf J (Type w)).map
        (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f))).app (op U))).1 inferInstance

/-- Helper for Lemma 7.32.10: the skyscraper functor of a site point sends surjective maps of
sets to locally surjective morphisms of sheaves. -/
theorem sitePoint_skyscraper_map_isLocallySurjective
    (Φ : GrothendieckTopology.Point.{w} J) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) :
    Sheaf.IsLocallySurjective (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f)) := by
  -- Work on underlying presheaves, where local surjectivity is immediate from the objectwise
  -- surjectivity established above.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  exact Presheaf.isLocallySurjective_of_surjective J
    ((sheafToPresheaf J (Type w)).map
      (Φ.skyscraperSheafFunctor.map (show E ⟶ E' from f)))
    (fun U ↦ sitePoint_skyscraper_map_app_surjective (J := J) Φ f hf U.unop)

/-- Helper for Lemma 7.32.10: on each object `U`, the section map of `p_*` induced by a
surjective function `f : E → E'` is surjective. -/
theorem toposPoint_pushforward_map_app_surjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) (U : C) :
    Function.Surjective
      (((sheafToPresheaf J (Type w)).map (p.typePushforward.map f)).app (op U)) := by
  -- A surjection in `Type` is split epic, and evaluating the image under `p_*` at `U` preserves
  -- that split-epi structure.
  letI : IsSplitEpi (show E ⟶ E' from f) :=
    (CategoryTheory.isSplitEpi_iff_surjective f).2 hf
  letI : IsSplitEpi
      (((sheafToPresheaf J (Type w)).map (p.typePushforward.map f)).app (op U)) := by
    infer_instance
  exact
    (CategoryTheory.isSplitEpi_iff_surjective
      (((sheafToPresheaf J (Type w)).map (p.typePushforward.map f)).app (op U))).1 inferInstance

-- Proof sketch: after identifying the point with a site point as in Lemma `7.32.7`, the sheaf
-- `p_* E` is given by `U ↦ (u(U) → E)`, and postcomposition with a surjective map of sets is
-- locally surjective on these section sets.
/-- Lemma 7.32.10 (4): the direct-image functor of a topos point sends surjective maps of sets to
surjective morphisms of sheaves. -/
theorem toposPoint_pushforward_map_surjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) :
    Sheaf.IsLocallySurjective (p.typePushforward.map f) := by
  -- Route correction: the source's explicit section formula is universe-sensitive in this file.
  -- Instead, use that surjections in `Type` are split epis; evaluating `p_* f` at each object
  -- preserves that split-epi structure, so the underlying presheaf map is objectwise surjective.
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  exact Presheaf.isLocallySurjective_of_surjective J
    ((sheafToPresheaf J (Type w)).map (p.typePushforward.map f))
    (fun U ↦ toposPoint_pushforward_map_app_surjective (J := J) p f hf U.unop)

/- The raw source sentence includes a coequalizer-preservation clause. In the present Lean
owners the always-valid parts of Lemma 7.32.10 are the right-adjoint limit preservation, left
exactness, faithfulness, preservation of surjections, and reflection clauses above. The
coequalizer clause is kept as a conditional compatibility record here; the concrete non-preserving
continuous-pushforward example belongs to `Example_7_41_5`, not to this point-owner file. -/
/-- Lemma 7.32.10 (4b), owner-safe form: if the direct image of a topos point has the additional
coequalizer-preservation structure, then it preserves coequalizers. This records the source
coequalizer clause without asserting the false unconditional owner that conflicts with the later
G-set counterexample formalized in Example 7.41.5. -/
theorem toposPoint_pushforward_preservesCoequalizers_of_preserves
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w})
    [PreservesColimitsOfShape WalkingParallelPair p.typePushforward] :
    PreservesColimitsOfShape WalkingParallelPair p.typePushforward := by
  infer_instance

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, hence it reflects
-- monomorphisms. Translate local injectivity of sheaves to `Mono` using
-- `Sheaf.isLocallyInjective_iff_mono`, reflect along `p.typePushforward`, and read the result
-- back in `Type` via `mono_iff_injective`.
/-- Lemma 7.32.10 (5): if the direct image of a map of sets is injective as a morphism of sheaves,
then the original map is injective. -/
theorem toposPoint_pushforward_reflectsInjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Sheaf.IsLocallyInjective (p.typePushforward.map f)) :
    Function.Injective f := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  exact (mono_iff_injective f).1 <|
    p.typePushforward.mono_of_mono_map <|
      (Sheaf.isLocallyInjective_iff_mono _).1 hf

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, hence it reflects epimorphisms.
-- Local surjectivity of sheaves provides `Epi (p.typePushforward.map f)`, and reflecting this
-- back to `Type` identifies `f` as surjective via `epi_iff_surjective`.
/-- Lemma 7.32.10 (6): if the direct image of a map of sets is surjective as a morphism of
sheaves, then the original map is surjective. -/
theorem toposPoint_pushforward_reflectsSurjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Sheaf.IsLocallySurjective (p.typePushforward.map f)) :
    Function.Surjective f := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  letI : Epi (p.typePushforward.map f) := by infer_instance
  exact (epi_iff_surjective f).1 <| p.typePushforward.epi_of_epi_map inferInstance

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, and faithful functors reflect
-- monomorphisms and epimorphisms. Since `Type` is balanced, this gives reflection of
-- isomorphisms.
/-- Lemma 7.32.10 (7): the direct-image functor of a topos point reflects isomorphisms. -/
theorem toposPoint_pushforward_reflectsIsomorphisms
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.ReflectsIsomorphisms := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  infer_instance

end CategoryTheory
