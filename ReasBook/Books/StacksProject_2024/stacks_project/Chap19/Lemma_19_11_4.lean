import Mathlib
import StacksProject_2024.Chap19.Definition_19_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U M : C}

/-- Helper for Lemma 19.11.4: if the image of a coproduct map is contained in a subobject, then
each coproduct component factors through that subobject. -/
lemma factors_component_of_imageSubobject_le
    {ι : Type*}
    [HasCoproduct fun _ : ι ↦ U]
    (g : (∐ fun _ : ι ↦ U) ⟶ M) (N : Subobject M)
    (h : imageSubobject g ≤ N) (i : ι) :
    N.Factors (Sigma.ι (fun _ : ι ↦ U) i ≫ g) := by
  -- Factor the chosen coproduct component through the image and then through `N`.
  simpa [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp] using
    (Subobject.factors_comp_arrow
      (Sigma.ι (fun _ : ι ↦ U) i ≫ factorThruImageSubobject g ≫ Subobject.ofLE _ _ h))

/- Domain-style sampling for Lemma 19.11.4:
- primary domain: generators/separators, coproduct presentations, and smallness of object
  properties in abelian and Grothendieck abelian categories;
- sampled owner declarations:
  `isSeparator_iff_exists_not_factors_subobject`,
  `Subobject M`,
  `HasCoproduct`,
  `HasCoproducts`,
  `Cardinal.mk (Subobject M)`,
  `Shrink.{w} (Subobject M)`,
  `ObjectProperty.EssentiallySmall`,
  the derived instance `EssentiallySmall P.FullSubcategory`;
- best owner abstractions: `IsSeparator U` together with the canonical owner
  `Subobject M` of the subobject lattice in the source-facing part (1), with
  `Shrink.{w} (Subobject M)` kept only as an internal bridge, and
  `ObjectProperty.EssentiallySmall` for the bounded-size class of objects in part (2);
- primitive data: the separator hypothesis `IsSeparator U`, the object `M`, and its canonical
  subobject type `Subobject M`, together with the single coproduct of copies of `U` needed to form
  the relevant sum in part (1);
- derived API: the canonical subobject-indexed epimorphism in part (1), the source-facing
  κ-bounded existential presentation derived from it, the shrink-indexed bridge theorem used to
  hide smallness bookkeeping, and the Grothendieck-level
  full-subcategory essential-smallness statement in part (2).

Source/core/bridge triage:
- `source-facing`: the coproduct presentation indexed by `Subobject M`, and the existential
  quotient statement by a coproduct of at most `κ` copies of `U`;
- `core/canonical`: the owner notions `IsSeparator`, `Subobject M`, `HasCoproducts.{max u v} C`,
  `Cardinal.mk (Subobject M)`, and `ObjectProperty.EssentiallySmall`;
- `bridge/view`: the shrink-indexed epimorphism used to pass through a smaller universe when
  needed, and the formulation of part (2) as essential smallness of the full subcategory.
-/ 

-- Proof sketch: for each proper subobject `N ⊊ M`, use
-- `isSeparator_iff_exists_not_factors_subobject` to choose a morphism `f_N : U ⟶ M` which does
-- not factor through `N`. Assembling these maps over `Subobject M` gives a morphism
-- `∐ fun _ : Subobject M ↦ U ⟶ M`; if its image were a proper subobject, the chosen map attached
-- to that image would factor through it via the coproduct inclusion, a contradiction, so the map
-- is epi. The shrink-indexed theorem below is the same construction pushed through
-- `Shrink.{w} (Subobject M)` when a smaller universe is needed for part (2).
/-- Canonical form of Lemma 19.11.4 (1): the `w`-small model `Shrink.{w} (Subobject M)` of the
subobject lattice of `M` indexes a coproduct of copies of `U` admitting an epimorphism onto `M`. -/
lemma exists_epi_from_coproduct_of_generator_of_subobject_shrink
    [Small.{w} (Subobject M)]
    [HasCoproduct fun _ : Shrink.{w} (Subobject M) ↦ U]
    (hU : IsSeparator U) :
    ∃ (f : (∐ fun _ : Shrink.{w} (Subobject M) ↦ U) ⟶ M), Epi f := by
  classical
  let chosen : Shrink.{w} (Subobject M) → (U ⟶ M) := fun i ↦
    let N : Subobject M := (equivShrink (Subobject M)).symm i
    if hN : N = ⊤ then
      0
    else
      Classical.choose
        (((isSeparator_iff_exists_not_factors_subobject C U).mp hU) N hN)
  let f : (∐ fun _ : Shrink.{w} (Subobject M) ↦ U) ⟶ M := Limits.Sigma.desc chosen
  refine ⟨f, ?_⟩
  -- Show that the image cannot be a proper subobject, using the chosen component at that image.
  have hImageTop : imageSubobject f = ⊤ := by
    by_contra hImage
    have hfactor :
        (imageSubobject f).Factors (chosen (equivShrink (Subobject M) (imageSubobject f))) := by
      simpa [f, chosen, hImage, Limits.Sigma.ι_desc] using
        factors_component_of_imageSubobject_le
          (g := f) (N := imageSubobject f) le_rfl
          (equivShrink (Subobject M) (imageSubobject f))
    have hchosen :
        ¬ (imageSubobject f).Factors
            (chosen (equivShrink (Subobject M) (imageSubobject f))) := by
      simpa [chosen, hImage] using
        (Classical.choose_spec
          (((isSeparator_iff_exists_not_factors_subobject C U).mp hU)
            (imageSubobject f) hImage))
    exact hchosen hfactor
  -- Once the image is `⊤`, the standard image factorization makes `f` an epimorphism.
  haveI : IsIso (imageSubobject f).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hImageTop
  have hEpi : Epi (factorThruImageSubobject f ≫ (imageSubobject f).arrow) := inferInstance
  simpa [imageSubobject_arrow_comp] using hEpi

/-- Canonical subobject-indexed form of Lemma 19.11.4 (1): if `U` is a generator of an abelian
category, then the coproduct of copies of `U` indexed by `Subobject M` admits an epimorphism onto
`M`. -/
lemma exists_epi_from_coproduct_of_generator_of_subobject
    [HasCoproducts.{max u v} C]
    (hU : IsSeparator U) :
    ∃ (f : (∐ fun _ : Subobject M ↦ U) ⟶ M), Epi f := by
  classical
  let chosen : Subobject M → (U ⟶ M) := fun N ↦
    if hN : N = ⊤ then
      0
    else
      Classical.choose
        (((isSeparator_iff_exists_not_factors_subobject C U).mp hU) N hN)
  let f : (∐ fun _ : Subobject M ↦ U) ⟶ M := Limits.Sigma.desc chosen
  refine ⟨f, ?_⟩
  -- The same source proof works directly over the full subobject lattice.
  have hImageTop : imageSubobject f = ⊤ := by
    by_contra hImage
    have hfactor : (imageSubobject f).Factors (chosen (imageSubobject f)) := by
      simpa [f, chosen, hImage, Limits.Sigma.ι_desc] using
        factors_component_of_imageSubobject_le
          (g := f) (N := imageSubobject f) le_rfl (imageSubobject f)
    have hchosen : ¬ (imageSubobject f).Factors (chosen (imageSubobject f)) := by
      simpa [chosen, hImage] using
        (Classical.choose_spec
          (((isSeparator_iff_exists_not_factors_subobject C U).mp hU)
            (imageSubobject f) hImage))
    exact hchosen hfactor
  -- The image computation upgrades the universal coproduct map to an epi.
  haveI : IsIso (imageSubobject f).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hImageTop
  have hEpi : Epi (factorThruImageSubobject f ≫ (imageSubobject f).arrow) := inferInstance
  simpa [imageSubobject_arrow_comp] using hEpi

/-- Lemma 19.11.4 (1): if `U` is a generator of an abelian category and
`|M| = #(Subobject M) ≤ κ`, then `M` is a quotient of a coproduct of at most `κ` copies of `U`. -/
lemma exists_epi_from_coproduct_of_generator_of_subobject_cardinal_le
    [HasCoproducts.{max u v} C]
    (hU : IsSeparator U) (κ : Cardinal.{max u v}) (hM : Cardinal.mk (Subobject M) ≤ κ) :
    ∃ (ι : Type (max u v))
      (_ : Cardinal.mk ι ≤ κ)
      (f : (∐ fun _ : ι ↦ U) ⟶ M), Epi f := by
  -- Use the canonical subobject lattice itself as the bounded index set.
  obtain ⟨f, hf⟩ := exists_epi_from_coproduct_of_generator_of_subobject (U := U) (M := M) hU
  exact ⟨Subobject M, hM, f, hf⟩

variable [IsGrothendieckAbelian.{w} C]

-- Proof sketch: in a Grothendieck abelian category, `WellPowered.{w}` makes every subobject
-- lattice `w`-small, so the shrink-indexed bridge above applies to every object with
-- `#(Subobject M) ≤ κ`. Thus every bounded object is a quotient of a coproduct of at most `κ`
-- copies of the chosen generator, using an index type in `Type w`. Quotients of all such
-- `w`-small coproducts are classified by a set via the corresponding subobject lattices, so the
-- resulting object property is essentially small; the source-facing full-subcategory statement is
-- then the canonical derived instance.
/-- Helper for Lemma 19.11.4: the supremum of the `w`-small cardinals whose lifts are bounded by
`κ`. -/
noncomputable def lowerLiftCardinalBound (κ : Cardinal.{max u v}) : Cardinal.{w} :=
  sSup { c : Cardinal.{w} | Cardinal.lift.{max u v} c ≤ Cardinal.lift.{w} κ }

/-- Helper for Lemma 19.11.4: the lower-universe cardinals whose lifts are bounded by `κ`
form a `w`-small type. -/
abbrev bounded_lift_cardinal (κ : Cardinal.{max u v}) :=
  { c : Cardinal.{w} // c ≤ lowerLiftCardinalBound (w := w) κ }

/-- Helper for Lemma 19.11.4: the lower-universe cardinals whose lifts are bounded by `κ`
form a `w`-small type. -/
lemma small_bounded_lift_cardinals (κ : Cardinal.{max u v}) :
    Small.{w} (bounded_lift_cardinal κ) := by
  -- This is the standard initial-segment smallness for lower-universe cardinals.
  simpa [bounded_lift_cardinal, lowerLiftCardinalBound] using
    (inferInstance : Small.{w} (Set.Iic (lowerLiftCardinalBound (w := w) κ)))

/-- Helper for Lemma 19.11.4: the canonical family of quotient representatives indexed by a
bounded lower-universe cardinal and a subobject of the corresponding separator-coproduct. -/
def bounded_separator_cokernel_property (κ : Cardinal.{max u v}) : ObjectProperty C :=
  ObjectProperty.ofObj fun
    p : Σ c : bounded_lift_cardinal κ,
      Subobject (∐ fun _ : c.1.out ↦ separator C) ↦
    cokernel p.2.arrow

/-- Helper for Lemma 19.11.4: the canonical family of bounded separator-cokernel representatives
is `w`-small. -/
lemma bounded_separator_cokernel_property_small (κ : Cardinal.{max u v}) :
    ObjectProperty.Small.{w} (bounded_separator_cokernel_property (C := C) κ) := by
  -- The first coordinate is the bounded-cardinal index; the second is `w`-small by well-poweredness.
  letI : Small.{w} (bounded_lift_cardinal κ) := small_bounded_lift_cardinals (κ := κ)
  letI (c : bounded_lift_cardinal κ) :
      Small.{w} (Subobject (∐ fun _ : c.1.out ↦ separator C)) := inferInstance
  simpa [bounded_separator_cokernel_property] using
    (inferInstance :
      ObjectProperty.Small.{w}
        (ObjectProperty.ofObj
          (fun p : Σ c : bounded_lift_cardinal κ,
              Subobject (∐ fun _ : c.1.out ↦ separator C) ↦
            cokernel p.2.arrow)))

/-- Helper for Lemma 19.11.4: the cokernels of subobjects of a fixed source object. -/
def cokernel_subobject_property (S : C) : ObjectProperty C :=
  ObjectProperty.ofObj fun A : Subobject S ↦ cokernel A.arrow

omit [IsGrothendieckAbelian.{w} C] in
/-- Helper for Lemma 19.11.4: an epimorphism from a fixed source presents its target as one of
the kernel-cokernel representatives attached to that source. -/
lemma mem_isoClosure_indexed_cokernel_subobject_property_of_epi
    {α : Type*} {S : α → C} (a : α) {M : C} (f : S a ⟶ M) [Epi f] :
    (ObjectProperty.ofObj
      (fun p : Σ a : α, Subobject (S a) ↦ cokernel p.2.arrow)).isoClosure M := by
  classical
  let A : Subobject (S a) := kernelSubobject f
  let s : Fork f 0 := Fork.ofι A.arrow (by simpa [A] using kernelSubobject_arrow_comp f)
  have hs : IsLimit s := by
    -- Replace the chosen kernel-subobject fork by the canonical kernel fork.
    refine IsLimit.ofIsoLimit (limit.isLimit (parallelPair f 0)) ?_
    exact Fork.ext (kernelSubobjectIso f).symm
  have hcolim :
      IsColimit
        (CokernelCofork.ofπ (f := A.arrow) f
          (by simpa [A] using kernelSubobject_arrow_comp f)) :=
    Abelian.epiIsCokernelOfKernel s hs
  let hQ :
      (ObjectProperty.ofObj
        (fun p : Σ a : α, Subobject (S a) ↦ cokernel p.2.arrow))
        (cokernel A.arrow) := by
    -- The cokernel of the kernel subobject is one of the representatives by definition.
    simpa [A] using
      (ObjectProperty.ofObj_apply
        (fun p : Σ a : α, Subobject (S a) ↦ cokernel p.2.arrow)
        ⟨a, A⟩)
  let i : cokernel A.arrow ≅ M :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel A.arrow) hcolim
  -- This canonical representative is isomorphic to the target object.
  exact ObjectProperty.prop_isoClosure hQ i.hom

/-- Helper for Lemma 19.11.4: every object whose subobject lattice has cardinality at most `κ`
lies in the iso-closure of the canonical bounded separator-cokernel family. -/
lemma mem_isoClosure_bounded_separator_cokernel_property
    {κ : Cardinal.{max u v}} {M : C}
    (hM : Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤ Cardinal.lift.{w} κ) :
    (bounded_separator_cokernel_property (C := C) κ).isoClosure M := by
  classical
  let ι := Shrink.{w} (Subobject M)
  haveI : HasCoproduct fun _ : ι ↦ separator C := inferInstance
  obtain ⟨f, hf⟩ :=
    exists_epi_from_coproduct_of_generator_of_subobject_shrink
      (U := separator C) (M := M) (hU := isSeparator_separator C)
  let c : bounded_lift_cardinal κ :=
    ⟨Cardinal.mk ι, by
      -- Compare the shrink index cardinal with the original subobject cardinal bound after lifting.
      have hι :
          Cardinal.lift.{max u v} (Cardinal.mk ι) =
            Cardinal.lift.{w} (Cardinal.mk (Subobject M)) :=
        Cardinal.lift_mk_eq'.2 ⟨(equivShrink (Subobject M)).symm⟩
      have hM' :
          Cardinal.lift.{max u v} (Cardinal.mk ι) ≤ Cardinal.lift.{w} κ :=
        hι.trans_le hM
      exact le_sSup hM'⟩
  let e :
      (∐ fun _ : c.1.out ↦ separator C) ≅
        (∐ fun _ : ι ↦ separator C) :=
    Limits.Sigma.reindex Cardinal.outMkEquiv (fun _ : ι ↦ separator C)
  let f' : (∐ fun _ : c.1.out ↦ separator C) ⟶ M := e.hom ≫ f
  have hf' : Epi f' := by
    dsimp [f']
    infer_instance
  -- Reuse the generic epi-to-kernel-cokernel classification for this chosen bounded source.
  simpa [bounded_separator_cokernel_property, c] using
    (mem_isoClosure_indexed_cokernel_subobject_property_of_epi
      (C := C) (a := c)
      (S := fun c : bounded_lift_cardinal κ ↦ ∐ fun _ : c.1.out ↦ separator C)
      (M := M) f')

/-- The object property `M ↦ Cardinal.mk (Subobject M) ≤ κ` is essentially small. -/
instance subobjectCardinalLE_essentiallySmall (κ : Cardinal.{max u v}) :
    ObjectProperty.EssentiallySmall.{w}
      (fun M : C ↦ Cardinal.mk (Subobject M) ≤ κ) := by
  let Q : ObjectProperty C :=
    bounded_separator_cokernel_property (C := C) κ
  letI : ObjectProperty.Small.{w} Q := by
    -- The witness property is small because the bounded-cardinal index family is `w`-small.
    simpa [Q] using
      bounded_separator_cokernel_property_small (C := C) κ
  refine ⟨⟨Q, inferInstance, ?_⟩⟩
  intro M hM
  have hM' :
      Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤ Cardinal.lift.{w} κ :=
    Cardinal.lift_le.2 hM
  -- Every bounded object is presented by one of the bounded-cardinal separator coproducts.
  simpa [Q] using
    mem_isoClosure_bounded_separator_cokernel_property
      (C := C) (M := M) (κ := κ) hM'

variable (κ : Cardinal.{max u v})

/- Lemma 19.11.4 (2): for every cardinal `κ`, the full subcategory of objects `M` with
`|M| = #(Subobject M) ≤ κ` is essentially small. This is the canonical full-subcategory instance
attached to `subobjectCardinalLE_essentiallySmall κ`. -/
/-- Lemma 19.11.4 (2): for every cardinal `κ`, the full subcategory of objects whose subobject
cardinal is at most `κ` is essentially small. -/
theorem boundedSubobjectFullSubcategoryEssentiallySmall :
    EssentiallySmall.{w}
      (ObjectProperty.FullSubcategory (fun M : C ↦ Cardinal.mk (Subobject M) ≤ κ)) := by
  -- The full subcategory inherits essential smallness from the packaged object property instance.
  infer_instance

end CategoryTheory
