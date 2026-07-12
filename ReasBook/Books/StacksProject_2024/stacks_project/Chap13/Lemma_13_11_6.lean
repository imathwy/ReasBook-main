import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Lemma_13_10_5
import StacksProject_2024.Chap13.Lemma_13_6_2
import StacksProject_2024.Chap13.Lemma_13_6_11
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_11_2
import StacksProject_2024.Chap13.Lemma_13_11_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 13.11.6:
- primary domain: derived-category localization of bounded homotopy categories by
  quasi-isomorphisms;
- sampled owner declarations:
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.lift`,
  `DerivedCategory.Qh`,
  `Functor.kernel`;
- best owner abstraction: the ambient owners are the unbounded quasi-isomorphism morphism
  property `HomotopyCategory.quasiIso 𝒜 (up ℤ)` and the acyclic triangulated subcategory
  `HomotopyCategory.subcategoryAcyclic 𝒜`; on the bounded categories, the source-facing objects
  are their inverse-image/restricted views along the inclusion `ObjectProperty.ι`.
- primitive vs. derived API: the primitive data are the bounded homotopy object properties from
  `Definition_13_8_1`, the canonical quotient functor `DerivedCategory.Qh`, and the ambient
  quasi-isomorphism / acyclic owners. The bounded localization functors and their kernel /
  localization statements are the derived bridge/view layer.
- source/core/bridge triage:
  `source-facing`: `Qis⁺(𝒜)`, `Qis⁻(𝒜)`, `Qisᵇ(𝒜)`, the bounded derived functors, and the nine
    localization statements of Lemma 13.11.6;
  `core/canonical`: `HomotopyCategory.quasiIso 𝒜 (up ℤ)`,
    `HomotopyCategory.subcategoryAcyclic 𝒜`, `DerivedCategory.Qh`, and `Functor.kernel`;
  `bridge/view`: inverse images to `K⁺(𝒜)`, `K⁻(𝒜)`, `Kᵇ(𝒜)` and the induced functors
    `K^*(𝒜) ⥤ D^*(𝒜)`.

The bounded quasi-isomorphism morphism properties are high-frequency bridge owners used downstream,
so they remain named here. The bounded acyclic object properties are only the direct inverse-image
views of `HomotopyCategory.subcategoryAcyclic 𝒜`, so this file uses source-facing notation for
them rather than introducing a second public owner layer. -/

/- Reuse the Chapter 13 boundedness owners on cochain complexes and their homotopy categories from
`Definition_13_8_1` and the bounded derived-category owners from `Definition_13_11_3`; this file
adds localization results on top of that canonical API rather than redeclaring parallel
bounded-derived notions. -/

/-- The quasi-isomorphisms in `K^+(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedBelowHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁺(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.plus 𝒜).ι

/-- The quasi-isomorphisms in `K^-(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedAboveHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁻(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.minus 𝒜).ι

/-- The quasi-isomorphisms in `K^b(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (Kᵇ(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (HomotopyCategory.bounded 𝒜).ι

scoped notation "Qis⁺(" A:arg ")" => boundedBelowHomotopyQuasiIso A
scoped notation "Qis⁻(" A:arg ")" => boundedAboveHomotopyQuasiIso A
scoped notation "Qisᵇ(" A:arg ")" => boundedHomotopyQuasiIso A

scoped notation "Ac⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.plus A))
scoped notation "Ac⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.minus A))
scoped notation "Acᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (HomotopyCategory.bounded A))

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-below homotopy objects
to bounded-below derived objects, via the canonical owner `DerivedCategory.IsGE`. -/
theorem qh_obj_mem_t_plus
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hK : CochainComplex.plus 𝒜 K := by
    simpa [K, HomotopyCategory.plus] using X.property
  rcases hK with ⟨n, hn⟩
  letI : K.IsStrictlyGE n := by simpa [K] using hn
  letI : K.IsGE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app K
  have hQ : (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsGE n
    exact (DerivedCategory.isGE_Q_obj_iff K n).2 inferInstance
  exact (t.plus : ObjectProperty (D(𝒜))).prop_of_iso e.symm hQ

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-above homotopy objects
to bounded-above derived objects, via the canonical owner `DerivedCategory.IsLE`. -/
theorem qh_obj_mem_t_minus
    (X : K⁻(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  let K : CochainComplex 𝒜 ℤ := X.obj.as
  have hK : CochainComplex.minus 𝒜 K := by
    simpa [K, HomotopyCategory.minus] using X.property
  rcases hK with ⟨n, hn⟩
  letI : K.IsStrictlyLE n := by simpa [K] using hn
  letI : K.IsLE n := inferInstance
  let e : DerivedCategory.Qh.obj X.obj ≅ DerivedCategory.Q.obj K := by
    simpa [K, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app K
  have hQ : (t.minus : ObjectProperty (D(𝒜))) (DerivedCategory.Q.obj K) := by
    refine ⟨n, ?_⟩
    change (DerivedCategory.Q.obj K).IsLE n
    exact (DerivedCategory.isLE_Q_obj_iff K n).2 inferInstance
  exact (t.minus : ObjectProperty (D(𝒜))).prop_of_iso e.symm hQ

-- Proof sketch: a bounded complex has cohomology vanishing outside a finite interval, and the
-- identity functor sends bounded complexes to the same derived objects, so both the bounded-below
-- and bounded-above vanishing conditions hold in the image.
/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded homotopy objects to
bounded derived objects. -/
theorem qh_obj_mem_t_bounded
    (X : Kᵇ(𝒜)) :
    (t.bounded : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := by
  -- Split boundedness of the representing complex into lower and upper support bounds.
  have hX : CochainComplex.bounded 𝒜 X.obj.as := by
    simpa [HomotopyCategory.bounded] using X.property
  rcases hX with ⟨hplus, hminus⟩
  rw [derivedCategory_t_bounded_iff]
  constructor
  ·
    let Xplus : K⁺(𝒜) :=
      ⟨X.obj, (HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).2 hplus⟩
    -- Reuse the bounded-below bridge on the same underlying homotopy object.
    have hPlus : (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj X.obj) := by
      change (t.plus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj Xplus.obj)
      exact qh_obj_mem_t_plus (𝒜 := 𝒜) Xplus
    exact (derivedCategory_t_plus_iff (𝒜 := 𝒜) (DerivedCategory.Qh.obj X.obj)).1 hPlus
  ·
    let Xminus : K⁻(𝒜) :=
      ⟨X.obj, (HomotopyCategory.minus_iff (𝒜 := 𝒜) X.obj).2 hminus⟩
    -- Reuse the bounded-above bridge on the same underlying homotopy object.
    have hMinus : (t.minus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj X.obj) := by
      change (t.minus : ObjectProperty (D(𝒜))) (DerivedCategory.Qh.obj Xminus.obj)
      exact qh_obj_mem_t_minus (𝒜 := 𝒜) Xminus
    exact (derivedCategory_t_minus_iff (𝒜 := 𝒜) (DerivedCategory.Qh.obj X.obj)).1 hMinus

/-- The canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
abbrev mapBoundedBelowHomotopyToDerivedBelow
    :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  (t.plus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_plus

/-- The canonical functor `K^-(\mathcal A) ⟶ D^-(\mathcal A)`. -/
abbrev mapBoundedAboveHomotopyToDerivedAbove
    :
    K⁻(𝒜) ⥤ D⁻(𝒜) :=
  (t.minus : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_minus

/-- The canonical functor `K^b(\mathcal A) ⟶ D^b(\mathcal A)`. -/
abbrev mapBoundedHomotopyToDerivedBounded
    :
    Kᵇ(𝒜) ⥤ Dᵇ(𝒜) :=
  (t.bounded : ObjectProperty (D(𝒜))).lift
    ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
    qh_obj_mem_t_bounded

namespace Functor

/-- If `Q : C ⥤ D` is essentially surjective and `F.map` is surjective on morphisms between
objects in the image of `Q`, then `F` is full. -/
theorem full_of_comp_essSurj
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) (Q : C ⥤ D) [Q.EssSurj]
    (h :
      ∀ {X Y : C},
        Function.Surjective
          (fun f : Q.obj X ⟶ Q.obj Y => F.map f)) :
    F.Full := by
  sorry

/-- If `Q : C ⥤ D` is essentially surjective and `F.map` is injective on morphisms between
objects in the image of `Q`, then `F` is faithful. -/
theorem faithful_of_comp_essSurj
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) (Q : C ⥤ D) [Q.EssSurj]
    (h :
      ∀ (X Y : C),
        Function.Injective
          (fun f : Q.obj X ⟶ Q.obj Y => F.map f)) :
    F.Faithful := by
  sorry

end Functor

/-- Helper for Lemma 13.11.6: any quasi-isomorphism out of a bounded-below object in
`K(\mathcal A)` can be refined so that the target is again bounded below. -/
lemma quasiIso_to_bounded_below_refinement
    (X : K⁺(𝒜)) {Y : K(𝒜)} (s : X.obj ⟶ Y)
    (hs : HomotopyCategory.quasiIso 𝒜 (up ℤ) s) :
    ∃ (Y' : K⁺(𝒜)) (t : Y ⟶ Y'.obj), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  -- Proof comment: the source bound on `X` forces eventual homology vanishing on `Y`, so
  -- Lemma 13.11.5 supplies a bounded-below truncation quasi-isomorphic to `Y`.
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨a, hXge⟩ :=
    (CochainComplex.plus_iff 𝒜 X.obj.as).1
      ((HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).1 X.property)
  have hYeventual : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (Y.as.homology n) := by
    refine ⟨a, ?_⟩
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := X.obj.as
    let _ : KX.IsStrictlyGE a := by
      simpa [KX] using hXge
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isGE (K := KX) a n hn
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj X.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y)) := by
      exact IsZero.of_iso hXhomotopy
        ((asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s)).symm)
    let KY : CochainComplex 𝒜 ℤ := Y.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  obtain ⟨a, hπ, htrunc⟩ :=
    exists_quasiIso_to_truncGE_of_eventually_isZero_homology (K := Y.as) hYeventual
  let Y' : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := Y.as) a), by
      -- Proof comment: the truncation bound gives the bounded-below structure on the refined
      -- target.
      rw [HomotopyCategory.plus_iff]
      exact (CochainComplex.plus_iff 𝒜 _).2 ⟨a, htrunc⟩⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: pass the truncation map to the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.πTruncGE (K := Y.as) a)
  · -- Proof comment: the truncation map is a quasi-isomorphism by construction.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.πTruncGE (K := Y.as) a)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hπ)

/-- Helper for Lemma 13.11.6: any quasi-isomorphism into a bounded-above object in
`K(\mathcal A)` can be refined so that the source is again bounded above. -/
lemma quasiIso_from_bounded_above_refinement
    (X : K⁻(𝒜)) {Y : K(𝒜)} (s : Y ⟶ X.obj)
    (hs : HomotopyCategory.quasiIso 𝒜 (up ℤ) s) :
    ∃ (Y' : K⁻(𝒜)) (t : Y'.obj ⟶ Y), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  -- Proof comment: this is the dual truncation argument, using eventual high-degree vanishing on
  -- `Y` inherited from the bounded-above source `X`.
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨b, hXle⟩ :=
    (CochainComplex.minus_iff 𝒜 X.obj.as).1
      ((HomotopyCategory.minus_iff (𝒜 := 𝒜) X.obj).1 X.property)
  have hYeventual : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (Y.as.homology n) := by
    refine ⟨b, ?_⟩
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := X.obj.as
    let _ : KX.IsStrictlyLE b := by
      simpa [KX] using hXle
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isLE (K := KX) b n hn
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj X.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y)) := by
      exact IsZero.of_iso hXhomotopy
        (asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s))
    let KY : CochainComplex 𝒜 ℤ := Y.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  obtain ⟨b, hι, htrunc⟩ :=
    exists_quasiIso_from_truncLE_of_eventually_isZero_homology (K := Y.as) hYeventual
  let Y' : K⁻(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncLE (K := Y.as) b), by
      -- Proof comment: the truncation bound gives the bounded-above structure on the refined
      -- source.
      rw [HomotopyCategory.minus_iff]
      exact (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htrunc⟩⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: pass the truncation inclusion to the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.ιTruncLE (K := Y.as) b)
  · -- Proof comment: the truncation inclusion is a quasi-isomorphism by construction.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.ιTruncLE (K := Y.as) b)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hι)

-- Proof sketch: identify quasi-isomorphisms in the ambient homotopy category with the Verdier
-- morphism property of the acyclic subcategory, then restrict along the inclusion
-- `K^{+}(\mathcal A) ⥤ K(\mathcal A)`.
/-- Lemma 13.11.6 (1): the saturated multiplicative system corresponding to
`Ac^{+}(\mathcal A)` is precisely `Qis^{+}(\mathcal A)`. -/
theorem boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁺(𝒜)).trW =
      Qis⁺(𝒜) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedBelowHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

-- Proof sketch: an object of `K^{+}(\mathcal A)` maps to zero in `D^{+}(\mathcal A)` exactly
-- when its image in the unbounded derived category is acyclic, which is the defining condition of
-- `Ac^{+}(\mathcal A)`.
/-- Lemma 13.11.6 (2): the kernel of `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` is
`Ac^{+}(\mathcal A)`. -/
theorem kernel_mapBoundedBelowHomotopyToDerivedBelow_eq_acyclic
    :
    Functor.kernel mapBoundedBelowHomotopyToDerivedBelow =
      Ac⁺(𝒜) := by
  -- Compare the bounded-below lift with the ambient quotient functor on underlying derived objects.
  ext X
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  let e :
      ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.plus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_plus).app X
  constructor
  · intro hX
    have hUnderlying : IsZero (ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X)) :=
      ιplus.map_isZero hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := e.isZero_iff.1 hUnderlying
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := hQh
    rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)] at hker
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hker
  · intro hX
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := by
      rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := hker
    have hUnderlying : IsZero (ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X)) :=
      e.isZero_iff.2 hQh
    exact IsZero.of_full_of_faithful_of_isZero ιplus _ hUnderlying

/-- Helper for Lemma 13.11.6: the bounded-below derived functor inverts the Verdier morphism
property attached to the bounded-below acyclic subcategory. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁺(𝒜)).trW)
      mapBoundedBelowHomotopyToDerivedBelow := by
  intro X Y f hf
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  have hQis : Qis⁺(𝒜) f := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
    -- unbounded derived localization inverting a quasi-isomorphism.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.plus 𝒜).ι.map f)
      (by simpa [boundedBelowHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := by
    -- Proof comment: the lift-to-inclusion comparison transports invertibility back to `D⁺`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_plus)
        f)).2 hUnderlying
  let _ : IsIso (ιplus.map (mapBoundedBelowHomotopyToDerivedBelow.map f)) := hLifted
  exact isIso_of_fully_faithful ιplus (mapBoundedBelowHomotopyToDerivedBelow.map f)

/-- Helper for Lemma 13.11.6: a chosen cochain-level preimage of a bounded-below derived object
has vanishing homology in sufficiently negative degrees. -/
theorem boundedBelow_objPreimage_eventually_isZero_homology
    (X : D⁺(𝒜)) :
    ∃ a : ℤ, ∀ i < a, IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := by
  -- Proof comment: transfer the bounded-below vanishing of `X` along the canonical preimage
  -- isomorphism in the ambient derived category.
  obtain ⟨a, ha⟩ := (derivedCategory_t_plus_iff (K := X.obj)).1 X.property
  refine ⟨a, ?_⟩
  intro i hi
  have hXi : IsZero ((H^i).obj X.obj) := ha i hi
  have hQpreimage :
      IsZero
        ((H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj))) := by
    let e :
        (H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj)) ≅
          (H^i).obj X.obj :=
      (H^i).mapIso (DerivedCategory.Q.objObjPreimageIso X.obj)
    exact (e.isZero_iff).2 hXi
  exact
    (((DerivedCategory.homologyFunctorFactors 𝒜 i).app
      (DerivedCategory.Q.objPreimage X.obj)).isZero_iff).1 hQpreimage

/-- Helper for Lemma 13.11.6: every bounded-below derived object admits a bounded-below homotopy
representative. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_essSurj
    :
    (mapBoundedBelowHomotopyToDerivedBelow (𝒜 := 𝒜)).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let K : CochainComplex 𝒜 ℤ := DerivedCategory.Q.objPreimage Y.obj
  obtain ⟨a, hK⟩ := boundedBelow_objPreimage_eventually_isZero_homology (𝒜 := 𝒜) Y
  obtain ⟨a, hπ, htrunc⟩ :=
    exists_quasiIso_to_truncGE_of_eventually_isZero_homology (K := K) ⟨a, hK⟩
  let X : K⁺(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := K) a), by
      -- Proof comment: Lemma 13.11.5 produces a lower truncation which is bounded below.
      rw [HomotopyCategory.plus_iff]
      exact (CochainComplex.plus_iff 𝒜 _).2 ⟨a, htrunc⟩⟩
  let ιplus : D⁺(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
  let eplus :
      ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.plus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.plus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_plus).app X
  let eQh :
      DerivedCategory.Qh.obj X.obj ≅
        DerivedCategory.Q.obj (CochainComplex.truncGE (K := K) a) := by
    simpa [X, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app (CochainComplex.truncGE (K := K) a)
  have hQπ : IsIso (DerivedCategory.Q.map (CochainComplex.πTruncGE (K := K) a)) := by
    -- Proof comment: the truncation map is a quasi-isomorphism, hence an isomorphism in `D(𝒜)`.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hπ
  let eAmbient :
      ιplus.obj (mapBoundedBelowHomotopyToDerivedBelow.obj X) ≅ Y.obj :=
    eplus ≪≫ eQh ≪≫
      (asIso (DerivedCategory.Q.map (CochainComplex.πTruncGE (K := K) a))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso Y.obj
  let hFF :
      ιplus.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιplus
  exact ⟨X, ⟨hFF.preimageIso eAmbient⟩⟩

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-below
localization model to `D^{+}(\mathcal A)`. -/
noncomputable abbrev boundedBelowLocalizationComparisonFunctor :
    ((Ac⁺(𝒜)).trW).Localization ⥤ D⁺(𝒜) :=
  Localization.lift mapBoundedBelowHomotopyToDerivedBelow
    mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
    ((Ac⁺(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: the bounded-below comparison functor is essentially surjective. -/
theorem boundedBelow_localization_comparison_essSurj
    :
    (boundedBelowLocalizationComparisonFunctor (𝒜 := 𝒜)).EssSurj := by
  let E := boundedBelowLocalizationComparisonFunctor (𝒜 := 𝒜)
  let hEss :
      mapBoundedBelowHomotopyToDerivedBelow.EssSurj :=
    mapBoundedBelowHomotopyToDerivedBelow_essSurj (𝒜 := 𝒜)
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X, ⟨eX⟩⟩ := hEss.mem_essImage Y
  refine ⟨((Ac⁺(𝒜)).trW).Q.obj X, ⟨?_⟩⟩
  -- Proof comment: compare `E` with `mapBoundedBelowHomotopyToDerivedBelow` on an actual
  -- bounded-below complex and then reuse the chosen representative of `Y`.
  let eFac :
      E.obj (((Ac⁺(𝒜)).trW).Q.obj X) ≅
        mapBoundedBelowHomotopyToDerivedBelow.obj X :=
    (Localization.fac mapBoundedBelowHomotopyToDerivedBelow
      mapBoundedBelowHomotopyToDerivedBelow_inverts_acyclic_trW
      ((Ac⁺(𝒜)).trW).Q).app X
  exact eFac ≪≫ eX

/-- Helper for Lemma 13.11.6: the ambient bounded-below derived functor
`K^{+}(\mathcal A) ⟶ D(\mathcal A)` inverts the Verdier morphism property attached to
`Ac^{+}(\mathcal A)`. -/
theorem mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁺(𝒜)).trW)
      (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh) := by
  intro X Y f hf
  have hQis : Qis⁺(𝒜) f := by
    simpa [boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
  -- unbounded derived localization inverting a quasi-isomorphism.
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.plus 𝒜).ι.map f))
  exact Localization.inverts
    (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))
    ((HomotopyCategory.plus 𝒜).ι.map f)
    (by simpa [boundedBelowHomotopyQuasiIso] using hQis)

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-below
localization model to the ambient derived category `D(\mathcal A)`. -/
noncomputable abbrev boundedBelowAmbientLocalizationComparisonFunctor :
    ((Ac⁺(𝒜)).trW).Localization ⥤ D(𝒜) :=
  Localization.lift
    (((HomotopyCategory.plus 𝒜).ι) ⋙ DerivedCategory.Qh)
    mapBoundedBelowHomotopyToDerived_inverts_acyclic_trW
    ((Ac⁺(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: every ambient derived morphism between bounded-below homotopy
objects is represented by a left fraction whose denominator still lies in `K^{+}(\mathcal A)`. -/
theorem boundedBelow_ambient_localization_comparison_surjective_on_Q_obj_hom
    (X Y : K⁺(𝒜)) :
    Function.Surjective
      (fun g : (((Ac⁺(𝒜)).trW).Q.obj X ⟶ ((Ac⁺(𝒜)).trW).Q.obj Y) =>
        (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  sorry

/-- Helper for Lemma 13.11.6: if two bounded-below roofs have the same image in the ambient
derived category, then they already agree in the bounded-below localization. -/
theorem boundedBelow_ambient_localization_comparison_injective_on_Q_obj_hom
    (X Y : K⁺(𝒜)) :
    Function.Injective
      (fun g : (((Ac⁺(𝒜)).trW).Q.obj X ⟶ ((Ac⁺(𝒜)).trW).Q.obj Y) =>
        (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  sorry

/-- Helper for Lemma 13.11.6: the comparison from the bounded-below localization model to the
ambient derived category is fully faithful. -/
theorem boundedBelow_ambient_localization_comparison_fullyFaithful :
    Nonempty (boundedBelowAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).FullyFaithful := by
  sorry

-- Proof sketch: Lemma 13.11.5 makes the bounded-below quasi-isomorphisms cofinal in the ambient
-- derived-category localization, so the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)`
-- satisfies the universal property of localization at `Qis^{+}(\mathcal A)`.
/-- Lemma 13.11.6 (3): the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` realizes
`D^{+}(\mathcal A)` as the localization of `K^{+}(\mathcal A)` at `Qis^{+}(\mathcal A)`. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_isLocalization
    :
    Functor.IsLocalization
      mapBoundedBelowHomotopyToDerivedBelow
      (Qis⁺(𝒜)) := by
  sorry

/-- The bounded-below homotopy-to-derived functor carries the canonical localization instance at
`Qis^+(\mathcal A)`. -/
instance boundedBelowHomotopyToDerived_isLocalization :
    Functor.IsLocalization
      mapBoundedBelowHomotopyToDerivedBelow
      (Qis⁺(𝒜)) :=
  mapBoundedBelowHomotopyToDerivedBelow_isLocalization

-- Proof sketch: use the unbounded identification between quasi-isomorphisms and the Verdier
-- morphism property of acyclic complexes, then restrict it to the bounded-above full subcategory.
/-- Lemma 13.11.6 (4): the saturated multiplicative system corresponding to
`Ac^{-}(\mathcal A)` is precisely `Qis^{-}(\mathcal A)`. -/
theorem boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁻(𝒜)).trW =
      Qis⁻(𝒜) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedAboveHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

-- Proof sketch: bounded-above objects die in `D^{-}(\mathcal A)` exactly when their image in the
-- unbounded derived category is acyclic, giving the same kernel criterion as in the bounded-below
-- case.
/-- Lemma 13.11.6 (5): the kernel of `K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` is
`Ac^{-}(\mathcal A)`. -/
theorem kernel_mapBoundedAboveHomotopyToDerivedAbove_eq_acyclic
    :
    Functor.kernel mapBoundedAboveHomotopyToDerivedAbove =
      Ac⁻(𝒜) := by
  -- Compare the bounded-above lift with the ambient quotient functor on underlying derived objects.
  ext X
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let e :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_minus).app X
  constructor
  · intro hX
    have hUnderlying : IsZero (ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X)) :=
      ιminus.map_isZero hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := e.isZero_iff.1 hUnderlying
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := hQh
    rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)] at hker
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hker
  · intro hX
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := by
      rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := hker
    have hUnderlying : IsZero (ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X)) :=
      e.isZero_iff.2 hQh
    exact IsZero.of_full_of_faithful_of_isZero ιminus _ hUnderlying

/-- Helper for Lemma 13.11.6: the bounded-above derived functor inverts the Verdier morphism
property attached to the bounded-above acyclic subcategory. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁻(𝒜)).trW)
      mapBoundedAboveHomotopyToDerivedAbove := by
  intro X Y f hf
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  have hQis : Qis⁻(𝒜) f := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
    -- unbounded derived localization inverting a quasi-isomorphism.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.minus 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.minus 𝒜).ι.map f)
      (by simpa [boundedAboveHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := by
    -- Proof comment: the lift-to-inclusion comparison transports invertibility back to `D⁻`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_minus)
        f)).2 hUnderlying
  let _ : IsIso (ιminus.map (mapBoundedAboveHomotopyToDerivedAbove.map f)) := hLifted
  exact isIso_of_fully_faithful ιminus (mapBoundedAboveHomotopyToDerivedAbove.map f)

/-- Helper for Lemma 13.11.6: a chosen cochain-level preimage of a bounded-above derived object
has vanishing homology in sufficiently large degrees. -/
theorem boundedAbove_objPreimage_eventually_isZero_homology
    (X : D⁻(𝒜)) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((DerivedCategory.Q.objPreimage X.obj).homology i) := by
  -- Proof comment: transfer the bounded-above vanishing of `X` along the canonical preimage
  -- isomorphism in the ambient derived category.
  obtain ⟨b, hb⟩ := (derivedCategory_t_minus_iff (K := X.obj)).1 X.property
  refine ⟨b, ?_⟩
  intro i hi
  have hXi : IsZero ((H^i).obj X.obj) := hb i hi
  have hQpreimage :
      IsZero
        ((H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj))) := by
    let e :
        (H^i).obj (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X.obj)) ≅
          (H^i).obj X.obj :=
      (H^i).mapIso (DerivedCategory.Q.objObjPreimageIso X.obj)
    exact (e.isZero_iff).2 hXi
  exact
    (((DerivedCategory.homologyFunctorFactors 𝒜 i).app
      (DerivedCategory.Q.objPreimage X.obj)).isZero_iff).1 hQpreimage

/-- Helper for Lemma 13.11.6: every bounded-above derived object admits a bounded-above homotopy
representative. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_essSurj
    :
    (mapBoundedAboveHomotopyToDerivedAbove (𝒜 := 𝒜)).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  let K : CochainComplex 𝒜 ℤ := DerivedCategory.Q.objPreimage Y.obj
  obtain ⟨b, hK⟩ := boundedAbove_objPreimage_eventually_isZero_homology (𝒜 := 𝒜) Y
  obtain ⟨b, hι, htrunc⟩ :=
    exists_quasiIso_from_truncLE_of_eventually_isZero_homology (K := K) ⟨b, hK⟩
  let X : K⁻(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncLE (K := K) b), by
      rw [HomotopyCategory.minus_iff]
      exact (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htrunc⟩⟩
  let ιminus : D⁻(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.minus : ObjectProperty (D(𝒜)))
  let eminus :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.minus : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.minus 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_minus).app X
  let eQh :
      DerivedCategory.Qh.obj X.obj ≅
        DerivedCategory.Q.obj (CochainComplex.truncLE (K := K) b) := by
    simpa [X, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso 𝒜).app (CochainComplex.truncLE (K := K) b)
  have hQι : IsIso (DerivedCategory.Q.map (CochainComplex.ιTruncLE (K := K) b)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hι
  let eAmbient :
      ιminus.obj (mapBoundedAboveHomotopyToDerivedAbove.obj X) ≅ Y.obj :=
    eminus ≪≫ eQh ≪≫
      asIso (DerivedCategory.Q.map (CochainComplex.ιTruncLE (K := K) b)) ≪≫
        DerivedCategory.Q.objObjPreimageIso Y.obj
  let hFF :
      ιminus.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful ιminus
  exact ⟨X, ⟨hFF.preimageIso eAmbient⟩⟩

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-above
localization model to `D^{-}(\mathcal A)`. -/
noncomputable abbrev boundedAboveLocalizationComparisonFunctor :
    ((Ac⁻(𝒜)).trW).Localization ⥤ D⁻(𝒜) :=
  Localization.lift mapBoundedAboveHomotopyToDerivedAbove
    mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
    ((Ac⁻(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: the bounded-above comparison functor is essentially surjective. -/
theorem boundedAbove_localization_comparison_essSurj
    :
    (boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)).EssSurj := by
  let F := boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)
  let hEss :
      mapBoundedAboveHomotopyToDerivedAbove.EssSurj :=
    mapBoundedAboveHomotopyToDerivedAbove_essSurj (𝒜 := 𝒜)
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨X, ⟨eX⟩⟩ := hEss.mem_essImage Y
  refine ⟨((Ac⁻(𝒜)).trW).Q.obj X, ⟨?_⟩⟩
  let eFac :
      F.obj (((Ac⁻(𝒜)).trW).Q.obj X) ≅
        mapBoundedAboveHomotopyToDerivedAbove.obj X :=
    (Localization.fac mapBoundedAboveHomotopyToDerivedAbove
      mapBoundedAboveHomotopyToDerivedAbove_inverts_acyclic_trW
      ((Ac⁻(𝒜)).trW).Q).app X
  exact eFac ≪≫ eX

/-- Helper for Lemma 13.11.6: the ambient bounded-above derived functor
`K^{-}(\mathcal A) ⟶ D(\mathcal A)` inverts the Verdier morphism property attached to
`Ac^{-}(\mathcal A)`. -/
theorem mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Ac⁻(𝒜)).trW)
      (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh) := by
  intro X Y f hf
  have hQis : Qis⁻(𝒜) f := by
    simpa [boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.minus 𝒜).ι.map f))
  exact Localization.inverts
    (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
    (HomotopyCategory.quasiIso 𝒜 (up ℤ))
    ((HomotopyCategory.minus 𝒜).ι.map f)
    (by simpa [boundedAboveHomotopyQuasiIso] using hQis)

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded-above
localization model to the ambient derived category `D(\mathcal A)`. -/
noncomputable abbrev boundedAboveAmbientLocalizationComparisonFunctor :
    ((Ac⁻(𝒜)).trW).Localization ⥤ D(𝒜) :=
  Localization.lift
    (((HomotopyCategory.minus 𝒜).ι) ⋙ DerivedCategory.Qh)
    mapBoundedAboveHomotopyToDerived_inverts_acyclic_trW
    ((Ac⁻(𝒜)).trW).Q

/-- Helper for Lemma 13.11.6: every ambient derived morphism between bounded-above homotopy
objects is represented by a right fraction whose source still lies in `K^{-}(\mathcal A)`. -/
theorem boundedAbove_ambient_localization_comparison_surjective_on_Q_obj_hom
    (X Y : K⁻(𝒜)) :
    Function.Surjective
      (fun g : (((Ac⁻(𝒜)).trW).Q.obj X ⟶ ((Ac⁻(𝒜)).trW).Q.obj Y) =>
        (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  sorry

/-- Helper for Lemma 13.11.6: if two bounded-above roofs have the same image in the ambient
derived category, then they already agree in the bounded-above localization. -/
theorem boundedAbove_ambient_localization_comparison_injective_on_Q_obj_hom
    (X Y : K⁻(𝒜)) :
    Function.Injective
      (fun g : (((Ac⁻(𝒜)).trW).Q.obj X ⟶ ((Ac⁻(𝒜)).trW).Q.obj Y) =>
        (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).map g) := by
  sorry

/-- Helper for Lemma 13.11.6: the comparison from the bounded-above localization model to the
ambient derived category is fully faithful. -/
theorem boundedAbove_ambient_localization_comparison_fullyFaithful :
    Nonempty (boundedAboveAmbientLocalizationComparisonFunctor (𝒜 := 𝒜)).FullyFaithful := by
  sorry

-- Proof sketch: Lemma 13.11.5 yields bounded-above representatives for the denominators in the
-- ambient localization, so the bounded-above functor has the universal property of localization at
-- `Qis^{-}(\mathcal A)`.
/-- Lemma 13.11.6 (6): the canonical functor `K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` realizes
`D^{-}(\mathcal A)` as the localization of `K^{-}(\mathcal A)` at `Qis^{-}(\mathcal A)`. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_isLocalization
    :
    Functor.IsLocalization
      mapBoundedAboveHomotopyToDerivedAbove
      (Qis⁻(𝒜)) := by
  sorry

-- Proof sketch: identify quasi-isomorphisms with the Verdier morphism property of acyclic
-- complexes in the ambient homotopy category and restrict to the bounded full subcategory.
/-- Lemma 13.11.6 (7): the saturated multiplicative system corresponding to
`Ac^{b}(\mathcal A)` is precisely `Qis^{b}(\mathcal A)`. -/
theorem boundedAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Acᵇ(𝒜)).trW =
      Qisᵇ(𝒜) := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff]
  simp [boundedHomotopyQuasiIso, HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]

-- Proof sketch: a bounded homotopy object becomes zero in `D^{b}(\mathcal A)` exactly when its
-- image in `D(\mathcal A)` is acyclic, so the kernel is the bounded acyclic subcategory.
/-- Lemma 13.11.6 (8): the kernel of `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` is
`Ac^{b}(\mathcal A)`. -/
theorem kernel_mapBoundedHomotopyToDerivedBounded_eq_acyclic
    :
    Functor.kernel mapBoundedHomotopyToDerivedBounded =
      Acᵇ(𝒜) := by
  -- Compare the bounded lift with the ambient quotient functor on underlying derived objects.
  ext X
  let ιbounded : Dᵇ(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.bounded : ObjectProperty (D(𝒜)))
  let e :
      ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj X) ≅
        DerivedCategory.Qh.obj X.obj :=
    (ObjectProperty.liftCompιIso
      (t.bounded : ObjectProperty (D(𝒜)))
      ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
      qh_obj_mem_t_bounded).app X
  constructor
  · intro hX
    have hUnderlying : IsZero (ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj X)) :=
      ιbounded.map_isZero hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := e.isZero_iff.1 hUnderlying
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := hQh
    rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)] at hker
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hker
  · intro hX
    have hker : Functor.kernel (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜)) X.obj := by
      rw [subcategoryAcyclic_kernel_Qh (A := 𝒜)]
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hX
    have hQh : IsZero (DerivedCategory.Qh.obj X.obj) := hker
    have hUnderlying : IsZero (ιbounded.obj (mapBoundedHomotopyToDerivedBounded.obj X)) :=
      e.isZero_iff.2 hQh
    exact IsZero.of_full_of_faithful_of_isZero ιbounded _ hUnderlying

/-- Helper for Lemma 13.11.6: the bounded derived functor inverts the Verdier morphism property
attached to the bounded acyclic subcategory. -/
theorem mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Acᵇ(𝒜)).trW)
      mapBoundedHomotopyToDerivedBounded := by
  intro X Y f hf
  let ιbounded : Dᵇ(𝒜) ⥤ D(𝒜) := ObjectProperty.ι (t.bounded : ObjectProperty (D(𝒜)))
  have hQis : Qisᵇ(𝒜) f := by
    simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hf
  have hUnderlying :
      IsIso (((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh).map f) := by
    -- Proof comment: after forgetting to the ambient homotopy category, this is exactly the
    -- unbounded derived localization inverting a quasi-isomorphism.
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.bounded 𝒜).ι.map f))
    exact Localization.inverts
      (DerivedCategory.Qh : K(𝒜) ⥤ D(𝒜))
      (HomotopyCategory.quasiIso 𝒜 (up ℤ))
      ((HomotopyCategory.bounded 𝒜).ι.map f)
      (by simpa [boundedHomotopyQuasiIso] using hQis)
  have hLifted :
      IsIso (ιbounded.map (mapBoundedHomotopyToDerivedBounded.map f)) := by
    -- Proof comment: the lift-to-inclusion comparison transports invertibility back to `Dᵇ`.
    exact
      ((NatIso.isIso_map_iff
        (ObjectProperty.liftCompιIso
          (t.bounded : ObjectProperty (D(𝒜)))
          ((HomotopyCategory.bounded 𝒜).ι ⋙ DerivedCategory.Qh)
          qh_obj_mem_t_bounded)
        f)).2 hUnderlying
  let _ : IsIso (ιbounded.map (mapBoundedHomotopyToDerivedBounded.map f)) := hLifted
  exact isIso_of_fully_faithful ιbounded (mapBoundedHomotopyToDerivedBounded.map f)

/- Proof sketch: apply the bounded-below refinement argument to the quasi-isomorphism
`s : X ⟶ Y`, but keep track of the ambient bounded-above hypothesis on `Y`; the lower truncation
produced there is a truncation of `Y.as`, so it remains bounded above as well. -/
/-- Helper for Lemma 13.11.6: the retained degree `n` of the lower truncation embedding
`embeddingUpIntGE a` is indexed by `n - a`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: on the retained range, the embedding is the affine map `i ↦ a + i`.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 13.11.6: above the cutoff, smart lower truncation keeps the original term. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : CochainComplex 𝒜 ℤ) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n :=
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n :=
    embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 13.11.6: if `K` is strictly zero above `b`, then any smart lower truncation
at a cutoff `a ≤ b` is still strictly zero above `b`. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE
    (K : CochainComplex 𝒜 ℤ) (a b : ℤ)
    (ha_le_b : a ≤ b) (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE b := by
  -- Proof comment: for `n > b`, the cutoff lies strictly below `n`, so the truncation term is
  -- canonically the original term of `K`, which already vanishes.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have han : a < n := lt_of_le_of_lt ha_le_b hn
  exact ((truncGE_term_iso_of_gt (K := K) a n han).isZero_iff).2
    (by
      rw [CochainComplex.isStrictlyLE_iff] at hK
      exact hK n hn)

/-- Helper for Lemma 13.11.6: a quasi-isomorphism from a bounded complex to a bounded-above
complex can be refined so that the target is bounded on both sides. -/
lemma quasiIso_to_bounded_refinement_of_bounded_above
    (X : Kᵇ(𝒜)) (Y : K⁻(𝒜)) (s : X.obj ⟶ Y.obj)
    (hs : HomotopyCategory.quasiIso 𝒜 (up ℤ) s) :
    ∃ (Y' : Kᵇ(𝒜)) (t : Y.obj ⟶ Y'.obj), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  -- Proof comment: keep the source-proof route from the bounded-below refinement, but choose the
  -- lower cutoff `a := min a₀ b` so the smart truncation of `Y` is still bounded above by `b`.
  let Xplus : K⁺(𝒜) :=
    ⟨X.obj, (HomotopyCategory.plus_iff (𝒜 := 𝒜) X.obj).2 <| by
      exact (CochainComplex.bounded_iff 𝒜 X.obj.as).1
        ((HomotopyCategory.bounded_iff (𝒜 := 𝒜) X.obj).1 X.property) |>.1⟩
  rw [HomotopyCategory.mem_quasiIso_iff] at hs
  obtain ⟨a₀, hXge⟩ :=
    (CochainComplex.plus_iff 𝒜 Xplus.obj.as).1
      ((HomotopyCategory.plus_iff (𝒜 := 𝒜) Xplus.obj).1 Xplus.property)
  obtain ⟨b, hYle⟩ :=
    (CochainComplex.minus_iff 𝒜 Y.obj.as).1
      ((HomotopyCategory.minus_iff (𝒜 := 𝒜) Y.obj).1 Y.property)
  let a : ℤ := min a₀ b
  have ha_le_b : a ≤ b := by
    dsimp [a]
    exact Int.min_le_right _ _
  have hYeventual : ∀ n : ℤ, n < a → IsZero (Y.obj.as.homology n) := by
    intro n hn
    let KX : CochainComplex 𝒜 ℤ := Xplus.obj.as
    let _ : KX.IsStrictlyGE a₀ := by
      simpa [KX] using hXge
    let _ : KX.HasHomology n := inferInstance
    have hXhomology : IsZero (KX.homology n) :=
      CochainComplex.isZero_of_isGE (K := KX) a₀ n (lt_of_lt_of_le hn <| by
        dsimp [a]
        exact Int.min_le_left _ _)
    have hXhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Xplus.obj)) := by
      simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
        HomotopyCategory.quotient_obj_as] using
        (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KX).isZero_iff).2
          hXhomology
    have hYhomotopy :
        IsZero (((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).obj Y.obj)) := by
      exact IsZero.of_iso hXhomotopy
        ((asIso ((HomotopyCategory.homologyFunctor 𝒜 (up ℤ) n).map s)).symm)
    let KY : CochainComplex 𝒜 ℤ := Y.obj.as
    simpa [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      HomotopyCategory.quotient_obj_as, KY] using
      (((HomotopyCategory.homologyFunctorFactors 𝒜 (up ℤ) n).app KY).isZero_iff).1
        hYhomotopy
  let KY : CochainComplex 𝒜 ℤ := Y.obj.as
  have hYge : KY.IsGE a := by
    -- Proof comment: vanishing of homology below `a` upgrades to the standard exactness owner.
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    simpa [KY] using hYeventual n hn
  let _ : KY.IsGE a := hYge
  have hπ : QuasiIso (CochainComplex.πTruncGE (K := KY) a) := inferInstance
  have htruncGE : (CochainComplex.truncGE (K := KY) a).IsStrictlyGE a := inferInstance
  have htruncLE : (CochainComplex.truncGE (K := KY) a).IsStrictlyLE b := by
    -- Proof comment: the chosen cutoff satisfies `a ≤ b`, so the retained terms above `b` are
    -- exactly the already-vanishing terms of `Y`.
    simpa [KY] using truncGE_isStrictlyLE_of_isStrictlyLE (K := KY) a b ha_le_b hYle
  have hY'bounded :
      HomotopyCategory.bounded 𝒜
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := KY) a)) := by
    -- Proof comment: the chosen lower truncation is bounded below by construction and remains
    -- bounded above because the original target was already bounded above.
    rw [HomotopyCategory.bounded_iff]
    exact (CochainComplex.bounded_iff 𝒜 _).2
      ⟨(CochainComplex.plus_iff 𝒜 _).2 ⟨a, htruncGE⟩,
        (CochainComplex.minus_iff 𝒜 _).2 ⟨b, htruncLE⟩⟩
  let Y' : Kᵇ(𝒜) :=
    ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj (CochainComplex.truncGE (K := KY) a),
      hY'bounded⟩
  refine ⟨Y', ?_, ?_⟩
  · -- Proof comment: the denominator is again the truncation map in the homotopy category.
    simpa [Y'] using
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map (CochainComplex.πTruncGE (K := KY) a)
  · -- Proof comment: this truncation map is the quasi-isomorphism produced by Lemma 13.11.5.
    simpa [Y'] using
      (show HomotopyCategory.quasiIso 𝒜 (up ℤ)
          ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
            (CochainComplex.πTruncGE (K := KY) a)) by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
        exact hπ)

/-- Helper for Lemma 13.11.6: a bounded-above complex whose image in the derived category is
bounded is quasi-isomorphic to a bounded complex. -/
lemma bounded_from_boundedAbove_derived_representative
    (Y : K⁻(𝒜))
    (hY :
      (t.bounded : ObjectProperty (D(𝒜)))
        (DerivedCategory.Qh.obj Y.obj)) :
    ∃ (Y' : Kᵇ(𝒜)) (t : Y.obj ⟶ Y'.obj), HomotopyCategory.quasiIso 𝒜 (up ℤ) t := by
  sorry

/-- Helper for Lemma 13.11.6: the bounded-above comparison functor is an equivalence. -/
theorem boundedAbove_localization_comparison_isEquivalence
    :
    (boundedAboveLocalizationComparisonFunctor (𝒜 := 𝒜)).IsEquivalence := by
  sorry

/-- Helper for Lemma 13.11.6: every bounded homotopy object is also bounded above. -/
theorem bounded_homotopy_obj_mem_minus
    (X : Kᵇ(𝒜)) :
    (HomotopyCategory.minus 𝒜) X.obj := by
  -- Proof comment: boundedness supplies both one-sided bounds, so we may forget the lower bound.
  rw [HomotopyCategory.minus_iff]
  exact (CochainComplex.bounded_iff 𝒜 X.obj.as).1
    ((HomotopyCategory.bounded_iff (𝒜 := 𝒜) X.obj).1 X.property) |>.2

/-- Helper for Lemma 13.11.6: the canonical inclusion `K^{b}(\mathcal A) ⥤ K^{-}(\mathcal A)`. -/
noncomputable abbrev boundedToBoundedAboveHomotopyFunctor :
    Kᵇ(𝒜) ⥤ K⁻(𝒜) :=
  (HomotopyCategory.minus 𝒜).lift
    ((HomotopyCategory.bounded 𝒜).ι)
    bounded_homotopy_obj_mem_minus

/-- Helper for Lemma 13.11.6: every bounded derived object is also bounded above. -/
theorem bounded_derived_obj_mem_minus
    (X : Dᵇ(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜))) X.obj := by
  -- Proof comment: a bounded derived object already satisfies the upper vanishing half.
  have hX := X.property
  rw [derivedCategory_t_bounded_iff] at hX
  exact (derivedCategory_t_minus_iff (𝒜 := 𝒜) X.obj).2 hX.2

/-- Helper for Lemma 13.11.6: the canonical inclusion `D^{b}(\mathcal A) ⥤ D^{-}(\mathcal A)`. -/
noncomputable abbrev boundedDerivedToDerivedAboveFunctor :
    Dᵇ(𝒜) ⥤ D⁻(𝒜) :=
  (t.minus : ObjectProperty (D(𝒜))).lift
    ((t.bounded : ObjectProperty (D(𝒜))).ι)
    bounded_derived_obj_mem_minus

/-- Helper for Lemma 13.11.6: the inclusion `K^{b}(\mathcal A) ⥤ K^{-}(\mathcal A)` sends
bounded acyclic Verdier morphisms to morphisms inverted in the bounded-above localization. -/
theorem boundedToBoundedAboveLocalization_inverts_acyclic_trW
    :
    MorphismProperty.IsInvertedBy
      ((Acᵇ(𝒜)).trW)
      (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
        ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization)) := by
  -- TODO: identify the image of a bounded quasi-isomorphism under `Kᵇ(𝒜) ⥤ K⁻(𝒜)` with a
  -- bounded-above quasi-isomorphism, then apply `Localization.inverts`.
  sorry

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor
`Qis^{b}(\mathcal A)^{-1}K^{b}(\mathcal A) ⥤ Qis^{-}(\mathcal A)^{-1}K^{-}(\mathcal A)`. -/
noncomputable abbrev boundedLocalizationToBoundedAboveLocalizationFunctor :
    ((Acᵇ(𝒜)).trW).Localization ⥤ ((Ac⁻(𝒜)).trW).Localization :=
  Localization.lift
    (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
      ((((Ac⁻(𝒜)).trW).Q) : K⁻(𝒜) ⥤ ((Ac⁻(𝒜)).trW).Localization))
    boundedToBoundedAboveLocalization_inverts_acyclic_trW
    (((Acᵇ(𝒜)).trW).Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)

/-- Helper for Lemma 13.11.6: the source-faithful comparison functor from the bounded
localization model to `D^{b}(\mathcal A)`. -/
noncomputable abbrev boundedLocalizationComparisonFunctor :
    ((Acᵇ(𝒜)).trW).Localization ⥤ Dᵇ(𝒜) :=
  Localization.lift mapBoundedHomotopyToDerivedBounded
    mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
    (((Acᵇ(𝒜)).trW).Q : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)

/-- Helper for Lemma 13.11.6: the bounded comparison functor is essentially surjective. -/
theorem bounded_localization_comparison_essSurj
    :
    (boundedLocalizationComparisonFunctor (𝒜 := 𝒜)).EssSurj := by
  -- TODO: use a bounded-above representative for the image in `D⁻(𝒜)` and replace it by a
  -- bounded representative via `bounded_from_boundedAbove_derived_representative`.
  sorry

/-- Helper for Lemma 13.11.6: every morphism in the bounded-above localization between bounded
objects is represented by a left fraction whose intermediate object is bounded. -/
theorem bounded_localization_comparison_surjective_on_Q_obj_hom
    (X Y : Kᵇ(𝒜)) :
    Function.Surjective
      (fun g : (((Acᵇ(𝒜)).trW).Q.obj X ⟶ ((Acᵇ(𝒜)).trW).Q.obj Y) =>
        (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).map g) := by
  sorry

/-- Helper for Lemma 13.11.6: if two bounded roofs become equal after passing to the
bounded-above localization, then they were already equal in the bounded localization. -/
theorem bounded_localization_comparison_injective_on_Q_obj_hom
    (X Y : Kᵇ(𝒜)) :
    Function.Injective
      (fun g : (((Acᵇ(𝒜)).trW).Q.obj X ⟶ ((Acᵇ(𝒜)).trW).Q.obj Y) =>
        (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).map g) := by
  sorry

/-- Helper for Lemma 13.11.6: the comparison from the bounded localization model to the
bounded-above localization model is fully faithful. -/
theorem boundedLocalizationToBoundedAboveLocalization_fullyFaithful :
    Nonempty (boundedLocalizationToBoundedAboveLocalizationFunctor (𝒜 := 𝒜)).FullyFaithful := by
  sorry

/-- Helper for Lemma 13.11.6: the bounded route to `D^{-}(\mathcal A)` agrees with first passing
to the bounded-above localization model. -/
noncomputable def bounded_localization_comparison_to_derivedAbove_iso :
    (boundedToBoundedAboveHomotopyFunctor (𝒜 := 𝒜) ⋙
        mapBoundedAboveHomotopyToDerivedAbove) ≅
      (mapBoundedHomotopyToDerivedBounded ⋙
        boundedDerivedToDerivedAboveFunctor (𝒜 := 𝒜)) := by
  sorry

/-- Helper for Lemma 13.11.6: the bounded comparison functor is an equivalence. -/
theorem bounded_localization_comparison_isEquivalence
    :
    (boundedLocalizationComparisonFunctor (𝒜 := 𝒜)).IsEquivalence := by
  sorry

-- Proof sketch: combine the bounded-above localization argument with the fact that bounded
-- denominators can be chosen inside `K^{b}(\mathcal A)`, again using the bounded replacement
-- statement from Lemma 13.11.5.
/-- Lemma 13.11.6 (9): the canonical functor `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` realizes
`D^{b}(\mathcal A)` as the localization of `K^{b}(\mathcal A)` at `Qis^{b}(\mathcal A)`. -/
theorem mapBoundedHomotopyToDerivedBounded_isLocalization
    :
    Functor.IsLocalization
      mapBoundedHomotopyToDerivedBounded
      (Qisᵇ(𝒜)) := by
  let F := boundedLocalizationComparisonFunctor (𝒜 := 𝒜)
  have hEqv : F.IsEquivalence :=
    bounded_localization_comparison_isEquivalence (𝒜 := 𝒜)
  let _ : F.IsEquivalence := hEqv
  have hLoc :
      mapBoundedHomotopyToDerivedBounded.IsLocalization ((Acᵇ(𝒜)).trW) := by
    -- Proof comment: once the bounded comparison functor is an equivalence, the bounded derived
    -- functor inherits the universal property of the localization functor `Q`.
    exact
      Functor.IsLocalization.of_equivalence_target
        ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization)
        ((Acᵇ(𝒜)).trW)
        mapBoundedHomotopyToDerivedBounded
        F.asEquivalence
        (Localization.fac
          mapBoundedHomotopyToDerivedBounded
          mapBoundedHomotopyToDerivedBounded_inverts_acyclic_trW
          ((((Acᵇ(𝒜)).trW).Q) : Kᵇ(𝒜) ⥤ ((Acᵇ(𝒜)).trW).Localization))
  simpa [boundedAcyclicHomotopyProperty_trW_eq_quasiIso (𝒜 := 𝒜)] using hLoc

end

end CategoryTheory
