import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap12.Lemma_12_10_6
import StacksProject_2024.Chap13.Lemma_13_5_4
import StacksProject_2024.Chap13.Lemma_13_6_10
import StacksProject_2024.Chap13.Lemma_13_11_2
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe uA vA

attribute [local instance] HasDerivedCategory.standard

namespace _root_.CategoryTheory.ObjectProperty

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

local notation "Q" => P.isoModSerre.Q

local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits Q :=
  preservesFiniteLimits Q P

local instance : PreservesFiniteColimits Q :=
  preservesFiniteColimits Q P

/- Domain-style sampling for 13.17.3:
- primary domain: Serre localizations of abelian categories and the induced functors on the
  ordinary and bounded derived categories;
- sampled owner declarations:
  `Adjunction.derived`,
  `Adjunction.isLocalization'`,
  `Functor.kernel`,
  `kernel_trW_eq_self`,
  `Functor.mapDerivedCategory`,
  `derivedCategoryBoundedBelowCohomologyInProperty`,
  `derivedCategoryBoundedAboveCohomologyInProperty`,
  `derivedCategoryBoundedCohomologyInProperty`,
  `ObjectProperty.lift`,
  `D⁺_{P}`,
  `D⁻_{P}`,
  `Dᵇ_{P}`;
- best owner abstraction: the canonical derived Serre quotient functor
  `(Q).mapDerivedCategory`, together with the canonical localization owner
  `Adjunction.isLocalization'` on the derived adjunction and the canonical kernel owner
  `Functor.kernel ((Q).mapDerivedCategory)`; the chapter owners `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}`
  then supply the bounded kernel subcategories, and on the bounded source categories the
  corresponding chapter-owned bounded properties
  `derivedCategoryBoundedBelowCohomologyInProperty P`,
  `derivedCategoryBoundedAboveCohomologyInProperty P`,
  `derivedCategoryBoundedCohomologyInProperty P`;
- primitive-vs-derived split:
  primitive data: the Serre quotient functor `Q`, its derived functor
    `(Q).mapDerivedCategory`, the canonical localization owner
    `Adjunction.isLocalization'` on the derived adjunction, the kernel owner
    `Functor.kernel ((Q).mapDerivedCategory)`, and the canonical bounded derived-category owners
    `t.plus`, `t.minus`, `t.bounded`;
  derived API: the restricted derived quotient functors on `D⁺(A)`, `D⁻(A)`, `Dᵇ(A)`, and the
    corresponding kernel identifications via the chapter-owned cohomology-in-`P` properties on
    `D(A)`, `D⁺(A)`, `D⁻(A)`, and `Dᵇ(A)`;
- source/core/bridge triage:
  `source-facing`: the localization statements on `D(A)`, `D⁺(A)`, `D⁻(A)`, `Dᵇ(A)`;
  `core/canonical`: `(Q).mapDerivedCategory`, `Adjunction.isLocalization'`,
    `Functor.kernel ((Q).mapDerivedCategory)`, `D⁺(-)`, `D⁻(-)`, `Dᵇ(-)`,
    `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}`,
    `derivedCategoryBoundedBelowCohomologyInProperty`,
    `derivedCategoryBoundedAboveCohomologyInProperty`,
    `derivedCategoryBoundedCohomologyInProperty`, and `ObjectProperty.lift`;
  `bridge/view`: the kernel identifications from `Functor.kernel ((Q).mapDerivedCategory)` to
    `derivedCategoryCohomologyInProperty P` and from the bounded restricted kernels to
    `derivedCategoryBoundedBelowCohomologyInProperty P`,
    `derivedCategoryBoundedAboveCohomologyInProperty P`, and
    `derivedCategoryBoundedCohomologyInProperty P`, together with the canonical inclusion
    functors from `D⁺_{P}`, `D⁻_{P}`, `Dᵇ_{P}` into `D⁺(A)`, `D⁻(A)`, and `Dᵇ(A)`.

This file therefore keeps the bounded kernel vocabulary from `Lemma_13_17_1` central and uses the
bounded source-category owners
`derivedCategoryBoundedBelowCohomologyInProperty P`,
`derivedCategoryBoundedAboveCohomologyInProperty P`, and
`derivedCategoryBoundedCohomologyInProperty P` in the main kernel and localization statements,
while the unbounded localization statement passes through the canonical kernel owner of
`(Q).mapDerivedCategory` before being restated in source-facing `D_{P}(A)` language. The
canonical inclusions of `D⁺_{P}`, `D⁻_{P}`, and `Dᵇ_{P}` remain bridge/view API rather than the
main theorem interface. -/

section

/-- Helper for Lemma 13.17.3: passing a cochain complex to the Serre quotient commutes with taking
homology in a fixed degree. -/
abbrev serre_quotient_homology_iso
    (K : CochainComplex A ℤ) (i : ℤ) :
    ((((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i) ≅
      Q.obj (K.homology i) :=
  -- Specialize the canonical exact-functor comparison on the short complex at degree `i`.
  (K.sc i).mapHomologyIso Q

/-- Helper for Lemma 13.17.3: if a complex becomes acyclic after applying the Serre quotient
functor, then every homology object of the original complex lies in the Serre class. -/
theorem homology_mem_of_serre_quotient_acyclic
    {K : CochainComplex A ℤ}
    (hK : (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) (i : ℤ) :
    P (K.homology i) := by
  -- Route correction: keep the source proof on the degreewise homology route instead of importing
  -- the heavier Chapter 12 file just for this exact comparison.
  rw [HomologicalComplex.acyclic_iff] at hK
  have hzero_mapped :
      IsZero ((((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK i
  have hzero_obj : IsZero (Q.obj (K.homology i)) := by
    exact hzero_mapped.of_iso (serre_quotient_homology_iso P K i).symm
  exact (isZero_obj_iff Q P (K.homology i)).1 hzero_obj

/-- Helper for Lemma 13.17.3: on derived objects, taking homology after the derived Serre quotient
agrees with taking homology first and then applying the Serre quotient functor. -/
noncomputable def derived_serre_quotient_homology_iso
    (X : D(A)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor P.isoModSerre.Localization i).obj
        (((Q).mapDerivedCategory).obj X)) ≅
      Q.obj ((DerivedCategory.homologyFunctor A i).obj X) :=
  let K : CochainComplex A ℤ := DerivedCategory.Q.objPreimage X
  let QK : CochainComplex P.isoModSerre.Localization ℤ :=
    ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eA :
      ((DerivedCategory.homologyFunctor A i).obj X) ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor A i).mapIso
      (DerivedCategory.Q.objObjPreimageIso X)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors A i).app K
  -- Proof comment: choose the canonical cochain representative of `X`, compare the mapped
  -- derived object with the derived image of that representative, and then apply the already
  -- established complex-level homology comparison.
  (DerivedCategory.homologyFunctor P.isoModSerre.Localization i).mapIso
      ((((Q).mapDerivedCategory.mapIso
        (DerivedCategory.Q.objObjPreimageIso X)).symm) ≪≫
        ((Q).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors P.isoModSerre.Localization i).app QK ≪≫
    serre_quotient_homology_iso P K i ≪≫
    Q.mapIso eA.symm

/-- Helper for Lemma 13.17.3: if the derived Serre quotient of an object is zero, then every
cohomology object of the original derived object lies in the Serre class. -/
theorem homology_mem_of_derived_serre_quotient_isZero
    {X : D(A)} (hX : IsZero (((Q).mapDerivedCategory).obj X)) (i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj X) := by
  -- Proof comment: apply degree-`i` homology to the zero object in the quotient derived category
  -- and transport that vanishing back along `derived_serre_quotient_homology_iso`.
  have hzero_mapped :
      IsZero
        ((DerivedCategory.homologyFunctor P.isoModSerre.Localization i).obj
          (((Q).mapDerivedCategory).obj X)) := by
    exact (DerivedCategory.homologyFunctor P.isoModSerre.Localization i).map_isZero hX
  have hzero_obj :
      IsZero (Q.obj ((DerivedCategory.homologyFunctor A i).obj X)) := by
    exact hzero_mapped.of_iso (derived_serre_quotient_homology_iso P X i).symm
  exact
    (isZero_obj_iff Q P ((DerivedCategory.homologyFunctor A i).obj X)).1 hzero_obj

-- Proof sketch: isolate the canonical localization owner first. The derived adjunction coming
-- from `u ⊣ P.isoModSerre.Q` should localize the right adjoint `(Q).mapDerivedCategory` at the
-- `trW` owner of its categorical kernel; only after that do we rewrite the kernel in
-- source-facing `D_{P}(A)` language.
/-- Helper for Lemma 13.17.3: the derived Serre quotient functor is canonically a localization at
the `trW` owner of its categorical kernel. -/
theorem serreQuotientDerivedFunctor_isLocalization_core
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (Q).mapDerivedCategory
      (Functor.kernel ((Q).mapDerivedCategory)).trW := by
  -- Route correction: previous attempts tried to package the derived adjunction localization and
  -- the kernel rewrite to `D_{P}(A)` in one declaration. We now stop at the canonical kernel owner
  -- first, exactly matching the source proof's localization step.
  let adjD :
      u.mapDerivedCategory ⊣ (Q).mapDerivedCategory :=
    Adjunction.derived
      (adj.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso P.isoModSerre.Localization (ComplexShape.up ℤ))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (u.mapDerivedCategoryFactors.hom)
      ((Q).mapDerivedCategoryFactors.inv)
  letI := adjD.rightAdjointCommShift ℤ
  letI := adjD.commShift_of_leftAdjoint ℤ
  letI : ((Q).mapDerivedCategory).IsTriangulated := adjD.isTriangulated_rightAdjoint
  -- Proof comment: the exact-functor kernel owner rewrites the Verdier morphism property
  -- inverted by `(Q).mapDerivedCategory` to the inverse image of isomorphisms, and the derived
  -- adjunction identifies that inverse-image owner with the canonical `isColocal` owner.
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor (Q).mapDerivedCategory]
  rw [← ObjectProperty.isColocal_eq_inverseImage_isomorphisms adjD]
  exact ObjectProperty.isLocalization_isColocal adjD

-- Proof sketch: the canonical owner for objects killed by an exact triangulated functor is
-- `Functor.kernel`; for `Q.mapDerivedCategory`, vanishing in the quotient derived category is
-- equivalent to all cohomology objects vanishing in the Serre quotient, hence to their lying in
-- `P`.
/-- The kernel of the derived Serre quotient functor is the cohomology-in-`P` owner on `D(A)`.
This is the bridge from the canonical kernel owner to the source-facing subcategory `D_{P}(A)`.
-/
theorem kernel_serreQuotientDerivedFunctor :
    Functor.kernel ((Q).mapDerivedCategory) =
      derivedCategoryCohomologyInProperty P := by
  ext X
  constructor
  · intro hX
    -- Proof comment: the forward direction is now the direct derived-level homology comparison.
    intro i
    exact homology_mem_of_derived_serre_quotient_isZero (P := P) hX i
  · intro hX
    let KX : CochainComplex A ℤ := DerivedCategory.Q.objPreimage X
    let QKX : CochainComplex P.isoModSerre.Localization ℤ :=
      ((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj KX
    let eMap :
        ((Q).mapDerivedCategory.obj X) ≅ DerivedCategory.Q.obj QKX :=
      (((Q).mapDerivedCategory.mapIso
        (DerivedCategory.Q.objObjPreimageIso X)).symm) ≪≫
        ((Q).mapDerivedCategoryFactors.app KX)
    have hQKX : QKX.Acyclic := by
      rw [HomologicalComplex.acyclic_iff]
      intro i
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      let eA :
          ((DerivedCategory.homologyFunctor A i).obj X) ≅ KX.homology i :=
        ((DerivedCategory.homologyFunctor A i).mapIso
          (DerivedCategory.Q.objObjPreimageIso X)).symm ≪≫
          (DerivedCategory.homologyFunctorFactors A i).app KX
      have hzero_obj :
          IsZero (Q.obj ((DerivedCategory.homologyFunctor A i).obj X)) :=
        (isZero_obj_iff Q P ((DerivedCategory.homologyFunctor A i).obj X)).2 (hX i)
      have hzero_homology : IsZero (Q.obj (KX.homology i)) := by
        exact (Q.mapIso eA.symm).isZero_iff.2 hzero_obj
      exact (serre_quotient_homology_iso P KX i).isZero_iff.2 hzero_homology
    let L : K(P.isoModSerre.Localization) :=
      (HomotopyCategory.quotient P.isoModSerre.Localization (ComplexShape.up ℤ)).obj QKX
    let eQh :
        DerivedCategory.Qh.obj L ≅ DerivedCategory.Q.obj QKX := by
      simpa [L, HomotopyCategory.quotient_obj_as] using
        (DerivedCategory.quotientCompQhIso P.isoModSerre.Localization).app QKX
    have hker :
        Functor.kernel
          (DerivedCategory.Qh :
            K(P.isoModSerre.Localization) ⥤ D(P.isoModSerre.Localization))
          L := by
      -- Proof comment: an acyclic representative lies in the Verdier kernel of `Qh`.
      rw [subcategoryAcyclic_kernel_Qh (A := P.isoModSerre.Localization)]
      simpa [L, HomotopyCategory.subcategoryAcyclic,
        ObjectProperty.prop_inverseImage_iff] using hQKX
    have hzero_QKX : IsZero (DerivedCategory.Q.obj QKX) := by
      exact eQh.isZero_iff.1 hker
    -- Proof comment: compare `((Q).mapDerivedCategory).obj X` with the image of the acyclic
    -- representative and transport zero back across the canonical comparison isomorphism.
    exact eMap.isZero_iff.2 hzero_QKX

-- Proof sketch: first use the canonical kernel-owner localization theorem for
-- `(Q).mapDerivedCategory`, and only then rewrite that kernel via
-- `kernel_serreQuotientDerivedFunctor` to recover the textbook `D_{P}(A)` statement.
/-- Lemma 13.17.3: if the Serre quotient functor `A ⥤ A/P` admits a fully faithful left adjoint,
then the induced functor on derived categories identifies `D(A/P)` with the Verdier quotient
`D(A) / D_P(A)`, formalized as localization at the morphisms whose cone lies in `D_P(A)`. -/
@[stacks 06XM]
theorem serreQuotientDerivedFunctor_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (Q).mapDerivedCategory
      (derivedCategoryCohomologyInProperty P).trW := by
  -- Proof comment: the source-facing theorem is now only a kernel rewrite of the canonical
  -- localization statement.
  simpa [kernel_serreQuotientDerivedFunctor (P := P)] using
    (serreQuotientDerivedFunctor_isLocalization_core (P := P) u adj)

-- Proof sketch: exact functors preserve cohomology vanishing in sufficiently negative degrees, so
-- applying the derived Serre quotient functor to a bounded-below object again yields a
-- bounded-below object in the quotient derived category.
/-- The derived Serre quotient functor sends bounded-below objects to bounded-below objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory
    (X : D⁺(A)) :
    (t.plus : ObjectProperty _) ((t.plus.ι ⋙ (Q).mapDerivedCategory).obj X) := by
  change (t.plus : ObjectProperty _) ((Q).mapDerivedCategory.obj X.obj)
  rcases X.property with ⟨n, hX⟩
  let _ : X.obj.IsGE n := hX
  obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE X.obj n
  let e' :
      ((Q).mapDerivedCategory.obj X.obj) ≅
        DerivedCategory.Q.obj
          (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    ((Q).mapDerivedCategory.mapIso e) ≪≫
      ((Q).mapDerivedCategoryFactors.app K)
  have hQ : (t.plus : ObjectProperty _)
      (DerivedCategory.Q.obj
        (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    refine ⟨n, ?_⟩
    change
      (DerivedCategory.Q.obj
        (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsGE n
    exact (DerivedCategory.isGE_Q_obj_iff
      (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n).2 inferInstance
  -- Proof comment: represent `X` by a bounded-below complex and pass the bound through the
  -- derived Serre quotient comparison isomorphism.
  exact (t.plus : ObjectProperty _).prop_of_iso e'.symm hQ

/-- The derived Serre quotient functor restricted to bounded-below objects. -/
abbrev serreQuotientDerivedFunctorPlus :
    D⁺(A) ⥤ D⁺(P.isoModSerre.Localization) :=
  (t.plus : ObjectProperty _).lift
    (t.plus.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory P)

/-- Helper for Lemma 13.17.3: the kernel of a lifted restriction of the derived Serre quotient
functor is the inverse image of the ambient kernel along the source inclusion. -/
theorem kernel_lift_eq_inverseImage_kernel_of_liftCompιIso
    (T : ObjectProperty (D(A)))
    (R : ObjectProperty (D(P.isoModSerre.Localization)))
    (hT : ∀ X : T.FullSubcategory, R ((T.ι ⋙ (Q).mapDerivedCategory).obj X)) :
    Functor.kernel ((R).lift (T.ι ⋙ (Q).mapDerivedCategory) hT) =
      (Functor.kernel ((Q).mapDerivedCategory)).inverseImage T.ι := by
  -- Proof comment: compare the lifted functor with the ambient one after composing with the
  -- inclusion `R.ι`, then transport `IsZero` objectwise across `ObjectProperty.liftCompιIso`.
  ext X
  let ιR : R.FullSubcategory ⥤ D(P.isoModSerre.Localization) := R.ι
  let e :
      ιR.obj (((R).lift (T.ι ⋙ (Q).mapDerivedCategory) hT).obj X) ≅
        (T.ι ⋙ (Q).mapDerivedCategory).obj X :=
    (ObjectProperty.liftCompιIso
      R
      (T.ι ⋙ (Q).mapDerivedCategory)
      hT).app X
  constructor
  · intro hX
    have hUnderlying :
        IsZero (ιR.obj (((R).lift (T.ι ⋙ (Q).mapDerivedCategory) hT).obj X)) :=
      ιR.map_isZero hX
    exact e.isZero_iff.1 hUnderlying
  · intro hX
    have hUnderlying :
        IsZero (ιR.obj (((R).lift (T.ι ⋙ (Q).mapDerivedCategory) hT).obj X)) :=
      e.isZero_iff.2 hX
    exact IsZero.of_full_of_faithful_of_isZero ιR _ hUnderlying

-- Proof sketch: apply the unbounded localization statement to the bounded-below full
-- subcategories, using that the derived Serre quotient functor preserves bounded-below objects
-- and that `D^+_P(A)` is the kernel subcategory inside `D^+(A)`.
/-- The kernel of the bounded-below derived Serre quotient functor is the bounded-below
cohomology-in-`P` object property on `D^+(A)`, equivalently the image of `D^+_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorPlus :
    Functor.kernel (serreQuotientDerivedFunctorPlus P) =
      derivedCategoryBoundedBelowCohomologyInProperty P := by
  -- Proof comment: the bounded-below kernel is the inverse image of the ambient kernel under the
  -- canonical inclusion `D⁺(A) ⥤ D(A)`.
  simpa [serreQuotientDerivedFunctorPlus,
    derivedCategoryBoundedBelowCohomologyInProperty,
    kernel_serreQuotientDerivedFunctor (P := P)] using
    (kernel_lift_eq_inverseImage_kernel_of_liftCompιIso
      (P := P)
      (T := (t.plus : ObjectProperty (D(A))))
      (R := (t.plus : ObjectProperty (D(P.isoModSerre.Localization))))
      (hT := serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory P))

/-- The bounded-below derived Serre quotient functor realizes `D^+(A/P)` as the Verdier quotient
`D^+(A) / D^+_P(A)`. -/
theorem serreQuotientDerivedFunctorPlus_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorPlus P)
      (derivedCategoryBoundedBelowCohomologyInProperty P).trW := by
  have hCore :
      Functor.IsLocalization
        (Q).mapDerivedCategory
        (Functor.kernel ((Q).mapDerivedCategory)).trW :=
    serreQuotientDerivedFunctor_isLocalization_core (P := P) u adj
  let G : D⁺(A) ⥤ D⁺(P.isoModSerre.Localization) := serreQuotientDerivedFunctorPlus P
  let ιplus : D⁺(P.isoModSerre.Localization) ⥤ D(P.isoModSerre.Localization) :=
    (t.plus : ObjectProperty (D(P.isoModSerre.Localization))).ι
  letI :
      (Q).mapDerivedCategory.IsLocalization
        (Functor.kernel ((Q).mapDerivedCategory)).trW := hCore
  letI :
      ((t.plus : ObjectProperty (D(A))).ι ⋙ (Q).mapDerivedCategory).IsLocalization
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.plus : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: restrict the ambient localization to the bounded-below source subcategory.
    simpa [ObjectProperty.inverseImage_trW_iff] using
      (Functor.IsLocalization.whisker_left
        (W := (Functor.kernel ((Q).mapDerivedCategory)).trW)
        (F := (Q).mapDerivedCategory)
        ((t.plus : ObjectProperty (D(A))).ι))
  letI :
      (G ⋙ ιplus).IsLocalization
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.plus : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: compose the lifted bounded-below functor with the target inclusion to recover
    -- the restricted ambient functor.
    simpa [G, ιplus, serreQuotientDerivedFunctorPlus] using
      (Functor.IsLocalization.of_iso
        ((ObjectProperty.liftCompιIso
          (t.plus : ObjectProperty (D(P.isoModSerre.Localization)))
          ((t.plus : ObjectProperty (D(A))).ι ⋙ (Q).mapDerivedCategory)
          (serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory P)))
  letI : ιplus.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms
      (t.plus : ObjectProperty (D(P.isoModSerre.Localization))).fullyFaithfulι
  have hLift :
      Functor.IsLocalization
        G
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.plus : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: the bounded-below inclusion into the ambient target reflects isomorphisms,
    -- so the localization property descends from the composite back to the lifted functor.
    exact Functor.IsLocalization.of_comp G ιplus
  -- Proof comment: the bounded-below kernel was already identified with the source-facing owner
  -- `D⁺_P(A)`, so the final statement is only a kernel rewrite.
  simpa [G, serreQuotientDerivedFunctorPlus,
    kernel_serreQuotientDerivedFunctorPlus (P := P)] using hLift

-- Proof sketch: exact functors preserve cohomology vanishing in sufficiently positive degrees, so
-- bounded-above objects remain bounded above after applying the derived Serre quotient functor.
/-- The derived Serre quotient functor sends bounded-above objects to bounded-above objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory
    (X : D⁻(A)) :
    (t.minus : ObjectProperty _) ((t.minus.ι ⋙ (Q).mapDerivedCategory).obj X) := by
  change (t.minus : ObjectProperty _) ((Q).mapDerivedCategory.obj X.obj)
  rcases X.property with ⟨n, hX⟩
  let _ : X.obj.IsLE n := hX
  obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X.obj n
  let e' :
      ((Q).mapDerivedCategory.obj X.obj) ≅
        DerivedCategory.Q.obj
          (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    ((Q).mapDerivedCategory.mapIso e) ≪≫
      ((Q).mapDerivedCategoryFactors.app K)
  have hQ : (t.minus : ObjectProperty _)
      (DerivedCategory.Q.obj
        (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    refine ⟨n, ?_⟩
    change
      (DerivedCategory.Q.obj
        (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsLE n
    exact (DerivedCategory.isLE_Q_obj_iff
      (((Q).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n).2 inferInstance
  -- Proof comment: the same representative-comparison route preserves the upper bound.
  exact (t.minus : ObjectProperty _).prop_of_iso e'.symm hQ

/-- The derived Serre quotient functor restricted to bounded-above objects. -/
abbrev serreQuotientDerivedFunctorMinus :
    D⁻(A) ⥤ D⁻(P.isoModSerre.Localization) :=
  (t.minus : ObjectProperty _).lift
    (t.minus.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory P)

-- Proof sketch: combine the unbounded localization statement with preservation of bounded-above
-- cohomology and identify `D^-_P(A)` as the kernel subcategory in `D^-(A)`.
/-- The kernel of the bounded-above derived Serre quotient functor is the bounded-above
cohomology-in-`P` object property on `D^-(A)`, equivalently the image of `D^-_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorMinus :
    Functor.kernel (serreQuotientDerivedFunctorMinus P) =
      derivedCategoryBoundedAboveCohomologyInProperty P := by
  -- Proof comment: this is the same inverse-image-of-the-ambient-kernel argument for the
  -- bounded-above inclusion `D⁻(A) ⥤ D(A)`.
  simpa [serreQuotientDerivedFunctorMinus,
    derivedCategoryBoundedAboveCohomologyInProperty,
    kernel_serreQuotientDerivedFunctor (P := P)] using
    (kernel_lift_eq_inverseImage_kernel_of_liftCompιIso
      (P := P)
      (T := (t.minus : ObjectProperty (D(A))))
      (R := (t.minus : ObjectProperty (D(P.isoModSerre.Localization))))
      (hT := serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory P))

/-- The bounded-above derived Serre quotient functor realizes `D^-(A/P)` as the Verdier quotient
`D^-(A) / D^-_P(A)`. -/
theorem serreQuotientDerivedFunctorMinus_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorMinus P)
      (derivedCategoryBoundedAboveCohomologyInProperty P).trW := by
  have hCore :
      Functor.IsLocalization
        (Q).mapDerivedCategory
        (Functor.kernel ((Q).mapDerivedCategory)).trW :=
    serreQuotientDerivedFunctor_isLocalization_core (P := P) u adj
  let G : D⁻(A) ⥤ D⁻(P.isoModSerre.Localization) := serreQuotientDerivedFunctorMinus P
  let ιminus : D⁻(P.isoModSerre.Localization) ⥤ D(P.isoModSerre.Localization) :=
    (t.minus : ObjectProperty (D(P.isoModSerre.Localization))).ι
  letI :
      (Q).mapDerivedCategory.IsLocalization
        (Functor.kernel ((Q).mapDerivedCategory)).trW := hCore
  letI :
      ((t.minus : ObjectProperty (D(A))).ι ⋙ (Q).mapDerivedCategory).IsLocalization
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.minus : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: this is the bounded-above restriction of the ambient localization.
    simpa [ObjectProperty.inverseImage_trW_iff] using
      (Functor.IsLocalization.whisker_left
        (W := (Functor.kernel ((Q).mapDerivedCategory)).trW)
        (F := (Q).mapDerivedCategory)
        ((t.minus : ObjectProperty (D(A))).ι))
  letI :
      (G ⋙ ιminus).IsLocalization
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.minus : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: the bounded-above lift composes with the inclusion to the restricted
    -- ambient functor.
    simpa [G, ιminus, serreQuotientDerivedFunctorMinus] using
      (Functor.IsLocalization.of_iso
        ((ObjectProperty.liftCompιIso
          (t.minus : ObjectProperty (D(P.isoModSerre.Localization)))
          ((t.minus : ObjectProperty (D(A))).ι ⋙ (Q).mapDerivedCategory)
          (serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory P)))
  letI : ιminus.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms
      (t.minus : ObjectProperty (D(P.isoModSerre.Localization))).fullyFaithfulι
  have hLift :
      Functor.IsLocalization
        G
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.minus : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: reflect invertibility through the bounded-above inclusion on the target.
    exact Functor.IsLocalization.of_comp G ιminus
  -- Proof comment: rewrite the restricted kernel in source-facing `D^-_P(A)` language.
  simpa [G, serreQuotientDerivedFunctorMinus,
    kernel_serreQuotientDerivedFunctorMinus (P := P)] using hLift

-- Proof sketch: preserve both the bounded-below and bounded-above vanishing ranges under the
-- derived Serre quotient functor to obtain preservation of boundedness.
/-- The derived Serre quotient functor sends bounded objects to bounded objects. -/
theorem serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory
    (X : Dᵇ(A)) :
    (t.bounded : ObjectProperty _) ((t.bounded.ι ⋙ (Q).mapDerivedCategory).obj X) := by
  change (t.bounded : ObjectProperty _) ((Q).mapDerivedCategory.obj X.obj)
  have hX := X.property
  rw [derivedCategory_t_bounded_iff] at hX ⊢
  constructor
  ·
    let Xplus : D⁺(A) :=
      ⟨X.obj, (derivedCategory_t_plus_iff (𝒜 := A) X.obj).2 hX.1⟩
    have hPlus :
        (t.plus : ObjectProperty _)
          ((t.plus.ι ⋙ (Q).mapDerivedCategory).obj Xplus) :=
      serreQuotientDerivedFunctor_obj_mem_boundedBelowDerivedCategory P Xplus
    -- Proof comment: boundedness below of the image is exactly the already-proved `D⁺` case.
    simpa [Xplus] using
      (derivedCategory_t_plus_iff
        (𝒜 := P.isoModSerre.Localization)
        ((Q).mapDerivedCategory.obj X.obj)).1 hPlus
  ·
    let Xminus : D⁻(A) :=
      ⟨X.obj, (derivedCategory_t_minus_iff (𝒜 := A) X.obj).2 hX.2⟩
    have hMinus :
        (t.minus : ObjectProperty _)
          ((t.minus.ι ⋙ (Q).mapDerivedCategory).obj Xminus) :=
      serreQuotientDerivedFunctor_obj_mem_boundedAboveDerivedCategory P Xminus
    -- Proof comment: boundedness above of the image is the corresponding `D⁻` specialization.
    simpa [Xminus] using
      (derivedCategory_t_minus_iff
        (𝒜 := P.isoModSerre.Localization)
        ((Q).mapDerivedCategory.obj X.obj)).1 hMinus

/-- The derived Serre quotient functor restricted to bounded objects. -/
abbrev serreQuotientDerivedFunctorBounded :
    Dᵇ(A) ⥤ Dᵇ(P.isoModSerre.Localization) :=
  (t.bounded : ObjectProperty _).lift
    (t.bounded.ι ⋙ (Q).mapDerivedCategory)
    (serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory P)

-- Proof sketch: combine the unbounded localization statement with preservation of boundedness and
-- identify `D^b_P(A)` as the Verdier kernel inside `D^b(A)`.
/-- The kernel of the bounded derived Serre quotient functor is the bounded cohomology-in-`P`
object property on `D^b(A)`, equivalently the image of `D^b_P(A)`. -/
theorem kernel_serreQuotientDerivedFunctorBounded :
    Functor.kernel (serreQuotientDerivedFunctorBounded P) =
      derivedCategoryBoundedCohomologyInProperty P := by
  -- Proof comment: once more, the bounded kernel is just the inverse image of the ambient kernel
  -- under the bounded inclusion `Dᵇ(A) ⥤ D(A)`.
  simpa [serreQuotientDerivedFunctorBounded,
    derivedCategoryBoundedCohomologyInProperty,
    kernel_serreQuotientDerivedFunctor (P := P)] using
    (kernel_lift_eq_inverseImage_kernel_of_liftCompιIso
      (P := P)
      (T := (t.bounded : ObjectProperty (D(A))))
      (R := (t.bounded : ObjectProperty (D(P.isoModSerre.Localization))))
      (hT := serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory P))

/-- The bounded derived Serre quotient functor realizes `D^b(A/P)` as the Verdier quotient
`D^b(A) / D^b_P(A)`. -/
theorem serreQuotientDerivedFunctorBounded_isLocalization_of_fullyFaithfulLeftAdjoint
    (u : P.isoModSerre.Localization ⥤ A) (adj : u ⊣ Q) [u.Full] [u.Faithful]
    :
    Functor.IsLocalization
      (serreQuotientDerivedFunctorBounded P)
      (derivedCategoryBoundedCohomologyInProperty P).trW := by
  have hCore :
      Functor.IsLocalization
        (Q).mapDerivedCategory
        (Functor.kernel ((Q).mapDerivedCategory)).trW :=
    serreQuotientDerivedFunctor_isLocalization_core (P := P) u adj
  let G : Dᵇ(A) ⥤ Dᵇ(P.isoModSerre.Localization) := serreQuotientDerivedFunctorBounded P
  let ιbounded : Dᵇ(P.isoModSerre.Localization) ⥤ D(P.isoModSerre.Localization) :=
    (t.bounded : ObjectProperty (D(P.isoModSerre.Localization))).ι
  letI :
      (Q).mapDerivedCategory.IsLocalization
        (Functor.kernel ((Q).mapDerivedCategory)).trW := hCore
  letI :
      ((t.bounded : ObjectProperty (D(A))).ι ⋙ (Q).mapDerivedCategory).IsLocalization
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.bounded : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: restrict the ambient localization to the bounded source inclusion.
    simpa [ObjectProperty.inverseImage_trW_iff] using
      (Functor.IsLocalization.whisker_left
        (W := (Functor.kernel ((Q).mapDerivedCategory)).trW)
        (F := (Q).mapDerivedCategory)
        ((t.bounded : ObjectProperty (D(A))).ι))
  letI :
      (G ⋙ ιbounded).IsLocalization
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.bounded : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: the bounded lift followed by the target inclusion is again the restricted
    -- ambient functor.
    simpa [G, ιbounded, serreQuotientDerivedFunctorBounded] using
      (Functor.IsLocalization.of_iso
        ((ObjectProperty.liftCompιIso
          (t.bounded : ObjectProperty (D(P.isoModSerre.Localization)))
          ((t.bounded : ObjectProperty (D(A))).ι ⋙ (Q).mapDerivedCategory)
          (serreQuotientDerivedFunctor_obj_mem_boundedDerivedCategory P)))
  letI : ιbounded.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms
      (t.bounded : ObjectProperty (D(P.isoModSerre.Localization))).fullyFaithfulι
  have hLift :
      Functor.IsLocalization
        G
        (((Functor.kernel ((Q).mapDerivedCategory)).inverseImage
          (t.bounded : ObjectProperty (D(A))).ι).trW) := by
    -- Proof comment: reflect invertibility through the bounded target inclusion.
    exact Functor.IsLocalization.of_comp G ιbounded
  -- Proof comment: rewrite the restricted kernel to recover the textbook bounded statement.
  simpa [G, serreQuotientDerivedFunctorBounded,
    kernel_serreQuotientDerivedFunctorBounded (P := P)] using hLift

end

end _root_.CategoryTheory.ObjectProperty
