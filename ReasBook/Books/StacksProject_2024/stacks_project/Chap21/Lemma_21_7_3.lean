import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.Chap18.Lemma_18_3_1
import StacksProject_2024.Chap19.Theorem_19_7_4
import StacksProject_2024.Chap21.Lemma_21_7_3.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u v

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}

namespace CategoryTheory.Sheaf

/-- Helper for Lemma 21.7.3: the presheaf-valued complex obtained by applying
`sheafToPresheaf J AddCommGrpCat` to an injective resolution. -/
private abbrev injectiveResolutionPresheafComplex
    [HasSheafify J AddCommGrpCat.{max u v}]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) :
    HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (ComplexShape.up ℕ) :=
  (((sheafToPresheaf J AddCommGrpCat.{max u v}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex)

/-- Helper for Lemma 21.7.3: sections over a fixed object of the site, specialized to abelian
sheaves. -/
private abbrev siteSectionsFunctor
    [HasSheafify J AddCommGrpCat.{max u v}]
    (U : C) : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  (sheafSections J AddCommGrpCat.{max u v}).obj (op U)

/-- Helper for Lemma 21.7.3: exactness of an injective resolution in positive degree makes every
cycle section locally into a boundary along a suitable covering. -/
lemma injectiveResolutionCoverLiftsCycle
    [HasSheafify J AddCommGrpCat.{max u v}] [HasExt (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    (F : Sheaf J AddCommGrpCat.{max u v}) (I : InjectiveResolution F) {U : C} (m : ℕ)
    (s : (I.cocomplex.X (m + 1)).1.obj (op U))
    (hs : ((I.cocomplex.d (m + 1) (m + 2)).hom.app (op U)) s = 0) :
    ∃ T : J.Cover U, ∀ a : T.Arrow, ∃ t : (I.cocomplex.X m).1.obj (op a.Y),
      ((I.cocomplex.d m (m + 1)).hom.app (op a.Y)) t =
        (I.cocomplex.X (m + 1)).1.map a.f.op s := by
  let S : ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
    ShortComplex.mk (I.cocomplex.d m (m + 1)) (I.cocomplex.d (m + 1) (m + 2)) (by simp)
  have hLiftLoc :
      Sheaf.IsLocallySurjective (kernel.lift S.g S.f S.zero) := by
    have hEpi : Epi (kernel.lift S.g S.f S.zero) :=
      ShortComplex.Exact.epi_kernelLift (S := S) (I.exact_succ m)
    exact
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v}
        (kernel.lift S.g S.f S.zero)).2 hEpi
  -- Proof comment: the source-text local-boundary step is exactly the local lifting criterion for
  -- the consecutive differential short complex of the injective resolution.
  simpa [S] using
    ShortComplex.cover_lifts_of_isLocallySurjective_kernel_lift (J := J) S hLiftLoc U s hs

/-- Helper for Lemma 21.7.3: restricting sections along `i : V ⟶ U` induces a chain map between
the evaluated sections complexes of an injective resolution. -/
private theorem sectionsComplexRestrictionMap_comm
    [HasSheafify J AddCommGrpCat.{max u v}]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F)
    {U V : C} (i : V ⟶ U) (p q : ℕ) (_h : ComplexShape.Rel (ComplexShape.up ℕ) p q) :
    (I.cocomplex.X p).1.map i.op ≫
        (((siteSectionsFunctor (J := J) V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).d p q =
      (((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).d p q ≫
        (I.cocomplex.X q).1.map i.op := by
  -- Proof comment: this is just naturality of the differential viewed as a map of presheaves.
  simpa using NatTrans.naturality ((I.cocomplex.d p q).hom) i.op

/-- Helper for Lemma 21.7.3: restriction along a cover arrow acts degreewise on the sections
complex of an injective resolution. -/
private noncomputable def sectionsComplexRestrictionMap
    [HasSheafify J AddCommGrpCat.{max u v}]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F)
    {U V : C} (i : V ⟶ U) :
    (((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex) ⟶
      (((siteSectionsFunctor (J := J) V).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex) where
  f := fun n ↦ (I.cocomplex.X n).1.map i.op
  comm' := fun p q h ↦ sectionsComplexRestrictionMap_comm (J := J) I i p q h

/-- Helper for Lemma 21.7.3: postcomposing the `ULift ℤ`-multiples morphism of an element with an
additive map gives the `ULift ℤ`-multiples morphism of the image element. -/
private lemma uliftMultiplesCompEq
    {A B : AddCommGrpCat} (φ : A ⟶ B) (x : A) :
    AddCommGrpCat.ofHom ((uliftZMultiplesHom A x)) ≫ φ =
      AddCommGrpCat.ofHom
        ((uliftZMultiplesHom B (ConcreteCategory.hom φ x))) := by
  -- Proof comment: evaluate both morphisms on a generator; both send it to the same integer
  -- multiple of `φ x`.
  ext z
  change ConcreteCategory.hom φ (((uliftZMultiplesHom A x) z)) =
      ((uliftZMultiplesHom B (ConcreteCategory.hom φ x)) z)
  rw [uliftZMultiplesHom_apply_apply, map_zsmul, uliftZMultiplesHom_apply_apply]

/-- Helper for Lemma 21.7.3: an elementwise boundary identity upgrades to the corresponding
owner-level equality between `ULift ℤ`-multiple morphisms. -/
private lemma uliftMultiplesBoundaryEqOfElementBoundary
    {K : HomologicalComplex AddCommGrpCat (ComplexShape.up ℕ)} {n : ℕ}
    {y : K.X n} {z : K.X (n + 1)}
    (hy : K.d n (n + 1) y = z) :
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (K.X (n + 1)) z)) =
      AddCommGrpCat.ofHom ((uliftZMultiplesHom (K.X n) y)) ≫ K.d n (n + 1) := by
  -- Proof comment: evaluating on a generator reduces the owner-level claim to the given element
  -- boundary identity.
  ext t
  change ((uliftZMultiplesHom (K.X (n + 1)) z) t) =
      ConcreteCategory.hom (K.d n (n + 1))
        (((uliftZMultiplesHom (K.X n) y) t))
  rw [uliftZMultiplesHom_apply_apply, uliftZMultiplesHom_apply_apply, map_zsmul, hy]

/-- Helper for Lemma 21.7.3: once the ambient representative of a cycle becomes a boundary on a
cover member, the corresponding restricted homology class vanishes in the evaluated sections
complex over that member. -/
private theorem restrictedSectionsHomologyClass_eq_zero_of_localBoundary
    [HasSheafify J AddCommGrpCat.{max u v}]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F) {U : C} (m : ℕ)
    (q : ((((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).cycles (m + 1)))
    {T : J.Cover U}
    (hT : ∀ a : T.Arrow, ∃ t : (I.cocomplex.X m).1.obj (op a.Y),
      ((I.cocomplex.d m (m + 1)).hom.app (op a.Y)) t =
        (I.cocomplex.X (m + 1)).1.map a.f.op
          (ConcreteCategory.hom
            ((((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              I.cocomplex).iCycles (m + 1)) q)) :
    ∀ a : T.Arrow,
      ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (sectionsComplexRestrictionMap (J := J) I a.f) (m + 1))
        (ConcreteCategory.hom
          ((((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            I.cocomplex).homologyπ (m + 1)) q) = 0 := by
  intro a
  let KU :=
    (((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex)
  let KY :=
    (((siteSectionsFunctor (J := J) a.Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex)
  let φ := sectionsComplexRestrictionMap (J := J) I a.f
  let qRes :
      KY.cycles (m + 1) :=
    ConcreteCategory.hom (HomologicalComplex.cyclesMap φ (m + 1)) q
  let qResHom : AddCommGrpCat.of (ULift.{max u v, 0} ℤ) ⟶ KY.cycles (m + 1) :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (KY.cycles (m + 1))) qRes)
  obtain ⟨t, ht⟩ := hT a
  let tHom : AddCommGrpCat.of (ULift.{max u v, 0} ℤ) ⟶ KY.X m :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (KY.X m)) t)
  have hqRes_iCycles :
      ConcreteCategory.hom (KY.iCycles (m + 1)) qRes =
        (I.cocomplex.X (m + 1)).1.map a.f.op
          (ConcreteCategory.hom (KU.iCycles (m + 1)) q) := by
    -- Proof comment: identify the restricted cycle in the ambient section object using the
    -- canonical `cyclesMap`/`iCycles` compatibility.
    simpa [KU, KY, φ] using
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ (m + 1)) q
  have hboundary :
      qResHom ≫ KY.iCycles (m + 1) = tHom ≫ KY.d m (m + 1) := by
    -- Proof comment: first rewrite the restricted cycle as the image of the ambient cycle, then
    -- upgrade the elementwise local boundary witness to a morphism equality.
    calc
      qResHom ≫ KY.iCycles (m + 1) =
          AddCommGrpCat.ofHom
            ((uliftZMultiplesHom (KY.X (m + 1)))
              (ConcreteCategory.hom (KY.iCycles (m + 1)) qRes)) := by
            simpa [qResHom] using
              uliftMultiplesCompEq (φ := KY.iCycles (m + 1)) qRes
      _ =
          AddCommGrpCat.ofHom
            ((uliftZMultiplesHom (KY.X (m + 1)))
              ((I.cocomplex.X (m + 1)).1.map a.f.op
                (ConcreteCategory.hom (KU.iCycles (m + 1)) q))) := by
            rw [hqRes_iCycles]
      _ = tHom ≫ KY.d m (m + 1) := by
            simpa [KY, tHom] using
              uliftMultiplesBoundaryEqOfElementBoundary
                (K := KY) (n := m) (y := t)
                (z := (I.cocomplex.X (m + 1)).1.map a.f.op
                  (ConcreteCategory.hom (KU.iCycles (m + 1)) q))
                ht
  have hzero : qResHom ≫ KY.homologyπ (m + 1) = 0 := by
    -- Proof comment: once the restricted cycle is exhibited as a boundary, the standard homology
    -- vanishing lemma kills its homology class.
    have hlift :
        KY.liftCycles (qResHom ≫ KY.iCycles (m + 1)) (m + 2) (by simp)
            (by
              rw [hboundary, Category.assoc]
              simp) =
          qResHom := by
      -- Proof comment: both cycle morphisms have the same composite into the ambient section
      -- object, so the mono `iCycles` identifies them.
      apply (cancel_mono (KY.iCycles (m + 1))).1
      simp [Category.assoc]
    have hzeroLift :
        KY.liftCycles (qResHom ≫ KY.iCycles (m + 1)) (m + 2) (by simp)
            (by
              rw [hboundary, Category.assoc]
              simp) ≫
          KY.homologyπ (m + 1) = 0 := by
      simpa using
        (HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
          (K := KY) (k := qResHom ≫ KY.iCycles (m + 1)) (j := m + 2) (hj := by simp)
          (x := tHom) (hx := hboundary))
    simpa [hlift] using hzeroLift
  -- Proof comment: rewrite the target through homology naturality and evaluate the vanishing
  -- morphism on the generator `⟨1⟩ : ULift ℤ`.
  change ConcreteCategory.hom (KU.homologyπ (m + 1) ≫ HomologicalComplex.homologyMap φ (m + 1)) q =
    0
  rw [HomologicalComplex.homologyπ_naturality]
  change ConcreteCategory.hom (KY.homologyπ (m + 1)) qRes = 0
  have hzeroEval := ConcreteCategory.congr_hom hzero ⟨1⟩
  change
    ConcreteCategory.hom (KY.homologyπ (m + 1))
      (((uliftZMultiplesHom (KY.cycles (m + 1))) qRes) ⟨1⟩) = 0 at hzeroEval
  rw [uliftZMultiplesHom_apply_apply, map_zsmul] at hzeroEval
  change (1 : ℤ) • ConcreteCategory.hom (KY.homologyπ (m + 1)) qRes = 0 at hzeroEval
  simpa using hzeroEval

/-- Helper for Lemma 21.7.3: the injective-resolution comparison from the evaluated right-derived
value to the homology of the sections complex commutes with restriction maps. -/
private theorem rightDerivedInclusion_app_obj_iso_homology_sections_complex_naturality
    [HasSheafify J AddCommGrpCat.{max u v}] [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F)
    {U V : C} (i : V ⟶ U) (p : ℕ) :
    ((((sheafToPresheaf J AddCommGrpCat.{max u v}).rightDerived p).obj F).map i.op) ≫
        (CategoryTheory.Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex
          J I V p).hom =
      (CategoryTheory.Sheaf.rightDerivedInclusion_app_obj_iso_homology_sections_complex
          J I U p).hom ≫
        HomologicalComplex.homologyMap
          (sectionsComplexRestrictionMap (J := J) I i) p := by
  -- TODO: combine evaluation naturality of `I.isoRightDerivedObj` with
  -- `NatTrans.app_homology` on the short complex `K.sc p`, but the current transport-normal form
  -- still drifts between `mapIso ... .hom` and `mapHomologyIso ... .symm.hom`.
  sorry

/-- Helper for Lemma 21.7.3: the objectwise comparison from cohomology to the sections-complex
homology model is natural with respect to restriction. -/
private theorem cohomologyAtObjectIsoHomologySections_naturality
    [HasSheafify J AddCommGrpCat.{max u v}] [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v})]
    {F : Sheaf J AddCommGrpCat.{max u v}} (I : InjectiveResolution F)
    {U V : C} (i : V ⟶ U) (p : ℕ) :
    ((F.cohomologyPresheaf p).map i.op) ≫
        (CategoryTheory.Sheaf.cohomologyAtObjectIsoHomologySections (J := J) I V p).hom =
      (CategoryTheory.Sheaf.cohomologyAtObjectIsoHomologySections (J := J) I U p).hom ≫
        HomologicalComplex.homologyMap
          (sectionsComplexRestrictionMap (J := J) I i) p := by
  -- TODO: compose the objectwise evaluation naturality of
  -- `cohomologyAtObjectIsoRightDerivedValue` with the previous right-derived/sections-complex
  -- naturality lemma once the transport-normal form is stabilized.
  sorry

/- Domain-style sampling for Lemma 21.7.3:
- primary domain: sheaf cohomology on a Grothendieck site and the restriction maps carried by the
  cohomology presheaf;
- sampled owner declarations:
  `Sheaf.H'`,
  `Sheaf.cohomologyPresheaf`,
  `SheafOfModules.toSheaf`,
  `RingedSpace.moduleUnderlyingSheaf` (downstream bridge use);
- best owner abstraction: the local-vanishing statement is intrinsically about the abelian sheaf
  cohomology class and its restriction maps, so the owner belongs at `F : Sheaf J AddCommGrpCat`;
  module and ringed-space statements are thin bridge uses through `SheafOfModules.toSheaf` and
  `moduleUnderlyingSheaf`;
- primitive data: the abelian sheaf `F`, the object `U`, the degree `n`, and the class
  `ξ : F.H' n U`;
- derived API: the restriction morphisms in the canonical presheaf `F.cohomologyPresheaf n`.

Source/core/bridge triage:
- `source-facing`: a positive-degree cohomology class becomes zero on some covering;
- `core/canonical`: `Sheaf.H'` and `Sheaf.cohomologyPresheaf`;
- `bridge/view`: forgetting module structure by `SheafOfModules.toSheaf`.

The former module-sheaf statement stored the bridge input `SheafOfModules.toSheaf 𝒪` as if it were
primitive owner data. The theorem is refined to the abelian-sheaf owner layer, and downstream
module/ringed-space files should invoke it through the canonical bridge rather than keeping
parallel copies.
-/

/-- Lemma 21.7.3: for a sheaf of modules on a ringed site, every positive-degree cohomology class
becomes zero after restricting to a suitable covering of the base object. In owner form, this is
the corresponding statement for an abelian sheaf on the site. -/
-- Proof sketch: write `n = m + 1`, choose an injective resolution `I` of `F`, represent `ξ` by a
-- cycle in the sections complex `Γ(U, I^•)`, use exactness in positive degree to refine to a
-- cover where that cycle becomes a boundary, and then transport the local boundary vanishing back
-- to the restricted cohomology classes.
@[stacks 01FW]
theorem exists_cover_restrict_eq_zero_of_positive_cohomology_class
    [HasSheafify J AddCommGrpCat.{max u v}] [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]
    (F : Sheaf J AddCommGrpCat.{max u v}) {U : C} {n : ℕ} (hn : 0 < n) (ξ : F.H' n U) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      (((F.cohomologyPresheaf n).map I.f.op) ξ = 0) := by
  letI : HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v}) := by
    let _ : EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}) :=
      siteAbelianSheaf_hasEnoughInjectives J
    infer_instance
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let ξ' : F.H' (m + 1) U :=
    cast (by simp [Sheaf.H']) ξ
  let I : InjectiveResolution F := injectiveResolution F
  let KU :=
    (((siteSectionsFunctor (J := J) U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex)
  let ξU : (F.cohomologyPresheaf (m + 1)).obj (op U) :=
    cast (by simp [Sheaf.H']) ξ
  let eU :
      F.H' (m + 1) U ≅ KU.homology (m + 1) :=
    CategoryTheory.Sheaf.cohomologyAtObjectIsoHomologySections (J := J) I U (m + 1)
  let ξK : KU.homology (m + 1) := ConcreteCategory.hom eU.hom ξ'
  obtain ⟨q, hq⟩ :=
    (AddCommGrpCat.epi_iff_surjective (KU.homologyπ (m + 1))).1 inferInstance ξK
  have hcycle :
      ((I.cocomplex.d (m + 1) (m + 2)).hom.app (op U))
          (ConcreteCategory.hom (KU.iCycles (m + 1)) q) = 0 := by
    -- Proof comment: a cycle representative is, by definition, killed by the next differential.
    simpa [KU] using ConcreteCategory.congr_hom (KU.iCycles_d (m + 1) (m + 2)) q
  obtain ⟨T, hT⟩ :=
    injectiveResolutionCoverLiftsCycle (J := J) F I m
      (ConcreteCategory.hom (KU.iCycles (m + 1)) q) hcycle
  have hξK :
      ξK = ConcreteCategory.hom (KU.homologyπ (m + 1)) q := by
    simpa [ξK] using hq.symm
  have hzeroHomology :
      ∀ a : T.Arrow,
        ConcreteCategory.hom
            (HomologicalComplex.homologyMap
              (sectionsComplexRestrictionMap (J := J) I a.f) (m + 1))
            ξK = 0 := by
    intro a
    -- Proof comment: the local boundary witnesses kill the restricted homology class on each
    -- cover member.
    rw [hξK]
    exact restrictedSectionsHomologyClass_eq_zero_of_localBoundary (J := J) I m q hT a
  refine ⟨T, ?_⟩
  intro a
  let ξa : F.H' (m + 1) a.Y :=
    ConcreteCategory.hom ((F.cohomologyPresheaf (m + 1)).map a.f.op) ξU
  let eY :
      F.H' (m + 1) a.Y ≅
        ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ)
            (m + 1)).obj
          (((siteSectionsFunctor (J := J) a.Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            I.cocomplex)) :=
    CategoryTheory.Sheaf.cohomologyAtObjectIsoHomologySections (J := J) I a.Y (m + 1)
  have hnat :
      ConcreteCategory.hom eY.hom ξa =
        ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (sectionsComplexRestrictionMap (J := J) I a.f) (m + 1))
          ξK :=
    by
      -- TODO: once `cohomologyAtObjectIsoHomologySections_naturality` is restored, evaluate it on
      -- `ξU` to identify the restricted cohomology class with the already-vanishing homology
      -- class.
      sorry
  have hleftZero :
      ConcreteCategory.hom eY.hom ξa = 0 := by
    -- Proof comment: after transporting to the sections-complex homology model, the restricted
    -- class is exactly the homology class already shown to vanish.
    exact hnat.trans (hzeroHomology a)
  have hξa : ξa = 0 := by
    -- Proof comment: the comparison map is an isomorphism, so it reflects the zero class.
    have hzeroMap : ConcreteCategory.hom eY.hom ξa = ConcreteCategory.hom eY.hom 0 := by
      calc
        ConcreteCategory.hom eY.hom ξa = 0 := hleftZero
        _ = ConcreteCategory.hom eY.hom 0 := by
          symm
          exact map_zero (ConcreteCategory.hom eY.hom)
    apply (AddCommGrpCat.mono_iff_injective eY.hom).1 inferInstance
    exact hzeroMap
  have hres :
      ConcreteCategory.hom ((F.cohomologyPresheaf (m + 1)).map a.f.op) ξU = 0 := by
    -- Proof comment: rewrite the normalized local class back to the presheaf restriction map.
    simpa [ξa] using hξa
  -- Proof comment: unfold the normalized degree and representative to match the theorem surface.
  simpa [ξU, Sheaf.H'] using hres

end CategoryTheory.Sheaf
