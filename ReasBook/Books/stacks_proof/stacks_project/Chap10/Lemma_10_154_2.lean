import Mathlib
import StacksProject_2024.Chap10.Lemma_10_138_15
import StacksProject_2024.Chap10.Lemma_10_127_7
import StacksProject_2024.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty Limits
open CommRingCat
open scoped TensorProduct

universe u v w z

namespace RingHom

/-!
The categorical part of the proof is local to this file: `CommRingCat.etale` is stable under
composition, stable under cobase change, and finitely presentable. The remaining file-local
blocker is now the direct finite-test composition argument for the source-facing wrapper, not the
previous common-`ULift` transport bridge.
-/

/-- Helper for Chap10 Lemma 10 154 2: étale morphisms of commutative rings are stable under
categorical composition. -/
private instance etale_isStableUnderComposition :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    -- Reduce the categorical composition statement to the ring-hom composition theorem.
    dsimp [CommRingCat.etale] at hf hg ⊢
    exact RingHom.Etale.stableUnderComposition f.hom g.hom hf hg

/-- Helper for Chap10 Lemma 10 154 2: étale morphisms of commutative rings are stable under
cobase change. -/
private instance etale_isStableUnderCobaseChange :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}).IsStableUnderCobaseChange := by
  -- Translate the ring-hom base-change theorem through the standard morphism-property bridge.
  simpa [CommRingCat.etale, RingHom.toMorphismProperty] using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Etale.isStableUnderBaseChange

/-- Helper for Chap10 Lemma 10 154 2: an étale morphism in `CommRingCat` is finitely
presentable as a morphism. -/
private lemma etale_le_isFinitelyPresentable :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}) ≤
      MorphismProperty.isFinitelyPresentable.{u} CommRingCat := by
  intro X Y f hf
  -- Extract finite presentation from the ring-hom characterization of étaleness.
  dsimp [CommRingCat.etale] at hf
  exact CommRingCat.isFinitelyPresentable_hom f
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).2.2

/-- Helper for Chap10 Lemma 10 154 2: under the standard finite-accessibility and spreading
prerequisites, ind-étale morphisms in one `CommRingCat` universe are stable under composition. -/
private lemma indEtale_isStableUnderComposition_of_preIndSpreads
    [∀ X : CommRingCat.{u}, IsFinitelyAccessibleCategory.{u} (Under X)]
    [MorphismProperty.PreIndSpreads.{u}
      (CommRingCat.etale : MorphismProperty CommRingCat.{u})] :
    (MorphismProperty.ind.{u}
      (CommRingCat.etale : MorphismProperty CommRingCat.{u})).IsStableUnderComposition := by
  -- The generic morphism-property theorem supplies the same-universe composition closure once
  -- étale finite presentation, cobase-change stability, and spread-out descent are available.
  exact MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads
    etale_le_isFinitelyPresentable

/-- Helper for Chap10 Lemma 10 154 2: a ring homomorphism transported through matching `ULift`
equivalences. -/
private abbrev commonLiftRingHom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : ULift.{z} R →+* ULift.{z} S :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

/-- Helper for Chap10 Lemma 10 154 2: the raw map used by
`RingHom.IsFilteredColimitOfEtale`, with the source lifted to the target universe and the target
lifted to the source universe. -/
private abbrev wrapperLiftRingHom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : ULift.{v} R →+* ULift.{u} S :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

/-- Helper for Chap10 Lemma 10 154 2: the common `ULift` transport sends a lifted element to the
lift of its image. -/
private lemma commonLiftRingHom_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : ULift.{z} R) :
    commonLiftRingHom.{u, v, z} f x = ULift.up (f x.down) := by
  -- Normalize the transported map to its concrete action on the underlying element.
  rfl

/-- Helper for Chap10 Lemma 10 154 2: the wrapper lift map has the expected concrete action. -/
private lemma wrapperLiftRingHom_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : ULift.{v} R) :
    wrapperLiftRingHom f x = ULift.up (f x.down) := by
  -- Normalize the asymmetric wrapper map to its action on underlying elements.
  rfl

/-- Helper for Chap10 Lemma 10 154 2: the asymmetric wrapper map is the algebra map installed
by the source-facing `RingHom.IsFilteredColimitOfEtale` owner. -/
private lemma wrapperLiftRingHom_eq_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra R (ULift.{u} S) := ULift.algebra
    let _ : Algebra (ULift.{v} R) (ULift.{u} S) := ULift.algebra' R (ULift.{u} S)
    wrapperLiftRingHom f = algebraMap (ULift.{v} R) (ULift.{u} S) := by
  -- The wrapper definition and the locally installed algebra map unfold to the same transported
  -- ring homomorphism.
  rfl

/-- Helper for Chap10 Lemma 10 154 2: applying the standard `CommRingCat` universe-lift functor
to an étale morphism again gives an étale morphism. -/
private lemma commRingCat_etale_uliftFunctor_map
    {X Y : CommRingCat.{u}} (f : X ⟶ Y) (hf : CommRingCat.etale f) :
    CommRingCat.etale ((commRingCat_uliftFunctor.{u, v}).map f) := by
  -- Expand the categorical property to the ring-hom property and transport it through the two
  -- canonical `ULift` ring equivalences.
  dsimp [CommRingCat.etale, commRingCat_uliftFunctor] at hf ⊢
  letI algSource :
      Algebra (ULift.{v} X) X :=
    (ULift.ringEquiv : ULift.{v} X ≃+* X).toRingHom.toAlgebra
  letI algMiddle :
      Algebra X Y :=
    f.hom.toAlgebra
  letI algComposite :
      Algebra (ULift.{v} X) Y :=
    ((f.hom.comp (ULift.ringEquiv.toRingHom : ULift.{v} X →+* X))).toAlgebra
  have hsource : Algebra.Etale (ULift.{v} X) X :=
    (RingHom.Etale.of_bijective ULift.ringEquiv.bijective :
      (ULift.ringEquiv.toRingHom : ULift.{v} X →+* X).Etale)
  have hmiddle : Algebra.Etale X Y := hf
  have hsourceMiddleTower : IsScalarTower (ULift.{v} X) X Y :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  have hcomposite : Algebra.Etale (ULift.{v} X) Y := by
    -- Compose étaleness for the source equivalence with the original étale map.
    exact @Algebra.Etale.comp (ULift.{v} X) X Y _ _ algSource _ algComposite algMiddle
      hsourceMiddleTower hsource hmiddle
  letI algTarget :
      Algebra Y (ULift.{v} Y) :=
    (ULift.ringEquiv.symm : Y ≃+* ULift.{v} Y).toRingHom.toAlgebra
  letI algLiftedComposite :
      Algebra (ULift.{v} X) (ULift.{v} Y) :=
    ((ULift.ringEquiv.symm.toRingHom : Y →+* ULift.{v} Y).comp
      (f.hom.comp (ULift.ringEquiv.toRingHom : ULift.{v} X →+* X))).toAlgebra
  have htarget : Algebra.Etale Y (ULift.{v} Y) :=
    (RingHom.Etale.of_bijective ULift.ringEquiv.symm.bijective :
      (ULift.ringEquiv.symm.toRingHom : Y →+* ULift.{v} Y).Etale)
  have hcompositeTargetTower : IsScalarTower (ULift.{v} X) Y (ULift.{v} Y) :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  have hlifted : Algebra.Etale (ULift.{v} X) (ULift.{v} Y) := by
    -- Compose the already transported source map with the target equivalence.
    exact @Algebra.Etale.comp (ULift.{v} X) Y (ULift.{v} Y) _ _ algComposite _
      algLiftedComposite algTarget hcompositeTargetTower hcomposite htarget
  -- The resulting composite is exactly the morphism produced by `commRingCat_uliftFunctor`.
  simpa [RingHom.Etale, RingHom.ulift] using hlifted

/-- Helper for Chap10 Lemma 10 154 2: an étale algebra over a same-universe filtered colimit
descends to an étale algebra over one stage, with the original algebra recovered by tensor base
change. -/
private theorem etale_isBaseChange_of_stage_of_isColimit
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (B : Type w) [CommRing B] [Algebra c.pt B] [Algebra.Etale c.pt B] :
    ∃ (j : J) (B_j : Type u) (_ : CommRing B_j) (_ : Algebra (F.obj j) B_j),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Algebra.Etale (F.obj j) B_j ∧ Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj j] B_j) := by
  -- First descend the étale algebra to a finitely generated `ℤ`-subalgebra of the colimit.
  let α := ulift_integers_to_ring_diagram (F := F)
  obtain ⟨A₀, B₀, _instB₀, _instAlgB₀, hA₀fg, _instEtaleB₀, hB⟩ :=
    Algebra.Etale.exists_subalgebra_fg (R := ℤ) (A := c.pt) (B := B)
  haveI : Algebra.FinitePresentation ℤ A₀ := by
    -- Finite generation over the noetherian ring `ℤ` upgrades to finite presentation.
    have hfiniteType : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀fg
    exact (Algebra.FinitePresentation.of_finiteType (R := ℤ) (A := A₀)).mp hfiniteType
  have hA₀fpZ : (algebraMap ℤ A₀).FinitePresentation := by
    -- Rephrase algebra finite presentation as the ring-hom finite-presentation predicate.
    simpa [RingHom.finitePresentation_algebraMap] using
      (show Algebra.FinitePresentation ℤ A₀ from inferInstance)
  have hA₀fp : (ulift_int_hom (A := A₀)).FinitePresentation := by
    -- Transport finite presentation across the canonical `ULift ℤ ≃+* ℤ` equivalence.
    rw [show ulift_int_hom (A := A₀) =
        (algebraMap ℤ A₀).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom by rfl]
    exact RingHom.FinitePresentation.comp hA₀fpZ
      (RingHom.FinitePresentation.of_bijective
        (ULift.ringEquiv.{0, u} (R := ℤ)).bijective)
  have hcompat :
      ∀ i,
        CommRingCat.ofHom (ulift_int_hom (A := A₀)) ≫ CommRingCat.ofHom A₀.val =
          α.app i ≫ c.ι.app i := by
    intro i
    -- Both composites are the canonical map from `ULift ℤ` to the colimit ring.
    apply CommRingCat.hom_ext
    ext n
    simpa [ulift_int_hom, CommRingCat.hom_comp] using
      (map_intCast ((c.ι.app i).hom) n.down).symm
  obtain ⟨j, φj, hφj_alg, hφj_factor⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := CommRingCat.of (ULift.{u} ℤ)) (F := F) (α := α)
      (S := CommRingCat.of A₀) (f := CommRingCat.ofHom (ulift_int_hom (A := A₀)))
      (c := c) (hc := hc) hA₀fp (CommRingCat.ofHom A₀.val) hcompat
  letI : Algebra A₀ (F.obj j) := φj.hom.toAlgebra
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let _ := hφj_alg
  have hstage_eq :
      algebraMap A₀ c.pt = (algebraMap (F.obj j) c.pt).comp (algebraMap A₀ (F.obj j)) := by
    -- The factorization identity is the scalar-tower compatibility for the chosen stage.
    ext a
    simpa [CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra] using
      congrArg (fun k : CommRingCat.of A₀ ⟶ c.pt => k.hom a) hφj_factor
  haveI : IsScalarTower A₀ (F.obj j) c.pt := IsScalarTower.of_algebraMap_eq' hstage_eq
  let B_j : Type u := (F.obj j) ⊗[A₀] B₀
  refine ⟨j, B_j, inferInstance, inferInstance, ?_⟩
  constructor
  · -- Étaleness descends to the stage by tensor base change from the finite `A₀`-model.
    infer_instance
  · -- The original algebra is recovered by the standard tensor cancellation equivalence.
    refine ⟨hB.some.trans ?_⟩
    exact (Algebra.TensorProduct.cancelBaseChange A₀ (F.obj j) c.pt c.pt B₀).symm

/-- Helper for Chap10 Lemma 10 154 2: common `ULift` transport preserves composition
definitionally. -/
private lemma commonLiftRingHom_comp
    {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (commonLiftRingHom.{v, w, z} g).comp (commonLiftRingHom.{u, v, z} f) =
      commonLiftRingHom.{u, w, z} (g.comp f) := by
  -- Compare both lifted composites on elements; the canonical `ULift` maps compute literally.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 154 2: an asymmetric wrapper `ind` witness transports to the
same-object-universe common `ULift` wrapper. -/
private lemma commonLiftIndEtale_of_wrapperIndEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (h : MorphismProperty.ind.{z, max u v, max u v + 1} CommRingCat.etale
      (CommRingCat.ofHom (wrapperLiftRingHom f))) :
    MorphismProperty.ind.{z, max u v, max u v + 1} CommRingCat.etale
      (CommRingCat.ofHom (commonLiftRingHom.{u, v, max u v} f)) := by
  -- Transport the source and target of the asymmetric wrapper to the common `ULift` spelling.
  let eR : CommRingCat.of (ULift.{max u v} R) ≅ CommRingCat.of (ULift.{v} R) :=
    RingEquiv.toCommRingCatIso
      ((ULift.ringEquiv : ULift.{max u v} R ≃+* R).trans
        (ULift.ringEquiv.symm : R ≃+* ULift.{v} R))
  let eS : CommRingCat.of (ULift.{u} S) ≅ CommRingCat.of (ULift.{max u v} S) :=
    RingEquiv.toCommRingCatIso
      ((ULift.ringEquiv : ULift.{u} S ≃+* S).trans
        (ULift.ringEquiv.symm : S ≃+* ULift.{max u v} S))
  have hTransported :
      MorphismProperty.ind.{z, max u v, max u v + 1} CommRingCat.etale
        (eR.hom ≫ CommRingCat.ofHom (wrapperLiftRingHom f) ≫ eS.hom) := by
    -- The `ind` property respects isomorphisms because the underlying étale property does.
    exact MorphismProperty.RespectsIso.postcomp _ eS.hom _
      (MorphismProperty.RespectsIso.precomp _ eR.hom _ h)
  -- The transported composite acts by `x ↦ ULift.up (f x.down)`, hence is the common lift.
  simpa [eR, eS, commonLiftRingHom, wrapperLiftRingHom] using hTransported

/-- Helper for Chap10 Lemma 10 154 2: an ind-étale witness indexed in one universe is also
available in any larger universe containing a small model of the same filtered category. -/
private lemma indEtaleOfSmallerIndex
    {X Y : CommRingCat.{u}} (f : X ⟶ Y)
    (h : MorphismProperty.ind.{z, u, u + 1} CommRingCat.etale f) :
    MorphismProperty.ind.{max u z, u, u + 1} CommRingCat.etale f := by
  -- Reindex the existing filtered presentation along `AsSmall`, which raises both object and
  -- morphism universes while preserving filteredness and the colimit cocone.
  rcases h with ⟨J, _hJcat, _hJfilt, D, t, s, hs, hmem⟩
  letI : (AsSmall.down : AsSmall.{max u z} J ⥤ J).IsEquivalence :=
    (AsSmall.equiv (C := J)).isEquivalence_inverse
  letI : (AsSmall.down : AsSmall.{max u z} J ⥤ J).Final := by
    simpa using
      (Functor.final_equivalence_comp (AsSmall.down : AsSmall.{max u z} J ⥤ J) (𝟭 J))
  let D' : AsSmall.{max u z} J ⥤ CommRingCat.{u} := AsSmall.down ⋙ D
  let t' : (Functor.const (AsSmall.{max u z} J)).obj X ⟶ D' :=
    { app j := t.app (ULift.down j)
      naturality j j' a := by
        exact t.naturality (ULift.down a) }
  let s' : D' ⟶ (Functor.const (AsSmall.{max u z} J)).obj Y :=
    { app j := s.app (ULift.down j)
      naturality j j' a := by
        exact s.naturality (ULift.down a) }
  have hs' : IsColimit (Cocone.mk Y s') := by
    -- The finality equivalence transports the original colimit to the raised index category.
    simpa [s'] using
      ((Functor.Final.isColimitWhiskerEquiv AsSmall.down (Cocone.mk Y s)).symm hs)
  refine ⟨AsSmall.{max u z} J, inferInstance, inferInstance, D', t', s', hs', ?_⟩
  -- Each raised stage is just the corresponding old stage, so the étale condition is unchanged.
  intro j
  exact hmem (ULift.down j)

section

/- Domain-style sampling:
* primary domain: composition closure for ind-étale morphisms in commutative algebra;
* owner declarations inspected:
  - `CategoryTheory.MorphismProperty.ind`;
  - `CategoryTheory.MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads`;
  - `CommRingCat.etale`;
  - `RingHom.IsFilteredColimitOfEtale`.
* owner decision:
  - `source-facing`: `RingHom.isFilteredColimitOfEtale_comp`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the `ULift`-based same-universe presentation hidden inside
    `RingHom.IsFilteredColimitOfEtale`.

Primitive data are just the composable ring maps `f`, `g` and their owner-level ind-étale
hypotheses. The universe-lift bookkeeping is derived bridge data and should stay hidden in the
source-facing owner rather than reappearing as a same-universe restriction on `A`, `B`, and `C`.
-/

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

-- Proof sketch: present `B` as a filtered colimit of étale `A`-algebras and `C` as a filtered
-- colimit of étale `B`-algebras. For a finitely presented `A`-algebra mapping to `C`, first factor
-- through some étale `B`-stage by finite presentation, then descend that stage to an étale
-- `A`-algebra by the base-change descent result of Lemma `10.143.3`. The factorization criterion
-- from Lemma `10.127.4` then shows that `A → C` is a filtered colimit of étale maps.
/-- Chap10 Lemma 10 154 2: the composite of two ring maps that are filtered colimits of étale
ring maps is again a filtered colimit of étale ring maps. -/
@[stacks 0BSI]
theorem isFilteredColimitOfEtale_comp
    (f : A →+* B) (g : B →+* C)
    (hf : RingHom.IsFilteredColimitOfEtale.{u, v, w} f)
    (hg : RingHom.IsFilteredColimitOfEtale.{v, w, u} g) :
    RingHom.IsFilteredColimitOfEtale.{u, w, v} (g.comp f) := by
  -- Route correction: the common-`ULift` route forced a global universe-lowering theorem for
  -- arbitrary ind presentations.  The remaining proof should stay in the native wrapper
  -- universes and run the finite-test argument of `ind_of_preIndSpreads` directly.
  have hfWrapper :
      MorphismProperty.ind.{w, max u v, max u v + 1} CommRingCat.etale
        (CommRingCat.ofHom (wrapperLiftRingHom f)) := by
    -- Normalize the first source-facing hypothesis to the explicit asymmetric wrapper map.
    dsimp [RingHom.IsFilteredColimitOfEtale] at hf
    simpa [wrapperLiftRingHom_eq_algebraMap] using hf
  have hgWrapper :
      MorphismProperty.ind.{u, max v w, max v w + 1} CommRingCat.etale
        (CommRingCat.ofHom (wrapperLiftRingHom g)) := by
    -- Normalize the second source-facing hypothesis in the same wrapper form.
    dsimp [RingHom.IsFilteredColimitOfEtale] at hg
    simpa [wrapperLiftRingHom_eq_algebraMap] using hg
  have hfCommonWrapper :
      MorphismProperty.ind.{w, max u v, max u v + 1} CommRingCat.etale
        (CommRingCat.ofHom (commonLiftRingHom.{u, v, max u v} f)) := by
    -- Move the first presentation to the same-object-universe wrapper used for common lifts.
    exact commonLiftIndEtale_of_wrapperIndEtale f hfWrapper
  have hgCommonWrapper :
      MorphismProperty.ind.{u, max v w, max v w + 1} CommRingCat.etale
        (CommRingCat.ofHom (commonLiftRingHom.{v, w, max v w} g)) := by
    -- Move the second presentation to its corresponding same-object-universe wrapper.
    exact commonLiftIndEtale_of_wrapperIndEtale g hgWrapper
  dsimp [RingHom.IsFilteredColimitOfEtale] at hf hg ⊢
  -- TODO: prove the direct finite-test composition step here.  The remaining construction should
  -- consume `hfCommonWrapper` and `hgCommonWrapper`: factor a finitely presentable test through a
  -- stage of the second presentation, spread that one finite étale stage over the first
  -- presentation using `etale_isBaseChange_of_stage_of_isColimit`, then assemble the native
  -- wrapper `ind` witness for `wrapperLiftRingHom (g.comp f)`.
  sorry

end

end RingHom
