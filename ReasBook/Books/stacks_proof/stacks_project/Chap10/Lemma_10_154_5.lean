import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_154_3
import stacks_proof.stacks_project.Chap10.Lemma_10_143_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty Limits
open CommRingCat

universe u v w z uA uB uC

namespace RingHom

/-- Helper for Chap10 Lemma 10 154 5: categorical common-base étaleness descends to the
comparison map. -/
private lemma commRingCatEtale_of_etale_over_common_base
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ B) (a : A ⟶ B)
    (_hf : CommRingCat.etale f) (_hg : CommRingCat.etale g) (h : f ≫ a = g) :
    CommRingCat.etale a := by
  -- Install the algebra structures carried by the three ring maps so the categorical square is
  -- exactly the scalar-tower compatibility required by the algebra theorem.
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R B := g.hom.toAlgebra
  letI : Algebra A B := a.hom.toAlgebra
  have hTower : IsScalarTower R A B := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    simpa [RingHom.algebraMap_toAlgebra] using (congrArg CommRingCat.Hom.hom h).symm
  have hEtale : Algebra.Etale A B := by
    exact Algebra.etale_of_etale_over_common_base
  simpa [CommRingCat.etale, RingHom.algebraMap_toAlgebra] using hEtale

/-- Helper for Chap10 Lemma 10 154 5: étale morphisms of commutative rings are stable under
categorical composition. -/
private instance commRingCatEtale_isStableUnderComposition :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    -- Reduce categorical composition to the ring-hom composition theorem.
    dsimp [CommRingCat.etale] at hf hg ⊢
    exact RingHom.Etale.stableUnderComposition f.hom g.hom hf hg

/-- Helper for Chap10 Lemma 10 154 5: étale morphisms of commutative rings are stable under
cobase change. -/
private instance commRingCatEtale_isStableUnderCobaseChange :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}).IsStableUnderCobaseChange := by
  -- Translate the ring-hom base-change theorem through the standard categorical bridge.
  simpa [CommRingCat.etale, RingHom.toMorphismProperty] using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Etale.isStableUnderBaseChange

/-- Helper for Chap10 Lemma 10 154 5: finite-stage étale maps cancel over a common base. -/
private instance commRingCatEtale_hasOfPrecompProperty :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}).HasOfPrecompProperty
      (CommRingCat.etale : MorphismProperty CommRingCat.{u}) where
  of_precomp {X Y Z} f g hf hfg := by
    -- View `f`, `f ≫ g`, and `g` as the two étale maps from the common source and their
    -- comparison map; Lemma 10.143.8 supplies the finite-stage cancellation.
    exact commRingCatEtale_of_etale_over_common_base f (f ≫ g) g hf hfg rfl

/-- Helper for Chap10 Lemma 10 154 5: an étale morphism in `CommRingCat` is finitely
presentable as a morphism. -/
private lemma commRingCatEtale_le_isFinitelyPresentable :
    (CommRingCat.etale : MorphismProperty CommRingCat.{u}) ≤
      MorphismProperty.isFinitelyPresentable.{u} CommRingCat := by
  intro X Y f hf
  -- Extract finite presentation from the ring-hom characterization of étaleness.
  dsimp [CommRingCat.etale] at hf
  exact CommRingCat.isFinitelyPresentable_hom f
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).2.2

/-- Helper for Chap10 Lemma 10 154 5: finite-stage étale maps cancel against an ind-étale
map over a common base. -/
private theorem commRingCatIndEtale_of_etale_commonBase
    {X Y Z : CommRingCat.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (a : Y ⟶ Z)
    (ha : f ≫ a = g) (hf : CommRingCat.etale f)
    (hg : MorphismProperty.ind.{u} CommRingCat.etale g) :
    MorphismProperty.ind.{u} CommRingCat.etale a := by
  -- Unpack the ind-presentation of `X → Z`; finite presentation of the étale map `X → Y`
  -- factors `Y → Z` through one stage of that presentation.
  dsimp [MorphismProperty.ind] at hg ⊢
  rcases hg with ⟨J, hJcat, hJfiltered, D, t, s, hs, hst⟩
  letI : SmallCategory J := hJcat
  letI : IsFiltered J := hJfiltered
  have hfFp : MorphismProperty.isFinitelyPresentable.{u} CommRingCat f :=
    commRingCatEtale_le_isFinitelyPresentable f hf
  have hfac : ∀ j, t.app j ≫ s.app j = f ≫ a := by
    intro j
    exact (hst j).2.trans ha.symm
  obtain ⟨j, q, hq_source, hq_target⟩ :=
    MorphismProperty.exists_hom_of_isFinitelyPresentable hs hfFp t a hfac
  -- Restrict the original filtered presentation to the cofinal tail below the chosen stage.
  let Dtail : Under j ⥤ CommRingCat.{u} := Under.forget j ⋙ D
  let stail : Dtail ⟶ (Functor.const (Under j)).obj Z :=
    ((Cocone.mk Z s).whisker (Under.forget j)).ι
  have hstail : IsColimit (Cocone.mk Z stail) := by
    simpa [stail] using
      ((Functor.Final.isColimitWhiskerEquiv (Under.forget j) (Cocone.mk Z s)).symm hs)
  let ttail : (Functor.const (Under j)).obj Y ⟶ Dtail :=
    { app := fun k => q ≫ D.map k.hom
      naturality := by
        intro k l e
        dsimp [Dtail]
        rw [Category.id_comp]
        have he : l.hom = k.hom ≫ e.right := by
          simpa using e.w
        simpa [he, D.map_comp, Category.assoc] }
  refine ⟨Under j, inferInstance, inferInstance, Dtail, ttail, stail, hstail, ?_⟩
  intro k
  constructor
  · have hbase : f ≫ ttail.app k = t.app k.right := by
      dsimp [ttail]
      rw [← Category.assoc, hq_source]
      simpa using (t.naturality k.hom).symm
    -- Each tail-stage map `Y → D k` is étale by finite common-base cancellation.
    exact commRingCatEtale_of_etale_over_common_base f (t.app k.right) (ttail.app k)
      hf (hst k.right).1 hbase
  · have hs_eq : D.map k.hom ≫ s.app k.right = s.app j := by
      simpa using s.naturality k.hom
    dsimp [ttail, stail]
    exact (Category.assoc q (D.map k.hom) (s.app k.right)).trans
      ((congrArg (fun m => q ≫ m) hs_eq).trans hq_target)

section

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Helper for Chap10 Lemma 10 154 5: after moving `R`, `A`, and `B` to one `ULift`
universe, the two canonical lifted algebra maps from the common base compose to the lifted
`R → B` algebra map. -/
private lemma uliftAlgebraMap_comp_commonBase :
    let _ : Algebra R (ULift.{z, v} A) := ULift.algebra
    let _ : Algebra (ULift.{z, u} R) (ULift.{z, v} A) :=
      ULift.algebra' R (ULift.{z, v} A)
    let _ : Algebra A (ULift.{z, w} B) := ULift.algebra
    let _ : Algebra (ULift.{z, v} A) (ULift.{z, w} B) :=
      ULift.algebra' A (ULift.{z, w} B)
    let _ : Algebra R (ULift.{z, w} B) := ULift.algebra
    let _ : Algebra (ULift.{z, u} R) (ULift.{z, w} B) :=
      ULift.algebra' R (ULift.{z, w} B)
    (algebraMap (ULift.{z, u} R) (ULift.{z, w} B)) =
      (algebraMap (ULift.{z, v} A) (ULift.{z, w} B)).comp
        (algebraMap (ULift.{z, u} R) (ULift.{z, v} A)) := by
  -- All three lifted algebra maps are transported from the original scalar tower, so the
  -- comparison is pointwise definitional after unfolding the local lifted instances.
  dsimp only
  ext x
  simpa [RingHom.comp_apply] using (IsScalarTower.algebraMap_apply R A B x.down)

/-- Helper for Chap10 Lemma 10 154 5: a ring homomorphism transported through matching `ULift`
equivalences to a single common universe. -/
private abbrev commonLiftRingHom {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : ULift.{z} R →+* ULift.{z} S :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

/-- Helper for Chap10 Lemma 10 154 5: common `ULift` transport sends a lifted element to the
lift of its image. -/
private lemma commonLiftRingHom_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : ULift.{z} R) :
    commonLiftRingHom.{u, v, z} f x = ULift.up (f x.down) := by
  -- Unfold the transported map once; both canonical `ULift` equivalences compute directly.
  rfl

/-- Helper for Chap10 Lemma 10 154 5: the common `ULift` transport is the algebra map for
the transported algebra structure. -/
private lemma commonLiftRingHom_eq_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra R (ULift.{z} S) := ULift.algebra
    let _ : Algebra (ULift.{z} R) (ULift.{z} S) := ULift.algebra' R (ULift.{z} S)
    commonLiftRingHom.{u, v, z} f = algebraMap (ULift.{z} R) (ULift.{z} S) := by
  -- Normalize the boundary transport once, so later proofs can rewrite through the named
  -- algebra-map bridge rather than unfolding the transported ring equivalences repeatedly.
  dsimp only
  rfl

/-- Helper for Chap10 Lemma 10 154 5: common `ULift` transport preserves composition
definitionally. -/
private lemma commonLiftRingHom_comp
    {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    (commonLiftRingHom.{v, w, z} g).comp (commonLiftRingHom.{u, v, z} f) =
      commonLiftRingHom.{u, w, z} (g.comp f) := by
  -- Compare both transported composites on lifted elements; the action lemma makes the two
  -- sides syntactically identical.
  ext x
  rfl

/-- Helper for Chap10 Lemma 10 154 5: in the minimal common object universe, the raw categorical
common-lift presentation is equivalent to the source-facing ind-étale wrapper. -/
private lemma rawIndCommonLift_iff_isFilteredColimitOfEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    MorphismProperty.ind.{z, max u v, max u v + 1} CommRingCat.etale
        (CommRingCat.ofHom (commonLiftRingHom.{u, v, max u v} f)) ↔
      RingHom.IsFilteredColimitOfEtale.{u, v, z} f := by
  -- Install the algebra structures used by the source-facing wrapper so the wrapper map has a
  -- concrete raw `CommRingCat` spelling.
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift.{u} S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift.{u} S) := ULift.algebra' R (ULift.{u} S)
  let eR : CommRingCat.of (ULift.{v} R) ≅ CommRingCat.of (ULift.{max u v} R) :=
    RingEquiv.toCommRingCatIso
      ((ULift.ringEquiv : ULift.{v} R ≃+* R).trans
        (ULift.ringEquiv.symm : R ≃+* ULift.{max u v} R))
  let eS : CommRingCat.of (ULift.{u} S) ≅ CommRingCat.of (ULift.{max u v} S) :=
    RingEquiv.toCommRingCatIso
      ((ULift.ringEquiv : ULift.{u} S ≃+* S).trans
        (ULift.ringEquiv.symm : S ≃+* ULift.{max u v} S))
  constructor
  · intro h
    have hTransported :
        MorphismProperty.ind.{z, max u v, max u v + 1} CommRingCat.etale
          (eR.hom ≫ CommRingCat.ofHom (commonLiftRingHom.{u, v, max u v} f) ≫
            eS.inv) := by
      -- Move the common-lift raw witness back to the asymmetric `ULift` spelling used by
      -- `RingHom.IsFilteredColimitOfEtale`.
      exact MorphismProperty.RespectsIso.precomp _ eR.hom _
        (MorphismProperty.RespectsIso.postcomp _ eS.inv _ h)
    dsimp [RingHom.IsFilteredColimitOfEtale]
    simpa [commonLiftRingHom, eR, eS, RingHom.algebraMap_toAlgebra] using hTransported
  · intro h
    dsimp [RingHom.IsFilteredColimitOfEtale] at h
    have hTransported :
        MorphismProperty.ind.{z, max u v, max u v + 1} CommRingCat.etale
          (eR.inv ≫ CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift.{u} S)) ≫
            eS.hom) := by
      -- Move the wrapper raw witness to the symmetric common-lift spelling.
      exact MorphismProperty.RespectsIso.precomp _ eR.inv _
        (MorphismProperty.RespectsIso.postcomp _ eS.hom _ h)
    simpa [commonLiftRingHom, eR, eS, RingHom.algebraMap_toAlgebra] using hTransported

/-- Helper for Chap10 Lemma 10 154 5: at the minimal common `ULift` universe, common transport
is exactly the same source-facing filtered-colimit-of-étale property. -/
private lemma commonLiftRingHom_min_isFilteredColimitOfEtale_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    RingHom.IsFilteredColimitOfEtale.{max u v, max u v, z}
        (commonLiftRingHom.{u, v, max u v} f) ↔
      RingHom.IsFilteredColimitOfEtale.{u, v, z} f := by
  -- Put the common-lift map in the algebra-map normal form expected by Lemma 10.154.3.
  let _ : Algebra (ULift.{max u v} R) (ULift.{max u v} S) :=
    (commonLiftRingHom.{u, v, max u v} f).toAlgebra
  -- The raw categorical bridge above and the same-universe wrapper bridge have identical
  -- left-hand raw `ind` statements after this normalization.
  have hWrapper :=
    (raw_ind_etale_algebraMap_iff_isFilteredColimitOfEtale.{max u v, z}
      (R := ULift.{max u v} R) (A := ULift.{max u v} S))
  simpa [RingHom.algebraMap_toAlgebra] using
    hWrapper.symm.trans (rawIndCommonLift_iff_isFilteredColimitOfEtale.{u, v, z} f)

/-- Helper for Chap10 Lemma 10 154 5: a categorical `ind` witness can be reindexed into a
larger index universe. -/
private lemma commRingCatInd_index_lift
    {X Y : CommRingCat.{u}} {P : MorphismProperty CommRingCat.{u}} (f : X ⟶ Y)
    (h : MorphismProperty.ind.{v} P f) :
    MorphismProperty.ind.{max v w} P f := by
  -- Work in the under-category presentation of `f`, then reindex its filtered presentation by
  -- the essentially-small model in the larger universe.
  rw [MorphismProperty.ind_iff_ind_underMk] at h ⊢
  rcases h with ⟨J, _, _, pres, hpres⟩
  exact ObjectProperty.of_essentiallySmall_index (P := P.underObj) pres hpres

/-- Helper for Chap10 Lemma 10 154 5: the source-facing filtered-colimit-of-étale owner is
monotone in the hidden index universe. -/
private lemma isFilteredColimitOfEtale_index_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (h : RingHom.IsFilteredColimitOfEtale.{u, v, w} f) :
    RingHom.IsFilteredColimitOfEtale.{u, v, max w z} f := by
  -- After unfolding the wrapper, this is exactly the categorical reindexing lemma above.
  dsimp [RingHom.IsFilteredColimitOfEtale] at h ⊢
  exact commRingCatInd_index_lift _ h

/-- Helper for Chap10 Lemma 10 154 5: the finite-stage factorization construction over the
common base yields the desired ind-étale comparison map. -/
private theorem indEtaleComparison_of_commonBase
    (hA : RingHom.IsFilteredColimitOfEtale.{u, v, uA} (algebraMap R A))
    (hB : RingHom.IsFilteredColimitOfEtale.{u, w, uB} (algebraMap R B)) :
    RingHom.IsFilteredColimitOfEtale.{v, w, uC} (algebraMap A B) := by
  -- Route correction: the generic raw-ind common-base cancellation route is not dependency
  -- closed.  The proved finite helper above handles each finite étale stage of the `R → A`
  -- presentation; the remaining assembly must turn those stagewise `Aᵢ → B` ind-étale maps into
  -- an ind-étale witness for the colimit arrow `A → B`.
  -- TODO: extract a directed presentation of `A` from `hA`, apply
  -- `commRingCatIndEtale_of_etale_commonBase` to each stage using `hB`, and prove the resulting
  -- arrow cocone with point `A → B` is colimiting (or provide the corresponding dependency-closed
  -- general filtered-arrow colimit theorem).
  sorry

/- Domain-style sampling for Lemma 10.154.5:
* primary domain: filtered-colimit closure of étale ring maps in commutative algebra, specialized
  to a common-base comparison map `A → B`;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner for ind-étale ring maps;
  - `RingHom.filteredColimitOfEtale_baseChange`, the owner-level base-change theorem;
  - `RingHom.isFilteredColimitOfEtale_comp`, the owner-level composition theorem;
  - `Algebra.etale_of_etale_over_common_base`, the stagewise common-base étale owner.
* owner decision:
  - `source-facing`: the Stacks lemma for the structural map `A → B` under common-base
    ind-étale hypotheses over `R`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the wrapper `RingHom.IsFilteredColimitOfEtale`, which hides the `ULift`
    presentation of the categorical owner across possibly different universes.
* primitive data: only the owner-level ind-étale hypotheses on `R → A` and `R → B`, together with
  the given `A`-algebra structure on `B`;
* derived API: the induced owner-level ind-étale statement for `A → B`.

This file should therefore speak directly through `RingHom.IsFilteredColimitOfEtale` rather than
repeating the raw `ind CommRingCat.etale (ofHom ...)` presentation or reintroducing an unnecessary
same-universe restriction in its public theorem surface.
-/

-- Proof sketch: write `A` and `B` as filtered colimits of étale `R`-algebras. For each étale
-- stage `Aᵢ → A`, finite presentation factors the composite `Aᵢ → B` through some étale
-- `R`-stage `Bⱼ → B`. By Lemma `10.143.8`, the induced map `Aᵢ → Bⱼ` is étale, and then base
-- change along `Aᵢ → A` keeps it étale over `A`. These tensor-product stages form a filtered
-- system whose colimit is `B`, yielding the desired presentation over `A`.
/-- Lemma 10.154.5: if `A` and `B` are filtered colimits of étale `R`-algebras and `B` is an
`A`-algebra over `R`, then `A → B` is a filtered colimit of étale `A`-algebras. -/
@[stacks 08HS]
theorem isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
    (hA : (algebraMap R A).IsFilteredColimitOfEtale)
    (hB : (algebraMap R B).IsFilteredColimitOfEtale) :
    (algebraMap A B).IsFilteredColimitOfEtale := by
  -- The public theorem is now a thin wrapper around the source-proof factorization construction;
  -- all remaining work is isolated in the named helper above.
  exact indEtaleComparison_of_commonBase hA hB

end

end RingHom
