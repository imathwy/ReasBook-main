import stacks_project.Chap08.Lemma_8_5_3.Support

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open BasedFunctor Functor IsStronglyCartesian

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- Helper for Lemma 8.5.3: for a fixed cover, the remaining task is to show that the canonical
descent functor for the associated groupoid projection is an equivalence. -/
theorem associated_groupoid_cover_toDescentData_isEquivalence
    [IsStackOnSite J p] {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).IsEquivalence := by
  let Fassoc := associated_groupoid_cover_descent_functor (J := J) (p := p) S
  let Famb := ambient_cover_descent_functor (J := J) (p := p) S
  let G := associated_groupoid_cover_forget_descent_data (J := J) (p := p) S
  let FI := FibredCategoryMor.fiberFunctor (associated_groupoid_inclusion (p := p)) U
  let compIso := associated_groupoid_cover_forget_toDescentData_iso (J := J) (p := p) S
  let hAmbEquiv := ambient_cover_toDescentData_isEquivalence (J := J) (p := p) S
  letI : Famb.IsEquivalence := hAmbEquiv
  letI : Famb.Full := hAmbEquiv.full
  letI : Famb.Faithful := hAmbEquiv.faithful
  letI : G.Faithful :=
    associated_groupoid_cover_forget_descent_data_faithful (J := J) (p := p) S
  letI : FI.Faithful := associated_groupoid_inclusion_fiberFunctor_faithful (p := p) U
  letI : (FI ⋙ Famb).Faithful := by
    refine ⟨?_⟩
    intro X Y f g hfg
    apply FI.map_injective
    apply Famb.map_injective
    simpa [Functor.comp_map] using hfg
  letI : Fassoc.Faithful := by
    refine ⟨?_⟩
    intro X Y f g hfg
    have hfgG : (Fassoc ⋙ G).map f = (Fassoc ⋙ G).map g := by
      simpa [Fassoc, G, Functor.comp_map] using congrArg G.map hfg
    have hcomp :
        compIso.hom.app X ≫ (FI ⋙ Famb).map f =
          compIso.hom.app X ≫ (FI ⋙ Famb).map g := by
      have hnat_f :
          compIso.hom.app X ≫ (FI ⋙ Famb).map f =
            (Fassoc ⋙ G).map f ≫ compIso.hom.app Y := by
        simpa using (compIso.hom.naturality f).symm
      have hnat_g :
          (Fassoc ⋙ G).map g ≫ compIso.hom.app Y =
            compIso.hom.app X ≫ (FI ⋙ Famb).map g := by
        simpa using compIso.hom.naturality g
      exact
        hnat_f.trans <|
          (congrArg (fun k ↦ k ≫ compIso.hom.app Y) hfgG).trans hnat_g
    exact map_injective (F := FI ⋙ Famb) ((cancel_epi (compIso.hom.app X)).1 hcomp)
  let ambientPreimage :
      ((canonicalFiberPseudofunctor p).DescentData (fun I : S.Arrow ↦ I.f)) →
        p.Fiber U :=
    fun D ↦ Classical.choose (Functor.EssSurj.mem_essImage (F := Famb) D)
  let ambientPreimageIso :
      ∀ D : ((canonicalFiberPseudofunctor p).DescentData (fun I : S.Arrow ↦ I.f)),
        Famb.obj (ambientPreimage D) ≅ D :=
    fun D ↦ Classical.choice (Classical.choose_spec (Functor.EssSurj.mem_essImage (F := Famb) D))
  let associatedPreimage :
      ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
        (fun I : S.Arrow ↦ I.f)) →
        (stronglyCartesianProjection p).Fiber U :=
    fun D ↦ associated_groupoid_fiber_obj (p := p) (ambientPreimage (G.obj D))
  have hObj :
      ∀ D :
        ((canonicalFiberPseudofunctor (stronglyCartesianProjection p)).DescentData
          (fun I : S.Arrow ↦ I.f)),
        Fassoc.obj (associatedPreimage D) ≅ D := by
    intro D
    let z := associatedPreimage D
    have hambient :
        (FI ⋙ Famb).obj z ≅ G.obj D := by
      -- The ambient stack equivalence gives an objectwise preimage after forgetting.
      simpa [associatedPreimage, ambientPreimage, Famb, FI, G, z] using
        ambientPreimageIso (G.obj D)
    -- Lift the ambient comparison isomorphism back into associated descent data.
    exact
      associated_groupoid_cover_forget_iso_lift (J := J) (p := p) S
        (compIso.app z ≪≫ hambient)
  letI : Fassoc.Full := by
    refine ⟨?_⟩
    intro x y η
    let ηIso : Fassoc.obj x ≅ Fassoc.obj y := by
      letI : IsIso η := associated_groupoid_descent_hom_isIso (J := J) (p := p) S η
      exact asIso η
    let eamb :
        Famb.obj (FI.obj x) ≅ Famb.obj (FI.obj y) :=
      (compIso.app x).symm ≪≫ G.mapIso ηIso ≪≫ compIso.app y
    let φamb :
        FI.obj x ⟶ FI.obj y :=
      ((Functor.FullyFaithful.ofFullyFaithful Famb).preimageIso eamb).hom
    let φassoc : x ⟶ y :=
      associated_groupoid_fiber_hom_of_isIso (p := p) φamb
    refine ⟨φassoc, ?_⟩
    -- Route correction: compare the candidate lift with `η` after forgetting to ambient descent
    -- data, where `compIso` and `preimageIso` identify both morphisms explicitly.
    apply G.map_injective
    have hnat :
        G.map (Fassoc.map φassoc) ≫ compIso.hom.app y =
          compIso.hom.app x ≫ Famb.map (FI.map φassoc) := by
      simpa [Fassoc, Famb, G, FI, Functor.comp_map] using compIso.hom.naturality φassoc
    have hforget :
        FI.map φassoc = φamb := by
      simpa [φassoc, φamb, FI] using
        associated_groupoid_fiber_hom_of_isIso_forget (p := p) (φ := φamb)
    have hpreimage :
        Famb.map φamb = eamb.hom := by
      simpa [Famb, φamb, eamb] using
        ambient_cover_preimageIso_hom_map (J := J) (p := p) S eamb
    have heamb :
        compIso.hom.app x ≫ eamb.hom =
          (G.mapIso ηIso).hom ≫ compIso.hom.app y := by
      -- Expand `eamb` to the chosen conjugation and cancel the left comparison isomorphism.
      change
        compIso.hom.app x ≫
            (((compIso.app x).symm ≪≫ G.mapIso ηIso ≪≫ compIso.app y).hom) =
          (G.mapIso ηIso).hom ≫ compIso.hom.app y
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc (compIso.app x)
          ((G.mapIso ηIso).hom ≫ compIso.hom.app y))
    have hmapη :
        (G.mapIso ηIso).hom = G.map η := by
      simpa [ηIso] using (Functor.mapIso_hom G ηIso)
    have hforget' :
        compIso.hom.app x ≫ Famb.map (FI.map φassoc) =
          compIso.hom.app x ≫ Famb.map φamb := by
      rw [hforget]
    have hpreimage' :
        compIso.hom.app x ≫ Famb.map φamb =
          compIso.hom.app x ≫ eamb.hom := by
      rw [hpreimage]
    have hmapη' :
        (G.mapIso ηIso).hom ≫ compIso.hom.app y =
          G.map η ≫ compIso.hom.app y := by
      rw [hmapη]
    have htransport :
        G.map (Fassoc.map φassoc) ≫ compIso.hom.app y =
          G.map η ≫ compIso.hom.app y := by
      -- Expand the ambient comparison isomorphism `eamb`, rewrite the two mapped morphisms to the
      -- chosen ambient comparison, and then cancel the left comparison isomorphism at `x`.
      exact
        hnat.trans <| hforget'.trans <| hpreimage'.trans <| heamb.trans hmapη'
    exact (cancel_mono (compIso.hom.app y)).1 htransport
  -- Once full faithfulness is established, the lifted objectwise preimages give the equivalence.
  exact
    Functor.fully_faithful_isEquivalence_of_objwise_iso
      (F := Fassoc) associatedPreimage (fun D ↦ (hObj D).symm)

end

end CategoryTheory
