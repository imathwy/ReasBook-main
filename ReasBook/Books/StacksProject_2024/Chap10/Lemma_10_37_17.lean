import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Polynomial

universe u
universe v

section

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Helper for Lemma 10.37.17: a ring equivalence identifies the prime localizations above
corresponding prime ideals. -/
noncomputable def localizationAtPrimeRingEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (p : PrimeSpectrum S) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom p).asIdeal ≃+*
      Localization.AtPrime p.asIdeal :=
  Localization.localRingEquiv _ _ e (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) p)

/-- Helper for Lemma 10.37.17: normality transports across ring equivalences. -/
theorem isNormalRing_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsNormalRing R] : IsNormalRing S := by
  refine ⟨fun p ↦ ?_⟩
  let q : PrimeSpectrum R := PrimeSpectrum.comap e.toRingHom p
  let eLoc := localizationAtPrimeRingEquiv e p
  have hDomain : IsDomain (Localization.AtPrime q.asIdeal) := isDomain_localizationAtPrime q
  have hIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime q
  refine ⟨?_, ?_⟩
  · -- Transfer the domain structure across the localization equivalence.
    simpa [eLoc] using
      ((eLoc : Localization.AtPrime q.asIdeal ≃* Localization.AtPrime p.asIdeal).isDomain_iff).mp
        hDomain
  · -- Transfer integrally closedness across the same equivalence.
    exact IsIntegrallyClosed.of_equiv eLoc

/-- Helper for Lemma 10.37.17: a filtered colimit of nontrivial commutative rings is nontrivial. -/
theorem filtered_colimit_nontrivial (F : J ⥤ CommRingCat.{max u v})
    [∀ j, Nontrivial (F.obj j)] :
    Nontrivial (CommRingCat.FilteredColimits.colimit F) := by
  let c := CommRingCat.FilteredColimits.colimitCocone F
  let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
  let i : J := IsFiltered.nonempty.some
  refine ⟨c.ι.app i 0, c.ι.app i 1, fun h ↦ ?_⟩
  -- Move the equality to the underlying filtered colimit of types and descend it to one stage.
  have h' : t.ι.app i 0 = t.ι.app i 1 := h
  obtain ⟨k, f, hk⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (F := F ⋙ forget CommRingCat) ht 0 1).mp h'
  have hk' : (0 : F.obj k) = 1 := by
    calc
      (0 : F.obj k) = F.map f 0 := by
        symm
        exact map_zero _
      _ = F.map f 1 := hk
      _ = 1 := map_one _
  exact zero_ne_one hk'

/-- Helper for Lemma 10.37.17: if a zero product occurs in the canonical colimit and both factors
come from one stage, then that zero product already occurs at a later stage. -/
theorem canonical_filtered_colimit_zero_product_descend
    (F : J ⥤ CommRingCat.{max u v}) {i : J} (xi yi : F.obj i)
    (hxy : (CommRingCat.FilteredColimits.colimitCocone F).ι.app i xi *
        (CommRingCat.FilteredColimits.colimitCocone F).ι.app i yi = 0) :
    ∃ (j : J) (f : i ⟶ j), F.map f xi * F.map f yi = 0 := by
  let c := CommRingCat.FilteredColimits.colimitCocone F
  let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
  have hxy' : t.ι.app i (xi * yi) = t.ι.app i 0 := by
    -- Rewrite the colimit equality as an equality between two images from the same stage.
    change c.ι.app i (xi * yi) = c.ι.app i 0
    calc
      c.ι.app i (xi * yi) = c.ι.app i xi * c.ι.app i yi := by
        exact map_mul _ _ _
      _ = 0 := hxy
      _ = c.ι.app i 0 := by
        symm
        exact map_zero _
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (F := F ⋙ forget CommRingCat) ht (xi * yi) 0).mp hxy'
  have hf' : F.map f (xi * yi) = 0 := by
    calc
      F.map f (xi * yi) = F.map f 0 := hf
      _ = 0 := map_zero _
  refine ⟨j, f, ?_⟩
  -- Translate the eventual equality in the underlying type colimit back to a product equality.
  calc
    F.map f xi * F.map f yi = F.map f (xi * yi) := by
      symm
      exact map_mul _ _ _
    _ = 0 := hf'

/-- Helper for Lemma 10.37.17: filtered colimits of domains are domains. -/
theorem isDomain_of_filtered_colimit_of_domains (F : J ⥤ CommRingCat.{max u v})
    [∀ j, IsDomain (F.obj j)] :
    IsDomain (CommRingCat.FilteredColimits.colimit F) := by
  letI : Nontrivial (CommRingCat.FilteredColimits.colimit F) :=
    filtered_colimit_nontrivial F
  let c := CommRingCat.FilteredColimits.colimitCocone F
  let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
  haveI : NoZeroDivisors (CommRingCat.FilteredColimits.colimit F) := by
    constructor
    intro x y hxy
    -- First represent both factors at one common stage of the filtered diagram.
    obtain ⟨i, xi, yi, rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ ht x y
    -- Then descend the zero product to an actual zero product in a later stage.
    obtain ⟨j, f, hf⟩ := canonical_filtered_colimit_zero_product_descend F xi yi hxy
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hf with hxi | hyi
    · left
      -- Push the stagewise vanishing back to the colimit using cocone naturality.
      calc
        c.ι.app i xi = c.ι.app j (F.map f xi) := by
          exact (ConcreteCategory.congr_hom (c.w f) xi).symm
        _ = c.ι.app j 0 := by rw [hxi]
        _ = 0 := map_zero _
    · right
      -- The same argument handles the right factor.
      calc
        c.ι.app i yi = c.ι.app j (F.map f yi) := by
          exact (ConcreteCategory.congr_hom (c.w f) yi).symm
        _ = c.ι.app j 0 := by rw [hyi]
        _ = 0 := map_zero _
  exact NoZeroDivisors.to_isDomain (CommRingCat.FilteredColimits.colimit F)

/-- Helper for Lemma 10.37.17: the prime of a stage induced by a prime of the colimit. -/
private noncomputable abbrev contractedPrimeIdeal
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (i : J) : Ideal (F.obj i) :=
  (PrimeSpectrum.comap ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom p).asIdeal

/-- Helper for Lemma 10.37.17: the canonical colimit leg on a source stage is the target leg
composed with the transition map, viewed as an equality of underlying ring homomorphisms. -/
private theorem colimit_leg_hom_comp
    (F : J ⥤ CommRingCat.{max u v}) {i j : J} (f : i ⟶ j) :
    ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom =
      ((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom.comp (F.map f).hom := by
  -- Push cocone naturality down to an equality of ring homomorphisms once and for all.
  ext x
  exact (ConcreteCategory.congr_hom ((CommRingCat.FilteredColimits.colimitCocone F).w f) x).symm

/-- Helper for Lemma 10.37.17: along a transition map, the contracted prime on the source stage is
the comap of the contracted prime on the target stage. -/
private theorem contractedPrimeIdeal_map_eq_comap
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) :
    contractedPrimeIdeal F p i =
      Ideal.comap (F.map f).hom (contractedPrimeIdeal F p j) := by
  -- Rewrite the contracted-prime statement as the corresponding equality in `PrimeSpectrum`.
  have hprime :
      PrimeSpectrum.comap ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom p =
        PrimeSpectrum.comap (F.map f).hom
          (PrimeSpectrum.comap ((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom p) := by
    -- Rewrite the composed colimit leg to the source-stage leg before converting to ideals.
    rw [colimit_leg_hom_comp F f]
    exact PrimeSpectrum.comap_comp_apply (F.map f).hom
      ((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom p
  -- Convert back from prime-spectrum comap to equality of the underlying ideals.
  simpa [contractedPrimeIdeal, PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal hprime

/-- Helper for Lemma 10.37.17: once the source ideal, target ideal, and ring map are fixed,
equality on algebra generators determines a map between prime localizations. -/
private theorem eq_localRingHom_of_generator_eq {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} [I.IsPrime] {J : Ideal S} [J.IsPrime] (f : R →+* S)
    (hIJ : I = Ideal.comap f J) (j : Localization.AtPrime I →+* Localization.AtPrime J)
    (hj : ∀ x : R, j (algebraMap _ _ x) = algebraMap _ _ (f x)) :
    j = Localization.localRingHom I J f hIJ := by
  -- Reverse the standard uniqueness theorem so later proofs can use the concrete composite map
  -- as the left-hand side and avoid re-elaborating the dependent localization data.
  symm
  exact Localization.localRingHom_unique _ _ _ _ hj

/-- Helper for Lemma 10.37.17: the filtered diagram obtained by localizing each stage at the
contracted prime lying under `p`. -/
private noncomputable def localizedAtPrimeDiagram
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    J ⥤ CommRingCat.{max u v} where
  obj i := CommRingCat.of (Localization.AtPrime (contractedPrimeIdeal F p i))
  map f := CommRingCat.ofHom <|
    Localization.localRingHom _ _ (F.map f).hom (contractedPrimeIdeal_map_eq_comap F p f)
  map_id := by
    intro i
    -- The localized transition map of an identity morphism is the identity.
    apply CommRingCat.hom_ext
    simpa [contractedPrimeIdeal] using
      (Localization.localRingHom_id (I := contractedPrimeIdeal F p i))
  map_comp := by
    intro i j k f g
    -- Composition of stage transitions localizes to composition of the localized maps.
    apply CommRingCat.hom_ext
    simpa [contractedPrimeIdeal, Functor.map_comp] using
      (Localization.localRingHom_comp
        (I := contractedPrimeIdeal F p i)
        (J := contractedPrimeIdeal F p j)
        (K := contractedPrimeIdeal F p k)
        (f := (F.map f).hom)
        (hIJ := contractedPrimeIdeal_map_eq_comap F p f)
        (g := (F.map g).hom)
        (hJK := contractedPrimeIdeal_map_eq_comap F p g))

/-- Helper for Lemma 10.37.17: the canonical stage-localized map into the localization of the
colimit at `p`. -/
private noncomputable def localizedAtPrimeLeg
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (i : J) :
    (localizedAtPrimeDiagram F p).obj i ⟶ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  CommRingCat.ofHom <|
    Localization.localRingHom _ _ ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom rfl

/-- Helper for Lemma 10.37.17: the localized stage maps form a cocone over the localized diagram. -/
private theorem localizedAtPrimeLeg_naturality
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) :
    (localizedAtPrimeDiagram F p).map f ≫ localizedAtPrimeLeg F p j =
      localizedAtPrimeLeg F p i := by
  -- Route correction: freeze the localized composite as an ordinary ring homomorphism and then
  -- identify it with the canonical localized colimit leg by checking equality on generators.
  apply CommRingCat.hom_ext
  let jhom : Localization.AtPrime (contractedPrimeIdeal F p i) →+* Localization.AtPrime p.asIdeal :=
    ((localizedAtPrimeLeg F p j).hom).comp (((localizedAtPrimeDiagram F p).map f).hom)
  -- With the dependent localization data fixed inside `jhom`, uniqueness reduces to the images of
  -- the `algebraMap` generators from the source stage.
  change jhom =
    Localization.localRingHom _ _ ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom rfl
  refine eq_localRingHom_of_generator_eq _ rfl jhom ?_
  intro x
  -- Evaluate the frozen composite on a generator and rewrite the colimit leg by cocone
  -- naturality at the underlying ring-hom level.
  change
    Localization.localRingHom _ _ ((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom rfl
        (Localization.localRingHom _ _ (F.map f).hom (contractedPrimeIdeal_map_eq_comap F p f)
          (algebraMap _ _ x)) =
      algebraMap (CommRingCat.FilteredColimits.colimit F) (Localization.AtPrime p.asIdeal)
        (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom x)
  let ϕ : ↑(CommRingCat.FilteredColimits.colimit F) →+* Localization.AtPrime p.asIdeal :=
    algebraMap _ _
  -- Both localized maps are characterized on generators by the underlying stage maps.
  rw [Localization.localRingHom_to_map
    (I := contractedPrimeIdeal F p i) (J := contractedPrimeIdeal F p j)
    (F.map f).hom (contractedPrimeIdeal_map_eq_comap F p f)]
  have houter :
      Localization.localRingHom
          (I := contractedPrimeIdeal F p j) (J := p.asIdeal)
          ((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom rfl
          (algebraMap (F.obj j) (Localization.AtPrime (contractedPrimeIdeal F p j))
            ((F.map f).hom x)) =
        ϕ (((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom ((F.map f).hom x)) := by
    -- Evaluate the outer localization map on the stage-`j` generator.
    simpa [ϕ, contractedPrimeIdeal] using
      (Localization.localRingHom_to_map
        (I := contractedPrimeIdeal F p j) (J := p.asIdeal)
        ((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom rfl ((F.map f).hom x))
  calc
    _ = ϕ (((CommRingCat.FilteredColimits.colimitCocone F).ι.app j).hom ((F.map f).hom x)) := by
          simpa [ϕ, contractedPrimeIdeal] using houter
    _ = ϕ (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom x) := by
          simpa [RingHom.comp_apply] using
            congrArg
              (fun g : F.obj i →+* CommRingCat.FilteredColimits.colimit F => ϕ (g x))
              (colimit_leg_hom_comp F f).symm
    _ = algebraMap (CommRingCat.FilteredColimits.colimit F) (Localization.AtPrime p.asIdeal)
          (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom x) := by
          rfl

/-- Helper for Lemma 10.37.17: the stage localizations descend to a cocone with apex
`Localization.AtPrime p.asIdeal`. -/
private noncomputable def localizedAtPrimeCocone
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    Cocone (localizedAtPrimeDiagram F p) where
  pt := CommRingCat.of (Localization.AtPrime p.asIdeal)
  ι :=
    { app := localizedAtPrimeLeg F p
      naturality := by
        intro i j f
        simpa using localizedAtPrimeLeg_naturality F p f }

/-- Helper for Lemma 10.37.17: the forward comparison from the filtered colimit of the localized
stages to the localization of the filtered colimit at `p`. -/
private noncomputable def localizedAtPrime_to_localization
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) →+*
      Localization.AtPrime p.asIdeal :=
  ((CommRingCat.FilteredColimits.colimitCoconeIsColimit (localizedAtPrimeDiagram F p)).desc
    (localizedAtPrimeCocone F p)).hom

/-- Helper for Lemma 10.37.17: the forward comparison agrees with the localized stage leg on each
generator coming from a stage localization. -/
@[simp] private theorem localizedAtPrime_to_localization_ι
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (i : J) (x : Localization.AtPrime (contractedPrimeIdeal F p i)) :
    localizedAtPrime_to_localization F p
        ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i x) =
      localizedAtPrimeLeg F p i x := by
  -- Apply the colimit descent formula on the stage-localized generator `x`.
  exact ConcreteCategory.congr_hom
    ((CommRingCat.FilteredColimits.colimitCoconeIsColimit
      (localizedAtPrimeDiagram F p)).fac (localizedAtPrimeCocone F p) i) x

/-- Helper for Lemma 10.37.17: the stage maps from `F.obj i` into the localized-stage colimit,
obtained by first localizing at the contracted prime and then using the localized colimit leg. -/
private noncomputable def base_to_localized_colimit_leg
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (i : J) :
    F.obj i →+* CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) :=
  ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i).hom.comp
    (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)))

/-- Helper for Lemma 10.37.17: evaluating the canonical localized colimit cocone on a source-stage
element agrees with first applying the localized transition map and then the target-stage leg. -/
private theorem localized_colimit_leg_hom_comp
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) (x : Localization.AtPrime (contractedPrimeIdeal F p i)) :
    ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i).hom x =
      ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app j).hom
        ((((localizedAtPrimeDiagram F p).map f).hom) x) := by
  -- Push cocone naturality for the localized diagram down to the chosen source-stage element.
  exact
    (ConcreteCategory.congr_hom
      ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).w f) x).symm

/-- Helper for Lemma 10.37.17: the stage maps into the localized-stage colimit are compatible with
the original filtered diagram. -/
private theorem base_to_localized_colimit_leg_comp_generator
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) (x : F.obj i) :
    ((base_to_localized_colimit_leg F p j).comp (F.map f).hom) x =
      ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app j)
        ((((localizedAtPrimeDiagram F p).map f).hom)
          (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) x)) := by
  let ιj := (CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app j
  have hmap :
      (((localizedAtPrimeDiagram F p).map f).hom)
          (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) x) =
        algebraMap (F.obj j) (Localization.AtPrime (contractedPrimeIdeal F p j))
          ((F.map f).hom x) := by
    -- Evaluate the localized transition map on the source generator `x`.
    simpa [localizedAtPrimeDiagram] using
      (Localization.localRingHom_to_map
        (I := contractedPrimeIdeal F p i)
        (J := contractedPrimeIdeal F p j)
        (F.map f).hom
        (contractedPrimeIdeal_map_eq_comap F p f)
        x)
  calc
    ((base_to_localized_colimit_leg F p j).comp (F.map f).hom) x
        = ιj (algebraMap (F.obj j) (Localization.AtPrime (contractedPrimeIdeal F p j))
            ((F.map f).hom x)) := by
              rfl
    _ = ιj ((((localizedAtPrimeDiagram F p).map f).hom)
          (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) x)) := by
            rw [hmap]

/-- Helper for Lemma 10.37.17: the stage maps into the localized-stage colimit are compatible with
the original filtered diagram. -/
private theorem base_to_localized_colimit_leg_naturality
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) :
    (base_to_localized_colimit_leg F p j).comp (F.map f).hom =
      base_to_localized_colimit_leg F p i := by
  -- Route correction: evaluate both sides on generators from `F.obj i`, then use the frozen
  -- localized cocone-leg equality instead of reopening dependent localization data.
  ext x
  let zi : Localization.AtPrime (contractedPrimeIdeal F p i) :=
    algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) x
  have hleg :
      ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i).hom zi =
        ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app j).hom
          ((((localizedAtPrimeDiagram F p).map f).hom) zi) := by
    -- Freeze the localized cocone naturality once at the source-stage generator `zi`.
    exact localized_colimit_leg_hom_comp F p f zi
  have hcomp :
      ((base_to_localized_colimit_leg F p j).comp (F.map f).hom) x =
        ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i).hom zi := by
    have hcomp' :
        ((base_to_localized_colimit_leg F p j).comp (F.map f).hom) x =
          ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app j).hom
            ((((localizedAtPrimeDiagram F p).map f).hom) zi) := by
      simpa [zi] using base_to_localized_colimit_leg_comp_generator F p f x
    exact hcomp'.trans hleg.symm
  -- Unfold the source-stage generator `zi` to recover the stage map on the right-hand side.
  simpa [base_to_localized_colimit_leg, zi] using hcomp

/-- Helper for Lemma 10.37.17: the stage maps into the localized-stage colimit form a cocone over
the original filtered diagram. -/
private theorem base_to_localized_colimit_naturality
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) :
    F.map f ≫ CommRingCat.ofHom (base_to_localized_colimit_leg F p j) =
      CommRingCat.ofHom (base_to_localized_colimit_leg F p i) := by
  apply CommRingCat.hom_ext
  exact base_to_localized_colimit_leg_naturality F p f

/-- Helper for Lemma 10.37.17: the original diagram maps into the localized-stage colimit via a
cocone. -/
private noncomputable def base_to_localized_colimit_cocone
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    Cocone F :=
  { pt := CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p)
    ι :=
      { app := fun i => CommRingCat.ofHom (base_to_localized_colimit_leg F p i)
        naturality := fun _ _ f => base_to_localized_colimit_naturality F p f } }

/-- Helper for Lemma 10.37.17: the filtered colimit ring maps to the colimit of the localized
stages by descending the stagewise localization maps. -/
private noncomputable def base_to_localized_colimit
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    CommRingCat.FilteredColimits.colimit F →+*
      CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) :=
  ((CommRingCat.FilteredColimits.colimitCoconeIsColimit F).desc
    (base_to_localized_colimit_cocone F p)).hom

/-- Helper for Lemma 10.37.17: the descended base map agrees with the obvious stage map on a
generator coming from one stage of the original diagram. -/
@[simp] private theorem base_to_localized_colimit_ι
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (i : J) (x : F.obj i) :
    base_to_localized_colimit F p ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i x) =
      ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i)
        (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) x) := by
  -- Apply the colimit descent formula on the original stage generator `x`.
  exact ConcreteCategory.congr_hom
    ((CommRingCat.FilteredColimits.colimitCoconeIsColimit F).fac
      (base_to_localized_colimit_cocone F p) i) x

/-- Helper for Lemma 10.37.17: the localized transition map sends a stage generator to the obvious
mapped generator in the next stage localization. -/
private theorem localizedAtPrimeDiagram_map_generator
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {i j : J} (f : i ⟶ j) (x : F.obj i) :
    (((localizedAtPrimeDiagram F p).map f).hom)
        (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) x) =
      algebraMap (F.obj j) (Localization.AtPrime (contractedPrimeIdeal F p j))
        ((F.map f).hom x) := by
  -- Freeze the dependent localization data and evaluate the localized transition on generators.
  simpa [localizedAtPrimeDiagram] using
    (Localization.localRingHom_to_map
      (I := contractedPrimeIdeal F p i)
      (J := contractedPrimeIdeal F p j)
      (F.map f).hom
      (contractedPrimeIdeal_map_eq_comap F p f)
      x)

/-- Helper for Lemma 10.37.17: an element outside the prime `p` becomes a unit after mapping to
the colimit of the localized stages. -/
private theorem base_to_localized_colimit_isUnit_of_mem_primeCompl
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    {x : CommRingCat.FilteredColimits.colimit F} (hx : x ∈ p.asIdeal.primeCompl) :
    IsUnit (base_to_localized_colimit F p x) := by
  let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
  -- Descend the colimit element to one stage of the original diagram.
  obtain ⟨i, xi, hxi_eq⟩ := Types.jointly_surjective_of_isColimit ht x
  let xi' : F.obj i := xi
  have hx_eq :
      ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i) xi' = x := by
    simpa [t, xi'] using hxi_eq
  have hxi :
      xi' ∈ (contractedPrimeIdeal F p i).primeCompl := by
    -- Membership in the contracted prime is exactly the stagewise form of `hx`.
    rw [← hx_eq] at hx
    simpa [contractedPrimeIdeal, xi'] using hx
  have hunit_stage :
      IsUnit (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) xi') := by
    -- Elements outside the contracted prime become units after localizing that stage.
    simpa using
      (IsLocalization.map_units
        (S := Localization.AtPrime (contractedPrimeIdeal F p i))
        ⟨xi', hxi⟩)
  -- Push the stage-local unit into the filtered colimit of localized stages.
  rw [← hx_eq, base_to_localized_colimit_ι]
  exact hunit_stage.map
    ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i).hom

/-- Helper for Lemma 10.37.17: the reverse comparison from `R_p` to the filtered colimit of the
stage localizations, obtained from the localization universal property. -/
private noncomputable def localization_to_localizedAtPrime
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    Localization.AtPrime p.asIdeal →+*
      CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) :=
  IsLocalization.lift
    (M := p.asIdeal.primeCompl)
    (S := Localization.AtPrime p.asIdeal)
    (g := base_to_localized_colimit F p)
    (fun y ↦ base_to_localized_colimit_isUnit_of_mem_primeCompl F p y.2)

/-- Helper for Lemma 10.37.17: the reverse comparison extends the descended base map on the
unlocalized colimit ring. -/
@[simp] private theorem localization_to_localizedAtPrime_comp
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    (localization_to_localizedAtPrime F p).comp
        (algebraMap (CommRingCat.FilteredColimits.colimit F) (Localization.AtPrime p.asIdeal)) =
      base_to_localized_colimit F p := by
  -- This is exactly the computation rule for `IsLocalization.lift`.
  simpa [localization_to_localizedAtPrime] using
    (IsLocalization.lift_comp
      (M := p.asIdeal.primeCompl)
      (S := Localization.AtPrime p.asIdeal)
      (g := base_to_localized_colimit F p)
      (hg := fun y ↦ base_to_localized_colimit_isUnit_of_mem_primeCompl F p y.2))

/-- Helper for Lemma 10.37.17: the reverse comparison agrees with the localized stage leg on each
generator coming from one stage localization. -/
@[simp] private theorem localization_to_localizedAtPrime_leg
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (i : J) (x : Localization.AtPrime (contractedPrimeIdeal F p i)) :
    localization_to_localizedAtPrime F p (localizedAtPrimeLeg F p i x) =
      (CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i x := by
  let j₁ :
      Localization.AtPrime (contractedPrimeIdeal F p i) →+*
        CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) :=
    (localization_to_localizedAtPrime F p).comp (localizedAtPrimeLeg F p i).hom
  let j₂ :
      Localization.AtPrime (contractedPrimeIdeal F p i) →+*
        CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) :=
    ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i).hom
  have hj : j₁ = j₂ := by
    -- Compare the two maps out of the stage localization on algebra generators.
    apply IsLocalization.ringHom_ext (contractedPrimeIdeal F p i).primeCompl
    ext y
    have hleg :
        localizedAtPrimeLeg F p i
            (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) y) =
          algebraMap
            (CommRingCat.FilteredColimits.colimit F)
            (Localization.AtPrime p.asIdeal)
            (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y) := by
      -- Evaluate the localized stage leg on a generator.
      simpa [localizedAtPrimeLeg, contractedPrimeIdeal] using
        (Localization.localRingHom_to_map
          (I := contractedPrimeIdeal F p i)
          (J := p.asIdeal)
          ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom
          rfl
          y)
    have hcomp :
        localization_to_localizedAtPrime F p
            (algebraMap
              (CommRingCat.FilteredColimits.colimit F)
              (Localization.AtPrime p.asIdeal)
              (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y)) =
          base_to_localized_colimit F p
            (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y) := by
      change
        ((localization_to_localizedAtPrime F p).comp
            (algebraMap
              (CommRingCat.FilteredColimits.colimit F)
              (Localization.AtPrime p.asIdeal)))
          (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y) =
        _
      exact DFunLike.congr_fun
        (localization_to_localizedAtPrime_comp F p)
        (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y)
    calc
      j₁ (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) y)
          = localization_to_localizedAtPrime F p
              (localizedAtPrimeLeg F p i
                (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) y)) := by
              rfl
      _ = localization_to_localizedAtPrime F p
            (algebraMap
              (CommRingCat.FilteredColimits.colimit F)
              (Localization.AtPrime p.asIdeal)
              (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y)) := by
              -- Evaluate the stage-localized leg on a generator.
              rw [hleg]
      _ = base_to_localized_colimit F p
            (((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom y) := by
            exact hcomp
      _ = j₂ (algebraMap (F.obj i) (Localization.AtPrime (contractedPrimeIdeal F p i)) y) := by
            simpa [j₂] using base_to_localized_colimit_ι F p i y
  exact congrArg (fun j => j x) hj

/-- Helper for Lemma 10.37.17: the forward comparison composed with the descended base map is the
canonical localization map on the colimit ring. -/
@[simp] private theorem localizedAtPrime_to_localization_comp_base_to_localized_colimit
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F))
    (x : CommRingCat.FilteredColimits.colimit F) :
    localizedAtPrime_to_localization F p (base_to_localized_colimit F p x) =
      algebraMap (CommRingCat.FilteredColimits.colimit F) (Localization.AtPrime p.asIdeal) x := by
  let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
  -- Descend the base-colimit element to one stage and compute both composites there.
  obtain ⟨i, xi, hxi_eq⟩ := Types.jointly_surjective_of_isColimit ht x
  let xi' : F.obj i := xi
  have hx_eq :
      ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i) xi' = x := by
    simpa [t, xi'] using hxi_eq
  rw [← hx_eq, base_to_localized_colimit_ι, localizedAtPrime_to_localization_ι]
  -- The forward comparison on a stage generator is exactly the localized stage leg.
  simpa [localizedAtPrimeLeg, contractedPrimeIdeal] using
    (Localization.localRingHom_to_map
      (I := contractedPrimeIdeal F p i)
      (J := p.asIdeal)
      ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom
      rfl
      xi')

/-- Helper for Lemma 10.37.17: the forward and reverse comparison maps are inverse on
`Localization.AtPrime p`. -/
private theorem localizedAtPrime_to_localization_left_inverse
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    (localizedAtPrime_to_localization F p).comp (localization_to_localizedAtPrime F p) =
      RingHom.id (Localization.AtPrime p.asIdeal) := by
  -- Compare the composite with the identity map on generators of the base colimit ring.
  apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
  ext x
  have hcomp :
      localization_to_localizedAtPrime F p
          (algebraMap
            (CommRingCat.FilteredColimits.colimit F)
            (Localization.AtPrime p.asIdeal) x) =
        base_to_localized_colimit F p x := by
    change
      ((localization_to_localizedAtPrime F p).comp
          (algebraMap
            (CommRingCat.FilteredColimits.colimit F)
            (Localization.AtPrime p.asIdeal))) x =
        _
    exact DFunLike.congr_fun (localization_to_localizedAtPrime_comp F p) x
  change
    localizedAtPrime_to_localization F p
        (localization_to_localizedAtPrime F p
          (algebraMap
            (CommRingCat.FilteredColimits.colimit F)
            (Localization.AtPrime p.asIdeal) x)) =
      algebraMap (CommRingCat.FilteredColimits.colimit F) (Localization.AtPrime p.asIdeal) x
  rw [hcomp]
  exact localizedAtPrime_to_localization_comp_base_to_localized_colimit F p x

/-- Helper for Lemma 10.37.17: the reverse and forward comparison maps are inverse on the colimit
of the localized stages. -/
private theorem localization_to_localizedAtPrime_right_inverse
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    (localization_to_localizedAtPrime F p).comp (localizedAtPrime_to_localization F p) =
      RingHom.id (CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p)) := by
  let t : Cocone ((localizedAtPrimeDiagram F p) ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone ((localizedAtPrimeDiagram F p) ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit
      ((localizedAtPrimeDiagram F p) ⋙ forget CommRingCat.{max u v})
  -- Every element of the localized filtered colimit comes from one localized stage.
  ext x
  obtain ⟨i, xi, hxi_eq⟩ := Types.jointly_surjective_of_isColimit ht x
  let xi' : Localization.AtPrime (contractedPrimeIdeal F p i) := xi
  have hx_eq :
      ((CommRingCat.FilteredColimits.colimitCocone (localizedAtPrimeDiagram F p)).ι.app i) xi' = x := by
    simpa [t, xi'] using hxi_eq
  rw [← hx_eq, RingHom.comp_apply, localizedAtPrime_to_localization_ι,
    localization_to_localizedAtPrime_leg]
  rfl

/-- Helper for Lemma 10.37.17: the localization at `p` is identified with the filtered colimit of
the stage localizations at the contracted primes. -/
private noncomputable def localizedAtPrime_ringEquiv
    (F : J ⥤ CommRingCat.{max u v}) (p : PrimeSpectrum (CommRingCat.FilteredColimits.colimit F)) :
    Localization.AtPrime p.asIdeal ≃+*
      CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p) :=
  RingEquiv.ofRingHom
    (localization_to_localizedAtPrime F p)
    (localizedAtPrime_to_localization F p)
    (localization_to_localizedAtPrime_right_inverse F p)
    (localizedAtPrime_to_localization_left_inverse F p)

/-- Helper for Lemma 10.37.17: any finite family of elements of the canonical filtered colimit
already appears at one common stage. -/
private theorem filtered_colimit_exists_stage_family
    (F : J ⥤ CommRingCat.{max u v}) :
    ∀ n : ℕ, ∀ a : Fin n → CommRingCat.FilteredColimits.colimit F,
      ∃ i, ∃ b : Fin n → F.obj i, ∀ m,
        (CommRingCat.FilteredColimits.colimitCocone F).ι.app i (b m) = a m
  | 0, a => by
      let i : J := IsFiltered.nonempty.some
      refine ⟨i, fun m => Fin.elim0 m, ?_⟩
      intro m
      exact Fin.elim0 m
  | n + 1, a => by
      let c := CommRingCat.FilteredColimits.colimitCocone F
      let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
        Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
      let ht : IsColimit t :=
        Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
      -- Descend the tail first, then enlarge to a common stage with the head coefficient.
      obtain ⟨i, b, hb⟩ := filtered_colimit_exists_stage_family F n (fun m : Fin n ↦ a m.succ)
      obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit ht (a 0)
      open IsFiltered in
      refine ⟨max j i, Fin.cons (F.map (leftToMax j i) x) (fun m ↦ F.map (rightToMax j i) (b m)),
        ?_⟩
      intro m
      refine Fin.cases ?_ ?_ m
      · -- The head element is transported from the stage where it was originally chosen.
        have hhead :
            c.ι.app (max j i) (F.map (leftToMax j i) x) = c.ι.app j x :=
          ConcreteCategory.congr_hom (c.w (leftToMax j i)) x
        exact hhead.trans (by simpa [t] using hx)
      · intro m
        -- The tail coefficients are transported from the inductively chosen common stage.
        have htail :
            c.ι.app (max j i) (F.map (rightToMax j i) (b m)) = c.ι.app i (b m) :=
          ConcreteCategory.congr_hom (c.w (rightToMax j i)) (b m)
        exact htail.trans (hb m)

/-- Helper for Lemma 10.37.17: a monic polynomial over the canonical filtered colimit already
comes from one stage by a monic polynomial. -/
private theorem filtered_colimit_exists_stage_monic_polynomial
    (F : J ⥤ CommRingCat.{max u v}) (q : Polynomial (CommRingCat.FilteredColimits.colimit F))
    (hq : q.Monic) :
    ∃ i, ∃ qi : Polynomial (F.obj i), qi.Monic ∧
      Polynomial.map ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom qi = q := by
  let n := q.natDegree
  obtain ⟨i, c, hc⟩ := filtered_colimit_exists_stage_family F n (fun m ↦ q.coeff m)
  let qi : Polynomial (F.obj i) :=
    X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ))
  refine ⟨i, qi, ?_, ?_⟩
  · -- The descended lower-degree tail has degree `< n`, so adjoining `X ^ n` is monic.
    have hdeg :
        degree (∑ m : Fin n, C (c m) * X ^ (m : ℕ)) < n :=
      degree_sum_fin_lt (fun m ↦ c m)
    dsimp [qi]
    exact monic_X_pow_add hdeg
  · -- Mapping the rebuilt stage polynomial recovers the original monic polynomial `q`.
    dsimp [qi]
    calc
      Polynomial.map ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom
          (X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ)))
          = X ^ n + Polynomial.map ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom
              (Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ))) := by
                rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum]
                simp
      _ = X ^ n + Finset.univ.sum
            (fun m : Fin n =>
              Polynomial.map ((CommRingCat.FilteredColimits.colimitCocone F).ι.app i).hom
                (C (c m) * X ^ (m : ℕ))) := by
              rw [Polynomial.map_sum]
      _ = X ^ n + Finset.univ.sum
            (fun m : Fin n ↦ C (q.coeff (m : ℕ)) * X ^ (m : ℕ)) := by
              exact congrArg (fun s ↦ X ^ n + s) <| by
                apply Finset.sum_congr rfl
                intro m hm
                rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hc m]
                rfl
      _ = X ^ n + Finset.sum (Finset.range n) (fun m ↦ C (q.coeff m) * X ^ m) := by
            exact congrArg (fun s ↦ X ^ n + s)
              ((Fin.sum_univ_eq_sum_range (fun m ↦ C (q.coeff m) * X ^ m)) n)
      _ = q := by
            simpa [n] using hq.as_sum.symm

/-- Helper for Lemma 10.37.17: if two elements from one stage become equal in the canonical
filtered colimit, then they become equal after passing to a later stage. -/
private theorem filtered_colimit_exists_stage_eq
    (F : J ⥤ CommRingCat.{max u v}) {i : J} {x y : F.obj i}
    (hxy :
      (CommRingCat.FilteredColimits.colimitCocone F).ι.app i x =
        (CommRingCat.FilteredColimits.colimitCocone F).ι.app i y) :
    ∃ (j : J) (f : i ⟶ j), F.map f x = F.map f y := by
  let t : Cocone (F ⋙ forget CommRingCat.{max u v}) :=
    Types.TypeMax.colimitCocone (F ⋙ forget CommRingCat.{max u v})
  let ht : IsColimit t :=
    Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat.{max u v})
  have hxy' : t.ι.app i x = t.ι.app i y := hxy
  -- Descend the colimit equality to a genuine equality at a later stage of the diagram.
  exact (Types.FilteredColimit.isColimit_eq_iff' (F := F ⋙ forget CommRingCat) ht x y).mp hxy'

/-- Helper for Lemma 10.37.17: a monic relation for `a / b` in the fraction ring yields the
corresponding cleared-denominator relation for `a` and `q.scaleRoots b` in the base ring. -/
private theorem scaleRoots_eval_eq_zero_of_aeval_div_eq_zero
    {A : Type*} [CommRing A] [IsDomain A] (q : Polynomial A) {a b : A} (hb : b ≠ 0)
    (hroot :
      aeval (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) q = 0) :
    Polynomial.eval a (q.scaleRoots b) = 0 := by
  have hs : b ∈ nonZeroDivisors A := mem_nonZeroDivisors_iff_ne_zero.mpr hb
  -- Use the canonical `scaleRoots` denominator-clearing lemma inside the fraction ring first.
  have hscaled :
      aeval (algebraMap A (FractionRing A) a) (q.scaleRoots b) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero
      (K := FractionRing A)
      (inj := IsFractionRing.injective A (FractionRing A))
      hroot hs
  -- Then read the fraction-ring equality back in the base ring via injectivity of `algebraMap`.
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, IsFractionRing.to_map_eq_zero_iff] at hscaled
  exact hscaled

/-- Helper for Lemma 10.37.17: a cleared-denominator relation for `a` and `q.scaleRoots b`
recovers the original monic relation for `a / b` in the fraction ring. -/
private theorem aeval_div_eq_zero_of_scaleRoots_eval_eq_zero
    {A : Type*} [CommRing A] [IsDomain A] (q : Polynomial A) {a b : A} (hb : b ≠ 0)
    (hscaled : Polynomial.eval a (q.scaleRoots b) = 0) :
    aeval (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) q = 0 := by
  have hbK : algebraMap A (FractionRing A) b ≠ 0 := by
    intro hb_zero
    exact hb (IsFractionRing.to_map_eq_zero_iff.mp hb_zero)
  have hscaledK :
      aeval (algebraMap A (FractionRing A) a) (q.scaleRoots b) = 0 := by
    rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, IsFractionRing.to_map_eq_zero_iff]
    exact hscaled
  have hmul_ab :
      algebraMap A (FractionRing A) b *
          (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) =
        algebraMap A (FractionRing A) a := by
    -- Normalize the scaled evaluation point in the fraction field before cancelling `b`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hbK]
  have hscale :
      aeval (algebraMap A (FractionRing A) a) (q.scaleRoots b) =
        algebraMap A (FractionRing A) b ^ q.natDegree *
          aeval (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) q := by
    -- `scaleRoots_eval₂_mul` packages the denominator-clearing identity in the right shape.
    simpa [Polynomial.aeval_def, hmul_ab] using
      (Polynomial.scaleRoots_eval₂_mul
        (p := q)
        (f := algebraMap A (FractionRing A))
        (r := algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)
        (s := b))
  have hmul_zero :
      algebraMap A (FractionRing A) b ^ q.natDegree *
          aeval (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) q = 0 := by
    rw [← hscale, hscaledK]
  -- Cancel the nonzero power of the denominator to recover the original fraction-field root.
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero _ hbK) hmul_zero

/-- Helper for Lemma 10.37.17: filtered colimits of integrally closed domains are integrally
closed. -/
private theorem isIntegrallyClosed_of_filtered_colimit_of_integrally_closed_domains
    (F : J ⥤ CommRingCat.{max u v}) [∀ j, IsDomain (F.obj j)]
    [∀ j, IsIntegrallyClosed (F.obj j)] :
    IsIntegrallyClosed (CommRingCat.FilteredColimits.colimit F) := by
  let A := CommRingCat.FilteredColimits.colimit F
  let c := CommRingCat.FilteredColimits.colimitCocone F
  letI : IsDomain A := isDomain_of_filtered_colimit_of_domains F
  rw [isIntegrallyClosed_iff (K := FractionRing A)]
  intro z hz
  -- Route correction: descend one fraction presentation and one monic annihilating polynomial to
  -- a common stage, then work entirely with the cleared `scaleRoots` relation in the base rings.
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  obtain ⟨q, hqMonic, hroot⟩ := hz
  obtain ⟨iq, qi, hqiMonic, hqi_map⟩ :=
    filtered_colimit_exists_stage_monic_polynomial F q hqMonic
  obtain ⟨iab, ab, hab⟩ :=
    filtered_colimit_exists_stage_family F 2 (fun m : Fin 2 ↦ Fin.cases a (fun _ ↦ b) m)
  let k : J := IsFiltered.max iab iq
  let g_ab : iab ⟶ k := IsFiltered.leftToMax iab iq
  let g_q : iq ⟶ k := IsFiltered.rightToMax iab iq
  let ak : F.obj k := F.map g_ab (ab 0)
  let bk : F.obj k := F.map g_ab (ab 1)
  let qk : Polynomial (F.obj k) := Polynomial.map (F.map g_q).hom qi
  have hak : ((c.ι.app k).hom) ak = a := by
    -- Move the descended numerator to the chosen common stage.
    have hcomp :
        ((c.ι.app k).hom) ak = ((c.ι.app iab).hom) (ab 0) := by
      simpa [ak, c] using
        congrArg (fun h : F.obj iab →+* A => h (ab 0)) (colimit_leg_hom_comp F g_ab).symm
    exact hcomp.trans (by simpa using hab 0)
  have hbk : ((c.ι.app k).hom) bk = b := by
    -- The denominator moves to the same common stage by the same cocone computation.
    have hcomp :
        ((c.ι.app k).hom) bk = ((c.ι.app iab).hom) (ab 1) := by
      simpa [bk, c] using
        congrArg (fun h : F.obj iab →+* A => h (ab 1)) (colimit_leg_hom_comp F g_ab).symm
    exact hcomp.trans (by simpa using hab 1)
  have hqkMonic : qk.Monic := by
    -- Monicity is preserved when the stage polynomial is pushed to the common stage.
    simpa [qk] using hqiMonic.map (F.map g_q).hom
  have hqk_map : Polynomial.map (c.ι.app k).hom qk = q := by
    -- Identify the common-stage polynomial with the original colimit polynomial.
    have hleg :
        ((c.ι.app k).hom.comp (F.map g_q).hom) = (c.ι.app iq).hom := by
      ext x
      simpa [c] using congrArg (fun h : F.obj iq →+* A => h x) (colimit_leg_hom_comp F g_q).symm
    dsimp [qk]
    rw [Polynomial.map_map]
    exact hleg ▸ hqi_map
  have hscaled :
      Polynomial.eval a (q.scaleRoots b) = 0 :=
    scaleRoots_eval_eq_zero_of_aeval_div_eq_zero q hb0 hroot
  have hmap_scaleRoots :
      Polynomial.map (c.ι.app k).hom (qk.scaleRoots bk) = q.scaleRoots b := by
    -- `scaleRoots` commutes with the map to the colimit once the leading coefficient is pinned.
    have hmap_one : ((c.ι.app k).hom) (1 : F.obj k) ≠ 0 := by
      intro h
      rw [map_one] at h
      letI : NeZero (1 : ↑A) := by infer_instance
      exact (NeZero.ne (1 : ↑A)) h
    have hlead :
        ((c.ι.app k).hom) qk.leadingCoeff ≠ 0 := by
      simpa [hqkMonic.leadingCoeff] using hmap_one
    have hmap_scaleRoots' :
        Polynomial.map (c.ι.app k).hom (qk.scaleRoots bk) =
          (Polynomial.map (c.ι.app k).hom qk).scaleRoots (((c.ι.app k).hom) bk) :=
      Polynomial.map_scaleRoots qk bk (c.ι.app k).hom hlead
    calc
      Polynomial.map (c.ι.app k).hom (qk.scaleRoots bk)
          = (Polynomial.map (c.ι.app k).hom qk).scaleRoots (((c.ι.app k).hom) bk) :=
            hmap_scaleRoots'
      _ = (Polynomial.map (c.ι.app k).hom qk).scaleRoots b := by rw [hbk]
      _ = q.scaleRoots b := by
            exact congrArg (fun p : Polynomial ↑A => p.scaleRoots b) hqk_map
  have hscaled_map_zero :
      ((c.ι.app k).hom) (Polynomial.eval ak (qk.scaleRoots bk)) = 0 := by
    -- Evaluate the mapped cleared polynomial relation in the colimit ring.
    calc
      ((c.ι.app k).hom) (Polynomial.eval ak (qk.scaleRoots bk))
          = Polynomial.eval (((c.ι.app k).hom) ak)
              (Polynomial.map (c.ι.app k).hom (qk.scaleRoots bk)) := by
                symm
                simpa using
                  (Polynomial.eval_map_apply
                    (p := qk.scaleRoots bk) ((c.ι.app k).hom) ak)
      _ = Polynomial.eval a (q.scaleRoots b) := by
            exact congrArg₂ Polynomial.eval hak hmap_scaleRoots
      _ = 0 := hscaled
  have hscaled_eq :
      ((c.ι.app k).hom) (Polynomial.eval ak (qk.scaleRoots bk)) =
        ((c.ι.app k).hom) 0 := by
    -- Package the colimit-ring equation in the exact shape needed for equality descent.
    calc
      ((c.ι.app k).hom) (Polynomial.eval ak (qk.scaleRoots bk)) = 0 := hscaled_map_zero
      _ = ((c.ι.app k).hom) 0 := by
            symm
            exact map_zero _
  obtain ⟨l, g, hlg⟩ := filtered_colimit_exists_stage_eq F (i := k) (x := Polynomial.eval ak (qk.scaleRoots bk))
    (y := 0) hscaled_eq
  let al : F.obj l := F.map g ak
  let bl : F.obj l := F.map g bk
  let ql : Polynomial (F.obj l) := Polynomial.map (F.map g).hom qk
  have hal : ((c.ι.app l).hom) al = a := by
    -- Push the numerator along the descended equality stage without changing its colimit image.
    have hcomp :
        ((c.ι.app l).hom) al = ((c.ι.app k).hom) ak := by
      simpa [al, c] using
        congrArg (fun h : F.obj k →+* A => h ak) (colimit_leg_hom_comp F g).symm
    exact hcomp.trans hak
  have hbl : ((c.ι.app l).hom) bl = b := by
    -- The denominator has the same colimit image after passing to the later stage.
    have hcomp :
        ((c.ι.app l).hom) bl = ((c.ι.app k).hom) bk := by
      simpa [bl, c] using
        congrArg (fun h : F.obj k →+* A => h bk) (colimit_leg_hom_comp F g).symm
    exact hcomp.trans hbk
  have hbl_ne : bl ≠ 0 := by
    -- If the later-stage denominator vanished, then its colimit image would also vanish.
    intro hzero
    apply hb0
    calc
      b = ((c.ι.app l).hom) bl := hbl.symm
      _ = ((c.ι.app l).hom) 0 := by rw [hzero]
      _ = 0 := map_zero _
  have hqlMonic : ql.Monic := by
    -- Monicity survives one more transition to the equality-descending stage.
    simpa [ql] using hqkMonic.map (F.map g).hom
  have hmap_scaleRoots_l :
      Polynomial.map (F.map g).hom (qk.scaleRoots bk) = ql.scaleRoots bl := by
    -- Freeze the transported polynomial relation in the exact later-stage shape we need.
    have hmap_one : ((F.map g).hom) (1 : F.obj k) ≠ 0 := by
      rw [map_one]
      exact zero_ne_one.symm
    have hlead :
        ((F.map g).hom) qk.leadingCoeff ≠ 0 := by
      simpa [hqkMonic.leadingCoeff] using hmap_one
    simpa [ql, bl] using
      (Polynomial.map_scaleRoots qk bk (F.map g).hom hlead)
  have hscaled_l : Polynomial.eval al (ql.scaleRoots bl) = 0 := by
    -- Rewrite the descended equality as a genuine polynomial equation in the later stage.
    calc
      Polynomial.eval al (ql.scaleRoots bl)
          = Polynomial.eval al (Polynomial.map (F.map g).hom (qk.scaleRoots bk)) := by
              rw [← hmap_scaleRoots_l]
      _ = (F.map g).hom (Polynomial.eval ak (qk.scaleRoots bk)) := by
            simpa [al] using
              (Polynomial.eval_map_apply
                (p := qk.scaleRoots bk) ((F.map g).hom) ak)
      _ = (F.map g).hom 0 := hlg
      _ = 0 := map_zero _
  have hroot_l :
      aeval (algebraMap (F.obj l) (FractionRing (F.obj l)) al /
          algebraMap (F.obj l) (FractionRing (F.obj l)) bl) ql = 0 :=
    aeval_div_eq_zero_of_scaleRoots_eval_eq_zero ql hbl_ne hscaled_l
  have hintegral_l :
      IsIntegral (F.obj l)
        (algebraMap (F.obj l) (FractionRing (F.obj l)) al /
          algebraMap (F.obj l) (FractionRing (F.obj l)) bl) := by
    -- The later-stage fraction now satisfies a monic polynomial over its own stage ring.
    exact ⟨ql, hqlMonic, hroot_l⟩
  obtain ⟨cl, hcl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hintegral_l
  have hblK : algebraMap (F.obj l) (FractionRing (F.obj l)) bl ≠ 0 := by
    intro hb_zero
    exact hbl_ne (IsFractionRing.to_map_eq_zero_iff.mp hb_zero)
  have hmul_l :
      algebraMap (F.obj l) (FractionRing (F.obj l)) cl *
          algebraMap (F.obj l) (FractionRing (F.obj l)) bl =
        algebraMap (F.obj l) (FractionRing (F.obj l)) al := by
    -- Clear the later-stage denominator inside the stage fraction ring.
    rw [eq_comm, div_eq_iff hblK] at hcl
    simpa [map_mul] using hcl.symm
  have hstage :
      cl * bl = al := by
    -- Inject the cleared equality back down from the stage fraction ring.
    apply IsFractionRing.injective (F.obj l) (FractionRing (F.obj l))
    simpa [map_mul] using hmul_l
  let ιl : F.obj l →+* A := ((CommRingCat.FilteredColimits.colimitCocone F).ι.app l).hom
  have hcolimit_mul :
      (ιl cl * b) = (a : ↑A) := by
    -- Map the stage identity back to the colimit ring and compare with the chosen `a / b`.
    have hstageA' : ιl (cl * bl) = ιl al := by
      dsimp [ιl]
      exact congrArg
        (fun x : F.obj l =>
          (CommRingCat.Hom.hom ((CommRingCat.FilteredColimits.colimitCocone F).ι.app l)) x)
        hstage
    have hstageA : (ιl cl) * (ιl bl) = ιl al := by
      simpa [ιl, map_mul] using hstageA'
    have hbl' : ιl bl = b := by
      simpa [ιl, c] using hbl
    have hal' : ιl al = a := by
      simpa [ιl, c] using hal
    calc
      ιl cl * b = ιl cl * ιl bl := by
        rw [hbl']
      _ = ιl al := hstageA
      _ = a := hal'
  refine ⟨ιl cl, ?_⟩
  have hbA : algebraMap A (FractionRing A) b ≠ 0 := by
    intro hb_zero
    exact hb0 (IsFractionRing.to_map_eq_zero_iff.mp hb_zero)
  -- One final denominator-clearing step in the colimit ring finishes the original fraction.
  rw [eq_comm, div_eq_iff hbA]
  simpa [map_mul] using (congrArg (algebraMap A (FractionRing A)) hcolimit_mul).symm

/-- Helper for Lemma 10.37.17: the canonical filtered colimit of normal rings is normal. -/
theorem isNormalRing_canonical_filtered_colimit (F : J ⥤ CommRingCat.{max u v})
    [∀ j, IsNormalRing (F.obj j)] :
    IsNormalRing (CommRingCat.FilteredColimits.colimit F) := by
  refine ⟨fun p ↦ ?_⟩
  let e := localizedAtPrime_ringEquiv F p
  have hDomainColimit :
      IsDomain (CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p)) := by
    letI : ∀ j, IsDomain ((localizedAtPrimeDiagram F p).obj j) := fun j => by
      change IsDomain (Localization.AtPrime (contractedPrimeIdeal F p j))
      infer_instance
    -- Each stage localization is a normal domain, so their filtered colimit is a domain.
    simpa using isDomain_of_filtered_colimit_of_domains (localizedAtPrimeDiagram F p)
  have hDomain : IsDomain (Localization.AtPrime p.asIdeal) := by
    -- Transport the domain structure back across the localization/colimit equivalence.
    exact ((e : Localization.AtPrime p.asIdeal ≃*
      CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p)).isDomain_iff).mpr
      hDomainColimit
  have hIntegrallyClosedColimit :
      IsIntegrallyClosed (CommRingCat.FilteredColimits.colimit (localizedAtPrimeDiagram F p)) := by
    letI : ∀ j, IsDomain ((localizedAtPrimeDiagram F p).obj j) := fun j => by
      change IsDomain (Localization.AtPrime (contractedPrimeIdeal F p j))
      infer_instance
    letI : ∀ j, IsIntegrallyClosed ((localizedAtPrimeDiagram F p).obj j) := fun j => by
      change IsIntegrallyClosed (Localization.AtPrime (contractedPrimeIdeal F p j))
      infer_instance
    -- Reduce the local normality claim to the domain-case descent for filtered colimits.
    simpa using
      isIntegrallyClosed_of_filtered_colimit_of_integrally_closed_domains
        (localizedAtPrimeDiagram F p)
  refine ⟨hDomain, ?_⟩
  -- Transport integrally closedness back across the localization/colimit equivalence.
  exact IsIntegrallyClosed.of_equiv e.symm

/-- Lemma 10.37.17: the colimit of a directed system of normal rings is a normal ring. -/
-- Proof sketch: for a prime ideal `p` of `colimit F`, compare `Localization.AtPrime p` with the
-- filtered colimit of the localizations of the stages at the induced prime ideals. Each of those
-- localizations is a normal domain by the stagewise assumption, so the problem reduces to the
-- domain case. Then any element of the fraction field of the colimit ring that is integral over
-- the colimit comes from some stage together with a monic polynomial relation there, and
-- normality of that stage forces the element to lie in the stage ring, hence in the colimit.
theorem isNormalRing_of_isColimit_filtered_system
    (F : J ⥤ CommRingCat.{max u v}) (c : Cocone F) (hc : IsColimit c)
    [∀ j, IsNormalRing (F.obj j)] :
    IsNormalRing c.pt := by
  -- Route correction: first transport to the canonical filtered-colimit cocone, so the remaining
  -- source-faithful blocker is concentrated in the canonical case only.
  let e := hc.coconePointUniqueUpToIso (CommRingCat.FilteredColimits.colimitCoconeIsColimit F)
  have hCanonical : IsNormalRing ((CommRingCat.FilteredColimits.colimitCocone F).pt) := by
    simpa using isNormalRing_canonical_filtered_colimit F
  -- Transfer normality back across the universal comparison isomorphism.
  exact @isNormalRing_of_equiv ((CommRingCat.FilteredColimits.colimitCocone F).pt) c.pt
    inferInstance inferInstance e.symm.commRingCatIsoToRingEquiv hCanonical

/-- Filtered colimits of diagrams of normal rings carry the canonical normal-ring instance. -/
instance (F : J ⥤ CommRingCat.{max u v}) [HasColimit F] [∀ j, IsNormalRing (F.obj j)] :
    IsNormalRing ↑(colimit F) := by
  simpa using
    isNormalRing_of_isColimit_filtered_system F (colimit.cocone F) (colimit.isColimit F)

end
