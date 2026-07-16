import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_112_1
import stacks_proof.stacks_project.Chap10.Lemma_10_155_1
import stacks_proof.stacks_project.Chap10.Lemma_10_155_2
import stacks_proof.stacks_project.Chap15.Lemma_15_44_2
import stacks_proof.stacks_project.Chap15.Lemma_15_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CommRingCat
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
* primary domain: Krull dimension of local rings under henselization and strict henselization;
* sampled owner declarations:
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `henselizationMap_faithfullyFlat`,
  `strictHenselizationMap_faithfullyFlat`,
  `IsHenselizationOf.map_maximalIdeal`,
  `IsStrictHenselizationOf.map_maximalIdeal`;
* owner abstraction: the source-facing statements compare the two local rings by first comparing
  their closed-point localizations, then transporting that equality back to the ambient local rings
  through `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`; faithful-flatness and maximal-ideal
  image are derived owner data supplying that closed-point comparison.
* primitive data: the local ring `R` and the chosen owner instances
  `IsHenselizationOf R Rh` / `IsStrictHenselizationOf R Rsh`;
* derived API: faithful-flatness of the structural maps, extension of the maximal ideal, and the
  zero-dimensional closed fiber at the closed point.

Layer triage:
* `source-facing`: the two equality statements for `ringKrullDim`;
* `core/canonical`: the local owner `ringKrullDim` together with the closed-point localization
  comparison;
* `bridge/view`: the passage between a local ring and the localization at its maximal ideal.
-/

-- Proof sketch: compare the two local rings at their closed points. Lemma `15.45.1` gives
-- faithful flatness of `R → Rh`, hence going down for the maximal ideal of `Rh`, and
-- `IsHenselizationOf.map_maximalIdeal` identifies the closed fiber with the residue field of the
-- localization at `maximalIdeal Rh`, so the closed-point comparison reduces to a zero-dimensional
-- fiber, after which the local and localized Krull dimensions are identified canonically by
-- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` and
-- `IsLocalization.AtPrime.ringKrullDim_eq_height`.
/-- Helper for Lemma 15.45.7: in a filtered colimit of types, any finite family of target elements
already comes from one common stage. -/
private theorem exists_common_stage_of_finite_family
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ Type u}
    (c : Cocone F) (hc : IsColimit c) (n : ℕ) (x : Fin n → c.pt) :
    ∃ j, ∃ y : Fin n → F.obj j, ∀ i, c.ι.app j (y i) = x i := by
  induction n with
  | zero =>
      let j : J := Classical.choice (CategoryTheory.IsFiltered.nonempty (C := J))
      refine ⟨j, fun i ↦ Fin.elim0 i, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      let xInit : Fin n → c.pt := fun i ↦ x i.castSucc
      obtain ⟨j₁, y₁, hy₁⟩ := ih xInit
      obtain ⟨j₂, y₂, hy₂⟩ :=
        CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hc (x (Fin.last n))
      let j : J := CategoryTheory.IsFiltered.max j₁ j₂
      let f₁ : j₁ ⟶ j := CategoryTheory.IsFiltered.leftToMax j₁ j₂
      let f₂ : j₂ ⟶ j := CategoryTheory.IsFiltered.rightToMax j₁ j₂
      refine ⟨j, Fin.lastCases (F.map f₂ y₂) (fun i ↦ F.map f₁ (y₁ i)), ?_⟩
      have hLast :
          c.ι.app j (Fin.lastCases (F.map f₂ y₂) (fun i ↦ F.map f₁ (y₁ i)) (Fin.last n)) =
            x (Fin.last n) := by
        rw [Fin.lastCases_last]
        exact (by
          have hNat : c.ι.app j (F.map f₂ y₂) = c.ι.app j₂ y₂ := by
            simpa using congrFun (c.ι.naturality f₂) y₂
          exact hNat.trans hy₂)
      have hCast :
          ∀ i : Fin n,
            c.ι.app j (Fin.lastCases (F.map f₂ y₂) (fun i ↦ F.map f₁ (y₁ i)) i.castSucc) =
              x i.castSucc := by
        intro i
        rw [Fin.lastCases_castSucc]
        have hNat : c.ι.app j (F.map f₁ (y₁ i)) = c.ι.app j₁ (y₁ i) := by
          simpa using congrFun (c.ι.naturality f₁) (y₁ i)
        exact hNat.trans (hy₁ i)
      intro i
      exact Fin.lastCases hLast hCast i

/-- Helper for Lemma 15.45.7: the canonical `ULift` of a local ring is again a local ring. -/
private theorem isLocalRing_ulift {A : Type u} [CommRing A] [IsLocalRing A] :
    IsLocalRing (ULift A) := by
  -- Transport the local-ring structure back along the canonical ring equivalence `ULift A ≃+* A`.
  let hLocal : IsLocalHom ((ULift.ringEquiv : ULift A ≃+* A).toRingHom) := by
    refine isLocalHom_of_leftInverse ((ULift.ringEquiv.symm : A ≃+* ULift A).toRingHom) ?_
    intro a
    rfl
  letI : IsLocalHom ((ULift.ringEquiv : ULift A ≃+* A).toRingHom) := hLocal
  exact RingHom.domain_isLocalRing ((ULift.ringEquiv : ULift A ≃+* A).toRingHom)

/-- Helper for Lemma 15.45.7: a faithfully flat local algebra map cannot decrease Krull
dimension. -/
private theorem ringKrullDim_base_le_of_faithfullyFlat_local
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    ringKrullDim R ≤ ringKrullDim S := by
  -- Going down along a faithfully flat map gives the lower bound on Krull dimensions.
  letI : Module.FaithfullyFlat R S := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  simpa using
    ringKrullDim_le_of_surjective_comap_of_specializing_or_generalizing
      (algebraMap R S)
      PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (.inr <| Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance)

/-- Helper for Lemma 15.45.7: localizing an étale stage at a prime over the closed point preserves
the base Krull dimension. -/
private theorem etale_localizationAtPrime_ringKrullDim_eq_base
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R) :
    ringKrullDim (Localization.AtPrime q) = ringKrullDim R := by
  -- First compare with the localization of the base at the contracted prime, then identify that
  -- localization with the original local ring at its maximal ideal.
  have hbase :
      ringKrullDim (Localization.AtPrime (q.under R)) = ringKrullDim R := by
    calc
      ringKrullDim (Localization.AtPrime (q.under R)) = (q.under R).height := by
        exact IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _
      _ = (maximalIdeal R).height := by
        simpa [hq]
      _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  calc
    ringKrullDim (Localization.AtPrime q) =
        ringKrullDim (Localization.AtPrime (q.under R)) := by
          simpa using
            (ringKrullDim_localizationAtPrime_eq_of_etale (A := R) (B := A) q).symm
    _ = ringKrullDim R := hbase

/-- Helper for Lemma 15.45.7: adjacent separating elements keep the contracted prime chain
strict after comap along a fixed ring map. -/
private theorem strictMono_comap_of_adjacent_separating_elements
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (l : LTSeries (PrimeSpectrum B))
    (hsep : ∀ i : Fin l.length, ∃ y : A,
      φ y ∈ (l i.succ).asIdeal ∧ φ y ∉ (l i.castSucc).asIdeal) :
    StrictMono (fun k ↦ PrimeSpectrum.comap φ (l k)) := by
  -- Separate any two contracted primes by using the witness already chosen for the first
  -- adjacent step between them.
  intro i j hij
  let k : Fin l.length := ⟨i.1, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.2)⟩
  obtain ⟨y, hy_succ, hy_cast⟩ := hsep k
  have hk_cast : k.castSucc = i := by
    ext
    rfl
  have hk_succ_le : k.succ ≤ j := by
    exact show k.1 + 1 ≤ j.1 from Nat.succ_le_of_lt hij
  have hle : PrimeSpectrum.comap φ (l i) ≤ PrimeSpectrum.comap φ (l j) := by
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).1 <|
      by
        simpa [PrimeSpectrum.comap_asIdeal] using
          Ideal.comap_mono
            ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 (l.monotone hij.le))
  have hy_mem_j : y ∈ (PrimeSpectrum.comap φ (l j)).asIdeal := by
    have hy_mem_lj : φ y ∈ (l j).asIdeal := by
      exact ((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 (l.monotone hk_succ_le)) hy_succ
    simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hy_mem_lj
  have hy_not_mem_i : y ∉ (PrimeSpectrum.comap φ (l i)).asIdeal := by
    simpa [hk_cast, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hy_cast
  refine lt_of_le_of_ne hle ?_
  intro hij_eq
  exact hy_not_mem_i (by simpa [hij_eq] using hy_mem_j)

/-- Helper for Lemma 15.45.7: transporting a local algebra map through the canonical `ULift`
equivalences preserves the local-homomorphism property. -/
private theorem ulift_algebraMap_isLocalHom
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    letI : Algebra (ULift.{u} A) (ULift.{u} B) := ULift.algebra' A (ULift.{u} B)
    IsLocalHom (algebraMap (ULift.{u} A) (ULift.{u} B)) := by
  letI : Algebra (ULift.{u} A) (ULift.{u} B) := ULift.algebra' A (ULift.{u} B)
  letI : IsLocalRing (ULift.{u} A) := isLocalRing_ulift (A := A)
  letI : IsLocalRing (ULift.{u} B) := isLocalRing_ulift (A := B)
  have hdown :
      IsLocalHom ((ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom) := by
    -- The downward `ULift` equivalence is surjective between local rings.
    exact Function.Surjective.isLocalHom _
      (ULift.ringEquiv : ULift.{u} A ≃+* A).surjective
  have hup :
      IsLocalHom ((ULift.ringEquiv.symm : B ≃+* ULift.{u} B).toRingHom) := by
    -- The upward `ULift` equivalence is likewise a surjective local map.
    exact Function.Surjective.isLocalHom _
      (ULift.ringEquiv.symm : B ≃+* ULift.{u} B).surjective
  let f : ULift.{u} A →+* ULift.{u} B :=
    ((ULift.ringEquiv.symm : B ≃+* ULift.{u} B).toRingHom).comp
      ((algebraMap A B).comp ((ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom))
  have hf : IsLocalHom f := by
    -- Local homomorphisms are stable under composition with the two `ULift` equivalences.
    dsimp [f]
    infer_instance
  have hf_eq : f = algebraMap (ULift.{u} A) (ULift.{u} B) := by
    -- The chosen `ULift` algebra structure is definitionally this transported composite.
    ext x
    rfl
  simpa [hf_eq] using hf

/-- Helper for Lemma 15.45.7: comap along a composed stage map can be rewritten through the
specified composite equality. -/
private theorem ideal_comap_stage_compat
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (I : Ideal C)
    (hcomp : g.comp f = h) :
    Ideal.comap f (Ideal.comap g I) = Ideal.comap h I := by
  -- Normalize the nested contraction to one comap, then rewrite the composed map.
  rw [Ideal.comap_comap]
  simp [hcomp]

/-- Helper for Lemma 15.45.7: an ind-étale local algebra cannot have larger Krull dimension than
its base local ring. -/
private theorem ringKrullDim_le_base_of_isFilteredColimitOfEtale_local
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    (hcolim : (algebraMap R S).IsFilteredColimitOfEtale) :
    ringKrullDim S ≤ ringKrullDim R := by
  -- Route correction: work entirely in the same-universe `ULift` presentation, descend only the
  -- finite separating elements, and then compare closed-point heights.
  dsimp [RingHom.IsFilteredColimitOfEtale] at hcolim
  rcases hcolim with ⟨J, _, _, D, t, s, hs, hstage⟩
  letI : Algebra R (ULift.{u} S) := ULift.algebra
  letI : Algebra (ULift.{u} R) (ULift.{u} S) := ULift.algebra' R (ULift.{u} S)
  letI : IsLocalRing (ULift.{u} R) := isLocalRing_ulift (A := R)
  letI : IsLocalRing (ULift.{u} S) := isLocalRing_ulift (A := S)
  have hheight :
      (maximalIdeal (ULift.{u} S)).height ≤ (maximalIdeal (ULift.{u} R)).height := by
    rw [Ideal.height_eq_primeHeight]
    refine Order.height_le_iff'.2 ?_
    intro l hl
    have hl_asIdeal : l.last.asIdeal = maximalIdeal (ULift.{u} S) := by
      simpa using congrArg PrimeSpectrum.asIdeal hl
    classical
    let cType := (forget CommRingCat).mapCocone (Cocone.mk _ s)
    have hsType : IsColimit cType := Limits.isColimitOfPreserves (forget CommRingCat) hs
    let hxSep :
        ∀ i : Fin l.length, ∃ z : cType.pt, z ∈ (l i.succ).asIdeal ∧ z ∉ (l i.castSucc).asIdeal :=
      fun i ↦
        SetLike.exists_of_lt <|
          (PrimeSpectrum.asIdeal_lt_asIdeal (l i.castSucc) (l i.succ)).2 (l.step i)
    let x : Fin l.length → cType.pt := fun i ↦ Classical.choose (hxSep i)
    have hx_mem : ∀ i : Fin l.length, x i ∈ (l i.succ).asIdeal := by
      intro i
      exact (Classical.choose_spec (hxSep i)).1
    have hx_not_mem : ∀ i : Fin l.length, x i ∉ (l i.castSucc).asIdeal := by
      intro i
      exact (Classical.choose_spec (hxSep i)).2
    obtain ⟨j, y, hy⟩ := exists_common_stage_of_finite_family cType hsType l.length x
    have hsepStage : ∀ i : Fin l.length, ∃ z : D.obj j,
        (s.app j).hom z ∈ (l i.succ).asIdeal ∧ (s.app j).hom z ∉ (l i.castSucc).asIdeal := by
      intro i
      refine ⟨y i, ?_, ?_⟩
      · have hyi : (s.app j).hom (y i) = x i := by
          simpa [cType] using hy i
        rw [hyi]
        exact hx_mem i
      · have hyi : (s.app j).hom (y i) = x i := by
          simpa [cType] using hy i
        rw [hyi]
        exact hx_not_mem i
    let lA : LTSeries (PrimeSpectrum (D.obj j)) :=
      LTSeries.mk l.length
        (fun i ↦ PrimeSpectrum.comap (s.app j).hom (l i))
        (strictMono_comap_of_adjacent_separating_elements (φ := (s.app j).hom) l hsepStage)
    have hlA_len : lA.length = l.length := rfl
    letI : Algebra (ULift.{u} R) (D.obj j) := (t.app j).hom.toAlgebra
    have hcomp :
        (s.app j).hom.comp (t.app j).hom = algebraMap (ULift.{u} R) (ULift.{u} S) := by
      simpa using congrArg CommRingCat.Hom.hom (hstage j).2
    have hmax_comap :
        Ideal.comap (algebraMap (ULift.{u} R) (ULift.{u} S)) (maximalIdeal (ULift.{u} S)) =
          maximalIdeal (ULift.{u} R) := by
      -- Install the transported local-hom instance, then use the canonical maximal-ideal API.
      haveI : IsLocalHom (algebraMap (ULift.{u} R) (ULift.{u} S)) := by
        simpa using (ulift_algebraMap_isLocalHom (A := R) (B := S))
      simpa using
        (IsLocalRing.maximalIdeal_comap (algebraMap (ULift.{u} R) (ULift.{u} S)))
    have hlA_last :
        lA.last.asIdeal.under (ULift.{u} R) = maximalIdeal (ULift.{u} R) := by
      have hlA_last_asIdeal :
          lA.last.asIdeal = Ideal.comap (s.app j).hom l.last.asIdeal := by
        simpa [lA] using PrimeSpectrum.comap_asIdeal (s.app j).hom l.last
      have hcomap_comp :
          Ideal.comap (t.app j).hom (Ideal.comap (s.app j).hom l.last.asIdeal) =
            Ideal.comap (algebraMap (ULift.{u} R) (ULift.{u} S)) l.last.asIdeal := by
        -- Rewrite the nested contraction through the stage compatibility equality.
        simpa using
          ideal_comap_stage_compat (f := (t.app j).hom) (g := (s.app j).hom)
            (h := algebraMap (ULift.{u} R) (ULift.{u} S)) l.last.asIdeal hcomp
      have hunder :
          lA.last.asIdeal.under (ULift.{u} R) =
            Ideal.comap (t.app j).hom (Ideal.comap (s.app j).hom l.last.asIdeal) := by
        change Ideal.comap (t.app j).hom lA.last.asIdeal =
          Ideal.comap (t.app j).hom (Ideal.comap (s.app j).hom l.last.asIdeal)
        rw [hlA_last_asIdeal]
      have hlA_last_mid :
          lA.last.asIdeal.under (ULift.{u} R) =
            Ideal.comap (algebraMap (ULift.{u} R) (ULift.{u} S)) l.last.asIdeal :=
        hunder.trans hcomap_comp
      calc
        lA.last.asIdeal.under (ULift.{u} R)
            = Ideal.comap (algebraMap (ULift.{u} R) (ULift.{u} S)) l.last.asIdeal := hlA_last_mid
        _ = maximalIdeal (ULift.{u} R) := by
                simpa [hl_asIdeal] using hmax_comap
    have hEtale : Algebra.Etale (ULift.{u} R) (D.obj j) := by
      -- The chosen stage is étale over the lifted base by construction of the ind-étale witness.
      refine (RingHom.etale_algebraMap (R := ULift.{u} R) (S := D.obj j)).mp ?_
      simpa [RingHom.algebraMap_toAlgebra, CommRingCat.etale] using (hstage j).1
    letI : Algebra.Etale (ULift.{u} R) (D.obj j) := hEtale
    have hboundA : (↑lA.length : WithBot ℕ∞) ≤ ringKrullDim (ULift.{u} R) := by
      -- Bound the descended chain by the height of its last prime, then identify that height with
      -- the Krull dimension of the étale localization over the closed point.
      calc
        (↑lA.length : WithBot ℕ∞) ≤ ↑(lA.last.asIdeal.height) := by
          have hlenHeight : (lA.length : ℕ∞) ≤ Order.height lA.last := Order.length_le_height_last
          have hlenHeight' : (lA.length : ℕ∞) ≤ lA.last.asIdeal.height := by
            rw [Ideal.height_eq_primeHeight]
            exact hlenHeight
          exact_mod_cast hlenHeight'
        _ = ringKrullDim (Localization.AtPrime lA.last.asIdeal) := by
            symm
            exact IsLocalization.AtPrime.ringKrullDim_eq_height lA.last.asIdeal
              (Localization.AtPrime lA.last.asIdeal)
        _ = ringKrullDim (ULift.{u} R) := by
            simpa using
              etale_localizationAtPrime_ringKrullDim_eq_base
                (R := ULift.{u} R) (A := D.obj j) lA.last.asIdeal hlA_last
    have hbound :
        (l.length : ℕ∞) ≤ (maximalIdeal (ULift.{u} R)).height := by
      have hboundA' : (↑lA.length : WithBot ℕ∞) ≤ ↑(maximalIdeal (ULift.{u} R)).height := by
        simpa [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using hboundA
      have hboundA'' : (lA.length : ℕ∞) ≤ (maximalIdeal (ULift.{u} R)).height := by
        exact_mod_cast hboundA'
      simpa [hlA_len] using hboundA''
    exact hbound
  calc
    ringKrullDim S = ringKrullDim (ULift.{u} S) := by
      simpa using
        (ringKrullDim_eq_of_ringEquiv (ULift.ringEquiv : ULift.{u} S ≃+* S)).symm
    _ = ↑(maximalIdeal (ULift.{u} S)).height := by
      exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ↑(maximalIdeal (ULift.{u} R)).height := by
      exact_mod_cast hheight
    _ = ringKrullDim (ULift.{u} R) := by
      exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim
    _ = ringKrullDim R := by
      simpa using ringKrullDim_eq_of_ringEquiv (ULift.ringEquiv : ULift.{u} R ≃+* R)

/-- Lemma 15.45.7 (1): a chosen henselization `Rh` of a local ring `R` has the same Krull
dimension as `R`. -/
@[stacks 06LK]
theorem ringKrullDim_henselization_eq :
    ringKrullDim R = ringKrullDim Rh := by
  -- The lower bound is faithful flat descent, and the upper bound comes from descending finite
  -- prime chains to one étale stage in the ind-étale presentation.
  refine le_antisymm ?_ ?_
  · exact ringKrullDim_base_le_of_faithfullyFlat_local
      (R := R) (S := Rh) algebraMap_faithfullyFlat_of_isHenselizationOf
  · exact ringKrullDim_le_base_of_isFilteredColimitOfEtale_local
      (R := R) (S := Rh) IsHenselizationOf.isFilteredColimitOfEtale

-- Proof sketch: as in part `(1)`, the canonical owner is the closed-point comparison
-- `Localization.AtPrime (maximalIdeal R) → Localization.AtPrime (maximalIdeal Rsh)`. The maximal
-- ideal of `Rsh` is the extension of `maximalIdeal R` by
-- `IsStrictHenselizationOf.map_maximalIdeal`, so the closed fiber is the residue field of the
-- localized target and has Krull dimension `0`; the ambient local equality again follows by the
-- canonical identification of a local ring with its closed-point localization on Krull dimension.
/-- Lemma 15.45.7 (2): a chosen strict henselization `Rsh` of a local ring `R` has the same Krull
dimension as `R`. -/
@[stacks 06LK]
theorem ringKrullDim_strictHenselization_eq :
    ringKrullDim R = ringKrullDim Rsh := by
  -- The same source-faithful two-sided comparison works for the strict henselization.
  refine le_antisymm ?_ ?_
  · exact ringKrullDim_base_le_of_faithfullyFlat_local
      (R := R) (S := Rsh) algebraMap_faithfullyFlat_of_isStrictHenselizationOf
  · exact ringKrullDim_le_base_of_isFilteredColimitOfEtale_local
      (R := R) (S := Rsh) IsStrictHenselizationOf.isFilteredColimitOfEtale

end
