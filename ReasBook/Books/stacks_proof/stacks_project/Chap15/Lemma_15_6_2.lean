import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_17_6
import stacks_proof.stacks_project.Chap15.Lemma_15_5_3
import stacks_proof.stacks_project.Chap15.Situation_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopCat CommRingCat
open PrimeSpectrum

universe u

noncomputable section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/- Domain-style sampling for 15.6.2:
- primary domain: prime-spectrum maps in `TopCat` and pushout squares in `CategoryTheory`;
- sampled owner declarations:
  `PrimeSpectrum.comap`,
  `PrimeSpectrum.continuous_comap`,
  `IsPushout`,
  `IsPushout.exists_desc`;
- best owner abstraction: the primitive source-facing data is still
  `S : SurjectiveRingPullbackSituation B A A'`; the induced maps on prime spectra are derived from
  the canonical owner `PrimeSpectrum.comap`, and the universal-property claim is owned by
  `IsPushout`;
- primitive data: the ring maps and surjectivity hypothesis stored in `S`;
- derived API: the topological-space object `S.specBprime` and the four canonical spectrum maps
  `S.specToB`, `S.specToAprime`, `S.specBToBprime`, and `S.specAprimeToBprime`.

Source/core/bridge triage:
- `source-facing`: the pushout statement for the spectrum square of Situation `15.6.1`;
- `core/canonical`: `PrimeSpectrum.comap`, `PrimeSpectrum.continuous_comap`, and `IsPushout`;
- `bridge/view`: the induced `TopCat` morphisms attached to `S`. -/

namespace SurjectiveRingPullbackSituation

variable (S : SurjectiveRingPullbackSituation B A A')

/-- Helper for Lemma 15.6.2: localizing away from an element that is already zero gives a trivial
localization ring. -/
lemma localizationAway_subsingleton_of_eq_zero {R : Type u} [CommRing R] {r : R} (hr : r = 0) :
    Subsingleton (Localization.Away r) := by
  -- Once the multiplicative set contains `0`, the away-localization collapses to a singleton.
  have hzero : (0 : R) ∈ Submonoid.powers r := by
    rw [hr]
    exact Submonoid.mem_powers (0 : R)
  exact IsLocalization.subsingleton (M := Submonoid.powers r) (S := Localization.Away r) hzero

/-- The topological space `Spec(B')` attached to a surjective ring pullback situation. -/
abbrev specBprime : TopCat :=
  TopCat.of (PrimeSpectrum S.Bprime)

/-- The canonical map `Spec(A) → Spec(B)` induced by `B → A`. -/
abbrev specToB : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum B) :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.toA, PrimeSpectrum.continuous_comap S.toA⟩

/-- The canonical map `Spec(A) → Spec(A')` induced by `A' → A`. -/
abbrev specToAprime : TopCat.of (PrimeSpectrum A) ⟶ TopCat.of (PrimeSpectrum A') :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.fromAprime, PrimeSpectrum.continuous_comap S.fromAprime⟩

/-- The canonical map `Spec(B) → Spec(B')` induced by `B' → B`. -/
abbrev specBToBprime : TopCat.of (PrimeSpectrum B) ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToB, PrimeSpectrum.continuous_comap S.bprimeToB⟩

/-- The canonical map `Spec(A') → Spec(B')` induced by `B' → A'`. -/
abbrev specAprimeToBprime : TopCat.of (PrimeSpectrum A') ⟶ S.specBprime :=
  TopCat.ofHom ⟨PrimeSpectrum.comap S.bprimeToAprime, PrimeSpectrum.continuous_comap S.bprimeToAprime⟩

/-- Helper for Lemma 15.6.2: the prime-spectrum square attached to the pullback ring commutes. -/
lemma spec_square_commutes :
    S.specToB ≫ S.specBToBprime = S.specToAprime ≫ S.specAprimeToBprime := by
  -- Evaluate the two composites on a prime of `A` and use the defining pullback identity in `S`.
  ext x y
  change S.toA (S.bprimeToB y) ∈ x.asIdeal ↔ S.fromAprime (S.bprimeToAprime y) ∈ x.asIdeal
  rw [show S.toA (S.bprimeToB y) = S.fromAprime (S.bprimeToAprime y) from
    congrArg (fun f : S.Bprime →+* A => f y) S.comm]

/-- Helper for Lemma 15.6.2: the projection `B' → B` from the fibre product ring is surjective
because `A' → A` is surjective. -/
lemma bprimeToB_surjective :
    Function.Surjective S.bprimeToB := by
  intro b
  obtain ⟨a', ha'⟩ := S.fromAprime_surjective (S.toA b)
  let t : (CommRingCat.pullbackCone (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).pt :=
    ⟨(b, a'), by
      change S.toA b = S.fromAprime a'
      simp [ha']⟩
  let lc : LimitCone (cospan (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)) :=
    ⟨CommRingCat.pullbackCone (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime),
      CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)⟩
  let e := limit.isoLimitCone lc
  refine ⟨e.inv t, ?_⟩
  -- The explicit pullback point `(b, a')` maps back to an element whose first projection is `b`.
  have hpoint :=
    congrArg
      (fun k : lc.cone.pt ⟶ CommRingCat.of B => k.hom t)
      (limit.isoLimitCone_inv_π lc WalkingCospan.left)
  change (e.inv ≫ pullback.fst (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).hom t = b
  simpa [lc, e, CommRingCat.pullbackCone, t] using hpoint

/-- Helper for Lemma 15.6.2: a prime of `B'` lies in the image of `Spec(B) → Spec(B')` exactly
when it contains the kernel of `B' → B`. -/
lemma mem_range_specBToBprime_iff (p' : PrimeSpectrum S.Bprime) :
    p' ∈ Set.range (PrimeSpectrum.comap S.bprimeToB) ↔ RingHom.ker S.bprimeToB ≤ p'.asIdeal := by
  -- Rewrite the image by the standard description for spectra of surjective maps.
  have hrange :
      Set.range (PrimeSpectrum.comap S.bprimeToB) =
        PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) :=
    @range_comap_of_surjective S.Bprime B inferInstance inferInstance S.bprimeToB
      (S.bprimeToB_surjective)
  rw [hrange]
  simp [PrimeSpectrum.mem_zeroLocus]

/-- Helper for Lemma 15.6.2: after localizing away from `u ∈ ker(B' → B)`, the pullback square
collapses and the localized map `B'_u → A'_{b'(u)}` becomes bijective. -/
lemma localizationAway_bprimeToAprime_bijective_of_mem_ker_bprimeToB
    (u : S.Bprime) (hu : S.bprimeToB u = 0) :
    Function.Bijective
      (IsLocalization.Away.map (Localization.Away u)
        (Localization.Away (S.bprimeToAprime u)) S.bprimeToAprime u) := by
  let Bg := Localization.Away (S.bprimeToB u)
  let Rf := Localization.Away (S.bprimeToAprime u)
  let Bh := Localization.Away u
  let Rh := Localization.Away (S.toA (S.bprimeToB u))
  -- The `B`- and `A`-corners become trivial after localizing away from an element mapping to `0`.
  letI : Subsingleton Bg :=
    localizationAway_subsingleton_of_eq_zero (r := S.bprimeToB u) hu
  have htoA : S.toA (S.bprimeToB u) = 0 := by
    simp [hu]
  letI : Subsingleton Rh :=
    localizationAway_subsingleton_of_eq_zero (r := S.toA (S.bprimeToB u)) htoA
  let bottom : Bg →+* Rh := IsLocalization.Away.map Bg Rh S.toA (S.bprimeToB u)
  have hbottom_injective : Function.Injective bottom := Function.injective_of_subsingleton bottom
  have hbottom_surjective : Function.Surjective bottom := fun y ↦ ⟨0, Subsingleton.elim _ _⟩
  let eBottom : CommRingCat.of Bg ≅ CommRingCat.of Rh :=
    (RingEquiv.ofBijective bottom ⟨hbottom_injective, hbottom_surjective⟩).toCommRingCatIso
  letI : IsIso (CommRingCat.ofHom bottom) := eBottom.isIso_hom
  let localizedSq :
      IsPullback
        (ofHom (IsLocalization.Away.map Bh Bg S.bprimeToB u))
        (ofHom (IsLocalization.Away.map Bh Rf S.bprimeToAprime u))
        (ofHom bottom)
        (ofHom (CategoryTheory.IsPullback.localizationAwayRightMap
          (left := S.bprimeToB) (right := S.bprimeToAprime) (s := S.toA) (t := S.fromAprime)
          (h := u) S.isPullback)) :=
    CategoryTheory.IsPullback.localization_away
      (left := S.bprimeToB) (right := S.bprimeToAprime) (s := S.toA) (t := S.fromAprime)
      (h := u) (Bg := Bg) (Rf := Rf) (Bh := Bh) (Rh := Rh) S.isPullback
  let trivialSq :
      IsPullback
        (CommRingCat.ofHom (CategoryTheory.IsPullback.localizationAwayRightMap
            (left := S.bprimeToB) (right := S.bprimeToAprime) (s := S.toA) (t := S.fromAprime)
            (h := u) S.isPullback) ≫
          eBottom.inv)
        (𝟙 (CommRingCat.of Rf))
        (ofHom bottom)
        (CommRingCat.ofHom (CategoryTheory.IsPullback.localizationAwayRightMap
          (left := S.bprimeToB) (right := S.bprimeToAprime) (s := S.toA) (t := S.fromAprime)
          (h := u) S.isPullback)) := by
    -- With the bottom edge now an isomorphism, the identity square on the `A'`-corner is a
    -- pullback by the standard vertical-isomorphism criterion.
    refine IsPullback.of_vert_isIso ?_
    refine ⟨?_⟩
    rw [show CommRingCat.ofHom bottom = eBottom.hom by rfl]
    simp [Category.assoc]
  let e : CommRingCat.of Bh ≅ CommRingCat.of Rf :=
    localizedSq.isoIsPullback _ _ trivialSq
  have hsnd :
      e.hom = ofHom (IsLocalization.Away.map Bh Rf S.bprimeToAprime u) := by
    simpa [e] using localizedSq.isoIsPullback_hom_snd _ _ trivialSq
  have he_bij : Function.Bijective e.hom.hom := e.commRingCatIsoToRingEquiv.bijective
  -- The comparison isomorphism identifies exactly with the localized `B'_u → A'_{b'(u)}` map.
  simpa [e, hsnd] using he_bij

/-- Helper for Lemma 15.6.2: for `u ∈ ker(B' → B)`, the induced map on the corresponding basic
opens is a homeomorphism. -/
noncomputable def basicOpen_homeomorph_of_mem_ker_bprimeToB
    (u : S.Bprime) (hu : S.bprimeToB u = 0) :
    PrimeSpectrum.basicOpen (S.bprimeToAprime u) ≃ₜ PrimeSpectrum.basicOpen u :=
  let e := RingEquiv.ofBijective
    (IsLocalization.Away.map (Localization.Away u)
      (Localization.Away (S.bprimeToAprime u)) S.bprimeToAprime u)
    (S.localizationAway_bprimeToAprime_bijective_of_mem_ker_bprimeToB u hu)
  (primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm.trans
    ((PrimeSpectrum.homeomorphOfRingEquiv e.symm).trans
      (primeSpectrum_localizationAway_homeomorph_D u))

/-- Helper for Lemma 15.6.2: the image of the `A'`-basic-open chart over an element of
`ker(B' → B)` is the corresponding basic open in `Spec(B')`. -/
lemma image_specAprimeToBprime_basicOpen_eq (u : S.Bprime) (hu : S.bprimeToB u = 0) :
    Set.image (PrimeSpectrum.comap S.bprimeToAprime)
      (PrimeSpectrum.basicOpen (S.bprimeToAprime u) : Set (PrimeSpectrum A')) =
        PrimeSpectrum.basicOpen u := by
  let Bh := Localization.Away u
  let Rf := Localization.Away (S.bprimeToAprime u)
  let locMap : Bh →+* Rf := IsLocalization.Away.map Bh Rf S.bprimeToAprime u
  have hbij : Function.Bijective locMap :=
    S.localizationAway_bprimeToAprime_bijective_of_mem_ker_bprimeToB u hu
  have hloc_surjective : Function.Surjective (PrimeSpectrum.comap locMap) := by
    exact (PrimeSpectrum.isHomeomorph_comap_of_bijective hbij).bijective.surjective
  have hcomp :
      PrimeSpectrum.comap S.bprimeToAprime ∘ PrimeSpectrum.comap (algebraMap A' Rf) =
        PrimeSpectrum.comap (algebraMap S.Bprime Bh) ∘ PrimeSpectrum.comap locMap := by
    -- The two composite comaps come from the same composite ring map by the defining formula for
    -- `IsLocalization.Away.map`.
    have hring :
        (algebraMap A' Rf).comp S.bprimeToAprime =
          locMap.comp (algebraMap S.Bprime Bh) := by
      ext y
      simp [locMap, IsLocalization.Away.map]
    rw [← PrimeSpectrum.comap_comp, ← PrimeSpectrum.comap_comp, hring]
  -- Rewrite both basic opens as ranges of localization maps and use surjectivity of the
  -- localized comparison on spectra.
  rw [← PrimeSpectrum.localization_away_comap_range Rf (S.bprimeToAprime u)]
  rw [← Set.range_comp, hcomp, Set.range_comp]
  rw [Set.range_eq_univ.2 hloc_surjective, Set.image_univ]
  exact PrimeSpectrum.localization_away_comap_range Bh u

/-- Helper for Lemma 15.6.2: the canonical map from the topological pushout to `Spec(B')`
obtained by descending the commuting cocone. -/
noncomputable def pushoutToSpecBprime :
    pushout S.specToB S.specToAprime ⟶ S.specBprime :=
  Classical.choose <|
    (IsPushout.of_hasPushout S.specToB S.specToAprime).exists_desc
      S.specBToBprime
      S.specAprimeToBprime
      (S.spec_square_commutes)

/-- Helper for Lemma 15.6.2: the descended pushout map agrees with `Spec(B) → Spec(B')` on the
left pushout leg. -/
lemma pushoutToSpecBprime_inl :
    pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime = S.specBToBprime := by
  -- This is the first defining equation of the descended map.
  exact
    (Classical.choose_spec <|
      (IsPushout.of_hasPushout S.specToB S.specToAprime).exists_desc
        S.specBToBprime
        S.specAprimeToBprime
        (S.spec_square_commutes)).1

/-- Helper for Lemma 15.6.2: the descended pushout map agrees with `Spec(A') → Spec(B')` on the
right pushout leg. -/
lemma pushoutToSpecBprime_inr :
    pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime = S.specAprimeToBprime := by
  -- This is the second defining equation of the descended map.
  exact
    (Classical.choose_spec <|
      (IsPushout.of_hasPushout S.specToB S.specToAprime).exists_desc
        S.specBToBprime
        S.specAprimeToBprime
        (S.spec_square_commutes)).2

/-- Helper for Lemma 15.6.2: an element of `ker(A' → A)` lifts to an element of `ker(B' → B)` by
using the explicit pullback point `(0, a')`. -/
lemma exists_lift_mem_ker_bprimeToB_of_mem_ker_fromAprime {a' : A'}
    (ha' : a' ∈ RingHom.ker S.fromAprime) :
    ∃ z : S.Bprime, S.bprimeToB z = 0 ∧ S.bprimeToAprime z = a' := by
  let t : (CommRingCat.pullbackCone (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).pt :=
    ⟨(0, a'), by
      change S.toA 0 = S.fromAprime a'
      simpa using ha'.symm⟩
  let lc : LimitCone (cospan (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)) :=
    ⟨CommRingCat.pullbackCone (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime),
      CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)⟩
  let e := limit.isoLimitCone lc
  refine ⟨e.inv t, ?_, ?_⟩
  · -- The explicit pullback point has first coordinate `0`, so its lift lands in `ker(B' → B)`.
    have hfst :=
      congrArg
        (fun k : lc.cone.pt ⟶ CommRingCat.of B => k.hom t)
        (limit.isoLimitCone_inv_π lc WalkingCospan.left)
    change (e.inv ≫ pullback.fst (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).hom t = 0
    simpa [lc, e, t] using hfst
  · -- The second coordinate of the same pullback point is exactly the original element `a'`.
    have hsnd :=
      congrArg
        (fun k : lc.cone.pt ⟶ CommRingCat.of A' => k.hom t)
        (limit.isoLimitCone_inv_π lc WalkingCospan.right)
    change (e.inv ≫ pullback.snd (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).hom t = a'
    simpa [lc, e, t] using hsnd

/-- Helper for Lemma 15.6.2: a point of `Spec(A')` lying over the closed locus
`V(ker(B' → B))` contains `ker(A' → A)`. -/
lemma ker_fromAprime_le_of_mem_closed_locus (q' : PrimeSpectrum A')
    (hq' : RingHom.ker S.bprimeToB ≤ (PrimeSpectrum.comap S.bprimeToAprime q').asIdeal) :
    RingHom.ker S.fromAprime ≤ q'.asIdeal := by
  intro a' ha'
  obtain ⟨z, hzB, hzA'⟩ := S.exists_lift_mem_ker_bprimeToB_of_mem_ker_fromAprime ha'
  have hzker : z ∈ RingHom.ker S.bprimeToB := by
    simp [RingHom.mem_ker, hzB]
  have hzcomap : z ∈ (PrimeSpectrum.comap S.bprimeToAprime q').asIdeal := hq' hzker
  -- Applying the closed-locus containment to the lifted pullback point returns the original
  -- element of `A'`.
  change S.bprimeToAprime z ∈ q'.asIdeal at hzcomap
  simpa [hzA'] using hzcomap

/-- Helper for Lemma 15.6.2: a right-hand point whose image in `Spec(B')` lies in the closed
locus already comes from `Spec(A)`, so the pushout identifies it with a left-hand representative. -/
lemma right_eq_left_of_mem_closed_locus (q' : PrimeSpectrum A')
    (hq' : RingHom.ker S.bprimeToB ≤ (PrimeSpectrum.comap S.bprimeToAprime q').asIdeal) :
    ∃ a : PrimeSpectrum A,
      PrimeSpectrum.comap S.fromAprime a = q' ∧
        (pushout.inr S.specToB S.specToAprime) q' =
          (pushout.inl S.specToB S.specToAprime) (PrimeSpectrum.comap S.toA a) := by
  have hker : RingHom.ker S.fromAprime ≤ q'.asIdeal :=
    S.ker_fromAprime_le_of_mem_closed_locus q' hq'
  have hrange :
      Set.range (PrimeSpectrum.comap S.fromAprime) =
        PrimeSpectrum.zeroLocus (RingHom.ker S.fromAprime : Set A') := by
    simpa using
      (range_comap_of_surjective (R := A') (S := A) S.fromAprime S.fromAprime_surjective)
  have hqzero : q' ∈ PrimeSpectrum.zeroLocus (RingHom.ker S.fromAprime : Set A') := by
    exact (PrimeSpectrum.mem_zeroLocus q' (RingHom.ker S.fromAprime : Set A')).2 hker
  rw [← hrange] at hqzero
  obtain ⟨a, rfl⟩ := hqzero
  refine ⟨a, rfl, ?_⟩
  -- The pushout relation glues the left and right representatives of the same point of
  -- `Spec(A)`.
  have hglue :=
    congrArg
      (fun f : TopCat.of (PrimeSpectrum A) ⟶ pushout S.specToB S.specToAprime => f a)
      (pushout.condition (f := S.specToB) (g := S.specToAprime))
  simpa using hglue.symm

/-- Helper for Lemma 15.6.2: every point coming from `Spec(B)` lands in the closed locus
`V(ker(B' → B))` of `Spec(B')`. -/
lemma preimage_specBToBprime_zeroLocus_eq_univ :
    (PrimeSpectrum.comap S.bprimeToB) ⁻¹'
        PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) =
      Set.univ := by
  -- On the left leg, the kernel of `B' → B` vanishes after applying `B' → B`.
  ext p
  constructor
  · intro _
    simp
  · intro _
    change (PrimeSpectrum.comap S.bprimeToB p) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime)
    rw [PrimeSpectrum.mem_zeroLocus]
    intro z hz
    change S.bprimeToB z ∈ p.asIdeal
    simp [RingHom.mem_ker.mp hz]

/-- Helper for Lemma 15.6.2: on the `Spec(A')` leg, pulling back the closed locus
`V(ker(B' → B))` gives exactly `V(ker(A' → A))`. -/
lemma preimage_specAprimeToBprime_zeroLocus_eq_zeroLocus :
    (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
        PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) =
      PrimeSpectrum.zeroLocus (RingHom.ker S.fromAprime : Set A') := by
  -- The forward direction is the already proved closed-locus bridge on `A'`.
  ext q'
  constructor
  · intro hq'
    change (PrimeSpectrum.comap S.bprimeToAprime q') ∈
      PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) at hq'
    rw [PrimeSpectrum.mem_zeroLocus] at hq' ⊢
    exact S.ker_fromAprime_le_of_mem_closed_locus q' hq'
  · intro hq'
    change (PrimeSpectrum.comap S.bprimeToAprime q') ∈
      PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime)
    rw [PrimeSpectrum.mem_zeroLocus] at hq' ⊢
    intro z hz
    change S.bprimeToAprime z ∈ q'.asIdeal
    have hzA : S.fromAprime (S.bprimeToAprime z) = 0 := by
      rw [← RingHom.comp_apply, ← S.comm]
      simp [RingHom.mem_ker.mp hz]
    exact hq' <| by
      simpa [RingHom.mem_ker, hzA]

/-- Helper for Lemma 15.6.2: on the `Spec(A')` leg, the pullback of the closed locus
`V(ker(B' → B))` is the image of `Spec(A)` under `Spec(A) → Spec(A')`. -/
lemma preimage_specAprimeToBprime_zeroLocus_eq_range_specToAprime :
    (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
        PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) =
      Set.range (PrimeSpectrum.comap S.fromAprime) := by
  -- Rewrite `V(ker(A' → A))` by the standard image description for a surjective spectrum map.
  rw [S.preimage_specAprimeToBprime_zeroLocus_eq_zeroLocus]
  simpa using
    (range_comap_of_surjective (R := A') (S := A) S.fromAprime S.fromAprime_surjective).symm

/-- Helper for Lemma 15.6.2: if `u ∈ ker(B' → B)`, then the left leg does not meet the basic
open `D(u)` in `Spec(B')`. -/
lemma preimage_specBToBprime_basicOpen_eq_empty
    (u : S.Bprime) (hu : S.bprimeToB u = 0) :
    (PrimeSpectrum.comap S.bprimeToB) ⁻¹'
        (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) =
      ∅ := by
  -- Along `Spec(B) → Spec(B')`, the element `u` becomes `0`, so `D(u)` pulls back to the empty
  -- basic open.
  ext p
  simp [hu]

/-- Helper for Lemma 15.6.2: pulling back `D(u) ⊆ Spec(B')` along `Spec(A') → Spec(B')` gives the
basic open `D(b'(u)) ⊆ Spec(A')`. -/
lemma preimage_specAprimeToBprime_basicOpen_eq_basicOpen (u : S.Bprime) :
    (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
        (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) =
      PrimeSpectrum.basicOpen (S.bprimeToAprime u) := by
  -- Membership in a basic open is just non-membership of the defining element in the prime ideal.
  ext q'
  simp

/-- Helper for Lemma 15.6.2: every pushout point comes from either the `Spec(B)` leg or the
`Spec(A')` leg after forgetting to the underlying type-level pushout. -/
lemma pushout_point_cases (x : ↑(pushout S.specToB S.specToAprime)) :
    (∃ p : PrimeSpectrum B, (pushout.inl S.specToB S.specToAprime) p = x) ∨
      ∃ q' : PrimeSpectrum A', (pushout.inr S.specToB S.specToAprime) q' = x := by
  -- Route correction: use the existing `Type`-level pushout representative lemma after forgetting
  -- the `TopCat` pushout cocone instead of rebuilding a local quotient model.
  let c : PushoutCocone S.specToB S.specToAprime :=
    PushoutCocone.mk
      (pushout.inl S.specToB S.specToAprime)
      (pushout.inr S.specToB S.specToAprime)
      (pushout.condition (f := S.specToB) (g := S.specToAprime))
  let hcType :
      IsColimit ((forget TopCat).mapCocone c) :=
    Limits.isColimitOfPreserves (forget TopCat)
      (pushoutIsPushout S.specToB S.specToAprime)
  let hType :
      IsPushout ((forget TopCat).map S.specToB) ((forget TopCat).map S.specToAprime)
        ((forget TopCat).map (pushout.inl S.specToB S.specToAprime))
        ((forget TopCat).map (pushout.inr S.specToB S.specToAprime)) :=
    IsPushout.of_isColimit_cocone hcType
  simpa using Types.eq_or_eq_of_isPushout hType x

/-- Helper for Lemma 15.6.2: openness on the topological pushout is detected on the two visible
legs `Spec(B)` and `Spec(A')`. -/
lemma pushout_isOpen_iff_on_legs (U : Set ↑(pushout S.specToB S.specToAprime)) :
    IsOpen U ↔
      IsOpen ((pushout.inl S.specToB S.specToAprime) ⁻¹' U) ∧
        IsOpen ((pushout.inr S.specToB S.specToAprime) ⁻¹' U) := by
  -- The pushout topology is the colimit topology, so it is enough to inspect the two generators.
  let c : PushoutCocone S.specToB S.specToAprime :=
    PushoutCocone.mk
      (pushout.inl S.specToB S.specToAprime)
      (pushout.inr S.specToB S.specToAprime)
      (pushout.condition (f := S.specToB) (g := S.specToAprime))
  have hopen :
      IsOpen U ↔ ∀ j : WalkingSpan, IsOpen ((c.ι.app j) ⁻¹' U) :=
    TopCat.isOpen_iff_of_isColimit c (pushoutIsPushout S.specToB S.specToAprime) U
  constructor
  · intro hU
    exact ⟨(hopen.mp hU) WalkingSpan.left, (hopen.mp hU) WalkingSpan.right⟩
  · rintro ⟨hleft, hright⟩
    refine hopen.mpr ?_
    intro j
    rcases j with _ | j
    ·
        -- On the zero object, the cocone map factors through the left leg.
        simpa [c, PushoutCocone.mk_ι_app_zero, Set.preimage_preimage] using
          hleft.preimage S.specToB.hom.continuous
    · cases j with
      | left =>
          simpa [c, PushoutCocone.mk_ι_app_left] using hleft
      | right =>
          simpa [c, PushoutCocone.mk_ι_app_right] using hright

/-- Helper for Lemma 15.6.2: the preimage of the closed locus `V(ker(B' → B))` along the
descended pushout map is exactly the left-hand image of `Spec(B)`. -/
lemma pushout_preimage_zeroLocus_eq_range_inl :
    S.pushoutToSpecBprime ⁻¹'
        PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) =
      Set.range (pushout.inl S.specToB S.specToAprime) := by
  -- Split a pushout point into left/right representatives and use the closed-locus description on
  -- each leg.
  ext x
  constructor
  · intro hx
    rcases S.pushout_point_cases x with ⟨p, rfl⟩ | ⟨q', hq'⟩
    · exact ⟨p, rfl⟩
    · have hx' :
          ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q') ∈
            PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
        simpa [hq'] using hx
      rw [S.pushoutToSpecBprime_inr] at hx'
      have hqmem :
          q' ∈ (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
            PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
        simpa [Set.mem_preimage] using hx'
      rw [S.preimage_specAprimeToBprime_zeroLocus_eq_range_specToAprime] at hqmem
      rcases hqmem with ⟨a, rfl⟩
      refine ⟨PrimeSpectrum.comap S.toA a, ?_⟩
      -- The pushout relation identifies the two legs on points coming from `Spec(A)`.
      calc
        (pushout.inl S.specToB S.specToAprime) (PrimeSpectrum.comap S.toA a) =
            (pushout.inr S.specToB S.specToAprime) (PrimeSpectrum.comap S.fromAprime a) := by
              have hglue :=
                congrArg
                  (fun f : TopCat.of (PrimeSpectrum A) ⟶ pushout S.specToB S.specToAprime => f a)
                  (pushout.condition (f := S.specToB) (g := S.specToAprime))
              simpa using hglue
        _ = x := by
              simpa using hq'
  · rintro ⟨p, rfl⟩
    -- Points from `Spec(B)` always land in the closed locus because `ker(B' → B)` maps to zero.
    have hp :
        ((PrimeSpectrum.comap S.bprimeToB) p) ∈
          PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
      have hp' :
          p ∈ (PrimeSpectrum.comap S.bprimeToB) ⁻¹'
            PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
        rw [S.preimage_specBToBprime_zeroLocus_eq_univ]
        simp
      exact hp'
    change ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime)
    rw [S.pushoutToSpecBprime_inl]
    exact hp

/-- Helper for Lemma 15.6.2: for `u ∈ ker(B' → B)`, the preimage of the basic open `D(u)` along
the descended pushout map is exactly the image of the corresponding right-hand basic-open chart. -/
lemma pushout_preimage_basicOpen_eq_range_inr_basicOpen
    (u : S.Bprime) (hu : S.bprimeToB u = 0) :
    S.pushoutToSpecBprime ⁻¹' (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) =
      Set.range
        (fun q : PrimeSpectrum.basicOpen (S.bprimeToAprime u) =>
          (pushout.inr S.specToB S.specToAprime) q.1) := by
  -- The left leg misses `D(u)` because `u` maps to zero in `B`, while the right leg pulls back
  -- `D(u)` to the basic open `D(b'(u))`.
  ext x
  constructor
  · intro hx
    rcases S.pushout_point_cases x with ⟨p, hp⟩ | ⟨q', hq'⟩
    · have hp' :
          ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p) ∈
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
        simpa [hp] using hx
      rw [S.pushoutToSpecBprime_inl] at hp'
      have hempty :
          p ∈ (PrimeSpectrum.comap S.bprimeToB) ⁻¹'
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := hp'
      rw [S.preimage_specBToBprime_basicOpen_eq_empty u hu] at hempty
      exact False.elim <| by simpa using hempty
    · have hqbasic :
          q' ∈ PrimeSpectrum.basicOpen (S.bprimeToAprime u) := by
        have hq' :
            ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q') ∈
              (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
          simpa [hq'] using hx
        rw [S.pushoutToSpecBprime_inr] at hq'
        have hqmem :
            q' ∈ (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
              (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
          simpa [Set.mem_preimage] using hq'
        rw [S.preimage_specAprimeToBprime_basicOpen_eq_basicOpen u] at hqmem
        exact hqmem
      exact ⟨⟨q', hqbasic⟩, by simpa using hq'⟩
  · rintro ⟨q, rfl⟩
    -- A point of the right-hand basic-open chart maps into the corresponding basic open of
    -- `Spec(B')`.
    have hq :
        (PrimeSpectrum.comap S.bprimeToAprime q.1) ∈
          (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
      have hq' :
          q.1 ∈ (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
            (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
        rw [S.preimage_specAprimeToBprime_basicOpen_eq_basicOpen u]
        exact q.2
      exact hq'
    change ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q.1) ∈
      (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime))
    rw [S.pushoutToSpecBprime_inr]
    exact hq

/-- Helper for Lemma 15.6.2: every prime of `B'` lies either on the closed image of `Spec(B)` or
in one of the kernel basic-open charts. -/
lemma closed_locus_or_mem_kernel_basicOpen (p' : PrimeSpectrum S.Bprime) :
    RingHom.ker S.bprimeToB ≤ p'.asIdeal ∨
      ∃ u : S.Bprime, S.bprimeToB u = 0 ∧ p' ∈ PrimeSpectrum.basicOpen u := by
  -- The source decomposition splits according to whether the kernel is contained in the prime.
  by_cases hclosed : RingHom.ker S.bprimeToB ≤ p'.asIdeal
  · exact Or.inl hclosed
  · right
    -- If the kernel is not contained, choose an element of the kernel outside the prime.
    change ¬ ∀ u : S.Bprime, u ∈ RingHom.ker S.bprimeToB → u ∈ p'.asIdeal at hclosed
    push Not at hclosed
    obtain ⟨u, huKer, huNotMem⟩ := hclosed
    refine ⟨u, ?_, ?_⟩
    · simpa [RingHom.mem_ker] using huKer
    · simpa [PrimeSpectrum.mem_basicOpen] using huNotMem

/-- Helper for Lemma 15.6.2: on a kernel basic-open chart, the constructed homeomorphism is just
the restricted comap `Spec(A') → Spec(B')`. -/
lemma basicOpen_homeomorph_of_mem_ker_bprimeToB_apply
    (u : S.Bprime) (hu : S.bprimeToB u = 0)
    (q : PrimeSpectrum.basicOpen (S.bprimeToAprime u)) :
    (S.basicOpen_homeomorph_of_mem_ker_bprimeToB u hu q).1 =
      PrimeSpectrum.comap S.bprimeToAprime q.1 := by
  -- Compare the chart homeomorphism with the defining localization maps on both sides.
  let Bh := Localization.Away u
  let Rf := Localization.Away (S.bprimeToAprime u)
  let locMap : Bh →+* Rf := IsLocalization.Away.map Bh Rf S.bprimeToAprime u
  let e := RingEquiv.ofBijective locMap
    (S.localizationAway_bprimeToAprime_bijective_of_mem_ker_bprimeToB u hu)
  have hloc :
      e.toRingHom.comp (algebraMap S.Bprime Bh) =
        (algebraMap A' Rf).comp S.bprimeToAprime := by
    ext x
    change locMap ((algebraMap S.Bprime Bh) x) = (algebraMap A' Rf) (S.bprimeToAprime x)
    simp [locMap, IsLocalization.Away.map]
  change PrimeSpectrum.comap (algebraMap S.Bprime Bh)
      ((PrimeSpectrum.homeomorphOfRingEquiv e.symm)
        ((primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm q)) =
    PrimeSpectrum.comap S.bprimeToAprime q.1
  change PrimeSpectrum.comap (algebraMap S.Bprime Bh)
      (PrimeSpectrum.comap e.toRingHom
        ((primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm q)) =
    PrimeSpectrum.comap S.bprimeToAprime q.1
  change PrimeSpectrum.comap (e.toRingHom.comp (algebraMap S.Bprime Bh))
      ((primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm q) =
    PrimeSpectrum.comap S.bprimeToAprime q.1
  rw [hloc]
  have hsymm' :=
    primeSpectrum_localizationAway_homeomorph_D_apply (S.bprimeToAprime u)
      ((primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm q)
  have hq :
      primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)
        ((primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm q) = q := by
    simp
  have hsymm :
      PrimeSpectrum.comap (algebraMap A' Rf)
        ((primeSpectrum_localizationAway_homeomorph_D (S.bprimeToAprime u)).symm q) = q.1 := by
    simpa [hq] using hsymm'.symm
  exact congrArg (PrimeSpectrum.comap S.bprimeToAprime) hsymm

/-- Helper for Lemma 15.6.2: on each kernel basic-open chart, `Spec(A') → Spec(B')` is
injective. -/
lemma specAprimeToBprime_injOn_basicOpen_of_mem_ker_bprimeToB
    (u : S.Bprime) (hu : S.bprimeToB u = 0) :
    Set.InjOn (PrimeSpectrum.comap S.bprimeToAprime)
      (PrimeSpectrum.basicOpen (S.bprimeToAprime u) : Set (PrimeSpectrum A')) := by
  -- The localized chart homeomorphism packages the comparison map as a genuine bijection.
  intro q₁ hq₁ q₂ hq₂ hq
  have hsub :
      (S.basicOpen_homeomorph_of_mem_ker_bprimeToB u hu ⟨q₁, hq₁⟩).1 =
        (S.basicOpen_homeomorph_of_mem_ker_bprimeToB u hu ⟨q₂, hq₂⟩).1 := by
    simpa [S.basicOpen_homeomorph_of_mem_ker_bprimeToB_apply u hu] using hq
  have hchart : (⟨q₁, hq₁⟩ : PrimeSpectrum.basicOpen (S.bprimeToAprime u)) = ⟨q₂, hq₂⟩ := by
    exact (S.basicOpen_homeomorph_of_mem_ker_bprimeToB u hu).injective <| Subtype.ext hsub
  exact congrArg Subtype.val hchart

/-- Helper for Lemma 15.6.2: the descended map from the topological pushout to `Spec(B')` is
bijective. -/
lemma pushoutToSpecBprime_bijective :
    Function.Bijective S.pushoutToSpecBprime := by
  constructor
  · intro x y hxy
    -- Split the common image point into the closed piece or a kernel basic-open chart.
    let p' : PrimeSpectrum S.Bprime := S.pushoutToSpecBprime x
    have hp' : S.pushoutToSpecBprime y = p' := by
      simpa [p'] using hxy.symm
    rcases S.closed_locus_or_mem_kernel_basicOpen p' with hclosed | ⟨u, hu, hbasic⟩
    · have hpclosed : p' ∈ PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
        rw [PrimeSpectrum.mem_zeroLocus]
        exact hclosed
      have hxclosed : x ∈ S.pushoutToSpecBprime ⁻¹'
          PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
        simpa [p', Set.mem_preimage] using hpclosed
      have hyclosed : y ∈ S.pushoutToSpecBprime ⁻¹'
          PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
        simpa [hp', Set.mem_preimage] using hpclosed
      rw [S.pushout_preimage_zeroLocus_eq_range_inl] at hxclosed hyclosed
      rcases hxclosed with ⟨p₁, rfl⟩
      rcases hyclosed with ⟨p₂, rfl⟩
      -- On the closed piece, injectivity comes from the surjective-spectrum closed embedding.
      have hp : PrimeSpectrum.comap S.bprimeToB p₁ = PrimeSpectrum.comap S.bprimeToB p₂ := by
        change ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p₁) =
          ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p₂) at hxy
        simpa [S.pushoutToSpecBprime_inl] using hxy
      have hinj : Function.Injective (PrimeSpectrum.comap S.bprimeToB) :=
        (PrimeSpectrum.isClosedEmbedding_comap_of_surjective B S.bprimeToB
          S.bprimeToB_surjective).toIsEmbedding.injective
      have hp12 : p₁ = p₂ := hinj hp
      simpa [hp12]
    · have hxbasic : x ∈ S.pushoutToSpecBprime ⁻¹'
          (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
        simpa [Set.mem_preimage, p'] using hbasic
      have hybasic : y ∈ S.pushoutToSpecBprime ⁻¹'
          (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum S.Bprime)) := by
        simpa [Set.mem_preimage, hp'] using hbasic
      rw [S.pushout_preimage_basicOpen_eq_range_inr_basicOpen u hu] at hxbasic hybasic
      rcases hxbasic with ⟨q₁, rfl⟩
      rcases hybasic with ⟨q₂, rfl⟩
      -- On each kernel chart, injectivity is the localized homeomorphism proved above.
      have hq : PrimeSpectrum.comap S.bprimeToAprime q₁.1 = PrimeSpectrum.comap S.bprimeToAprime q₂.1 := by
        change ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q₁.1) =
          ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q₂.1) at hxy
        simpa [S.pushoutToSpecBprime_inr] using hxy
      have hqeq : q₁.1 = q₂.1 :=
        S.specAprimeToBprime_injOn_basicOpen_of_mem_ker_bprimeToB u hu q₁.2 q₂.2 hq
      simpa [hqeq]
  · intro p'
    -- Every target prime comes either from the closed piece or from a kernel chart.
    rcases S.closed_locus_or_mem_kernel_basicOpen p' with hclosed | ⟨u, hu, hbasic⟩
    · rw [← S.mem_range_specBToBprime_iff p'] at hclosed
      rcases hclosed with ⟨p, hp⟩
      refine ⟨(pushout.inl S.specToB S.specToAprime) p, ?_⟩
      change ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p) = p'
      simpa [S.pushoutToSpecBprime_inl] using hp
    · have hbasic' :
          p' ∈ Set.image (PrimeSpectrum.comap S.bprimeToAprime)
            (PrimeSpectrum.basicOpen (S.bprimeToAprime u) : Set (PrimeSpectrum A')) := by
        exact (S.image_specAprimeToBprime_basicOpen_eq u hu).symm ▸ hbasic
      rcases hbasic' with ⟨q', hq', hqeq⟩
      refine ⟨(pushout.inr S.specToB S.specToAprime) q', ?_⟩
      change ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q') = p'
      simpa [S.pushoutToSpecBprime_inr] using hqeq

/-- Helper for Lemma 15.6.2: the image of a subset of the pushout under the descended map is the
union of the images of its two legwise preimages. -/
lemma pushoutToSpecBprime_image_eq_leg_images
    (U : Set ↑(pushout S.specToB S.specToAprime)) :
    S.pushoutToSpecBprime '' U =
      Set.image (PrimeSpectrum.comap S.bprimeToB)
        ((pushout.inl S.specToB S.specToAprime) ⁻¹' U) ∪
      Set.image (PrimeSpectrum.comap S.bprimeToAprime)
        ((pushout.inr S.specToB S.specToAprime) ⁻¹' U) := by
  ext x
  constructor
  · rintro ⟨y, hyU, rfl⟩
    -- Split the pushout point into the left or right leg and rewrite through the descended map.
    rcases S.pushout_point_cases y with ⟨p, rfl⟩ | ⟨q', rfl⟩
    · left
      refine ⟨p, hyU, ?_⟩
      change PrimeSpectrum.comap S.bprimeToB p =
        ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p)
      simp [S.pushoutToSpecBprime_inl]
    · right
      refine ⟨q', hyU, ?_⟩
      change PrimeSpectrum.comap S.bprimeToAprime q' =
        ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q')
      simp [S.pushoutToSpecBprime_inr]
  · rintro (⟨p, hpU, rfl⟩ | ⟨q', hqU, rfl⟩)
    · -- Each left-hand image point comes from the corresponding pushout generator.
      refine ⟨(pushout.inl S.specToB S.specToAprime) p, hpU, ?_⟩
      change ((pushout.inl S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) p) =
        PrimeSpectrum.comap S.bprimeToB p
      simp [S.pushoutToSpecBprime_inl]
    · -- Each right-hand image point comes from the corresponding pushout generator.
      refine ⟨(pushout.inr S.specToB S.specToAprime) q', hqU, ?_⟩
      change ((pushout.inr S.specToB S.specToAprime ≫ S.pushoutToSpecBprime) q') =
        PrimeSpectrum.comap S.bprimeToAprime q'
      simp [S.pushoutToSpecBprime_inr]

/-- Helper for Lemma 15.6.2: if a right-hand point of a compatible open pair lands in the closed
locus, then it already has a left representative lying in the left open. -/
lemma exists_left_preimage_of_compatible_opens_of_right_mem_closed_locus
    {V : Set (PrimeSpectrum B)} {U' : Set (PrimeSpectrum A')}
    (hcompat : S.specToB ⁻¹' V = S.specToAprime ⁻¹' U')
    {q' : PrimeSpectrum A'} (hq' : q' ∈ U')
    (hq'closed : RingHom.ker S.bprimeToB ≤ (PrimeSpectrum.comap S.bprimeToAprime q').asIdeal) :
    ∃ p ∈ V,
      PrimeSpectrum.comap S.bprimeToB p = PrimeSpectrum.comap S.bprimeToAprime q' := by
  -- Move the closed-locus point to the left via the already-proved range description.
  obtain ⟨a, ha, _⟩ := S.right_eq_left_of_mem_closed_locus q' hq'closed
  have haU : a ∈ S.specToAprime ⁻¹' U' := by
    simpa [ha]
  rw [← hcompat] at haU
  refine ⟨PrimeSpectrum.comap S.toA a, haU, ?_⟩
  -- The two left/right representatives have the same image in `Spec(B')` by commutativity.
  have hsq :=
    congrArg
      (fun f : TopCat.of (PrimeSpectrum A) ⟶ S.specBprime => f a)
      (S.spec_square_commutes)
  change PrimeSpectrum.comap S.bprimeToB (PrimeSpectrum.comap S.toA a) =
    PrimeSpectrum.comap S.bprimeToAprime (PrimeSpectrum.comap S.fromAprime a) at hsq
  simpa [ha] using hsq

/-- Helper for Lemma 15.6.2: a compatible pair `(b, a')` with the same image in `A` comes from a
point of the pullback ring `B'`. -/
lemma exists_bprime_of_compatible_pair {b : B} {a' : A'}
    (hcompat : S.toA b = S.fromAprime a') :
    ∃ z : S.Bprime, S.bprimeToB z = b ∧ S.bprimeToAprime z = a' := by
  have hpair : S.toA b = S.fromAprime a' := hcompat
  let t : (CommRingCat.pullbackCone (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).pt :=
    ⟨(b, a'), hpair⟩
  let lc : LimitCone (cospan (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)) :=
    ⟨CommRingCat.pullbackCone (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime),
      CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)⟩
  let e := limit.isoLimitCone lc
  refine ⟨e.inv t, ?_, ?_⟩
  · -- The first pullback projection recovers the chosen `b`.
    have hfst :=
      congrArg
        (fun k : lc.cone.pt ⟶ CommRingCat.of B => k.hom t)
        (limit.isoLimitCone_inv_π lc WalkingCospan.left)
    change (e.inv ≫ pullback.fst (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).hom t = b
    simpa [lc, e, t] using hfst
  · -- The second pullback projection recovers the chosen `a'`.
    have hsnd :=
      congrArg
        (fun k : lc.cone.pt ⟶ CommRingCat.of A' => k.hom t)
        (limit.isoLimitCone_inv_π lc WalkingCospan.right)
    change (e.inv ≫ pullback.snd (CommRingCat.ofHom S.toA) (CommRingCat.ofHom S.fromAprime)).hom t = a'
    simpa [lc, e, t] using hsnd

/-- Helper for Lemma 15.6.2: a right-hand point outside the closed locus admits a kernel
basic-open neighborhood whose image is still inside the right-hand open set. -/
lemma right_image_neighborhood_of_open
    {U' : Set (PrimeSpectrum A')}
    (hU' : IsOpen U')
    {q' : PrimeSpectrum A'} (hq' : q' ∈ U')
    (hnot : ¬ RingHom.ker S.fromAprime ≤ q'.asIdeal) :
    ∃ W : Set (PrimeSpectrum S.Bprime),
      IsOpen W ∧ PrimeSpectrum.comap S.bprimeToAprime q' ∈ W ∧
        W ⊆ Set.image (PrimeSpectrum.comap S.bprimeToAprime) U' := by
  have hq'nhds : U' ∈ nhds q' := hU'.mem_nhds hq'
  rcases (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 hq'nhds with
    ⟨T, hT, hq'T, hTsub⟩
  rcases hT with ⟨b', rfl⟩
  change b' ∉ q'.asIdeal at hq'T
  change ¬ ∀ a' : A', a' ∈ RingHom.ker S.fromAprime → a' ∈ q'.asIdeal at hnot
  push Not at hnot
  obtain ⟨a', haKer, haNotMem⟩ := hnot
  have habKer : a' * b' ∈ RingHom.ker S.fromAprime := by
    exact Ideal.mul_mem_right _ _ haKer
  have habNotMem : a' * b' ∉ q'.asIdeal := by
    intro habMem
    rcases q'.2.mem_or_mem habMem with haMem | hbMem
    · exact haNotMem haMem
    · exact hq'T hbMem
  obtain ⟨u, huB, huA⟩ := S.exists_lift_mem_ker_bprimeToB_of_mem_ker_fromAprime habKer
  refine ⟨PrimeSpectrum.basicOpen u, isOpen_basicOpen, ?_, ?_⟩
  · -- The chosen kernel element still avoids the original prime, so its image point lies in
    -- the corresponding basic-open chart.
    change S.bprimeToAprime u ∉ q'.asIdeal
    simpa [huA] using habNotMem
  · intro x hx
    -- On a kernel chart the right-hand map is a homeomorphism onto its image.
    have hx' :
        x ∈ Set.image (PrimeSpectrum.comap S.bprimeToAprime)
          (PrimeSpectrum.basicOpen (S.bprimeToAprime u) : Set (PrimeSpectrum A')) := by
      rw [S.image_specAprimeToBprime_basicOpen_eq u huB]
      exact hx
    rcases hx' with ⟨r, hr, rfl⟩
    have hrNotMem : S.bprimeToAprime u ∉ r.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hr
    have hrb' : b' ∉ r.asIdeal := by
      intro hbMem
      have habMem : a' * b' ∈ r.asIdeal := Ideal.mul_mem_left _ _ hbMem
      exact hrNotMem <| by simpa [huA] using habMem
    refine ⟨r, hTsub ?_, rfl⟩
    simpa [PrimeSpectrum.mem_basicOpen] using hrb'

/-- Helper for Lemma 15.6.2: from a left basic-open chart contained in a compatible open `V`, one
can clear denominators on the right and find a basic-open chart contained in `U'`. -/
lemma exists_right_basicOpen_subset_of_compatible_left_basicOpen
    {V : Set (PrimeSpectrum B)} {U' : Set (PrimeSpectrum A')}
    (hU' : IsOpen U')
    (hcompat : S.specToB ⁻¹' V = S.specToAprime ⁻¹' U')
    {g : B} (hgV : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)) ⊆ V)
    {f' : A'} (hf' : S.fromAprime f' = S.toA g) :
    ∃ n : ℕ, ∃ a' : A',
      S.fromAprime a' = S.toA g ^ n ∧
        (PrimeSpectrum.basicOpen (a' * f') : Set (PrimeSpectrum A')) ⊆ U' := by
  -- Route correction: package the source's localized separator on `D(f')` as the equivalent
  -- global statement `f' ∈ radical (ker(fromAprime) ⊔ J)`, where `U'ᶜ = V(J)`.
  obtain ⟨J, hJ⟩ :=
    (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (R := A') U'ᶜ).mp hU'.isClosed_compl
  have hdisj :
      PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A') ∩
        (PrimeSpectrum.basicOpen f' : Set (PrimeSpectrum A')) = ∅ := by
    -- A prime in `V(ker(fromAprime)) ∩ D(f')` comes from `Spec(A)` and therefore lands in `U'`
    -- by compatibility, contradicting membership in the closed complement `V(J) = U'ᶜ`.
    rw [Set.eq_empty_iff_forall_notMem]
    intro q hq
    have hqzero :
        q ∈ PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A') := hq.1
    have hqbasic : q ∈ PrimeSpectrum.basicOpen f' := hq.2
    rw [PrimeSpectrum.mem_zeroLocus] at hqzero
    have hqker : RingHom.ker S.fromAprime ≤ q.asIdeal :=
      le_trans (show RingHom.ker S.fromAprime ≤ RingHom.ker S.fromAprime ⊔ J from le_sup_left)
        hqzero
    have hqJ : J ≤ q.asIdeal :=
      le_trans (show J ≤ RingHom.ker S.fromAprime ⊔ J from le_sup_right) hqzero
    have hqrange : q ∈ Set.range (PrimeSpectrum.comap S.fromAprime) := by
      rw [range_comap_of_surjective (R := A') (S := A) S.fromAprime S.fromAprime_surjective]
      exact (PrimeSpectrum.mem_zeroLocus q (RingHom.ker S.fromAprime : Set A')).2 hqker
    rcases hqrange with ⟨a, rfl⟩
    have haBasic : PrimeSpectrum.comap S.toA a ∈ PrimeSpectrum.basicOpen g := by
      -- The equation `fromAprime f' = toA g` transports the `D(f')` condition to the left leg.
      change S.toA g ∉ a.asIdeal
      simpa [PrimeSpectrum.mem_basicOpen, hf'] using hqbasic
    have haV : PrimeSpectrum.comap S.toA a ∈ V := hgV haBasic
    have haU' : PrimeSpectrum.comap S.fromAprime a ∈ U' := by
      -- Compatibility of the two opens sends the corresponding left point back into `U'`.
      have ha : a ∈ S.specToB ⁻¹' V := haV
      rw [hcompat] at ha
      exact ha
    have hqCompl : PrimeSpectrum.comap S.fromAprime a ∈ U'ᶜ := by
      rw [hJ]
      exact (PrimeSpectrum.mem_zeroLocus _ (J : Set A')).2 hqJ
    exact hqCompl haU'
  have hsubset :
      PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A') ⊆
        PrimeSpectrum.zeroLocus ({f'} : Set A') := by
    -- Empty intersection with `D(f')` means every prime above `ker(fromAprime) ⊔ J` contains `f'`.
    intro q hq
    by_contra hqf
    have hqbasic : q ∈ PrimeSpectrum.basicOpen f' := by
      simpa [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] using hqf
    have hqinter : q ∈ PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A') ∩
        (PrimeSpectrum.basicOpen f' : Set (PrimeSpectrum A')) := ⟨hq, hqbasic⟩
    rw [hdisj] at hqinter
    simpa using hqinter
  have hfRad : f' ∈ (RingHom.ker S.fromAprime ⊔ J).radical := by
    -- Translate the topological containment into the radical inclusion `f' ∈ √(ker ⊔ J)`.
    have hsubsetSpan :
        PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A') ⊆
          PrimeSpectrum.zeroLocus (Ideal.span ({f'} : Set A') : Set A') := by
      simpa [PrimeSpectrum.zeroLocus_span] using hsubset
    have hsubsetVan :
        Ideal.span ({f'} : Set A') ≤
          PrimeSpectrum.vanishingIdeal
            (PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A')) :=
      (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal _ _).1 hsubsetSpan
    have hfVan :
        f' ∈ PrimeSpectrum.vanishingIdeal
          (PrimeSpectrum.zeroLocus ((RingHom.ker S.fromAprime ⊔ J : Ideal A') : Set A')) :=
      hsubsetVan (Ideal.subset_span (by simp))
    rwa [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical] at hfVan
  rw [Ideal.mem_radical_iff] at hfRad
  obtain ⟨n, hn⟩ := hfRad
  rcases Submodule.mem_sup.mp hn with ⟨k, hkKer, a', ha'J, hsum⟩
  refine ⟨n, a', ?_, ?_⟩
  · -- Applying `fromAprime` to the cleared relation kills the kernel part and yields the target
    -- power of `toA g`.
    have hk0 : S.fromAprime k = 0 := by
      simpa [RingHom.mem_ker] using hkKer
    have hmap := congrArg S.fromAprime hsum
    simpa [hk0, hf', RingHom.map_pow] using hmap
  · -- Membership `a' ∈ J` forces any point of `D(a' * f')` to avoid `V(J) = U'ᶜ`.
    intro q hq
    by_contra hqU
    have hqCompl : q ∈ U'ᶜ := by
      simpa using hqU
    have hqzero : q ∈ PrimeSpectrum.zeroLocus (J : Set A') := by
      simpa [hJ] using hqCompl
    have hqJ : J ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus q (J : Set A')).1 hqzero
    have haMem : a' ∈ q.asIdeal := hqJ ha'J
    have hmulMem : a' * f' ∈ q.asIdeal := q.asIdeal.mul_mem_right _ haMem
    have hqNot : a' * f' ∉ q.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hq
    exact hqNot hmulMem

/-- Helper for Lemma 15.6.2: every left-hand point of a compatible open pair has an ambient open
neighborhood in `Spec(B')` contained in the union of the two leg-images. -/
lemma left_image_neighborhood_of_compatible_opens
    {V : Set (PrimeSpectrum B)} {U' : Set (PrimeSpectrum A')}
    (hV : IsOpen V) (hU' : IsOpen U')
    (hcompat : S.specToB ⁻¹' V = S.specToAprime ⁻¹' U')
    {p : PrimeSpectrum B} (hpV : p ∈ V) :
    ∃ W : Set (PrimeSpectrum S.Bprime),
      IsOpen W ∧ PrimeSpectrum.comap S.bprimeToB p ∈ W ∧
        W ⊆ Set.image (PrimeSpectrum.comap S.bprimeToB) V ∪
          Set.image (PrimeSpectrum.comap S.bprimeToAprime) U' := by
  have hpNhds : V ∈ nhds p := hV.mem_nhds hpV
  rcases (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 hpNhds with
    ⟨T, hTbasic, hpT, hTsub⟩
  rcases hTbasic with ⟨g, rfl⟩
  obtain ⟨f', hf'⟩ := S.fromAprime_surjective (S.toA g)
  obtain ⟨n, a', ha', haU'⟩ :=
    S.exists_right_basicOpen_subset_of_compatible_left_basicOpen hU' hcompat hTsub hf'
  have hhcompat : S.toA (g ^ (n + 1)) = S.fromAprime (a' * f') := by
    rw [RingHom.map_mul, hf', ha', RingHom.map_pow]
    ring
  obtain ⟨h', hh'B, hh'A⟩ := S.exists_bprime_of_compatible_pair hhcompat
  refine ⟨PrimeSpectrum.basicOpen h', isOpen_basicOpen, ?_, ?_⟩
  · -- The chosen basic-open on `Spec(B')` still contains the original left-hand point.
    have hpNot : g ∉ p.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hpT
    have hpNotPow : g ^ (n + 1) ∉ p.asIdeal := by
      intro hpow
      exact hpNot (p.2.mem_of_pow_mem _ hpow)
    simpa [PrimeSpectrum.mem_basicOpen, hh'B] using hpNotPow
  · intro x hx
    rcases S.closed_locus_or_mem_kernel_basicOpen x with hclosed | ⟨u, hu, hux⟩
    · -- Closed-locus points already come from the left, and `h'` forces them to stay in `D(g)`.
      rw [← S.mem_range_specBToBprime_iff x] at hclosed
      rcases hclosed with ⟨r, rfl⟩
      left
      refine ⟨r, ?_, rfl⟩
      have hrNotPow : g ^ (n + 1) ∉ r.asIdeal := by
        simpa [PrimeSpectrum.mem_basicOpen, hh'B] using hx
      have hrNot : g ∉ r.asIdeal := by
        intro hg
        exact hrNotPow <|
          (Ideal.pow_le_self (I := r.asIdeal) (Nat.succ_ne_zero n))
            (Ideal.pow_mem_pow hg (n + 1))
      have hrBasic : r ∈ PrimeSpectrum.basicOpen g := by
        simpa [PrimeSpectrum.mem_basicOpen] using hrNot
      exact hTsub hrBasic
    · -- Off the closed locus, multiply the kernel witness by `h'` and move to the right chart.
      have huNot : u ∉ x.asIdeal := by
        simpa [PrimeSpectrum.mem_basicOpen] using hux
      have hhNot : h' ∉ x.asIdeal := by
        simpa [PrimeSpectrum.mem_basicOpen] using hx
      have hxMul : x ∈ PrimeSpectrum.basicOpen (u * h') := by
        change u * h' ∉ x.asIdeal
        intro hMul
        rcases x.2.mem_or_mem hMul with huMem | hhMem
        · exact huNot huMem
        · exact hhNot hhMem
      have huMul : S.bprimeToB (u * h') = 0 := by
        simp [hu]
      have hxImage :
          x ∈ Set.image (PrimeSpectrum.comap S.bprimeToAprime)
            (PrimeSpectrum.basicOpen (S.bprimeToAprime (u * h')) : Set (PrimeSpectrum A')) := by
        rw [S.image_specAprimeToBprime_basicOpen_eq (u * h') huMul]
        exact hxMul
      rcases hxImage with ⟨q', hqBasic, rfl⟩
      right
      refine ⟨q', ?_, rfl⟩
      have hqNotMul : S.bprimeToAprime (u * h') ∉ q'.asIdeal := by
        simpa [PrimeSpectrum.mem_basicOpen] using hqBasic
      have hqNotRight : a' * f' ∉ q'.asIdeal := by
        intro hmem
        apply hqNotMul
        have hmulMem : S.bprimeToAprime u * (a' * f') ∈ q'.asIdeal :=
          Ideal.mul_mem_left _ _ hmem
        simpa [RingHom.map_mul, hh'A] using hmulMem
      have hqRight : q' ∈ PrimeSpectrum.basicOpen (a' * f') := by
        simpa [PrimeSpectrum.mem_basicOpen] using hqNotRight
      exact haU' hqRight

/-- Helper for Lemma 15.6.2: once the left-hand neighborhood construction is available, the image
of a compatible pair of opens is open in `Spec(B')`. -/
lemma compatible_opens_image_isOpen
    {V : Set (PrimeSpectrum B)} {U' : Set (PrimeSpectrum A')}
    (hV : IsOpen V) (hU' : IsOpen U')
    (hcompat : S.specToB ⁻¹' V = S.specToAprime ⁻¹' U') :
    IsOpen
      (Set.image (PrimeSpectrum.comap S.bprimeToB) V ∪
        Set.image (PrimeSpectrum.comap S.bprimeToAprime) U') := by
  refine isOpen_iff_mem_nhds.2 ?_
  intro x hx
  rcases hx with ⟨p, hpV, rfl⟩ | ⟨q', hqU', rfl⟩
  · obtain ⟨W, hWopen, hpW, hWsub⟩ :=
      S.left_image_neighborhood_of_compatible_opens hV hU' hcompat hpV
    refine Filter.mem_of_superset (hWopen.mem_nhds hpW) ?_
    intro y hy
    exact hWsub hy
  · by_cases hclosed :
        RingHom.ker S.bprimeToB ≤ (PrimeSpectrum.comap S.bprimeToAprime q').asIdeal
    · -- Closed-locus points from the right already have a left representative in the compatible
      -- open set, so the same left-hand neighborhood argument applies.
      obtain ⟨p, hpV, hpEq⟩ :=
        S.exists_left_preimage_of_compatible_opens_of_right_mem_closed_locus hcompat hqU' hclosed
      obtain ⟨W, hWopen, hpW, hWsub⟩ :=
        S.left_image_neighborhood_of_compatible_opens hV hU' hcompat hpV
      refine Filter.mem_of_superset (hWopen.mem_nhds (hpEq ▸ hpW)) ?_
      intro y hy
      exact hWsub hy
    · have hnot : ¬ RingHom.ker S.fromAprime ≤ q'.asIdeal := by
        intro hker
        have hmem :
            q' ∈ PrimeSpectrum.zeroLocus (RingHom.ker S.fromAprime : Set A') := by
          rw [PrimeSpectrum.mem_zeroLocus]
          exact hker
        have hmem' :
            q' ∈ (PrimeSpectrum.comap S.bprimeToAprime) ⁻¹'
              PrimeSpectrum.zeroLocus (RingHom.ker S.bprimeToB : Set S.Bprime) := by
          rw [S.preimage_specAprimeToBprime_zeroLocus_eq_zeroLocus]
          exact hmem
        exact hclosed hmem'
      obtain ⟨W, hWopen, hqW, hWsub⟩ := S.right_image_neighborhood_of_open hU' hqU' hnot
      refine Filter.mem_of_superset (hWopen.mem_nhds hqW) ?_
      intro y hy
      exact Or.inr (hWsub hy)

/-- Helper for Lemma 15.6.2: the descended pushout map is open.

This is the remaining source-faithful locality step: combine the closed-locus image of `Spec(B)`
with the kernel basic-open charts coming from `Spec(A')`. -/
lemma pushoutToSpecBprime_isOpenMap :
    IsOpenMap S.pushoutToSpecBprime := by
  intro U hU
  let V : Set (PrimeSpectrum B) := (pushout.inl S.specToB S.specToAprime) ⁻¹' U
  let U' : Set (PrimeSpectrum A') := (pushout.inr S.specToB S.specToAprime) ⁻¹' U
  have hlegs : IsOpen V ∧ IsOpen U' := by
    simpa [V, U'] using (S.pushout_isOpen_iff_on_legs U).1 hU
  have hcompat : S.specToB ⁻¹' V = S.specToAprime ⁻¹' U' := by
    ext a
    have hglue :=
      congrArg
        (fun f : TopCat.of (PrimeSpectrum A) ⟶ pushout S.specToB S.specToAprime => f a)
        (pushout.condition (f := S.specToB) (g := S.specToAprime))
    have hglue' :
        (pushout.inl S.specToB S.specToAprime) (S.specToB a) =
          (pushout.inr S.specToB S.specToAprime) (S.specToAprime a) := by
      simpa using hglue
    constructor
    · intro ha
      change (pushout.inl S.specToB S.specToAprime (S.specToB a)) ∈ U at ha
      change (pushout.inr S.specToB S.specToAprime (S.specToAprime a)) ∈ U
      exact hglue' ▸ ha
    · intro ha
      change (pushout.inr S.specToB S.specToAprime (S.specToAprime a)) ∈ U at ha
      change (pushout.inl S.specToB S.specToAprime (S.specToB a)) ∈ U
      exact hglue'.symm ▸ ha
  -- Rewrite the pushout image as the image of a compatible pair of opens on the two legs.
  rw [S.pushoutToSpecBprime_image_eq_leg_images U]
  simpa [V, U'] using S.compatible_opens_image_isOpen hlegs.1 hlegs.2 hcompat

end SurjectiveRingPullbackSituation

-- Proof sketch: let `B'` be the categorical pullback of `B → A ← A'`. The two projection maps
-- `B' → B` and `B' → A'` induce a cocone `Spec(B) ← Spec(A) → Spec(A') ⟶ Spec(B')`. The
-- textbook proof shows that the induced map from the topological pushout to `Spec(B')` is
-- bijective, separating primes according to whether they contain `ker(A' → A)`, and then proves
-- openness of this map by the localization argument using Lemma `15.5.3`.
/-- Lemma 15.6.2: in a surjective ring pullback situation, the prime spectrum of the fibre product
ring `B ×_A A'` is the pushout of `Spec(B) ← Spec(A) → Spec(A')` in the category of topological
spaces. -/
@[stacks 0B7J]
theorem spec_pullback_of_surjective_isPushout
    (S : SurjectiveRingPullbackSituation B A A') :
    IsPushout S.specToB S.specToAprime S.specBToBprime S.specAprimeToBprime := by
  -- We first descend the commuting cocone to the canonical map from the topological pushout.
  let φ : pushout S.specToB S.specToAprime ⟶ S.specBprime := S.pushoutToSpecBprime
  have hφ_inl : pushout.inl S.specToB S.specToAprime ≫ φ = S.specBToBprime :=
    S.pushoutToSpecBprime_inl
  have hφ_inr : pushout.inr S.specToB S.specToAprime ≫ φ = S.specAprimeToBprime :=
    S.pushoutToSpecBprime_inr
  -- Route correction: the pushout-side subset formulas are now used only to prove bijectivity of
  -- `φ`; the remaining source-faithful blocker is the openness step on the target-side cover.
  have hbij : Function.Bijective φ := S.pushoutToSpecBprime_bijective
  have hopen : IsOpenMap φ := S.pushoutToSpecBprime_isOpenMap
  have hφIso : IsIso φ := TopCat.isIso_of_bijective_of_isOpenMap φ hbij hopen
  let c : PushoutCocone S.specToB S.specToAprime :=
    PushoutCocone.mk S.specBToBprime S.specAprimeToBprime (S.spec_square_commutes)
  have hdesc : (pushoutIsPushout S.specToB S.specToAprime).desc c = φ := by
    -- Both descended maps agree on the two pushout legs, so uniqueness identifies them.
    refine (IsPushout.of_hasPushout S.specToB S.specToAprime).hom_ext ?_ ?_
    · calc
        pushout.inl S.specToB S.specToAprime ≫ (pushoutIsPushout S.specToB S.specToAprime).desc c
            = S.specBToBprime := by
              simpa [c] using
                (pushout.inl_desc S.specBToBprime S.specAprimeToBprime (S.spec_square_commutes))
        _ = pushout.inl S.specToB S.specToAprime ≫ φ := hφ_inl.symm
    · calc
        pushout.inr S.specToB S.specToAprime ≫ (pushoutIsPushout S.specToB S.specToAprime).desc c
            = S.specAprimeToBprime := by
              simpa [c] using
                (pushout.inr_desc S.specBToBprime S.specAprimeToBprime (S.spec_square_commutes))
        _ = pushout.inr S.specToB S.specToAprime ≫ φ := hφ_inr.symm
  letI : IsIso ((pushoutIsPushout S.specToB S.specToAprime).desc c) := by
    simpa [hdesc] using hφIso
  -- Transport the standard pushout cocone across the isomorphism from its point to `Spec(B')`.
  exact IsPushout.of_isColimit (c := c) <|
    IsColimit.ofPointIso (pushoutIsPushout S.specToB S.specToAprime)

end
