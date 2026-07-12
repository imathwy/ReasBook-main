import StacksProject_2024.Chap15.Situation_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CommRingCat

noncomputable section

universe u

namespace SurjectiveRingPullbackSituation

variable {B R R' : Type u} [CommRing B] [CommRing R] [CommRing R']

/-- The canonical map `Spec(R') → Spec(B')` induced by the pullback projection `B' → R'`. -/
abbrev specAprimeToBprime
    (S : SurjectiveRingPullbackSituation B R R') :
    Spec (of R') ⟶ Spec S.Bprime :=
  TopCat.ofHom
    ⟨PrimeSpectrum.comap S.bprimeToAprime, PrimeSpectrum.continuous_comap S.bprimeToAprime⟩

/-- The localized comparison map `B[1 / g] → R[1 / s(g)]` attached to a surjective pullback
situation. -/
abbrev awayMap
    (S : SurjectiveRingPullbackSituation B R R')
    (g : B) :
    Localization.Away g →+* Localization.Away (S.toA g) :=
  Localization.awayMap S.toA g

/-- For an open subscheme `W' ⊆ Spec(R')`, the induced morphism `W' ⟶ Spec(B')` is obtained by
restricting `Spec(B' → R')`. -/
abbrev restrictSpecMap
    (S : SurjectiveRingPullbackSituation B R R')
    (W' : (Spec (of R')).Opens) :
    W' ⟶ Spec S.Bprime :=
  W'.ι ≫ S.specAprimeToBprime

-- Semantic recall: the Chapter 15 owner
-- `SurjectiveRingPullbackSituation.spec_pullback_of_surjective_isPushout` packages the spectrum
-- square attached to the cartesian ring diagram, and its proof uses the localization-away bridge
-- of Lemma `15.5.3` on basic opens. The present item keeps the source-facing open-immersion
-- conclusion, with only the thin scheme-side abbreviations `awayMap` and `restrictSpecMap`.

/-- Lemma 32.5.2: in a cartesian square `B → R ← R'` with fibre product ring `B'`, if an open
`W' ⊆ Spec(R')` is a finite union of basic opens `D(f_i)` such that each `f_i` comes from some
`g_i ∈ B` and the canonical localized map `B[1 / g_i] → R[1 / s(g_i)]` is bijective, then the
induced morphism `W' ⟶ Spec(B')` is an open immersion. -/
@[stacks 01Z9]
theorem isOpenImmersion_restrictSpecMap_of_basicOpenCover
    (S : SurjectiveRingPullbackSituation B R R')
    {n : ℕ}
    (W' : (Spec (of R')).Opens)
    (f : Fin n → R')
    (g : Fin n → B)
    (hW' : W' = ⨆ i, PrimeSpectrum.basicOpen (f i))
    (hfg : ∀ i, S.fromAprime (f i) = S.toA (g i))
    (hlocal : ∀ i, Function.Bijective (S.awayMap (g i))) :
    IsOpenImmersion (S.restrictSpecMap W') := sorry

end SurjectiveRingPullbackSituation
