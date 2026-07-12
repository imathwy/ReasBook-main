import Mathlib
import StacksProject_2024.Chap10.Lemma_10_137_2
import StacksProject_2024.Chap10.Lemma_10_137_12
import StacksProject_2024.Chap16.Definition_16_2_3
import StacksProject_2024.Chap16.Lemma_16_6_1
import StacksProject_2024.Chap16.Lemma_16_7_2
import StacksProject_2024.Chap16.Situation_16_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y z

namespace Algebra

open scoped SingularIdealNotation

section

variable {R : Type u} {A : Type v} {Cbar : Type w} {Λ : Type x}
variable [CommRing R] [CommRing A] [CommRing Cbar] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

variable (π : R)

local notation "I4" => Ideal.span ({π ^ 4} : Set R)
local notation "I8" => Ideal.span ({π ^ 8} : Set R)
local notation "I4A" => Ideal.map (algebraMap R A) I4
local notation "I8A" => Ideal.map (algebraMap R A) I8
local notation "I8Λ" => Ideal.map (algebraMap R Λ) I8
local notation "R4" => R ⧸ I4
local notation "R8" => R ⧸ I8
local notation "A4" => A ⧸ I4A
local notation "A8" => A ⧸ I8A
local notation "Λ4" => Λ ⧸ Ideal.map (algebraMap R Λ) I4
local notation "Λ8" => Λ ⧸ I8Λ
local notation "AnnR[" x "]" => Ideal.torsionOf R R x
local notation "AnnΛ[" x "]" => Ideal.torsionOf Λ Λ x

/-
Domain-style sampling for Lemma 16.7.3:
- primary domain: commutative algebra of finitely presented factorizations, singular ideals, and
  reduction modulo `π⁸` under smoothness after inverting `π`;
- sampled owner declarations:
  `Ideal.quotientMapₐ`,
  `Ideal.quotient_map_comp_mkₐ`,
  `piPowFourQuotientMap`,
  `RingHom.singularIdealIn`,
  `Algebra.IsStrictlyStandard`,
  `Smooth`;
- best owner abstraction: this item is a source-facing existence theorem, but its bridge layer
  should reuse the canonical quotient-map owner `Ideal.quotientMapₐ`, packaged through the chapter
  bridge pattern `piPowEightQuotientMap`, and the chapter owner `g.singularIdealIn R` instead of
  introducing parallel local wrappers;
- primitive data: the map `fA : A →ₐ[R] Λ`, the mod-`π⁸` factorization
  `A / π⁸A → C̄ → Λ / π⁸Λ`, the annihilator equalities, and strict standardness of `π` in `A`;
- derived API: the induced quotient comparison map `piPowEightQuotientMap π fA`, the reduced image of
  `g.singularIdealIn R` in `Λ / π⁸Λ`, and the smoothness/singular-ideal control properties of the
  constructed factorization.

Source/core/bridge triage:
- source-facing: the existence theorem below;
- core/canonical: `Ideal.quotientMapₐ`, `Ideal.quotient_map_comp_mkₐ`, `RingHom.singularIdealIn`,
  `IsStrictlyStandard`, and `Smooth`;
- bridge/view: `piPowEightQuotientMap π fA`, the mod-`π⁸` factorization compatibility equation,
  and the quotient image of `g.singularIdealIn R`.
-/

private theorem isLocalizationAway_ofId_image {B : Type y} [CommRing B] [Algebra R B] :
    IsLocalization.Away ((Algebra.ofId R B) π) (Localization.Away (algebraMap R B π)) := by
  simpa using
    (inferInstance : IsLocalization.Away (algebraMap R B π) (Localization.Away (algebraMap R B π)))

local instance {B : Type y} [CommRing B] [Algebra R B] :
    IsLocalization.Away ((Algebra.ofId R B) π) (Localization.Away (algebraMap R B π)) :=
  isLocalizationAway_ofId_image π

noncomputable local instance {B : Type y} [CommRing B] [Algebra R B] :
    Algebra (Localization.Away π) (Localization.Away (algebraMap R B π)) :=
  (IsLocalization.Away.mapₐ (Localization.Away π)
    (Localization.Away (algebraMap R B π))
    (Algebra.ofId R B) π).toAlgebra

/-- Helper for Lemma 16.7.3: the principal ideal `(π⁸)` is contained in `(π⁴)`. -/
private theorem piPowEight_le_piPowFour :
    I8 ≤ I4 := by
  -- The generator `π⁸` is just `π⁴ * π⁴`, so it already lies in `(π⁴)`.
  rw [Ideal.span_singleton_le_iff_mem]
  rw [show π ^ 8 = π ^ 4 * π ^ 4 by ring_nf]
  exact Ideal.mul_mem_left I4 (π ^ 4) (Ideal.mem_span_singleton_self (π ^ 4))

/-- Helper for Lemma 16.7.3: the quotient base required by Lemma `16.6.1` at `π⁴` is exactly the
current quotient by `π⁸`. -/
private theorem span_piPowFour_sq_eq_piPowEight :
    Ideal.span ({(π ^ 4) ^ 2} : Set R) = I8 := by
  -- This freezes the one non-definitional ideal identity needed for the planned transport.
  have hpow : (π ^ 4) ^ 2 = π ^ 8 := by ring
  change Ideal.span ({(π ^ 4) ^ 2} : Set R) = Ideal.span ({π ^ 8} : Set R)
  rw [hpow]

/-- Helper for Lemma 16.7.3: the same `((π⁴)² = π⁸)` identification after mapping into `Λ`. -/
private theorem map_span_piPowFour_sq_eq_piPowEight :
    Ideal.map (algebraMap R Λ) (Ideal.span ({(π ^ 4) ^ 2} : Set R)) = I8Λ := by
  -- The mapped quotient ideal is transported by the same principal-ideal identity.
  rw [span_piPowFour_sq_eq_piPowEight (R := R) (π := π)]

/-- Helper for Lemma 16.7.3: once `Ann(x) = Ann(x²)`, every positive power of `x` has the same
annihilator as its successor power. -/
private theorem torsionOf_pow_eq_succ_of_square_step
    {S : Type y} [CommRing S] (x : S)
    (hAnn : Ideal.torsionOf S S x = Ideal.torsionOf S S (x ^ 2)) :
    ∀ n : ℕ, n ≠ 0 →
      Ideal.torsionOf S S (x ^ n) = Ideal.torsionOf S S (x ^ (n + 1))
  | 0, hn => (hn rfl).elim
  | n + 1, _ => by
      ext y
      constructor
      · intro hy
        rw [Ideal.mem_torsionOf_iff] at hy ⊢
        simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t ↦ t * x) hy
      · intro hy
        rw [Ideal.mem_torsionOf_iff] at hy ⊢
        have hy' : y * x ^ n ∈ Ideal.torsionOf S S (x ^ 2) := by
          rw [Ideal.mem_torsionOf_iff]
          simpa [pow_two, pow_succ', mul_assoc, mul_left_comm, mul_comm] using hy
        have hy'' : y * x ^ n ∈ Ideal.torsionOf S S x := by
          simpa [hAnn] using hy'
        rw [Ideal.mem_torsionOf_iff] at hy''
        simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hy''

/-- Helper for Lemma 16.7.3: the square-step stabilization `Ann(x) = Ann(x²)` propagates to the
comparison `Ann(x⁴) = Ann(x⁸)`. -/
private theorem torsionOf_powFour_eq_powEight_of_square_step
    {S : Type y} [CommRing S] (x : S)
    (hAnn : Ideal.torsionOf S S x = Ideal.torsionOf S S (x ^ 2)) :
    Ideal.torsionOf S S (x ^ 4) = Ideal.torsionOf S S ((x ^ 4) ^ 2) := by
  have hAnn_pow :
      ∀ n : ℕ, n ≠ 0 →
        Ideal.torsionOf S S (x ^ n) = Ideal.torsionOf S S (x ^ (n + 1)) :=
    torsionOf_pow_eq_succ_of_square_step (S := S) x hAnn
  calc
    Ideal.torsionOf S S (x ^ 4) = Ideal.torsionOf S S (x ^ 5) := hAnn_pow 4 (by decide)
    _ = Ideal.torsionOf S S (x ^ 6) := hAnn_pow 5 (by decide)
    _ = Ideal.torsionOf S S (x ^ 7) := hAnn_pow 6 (by decide)
    _ = Ideal.torsionOf S S (x ^ 8) := hAnn_pow 7 (by decide)
    _ = Ideal.torsionOf S S ((x ^ 4) ^ 2) := by
      congr 1
      ring

/-- The ideal generated by `π⁸` maps into the corresponding quotient ideal along any `R`-algebra
map. -/
-- Proof sketch: the generator `π⁸` of the source ideal maps to the generator `π⁸` of the target
-- ideal, so every element of `(π⁸)S` lands in the preimage of `(π⁸)T`.
private theorem map_piPowEight_le_comap_map_piPowEight
    {S : Type y} {T : Type z} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) :
    Ideal.map (algebraMap R S) I8 ≤
      Ideal.comap f (Ideal.map (algebraMap R T) I8) := by
  -- This is the same quotient-map compatibility used in the `π⁴` version, with `π⁸` in place of
  -- `π⁴`.
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap R S) I8 ≤
        Ideal.comap (f : S →+* T) (Ideal.map (f : S →+* T) (Ideal.map (algebraMap R S) I8)) from
      Ideal.le_comap_map)

/-- Helper for Lemma 16.7.3: mapping the inclusion `(π⁸) ⊆ (π⁴)` into any `R`-algebra produces
the quotient step from mod `π⁸` to mod `π⁴`. -/
private theorem map_piPowEight_le_map_piPowFour
    {S : Type y} [CommRing S] [Algebra R S] :
    Ideal.map (algebraMap R S) I8 ≤ Ideal.map (algebraMap R S) I4 := by
  -- Ideal maps preserve the principal-ideal containment already proved over `R`.
  exact Ideal.map_mono (piPowEight_le_piPowFour (R := R) (π := π))

/-- Helper for Lemma 16.7.3: if an element lies in the singular ideal, then localizing away from
it is smooth. -/
private theorem smoothAway_of_memSingularIdeal
    {S : Type y} [CommRing S] [Algebra R S] [FinitePresentation R S] {s : S}
    (hs : s ∈ H[S⁄R]) :
    Smooth R (Localization.Away s) := by
  -- The basic open cut out by `s` avoids the nonsmooth locus because `s` vanishes there.
  rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  intro p hp
  have hpzero : p ∉ PrimeSpectrum.zeroLocus (H[S⁄R]) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun hHs ↦ hp (hHs hs)
  simpa [Algebra.zeroLocus_singularIdeal_eq_compl_smoothLocus] using hpzero

/-- Helper for Lemma 16.7.3: smoothness after inverting `π⁴` forces the image of `(π⁴)` to lie in
the singular ideal. -/
private theorem mapPiPowFourIdeal_le_singularIdeal_of_smoothAway
    {S : Type y} [CommRing S] [Algebra R S] [FinitePresentation R S]
    (hSmooth : Smooth (Localization.Away (π ^ 4))
      (Localization.Away (algebraMap R S (π ^ 4)))) :
    Ideal.map (algebraMap R S) I4 ≤ H[S⁄R] := by
  -- The basic open cut out by `π⁴` lies in the smooth locus, so any nonsmooth prime must contain
  -- the image of `(π⁴)`.
  have hBasic :
      PrimeSpectrum.basicOpen (algebraMap R S (π ^ 4)) ⊆ Algebra.smoothLocus R S :=
    (Algebra.basicOpen_subset_smoothLocus_iff_smooth
      (R := R) (A := S) (f := algebraMap R S (π ^ 4))).mp hSmooth
  have hsubset :
      PrimeSpectrum.zeroLocus (H[S⁄R] : Set S) ⊆
        PrimeSpectrum.zeroLocus (Ideal.map (algebraMap R S) I4 : Set S) := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus]
    by_contra hI4
    have hpi4 : algebraMap R S (π ^ 4) ∉ q.asIdeal := by
      intro hmem
      apply hI4
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have hqSmooth : q ∈ Algebra.smoothLocus R S := hBasic hpi4
    have hqNotSmooth : q ∉ Algebra.smoothLocus R S := by
      simpa [Algebra.zeroLocus_singularIdeal_eq_compl_smoothLocus] using hq
    exact hqNotSmooth hqSmooth
  have hmapLeVan :
      Ideal.map (algebraMap R S) I4 ≤
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (H[S⁄R] : Set S)) :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal _ _).1 hsubset
  calc
    Ideal.map (algebraMap R S) I4 ≤
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (H[S⁄R] : Set S)) := hmapLeVan
    _ = (H[S⁄R]).radical := by rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
    _ = H[S⁄R] := by rw [(singularIdeal_isRadical (R := R) (A := S)).radical]

/-- The reduction modulo `π⁸` induced by an `R`-algebra map. -/
def piPowEightQuotientMap
    (f : A →ₐ[R] Λ) :
    A8 →ₐ[R8] Λ8 :=
  { toRingHom := Ideal.quotientMap _ f.toRingHom (map_piPowEight_le_comap_map_piPowEight π f)
    commutes' := by
      intro r
      refine Quotient.inductionOn' r ?_
      intro r
      change Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I8) (f (algebraMap R A r)) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I8) (algebraMap R Λ r)
      rw [f.commutes] }

/-- Helper for Lemma 16.7.3: further reducing the mod-`π⁸` quotient map modulo `π⁴` agrees with
the canonical mod-`π⁴` quotient map. -/
private theorem factorPiPowEightQuotientMap_eq_piPowFourQuotientMap
    (f : A →ₐ[R] Λ) :
    (Ideal.Quotient.factorₐ R
        (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π))).comp
        ((piPowEightQuotientMap (R := R) (A := A) (Λ := Λ) π f).restrictScalars R) =
      ((piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π f).restrictScalars R).comp
        (Ideal.Quotient.factorₐ R
          (map_piPowEight_le_map_piPowFour (R := R) (S := A) (π := π)) : A8 →ₐ[R] A4) := by
  -- Both composites send the class of `a : A` to the class of `f a` modulo `π⁴`.
  ext x
  refine Quotient.inductionOn' x ?_
  intro a
  change Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4) (f a) =
    Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4) (f a)
  rfl

/-- Helper for Lemma 16.7.3: an `R`-algebra map into `D / π⁴D` factors through `A / π⁴A` once the
image of `π⁴` is zero. -/
private theorem map_piPowFour_ideal_le_ker_of_generator_eq_zero
    {D : Type y} [CommRing D] [Algebra R D]
    (σ : A →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4))
    (hσ : σ (algebraMap R A (π ^ 4)) = 0) :
    I4A ≤ RingHom.ker σ := by
  -- The ideal `(π⁴)A` is principal, so it is enough to check that its generator maps to zero.
  rw [Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem]
  rw [Ideal.mem_comap, RingHom.mem_ker]
  exact hσ

/-- Helper for Lemma 16.7.3: descending a map `A → D / π⁴D` through the quotient `A / π⁴A`. -/
private noncomputable def descendToPiPowFourQuotient
    {D : Type y} [CommRing D] [Algebra R D]
    (σ : A →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4))
    (hσ : σ (algebraMap R A (π ^ 4)) = 0) :
    A4 →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4) :=
  Ideal.Quotient.liftₐ I4A σ
    (map_piPowFour_ideal_le_ker_of_generator_eq_zero
      (R := R) (A := A) (D := D) (π := π) σ hσ)

/-- Helper for Lemma 16.7.3: the descended `A / π⁴A → D / π⁴D` map agrees with the original map
on representatives. -/
private theorem descendToPiPowFourQuotient_comp_mk
    {D : Type y} [CommRing D] [Algebra R D]
    (σ : A →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4))
    (hσ : σ (algebraMap R A (π ^ 4)) = 0) :
    (descendToPiPowFourQuotient (R := R) (A := A) (D := D) (π := π) σ hσ).comp
        (Ideal.Quotient.mkₐ R I4A) =
      σ := by
  -- The quotient lift was defined by `Ideal.Quotient.liftₐ`, so precomposing with the quotient
  -- map returns the original comparison map.
  simpa [descendToPiPowFourQuotient] using
    (Ideal.Quotient.liftₐ_comp
      (R₁ := R)
      I4A
      σ
      (map_piPowFour_ideal_le_ker_of_generator_eq_zero
        (R := R) (A := A) (D := D) (π := π) σ hσ))

/-- Helper for Lemma 16.7.3: the same descent as `A / π⁴A → D / π⁴D`, now recorded over the
quotient base ring `R / π⁴R` expected by Lemma `16.7.2`. -/
private noncomputable def descendToPiPowFourQuotientOverR4
    {D : Type y} [CommRing D] [Algebra R D]
    (σ : A →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4))
    (hσ : σ (algebraMap R A (π ^ 4)) = 0) :
    A4 →ₐ[R4] (D ⧸ Ideal.map (algebraMap R D) I4) :=
  { toRingHom :=
      (descendToPiPowFourQuotient (R := R) (A := A) (D := D) (π := π) σ hσ).toRingHom
    commutes' := by
      -- Both sides are the class of the same scalar from `R` modulo `π⁴`.
      intro r
      refine Quotient.inductionOn' r ?_
      intro r
      change
        Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4) (σ (algebraMap R A r)) =
          Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4) (algebraMap R D r)
      rw [σ.commutes] }

/-- Helper for Lemma 16.7.3: once `lift = g ∘ fDB` and `H[D/R]` maps into `H[B/R]`, the mod-`π⁸`
image of the target-side singular ideal of `lift` is contained in the corresponding image for
`g`. -/
private theorem modPiPowEight_liftSingular_le_targetSingular
    {D : Type y} {B : Type z}
    [CommRing D] [CommRing B] [Algebra R D] [Algebra R B]
    (lift : D →ₐ[R] Λ) (fDB : D →ₐ[R] B) (g : B →ₐ[R] Λ)
    (hcomp : g.comp fDB = lift)
    (hSing : Ideal.map fDB.toRingHom (H[D⁄R]) ≤ H[B⁄R]) :
    Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R) ≤
      Ideal.map (Ideal.Quotient.mk I8Λ) (g.singularIdealIn R) := by
  -- Expand both target-side singular ideals once, and then compare the underlying mapped source
  -- singular ideals before taking radicals.
  rw [RingHom.singularIdealIn, RingHom.singularIdealIn]
  refine Ideal.map_mono ?_
  refine Ideal.radical_mono ?_
  rw [← hcomp, Ideal.map_map]
  exact (Ideal.map_mono hSing).trans Ideal.le_radical

/-- Helper for Lemma 16.7.3: if every prime of the target containing `J` pulls back to a
nonsmooth prime of the source, then the image of the source singular ideal is contained in `J`. -/
private theorem map_singularIdeal_le_of_nonsmooth_comap
    {S : Type y} {T : Type z}
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [FinitePresentation R S]
    (f : S →ₐ[R] T) (J : Ideal T) (hJrad : J.IsRadical)
    (hNonsmooth : ∀ q : PrimeSpectrum T, J ≤ q.asIdeal →
      ¬ SmoothAtPrime R S (PrimeSpectrum.comap f.toRingHom q)) :
    Ideal.map f.toRingHom (H[S⁄R]) ≤ J := by
  have hsubset :
      PrimeSpectrum.zeroLocus (J : Set T) ⊆
        PrimeSpectrum.zeroLocus (Ideal.map f.toRingHom (H[S⁄R]) : Set T) := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus]
    have hJq : J ≤ q.asIdeal := by
      simpa [PrimeSpectrum.mem_zeroLocus] using hq
    have hqNotSmooth : ¬ SmoothAtPrime R S (PrimeSpectrum.comap f.toRingHom q) :=
      hNonsmooth q hJq
    have hqNotIsSmooth : ¬ IsSmoothAt R (PrimeSpectrum.comap f.toRingHom q).asIdeal := by
      intro hqSmooth
      exact hqNotSmooth ((smoothAtPrime_iff_isSmoothAt
        (R := R) (S := S) (PrimeSpectrum.comap f.toRingHom q)).2 hqSmooth)
    have hqSource :
        H[S⁄R] ≤ (PrimeSpectrum.comap f.toRingHom q).asIdeal := by
      simpa [PrimeSpectrum.mem_zeroLocus, Algebra.zeroLocus_singularIdeal_eq_compl_smoothLocus,
        smoothLocus] using hqNotIsSmooth
    exact Ideal.map_le_iff_le_comap.mpr hqSource
  have hmapLeVan :
      Ideal.map f.toRingHom (H[S⁄R]) ≤
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (J : Set T)) :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal _ _).1 hsubset
  calc
    Ideal.map f.toRingHom (H[S⁄R]) ≤
        PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (J : Set T)) := hmapLeVan
    _ = J.radical := by rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
    _ = J := hJrad.radical

/-- Helper for Lemma 16.7.3: smoothness of `R → B_πB` upgrades to smoothness of
`R_π → B_πB`. -/
private theorem smoothAwayPi_of_smoothAwayImage
    {B : Type y} [CommRing B] [Algebra R B]
    (hSmooth : Smooth R (Localization.Away (algebraMap R B π))) :
    Smooth (Localization.Away π) (Localization.Away (algebraMap R B π)) := by
  letI : Smooth R (Localization.Away (algebraMap R B π)) := hSmooth
  have hUnit : IsUnit (algebraMap R (Localization.Away (algebraMap R B π)) π) := by
    change IsUnit (algebraMap B (Localization.Away (algebraMap R B π)) (algebraMap R B π))
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R B π)
  have hAwaySmooth :
      RingHom.Smooth
        (Localization.awayLift
          (algebraMap R (Localization.Away (algebraMap R B π))) π hUnit) :=
    Algebra.smooth_away_lift_of_isUnit
      (R := R) (S := Localization.Away (algebraMap R B π)) (f := π) hUnit
  have hAwayEq :
      Localization.awayLift
          (algebraMap R (Localization.Away (algebraMap R B π))) π hUnit =
        algebraMap (Localization.Away π) (Localization.Away (algebraMap R B π)) := by
    ext x
    simp [Localization.awayLift]
  rw [← hAwayEq] at hAwaySmooth
  exact hAwaySmooth.toAlgebra

/-- Helper for Lemma 16.7.3: postcomposing the mod-`π⁸` quotient map with the canonical reduction
to mod `π⁴` agrees with quotienting directly modulo `π⁴`. -/
private theorem factorPiPowEightToPiPowFour_comp_quotientMk :
    ((Ideal.Quotient.factorₐ R
          (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)) : Λ8 →ₐ[R] Λ4)).comp
        (Ideal.Quotient.mkₐ R I8Λ) =
      Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R Λ) I4) := by
  -- Both quotient maps send `x : Λ` to its class modulo `π⁴`.
  ext x
  rfl

/-- Helper for Lemma 16.7.3: the image of `(π⁴)` in `Λ` is contained in the lift singular ideal as
soon as `(π⁴)` maps into the singular ideal of the source algebra `D`. -/
private theorem map_piPowFourIdeal_le_liftSingularIdeal
    {D : Type y} [CommRing D] [Algebra R D]
    (lift : D →ₐ[R] Λ)
    (hI4IntoHD : Ideal.map (algebraMap R D) I4 ≤ H[D⁄R]) :
    Ideal.map (algebraMap R Λ) I4 ≤ lift.singularIdealIn R := by
  -- Push the source-side containment across `lift` and then expand the target singular ideal once.
  rw [RingHom.singularIdealIn]
  calc
    Ideal.map (algebraMap R Λ) I4 = Ideal.map lift.toRingHom (Ideal.map (algebraMap R D) I4) := by
      rw [Ideal.map_map]
      congr 1
      ext r
      simp [lift.commutes]
    _ ≤ Ideal.map lift.toRingHom (H[D⁄R]) := Ideal.map_mono hI4IntoHD
    _ ≤ (Ideal.map lift.toRingHom (H[D⁄R])).radical := Ideal.le_radical

/-- Helper for Lemma 16.7.3: the kernel of the reduction `Λ / π⁸Λ → Λ / π⁴Λ` is already contained
in the mod-`π⁸` image of the lift singular ideal once `(π⁴)` maps into that ideal. -/
private theorem ker_factorPiPowEightToPiPowFour_le_modPiPowEightLiftSingular
    {D : Type y} [CommRing D] [Algebra R D]
    (lift : D →ₐ[R] Λ)
    (hI4IntoHD : Ideal.map (algebraMap R D) I4 ≤ H[D⁄R]) :
    RingHom.ker
        ((Ideal.Quotient.factorₐ R
          (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)) : Λ8 →ₐ[R] Λ4).toRingHom) ≤
      Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R) := by
  intro x hx
  refine Quotient.inductionOn' x ?_
  intro x
  change Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4) x = 0 at hx
  have hxI4 : x ∈ Ideal.map (algebraMap R Λ) I4 :=
    Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hxSingular : x ∈ lift.singularIdealIn R :=
    (map_piPowFourIdeal_le_liftSingularIdeal
      (R := R) (Λ := Λ) (D := D) (π := π) lift hI4IntoHD) hxI4
  exact Ideal.mem_map_of_mem _ hxSingular

/-- Helper for Lemma 16.7.3: an element of `Λ / π⁸Λ` whose mod-`π⁴` image lies in the image of
the lift singular ideal already lies in the mod-`π⁸` image of that singular ideal. -/
private theorem mem_modPiPowEightLiftSingular_of_factor_mem
    {D : Type y} [CommRing D] [Algebra R D]
    (lift : D →ₐ[R] Λ)
    (hI4IntoHD : Ideal.map (algebraMap R D) I4 ≤ H[D⁄R])
    {x : Λ8}
    (hx :
      (Ideal.Quotient.factorₐ R
          (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)) : Λ8 →ₐ[R] Λ4) x ∈
        Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4)) (lift.singularIdealIn R)) :
    x ∈ Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R) := by
  let q84 : Λ8 →ₐ[R] Λ4 :=
    Ideal.Quotient.factorₐ R
      (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π))
  let J8 : Ideal Λ8 := Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R)
  have hMapJ8 :
      Ideal.map q84.toRingHom J8 =
        Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4)) (lift.singularIdealIn R) := by
    -- The two quotient routes agree on representatives from `Λ`.
    unfold J8 q84
    rw [Ideal.map_map]
    congr 1
    ext r
    exact congrArg (fun f : Λ →ₐ[R] Λ4 => f r)
      (factorPiPowEightToPiPowFour_comp_quotientMk (R := R) (Λ := Λ) (π := π))
  have hxMap : q84 x ∈ Ideal.map q84.toRingHom J8 := by
    simpa [hMapJ8]
      using hx
  rw [Ideal.mem_map_iff_of_surjective q84.toRingHom q84.surjective] at hxMap
  rcases hxMap with ⟨y, hyJ8, hxy⟩
  have hxyKer : x - y ∈ RingHom.ker q84.toRingHom := by
    rw [RingHom.mem_ker]
    simpa [map_sub, hxy]
  have hdiffJ8 :
      x - y ∈ J8 :=
    (ker_factorPiPowEightToPiPowFour_le_modPiPowEightLiftSingular
      (R := R) (Λ := Λ) (D := D) (π := π) lift hI4IntoHD) hxyKer
  have hxJ8 : x = (x - y) + y := by abel
  have hxInJ8 : x ∈ J8 := by
    rw [hxJ8]
    exact Ideal.add_mem J8 hdiffJ8 hyJ8
  simpa [J8] using hxInJ8

-- Proof sketch: apply Lemma `16.6.1` to the mod-`π⁸` factorization through `C̄` to obtain an
-- auxiliary finitely presented lift that is smooth after inverting `π` and on the smooth locus of
-- `C̄`. Then apply Lemma `16.7.2` to combine that lift with `A`, preserving finite presentation
-- and forcing the singular ideal of the auxiliary algebra to map into the singular ideal of the
-- new algebra `B`. Reducing modulo `π⁸` gives the stated containment in `Λ / π⁸Λ`.
/-- Lemma 16.7.3: let `R` be Noetherian, let `Λ` be an `R`-algebra, let `π ∈ R`, and assume
`Ann_R(π) = Ann_R(π²)` and `Ann_Λ(π) = Ann_Λ(π²)`. Let `A → Λ` be an `R`-algebra map with `A` of
finite presentation and assume the image of `π` is strictly standard in `A` over `R`. For a
factorization `A / π⁸A → C̄ → Λ / π⁸Λ` with `C̄` of finite presentation over `R / π⁸R`, there is
a factorization `A → B → Λ` with `B` of finite presentation such that `R_π → B_π` is smooth and
the image of `H_{\bar C/(R/π⁸R)}` in `Λ / π⁸Λ` is contained in the reduction modulo `π⁸` of
`√(H_{B/R}Λ)`. -/
theorem exists_finitePresentation_factorization_with_piPowEight_desingularization
    [IsNoetherianRing R] [FinitePresentation R A] [Algebra R8 Cbar]
    [FinitePresentation R8 Cbar]
    (fA : A →ₐ[R] Λ)
    (hAnnR : AnnR[π] = AnnR[π ^ 2])
    (hAnnΛ : AnnΛ[algebraMap R Λ π] = AnnΛ[algebraMap R Λ (π ^ 2)])
    (hπ : IsStrictlyStandard R (algebraMap R A π))
    (fbar : A8 →ₐ[R8] Cbar)
    (gbar : Cbar →ₐ[R8] Λ8)
    (hfactor : gbar.comp fbar = piPowEightQuotientMap π fA) :
    ∃ (B : Type (max u v w x)) (_ : CommRing B) (_ : Algebra R B) (_ : FinitePresentation R B)
      (fAB : A →ₐ[R] B) (g : B →ₐ[R] Λ),
      g.comp fAB = fA ∧
        Smooth (Localization.Away π) (Localization.Away (algebraMap R B π)) ∧
        Ideal.map gbar.toRingHom (H[Cbar⁄R8]) ≤
          Ideal.map (Ideal.Quotient.mk I8Λ) (g.singularIdealIn R) := by
  -- Route correction: the remaining obstruction is not the `16.7.2` assembly itself, but the
  -- transport that packages Lemma `16.6.1` at `π⁴` directly on the current `R / π⁸` surface.
  have hAnnR4 :
      Ideal.torsionOf R R (π ^ 4) = Ideal.torsionOf R R ((π ^ 4) ^ 2) :=
    torsionOf_powFour_eq_powEight_of_square_step (S := R) π hAnnR
  have hAnnΛ4 :
      Ideal.torsionOf Λ Λ ((algebraMap R Λ π) ^ 4) =
        Ideal.torsionOf Λ Λ (((algebraMap R Λ π) ^ 4) ^ 2) := by
    have hAnnΛsq :
        Ideal.torsionOf Λ Λ (algebraMap R Λ π) =
          Ideal.torsionOf Λ Λ ((algebraMap R Λ π) ^ 2) := by
      simpa [map_pow] using hAnnΛ
    simpa using
      torsionOf_powFour_eq_powEight_of_square_step
        (S := Λ) (algebraMap R Λ π) hAnnΛsq
  have hI8Base :
      Ideal.span ({(π ^ 4) ^ 2} : Set R) = I8 :=
    span_piPowFour_sq_eq_piPowEight (R := R) (π := π)
  have hI8Target :
      Ideal.map (algebraMap R Λ) (Ideal.span ({(π ^ 4) ^ 2} : Set R)) = I8Λ :=
    map_span_piPowFour_sq_eq_piPowEight (R := R) (Λ := Λ) (π := π)
  have hFactorMap :
      (Ideal.Quotient.factorₐ R
          (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π))).comp
          ((piPowEightQuotientMap (R := R) (A := A) (Λ := Λ) π fA).restrictScalars R) =
        ((piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π fA).restrictScalars R).comp
          (Ideal.Quotient.factorₐ R
          (map_piPowEight_le_map_piPowFour (R := R) (S := A) (π := π)) : A8 →ₐ[R] A4) :=
    factorPiPowEightQuotientMap_eq_piPowFourQuotientMap
      (R := R) (A := A) (Λ := Λ) (π := π) fA
  -- Package the entire `16.6.1` transport into one local datum so the rest of the theorem only
  -- sees the `π⁴`-level comparison map and the mod-`π⁸` singular-ideal control it needs.
  have hLiftComparison :
      ∃ (D : Type (max u w x)) (_ : CommRing D) (_ : Algebra R D) (_ : FinitePresentation R D)
        (lift : D →ₐ[R] Λ) (φ : A4 →ₐ[R4] (D ⧸ Ideal.map (algebraMap R D) I4)),
        (piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).comp φ =
            piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π fA ∧
          Smooth (Localization.Away (π ^ 4))
            (Localization.Away (algebraMap R D (π ^ 4))) ∧
          Ideal.map gbar.toRingHom (H[Cbar⁄R8]) ≤
            Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R) := by
    obtain ⟨D, hD, hAlgD, hfpD, lift, ψ, hψcompat, hSmoothD, hPrimewise, _⟩ := by
      -- First freeze the raw `16.6.1` output at parameter `π⁴`, rewritten directly into the
      -- current mod-`π⁸` notation.
      simpa [span_piPowFour_sq_eq_piPowEight (R := R) (π := π),
        map_span_piPowFour_sq_eq_piPowEight (R := R) (Λ := Λ) (π := π)] using
        (exists_finitePresentation_lift_with_smooth_mod_pi
          (R := R) (Λ := Λ) (Cbar := Cbar) (π := π ^ 4)
          (toLambda2 := gbar) hAnnR4 hAnnΛ4)
    letI : CommRing D := hD
    letI : Algebra R D := hAlgD
    letI : FinitePresentation R D := hfpD
    let σ : A →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4) :=
      (ψ.restrictScalars R).comp
        ((fbar.restrictScalars R).comp (Ideal.Quotient.mkₐ R I8A))
    have hσzero : σ (algebraMap R A (π ^ 4)) = 0 := by
      -- The descended comparison map kills `π⁴` because `π⁴` is zero in `D / π⁴D`.
      rw [σ.commutes]
      change Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4) (algebraMap R D (π ^ 4)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self (π ^ 4))
    let φ : A4 →ₐ[R4] (D ⧸ Ideal.map (algebraMap R D) I4) :=
      descendToPiPowFourQuotientOverR4
        (R := R) (A := A) (D := D) (π := π) σ hσzero
    have hφcompat :
        (piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).comp φ =
          piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π fA := by
      -- Compare both maps on representatives from `A`, using the transported `16.6.1`
      -- compatibility and the already-frozen `π⁸ → π⁴` factor map.
      ext x
      refine Quotient.inductionOn' x ?_
      intro a
      have hdesc :
          (descendToPiPowFourQuotient
              (R := R) (A := A) (D := D) (π := π) σ hσzero)
              (Ideal.Quotient.mk I4A a) = σ a := by
        exact congrArg (fun τ : A →ₐ[R] (D ⧸ Ideal.map (algebraMap R D) I4) => τ a)
          (descendToPiPowFourQuotient_comp_mk
            (R := R) (A := A) (D := D) (π := π) σ hσzero)
      have hψa :
          ((piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).restrictScalars R) (σ a) =
            (Ideal.Quotient.factorₐ R
                (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)))
              (gbar (fbar (Ideal.Quotient.mk I8A a))) := by
        exact congrArg (fun τ : Cbar →ₐ[R] Λ4 => τ (fbar (Ideal.Quotient.mk I8A a))) hψcompat
      have hfactora :
          gbar (fbar (Ideal.Quotient.mk I8A a)) =
            piPowEightQuotientMap (R := R) (A := A) (Λ := Λ) π fA (Ideal.Quotient.mk I8A a) := by
        exact congrArg (fun τ : A8 →ₐ[R8] Λ8 => τ (Ideal.Quotient.mk I8A a)) hfactor
      have hFactorMapa :
          (Ideal.Quotient.factorₐ R
                (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)))
              ((piPowEightQuotientMap (R := R) (A := A) (Λ := Λ) π fA)
                (Ideal.Quotient.mk I8A a)) =
            (piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π fA)
              ((Ideal.Quotient.factorₐ R
                  (map_piPowEight_le_map_piPowFour (R := R) (S := A) (π := π)) : A8 →ₐ[R] A4)
                (Ideal.Quotient.mk I8A a)) := by
        simpa [AlgHom.comp_apply]
          using congrArg (fun τ : A8 →ₐ[R] Λ4 => τ (Ideal.Quotient.mk I8A a)) hFactorMap
      calc
        (piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift)
            (φ (Ideal.Quotient.mk I4A a)) =
          (piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift) (σ a) := by
            simpa [φ] using congrArg
              (fun z ↦ (piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift) z) hdesc
        _ =
          (Ideal.Quotient.factorₐ R
              (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)))
            (gbar (fbar (Ideal.Quotient.mk I8A a))) := by
              simpa [σ, AlgHom.comp_apply] using hψa
        _ =
          (Ideal.Quotient.factorₐ R
              (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)))
            ((piPowEightQuotientMap (R := R) (A := A) (Λ := Λ) π fA)
              (Ideal.Quotient.mk I8A a)) := by
              rw [hfactora]
        _ =
          (piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π fA)
            ((Ideal.Quotient.factorₐ R
                (map_piPowEight_le_map_piPowFour (R := R) (S := A) (π := π)) : A8 →ₐ[R] A4)
              (Ideal.Quotient.mk I8A a)) := by
              exact hFactorMapa
        _ =
          (piPowFourQuotientMap (R := R) (A := A) (Λ := Λ) π fA) (Ideal.Quotient.mk I4A a) := by
            rfl
    have hI4IntoHD :
        Ideal.map (algebraMap R D) I4 ≤ H[D⁄R] :=
      mapPiPowFourIdeal_le_singularIdeal_of_smoothAway
        (R := R) (S := D) (π := π) hSmoothD
    have hSourceToLiftD4 :
        Ideal.map ψ.toRingHom (H[Cbar⁄R8]) ≤
          Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) (H[D⁄R]) := by
      -- A prime of `D / π⁴D` containing the image of `H_{D/R}` comes from a nonsmooth prime of
      -- `D`, so the contrapositive of the primewise clause from `16.6.1` forces the pullback
      -- prime on `C̄` to be nonsmooth.
      have hTargetRadical :
          (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) (H[D⁄R])).IsRadical := by
        simpa using
          (singularIdeal_isRadical (R := R) (A := D)).map
            (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4))
      refine map_singularIdeal_le_of_nonsmooth_comap
        (R := R8) (S := Cbar)
        (T := D ⧸ Ideal.map (algebraMap R D) I4)
        ψ
        (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) (H[D⁄R]))
        hTargetRadical ?_
      intro q hq hqSmooth
      have hqSmoothD :
          SmoothAtPrime R D
            (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) q) :=
        hPrimewise q hqSmooth
      have hqNotIsSmoothD :
          ¬ IsSmoothAt R
            (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) q).asIdeal := by
        intro hIsSmooth
        exact
          (smoothAtPrime_iff_isSmoothAt
            (R := R) (S := D)
            (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) q)).not.mpr
            hIsSmooth hqSmoothD
      have hqContainsSingular :
          H[D⁄R] ≤ (PrimeSpectrum.comap
            (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) q).asIdeal := by
        exact Ideal.map_le_iff_le_comap.mp hq
      have hqSmoothIdeal :
          ¬ H[D⁄R] ≤
            (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) q).asIdeal := by
        intro hSing
        have hqZero :
            PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) q ∈
              PrimeSpectrum.zeroLocus (H[D⁄R] : Set D) := by
          simpa [PrimeSpectrum.mem_zeroLocus] using hSing
        exact hqNotIsSmoothD <| by
          simpa [Algebra.zeroLocus_singularIdeal_eq_compl_smoothLocus, smoothLocus] using hqZero
      exact hqSmoothIdeal hqContainsSingular
    have hSourceToLiftΛ4 :
        Ideal.map
            (((Ideal.Quotient.factorₐ R
                (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π))).comp
                (gbar.restrictScalars R)).toRingHom)
            (H[Cbar⁄R8]) ≤
          Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4)) (lift.singularIdealIn R) := by
      -- Push the `D / π⁴D` containment forward to `Λ / π⁴Λ`.
      have hMapped :
          Ideal.map
              ((piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).toRingHom)
              (Ideal.map ψ.toRingHom (H[Cbar⁄R8])) ≤
            Ideal.map
              ((piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).toRingHom)
              (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) (H[D⁄R])) :=
        Ideal.map_mono hSourceToLiftD4
      calc
        Ideal.map
            (((Ideal.Quotient.factorₐ R
                (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π))).comp
                (gbar.restrictScalars R)).toRingHom)
            (H[Cbar⁄R8]) =
          Ideal.map
              ((piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).toRingHom)
              (Ideal.map ψ.toRingHom (H[Cbar⁄R8])) := by
                simpa [Ideal.map_map, hψcompat]
        _ ≤ Ideal.map
              ((piPowFourQuotientMap (R := R) (A := D) (Λ := Λ) π lift).toRingHom)
              (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R D) I4)) (H[D⁄R])) := hMapped
        _ = Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4))
              (Ideal.map lift.toRingHom (H[D⁄R])) := by
                simp [Ideal.map_map]
        _ ≤ Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4))
              (lift.singularIdealIn R) := by
                rw [RingHom.singularIdealIn]
                exact Ideal.map_mono Ideal.le_radical
    have hSourceToLift :
        Ideal.map gbar.toRingHom (H[Cbar⁄R8]) ≤
          Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R) := by
      -- An element whose mod-`π⁴` image lies in the lift singular ideal already lies in the
      -- mod-`π⁸` image, because the kernel of `Λ / π⁸Λ → Λ / π⁴Λ` is cut out by `(π⁴)` and
      -- `(π⁴)` already maps into the lift singular ideal.
      refine Ideal.map_le_iff_le_comap.mpr ?_
      intro c hc
      have hc4 :
          (Ideal.Quotient.factorₐ R
              (map_piPowEight_le_map_piPowFour (R := R) (S := Λ) (π := π)) : Λ8 →ₐ[R] Λ4)
              (gbar c) ∈
            Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R Λ) I4))
              (lift.singularIdealIn R) :=
        hSourceToLiftΛ4 (Ideal.mem_map_of_mem _ hc)
      exact mem_modPiPowEightLiftSingular_of_factor_mem
        (R := R) (Λ := Λ) (D := D) (π := π) lift hI4IntoHD hc4
    exact ⟨D, hD, hAlgD, hfpD, lift, φ, hφcompat, hSmoothD, hSourceToLift⟩
  rcases hLiftComparison with ⟨D, hD, hAlgD, hfpD, lift, φ, hφcompat, hSmoothD, hSourceToLift⟩
  letI : CommRing D := hD
  letI : Algebra R D := hAlgD
  letI : FinitePresentation R D := hfpD
  obtain ⟨B, hB, hAlgB, hfpB, fAB, fDB, g, hgA, hgD, hDBSingular, hBSingular⟩ :=
    exists_common_finitePresentation_factorization_with_singularIdeal_control
      (R := R) (A := A) (D := D) (Λ := Λ) (π := π)
      fA lift hAnnR hAnnΛ hπ ⟨φ, hφcompat⟩
  letI : CommRing B := hB
  letI : Algebra R B := hAlgB
  letI : FinitePresentation R B := hfpB
  have hLiftToTarget :
      Ideal.map (Ideal.Quotient.mk I8Λ) (lift.singularIdealIn R) ≤
        Ideal.map (Ideal.Quotient.mk I8Λ) (g.singularIdealIn R) :=
    modPiPowEight_liftSingular_le_targetSingular
      (R := R) (Λ := Λ) (π := π) lift fDB g hgD hBSingular
  have hTargetContainment :
      Ideal.map gbar.toRingHom (H[Cbar⁄R8]) ≤
        Ideal.map (Ideal.Quotient.mk I8Λ) (g.singularIdealIn R) :=
    hSourceToLift.trans hLiftToTarget
  have hI4IntoHD :
      Ideal.map (algebraMap R D) I4 ≤ H[D⁄R] :=
    mapPiPowFourIdeal_le_singularIdeal_of_smoothAway
      (R := R) (S := D) (π := π) hSmoothD
  have hMapI4 :
      Ideal.map fDB.toRingHom (Ideal.map (algebraMap R D) I4) =
        Ideal.map (algebraMap R B) I4 := by
    -- This is the scalar-compatibility rewrite needed to push `(π⁴)` from `D` to `B`.
    rw [Ideal.map_map]
    congr 1
    ext r
    simp [fDB.commutes]
  have hI4IntoHB :
      Ideal.map (algebraMap R B) I4 ≤ H[B⁄R] := by
    -- First map the `D`-containment into `B`, then use the singular-ideal containment from
    -- Lemma `16.7.2`.
    rw [← hMapI4]
    exact (Ideal.map_mono hI4IntoHD).trans hBSingular
  have hpiPowFourMem : algebraMap R B (π ^ 4) ∈ H[B⁄R] := by
    exact hI4IntoHB (Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp)))
  have hpiMem : algebraMap R B π ∈ H[B⁄R] := by
    -- Radicality turns membership of `(π_B)^4` into membership of `π_B`.
    have hpowMem : (algebraMap R B π) ^ 4 ∈ H[B⁄R] := by
      simpa [map_pow] using hpiPowFourMem
    have hrad :
        algebraMap R B π ∈ (H[B⁄R]).radical :=
      Ideal.mem_radical.mpr ⟨4, hpowMem⟩
    rwa [(singularIdeal_isRadical (R := R) (A := B)).radical] at hrad
  have hSmoothAwayImage :
      Smooth R (Localization.Away (algebraMap R B π)) :=
    smoothAway_of_memSingularIdeal (R := R) (S := B) hpiMem
  have hSmoothB :
      Smooth (Localization.Away π) (Localization.Away (algebraMap R B π)) := by
    -- The remaining localization step is the canonical `awayLift` upgrade from
    -- `R → B_πB` to `R_π → B_πB`.
    exact smoothAwayPi_of_smoothAwayImage (R := R) (B := B) (π := π) hSmoothAwayImage
  exact ⟨B, hB, hAlgB, hfpB, fAB, g, hgA, hSmoothB, hTargetContainment⟩

end

end Algebra
