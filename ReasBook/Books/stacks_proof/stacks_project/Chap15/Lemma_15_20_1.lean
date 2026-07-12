import Mathlib
import StacksProject_2024.Chap10.Theorem_10_129_4
import StacksProject_2024.Chap10.Lemma_10_99_11
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap15.Lemma_15_16_1
import StacksProject_2024.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsNoetherianRing R] [IsNoetherianRing S]
variable [IsAdicComplete (maximalIdeal R) R]
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

namespace Ideal

/-- An ideal `J` cuts out a quotient triple whose closed fiber is flat if `J` lies in the maximal
ideal of the local base ring and the closed subset of `Spec (S / JS)` above the closed point of
`Spec (R / J)` lies in the flat-over-base locus of `M / JM`. -/
abbrev IsClosedFiberFlatQuotient (J : Ideal R) (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] [IsLocalRing R] : Prop :=
  let Sbar := S ⧸ Ideal.map (algebraMap R S) J
  let Mbar := M ⧸ ((Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M))
  let _ : Module (R ⧸ J) Mbar := Module.compHom _ (algebraMap (R ⧸ J) Sbar)
  let _ : IsScalarTower (R ⧸ J) Sbar Mbar := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let mbar := Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R)
  let Kbar := Ideal.map (algebraMap (R ⧸ J) Sbar) mbar
  J ≤ maximalIdeal R ∧ zeroLocus (Kbar : Set Sbar) ⊆ Module.flatOverBaseLocus (R ⧸ J) Sbar Mbar

end Ideal

/- Domain triage:
- primary domain: flatness on the closed fiber of a quotient triple in local commutative algebra;
- sampled owner declarations: `Ideal.IsClosedFiberFlatQuotient`, `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `IsLocalRing.quotient`, and
  `IsLocalRing.map_maximalIdeal_of_surjective`;
- best owner abstraction: the source-facing ideal predicate `J.IsClosedFiberFlatQuotient S M`,
  whose flatness clause is canonically expressed through `Module.flatOverBaseLocus`;
- primitive data: the quotient triple `(R ⧸ J → S ⧸ JS, M ⧸ JM)`;
- derived API: the source-facing primewise reformulation and the least-ideal existence theorem.
-/

local notation "Sbar[" J "]" => S ⧸ Ideal.map (algebraMap R S) J
local notation "Mbar[" J "]" => M ⧸ ((Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M))
local notation "mbar[" J "]" => Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R)
local notation "Kbar[" J "]" => Ideal.map (algebraMap (R ⧸ J) (Sbar[J])) (mbar[J])

/-- The quotient module `M / J M`, regarded as an `R / J`-module by restricting scalars along
`R / J → S / JS`. -/
local instance quotientModule_module_over_baseQuotient (J : Ideal R) :
    Module (R ⧸ J) (Mbar[J]) :=
  Module.compHom _ (algebraMap (R ⧸ J) (Sbar[J]))

local instance quotientModule_isScalarTower (J : Ideal R) :
    IsScalarTower (R ⧸ J) (Sbar[J]) (Mbar[J]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

namespace Ideal

/-- Helper for Lemma 15.20.1: an ideal `J` gives a flat quotient if `M / JM` is flat over
`R ⧸ J`. -/
abbrev IsFlatQuotientOverAlgebra (J : Ideal R) (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] : Prop :=
  let Sbar := S ⧸ Ideal.map (algebraMap R S) J
  let Mbar := M ⧸ ((Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M))
  let _ : Module (R ⧸ J) Mbar := Module.compHom _ (algebraMap (R ⧸ J) Sbar)
  Module.Flat (R ⧸ J) Mbar

end Ideal

attribute [local instance] quotientModule_module_over_baseQuotient quotientModule_isScalarTower

/- Helper for Lemma 15.20.1: over a local base ring, a prime of an algebra lies above the closed
point exactly when it contains the image of the maximal ideal. -/
lemma mem_zeroLocus_map_maximalIdeal_iff_comap_eq_maximalIdeal
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    (q : PrimeSpectrum B) :
    q ∈ zeroLocus (Ideal.map (algebraMap A B) (maximalIdeal A) : Set B) ↔
      Ideal.comap (algebraMap A B) q.asIdeal = maximalIdeal A := by
  constructor
  · intro hq
    have hle :
        maximalIdeal A ≤ Ideal.comap (algebraMap A B) q.asIdeal :=
      Ideal.map_le_iff_le_comap.mp <| (mem_zeroLocus q
        (Ideal.map (algebraMap A B) (maximalIdeal A) : Set B)).1 hq
    letI : (Ideal.comap (algebraMap A B) q.asIdeal).IsPrime :=
      Ideal.comap_isPrime (algebraMap A B) q.asIdeal
    -- In a local ring every prime ideal lies under the maximal ideal, so the two ideals coincide.
    exact le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime _) hle
  · intro hq
    -- Rewrite the closed-point condition back as containment of the mapped maximal ideal.
    refine (mem_zeroLocus q (Ideal.map (algebraMap A B) (maximalIdeal A) : Set B)).2 ?_
    exact Ideal.map_le_iff_le_comap.mpr <| by simpa [hq]

-- Proof sketch: `Module.flatOverBaseLocus` is the owner abstraction for flatness on a closed
-- subset of `Spec (S ⧸ JS)`. For `J ≤ maximalIdeal R`, the ideal cutting out the closed point of
-- `Spec (R ⧸ J)` is `maximalIdeal (R ⧸ J)`, identified with the image of `maximalIdeal R`, so a
-- prime of `S ⧸ JS` contains its image exactly when its pullback is that maximal ideal.
/-- Unfolding the owner-level closed-fiber flatness condition for the quotient triple by `J`
recovers the source-facing primewise formulation over the closed point of `Spec (R ⧸ J)`. -/
theorem quotient_primewise_flat_over_closed_point_iff
    (J : Ideal R) (hJ : J ≤ maximalIdeal R) :
    let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
    zeroLocus
        (Ideal.map (algebraMap (R ⧸ J) (Sbar[J])) (maximalIdeal (R ⧸ J)) : Set (Sbar[J])) ⊆
      Module.flatOverBaseLocus (R ⧸ J) (Sbar[J]) (Mbar[J]) ↔
      ∀ q : PrimeSpectrum (Sbar[J]),
        Ideal.comap (algebraMap (R ⧸ J) (Sbar[J])) q.asIdeal = maximalIdeal (R ⧸ J) →
          Module.Flat (R ⧸ J) (LocalizedModule.AtPrime q.asIdeal (Mbar[J])) := by
  let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
  constructor
  · intro hflat q hq
    -- Translate the closed-point hypothesis into zero-locus membership and apply the owner lemma.
    exact
      (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
        (R := R ⧸ J) (S := Sbar[J]) (M := Mbar[J])
        (Ideal.map (algebraMap (R ⧸ J) (Sbar[J])) (maximalIdeal (R ⧸ J)))).1 hflat q <|
        (mem_zeroLocus_map_maximalIdeal_iff_comap_eq_maximalIdeal q).2 hq
  · intro hflat
    -- Conversely, the primewise closed-point criterion is exactly the zero-locus formulation.
    refine
      (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
        (R := R ⧸ J) (S := Sbar[J]) (M := Mbar[J])
        (Ideal.map (algebraMap (R ⧸ J) (Sbar[J])) (maximalIdeal (R ⧸ J)))).2 ?_
    intro q hq
    exact hflat q <|
      (mem_zeroLocus_map_maximalIdeal_iff_comap_eq_maximalIdeal q).1 hq

/-- Helper for Lemma 15.20.1: the closed-fiber-flat quotient condition already records that the
ideal lies inside the maximal ideal of the local base ring. -/
lemma isClosedFiberFlatQuotient_le_maximalIdeal
    {J : Ideal R} (hJ : J.IsClosedFiberFlatQuotient S M) :
    J ≤ maximalIdeal R := by
  -- Proof comment: this is the first conjunct in the owner predicate.
  exact hJ.1

/-- Helper for Lemma 15.20.1: the owner predicate on an ideal `I` is exactly the quotient-side
zero-locus inclusion over `R ⧸ I`, after rewriting the quotient maximal ideal. -/
lemma quotient_closedFiberFlat_zeroLocus_subset_flatOverBaseLocus
    {I : Ideal R}
    (hI : I.IsClosedFiberFlatQuotient S M) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI.1
    zeroLocus
        (Ideal.map (algebraMap (R ⧸ I) (Sbar[I])) (maximalIdeal (R ⧸ I)) : Set (Sbar[I])) ⊆
      Module.flatOverBaseLocus (R ⧸ I) (Sbar[I]) (Mbar[I]) := by
  let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI.1
  have hmax :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) := by
    -- Proof comment: quotienting a local ring by an ideal inside its maximal ideal preserves the
    -- closed point as the image of the original maximal ideal.
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  -- Proof comment: after identifying the quotient maximal ideal, the stored owner predicate is
  -- exactly the desired zero-locus inclusion over the quotient triple.
  simpa [Ideal.IsClosedFiberFlatQuotient, hmax] using hI.2

/-- Helper for Lemma 15.20.1: once the quotient-side zero-locus inclusion is unpacked, the
closed-fiber-flat condition gives the expected primewise flatness criterion over the closed point
of `Spec (R ⧸ J)`. -/
lemma quotient_closedFiberFlat_primewise_flat
    {J : Ideal R}
    (hJ : J.IsClosedFiberFlatQuotient S M) :
    let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ.1
    ∀ q : PrimeSpectrum (Sbar[J]),
      Ideal.comap (algebraMap (R ⧸ J) (Sbar[J])) q.asIdeal = maximalIdeal (R ⧸ J) →
        Module.Flat (R ⧸ J) (LocalizedModule.AtPrime q.asIdeal (Mbar[J])) := by
  let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ.1
  -- Proof comment: combine the quotient-side zero-locus inclusion with the primewise closed-point
  -- reformulation already established above.
  exact
    (quotient_primewise_flat_over_closed_point_iff (J := J) hJ.1).1 <|
      quotient_closedFiberFlat_zeroLocus_subset_flatOverBaseLocus (S := S) (M := M) hJ

/-- Helper for Lemma 15.20.1: the maximal ideal itself is always a closed-fiber-flat quotient
ideal, because the residue field quotient makes every module flat over the base. -/
lemma maximalIdeal_isClosedFiberFlatQuotient :
    (maximalIdeal R).IsClosedFiberFlatQuotient S M := by
  let _ : IsLocalRing (R ⧸ maximalIdeal R) := IsLocalRing.quotient (maximalIdeal R) <|
    (maximalIdeal.isMaximal R).ne_top
  refine ⟨le_rfl, ?_⟩
  -- Proof comment: over the residue field `R ⧸ maximalIdeal R`, every localized quotient module
  -- is flat, so the entire closed fiber lies in the flat-over-base locus.
  refine
    (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := R ⧸ maximalIdeal R) (S := Sbar[maximalIdeal R]) (M := Mbar[maximalIdeal R])
      (Kbar[maximalIdeal R])).2 ?_
  intro q hq
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

/-- Helper for Lemma 15.20.1: in a quotient by an ideal inside the maximal ideal, the original
ideal is the intersection of its thickenings by powers of the maximal ideal. -/
lemma ideal_eq_iInf_sup_maximalIdeal_pow_of_complete_quotient
    (J : Ideal R) (hJ : J ≤ maximalIdeal R) :
    J = ⨅ n : ℕ, J ⊔ maximalIdeal R ^ n := by
  let π : R →+* R ⧸ J := Ideal.Quotient.mk J
  have hJ_ne_top : J ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
  letI : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J hJ_ne_top
  have hbot :
      (⨅ n : ℕ, maximalIdeal (R ⧸ J) ^ n) = (⊥ : Ideal (R ⧸ J)) := by
    -- In the local quotient ring, Krull intersection identifies the maximal-ideal power tower.
    simpa using
      Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (R ⧸ J))
        (maximalIdeal.isMaximal (R ⧸ J)).ne_top
  have hcomap_bot : Ideal.comap π (⊥ : Ideal (R ⧸ J)) = J := by
    ext x
    change π x = 0 ↔ x ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem
  have hpullback := congrArg (Ideal.comap π) hbot
  -- Pull the quotient-side intersection back along the quotient map `R → R ⧸ J`.
  rw [Ideal.comap_iInf] at hpullback
  rw [hcomap_bot] at hpullback
  -- Rewrite each pulled-back stage using the image of the maximal ideal in the quotient.
  simp_rw [← IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
    hcomap_bot, sup_comm] at hpullback
  simpa using hpullback.symm

/-- Helper for Lemma 15.20.1: quotienting a Noetherian local ring by a positive power of its
maximal ideal produces an Artinian local ring. -/
lemma isArtinianRing_quotient_maximalIdeal_pow
    (n : ℕ) (hn : 1 ≤ n) :
    IsArtinianRing (R ⧸ maximalIdeal R ^ n) := by
  let K : Ideal R := maximalIdeal R ^ n
  have hK_le : K ≤ maximalIdeal R := by
    -- Proof comment: positive powers of the maximal ideal remain inside the maximal ideal.
    simpa [K] using Ideal.pow_le_self (I := maximalIdeal R) (Nat.ne_of_gt hn)
  have hK_ne_top : K ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hK_le
  letI : IsLocalRing (R ⧸ K) := IsLocalRing.quotient K hK_ne_top
  -- Proof comment: the image of `maximalIdeal R` is the maximal ideal downstairs, and its `n`th
  -- power vanishes because `maximalIdeal R ^ n` is killed by the quotient map.
  refine (isArtinianRing_iff_isNilpotent_maximalIdeal (R := R ⧸ K)).mpr ?_
  refine ⟨n, ?_⟩
  have hmax :
      Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R) = maximalIdeal (R ⧸ K) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hpow_bot :
      Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R ^ n) = (⊥ : Ideal (R ⧸ K)) := by
    -- Proof comment: quotienting by `K = maximalIdeal R ^ n` kills that ideal exactly.
    exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk K)).2 <| by
      simpa [K, Ideal.mk_ker]
  calc
    maximalIdeal (R ⧸ K) ^ n = (Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R)) ^ n := by
      rw [← hmax]
    _ = Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R ^ n) := by
      rw [← Ideal.map_pow]
    _ = ⊥ := hpow_bot

/-- Helper for Lemma 15.20.1: after quotienting by `J ≤ maximalIdeal R`, the image of the stage
ideal `J ⊔ maximalIdeal R ^ n` is exactly the `n`th power of the maximal ideal downstairs. -/
lemma map_sup_maximalIdeal_pow_eq_maximalIdeal_pow
    (J : Ideal R) (hJ : J ≤ maximalIdeal R) (n : ℕ) :
    let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
    Ideal.map (Ideal.Quotient.mk J) (J ⊔ maximalIdeal R ^ n) =
      maximalIdeal (R ⧸ J) ^ n := by
  let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
  have hmax :
      Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) = maximalIdeal (R ⧸ J) := by
    -- Proof comment: the closed point of the quotient local ring is the image of the original
    -- maximal ideal.
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax_pow :
      Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) ^ n =
        maximalIdeal (R ⧸ J) ^ n := by
    rw [hmax]
  -- Proof comment: mapping the stage ideal to the quotient kills `J` and sends the remaining
  -- maximal-ideal power to the corresponding power downstairs.
  calc
    Ideal.map (Ideal.Quotient.mk J) (J ⊔ maximalIdeal R ^ n) =
        Ideal.map (Ideal.Quotient.mk J) J ⊔
          Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R ^ n) := by
          rw [Ideal.map_sup]
    _ = ⊥ ⊔ Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R ^ n) := by
          congr 1
          exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk J)).2 <| by
            simpa [Ideal.mk_ker]
    _ = Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R ^ n) := by simp
    _ = mbar[J] ^ n := by
          rw [Ideal.map_pow]
    _ = maximalIdeal (R ⧸ J) ^ n := hmax_pow

/-- Helper for Lemma 15.20.1: flatness is unchanged when one restricts scalars along a ring
equivalence. -/
lemma flat_over_ringEquiv_iff
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B)
    {N : Type*} [AddCommGroup N] [Module B N] :
    let _ : Module A N := Module.compHom N e.toRingHom
    Module.Flat A N ↔ Module.Flat B N := by
  constructor
  · intro h
    let _ : Algebra B A := e.symm.toRingHom.toAlgebra
    let _ : Module A N := Module.compHom N e.toRingHom
    let _ : IsScalarTower B A N := IsScalarTower.of_algebraMap_smul fun b n ↦ by
      change e (e.symm b) • n = b • n
      simp
    let _ : Module.Flat B A := by
      -- Proof comment: the inverse ring equivalence is a flat ring map because it is bijective.
      simpa [RingHom.Flat] using
        (RingHom.Flat.of_bijective e.symm.bijective : e.symm.toRingHom.Flat)
    let _ : Module.Flat A N := h
    -- Proof comment: compose the flat restriction map `B → A` with the given `A`-flat module.
    simpa using Module.Flat.trans B A N
  · intro h
    let _ : Algebra A B := e.toRingHom.toAlgebra
    let _ : Module A N := Module.compHom N e.toRingHom
    let _ : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let _ : Module.Flat A B := by
      -- Proof comment: the forward ring equivalence is likewise flat by bijectivity.
      simpa [RingHom.Flat] using
        (RingHom.Flat.of_bijective e.bijective : e.toRingHom.Flat)
    let _ : Module.Flat B N := h
    -- Proof comment: compose `A → B` with the known `B`-flatness of `N`.
    simpa using Module.Flat.trans A B N

/-- Helper for Lemma 15.20.1: mapping the image of `J` in `R ⧸ K` into `S / KS` agrees with first
mapping `J` into `S` and then quotienting by `KS`. -/
lemma map_image_in_base_quotient_eq_target_quotient_image
    {K J : Ideal R} :
    Ideal.map (algebraMap (R ⧸ K) (Sbar[K])) (Ideal.map (Ideal.Quotient.mk K) J) =
      Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) K))
        (Ideal.map (algebraMap R S) J) := by
  -- Proof comment: both ideals are the image of `J` under the two factorizations of
  -- `R → S / KS`.
  have hcomp :
      (algebraMap (R ⧸ K) (Sbar[K])).comp (Ideal.Quotient.mk K) =
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) K)).comp (algebraMap R S) := by
    ext x
    rfl
  calc
    Ideal.map (algebraMap (R ⧸ K) (Sbar[K])) (Ideal.map (Ideal.Quotient.mk K) J) =
        Ideal.map ((algebraMap (R ⧸ K) (Sbar[K])).comp (Ideal.Quotient.mk K)) J := by
          rw [Ideal.map_map]
    _ =
        Ideal.map
          (((Ideal.Quotient.mk (Ideal.map (algebraMap R S) K)).comp (algebraMap R S))) J := by
          rw [hcomp]
    _ =
        Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) K))
          (Ideal.map (algebraMap R S) J) := by
          rw [← Ideal.map_map]

/-- Helper for Lemma 15.20.1: quotienting `M / KS M` again by the image of `JS` recovers
`M / JS M` as an `S`-linear quotient-of-quotient equivalence. -/
noncomputable def quotient_quotient_smul_top_equiv_of_le_algebra
    {K J : Ideal R} (hKJ : K ≤ J) :
    let Ksm : Submodule S M := (Ideal.map (algebraMap R S) K) • (⊤ : Submodule S M)
    let Jsm : Submodule S M := (Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M)
    ((M ⧸ Ksm) ⧸
      ((((Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) K))
            (Ideal.map (algebraMap R S) J)) •
          (⊤ : Submodule (Sbar[K]) (M ⧸ Ksm))) :
            Submodule (Sbar[K]) (M ⧸ Ksm)).restrictScalars S)) ≃ₗ[S]
      M ⧸ Jsm := by
  let Ksm : Submodule S M := (Ideal.map (algebraMap R S) K) • (⊤ : Submodule S M)
  let Jsm : Submodule S M := (Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M)
  have hmap_le :
      Ideal.map (algebraMap R S) K ≤ Ideal.map (algebraMap R S) J :=
    Ideal.map_mono hKJ
  have hden :
      ((((Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) K))
            (Ideal.map (algebraMap R S) J)) •
          (⊤ : Submodule (Sbar[K]) (M ⧸ Ksm))) :
            Submodule (Sbar[K]) (M ⧸ Ksm)).restrictScalars S) =
        Jsm.map Ksm.mkQ := by
    -- Proof comment: rewrite the quotient-ring action back to the original `S`-action, then
    -- identify the denominator with the image of `JS M` inside `M / KS M`.
    calc
      ((((Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) K))
            (Ideal.map (algebraMap R S) J)) •
          (⊤ : Submodule (Sbar[K]) (M ⧸ Ksm))) :
            Submodule (Sbar[K]) (M ⧸ Ksm)).restrictScalars S) =
          Ideal.map (algebraMap R S) J • (⊤ : Submodule S (M ⧸ Ksm)) := by
            simpa [Ksm] using
              (Ideal.smul_restrictScalars
                (R := S) (S := Sbar[K]) (M := M ⧸ Ksm)
                (Ideal.map (algebraMap R S) J) (⊤ : Submodule (Sbar[K]) (M ⧸ Ksm)))
      _ = Jsm.map Ksm.mkQ := by
            simpa [Jsm] using
              (Submodule.map_smul'' (f := Ksm.mkQ)
                (Ideal.map (algebraMap R S) J) (⊤ : Submodule S M))
  -- Proof comment: after identifying the denominator, apply the standard third isomorphism
  -- theorem for submodule quotients.
  exact
    (Submodule.quotEquivOfEq _ _ hden).trans
      (Submodule.quotientQuotientEquivQuotient Ksm Jsm (Submodule.smul_mono hmap_le le_rfl))

/-- Helper for Lemma 15.20.1: after restricting scalars to the base ring, quotienting by the
extended ideal agrees with quotienting by the base ideal action. -/
noncomputable def quotientModule_over_algebra_equiv_base_quotientModule_restrictScalars
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (I : Ideal A) :
    (N ⧸ ((Ideal.map (algebraMap A B) I) • (⊤ : Submodule B N))) ≃ₗ[A]
      (N ⧸ (I • (⊤ : Submodule A N))) := by
  -- Proof comment: forget the algebra quotient to the corresponding `A`-module quotient, then
  -- identify the denominator with `I N` by restricting scalars.
  exact
    (Submodule.Quotient.restrictScalarsEquiv A
      (((Ideal.map (algebraMap A B) I) • (⊤ : Submodule B N)) : Submodule B N)).symm.trans
      (Submodule.quotEquivOfEq
        (Submodule.restrictScalars A
          (((Ideal.map (algebraMap A B) I) • (⊤ : Submodule B N)) : Submodule B N))
        ((I • (⊤ : Submodule A N)) : Submodule A N)
        (by
          -- Proof comment: restricting scalars converts the extended-ideal quotient into the
          -- ordinary base-module quotient by `I N`.
          simpa using
            (Ideal.smul_restrictScalars
              (R := A) (S := B) (M := N) I (⊤ : Submodule B N))))

/-- Helper for Lemma 15.20.1: the quotient-ring-linear refinement of the preceding scalar-restricted
bridge identifies the algebra-side quotient module with the base quotient module. -/
noncomputable def quotientModule_over_algebra_equiv_base_quotientModule
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (I : Ideal A) :
    let Nbar := N ⧸ ((Ideal.map (algebraMap A B) I) • (⊤ : Submodule B N))
    let _ : Module (A ⧸ I) Nbar :=
      Module.compHom _ (algebraMap (A ⧸ I) (B ⧸ Ideal.map (algebraMap A B) I))
    Nbar ≃ₗ[A ⧸ I] (N ⧸ (I • (⊤ : Submodule A N))) := by
  -- TODO: upgrade the proved `A`-linear bridge
  -- `quotientModule_over_algebra_equiv_base_quotientModule_restrictScalars` to `A ⧸ I`-linearity
  -- by an explicit computation on quotient classes for the scalar action of `Ideal.Quotient.mk I`.
  sorry

/-- Helper for Lemma 15.20.1: the algebra-side flat quotient predicate is equivalent to the
earlier base-ring flat quotient predicate on the same ideal. -/
lemma isFlatQuotientOverAlgebra_iff_isFlatQuotient
    {A : Type*} {B : Type*} {N : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (I : Ideal A) :
    I.IsFlatQuotientOverAlgebra B N ↔ I.IsFlatQuotient N := by
  dsimp [Ideal.IsFlatQuotientOverAlgebra, Ideal.IsFlatQuotient]
  constructor
  · intro h
    let _ : Module.Flat (A ⧸ I)
        (N ⧸ ((Ideal.map (algebraMap A B) I) • (⊤ : Submodule B N))) := h
    exact
      Module.Flat.of_linearEquiv
        (quotientModule_over_algebra_equiv_base_quotientModule
          (A := A) (B := B) (N := N) I).symm
  · intro h
    let _ : Module.Flat (A ⧸ I) (N ⧸ (I • (⊤ : Submodule A N))) := h
    exact
      Module.Flat.of_linearEquiv
        (quotientModule_over_algebra_equiv_base_quotientModule
          (A := A) (B := B) (N := N) I)

/-- Helper for Lemma 15.20.1: quotient flatness over `R ⧸ K` for the image of `J` is exactly the
same as quotient flatness upstairs for `J`. -/
lemma isFlatQuotientOverAlgebra_map_iff
    {K J : Ideal R} (hKJ : K ≤ J) :
    (Ideal.map (Ideal.Quotient.mk K) J).IsFlatQuotientOverAlgebra (Sbar[K]) (Mbar[K]) ↔
      J.IsFlatQuotientOverAlgebra S M := by
  -- TODO: combine `quotientModule_over_algebra_equiv_base_quotientModule` with
  -- `quotient_quotient_smul_top_equiv_of_le_algebra` so that the quotient-of-quotient module on
  -- the left is transported all the way to the base quotient module used by
  -- `Ideal.isFlatQuotient_map_iff`.
  sorry

/-- Helper for Lemma 15.20.1: for each positive power of the maximal ideal, there is a least
ideal above that power whose quotient module is flat over the corresponding quotient ring. -/
lemma exists_isLeast_flat_quotient_ideal_above_maximalIdeal_pow
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ I : Ideal R,
      IsLeast {J : Ideal R | maximalIdeal R ^ n ≤ J ∧ J.IsFlatQuotientOverAlgebra S M} I := by
  -- TODO: apply the Artinian least-flat-quotient theorem over `R ⧸ maximalIdeal R ^ n` and
  -- transport it back along `Ideal.map (Ideal.Quotient.mk _)`; this file now has the needed
  -- `isFlatQuotientOverAlgebra_map_iff`, but the canonical owner `Lemma_15_17_1` cannot yet be
  -- imported in this workspace because of the duplicated `Ideal.IsFlatQuotient` API.
  sorry

/-- Helper for Lemma 15.20.1: closed-fiber flatness is equivalent to flatness of all thickenings
by positive powers of the maximal ideal. -/
lemma isClosedFiberFlatQuotient_iff_forall_stage_flat_sup_maximalIdeal_pow
    (J : Ideal R) :
    J.IsClosedFiberFlatQuotient S M ↔
      ∀ n : ℕ, 1 ≤ n → (J ⊔ maximalIdeal R ^ n).IsFlatQuotientOverAlgebra S M := by
  -- TODO: rewrite the quotient triple by `J` and apply
  -- `flat_localizedModule_atPrime_of_flat_quotients_by_ideal_powers`; the remaining bridge is to
  -- convert its quotient-stage hypotheses back to `J ⊔ maximalIdeal R ^ n` using the proved
  -- quotient-image transport and `map_sup_maximalIdeal_pow_eq_maximalIdeal_pow`.
  sorry

/-- Helper for Lemma 15.20.1: the least stage-flat ideals above successive powers of the maximal
ideal satisfy the compatibility relation from the source proof. -/
lemma flat_quotient_approximation_compatible
    (Istage : ℕ → Ideal R)
    (hstage :
      ∀ n : ℕ, 1 ≤ n →
        IsLeast {J : Ideal R | maximalIdeal R ^ n ≤ J ∧ J.IsFlatQuotientOverAlgebra S M}
          (Istage n)) :
    ∀ n : ℕ, 1 ≤ n → Istage (n + 1) ⊔ maximalIdeal R ^ n = Istage n := by
  -- TODO: show that `Istage (n + 1)` descends to a stage-`n` flat quotient through the quotient
  -- by `maximalIdeal R ^ n`, then apply stage-`n` leastness to
  -- `Istage (n + 1) ⊔ maximalIdeal R ^ n` and stage-`(n + 1)` leastness to `Istage n`.
  sorry

/-- Helper for Lemma 15.20.1: a compatible tower of ideals modulo the powers of the maximal ideal
comes from a single ideal of the complete local ring. -/
lemma ideal_of_compatible_maximalIdeal_tower
    (Istage : ℕ → Ideal R)
    (hbounded : ∀ n : ℕ, 1 ≤ n → Istage n ≤ maximalIdeal R)
    (hcompat : ∀ n : ℕ, 1 ≤ n → Istage (n + 1) ⊔ maximalIdeal R ^ n = Istage n) :
    ∃ I : Ideal R, ∀ n : ℕ, 1 ≤ n → I ⊔ maximalIdeal R ^ n = Istage n := by
  -- TODO: realize the compatible tower as a single ideal by lifting compatible stage classes
  -- through the `maximalIdeal R`-adic completion of `R`; the current blocker is packaging those
  -- compatible quotient classes into the exact `AdicCompletion` API used in this project.
  sorry


-- Proof sketch: apply the Artinian approximation statement to the quotients by powers of
-- `maximalIdeal R`, use compatibility of the resulting smallest ideals modulo successive powers,
-- and pass to the inverse limit using adic completeness of `R`.
/-- Lemma 15.20.1: for a complete Noetherian local ring `R`, a Noetherian `R`-algebra `S`, and a
finite `S`-module `M`, there exists a smallest ideal `I ⊆ maximalIdeal R` such that for every
prime of `S / IS` lying over the closed point of `Spec R`, the localization of `M / I M` is flat
over `R / I`. -/
@[stacks 0526]
theorem exists_isLeast_quotient_primewise_flat_over_closed_point_ideal :
    ∃ I : Ideal R,
      IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I := by
  classical
  let stageSet (n : ℕ) : Set (Ideal R) :=
    {J : Ideal R | maximalIdeal R ^ n ≤ J ∧ J.IsFlatQuotientOverAlgebra S M}
  let Istage : ℕ → Ideal R := fun n ↦
    if hn : 1 ≤ n then
      Classical.choose
        (exists_isLeast_flat_quotient_ideal_above_maximalIdeal_pow
          (R := R) (S := S) (M := M) n hn)
    else
      maximalIdeal R
  have hstage :
      ∀ n : ℕ, 1 ≤ n → IsLeast (stageSet n) (Istage n) := by
    intro n hn
    -- Proof comment: for positive stages, `Istage n` is chosen from the stagewise least-ideal
    -- existence theorem above `maximalIdeal R ^ n`.
    simpa [Istage, hn, stageSet] using
      (Classical.choose_spec
        (exists_isLeast_flat_quotient_ideal_above_maximalIdeal_pow
          (R := R) (S := S) (M := M) n hn))
  have hmax_flat :
      ∀ n : ℕ, 1 ≤ n → (maximalIdeal R).IsFlatQuotientOverAlgebra S M := by
    intro n hn
    -- Proof comment: apply the stage bridge to the closed-fiber-flat maximal ideal itself, then
    -- simplify the thickening `maximalIdeal R ⊔ maximalIdeal R ^ n`.
    have hstage_flat :=
      (isClosedFiberFlatQuotient_iff_forall_stage_flat_sup_maximalIdeal_pow
        (R := R) (S := S) (M := M) (maximalIdeal R)).1
        (maximalIdeal_isClosedFiberFlatQuotient (R := R) (S := S) (M := M)) n hn
    have hpow_le : maximalIdeal R ^ n ≤ maximalIdeal R :=
      Ideal.pow_le_self (I := maximalIdeal R) (Nat.ne_of_gt hn)
    simpa [sup_eq_left.mpr hpow_le] using hstage_flat
  have hbounded :
      ∀ n : ℕ, 1 ≤ n → Istage n ≤ maximalIdeal R := by
    intro n hn
    -- Proof comment: the maximal ideal is a valid stage-flat competitor at every positive stage,
    -- so leastness forces the chosen stage ideal to lie inside it.
    have hpow_le : maximalIdeal R ^ n ≤ maximalIdeal R :=
      Ideal.pow_le_self (I := maximalIdeal R) (Nat.ne_of_gt hn)
    exact (hstage n hn).2 ⟨hpow_le, hmax_flat n hn⟩
  have hcompat :
      ∀ n : ℕ, 1 ≤ n → Istage (n + 1) ⊔ maximalIdeal R ^ n = Istage n :=
    flat_quotient_approximation_compatible
      (R := R) (S := S) (M := M) Istage hstage
  obtain ⟨I, hIstage⟩ :=
    ideal_of_compatible_maximalIdeal_tower
      (R := R) Istage hbounded hcompat
  have hI_le_maximal : I ≤ maximalIdeal R := by
    have hstage_one : I ⊔ maximalIdeal R ^ 1 = Istage 1 :=
      hIstage 1 (by decide)
    have hbound_one : Istage 1 ≤ maximalIdeal R := hbounded 1 (by decide)
    rw [pow_one] at hstage_one
    have hsuple : I ⊔ maximalIdeal R ≤ maximalIdeal R := by
      rw [hstage_one]
      exact hbound_one
    exact le_trans le_sup_left hsuple
  have hI_closed : I.IsClosedFiberFlatQuotient S M := by
    -- Proof comment: each thickening of `I` matches a chosen stage ideal, hence is flat over the
    -- corresponding quotient ring by construction.
    rw [isClosedFiberFlatQuotient_iff_forall_stage_flat_sup_maximalIdeal_pow
      (R := R) (S := S) (M := M) I]
    intro n hn
    rw [hIstage n hn]
    exact (hstage n hn).1.2
  refine ⟨I, ⟨hI_closed, ?_⟩⟩
  intro J hJ
  have hJ_stage :
      ∀ n : ℕ, 1 ≤ n → (J ⊔ maximalIdeal R ^ n).IsFlatQuotientOverAlgebra S M := by
    exact
      (isClosedFiberFlatQuotient_iff_forall_stage_flat_sup_maximalIdeal_pow
        (R := R) (S := S) (M := M) J).1 hJ
  have hthick_le :
      ∀ n : ℕ, I ⊔ maximalIdeal R ^ n ≤ J ⊔ maximalIdeal R ^ n := by
    intro n
    by_cases hn : 1 ≤ n
    · rw [hIstage n hn]
      exact (hstage n hn).2 ⟨le_sup_right, hJ_stage n hn⟩
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      simp
  have hIeq :
      I = ⨅ n : ℕ, I ⊔ maximalIdeal R ^ n :=
    ideal_eq_iInf_sup_maximalIdeal_pow_of_complete_quotient
      (R := R) I hI_le_maximal
  have hJeq :
      J = ⨅ n : ℕ, J ⊔ maximalIdeal R ^ n :=
    ideal_eq_iInf_sup_maximalIdeal_pow_of_complete_quotient
      (R := R) J hJ.1
  have hiInf_le :
      (⨅ n : ℕ, I ⊔ maximalIdeal R ^ n) ≤
        ⨅ n : ℕ, J ⊔ maximalIdeal R ^ n := by
    refine le_iInf ?_
    intro n
    exact le_trans (iInf_le (fun k : ℕ ↦ I ⊔ maximalIdeal R ^ k) n) (hthick_le n)
  rw [hIeq, hJeq]
  exact hiInf_le

end
