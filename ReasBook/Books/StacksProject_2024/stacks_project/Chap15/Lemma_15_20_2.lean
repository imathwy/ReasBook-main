import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap10.Lemma_10_101_7
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')]
variable [IsNoetherianRing R']
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

namespace Ideal

/-- Helper for Lemma 15.20.2: an ideal `J` cuts out a quotient triple whose closed fiber is flat
if `J` lies in the maximal ideal of the local base ring and the closed subset of `Spec (S / JS)`
above the closed point of `Spec (R / J)` lies in the flat-over-base locus of `M / JM`. -/
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

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] IsScalarTower.right

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M
local notation "Sbar[" J "]" => S ⧸ Ideal.map (algebraMap R S) J
local notation "Mbar[" J "]" => M ⧸ ((Ideal.map (algebraMap R S) J) • (⊤ : Submodule S M))

/-- Helper for Lemma 15.20.2: the quotient module `M / J M`, regarded as an `R / J`-module by
restricting scalars along `R / J → S / JS`. -/
local instance quotientModule_module_over_baseQuotient (J : Ideal R) :
    Module (R ⧸ J) (Mbar[J]) :=
  Module.compHom _ (algebraMap (R ⧸ J) (Sbar[J]))

/-- Helper for Lemma 15.20.2: the quotient module `M / J M` is an `R / J`-to-`S / JS`
scalar tower. -/
local instance quotientModule_isScalarTower (J : Ideal R) :
    IsScalarTower (R ⧸ J) (Sbar[J]) (Mbar[J]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.20.2: the quotient module `M / J M` is also an `R`-module by restricting
scalars along `R → S / JS`. -/
local instance quotientModule_module_over_source (J : Ideal R) :
    Module R (Mbar[J]) :=
  Module.compHom _ (algebraMap R (Sbar[J]))

/-- Helper for Lemma 15.20.2: the quotient module `M / J M` forms an `R`-to-`S / JS`
scalar tower. -/
local instance quotientModule_isScalarTower_over_source (J : Ideal R) :
    IsScalarTower R (Sbar[J]) (Mbar[J]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.20.2: the quotient module `M / J M` also forms the scalar tower
`R → R ⧸ J → M / J M`. -/
local instance quotientModule_isScalarTower_over_sourceQuotient (J : Ideal R) :
    IsScalarTower R (R ⧸ J) (Mbar[J]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Lemma 15.20.2: the quotient module `M / J M` still forms the ambient scalar tower
`R → S → M / J M`. -/
local instance quotientModule_isScalarTower_over_ambient (J : Ideal R) :
    IsScalarTower R S (Mbar[J]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

attribute [local instance] quotientModule_module_over_baseQuotient quotientModule_isScalarTower

omit [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: over a local base ring, a prime of an algebra lies above the closed
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
    let _ : (Ideal.comap (algebraMap A B) q.asIdeal).IsPrime :=
      Ideal.comap_isPrime (algebraMap A B) q.asIdeal
    -- Proof comment: in a local ring every prime lies under the maximal ideal, so the two ideals
    -- coincide.
    exact le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime _) hle
  · intro hq
    -- Proof comment: rewrite the closed-point condition back as containment of the mapped maximal
    -- ideal.
    refine (mem_zeroLocus q (Ideal.map (algebraMap A B) (maximalIdeal A) : Set B)).2 ?_
    exact Ideal.map_le_iff_le_comap.mpr <| by simpa [hq]

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: the kernel of `R → R'` maps to zero in `R'`. -/
lemma kernel_map_eq_bot :
    Ideal.map (algebraMap R R') (RingHom.ker (algebraMap R R')) = ⊥ := by
  -- Proof comment: the kernel ideal is, by definition, contained in the kernel of the same map.
  exact (Ideal.map_eq_bot_iff_le_ker (f := algebraMap R R')).2 le_rfl

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: if the image of `J` in `R'` is zero, then each element of `J`
maps to zero in `R'`. -/
lemma map_eq_zero_of_mem_of_map_eq_bot
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥)
    {a : R}
    (ha : a ∈ J) :
    (algebraMap R R') a = 0 := by
  -- Proof comment: vanishing of the mapped ideal is equivalent to containment in the kernel of
  -- `R → R'`, which can then be read elementwise.
  have hle : J ≤ RingHom.ker (algebraMap R R') :=
    (Ideal.map_eq_bot_iff_le_ker (f := algebraMap R R')).mp hmap
  exact RingHom.mem_ker.mp (hle ha)

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: when `J` vanishes in `R'`, the algebra map `R → R'` factors through
the quotient `R ⧸ J`. -/
noncomputable abbrev quotient_factor_alg_hom
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥) :
    R ⧸ J →ₐ[R] R' :=
  Ideal.Quotient.liftₐ (R₁ := R) (I := J) (Algebra.ofId R R')
    (fun a ha ↦ map_eq_zero_of_mem_of_map_eq_bot (R := R) (R' := R') hmap (a := a) ha)

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: if an ideal vanishes in `R'`, then its extension to `S` also
vanishes in `S ⊗[R] R'`. -/
lemma map_baseChangeIdeal_eq_bot_of_map_eq_bot
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥) :
    Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) J) = ⊥ := by
  -- Proof comment: functoriality rewrites the `S`-side extension as the image of `J` in `S'`,
  -- and then the right-tensor algebra structure factors that through the already vanishing image in
  -- `R'`.
  calc
    Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) J) =
        Ideal.map (algebraMap R S') J := by
          rw [Ideal.map_map]
          rfl
    _ = Ideal.map (algebraMap R' S') (Ideal.map (algebraMap R R') J) := by
          rw [Ideal.map_map]
          congr 1
          ext r
          simp [IsScalarTower.algebraMap_eq R R' S']
    _ = Ideal.map (algebraMap R' S') ⊥ := by
          rw [hmap]
    _ = ⊥ := Ideal.map_bot

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: once `J` vanishes in `R'`, the quotient algebra `S / JS` maps
canonically to `S ⊗[R] R'`. -/
noncomputable abbrev quotient_factor_baseChange_alg_hom
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥) :
    Sbar[J] →ₐ[S] S' :=
  quotient_factor_alg_hom (R := S) (R' := S')
    (J := Ideal.map (algebraMap R S) J)
    (map_baseChangeIdeal_eq_bot_of_map_eq_bot
      (R := R) (S := S) (R' := R') hmap)

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: the canonical map from the kernel quotient into the target is
injective. -/
lemma kernel_quotient_algebraMap_injective :
    Function.Injective
      (Ideal.kerLiftAlg (Algebra.ofId R R') :
        R ⧸ RingHom.ker (algebraMap R R') →ₐ[R] R') := by
  -- Proof comment: `Ideal.kerLiftAlg` is the quotient-by-kernel comparison, whose injectivity is
  -- already packaged by the canonical owner theorem.
  simpa using (Ideal.kerLiftAlg_injective (Algebra.ofId R R'))

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: if `I` vanishes in `R'`, then `R → R'` factors through
`R ⧸ I`. -/
noncomputable def quotient_algebraMap_of_map_eq_bot
    {I : Ideal R}
    (hmap : Ideal.map (algebraMap R R') I = ⊥) :
    R ⧸ I →+* R' :=
  Ideal.Quotient.lift I (algebraMap R R')
    ((Ideal.map_eq_bot_iff_le_ker (algebraMap R R')).mp hmap)

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: the quotient factorization recovers the original map after
precomposing with the quotient projection. -/
lemma quotient_algebraMap_of_map_eq_bot_comp_mk
    {I : Ideal R}
    (hmap : Ideal.map (algebraMap R R') I = ⊥) :
    (quotient_algebraMap_of_map_eq_bot (R := R) (R' := R') hmap).comp (Ideal.Quotient.mk I) =
      algebraMap R R' := by
  -- Proof comment: this is the defining compatibility of `Ideal.Quotient.lift`.
  ext r
  rfl

/-- Helper for Lemma 15.20.2: an injective local map into an Artinian local ring forces the source
maximal ideal to be nilpotent. -/
lemma isNilpotent_maximalIdeal_of_injective_local_artinianTarget
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsArtinianRing B]
    (hinj : Function.Injective (algebraMap A B)) :
    IsNilpotent (maximalIdeal A) := by
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
  have hmap_le :
      Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B := by
    -- Proof comment: local homomorphisms preserve nonunits, hence map the source maximal ideal
    -- into the target maximal ideal.
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change (algebraMap A B) a ∈ maximalIdeal B
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    intro hunit
    exact ha (isUnit_of_map_unit (algebraMap A B) a hunit)
  refine ⟨n, ?_⟩
  have hpow_le :
      Ideal.map (algebraMap A B) (maximalIdeal A) ^ n ≤ maximalIdeal B ^ n := by
    simpa using pow_le_pow_left' hmap_le n
  have hmap_pow_le :
      Ideal.map (algebraMap A B) (maximalIdeal A ^ n) ≤ ⊥ := by
    calc
      Ideal.map (algebraMap A B) (maximalIdeal A ^ n) =
          Ideal.map (algebraMap A B) (maximalIdeal A) ^ n := by
            rw [Ideal.map_pow]
      _ ≤ maximalIdeal B ^ n := hpow_le
      _ = ⊥ := hn
  have hmap_pow :
      Ideal.map (algebraMap A B) (maximalIdeal A ^ n) = ⊥ := by
    -- Proof comment: mapping powers of the source maximal ideal lands inside the nilpotent power
    -- of the target maximal ideal.
    exact le_antisymm hmap_pow_le bot_le
  refine le_antisymm ?_ bot_le
  intro a ha
  apply hinj
  have ha_map :
      (algebraMap A B) a ∈ Ideal.map (algebraMap A B) (maximalIdeal A ^ n) :=
    Ideal.mem_map_of_mem _ ha
  simpa [hmap_pow] using ha_map

/- Domain triage:
- primary domain: closed-fiber flatness loci under local base change in commutative algebra;
- sampled owner declarations: `Ideal.IsClosedFiberFlatQuotient`, `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange`, and
  `exists_isLeast_quotient_primewise_flat_over_closed_point_ideal`;
- core/canonical owners: `Ideal.IsClosedFiberFlatQuotient` for the ideal-level source condition and
  `Module.flatOverBaseLocus` for its flatness clause;
- layer choice here: `source-facing`; the lemma keeps the Stacks iff, but phrases the least-ideal
  hypothesis through the chapter owner and the flatness side through the canonical
  closed-subset inclusion.
-/

-- Proof sketch: the forward implication applies Lemma `15.18.1` after base change and then uses
-- Artin-Rees in the Noetherian local ring `R'` to reduce vanishing of `I R'` to the Artinian
-- quotients `R' / (maximalIdeal R')^n`. For the converse, let `J = RingHom.ker (algebraMap R R')`;
-- the hypothesis implies the base-changed closed-fiber condition over `R'`, so after reducing to
-- the Artinian case one shows `M / J M` is flat over `R / J`, and the leastness of `I` forces
-- `I ≤ J`, equivalently `Ideal.map (algebraMap R R') I = ⊥`.
omit [IsLocalRing R] [IsLocalHom (algebraMap R R')] in
/-- Helper for Lemma 15.20.2: over an Artinian local target, every prime of `S ⊗[R] R'` lies over
the closed point of `Spec R'`. -/
lemma comap_asIdeal_eq_maximalIdeal_of_isArtinianTarget
    [IsArtinianRing R'] (q : PrimeSpectrum S') :
    Ideal.comap (algebraMap R' S') q.asIdeal = maximalIdeal R' := by
  -- Proof comment: an Artinian local ring has Krull dimension `0`, so every prime equals the
  -- unique maximal ideal.
  letI : Ring.KrullDimLE 0 R' := (isArtinianRing_iff_krullDimLE_zero (R := R')).mp inferInstance
  simpa using
    Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
      (Ideal.comap (algebraMap R' S') q.asIdeal)

/-- Helper for Lemma 15.20.2: if a stalk is flat over the base ring, then it is also flat over
the localization at the contracted prime. -/
lemma flat_localizedModule_atPrime_over_under_of_flat_over_base
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (q : PrimeSpectrum A)
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)) :
    Module.Flat (Localization.AtPrime (q.asIdeal.under R))
      (LocalizedModule.AtPrime q.asIdeal N) := by
  -- Proof comment: the imported Chapter 10 instances already give the localized module its
  -- `R_(q ∩ R)`-module structure, so flatness over `R` and over `R_(q ∩ R)` are equivalent by the
  -- owner localization theorem.
  let _ :
      IsScalarTower R (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal N) :=
    IsScalarTower.of_algebraMap_smul <| fun r x ↦ by
      change
        (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl
          ((algebraMap R (Localization.AtPrime (q.asIdeal.under R))) r)) • x = r • x
      rw [Localization.localRingHom_to_map]
      simpa [IsScalarTower.algebraMap_apply R A (Localization.AtPrime q.asIdeal)]
  let hloc :
      Module.Flat (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime q.asIdeal N) ↔
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal N) :=
    Module.flat_iff_of_isLocalization
      (R := R)
      (S := Localization.AtPrime (q.asIdeal.under R))
      (p := (q.asIdeal.under R).primeCompl)
      (M := LocalizedModule.AtPrime q.asIdeal N)
  exact hloc.symm.mp hflat

/-- Helper for Lemma 15.20.2: localizing a flat module at a prime of an algebra stays flat over
the original base ring. -/
lemma flat_localizedModule_atPrime_of_flat
    {A : Type*} [CommRing A] [Algebra R A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (q : PrimeSpectrum A)
    (hflat : Module.Flat R N) :
    Module.Flat R (LocalizedModule.AtPrime q.asIdeal N) := by
  -- Proof comment: first use the relative primewise criterion to get flatness over
  -- `R_(q ∩ R)`, then forget back to `R` through the same localization equivalence.
  have hq :
      Module.Flat (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal N) :=
    (flat_iff_flat_localizedModule_atPrime_over_under (R := R) (A := A) (M := N)).1 hflat q
  let _ :
      IsScalarTower R (Localization.AtPrime (q.asIdeal.under R))
        (LocalizedModule.AtPrime q.asIdeal N) :=
    IsScalarTower.of_algebraMap_smul <| fun r x ↦ by
      change
        (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl
          ((algebraMap R (Localization.AtPrime (q.asIdeal.under R))) r)) • x = r • x
      rw [Localization.localRingHom_to_map]
      simpa [IsScalarTower.algebraMap_apply R A (Localization.AtPrime q.asIdeal)]
  let hloc :
      Module.Flat (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime q.asIdeal N) ↔
        Module.Flat R (LocalizedModule.AtPrime q.asIdeal N) :=
    Module.flat_iff_of_isLocalization
      (R := R)
      (S := Localization.AtPrime (q.asIdeal.under R))
      (p := (q.asIdeal.under R).primeCompl)
      (M := LocalizedModule.AtPrime q.asIdeal N)
  exact hloc.mp hq

/-- Helper for Lemma 15.20.2: in the Artinian target case, the closed-fiber condition already
forces the whole base-changed module to be flat over `R'`. -/
lemma flat_of_closedFiberFlat_of_isArtinianTarget
    [IsArtinianRing R']
    (hflat :
      zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
        Module.flatOverBaseLocus R' S' M') :
    Module.Flat R' M' := by
  -- Proof comment: in the Artinian local target every prime lies over the closed point, so the
  -- closed-fiber hypothesis already gives `R'`-flatness of every stalk.
  refine (flat_iff_flat_localizedModule_atPrime_over_under (R := R') (A := S') (M := M')).2 ?_
  intro q
  have hq_closed :
      q ∈ zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') := by
    exact
      (mem_zeroLocus_map_maximalIdeal_iff_comap_eq_maximalIdeal q).2 <|
        comap_asIdeal_eq_maximalIdeal_of_isArtinianTarget
          (R := R) (S := S) (R' := R') q
  have hstalk :
      Module.Flat R' (LocalizedModule.AtPrime q.asIdeal M') :=
    (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := R') (S := S') (M := M')
      (Ideal.map (algebraMap R' S') (maximalIdeal R'))).1 hflat q hq_closed
  -- Proof comment: convert each stalk from `R'`-flatness to flatness over the contracted
  -- localization, which is the input expected by the prime-local criterion.
  exact
    flat_localizedModule_atPrime_over_under_of_flat_over_base
      (R := R') (A := S') (N := M') q hstalk

/-- Helper for Lemma 15.20.2: the closed-fiber-flat quotient condition already records that the
ideal lies inside the maximal ideal of the local base ring. -/
lemma isClosedFiberFlatQuotient_le_maximalIdeal
    {J : Ideal R} (hJ : J.IsClosedFiberFlatQuotient S M) :
    J ≤ maximalIdeal R := by
  -- Proof comment: this is the first conjunct in the owner predicate.
  exact hJ.1

/-- Helper for Lemma 15.20.2: the owner predicate on an ideal `I` is exactly the quotient-side
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

/-- Helper for Lemma 15.20.2: if `M / J M` is already flat over `R ⧸ J`, then `J` satisfies the
owner predicate `Ideal.IsClosedFiberFlatQuotient`. -/
lemma isClosedFiberFlatQuotient_of_flat_quotient_module
    (J : Ideal R) (hJ : J ≤ maximalIdeal R) :
    let _ : Module (R ⧸ J) (Mbar[J]) := Module.compHom _ (algebraMap (R ⧸ J) (Sbar[J]))
    let _ : IsScalarTower (R ⧸ J) (Sbar[J]) (Mbar[J]) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    Module.Flat (R ⧸ J) (Mbar[J]) → J.IsClosedFiberFlatQuotient S M := by
  dsimp
  intro hflat
  refine ⟨hJ, ?_⟩
  let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
  have hmax :
      Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R) = maximalIdeal (R ⧸ J) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  -- Proof comment: `J.IsClosedFiberFlatQuotient` is the quotient-side zero-locus inclusion, so it
  -- suffices to show every prime in that closed subset has an `R ⧸ J`-flat stalk.
  have hzero :
      zeroLocus
          (Ideal.map (algebraMap (R ⧸ J) (Sbar[J]))
            (maximalIdeal (R ⧸ J)) : Set Sbar[J]) ⊆
        Module.flatOverBaseLocus (R ⧸ J) (Sbar[J]) (Mbar[J]) := by
    refine
    (Ideal.zeroLocus_subset_flatOverBaseLocus_iff
      (R := R ⧸ J) (S := Sbar[J]) (M := Mbar[J])
      (Ideal.map (algebraMap (R ⧸ J) (Sbar[J])) (maximalIdeal (R ⧸ J)))).2 ?_
    intro q hq
    exact flat_localizedModule_atPrime_of_flat
      (R := R ⧸ J) (A := Sbar[J]) (N := Mbar[J]) q hflat
  simpa [Ideal.IsClosedFiberFlatQuotient, hmax] using hzero

/-- Helper for Lemma 15.20.2: once `I` vanishes in `R'`, the induced map `R ⧸ I → R'` sends the
closed point of `Spec (R ⧸ I)` into the closed point of `Spec R'`. -/
lemma quotient_maximalIdeal_map_le_target_maximalIdeal
    {I : Ideal R}
    (hI : I ≤ maximalIdeal R)
    (hmap : Ideal.map (algebraMap R R') I = ⊥) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I <|
      ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
    Ideal.map (quotient_algebraMap_of_map_eq_bot (R := R) (R' := R') hmap)
      (maximalIdeal (R ⧸ I)) ≤ maximalIdeal R' := by
  let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  have hmax :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  -- Proof comment: after rewriting the quotient maximal ideal as the image of `maximalIdeal R`,
  -- functoriality reduces the claim to the standard local-hom containment for `R → R'`.
  have hmap_le :
      Ideal.map (quotient_algebraMap_of_map_eq_bot (R := R) (R' := R') hmap)
        (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) ≤ maximalIdeal R' := by
    calc
      Ideal.map (quotient_algebraMap_of_map_eq_bot (R := R) (R' := R') hmap)
          (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) =
        Ideal.map (algebraMap R R') (maximalIdeal R) := by
          rw [Ideal.map_map, quotient_algebraMap_of_map_eq_bot_comp_mk]
      _ ≤ maximalIdeal R' := by
          have hcomap :
              Ideal.comap (algebraMap R R') (maximalIdeal R') = maximalIdeal R := by
            simpa using (IsLocalRing.maximalIdeal_comap (algebraMap R R'))
          exact Ideal.map_le_iff_le_comap.mpr <| by
            simpa [hcomap] using (show maximalIdeal R ≤ maximalIdeal R by exact le_rfl)
  simpa [hmax] using hmap_le

/-- Helper for Lemma 15.20.2: quotienting the Noetherian local target ring by a positive power of
its maximal ideal produces an Artinian ring. -/
lemma isArtinianRing_quotient_maximalIdeal_pow
    (n : ℕ) (hn : 1 ≤ n) :
    IsArtinianRing (R' ⧸ maximalIdeal R' ^ n) := by
  let K : Ideal R' := maximalIdeal R' ^ n
  have hK_le : K ≤ maximalIdeal R' := by
    -- Proof comment: positive powers of the maximal ideal remain inside the maximal ideal itself.
    simpa [K] using Ideal.pow_le_self (I := maximalIdeal R') (Nat.ne_of_gt hn)
  have hK_ne_top : K ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R').ne_top hK_le
  let _ : IsLocalRing (R' ⧸ K) := IsLocalRing.quotient K hK_ne_top
  -- Proof comment: the image of `maximalIdeal R'` is the maximal ideal downstairs, and its `n`th
  -- power vanishes because the quotient kills `K = (maximalIdeal R') ^ n`.
  refine (isArtinianRing_iff_isNilpotent_maximalIdeal (R := R' ⧸ K)).mpr ?_
  refine ⟨n, ?_⟩
  have hmax :
      Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R') = maximalIdeal (R' ⧸ K) := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hpow_bot :
      Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R' ^ n) = (⊥ : Ideal (R' ⧸ K)) := by
    -- Proof comment: quotienting by `K` kills the defining `n`th power exactly.
    exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk K)).2 <| by
      simpa [K, Ideal.mk_ker]
  calc
    maximalIdeal (R' ⧸ K) ^ n = (Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R')) ^ n := by
      rw [← hmax]
    _ = Ideal.map (Ideal.Quotient.mk K) (maximalIdeal R' ^ n) := by
      rw [← Ideal.map_pow]
    _ = ⊥ := hpow_bot

/-- Helper for Lemma 15.20.2: mapping an ideal to the Artinian stage
`R' ⧸ (maximalIdeal R') ^ n` is zero exactly when the ideal is contained in
`(maximalIdeal R') ^ n`. -/
lemma map_eq_bot_iff_le_maximalIdeal_pow_quotient
    {J : Ideal R'} (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) J = ⊥ ↔
      J ≤ maximalIdeal R' ^ n := by
  -- Proof comment: this is the standard `map_eq_bot` to kernel containment rewrite for the stage
  -- quotient map, whose kernel is exactly `(maximalIdeal R') ^ n`.
  simpa [Ideal.mk_ker] using
    (Ideal.map_eq_bot_iff_le_ker (f := Ideal.Quotient.mk (maximalIdeal R' ^ n)) (I := J))

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: if `J` vanishes in `R'`, then its extension to the base-changed
module `M'` acts trivially. -/
lemma map_baseChangeIdeal_smul_top_eq_bot_of_map_eq_bot
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥) :
    Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) J) •
        (⊤ : Submodule S' M') = ⊥ := by
  -- Proof comment: rewrite the scalar ideal through the previously established vanishing of its
  -- base-changed image, then the induced submodule is visibly zero.
  simpa [map_baseChangeIdeal_eq_bot_of_map_eq_bot
    (R := R) (S := S) (R' := R') hmap]

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: after factoring `R → R'` through `R ⧸ J`, tensoring `M / JSM` over
`R ⧸ J` agrees with tensoring it over `R`. -/
noncomputable abbrev factor_tensor_closedFiberQuotient_equiv_base_tensor_closedFiberQuotient
    {J : Ideal R}
    [Algebra (R ⧸ J) R']
    [IsScalarTower R (R ⧸ J) R'] :
    (R' ⊗[R ⧸ J] Mbar[J]) ≃ₗ[R'] (R' ⊗[R] Mbar[J]) :=
  -- Proof comment: first identify `(R ⧸ J) ⊗[R] Mbar[J]` with `Mbar[J]` via the quotient
  -- scalar tower, then cancel the intermediate base change.
  letI :
      TensorProduct.CompatibleSMul R (R ⧸ J) (R ⧸ J) (Mbar[J]) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R) (A := R ⧸ J) (M := R ⧸ J) (N := Mbar[J]) Ideal.Quotient.mk_surjective
  let eLid : ((R ⧸ J) ⊗[R] Mbar[J]) ≃ₗ[R ⧸ J] Mbar[J] :=
    TensorProduct.lidOfCompatibleSMul R (R ⧸ J) (Mbar[J])
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') eLid.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ J) R' R' (Mbar[J]))

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: if `J` vanishes in `R'`, then tensoring the quotient module
`M / JSM` over `S` recovers the original base-changed module `M'`. -/
noncomputable abbrev base_tensor_closedFiberQuotient_equiv_tensor_of_map_eq_bot
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥) :
    (S' ⊗[S] Mbar[J]) ≃ₗ[S'] M' :=
  -- Proof comment: quotienting by the zero ideal on the base-changed side does nothing, so the
  -- standard tensor/quotient comparison over `S` identifies the quotient tensor with `M'`.
  let eBot :
      M' ≃ₗ[S']
        (M' ⧸
          Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) J) •
            (⊤ : Submodule S' M')) :=
    ((Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) J) •
        (⊤ : Submodule S' M')).quotEquivOfEqBot
      (map_baseChangeIdeal_smul_top_eq_bot_of_map_eq_bot
        (R := R) (S := S) (M := M) (R' := R') hmap)).symm
  let eTensorQuot :
      (M' ⧸
          Ideal.map (algebraMap S S') (Ideal.map (algebraMap R S) J) •
            (⊤ : Submodule S' M')) ≃ₗ[S']
        (S' ⊗[S] Mbar[J]) :=
    TensorProduct.tensorQuotMapSMulEquivTensorQuot
      (S := S') (M := M) (Ideal.map (algebraMap R S) J)
  (eBot.trans eTensorQuot).symm

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] [IsNoetherianRing R'] in
/-- Helper for Lemma 15.20.2: if `J` vanishes in `R'`, then the quotient module `M / JSM`
base-changed from `R ⧸ J` identifies canonically with `M'`. -/
noncomputable abbrev baseChange_quotient_module_equiv_of_map_eq_bot
    {J : Ideal R}
    (hmap : Ideal.map (algebraMap R R') J = ⊥) :
    let φ : R ⧸ J →ₐ[R] R' := quotient_factor_alg_hom (R := R) (R' := R') hmap
    let _ : Algebra (R ⧸ J) R' := φ.toRingHom.toAlgebra
    (R' ⊗[R ⧸ J] Mbar[J]) ≃ₗ[R'] M' := by
  -- Proof comment: compose the factor-ring tensor comparison with the pushout cancellation
  -- `R' ⊗[R] Mbar[J] ≃ (S ⊗[R] R') ⊗[S] Mbar[J]`, then finish with the quotient/tensor collapse.
  let φ : R ⧸ J →ₐ[R] R' := quotient_factor_alg_hom (R := R) (R' := R') hmap
  let _ : Algebra (R ⧸ J) R' := φ.toRingHom.toAlgebra
  let eFactor :
      (R' ⊗[R ⧸ J] Mbar[J]) ≃ₗ[R'] (R' ⊗[R] Mbar[J]) :=
    factor_tensor_closedFiberQuotient_equiv_base_tensor_closedFiberQuotient
      (R := R) (S := S) (M := M) (R' := R') (J := J)
  let ePushout :
      (R' ⊗[R] Mbar[J]) ≃ₗ[R'] (S' ⊗[S] Mbar[J]) :=
    (Algebra.IsPushout.cancelBaseChange R R' S S' (Mbar[J])).symm
  let eTensor :
      (S' ⊗[S] Mbar[J]) ≃ₗ[R'] M' :=
    (base_tensor_closedFiberQuotient_equiv_tensor_of_map_eq_bot
      (R := R) (S := S) (M := M) (R' := R') (J := J) hmap).restrictScalars R'
  dsimp
  exact eFactor.trans <| ePushout.trans eTensor

/-- Helper for Lemma 15.20.2: in the Artinian target case, closed-fiber flatness forces the least
ideal `I` to vanish after base change. -/
lemma map_eq_bot_of_closedFiberFlat_of_isArtinianTarget
    [IsArtinianRing R'] {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I)
    (hflat :
      zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
        Module.flatOverBaseLocus R' S' M') :
    Ideal.map (algebraMap R R') I = ⊥ := by
  let J : Ideal R := RingHom.ker (algebraMap R R')
  have hJmax : J ≤ maximalIdeal R := by
    -- Proof comment: the kernel lands inside the pullback of the target closed point, which is
    -- the source maximal ideal for a local homomorphism.
    have hcomap :
        Ideal.comap (algebraMap R R') (maximalIdeal R') = maximalIdeal R := by
      simpa using (IsLocalRing.maximalIdeal_comap (algebraMap R R'))
    rw [← hcomap]
    intro r hr
    change (algebraMap R R') r ∈ maximalIdeal R'
    simpa [RingHom.mem_ker.mp hr]
  let _ : IsLocalRing (R ⧸ J) := IsLocalRing.quotient J <|
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJmax
  let φ : R ⧸ J →ₐ[R] R' := quotient_factor_alg_hom (R := R) (R' := R') kernel_map_eq_bot
  let _ : Algebra (R ⧸ J) R' := φ.toRingHom.toAlgebra
  have hinj : Function.Injective (algebraMap (R ⧸ J) R') := by
    -- Proof comment: the kernel quotient compares injectively with the target by the canonical
    -- quotient-by-kernel map.
    change Function.Injective φ
    simpa [φ, quotient_factor_alg_hom, kernel_map_eq_bot] using
      (kernel_quotient_algebraMap_injective (R := R) (R' := R'))
  let _ : IsLocalHom (algebraMap (R ⧸ J) R') := by
    -- Proof comment: the factored map is local because its composition with the quotient map is
    -- the original local homomorphism `R → R'`.
    refine ⟨?_⟩
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change IsUnit ((algebraMap R R') r) at ha
    exact (Ideal.Quotient.mk J).isUnit_map (isUnit_of_map_unit (algebraMap R R') r ha)
  have hnil :
      IsNilpotent (maximalIdeal (R ⧸ J)) :=
    isNilpotent_maximalIdeal_of_injective_local_artinianTarget
      (A := R ⧸ J) (B := R') hinj
  have hflat_base : Module.Flat R' M' :=
    flat_of_closedFiberFlat_of_isArtinianTarget (R := R) (S := S) (M := M) (R' := R') hflat
  have hflat_tensor :
      Module.Flat R' (R' ⊗[R ⧸ J] Mbar[J]) := by
    let e :
        (R' ⊗[R ⧸ J] Mbar[J]) ≃ₗ[R'] M' :=
      baseChange_quotient_module_equiv_of_map_eq_bot
        (R := R) (S := S) (M := M) (R' := R') (J := J) kernel_map_eq_bot
    let _ : Module.Flat R' M' := hflat_base
    exact Module.Flat.of_linearEquiv e
  have hflat_mod_max :
      Module.Flat ((R ⧸ J) ⧸ maximalIdeal (R ⧸ J))
        ((Mbar[J]) ⧸ (maximalIdeal (R ⧸ J) • (⊤ : Submodule (R ⧸ J) (Mbar[J])))) := by
    -- Proof comment: the quotient of a local ring by its maximal ideal is a field, so every
    -- module over it is flat.
    let _ : Field ((R ⧸ J) ⧸ maximalIdeal (R ⧸ J)) :=
      Ideal.Quotient.field (maximalIdeal (R ⧸ J))
    infer_instance
  have hflat_quot :
      Module.Flat (R ⧸ J) (Mbar[J]) := by
    -- Route correction: descend along the kernel quotient using the nilpotent maximal ideal of
    -- `R ⧸ J`; this avoids the earlier false dependency on an Artinian instance for `R ⧸ J`.
    exact
      flat_of_nilpotent_ideal_of_injective_algebraMap_of_flat_mod_ideal_and_flat_baseChange
        (R := R ⧸ J) (R' := R') (I := maximalIdeal (R ⧸ J)) (M := Mbar[J])
        hnil hinj hflat_mod_max hflat_tensor
  have hJclosed : J.IsClosedFiberFlatQuotient S M :=
    (isClosedFiberFlatQuotient_of_flat_quotient_module
      (R := R) (S := S) (M := M) J hJmax) hflat_quot
  have hle : I ≤ J := hI.2 hJclosed
  exact (Ideal.map_eq_bot_iff_le_ker (f := algebraMap R R')).2 hle

/-- Lemma 15.20.2: if `I` is the least ideal from Lemma `15.20.1`, then for a local homomorphism
`R → R'` with `R'` Noetherian, the base-changed triple `(R' → S', M')` satisfies the
closed-fiber flatness condition
`(15.18.0.1)` exactly when the image of `I` in `R'` is zero. -/
theorem baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := by
  constructor
  · intro hflat
    -- Proof comment: the source proof reduces vanishing of `I R'` to the Artinian quotients
    -- `R' ⧸ (maximalIdeal R')^(n + 1)`, applies the Artinian helper at every stage, and then
    -- concludes by Krull intersection in the Noetherian local ring `R'`.
    let J : Ideal R' := Ideal.map (algebraMap R R') I
    have hpow : ∀ n : ℕ, J ≤ maximalIdeal R' ^ n := by
      intro n
      cases n with
      | zero =>
          -- Proof comment: the zeroth power is the unit ideal, so the containment is automatic.
          simpa [J] using (show J ≤ (⊤ : Ideal R') by exact le_top)
      | succ k =>
          let A : Type x := R' ⧸ maximalIdeal R' ^ (k + 1)
          let _ : CommRing A := inferInstance
          let _ : Algebra R' A := (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))).toAlgebra
          let _ : Algebra R A := RingHom.comp
            (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))) (algebraMap R R')
          let _ : IsLocalRing A := inferInstance
          let _ : IsLocalHom (algebraMap R A) := inferInstance
          let _ : IsNoetherianRing A := inferInstance
          let _ : IsArtinianRing A :=
            isArtinianRing_quotient_maximalIdeal_pow
              (R' := R') (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
          have hmapMax :
              Ideal.map (algebraMap R' A) (maximalIdeal R') ≤ maximalIdeal A := by
            have hmax :
                Ideal.map (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))) (maximalIdeal R') =
                  maximalIdeal A := by
              -- Proof comment: quotienting a local ring by a proper ideal preserves the closed
              -- point as the image of the original maximal ideal.
              exact IsLocalRing.map_maximalIdeal_of_surjective
                (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))) Ideal.Quotient.mk_surjective
            simpa [A] using (show
              Ideal.map (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))) (maximalIdeal R') ≤
                maximalIdeal A by
              rw [hmax])
          have hflatA :
              zeroLocus (Ideal.map (algebraMap A (S' ⊗[R'] A)) (maximalIdeal A) :
                  Set (S' ⊗[R'] A)) ⊆
                Module.flatOverBaseLocus A (S' ⊗[R'] A) ((S' ⊗[R'] A) ⊗[S'] M') := by
            -- Proof comment: base change the closed-fiber-flatness inclusion from `R'` to the
            -- Artinian quotient `A`.
            simpa using
              (Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange
                (R := R') (S := S') (M := M') (R' := A)
                (I := maximalIdeal R') hflat hmapMax)
          have hmapA :
              Ideal.map (algebraMap R A) I = ⊥ :=
            map_eq_bot_of_closedFiberFlat_of_isArtinianTarget
              (R := R) (S := S) (M := M) (R' := A) hI hflatA
          have hmapJ :
              Ideal.map (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))) J = ⊥ := by
            -- Proof comment: the stage map on `J = I R'` is exactly the map of `I` to the
            -- quotient target.
            calc
              Ideal.map (Ideal.Quotient.mk (maximalIdeal R' ^ (k + 1))) J =
                  Ideal.map (algebraMap R A) I := by
                    rw [J, Ideal.map_map]
                    congr 1
                    ext r
                    rfl
              _ = ⊥ := hmapA
          -- Proof comment: vanishing in the stage quotient is equivalent to containment in the
          -- corresponding power of the maximal ideal.
          exact
            (map_eq_bot_iff_le_maximalIdeal_pow_quotient
              (R' := R') (J := J) (k + 1)).1 hmapJ
    have hJle :
        J ≤ ⨅ n : ℕ, maximalIdeal R' ^ n := by
      -- Proof comment: the Artinian-stage argument gives containment in every positive power, and
      -- the zeroth power is automatic.
      refine le_iInf hpow
    have hiInf :
        (⨅ n : ℕ, maximalIdeal R' ^ n) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R')
    exact le_antisymm (by simpa [J, hiInf] using hJle) bot_le
  · intro hmap
    -- Route correction: earlier attempts tried to normalize the present triple directly. The
    -- source-faithful route first base-changes the quotient triple from `hI.1` along
    -- `R ⧸ I → R'`, and only then compares the resulting algebra/module pair with `(S', M')`.
    let φ : R ⧸ I →ₐ[R] R' := quotient_factor_alg_hom (R := R) (R' := R') hmap
    let _ : Algebra (R ⧸ I) R' := φ.toRingHom.toAlgebra
    let _ : Algebra (Sbar[I]) S' := (quotient_factor_baseChange_alg_hom
      (R := R) (S := S) (R' := R') (J := I) hmap).toRingHom.toAlgebra
    have hquot :
        let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I <|
          ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI.1.1
        zeroLocus
            (Ideal.map (algebraMap (R ⧸ I) (Sbar[I])) (maximalIdeal (R ⧸ I)) : Set (Sbar[I])) ⊆
          Module.flatOverBaseLocus (R ⧸ I) (Sbar[I]) (Mbar[I]) :=
      quotient_closedFiberFlat_zeroLocus_subset_flatOverBaseLocus
        (R := R) (S := S) (M := M) hI.1
    have hmapMax :
        let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I <|
          ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI.1.1
        Ideal.map φ.toRingHom (maximalIdeal (R ⧸ I)) ≤ maximalIdeal R' :=
      quotient_maximalIdeal_map_le_target_maximalIdeal
        (R := R) (R' := R') hI.1.1 hmap
    let _ := hquot
    let _ := hmapMax
    -- TODO: apply Lemma `15.18.1` to the quotient triple over `R ⧸ I`, then transport the
    -- resulting closed-fiber inclusion across the canonical algebra comparison
    -- `(Sbar[I]) ⊗[R ⧸ I] R' ≃ₐ[R'] S'` and the module equivalence
    -- `baseChange_quotient_module_equiv_of_map_eq_bot`. The remaining blocker is packaging that
    -- algebra-side comparison so the flat-over-base-locus subset rewrites to the target statement.
    sorry

end
