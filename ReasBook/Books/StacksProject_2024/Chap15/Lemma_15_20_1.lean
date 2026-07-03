import Mathlib
import stacks_project.Chap10.Theorem_10_129_4
import stacks_project.Chap10.Lemma_10_156_2

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

/-- The localization of the quotient module `M / J M` at a prime of `S / JS`, regarded as an
`R / J`-module by restriction of scalars. -/
local instance localizedQuotientModuleAtPrime_module_over_baseQuotient
    (J : Ideal R) (q : PrimeSpectrum (Sbar[J])) :
    Module (R ⧸ J) (LocalizedModule.AtPrime q.asIdeal (Mbar[J])) :=
  Module.compHom _ (algebraMap (R ⧸ J) (Localization.AtPrime q.asIdeal))

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
          Module.Flat (R ⧸ J) (LocalizedModule.AtPrime q.asIdeal (Mbar[J])) := sorry

-- Proof sketch: apply the Artinian approximation statement to the quotients by powers of
-- `maximalIdeal R`, use compatibility of the resulting smallest ideals modulo successive powers,
-- and pass to the inverse limit using adic completeness of `R`.
/-- Lemma 15.20.1: for a complete Noetherian local ring `R`, a Noetherian `R`-algebra `S`, and a
finite `S`-module `M`, there exists a smallest ideal `I ⊆ maximalIdeal R` such that for every
prime of `S / IS` lying over the closed point of `Spec R`, the localization of `M / I M` is flat
over `R / I`. -/
theorem exists_isLeast_quotient_primewise_flat_over_closed_point_ideal :
    ∃ I : Ideal R,
      IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I := sorry

end
