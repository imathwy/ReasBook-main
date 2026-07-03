import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_20_1 (from Chap15) -/
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

/-! ### Lemma_15_20_2 (from Chap15) -/
open PrimeSpectrum IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')]
variable [IsNoetherianRing R']
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

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
/-- Lemma 15.20.2: if `I` is the least ideal from Lemma `15.20.1`, then for a local homomorphism
`R → R'` with `R'` Noetherian, the base-changed triple `(R' → S', M')` satisfies the
closed-fiber flatness condition
`(15.18.0.1)` exactly when the image of `I` in `R'` is zero. -/
theorem baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := sorry

end

/-! ### Lemma_15_20_3 (from Chap15) -/
open PrimeSpectrum IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
variable [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]
variable [AddCommGroup M] [Module S M] [Module.Finite S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/- Domain triage:
- primary domain: closed-fiber flatness loci under local base change in commutative algebra;
- sampled owner declarations:
  `Ideal.IsClosedFiberFlatQuotient`,
  `Module.flatOverBaseLocus`,
  `exists_stage_zeroLocus_subset_flatOverBaseLocus_of_direct_limit_base_change`,
  `baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal`;
- best owner abstraction: the source-facing least-ideal predicate
  `Ideal.IsClosedFiberFlatQuotient S M`, with `Module.flatOverBaseLocus` as the flatness-locus
  owner and `baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal` from
  `15.20.2` as the Noetherian-target bridge;
- primitive data: the least ideal `I` for `Ideal.IsClosedFiberFlatQuotient S M`, the local base
  change `R → R'`, and the finite type hypothesis on `R → S`;
- derived API: the elimination of the Noetherian target hypothesis by descending the base-changed
  closed-fiber flatness condition to an essentially finite type local `R`-subalgebra of `R'`.

Source/core/bridge triage:
- `source-facing`: the finite-type strengthening from the Stacks text, removing the Noetherian
  hypothesis on the target local ring;
- `core/canonical`: `Ideal.IsClosedFiberFlatQuotient S M` and `Module.flatOverBaseLocus`;
- `bridge/view`: Lemma `15.20.2`, used after descending along directed local approximations.
-/

-- Proof sketch: `(←)` is still Lemma `15.18.1`. For `(→)`, because `R` is Noetherian and
-- `R → S` is finite type, both `S` and the finite `S`-module `M` are finitely presented. Write
-- `R'` as a directed colimit of local `R`-subalgebras essentially of finite type over `R`; then
-- Lemma `15.18.3` descends the base-changed closed-fiber flatness condition to one stage `R_λ`.
-- Since `R_λ` is Noetherian, Lemma `15.20.2` shows that `I` maps to zero in `R_λ`, hence also in
-- `R'`.
/-- Lemma 15.20.3: if `I` is the least ideal from Lemma `15.20.1` and `R → S` is finite type,
then for any local homomorphism of local rings `R → R'` the base-changed triple
`(R' → S ⊗[R] R', (S ⊗[R] R') ⊗[S] M)` satisfies the closed-fiber flatness condition
`(15.18.0.1)` exactly when the image of `I` in `R'` is zero. -/
theorem baseChange_closedFiberFlat_iff_map_eq_bot_of_isLeast_closedFiberFlat_ideal_of_finiteType
    {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsClosedFiberFlatQuotient S M} I) :
    zeroLocus (Ideal.map (algebraMap R' S') (maximalIdeal R') : Set S') ⊆
      Module.flatOverBaseLocus R' S' M' ↔
      Ideal.map (algebraMap R R') I = ⊥ := by
  sorry

end
