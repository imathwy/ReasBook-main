import Mathlib
import stacks_project.Chap10.Lemma_10_52_6
import stacks_project.Chap10.Lemma_10_52_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open IsLocalRing LocalizedModule

universe u v w

noncomputable section

section Length

local notation "AtPrime" => LocalizedModule.AtPrime

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [Finite (MaximalSpectrum B)]

local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-
Domain triage:
* primary domain: finite-length modules over a semilocal algebra, decomposed by maximal ideals and
  the corresponding residue-field extensions;
* sampled owner API:
  `CompositionSeries.factor_count_eq_length_localizedModule`,
  `module_length_eq_rank_quotient_of_isTorsionBySet`,
  `Module.length_eq_add_of_exact`,
  `Module.length_ne_top_iff`;
* source-facing layer: the semilocal localization formula and its finite-length corollary;
* core/canonical owners: `CompositionSeries (Submodule B M)` for the localized factor counts and
  `IsFiniteLength` / `Module.IsTorsionBySet` for finite-length and residue-field computations;
* bridge/view: this file keeps the source-facing sum formula while routing its local simple-factor
  terms through the owner statements from `10.52.11` and `10.52.6` instead of duplicating those
  lower-level APIs.
-/

section ResidueFieldData

variable
    (hcomap : ∀ m : MaximalSpectrum B,
      Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)

private abbrev residueFieldModule (m : MaximalSpectrum B) :
    Module κA (Ideal.ResidueField m.asIdeal) :=
  ((Ideal.ResidueField.map (maximalIdeal A) m.asIdeal (algebraMap A B) (hcomap m).symm).toAlgebra).toModule

variable
    (hfinitek : ∀ m : MaximalSpectrum B,
      let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
      Module.Finite κA (Ideal.ResidueField m.asIdeal))

-- Proof sketch: choose a composition series of the finite-length `B`-module `M`. By Lemma
-- 10.52.11, each factor is a residue field `J.ResidueField` for a unique maximal ideal `J` of
-- `B`, and the number of times `J.ResidueField` occurs is the length of `M` localized at `J`.
-- Restrict scalars to `A`, identify the `A`-length of each factor with the length of the induced
-- residue-field extension `κ(maximalIdeal A) → κ(J)` via Lemma 10.52.6, and sum the contributions
-- using additivity of length from Lemma 10.52.3.
/-- Lemma 10.52.12 (Tag `02M0`): if `A → B` maps the semilocal ring `B` to the local ring `A`
so that every maximal ideal of `B` lies over `maximalIdeal A`, every residue-field extension
`κ(m) / κ(maximalIdeal A)` is finite, and `M` has finite length as a `B`-module, then the
`A`-length of `M` is the sum of the residue-field degrees
`[κ(m) : κ(maximalIdeal A)]` times the lengths of the localizations `Mₘ`.

Canonical Lean form: the semilocal structure is expressed by `[Finite (MaximalSpectrum B)]`, the
finite-length hypothesis is the owner predicate `IsFiniteLength B M`, and the residue-field degree
is written as `Module.finrank`. -/
theorem length_eq_sum_residueFieldDegree_mul_length_localizedModule
    (hM : IsFiniteLength B M) :
    let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
    Module.length A M =
      ∑ m : MaximalSpectrum B,
        let _ : Module κA (Ideal.ResidueField m.asIdeal) := residueFieldModule hcomap m
        let _ : Module.Finite κA (Ideal.ResidueField m.asIdeal) := hfinitek m
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ENat) *
          Module.length (Localization.AtPrime m.asIdeal) (AtPrime m.asIdeal M) := sorry

-- Proof sketch: apply the semilocal localization formula above. Each summand is finite because the
-- residue-field factor is finite by hypothesis and the localized length is bounded by the original
-- finite `B`-length. A finite sum of finite `ENat` values is finite.
/-- Under the hypotheses of the semilocal localization formula, `M` has finite length over `A`. -/
theorem isFiniteLength_of_finiteLength_over_semilocal
    (hM : IsFiniteLength B M) :
    IsFiniteLength A M := sorry

end ResidueFieldData

end Length
