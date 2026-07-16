import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-
Source/core/bridge triage:
* primary domain: Noether normalization for finite-type algebras over a field, localized on a
  basic open neighborhood of a point of `Spec(S)`;
* sampled owner API:
  `topologicalKrullDimAt` and
  `exists_openNhdsOf_topologicalKrullDimAt_eq` from `Definition 5.10.1`,
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether normalization file,
  `ringKrullDim_quotient_mvPolynomial_eq_of_finite_injective_polynomial_algebra` from
  Lemma `10.115.4`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField` from
  Lemma `10.116.3`;
* source-facing: the existence of a basic open neighborhood of `x` whose coordinate ring realizes
  the local dimension at `x` and admits Noether normalization;
* core/canonical: finite injective polynomial-algebra maps and the local-dimension owner formula;
* bridge/view: this lemma specializes those owners to a localization away from one element
  `g ∉ x.asIdeal`.

Primitive data are the basic-open witness `g` and the finite injective algebra map into
`Localization.Away g`. The polynomial source still needs a literal `ℕ` index, so the statement
keeps the minimal witness `d : ℕ` only to record that the canonical owners
`ringKrullDim (Localization.Away g)` and `topologicalKrullDimAt x` are realized by a finite
number of variables.
-/

/-- A witness that `Localization.Away g` realizes the local dimension at `x` and admits a finite
injective Noether normalization by a polynomial ring in `d` variables. -/
structure IsNoetherNormalizationLocalizationAwayAtPoint
    (x : PrimeSpectrum S) (g : S) (d : ℕ)
    (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g) : Prop where
  not_mem_asIdeal : g ∉ x.asIdeal
  ringKrullDim_eq : ringKrullDim (Localization.Away g) = d
  topologicalKrullDimAt_eq : topologicalKrullDimAt x = d
  injective : Function.Injective f
  finite : AlgHom.Finite f

-- Proof sketch: choose a basic open `D(g)` with `g ∉ x.asIdeal` whose dimension equals the local
-- dimension at `x`. Apply Lemma `10.115.4` to a polynomial presentation of `Localization.Away g`.
-- The number of variables is then the canonical owner `ringKrullDim (Localization.Away g)`, and
-- the local-dimension equality identifies this with `topologicalKrullDimAt x`.
/-- Lemma 10.115.5: for a point `x` of `X = Spec(S)`, where `S` is a finite type `k`-algebra,
there exists `g ∉ x.asIdeal` such that the localization `S_g`, formalized as
`Localization.Away g`, has Krull dimension equal to the local dimension at `x`; writing this
common finite value as `d`, there is a finite injective `k`-algebra map from
`MvPolynomial (Fin d) k` to `Localization.Away g`. -/
lemma exists_noether_normalization_localizationAway_at_point (x : PrimeSpectrum S) :
    ∃ (g : S) (d : ℕ) (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g),
      IsNoetherNormalizationLocalizationAwayAtPoint x g d f := sorry

end
