import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_125_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/-
Domain-style sampling:
- primary domain: relative fiber dimension for finite type algebras over a field, under tensor base
  change along a field extension;
- sampled owner declarations of the same kind:
  `relativeDimensionAt`,
  `fiberLocalRingAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown`;
- best owner abstraction: the source-facing fiber-dimension quantity is already owned in this
  chapter by `relativeDimensionAt`; the ring `fiberLocalRingAt` is primitive supporting data, not
  the public dimension owner;
- primitive data: the points `x : PrimeSpectrum S`, `xK : PrimeSpectrum S_K`, and the contraction
  witness `hxK : PrimeSpectrum.comap iSK xK = x`;
- derived API: the additive identities comparing `relativeDimensionAt S S_K xK` with local-ring
  dimensions and residue-field transcendence degrees.

Source/core/bridge triage:
* `source-facing`: the fiber-dimension formulas and zero-dimensional fiber point over `x`;
* `core/canonical`: `relativeDimensionAt`, together with the supporting owners
  `Localization.AtPrime`, `fiberLocalRingAt`, and the Chapter 10 local-dimension formulas;
* `bridge/view`: the tensor base-change map `iSK` and the lies-over equation
  `PrimeSpectrum.comap iSK xK = x`.
-/

-- Proof sketch: localize the flat base-change map `S → S_K` at `x` and `xK`, then apply the
-- flat-local dimension formula from Lemma `10.112.7` to identify the dimension of the localized
-- special fiber with the difference between the dimensions of `(S_K)_{xK}` and `S_x`. Since the
-- project records Krull dimensions in `WithBot ℕ∞`, this is stated in the equivalent additive
-- form.
/-- Lemma 10.116.7 (1): for a finite type `k`-algebra `S`, a field extension `K / k`, a point
`x : Spec(S)`, and a point `xK : Spec(K ⊗[k] S)` lying over `x`, the relative dimension of
`S_K / S` at `xK`, plus the dimension of `S_x`, equals the dimension of `(K ⊗[k] S)_{xK}`. -/
lemma relativeDimensionAt_add_ringKrullDim_localizationAtPrime_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    relativeDimensionAt S S_K xK + ringKrullDim (Localization.AtPrime x.asIdeal) =
      ringKrullDim (Localization.AtPrime xK.asIdeal) := sorry

-- Proof sketch: combine Lemma `10.116.6`, which identifies the local dimensions of `Spec(S)` and
-- `Spec(S_K)` at corresponding points, with Lemma `10.116.3`, which expresses those local
-- dimensions as `dim S_x + trdeg_k κ(x)` and `dim (S_K)_{xK} + trdeg_K κ(xK)`. Cancelling the
-- local-dimension terms gives the transcendence-degree formula for the fiber dimension, again
-- written in additive form because the dimension values lie in `WithBot ℕ∞`.
/-- Lemma 10.116.7 (2): for a finite type `k`-algebra `S`, a field extension `K / k`, a point
`x : Spec(S)`, and a point `xK : Spec(K ⊗[k] S)` lying over `x`, the relative dimension of
`S_K / S` at `xK`, plus the transcendence degree of `κ(xK)` over `K`, equals the
transcendence degree of `κ(x)` over `k`. -/
lemma relativeDimensionAt_add_trdeg_residueField_eq_of_tensorProduct_fieldExtension
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    relativeDimensionAt S S_K xK + Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

-- Proof sketch: choose a prime of `S_K` minimal over the extended prime `x.asIdeal • ⊤`; such a
-- point lies over `x`, and the corresponding fiber local ring is zero-dimensional because a
-- minimal prime of the fiber has Krull dimension `0`.
/-- Lemma 10.116.7 (3): for every point `x : Spec(S)`, one can choose a point of
`Spec(K ⊗[k] S)` lying over `x` whose relative dimension is `0`. -/
lemma exists_primeSpectrum_tensorProduct_fieldExtension_with_relativeDimensionAt_eq_zero
    (x : PrimeSpectrum S) :
    ∃ xK : PrimeSpectrum S_K,
      PrimeSpectrum.comap iSK xK = x ∧ relativeDimensionAt S S_K xK = 0 := sorry

end
