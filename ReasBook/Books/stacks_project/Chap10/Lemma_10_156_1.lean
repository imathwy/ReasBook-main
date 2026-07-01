import Mathlib
import stacks_project.Chap10.Lemma_10_153_4
import stacks_project.Chap10.Lemma_10_154_7
import stacks_project.Chap10.Lemma_10_155_8

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u

noncomputable section

/-
Lemma 10.156.1 (1): this is the owner-level henselization statement already proved in
Lemma `10.155.8` for the canonical local map between localizations. The present file uses that
source-facing statement directly rather than keeping a parallel local alias.
-/
recall isHenselizationOf_localizationAt_henselizationTensorPrime

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable {Rph Sqh : Type u} [CommRing Rph] [CommRing Sqh]
variable [Algebra (Localization.AtPrime p) Rph]
variable [IsHenselizationOf (Localization.AtPrime p) Rph]
variable [Algebra (Localization.AtPrime q) Sqh]
variable [IsHenselizationOf (Localization.AtPrime q) Sqh]

local notation "Rp" => Localization.AtPrime p
local notation "Sq" => Localization.AtPrime q

noncomputable local instance : Algebra Rp Sq :=
  (Localization.localRingHom p q (algebraMap R S) (Ideal.over_def q p)).toAlgebra

local instance : IsLocalHom (algebraMap Rp Sq) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom p q (algebraMap R S) (Ideal.over_def q p)

local notation "comparison" =>
  @henselizationMapRingHom Rp Rph Sqh _ _ _ _ _ _ Sq _ _ _ _ _ _

/- Domain-style sampling:
- primary domain: local commutative algebra of henselizations along the canonical local map
  `Localization.AtPrime p → Localization.AtPrime q`;
- sampled owner declarations of the same kind:
  `Algebra.FiniteType.QuasiFiniteAt`,
  `IsHenselizationOf`,
  `henselizationMap`,
  `moduleFinite_localizationAtPrime_of_quasiFiniteAt_over_maximalIdeal`,
  `henselizationTensorPrime`,
  `isHenselizationOf_localizationAt_henselizationTensorPrime`;
- best owner abstraction: this file is a `bridge/view` refinement over the owner layer
  `IsHenselizationOf`, while the source-facing quasi-finite input remains
  `Algebra.FiniteType.QuasiFiniteAt R S q`; the `Rₚ`-algebra structure and tower on `Sqh` must be
  derived internally from the canonical local map `Rₚ → S_q → S_q^h`, while the comparison
  `Rₚ^h → S_q^h` itself must be the canonical owner map `henselizationMap`;
- primitive data: the henselization owners on `R_p` and `S_q`, the canonical local map
  `R_p → S_q`, and the source-facing quasi-finite package at `q`;
- derived API: the canonical comparison `henselizationMap : R_p^h → S_q^h`, its finiteness
  property, and the tensor-localization owner theorem already provided upstream by Lemma
  `10.155.8`.

Source/core/bridge triage:
- `source-facing`: the quasi-finite finiteness of the induced map `R_p^h → S_q^h`;
- `core/canonical`: `IsHenselizationOf`, `henselizationMap`, and
  `isHenselizationOf_localizationAt_henselizationTensorPrime`;
- `bridge/view`: the canonical comparison morphism `henselizationMap`.
-/

-- Proof sketch: after identifying `S_q^h` with the localization of `R_p^h ⊗[R_p] S_q` from
-- clause (1), apply the quasi-finite finiteness statement over the henselian base `R_p^h` to that
-- localization and then use the canonical identification of `S_q^h` with its localization at the
-- maximal ideal.
/-- Lemma 10.156.1 (2): under the same quasi-finite hypothesis at `q`, the canonical comparison map
`R_p^h → S_q^h` given by `henselizationMap` is finite. -/
theorem henselizationMap_finite_of_quasiFiniteAt
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    RingHom.Finite comparison := by
  sorry

end
