import stacks_project.Chap15.Definition_15_112_7
import stacks_project.Chap15.Lemma_15_112_9
import stacks_project.Chap15.Lemma_15_112_3
import stacks_project.Chap15.Lemma_15_115_6

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing Algebra

universe u v w

section

variable {A : Type u} {L : Type v} {M : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L]
variable [Algebra.IsSeparable (FractionRing A) L]
variable [Field M] [Algebra A M] [Algebra L M] [Algebra (FractionRing A) M]
variable [IsScalarTower A L M] [IsScalarTower A (FractionRing A) M]
variable [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional L M]
variable [Algebra.IsSeparable L M]

local notation "B" => integralClosure A L
local notation "C" => integralClosure A M
local notation "κA" => Ideal.ResidueField (maximalIdeal A)

/-- The canonical map `B → C` on integral closures induced by the tower map `L → M`. -/
private noncomputable abbrev integralClosureTowerMap : B →ₐ[A] C :=
  (IsScalarTower.toAlgHom A L M).mapIntegralClosure

noncomputable local instance : Algebra B C :=
  integralClosureTowerMap.toAlgebra

local instance : IsScalarTower A B C := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  ext
  simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A L M]

private instance liesOver_maximalIdeal_base (p : Ideal B) [p.IsMaximal] :
    p.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p)).symm⟩

private instance liesOver_maximalIdeal_top (P : Ideal C) [P.IsMaximal] :
    P.LiesOver (maximalIdeal A) :=
  ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩

/- Domain-style sampling for tame ramification in an integral-closure tower:
- primary domain: ramification theory for finite separable extensions over a discrete valuation
  ring, measured on maximal ideals of integral closures;
- owner abstraction: `IsTamelyRamifiedWithRespectTo A L` from
  `Definition_15_112_7`, together with the tower bridge for `Ideal.ramificationIdx` from
  `Lemma_15_112_3`;
- source/core/bridge triage: this file is a `bridge/view` statement, lifting primitive local tame
  branch data on `B ⊆ C` to the global owner on `A ⊆ M`;
- primitive data: for each maximal branch `P` of `C`, the intermediate branch ideal is
  canonically `P.under B`; the primitive local data are that the residue-field extension
  `(P.under B).ResidueField ⊂ P.ResidueField` is separable and the relative ramification index
  `ramificationIdx (P.under B) P` is prime to the residue characteristic of `(P.under B).ResidueField`.

This local branch data is primitive theorem input, not a second packaged owner. -/

-- Proof sketch: for a maximal ideal `P` of `C`, let `p = P ∩ B`. The
-- assumption on `L/K` gives tameness of `p` over `A`, and the assumption on `M/L` gives tameness
-- of `P` over `p`. Use the tower `κ(P)/κ(p)/κA` for separability of residue fields and Lemma
-- `15.112.3` for multiplicativity of ramification indices to conclude that the ramification index
-- of `P` over `A` is still prime to the residue characteristic.
/-- Lemma 15.115.5: let `A` be a discrete valuation ring with fraction field `FractionRing A`, let
`L / FractionRing A` and `M / L` be finite separable extensions, and let `B = integralClosure A L`.
If `L / FractionRing A` is tamely ramified with respect to `A`, and for every maximal ideal
`P : Ideal C` the canonical intermediate branch ideal `P.under B` induces a tame extension on the
localized step `B_(P ∩ B) ⊂ C_P`, then `M / FractionRing A` is tamely ramified with respect to
`A`; the branchwise `LiesOver (maximalIdeal A)` conditions are supplied canonically because every
maximal ideal of an integral closure over the discrete valuation ring `A` contracts to
`maximalIdeal A`. -/
theorem isTamelyRamifiedWithRespectTo_of_tame_of_forall_tame_over_integralClosure
    (hL : IsTamelyRamifiedWithRespectTo A L)
    (hM_sep : ∀ (P : Ideal C) [P.IsMaximal],
      Algebra.IsSeparable (P.under B).ResidueField P.ResidueField)
    (hM_coprime : ∀ (P : Ideal C) [P.IsMaximal]
      (q : ℕ) [Fact q.Prime] [CharP (P.under B).ResidueField q],
        Nat.Coprime (ramificationIdx (P.under B) P) q) :
    IsTamelyRamifiedWithRespectTo A M := by
  let _ : FiniteDimensional (FractionRing A) M :=
    FiniteDimensional.trans (FractionRing A) L M
  let _ : Algebra.IsSeparable (FractionRing A) M :=
    Algebra.IsSeparable.trans (FractionRing A) L M
  sorry

end
