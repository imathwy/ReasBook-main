import Mathlib
import StacksProject_2024.Chap09.Lemma_9_21_5
import StacksProject_2024.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open IntermediateField

/- Domain-style sampling:
- source-facing owner: `IsUnramifiedWithRespectTo A L` from `Definition_15_112_7`;
- sampled canonical declarations in this domain:
  `IsUnramifiedWithRespectTo`,
  `isUnramifiedAt_of_integralClosure_tower`,
  `normalClosure K L (AlgebraicClosure L)`,
  `isGalois_normalClosure_of_separable`,
  `IntermediateField.finiteDimensional_sup`,
  `IntermediateField.isSeparable_sup`;
- best owner abstraction: the chapter owner `IsUnramifiedWithRespectTo`, with
  the source-facing existential overfield statement as the main theorem for clause `(2)`,
  the canonical Galois-closure field `normalClosure K L (AlgebraicClosure L)` as its preferred
  bridge witness, and `isUnramifiedAt_of_integralClosure_tower` as the canonical bridge from
  branchwise `Algebra.IsUnramifiedAt` data along integral-closure towers;
- primitive-vs-derived split: the finite/separable hypotheses on the bottom extension
  `L / FractionRing A` are primitive because they supply the integral-closure finite-type owner
  needed by `IsUnramifiedWithRespectTo A L`, while the tower hypotheses
  `[FiniteDimensional K L]`, `[FiniteDimensional L M]`, `[Algebra.IsSeparable K L]`, and
  `[Algebra.IsSeparable L M]` canonically derive the corresponding finite/separable structure on
  `M / K`, hence also the `Algebra.EssFiniteType A (integralClosure A M)` owner needed to state
  `IsUnramifiedWithRespectTo A M`; in the theorem surface below, those top-extension instances are
  derived locally from the tower rather than exposed as public binders.

This file is therefore a `bridge/view` layer: its numbered statements remain source-facing
existence theorems, while the canonical tower, normal-closure, and compositum owners serve only as
bridge infrastructure rather than parallel local wrappers.
-/

end

section

open IntermediateField

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

section Tower

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable {M : Type w} [Field M] [Algebra A M] [Algebra (FractionRing A) M] [Algebra L M]
variable [IsScalarTower A (FractionRing A) M] [IsScalarTower (FractionRing A) L M]
variable [FiniteDimensional (FractionRing A) L] [FiniteDimensional L M]
variable [Algebra.IsSeparable (FractionRing A) L] [Algebra.IsSeparable L M]

local notation "K" => FractionRing A

-- Proof sketch: let `B = integralClosure A L` and `C = integralClosure A M`. For a maximal ideal
-- `p : Ideal B` over `maximalIdeal A`, choose a maximal ideal `P : Ideal C` above `p` by lying
-- over. Since `M` is unramified with respect to `A`, the branch `P` is unramified over `A`, so
-- its ramification index over `maximalIdeal A` is `1` and the residue-field extension is
-- separable. Comparing ramification indices in the tower `A ⊆ B ⊆ C` and descending separability
-- along `κ(P) / κ(p) / κA` gives that `p` is unramified over `A`.
/-- Lemma 15.112.8 (1): in a tower `M/L/K` of finite separable extensions over the fraction field
of a discrete valuation ring `A`, unramifiedness with respect to `A` descends from `M` to `L`. -/
theorem isUnramifiedWithRespectTo_of_tower
    (hM : IsUnramifiedWithRespectTo A M) :
    IsUnramifiedWithRespectTo A L := sorry

end Tower

section NormalClosure

variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L]
variable [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]

local notation "K" => FractionRing A
local notation "N" => normalClosure K L (AlgebraicClosure L)

-- Proof sketch: take the canonical normal closure `normalClosure K L (AlgebraicClosure L)`;
-- Lemma `9.21.5` gives its Galois structure over `K`, and the remaining input is the companion
-- bridge that this normal closure is still unramified with respect to `A`.
/-- Companion bridge for Lemma 15.112.8 (2): the canonical normal closure witness inside
`AlgebraicClosure L` is itself unramified with respect to `A`. -/
theorem isUnramifiedWithRespectTo_normalClosure
    (hL : IsUnramifiedWithRespectTo A L) :
    IsUnramifiedWithRespectTo A N := sorry

/-- Lemma 15.112.8 (2): if `L / K` is finite separable and unramified with respect to `A`, then
there exists a finite Galois extension of `K` containing `L` that is still unramified with
respect to `A`. The canonical witness is the normal closure of `L / K` inside
`AlgebraicClosure L`. -/
theorem exists_isGalois_unramifiedWithRespectTo
    (hL : IsUnramifiedWithRespectTo A L) :
    ∃ (M : Type v) (_ : Field M) (_ : Algebra A M) (_ : Algebra K M) (_ : Algebra L M)
      (_ : IsScalarTower A K M),
      IsScalarTower K L M ∧ FiniteDimensional K M ∧ IsGalois K M ∧
        IsUnramifiedWithRespectTo A M := by
  refine ⟨N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact
    ⟨inferInstance, ⟨inferInstance,
      ⟨isGalois_normalClosure_of_separable, isUnramifiedWithRespectTo_normalClosure hL⟩⟩⟩

end NormalClosure

section CommonExtension

variable {L₁ : Type v} [Field L₁] [Algebra A L₁] [Algebra (FractionRing A) L₁]
  [IsScalarTower A (FractionRing A) L₁]
variable {L₂ : Type w} [Field L₂] [Algebra A L₂] [Algebra (FractionRing A) L₂]
  [IsScalarTower A (FractionRing A) L₂]
variable [FiniteDimensional (FractionRing A) L₁] [FiniteDimensional (FractionRing A) L₂]
variable [Algebra.IsSeparable (FractionRing A) L₁] [Algebra.IsSeparable (FractionRing A) L₂]

local notation "K" => FractionRing A

-- Proof sketch: embed both fields into a common normal closure and then pass to the compositum of
-- their images; `IntermediateField.finiteDimensional_sup` and
-- `IntermediateField.isSeparable_sup` provide the canonical finite/separable overfield owner.
/-- Lemma 15.112.8 (3): two finite separable extensions of `K` that are unramified with respect to
`A` embed in a common finite separable extension that is unramified with respect to `A`. -/
theorem exists_common_unramifiedWithRespectTo_extension
    (hL₁ : IsUnramifiedWithRespectTo A L₁) (hL₂ : IsUnramifiedWithRespectTo A L₂) :
    ∃ (L : Type (max v w)) (_ : Field L) (_ : Algebra A L) (_ : Algebra K L)
      (_ : Algebra L₁ L) (_ : Algebra L₂ L) (_ : IsScalarTower A K L),
      IsScalarTower K L₁ L ∧ IsScalarTower K L₂ L ∧
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
        IsUnramifiedWithRespectTo A L := sorry

end CommonExtension

end
