import Mathlib
import stacks_project.Chap15.Lemma_15_113_4
import stacks_project.Chap15.Lemma_15_113_5

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped Pointwise

universe u v

noncomputable section

section

/- Domain-style sampling for Lemma 15.113.7:
- primary domain: tame inertia characters and the decomposition-group action on the residue field
  in a finite Galois extension over a discrete valuation ring;
- sampled owner declarations:
  `tameInertiaCharacter`,
  `tameInertiaCharacter_ker`,
  `tameInertiaCharacter_surjective`,
  `restrictRootsOfUnity`,
  `MulEquiv.restrictRootsOfUnity`,
  `Ideal.inertia`,
  `MulAction.stabilizer`,
  `IsFractionRing.stabilizerHom`;
- best owner abstraction: the source-facing character owner is already the canonical
  `tameInertiaCharacter K m`, while the genuinely new content of this file is the conjugation
  compatibility with the canonical decomposition-group action on `μ_e(κ(m))` induced from
  `IsFractionRing.stabilizerHom` by `MulEquiv.restrictRootsOfUnity`;
- primitive data: the ideal-theoretic inertia and decomposition groups attached to `m`, together
  with the maximal-ideal specialization of the residue-field action
  `IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField`;
- derived API: the compatibility predicate for a tame inertia character and the existential
  source-facing reformulation obtained by applying it to `tameInertiaCharacter K m`.

Layer triage:
- `source-facing`: the conjugation-compatibility theorem for the canonical tame inertia character
  `tameInertiaCharacter K m`, which is the source character already fixed in Lemma `15.113.5`;
- `core/canonical`: `tameInertiaCharacter K m`, `MulAction.stabilizer Gal(L/K) m`, and
  `m.inertia Gal(L/K)`, together with
  `IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField` and its induced
  `MulEquiv.restrictRootsOfUnity` action on `rootsOfUnity e m.ResidueField`;
- `bridge/view`: the existential source reformulation obtained by packaging the canonical owner
  theorem together with the already established kernel and surjectivity facts from
  Lemma `15.113.5`.

Primitive-vs-derived split:
- primitive data in this file: only the residue-field action of the decomposition group and the
  induced roots-of-unity action of the decomposition group and the compatibility relation with
  conjugation on inertia;
- derived API imported from `15.113.5`: the kernel and surjectivity facts for the canonical tame
  inertia character.

The refinement therefore makes the source-facing numbered item the direct compatibility theorem
for the canonical owner `tameInertiaCharacter K m`, while keeping the existential packaging only
as a derived companion obtained from Lemma `15.113.5`; the compatibility itself is stated directly
against the canonical roots-of-unity action induced from `IsFractionRing.stabilizerHom`. -/

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "κA" => Ideal.ResidueField p

local instance integralClosure_mulSemiringAction :
    MulSemiringAction Gal(L/K) B :=
  IsIntegralClosure.MulSemiringAction A K L B

private theorem integralClosure_smulCommClass :
    SMulCommClass Gal(L/K) A B := sorry

attribute [local instance] integralClosure_smulCommClass

private theorem integralClosure_isInvariant :
    Algebra.IsInvariant A B Gal(L/K) := sorry

attribute [local instance] integralClosure_isInvariant

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

local notation "D" => MulAction.stabilizer Gal(L/K) m
local notation "I" => m.inertia Gal(L/K)
local notation "e" => Ideal.ramificationIdxIn p B

private local instance liesOver_maximalIdeal_of_isMaximal : m.LiesOver p :=
  ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m)).symm⟩

local instance residueFieldAlgebra :
    Algebra κA m.ResidueField :=
  inferInstance

local notation "ρ" => IsFractionRing.stabilizerHom Gal(L/K) p m κA m.ResidueField

/-- Conjugating an inertia element by an element of the decomposition group stays in the inertia
subgroup. -/
-- Proof sketch: the inertia subgroup is normal inside the stabilizer of `m`; apply normality to
-- the subgroup inclusion `I ≤ D` and then rewrite the resulting conjugate back in `Gal(L / K)`.
theorem inertia_conj_mem
    (τ : D) (σ : I) :
    τ.1 * σ.1 * τ.1⁻¹ ∈ I := sorry

/-- Conjugation by the decomposition group induces an endomorphism of the inertia subgroup. -/
abbrev inertiaConj (τ : D) (σ : I) : I :=
  ⟨τ.1 * σ.1 * τ.1⁻¹, inertia_conj_mem m τ σ⟩

-- Proof sketch: this is the source content of Lemma `15.113.7`, stated directly for the canonical
-- tame inertia character already fixed in Lemma `15.113.5`.
/-- Lemma 15.113.7: the canonical tame inertia character from Lemma `15.113.5` is compatible with
conjugation by the decomposition group. -/
theorem tameInertiaCharacter_conj_compatible
    (τ : D) (σ : I) :
    tameInertiaCharacter K m (inertiaConj m τ σ) =
      ((ρ τ).toMulEquiv.restrictRootsOfUnity e) (tameInertiaCharacter K m σ) :=
  sorry

-- Proof sketch: package the canonical owner theorem with the kernel and surjectivity statements
-- already proved in Lemma `15.113.5`.
/-- Companion existential reformulation of Lemma `15.113.7`: the canonical tame inertia character
from Lemma `15.113.5` provides a witness with the expected kernel, surjectivity, and conjugation
compatibility properties. -/
theorem exists_tameInertiaCharacter_conj_compatible_companion :
    ∃ θ : I →* rootsOfUnity e m.ResidueField,
      θ.ker = (wildInertiaSubgroup K m).subgroupOf I ∧
        Function.Surjective θ ∧
        ∀ (τ : D) (σ : I),
          θ (inertiaConj m τ σ) =
            ((ρ τ).toMulEquiv.restrictRootsOfUnity e) (θ σ) := by
  refine ⟨tameInertiaCharacter K m, ?_, tameInertiaCharacter_surjective K m,
    fun τ σ ↦ tameInertiaCharacter_conj_compatible m τ σ⟩
  simpa using tameInertiaCharacter_ker K m

end
