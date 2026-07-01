import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap15.Lemma_15_113_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

local notation "B" => integralClosure A L

variable (m : Ideal B) [m.IsMaximal]

/- Domain-style sampling for 15.113.5.1:
- primary domain: tame inertia characters in ramification theory for finite Galois extensions of
  fraction fields of discrete valuation rings;
- sampled owner declarations:
  `m.inertia Gal(L/K)`,
  `wildInertiaSubgroup`,
  `tameInertiaQuotient`,
  `tameInertiaQuotientMulEquiv`,
  `tameInertiaCharacter`;
- best owner abstraction: the source-facing tame inertia character
  `tameInertiaCharacter K m`, with the quotient equivalence
  `tameInertiaQuotientMulEquiv K m` as the canonical bridge from the tame inertia quotient;
- primitive data: the inertia group `m.inertia Gal(L/K)`, the tame inertia quotient
  `tameInertiaQuotient K m`, and the residue field `m.ResidueField`;
- derived API: the source-specific formula `σ ↦ \overline{θ_σ}` obtained from the action of
  inertia on a chosen uniformizer of the localization `B_m`.

Layer triage:
- `source-facing`: the textbook formula sending `σ` to the residue class of the unit `θ_σ`
  determined by `σ(π) = θ_σ π` for a chosen uniformizer `π` of `B_m`;
- `core/canonical`: the quotient owner `tameInertiaQuotient K m`;
- `bridge/view`: the canonical quotient equivalence `tameInertiaQuotientMulEquiv K m` and the
  induced tame inertia character `tameInertiaCharacter K m`.

This file should therefore not introduce a second public owner by packaging arbitrary chosen units
in an abstract local ring. The public entry is the chapter-level owner
`tameInertiaCharacter K m`, with the source formula understood as the construction mechanism
behind it. -/

/- 15.113.5.1: choosing a uniformizer `π` of `B_m`, one obtains units `θ_σ` from the inertia
action via `σ(π) = θ_σ π`, and the tame inertia character is the resulting map
`σ ↦ \overline{θ_σ}` into the `e`th roots of unity of `κ(m)`, where
`e = Ideal.ramificationIdxIn (maximalIdeal A) B`. In the chapter API this source-facing map is
recorded by the canonical owner `tameInertiaCharacter K m`, and the quotient equivalence behind
it is recorded by `tameInertiaQuotientMulEquiv K m`. -/
recall tameInertiaCharacter

end
