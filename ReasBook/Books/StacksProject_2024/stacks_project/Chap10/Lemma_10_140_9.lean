import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Bridge/view: the Stacks-project separability predicate on the induced fraction-field extension
attached to an injective finite-type map of domains. The only non-source-facing data are the
derived faithful action of `R` on `S` and the canonical induced algebra `FractionRing R →
FractionRing S`, both kept internal to this bridge. -/
noncomputable abbrev fractionRingIsSeparableOver
    (hinj : Function.Injective (algebraMap R S)) : Prop :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  let _ : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  IsSeparableOver (FractionRing R) (FractionRing S)

-- Proof sketch: for the forward implication, replace the smooth-at-`(0)` hypothesis by a smooth
-- localization `S_g`, base change along `R → FractionRing R`, and use the field case together with
-- geometric reducedness to deduce that `FractionRing S / FractionRing R` is separable in the
-- Stacks Project sense. For the reverse implication, first localize so the map is of finite
-- presentation, apply smooth-locus base change to the generic fiber over `FractionRing R`, and
-- then use the field criterion from Lemma `10.140.5` at the generic point.
/-- Lemma 10.140.9: let `R → S` be an injective finite type ring map of domains. Then `R → S` is
smooth at the generic point `q = (0)` if and only if the induced extension of fraction fields
`FractionRing S / FractionRing R` is separable in the Stacks Project sense. -/
theorem isSmoothAt_zero_iff_isSeparableOver_fractionRing
    (hinj : Function.Injective (algebraMap R S)) :
    IsSmoothAt R (⊥ : Ideal S) ↔ fractionRingIsSeparableOver hinj := sorry

end

end Algebra
