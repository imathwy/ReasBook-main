import Mathlib
import stacks_project.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `cohenMacaulay_iff_restrictScalars_of_surjective`, the textbook invariance of the
  Cohen-Macaulay condition under a surjective local map;
* core/canonical: the owner class `Module.CohenMacaulay`;
* bridge/view: `Module.CohenMacaulay.of_surjective`, the forward transport used when the owner
  instance over `S` is already available.

Primitive data are the surjective algebra map and the owner class itself. Finiteness over `R`
belongs to the derived API, obtained canonically from finiteness over `S` by restricting scalars,
rather than being packaged as separate primitive data in this file.
-/

-- Proof sketch: identify `S` with a quotient of `R` using surjectivity of `algebraMap R S`.
-- Under restriction of scalars, the maximal ideal of `S` is the image of the maximal ideal of
-- `R`, and both the depth and the support dimension of `N` are unchanged by passage to this
-- quotient presentation. Therefore the defining equality for Cohen-Macaulay modules is equivalent
-- over `S` and over `R`.
/-- Lemma 10.103.6: for a surjective homomorphism `R → S` of Noetherian local rings and a finite
`S`-module `N`, the module `N` is Cohen-Macaulay over `S` if and only if it is
Cohen-Macaulay over `R` via restriction of scalars. -/
theorem cohenMacaulay_iff_restrictScalars_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) :
    CohenMacaulay S N ↔ CohenMacaulay R N := sorry

namespace CohenMacaulay

/-- Restricting scalars along a surjective local ring map preserves the Cohen-Macaulay property. -/
theorem of_surjective (hsurj : Function.Surjective (algebraMap R S)) [CohenMacaulay S N] :
    CohenMacaulay R N :=
  (cohenMacaulay_iff_restrictScalars_of_surjective hsurj).1 ‹_›

end CohenMacaulay

end Module

end
