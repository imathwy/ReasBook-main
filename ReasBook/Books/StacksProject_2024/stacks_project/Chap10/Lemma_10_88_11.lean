import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section RestrictScalars

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S] [Algebra.FinitePresentation R S]

/- Source/core/bridge triage:
* source-facing: the restriction-of-scalars stability statement from Lemma `10.88.11`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: viewing an `S`-module as an `R`-module along `R → S`.
-/
-- Proof sketch: choose a directed colimit presentation of `M` by finitely presented `S`-modules
-- with the eventual factorization property from `Module.MittagLeffler S M`. By Lemma `10.36.23`,
-- each stage is also finitely presented over `R`, and the same transition maps and factorization
-- identities remain valid after restriction of scalars, yielding a Mittag-Leffler presentation
-- over `R`.
/-- Lemma 10.88.11: if `R → S` is finite and finitely presented, then every Mittag-Leffler
`S`-module is Mittag-Leffler when viewed as an `R`-module by restriction of scalars. -/
theorem mittagLeffler_restrictScalars_of_finite_finitePresentation [MittagLeffler S M] :
    MittagLeffler R M := sorry

end RestrictScalars

end Module
