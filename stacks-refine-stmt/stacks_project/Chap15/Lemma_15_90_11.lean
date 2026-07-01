import stacks_project.Chap15.Remark_15_90_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)

/- Domain-style sampling:
- primary domain: categorical formal glueing for module categories;
- sampled owner declarations:
  `CategoryTheory.Adjunction`,
  `FormalGlueingDatum`,
  `formalGlueingCan`,
  `formalGlueingH0`,
  `Functor.IsLeftAdjoint`;
- best owner abstraction: the source-facing adjunction
  `formalGlueingCan S f ⊣ formalGlueingH0 S f`;
- primitive data: the canonical functors `formalGlueingCan S f` and `formalGlueingH0 S f`;
- derived API: the left/right adjoint typeclass instances used by downstream generic categorical
  lemmas.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCanAdjunction`;
- `core/canonical`: `CategoryTheory.Adjunction`;
- `bridge/view`: the derived adjointness instances below for typeclass-driven reuse.
-/

-- Proof sketch: Remark `15.90.10` already defines the canonical source-facing right adjoint
-- `formalGlueingH0 S f`, so the lemma should expose the actual adjunction
-- `formalGlueingCan S f ⊣ formalGlueingH0 S f`. The proposition-level `IsLeftAdjoint` and
-- `IsRightAdjoint` owners are then derived consequences for downstream typeclass-driven reuse.
/-- Lemma 15.90.11: for the genuine formal glueing category `Glue(R → S, f₁, \ldots, fₜ)` from
Remark `15.90.10`, the canonical functor `Can` is left adjoint to the degree-zero functor
`H^0`. -/
noncomputable def formalGlueingCanAdjunction :
    formalGlueingCan S f ⊣ formalGlueingH0 S f := by
  sorry

noncomputable instance : (formalGlueingCan S f).IsLeftAdjoint :=
  (formalGlueingCanAdjunction f).isLeftAdjoint

noncomputable instance : (formalGlueingH0 S f).IsRightAdjoint :=
  (formalGlueingCanAdjunction f).isRightAdjoint

end
