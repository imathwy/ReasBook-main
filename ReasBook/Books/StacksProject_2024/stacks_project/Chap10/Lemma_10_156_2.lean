import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and quotient rings at the closed
  point;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `Ideal.Quotient.nontrivial`,
  `isLocalHom_of_le_jacobson_bot`,
  `IsLocalRing.le_maximalIdeal`,
  `IsLocalRing.of_surjective'`;
- best owner abstraction: the main result stays source-facing as a quotient theorem for the owner
  `IsHenselizationOf`, while the local-ring structure on `R ⧸ I` is derived API belonging under
  the owner namespace `IsLocalRing`;
- primitive data: the henselization owner on `R → Rh` and the properness hypothesis `I ≠ ⊤`;
- derived API: the induced local-ring structure on `R ⧸ I` and the inclusion
  `I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI`.

Source/core/bridge triage:
- `source-facing`: `henselization_quotient_isHenselizationOf_quotient`;
- `core/canonical`: `IsHenselizationOf`, `HenselianLocalRing`, `IsLocalHom`;
- `bridge/view`: `IsLocalRing.quotient`.
-/

namespace IsLocalRing

-- Proof sketch: if `I ≠ ⊤`, then `R ⧸ I` is nontrivial by `Ideal.Quotient.nontrivial`; the
-- quotient map `R → R ⧸ I` is surjective, so `IsLocalRing.of_surjective'` transports the
-- local-ring structure.
/-- The quotient of a local ring by a proper ideal is again a local ring. -/
theorem quotient (I : Ideal R) (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) := by
  let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

end IsLocalRing

end

section

variable {R Rh : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- Proof sketch: apply the quotient case of the henselization comparison from Lemma `10.156.1` to
-- the surjective local map `R → R ⧸ I`. The quotient `Rh ⧸ Ideal.map (algebraMap R Rh) I`
-- inherits the filtered-colimit-of-étale, local, maximal-ideal, and residue-field conditions, so
-- it is a henselization of `R ⧸ I`.
/-- Lemma 10.156.2: if `Rh` is a henselization of the local ring `R` and `I` is a proper ideal of
`R` (equivalently, in a local ring, `I ⊆ maximalIdeal R`), then the quotient
`Rh ⧸ Ideal.map (algebraMap R Rh) I` is a henselization of the quotient ring `R ⧸ I`. -/
theorem henselization_quotient_isHenselizationOf_quotient
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    IsHenselizationOf (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) := sorry

end
