import Mathlib
import stacks_project.Chap10.Lemma_10_156_2
import stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R Rsh : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
- primary domain: local commutative algebra of strict henselizations and quotients by ideals inside
  the closed point;
- sampled owner declarations: `StrictHenselianLocalRing`, `IsStrictHenselizationOf`,
  `RingHom.IsFilteredColimitOfEtale`, and `IsLocalRing.quotient`;
- best owner abstraction: the quotient theorem should stay source-facing as an
  `IsStrictHenselizationOf` statement, while the local-ring quotient fact is reused from the
  upstream Chapter 10 owner rather than duplicated locally;
- primitive data: the strict henselization owner on `R → Rsh` and the properness hypothesis
  `I ≠ ⊤`;
- derived API: the local-ring structure on `R ⧸ I`.
-/

-- Proof sketch: combine the quotient local-ring lemma from `Lemma 10.156.2` with the strict
-- analogue of the henselization quotient construction. The quotient of a strict henselization
-- remains henselian local with separably closed residue field, and the filtered-colimit-of-étale
-- and maximal-ideal conditions descend through the quotient by `Ideal.map (algebraMap R Rsh) I`.
/-- Lemma 10.156.4: if `Rsh` is a strict henselization of the local ring `R` and `I` is a proper
ideal of `R`, then the quotient `Rsh ⧸ Ideal.map (algebraMap R Rsh) I` is a strict henselization
of the quotient ring `R ⧸ I`. -/
theorem strictHenselization_quotient_isStrictHenselizationOf_quotient
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) := sorry

end
