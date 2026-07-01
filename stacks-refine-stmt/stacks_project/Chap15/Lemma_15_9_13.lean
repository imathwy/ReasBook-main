import Mathlib
import stacks_project.Chap10.Lemma_10_78_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]

/- Domain triage:
- primary domain: smooth commutative algebra maps and symmetric algebras;
- sampled owner declarations:
  `Algebra.Smooth`,
  `SymmetricAlgebra`,
  `SymmetricAlgebra.algebraMapInv`,
  `Module.FiniteProjective`;
- best owner abstraction: the source-facing statement should use the canonical smoothness owner
  `Algebra.Smooth A (SymmetricAlgebra A M)` and the project-level finite-projective owner
  `Module.FiniteProjective A M`;
- primitive data: the base ring `A` and the `A`-module `M`;
- derived API: the smoothness criterion for the symmetric algebra.

Source/core/bridge triage:
- `source-facing`: the smoothness criterion for `Sym_A^*(M)`;
- `core/canonical`: `Algebra.Smooth`, `SymmetricAlgebra`, and `Module.FiniteProjective`;
- `bridge/view`: the proof sketch passes through the augmentation
  `SymmetricAlgebra.algebraMapInv` and the conormal computation of Lemma `15.9.12`. -/

-- Proof sketch: for the forward implication, use the augmentation
-- `SymmetricAlgebra.algebraMapInv : SymmetricAlgebra A M →ₐ[A] A` and Lemma `10.139.4` to identify
-- the conormal module of its kernel with `M`, since the positive-degree ideal modulo its square is
-- the degree-one piece. For the reverse implication, choose a finite free presentation of the
-- finite projective module `M`, apply the conormal-sequence computation of Lemma `15.9.12`, and
-- conclude from the characterization of smoothness in Definition `10.137.1`.
/-- Lemma 15.9.13: the symmetric algebra `Sym_A^*(M)` is smooth over `A` if and only if `M` is a
finite `A`-module and a projective `A`-module. -/
theorem smooth_symmetricAlgebra_iff_finite_and_projective :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔
      Module.FiniteProjective A M := sorry

end
