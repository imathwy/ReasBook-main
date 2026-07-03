import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Polynomial

universe u

namespace Polynomial

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
* primary domain: splitting monic polynomials after finite flat base change in commutative algebra;
* sampled owner declarations:
  `Polynomial.Monic.exists_splits_map`,
  `Polynomial.Splits`,
  `Polynomial.Splits.eq_prod_roots_of_monic`,
  `RingHom.Syntomic`;
* best owner abstraction:
  the extension itself remains source-facing existential data, while the splitting conclusion
  should use the canonical owner `Polynomial.Splits`; the explicit linear-factor product is
  derived API from that owner for monic polynomials;
* primitive vs. derived:
  primitive data are the extension ring `A'` and its syntomic / finite free / faithfully flat
  structure over `A`; a chosen family of roots indexed by `Fin P.natDegree` is derived packaging
  and should not be primitive public output.
-/

-- Proof sketch: base change the universal elementary-symmetric factorization ring of Example
-- `10.136.8` along the map sending the elementary-symmetric coefficients to the coefficients of
-- `P`. The resulting algebra is finite free and faithfully flat by base change, and it is
-- syntomic by Lemma `10.136.13`. Its tautological roots show that
-- `P.map (algebraMap A A')` splits; the explicit linear-factor product is then derived from the
-- canonical owner lemma `Polynomial.Splits.eq_prod_roots_of_monic`.
/-- Lemma 10.136.14: a monic polynomial over `A` splits after a syntomic finite free faithfully
flat extension of `A`. -/
theorem exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic
    (P : A[X]) (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : (algebraMap A A').Syntomic)
      (_ : Module.Free A A') (_ : Module.Finite A A')
      (_ : (algebraMap A A').FaithfullyFlat),
      (P.map (algebraMap A A')).Splits := sorry

end

end Polynomial
