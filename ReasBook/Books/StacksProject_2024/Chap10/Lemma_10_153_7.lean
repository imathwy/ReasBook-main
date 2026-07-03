import Mathlib
import StacksProject_2024.Chap15.Lemma_15_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R]

/- Domain-style sampling:
- primary domain: finite étale algebras and reduction modulo an ideal;
- sampled owner declarations:
  `finiteEtaleAlgebraProperty`,
  `finiteEtaleAlgebras`,
  `quotientCommAlgFunctor`,
  `quotientFiniteEtaleAlgebraFunctor`,
  `quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing`;
- best owner abstraction: the canonical ambient owner is `CommAlgCat A`, with the finite étale
  category realized as the full subcategory `finiteEtaleAlgebras A` and the reduction functor as
  the restriction of the Chapter 15 owner `quotientCommAlgFunctor`;
- primitive data vs. derived API: the primitive data is an object of `CommAlgCat A` together with
  finiteness and étaleness, while the Chapter 10 "special fiber" construction is only the
  specialization `I = maximalIdeal R`, hence a bridge/view rather than a second owner.

Source/core/bridge triage:
- `source-facing`: Lemma 10.153.7, phrased as the special-fiber equivalence for a henselian local
  ring;
- `core/canonical`: Chapter 15's quotient reduction functor modulo an ideal and its henselian-pair
  equivalence theorem;
- `bridge/view`: the specialization `I = maximalIdeal R`, with `R ⧸ maximalIdeal R`
  definitionally equal to `ResidueField R`.
-/

variable [HenselianLocalRing R]

/-- Lemma 10.153.7: for a henselian local ring `R`, the special-fiber functor
`S ↦ S / maximalIdeal R • S`, formalized by base change to `ResidueField R`, is an equivalence
from the category of finite étale extensions of `R` to the category of finite étale algebras over
`ResidueField R`. -/
theorem finiteEtaleSpecialFiberFunctor_isEquivalence_of_henselianLocalRing :
    Functor.IsEquivalence (quotientFiniteEtaleAlgebraFunctor (maximalIdeal R)) := by
  simpa using quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing (maximalIdeal R)

end
