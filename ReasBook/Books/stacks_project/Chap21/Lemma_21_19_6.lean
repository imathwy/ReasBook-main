import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 21.19.6: for a morphism of ringed topoi and a complex `\mathcal K^\bullet`, the square
in `D(\mathcal O_\mathcal C)` built from the comparison `Lf^* \to f^*` on complexes, the
comparison `f_* \to Rf_*` on complexes, the underived counit
`f^* f_* \mathcal K^\bullet \to \mathcal K^\bullet`, and the derived counit
`Lf^* Rf_* \mathcal K^\bullet \to \mathcal K^\bullet` commutes. In canonical mathlib form this is
the generic derived-adjunction counit compatibility
`CategoryTheory.Adjunction.derivedε_fac_app`. -/
recall CategoryTheory.Adjunction.derivedε_fac_app
