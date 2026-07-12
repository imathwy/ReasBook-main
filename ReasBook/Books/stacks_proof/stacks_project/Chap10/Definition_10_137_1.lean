import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
- primary domain: smooth commutative algebra maps and their cotangent-theoretic consequences;
- sampled owner declarations:
  `Algebra.Smooth`,
  `Algebra.Smooth.finitePresentation`,
  `Algebra.FormallySmooth.subsingleton_h1Cotangent`,
  `KaehlerDifferential.finite`;
- best owner abstraction: `Algebra.Smooth R S`;
- primitive data: the smoothness owner instance on the `R`-algebra `S`;
- derived API: finite presentation of `S`, vanishing of `H¹(L_{S/R})`, and projective/finite
  Kähler differentials.

This file is therefore a `core/canonical` recall file: it should reuse the owner declarations
directly and avoid any parallel local smoothness wrapper.
-/
/- Definition 10.137.1: a ring map `R → S` is smooth when the corresponding `R`-algebra `S` is
smooth, i.e. of finite presentation and with naive cotangent complex quasi-isomorphic to a finite
projective module concentrated in degree `0`. -/
recall Smooth

/- Smooth algebras are finitely presented over the base ring. -/
recall Smooth.finitePresentation

/- Smooth `R`-algebras have vanishing first homology of the naive cotangent complex. -/
recall FormallySmooth.subsingleton_h1Cotangent

/- Smooth `R`-algebras have projective Kähler differentials. -/
recall FormallySmooth.projective_kaehlerDifferential

section

variable [Smooth R S]

/- Smooth `R`-algebras have finite Kähler differentials. -/
recall KaehlerDifferential.finite

end

end Algebra
