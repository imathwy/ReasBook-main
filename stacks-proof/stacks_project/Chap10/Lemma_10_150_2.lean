import Mathlib.RingTheory.Etale.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
- primary domain: formal etaleness of commutative algebras and tensor-product base change;
- sampled owner API:
  `Algebra.FormallyEtale`,
  `Algebra.FormallyEtale.iff_comp_bijective`,
  `Algebra.FormallyEtale.of_isLocalization`,
  `Algebra.FormallyEtale.instTensorProduct`;
- source-facing: the textbook base-change lemma for formally étale maps;
- core/canonical: the mathlib owner class `Algebra.FormallyEtale`;
- bridge/view: none; the source statement is exactly the owner-level tensor-product base-change
  instance.

Primitive data are only the commutative rings, algebra structures, and the input formally étale
hypothesis. The formally étale structure on the base-changed algebra is derived API owned upstream
by `Algebra.FormallyEtale.instTensorProduct`, so this file should recall that owner instance
directly and not keep a parallel local wrapper.
-/

/- Lemma 10.150.2: if `R → S` is formally étale, then for any ring map `R → R'`, the base
change `R' ⊗[R] S` is formally étale over `R'`. This is exactly the canonical tensor-product
base-change instance `Algebra.FormallyEtale.instTensorProduct`. -/
recall Algebra.FormallyEtale.instTensorProduct
