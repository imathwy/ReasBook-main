import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/- Domain triage:
* primary domain: homological algebra of `Ext` groups in `ModuleCat` over a Noetherian ring;
* sampled owner-style declarations in this domain: `CategoryTheory.Abelian.Ext.addEquiv₀`,
  `CategoryTheory.Abelian.Ext.linearEquiv₀`, `CategoryTheory.ModuleCat.homLinearEquiv`, and the
  finiteness owner instance `ModuleCat.finite_ext`;
* source-facing layer: finiteness of the canonical `Ext` module `Ext^i_R(M, N)` for finite
  modules over a Noetherian ring;
* core/canonical owner abstraction: the typeclass instance `ModuleCat.finite_ext`, which supplies
  `Module.Finite R (Ext (ModuleCat.of R M) (ModuleCat.of R N) i)` directly;
* bridge/view layer: none, because the source statement is already expressed on the canonical
  owner object;
* primitive data: the ring, the two finite module objects, and the Ext degree `i`;
* derived API: finiteness of the Ext module by ordinary typeclass inference.

This item is therefore `core/canonical`: there is no additional source-defined data to package, so
the correct refinement is direct recall of the owner instance rather than a parallel local theorem.
-/

/- Lemma 10.71.9: for a Noetherian ring `R` and finite `R`-modules `M` and `N`, the module
`Ext^i_R(M, N)` is finite for every `i`. This is exactly the canonical owner instance
`ModuleCat.finite_ext`. -/
recall ModuleCat.finite_ext

end
