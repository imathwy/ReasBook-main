import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap08.Lemma_8_3_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Definition 8.3.4:
- primary domain: pullback functoriality on descent data for morphisms of fixed-target families in
  a fibred category;
- sampled owner abstractions:
  `Pseudofunctor.DescentData.pullFunctor`,
  `Pseudofunctor.DescentData.pullFunctorIso`,
  `Pseudofunctor.DescentData'.descentDataEquivalence`,
  `pullbackFamilyDescentFunctor` from 8.3.3;
- source-facing layer: pullback on descent data attached to a morphism of fixed-target families
  over a base map;
- core/canonical owner: `Pseudofunctor.DescentData.pullFunctor`;
- bridge/view layer: `pullbackFamilyDescentFunctor`, the chapter specialization through
  `DescentDatum p hc 𝒰`.

Primitive data are the two fixed-target families and a morphism between them over a base arrow.
The induced pullback functor and its same-base comparison isomorphism are derived owner-level API,
so this file should remain a pure recall surface rather than introducing a parallel wrapper.
-/

/- Definition 8.3.4: with `𝒰 = {U_i ⟶ U}_{i ∈ I}`, `𝒱 = {V_j ⟶ V}_{j ∈ J}`, an index map
`α : I → J`, a base morphism `h : U ⟶ V`, and component maps `g_i : U_i ⟶ V_{α(i)}` as in Lemma
8.3.3, the functor
`(Y_j, \varphi_{jj'}) ↦ (g_i^* Y_{α(i)}, (g_i × g_{i'})^* \varphi_{α(i)α(i')})`
constructed there is the pullback functor on descent data. -/
recall pullbackFamilyDescentFunctor

/- Companion recall: if two morphisms of fixed-target families have the same base map, then the
resulting pullback functors on descent data are canonically isomorphic. This is the source-text
reason one may write `h^*` when the chosen lift of `h` is irrelevant. -/
recall pullbackFamilyDescentFunctorIso

end CategoryTheory
