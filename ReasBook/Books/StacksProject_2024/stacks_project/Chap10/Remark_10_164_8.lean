import Mathlib
import StacksProject_2024.Chap10.Lemma_10_105_9
import StacksProject_2024.Chap10.Lemma_10_106_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-
Domain-style sampling:
- primary domain: universal catenarity and its failure to descend along local étale maps in
  commutative algebra;
- sampled owner declarations:
  `UniversallyCatenaryRing`,
  `CohenMacaulayRing`,
  `universallyCatenaryRing_of_cohenMacaulayRing`,
  `regularLocalRing_selfModule_cohenMacaulay`;
- best owner abstraction: the ring-level owner `UniversallyCatenaryRing`;
- primitive vs. derived: the source-facing content here is only the existential counterexample,
  while the universally catenary owner and the Cohen-Macaulay bridge are upstream canonical API
  that this remark may reference but should not duplicate with extra owner-level specializations.
-/

-- Proof sketch: use the finite unramified counterexample `A → B` from Examples, Section 110.19
-- together with Lemma `10.152.3` to pass to a local étale extension `A → A'` for which
-- `B ⊗[A] A'` splits into two surjective factors. The resulting minimal-prime quotients of `A'`
-- are regular local rings, hence universally catenary, and Lemma `10.105.8` then gives that `A'`
-- is universally catenary while `A` is not.
/-- Remark 10.164.8: universal catenarity does not descend, even along local étale ring maps. In
particular, there exist a Noetherian local ring `A` and a local étale `A`-algebra `A'` such that
`A'` is universally catenary but `A` is not. -/
theorem exists_local_etale_counterexample_to_universallyCatenary_descent :
    ∃ (A : Type u) (A' : Type u),
      ∃ (_ : CommRing A) (_ : CommRing A') (_ : IsLocalRing A) (_ : IsLocalRing A')
        (_ : IsNoetherianRing A) (_ : Algebra A A') (_ : IsLocalHom (algebraMap A A'))
        (_ : Algebra.Etale A A') (_ : UniversallyCatenaryRing A'),
        ¬ UniversallyCatenaryRing A := sorry

end
