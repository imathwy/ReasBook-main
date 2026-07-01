import stacks_project.Chap19.Lemma_19_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

namespace CochainComplex

/-
Domain-style sampling for Lemma 19.12.5:
- primary domain: functorial cochain-complex approximations in a Grothendieck abelian category,
  upgraded by degreewise factorization through injective subobjects;
- sampled owner declarations:
  `FunctorialComplexApproximation`,
  `HasFunctorialInjectiveEmbeddings`,
  `HasFunctorialInjectiveEmbeddings.under`,
  `InjectivePresentation`,
  `Subobject.Factors`;
- best owner abstraction: the core owner remains `FunctorialComplexApproximation C` from
  Lemma 19.12.4, while the injective-subobject factorization is derived theorem-level data about
  its degreewise comparison maps rather than a second packaged owner;
- primitive data: a functorial complex approximation;
- derived API: for each degreewise component `(J.ι.app M).f n`, an injective subobject of
  `(J.toFunctor.obj M).X n` together with the canonical factorization property
  `I.Factors ((J.ι.app M).f n)`.

Source/core/bridge triage:
- `source-facing`: the existence statement that the comparison maps factor through injective
  subobjects degreewise;
- `core/canonical`: `FunctorialComplexApproximation C`;
- `bridge/view`: the degreewise factorization witnesses for the comparison morphism.
-/

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Lemma 19.12.5: in a Grothendieck abelian category there exists a functorial cochain-complex
replacement `M ↦ N(M)` together with a natural map `j_M : M ⟶ N(M)` that is termwise injective
and a quasi-isomorphism, and whose degreewise components factor through injective subobjects of the
corresponding terms of `N(M)` in the canonical `Subobject.Factors` sense. -/
-- Proof sketch: apply Theorem 19.11.7 termwise to obtain functorial monomorphisms
-- `Mⁿ ⟶ I(Mⁿ)`, assemble these into the standard auxiliary complex `J(M)`, and form the shifted
-- mapping cone of the quotient map `J(M) ⟶ Q(M)`. The induced map `j_M : M ⟶ N(M)` is termwise
-- mono, each component lands in an injective subobject by construction, and the long exact
-- cohomology sequence for the defining short exact sequence gives that `j_M` is a quasi-isomorphism.
theorem exists_functorial_injective_subobject_complex_approximation :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (M : CochainComplex C ℤ) (n : ℤ),
        ∃ I : Subobject ((J.toFunctor.obj M).X n),
          Injective (I : C) ∧ I.Factors ((J.ι.app M).f n) := sorry

end CochainComplex
