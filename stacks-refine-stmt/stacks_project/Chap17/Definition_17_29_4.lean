import Mathlib
import stacks_project.Chap17.Lemma_17_29_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat.Sheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {𝒪₁ 𝒪₂ : TopCat.Sheaf CommRingCat.{u} X} (varphi : 𝒪₁ ⟶ 𝒪₂)
variable (ℱ : SheafOfModules (ringSheaf 𝒪₂))
variable (k : ℕ)

/- Domain-style sampling for Definition 17.29.4:
- primary domain: sheaf-level principal parts and differential operators relative to
  `𝒪₁ ⟶ 𝒪₂`;
- sampled owner declarations:
  `Functor.CorepresentableBy`,
  `differentialOperatorsFunctor`,
  `exists_principal_parts_of_order`,
  `principal_parts_linear_map_equiv_differential_operators`;
- best owner abstraction: the specialized canonical owner
  `(differentialOperatorsFunctor varphi ℱ k).CorepresentableBy`.

Primitive-vs-derived split:
- primitive data here: none beyond the already defined differential-operator functor;
- derived API: existence of a corepresenting sheaf, already supplied by
  `exists_principal_parts_of_order`.

Source/core/bridge triage:
- `source-facing`: the phrase “`P` is a module of principal parts of order `k` of `ℱ`”;
- `core/canonical`: `(differentialOperatorsFunctor varphi ℱ k).CorepresentableBy`;
- `bridge/view`: the existence theorem in Lemma `17.29.3`.

This numbered definition is recall-only, so the file should use the canonical owner directly and
not keep a second existence theorem with the same interface under a new local name.
-/
/- Definition 17.29.4: a sheaf of `\mathcal O_2`-modules is a module of principal parts of order
`k` of `\mathcal F` relative to `\mathcal O_1 \to \mathcal O_2` precisely when it
corepresents the functor of differential operators of order `k` out of `\mathcal F`. -/
#check (differentialOperatorsFunctor varphi ℱ k).CorepresentableBy

end
