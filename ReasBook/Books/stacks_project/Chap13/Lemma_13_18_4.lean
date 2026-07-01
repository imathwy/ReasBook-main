import Mathlib
import stacks_project.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.18.4:
- primary domain: bounded-below injective cochain complexes and null-homotopies from acyclic
  complexes;
- sampled owner declarations:
  `CochainComplex.IsKInjective.nonempty_homotopy_zero`,
  `CochainComplex.IsKInjective`,
  `CochainComplex.InjectivePlus`,
  `PlusWithTermsIn.instIsKInjective`;
- best owner abstraction: `InjectivePlus 𝒜`, the chapter owner for bounded-below cochain
  complexes with injective terms; the null-homotopy conclusion is derived by upgrading this
  source-facing owner to the canonical core owner `CochainComplex.IsKInjective`;
- primitive vs. derived API:
  the primitive data is the acyclic source complex `K`, the bounded-below injective target
  `I : InjectivePlus 𝒜`, and the morphism `α : K ⟶ I`;
  the `IsKInjective` structure on the target and the null-homotopy conclusion are derived API and
  should be read from the canonical owner theorem rather than from repeated bounded-below and
  termwise-injective hypotheses.

Source/core/bridge triage:
- `source-facing`: the statement that any map from an acyclic complex to a bounded-below
  injective complex is homotopic to zero;
- `core/canonical`: `IsKInjective` and `IsKInjective.nonempty_homotopy_zero`;
- `bridge/view`: `PlusWithTermsIn.instIsKInjective` in `Definition 13.18.1` upgrades the
  bounded-below injective owner to the canonical `IsKInjective` owner used by the homotopy
  theorem.
-/

variable {K : CochainComplex 𝒜 ℤ}

-- Proof sketch: the bounded-below injective owner `InjectivePlus 𝒜` carries a canonical
-- `IsKInjective` instance, so the statement is exactly the owner theorem
-- `CochainComplex.IsKInjective.nonempty_homotopy_zero`.
/-- Lemma 13.18.4: if `K^•` is acyclic and `I^•` is a bounded-below cochain complex whose terms
are injective objects, then every morphism `K^• ⟶ I^•` is homotopic to zero. -/
lemma homotopic_to_zero_of_acyclic_to_boundedBelow_injective
    (I : InjectivePlus 𝒜) (α : K ⟶ I) (hK : K.Acyclic) :
    Nonempty (Homotopy α 0) :=
  IsKInjective.nonempty_homotopy_zero α hK

end CochainComplex
