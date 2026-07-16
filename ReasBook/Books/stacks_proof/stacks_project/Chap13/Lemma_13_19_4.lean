import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K : CochainComplex 𝒜 ℤ}

/- Domain-style sampling for Lemma 13.19.4:
- primary domain: null-homotopies from bounded-above projective cochain complexes to acyclic
  cochain complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.IsKProjective`,
  `CochainComplex.IsKProjective.nonempty_homotopy_zero`;
- best owner abstraction: the chapter owner `ProjectiveMinus 𝒜` for the bounded-above projective
  source complex, together with the canonical core owner theorem
  `CochainComplex.IsKProjective.nonempty_homotopy_zero`;
- primitive data: a bounded-above projective source
  `P : ProjectiveMinus 𝒜`, a morphism
  `α : (P : CochainComplex 𝒜 ℤ) ⟶ K`, and an acyclicity proof `hK : K.Acyclic`;
- derived API: the resulting null-homotopy.

Source/core/bridge triage:
- `source-facing`: the textbook bounded-above/projective-to-acyclic null-homotopy statement;
- `core/canonical`: `CochainComplex.IsKProjective.nonempty_homotopy_zero`;
- `bridge/view`: `CochainComplex.MinusWithTermsIn.instIsKProjective`, which upgrades the
  source-facing owner to the canonical K-projective owner.
-/

-- Proof sketch: `P` already carries the canonical `IsKProjective` instance from
-- `Definition 13.19.1`, so the claim is exactly the owner theorem
-- `CochainComplex.IsKProjective.nonempty_homotopy_zero`.
/-- Lemma 13.19.4: if `P^•` is a bounded-above cochain complex of projective objects and `K^•`
is acyclic, then every morphism `P^• ⟶ K^•` is homotopic to zero. -/
@[stacks 0647]
theorem homotopic_to_zero_of_boundedAbove_projective_to_acyclic
    (P : ProjectiveMinus 𝒜) (α : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (hK : K.Acyclic) :
    Nonempty (Homotopy α 0) :=
  IsKProjective.nonempty_homotopy_zero α hK

end CochainComplex
