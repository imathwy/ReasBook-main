import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 13.18.4: the bounded-below cochain complexes whose terms satisfy the object
property `P`. -/
private abbrev boundedBelowTermsIn (P : CategoryTheory.ObjectProperty 𝒜) :=
  CategoryTheory.ObjectProperty.FullSubcategory fun K : Plus 𝒜 ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace boundedBelowTermsIn

/-- Helper for Lemma 13.18.4: a bounded-below complex with terms in `P` coerces to its underlying
cochain complex. -/
private instance instCoeOutCochainComplex (P : CategoryTheory.ObjectProperty 𝒜) :
    CoeOut (boundedBelowTermsIn (𝒜 := 𝒜) P) (CochainComplex 𝒜 ℤ) where
  coe K := K.obj.obj

/-- Helper for Lemma 13.18.4: a bounded-below complex with terms in `P` is bounded below as a
cochain complex. -/
private theorem plus {P : CategoryTheory.ObjectProperty 𝒜}
    (K : boundedBelowTermsIn (𝒜 := 𝒜) P) :
    CochainComplex.plus 𝒜 (K : CochainComplex 𝒜 ℤ) := by
  simpa using K.obj.property

/-- Helper for Lemma 13.18.4: each term of a bounded-below complex with terms in `P` again
satisfies `P`. -/
private theorem term_mem {P : CategoryTheory.ObjectProperty 𝒜}
    (K : boundedBelowTermsIn (𝒜 := 𝒜) P) (n : ℤ) :
    P ((K : CochainComplex 𝒜 ℤ).X n) := by
  simpa using K.property n

/-- Helper for Lemma 13.18.4: a bounded-below complex with terms in `P` is zero in all
sufficiently negative degrees. -/
private theorem exists_isStrictlyGE {P : CategoryTheory.ObjectProperty 𝒜}
    (K : boundedBelowTermsIn (𝒜 := 𝒜) P) :
    ∃ a : ℤ, (K : CochainComplex 𝒜 ℤ).IsStrictlyGE a :=
  (CochainComplex.plus_iff 𝒜 (K : CochainComplex 𝒜 ℤ)).1 K.plus

end boundedBelowTermsIn

/-- Helper for Lemma 13.18.4: the bounded-below cochain complexes whose terms are injective
objects. -/
private abbrev InjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  boundedBelowTermsIn (𝒜 := 𝒜) (isInjective 𝒜)

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

/-- Helper for Lemma 13.18.4: a bounded-below cochain complex whose terms are injective objects
is K-injective. -/
private theorem boundedBelow_injective_isKInjective (I : InjectivePlus 𝒜) :
    CochainComplex.IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := I.exists_isStrictlyGE
  let _ : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective ((I : CochainComplex 𝒜 ℤ).X n) := I.term_mem
  exact isKInjective_of_injective (I : CochainComplex 𝒜 ℤ) a

variable {K : CochainComplex 𝒜 ℤ}

-- Proof sketch: the bounded-below injective owner `InjectivePlus 𝒜` carries a canonical
-- `IsKInjective` instance, so the statement is exactly the owner theorem
-- `CochainComplex.IsKInjective.nonempty_homotopy_zero`.
/-- Lemma 13.18.4: if `K^•` is acyclic and `I^•` is a bounded-below cochain complex whose terms
are injective objects, then every morphism `K^• ⟶ I^•` is homotopic to zero. -/
@[stacks 013R]
lemma homotopic_to_zero_of_acyclic_to_boundedBelow_injective
    (I : InjectivePlus 𝒜) (α : K ⟶ I) (hK : K.Acyclic) :
    Nonempty (Homotopy α 0) := by
  let _ : IsKInjective (I : CochainComplex 𝒜 ℤ) :=
    boundedBelow_injective_isKInjective (𝒜 := 𝒜) I
  exact IsKInjective.nonempty_homotopy_zero α hK

end CochainComplex
