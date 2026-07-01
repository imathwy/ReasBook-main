import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

namespace CategoryTheory.ObjectProperty

variable {A : Type u} [Category.{v} A]

/-- An object property has mono embeddings if every object admits a monomorphism into an object
satisfying the property. -/
class HasMonoEmbedding (P : ObjectProperty A) : Prop where
  exists_mono (X : A) : ∃ Y : A, P Y ∧ ∃ f : X ⟶ Y, Mono f

-- Proof sketch: take `Y = X` and the identity morphism, which is monic.
/-- The maximal object property has mono embeddings, using the identity monomorphism of each
object. -/
instance instHasMonoEmbeddingTop : HasMonoEmbedding (⊤ : ObjectProperty A) := sorry

end CategoryTheory.ObjectProperty

open CategoryTheory.ObjectProperty

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 13.15.5:
- primary domain: bounded-below replacements of cochain complexes by complexes whose terms lie in
  an object property, together with quasi-isomorphisms and degreewise monomorphy;
- sampled owner declarations:
  `ObjectProperty.HasEpiCover`,
  `IsStrictlyGEWithTermsIn`,
  `IsTermwiseMonoStrictlyGEWithTermsIn`,
  `IsStrictlyLEQuasiIsoWithTermsIn`,
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction:
  `ObjectProperty.HasMonoEmbedding` is the primitive object-property owner for the existence
  hypothesis, while `IsStrictlyGEWithTermsIn` and `IsTermwiseMonoStrictlyGEWithTermsIn` are the
  primitive bundled-target bounded-below stage owners and
  `IsStrictlyGEQuasiIsoWithTermsIn` / `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn` are the
  source-facing quasi-isomorphic refinements;
- primitive data:
  the comparison morphism `α : K ⟶ I` together with `QuasiIso α`, `I.IsStrictlyGE a`, and the
  termwise property `∀ n, P (I.X n)`;
- derived API:
  the quasi-isomorphic refinements and the two existence theorems below.

Source/core/bridge triage:
- `source-facing`: the two quasi-isomorphic bounded-below stage predicates and existence theorems
    below;
- `core/canonical`: `QuasiIso`, `I.IsStrictlyGE a`, `ObjectProperty.HasMonoEmbedding`, and the
  bundled-target owners `IsStrictlyGEWithTermsIn` / `IsTermwiseMonoStrictlyGEWithTermsIn`;
- `bridge/view`: downstream constructions such as lower truncation resolution systems, which should
  reuse these owners rather than redefine them.
-/

namespace CochainComplex

section

variable [HasZeroMorphisms A]

/-- The bounded-below cochain complexes whose terms satisfy the object property `P`. -/
abbrev PlusWithTermsIn (P : ObjectProperty A) :=
  ObjectProperty.FullSubcategory fun K : Plus A ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace PlusWithTermsIn

instance (P : ObjectProperty A) : CoeOut (PlusWithTermsIn P) (Plus A) where
  coe K := K.obj

instance (P : ObjectProperty A) :
    CoeOut (PlusWithTermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-below cochain complexes with terms in `P` into all cochain
complexes. -/
abbrev ι (P : ObjectProperty A) : PlusWithTermsIn P ⥤ CochainComplex A ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Plus.ι A

/-- A bounded-below cochain complex with terms in `P` is bounded below. -/
theorem plus {P : ObjectProperty A} (K : PlusWithTermsIn P) :
    CochainComplex.plus A (K : CochainComplex A ℤ) := by
  simpa using (K : Plus A).property

/-- Each term of a bounded-below cochain complex with terms in `P` again satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : PlusWithTermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := by
  simpa using K.property n

/-- A bounded-below cochain complex with terms in `P` is zero in all sufficiently negative
degrees. -/
theorem exists_isStrictlyGE {P : ObjectProperty A} (K : PlusWithTermsIn P) :
    ∃ a : ℤ, (K : CochainComplex A ℤ).IsStrictlyGE a :=
  (CochainComplex.plus_iff A (K : CochainComplex A ℤ)).1 K.plus

end PlusWithTermsIn

end

end CochainComplex

section

variable [HasZeroMorphisms A] [CategoryWithHomology A]

/-- A morphism `α : K ⟶ I` into a bounded-below complex whose terms satisfy `P` records only the
primitive bounded-below stage data carried by the owner `CochainComplex.PlusWithTermsIn P`. -/
structure IsStrictlyGEWithTermsIn
    (P : ObjectProperty A) (a : ℤ) {K : CochainComplex A ℤ}
    (I : CochainComplex.PlusWithTermsIn P) (α : K ⟶ I) : Prop where
  strictlyGE : (I : CochainComplex A ℤ).IsStrictlyGE a

/-- A morphism `α : K ⟶ I` into a bounded-below complex with terms in `P` is termwise
monomorphic if each degree component is monic. -/
structure IsTermwiseMonoStrictlyGEWithTermsIn
    (P : ObjectProperty A) (a : ℤ) {K : CochainComplex A ℤ}
    (I : CochainComplex.PlusWithTermsIn P) (α : K ⟶ I) : Prop extends
    IsStrictlyGEWithTermsIn P a I α where
  term_mono (n : ℤ) : Mono (α.f n)

/-- A morphism `α : K ⟶ I` exhibits `I` as a bounded-below cochain complex whose terms satisfy the
object property `P` and which is quasi-isomorphic to `K`. -/
structure IsStrictlyGEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop where
  quasiIso : QuasiIso α
  strictlyGE : I.IsStrictlyGE a
  term_mem (n : ℤ) : P (I.X n)

/-- A morphism `α : K ⟶ I` exhibits `I` as a bounded-below cochain complex with terms in `P`
which is quasi-isomorphic to `K` and termwise monomorphic. -/
structure IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K I : CochainComplex A ℤ) (α : K ⟶ I) : Prop extends
    IsStrictlyGEQuasiIsoWithTermsIn P a K I α where
  term_mono (n : ℤ) : Mono (α.f n)

namespace IsStrictlyGEWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}
variable {I : CochainComplex.PlusWithTermsIn P} {α : K ⟶ I}

/-- The primitive bounded-below stage data already packages its target as an element of the owner
`CochainComplex.PlusWithTermsIn P`. -/
abbrev toPlusWithTermsIn (h : IsStrictlyGEWithTermsIn P a I α) :
    CochainComplex.PlusWithTermsIn P :=
  I

end IsStrictlyGEWithTermsIn

namespace IsTermwiseMonoStrictlyGEWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K : CochainComplex A ℤ}
variable {I : CochainComplex.PlusWithTermsIn P} {α : K ⟶ I}

/-- A termwise-monomorphic morphism of cochain complexes is monomorphic as a morphism of
complexes. -/
theorem mono (h : IsTermwiseMonoStrictlyGEWithTermsIn P a I α) : Mono α :=
  HomologicalComplex.mono_of_mono_f α h.term_mono

/-- The primitive termwise-monomorphic bounded-below stage data keeps the same bundled target. -/
abbrev toPlusWithTermsIn (h : IsTermwiseMonoStrictlyGEWithTermsIn P a I α) :
    CochainComplex.PlusWithTermsIn P :=
  I

end IsTermwiseMonoStrictlyGEWithTermsIn

namespace IsStrictlyGEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K I : CochainComplex A ℤ} {α : K ⟶ I}

/-- The source-facing bounded-below replacement data canonically packages its resolving complex as
an element of the owner `CochainComplex.PlusWithTermsIn P`. -/
abbrev toPlusWithTermsIn (h : IsStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    CochainComplex.PlusWithTermsIn P :=
  ⟨⟨I, (CochainComplex.plus_iff A I).2 ⟨a, h.strictlyGE⟩⟩, h.term_mem⟩

/-- Forgetting the quasi-isomorphism keeps only the primitive bounded-below stage data owned by
`CochainComplex.PlusWithTermsIn P`. -/
abbrev toIsStrictlyGEWithTermsIn (h : IsStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    IsStrictlyGEWithTermsIn P a h.toPlusWithTermsIn α where
  strictlyGE := h.strictlyGE

end IsStrictlyGEQuasiIsoWithTermsIn

namespace IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K I : CochainComplex A ℤ} {α : K ⟶ I}

/-- Forgetting the quasi-isomorphism keeps only the primitive bounded-below termwise-monomorphic
stage data owned by `CochainComplex.PlusWithTermsIn P`. -/
abbrev toIsTermwiseMonoStrictlyGEWithTermsIn
    (h : IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    IsTermwiseMonoStrictlyGEWithTermsIn P a h.toIsStrictlyGEQuasiIsoWithTermsIn.toPlusWithTermsIn α where
  toIsStrictlyGEWithTermsIn := h.toIsStrictlyGEQuasiIsoWithTermsIn.toIsStrictlyGEWithTermsIn
  term_mono := h.term_mono

/-- A termwise-monomorphic morphism of cochain complexes is monomorphic as a morphism of
complexes. -/
theorem mono (h : IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α) : Mono α :=
  h.toIsTermwiseMonoStrictlyGEWithTermsIn.mono

/-- The termwise-monomorphic bounded-below replacement data packages its resolving complex as an
element of the owner `CochainComplex.PlusWithTermsIn P`. -/
abbrev toPlusWithTermsIn (h : IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α) :
    CochainComplex.PlusWithTermsIn P :=
  h.toIsStrictlyGEQuasiIsoWithTermsIn.toPlusWithTermsIn

end IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn

end

section

variable [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasMonoEmbedding]

-- Proof sketch: argue by ascending induction on the degree. At stage `n + 1`, choose a
-- monomorphism from the cokernel of the partial differential into an object of `P`, splice this
-- into the next term, and extend the comparison map. The inductive construction yields a
-- bounded-below complex `I` with terms in `P`, a termwise-monomorphic map `K ⟶ I`, and a
-- quasi-isomorphism.
/-- Lemma 13.15.5 (1): if a cochain complex `K` is zero in degrees below `a`, then there exists a
bounded-below cochain complex `I` whose terms satisfy the object property `P`, together with a
quasi-isomorphism `K ⟶ I` that is termwise monomorphic. -/
theorem exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyGE a) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α := sorry

-- Proof sketch: first replace `K` by the stupid truncation `K.truncGE a`, which is
-- quasi-isomorphic to `K` under the vanishing of homology below `a`. Then apply part (1) to the
-- bounded-below complex `K.truncGE a` and compose `K.πTruncGE a` with the resulting
-- quasi-isomorphism.
/-- Lemma 13.15.5 (2): if the homology of a cochain complex `K` vanishes in degrees below `a`,
then there exists a bounded-below cochain complex `I` whose terms satisfy the object property `P`,
together with a quasi-isomorphism `K ⟶ I`. -/
theorem exists_quasiIso_with_terms_in_of_isZero_homology_below
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      IsStrictlyGEQuasiIsoWithTermsIn P a K I α := sorry

end
