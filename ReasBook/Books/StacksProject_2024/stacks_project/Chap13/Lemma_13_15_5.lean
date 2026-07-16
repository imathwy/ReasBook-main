import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex
open Opposite

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
instance instHasMonoEmbeddingTop : HasMonoEmbedding (⊤ : ObjectProperty A) where
  exists_mono X := by
    -- Choose the object itself and the identity monomorphism.
    refine ⟨X, by simp, 𝟙 X, inferInstance⟩

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
abbrev toPlusWithTermsIn (_h : IsStrictlyGEWithTermsIn P a I α) :
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
abbrev toPlusWithTermsIn (_h : IsTermwiseMonoStrictlyGEWithTermsIn P a I α) :
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

/-- Helper for Lemma 13.15.5: the opposite-side object property attached to `P`. -/
abbrev oppositeProperty : ObjectProperty Aᵒᵖ :=
  P.op

/-- Helper for Lemma 13.15.5: mono embeddings in `P` give epi covers in the opposite category. -/
instance oppositeProperty_hasEpiCover : (oppositeProperty P).HasEpiCover where
  exists_epi X := by
    -- Apply the embedding hypothesis to the underlying object and then opposite the monomorphism.
    obtain ⟨Y, hY, f, hf⟩ := (inferInstance : P.HasMonoEmbedding).exists_mono X.unop
    refine ⟨Opposite.op Y, ?_, f.op, inferInstance⟩
    simpa [oppositeProperty] using hY

/-- Helper for Lemma 13.15.5: the opposite transport of a bounded-below complex is bounded above
at the negated cutoff. -/
lemma isStrictlyLE_op_obj_of_isStrictlyGE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyGE a) :
    ((CochainComplex.opEquivalence A).functor.obj (Opposite.op K)).IsStrictlyLE (-a) := by
  -- Proof comment: the opposite/cochain transport sends degree `n` to degree `-n`, so strict
  -- lower vanishing for `K` becomes strict upper vanishing for the transported opposite complex.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have hneg : -n < a := by
    omega
  have hzero : IsZero (K.X (-n)) := K.isZero_of_isStrictlyGE a (-n) hneg
  simpa [CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
    HomologicalComplex.opEquivalence] using IsZero.op hzero

/-- Helper for Lemma 13.15.5: the canonical lower truncation is a quasi-isomorphism when the
homology vanishes below the cutoff. -/
lemma quasiIso_piTruncGE_of_isZero_homology_below
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    QuasiIso (K.πTruncGE a) := by
  -- Turn the homology vanishing range into the standard exactness owner `K.IsGE a`.
  have hGE : K.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK n hn
  letI := hGE
  infer_instance

/-- Helper for Lemma 13.15.5: transport an opposite-side cochain complex back to `A` through the
canonical opposite equivalence. -/
private noncomputable abbrev transported_complex_from_opposite
    {Q : CochainComplex Aᵒᵖ ℤ} :
    CochainComplex A ℤ :=
  ((CochainComplex.opEquivalence A).inverse.obj Q).unop

/-- Helper for Lemma 13.15.5: transport the opposite-side comparison map back to a map
`K ⟶ I` on the original complex. -/
private noncomputable abbrev transported_map_from_opposite
    (K : CochainComplex A ℤ)
    {Q : CochainComplex Aᵒᵖ ℤ}
    (β : Q ⟶ (CochainComplex.opEquivalence A).functor.obj (Opposite.op K)) :
    K ⟶ transported_complex_from_opposite (A := A) (Q := Q) :=
  (((CochainComplex.opEquivalence A).unitIso.app (Opposite.op K)).unop).inv ≫
    (((CochainComplex.opEquivalence A).inverse.map β).unop)

/-- Helper for Lemma 13.15.5: quasi-isomorphisms remain quasi-isomorphisms after transporting the
opposite-side comparison map back to `A`. -/
private theorem quasiIso_transported_map_from_opposite
    (K : CochainComplex A ℤ)
    {Q : CochainComplex Aᵒᵖ ℤ}
    (β : Q ⟶ (CochainComplex.opEquivalence A).functor.obj (Opposite.op K))
    (hβ : QuasiIso β) :
    QuasiIso (transported_map_from_opposite (A := A) K β) := by
  sorry

/-- Helper for Lemma 13.15.5: a bounded-above opposite complex transports to a bounded-below
complex on the original side. -/
private theorem transported_complex_isStrictlyGE
    (a : ℤ) {Q : CochainComplex Aᵒᵖ ℤ}
    (hQ : Q.IsStrictlyLE (-a)) :
    (transported_complex_from_opposite (A := A) (Q := Q)).IsStrictlyGE a := by
  -- Proof comment: degree `n < a` on the unop side corresponds to degree `-n > -a` on the
  -- opposite side, so the original strict-upper bound becomes the required strict-lower bound.
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hneg : -a < -n := by
    omega
  have hzero : IsZero (Q.X (-n)) := Q.isZero_of_isStrictlyLE (-a) (-n) hneg
  simpa [transported_complex_from_opposite, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence] using
    IsZero.unop hzero

/-- Helper for Lemma 13.15.5: the termwise object-property condition on the opposite-side
resolution transports back to the original complex. -/
private theorem transported_complex_term_mem
    (a : ℤ) (K : CochainComplex A ℤ)
    {Q : CochainComplex Aᵒᵖ ℤ}
    (β : Q ⟶ (CochainComplex.opEquivalence A).functor.obj (Opposite.op K))
    (hβ : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn (oppositeProperty P) (-a)
      ((CochainComplex.opEquivalence A).functor.obj (Opposite.op K)) Q β)
    (n : ℤ) :
    P ((transported_complex_from_opposite (A := A) (Q := Q)).X n) := by
  -- Proof comment: term `n` of the transported complex is exactly term `-n` of `Q`, viewed back
  -- in `A`, so the opposite-side termwise property rewrites directly.
  simpa [transported_complex_from_opposite, oppositeProperty, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence] using hβ.term_mem (-n)

/-- Helper for Lemma 13.15.5: the degreewise epimorphy of the opposite-side comparison map
becomes degreewise monomorphy after transporting back to `A`. -/
private theorem transported_map_term_mono
    (a : ℤ) (K : CochainComplex A ℤ)
    {Q : CochainComplex Aᵒᵖ ℤ}
    (β : Q ⟶ (CochainComplex.opEquivalence A).functor.obj (Opposite.op K))
    (hβ : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn (oppositeProperty P) (-a)
      ((CochainComplex.opEquivalence A).functor.obj (Opposite.op K)) Q β)
    (n : ℤ) :
    Mono ((transported_map_from_opposite (A := A) K β).f n) := by
  sorry

/-- Helper for Lemma 13.15.5: an opposite-side bounded-above resolution transports to a
termwise-monomorphic bounded-below resolution on the original complex. -/
lemma transport_termwise_mono_resolution_from_opposite
    (a : ℤ) (K : CochainComplex A ℤ)
    {Q : CochainComplex Aᵒᵖ ℤ}
    (β : Q ⟶ (CochainComplex.opEquivalence A).functor.obj (Opposite.op K))
    (hβ : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn (oppositeProperty P) (-a)
      ((CochainComplex.opEquivalence A).functor.obj (Opposite.op K)) Q β) :
    ∃ (I : CochainComplex A ℤ) (α : K ⟶ I),
      IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α := by
  -- Route correction: the source proof first chooses the opposite-side bounded-above resolution
  -- and then transports that chosen witness back through `CochainComplex.opEquivalence`; we now
  -- keep that transport explicit instead of rebuilding the replacement on `A`.
  let I : CochainComplex A ℤ := transported_complex_from_opposite (A := A) (Q := Q)
  let α : K ⟶ I := transported_map_from_opposite (A := A) K β
  have hquasiIso : QuasiIso α := by
    simpa [α] using quasiIso_transported_map_from_opposite (A := A) K β hβ.quasiIso
  refine ⟨I, α, ?_⟩
  refine
    { quasiIso := hquasiIso
      strictlyGE := transported_complex_isStrictlyGE (A := A) (a := a) hβ.strictlyLE
      term_mem := transported_complex_term_mem (A := A) (P := P) a K β hβ
      term_mono := transported_map_term_mono (A := A) (P := P) a K β hβ }

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
      IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn P a K I α := by
  let Kop : CochainComplex Aᵒᵖ ℤ :=
    (CochainComplex.opEquivalence A).functor.obj (Opposite.op K)
  -- Resolve the opposite complex by the already constructed bounded-above theorem.
  have hKop : Kop.IsStrictlyLE (-a) :=
    isStrictlyLE_op_obj_of_isStrictlyGE a K hK
  obtain ⟨Q, β, hβ⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
      (oppositeProperty P) (-a) Kop hKop
  -- Transport the opposite-side witness back to the original category.
  exact transport_termwise_mono_resolution_from_opposite (P := P) a K β hβ

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
      IsStrictlyGEQuasiIsoWithTermsIn P a K I α := by
  -- First truncate below `a`; the vanishing hypothesis makes this a quasi-isomorphism.
  have hπ : QuasiIso (K.πTruncGE a) :=
    quasiIso_piTruncGE_of_isZero_homology_below a K hK
  obtain ⟨I, α, hα⟩ :=
    exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE
      P a (K.truncGE a) inferInstance
  letI := hπ
  letI := hα.quasiIso
  -- Compose the truncation quasi-isomorphism with the bounded-below replacement.
  refine ⟨I, K.πTruncGE a ≫ α, ?_⟩
  refine
    { quasiIso := by infer_instance
      strictlyGE := hα.strictlyGE
      term_mem := hα.term_mem }

end
