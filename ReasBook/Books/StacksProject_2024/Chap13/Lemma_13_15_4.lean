import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 13.15.4:
- primary domain: bounded-above replacements of cochain complexes by complexes whose terms lie in
  an object property, together with quasi-isomorphisms and degreewise epimorphy;
- sampled owner declarations in this domain:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `CochainComplex.Minus`,
  `CochainComplex.Minus.ι`,
  `CochainComplex.minus`,
  `QuasiIso`,
  `ObjectProperty.HasEpiCover`;
- best owner abstraction:
  `CochainComplex.MinusWithTermsIn P` should be the full subcategory of the canonical bounded-above
  owner `CochainComplex.Minus A` cut out by the termwise `P`-condition, with owner inclusion
  `ObjectProperty.ι _ : MinusWithTermsIn P ⥤ Minus A`; the two predicates below are the
  source-facing layer adding the comparison morphism and its quasi-isomorphism / epimorphism
  properties, while the owner conversion `toMinusWithTermsIn` remains a bridge;
- primitive-vs-derived split:
  primitive data are the comparison morphism `α : Q ⟶ K` together with the three source-faithful
  properties `QuasiIso α`, `Q.IsStrictlyLE a`, and the termwise predicate
  `term_mem (n : ℤ) : P (Q.X n)`;
  the termwise-epimorphic variant adds the source-facing degreewise epimorphism predicate
  `term_epi (n : ℤ) : Epi (α.f n)`, while any complex-level `Epi α` fact is derived API from the
  canonical owner lemma `HomologicalComplex.epi_of_epi_f`.

Source/core/bridge triage:
- `source-facing`: `IsStrictlyLEQuasiIsoWithTermsIn` and
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- `core/canonical`: `CochainComplex.MinusWithTermsIn P`, `QuasiIso`, `ObjectProperty.HasEpiCover`,
  and the componentwise `Epi` predicate;
- `bridge/view`: the owner inclusion `ObjectProperty.ι _ : MinusWithTermsIn P ⥤ Minus A` and its
  composite with `CochainComplex.Minus.ι A`,
  `IsStrictlyLEQuasiIsoWithTermsIn.toMinusWithTermsIn`, and the existence theorems below, which
  package a source-level bounded-above replacement into these owner predicates.
-/

namespace CochainComplex

section

variable [HasZeroMorphisms A]

/-- The bounded-above cochain complexes whose terms satisfy the object property `P`. -/
abbrev MinusWithTermsIn (P : ObjectProperty A) :=
  ObjectProperty.FullSubcategory fun K : Minus A ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace MinusWithTermsIn

instance (P : ObjectProperty A) : CoeOut (MinusWithTermsIn P) (Minus A) where
  coe K := K.obj

instance (P : ObjectProperty A) :
    CoeOut (MinusWithTermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-above cochain complexes with terms in `P` into all cochain
complexes. -/
abbrev ι (P : ObjectProperty A) : MinusWithTermsIn P ⥤ CochainComplex A ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Minus.ι A

/-- A bounded-above cochain complex with terms in `P` is bounded above. -/
theorem minus {P : ObjectProperty A} (K : MinusWithTermsIn P) :
    CochainComplex.minus A (K : CochainComplex A ℤ) := by
  simpa using (K : Minus A).property

/-- Each term of a bounded-above cochain complex with terms in `P` again satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : MinusWithTermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := by
  simpa using K.property n

/-- A bounded-above cochain complex with terms in `P` is zero in all sufficiently high degrees. -/
theorem exists_isStrictlyLE {P : ObjectProperty A} (K : MinusWithTermsIn P) :
    ∃ b : ℤ, (K : CochainComplex A ℤ).IsStrictlyLE b :=
  (CochainComplex.minus_iff A (K : CochainComplex A ℤ)).1 K.minus

end MinusWithTermsIn

end

end CochainComplex

section

variable [HasZeroMorphisms A] [CategoryWithHomology A]

/-- A morphism `α : Q ⟶ K` exhibits `Q` as a bounded-above cochain complex whose terms satisfy
the object property `P` and which is quasi-isomorphic to `K`. -/
structure IsStrictlyLEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop where
  quasiIso : QuasiIso α
  strictlyLE : Q.IsStrictlyLE a
  term_mem (n : ℤ) : P (Q.X n)

namespace IsStrictlyLEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- The source-facing bounded-above replacement data canonically packages its resolving complex as
an element of the owner `CochainComplex.MinusWithTermsIn P`. -/
abbrev toMinusWithTermsIn (h : IsStrictlyLEQuasiIsoWithTermsIn P a K Q α) :
    CochainComplex.MinusWithTermsIn P :=
  ⟨⟨Q, (CochainComplex.minus_iff A Q).2 ⟨a, h.strictlyLE⟩⟩, h.term_mem⟩

end IsStrictlyLEQuasiIsoWithTermsIn

/-- A morphism `α : Q ⟶ K` exhibits `Q` as a bounded-above cochain complex with terms in `P`
which is quasi-isomorphic to `K` and termwise epimorphic. -/
structure IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop extends
    IsStrictlyLEQuasiIsoWithTermsIn P a K Q α where
  term_epi (n : ℤ) : Epi (α.f n)

namespace IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- A termwise-epimorphic morphism of cochain complexes is epimorphic as a morphism of
complexes. -/
theorem epi (h : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α) : Epi α :=
  epi_of_epi_f α h.term_epi

/-- The termwise-epimorphic bounded-above replacement data packages its resolving complex as an
element of the owner `CochainComplex.MinusWithTermsIn P`. -/
abbrev toMinusWithTermsIn (h : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α) :
    CochainComplex.MinusWithTermsIn P :=
  h.toIsStrictlyLEQuasiIsoWithTermsIn.toMinusWithTermsIn

end IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn

end

section

variable [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]

-- Proof sketch: argue by descending induction on the degree. At stage `n - 1`, choose an
-- epimorphism from an object of `P` onto the pullback `K.X (n - 1) ×_{K.X n} ker(d_Q^n)`, then
-- extend the partial complex and comparison map. The inductive construction yields a bounded-above
-- complex `Q` with terms in `P`, a termwise-epimorphic map `Q ⟶ K`, and a quasi-isomorphism.
/-- Lemma 13.15.4 (1): if a cochain complex `K` is zero in degrees above `a`, then there exists a
bounded-above cochain complex `Q` whose terms satisfy the object property `P`, together with a
quasi-isomorphism `Q ⟶ K` that is termwise epimorphic. -/
theorem exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := sorry

-- Proof sketch: first replace `K` by the stupid truncation `K.truncLE a`, which is
-- quasi-isomorphic to `K` under the vanishing of homology above `a`. Then apply part (1) to the
-- bounded-above complex `K.truncLE a` and compose the resulting quasi-isomorphism with
-- `K.ιTruncLE a`.
/-- Lemma 13.15.4 (2): if the homology of a cochain complex `K` vanishes in degrees above `a`,
then there exists a bounded-above cochain complex `Q` whose terms satisfy the object property `P`,
together with a quasi-isomorphism `Q ⟶ K`. -/
theorem exists_quasiIso_with_terms_in_of_isZero_homology_above
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsStrictlyLEQuasiIsoWithTermsIn P a K Q α := sorry

end
