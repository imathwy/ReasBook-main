import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory Limits HomologicalComplex ComplexShape

universe u v

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 12.13.9:
- primary domain: homological complexes, with monomorphisms, epimorphisms, and exactness detected
  degreewise.
- sampled owner declarations in this domain:
  `HomologicalComplex.mono_of_mono_f`,
  `HomologicalComplex.epi_of_epi_f`,
  `HomologicalComplex.exact_iff_degreewise_exact`,
  `HomologicalComplex.instAbelian`.
- owner abstraction: `CochainComplex A ℤ` is the source-facing specialization of
  `HomologicalComplex A (up ℤ)`.
- primitive data: the degreewise components `φ.f i` of a morphism and the degreewise short
  complexes `S.map (eval A (up ℤ) i)`.
- derived API: the source-facing degreewise bridge lemmas `(1)` and `(2)`.
- source/core/bridge triage:
  `(1)` and `(2)` are `source-facing` bridge declarations;
  the abelian instance and the exactness equivalence in `(3)` are `core/canonical` owner API
  already provided by `HomologicalComplex`, so this file should reuse them directly rather than
  keep parallel local wrappers. -/

section

variable [HasZeroMorphisms A] [HasPullbacks A]

/-- Lemma 12.13.9 (1): a morphism of cochain complexes is monomorphic exactly when each degree
component is monomorphic. This is the cochain-complex specialization of the canonical owner
construction `mono_of_mono_f`, and the forward implication only uses that evaluation preserves
pullbacks. -/
theorem cochainComplex_mono_iff_degreewise_mono {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    Mono φ ↔ ∀ i : ℤ, Mono (φ.f i) := by
  constructor
  · intro hφ i
    letI : Mono φ := hφ
    change Mono ((eval A (up ℤ) i).map φ)
    infer_instance
  · exact mono_of_mono_f φ

end

section

variable [HasZeroMorphisms A] [HasPushouts A]

/-- Lemma 12.13.9 (2): a morphism of cochain complexes is epimorphic exactly when each degree
component is epimorphic. This is the cochain-complex specialization of the canonical owner
construction `epi_of_epi_f`, and the forward implication only uses that evaluation preserves
pushouts. -/
theorem cochainComplex_epi_iff_degreewise_epi {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    Epi φ ↔ ∀ i : ℤ, Epi (φ.f i) := by
  constructor
  · intro hφ i
    letI : Epi φ := hφ
    change Epi ((eval A (up ℤ) i).map φ)
    infer_instance
  · exact epi_of_epi_f φ

end

section

/- Lemma 12.13.9: if `A` is an abelian category, then the category of cochain complexes in `A`
is abelian. -/
variable [Abelian A]

recall HomologicalComplex.instAbelian

section

variable (S : ShortComplex (CochainComplex A ℤ))

/- Lemma 12.13.9 (3): exactness for short complexes of cochain complexes is exactly the canonical
degreewise exactness statement `HomologicalComplex.exact_iff_degreewise_exact`, specialized to the
shape `up ℤ`. -/
recall HomologicalComplex.exact_iff_degreewise_exact

end
end
