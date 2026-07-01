import Mathlib
import Mathlib.Tactic.Recall

open CategoryTheory Limits HomologicalComplex ComplexShape

universe v u

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 12.13.3:
- primary domain: homological complexes, with monomorphisms, epimorphisms, and exactness detected
  degreewise.
- sampled owner declarations in this domain:
  `HomologicalComplex.mono_of_mono_f`,
  `HomologicalComplex.epi_of_epi_f`,
  `HomologicalComplex.exact_iff_degreewise_exact`,
  `HomologicalComplex.instAbelian`.
- owner abstraction: `ChainComplex A ℤ` is the source-facing specialization of
  `HomologicalComplex A (ComplexShape.down ℤ)`.
- primitive data: the degreewise components `φ.f i` of a morphism and the degreewise short
  complexes `S.map (eval A (ComplexShape.down ℤ) i)`.
- derived API: the source-facing degreewise bridge lemmas `(1)` and `(2)`.
- source/core/bridge triage:
  `(1)` and `(2)` are `source-facing` bridge declarations;
  the abelian instance and the exactness equivalence in `(3)` are `core/canonical` owner API
  already provided by `HomologicalComplex`, so this file should reuse them directly rather than
  keep parallel local wrappers. -/

section

variable [HasZeroMorphisms A] [HasPullbacks A]

/-- Lemma 12.13.3 (1): a morphism of chain complexes is monomorphic exactly when each degree
component is monomorphic. This is the chain-complex specialization of the canonical owner
construction `mono_of_mono_f`, with the forward implication coming from the owner evaluation
functors. -/
theorem chainComplex_mono_iff_degreewise_mono {K L : ChainComplex A ℤ} (φ : K ⟶ L) :
    Mono φ ↔ ∀ i : ℤ, Mono (φ.f i) := by
  constructor
  · intro hφ i
    letI : Mono φ := hφ
    have : Mono ((eval A (down ℤ) i).map φ) := inferInstance
    simpa using this
  · intro hφ
    exact mono_of_mono_f φ hφ

end

section

variable [HasZeroMorphisms A] [HasPushouts A]

/-- Lemma 12.13.3 (2): a morphism of chain complexes is epimorphic exactly when each degree
component is epimorphic. This is the chain-complex specialization of the canonical owner
construction `epi_of_epi_f`, with the forward implication coming from the owner evaluation
functors. -/
theorem chainComplex_epi_iff_degreewise_epi {K L : ChainComplex A ℤ} (φ : K ⟶ L) :
    Epi φ ↔ ∀ i : ℤ, Epi (φ.f i) := by
  constructor
  · intro hφ i
    letI : Epi φ := hφ
    have : Epi ((eval A (down ℤ) i).map φ) := inferInstance
    simpa using this
  · intro hφ
    exact epi_of_epi_f φ hφ

end

section

/- Lemma 12.13.3: if `A` is an abelian category, then the category of chain complexes in `A`
is abelian. -/
variable [Abelian A]

recall HomologicalComplex.instAbelian

section

variable (S : ShortComplex (ChainComplex A ℤ))

/- Lemma 12.13.3 (3): exactness for short complexes of chain complexes is exactly the canonical
degreewise exactness statement `HomologicalComplex.exact_iff_degreewise_exact`, specialized to the
shape `down ℤ`. -/
recall HomologicalComplex.exact_iff_degreewise_exact

end
end
