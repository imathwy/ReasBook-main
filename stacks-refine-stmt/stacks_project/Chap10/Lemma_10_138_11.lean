import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

universe u

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.FormallySmooth A B]

/- Domain triage:
* primary domain: the surjective Jacobi-Zariski conormal sequence on first cotangent homology for
  a tower `A → B → C`;
* sampled owner declarations:
  - `H1Cotangent.δ`, the canonical surjection candidate in the Jacobi-Zariski sequence;
  - `surjective_jacobi_zariski_conormal_sequence`, the chapter owner of exactness and surjectivity
    for `H1Cotangent.map A B C C` and `H1Cotangent.δ A B C` under `A → C` surjective;
  - `Algebra.formallySmooth_iff`, which packages formal smoothness as
    `Subsingleton (H1Cotangent A B)` plus projectivity of `Ω[B⁄A]`;
  - `Module.Projective.iff_split_of_projective`, the owner criterion turning projectivity of the
    codomain of a surjective linear map into a section.
* best owner abstraction: the new split data should be carried by the canonical surjection
  `H1Cotangent.δ A B C`; the retraction of `H1Cotangent.map A B C C` is derived from exactness via
  `Function.Exact.split_tfae'`, so it should not remain the primitive public surface here.
* primitive data vs. derived API:
  - primitive data: the surjective map `A → C` and the formally smooth algebra `A → B`;
  - derived API: a section of `H1Cotangent.δ A B C`, with the left-map retraction recoverable from
    the earlier exactness theorem.
* layer triage:
  - `source-facing`: split exactness of the surjective Jacobi-Zariski conormal sequence;
  - `core/canonical`: `H1Cotangent.δ A B C` together with
    `surjective_jacobi_zariski_conormal_sequence` and `Algebra.formallySmooth_iff`;
  - `bridge/view`: translating the split surjection into a retraction of
    `H1Cotangent.map A B C C`.
-/

-- Proof sketch: Lemma `10.134.7` gives exactness of
-- `H1Cotangent.map A B C C` followed by `H1Cotangent.δ A B C`, and also surjectivity of
-- `H1Cotangent.δ A B C`, when `A → C` is surjective. Since `A → B` is formally smooth,
-- `Ω[B⁄A]` is projective over `B`, hence after base change to `C` the module
-- `C ⊗[B] Ω[B⁄A]` is projective over `C`. Therefore the surjection `H1Cotangent.δ A B C`
-- admits a `C`-linear section, which is the canonical split-exact owner data for this sequence.
/-- Lemma 10.138.11: if `A → C` is surjective and `A → B` is formally smooth, then the exact
sequence of Lemma `10.134.7`,
`0 → I/I² → J/J² → Ω[B⁄A] ⊗[B] C → 0`,
is split exact. In the canonical Jacobi-Zariski formulation, this means that the surjection
`H1Cotangent.δ A B C : H1Cotangent B C →ₗ[C] C ⊗[B] Ω[B⁄A]` admits a `C`-linear section. -/
theorem jacobi_zariski_conormal_sequence_splits_of_formallySmooth
    (hAC : Function.Surjective (algebraMap A C)) :
    ∃ σ : C ⊗[B] Ω[B⁄A] →ₗ[C] H1Cotangent B C,
      (H1Cotangent.δ A B C).comp σ = LinearMap.id := sorry

end
