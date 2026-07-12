import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open KaehlerDifferential

universe u v w

noncomputable section

variable (R : Type u) (S : Type v) (S' : Type w)
  [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [Algebra S S']
  [IsScalarTower R S S']

/- Domain-style sampling for Lemma 10.131.10:
- primary domain: the conormal exact sequence for a surjective map of commutative `R`-algebras,
  together with its splitting under an `R`-algebra section;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `KaehlerDifferential.mapBaseChange_surjective`,
  `retractionKerCotangentToTensorEquivSection`;
- best owner abstraction: the owner conormal map `kerCotangentToTensor R S S'` and its exact pair
  with `mapBaseChange R S S'`; the section/retraction correspondence above is the canonical split
  abstraction in the same domain.

Primitive-vs-derived split:
- primitive data: the surjective algebra map `S → S'` and, in the split case, an `R`-algebra
  section `S' → S`;
- derived API: exactness and surjectivity of the owner conormal sequence, and the source-facing
  splitting statement.

Source/core/bridge triage:
- `source-facing`: split exactness of the conormal sequence under a chosen section;
- `core/canonical`: `exact_kerCotangentToTensor_mapBaseChange`,
  `mapBaseChange_surjective`, and `retractionKerCotangentToTensorEquivSection`;
- `bridge/view`: the textbook phrasing as the split short exact conormal sequence.

The first two items in the previous version were exact-interface wrappers around canonical mathlib
owners, so they are refined away in favor of direct recall. -/

/- The conormal sequence
`I/I² → S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R]` is exact when `S → S'` is surjective, with
`I = ker(S → S')`. This is exactly
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`. -/
recall KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange

/- The map `S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R]` in the conormal sequence is surjective when
`S → S'` is surjective. This is exactly `KaehlerDifferential.mapBaseChange_surjective`. -/
recall KaehlerDifferential.mapBaseChange_surjective

/-
The canonical split-conormal owner for a chosen section modulo the square of the kernel is
`retractionKerCotangentToTensorEquivSection`. -/
recall retractionKerCotangentToTensorEquivSection

/-
Proof sketch: the chosen section `β : S' →ₐ[R] S` determines a section
`σ : S' →ₐ[R] S ⧸ ker(algebraMap S S')²`, and
`retractionKerCotangentToTensorEquivSection` converts `σ` into a retraction of
`kerCotangentToTensor R S S'`. Together with the recalled exactness and surjectivity of the
conormal sequence for a surjective algebra map, this gives the source-facing split short exact
sequence. -/
/-- Lemma 10.131.10: if the surjection `S → S'` admits an `R`-algebra section, then the conormal
sequence
`0 → I/I² → S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R] → 0`,
with `I = ker(S → S')`, is split: the canonical conormal map is exact, the right map is
surjective, and the chosen section induces a retraction of the left map. -/
@[stacks 02HP]
theorem kaehlerDifferential_conormal_sequence_split_of_section
    (β : S' →ₐ[R] S)
    (hβ : (IsScalarTower.toAlgHom R S S').comp β = AlgHom.id R S') :
    Function.Exact
        (kerCotangentToTensor R S S')
        (KaehlerDifferential.mapBaseChange R S S') ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange R S S') ∧
      ∃ l : S' ⊗[S] Ω[S⁄R] →ₗ[S] (RingHom.ker (algebraMap S S')).Cotangent,
        l ∘ₗ kerCotangentToTensor R S S' = LinearMap.id := by
  let σ : S' →ₐ[R] S ⧸ RingHom.ker (algebraMap S S') ^ 2 :=
    (Ideal.Quotient.mkₐ R (RingHom.ker (algebraMap S S') ^ 2)).comp β
  let hσ : (IsScalarTower.toAlgHom R S S').kerSquareLift.comp σ = AlgHom.id R S' := by
    ext x
    simpa [σ] using DFunLike.congr_fun hβ x
  have hsurj : Function.Surjective (algebraMap S S') := fun x ↦ ⟨β x, DFunLike.congr_fun hβ x⟩
  refine ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S S' hsurj,
    KaehlerDifferential.mapBaseChange_surjective R S S' hsurj, ?_⟩
  exact ⟨((retractionKerCotangentToTensorEquivSection hsurj).symm ⟨σ, hσ⟩).1,
    ((retractionKerCotangentToTensorEquivSection hsurj).symm ⟨σ, hσ⟩).2⟩

end
