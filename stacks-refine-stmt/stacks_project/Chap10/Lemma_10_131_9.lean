import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S']

/- Domain triage:
- primary domain: the conormal exact sequence for a surjective map of commutative `R`-algebras;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.kerCotangentToTensor_toCotangent`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `Ideal.Cotangent.equivOfEq`,
  `KaehlerDifferential.mapBaseChange_surjective`;
- best owner abstraction: the ring-level conormal map
  `KaehlerDifferential.kerCotangentToTensor R S S'`, together with the canonical cotangent
  transport `Ideal.Cotangent.equivOfEq` induced by an equality of ideals;
- layer: `bridge/view`, since the Stacks statement uses an explicitly named ideal `I` equipped with
  an identification `ker(S → S') = I`, while the core owner is phrased directly for the kernel;
- primitive data: the surjective map `S → S'` and the kernel identification `hI`;
- derived API: the canonical cotangent transport
  `Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap S S')) hI.symm`, its composite with
  `KaehlerDifferential.kerCotangentToTensor R S S'`, the resulting class formula, and the exactness
  statement.

The previous file duplicated the owner map as a local `abbrev`. That wrapper carried no new
mathematics, so the refined file keeps only the source-facing bridge theorems and states them
directly with the canonical mathlib owner. -/

/-- On a class represented by `f ∈ I`, the canonical conormal map
`I/I² → S' ⊗[S] Ω[S⁄R]` sends `f` to `1 ⊗ d f`. This is the kernel-identified form of
  `KaehlerDifferential.kerCotangentToTensor_toCotangent`. -/
theorem kerCotangentToTensorOfKerEq_toCotangent
    (I : Ideal S) (hI : RingHom.ker (algebraMap S S') = I) (x : I) :
    ((KaehlerDifferential.kerCotangentToTensor R S S').comp
      (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap S S')) hI.symm).toLinearMap)
        (Ideal.toCotangent I x) =
      1 ⊗ₜ[S] KaehlerDifferential.D R S x := by
  cases hI
  change
    KaehlerDifferential.kerCotangentToTensor R S S'
        ((Ideal.Cotangent.equivOfEq
          (RingHom.ker (algebraMap S S'))
          (RingHom.ker (algebraMap S S')) rfl)
          (Ideal.toCotangent (RingHom.ker (algebraMap S S')) x)) =
      1 ⊗ₜ[S] KaehlerDifferential.D R S x
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  simp

variable [Algebra R S'] [IsScalarTower R S S']

/-- Lemma 10.131.9: if `S → S'` is surjective with kernel `I`, then the canonical conormal
sequence
`I/I² → S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R] → 0`
is exact. This is the kernel-identified form of
`KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange` together with
`KaehlerDifferential.mapBaseChange_surjective`. -/
theorem kaehlerDifferential_exact_cotangent_tensor_of_surjective
    (I : Ideal S) (hI : RingHom.ker (algebraMap S S') = I)
    (hsurj : Function.Surjective (algebraMap S S')) :
    Function.Exact
        ((KaehlerDifferential.kerCotangentToTensor R S S').comp
          (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap S S')) hI.symm).toLinearMap)
        (KaehlerDifferential.mapBaseChange R S S') ∧
      Function.Surjective (KaehlerDifferential.mapBaseChange R S S') := by
  cases hI
  have hcomp :
      (KaehlerDifferential.kerCotangentToTensor R S S').comp
          (Ideal.Cotangent.equivOfEq
            (RingHom.ker (algebraMap S S'))
            (RingHom.ker (algebraMap S S')) rfl).toLinearMap =
        KaehlerDifferential.kerCotangentToTensor R S S' := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker (algebraMap S S')) x
    simp
  rw [hcomp]
  exact ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S S' hsurj,
    KaehlerDifferential.mapBaseChange_surjective R S S' hsurj⟩

end
