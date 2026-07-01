import Mathlib
import stacks_project.Chap10.Lemma_10_116_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open TopologicalSpace

section

variable {k : Type u} [Field k]
variable {S' : Type v} [CommRing S'] [Algebra k S'] [Algebra.FiniteType k S']
variable {S : Type w} [CommRing S] [Algebra k S]

/- 
Domain-style sampling:
- primary domain: local Krull dimension on affine schemes of finite type over a field, compared
  along the prime-spectrum map induced by a surjective algebra homomorphism;
- sampled owner declarations of the same kind:
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `RingHom.strictMono_comap_of_surjective`,
  `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`;
- best owner abstraction: the ambient owner remains `topologicalKrullDimAt`, while the
  localization-height and residue-field comparison data are already canonically owned upstream by
  `Localization.AtPrime`, `Ideal.height`, and `Ideal.ResidueField.mapₐ`;
- primitive data: the surjective `k`-algebra map `f : S' →ₐ[k] S`, its surjectivity witness `hf`,
  and the point `x : PrimeSpectrum S`;
- derived API: the local-dimension comparison formula, obtained by reusing the local dimension
  decomposition from Lemma `10.116.3`, the canonical height formula for localizations, and the
  canonical residue-field isomorphism induced by surjectivity on stalks.

Source/core/bridge triage:
* `source-facing`: the dimension comparison formula at corresponding points under a surjective
  morphism;
* `core/canonical`: `topologicalKrullDimAt`,
  `topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`, and `Ideal.ResidueField.mapₐ`;
* `bridge/view`: the strict monotonicity of `PrimeSpectrum.comap` for surjective maps and the
  residue-field bijectivity theorem derived from `RingHom.surjectiveOnStalks_of_surjective`.
-/

-- Proof sketch: apply Lemma `10.116.3` to `x` and to its inverse-image
-- `PrimeSpectrum.comap f.toRingHom x`. For a surjective `k`-algebra map, the induced extension of
-- residue fields at corresponding primes is an isomorphism, so the transcendence-degree terms are
-- equal and cancel. The remaining terms are the heights of the corresponding prime ideals.
/-- Lemma 10.116.4: if `f : S' →ₐ[k] S` is a surjective morphism, where `S'` is a finite type
`k`-algebra, and `x : PrimeSpectrum S` corresponds to the prime ideal `𝔭 ⊂ S`, then for the
corresponding point `PrimeSpectrum.comap f.toRingHom x : PrimeSpectrum S'`, corresponding to
`𝔭' = Ideal.comap f.toRingHom 𝔭`, the local-dimension difference is the height difference.
Since local dimensions take values in `WithBot ℕ∞`, this is stated in the equivalent additive
form `dim_{x'}(Spec S') = dim_x(Spec S) + (height(𝔭') - height(𝔭))`. -/
theorem topologicalKrullDimAt_comap_eq_add_height_sub_of_surjective_of_finiteType_over_field
    (f : S' →ₐ[k] S) (hf : Function.Surjective f) (x : PrimeSpectrum S) :
    topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom x) =
      topologicalKrullDimAt x +
        (((PrimeSpectrum.comap f.toRingHom x).asIdeal.height - x.asIdeal.height : ℕ∞) :
          WithBot ℕ∞) := by
  letI : Algebra.FiniteType k S := Algebra.FiniteType.of_surjective f hf
  set x' : PrimeSpectrum S' := PrimeSpectrum.comap f.toRingHom x
  have htrdeg :
      Cardinal.toNat (Algebra.trdeg k x'.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
    let e : x'.asIdeal.ResidueField ≃ₐ[k] x.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ x'.asIdeal x.asIdeal f rfl)
        ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective _ _ rfl)
    have htrdeg' := congrArg Cardinal.toNat (AlgEquiv.lift_trdeg_eq e)
    simpa [Cardinal.toNat_lift] using htrdeg'
  have hheight_le : x.asIdeal.height ≤ x'.asIdeal.height := by
    simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight] using
      (Order.height_le_height_apply_of_strictMono
        (PrimeSpectrum.comap f.toRingHom)
        (RingHom.strictMono_comap_of_surjective hf)
        x)
  have hheight :
      ((x'.asIdeal.height : WithBot ℕ∞) : WithBot ℕ∞) =
        (x.asIdeal.height : WithBot ℕ∞) +
          (((x'.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
    exact_mod_cast (add_tsub_cancel_of_le hheight_le).symm
  calc
    topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom x)
        = (x'.asIdeal.height : WithBot ℕ∞) +
            Cardinal.toNat (Algebra.trdeg k x'.asIdeal.ResidueField) := by
          rw [show topologicalKrullDimAt x' =
              ringKrullDim (Localization.AtPrime x'.asIdeal) +
                Cardinal.toNat (Algebra.trdeg k x'.asIdeal.ResidueField) from
            topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
              x']
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height x'.asIdeal
            (Localization.AtPrime x'.asIdeal)]
    _ = (x'.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := by
          rw [htrdeg]
    _ =
        ((x.asIdeal.height : WithBot ℕ∞) +
          Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField)) +
            (((x'.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          rw [hheight]
          ac_rfl
    _ = topologicalKrullDimAt x +
          (((x'.asIdeal.height - x.asIdeal.height : ℕ∞) : WithBot ℕ∞)) := by
          rw [show topologicalKrullDimAt x =
              ringKrullDim (Localization.AtPrime x.asIdeal) +
                Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) from
            topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
              x]
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
            (Localization.AtPrime x.asIdeal)]

end
