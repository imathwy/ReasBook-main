import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_131_9
import stacks_proof.stacks_project.Chap10.Lemma_10_131_10
import stacks_proof.stacks_project.Chap10.Theorem_10_34_1_Hilbert_Nullstellensatz

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

noncomputable section

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [IsAlgClosed k]
variable (m : Ideal S) [m.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/- Domain-style sampling for Lemma 10.140.1:
- primary domain: the conormal sequence at a maximal ideal and the closed-point fiber of Kähler
  differentials over an algebraically closed base field;
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`,
  `finite_residueField_of_isMaximal_of_finiteType`,
  `Ideal.bijective_algebraMap_quotient_residueField`;
- best owner abstraction: the canonical conormal map
  `KaehlerDifferential.kerCotangentToTensor k S m.ResidueField`;
- primitive data: the maximal ideal `m` in the finite type `k`-algebra `S`;
- derived API: exactness of the conormal sequence, the finite closed-point residue field supplied
  by Hilbert Nullstellensatz, and the quotient-residue comparison for maximal ideals.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma for a closed point over an algebraically closed field,
  asserting equality of the cotangent-space dimension and the Kähler-fiber dimension at `m`;
- `core/canonical`: the conormal owner map `KaehlerDifferential.kerCotangentToTensor k S
  m.ResidueField` and its exactness API;
- `bridge/view`: the maximal-ideal equivalence between `S ⧸ m` and `m.ResidueField`, used only to
  present the closed-point fiber in the quotient form used downstream. -/

-- Proof sketch: the conormal exact sequence for the surjective residue map `S → m.ResidueField`
-- gives `m / m² → m.ResidueField ⊗[S] Ω[S⁄k] → Ω[m.ResidueField⁄k] → 0`. For a maximal ideal of a
-- finite type algebra over an algebraically closed field, Hilbert Nullstellensatz identifies the
-- closed-point residue field with a finite extension of `k`, and the algebraically closed base
-- hypothesis places this in the source-faithful closed-point case where the terminal Kähler term
-- vanishes. Exactness then identifies the Kähler fiber with the cotangent space, and the
-- quotient-residue comparison rewrites the result in the downstream quotient form.
/-- Lemma 10.140.1: if `k` is algebraically closed, `S` is a finite type `k`-algebra, and `m` is
a maximal ideal of `S`, then the closed-point fiber of `Ω[S⁄k]` at `m` and the cotangent space
`m / m²` have the same `κ(m) = S ⧸ m`-dimension. -/
@[stacks 00TR]
theorem finrank_kaehlerFiber_eq_finrank_cotangent :
    Module.finrank (S ⧸ m) ((S ⧸ m) ⊗[S] Ω[S⁄k]) =
      Module.finrank (S ⧸ m) m.Cotangent := by
  let eResidue : (S ⧸ m) ≃ₐ[k] m.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k (S ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  letI : Module.Finite k m.ResidueField :=
    finite_residueField_of_isMaximal_of_finiteType k m
  letI : Module.Finite k (S ⧸ m) := Module.Finite.equiv eResidue.toLinearEquiv.symm
  letI : Algebra.IsIntegral k (S ⧸ m) := Algebra.IsIntegral.of_finite k (S ⧸ m)
  let eBase : k ≃ₐ[k] (S ⧸ m) :=
    AlgEquiv.ofBijective
      (Algebra.ofId k (S ⧸ m))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k))
  let β : S ⧸ m →ₐ[k] S :=
    (Algebra.ofId k S).comp eBase.symm.toAlgHom
  have hβ : (IsScalarTower.toAlgHom k S (S ⧸ m)).comp β = AlgHom.id k (S ⧸ m) := by
    ext x
    change eBase (eBase.symm x) = x
    simpa using eBase.apply_symm_apply x
  have hsurjQuot : Function.Surjective (algebraMap S (S ⧸ m)) := by
    simpa using (Ideal.Quotient.mkₐ_surjective k m)
  have hsurjBase : Function.Surjective (algebraMap k (S ⧸ m)) := by
    simpa using eBase.surjective
  letI : Subsingleton Ω[S ⧸ m⁄k] :=
    KaehlerDifferential.subsingleton_of_surjective k (S ⧸ m) hsurjBase
  have hker : RingHom.ker (algebraMap S (S ⧸ m)) = m := by
    simpa using (Ideal.Quotient.mkₐ_ker k m)
  let eCot :
      m.Cotangent ≃ₗ[S] (RingHom.ker (algebraMap S (S ⧸ m))).Cotangent :=
    Ideal.Cotangent.equivOfEq m (RingHom.ker (algebraMap S (S ⧸ m))) hker.symm
  let cotangentToTensor :
      m.Cotangent →ₗ[S] ((S ⧸ m) ⊗[S] Ω[S⁄k]) :=
    (KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m)).comp eCot.toLinearMap
  letI : IsScalarTower k (S ⧸ m) m.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent (R := S) (I := m))
  let cotangentToTensorOverQuotient :
      m.Cotangent →ₗ[S ⧸ m] ((S ⧸ m) ⊗[S] Ω[S⁄k]) :=
    (cotangentToTensor.restrictScalars k).extendScalarsOfSurjective hsurjBase
  -- The source proof identifies the closed point with the base field, so the quotient map splits.
  have hsplit :
      Function.Exact
          (KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m))
          (KaehlerDifferential.mapBaseChange k S (S ⧸ m)) ∧
        Function.Surjective (KaehlerDifferential.mapBaseChange k S (S ⧸ m)) ∧
        ∃ l : (S ⧸ m) ⊗[S] Ω[S⁄k] →ₗ[S]
            (RingHom.ker (algebraMap S (S ⧸ m))).Cotangent,
          l ∘ₗ KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m) = LinearMap.id :=
    kaehlerDifferential_conormal_sequence_split_of_section k S (S ⧸ m) β hβ
  obtain ⟨-, -, lOwner, hlOwner⟩ := hsplit
  let leftInverse :
      ((S ⧸ m) ⊗[S] Ω[S⁄k]) →ₗ[S] m.Cotangent :=
    eCot.symm.toLinearMap.comp lOwner
  have hleftInverse :
      leftInverse.comp cotangentToTensor = LinearMap.id := by
    ext x
    have hx := LinearMap.congr_fun hlOwner (eCot x)
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    change eCot.symm (lOwner ((KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m)) (eCot x))) = x
    have hx' :
        lOwner ((KaehlerDifferential.kerCotangentToTensor k S (S ⧸ m)) (eCot x)) = eCot x := by
      simpa using hx
    rw [hx']
    exact eCot.symm_apply_apply x
  have hInjective :
      Function.Injective cotangentToTensorOverQuotient := by
    have hLeftInverseFun : Function.LeftInverse leftInverse cotangentToTensor := by
      intro x
      exact LinearMap.congr_fun hleftInverse x
    have hInjectiveS : Function.Injective cotangentToTensor := hLeftInverseFun.injective
    simpa [cotangentToTensorOverQuotient] using hInjectiveS
  -- Since `Ω[(S ⧸ m)⁄k] = 0`, exactness forces the conormal map to be surjective as well.
  have hExact :
      Function.Exact cotangentToTensor (KaehlerDifferential.mapBaseChange k S (S ⧸ m)) :=
    (kaehlerDifferential_exact_cotangent_tensor_of_surjective
      (R := k) (S := S) (S' := S ⧸ m) m hker hsurjQuot).1
  have hMapBaseChangeZero :
      ((KaehlerDifferential.mapBaseChange k S (S ⧸ m)) :
        ((S ⧸ m) ⊗[S] Ω[S⁄k]) →ₗ[S] Ω[S ⧸ m⁄k]) = 0 := by
    exact Subsingleton.elim _ _
  have hSurjective :
      Function.Surjective cotangentToTensorOverQuotient := by
    have hSurjectiveS : Function.Surjective cotangentToTensor := by
      have hKer :
          LinearMap.ker
              (((KaehlerDifferential.mapBaseChange k S (S ⧸ m)) :
                ((S ⧸ m) ⊗[S] Ω[S⁄k]) →ₗ[S] Ω[S ⧸ m⁄k])) = ⊤ := by
        rw [hMapBaseChangeZero, LinearMap.ker_zero]
      rw [← LinearMap.range_eq_top]
      rw [← Function.Exact.linearMap_ker_eq hExact]
      exact hKer
    intro x
    obtain ⟨y, hy⟩ := hSurjectiveS x
    exact ⟨y, hy⟩
  -- The conormal map is therefore a quotient-linear equivalence, and finrank is preserved.
  let eFiber :
      m.Cotangent ≃ₗ[S ⧸ m] ((S ⧸ m) ⊗[S] Ω[S⁄k]) :=
    LinearEquiv.ofBijective cotangentToTensorOverQuotient ⟨hInjective, hSurjective⟩
  simpa using eFiber.finrank_eq.symm

end
