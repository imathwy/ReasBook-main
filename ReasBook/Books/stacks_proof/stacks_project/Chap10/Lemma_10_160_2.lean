import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_97_8
import stacks_proof.stacks_project.Chap10.Lemma_10_156_1
import stacks_proof.stacks_project.Chap10.Lemma_10_156_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing AdicCompletion
open scoped TensorProduct

/-
Domain-style sampling:
* primary domain: complete local rings, finite algebras over them, and the canonical product
  decomposition indexed by primes over the maximal ideal;
* sampled owner declarations in the chapter/domain:
  `IsCompleteLocalRing`,
  `IsLocalRing.quotient`,
  `Algebra.QuasiFinite.finite_primesOver`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion`,
  `Ideal.primesOver`;
* best owner abstraction:
  - for part `(1)`, the chapter owner `IsCompleteLocalRing`;
  - for part `(2)`, the canonical `maximalIdeal R`-fiber `((maximalIdeal R).primesOver S)` and the
    associated completed-local factors, rather than an ad hoc existential package of unnamed rings;
* primitive data:
  - part `(1)`: a complete local ring `R` and a proper quotient ideal `I`;
  - part `(2)`: a finite `R`-algebra `S` over a Noetherian complete local base;
* derived API:
  - quotient stability of the owner `IsCompleteLocalRing`;
  - the product decomposition of `S` as the canonical product of the completed localizations at
    primes over `maximalIdeal R`, with finiteness of that owner index set supplied by the
    canonical theorem `Algebra.QuasiFinite.finite_primesOver`.

Layer classification:
* `quotient_isCompleteLocalRing` is `source-facing`;
* `finiteProductOfNoetherianCompleteLocalRings_of_finite` is `bridge/view`: it records the source
  finite-product conclusion through the chapter's canonical `primesOver`-indexed completion owner.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- The quotient-local part is straightforward, so the remaining frontier is the adic-completeness
owner for the image of the maximal ideal. -/
/-- Helper for Lemma 10.160.2: for a proper quotient of a local ring, the maximal ideal of the
quotient is the image of the maximal ideal of the source. -/
lemma quotient_maximalIdeal_eq_map (I : Ideal R) [IsLocalRing (R ⧸ I)] :
    Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) := by
  -- Proof comment: once the quotient is known to be local, surjectivity identifies its maximal
  -- ideal with the image of the source maximal ideal.
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Helper for Lemma 10.160.2: the `maximalIdeal R`-adic completion of the quotient `R ⧸ I`,
viewed as an `R`-module, identifies canonically with the quotient itself. -/
noncomputable def quotient_completion_linearEquiv (I : Ideal R) :
    AdicCompletion (maximalIdeal R) (R ⧸ I) ≃ₗ[R] R ⧸ I :=
  let eCompletion :
      AdicCompletion (maximalIdeal R) (R ⧸ I) ≃ₗ[R]
        AdicCompletion (maximalIdeal R) R ⊗[R] (R ⧸ I) :=
    (LinearEquiv.restrictScalars R
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) (R ⧸ I))).symm
  let eTensor :
      (R ⧸ I) ≃ₐ[R] AdicCompletion (maximalIdeal R) R ⊗[R] (R ⧸ I) :=
    (Algebra.TensorProduct.lid R (R ⧸ I)).symm.trans
      (Algebra.TensorProduct.congr
        (AdicCompletion.ofAlgEquiv (maximalIdeal R))
        (show (R ⧸ I) ≃ₐ[R] (R ⧸ I) from AlgEquiv.refl))
  eCompletion.trans eTensor.symm.toLinearEquiv

/-- Helper for Lemma 10.160.2: the quotient-completion equivalence sends the canonical completion
class of `x` back to `x`. -/
lemma quotient_completion_linearEquiv_of (I : Ideal R) (x : R ⧸ I) :
    quotient_completion_linearEquiv (R := R) I
        (AdicCompletion.of (maximalIdeal R) (R ⧸ I) x) = x := by
  -- Proof comment: the finite-module tensor/completion comparison sends `of x` to `1 ⊗ x`,
  -- the base-completion equivalence sends `1` back to `1`, and `TensorProduct.lid` evaluates
  -- `1 ⊗ x` to `x`.
  simp [quotient_completion_linearEquiv]

/-- Helper for Lemma 10.160.2: as an `R`-module, the quotient `R ⧸ I` is complete for the
`maximalIdeal R`-adic topology. -/
lemma quotient_isAdicComplete_maximalIdeal (I : Ideal R) :
    IsAdicComplete (maximalIdeal R) (R ⧸ I) := by
  have hof_eq :
      (AdicCompletion.of (maximalIdeal R) (R ⧸ I) :
          (R ⧸ I) →ₗ[R] AdicCompletion (maximalIdeal R) (R ⧸ I)) =
        (quotient_completion_linearEquiv (R := R) I).symm.toLinearMap := by
    -- Proof comment: apply the constructed equivalence to both sides; both images are the source
    -- element of the quotient by the previous computation.
    apply LinearMap.ext
    intro x
    apply (quotient_completion_linearEquiv (R := R) I).injective
    simp [quotient_completion_linearEquiv_of]
  -- Proof comment: once the completion map is identified with the inverse equivalence, its
  -- bijectivity is immediate and `of_bijective_iff` turns that into adic completeness.
  exact (AdicCompletion.of_bijective_iff).mp <| by
    simpa [hof_eq] using (quotient_completion_linearEquiv (R := R) I).symm.bijective

/-- Helper for Lemma 10.160.2: the remaining source-faithful completeness step is to show that the
proper quotient is adically complete for the image of the source maximal ideal. -/
lemma quotient_isAdicComplete_mapped_maximalIdeal (I : Ideal R) (_hI : I ≠ ⊤) :
    IsAdicComplete (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) (R ⧸ I) := by
  -- Route correction: the old closedness route tried to prove that `I` is closed in the
  -- `maximalIdeal R`-adic topology. The source proof instead uses that `R ⧸ I` is a finite
  -- `R`-module, hence complete as an `R`-module, and then transports completeness across the
  -- quotient algebra map.
  -- Proof comment: first read the quotient as complete for the source maximal ideal, then rewrite
  -- that completeness along `R → R ⧸ I` to the image ideal.
  exact
    (IsAdicComplete.map_algebraMap_iff
      (R := R) (S := R ⧸ I) (I := maximalIdeal R) (M := R ⧸ I)).2 <|
      quotient_isAdicComplete_maximalIdeal (R := R) I

-- Proof sketch: the quotient of a local ring by a proper ideal is local, and maximal-ideal adic
-- completeness descends along quotient maps in the Noetherian setting of the source lemma.
/-- Lemma 10.160.2 (1): if `I` is a proper ideal of a Noetherian complete local ring `R`, then the
quotient `R ⧸ I` is again a complete local ring. -/
@[stacks 0325]
theorem quotient_isCompleteLocalRing (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := by
  letI : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
  have hcomplete : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I) := by
    -- Proof comment: rewrite the quotient maximal ideal into the mapped source maximal ideal so
    -- that the completeness input is stated on the canonical quotient map.
    rw [← quotient_maximalIdeal_eq_map (R := R) I]
    exact quotient_isAdicComplete_mapped_maximalIdeal (R := R) I hI
  letI : IsAdicComplete (maximalIdeal (R ⧸ I)) (R ⧸ I) := hcomplete
  -- Proof comment: the chapter owner `IsCompleteLocalRing` is exactly locality plus maximal-ideal
  -- adic completeness.
  exact
    { toIsLocalRing := IsLocalRing.quotient I hI
      toIsAdicComplete := hcomplete }

end

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
variable {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S]

attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right

local notation "Rₚ" => Localization.AtPrime (maximalIdeal R)
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S (Ideal.primeCompl (maximalIdeal R)))
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)
local notation "Rₚ^" => AdicCompletion (maximalIdeal Rₚ) Rₚ
local notation "Sₚ^" => AdicCompletion pSₚ Sₚ
private abbrev CompletionFactors : Type u :=
  ∀ q : (maximalIdeal R).primesOver S,
    AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)
private abbrev closedPoint : PrimeSpectrum R :=
  ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩

omit [IsNoetherianRing R] in
private theorem localizedBase_isAdicComplete :
    IsAdicComplete (maximalIdeal Rₚ) Rₚ := by
  rw [← IsAdicComplete.congr_ringEquiv
    (maximalIdeal Rₚ)
    ((IsLocalization.algEquiv (maximalIdeal R).primeCompl Rₚ R).toRingEquiv)]
  simpa [IsLocalRing.map_ringEquiv_maximalIdeal] using
    (inferInstance : IsAdicComplete (maximalIdeal R) R)

-- Proof sketch: specialize Lemma `10.97.8` to the closed point `p = maximalIdeal R`. The local
-- ring `R_(maximalIdeal R)` identifies canonically with `R`, and since `R` is complete local, so
-- does its maximal-ideal completion. After these owner-level identifications, the tensor term
-- `R^∧ ⊗[R] S` reduces via `TensorProduct.lid` to `S`. The finiteness of the index owner
-- `((maximalIdeal R).primesOver S)` is already the canonical theorem
-- `Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) (maximalIdeal R)`.
/-- Lemma 10.160.2 (2): for a finite algebra over a Noetherian complete local ring, the target
ring is canonically the product of the completed localizations at the primes lying over the
maximal ideal of the base, indexed by the owner set `((maximalIdeal R).primesOver S)`. -/
@[stacks 0325]
noncomputable def finiteProductOfNoetherianCompleteLocalRings_of_finite :
    S ≃+* ∀ q : (maximalIdeal R).primesOver S,
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) := by
  change S ≃+* CompletionFactors
  letI : IsAdicComplete (maximalIdeal Rₚ) Rₚ := localizedBase_isAdicComplete
  letI : IsScalarTower R Rₚ^ Rₚ^ := IsScalarTower.right
  let eBase : R ≃ₐ[R] Rₚ^ :=
    (IsLocalization.algEquiv (maximalIdeal R).primeCompl Rₚ R).symm.trans <|
      (AdicCompletion.ofAlgEquiv (maximalIdeal Rₚ)).restrictScalars R
  let eTensor : S ≃ₐ[R] Rₚ^ ⊗[R] S :=
    (Algebra.TensorProduct.lid R S).symm.trans
      (Algebra.TensorProduct.congr eBase (show S ≃ₐ[R] S from AlgEquiv.refl))
  let ePi : Rₚ^ ⊗[R] S ≃+* CompletionFactors :=
    completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion S closedPoint
  exact eTensor.toRingEquiv.trans <|
    ePi

end
