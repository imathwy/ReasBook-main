import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_160_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_156_1

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

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R]

-- Proof sketch: the quotient of a local ring by a proper ideal is local, and maximal-ideal adic
-- completeness descends along quotient maps.
/-- Lemma 10.160.2 (1): if `I` is a proper ideal of a complete local ring `R`, then the quotient
`R ⧸ I` is again a complete local ring. -/
theorem quotient_isCompleteLocalRing (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := sorry

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
