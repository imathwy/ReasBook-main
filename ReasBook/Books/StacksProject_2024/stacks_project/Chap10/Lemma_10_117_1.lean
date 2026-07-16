import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_57_8
import StacksProject_2024.stacks_project.Chap10.Definition_10_59_6
import StacksProject_2024.stacks_project.Chap10.Definition_10_59_8
import StacksProject_2024.stacks_project.Chap10.Proposition_10_60_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_114_6

open Filter Ideal HomogeneousIdeal IsLocalRing TopologicalSpace

universe u

noncomputable section

section

variable {k : Type u} [Field k]
variable {S : Type u} [CommRing S] [Algebra k S]
variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

local notation "S₊" => HomogeneousIdeal.irrelevant 𝒜

/-
Domain-style sampling:
* primary domain: standard graded algebras over a field, their irrelevant maximal ideal, and the
  local Hilbert function and Hilbert-Samuel polynomial of the corresponding local ring;
* sampled owner declarations:
  `minimalPrimes`,
  `Algebra.adjoin`,
  `finiteType_iff_irrelevant_fg`,
  `isHomogeneous_of_mem_minimalPrimes`,
  `Ideal.hilbertSamuelPhi`,
  `hilbertSamuelPolynomialDegree`,
  `topologicalKrullDimAt_closedPoint_eq_ringKrullDim_localizationAtMaximal`;
* best owner abstraction: the source-facing graded-ring input for this lemma is the primitive
  ring-level data `Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤`, `Algebra.FiniteType (𝒜 0) S`, and the
  degree-zero identification `k ≃ₐ[k] 𝒜 0`; minimal primes are organized by the owner
  `minimalPrimes S`, and the local Hilbert-function and dimension statements are organized by the
  existing owners `Ideal.hilbertSamuelPhi`, `hilbertSamuelPolynomialDegree`, `MaximalSpectrum`,
  `PrimeSpectrum`, and `Localization.AtPrime`;
* primitive data: generation in degree `1`, finite type over `𝒜 0`, and the canonical degree-zero
  identification `zeroIso : k ≃ₐ[k] 𝒜 0`;
* derived API: finite type over `k`, maximality of the irrelevant ideal, containment of minimal
  primes in that ideal, and the local/global dimension and Hilbert-function comparisons at the
  corresponding canonical point of `MaximalSpectrum S`.

Source/core/bridge triage:
* `source-facing`: the textbook assertions of Lemma `10.117.1`;
* `core/canonical`: `Algebra.adjoin`, `Algebra.FiniteType`, `Ideal.hilbertSamuelPhi`,
  `hilbertSamuelPolynomialDegree`, `topologicalKrullDimAt`, `MaximalSpectrum`, and
  `Localization.AtPrime`;
* `bridge/view`: the finite-type transfer from `𝒜 0` to `k` through `zeroIso`, the canonical
  maximal-spectrum point with underlying ideal `S₊.toIdeal`, and the comparison from the local
  Hilbert function of its localization to the function `d ↦ dimₖ(S_d)`.
-/

/-- Derived bridge: finite type over `𝒜 0`, together with the degree-zero identification
`k ≃ₐ[k] 𝒜 0`, canonically yields the finite-type instance `Algebra.FiniteType k S`. -/
theorem finiteType_of_degreeZeroIso
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    Algebra.FiniteType k S := by
  rw [← RingHom.finiteType_algebraMap]
  have h0S : (algebraMap (𝒜 0) S).FiniteType := by
    rw [RingHom.finiteType_algebraMap]
    exact hfiniteType
  have hk0 : (algebraMap k (𝒜 0)).FiniteType := by
    convert RingHom.FiniteType.of_surjective zeroIso.toAlgHom.toRingHom zeroIso.surjective using 1
    ext r
    simpa using (congrArg (fun x : 𝒜 0 ↦ (x : S)) (zeroIso.commutes r)).symm
  exact RingHom.FiniteType.comp h0S hk0

/-- If the degree-zero piece is identified with the field `k`, then the irrelevant ideal is
maximal. -/
theorem irrelevant_isMaximal
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    S₊.toIdeal.IsMaximal := by
  sorry

/-- The canonical closed point of `Spec(S)` defined by the irrelevant ideal. -/
abbrev irrelevantClosedPoint
    (zeroIso : k ≃ₐ[k] 𝒜 0) : MaximalSpectrum S :=
  ⟨S₊.toIdeal, irrelevant_isMaximal 𝒜 zeroIso⟩

/-- Every minimal prime of a graded ring is homogeneous. This is the canonical subtype-facing
companion to `isHomogeneous_of_mem_minimalPrimes`. -/
theorem minimalPrime_isHomogeneous
    (p : minimalPrimes S) :
    p.1.IsHomogeneous 𝒜 := by
  simpa using isHomogeneous_of_mem_minimalPrimes 𝒜 p.2

/-- If the degree-zero piece is identified with the field `k`, then every minimal prime of `S` is
contained in the irrelevant ideal. Together with `minimalPrime_isHomogeneous`, this is clause `(2)`
of Lemma `10.117.1`. -/
theorem minimalPrime_le_irrelevant
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (p : minimalPrimes S) :
    p.1 ≤ S₊.toIdeal := by
  sorry

/-- If `S` is finite type over `𝒜 0` and `𝒜 0 ≃ k`, then at the closed point of `Spec(S)`
corresponding to the irrelevant ideal, the local dimension equals the global dimension of `S`. -/
theorem ringKrullDim_eq_topologicalKrullDimAt_irrelevant_closedPoint
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    ringKrullDim S =
      topologicalKrullDimAt (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum := by
  let _ : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  sorry

/-- If `S` is finite type over `𝒜 0` and `𝒜 0 ≃ k`, then the localization of `S` at the
irrelevant ideal `S₊.toIdeal` has the same Krull dimension as `S`. -/
theorem ringKrullDim_eq_ringKrullDim_irrelevant_localization
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0) :
    ringKrullDim S =
      ringKrullDim
        (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) := by
  let _ : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  sorry

/-- If `S` is generated in degree `1`, finite type over `𝒜 0`, and `𝒜 0 ≃ k`, then the local ring
obtained by localizing at the irrelevant ideal `S₊.toIdeal` has the same Hilbert function as the
graded ring `S`: its Hilbert-Samuel `φ`-function is exactly `d ↦ dimₖ(S_d)`. -/
theorem hilbertSamuelPhi_eq_degreePieceFinrank_of_irrelevant_localization
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (d : ℕ) :
    φ_
        (maximalIdeal
          (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal))
        (Localization.AtPrime (irrelevantClosedPoint 𝒜 zeroIso).toPrimeSpectrum.asIdeal) d =
      (Module.finrank k (𝒜 d) : ℕ∞) := by
  sorry

/-- Lemma 10.117.1: if `S` is generated in degree `1`, finite type over `S₀`, and `S₀ ≃ k`, then
any polynomial that eventually agrees with `d ↦ dimₖ(S_d)` computes the dimension of `S` by the
exact canonical degree formula `P.degree.succ`, which already gives `0` for the zero polynomial. -/
theorem ringKrullDim_eq_degree_succ_of_eventuallyEq_degreePieceFinrank
    (hgenerated : Algebra.adjoin (𝒜 0) (𝒜 1 : Set S) = ⊤)
    (hfiniteType : Algebra.FiniteType (𝒜 0) S)
    (zeroIso : k ≃ₐ[k] 𝒜 0)
    (P : Polynomial ℚ)
    (hP : ∀ᶠ d : ℕ in atTop,
      P.eval (d : ℚ) = (Module.finrank k (𝒜 d) : ℚ)) :
    ringKrullDim S = P.degree.succ := by
  let _ : Algebra.FiniteType k S :=
    finiteType_of_degreeZeroIso 𝒜 hfiniteType zeroIso
  sorry

end
