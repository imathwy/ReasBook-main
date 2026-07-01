import Mathlib
import stacks_project.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open KaehlerDifferential
open scoped TensorProduct

universe u v

namespace Algebra

noncomputable section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]

/- Domain-style sampling:
* primary domain: local geometric regularity in characteristic `p`, expressed through a chosen
  polynomial map `k[y₁, …, yₘ] → A`, its induced localization at the inverse-image of the maximal
  ideal, and the cotangent-theoretic differential family over a finitely generated residue-field
  subextension;
* sampled owner declarations:
  - `IsGeometricallyRegular`,
  - `Localization.AtPrime`,
  - `Localization.localRingHom`,
  - `Ideal.Fiber`,
  - `closedFiberQuotAlgEquiv`,
  - `KaehlerDifferential.D`,
  - `LinearIndependent`,
  - `Submodule.span`,
  - `IntermediateField`;
* best owner abstraction: this file is `source-facing`, and the conclusion should be stated for
  the canonical local map from the localized polynomial ring
  `Localization.AtPrime (Ideal.comap φ.toRingHom (maximalIdeal A))` to `A`; the matching closed
  fiber should live on the canonical owner `Ideal.Fiber (maximalIdeal Aφ) A`, while the explicit
  quotient of `A` by the image of the source maximal ideal under that map is only the companion
  bridge/view supplied upstream by `closedFiberQuotAlgEquiv`; the finitely generated residue-field
  subextension should be carried by the canonical owner `IntermediateField k (ResidueField A)`;
* primitive data vs. derived API:
  - primitive data: `m`, `φ`, the chosen generators in
    `F : IntermediateField k (ResidueField A)`, the finite-generation hypothesis `F.FG`, the
    residue-field compatibility, and the differential family together with its linear independence
    and spanning;
  - derived API: the inverse-image prime
    `Ideal.comap φ.toRingHom (maximalIdeal A)`, the canonical localized map
    `Localization.AtPrime 𝔭 →+* A`, and the quotient presentation of its canonical closed fiber.

Source/core/bridge triage:
* `source-facing`: the theorem below;
* `core/canonical`: `IsGeometricallyRegular`, `Localization.AtPrime`,
  `Localization.localRingHom`, `Localization.algEquiv`, `Ideal.Fiber`,
  `KaehlerDifferential.D`, `LinearIndependent`, and `Submodule.span`;
* `bridge/view`: the derived prime ideal of `φ` and the quotient presentation of the closed fiber.
-/

section LocalRingLocalization

variable {A : Type v} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

attribute [local instance] self_isLocalization_primeCompl_maximalIdeal

end LocalRingLocalization

private instance localRing_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A :=
  self_isLocalization_primeCompl_maximalIdeal

variable {p : ℕ} [Fact p.Prime] [CharP k p]

section LocalizedPolynomialSubextensionMap

variable (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] A)

local notation "pφ" => Ideal.comap φ.toRingHom (maximalIdeal A)
local notation "Aφ" => Localization.AtPrime pφ

/-- The canonical local map from the localized polynomial presentation
`Localization.AtPrime (Ideal.comap φ.toRingHom (maximalIdeal A))` to `A`. -/
noncomputable def localizedPolynomialSubextensionMap : Aφ →+* A :=
  ((Localization.algEquiv (maximalIdeal A).primeCompl A).toRingHom).comp
    (Localization.localRingHom pφ (maximalIdeal A) φ.toRingHom rfl)

local instance localizedPolynomialSubextensionMapAlgebra : Algebra Aφ A :=
  (localizedPolynomialSubextensionMap m φ).toAlgebra

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal Aφ) A

private instance polynomialSubextensionPrime_isPrime :
    (Ideal.comap φ.toRingHom (maximalIdeal A)).IsPrime := by
  let _ : (maximalIdeal A).IsPrime := (maximalIdeal.isMaximal A).isPrime
  exact Ideal.comap_isPrime φ.toRingHom (maximalIdeal A)

-- Proof sketch: apply Proposition `15.35.1` to the localized polynomial source
-- `k[y₁, …, yₘ]_𝔭`, using that a polynomial algebra over a field is geometrically regular and that
-- the differentials `D k F (y i)` are linearly independent and span `Ω[F⁄k]`, so they identify the
-- residue-field cotangent map with the inclusion from
-- the finitely generated subextension `F ⊆ κ(A)`. The injectivity criterion then implies that the
-- localized map is flat and that the canonical closed fiber of `Aφ → A`, equivalently the
-- quotient of `A` by the image of the maximal ideal of `Aφ`, is a regular local ring.
/-- Lemma 15.35.2: let `k` be a field of characteristic `p > 0`, let `A` be a Noetherian local
`k`-algebra that is geometrically regular over `k`, and let `F ⊆ κ(A)` be a finitely generated
subextension with a polynomial presentation `k[y₁, …, yₘ] → A` whose residue-field values lie in
`F` and whose differentials are linearly independent and span `Ω[F⁄k]`. Then the localized map
`Aφ → A`, with `Aφ = Localization.AtPrime pφ` and `pφ = φ⁻¹(maximalIdeal A)`, is flat and its
canonical closed fiber `Ideal.Fiber (maximalIdeal Aφ) A`, equivalently the quotient
`A / Ideal.map (Aφ → A) (maximalIdeal Aφ)`, is a regular local ring. -/
theorem localizedPolynomialSubextensionMap_flat_and_regular_closedFiber_of_geometricallyRegularLocalRing
    [IsGeometricallyRegular k A]
    (F : IntermediateField k (ResidueField A)) (hF : F.FG)
    (y : Fin m → F)
    (hresidue :
      ∀ i, residue A (φ (MvPolynomial.X i)) = algebraMap F (ResidueField A) (y i))
    (hy : LinearIndependent F (D k F ∘ y))
    (hspan : Submodule.span F (Set.range (D k F ∘ y)) = ⊤) :
    (localizedPolynomialSubextensionMap m φ).Flat ∧ IsRegularLocalRing ClosedFiber := by
  sorry

end LocalizedPolynomialSubextensionMap

end

end Algebra
