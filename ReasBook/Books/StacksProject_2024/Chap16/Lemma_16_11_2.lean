import Mathlib
import StacksProject_2024.Chap10.Definition_10_137_10
import StacksProject_2024.Chap10.Lemma_10_97_7
import StacksProject_2024.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing

universe u v w

namespace Algebra

section

variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ] [Algebra k Λ]
variable {m : ℕ} {𝔭 : Ideal (MvPolynomial (Fin m) k)} [𝔭.IsPrime]
variable {𝔮 : Ideal Λ} [𝔮.IsPrime] {n : ℕ}
variable {D : Type w} [CommRing D] [IsArtinianRing D] [IsLocalRing D]

/- Domain-style sampling for Lemma 16.11.2.

Primary domain: localized prime quotients by maximal-ideal powers and their factorization through
local Artinian rings in the approximation step for geometrically regular `k`-algebras.

Sampled owner declarations in the surrounding project/mathlib style:
* `Localization.AtPrime` and `Localization.localRingHom` for the canonical localized source/target
  rings and the induced local map;
* `Localization.AtPrime.map_eq_maximalIdeal` and
  `pow_maximalIdeal_le_comap_pow_maximalIdeal` for the canonical maximal-ideal owner on those
  localizations and the induced quotient map API;
* `SmoothAtPrime` and `Module.Flat` for the source-smoothness and target-flatness conditions;
* `Algebra.exists_artinianLocalSubalgebraApproximation` from `Lemma_16_11_1.lean`, which exposes
  the approximation-family properties directly on a family `S : ι → Subalgebra k Λ`.

Best owner abstraction: the primitive owner here is the pair of maps
`k[y]_𝔭 / 𝔪(k[y]_𝔭)^n → D → Λ_𝔮 / 𝔪(Λ_𝔮)^n` together with the canonical localized source data.
The factorization conditions form a `Prop`-valued owner predicate on that primitive data. The
identification of these maximal ideals with the extended prime ideals remains companion data, while
finite-subset containment is extra source-facing output of Lemma `16.11.2`, not primitive owner
data.

Layering:
* `source-facing`: existence of primitive factorization data whose image contains the chosen finite
  subset `E`;
* `core/canonical`: the localized prime ideals, localized quotient rings, and the factorization
  property built from `Localization.localRingHom` and `Ideal.quotientMap`;
* `bridge/view`: the containment condition `E ⊆ range DToTarget`, which is a property of a chosen
  factorization rather than primitive owner data.
-/

local notation:max "k[y]_" 𝔭 => Localization.AtPrime 𝔭
local notation:max "Λ_" 𝔮 => Localization.AtPrime 𝔮

/-- The primitive factorization data
`k[y₁, …, yₘ]_𝔭 / 𝔪(k[y₁, …, yₘ]_𝔭)^n → D → Λ_𝔮 / 𝔪(Λ_𝔮)^n`
from Lemma `16.11.2` form a local Artinian polynomial factorization when the chosen prime is the
inverse image of `𝔮`, the induced local map on localizations is flat, the quotient map factors
through `D`, the source map is essentially smooth at the closed point of `D`, and the target map
is flat. The equality
`Ideal.map (Localization.localRingHom 𝔭 𝔮 φ.toRingHom p_eq_comap) (maximalIdeal (k[y]_𝔭)) =
  maximalIdeal (Λ_ 𝔮)`
is then the canonical localization theorem `Localization.AtPrime.map_eq_maximalIdeal`, so it is
derived API rather than primitive owner data. -/
class IsLocalArtinianPolynomialFactorization
    (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
    (sourceToD : ((k[y]_𝔭) ⧸ (maximalIdeal (k[y]_𝔭)) ^ n) →+* D)
    (DToTarget : D →+* ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) : Prop where
  /-- The chosen prime is the inverse image of `𝔮` under `φ`. -/
  p_eq_comap : 𝔭 = Ideal.comap φ.toRingHom 𝔮
  /-- The local ring map `k[y]_𝔭 → Λ_𝔮` is flat. -/
  localized_flat :
    let localMap := Localization.localRingHom 𝔭 𝔮 φ.toRingHom p_eq_comap
    localMap.Flat
  /-- The two maps factor the canonical quotient map induced by `φ`. -/
  factorization :
    let localMap := Localization.localRingHom 𝔭 𝔮 φ.toRingHom p_eq_comap
    DToTarget.comp sourceToD =
      Ideal.quotientMap
        ((maximalIdeal (Λ_ 𝔮)) ^ n)
        localMap
        (pow_maximalIdeal_le_comap_pow_maximalIdeal localMap n)
  /-- The map from the localized polynomial quotient to `D` is essentially smooth at the closed
  point of the local Artinian ring `D`. -/
  source_smoothAt_closedPoint :
    let _ : Algebra ((k[y]_𝔭) ⧸ (maximalIdeal (k[y]_𝔭)) ^ n) D := sourceToD.toAlgebra
    SmoothAtPrime
      (((k[y]_𝔭) ⧸ (maximalIdeal (k[y]_𝔭)) ^ n))
      D
      (closedPoint D)
  /-- The map `D → Λ_𝔮 / (𝔮 Λ_𝔮)^n` is flat. -/
  target_flat :
    let _ : Algebra D ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n) := DToTarget.toAlgebra
    Module.Flat D ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)

-- Proof sketch: apply Lemma `16.11.1` to the local Artinian quotient
-- `Λ_𝔮 / (𝔮 Λ_𝔮)^n` to find an essentially finite type local Artinian subalgebra containing `E`;
-- choose polynomial generators lifting a basis of differentials of its residue field and then add a
-- regular system of parameters for the remaining regular local quotient. The resulting localized
-- polynomial algebra is flat over `Λ_𝔮`, the induced quotient map factors through the chosen local
-- Artinian subalgebra, and Lemmas `10.39.9`, `10.54.4`, and `10.143.7` upgrade that factorization
-- to the required flat and essentially smooth local factorization.
/-- Lemma 16.11.2: let `k` be a field of characteristic `p > 0`, let `Λ` be a geometrically
regular `k`-algebra, let `𝔮 ⊂ Λ` be a prime ideal, let `n ≥ 1` be a natural number, and let
`E` be a finite subset of `Λ_𝔮 / 𝔪(Λ_𝔮)^n`, equivalently
`Λ_𝔮 / (𝔮 Λ_𝔮)^n`. Then there exists a localized polynomial algebra `k[y₁, …, yₘ]_𝔭` mapping to
`Λ_𝔮` whose induced quotient modulo the `n`th powers of the localized maximal ideals factors
through a local Artinian ring `D`, with the source-to-`D` map essentially smooth, the map
`D → Λ_𝔮 / 𝔪(Λ_𝔮)^n` flat, and `E` contained in the image of `D`. -/
theorem exists_localArtinianPolynomialApproximation
    {p : ℕ} [Fact p.Prime] [CharP k p] [IsGeometricallyRegular k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (n : ℕ) (hn : 1 ≤ n)
    (E : Finset ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)) :
    ∃ (m : ℕ) (φ : MvPolynomial (Fin m) k →ₐ[k] Λ)
      (𝔭 : Ideal (MvPolynomial (Fin m) k)) (_ : 𝔭.IsPrime)
      (D : Type w) (_ : CommRing D) (_ : IsArtinianRing D) (_ : IsLocalRing D)
      (sourceToD : ((k[y]_𝔭) ⧸ (maximalIdeal (k[y]_𝔭)) ^ n) →+* D)
      (DToTarget : D →+* ((Λ_ 𝔮) ⧸ (maximalIdeal (Λ_ 𝔮)) ^ n)),
      IsLocalArtinianPolynomialFactorization φ sourceToD DToTarget ∧
        ∀ x ∈ E, ∃ y : D, DToTarget y = x := by
  sorry

end

end Algebra
