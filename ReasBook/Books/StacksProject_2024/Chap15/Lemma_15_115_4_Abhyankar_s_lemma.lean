import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} {K : Type u} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable (hinj : Function.Injective (algebraMap A B))
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "B1" => A1 ⊗[A] B

-- Proof sketch: for a local homomorphism of local rings, the inverse image of the maximal ideal of
-- the target is the maximal ideal of the source; apply this to `algebraMap A B`.
/-- The maximal ideal of the target discrete valuation ring contracts to the maximal ideal of the
source under a local extension of discrete valuation rings. -/
lemma comap_maximalIdeal_of_isLocalHom :
    Ideal.comap (algebraMap A B) (maximalIdeal B) = maximalIdeal A := sorry

/-- The induced map on residue fields for the extension `A ⊂ B` of discrete valuation rings. -/
noncomputable abbrev baseResidueFieldMap :
    Ideal.ResidueField (maximalIdeal A) →+* Ideal.ResidueField (maximalIdeal B) :=
  Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
    comap_maximalIdeal_of_isLocalHom.symm

/-- The canonical algebra structure on the residue field of `B` over the residue field of `A`. -/
noncomputable instance baseResidueFieldAlgebra :
    Algebra (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField (maximalIdeal B)) :=
  baseResidueFieldMap.toAlgebra

/-- The localization of the tensor base change `B1 = A1 ⊗[A] B` at a prime above `m` is naturally
an algebra over the localization of `A1` at `m`. -/
noncomputable instance localizedIntegralClosureTensorBaseChangeAlgebra
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] :
    Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
  (Localization.localRingHom m n (algebraMap A1 B1) Ideal.LiesOver.over).toAlgebra

/-- The canonical local map from `(A1)_m` to `(B1)_n` for a prime `n` of `B1` lying over
`m : Ideal A1`. -/
noncomputable abbrev localizedIntegralClosureTensorBaseChangeMap
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] :
    Localization.AtPrime m →+* Localization.AtPrime n :=
  algebraMap (Localization.AtPrime m) (Localization.AtPrime n)

/-- The assertion that the localized tensor-base-change map `(A1)_m → (B1)_n` is formally smooth
for the maximal-ideal-adic topology on `(B1)_n`. -/
abbrev localizedTensorBaseChangeFormallySmoothForAdic
    (m : Ideal A1) [m.IsPrime] (n : Ideal B1) [n.IsPrime] [n.LiesOver m] : Prop :=
  let S := Localization.AtPrime n
  let _ : CommRing S := inferInstance
  RingHom.formally_smooth_for_adic.{w, max v w, max v w}
    (show Localization.AtPrime m →+* S from
      localizedIntegralClosureTensorBaseChangeMap m n)
    (show Ideal S from maximalIdeal S)

-- Proof sketch: after adjoining an `e`th root of a suitable unit, reduce to the Kummer case
-- `K1 = K[π^(1/e)]`. Lemma `15.115.2` identifies the corresponding integral closure of `A` as a
-- totally ramified degree-`e` extension, and the coprimality hypothesis makes the induced
-- extension on the `B`-side finite étale. Then the local factors above `m` are weakly unramified
-- with separable residue field over `(A1)_m`, so Lemma `15.112.5` yields formal smoothness for
-- the maximal-ideal-adic topology.
/-- Lemma 15.115.4 (Abhyankar's lemma): let `A ⊂ B` be an extension of discrete valuation rings,
let `K` be a fraction field of `A`, and let `K1 / K` be a finite extension. Write
`A1 = integralClosure A K1` and `B1 = A1 ⊗[A] B`. Assume the residue-field extension
`ResidueField (maximalIdeal B) / ResidueField (maximalIdeal A)` is separable and that the
ramification index of `A ⊂ B` is prime to the residue characteristic of `A`. If `m` is a maximal
ideal of `A1` above `maximalIdeal A` such that the ramification index of `A ⊂ B` divides the
ramification index of `A ⊂ (A1)_m` (equivalently `Ideal.ramificationIdx (maximalIdeal A) m`),
then every maximal ideal `n` of `B1` lying over `m` yields a formally smooth local extension
`(A1)_m → (B1)_n` for the `maximalIdeal (Localization.AtPrime n)`-adic topology. -/
theorem formallySmoothForAdic_localized_tensorBaseChange_of_tame_and_dvd_ramificationIdx
    (hsep : Algebra.IsSeparable
      (Ideal.ResidueField (maximalIdeal A)) (Ideal.ResidueField (maximalIdeal B)))
    (hprime : ∀ (p : ℕ) [Fact p.Prime] [CharP (Ideal.ResidueField (maximalIdeal A)) p],
      Nat.Coprime (Ideal.ramificationIdx (maximalIdeal A) (maximalIdeal B)) p)
    (m : Ideal A1) [m.IsMaximal] [m.LiesOver (maximalIdeal A)]
    (hmul : Ideal.ramificationIdx (maximalIdeal A) (maximalIdeal B) ∣
      Ideal.ramificationIdx (maximalIdeal A) m) :
    ∀ (n : Ideal B1) [n.IsMaximal] [n.LiesOver m],
      localizedTensorBaseChangeFormallySmoothForAdic m n := sorry

end
