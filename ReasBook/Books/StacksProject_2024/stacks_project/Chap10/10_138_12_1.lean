import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.Extension

universe u v w

noncomputable section

section

variable {R : Type u} {S : Type v} {ι : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R)
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

/- Domain triage:
* primary domain: cotangent/conormal sequences for surjective polynomial presentations, after
  base change along the quotient map `S → S ⧸ IS`;
* sampled owner declarations:
  - `Algebra.Extension.cotangentComplex`;
  - `Algebra.Extension.toKaehler`;
  - `Algebra.Extension.formallySmooth_iff_split_injection`;
  - `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`;
* best owner abstraction: the extension-level presentation
  `P[hSurj] : Algebra.Extension R S` coming from the surjection `MvPolynomial ι R → S`;
* primitive data: the quotient algebra `S̄ = S ⧸ IS` and the owner maps
  `P[hSurj].cotangentComplex`, `P[hSurj].toKaehler`;
* derived API: the base-changed maps `LinearMap.baseChange S̄ ...`;
* layer triage:
  - `source-facing`: the conormal sequence modulo `I`;
  - `core/canonical`: the presentation-level owners `cotangentComplex` and `toKaehler`;
  - `bridge/view`: quotienting/base-changing those owner maps along `S → S̄`. -/

local notation "S̄" => S ⧸ Ideal.map (algebraMap R S) I

-- Proof sketch: the unquotiented cotangent complex is a complex, so
-- `toKaehler.comp cotangentComplex = 0`; after base change to `S / IS`, the same relation holds
-- for the induced maps.
/-- The two base-changed maps in the conormal sequence compose to zero. -/
theorem polynomialConormalSequenceModuloIdeal_comp_eq_zero
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    (LinearMap.baseChange S̄ P.toKaehler).comp
        (LinearMap.baseChange S̄ P.cotangentComplex) =
      0 := sorry

-- Proof sketch: the unquotiented map `P ⊗[P] Ω[P⁄R] → Ω[S⁄R]` is surjective for a surjective
-- polynomial presentation, and base change along `S → S / IS` preserves surjectivity.
/-- The right map in the base-changed conormal sequence is surjective. -/
theorem polynomialBaseChangedKaehlerDifferentialToKaehlerModuloIdeal_surjective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Surjective (LinearMap.baseChange S̄ P.toKaehler) := sorry

-- Proof sketch: apply the formal-smoothness criterion for the quotient map
-- `R ⧸ I → S ⧸ IS` to the induced surjective polynomial presentation
-- `(MvPolynomial ι R) ⧸ I → S ⧸ IS`. This gives a splitting of the base-changed conormal map, and
-- hence the displayed sequence is exact with injective left map; together with the surjectivity
-- of `polynomialBaseChangedKaehlerDifferentialToKaehlerModuloIdeal`, this yields the short exact
-- conormal sequence modulo `I`.
/-- 10.138.12.1: if the quotient map `R ⧸ I → S ⧸ IS` is formally smooth, then for a surjective
polynomial presentation `P = MvPolynomial ι R → S` the base-changed conormal sequence
`0 → J / (I J + J²) → Ω[P⁄R] ⊗[P] S / IS → Ω[S⁄R] ⊗[S] S / IS → 0`
is exact; in Lean the three terms are represented by the quotiented conormal module, the
quotiented cotangent-space term, and the base change of `Ω[S⁄R]`. -/
theorem polynomial_presentation_conormal_sequence_mod_ideal
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Injective
        (LinearMap.baseChange S̄ P.cotangentComplex) ∧
      Function.Exact
        (LinearMap.baseChange S̄ P.cotangentComplex)
        (LinearMap.baseChange S̄ P.toKaehler) := sorry

end
