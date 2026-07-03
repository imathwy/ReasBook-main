import Mathlib
import StacksProject_2024.Chap15.Lemma_15_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits CommRingCat

universe u

section

variable {ι R : Type u} [Finite ι] [CommRing R]
variable {P Q : Type u} {A B : ι → Type u}
variable [CommRing P] [CommRing Q] [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
variable [Algebra R P] [Algebra R Q] [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]

/- Domain-style sampling:
- primary domain: finite-type stability for finite fibre products of commutative `R`-algebras,
  expressed through pullback squares in `CommRingCat`;
- sampled owner declarations:
  `CommRingCat.pullbackCone`,
  `CommRingCat.pullbackConeIsLimit`,
  `AlgHom.equalizer`,
  `finiteType_fiberProduct_of_surjective_of_finite`;
- best owner abstraction: the source-facing data is the finite family of comparison maps together
  with a categorical pullback witness in `CommRingCat`, while the canonical owner for the
  underlying binary fibre-product ring is still the equalizer/fibre-product API from
  `Lemma_15_5_1`;
- primitive data: the families `φ`, `ψ`, the maps `f`, `g`, the pointwise surjectivity
  hypotheses, and the pullback witness `hcart`;
- derived API: the finite-type conclusion for the pullback ring `P`.

Source/core/bridge triage:
- `source-facing`: the statement about an arbitrary pullback square in `CommRingCat`;
- `core/canonical`: `CommRingCat.pullbackCone` for the categorical owner and
  `finiteType_fiberProduct_of_surjective_of_finite` for the binary algebraic fibre-product
  owner;
- `bridge/view`: passing from the abstract pullback witness `hcart` to the canonical fibre-product
  presentation used by the binary finite-type theorem. -/

-- Proof sketch: induct on the finite index type `ι`. For the inductive step, split off one index
-- `i₀`, apply the induction hypothesis to the pullback defined by the remaining family, and then
-- apply Lemma 15.5.1 to the resulting binary fibre product square with `A i₀ → B i₀`.
/-- Lemma 15.5.2: for a finite family of surjections `Aᵢ → Bᵢ` and `Q → Bᵢ` over a Noetherian
base ring `R`, any pullback ring `P` of `Q → ∏ i, B i` and `∏ i, A i → ∏ i, B i` is of finite
type over `R` as soon as `Q` and all `Aᵢ` are of finite type over `R`; finite type of each `Bᵢ`
is derived from the surjections `Q → Bᵢ`. -/
theorem finiteType_of_isPullback_pi_of_surjective
    [IsNoetherianRing R] [Algebra.FiniteType R Q]
    [∀ i, Algebra.FiniteType R (A i)]
    (φ : ∀ i, A i →ₐ[R] B i) (ψ : ∀ i, Q →ₐ[R] B i) (f : P →ₐ[R] Q)
    (g : P →ₐ[R] ∀ i, A i) (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i)) (hcart : IsPullback (ofHom f.toRingHom)
      (ofHom g.toRingHom) (ofHom (Pi.algHom R B ψ).toRingHom)
      (ofHom (Pi.algHom R B fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)).toRingHom)) :
    Algebra.FiniteType R P := sorry

end
