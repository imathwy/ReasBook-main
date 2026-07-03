import Mathlib
import stacks_project.Chap16.Lemma_16_2_8
import stacks_project.Chap16.Lemma_16_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {B : Type v} {Λ : Type u}
variable [CommRing R] [CommRing B] [CommRing Λ]
variable [Algebra R B] [Algebra R Λ]

/- Domain-style sampling for smooth factorizations killing a finitely generated ideal:
* primary domain: commutative algebra of smooth `R`-algebras, square-zero ideals, and filtered
  colimits of smooth quotient algebras;
* sampled owner declarations:
  `Smooth R B`,
  `(algebraMap (R ⧸ I) _).IsFilteredColimitOfSmooth`,
  `exists_smooth_quotient_factorization_of_square_zero`,
  `exists_smooth_factorization_of_singularIdeal_map_eq_top`;
* best owner abstraction: this item is a source-facing bridge theorem, not a new packaged owner.
  Its canonical surface is the direct existence of a smooth factorization `B ─α→ B' ─β→ Λ`
  subject to the intrinsic ideal-theoretic conditions on `J`.

Source/core/bridge triage:
* `source-facing`: the factorization statement killing a finitely generated ideal `J ⊆ IB`;
* `core/canonical`: `Smooth`, `Ideal`, quotient algebras, and
  `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the comparison maps `α` and `β` exhibiting the refined factorization.

Primitive input data are exactly `J`, the inclusion `J ≤ I.map (algebraMap R B)`, finite
generation of `J`, and the annihilation condition `J ≤ RingHom.ker φ`. The factorization
maps are derived output data, so a wrapper structure would only duplicate the owner declarations
already present upstream in Chapter 16.
-/

-- Proof sketch: argue by induction on the number of generators of `J`, reducing to the principal
-- case. For a generator `h = ∑ εᵢ bᵢ` with `εᵢ ∈ I`, apply the equational criterion of flatness to
-- the relation `∑ εᵢ φ(bᵢ) = 0` in the flat `R`-algebra `Λ`, build the auxiliary algebra
-- `C = B[x₁, …, xₘ]/(bᵢ - ∑ aᵢⱼ xⱼ)`, factor `C → Λ` through Lemma `16.5.1`, and then lift
-- `B → C → B' ⧸ J'` to `α : B → B'` by smoothness of `B` over `R`. The imposed relations and the
-- square-zero hypothesis `I² = 0` force `α` to kill `J`.
/-- Lemma 16.5.2: let `R → Λ` be a flat ring map, let `I ⊂ R` be a square-zero ideal, and assume
`Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras. If `φ : B → Λ` is an `R`-algebra map
with `B` smooth over `R`, and if `J ⊆ IB` is a finitely generated ideal killed by `φ`, then `φ`
factors as `B ─α→ B' ─β→ Λ` with `B'` smooth over `R` and with `α` killing `J`. -/
theorem exists_smooth_factorization_killing_ideal_of_square_zero
    (I : Ideal R) [Module.Flat R Λ] [Smooth R B] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : B →ₐ[R] Λ) (J : Ideal B)
    (hJ : J ≤ I.map (algebraMap R B)) (hJfg : J.FG)
    (hφJ : J ≤ RingHom.ker φ) :
    ∃ (B' : Type (max u v)) (_ : CommRing B') (_ : Algebra R B') (_ : Smooth R B')
      (α : B →ₐ[R] B') (β : B' →ₐ[R] Λ),
      J ≤ RingHom.ker α ∧ β.comp α = φ := sorry

end

end Algebra
