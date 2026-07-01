import Mathlib
import stacks_project.Chap10.Definition_10_69_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {S : Type w} [CommRing S] [Algebra R S] [Module.Flat R S]

/- 
Domain triage:
* primary domain: quasi-regular sequences in commutative algebra and their behavior under flat
  base change;
* sampled owner API:
  `RingTheory.Sequence.IsQuasiRegular`,
  `IsBaseChange.linearMap`,
  `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`,
  `RingTheory.Sequence.IsWeaklyRegular.of_flat`;
* source-facing layer: `RingTheory.Sequence.IsQuasiRegular M rs`;
* core/canonical owner abstraction for base change: `IsBaseChange S f`;
* bridge/view split: quasi-regularity is the source-facing graded-comparison predicate, while
  flat-base-change transport is best organized first through the owner abstraction `IsBaseChange`
  and only then specialized to the canonical tensor-product model.
-/

-- Proof sketch: write quasi-regularity via the associated graded map from `10.69.0.1`. Flatness
-- identifies `(Ideal.ofList rs ^ n) • ⊤` after tensoring with the corresponding powers of the
-- extended ideal, and the graded pieces commute with tensor product. Tensoring the defining
-- isomorphism for `rs` with `S` then yields the quasi-regularity criterion for the image sequence
-- on `S ⊗[R] M`, the canonical Lean model for the textbook tensor product `M ⊗[R] S`.
namespace IsQuasiRegular

variable {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

-- Proof sketch: reinterpret quasi-regularity through the associated-graded comparison map and use
-- the owner-level base-change equivalence `hf.equiv` to transport the source graded pieces to the
-- target ones. Flatness identifies the graded pieces after scalar extension, so tensoring the
-- defining isomorphism for `M` yields the desired isomorphism for `N`.
/-- Canonical flat-base-change bridge for quasi-regular sequences along an owner-level base-change
map. The textbook tensor-product statement is the specialization `of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {rs : List R}
    (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular N (rs.map (algebraMap R S)) := sorry

-- Proof sketch: specialize `of_flat_of_isBaseChange` to the canonical tensor-product base-change
-- map `TensorProduct.mk R S M 1`, whose base-change property is `TensorProduct.isBaseChange`.
/-- Lemma 10.69.3: for a flat ring map `R → S`, an `M`-quasi-regular sequence in `R` remains
quasi-regular after extending scalars to `S`. -/
theorem of_flat {rs : List R} (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := sorry

end IsQuasiRegular

end RingTheory.Sequence
