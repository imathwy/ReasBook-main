import Mathlib
import StacksProject_2024.Chap15.Definition_15_30_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped TensorProduct

namespace RingTheory.Sequence

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

variable {M N : Type u} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/- Domain triage:
* primary domain: module-valued regularity predicates defined by Koszul homology and their
  behavior under flat base change;
* sampled owner API: `IsH1RegularOn`, `IsKoszulRegularOn`, `IsBaseChange`, `TensorProduct.isBaseChange`,
  and the earlier chapter base-change pattern `IsQuasiRegular.of_flat_of_isBaseChange`;
* owner abstraction: the source-facing owners are `IsH1RegularOn` and `IsKoszulRegularOn`, while
  `IsBaseChange S f` is the core/canonical owner for the chosen base-change realization;
* primitive data vs derived API: the primitive content here is the owner-level transport across an
  arbitrary `IsBaseChange S f`; the tensor-product statements are derived bridge/view
  specializations obtained from `TensorProduct.isBaseChange`.
-/

namespace IsH1RegularOn

-- Proof sketch: identify the Koszul complex on the image family `algebraMap R S ∘ f` with the
-- base change of the Koszul complex on `f` along the owner map `M →ₗ[R] N`. Since `S` is flat over
-- `R`, tensoring with `S` preserves the vanishing of first homology, so `H₁`-regularity descends
-- across any canonical base-change realization.
/-- Lemma 15.30.5 (1), owner form: `H_1`-regularity is preserved by flat base change along an
owner-level base-change map. The textbook tensor-product statement is the specialization
`IsH1RegularOn.of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {r : ℕ}
    {s : Fin r → R} (hreg : IsH1RegularOn M s) :
    IsH1RegularOn N (fun i ↦ algebraMap R S (s i)) := sorry

/-- Lemma 15.30.5 (1): if `s` is an `M`-`H_1`-regular sequence over `R`, then its image in `S` is
an `S ⊗[R] M`-`H_1`-regular sequence after flat base change. -/
theorem of_flat {r : ℕ} {s : Fin r → R} (hreg : IsH1RegularOn M s) :
    IsH1RegularOn (S ⊗[R] M) (fun i ↦ algebraMap R S (s i)) := by
  simpa using hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)

end IsH1RegularOn

namespace IsKoszulRegularOn

-- Proof sketch: identify `(K^•(s) ⊗ M)` after applying the owner base-change map
-- `M →ₗ[R] N` with the tensor Koszul complex over `S` on the image family `algebraMap R S ∘ s`.
-- Flatness makes homology commute with this base change, so vanishing of all positive homology
-- groups is preserved across any canonical base-change realization.
/-- Lemma 15.30.5 (2), owner form: Koszul-regularity is preserved by flat base change along an
owner-level base-change map. The textbook tensor-product statement is the specialization
`IsKoszulRegularOn.of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {r : ℕ}
    {s : Fin r → R} (hreg : IsKoszulRegularOn M s) :
    IsKoszulRegularOn N (fun i ↦ algebraMap R S (s i)) := sorry

/-- Lemma 15.30.5 (2): if `s` is an `M`-Koszul-regular sequence over `R`, then its image in `S`
is an `S ⊗[R] M`-Koszul-regular sequence after flat base change. -/
theorem of_flat {r : ℕ} {s : Fin r → R} (hreg : IsKoszulRegularOn M s) :
    IsKoszulRegularOn (S ⊗[R] M) (fun i ↦ algebraMap R S (s i)) := by
  simpa using hreg.of_flat_of_isBaseChange (TensorProduct.isBaseChange R M S)

end IsKoszulRegularOn

end RingTheory.Sequence
