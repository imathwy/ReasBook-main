import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_32_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct Algebra.TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
Domain triage:
- primary domain: surjective ring maps, the induced map on prime spectra and residue fields, and
  stability of the kernel under tensor-product base change;
- sampled owner declarations: `PrimeSpectrum.isHomeomorph_comap`,
  `RingHom.SurjectiveOnStalks.residueFieldMap_bijective`,
  `Algebra.TensorProduct.includeLeft_surjective`,
  `Algebra.TensorProduct.rTensor_ker`,
  `Algebra.TensorProduct.includeRight`,
  `Algebra.TensorProduct.includeLeft`,
  `Ideal.map_isLocallyNilpotent`;
- best owner abstraction: parts (1)–(3) are direct recalls of their canonical owners, and for
  clause (4) the `core/canonical` owner is the tensor-product inclusion
  `Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] S`, while the `source-facing` layer keeps
  the chosen ring maps `f : R →+* S` and `f' : R →+* R'` explicit and derives the base-changed map
  from them; the proof first establishes the symmetric owner theorem for
  `Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗[R] R'` and then transports it across
  `TensorProduct.comm`;
- primitive data: ring maps `f : R →+* S` and `f' : R →+* R'`, surjectivity of `f`, and local
  nilpotence of `RingHom.ker f`;
  derived API: the homeomorphism, stalk and residue-field transport, surjectivity after base
  change, the owner theorem for `includeRight`, the textbook-order owner bridge, and the
  source-facing base-change theorem with explicit `f` and `f'`.
-/

/- Lemma 10.46.1 (1): the Stacks source assumes `f : R →+* S` is surjective with locally
nilpotent kernel. Surjectivity is the special case of the canonical hypothesis
`∀ x : S, ∃ n > 0, x ^ n ∈ f.range` obtained by taking `n = 1`, so the homeomorphism statement is
the mathlib theorem `PrimeSpectrum.isHomeomorph_comap`. -/
recall PrimeSpectrum.isHomeomorph_comap

/- Lemma 10.46.1 (2): the residue-field statement in the surjective case is obtained by combining
surjectivity on stalks for surjective ring maps with the canonical residue-field bijection for maps
surjective on stalks. -/
recall RingHom.surjectiveOnStalks_of_surjective

/- Companion recall for Lemma 10.46.1 (2): once `f : R →+* S` is surjective on stalks, the
induced map on residue fields over corresponding primes is bijective. -/
recall RingHom.SurjectiveOnStalks.residueFieldMap_bijective

/- Lemma 10.46.1 (3): after base change along `R → R'`, the canonical map
`R' → R' ⊗[R] S` is exactly the canonical surjectivity theorem
`Algebra.TensorProduct.includeLeft_surjective`. -/
recall Algebra.TensorProduct.includeLeft_surjective

section BaseChangeKernel

variable [Algebra R S]
variable {R' : Type w} [CommRing R'] [Algebra R R']
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.TensorProduct

-- Proof sketch: right exactness identifies the kernel of the canonical owner map
-- `includeRight : R' →ₐ[R] S ⊗[R] R'` with the extension of `RingHom.ker (algebraMap R S)`
-- to `R ⊗[R] R'`; then `Ideal.map_isLocallyNilpotent` transports local nilpotence across that
-- extension and across the left-unit equivalence `R ⊗[R] R' ≃ₐ[R] R'`.
/-- Lemma 10.46.1 (4) at the `core/canonical` owner layer: if `algebraMap R S` is surjective with
locally nilpotent kernel, then after base change along `R → R'` the kernel of the canonical owner
map `includeRight : R' →ₐ[R] S ⊗[R] R'` remains locally nilpotent. -/
@[stacks 0BR6]
theorem ker_includeRight_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : (RingHom.ker (algebraMap R S)).IsLocallyNilpotent) :
    (RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R')).IsLocallyNilpotent := by
  let g := map (Algebra.ofId R S) (AlgHom.id R R')
  have hg_locnil : (RingHom.ker g).IsLocallyNilpotent := by
    have hgker : RingHom.ker g =
        Ideal.map (includeLeft : R →ₐ[R] R ⊗[R] R') (RingHom.ker (algebraMap R S)) := by
      simpa [g, RingHom.algebraMap_toAlgebra] using
        rTensor_ker (Algebra.ofId R S) hsurj
    rw [hgker]
    simpa using Ideal.map_isLocallyNilpotent (includeLeft : R →ₐ[R] R ⊗[R] R').toRingHom hker
  let l := Algebra.TensorProduct.lid R R'
  have howner : (RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R')).IsLocallyNilpotent := by
    have hg_eq :
        (g : R ⊗[R] R' →+* S ⊗[R] R') =
          ((includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom).comp l.toRingHom := by
      apply ringHom_ext
      · ext r
        change g (r ⊗ₜ[R] (1 : R')) =
          includeRight (l (r ⊗ₜ[R] (1 : R')))
        have hl : l (r ⊗ₜ[R] (1 : R')) = algebraMap R R' r := by
          rw [Algebra.algebraMap_eq_smul_one]
          simp [l]
        rw [hl]
        change includeLeftRingHom (algebraMap R S r) = includeRight (algebraMap R R' r)
        exact congrArg (fun φ : R →+* S ⊗[R] R' ↦ φ r) includeLeftRingHom_comp_algebraMap
      · ext r
        change g (1 ⊗ₜ[R] r) =
          includeRight (l (1 ⊗ₜ[R] r))
        rw [show g (1 ⊗ₜ[R] r) = 1 ⊗ₜ[R] r by simp [g]]
        rw [show l (1 ⊗ₜ[R] r) = r by simp [l]]
        exact (Algebra.TensorProduct.right_algebraMap_apply r).symm
    have hgker :
        RingHom.ker (g : R ⊗[R] R' →+* S ⊗[R] R') =
          Ideal.comap l.toRingHom (RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R')) := by
      rw [hg_eq, RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot]
      simpa using
        (RingHom.comap_ker ((includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom) l.toRingHom).symm
    have hker_lid :
        RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R') =
          (RingHom.ker g).map l.toRingHom := by
      change RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R') =
        Ideal.map l.toRingHom (RingHom.ker (g : R ⊗[R] R' →+* S ⊗[R] R'))
      rw [hgker]
      symm
      exact Ideal.map_comap_of_surjective l.toRingHom l.surjective _
    rw [hker_lid]
    simpa using Ideal.map_isLocallyNilpotent l.toRingHom hg_locnil
  simpa using howner

end Algebra.TensorProduct

namespace Algebra

-- Proof sketch: the textbook-order owner `includeLeft : R' →ₐ[R] R' ⊗[R] S` is obtained from the
-- symmetric owner `includeRight : R' →ₐ[R] S ⊗[R] R'` by the tensor symmetry `comm R S R'`.
/-- Lemma 10.46.1 (4), source-facing base-change clause: if `algebraMap R S` is surjective with
locally nilpotent kernel, then after base change along `R → R'` the kernel of the canonical map
`R' → R' ⊗[R] S` remains locally nilpotent. -/
@[stacks 0BR6]
theorem ker_baseChange_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : (RingHom.ker (algebraMap R S)).IsLocallyNilpotent) :
    (RingHom.ker (includeLeft : R' →ₐ[R] R' ⊗[R] S)).IsLocallyNilpotent := by
  have hker_eq :
      RingHom.ker (includeLeft : R' →ₐ[R] R' ⊗[R] S) =
        RingHom.ker (includeRight : R' →ₐ[R] S ⊗[R] R') := by
    simpa using RingHom.ker_equiv_comp
      ((includeRight : R' →ₐ[R] S ⊗[R] R').toRingHom)
      (TensorProduct.comm R S R').toRingEquiv
  rw [hker_eq]
  exact Algebra.TensorProduct.ker_includeRight_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    hsurj hker

end Algebra

end BaseChangeKernel

namespace RingHom

/-- The canonical tensor-product base change of a ring homomorphism `f : R →+* S` along
`f' : R →+* R'`, viewed as a source-facing `RingHom` rather than through ambient `Algebra`
instances. This is a `bridge/view` owner for the canonical tensor-product inclusion
`Algebra.TensorProduct.includeLeft`. -/
abbrev baseChange {R' : Type w} [CommRing R'] (f : R →+* S) (f' : R →+* R') :
    let _ : Algebra R S := f.toAlgebra
    let _ : Algebra R R' := f'.toAlgebra
    R' →+* R' ⊗[R] S :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R R' := f'.toAlgebra
  algebraMap R' (R' ⊗[R] S)

/-- Lemma 10.46.1 (4), source-facing base-change clause: if `f : R →+* S` is surjective with
locally nilpotent kernel, then for every ring map `f' : R →+* R'` the induced base-changed map
`f.baseChange f' : R' →+* R' ⊗[R] S` also has locally nilpotent kernel. -/
@[stacks 0BR6]
theorem ker_baseChange_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent
    {R' : Type w} [CommRing R'] (f : R →+* S) (f' : R →+* R')
    (hsurj : Function.Surjective f) (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (RingHom.ker (f.baseChange f')).IsLocallyNilpotent := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R R' := f'.toAlgebra
  simpa [RingHom.baseChange, RingHom.algebraMap_toAlgebra] using
    (Algebra.ker_baseChange_isLocallyNilpotent_of_surjective_of_isLocallyNilpotent hsurj hker)

end RingHom

end
