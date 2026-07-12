import StacksProject_2024.Chap15.«15_18_0_1»
import StacksProject_2024.Chap10.Lemma_10_100_1
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open Algebra.TensorProduct
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable {I : Ideal R} {I' : Ideal R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S'" => S ⊗[R] R'
local notation "M'" => S' ⊗[S] M

/-- Helper for Lemma 15.18.2: if a prime of `S` contains the extension of `I`, then its
contraction to `R` contains `I`. -/
lemma mem_zeroLocus_comap_of_mem_zeroLocus_map
    {q : PrimeSpectrum S}
    (hq : q ∈ zeroLocus (Ideal.map (algebraMap R S) I : Set S)) :
    PrimeSpectrum.comap (algebraMap R S) q ∈ zeroLocus (I : Set R) := by
  -- Rewrite closed-subset membership as ideal containment, then contract the containment.
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hq_le : Ideal.map (algebraMap R S) I ≤ q.asIdeal :=
    (mem_zeroLocus q (Ideal.map (algebraMap R S) I : Set S)).1 hq
  have hp_le : I ≤ p.asIdeal := by
    change I ≤ Ideal.comap (algebraMap R S) q.asIdeal
    exact Ideal.map_le_iff_le_comap.mp hq_le
  exact (mem_zeroLocus p (I : Set R)).2 hp_le

/-- Helper for Lemma 15.18.2: closed-subset membership for `p' ∈ V(I')` ascends along a prime of
`S ⊗[R] R'` whose contraction to `R'` is `p'`. -/
lemma mem_zeroLocus_map_of_comap_eq
    {q' : PrimeSpectrum S'} {p' : PrimeSpectrum R'}
    (hp' : p' ∈ zeroLocus (I' : Set R'))
    (hq' : PrimeSpectrum.comap (algebraMap R' S') q' = p') :
    q' ∈ zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') := by
  -- Convert `p' ∈ V(I')` to an ideal containment and transport it across the contraction formula.
  have hp'_le : I' ≤ p'.asIdeal := (mem_zeroLocus p' (I' : Set R')).1 hp'
  have hmap_le : Ideal.map (algebraMap R' S') I' ≤ q'.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    change I' ≤ (PrimeSpectrum.comap (algebraMap R' S') q').asIdeal
    simpa [hq'] using hp'_le
  exact (mem_zeroLocus q' (Ideal.map (algebraMap R' S') I' : Set S')).2 hmap_le

/-- Helper for Lemma 15.18.2: after fixing a prime `p'` of `R'`, the `p'`-fiber of
`R' ⊗[R] S` is canonically identified with `κ(p') ⊗[R] S`. -/
noncomputable abbrev fiber_tensor_base_change_rightOrderAlgEquiv
    (p' : PrimeSpectrum R') :
    p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField] p'.asIdeal.ResidueField ⊗[R] S :=
  Algebra.TensorProduct.cancelBaseChange R R' p'.asIdeal.ResidueField
    p'.asIdeal.ResidueField S

/-- Helper for Lemma 15.18.2: after fixing compatible primes `q` of `S` and `p'` of `R'`, the
true source-side base change of the fixed fiber over `p = q ∩ R` is canonically the `p'`-fiber of
`R' ⊗[R] S`. -/
noncomputable abbrev baseChanged_sourceFiber_algEquiv_rightOrderedFiber
    (q : PrimeSpectrum S) (p' : PrimeSpectrum R')
    (hcompat :
      PrimeSpectrum.comap (algebraMap R R') p' =
        PrimeSpectrum.comap (algebraMap R S) q) :
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
    let _ : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
      (Ideal.ResidueField.mapₐ p.asIdeal p'.asIdeal (Algebra.ofId R R')
        (by
          simpa [p, PrimeSpectrum.comap_asIdeal] using
            (congrArg PrimeSpectrum.asIdeal hcompat).symm)).toAlgebra
    p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.Fiber (R' ⊗[R] S) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let _ : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
    (Ideal.ResidueField.mapₐ p.asIdeal p'.asIdeal (Algebra.ofId R R')
      (by
        simpa [p, PrimeSpectrum.comap_asIdeal] using
          (congrArg PrimeSpectrum.asIdeal hcompat).symm)).toAlgebra
  -- First cancel the source-side base change of the fixed fiber, then identify the resulting
  -- tensor product with the `p'`-fiber of `R' ⊗[R] S`.
  exact
    (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField
      p'.asIdeal.ResidueField p'.asIdeal.ResidueField S).trans
      (fiber_tensor_base_change_rightOrderAlgEquiv (R := R) (S := S) (R' := R') p').symm

/-- Helper for Lemma 15.18.2: tensor commutativity transports a prime of `R' ⊗[R] S` with fixed
contractions to the corresponding prime of `S ⊗[R] R'`. -/
lemma prime_over_tensor_comm
    {q0 : PrimeSpectrum (R' ⊗[R] S)} {q : PrimeSpectrum S} {p' : PrimeSpectrum R'}
    (hq0S : PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q0 = q)
    (hq0R' : PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q0 = p') :
    ∃ q' : PrimeSpectrum S',
      PrimeSpectrum.comap (algebraMap S S') q' = q ∧
        PrimeSpectrum.comap (algebraMap R' S') q' = p' := by
  let e : S' ≃ₐ[R] R' ⊗[R] S := Algebra.TensorProduct.comm R S R'
  refine ⟨PrimeSpectrum.comap e.toAlgHom q0, ?_, ?_⟩
  · -- Follow the `S`-contraction through tensor commutativity and simplify the composite map.
    rw [← PrimeSpectrum.comap_comp_apply]
    change PrimeSpectrum.comap (e.toAlgHom.toRingHom.comp (algebraMap S S')) q0 = q
    have hcompS :
        e.toAlgHom.toRingHom.comp (algebraMap S S') = algebraMap S (R' ⊗[R] S) := by
      ext s
      change (1 : R') ⊗ₜ[R] s = (algebraMap S (R' ⊗[R] S)) s
      change (1 : R') ⊗ₜ[R] s = (1 : R') ⊗ₜ[R] s
      rfl
    rw [hcompS]
    exact hq0S
  · -- The same functoriality argument identifies the `R'`-contraction after transport.
    rw [← PrimeSpectrum.comap_comp_apply]
    change PrimeSpectrum.comap (e.toAlgHom.toRingHom.comp (algebraMap R' S')) q0 = p'
    have hcompR' :
        e.toAlgHom.toRingHom.comp (algebraMap R' S') = algebraMap R' (R' ⊗[R] S) := by
      ext r
      change
        (Algebra.TensorProduct.comm R S R') ((algebraMap R' (S ⊗[R] R')) r) =
          (algebraMap R' (R' ⊗[R] S)) r
      change (Algebra.TensorProduct.comm R S R') ((1 : S) ⊗ₜ[R] r) = r ⊗ₜ[R] (1 : S)
      simpa using (Algebra.TensorProduct.comm_tmul (R := R) (a := (1 : S)) (b := r))
    rw [hcompR']
    exact hq0R'

/-- Helper for Lemma 15.18.2: tensor commutativity also transports a prime of the left-ordered
tensor product `S ⊗[R] R'` to the right-ordered tensor product `R' ⊗[R] S`, while preserving its
contractions to `S` and `R'`. -/
lemma rightOrderedPrime_of_leftOrderedPrime
    (q' : PrimeSpectrum S') :
    ∃ q0 : PrimeSpectrum (R' ⊗[R] S),
      PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q0 =
        PrimeSpectrum.comap (algebraMap S S') q' ∧
      PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q0 =
        PrimeSpectrum.comap (algebraMap R' S') q' := by
  let e : S' ≃ₐ[R] R' ⊗[R] S := Algebra.TensorProduct.comm R S R'
  refine ⟨PrimeSpectrum.comap e.symm.toAlgHom q', ?_, ?_⟩
  · -- Rewrite the `S`-contraction through the inverse tensor-commutativity equivalence.
    rw [← PrimeSpectrum.comap_comp_apply]
    change
      PrimeSpectrum.comap (e.symm.toAlgHom.toRingHom.comp (algebraMap S (R' ⊗[R] S))) q' =
        PrimeSpectrum.comap (algebraMap S S') q'
    have hcompS :
        e.symm.toAlgHom.toRingHom.comp (algebraMap S (R' ⊗[R] S)) = algebraMap S S' := by
      ext s
      change
        (Algebra.TensorProduct.comm R S R').symm ((algebraMap S (R' ⊗[R] S)) s) =
          (algebraMap S S') s
      change (Algebra.TensorProduct.comm R S R').symm ((1 : R') ⊗ₜ[R] s) = s ⊗ₜ[R] (1 : R')
      simpa using (Algebra.TensorProduct.comm_symm_tmul (R := R) (a := (1 : R')) (b := s))
    rw [hcompS]
  · -- The same calculation identifies the `R'`-contraction on the right-ordered tensor product.
    rw [← PrimeSpectrum.comap_comp_apply]
    change
      PrimeSpectrum.comap (e.symm.toAlgHom.toRingHom.comp (algebraMap R' (R' ⊗[R] S))) q' =
        PrimeSpectrum.comap (algebraMap R' S') q'
    have hcompR' :
        e.symm.toAlgHom.toRingHom.comp (algebraMap R' (R' ⊗[R] S)) = algebraMap R' S' := by
      ext r
      change
        (Algebra.TensorProduct.comm R S R').symm ((algebraMap R' (R' ⊗[R] S)) r) =
          (algebraMap R' S') r
      change (Algebra.TensorProduct.comm R S R').symm (r ⊗ₜ[R] (1 : S)) = (1 : S) ⊗ₜ[R] r
      simpa using (Algebra.TensorProduct.comm_symm_tmul (R := R) (a := r) (b := (1 : S)))
    rw [hcompR']

/-- Helper for Lemma 15.18.2: the prime of a fixed fiber contracts back to the original prime of
the ambient algebra under the right tensor-factor inclusion. -/
lemma preimageEquivFiber_asIdeal_comap
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Ideal.comap includeRight.toRingHom
      ((PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩).asIdeal) = q.asIdeal := by
  -- Rewrite the fiber prime back through `PrimeSpectrum.preimageEquivFiber`.
  change
    ((PrimeSpectrum.preimageEquivFiber R S p).symm
      (PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩)).1.asIdeal = q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)

/-- Helper for Lemma 15.18.2: once a prime of the fixed `p'`-fiber of `R' ⊗[R] S` contracts to
`q` along the composite `S → R' ⊗[R] S → κ(p') ⊗[R'] (R' ⊗[R] S)`, it yields an honest prime of
`R' ⊗[R] S` lying over both `q` and `p'`. -/
lemma tensor_prime_of_fiber_prime
    (p' : PrimeSpectrum R') (q : PrimeSpectrum S)
    (Q0 : PrimeSpectrum (p'.asIdeal.Fiber (R' ⊗[R] S)))
    (hQ0S :
      Ideal.comap
        (((includeRight :
            (R' ⊗[R] S) →ₐ[R'] p'.asIdeal.Fiber (R' ⊗[R] S)).toRingHom).comp
          (algebraMap S (R' ⊗[R] S)))
        Q0.asIdeal = q.asIdeal) :
    ∃ q0 : PrimeSpectrum (R' ⊗[R] S),
      PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q0 = q ∧
        PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q0 = p' := by
  let q0 := (PrimeSpectrum.preimageEquivFiber R' (R' ⊗[R] S) p').symm Q0
  refine ⟨q0.1, ?_, q0.2⟩
  -- Compare ideals first, then upgrade the equality back to the corresponding prime of `S`.
  apply PrimeSpectrum.ext
  have hfiber :
      Ideal.comap
        (includeRight :
          (R' ⊗[R] S) →ₐ[R'] p'.asIdeal.Fiber (R' ⊗[R] S)).toRingHom
        Q0.asIdeal = q0.1.asIdeal := by
    simpa [q0] using
      preimageEquivFiber_asIdeal_comap
        (R := R') (S := R' ⊗[R] S) p' q0.1 q0.2
  simpa [PrimeSpectrum.comap_asIdeal, hfiber, Ideal.comap_comap] using hQ0S

/-- Helper for Lemma 15.18.2: this is the source-faithful fiber step. After fixing compatible
primes `q` of `S` and `p'` of `R'`, one first lifts the induced prime of the `p`-fiber of `S`
along the residue-field base change `κ(p) → κ(p')`, and only then transports that lifted fiber
prime to the `p'`-fiber of `R' ⊗[R] S`. -/
theorem fiber_prime_lift_to_rightOrderedFiber
    (q : PrimeSpectrum S) (p' : PrimeSpectrum R')
    (hcompat :
      PrimeSpectrum.comap (algebraMap R R') p' =
        PrimeSpectrum.comap (algebraMap R S) q) :
    ∃ Q0 : PrimeSpectrum (p'.asIdeal.Fiber (R' ⊗[R] S)),
      Ideal.comap
        (((includeRight :
            (R' ⊗[R] S) →ₐ[R'] p'.asIdeal.Fiber (R' ⊗[R] S)).toRingHom).comp
          (algebraMap S (R' ⊗[R] S)))
        Q0.asIdeal = q.asIdeal := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let _ : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
    (Ideal.ResidueField.mapₐ p.asIdeal p'.asIdeal (Algebra.ofId R R')
      (by
        simpa [p, PrimeSpectrum.comap_asIdeal] using
          (congrArg PrimeSpectrum.asIdeal hcompat).symm)).toAlgebra
  let T :=
    p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S
  let qbar : PrimeSpectrum (p.asIdeal.Fiber S) :=
    PrimeSpectrum.preimageEquivFiber R S p ⟨q, rfl⟩
  let e :
      T ≃ₐ[p'.asIdeal.ResidueField] p'.asIdeal.Fiber (R' ⊗[R] S) :=
    baseChanged_sourceFiber_algEquiv_rightOrderedFiber
      (R := R) (S := S) (R' := R') q p' hcompat
  let _ := qbar
  let _ := e
  -- Route correction: the proof is now pinned to the true source-side base-changed fiber `T`
  -- together with the canonical equivalence `e : T ≃ₐ κ(p') ⊗[R'] (R' ⊗[R] S)`.
  -- TODO: first obtain `Qbase : PrimeSpectrum T` lying over `qbar` by faithful-flat spectrum
  -- surjectivity for `p.Fiber S → T`, then transport `Qbase` across `e` and rewrite the final
  -- contraction back to `q` using `preimageEquivFiber_asIdeal_comap`.
  sorry

/-- Helper for Lemma 15.18.2: compatible primes `q` of `S` and `p'` of `R'` lift first to the
right-ordered tensor product `R' ⊗[R] S` lying over both. -/
theorem exists_prime_over_rightOrdered_tensor_base_change
    (q : PrimeSpectrum S) (p' : PrimeSpectrum R')
    (hcompat :
      PrimeSpectrum.comap (algebraMap R R') p' =
        PrimeSpectrum.comap (algebraMap R S) q) :
    ∃ q0 : PrimeSpectrum (R' ⊗[R] S),
      PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q0 = q ∧
        PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q0 = p' := by
  -- The theorem is now a short assembly: the only genuine source-side difficulty is the named
  -- fiber-lift theorem, and `tensor_prime_of_fiber_prime` handles the transport back upstairs.
  obtain ⟨Q0, hQ0S⟩ :=
    fiber_prime_lift_to_rightOrderedFiber (R := R) (S := S) (R' := R') q p' hcompat
  exact tensor_prime_of_fiber_prime (R := R) (S := S) (R' := R') p' q Q0 hQ0S

/-- Helper for Lemma 15.18.2: compatible primes `q` of `S` and `p'` of `R'` lift to a prime of
`S ⊗[R] R'` lying over both. -/
theorem exists_prime_over_tensor_base_change
    (q : PrimeSpectrum S) (p' : PrimeSpectrum R')
    (hcompat :
      PrimeSpectrum.comap (algebraMap R R') p' =
        PrimeSpectrum.comap (algebraMap R S) q) :
    ∃ q' : PrimeSpectrum S',
      PrimeSpectrum.comap (algebraMap S S') q' = q ∧
        PrimeSpectrum.comap (algebraMap R' S') q' = p' := by
  -- Route correction: first lift to the right-ordered tensor product, then transport across the
  -- tensor-commutativity equivalence.
  obtain ⟨q0, hq0S, hq0R'⟩ := exists_prime_over_rightOrdered_tensor_base_change q p' hcompat
  exact prime_over_tensor_comm (q0 := q0) (q := q) (p' := p') hq0S hq0R'

/-- Helper for Lemma 15.18.2: local flatness of the tensor-base-changed module at `q'` descends
to local flatness of `M` at the contracted prime of `S`. -/
-- TODO: instantiate Lemma `10.100.1` on the localized tensor square
-- `Localization.AtPrime (PrimeSpectrum.comap (algebraMap S S') q').asIdeal S`
-- and `Localization.AtPrime (PrimeSpectrum.comap (algebraMap R' S') q').asIdeal R'`,
-- then rewrite the localized base change with `LocalizedModule.equivTensorProduct`.
theorem flat_localizedModule_of_flat_tensor_base_change
    (q' : PrimeSpectrum S')
    (hflat_q' : Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M'))
    (hflat_p' :
      Module.Flat R
        (LocalizedModule.AtPrime
          (PrimeSpectrum.comap (algebraMap R' S') q').asIdeal R')) :
    Module.Flat R
      (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap S S') q').asIdeal M) := by
  -- Move first to the right-ordered tensor product, where the ring-side localization owner matches
  -- the source proof and the descent theorem from Lemma `10.100.1`.
  obtain ⟨q0, hq0S, hq0R'⟩ :=
    rightOrderedPrime_of_leftOrderedPrime (R := R) (S := S) (R' := R') q'
  let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S (R' ⊗[R] S)) q0
  let p' : PrimeSpectrum R' := PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q0
  have hq_def : q = PrimeSpectrum.comap (algebraMap S S') q' := by
    simpa [q] using hq0S
  have hp'_def : p' = PrimeSpectrum.comap (algebraMap R' S') q' := by
    simpa [p'] using hq0R'
  -- TODO: transport `hflat_q'` across tensor commutativity to the corresponding localization at
  -- `q0`, prove the ring-side localization owner for
  -- `(Localization.AtPrime q.asIdeal S) ⊗[R] (Localization.AtPrime p'.asIdeal R')`, and apply
  -- Lemma `10.100.1 (2)` with `LocalizedModule.equivTensorProduct` as the final module rewrite.
  sorry

/-- Lemma 15.18.2: if the canonical closed-subset inclusion
`V(I'(S ⊗[R] R')) ⊆ Module.flatOverBaseLocus R' (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M)` holds after the
tensor-product base change `R → R'`, then the corresponding inclusion
`V(IS) ⊆ Module.flatOverBaseLocus R S M` already holds over `R`, provided `IR' ≤ I'`, the induced
map `V(I') → V(I)` is surjective, and `I'` has flat-over-`R` zero locus on `Spec R'`. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_descends
    (hI' : Ideal.map (algebraMap R R') I ≤ I')
    (hsurj : Set.SurjOn (PrimeSpectrum.comap (algebraMap R R'))
      (zeroLocus (I' : Set R')) (zeroLocus (I : Set R)))
    (hlocFlat : zeroLocus (I' : Set R') ⊆ Module.flatOverBaseLocus R R' R')
    (hbase :
      zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') ⊆
        Module.flatOverBaseLocus R' S' M') :
    zeroLocus (Ideal.map (algebraMap R S) I : Set S) ⊆ Module.flatOverBaseLocus R S M := by
  let _ := hI'
  -- Route correction: replace the forbidden later-owner specialization by the source-faithful
  -- primewise descent route through a compatible prime of the tensor product.
  refine (Ideal.zeroLocus_subset_flatOverBaseLocus_iff (R := R) (S := S) (M := M)
      (Ideal.map (algebraMap R S) I)).2 ?_
  intro q hq
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hp : p ∈ zeroLocus (I : Set R) := mem_zeroLocus_comap_of_mem_zeroLocus_map hq
  obtain ⟨p', hp', hp'comap⟩ := hsurj hp
  obtain ⟨q', hq'S, hq'R'⟩ := exists_prime_over_tensor_base_change q p' (by
    simpa [p] using hp'comap)
  have hq'_zero : q' ∈ zeroLocus (Ideal.map (algebraMap R' S') I' : Set S') :=
    mem_zeroLocus_map_of_comap_eq hp' hq'R'
  -- The upstairs hypothesis gives flatness after localizing the tensor-base-changed module at
  -- the lifted prime `q'`.
  have hflat_q' : Module.Flat R' (LocalizedModule.AtPrime q'.asIdeal M') :=
    (Module.mem_flatOverBaseLocus R' S' M' q').1 (hbase hq'_zero)
  -- The local flatness hypothesis on `R'` provides the base-ring flatness needed for descent.
  have hflat_p' : Module.Flat R (LocalizedModule.AtPrime p'.asIdeal R') :=
    (Module.mem_flatOverBaseLocus R R' R' p').1 (hlocFlat hp')
  -- Descend local flatness along the localized tensor square.
  have hflat_q'R' :
      Module.Flat R
        (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap R' S') q').asIdeal R') := by
    -- Transport along the equality of primes rather than rewriting the dependent localization type.
    cases hq'R'
    simpa using hflat_p'
  have hflat_q : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := by
    -- The descent helper returns flatness at the contracted prime; rewrite that prime back to `q`.
    have hflat_q'' :
        Module.Flat R
          (LocalizedModule.AtPrime (PrimeSpectrum.comap (algebraMap S S') q').asIdeal M) :=
      flat_localizedModule_of_flat_tensor_base_change q' hflat_q' hflat_q'R'
    cases hq'S
    simpa using hflat_q''
  exact hflat_q

end
