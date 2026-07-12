import Mathlib
import StacksProject_2024.Chap10.Lemma_10_46_8
import StacksProject_2024.Chap10.Lemma_10_130_4
import StacksProject_2024.Chap10.Lemma_10_130_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Helper for Chap10 Lemma 10 130 7: contraction of an upstairs prime through the two sides of
the tensor-product base-change square gives the same base prime of `R`. -/
private theorem baseChange_basePrime_comap (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap (algebraMap R R')
        (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q') =
      PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap includeRight.toRingHom q') := by
  -- Proof comment: compare the two contracted ideals after pushing both paths through the
  -- defining tensor-product square `R → R'` and `R → S`.
  ext r
  simp [PrimeSpectrum.comap_asIdeal]

/-- Helper for Chap10 Lemma 10 130 7: the base-prime equality from the tensor-product square,
written as an ideal contraction for constructing the residue-field extension. -/
private theorem baseChange_basePrime_asIdeal_comap (q' : PrimeSpectrum (R' ⊗[R] S)) :
    Ideal.comap (algebraMap R R')
        (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q').asIdeal =
      (PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap includeRight.toRingHom q')).asIdeal := by
  -- Proof comment: pass the spectrum-level equality to ideals and unfold `comap` on spectra.
  simpa [PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal (baseChange_basePrime_comap q')

/-- Helper for Chap10 Lemma 10 130 7: the base-prime equality from the tensor-product square,
written in the `Ideal.under` form used by the residue-field fiber construction. -/
private theorem baseChange_basePrime_under (q' : PrimeSpectrum (R' ⊗[R] S)) :
    (PrimeSpectrum.comap includeRight.toRingHom q').asIdeal.under R =
      (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q').asIdeal.under R := by
  -- Proof comment: `under` is ideal contraction along the relevant algebra map, so this is the
  -- already proved base-prime contraction equality with the sides oriented for the source fiber.
  simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
    (baseChange_basePrime_asIdeal_comap (R := R) (S := S) (R' := R') q').symm

/-- Helper for Chap10 Lemma 10 130 7: the canonical prime of a fiber ring contracts back to the
ambient prime that defines that fiber. -/
private theorem fiberPrimeAt_includeRight_comap
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    PrimeSpectrum.comap
        ((includeRight : B →ₐ[A] ((q.asIdeal.under A).Fiber B)).toRingHom)
        (fiberPrimeAt A B q) =
      q := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  have hinv :
      ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q)) = q := by
    -- Proof comment: `fiberPrimeAt` is the forward image of `q` under the fiber equivalence, so
    -- applying the inverse equivalence recovers the original ambient prime.
    simpa [p, fiberPrimeAt] using
      congrArg Subtype.val
        ((PrimeSpectrum.preimageEquivFiber A B p).symm_apply_apply ⟨q, rfl⟩)
  -- Proof comment: unfold only the contraction component of the preimage equivalence, then
  -- rewrite by the inverse computation above.
  calc
    PrimeSpectrum.comap
        ((includeRight : B →ₐ[A] (p.asIdeal.Fiber B)).toRingHom)
        (fiberPrimeAt A B q) =
        ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q)) := by
          change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
              (fiberPrimeAt A B q) =
            ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q))
          rfl
    _ = q := hinv

/-- Helper for Chap10 Lemma 10 130 7: the canonical fiber prime has ideal contraction equal to
the ambient prime ideal that defines the fiber. -/
private theorem fiberPrimeAt_includeRight_comap_asIdeal
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    Ideal.comap
        ((includeRight : B →ₐ[A] ((q.asIdeal.under A).Fiber B)).toRingHom)
        (fiberPrimeAt A B q).asIdeal =
      q.asIdeal := by
  -- Proof comment: pass the spectrum-level contraction statement to prime ideals.
  simpa [PrimeSpectrum.comap_asIdeal] using
    congrArg PrimeSpectrum.asIdeal (fiberPrimeAt_includeRight_comap (A := A) (B := B) q)

/-- Helper for Chap10 Lemma 10 130 7: a prime of a fiber ring is the canonical fiber prime once
its contraction along the tensor-product inclusion is the original ambient prime. -/
private theorem fiberPrimeAt_eq_of_includeRight_comap_eq
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B)
    (r : PrimeSpectrum ((q.asIdeal.under A).Fiber B))
    (h :
      PrimeSpectrum.comap
          ((includeRight : B →ₐ[A] ((q.asIdeal.under A).Fiber B)).toRingHom) r =
        q) :
    r = fiberPrimeAt A B q := by
  let e := PrimeSpectrum.preimageEquivFiber A B (PrimeSpectrum.comap (algebraMap A B) q)
  have hs :
      e.symm r = ⟨q, rfl⟩ := by
    -- Proof comment: after returning through the fiber equivalence, equality of subtypes is
    -- exactly the assumed contraction equality.
    apply Subtype.ext
    simpa [e] using h
  -- Proof comment: rewrite the canonical fiber prime to the same equivalence, then replace the
  -- corresponding ambient prime by the one recovered from `r`.
  rw [fiberPrimeAt]
  rw [← hs]
  exact (e.apply_symm_apply r).symm

variable [Algebra.FiniteType R S]

/-- Helper for Chap10 Lemma 10 130 7: a ring equivalence between Noetherian local rings preserves
the Cohen-Macaulay property of the self-module. -/
private theorem cohenMacaulaySelf_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) [hA : Module.CohenMacaulay A A] :
    Module.CohenMacaulay B B := by
  -- Proof comment: view the ring equivalence as a surjective algebra map and compare the
  -- self-module with its restriction of scalars through the induced linear equivalence.
  letI : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := by
    simpa using e.surjective
  let eA : A ≃ₗ[A] B :=
    LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨by
      simpa using e.injective, hsurj⟩
  letI : Module.Finite A B := Module.Finite.equiv eA
  have hAB : Module.CohenMacaulay A B := by
    refine Module.CohenMacaulay.mk ?_
    rw [← Module.supportDim_eq_of_equiv eA, ← moduleDepth_eq_of_equiv eA,
      hA.supportDim_eq_moduleDepth]
  -- Proof comment: descend the Cohen-Macaulay condition from the restricted module back to the
  -- target self-module using the surjective algebra map from the equivalence.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := A) (S := B) (N := B) hsurj).mpr hAB

/-- Helper for Chap10 Lemma 10 130 7: a ring equivalence between Noetherian local rings
preserves and reflects the Cohen-Macaulay property of the self-module. -/
private theorem cohenMacaulaySelf_ringEquiv_iff
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) :
    Module.CohenMacaulay A A ↔ Module.CohenMacaulay B B := by
  -- Proof comment: apply the one-way transport to the equivalence and to its inverse.
  constructor
  · intro hA
    letI : Module.CohenMacaulay A A := hA
    exact cohenMacaulaySelf_of_ringEquiv e
  · intro hB
    letI : Module.CohenMacaulay B B := hB
    exact cohenMacaulaySelf_of_ringEquiv e.symm

/-- Helper for Chap10 Lemma 10 130 7: localizations at corresponding primes under a ring
equivalence have the same Cohen-Macaulay self-module condition. -/
private theorem cohenMacaulaySelf_localizationAtPrime_comapEquiv_iff
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (q : PrimeSpectrum A)
    [IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [IsNoetherianRing
      (Localization.AtPrime ((PrimeSpectrum.comapEquiv e) q).asIdeal)] :
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) ↔
      Module.CohenMacaulay
        (Localization.AtPrime ((PrimeSpectrum.comapEquiv e) q).asIdeal)
        (Localization.AtPrime ((PrimeSpectrum.comapEquiv e) q).asIdeal) := by
  let qB : PrimeSpectrum B := (PrimeSpectrum.comapEquiv e) q
  have hqB : Ideal.comap e.toRingHom qB.asIdeal = q.asIdeal := by
    -- Proof comment: the inverse half of `comapEquiv` says that contracting the transported prime
    -- along the original equivalence recovers the source prime.
    simpa [qB, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal ((PrimeSpectrum.comapEquiv e).left_inv q)
  let eLocal :
      Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime qB.asIdeal :=
    Localization.localRingEquiv q.asIdeal qB.asIdeal e hqB.symm
  -- Proof comment: after the localizations are identified by `Localization.localRingEquiv`, the
  -- Cohen-Macaulay comparison is exactly ring-equivalence transport.
  simpa [qB] using cohenMacaulaySelf_ringEquiv_iff eLocal

/-- Helper for Chap10 Lemma 10 130 7: the localization comparison for primes transported by a
ring equivalence, oriented from the transported prime back to the original prime. -/
private theorem cohenMacaulaySelf_localizationAtPrime_comapEquiv_symm_iff
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (q : PrimeSpectrum A)
    [IsNoetherianRing (Localization.AtPrime q.asIdeal)]
    [IsNoetherianRing
      (Localization.AtPrime ((PrimeSpectrum.comapEquiv e) q).asIdeal)] :
    Module.CohenMacaulay
        (Localization.AtPrime ((PrimeSpectrum.comapEquiv e) q).asIdeal)
        (Localization.AtPrime ((PrimeSpectrum.comapEquiv e) q).asIdeal) ↔
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: reuse the forward transport lemma and reverse its direction for the upstairs
  -- side of the base-change comparison.
  exact (cohenMacaulaySelf_localizationAtPrime_comapEquiv_iff e q).symm

/-- Helper for Chap10 Lemma 10 130 7: Cohen-Macaulayness of the canonical fiber local ring is
unchanged by arbitrary base change at a fixed upstairs prime. -/
private theorem cohenMacaulay_fiberLocalRingAt_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    Module.CohenMacaulay
        (fiberLocalRingAt R S (PrimeSpectrum.comap includeRight.toRingHom q'))
        (fiberLocalRingAt R S (PrimeSpectrum.comap includeRight.toRingHom q')) ↔
      Module.CohenMacaulay (fiberLocalRingAt R' (R' ⊗[R] S) q')
        (fiberLocalRingAt R' (R' ⊗[R] S) q') := by
  let p' : PrimeSpectrum R' :=
    PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] S)) q'
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let _ : Algebra p.asIdeal.ResidueField p'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal p'.asIdeal (algebraMap R R') rfl).toAlgebra
  let e :
      p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
        p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S :=
    baseChange_fiber_algEquiv (R := R) (S := S) p'
  let qK :
      PrimeSpectrum
        (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber S) :=
    PrimeSpectrum.comapEquiv e.toRingEquiv (fiberPrimeAt R' (R' ⊗[R] S) q')
  have hField :
      (let q := PrimeSpectrum.comap includeRight.toRingHom qK
       Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal) ↔
        Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
          (Localization.AtPrime qK.asIdeal)) := by
    -- Proof comment: Lemma 10.130.6 applies to the field extension of residue fields and the
    -- downstairs fiber algebra after the upstairs fiber prime is transported by the base-change
    -- fiber equivalence.
    exact
      cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension
        (k := p.asIdeal.ResidueField) (K := p'.asIdeal.ResidueField)
        (S := p.asIdeal.Fiber S) qK
  have hUp :
      Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
          (Localization.AtPrime qK.asIdeal) ↔
        Module.CohenMacaulay
          (Localization.AtPrime (fiberPrimeAt R' (R' ⊗[R] S) q').asIdeal)
          (Localization.AtPrime (fiberPrimeAt R' (R' ⊗[R] S) q').asIdeal) := by
    -- Proof comment: `qK` is the spectrum transport of the upstairs fiber prime, so localizing at
    -- the corresponding primes gives equivalent local rings.
    simpa [qK] using
      cohenMacaulaySelf_localizationAtPrime_comapEquiv_symm_iff e.toRingEquiv
        (fiberPrimeAt R' (R' ⊗[R] S) q')
  -- Proof comment: unfold the canonical fiber-local-ring owner and compose the field-extension
  -- comparison with the upstairs localization transport.
  simpa [fiberLocalRingAt, fiberPrimeAt, p, p', qK, e, baseChange_fiber_algEquiv,
    baseChange_basePrime_under (R := R) (S := S) (R' := R') q'] using hField.trans hUp

/-- Helper for Chap10 Lemma 10 130 7: the pointwise Cohen-Macaulay fiber-locus condition is
preserved under the tensor-product base-change map on spectra. -/
private theorem mem_cohenMacaulayFiberLocus_baseChange_iff
    (q' : PrimeSpectrum (R' ⊗[R] S)) :
    PrimeSpectrum.comap includeRight.toRingHom q' ∈
        PrimeSpectrum.cohenMacaulayFiberLocus R S ↔
      q' ∈ PrimeSpectrum.cohenMacaulayFiberLocus R' (R' ⊗[R] S) := by
  -- Proof comment: unfold the locus owner on both sides and use the fiber-local-ring
  -- Cohen-Macaulay comparison isolated above.
  rw [PrimeSpectrum.mem_cohenMacaulayFiberLocus, PrimeSpectrum.mem_cohenMacaulayFiberLocus]
  exact cohenMacaulay_fiberLocalRingAt_baseChange_iff q'

/-- Helper for Chap10 Lemma 10 130 7: the inverse image of the downstairs Cohen-Macaulay fiber
locus is contained in the upstairs Cohen-Macaulay fiber locus after base change. -/
private theorem cohenMacaulayFiberLocus_baseChange_subset :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        PrimeSpectrum.cohenMacaulayFiberLocus R S ⊆
      PrimeSpectrum.cohenMacaulayFiberLocus R' (R' ⊗[R] S) := by
  -- Proof comment: convert a point of the inverse image into the corresponding upstairs
  -- pointwise condition using the membership bridge.
  intro q' hq'
  exact (mem_cohenMacaulayFiberLocus_baseChange_iff q').mp hq'

/-- Helper for Chap10 Lemma 10 130 7: every upstairs Cohen-Macaulay fiber point maps into the
downstairs Cohen-Macaulay fiber locus. -/
private theorem cohenMacaulayFiberLocus_subset_baseChange :
    PrimeSpectrum.cohenMacaulayFiberLocus R' (R' ⊗[R] S) ⊆
      PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        PrimeSpectrum.cohenMacaulayFiberLocus R S := by
  -- Proof comment: use the reverse implication of the same pointwise membership bridge.
  intro q' hq'
  exact (mem_cohenMacaulayFiberLocus_baseChange_iff q').mpr hq'

/- 
Domain-style sampling:
- primary domain: base change on `PrimeSpectrum` for loci cut out by a fiber-local ring property;
- sampled owner declarations of the same kind:
  `PrimeSpectrum.cohenMacaulayFiberLocus`,
  `fiberLocalRingAt`,
  `Module.CohenMacaulay`,
  `relativeDimensionAt_le_preimage_eq_baseChange`,
  `smoothLocus_baseChange_preimage_eq`;
- best owner abstraction: the upstream named locus owner
  `PrimeSpectrum.cohenMacaulayFiberLocus R S`, whose membership is defined through the canonical
  fiber-local-ring owner `fiberLocalRingAt R S q` and the local self-module predicate
  `Module.CohenMacaulay (fiberLocalRingAt R S q) (fiberLocalRingAt R S q)`;
- primitive data: the finite type map `R → S`, the arbitrary base change `R → R'`, and the
  induced map `Spec(R' ⊗[R] S) → Spec(S)`;
- derived API: the base-change equality for the inverse image of that locus owner.

Source/core/bridge triage:
* `source-facing`: the Cohen-Macaulay fiber locus of `Spec(S)`;
* `core/canonical`: `fiberLocalRingAt` and `Module.CohenMacaulay` on the fiber local self-module;
* `bridge/view`: inverse image along `PrimeSpectrum.comap includeRight.toRingHom`.
-/

-- Proof sketch: for `q' : Spec(R' ⊗[R] S)`, let `q` be its image in `Spec(S)`. The local fiber
-- ring of `S'/R'` at `q'` is the base change of the local fiber ring of `S/R` at `q` along the
-- residue-field extension `κ(q ∩ R) → κ(q' ∩ R')`. Apply Lemma `10.130.6` to that field extension
-- and then unwind the definitions of the two loci.
/-- Lemma 10.130.7: for a finite type ring map `R → S`, an arbitrary base change `R → R'`, and
`S' = R' ⊗[R] S`, the locus of primes of `S'` where the local fiber ring of `S'/R'` is
Cohen-Macaulay is exactly the inverse image of the corresponding locus of `S/R` under
`Spec(S') → Spec(S)`. -/
@[stacks 00RK]
theorem cohenMacaulayFiberLocus_baseChange_preimage_eq :
    PrimeSpectrum.comap includeRight.toRingHom ⁻¹'
        PrimeSpectrum.cohenMacaulayFiberLocus R S =
      PrimeSpectrum.cohenMacaulayFiberLocus R' (R' ⊗[R] S) := by
  -- Proof comment: assemble the equality from the two pointwise subset directions proved above.
  apply Set.Subset.antisymm
  · exact cohenMacaulayFiberLocus_baseChange_subset
  · exact cohenMacaulayFiberLocus_subset_baseChange

end
