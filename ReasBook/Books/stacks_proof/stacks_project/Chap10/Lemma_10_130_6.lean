import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_104_1
import stacks_proof.stacks_project.Chap10.Lemma_10_103_6
import stacks_proof.stacks_project.Chap10.Lemma_10_130_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/-- Helper for Chap10 Lemma 10 130 6: a linear equivalence preserves the possible lengths of
regular sequences contained in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- A regular sequence on one side transports across the equivalence, and the ideal condition is
  -- unchanged because the sequence itself is not altered.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Chap10 Lemma 10 130 6: ideal depth is invariant under linear equivalence of
finite modules. -/
private theorem idealDepth_eq_of_linearEquiv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- The top-submodule exceptional case in the definition of depth is preserved by mapping along
  -- the equivalence.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  -- Away from that exceptional case, depth is the supremum of the transported regular-sequence
  -- lengths.
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM,
      Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv I e]

/-- Helper for Chap10 Lemma 10 130 6: module depth over a local ring is invariant under linear
equivalence of finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Module depth is ideal depth at the maximal ideal, so the ideal-depth comparison applies
  -- directly.
  exact idealDepth_eq_of_linearEquiv (IsLocalRing.maximalIdeal R) e

/-- Helper for Chap10 Lemma 10 130 6: Cohen-Macaulayness is transported by a linear equivalence
over a Noetherian local ring. -/
private theorem cohenMacaulay_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (hM : Module.CohenMacaulay A M) :
    Module.CohenMacaulay A N := by
  letI : Module.CohenMacaulay A M := hM
  let _ : Module.Finite A N := Module.Finite.equiv e
  -- The defining Cohen-Macaulay equality is unchanged after rewriting both support dimension and
  -- depth across the equivalence.
  have hdepthDim :
      Module.supportDim A N = WithBot.some (moduleDepth A N) := by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_linearEquiv e,
      hM.supportDim_eq_moduleDepth]
  exact Module.CohenMacaulay.mk hdepthDim

/-- Helper for Chap10 Lemma 10 130 6: a ring equivalence transports the Cohen-Macaulay
self-module condition. -/
private theorem cohenMacaulaySelf_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B]
    (e : A ≃+* B) (hA : Module.CohenMacaulay A A) :
    Module.CohenMacaulay B B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := by
    simpa using e.surjective
  have hinj : Function.Injective (Algebra.linearMap A B) := by
    simpa using e.injective
  let eA : A ≃ₗ[A] B := LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨hinj, hsurj⟩
  have hAB : Module.CohenMacaulay A B :=
    cohenMacaulay_of_linearEquiv eA hA
  -- The induced algebra map is surjective, so the scalar-restriction theorem converts the
  -- transported `A`-module statement into the target self-module statement.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := A) (S := B) (N := B) hsurj).mpr hAB

/-- Helper for Chap10 Lemma 10 130 6: Cohen-Macaulayness of the self-module is invariant under
ring equivalence. -/
private theorem cohenMacaulaySelf_ringEquiv_iff
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B]
    (e : A ≃+* B) :
    Module.CohenMacaulay A A ↔ Module.CohenMacaulay B B := by
  -- Apply the one-way transport to the equivalence and to its inverse.
  constructor
  · intro hA
    exact cohenMacaulaySelf_of_ringEquiv e hA
  · intro hB
    exact cohenMacaulaySelf_of_ringEquiv e.symm hB

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: the canonical map `S → K ⊗[k] S` is flat because it is
obtained from the flat `k`-module `K` by base change. -/
private theorem tensorProduct_right_flat :
    Module.Flat S S_K := by
  -- Base-change flatness first gives flatness of `S ⊗[k] K` over `S`.
  letI : Module.Flat k K := Module.Flat.of_projective
  have hBase : Module.Flat S (S ⊗[k] K) := by
    exact Module.Flat.baseChange (R := k) (S := S) (M := K)
  -- The tensor commutativity equivalence moves this flat module to the chosen spelling `K ⊗[k] S`.
  exact Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight k S K).symm.toLinearEquiv

/-- Helper for Chap10 Lemma 10 130 6: the tensor-product algebra map `S → K ⊗[k] S` is flat. -/
private theorem tensorProduct_algebraMap_flat :
    (algebraMap S S_K).Flat := by
  -- The previously established module-flatness is exactly flatness of the algebra map.
  letI : Module.Flat S S_K := tensorProduct_right_flat (k := k) (K := K) (S := S)
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: the tensor-product map remains flat after localizing at
an upstairs prime and its contraction. -/
private theorem tensorProduct_localRingHom_flat (qK : PrimeSpectrum S_K) :
    (Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)).Flat := by
  -- Localize the already proved flat tensor-product algebra map at the contracted prime pair.
  exact
    RingHom.Flat.localRingHom (tensorProduct_algebraMap_flat (k := k) (K := K) (S := S))
      qK.asIdeal (PrimeSpectrum.comap iSK qK).asIdeal
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: the localized tensor-product map is a local homomorphism
for the contracted prime and the chosen upstairs prime. -/
private theorem tensorProduct_localRingHom_isLocalHom (qK : PrimeSpectrum S_K) :
    IsLocalHom (Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)) := by
  -- The localization construction gives a local homomorphism once the upstairs prime contracts to
  -- the named downstairs prime.
  exact
    Localization.isLocalHom_localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)

/-- Helper for Chap10 Lemma 10 130 6: a flat local ring homomorphism becomes faithfully flat after
using the ring homomorphism as the algebra structure. -/
private theorem faithfullyFlat_of_flat_localRingHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) (hlocal : IsLocalHom f) :
    let _ : Algebra A B := f.toAlgebra
    Module.FaithfullyFlat A B := by
  -- First read flatness of the ring homomorphism as module-flatness for the induced algebra.
  letI : Algebra A B := f.toAlgebra
  have hflat : Module.Flat A B := by
    exact (RingHom.flat_algebraMap_iff).mp (by simpa using hf)
  letI : Module.Flat A B := hflat
  have hlocal' : IsLocalHom (algebraMap A B) := by
    simpa using hlocal
  -- A flat local map of local rings is faithfully flat.
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: the localized tensor-product map is faithfully flat once it
is used as the algebra structure between the two local rings. -/
private theorem tensorProduct_localRingHom_faithfullyFlat (qK : PrimeSpectrum S_K) :
    let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
    let _ : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := by
  -- Combine the already proved localized flatness with locality of `Localization.localRingHom`.
  let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
  exact
    faithfullyFlat_of_flat_localRingHom f
      (tensorProduct_localRingHom_flat (k := k) (K := K) (S := S) qK)
      (tensorProduct_localRingHom_isLocalHom (k := k) (K := K) (S := S) qK)

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: after using the localized tensor-product map as the algebra
structure, the target localization is flat over the source localization. -/
private theorem tensorProduct_localizedAlgebraMap_flat (qK : PrimeSpectrum S_K) :
    let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
    let _ : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
    Module.Flat (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := by
  let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
  letI : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
  -- Read the already proved ring-hom flatness through the algebra structure induced by `f`.
  exact (RingHom.flat_algebraMap_iff).mp <| by
    simpa [f] using tensorProduct_localRingHom_flat (k := k) (K := K) (S := S) qK

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: after using the localized tensor-product map as the algebra
structure, the resulting algebra map is a local homomorphism. -/
private theorem tensorProduct_localizedAlgebraMap_isLocalHom (qK : PrimeSpectrum S_K) :
    let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
    let _ : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
    IsLocalHom
      (algebraMap (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
        (Localization.AtPrime qK.asIdeal)) := by
  let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
  letI : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
  -- The algebra map for `f.toAlgebra` is propositionally the localized tensor-product map.
  simpa [f] using tensorProduct_localRingHom_isLocalHom (k := k) (K := K) (S := S) qK

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: after using the localized tensor-product map as the algebra
structure, the target local ring is faithfully flat over the contracted source local ring. -/
private theorem tensorProduct_localizedAlgebraMap_faithfullyFlat (qK : PrimeSpectrum S_K) :
    let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
    let _ : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := by
  let f := Localization.localRingHom (PrimeSpectrum.comap iSK qK).asIdeal qK.asIdeal iSK
      (PrimeSpectrum.comap_asIdeal (f := iSK) qK)
  letI : Algebra (Localization.AtPrime (PrimeSpectrum.comap iSK qK).asIdeal)
      (Localization.AtPrime qK.asIdeal) := f.toAlgebra
  -- The already packaged faithful-flat result uses the same algebra structure induced by `f`.
  exact tensorProduct_localRingHom_faithfullyFlat (k := k) (K := K) (S := S) qK

omit [Field k] [Field K] [Algebra k K] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 130 6: localizing a localization at a prime preserves the
Cohen-Macaulay self-module condition after contracting the prime to the original ring. -/
private theorem cohenMacaulay_atPrime_iff_localizationAtPrime_comap
    {R : Type*} [CommRing R] {M : Submonoid R} (q : PrimeSpectrum (Localization M))
    [IsNoetherianRing (Localization.AtPrime
      (q.asIdeal.comap (algebraMap R (Localization M))))]
    [IsNoetherianRing (Localization.AtPrime q.asIdeal)] :
    Module.CohenMacaulay
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R (Localization M))))
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R (Localization M)))) ↔
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
  -- The iterated localization is canonically isomorphic to localization at the contracted prime,
  -- so Cohen-Macaulayness transports across the induced ring equivalence.
  exact
    cohenMacaulaySelf_ringEquiv_iff
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := M) q.asIdeal).toRingEquiv

/-- Helper for Chap10 Lemma 10 130 6: on the expected dimension stratum, the polynomial
flat-locus theorem is a pointwise equivalence between Cohen-Macaulayness and flatness. -/
private theorem cohenMacaulayAtPrime_iff_flatOverBaseLocus_of_mem_dimensionStratum
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A] [Algebra.FiniteType F A]
    {d : ℕ} (π : MvPolynomial (Fin d) F →ₐ[F] A) (hπ : π.QuasiFinite)
    (q : PrimeSpectrum A) (hdim : q ∈ PrimeSpectrum.dimensionStratum A d) :
    let _ : Algebra (MvPolynomial (Fin d) F) A := π.toAlgebra
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) ↔
      q ∈ Module.flatOverBaseLocus (MvPolynomial (Fin d) F) A A := by
  let P := MvPolynomial (Fin d) F
  letI : Algebra P A := π.toAlgebra
  have hset :
      Module.flatOverBaseLocus P A A =
        { q : PrimeSpectrum A |
            Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
              (Localization.AtPrime q.asIdeal) } ∩
          PrimeSpectrum.dimensionStratum A d := by
    -- The global flat-locus identity is the source theorem; evaluate it at the chosen prime.
    simpa [P] using
      flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial
        (S := A) π hπ
  have hpoint :
      q ∈ Module.flatOverBaseLocus P A A ↔
        Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal) ∧
          q ∈ PrimeSpectrum.dimensionStratum A d := by
    -- Rewriting the set equality turns membership in the flat locus into the two pointwise
    -- conditions; the dimension-stratum hypothesis will supply the second conjunct.
    rw [hset]
    simp
  constructor
  · intro hCM
    exact hpoint.mpr ⟨hCM, hdim⟩
  · intro hflat
    exact (hpoint.mp hflat).1

/- 
Domain-style sampling:
- primary domain: Cohen-Macaulay local rings under tensor base change along a field extension;
- sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.LocallyCohenMacaulay`,
  `primeSpectrumTopologicalKrullDimAt_eq_of_tensorProduct_fieldExtension`,
  `flat_locus_eq_cohenMacaulay_inter_dimensionStratum_of_quasiFinite_polynomial`;
- best owner abstraction: the local Cohen-Macaulay owner `Module.CohenMacaulay` on the localized
  self-modules downstairs and upstairs;
- primitive data: the finite type `k`-algebra `S` and the upstairs prime
  `qK : PrimeSpectrum S_K`; the downstairs prime is the canonical contraction
  `PrimeSpectrum.comap iSK qK`;
- derived API: the local dimension comparison from Lemma `10.116.6` and the flat-locus
  description from Lemma `10.130.1`, which support the proof but should not be repackaged as a
  second public owner here.

Source/core/bridge triage:
* `source-facing`: invariance of the Cohen-Macaulay condition for the local rings at the canonical
  contracted/lying-over pair of primes under the tensor base change `S ↦ K ⊗[k] S`;
* `core/canonical`: `Module.CohenMacaulay` on `Localization.AtPrime q.asIdeal` and
  `Localization.AtPrime qK.asIdeal`;
* `bridge/view`: the tensor-product map `iSK` and the induced contraction
  `PrimeSpectrum.comap iSK qK`.

The public statement should therefore stay directly on `Module.CohenMacaulay`; adding a separate
ring-level alias here would only duplicate the chapter owner abstraction.
-/

-- Proof sketch: after replacing `S` by a localization away from `q`, use Noether normalization to
-- choose a finite injective map `k[x₁, …, x_d] → S`. Base change this map to `K[x₁, …, x_d] →
-- K ⊗[k] S`, use Lemma `10.116.6` to identify the relevant relative dimensions, and apply Lemma
-- `10.130.1` to reduce both Cohen-Macaulay conditions to flatness of the two vertical maps in the
-- normalization square. Since the bottom horizontal map is flat, the two flatness conditions are
-- equivalent.
/-- Lemma 10.130.6: for a field extension `K / k`, a finite type `k`-algebra `S`, a prime
`qK : Spec(K ⊗[k] S)`, and its contraction `q := PrimeSpectrum.comap iSK qK`, the local ring
`S_q` is Cohen-Macaulay if and only if the local ring `(K ⊗[k] S)_{qK}` is Cohen-Macaulay. -/
@[stacks 00RJ]
theorem cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ↔
      Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
        (Localization.AtPrime qK.asIdeal) := by
  -- Route correction: the dependency-closed proof now pivots to the source route through an
  -- away chart and the flat-locus theorem, rather than the unavailable later closed-fiber transfer.
  let q := PrimeSpectrum.comap iSK qK
  have hflatLocal := tensorProduct_localRingHom_flat (k := k) (K := K) (S := S) qK
  have hlocal := tensorProduct_localRingHom_isLocalHom (k := k) (K := K) (S := S) qK
  -- The localized tensor-product map is now available as a verified flat local bridge. The
  -- localization-at-prime transport has also been isolated above; the remaining blocker is the
  -- dependency-closed Cohen-Macaulay comparison through the away Noether-normalization chart and
  -- the flat-locus/dimension-stratum normal form.
  -- TODO: choose the Noether-normalization away chart from Lemma `10.115.5`, transport both local
  -- rings with a localization-away Cohen-Macaulay transport lemma, and finish by comparing the
  -- two flat-locus and dimension-stratum conjuncts from Lemmas `10.130.1` and `10.116.6`.
  sorry

end
