import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_1
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap10.Lemma_10_46_8
import StacksProject_2024.Chap10.Lemma_10_31_8
import StacksProject_2024.Chap10.Lemma_10_103_6
import StacksProject_2024.Chap10.Lemma_10_163_3
import StacksProject_2024.Chap10.Lemma_10_163_5
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_167_1

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {S : Type w} [CommRing S] [Algebra k S] [IsNoetherianRing S]

local notation "S_K" => K ⊗[k] S

/- Domain-style sampling:
- primary domain: Cohen-Macaulay local rings under tensor base change along a finitely generated
  field extension;
- sampled owner declarations of the same kind:
  `Algebra.EssFiniteType` from Definition `9.6.6`,
  `isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.31.8`,
  `cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.167.1`,
  `cohenMacaulayRing_iff_source_and_closedFiber` from Lemma `10.163.3`;
- best owner abstraction: the field-extension hypothesis belongs on the canonical owner
  `Algebra.EssFiniteType k K`, while the Cohen-Macaulay condition itself belongs directly on the
  local self-module owner `Module.CohenMacaulay`;
- primitive data: only the upstairs prime `qK` of `K ⊗[k] S`;
- derived API: Noetherianity of `S_K`, the local flatness of the induced map on localizations, and
  the Cohen-Macaulayness of the closed fiber over the canonical contraction `qK.under S`.

Source/core/bridge triage:
* `source-facing`: the Stacks lemma comparing the local rings at an upstairs prime and its
  downstairs contraction;
* `core/canonical`: `Algebra.EssFiniteType k K` and `Module.CohenMacaulay` on the localized
  self-modules;
* `bridge/view`: the induced localization map
  `Localization.AtPrime (qK.under S) → Localization.AtPrime qK` and the closed-fiber comparison
  with `K ⊗[k] (qK.under S).ResidueField`.

This file therefore should not keep a parallel finite-type field-extension hypothesis or a local
duplicate of the tensor-product Noetherianity theorem. Once `qK` is fixed, the downstairs prime is
canonically `qK.under S`, so separate public data `q` and `qK.LiesOver q` would be redundant.
-/

-- The tensor product ring is Noetherian by the chapter owner theorem for finitely generated field
-- extensions, already formulated on `Algebra.EssFiniteType`.
local instance tensorProduct_isNoetherianRing : IsNoetherianRing S_K :=
  isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension

/-- Helper for Lemma 10.167.2: a ring equivalence between Noetherian local rings preserves the
local Cohen-Macaulay property of the self-module. -/
private theorem cohenMacaulay_of_ringEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) [hA : Module.CohenMacaulay A A] :
    Module.CohenMacaulay B B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  have hsurj : Function.Surjective (algebraMap A B) := by
    simpa using e.surjective
  let eA : A ≃ₗ[A] B :=
    LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨by
      simpa using e.injective, hsurj⟩
  letI : Module.Finite A B := Module.Finite.equiv eA
  have hAB : Module.CohenMacaulay A B := by
    -- The source ring and its image under the equivalence are the same finite `A`-module.
    refine Module.CohenMacaulay.mk ?_
    rw [← Module.supportDim_eq_of_equiv eA, ← moduleDepth_eq_of_equiv eA,
      hA.supportDim_eq_moduleDepth]
  -- A ring equivalence is in particular a surjective local algebra map.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := A) (S := B) (N := B) hsurj).mpr hAB

omit [Algebra.EssFiniteType k K] [IsNoetherianRing S] in
/-- Helper for Lemma 10.167.2: the canonical `S`-algebra `K ⊗[k] S` is flat over `S`. -/
private theorem tensorProduct_right_flat :
    Module.Flat S S_K := by
  letI : Module.Flat k K := Module.Flat.of_projective
  have hBase : Module.Flat S (S ⊗[k] K) := by
    -- Proof comment: flatness of the field extension `K / k` survives base change along `k → S`.
    exact Module.Flat.baseChange (R := k) (S := S) (M := K)
  -- Proof comment: the right-commutativity equivalence identifies `S ⊗[k] K` with
  -- `K ⊗[k] S` as an `S`-module.
  exact Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight k S K).symm.toLinearEquiv

-- The public fiber-presentation API from Lemma `10.163.5` works over a flat base ring map, so
-- keep the canonical flatness instance for `S → K ⊗[k] S` available throughout this file.
local instance tensorProduct_moduleFlat : Module.Flat S S_K :=
  tensorProduct_right_flat (k := k) (K := K) (S := S)

/-- Helper for Lemma 10.167.2: the localized map `S_(q ∩ S) → (K ⊗[k] S)_q` supplies the
canonical algebra structure on the target localization. -/
private noncomputable instance localizedTensorProductAlgebra (q : PrimeSpectrum S_K) :
    Algebra (Localization.AtPrime (q.asIdeal.under S)) (Localization.AtPrime q.asIdeal) :=
  (Localization.localRingHom (q.asIdeal.under S) q.asIdeal (algebraMap S S_K)
    rfl).toAlgebra

omit [Algebra.EssFiniteType k K] [IsNoetherianRing S] in
/-- Helper for Lemma 10.167.2: localizing `S → K ⊗[k] S` at `p = q ∩ S` and `q` gives a flat
local map `S_p → (K ⊗[k] S)_q`. -/
private theorem localized_algebraMap_flat_local_at_under
    (q : PrimeSpectrum S_K) :
    let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
    (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat ∧
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  have halg :
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap S S_K)
          (q.asIdeal.over_def p.asIdeal) =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      -- Proof comment: both maps are the canonical scalar-extension map from `S` into the
      -- localization at `q`.
      rw [← IsScalarTower.algebraMap_apply S S_K (Localization.AtPrime q.asIdeal) x]
      rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) x]
  letI : Module.Flat S S_K := tensorProduct_right_flat (k := k) (K := K) (S := S)
  have hflatSK : (algebraMap S S_K).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat := by
    -- Proof comment: flatness of `S → K ⊗[k] S` survives localization at `p = q ∩ S` and `q`.
    simpa [halg] using
      (RingHom.Flat.localRingHom hflatSK q.asIdeal p.asIdeal (q.asIdeal.over_def p.asIdeal))
  have hlocal :
      IsLocalHom
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- Proof comment: the universal localized map is local by construction.
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal
        (algebraMap S S_K) (q.asIdeal.over_def p.asIdeal))
  exact ⟨hflat, hlocal⟩

/-- Helper for Lemma 10.167.2: the fiber ring over `p` of the tensor product `K ⊗[k] S`
identifies with `K ⊗[k] κ(p)`. -/
private noncomputable def tensorProduct_fiber_algEquiv
    (p : PrimeSpectrum S) :
    p.asIdeal.Fiber S_K ≃ₐ[p.asIdeal.ResidueField] (K ⊗[k] p.asIdeal.ResidueField) :=
  let e₁ :
      p.asIdeal.Fiber S_K ≃ₐ[p.asIdeal.ResidueField]
        p.asIdeal.ResidueField ⊗[S] (S ⊗[k] K) :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.commRight k S K).symm
  let e₂ :
      p.asIdeal.ResidueField ⊗[S] (S ⊗[k] K) ≃ₐ[p.asIdeal.ResidueField]
        p.asIdeal.ResidueField ⊗[k] K :=
    Algebra.TensorProduct.cancelBaseChange k S p.asIdeal.ResidueField p.asIdeal.ResidueField K
  let e₃ :
      p.asIdeal.ResidueField ⊗[k] K ≃ₐ[p.asIdeal.ResidueField] (K ⊗[k] p.asIdeal.ResidueField) :=
    Algebra.TensorProduct.commRight k p.asIdeal.ResidueField K
  e₁.trans (e₂.trans e₃)

omit [IsNoetherianRing S] in
/-- Helper for Lemma 10.167.2: the canonical fiber local ring at an upstairs prime is
Cohen-Macaulay because it is a localization of `K ⊗[k] κ(p)`. -/
private theorem fiberLocalRingAt_cohenMacaulay_of_tensorProduct_field_extension
    (q : PrimeSpectrum S_K) :
    Module.CohenMacaulay (fiberLocalRingAt S S_K q) (fiberLocalRingAt S S_K q) := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let eFiber :
      p.asIdeal.Fiber S_K ≃ₐ[p.asIdeal.ResidueField] (K ⊗[k] p.asIdeal.ResidueField) :=
    tensorProduct_fiber_algEquiv (k := k) (K := K) (S := S) p
  let qTensor : PrimeSpectrum (K ⊗[k] p.asIdeal.ResidueField) :=
    PrimeSpectrum.comapEquiv eFiber.toRingEquiv (fiberPrimeAt S S_K q)
  have hqTensor :
      Ideal.comap eFiber.toRingHom qTensor.asIdeal = (fiberPrimeAt S S_K q).asIdeal := by
    simpa [qTensor] using
      congrArg PrimeSpectrum.asIdeal
        ((PrimeSpectrum.comapEquiv eFiber.toRingEquiv).left_inv (fiberPrimeAt S S_K q))
  let eLocal0 :
      Localization.AtPrime (fiberPrimeAt S S_K q).asIdeal ≃+*
        Localization.AtPrime qTensor.asIdeal :=
    Localization.localRingEquiv (fiberPrimeAt S S_K q).asIdeal qTensor.asIdeal
      eFiber.toRingEquiv
      hqTensor.symm
  let eLocal :
      fiberLocalRingAt S S_K q ≃+* Localization.AtPrime qTensor.asIdeal := by
    simpa [fiberLocalRingAt] using eLocal0
  letI : CohenMacaulayRing (K ⊗[k] p.asIdeal.ResidueField) :=
    cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension
      (k := k) (K := K) (L := p.asIdeal.ResidueField)
  letI :
      Module.CohenMacaulay (Localization.AtPrime qTensor.asIdeal)
        (Localization.AtPrime qTensor.asIdeal) :=
    localizedRing_cohenMacaulay (K ⊗[k] p.asIdeal.ResidueField) qTensor
  letI : IsNoetherianRing (fiberLocalRingAt S S_K q) :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime qTensor.asIdeal) eLocal.symm
  -- Transport the localized Cohen-Macaulay property across the canonical local ring equivalence.
  exact cohenMacaulay_of_ringEquiv eLocal.symm

omit [IsNoetherianRing S] in
/-- Helper for Lemma 10.167.2: the canonical fiber local ring at an upstairs prime is Noetherian
because it is a localization of `K ⊗[k] κ(p)`. -/
private theorem fiberLocalRingAt_isNoetherianRing_of_tensorProduct_field_extension
    (q : PrimeSpectrum S_K) :
    IsNoetherianRing (fiberLocalRingAt S S_K q) := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let eFiber :
      p.asIdeal.Fiber S_K ≃ₐ[p.asIdeal.ResidueField] (K ⊗[k] p.asIdeal.ResidueField) :=
    tensorProduct_fiber_algEquiv (k := k) (K := K) (S := S) p
  let qTensor : PrimeSpectrum (K ⊗[k] p.asIdeal.ResidueField) :=
    PrimeSpectrum.comapEquiv eFiber.toRingEquiv (fiberPrimeAt S S_K q)
  have hqTensor :
      Ideal.comap eFiber.toRingHom qTensor.asIdeal = (fiberPrimeAt S S_K q).asIdeal := by
    simpa [qTensor] using
      congrArg PrimeSpectrum.asIdeal
        ((PrimeSpectrum.comapEquiv eFiber.toRingEquiv).left_inv (fiberPrimeAt S S_K q))
  let eLocal0 :
      Localization.AtPrime (fiberPrimeAt S S_K q).asIdeal ≃+*
        Localization.AtPrime qTensor.asIdeal :=
    Localization.localRingEquiv (fiberPrimeAt S S_K q).asIdeal qTensor.asIdeal
      eFiber.toRingEquiv
      hqTensor.symm
  let eLocal :
      fiberLocalRingAt S S_K q ≃+* Localization.AtPrime qTensor.asIdeal := by
    simpa [fiberLocalRingAt] using eLocal0
  exact isNoetherianRing_of_ringEquiv (Localization.AtPrime qTensor.asIdeal) eLocal.symm

omit [Algebra.EssFiniteType k K] [IsNoetherianRing S] in
/-- Helper for Lemma 10.167.2: contracting the fiber prime attached to `q` back to `K ⊗[k] S`
recovers `q` itself. -/
private lemma tensorProduct_fiberPrimeAt_comap
    (q : PrimeSpectrum S_K) :
    let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
    Ideal.comap (algebraMap S_K (p.asIdeal.Fiber S_K)) (fiberPrimeAt S S_K q).asIdeal =
      q.asIdeal := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  have hq :
      ↑((PrimeSpectrum.preimageEquivFiber S S_K p).symm (fiberPrimeAt S S_K q)) = q := by
    simpa [p, fiberPrimeAt] using
      congrArg Subtype.val
        ((PrimeSpectrum.preimageEquivFiber S S_K p).symm_apply_apply ⟨q, rfl⟩)
  -- Proof comment: `fiberPrimeAt` is defined via `preimageEquivFiber`, so the canonical
  -- contraction lemma from Lemma `10.46.8` gives back the original upstairs prime.
  change Ideal.comap Algebra.TensorProduct.includeRight.toRingHom
      (fiberPrimeAt S S_K q).asIdeal = q.asIdeal
  calc
    Ideal.comap Algebra.TensorProduct.includeRight.toRingHom (fiberPrimeAt S S_K q).asIdeal =
        (((PrimeSpectrum.preimageEquivFiber S S_K p).symm (fiberPrimeAt S S_K q)).1).asIdeal := by
          simpa [p, fiberPrimeAt] using
            (fiber_prime_comap_asIdeal (R := S) (S := S_K) p (fiberPrimeAt S S_K q))
    _ = q.asIdeal := by
          simpa using congrArg PrimeSpectrum.asIdeal hq

/-- Helper for Lemma 10.167.2: in the quotient-localization presentation of the fiber over
`p = q ∩ S`, the induced prime contracts to the quotient prime `q̄`. -/
private lemma tensorProduct_qT_comap_eq_qbar
    (q : PrimeSpectrum S_K) :
    let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
    let I : Ideal S_K := Ideal.map (algebraMap S S_K) p.asIdeal
    let T : Submonoid (S_K ⧸ I) :=
      Algebra.algebraMapSubmonoid (S_K ⧸ I) (nonZeroDivisors (S ⧸ p.asIdeal))
    let eFiber : Localization T ≃ₐ[S_K ⧸ I] p.asIdeal.Fiber S_K :=
      fiber_quotient_localization_algEquiv (R := S) (S := S_K) p
    let qT : PrimeSpectrum (Localization T) :=
      PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt S S_K q)
    Ideal.comap (algebraMap (S_K ⧸ I) (Localization T)) qT.asIdeal =
      Ideal.map (Ideal.Quotient.mk I) q.asIdeal := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let I : Ideal S_K := Ideal.map (algebraMap S S_K) p.asIdeal
  let T : Submonoid (S_K ⧸ I) :=
    Algebra.algebraMapSubmonoid (S_K ⧸ I) (nonZeroDivisors (S ⧸ p.asIdeal))
  let eFiber : Localization T ≃ₐ[S_K ⧸ I] p.asIdeal.Fiber S_K :=
    fiber_quotient_localization_algEquiv (R := S) (S := S_K) p
  let qT : PrimeSpectrum (Localization T) :=
    PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt S S_K q)
  have hI_le_q : I ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    simpa [I, p, PrimeSpectrum.comap_asIdeal]
  have hFiberComap :
      Ideal.comap (algebraMap S_K (p.asIdeal.Fiber S_K)) (fiberPrimeAt S S_K q).asIdeal =
        q.asIdeal := by
    simpa [p] using
      (tensorProduct_fiberPrimeAt_comap (k := k) (K := K) (S := S) q)
  -- Proof comment: after quotienting by `pS_K`, the presentation map to the fiber ring agrees
  -- with the canonical algebra map on generators, so contraction along the localization map
  -- matches contraction along the fiber inclusion.
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  calc
    Ideal.comap ((algebraMap (S_K ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I))
        (Ideal.comap eFiber.toRingHom (fiberPrimeAt S S_K q).asIdeal) =
      Ideal.comap
        (eFiber.toRingHom.comp
          ((algebraMap (S_K ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)))
        (fiberPrimeAt S S_K q).asIdeal := by
          rfl
    _ =
      Ideal.comap (algebraMap S_K (p.asIdeal.Fiber S_K)) (fiberPrimeAt S S_K q).asIdeal := by
        congr 1
        apply RingHom.ext
        intro y
        calc
          eFiber.toRingHom
              ((algebraMap (S_K ⧸ I) (Localization T)) (Ideal.Quotient.mk I y)) =
              algebraMap (S_K ⧸ I) (p.asIdeal.Fiber S_K) (Ideal.Quotient.mk I y) := by
                exact eFiber.commutes (Ideal.Quotient.mk I y)
          _ = algebraMap S_K (p.asIdeal.Fiber S_K) y := by
                rw [quotient_to_fiber_algebraMap_mk (R := S) (S := S_K) (p := p)]
                rfl
    _ = q.asIdeal := hFiberComap
    _ = Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q.asIdeal) := by
        symm
        exact Ideal.comap_map_mk hI_le_q

/-- Helper for Lemma 10.167.2: the quotient model of the localized closed fiber at `q`. -/
private noncomputable def localized_quotient_at_tensorProduct_prime
    (q : PrimeSpectrum S_K) : Type _ :=
  (Localization.AtPrime q.asIdeal) ⧸
    Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) (q.asIdeal.under S)

/-- Helper for Lemma 10.167.2: the quotient model of the localized closed fiber carries its
canonical commutative-ring structure. -/
noncomputable instance localized_quotient_at_tensorProduct_prime_commRing (q : PrimeSpectrum S_K) :
    CommRing (localized_quotient_at_tensorProduct_prime (S := S) q) := by
  dsimp [localized_quotient_at_tensorProduct_prime]
  infer_instance

/-- Helper for Lemma 10.167.2: the quotient model acts on itself by multiplication. -/
noncomputable instance localized_quotient_at_tensorProduct_prime_module (q : PrimeSpectrum S_K) :
    Module (localized_quotient_at_tensorProduct_prime (S := S) q)
      (localized_quotient_at_tensorProduct_prime (S := S) q) :=
  Semiring.toModule

/-- Helper for Lemma 10.167.2: the localized quotient presentation
`(K ⊗[k] S)_q / p (K ⊗[k] S)_q` identifies with the canonical fiber local ring at `q`. -/
private lemma quotient_primeCompl_eq_algebraMapSubmonoid_at_under
    {A : Type*} [CommRing A] (I q : Ideal A) [q.IsPrime]
    [(Ideal.map (Ideal.Quotient.mk I) q).IsPrime] (hIq : I ≤ q) :
    Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl =
      (Ideal.map (Ideal.Quotient.mk I) q).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Proof comment: if `a mod I` landed in the quotient prime, pulling back along the quotient
    -- map would force `a ∈ q`, contradicting `a ∉ q`.
    change Ideal.Quotient.mk I a ∉ Ideal.map (Ideal.Quotient.mk I) q
    intro hx
    have hqx : a ∈ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) := by
      exact hx
    exact ha <| by simpa [Ideal.comap_map_mk hIq] using hqx
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_, rfl⟩
    -- Proof comment: conversely, if `a mod I` avoids the quotient prime, then `a` itself already
    -- avoids `q`.
    intro ha
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) ha)

/-- Helper for Lemma 10.167.2: the named localized closed fiber of
`S_(q ∩ S) → (K ⊗[k] S)_q`. -/
private noncomputable def local_closed_fiber_at_under (q : PrimeSpectrum S_K) : Type _ :=
  let Rp := Localization.AtPrime (q.asIdeal.under S)
  let Sq := Localization.AtPrime q.asIdeal
  (IsLocalRing.maximalIdeal Rp).Fiber Sq

/-- Helper for Lemma 10.167.2: the named localized closed fiber carries its canonical
commutative-ring structure. -/
noncomputable instance local_closed_fiber_at_under_commRing (q : PrimeSpectrum S_K) :
    CommRing (local_closed_fiber_at_under (S := S) q) := by
  dsimp [local_closed_fiber_at_under]
  infer_instance

/-- Helper for Lemma 10.167.2: the named localized closed fiber acts on itself by multiplication. -/
noncomputable instance local_closed_fiber_at_under_module (q : PrimeSpectrum S_K) :
    Module (local_closed_fiber_at_under (S := S) q)
      (local_closed_fiber_at_under (S := S) q) :=
  Semiring.toModule

/-- Helper for Lemma 10.167.2: the closed fiber of a Noetherian local homomorphism is local via
its quotient presentation. -/
private theorem closed_fiber_isLocalRing_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] :
    IsLocalRing ((IsLocalRing.maximalIdeal A).Fiber B) := by
  let I : Ideal B := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
  letI : IsLocalRing (B ⧸ I) := by
    have hI_lt_top : I < (⊤ : Ideal B) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)
    have : Nontrivial (B ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hI_lt_top.ne
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  -- Proof comment: the canonical quotient model of the closed fiber carries the local-ring
  -- structure, so the equivalence transports it to the literal fiber ring.
  exact (closedFiber_quotient_equiv (R := A) (S := B)).toRingEquiv.isLocalRing

/-- Helper for Lemma 10.167.2: the closed fiber of a Noetherian local homomorphism is Noetherian
via its quotient presentation. -/
private theorem closed_fiber_isNoetherianRing_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] :
    IsNoetherianRing ((IsLocalRing.maximalIdeal A).Fiber B) :=
  isNoetherianRing_of_ringEquiv
    (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))
    (closedFiber_quotient_equiv (R := A) (S := B)).toRingEquiv

/-- Helper for Lemma 10.167.2: the named closed fiber of `S_(q ∩ S) → (K ⊗[k] S)_q` is local. -/
private theorem local_closed_fiber_at_under_isLocalRing (q : PrimeSpectrum S_K) :
    IsLocalRing (local_closed_fiber_at_under (S := S) q) := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hflatLocal := localized_algebraMap_flat_local_at_under (k := k) (K := K) (S := S) q
  letI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the localized algebra map is local by the same canonical localization
    -- comparison used in the main proof.
    simpa [p, Rp, Sq, local_closed_fiber_at_under] using hflatLocal.2
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (closed_fiber_isLocalRing_of_localHom (A := Rp) (B := Sq))

/-- Helper for Lemma 10.167.2: the named localized closed fiber inherits its local-ring
structure from the quotient presentation. -/
noncomputable instance local_closed_fiber_at_under_isLocalRing_inst (q : PrimeSpectrum S_K) :
    IsLocalRing (local_closed_fiber_at_under (S := S) q) :=
  local_closed_fiber_at_under_isLocalRing (k := k) (K := K) (S := S) q

/-- Helper for Lemma 10.167.2: the named closed fiber of `S_(q ∩ S) → (K ⊗[k] S)_q` is
Noetherian. -/
private theorem local_closed_fiber_at_under_isNoetherianRing (q : PrimeSpectrum S_K) :
    IsNoetherianRing (local_closed_fiber_at_under (S := S) q) := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  have hflatLocal := localized_algebraMap_flat_local_at_under (k := k) (K := K) (S := S) q
  letI : IsLocalHom (algebraMap Rp Sq) := by
    -- Proof comment: the same localized algebra map supplies the local-hom hypothesis needed by
    -- the quotient presentation of the named closed fiber.
    simpa [p, Rp, Sq, local_closed_fiber_at_under] using hflatLocal.2
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (closed_fiber_isNoetherianRing_of_localHom (A := Rp) (B := Sq))

/-- Helper for Lemma 10.167.2: the named localized closed fiber inherits Noetherianity from its
quotient presentation. -/
noncomputable instance local_closed_fiber_at_under_isNoetherianRing_inst (q : PrimeSpectrum S_K) :
    IsNoetherianRing (local_closed_fiber_at_under (S := S) q) :=
  local_closed_fiber_at_under_isNoetherianRing (k := k) (K := K) (S := S) q

attribute [local instance]
  local_closed_fiber_at_under_commRing
  local_closed_fiber_at_under_module
  local_closed_fiber_at_under_isLocalRing_inst
  local_closed_fiber_at_under_isNoetherianRing_inst

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 5000000 in
/-- Helper for Lemma 10.167.2: the quotient presentation
`(K ⊗[k] S)_q / (q ∩ S)(K ⊗[k] S)_q` identifies with the canonical fiber local ring at `q`. -/
private noncomputable def localized_quotient_ringEquiv_fiberLocalRingAt
    (q : PrimeSpectrum S_K) := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let I : Ideal S_K := Ideal.map (algebraMap S S_K) p.asIdeal
  letI : CommRing (S_K ⧸ I) := by
    infer_instance
  letI : Module (S_K ⧸ I) (S_K ⧸ I) :=
    Semiring.toModule
  let Qloc :=
    (Localization.AtPrime q.asIdeal) ⧸
      Ideal.map (algebraMap S_K (Localization.AtPrime q.asIdeal)) I
  have hQloc :
      Ideal.map (algebraMap S_K (Localization.AtPrime q.asIdeal)) I =
        Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    -- Proof comment: extending `p` to `K ⊗[k] S` and then localizing is the same as extending `p`
    -- directly to `(K ⊗[k] S)_q`.
    dsimp [I]
    simpa [IsScalarTower.algebraMap_eq S S_K (Localization.AtPrime q.asIdeal)] using
      (Ideal.map_map (I := p.asIdeal) (f := algebraMap S S_K)
        (g := algebraMap S_K (Localization.AtPrime q.asIdeal)))
  let eTarget :
      Qloc ≃+*
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap S (Localization.AtPrime q.asIdeal)) (q.asIdeal.under S)) :=
    Ideal.quotEquivOfEq hQloc
  have hqbarPrime : (Ideal.map (Ideal.Quotient.mk I) q.asIdeal).IsPrime := by
    have hI_le_q : I ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [I, p, PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective <| by
        simpa [Ideal.mk_ker] using hI_le_q
  let qbar : PrimeSpectrum (S_K ⧸ I) :=
    ⟨Ideal.map (Ideal.Quotient.mk I) q.asIdeal, hqbarPrime⟩
  let M : Submonoid (S_K ⧸ I) :=
    Algebra.algebraMapSubmonoid (S_K ⧸ I) q.asIdeal.primeCompl
  let eLoc :
      Localization M ≃ₐ[S_K ⧸ I] Qloc :=
    Localization.algEquiv M Qloc
  have hSub :
      M = qbar.asIdeal.primeCompl := by
    -- Proof comment: quotienting by `pS_K` turns `q` into the induced prime `q̄`, so the
    -- denominator submonoid is exactly `q̄.primeCompl`.
    simpa [M, qbar] using
      quotient_primeCompl_eq_algebraMapSubmonoid_at_under I q.asIdeal
        (by
          rw [Ideal.map_le_iff_le_comap]
          simpa [I, p, PrimeSpectrum.comap_asIdeal])
  letI : IsLocalization M (Localization.AtPrime qbar.asIdeal) := by
    simpa [hSub] using
      (inferInstance : IsLocalization qbar.asIdeal.primeCompl (Localization.AtPrime qbar.asIdeal))
  let eQuot :
      Qloc ≃ₐ[S_K ⧸ I] Localization.AtPrime qbar.asIdeal :=
    eLoc.symm.trans (Localization.algEquiv M (Localization.AtPrime qbar.asIdeal))
  let T : Submonoid (S_K ⧸ I) :=
    Algebra.algebraMapSubmonoid (S_K ⧸ I) (nonZeroDivisors (S ⧸ p.asIdeal))
  let eFiber :
      Localization T ≃ₐ[S_K ⧸ I] p.asIdeal.Fiber S_K :=
    fiber_quotient_localization_algEquiv (R := S) (S := S_K) p
  let qT : PrimeSpectrum (Localization T) :=
    PrimeSpectrum.comap eFiber.toRingHom (fiberPrimeAt S S_K q)
  have hqTcomap :
      Ideal.comap (algebraMap (S_K ⧸ I) (Localization T)) qT.asIdeal = qbar.asIdeal := by
    -- Proof comment: the prime of the fiber ring corresponding to `q` contracts back to the
    -- induced quotient prime `q̄`.
    simpa [I, qbar, qT] using
      tensorProduct_qT_comap_eq_qbar (k := k) (K := K) (S := S) q
  let qbar' : PrimeSpectrum (S_K ⧸ I) :=
    PrimeSpectrum.comap (algebraMap (S_K ⧸ I) (Localization T)) qT
  let eSource :
      Localization.AtPrime qbar.asIdeal ≃+* Localization.AtPrime qbar'.asIdeal :=
    Localization.localRingEquiv qbar.asIdeal qbar'.asIdeal (RingEquiv.refl (S_K ⧸ I))
      (by simpa [qbar'] using hqTcomap.symm)
  let eTower :
      Localization.AtPrime qbar'.asIdeal ≃+* Localization.AtPrime qT.asIdeal :=
    -- Proof comment: localizing the quotient presentation again at the prime over `q̄`
    -- collapses the localization tower.
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := T) qT.asIdeal).toRingEquiv
  let eFiberLocal0 :
      Localization.AtPrime qT.asIdeal ≃+*
        Localization.AtPrime (fiberPrimeAt S S_K q).asIdeal :=
    -- Proof comment: localizing corresponding primes along the quotient-to-fiber equivalence
    -- recovers the canonical fiber local ring.
    Localization.localRingEquiv qT.asIdeal (fiberPrimeAt S S_K q).asIdeal eFiber.toRingEquiv
      (PrimeSpectrum.comap_asIdeal (f := eFiber.toRingHom) (fiberPrimeAt S S_K q))
  -- Proof comment: composing the quotient-localization comparison with the fiber presentation
  -- gives the source proof's canonical quotient model of the local fiber ring.
  simpa [p] using
    ((((eTarget.symm.trans eQuot.toRingEquiv).trans eSource).trans eTower).trans eFiberLocal0)

/-- Helper for Lemma 10.167.2: the named localized closed fiber identifies with the canonical
fiber local ring at `q`. -/
private noncomputable def local_closed_fiber_at_under_ringEquiv_fiberLocalRingAt
    (q : PrimeSpectrum S_K) :
    local_closed_fiber_at_under (S := S) q ≃+* fiberLocalRingAt S S_K q := by
  letI : CommRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_commRing (S := S) q
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : q.asIdeal.LiesOver p.asIdeal := by
    simpa [p] using (Ideal.over_under q.asIdeal)
  let eClosedFiber :
      local_closed_fiber_at_under (S := S) q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (closedFiber_quotient_equiv (R := Rp) (S := Sq)).symm.toRingEquiv
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        (Sq ⧸ Ideal.map (algebraMap S Sq) p.asIdeal) :=
    Ideal.quotEquivOfEq
      (localized_base_prime_eq_map_maximalIdeal
        (R := S) (S := S_K) p.asIdeal q.asIdeal inferInstance)
  let eQuotToFiber :
      (Sq ⧸ Ideal.map (algebraMap S Sq) p.asIdeal) ≃+* fiberLocalRingAt S S_K q := by
    simpa [fiberLocalRingAt, p, Sq] using
      (localized_quotient_ringEquiv_fiberLocalRingAt (k := k) (K := K) (S := S) q)
  -- Proof comment: rewrite the literal closed fiber of `S_p → (K ⊗[k] S)_q` to the quotient
  -- `(K ⊗[k] S)_q / p (K ⊗[k] S)_q`, then use the canonical quotient presentation of the fiber
  -- local ring.
  simpa [p, Rp, Sq, local_closed_fiber_at_under] using
    (eClosedFiber.trans eRewrite).trans
      eQuotToFiber

/-- Helper for Lemma 10.167.2: the actual closed fiber of
`S_(q ∩ S) → (K ⊗[k] S)_q` is Cohen-Macaulay because its quotient presentation is. -/
private theorem closedFiber_cohenMacaulay_at_tensorProduct_prime
    (q : PrimeSpectrum S_K) :
    let _ : CommRing (local_closed_fiber_at_under (S := S) q) :=
      local_closed_fiber_at_under_commRing (S := S) q
    let _ : Module (local_closed_fiber_at_under (S := S) q)
        (local_closed_fiber_at_under (S := S) q) :=
      local_closed_fiber_at_under_module (S := S) q
    let _ : IsLocalRing (local_closed_fiber_at_under (S := S) q) :=
      local_closed_fiber_at_under_isLocalRing (k := k) (K := K) (S := S) q
    let _ : IsNoetherianRing (local_closed_fiber_at_under (S := S) q) :=
      local_closed_fiber_at_under_isNoetherianRing (k := k) (K := K) (S := S) q
    Module.CohenMacaulay
      (local_closed_fiber_at_under (S := S) q)
      (local_closed_fiber_at_under (S := S) q) := by
  letI : CommRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_commRing (S := S) q
  letI : Module (local_closed_fiber_at_under (S := S) q)
      (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_module (S := S) q
  letI : IsLocalRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_isLocalRing (k := k) (K := K) (S := S) q
  letI : IsNoetherianRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_isNoetherianRing (k := k) (K := K) (S := S) q
  let e :
      local_closed_fiber_at_under (S := S) q ≃+* fiberLocalRingAt S S_K q :=
    local_closed_fiber_at_under_ringEquiv_fiberLocalRingAt (k := k) (K := K) (S := S) q
  letI : Module.CohenMacaulay (fiberLocalRingAt S S_K q) (fiberLocalRingAt S S_K q) :=
    fiberLocalRingAt_cohenMacaulay_of_tensorProduct_field_extension
      (k := k) (K := K) (S := S) q
  letI : IsNoetherianRing (fiberLocalRingAt S S_K q) :=
    fiberLocalRingAt_isNoetherianRing_of_tensorProduct_field_extension
      (k := k) (K := K) (S := S) q
  -- Proof comment: the actual closed fiber is Cohen-Macaulay because it is canonically the
  -- fiber local ring over `q`.
  exact cohenMacaulay_of_ringEquiv e.symm

/-- Helper for Lemma 10.167.2: the quotient model of the localized closed fiber is local because
it is the standard quotient presentation of the actual closed fiber. -/
private theorem localized_quotient_at_tensorProduct_prime_isLocalRing
    (q : PrimeSpectrum S_K) :
    IsLocalRing (localized_quotient_at_tensorProduct_prime (S := S) q) := by
  letI : CommRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
    localized_quotient_at_tensorProduct_prime_commRing (S := S) q
  letI : CommRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_commRing (S := S) q
  letI : IsLocalRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_isLocalRing (k := k) (K := K) (S := S) q
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : Algebra Rp Sq := localizedTensorProductAlgebra (S := S) q
  let eClosedFiber :
      local_closed_fiber_at_under (S := S) q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (closedFiber_quotient_equiv (R := Rp) (S := Sq)).symm.toRingEquiv
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        localized_quotient_at_tensorProduct_prime (S := S) q :=
    Ideal.quotEquivOfEq
      (localized_base_prime_eq_map_maximalIdeal
        (R := S) (S := S_K) p.asIdeal q.asIdeal inferInstance)
  -- Proof comment: the quotient model is the standard quotient presentation of the actual closed
  -- fiber, so the local-ring structure transports across that equivalence.
  exact (eClosedFiber.trans eRewrite).isLocalRing

/-- Helper for Lemma 10.167.2: the quotient model of the localized closed fiber inherits its
local-ring structure from the actual closed fiber. -/
noncomputable instance localized_quotient_at_tensorProduct_prime_isLocalRing_inst
    (q : PrimeSpectrum S_K) :
    IsLocalRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
  localized_quotient_at_tensorProduct_prime_isLocalRing (k := k) (K := K) (S := S) q

/-- Helper for Lemma 10.167.2: the quotient model of the localized closed fiber is Noetherian
because it is canonically ring-equivalent to the actual closed fiber. -/
private theorem localized_quotient_at_tensorProduct_prime_isNoetherianRing
    (q : PrimeSpectrum S_K) :
    IsNoetherianRing (localized_quotient_at_tensorProduct_prime (S := S) q) := by
  letI : CommRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
    localized_quotient_at_tensorProduct_prime_commRing (S := S) q
  letI : CommRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_commRing (S := S) q
  letI : IsNoetherianRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_isNoetherianRing (k := k) (K := K) (S := S) q
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : Algebra Rp Sq := localizedTensorProductAlgebra (S := S) q
  let eClosedFiber :
      local_closed_fiber_at_under (S := S) q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (closedFiber_quotient_equiv (R := Rp) (S := Sq)).symm.toRingEquiv
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        localized_quotient_at_tensorProduct_prime (S := S) q :=
    Ideal.quotEquivOfEq
      (localized_base_prime_eq_map_maximalIdeal
        (R := S) (S := S_K) p.asIdeal q.asIdeal inferInstance)
  -- Proof comment: the quotient model is Noetherian because the actual closed fiber is, and the
  -- two rings are canonically equivalent.
  exact isNoetherianRing_of_ringEquiv (local_closed_fiber_at_under (S := S) q)
    (eClosedFiber.trans eRewrite)

/-- Helper for Lemma 10.167.2: the quotient model of the localized closed fiber inherits
Noetherianity from the actual closed fiber. -/
noncomputable instance localized_quotient_at_tensorProduct_prime_isNoetherianRing_inst
    (q : PrimeSpectrum S_K) :
    IsNoetherianRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
  localized_quotient_at_tensorProduct_prime_isNoetherianRing
    (k := k) (K := K) (S := S) q

/-- Helper for Lemma 10.167.2: the quotient presentation
`(K ⊗[k] S)_q / p (K ⊗[k] S)_q` is Cohen-Macaulay because it is the standard quotient model of
the actual closed fiber. -/
private theorem localized_quotient_cohenMacaulay_at_tensorProduct_prime
    (q : PrimeSpectrum S_K) :
    let _ : CommRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
      localized_quotient_at_tensorProduct_prime_commRing (S := S) q
    let _ : Module (localized_quotient_at_tensorProduct_prime (S := S) q)
        (localized_quotient_at_tensorProduct_prime (S := S) q) :=
      localized_quotient_at_tensorProduct_prime_module (S := S) q
    let _ : IsLocalRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
      localized_quotient_at_tensorProduct_prime_isLocalRing (k := k) (K := K) (S := S) q
    let _ : IsNoetherianRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
      localized_quotient_at_tensorProduct_prime_isNoetherianRing (k := k) (K := K) (S := S) q
    Module.CohenMacaulay
      (localized_quotient_at_tensorProduct_prime (S := S) q)
      (localized_quotient_at_tensorProduct_prime (S := S) q) := by
  letI : CommRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
    localized_quotient_at_tensorProduct_prime_commRing (S := S) q
  letI : Module (localized_quotient_at_tensorProduct_prime (S := S) q)
      (localized_quotient_at_tensorProduct_prime (S := S) q) :=
    localized_quotient_at_tensorProduct_prime_module (S := S) q
  letI : IsLocalRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
    localized_quotient_at_tensorProduct_prime_isLocalRing (k := k) (K := K) (S := S) q
  letI : IsNoetherianRing (localized_quotient_at_tensorProduct_prime (S := S) q) :=
    localized_quotient_at_tensorProduct_prime_isNoetherianRing
      (k := k) (K := K) (S := S) q
  letI : CommRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_commRing (S := S) q
  letI : Module (local_closed_fiber_at_under (S := S) q)
      (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_module (S := S) q
  letI : IsLocalRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_isLocalRing (k := k) (K := K) (S := S) q
  letI : IsNoetherianRing (local_closed_fiber_at_under (S := S) q) :=
    local_closed_fiber_at_under_isNoetherianRing (k := k) (K := K) (S := S) q
  letI : Module.CohenMacaulay
      (local_closed_fiber_at_under (S := S) q) (local_closed_fiber_at_under (S := S) q) :=
    closedFiber_cohenMacaulay_at_tensorProduct_prime (k := k) (K := K) (S := S) q
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : Algebra Rp Sq := localizedTensorProductAlgebra (S := S) q
  let eClosedFiber :
      local_closed_fiber_at_under (S := S) q ≃+*
        (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) :=
    (closedFiber_quotient_equiv (R := Rp) (S := Sq)).symm.toRingEquiv
  let eRewrite :
      (Sq ⧸ Ideal.map (algebraMap Rp Sq) (IsLocalRing.maximalIdeal Rp)) ≃+*
        localized_quotient_at_tensorProduct_prime (S := S) q :=
    Ideal.quotEquivOfEq
      (localized_base_prime_eq_map_maximalIdeal
        (R := S) (S := S_K) p.asIdeal q.asIdeal inferInstance)
  -- Proof comment: the quotient presentation is Cohen-Macaulay because it is canonically the
  -- standard quotient model of the actual closed fiber.
  exact cohenMacaulay_of_ringEquiv (eClosedFiber.trans eRewrite)

-- Proof sketch: the local map `S_(q_K ∩ S) → (K ⊗[k] S)_{q_K}` is flat because it is obtained from the
-- flat base-change map `S → K ⊗[k] S` by localization. Its closed fiber is a localization of
-- `κ(q_K ∩ S) ⊗[k] K`, which is Cohen-Macaulay by Lemma `10.167.1`. Apply Lemma `10.163.3` to
-- this flat local map and the Cohen-Macaulay closed fiber.
/-- Lemma 10.167.2: for a field `k`, a Noetherian `k`-algebra `S`, a finitely generated field
extension `K / k`, recorded canonically by `Algebra.EssFiniteType k K`, and a prime `q_K` of
`K ⊗[k] S`, the local ring `S_(q_K ∩ S)` is Cohen-Macaulay if and only if
`(K ⊗[k] S)_{q_K}` is Cohen-Macaulay. -/
@[stacks 045N]
theorem cohenMacaulayRing_localizationAtPrime_under_iff_tensorProduct_localizationAtPrime
    (qK : Ideal S_K) [qK.IsPrime] :
    Module.CohenMacaulay (Localization.AtPrime (qK.under S)) (Localization.AtPrime (qK.under S)) ↔
      Module.CohenMacaulay (Localization.AtPrime qK) (Localization.AtPrime qK) := by
  let q : PrimeSpectrum S_K := ⟨qK, inferInstance⟩
  let p : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S S_K) q
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  letI : Algebra Rp Sq := localizedTensorProductAlgebra (S := S) q
  letI : Module Rp Sq := Algebra.toModule
  have hflatLocal := localized_algebraMap_flat_local_at_under (k := k) (K := K) (S := S) q
  letI : Module.Flat Rp Sq := (RingHom.flat_algebraMap_iff).mp <| by
    simpa [p, Rp, Sq] using hflatLocal.1
  letI : IsLocalHom (algebraMap Rp Sq) := by
    simpa [p, Rp, Sq] using hflatLocal.2
  letI : IsLocalRing ((IsLocalRing.maximalIdeal Rp).Fiber Sq) :=
    closed_fiber_isLocalRing_of_localHom (A := Rp) (B := Sq)
  letI : IsNoetherianRing ((IsLocalRing.maximalIdeal Rp).Fiber Sq) :=
    closed_fiber_isNoetherianRing_of_localHom (A := Rp) (B := Sq)
  have hiff :
      Module.CohenMacaulay Sq Sq ↔
        Module.CohenMacaulay Rp Rp ∧
          Module.CohenMacaulay ((IsLocalRing.maximalIdeal Rp).Fiber Sq)
            ((IsLocalRing.maximalIdeal Rp).Fiber Sq) := by
    exact cohenMacaulayRing_iff_source_and_closedFiber (R := Rp) (S := Sq)
  have hfiber :
      Module.CohenMacaulay ((IsLocalRing.maximalIdeal Rp).Fiber Sq)
        ((IsLocalRing.maximalIdeal Rp).Fiber Sq) := by
    -- Proof comment: the closed fiber of the localized tensor-product map is a localization of
    -- `K ⊗[k] κ(p)`, hence Cohen-Macaulay by Lemma `10.167.1`.
    simpa [p, Rp, Sq, local_closed_fiber_at_under] using
      (closedFiber_cohenMacaulay_at_tensorProduct_prime (k := k) (K := K) (S := S) q)
  -- Proof comment: once the closed fiber is known to be Cohen-Macaulay, Lemma `10.163.3`
  -- reduces the target Cohen-Macaulay condition to the source one for the flat local map
  -- `S_p → (K ⊗[k] S)_q`.
  simpa [q, p, Rp, Sq] using
    show Module.CohenMacaulay Rp Rp ↔ Module.CohenMacaulay Sq Sq from by
      constructor
      · intro hRp
        exact hiff.mpr ⟨hRp, hfiber⟩
      · intro hSq
        exact (hiff.mp hSq).1

end
