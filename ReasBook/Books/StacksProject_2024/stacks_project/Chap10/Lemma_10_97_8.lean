import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_97_7

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Ideal AdicCompletion
open scoped TensorProduct

universe u v

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable (p : PrimeSpectrum R)

local notation "Rₚ" => Localization.AtPrime p.asIdeal
local notation "Sₚ" => Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
local notation "mₚ" => maximalIdeal Rₚ
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) mₚ
local notation "Rₚ^" => AdicCompletion mₚ Rₚ

/- Domain triage:
* primary domain: semilocal localization of a finite algebra over a prime, and completion along
  the induced maximal ideal;
* source-facing layer: the product decomposition of the completed semilocal localization into the
  completed local rings at the primes lying over `p`;
* core/canonical owners sampled for this refinement:
  `Ideal.primesOver`,
  `PrimeSpectrum.primesOverOrderIsoFiber`,
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`,
  `MaximalSpectrum.toPiLocalizationEquiv`,
  `AdicCompletion.piEquivOfFintype`;
* bridge/view role here: the source theorem is phrased on the fiber of `Spec(S) → Spec(R)`,
  while the owner object for the indexing set is `p.asIdeal.primesOver S`; the bridge is
  `PrimeSpectrum.primesOverOrderIsoFiber`.

Primitive data are `R`, `S`, the prime `p`, and the finite set `p.asIdeal.primesOver S`. The
public output is the source-facing tensor term `Rₚ^ ⊗[R] S`, its canonical bridge to the
localized tensor product `Rₚ^ ⊗[Rₚ] Sₚ`, and the comparison map from the completed semilocal
localization to the product of completed local rings indexed by that owner set; bijectivity then
packages the latter as the canonical equivalence. -/

/- Companion owners used below:
`PrimeSpectrum.primesOverOrderIsoFiber` identifies the textbook fiber with the owner set
`p.asIdeal.primesOver S`, and
`Localization.tensorRightAlgEquiv p.asIdeal.primeCompl S` is the localization/base-change
identification `Rₚ ⊗[R] S ≃ₐ[Rₚ] Sₚ`, while
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ` is the specialized
tensor-product/completion comparison after localizing at `p`. -/

/-- Lemma 10.97.8, source-facing bridge: the textbook left-hand tensor term `Rₚ^ ⊗[R] S`
canonically identifies with the localized tensor product `Rₚ^ ⊗[Rₚ] Sₚ`. Composing this bridge
with `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ` recovers the tensor/completion
comparison in the localized owner form. -/
noncomputable def completion_tensorProductOverBase_algEquiv_localizedTensorProduct :
    Rₚ^ ⊗[R] S ≃ₐ[Rₚ^] Rₚ^ ⊗[Rₚ] Sₚ := by
  letI : Algebra Rₚ^ (Rₚ^ ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra Rₚ^ (Rₚ^ ⊗[Rₚ] Sₚ) := Algebra.TensorProduct.leftAlgebra
  exact
    (Algebra.TensorProduct.cancelBaseChange R Rₚ Rₚ^ Rₚ^ S).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : Rₚ^ ≃ₐ[Rₚ^] Rₚ^)
        (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl S))

/-- Bridge/view for Lemma 10.97.8: the localized tensor product `Rₚ^ ⊗[Rₚ] Sₚ` canonically
identifies, as an `Rₚ`-algebra, with the `mₚ`-adic completion of the semilocal localization
`Sₚ`. This upgrades the canonical tensor/completion comparison
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian mₚ Sₚ` from its linear owner form to the
ring-level comparison used in the source statement. -/
private noncomputable def completionBaseQuotientMap (n : ℕ) : Rₚ^ →ₐ[Rₚ] Sₚ ⧸ pSₚ ^ n :=
  (Ideal.quotientMapₐ (pSₚ ^ n) (Algebra.ofId Rₚ Sₚ)
    ((Ideal.pow_right_mono (Ideal.le_comap_map : mₚ ≤ Ideal.comap (algebraMap Rₚ Sₚ) pSₚ) n).trans
      (Ideal.le_comap_pow (algebraMap Rₚ Sₚ) n))).comp
    (AdicCompletion.evalₐ mₚ n)

private theorem completionBaseQuotientMap_compatible {m n : ℕ} (h : m ≤ n) :
    ((Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h) :
      Sₚ ⧸ pSₚ ^ n →ₐ[Rₚ] Sₚ ⧸ pSₚ ^ m)).comp (completionBaseQuotientMap p n) =
      completionBaseQuotientMap p m := by
  sorry

private noncomputable def completionBaseAlgHom : Rₚ^ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  AdicCompletion.liftAlgHom pSₚ (completionBaseQuotientMap p)
    (completionBaseQuotientMap_compatible p)

private noncomputable def localizedTensorProduct_to_completion_localizationAtPrime :
    Rₚ^ ⊗[Rₚ] Sₚ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  Algebra.TensorProduct.productMap (completionBaseAlgHom p)
    ((Algebra.ofId Sₚ (AdicCompletion pSₚ Sₚ)).restrictScalars Rₚ)

section

variable [IsNoetherianRing R] [Module.Finite R S]

private theorem localizedTensorProduct_to_completion_localizationAtPrime_bijective :
    Function.Bijective
      ((localizedTensorProduct_to_completion_localizationAtPrime p :
        Rₚ^ ⊗[Rₚ] Sₚ →ₐ[Rₚ] AdicCompletion pSₚ Sₚ) :
        Rₚ^ ⊗[Rₚ] Sₚ → AdicCompletion pSₚ Sₚ) := by
  sorry

noncomputable def localizedTensorProduct_algEquiv_completion_localizationAtPrime :
    Rₚ^ ⊗[Rₚ] Sₚ ≃ₐ[Rₚ] AdicCompletion pSₚ Sₚ :=
  AlgEquiv.ofBijective (localizedTensorProduct_to_completion_localizationAtPrime p)
    (localizedTensorProduct_to_completion_localizationAtPrime_bijective p)

/-- Lemma 10.97.8, first equality: the textbook tensor term `Rₚ^ ⊗[R] S` canonically identifies,
as a ring, with the completion of the semilocal localization `Sₚ`. This is the source-facing
first comparison `Rₚ^ ⊗[R] S = (Sₚ)^∧`, before passing to the product decomposition. -/
noncomputable def completion_tensorProductOverBase_ringEquiv_completion_localizationAtPrime :
    Rₚ^ ⊗[R] S ≃+* AdicCompletion pSₚ Sₚ :=
  ((completion_tensorProductOverBase_algEquiv_localizedTensorProduct p).toRingEquiv).trans
    (localizedTensorProduct_algEquiv_completion_localizationAtPrime p).toRingEquiv

end

-- The factor map from the semilocal localization `Sₚ` to the local ring at a prime `q` over `p`.
private lemma localizedFactorSubmonoid_le_primeCompl (q : p.asIdeal.primesOver S) :
    Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl ≤
      Submonoid.comap (RingHom.id S) q.1.primeCompl := by
  intro y hy
  have hy' : y ∈ Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl := hy
  rw [Submonoid.mem_comap]
  have hy'' : ∃ x ∉ p.asIdeal, algebraMap R S x = y := by
    simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hy'
  rcases hy'' with ⟨x, hx, rfl⟩
  have hxq : algebraMap R S x ∉ q.1 := by
    intro hmem
    have hqover : p.asIdeal = Ideal.comap (algebraMap R S) q.1 := Ideal.LiesOver.over
    have hxmem : x ∈ p.asIdeal := by
      simpa [hqover, Ideal.mem_comap] using hmem
    exact hx hxmem
  exact show (RingHom.id S) (algebraMap R S x) ∈ q.1.primeCompl by
    simpa using hxq

private noncomputable def localizedFactorRingHom (q : p.asIdeal.primesOver S) :
    Sₚ →+* Localization.AtPrime q.1 :=
  IsLocalization.map (Localization.AtPrime q.1) (RingHom.id S)
    (localizedFactorSubmonoid_le_primeCompl p q)

private lemma localizedFactorRingHom_comp (q : p.asIdeal.primesOver S) :
    (localizedFactorRingHom p q).comp (algebraMap Rₚ Sₚ) =
      Localization.localRingHom p.asIdeal q.1 (algebraMap R S) Ideal.LiesOver.over := by
  have hsub :
      p.asIdeal.primeCompl ≤
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl).comap (algebraMap R S) := by
    simpa [Algebra.algebraMapSubmonoid] using
      (Submonoid.le_comap_map p.asIdeal.primeCompl :
        p.asIdeal.primeCompl ≤
          (Submonoid.map (algebraMap R S) p.asIdeal.primeCompl).comap (algebraMap R S))
  have hmap :
      algebraMap Rₚ Sₚ =
        IsLocalization.map Sₚ (algebraMap R S) hsub := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [hmap]
  symm
  apply Localization.localRingHom_unique p.asIdeal q.1 (algebraMap R S) Ideal.LiesOver.over
  intro y
  have hcomp :
      (localizedFactorRingHom p q).comp (algebraMap S Sₚ) =
        (algebraMap S (Localization.AtPrime q.1)).comp (RingHom.id S) := by
    ext y
    simp [localizedFactorRingHom]
  have h :=
    congrArg (fun g : S →+* Localization.AtPrime q.1 ↦ g ((algebraMap R S) y))
      hcomp
  convert h using 1
  · simp [localizedFactorRingHom, RingHom.comp_apply]

private noncomputable def localizedFactorAlgHom (q : p.asIdeal.primesOver S) :
    Sₚ →ₐ[Rₚ] Localization.AtPrime q.1 :=
  { toRingHom := localizedFactorRingHom p q
    commutes' := by
      intro x
      simpa [RingHom.algebraMap_toAlgebra] using
        congrArg (fun g : Rₚ →+* Localization.AtPrime q.1 ↦ g x)
          (localizedFactorRingHom_comp p q) }

private lemma localizedFactorAlgHom_map_pSₚ_le (q : p.asIdeal.primesOver S) :
    Ideal.map (localizedFactorAlgHom p q).toRingHom pSₚ ≤ maximalIdeal (Localization.AtPrime q.1) := by
  have hcomp :
      (localizedFactorAlgHom p q).toRingHom.comp (algebraMap Rₚ Sₚ) =
        Localization.localRingHom p.asIdeal q.1 (algebraMap R S)
          Ideal.LiesOver.over :=
    localizedFactorRingHom_comp p q
  rw [show pSₚ = Ideal.map (algebraMap Rₚ Sₚ) mₚ by rfl, Ideal.map_map]
  rw [hcomp]
  simpa using IsLocalRing.map_maximalIdeal_le
    (Localization.localRingHom p.asIdeal q.1 (algebraMap R S)
      Ideal.LiesOver.over)

private lemma localizedFactorPow_le_comap (q : p.asIdeal.primesOver S) (n : ℕ) :
    pSₚ ^ n ≤ Ideal.comap (localizedFactorAlgHom p q).toRingHom
      (maximalIdeal (Localization.AtPrime q.1) ^ n) := by
  exact
    (Ideal.map_le_iff_le_comap).mp <| by
      simpa [Ideal.map_pow] using
        Ideal.pow_right_mono (localizedFactorAlgHom_map_pSₚ_le p q) n

private noncomputable def completionFactorAlgHom (q : p.asIdeal.primesOver S) :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  let quotientMap :
      (n : ℕ) →
        AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
          Localization.AtPrime q.1 ⧸ maximalIdeal (Localization.AtPrime q.1) ^ n :=
    fun n ↦
      (Ideal.quotientMapₐ _ (localizedFactorAlgHom p q)
        (localizedFactorPow_le_comap p q n)).comp
        ((AdicCompletion.evalₐ pSₚ n).restrictScalars Rₚ)
  let quotientMap_compatible :
      ∀ {m n : ℕ} (h : m ≤ n),
        (Ideal.Quotient.factorₐ Rₚ (Ideal.pow_le_pow_right h)).comp
          (quotientMap n) =
        quotientMap m := by
      intro m n h
      sorry
  AdicCompletion.liftAlgHom (maximalIdeal (Localization.AtPrime q.1))
    quotientMap quotientMap_compatible

variable (S) in
/-- The canonical comparison map from the completion of the semilocal localization `Sₚ` to the
product of the completed local rings indexed by the owner set `p.asIdeal.primesOver S`. -/
noncomputable def completion_localizationAtPrime_toPiLocalRingCompletion :
    AdicCompletion pSₚ Sₚ →ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  Pi.algHom Rₚ
    (fun q : p.asIdeal.primesOver S ↦
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1))
    (fun q ↦ completionFactorAlgHom p q)

section

variable [IsNoetherianRing R] [Module.Finite R S]

variable (S) in
/-- Lemma 10.97.8, product side: the canonical comparison map from the completed semilocal
localization `Sₚ` to the product of the completed local rings at the primes of `S` lying over `p`
is bijective. -/
theorem completion_localizationAtPrime_toPiLocalRingCompletion_bijective :
    Function.Bijective
      (completion_localizationAtPrime_toPiLocalRingCompletion S p :
        AdicCompletion pSₚ Sₚ →
          ∀ q : p.asIdeal.primesOver S,
            AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) := by
  sorry

variable (S) in
/-- Lemma 10.97.8: the completion of the semilocal localization `Sₚ` along the ideal induced by
`p` is canonically identified, as an `Rₚ`-algebra, with the product of the completed local rings
at the primes of `S` lying over `p`. This is the product-side companion used to obtain the direct
source-facing tensor decomposition below. -/
noncomputable def completion_localizationAtPrime_algEquiv_pi_localRingCompletion :
    AdicCompletion pSₚ Sₚ ≃ₐ[Rₚ]
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  AlgEquiv.ofBijective (completion_localizationAtPrime_toPiLocalRingCompletion S p)
    (completion_localizationAtPrime_toPiLocalRingCompletion_bijective S p)

variable (S) in
/-- Lemma 10.97.8: the completed tensor product `Rₚ^ ⊗[R] S` is canonically identified, as a
ring, with the product of the completed local rings `∏_{q | p} S_q^∧`, indexed by the canonical
owner set `p.asIdeal.primesOver S`. This is the direct source-facing composite of the two
textbook equalities `Rₚ^ ⊗[R] S = (Sₚ)^∧ = ∏_{q | p} S_q^∧`. -/
noncomputable def completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion :
    Rₚ^ ⊗[R] S ≃+*
      ∀ q : p.asIdeal.primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) :=
  (completion_tensorProductOverBase_ringEquiv_completion_localizationAtPrime p).trans
    (completion_localizationAtPrime_algEquiv_pi_localRingCompletion S p).toRingEquiv

end

end
