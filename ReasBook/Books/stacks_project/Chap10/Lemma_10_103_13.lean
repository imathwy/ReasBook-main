import Mathlib
import stacks_project.Chap10.Definition_10_103_12
import stacks_project.Chap10.Definition_10_157_1
import stacks_project.Chap10.Lemma_10_103_6
import stacks_project.Chap10.Lemma_10_40_6
import stacks_project.Chap10.Lemma_10_115_2
import stacks_project.Chap10.Lemma_10_112_7
import stacks_project.Chap10.Lemma_10_72_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module.LocallyCohenMacaulay

/-
Source/core/bridge triage:
* source-facing: local Cohen-Macaulayness of a finite module over a Noetherian ring;
* core/canonical: `Module.LocallyCohenMacaulay R M` from `Definition_10_103_12`;
* bridge/view: the polynomial-base-change closure theorem for that owner.

Primitive data are only the module `M` and the owner hypothesis
`Module.LocallyCohenMacaulay R M`. The primewise Cohen-Macaulay localizations of the polynomial
base change are derived API from the resulting owner instance, so the theorem should return
`Module.LocallyCohenMacaulay` directly instead of a parallel family of explicit equalities.
-/

/-- Helper for Lemma 10.103.13: on the polynomial-module model, a polynomial whose leading
coefficient is a unit has trivial kernel. -/
private theorem polynomialModule_eq_zero_of_smul_eq_zero_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (f : Polynomial A) (hf : IsUnit f.leadingCoeff) {g : PolynomialModule A N}
    (hfg : f • g = 0) : g = 0 := by
  by_contra hg
  classical
  let n : ℕ := g.support.max' (Finsupp.support_nonempty_iff.mpr hg)
  have hn_mem : n ∈ g.support := Finset.max'_mem _ _
  have hgn : g n ≠ 0 := Finsupp.mem_support_iff.mp hn_mem
  have htop :
      (f • g) (f.natDegree + n) = f.leadingCoeff • g n := by
    -- At the top index `natDegree f + n`, every antidiagonal summand but the leading one
    -- vanishes, either because the coefficient of `f` is above its degree or because the
    -- corresponding coefficient of `g` lies above the support maximum `n`.
    rw [PolynomialModule.smul_apply]
    calc
      ∑ a ∈ Finset.antidiagonal (f.natDegree + n), f.coeff a.1 • g a.2
          = ∑ a ∈ Finset.antidiagonal (f.natDegree + n),
              if a = (f.natDegree, n) then f.leadingCoeff • g n else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rcases a with ⟨i, j⟩
            by_cases hmain : (i, j) = (f.natDegree, n)
            · rcases Prod.mk.inj hmain with ⟨rfl, rfl⟩
              simp [Polynomial.coeff_natDegree]
            · have hij : i + j = f.natDegree + n := by
                simpa using (Finset.mem_antidiagonal.mp ha)
              have hterm_zero : f.coeff i • g j = 0 := by
                by_cases hi : i = f.natDegree
                · have hj : j = n := by
                    omega
                  exact False.elim (hmain (by simp [hi, hj]))
                · rcases lt_or_gt_of_ne hi with hi_lt | hi_gt
                  · have hj_gt : n < j := by
                      omega
                    have hgj : g j = 0 := by
                      by_contra hgj
                      have hj_mem : j ∈ g.support := Finsupp.mem_support_iff.mpr hgj
                      exact (not_lt_of_ge (Finset.le_max' _ _ hj_mem)) hj_gt
                    simp [hgj]
                  · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi_gt]
              simp [hmain, hterm_zero]
      _ = f.leadingCoeff • g n := by
          simp [Finset.mem_antidiagonal]
  have hzero : f.leadingCoeff • g n = 0 := by
    simpa [hfg] using htop.symm
  exact hgn ((hf.smul_eq_zero).1 hzero)

/-- Helper for Lemma 10.103.13: transporting the polynomial-module comparison shows that a
polynomial with unit leading coefficient is a nonzerodivisor on the polynomial tensor module. -/
private theorem polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (f : Polynomial A) (hf : IsUnit f.leadingCoeff) :
    IsSMulRegular ((Polynomial A) ⊗[A] N) f := by
  let e := PolynomialModule.polynomialTensorProductLEquivPolynomialModule A N
  have hreg : IsSMulRegular (PolynomialModule A N) f := by
    intro x y hxy
    have hzero : f • (x - y) = 0 := by
      simpa [smul_sub, hxy]
    exact sub_eq_zero.mp <|
      polynomialModule_eq_zero_of_smul_eq_zero_of_isUnit_leadingCoeff (N := N) f hf hzero
  -- The tensor-product model and the polynomial-module model carry the same `A[X]`-action.
  exact (LinearEquiv.isSMulRegular_congr e f).2 hreg

/-- Helper for Lemma 10.103.13: Cohen-Macaulayness is unchanged by an `R`-linear equivalence over
the same local Noetherian ring. -/
private theorem cohenMacaulay_of_linearEquiv [IsLocalRing R]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') [h : Module.CohenMacaulay R N] : Module.CohenMacaulay R N' := by
  let _ : Module.Finite R N' := Module.Finite.equiv e
  -- Transport both invariants appearing in the owner definition across the linear equivalence.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e, h.supportDim_eq_moduleDepth]⟩

/-- Helper for Lemma 10.103.13: local Cohen-Macaulayness is unchanged by an `R`-linear
equivalence over the same Noetherian ring. -/
private theorem locallyCohenMacaulay_of_linearEquiv
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') [h : Module.LocallyCohenMacaulay R N] :
    Module.LocallyCohenMacaulay R N' := by
  let _ : Module.Finite R N' := Module.Finite.equiv e
  refine ⟨fun p ↦ ?_⟩
  let ep : LocalizedModule.AtPrime p.asIdeal N ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal N' :=
    LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
  -- Localize the linear equivalence and reuse the localized Cohen-Macaulay owner.
  let _ :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
    h.localizedModule_cohenMacaulay p
  exact cohenMacaulay_of_linearEquiv ep

/-- Helper for Lemma 10.103.13: over a Noetherian local ring, a finite module with
zero-dimensional support is already Cohen-Macaulay. -/
private theorem cohen_macaulay_of_supportDim_zero_local
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdim : Module.supportDim A N = 0) : Module.CohenMacaulay A N := by
  refine Module.CohenMacaulay.mk ?_
  let _ : Nontrivial N := by
    simp [← Module.supportDim_ne_bot_iff_nontrivial A, hdim]
  have hdepth_le : WithBot.some (moduleDepth A N : ℕ∞) ≤ 0 := by
    -- In dimension zero the standard depth bound forces the depth to be zero as well.
    rw [← hdim]
    exact depth_le_supportDim
  have hdepth_eq : moduleDepth A N = 0 := by
    simpa using hdepth_le
  -- With both invariants equal to zero, the owner equality is immediate.
  simpa [hdepth_eq] using hdim

/-- Helper for Lemma 10.103.13: after adjoining one variable to `A`, tensoring `M` directly over
`R` agrees with first base-changing `M` to `A` and then extending scalars from `A` to
`A[X]`. -/
private noncomputable def polynomial_tensor_baseChange_linearEquiv
    {A : Type*} [CommRing A] [Algebra R A] :
    ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
      ((Polynomial A) ⊗[A] (A ⊗[R] M)) := by
  -- Insert the redundant `A`-tensor factor and then reassociate so the one-variable theorem can
  -- be applied to the already base-changed module `A ⊗[R] M`.
  let eInsert :
      ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
        (((Polynomial A) ⊗[A] A) ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.congr
      (Algebra.TensorProduct.rid A (Polynomial A) (Polynomial A)).symm.toLinearEquiv
      (LinearEquiv.refl R M)
  let eAssoc :
      (((Polynomial A) ⊗[A] A) ⊗[R] M) ≃ₗ[Polynomial A]
        ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
    TensorProduct.AlgebraTensorModule.assoc R A (Polynomial A) (Polynomial A) A M
  exact eInsert.trans eAssoc

/-- Helper for Lemma 10.103.13: an `R`-algebra equivalence identifies the prime complements of
corresponding prime ideals. -/
private theorem primeCompl_map_eq_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Submonoid.map e.toMulEquiv (PrimeSpectrum.comap e.toRingHom q).asIdeal.primeCompl =
      q.asIdeal.primeCompl := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Re-express membership in the contracted prime so the image element can be read in `q`.
    simpa [PrimeSpectrum.comap_asIdeal] using ha
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    -- Pulling `b` back along `e` lands outside the contracted prime for the same reason.
    simpa [PrimeSpectrum.comap_asIdeal] using hb

/-- Helper for Lemma 10.103.13: localizing corresponding prime ideals along an `R`-algebra
equivalence gives an `R`-algebra equivalence of the local rings. -/
private noncomputable def localizationAtPrime_algEquiv_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  -- This is the ring-side transport required by the source-local comparison at each prime.
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

/-- Helper for Lemma 10.103.13: after localizing corresponding prime ideals along an `R`-algebra
equivalence, the localized tensor modules agree over the localized source ring. -/
private noncomputable def localized_tensor_linearEquiv_of_algEquiv_atPrime
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    let p := PrimeSpectrum.comap e.toRingHom q
    let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
    let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      eLoc.toRingHom.toAlgebra
    let _ :
        Module (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
      Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
    LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) := by
  let p := PrimeSpectrum.comap e.toRingHom q
  let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    eLoc.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algHom eLoc.toAlgHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[R] M) :=
    Module.compHom (Localization.AtPrime q.asIdeal ⊗[R] M) eLoc.toRingHom
  let eLocLinear :
      Localization.AtPrime p.asIdeal ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal :=
    { __ := eLoc.toAddEquiv
      map_smul' := fun a x ↦ by
        -- On the codomain, the `Localization.AtPrime p.asIdeal`-action is induced by `eLoc`.
        simpa [Algebra.smul_def] using eLoc.map_mul a x }
  -- Rewrite both localizations as literal tensor base changes over `R`.
  let eLeft :
      LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime p.asIdeal ⊗[R] M :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (A ⊗[R] M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R A (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) M)
  let eMid :
      Localization.AtPrime p.asIdeal ⊗[R] M ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.congr eLocLinear (LinearEquiv.refl R M)
  let eRightB :
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) ≃ₗ[Localization.AtPrime q.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl (B ⊗[R] M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R B (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) M)
  let eRight :
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    { __ := eRightB.toAddEquiv
      map_smul' := fun a x ↦ by
        -- The q-side comparison is `B_q`-linear, hence also `A_p`-linear after restricting
        -- scalars along `eLoc`.
        change
          eRightB ((algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) a) • x) =
            (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal) a) • eRightB x
        exact
          eRightB.map_smul (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) a) x }
  -- The middle `TensorProduct.congr` is the only nontrivial transport; the outer equivalences are
  -- the canonical localized-module-to-tensor-product comparisons.
  exact eLeft.trans <| eMid.trans eRight.symm

/-- Helper for Lemma 10.103.13: an `R`-algebra equivalence between scalar-extension rings should
transport local Cohen-Macaulayness of the corresponding tensor-base-changed module. -/
private theorem locallyCohenMacaulay_tensor_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] [IsNoetherianRing A]
    {B : Type*} [CommRing B] [Algebra R B] [IsNoetherianRing B]
    (e : A ≃ₐ[R] B) (h : Module.LocallyCohenMacaulay A (A ⊗[R] M)) :
    Module.LocallyCohenMacaulay B (B ⊗[R] M) := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algHom e.toAlgHom
  let eBaseChange :
      (B ⊗[R] M) ≃ₗ[B] (B ⊗[A] (A ⊗[R] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).symm
  let _ : Module.Finite B (B ⊗[A] (A ⊗[R] M)) := inferInstance
  let _ : Module.Finite B (B ⊗[R] M) := Module.Finite.equiv eBaseChange.symm
  refine ⟨fun q ↦ ?_⟩
  let p := PrimeSpectrum.comap e.toRingHom q
  let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    eLoc.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algHom eLoc.toAlgHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
  let _ :
      IsScalarTower (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M))
  let eqv :
      LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) :=
    localized_tensor_linearEquiv_of_algEquiv_atPrime (R := R) (M := M) e q
  let _ :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M)) :=
    h.localizedModule_cohenMacaulay p
  have hrestrict :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) := by
    -- First move the localized owner across the canonical localized tensor comparison.
    exact cohenMacaulay_of_linearEquiv eqv
  have hsurj :
      Function.Surjective
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- The localized algebra equivalence identifies the target local ring with a quotient-free copy
    -- of the source one, so the induced local map is surjective.
    simpa using eLoc.surjective
  -- Then upgrade from the restricted `A_p`-module view back to the genuine `B_q`-module owner.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := Localization.AtPrime p.asIdeal)
      (S := Localization.AtPrime q.asIdeal)
      (N := LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M))
      hsurj).2 hrestrict

/-- Helper for Lemma 10.103.13: localizing the one-variable scalar extension at a maximal ideal
identifies it with tensoring the localized coefficient ring with the localized source module. -/
private noncomputable def localized_polynomial_tensor_equiv_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm]
      Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  let eLocalized :
      LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm]
        Sm ⊗[Polynomial A] ((Polynomial A) ⊗[A] N) :=
    -- First rewrite localization at `m` as tensoring with the local ring `Sm`.
    LocalizedModule.equivTensorProduct m.asIdeal.primeCompl ((Polynomial A) ⊗[A] N)
  let eCancelPolynomial :
      Sm ⊗[Polynomial A] ((Polynomial A) ⊗[A] N) ≃ₗ[Sm] Sm ⊗[A] N :=
    -- Cancel the intermediate polynomial-ring base change.
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (Polynomial A) Sm Sm N
  let eInsertLocalization :
      Sm ⊗[A] N ≃ₗ[Sm] Sm ⊗[Ap] (Ap ⊗[A] N) :=
    -- Reinsert the coefficient localization so the source module appears as `N_p`.
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap Sm Sm N).symm
  let eLocalizedSource :
      Sm ⊗[Ap] (Ap ⊗[A] N) ≃ₗ[Sm] Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Sm Sm)
      (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N).symm
  exact eLocalized.trans <| eCancelPolynomial.trans <| eInsertLocalization.trans eLocalizedSource

/-- Helper for Lemma 10.103.13: the closed fiber of the local map `A_p → A[X]_m` has Krull
dimension `1`. -/
private theorem ringKrullDim_closedFiber_polynomial_atMaximal_eq_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) = 1 := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  have hformula :
      ringKrullDim Sm =
        ringKrullDim Ap + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
    -- The quotient form of Lemma `10.112.7` expresses the local dimension by base plus fiber.
    simpa [p, Ap, Sm] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
        (R := A) (S := Polynomial A) m.toPrimeSpectrum
  have hSm :
      ringKrullDim Sm = p.asIdeal.height + 1 := by
    -- Identify `dim(Sm)` with the height of `m`, then use the polynomial height jump formula.
    calc
      ringKrullDim Sm = m.asIdeal.height := by
        simpa [Sm] using (IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal Sm)
      _ = p.asIdeal.height + 1 := by
        simpa [p] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞))
            (Polynomial.height_eq_height_add_one (p := p.asIdeal) (P := m.asIdeal))
  have hAp : ringKrullDim Ap = p.asIdeal.height := by
    -- The contracted base localization has dimension equal to the height of `p`.
    simpa [Ap] using (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Ap)
  have hfiber :
      ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) = 1 := by
    let d : ℕ := p.asIdeal.height.toNat
    have hd : (d : WithBot ℕ∞) = p.asIdeal.height := by
      have hneTop : p.asIdeal.height ≠ ⊤ := ne_of_lt (Ideal.height_lt_top Ideal.IsPrime.ne_top')
      simpa [d] using
        (congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm).symm
    have hformula' :
        p.asIdeal.height + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
          p.asIdeal.height + 1 := by
      calc
        p.asIdeal.height + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
            ringKrullDim Ap + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
              rw [hAp]
        _ = ringKrullDim Sm := hformula.symm
        _ = p.asIdeal.height + 1 := hSm
    have hformula'' :
        (d : WithBot ℕ∞) + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
          d + 1 := by
      simpa [hd] using hformula'
    exact (ENat.WithBot.natCast_add_cancel (a := ringKrullDim
      (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal)) (b := (1 : WithBot ℕ∞)) (c := d)).1
      hformula''
  have hmap :
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
        Ideal.map (algebraMap A Sm) p.asIdeal := by
    -- The maximal ideal of `Ap` is exactly the extension of `p`, so the two fiber ideals agree.
    calc
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
          Ideal.map (algebraMap Ap Sm) (Ideal.map (algebraMap A Ap) p.asIdeal) := by
            rw [Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      _ = Ideal.map ((algebraMap Ap Sm).comp (algebraMap A Ap)) p.asIdeal := by
            rw [Ideal.map_map]
      _ = Ideal.map (algebraMap A Sm) p.asIdeal := by
            simp [IsScalarTower.algebraMap_eq A Ap Sm]
  simpa [p, Ap, Sm] using
    calc
      ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) =
          ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
            rw [hmap]
      _ = 1 := hfiber

/-- Helper for Lemma 10.103.13: once the source quotient over `A_p` has zero-dimensional support,
its tensor base change to `A[X]_m` has support dimension `1`. -/
private theorem supportDim_tensor_of_zeroDim_local_eq_one_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A))
    {Q0 : Type*} [AddCommGroup Q0]
    [Module (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal) Q0]
    [Module.Finite (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal)
      Q0]
    (hQ0 :
      Module.supportDim
          (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal)
          Q0 = 0) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    Module.supportDim Sm (Sm ⊗[Ap] Q0) = 1 := by
  -- TODO for Lemma 10.103.13: use Lemma `10.40.6` to rewrite the support of `Sm ⊗[Ap] Q0` as
  -- the inverse image of the closed point of `Spec(A_p)`, identify that inverse image with the
  -- zero locus of the extended maximal ideal, and invoke the previous closed-fiber-dimension
  -- helper.
  sorry

-- Proof sketch: the source argument first proves the one-variable statement over `A[X]` for an
-- arbitrary locally Cohen-Macaulay `A`-module, and only afterward iterates it through the
-- last-variable identification for `MvPolynomial`.
/-- Helper for Lemma 10.103.13: the source-faithful one-variable step for polynomial scalar
extension. -/
private theorem polynomial
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) :
    Module.LocallyCohenMacaulay (Polynomial A) ((Polynomial A) ⊗[A] N) := by
  -- TODO for Lemma 10.103.13: localize at a maximal ideal of `A[X]`, pull back a maximal
  -- regular sequence from `A_p`, identify the closed-fiber quotient support as one-dimensional,
  -- choose a polynomial with unit leading coefficient, and finish with
  -- `polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff`.
  sorry

-- Proof sketch: argue by induction on the number of variables, reducing from
-- `MvPolynomial (Fin (n + 1)) R` to a one-variable polynomial extension over
-- `MvPolynomial (Fin n) R`. For the one-variable step, localize at a prime of `A[X]`, pull back a
-- maximal regular sequence from `A_p`, identify the quotient support in the closed fiber, and use
-- `polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff` for the final nonzerodivisor step.
/-- Lemma 10.103.13: if `M` is a locally Cohen-Macaulay module over a Noetherian ring `R`, then
its scalar extension to `R[x₁, …, xₙ]`, represented canonically by
`MvPolynomial (Fin n) R ⊗[R] M`, is again locally Cohen-Macaulay. -/
theorem mvPolynomial (hCM : Module.LocallyCohenMacaulay R M) (n : ℕ) :
    Module.LocallyCohenMacaulay (MvPolynomial (Fin n) R) ((MvPolynomial (Fin n) R) ⊗[R] M) := by
  -- Route correction: the source proof is local and one-variable at each step, so the remaining
  -- blocker is now isolated into the named one-variable theorem and the algebra-equivalence
  -- transport between successive polynomial presentations.
  induction n with
  | zero =>
      let e₀ : R ≃ₐ[R] MvPolynomial (Fin 0) R := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
      -- First rewrite `M` as `R ⊗[R] M`, then transport that local Cohen-Macaulay owner across
      -- the zero-variable algebra equivalence.
      let hTensor : Module.LocallyCohenMacaulay R (R ⊗[R] M) := by
        let _ : Module.LocallyCohenMacaulay R M := hCM
        exact locallyCohenMacaulay_of_linearEquiv
          (((TensorProduct.comm R R M).trans (TensorProduct.rid R M)).symm)
      exact locallyCohenMacaulay_tensor_of_algEquiv (R := R) (M := M) e₀ hTensor
  | succ n ih =>
      let A := MvPolynomial (Fin n) R
      let eLast : Polynomial A ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
        (noetherNormalizationLastVariableEquiv (R := R) (n := n)).symm
      let eAssoc :
          ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
            ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
        polynomial_tensor_baseChange_linearEquiv (R := R) (M := M) (A := A)
      -- Apply the one-variable theorem over the `n`-variable coefficient ring and then undo the
      -- canonical reassociation of the tensor module.
      let hPolyAssoc :
          Module.LocallyCohenMacaulay (Polynomial A)
            ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
        polynomial (A := A) (N := A ⊗[R] M) ih
      let hPoly :
          Module.LocallyCohenMacaulay (Polynomial A) ((Polynomial A) ⊗[R] M) := by
        let _ :
            Module.LocallyCohenMacaulay (Polynomial A)
              ((Polynomial A) ⊗[A] (A ⊗[R] M)) := hPolyAssoc
        exact locallyCohenMacaulay_of_linearEquiv (R := Polynomial A) eAssoc.symm
      -- Transport the polynomial-ring statement back to the canonical `MvPolynomial` presentation
      -- of the next stage.
      exact locallyCohenMacaulay_tensor_of_algEquiv (R := R) (M := M) eLast hPoly

end Module.LocallyCohenMacaulay

end
