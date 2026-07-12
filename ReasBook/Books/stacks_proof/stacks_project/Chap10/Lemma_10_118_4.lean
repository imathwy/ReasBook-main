import StacksProject_2024.Chap10.«10_118_3_2»
import StacksProject_2024.Chap10.Lemma_10_5_3
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum GenericFlatness

/-
Domain-style sampling:
* primary domain: generic flatness on `Spec R`, with the short exact sequence treated through the
  chapter's canonical owner `ShortComplex (ModuleCat S)`.
* inspected owner declarations:
  `GenericFlatness.goodLocus`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂`,
  `Module.FinitePresentation.of_exact`,
  `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`.
* best owner abstraction: a short exact complex `T : ShortComplex (ModuleCat S)`.
* layer triage: the short exact complex is `core/canonical`; the textbook inclusion of good loci
  remains `source-facing`.
* primitive data: `T` and `hT : T.ShortExact`.
* derived API: the inclusion
  `goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂`.
-/

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {T : ShortComplex (ModuleCat.{max u v} S)}

/-- Helper for Lemma 10.118.4: in an exact sequence of modules over a commutative ring, if the
outer terms are free, then the middle term is free. -/
lemma free_middle_of_exact_of_free_ends
    {A : Type*} [CommRing A]
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.Free A M₁] [Module.Free A M₃] :
    Module.Free A M₂ := by
  -- Split the surjection using projectivity of the free quotient.
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  -- Then identify the middle term with the product of the two free endpoint modules.
  obtain ⟨e, _, _⟩ := ((hfg.split_tfae hf hg).out 0 2 rfl rfl).mp ⟨s, hs⟩
  exact Module.Free.of_equiv' inferInstance e.symm

/-- Helper for Lemma 10.118.4: `R_(fg)` carries the canonical `R_f`-algebra structure. -/
noncomputable instance product_away_algebra_over_left (f g : R) :
    Algebra (Localization.Away f) (Localization.Away (f * g)) :=
  (IsLocalization.Away.awayToAwayRight (S := Localization.Away f) f g).toAlgebra

/-- Helper for Lemma 10.118.4: `S_(fg)` carries the canonical `S_f`-algebra structure. -/
noncomputable instance target_product_away_algebra_over_left (f g : R) :
    Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S (f * g))) :=
  by
    -- The target localization is still away from the product image `(fg)`, hence away from
    -- `(algebraMap R S f) * (algebraMap R S g)` after rewriting `map_mul`.
    have : IsLocalization.Away ((algebraMap R S f) * (algebraMap R S g))
        (Localization.Away (algebraMap R S (f * g))) := by
      simpa [map_mul] using
        (inferInstance :
          IsLocalization.Away (algebraMap R S (f * g))
            (Localization.Away (algebraMap R S (f * g))))
    exact (IsLocalization.Away.awayToAwayRight (S := Localization.Away (algebraMap R S f))
      (algebraMap R S f) (algebraMap R S g)).toAlgebra

/-- Helper for Lemma 10.118.4: after localizing away from `f`, multiplying the second parameter by
`f` only changes it by an associate. -/
lemma away_mul_associated_right (f g : R) :
    Associated (algebraMap R (Localization.Away f) (f * g))
      (algebraMap R (Localization.Away f) g) := by
  -- Rewrite `(fg) / 1` as `(f / 1) * (g / 1)` and cancel the unit `f / 1`.
  rw [map_mul]
  simpa [mul_comm] using
    (associated_mul_unit_left
      (algebraMap R (Localization.Away f) g)
      (algebraMap R (Localization.Away f) f)
      (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f)))

/-- Helper for Chap10 Lemma 10 118 4: scalar multiplication units remain units after restricting
scalars along an algebra map. -/
lemma isUnitRestrictScalarsAlgebraMapEnd
    {A : Type*} {B : Type*} {P : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (a : A)
    (h : IsUnit (algebraMap B (Module.End B P) (algebraMap A B a))) :
    IsUnit (algebraMap A (Module.End A P) a) := by
  -- Reduce unithood of scalar endomorphisms to bijectivity and identify the two scalar actions.
  rw [Module.End.isUnit_iff] at h ⊢
  convert h using 1
  ext x
  exact (algebraMap_smul B a x).symm

/-- Helper for Chap10 Lemma 10 118 4: localizing a module away from an algebra-map image remains
a localization after restricting scalars. -/
lemma isLocalizedModuleRestrictScalarsPowersAlgebraMap
    {A : Type*} {B : Type*} {N : Type*} {N' : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [AddCommGroup N'] [Module B N'] [Module A N'] [IsScalarTower A B N']
    (t : A) (f : N →ₗ[B] N')
    [IsLocalizedModule (Submonoid.powers (algebraMap A B t)) f] :
    IsLocalizedModule (Submonoid.powers t) (f.restrictScalars A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    -- Map the denominator power from `A` to the corresponding power in `B`.
    rcases (Submonoid.mem_powers_iff s.1 t).mp s.2 with ⟨n, hn⟩
    apply isUnitRestrictScalarsAlgebraMapEnd (A := A) (B := B) (P := N') (a := s.1)
    have hsB : algebraMap A B s.1 ∈ Submonoid.powers (algebraMap A B t) := by
      rw [← hn, map_pow]
      exact Submonoid.pow_mem (Submonoid.powers (algebraMap A B t))
        (Submonoid.mem_powers (algebraMap A B t)) n
    exact IsLocalizedModule.map_units f ⟨algebraMap A B s.1, hsB⟩
  · intro y
    -- Lift the localized-module surjectivity witness back to the matching power of `t`.
    obtain ⟨⟨x, sB⟩, hsB_y⟩ :=
      IsLocalizedModule.surj (Submonoid.powers (algebraMap A B t)) f y
    rcases (Submonoid.mem_powers_iff sB.1 (algebraMap A B t)).mp sB.2 with ⟨n, hn⟩
    let sA : Submonoid.powers t :=
      ⟨t ^ n, Submonoid.pow_mem (Submonoid.powers t) (Submonoid.mem_powers t) n⟩
    refine ⟨⟨x, sA⟩, ?_⟩
    have hsval : algebraMap A B sA.1 = sB.1 := by
      simp [sA, hn, map_pow]
    calc
      sA • y = (algebraMap A B sA.1) • y := by
        simp [Submonoid.smul_def]
      _ = sB • y := by
        rw [hsval]
        simp [Submonoid.smul_def]
      _ = f x := hsB_y
  · intro x₁ x₂ h
    -- The equality criterion is transported by choosing the same exponent in the source ring.
    obtain ⟨cB, hcB⟩ :=
      IsLocalizedModule.exists_of_eq (S := Submonoid.powers (algebraMap A B t)) (f := f) h
    rcases (Submonoid.mem_powers_iff cB.1 (algebraMap A B t)).mp cB.2 with ⟨n, hn⟩
    let cA : Submonoid.powers t :=
      ⟨t ^ n, Submonoid.pow_mem (Submonoid.powers t) (Submonoid.mem_powers t) n⟩
    refine ⟨cA, ?_⟩
    have hcval : algebraMap A B cA.1 = cB.1 := by
      simp [cA, hn, map_pow]
    calc
      cA • x₁ = (algebraMap A B cA.1) • x₁ := by
        simp [Submonoid.smul_def]
      _ = cB • x₁ := by
        rw [hcval]
        simp [Submonoid.smul_def]
      _ = cB • x₂ := hcB
      _ = (algebraMap A B cA.1) • x₂ := by
        rw [hcval]
        simp [Submonoid.smul_def]
      _ = cA • x₂ := by
        simp [Submonoid.smul_def]

/-- Helper for Chap10 Lemma 10 118 4: finite presentation of an algebra survives away
localization on both sides. -/
lemma awayAlgebraFinitePresentationOverBase
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] (t : A) :
    Algebra.FinitePresentation (Localization.Away t) (Localization.Away (algebraMap A B t)) := by
  -- View the target as finitely presented over `A`, then descend the base to `A_t`.
  letI : IsScalarTower A (Localization.Away t) (Localization.Away (algebraMap A B t)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  haveI : Algebra.FinitePresentation A (Localization.Away (algebraMap A B t)) := by
    infer_instance
  haveI : Algebra.FiniteType A (Localization.Away t) :=
    Algebra.FiniteType.of_finitePresentation
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A
    (Localization.Away t) (Localization.Away (algebraMap A B t))

/-- Helper for Chap10 Lemma 10 118 4: finite presentation of a module survives away
localization. -/
lemma awayModuleFinitePresentation
    {A : Type*} {M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (t : A) :
    Module.FinitePresentation (Localization.Away t) (LocalizedModule.Away t M) := by
  -- This isolates the localized-module finite-presentation instance from the larger condition.
  infer_instance

/-- Helper for Chap10 Lemma 10 118 4: finite presentation of algebras is invariant under
compatible equivalences of both the base ring and the target algebra. -/
lemma algebraFinitePresentationOfRingEquiv
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    [Algebra.FinitePresentation A B] :
    Algebra.FinitePresentation A' B' := by
  -- First view the target algebra as an `A`-algebra through the base equivalence.
  letI : Algebra A A' := eA.toRingHom.toAlgebra
  letI : Algebra A B' := Algebra.compHom B' eA.toRingHom
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfpBase : Algebra.FinitePresentation A A' := by
    -- The base change ring is finitely presented over `A` because it is equivalent to `A`.
    let eAlg : A ≃ₐ[A] A' := AlgEquiv.ofRingEquiv (R := A) (f := eA) (by intro; rfl)
    exact Algebra.FinitePresentation.equiv eAlg
  have hfpTargetOverA : Algebra.FinitePresentation A B' := by
    -- Transport finite presentation of the localized algebra through the compatible equivalence.
    let eAlg : B ≃ₐ[A] B' := AlgEquiv.ofRingEquiv (R := A) (f := eB) hcompat
    exact Algebra.FinitePresentation.equiv eAlg
  haveI : Algebra.FinitePresentation A B' := hfpTargetOverA
  haveI : Algebra.FiniteType A A' := Algebra.FiniteType.of_finitePresentation
  -- Descend from the restricted `A`-presentation to the desired `A'`-presentation.
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'

/-- Helper for Chap10 Lemma 10 118 4: finite presentation of modules is invariant under a
semilinear equivalence whose scalar homomorphism is a ring equivalence. -/
lemma moduleFinitePresentationOfSemilinearEquiv
    {A A' N N' : Type*} [Ring A] [Ring A'] [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A' N'] {σ : A →+* A'} {σ' : A' →+* A}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : N ≃ₛₗ[σ] N') [Module.FinitePresentation A N] :
    Module.FinitePresentation A' N' := by
  classical
  obtain ⟨s, hs_span, hs_ker⟩ := Module.FinitePresentation.out (R := A) (M := N)
  let eA : A ≃+* A' := RingHomInvPair.toRingEquiv σ σ'
  let eFree : (s →₀ A) ≃ₛₗ[σ] (s →₀ A') :=
    Finsupp.mapRange.linearEquiv eA.toSemilinearEquiv
  let lA : (s →₀ A) →ₗ[A] N := Finsupp.linearCombination A ((↑) : s → N)
  let lA' : (s →₀ A') →ₗ[A'] N' :=
    Finsupp.linearCombination A' (fun x : s ↦ e x.1)
  have hcomp (x : s →₀ A) : lA' (eFree x) = e (lA x) := by
    -- The free presentation map is carried coefficientwise by the scalar equivalence.
    have hsum : x.sum (fun a b ↦ eA.toSemilinearEquiv b • e ↑a) =
        x.sum (fun a b ↦ σ b • e ↑a) := by
      apply Finsupp.sum_congr
      intro _ _
      rfl
    simpa [lA, lA', eFree, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index, map_finsuppSum, map_smulₛₗ] using hsum
  have hsurjA : Function.Surjective lA := by
    -- The original finite-presentation generators give a surjective free presentation.
    rw [← LinearMap.range_eq_top]
    simpa [lA, Finsupp.range_linearCombination] using hs_span
  have hsurjA' : Function.Surjective lA' := by
    -- Transport every preimage through the semilinear equivalence of free modules.
    intro y
    obtain ⟨x, hx⟩ := hsurjA (e.symm y)
    refine ⟨eFree x, ?_⟩
    calc
      lA' (eFree x) = e (lA x) := hcomp x
      _ = e (e.symm y) := by rw [hx]
      _ = y := e.apply_symm_apply y
  have hkerA : (LinearMap.ker lA).FG := by
    simpa [lA] using hs_ker
  refine Module.finitePresentation_of_surjective lA' hsurjA' ?_
  have hker_eq :
      LinearMap.ker lA' =
        (LinearMap.ker lA).map (eFree : (s →₀ A) →ₛₗ[σ] (s →₀ A')) := by
    -- The kernel is exactly the image of the original kernel under the free semilinear map.
    ext x
    constructor
    · intro hx
      refine ⟨eFree.symm x, ?_, ?_⟩
      · have hx0 : lA' x = 0 := by simpa [LinearMap.mem_ker] using hx
        have hx1 : lA' (eFree (eFree.symm x)) = 0 := by simpa using hx0
        have hx2 : e (lA (eFree.symm x)) = 0 := by
          rw [← hcomp (eFree.symm x)]
          exact hx1
        exact e.map_eq_zero_iff.mp hx2
      · exact eFree.apply_symm_apply x
    · rintro ⟨y, hy, rfl⟩
      have hy0 : lA y = 0 := by simpa [LinearMap.mem_ker] using hy
      rw [LinearMap.mem_ker]
      exact (hcomp y).trans (by simp [hy0])
  simpa [hker_eq] using hkerA.map (eFree : (s →₀ A) →ₛₗ[σ] (s →₀ A'))

/-- Helper for Chap10 Lemma 10 118 4: finite presentation transports across a ring equivalence
when the target module structure is pulled back along the inverse equivalence. -/
private theorem moduleFinitePresentationOfRingEquivCompHom
    {A A' N : Type*} [Ring A] [Ring A'] [AddCommGroup N] [Module A N]
    (eA : A ≃+* A') (hfp : Module.FinitePresentation A N) :
    letI : Module A' N := Module.compHom N (eA.symm : A' →+* A)
    Module.FinitePresentation A' N := by
  -- The identity map is semilinear because the `A'`-action is defined by pulling scalars back
  -- through `eA.symm`.
  letI : Module A' N := Module.compHom N (eA.symm : A' →+* A)
  letI : RingHomInvPair (eA : A →+* A') (eA.symm : A' →+* A) :=
    RingHomInvPair.of_ringEquiv eA
  letI : RingHomInvPair (eA.symm : A' →+* A) (eA : A →+* A') :=
    RingHomInvPair.symm (eA : A →+* A') (eA.symm : A' →+* A)
  let idSemi : N ≃ₛₗ[(eA : A →+* A')] N :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a n ↦ by
        change a • n = eA.symm (eA a) • n
        rw [eA.symm_apply_apply] }
  letI : Module.FinitePresentation A N := hfp
  exact moduleFinitePresentationOfSemilinearEquiv idSemi

/-- Helper for Chap10 Lemma 10 118 4: finite presentation transports across a linear
equivalence, with the source finite-presentation proof passed explicitly. -/
private theorem moduleFinitePresentationOfLinearEquivExplicit
    {A N N' : Type*} [Ring A] [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (hfp : Module.FinitePresentation A N) :
    Module.FinitePresentation A N' := by
  -- Keep instance search out of the main proof by installing the source proof only locally.
  letI : Module.FinitePresentation A N := hfp
  exact Module.FinitePresentation.of_equiv e

/-- Helper for Chap10 Lemma 10 118 4: after extending scalars from a localization, a linear
equivalence still transports finite presentation. -/
private theorem moduleFinitePresentationOfExtendedLocalizedEquiv
    {A Aₛ N N' : Type*} [CommRing A] (T : Submonoid A)
    [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization T Aₛ]
    [AddCommGroup N] [Module A N] [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module Aₛ N'] [IsScalarTower A Aₛ N']
    (e : N ≃ₗ[A] N') (hfp : Module.FinitePresentation Aₛ N) :
    Module.FinitePresentation Aₛ N' := by
  -- Extend the equivalence to the localized scalar ring in a separate declaration budget.
  exact moduleFinitePresentationOfLinearEquivExplicit
    (e.extendScalarsOfIsLocalization T Aₛ) hfp

/-- Helper for Chap10 Lemma 10 118 4: under compatible ring equivalences, the pulled-back
target-ring action on the source agrees with the original base action. -/
private theorem source_smul_of_compatibleRingEquivCompHom
    {A A' B B' N : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a)) :
    letI : Module B' N := Module.compHom N (eB.symm : B' →+* B)
    ∀ (a : A) (n : N), algebraMap A' B' (eA a) • n = a • n := by
  -- Pull the scalar in `B'` back to `B`, then use the original scalar tower on `N`.
  letI : Module B' N := Module.compHom N (eB.symm : B' →+* B)
  intro a n
  change eB.symm (algebraMap A' B' (eA a)) • n = a • n
  have hs : eB.symm (algebraMap A' B' (eA a)) = algebraMap A B a := by
    apply eB.injective
    rw [eB.apply_symm_apply, hcompat a]
  rw [hs]
  exact IsScalarTower.algebraMap_smul B a n

/-- Helper for Chap10 Lemma 10 118 4: freeness transports through a localized linear equivalence
when source and target base scalar actions are compatible with a base-ring equivalence. -/
private theorem moduleFreeOfExtendedLocalizedEquiv
    {C B' A A' N N' : Type*} [CommRing C] (T : Submonoid C)
    [CommRing B'] [Algebra C B'] [IsLocalization T B']
    [CommRing A] [CommRing A'] [Algebra A' B']
    [AddCommGroup N] [Module C N] [Module B' N] [IsScalarTower C B' N] [Module A N]
    [AddCommGroup N'] [Module C N'] [Module B' N'] [IsScalarTower C B' N'] [Module A' N']
    [IsScalarTower A' B' N']
    (eA : A ≃+* A') (e : N ≃ₗ[C] N')
    (hsource : ∀ (a : A) (n : N), algebraMap A' B' (eA a) • n = a • n)
    (hfree : Module.Free A N) :
    Module.Free A' N' := by
  -- Extend the comparison to the localized target ring, then reinterpret it as semilinear over
  -- the base-ring equivalence.
  letI : RingHomInvPair (eA : A →+* A') (eA.symm : A' →+* A) :=
    RingHomInvPair.of_ringEquiv eA
  letI : RingHomInvPair (eA.symm : A' →+* A) (eA : A →+* A') :=
    RingHomInvPair.symm (eA : A →+* A') (eA.symm : A' →+* A)
  let eB' : N ≃ₗ[B'] N' := e.extendScalarsOfIsLocalization T B'
  let eSemi : N ≃ₛₗ[(eA : A →+* A')] N' :=
    { toFun := eB'
      invFun := eB'.symm
      left_inv := eB'.left_inv
      right_inv := eB'.right_inv
      map_add' := eB'.map_add
      map_smul' := fun a n ↦ by
        calc
          eB' (a • n) = eB' ((algebraMap A' B' (eA a)) • n) := by
            rw [hsource a n]
          _ = (algebraMap A' B' (eA a)) • eB' n := by
            rw [map_smul]
          _ = eA a • eB' n := by
            exact IsScalarTower.algebraMap_smul B' (eA a) (eB' n) }
  letI : Module.Free A N := hfree
  exact Module.Free.of_equiv eSemi

/-- Helper for Chap10 Lemma 10 118 4: compatible ring equivalences are semilinear for the
algebra scalar actions. -/
private lemma ringEquiv_map_smul_of_compatible
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (a : A) (b : B) :
    eB (a • b) = eA a • eB b := by
  -- Expand both scalar actions to multiplication and use the compatibility of algebra maps.
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcompat a]

/-- Helper for Chap10 Lemma 10 118 4: freeness of an algebra as a module is invariant under
compatible equivalences of the base and target rings. -/
private theorem moduleFreeOfCompatibleRingEquiv
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcompat : ∀ a : A, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (hfree : Module.Free A B) :
    Module.Free A' B' := by
  -- Package the compatible ring equivalence as a semilinear equivalence and use the standard
  -- free-module transport theorem.
  letI : RingHomInvPair (eA : A →+* A') (eA.symm : A' →+* A) :=
    RingHomInvPair.of_ringEquiv eA
  letI : RingHomInvPair (eA.symm : A' →+* A) (eA : A →+* A') :=
    RingHomInvPair.symm (eA : A →+* A') (eA.symm : A' →+* A)
  let e : B ≃ₛₗ[(eA : A →+* A')] B' :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := fun a b ↦ ringEquiv_map_smul_of_compatible eA eB hcompat a b }
  letI : Module.Free A B := hfree
  exact Module.Free.of_equiv e

/-- Helper for Chap10 Lemma 10 118 4: the canonical map into an iterated localization
`S⁻¹(S'⁻¹N)`. -/
private noncomputable abbrev iteratedLocalizedModuleMkLinearMap
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (S S' : Submonoid A) :
    N →ₗ[A] LocalizedModule S (LocalizedModule S' N) :=
  (LocalizedModule.mkLinearMap S (LocalizedModule S' N)).comp
    (LocalizedModule.mkLinearMap S' N)

/-- Helper for Chap10 Lemma 10 118 4: a scalar endomorphism that is invertible before
localization remains invertible after any localized-module map. -/
private theorem isLocalizedModuleEnd_isUnit_of_isUnit
    {A : Type*} [CommRing A] (S : Submonoid A)
    {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (f : N →ₗ[A] N') [IsLocalizedModule S f] {r : A}
    (h : IsUnit (algebraMap A (Module.End A N) r)) :
    IsUnit (algebraMap A (Module.End A N') r) := by
  -- Localize the source scalar endomorphism and identify the localized map with scalar
  -- multiplication on the target localized module.
  let localizedEnd :
      Module.End A N' :=
    IsLocalizedModule.map S f f (algebraMap A (Module.End A N) r)
  have hbij : Function.Bijective localizedEnd := by
    have hbij₀ : Function.Bijective (algebraMap A (Module.End A N) r) :=
      (Module.End.isUnit_iff _).mp h
    constructor
    · exact
        IsLocalizedModule.map_injective (S := S) (f := f) (g := f)
          (h := algebraMap A (Module.End A N) r) hbij₀.1
    · exact
        IsLocalizedModule.map_surjective (S := S) (f := f) (g := f)
          (h := algebraMap A (Module.End A N) r) hbij₀.2
  have hEq :
      localizedEnd = algebraMap A (Module.End A N') r := by
    -- The localized endomorphism and scalar multiplication agree on original numerators.
    apply IsLocalizedModule.linearMap_ext S f f
    ext x
    simp [localizedEnd]
  rw [← hEq]
  exact (Module.End.isUnit_iff _).2 hbij

/-- Helper for Chap10 Lemma 10 118 4: composing two localized-module maps localizes at the
supremum of the two denominator submonoids. -/
private theorem isLocalizedModule_comp_sup
    {A : Type*} [CommRing A] {N N₁ N₂ : Type*}
    [AddCommGroup N] [Module A N]
    [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂]
    (S S' : Submonoid A)
    (f₁ : N →ₗ[A] N₁) [IsLocalizedModule S' f₁]
    (f₂ : N₁ →ₗ[A] N₂) [IsLocalizedModule S f₂] :
    IsLocalizedModule (S ⊔ S') (f₂.comp f₁) := by
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨s, hs, s', hs', hss'⟩
    have hx : (x : A) = s * s' := by
      simpa using hss'.symm
    -- Denominators from the outer localization are already units; denominators from the inner
    -- localization remain units after the outer localization.
    have hsUnit :
        IsUnit (algebraMap A (Module.End A N₂) s) :=
      IsLocalizedModule.map_units (f := f₂) ⟨s, hs⟩
    have hs'Unit₀ :
        IsUnit (algebraMap A (Module.End A N₁) s') :=
      IsLocalizedModule.map_units (f := f₁) ⟨s', hs'⟩
    have hs'Unit :
        IsUnit (algebraMap A (Module.End A N₂) s') :=
      isLocalizedModuleEnd_isUnit_of_isUnit S f₂ hs'Unit₀
    rw [hx, map_mul]
    exact hsUnit.mul hs'Unit
  · intro m
    -- Clear the outer denominator, then the inner denominator, and multiply the two witnesses.
    obtain ⟨⟨p, s⟩, hs⟩ := IsLocalizedModule.surj S f₂ m
    obtain ⟨⟨x, s'⟩, hs'⟩ := IsLocalizedModule.surj S' f₁ p
    refine ⟨⟨x, ⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩⟩, ?_⟩
    change (s.1 * s'.1 : A) • m = f₂ (f₁ x)
    calc
      (s.1 * s'.1 : A) • m = (s'.1 * s.1 : A) • m := by rw [mul_comm]
      _ = s'.1 • (s • m) := by
        change (s'.1 * s.1 : A) • m = (s'.1 : A) • ((s : A) • m)
        rw [smul_smul]
      _ = s'.1 • f₂ p := by rw [hs]
      _ = f₂ (s'.1 • p) := by rw [LinearMap.map_smul_of_tower]
      _ = f₂ (f₁ x) := congrArg f₂ hs'
  · intro x₁ x₂ h
    -- Equality after the composite clears in the outer localization and then in the inner one.
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f₂) h
    have hs₁ : f₁ (s • x₁) = f₁ (s • x₂) := by
      simpa [LinearMap.map_smul_of_tower] using hs
    obtain ⟨s', hs'⟩ := IsLocalizedModule.exists_of_eq (S := S') (f := f₁) hs₁
    refine ⟨⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩, ?_⟩
    change (s.1 * s'.1 : A) • x₁ = (s.1 * s'.1 : A) • x₂
    calc
      (s.1 * s'.1 : A) • x₁ = (s'.1 * s.1 : A) • x₁ := by rw [mul_comm]
      _ = s'.1 • (s • x₁) := by
        change (s'.1 * s.1 : A) • x₁ = (s'.1 : A) • ((s : A) • x₁)
        rw [smul_smul]
      _ = s'.1 • (s • x₂) := hs'
      _ = (s'.1 * s.1 : A) • x₂ := by
        change (s'.1 : A) • ((s : A) • x₂) = (s'.1 * s.1 : A) • x₂
        rw [smul_smul]
      _ = (s.1 * s'.1 : A) • x₂ := by rw [mul_comm]

/-- Helper for Chap10 Lemma 10 118 4: invertible scalar endomorphisms remain invertible after
localizing a module. -/
private theorem localizedModuleEnd_isUnit
    {A : Type*} [CommRing A] (S : Submonoid A)
    {N : Type*} [AddCommGroup N] [Module A N] {r : A}
    (h : IsUnit (algebraMap A (Module.End A N) r)) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule S N)) r) := by
  -- Localize the scalar endomorphism and identify it with scalar multiplication upstairs.
  let localizedEnd :
      Module.End A (LocalizedModule S N) :=
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N)
      (LocalizedModule.mkLinearMap S N) (algebraMap A (Module.End A N) r)
  have hbij : Function.Bijective localizedEnd := by
    have hbij₀ : Function.Bijective (algebraMap A (Module.End A N) r) :=
      (Module.End.isUnit_iff _).mp h
    constructor
    · exact
        IsLocalizedModule.map_injective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap A (Module.End A N) r) hbij₀.1
    · exact
        IsLocalizedModule.map_surjective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap A (Module.End A N) r) hbij₀.2
  have hEq :
      localizedEnd = algebraMap A (Module.End A (LocalizedModule S N)) r := by
    -- Check the two endomorphisms on canonical localized numerators.
    ext x
    induction x using LocalizedModule.induction_on with
    | _ n s =>
        simp [localizedEnd, IsLocalizedModule.map_LocalizedModules, LocalizedModule.smul'_mk]
  rw [← hEq]
  exact (Module.End.isUnit_iff _).2 hbij

/-- Helper for Chap10 Lemma 10 118 4: iterated localization is localization at the supremum of
the two denominator submonoids. -/
private instance iteratedLocalizedModule_isLocalizedModule_sup
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (S S' : Submonoid A) :
    IsLocalizedModule (S ⊔ S')
      (iteratedLocalizedModuleMkLinearMap (A := A) (N := N) S S') := by
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨s, hs, s', hs', hss'⟩
    have hx : (x : A) = s * s' := by
      simpa using hss'.symm
    -- The outer localization inverts `S`; elements of `S'` remain invertible after the
    -- second localization by functoriality of localized endomorphisms.
    have hsUnit :
        IsUnit
          (algebraMap A (Module.End A (LocalizedModule S (LocalizedModule S' N))) s) :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S (LocalizedModule S' N))
        ⟨s, hs⟩
    have hs'Unit₀ :
        IsUnit (algebraMap A (Module.End A (LocalizedModule S' N)) s') :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S' N) ⟨s', hs'⟩
    have hs'Unit :
        IsUnit
          (algebraMap A (Module.End A (LocalizedModule S (LocalizedModule S' N))) s') :=
      localizedModuleEnd_isUnit (S := S) hs'Unit₀
    rw [hx, map_mul]
    exact hsUnit.mul hs'Unit
  · intro m
    -- Clear the outer denominator first, then the inner denominator, and multiply them in
    -- the supremum.
    obtain ⟨⟨p, s⟩, hs⟩ :=
      IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) m
    obtain ⟨⟨x, s'⟩, hs'⟩ :=
      IsLocalizedModule.surj S' (LocalizedModule.mkLinearMap S' N) p
    refine ⟨⟨x, ⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩⟩, ?_⟩
    change (s.1 * s'.1 : A) • m =
      (LocalizedModule.mkLinearMap S (LocalizedModule S' N))
        ((LocalizedModule.mkLinearMap S' N) x)
    calc
      (s.1 * s'.1 : A) • m = (s'.1 * s.1 : A) • m := by rw [mul_comm]
      _ = s'.1 • (s • m) := by
        change (s'.1 * s.1 : A) • m = (s'.1 : A) • ((s : A) • m)
        rw [smul_smul]
      _ = s'.1 • (LocalizedModule.mkLinearMap S (LocalizedModule S' N) p) := by rw [hs]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) (s'.1 • p) := by
        rw [LinearMap.map_smul_of_tower]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' N))
            ((LocalizedModule.mkLinearMap S' N) x) := by
        simpa using congrArg (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) hs'
  · intro x₁ x₂ h
    -- Equality in the iterated localization clears first in the outer localization and then in
    -- the inner localization.
    obtain ⟨s, hs⟩ :=
      IsLocalizedModule.exists_of_eq (S := S)
        (f := LocalizedModule.mkLinearMap S (LocalizedModule S' N)) h
    have hs'₀ :
        (LocalizedModule.mkLinearMap S' N) (s • x₁) =
          (LocalizedModule.mkLinearMap S' N) (s • x₂) := by
      simpa [LinearMap.map_smul_of_tower] using hs
    obtain ⟨s', hs'⟩ :=
      IsLocalizedModule.exists_of_eq (S := S')
        (f := LocalizedModule.mkLinearMap S' N) hs'₀
    refine ⟨⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩, ?_⟩
    change (s.1 * s'.1 : A) • x₁ = (s.1 * s'.1 : A) • x₂
    calc
      (s.1 * s'.1 : A) • x₁ = (s'.1 * s.1 : A) • x₁ := by rw [mul_comm]
      _ = s'.1 • (s • x₁) := by
        change (s'.1 * s.1 : A) • x₁ = (s'.1 : A) • ((s : A) • x₁)
        rw [smul_smul]
      _ = s'.1 • (s • x₂) := by simpa using hs'
      _ = (s'.1 * s.1 : A) • x₂ := by
        change (s'.1 : A) • ((s : A) • x₂) = (s'.1 * s.1 : A) • x₂
        rw [smul_smul]
      _ = (s.1 * s'.1 : A) • x₂ := by rw [mul_comm]

/-- Helper for Chap10 Lemma 10 118 4: direct localization away from `ab` is also localization at
the supremum of the two principal denominator submonoids. -/
private instance mkLinearMap_isLocalizedModule_sup_away_mul
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N) := by
  -- The submonoids generated by `a`, `b`, and `ab` have the same saturation.
  refine
    IsLocalizedModule.of_exists_mul_mem (S := Submonoid.powers (a * b))
      (T := Submonoid.powers a ⊔ Submonoid.powers b) ?_ ?_
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)
  · intro x hx
    rcases (Submonoid.mem_powers_iff x (a * b)).mp hx with ⟨n, rfl⟩
    simpa [mul_pow] using
      (Submonoid.mul_mem_sup
        (show a ^ n ∈ Submonoid.powers a from ⟨n, rfl⟩)
        (show b ^ n ∈ Submonoid.powers b from ⟨n, rfl⟩))
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨y, hy, z, hz, hyz⟩
    have hx : (x : A) = y * z := by
      simpa using hyz.symm
    rcases (Submonoid.mem_powers_iff y a).mp hy with ⟨m, rfl⟩
    rcases (Submonoid.mem_powers_iff z b).mp hz with ⟨n, rfl⟩
    refine ⟨a ^ n * b ^ m, ?_⟩
    rw [hx]
    refine ⟨m + n, ?_⟩
    simp [pow_add, mul_pow, mul_assoc, mul_left_comm]

/-- Helper for Chap10 Lemma 10 118 4: the symmetric supremum description of direct localization
away from `ab`. -/
private instance mkLinearMap_isLocalizedModule_sup_away_mul_comm
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N) := by
  -- Swap the two generators in the supremum and use commutativity of multiplication.
  simpa [sup_comm, mul_comm] using
    (mkLinearMap_isLocalizedModule_sup_away_mul (A := A) (N := N) a b :
      IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
        (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N))

/-- Helper for Chap10 Lemma 10 118 4: reindex direct away-localizations along an equality of
denominators. -/
private noncomputable abbrev awayEqLinearEquiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {a b : A} (h : a = b) :
    LocalizedModule.Away a N ≃ₗ[A] LocalizedModule.Away b N :=
  h.rec (LinearEquiv.refl A (LocalizedModule.Away a N))

/-- Helper for Chap10 Lemma 10 118 4: localizing first away from `a` and then away from `b`
agrees with direct localization away from `ab`. -/
private noncomputable abbrev awayMulLinearEquiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    LocalizedModule.Away b (LocalizedModule.Away a N) ≃ₗ[A]
      LocalizedModule.Away (a * b) N :=
  IsLocalizedModule.linearEquiv (Submonoid.powers b ⊔ Submonoid.powers a)
    (iteratedLocalizedModuleMkLinearMap (A := A) (N := N)
      (Submonoid.powers b) (Submonoid.powers a))
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)

/-- Helper for Lemma 10.118.4: localizing the already-free algebra `S_f` once more at `g / 1`
keeps it free over `(R_f)_g`. -/
lemma iterated_away_free_algebra_over_base
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (Localization.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let At := Localization.Away t
  let Bt := Localization.Away (algebraMap A B t)
  let alg := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := alg.toSMul
  letI : Algebra At Bt := alg
  -- Pin the scalar tower through the explicit away map so instance search does not unfold the
  -- localized algebra structures repeatedly.
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  have hIso : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) Bt :=
    inferInstance
  have hloc : IsLocalizedModule (Submonoid.powers t)
      (IsScalarTower.toAlgHom A B Bt).toLinearMap :=
    (isLocalizedModule_iff_isLocalization (S := Submonoid.powers t) (A := B) (Aₛ := Bt)).mpr
      hIso
  have hfree : Module.Free A B := hf.free_algebra
  -- The algebra localization is the base change of the already-free `R_f`-module `S_f`.
  exact @Module.free_of_isLocalizedModule A B _ _ _ At Bt _ _ _ _ _ _
    (Submonoid.powers t) (IsScalarTower.toAlgHom A B Bt).toLinearMap inferInstance hloc hfree

/-- Helper for Lemma 10.118.4: localizing the already-free module `M_f` once more at `g / 1`
keeps it free over `(R_f)_g`. -/
lemma iterated_away_free_module_over_base
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (LocalizedModule.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))
        (LocalizedModule.Away (algebraMap R S f) M)) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let At := Localization.Away t
  let c : B := algebraMap A B t
  let Bt := Localization.Away c
  let Nt := LocalizedModule.Away c N
  let alg := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := alg.toSMul
  letI : Algebra At Bt := alg
  -- Keep the iterated ring and module localizations in the same scalar-tower normal form.
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower A B N := by
    refine IsScalarTower.mk ?_
    intro a b n
    change ((algebraMap A B) a * b) • n = (algebraMap A B a) • (b • n)
    exact smul_assoc (algebraMap A B a) b n
  let moduleA : Module A Nt := Module.compHom Nt (algebraMap A B)
  letI : SMul A Nt := moduleA.toSMul
  letI : Module A Nt := moduleA
  letI : IsScalarTower A B Nt := by
    refine IsScalarTower.mk ?_
    intro a b n
    change ((algebraMap A B) a * b) • n = (algebraMap A B a) • (b • n)
    exact smul_assoc (algebraMap A B a) b n
  let moduleAt : Module At Nt := Module.compHom Nt (algebraMap At Bt)
  letI : SMul At Nt := moduleAt.toSMul
  letI : Module At Nt := moduleAt
  letI : IsScalarTower A At Nt := by
    refine IsScalarTower.mk ?_
    intro a b n
    rw [Algebra.smul_def]
    rw [show ∀ x : At, x • n = (algebraMap At Bt x) • n from fun x ↦ rfl]
    rw [show b • n = (algebraMap At Bt b) • n from rfl]
    rw [map_mul]
    rw [show algebraMap At Bt (algebraMap A At a) = algebraMap B Bt (algebraMap A B a) from
      (IsScalarTower.algebraMap_apply A At Bt a).symm.trans
        (IsScalarTower.algebraMap_apply A B Bt a)]
    rw [mul_smul]
    rw [algebraMap_smul]
    rfl
  let locB : N →ₗ[B] Nt := LocalizedModule.mkLinearMap (Submonoid.powers c) N
  let locA : N →ₗ[A] Nt := locB.restrictScalars A
  have hfree : Module.Free A N := hf.free_module
  have hloc : IsLocalizedModule (Submonoid.powers t) locA := by
    -- Restrict the canonical `B`-localization at `algebraMap A B t` to the corresponding
    -- `A`-localization at `t`.
    exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := A) (B := B) (N := N)
      (N' := Nt) t locB
  -- The restricted localized-module map presents `(M_f)_g` as the base change of the free
  -- `R_f`-module `M_f`.
  exact @Module.free_of_isLocalizedModule A N _ _ _ At Nt _ _ _ _ _ _
    (Submonoid.powers t) locA inferInstance hloc hfree

/-- Helper for Lemma 10.118.4: once `(10.118.3.1)` holds at `f`, all four localization-condition
fields survive one more localization in the already-localized `f`-world. -/
lemma localizationCondition_map_away_self
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  letI : Algebra.FinitePresentation A B := hf.finitePresentation_algebra
  letI : Module.FinitePresentation B N := hf.finitePresentation_module
  -- Package the standard localized finite-presentation instances with the two freeness helpers.
  have hfpAlg : Algebra.FinitePresentation (Localization.Away t)
      (Localization.Away (algebraMap A B t)) :=
    awayAlgebraFinitePresentationOverBase (A := A) (B := B) t
  have hfpModule : Module.FinitePresentation (Localization.Away (algebraMap A B t))
      (LocalizedModule.Away (algebraMap A B t) N) :=
    awayModuleFinitePresentation (A := B) (M := N) (algebraMap A B t)
  have hfreeAlg : Module.Free (Localization.Away t)
      (Localization.Away (algebraMap A B t)) :=
    iterated_away_free_algebra_over_base (R := R) (S := S) (M := M) f g hf
  have hfreeModule : Module.Free (Localization.Away t)
      (LocalizedModule.Away (algebraMap A B t) N) :=
    iterated_away_free_module_over_base (R := R) (S := S) (M := M) f g hf
  exact
    { finitePresentation_algebra := hfpAlg
      finitePresentation_module := hfpModule
      free_algebra := hfreeAlg
      free_module := hfreeModule }

/-- Helper for Chap10 Lemma 10 118 4: finite presentation of the target algebra transports from
the iterated product localization to the direct product localization. -/
private lemma productAwayAlgebraFinitePresentation
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R)
    (hfg :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g)) :
    Algebra.FinitePresentation (Localization.Away (f * g))
      (Localization.Away (algebraMap R S (f * g))) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the direct product algebra map to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the first localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the second localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Compose the two pinned source scalar towers.
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  have hAtLoc : IsLocalization.Away (f * g) At := by
    -- The iterated source localization is a localization away from the product.
    dsimp [At, t, A]
    exact IsLocalization.Away.mul' (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) f g
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the `S_f` scalar tower.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of the product.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (f * g) At := hAtLoc
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eR : At ≃+* Rfg :=
    (IsLocalization.algEquiv (Submonoid.powers (f * g)) At Rfg).toRingEquiv
  let eS : Bt ≃+* Sfg :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Bt Sfg).toRingEquiv
  have hcompat : ∀ a : At, eS (algebraMap At Bt a) = algebraMap Rfg Sfg (eR a) := by
    -- The two localization equivalences commute with the algebra maps.
    intro a
    dsimp [eR, eS]
    exact IsLocalization.algEquiv_comp_algebraMap_apply
      (R := R) (S := S)
      (M := Submonoid.powers (f * g))
      (N := Submonoid.powers (algebraMap R S (f * g)))
      (Rₘ := At) (Sₙ := Bt) (Rₘ' := Rfg) (Sₙ' := Sfg) a
  letI : Algebra.FinitePresentation At Bt := hfg.finitePresentation_algebra
  exact algebraFinitePresentationOfRingEquiv eR eS hcompat

/-- Helper for Chap10 Lemma 10 118 4: freeness of the target algebra transports from the
iterated product localization to the direct product localization. -/
private lemma productAwayAlgebraFree
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R)
    (hfg :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g)) :
    Module.Free (Localization.Away (f * g))
      (Localization.Away (algebraMap R S (f * g))) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the direct product algebra map to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the first localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the second localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Compose the two pinned source scalar towers.
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  have hAtLoc : IsLocalization.Away (f * g) At := by
    -- The iterated source localization is a localization away from the product.
    dsimp [At, t, A]
    exact IsLocalization.Away.mul' (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) f g
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the `S_f` scalar tower.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of the product.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (f * g) At := hAtLoc
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eR : At ≃+* Rfg :=
    (IsLocalization.algEquiv (Submonoid.powers (f * g)) At Rfg).toRingEquiv
  let eS : Bt ≃+* Sfg :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Bt Sfg).toRingEquiv
  have hcompat : ∀ a : At, eS (algebraMap At Bt a) = algebraMap Rfg Sfg (eR a) := by
    -- The two localization equivalences commute with the algebra maps.
    intro a
    dsimp [eR, eS]
    exact IsLocalization.algEquiv_comp_algebraMap_apply
      (R := R) (S := S)
      (M := Submonoid.powers (f * g))
      (N := Submonoid.powers (algebraMap R S (f * g)))
      (Rₘ := At) (Sₙ := Bt) (Rₘ' := Rfg) (Sₙ' := Sfg) a
  exact moduleFreeOfCompatibleRingEquiv eR eS hcompat hfg.free_algebra

/-- Helper for Chap10 Lemma 10 118 4: the iterated and direct product localizations of the module
are `S`-linearly equivalent. -/
private lemma productAwayModuleLinearEquiv_nonempty
    {M : Type*} [AddCommGroup M] [Module S M] (f g : R) :
    let A := Localization.Away f
    let B := Localization.Away (algebraMap R S f)
    let N := LocalizedModule.Away (algebraMap R S f) M
    let t : A := algebraMap R A g
    let c : B := algebraMap A B t
    Nonempty
      (LocalizedModule.Away c N ≃ₗ[S] LocalizedModule.Away (algebraMap R S (f * g)) M) := by
  -- Compare the second `B`-localization with localization at `g` over `S`, then use the
  -- generic product-localization equivalence over `S`.
  dsimp
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let Nt := LocalizedModule.Away c N
  let Mfg := LocalizedModule.Away (algebraMap R S (f * g)) M
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the first localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the `S_f` scalar tower.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R A B g]
  letI : IsScalarTower S B N := inferInstance
  letI : IsScalarTower S B Nt := inferInstance
  let locB : N →ₗ[B] Nt := LocalizedModule.mkLinearMap (Submonoid.powers c) N
  have hlocB :
      IsLocalizedModule (Submonoid.powers (algebraMap S B (algebraMap R S g))) locB := by
    -- Rewrite the canonical `B`-denominator `c` to the image of `g` from `S`.
    simpa [hc] using
      (inferInstance :
        IsLocalizedModule (Submonoid.powers c)
          (LocalizedModule.mkLinearMap (Submonoid.powers c) N))
  let locS : N →ₗ[S] Nt := locB.restrictScalars S
  have hlocS : IsLocalizedModule (Submonoid.powers (algebraMap R S g)) locS := by
    -- Restrict the `B`-localized-module map to `S`.
    letI : IsLocalizedModule
        (Submonoid.powers (algebraMap S B (algebraMap R S g))) locB := hlocB
    exact isLocalizedModuleRestrictScalarsPowersAlgebraMap (A := S) (B := B)
      (N := N) (N' := Nt) (algebraMap R S g) locB
  let directG : N →ₗ[S] LocalizedModule.Away (algebraMap R S g) N :=
    LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S g)) N
  let eIter : Nt ≃ₗ[S] LocalizedModule.Away (algebraMap R S g) N :=
    IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R S g)) locS directG
  let eMul :
      LocalizedModule.Away (algebraMap R S g) N ≃ₗ[S]
        LocalizedModule.Away ((algebraMap R S f) * (algebraMap R S g)) M :=
    awayMulLinearEquiv (A := S) (N := M) (algebraMap R S f) (algebraMap R S g)
  let eEq :
      LocalizedModule.Away ((algebraMap R S f) * (algebraMap R S g)) M ≃ₗ[S] Mfg :=
    awayEqLinearEquiv (A := S) (N := M) (by rw [map_mul])
  exact ⟨eIter.trans (eMul.trans eEq)⟩

/-- Helper for Chap10 Lemma 10 118 4: the canonical source and target product-localization ring
equivalences commute with algebra maps and fix target numerators. -/
private lemma productAwayRingEquivData_nonempty (f g : R) :
    let A := Localization.Away f
    let B := Localization.Away (algebraMap R S f)
    let t : A := algebraMap R A g
    let c : B := algebraMap A B t
    let At := Localization.Away t
    let Bt := Localization.Away c
    let Rfg := Localization.Away (f * g)
    let Sfg := Localization.Away (algebraMap R S (f * g))
    ∃ (eR : At ≃+* Rfg) (eS : Bt ≃+* Sfg),
      (∀ a : At, eS (algebraMap At Bt a) = algebraMap Rfg Sfg (eR a)) ∧
        (∀ s : S, eS (algebraMap S Bt s) = algebraMap S Sfg s) := by
  -- The two iterated rings are localizations away from the same product denominators, so the
  -- universal property gives the required compatible equivalences.
  dsimp
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the direct product algebra map to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the first localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the second localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Compose the two pinned source scalar towers.
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  have hAtLoc : IsLocalization.Away (f * g) At := by
    -- The iterated source localization is a localization away from the product.
    dsimp [At, t, A]
    exact IsLocalization.Away.mul' (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) f g
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the `S_f` scalar tower.
    dsimp [c, t, A, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R A B g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of the product.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (f * g) At := hAtLoc
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eR : At ≃+* Rfg :=
    (IsLocalization.algEquiv (Submonoid.powers (f * g)) At Rfg).toRingEquiv
  let eS : Bt ≃+* Sfg :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Bt Sfg).toRingEquiv
  have hcompat : ∀ a : At, eS (algebraMap At Bt a) = algebraMap Rfg Sfg (eR a) := by
    -- The two localization equivalences commute with the algebra maps.
    intro a
    dsimp [eR, eS]
    exact IsLocalization.algEquiv_comp_algebraMap_apply
      (R := R) (S := S)
      (M := Submonoid.powers (f * g))
      (N := Submonoid.powers (algebraMap R S (f * g)))
      (Rₘ := At) (Sₙ := Bt) (Rₘ' := Rfg) (Sₙ' := Sfg) a
  have hScompat : ∀ s : S, eS (algebraMap S Bt s) = algebraMap S Sfg s := by
    -- The target equivalence fixes original `S`-numerators.
    intro s
    dsimp [eS]
    exact AlgEquiv.commutes
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Bt Sfg) s
  exact ⟨eR, eS, hcompat, hScompat⟩

/-- Helper for Chap10 Lemma 10 118 4: finite presentation of the localized module transports
from the iterated product localization to the direct product localization. -/
private lemma productAwayModuleFinitePresentation
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R)
    (hfg :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g)) :
    Module.FinitePresentation (Localization.Away (algebraMap R S (f * g)))
      (LocalizedModule.Away (algebraMap R S (f * g)) M) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let Bt := Localization.Away c
  let Nt := LocalizedModule.Away c N
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let Mfg := LocalizedModule.Away (algebraMap R S (f * g)) M
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the first localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  have hc : algebraMap S B (algebraMap R S g) = c := by
    -- The second target denominator is the image of `g` through the `S_f` scalar tower.
    dsimp [c, t, B]
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S f)) g,
      ← IsScalarTower.algebraMap_apply R (Localization.Away f)
        (Localization.Away (algebraMap R S f)) g]
  have hBtLoc : IsLocalization.Away (algebraMap R S (f * g)) Bt := by
    -- The iterated target localization is a localization away from the image of the product.
    dsimp [Bt]
    have hloc_c :
        IsLocalization.Away (algebraMap S B (algebraMap R S g)) (Localization.Away c) := by
      simpa [hc] using (inferInstance : IsLocalization.Away c (Localization.Away c))
    simpa [map_mul] using
      (IsLocalization.Away.mul' B (Localization.Away c)
        (algebraMap R S f) (algebraMap R S g))
  letI : IsLocalization.Away (algebraMap R S (f * g)) Bt := hBtLoc
  let eS : Bt ≃+* Sfg :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Bt Sfg).toRingEquiv
  have hScompat : ∀ s : S, eS (algebraMap S Bt s) = algebraMap S Sfg s := by
    -- The target equivalence fixes original `S`-numerators.
    intro s
    dsimp [eS]
    exact AlgEquiv.commutes
      (IsLocalization.algEquiv (Submonoid.powers (algebraMap R S (f * g))) Bt Sfg) s
  obtain ⟨eM⟩ := productAwayModuleLinearEquiv_nonempty (R := R) (S := S) (M := M) f g
  let moduleSfgNt : Module Sfg Nt := Module.compHom Nt (eS.symm : Sfg →+* Bt)
  letI : Module Sfg Nt := moduleSfgNt
  letI : SMul Sfg Nt := moduleSfgNt.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul Sfg Nt Nt := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction Sfg Nt := Module.toDistribMulAction
  letI : MulAction Sfg Nt := DistribMulAction.toMulAction
  letI : IsScalarTower S Bt Nt := inferInstance
  letI : IsScalarTower S Sfg Nt := by
    -- The pulled-back `Sfg`-action restricts to the original `S`-action.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro s n
    have hsymm : eS.symm (algebraMap S Sfg s) = algebraMap S Bt s := by
      apply eS.injective
      rw [eS.apply_symm_apply, hScompat s]
    calc
      algebraMap S Sfg s • n = eS.symm (algebraMap S Sfg s) • n := rfl
      _ = algebraMap S Bt s • n := by rw [hsymm]
      _ = s • n := IsScalarTower.algebraMap_smul Bt s n
  have hfpNt : Module.FinitePresentation Sfg Nt :=
    moduleFinitePresentationOfRingEquivCompHom eS hfg.finitePresentation_module
  exact moduleFinitePresentationOfExtendedLocalizedEquiv
    (A := S) (Aₛ := Sfg) (N := Nt) (N' := Mfg)
    (Submonoid.powers (algebraMap R S (f * g))) eM hfpNt

/-- Helper for Chap10 Lemma 10 118 4: freeness of the localized module transports from the
iterated product localization to the direct product localization. -/
private lemma productAwayModuleFree
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R)
    (hfg :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g)) :
    Module.Free (Localization.Away (f * g))
      (LocalizedModule.Away (algebraMap R S (f * g)) M) := by
  let A := Localization.Away f
  let B := Localization.Away (algebraMap R S f)
  let N := LocalizedModule.Away (algebraMap R S f) M
  let t : A := algebraMap R A g
  let c : B := algebraMap A B t
  let At := Localization.Away t
  let Bt := Localization.Away c
  let Nt := LocalizedModule.Away c N
  let Rfg := Localization.Away (f * g)
  let Sfg := Localization.Away (algebraMap R S (f * g))
  let Mfg := LocalizedModule.Away (algebraMap R S (f * g)) M
  let algRfgSfg := (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).toAlgebra
  letI : SMul Rfg Sfg := algRfgSfg.toSMul
  letI : Algebra Rfg Sfg := algRfgSfg
  letI : IsScalarTower R Rfg Sfg :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the direct product algebra map to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun
        (Localization.awayMapₐ (Algebra.ofId R S) (f * g)).comp_algebraMap x
  let algAB := (Localization.awayMapₐ (Algebra.ofId R S) f).toAlgebra
  letI : SMul A B := algAB.toSMul
  letI : Algebra A B := algAB
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the first localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId R S) f).comp_algebraMap x
  let algAtBt := (Localization.awayMapₐ (Algebra.ofId A B) t).toAlgebra
  letI : SMul At Bt := algAtBt.toSMul
  letI : Algebra At Bt := algAtBt
  letI : IsScalarTower A At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Pin the second localized target algebra to the canonical away-map spelling.
      symm
      exact DFunLike.congr_fun (Localization.awayMapₐ (Algebra.ofId A B) t).comp_algebraMap x
  letI : IsScalarTower R At Bt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      -- Compose the two pinned source scalar towers.
      calc
        algebraMap R Bt x = algebraMap A Bt (algebraMap R A x) := by
          rw [IsScalarTower.algebraMap_apply R A Bt]
        _ = algebraMap At Bt (algebraMap A At (algebraMap R A x)) := by
          rw [IsScalarTower.algebraMap_apply A At Bt]
        _ = algebraMap At Bt (algebraMap R At x) := by
          rw [← IsScalarTower.algebraMap_apply R A At x]
  obtain ⟨eR, eS, hcompat, hScompat⟩ :=
    productAwayRingEquivData_nonempty (R := R) (S := S) f g
  obtain ⟨eM⟩ := productAwayModuleLinearEquiv_nonempty (R := R) (S := S) (M := M) f g
  let moduleSfgNt : Module Sfg Nt := Module.compHom Nt (eS.symm : Sfg →+* Bt)
  letI : Module Sfg Nt := moduleSfgNt
  letI : SMul Sfg Nt := moduleSfgNt.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul Sfg Nt Nt := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction Sfg Nt := Module.toDistribMulAction
  letI : MulAction Sfg Nt := DistribMulAction.toMulAction
  letI : IsScalarTower S Bt Nt := inferInstance
  letI : IsScalarTower S Sfg Nt := by
    -- The pulled-back `Sfg`-action restricts to the original `S`-action.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro s n
    have hsymm : eS.symm (algebraMap S Sfg s) = algebraMap S Bt s := by
      apply eS.injective
      rw [eS.apply_symm_apply, hScompat s]
    calc
      algebraMap S Sfg s • n = eS.symm (algebraMap S Sfg s) • n := rfl
      _ = algebraMap S Bt s • n := by rw [hsymm]
      _ = s • n := IsScalarTower.algebraMap_smul Bt s n
  let moduleAtNt : Module At Nt := Module.compHom Nt (algebraMap At Bt)
  letI : Module At Nt := moduleAtNt
  letI : SMul At Nt := moduleAtNt.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul At Nt Nt := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction At Nt := Module.toDistribMulAction
  letI : MulAction At Nt := DistribMulAction.toMulAction
  letI : IsScalarTower At Bt Nt := by
    -- The pulled-back `At`-action on `Nt` is defined through the algebra map to `Bt`.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a n
    rfl
  let moduleRfgMfg : Module Rfg Mfg := Module.compHom Mfg (algebraMap Rfg Sfg)
  letI : Module Rfg Mfg := moduleRfgMfg
  letI : SMul Rfg Mfg := moduleRfgMfg.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : HSMul Rfg Mfg Mfg := ⟨fun a n ↦ SMul.smul a n⟩
  letI : DistribMulAction Rfg Mfg := Module.toDistribMulAction
  letI : MulAction Rfg Mfg := DistribMulAction.toMulAction
  letI : IsScalarTower Rfg Sfg Mfg := by
    -- The direct product module action over `Rfg` is the restriction of the `Sfg`-action.
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a n
    rfl
  have hsource : ∀ (a : At) (n : Nt), algebraMap Rfg Sfg (eR a) • n = a • n := by
    -- Compatible ring equivalences identify source scalars after pulling back the target action.
    simpa using source_smul_of_compatibleRingEquivCompHom eR eS hcompat
  exact moduleFreeOfExtendedLocalizedEquiv
    (C := S) (B' := Sfg) (A := At) (A' := Rfg) (N := Nt) (N' := Mfg)
    (Submonoid.powers (algebraMap R S (f * g))) eR eM hsource hfg.free_module

/-- Helper for Lemma 10.118.4: package the direct-versus-iterated comparison for the product case.
The ring-side associate rewrite is already isolated in `away_mul_associated_right`; what remains is
to transport the module-side freeness and finite-presentation data through the canonical
localization equivalences. -/
lemma localizationCondition_of_map_away_product
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R)
    (hfg :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g)) :
    LocalizationCondition R S M (f * g) := by
  -- Route correction: the previous monolithic transport proof typed in pieces, but the whole
  -- declaration times out at `whnf` while elaborating the direct-versus-iterated localization
  -- comparison. The field transports are now isolated in separate helpers, so assembly is cheap.
  exact
    { finitePresentation_algebra := productAwayAlgebraFinitePresentation (R := R) (S := S) f g hfg
      finitePresentation_module := productAwayModuleFinitePresentation (R := R) (S := S) f g hfg
      free_algebra := productAwayAlgebraFree (R := R) (S := S) f g hfg
      free_module := productAwayModuleFree (R := R) (S := S) f g hfg }

lemma localizationCondition_mul_right
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition R S M (f * g) := by
  -- First localize the already-good `f`-world once more at `g / 1`, then identify that iterated
  -- witness with the direct `(fg)`-localization.
  exact localizationCondition_of_map_away_product (R := R) (S := S) (M := M) f g <|
    localizationCondition_map_away_self (R := R) (S := S) (M := M) f g hf

/-- Helper for Lemma 10.118.4: at a fixed localization parameter, exactness plus the endpoint
generic-flatness conditions imply the middle generic-flatness condition. -/
lemma localizationCondition_middle_of_shortExact
    (f : R) (hT : T.ShortExact)
    (h₁ : LocalizationCondition R S T.X₁ f) (h₃ : LocalizationCondition R S T.X₃ f) :
    LocalizationCondition R S T.X₂ f := by
  let S₀ : Submonoid S := Submonoid.powers (algebraMap R S f)
  let f₁ : T.X₁ →ₗ[S] LocalizedModule S₀ T.X₁ := LocalizedModule.mkLinearMap S₀ T.X₁
  let f₂ : T.X₂ →ₗ[S] LocalizedModule S₀ T.X₂ := LocalizedModule.mkLinearMap S₀ T.X₂
  let f₃ : T.X₃ →ₗ[S] LocalizedModule S₀ T.X₃ := LocalizedModule.mkLinearMap S₀ T.X₃
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) T.X₁) := h₁.finitePresentation_module
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) T.X₃) := h₃.finitePresentation_module
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) T.X₁) := h₁.free_module
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) T.X₃) := h₃.free_module
  -- Localizing a short exact sequence preserves exactness and the endpoint injective/surjective
  -- maps.
  have hExact : Function.Exact T.f.hom T.g.hom := by
    simpa using (moduleCat_exact_iff_function_exact T).mp hT.exact
  have hLocExact :
      Function.Exact (IsLocalizedModule.map S₀ f₁ f₂ T.f.hom)
        (IsLocalizedModule.map S₀ f₂ f₃ T.g.hom) := by
    simpa [f₁, f₂, f₃] using IsLocalizedModule.map_exact S₀ f₁ f₂ f₃ T.f.hom T.g.hom hExact
  have hLocInj : Function.Injective (IsLocalizedModule.map S₀ f₁ f₂ T.f.hom) := by
    simpa [f₁, f₂, f₃] using LocalizedModule.map_injective S₀ T.f.hom hT.moduleCat_injective_f
  have hLocSurj : Function.Surjective (IsLocalizedModule.map S₀ f₂ f₃ T.g.hom) := by
    simpa [f₁, f₂, f₃] using LocalizedModule.map_surjective S₀ T.g.hom hT.moduleCat_surjective_g
  let mapf :
      LocalizedModule.Away (algebraMap R S f) T.X₁ →ₗ[Localization.Away (algebraMap R S f)]
        LocalizedModule.Away (algebraMap R S f) T.X₂ := by
    simpa [S₀] using
      (LocalizedModule.map S₀ T.f.hom :
        LocalizedModule S₀ T.X₁ →ₗ[Localization S₀] LocalizedModule S₀ T.X₂)
  let mapg :
      LocalizedModule.Away (algebraMap R S f) T.X₂ →ₗ[Localization.Away (algebraMap R S f)]
        LocalizedModule.Away (algebraMap R S f) T.X₃ := by
    simpa [S₀] using
      (LocalizedModule.map S₀ T.g.hom :
        LocalizedModule S₀ T.X₂ →ₗ[Localization S₀] LocalizedModule S₀ T.X₃)
  have hLocExactAway : Function.Exact mapf mapg := by
    simpa [mapf, mapg, S₀] using hLocExact
  have hLocInjAway : Function.Injective mapf := by
    simpa [mapf, S₀] using hLocInj
  have hLocSurjAway : Function.Surjective mapg := by
    simpa [mapg, S₀] using hLocSurj
  -- Finite presentation of the localized middle term comes from Lemma 10.5.3.
  have hfp₂ :
      Module.FinitePresentation (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) T.X₂) := by
    exact Module.finitePresentation_of_exact mapf mapg hLocInjAway hLocSurjAway hLocExactAway
  let locf :
      LocalizedModule.Away (algebraMap R S f) T.X₁ →ₗ[Localization.Away f]
        LocalizedModule.Away (algebraMap R S f) T.X₂ :=
    { toFun := mapf
      map_add' := mapf.map_add
      map_smul' := fun r x ↦ by
        change mapf ((algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • x) =
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • mapf x
        simpa using mapf.map_smulₛₗ ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R S f)) r)) x }
  let locg :
      LocalizedModule.Away (algebraMap R S f) T.X₂ →ₗ[Localization.Away f]
        LocalizedModule.Away (algebraMap R S f) T.X₃ :=
    { toFun := mapg
      map_add' := mapg.map_add
      map_smul' := fun r x ↦ by
        change mapg ((algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • x) =
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • mapg x
        simpa using mapg.map_smulₛₗ ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R S f)) r)) x }
  have hLocExact' : Function.Exact locf locg := by
    simpa [locf, locg] using hLocExactAway
  have hLocInj' : Function.Injective locf := by
    simpa [locf] using hLocInjAway
  have hLocSurj' : Function.Surjective locg := by
    simpa [locg] using hLocSurjAway
  -- The localized middle term is free because the localized short exact sequence splits.
  have hfree₂ :
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R S f) T.X₂) :=
    free_middle_of_exact_of_free_ends locf locg hLocInj' hLocSurj' hLocExact'
  exact
    { finitePresentation_algebra := h₁.finitePresentation_algebra
      finitePresentation_module := hfp₂
      free_algebra := h₁.free_algebra
      free_module := hfree₂ }

-- Proof sketch: let `u` lie in both good loci. Choose basic opens around `u` coming from elements
-- `f1, f3 : R` witnessing the generic-flatness condition for `T.X₁` and `T.X₃`, and replace them by
-- the common refinement `f1 * f3`. Localizing the short exact sequence at that element preserves
-- exactness; then the endpoint assumptions imply the middle localized module is finitely presented
-- by Lemma `10.5.3`, and freeness is preserved under extensions. Hence the same basic open is
-- contained in the good locus of `T.X₂`.
/-- Chap10 Lemma 10 118 4: for a short exact sequence `0 → M1 → M2 → M3 → 0` of `S`-modules, the
intersection of the generic-flatness good loci of the outer terms is contained in the good locus
of the middle term. -/
@[stacks 051W]
theorem goodLocus_inter_subset_of_shortExact
    (hT : T.ShortExact) :
    goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂ := by
  intro u hu
  rw [goodLocus_eq_iUnion] at hu ⊢
  rcases hu with ⟨hu₁, hu₃⟩
  rcases Set.mem_iUnion.mp hu₁ with ⟨f₁, hf₁⟩
  rcases Set.mem_iUnion.mp hu₃ with ⟨f₃, hf₃⟩
  -- Refine the two basic-open witnesses to their common product witness.
  refine Set.mem_iUnion.mpr ?_
  refine ⟨⟨f₁.1 * f₃.1, ?_⟩, ?_⟩
  · have h₁' : LocalizationCondition R S T.X₁ (f₁.1 * f₃.1) :=
      localizationCondition_mul_right (R := R) (S := S) (M := T.X₁) f₁.1 f₃.1 f₁.2
    have h₃' : LocalizationCondition R S T.X₃ (f₁.1 * f₃.1) := by
      simpa [mul_comm] using
        (localizationCondition_mul_right (R := R) (S := S) (M := T.X₃) f₃.1 f₁.1 f₃.2)
    exact localizationCondition_middle_of_shortExact (R := R) (S := S) (T := T)
      (f₁.1 * f₃.1) hT h₁' h₃'
  · -- The point remains in the refined basic open because `D(f₁f₃) = D(f₁) ∩ D(f₃)`.
    rw [basicOpen_mul]
    exact ⟨hf₁, hf₃⟩

end

end ShortExact
end ShortComplex
end CategoryTheory
