import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_15
import stacks_proof.stacks_project.Chap10.Lemma_10_75_2
import stacks_proof.stacks_project.Chap10.Lemma_10_75_5
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap10.Lemma_10_76_1
import stacks_proof.stacks_project.Chap10.Lemma_10_77_5
import stacks_proof.stacks_project.Chap10.Remark_10_75_9

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pointwise
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Helper for Lemma 10.99.16: the public owner `N ↦ Tor₁^A(M, N)` is exact on the first two
arrows of a short exact row. -/
lemma tor_one_exact_of_shortExact
    (X : ModuleCat A) {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    Function.Exact ((((Tor (ModuleCat A) 1).obj X).map S.f).hom)
      ((((Tor (ModuleCat A) 1).obj X).map S.g).hom) := by
  let T := ModuleCat.torTensorSixTermSequence X hS
  have hT : T.Exact := ModuleCat.torTensorSixTermSequence_exact X hS
  -- Read off the first short-complex window from the canonical six-term exact Tor row.
  simpa [T] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := T.sc hT.toIsComplex 0)).1
      (hT.exact 0)

/-- Helper for Lemma 10.99.16: if the localization of an ideal away from `f` is the unit ideal,
then the ideal contains a power of `f`. -/
lemma pow_mem_of_away_localized_ideal_eq_top (f : A) (J : Ideal A)
    (hJ : Ideal.map (algebraMap A (Localization.Away f)) J = ⊤) :
    ∃ n : ℕ, f ^ n ∈ J := by
  by_contra hpow
  have hdisjoint : Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (J : Set A) := by
    rw [Set.disjoint_left]
    intro x hxpow hxJ
    change x ∈ Submonoid.powers f at hxpow
    rcases (Submonoid.mem_powers_iff x f).mp hxpow with ⟨n, rfl⟩
    exact hpow ⟨n, hxJ⟩
  have hmap_ne_top :
      Ideal.map (algebraMap A (Localization.Away f)) J ≠ ⊤ := by
    rw [IsLocalization.map_algebraMap_ne_top_iff_disjoint (M := Submonoid.powers f)
      (S := Localization.Away f)]
    exact hdisjoint
  exact hmap_ne_top hJ

/-- Helper for Lemma 10.99.16: if localization away from `f` kills a module and multiplication by
`f` is injective on that module, then the module is zero. -/
lemma isZero_of_localizedAway_isZero_of_smul_injective
    {T : Type u} [AddCommGroup T] [Module A T] (f : A)
    (hinj : Function.Injective fun t : T ↦ f • t)
    [Subsingleton (LocalizedModule.Away f T)] :
    IsZero (ModuleCat.of A T) := by
  rw [ModuleCat.isZero_of_iff_subsingleton]
  refine ⟨fun x y ↦ ?_⟩
  -- A power of `f` acts injectively because the single-step action is injective.
  have hpow_inj : ∀ n : ℕ, Function.Injective fun t : T ↦ f ^ n • t := by
    intro n
    induction n with
    | zero =>
        intro u v huv
        simpa using huv
    | succ n ih =>
        intro u v huv
        apply ih
        apply hinj
        simpa [pow_succ', mul_smul] using huv
  -- Subsingleton localization means some power of `f` kills every difference.
  have hsub :
      ∀ t : T, ∃ s ∈ (Submonoid.powers f : Submonoid A), s • t = 0 :=
    (LocalizedModule.subsingleton_iff (R := A) (M := T) (S := Submonoid.powers f)).mp
      inferInstance
  rcases hsub (x - y) with ⟨s, hs, hs0⟩
  rw [Submonoid.mem_powers_iff] at hs
  rcases hs with ⟨n, rfl⟩
  have hxy : x - y = 0 := hpow_inj n <| by simpa using hs0
  exact sub_eq_zero.mp hxy

/-- Helper for Lemma 10.99.16: if `(f)` is contained in the annihilator of `N`, then `f` kills
`N` elementwise. -/
lemma isTorsionBy_of_span_singleton_le_annihilator
    (f : A) {N : Type u} [AddCommGroup N] [Module A N]
    (hN : Ideal.span ({f} : Set A) ≤ Module.annihilator A N) :
    Module.IsTorsionBy A N f := by
  -- The source route starts by turning the quotient-ring hypothesis into literal `f`-torsion.
  rw [Module.isTorsionBy_iff_mem_annihilator]
  exact hN (Ideal.subset_span (by simp))

/-- Helper for Lemma 10.99.16: vanishing of the kernel of `I ⊗[A] N → N` forces the module-first
quotient `Tor₁` owner to vanish. -/
lemma tor_one_module_quotient_vanishes_of_ker_eq_bot
    {I : Ideal A} {N : Type u} [AddCommGroup N] [Module A N]
    (hker :
      LinearMap.ker (TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)) = ⊥) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
      (ModuleCat.of A (A ⧸ I)))) := by
  let μ : I ⊗[A] N →ₗ[A] N :=
    TensorProduct.lift ((LinearMap.lsmul A N).comp I.subtype)
  have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
    -- Proof comment: the assumed kernel equality identifies the kernel module with the zero
    -- submodule.
    exact (Submodule.subsingleton_iff_eq_bot).2 (by simpa [μ] using hker)
  let e :
      (((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj (ModuleCat.of A (A ⧸ I))) ≃ₗ[A]
        LinearMap.ker μ :=
    tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := N) I
  have hsub :
      Subsingleton ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A N)).obj
        (ModuleCat.of A (A ⧸ I)))) := by
    refine ⟨fun x y ↦ ?_⟩
    apply e.injective
    exact Subsingleton.elim _ _
  -- Proof comment: Remark `10.75.9` identifies the Tor owner with the zero kernel.
  exact (ModuleCat.isZero_iff_subsingleton).2 hsub

/-- Helper for Lemma 10.99.16: regularity of `f` on `A` and `M` kills the first quotient `Tor`
term `Tor₁^A(M, A / (f))`. -/
lemma tor_one_module_quotient_by_regular_element_vanishes
    (f : A) (hfA : IsRegular f) (hfM : IsSMulRegular M f) :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A))))) := by
  let _ := hfM
  let I : Ideal A := Ideal.span ({f} : Set A)
  let φ : A →ₗ[A] I :=
    { toFun := fun a ↦ ⟨a * f, (Ideal.mem_span_singleton').2 ⟨a, rfl⟩⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        simpa [add_mul]
      map_smul' := by
        intro a b
        apply Subtype.ext
        simp [mul_assoc, mul_left_comm, mul_comm] }
  let hspan : A ≃ₗ[A] I := by
    -- Proof comment: multiplication by `f` identifies `A` with the principal ideal `(f)`,
    -- because every element of `(f)` is a multiple of `f` and `f` acts injectively on `A`.
    refine LinearEquiv.ofBijective φ ?_
    constructor
    · intro a b hab
      apply Subtype.ext_iff.mp at hab
      exact hfA.right hab
    · intro x
      rcases (Ideal.mem_span_singleton').1 x.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext_iff.mpr
      simpa [φ] using ha
  let μ : I ⊗[A] M →ₗ[A] M :=
    TensorProduct.lift ((LinearMap.lsmul A M).comp I.subtype)
  let e : I ⊗[A] M ≃ₗ[A] A ⊗[A] M :=
    TensorProduct.congr hspan.symm (LinearEquiv.refl A M)
  have hμ :
      μ =
        (LinearMap.lsmul A M f).comp
          ((TensorProduct.lid A M).toLinearMap.comp e.toLinearMap) := by
    -- Proof comment: after identifying `(f)` with `A`, the tensor multiplication map is exactly
    -- multiplication by `f` on `M`.
    ext a m
    change a.1 • m = f • ((hspan.symm a : A) • m)
    rw [← mul_smul]
    have ha : (hspan.symm a : A) * f = a.1 := by
      exact congrArg Subtype.val (hspan.apply_symm_apply a)
    calc
      a.1 • m = ((hspan.symm a : A) * f) • m := by simpa [ha]
      _ = (f * hspan.symm a) • m := by rw [mul_comm]
  have hμ_injective : Function.Injective μ := by
    rw [hμ]
    exact hfM.comp ((TensorProduct.lid A M).injective.comp e.injective)
  have hker : LinearMap.ker μ = ⊥ := by
    exact LinearMap.ker_eq_bot.mpr hμ_injective
  -- Proof comment: the principal-ideal kernel now vanishes, so Remark `10.75.9` kills the Tor
  -- owner itself.
  simpa [I] using
    tor_one_module_quotient_vanishes_of_ker_eq_bot (A := A) (I := I) (N := M) hker

/-- Helper for Lemma 10.99.16: the quotient module `M / fM` is annihilated by `(f)`, so it carries
the expected scalar-tower structure over `A ⧸ (f)`. -/
lemma quotSMulTop_isTorsionBySet_span_singleton (f : A) :
    Module.IsTorsionBySet A (QuotSMulTop f M) (Ideal.span ({f} : Set A)) :=
  -- This is the fixed source module `M / fM`, viewed as an `A ⧸ (f)`-module.
  (Module.isTorsionBySet_span_singleton_iff f).mpr
    (Module.isTorsionBy_quotient_element_smul (M := M) f)

/-- Helper for Lemma 10.99.16: for an `A`-module annihilated by `(f)`, rewrite the source tensor
`M ⊗[A] N` as the quotient tensor over `A ⧸ (f)` used in the source proof. -/
noncomputable def tensor_compare_of_f_annihilated
    (f : A) {N : Type u} [AddCommGroup N] [Module A N]
    (hN : Ideal.span ({f} : Set A) ≤ Module.annihilator A N) :=
  let Abar : Type u := A ⧸ Ideal.span ({f} : Set A)
  let _ : CommRing Abar := inferInstance
  let _ : Algebra A Abar := Ideal.Quotient.algebra _
  let hfN : Module.IsTorsionBy A N f :=
    isTorsionBy_of_span_singleton_le_annihilator (A := A) f hN
  let hNset : Module.IsTorsionBySet A N (Ideal.span ({f} : Set A)) :=
    (Module.isTorsionBySet_span_singleton_iff f).mpr hfN
  let _ : Module Abar N :=
    Module.IsTorsionBySet.module (R := A) (M := N) (I := Ideal.span ({f} : Set A)) hNset
  let _ : IsScalarTower A Abar N :=
    Module.IsTorsionBySet.isScalarTower
      (R := A) (M := N) (I := Ideal.span ({f} : Set A)) hNset
  let hQset : Module.IsTorsionBySet A (QuotSMulTop f M) (Ideal.span ({f} : Set A)) :=
    quotSMulTop_isTorsionBySet_span_singleton (A := A) (M := M) f
  let _ : IsScalarTower A Abar (QuotSMulTop f M) :=
    Module.IsTorsionBySet.isScalarTower
      (R := A) (M := QuotSMulTop f M) (I := Ideal.span ({f} : Set A)) hQset
  -- Proof comment: commute the tensor, cancel the base change, and then replace
  -- `Abar ⊗[A] M` by the quotient module `M / fM`.
  let e₁ := TensorProduct.comm A M N
  let e₂ :=
    LinearEquiv.restrictScalars A <|
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A Abar Abar N M).symm
  let e₃base :=
    linearEquiv_over_quotient (R := A) (I := Ideal.span ({f} : Set A))
      (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span ({f} : Set A)))
  let e₃ :=
    LinearEquiv.restrictScalars A <|
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Abar N) e₃base
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 10.99.16: the image of multiplication by `f` on an `A`-module is the
pointwise submodule `fK`. -/
lemma range_lsmul_eq_pointwise_smul_top
    (f : A) {K : Type u} [AddCommGroup K] [Module A K] :
    LinearMap.range (LinearMap.lsmul A K f) = f • (⊤ : Submodule A K) := by
  -- Proof comment: both sides are the image of the same scalar-multiplication endomorphism of
  -- `K`, written once as a range and once as a pointwise-scaled top submodule.
  rw [Submodule.pointwise_smul_def, LinearMap.range_eq_map]
  rfl

end
