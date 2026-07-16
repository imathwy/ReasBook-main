import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import stacks_proof.stacks_project.Chap10.Definition_10_69_1

universe u v

open RingTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace RingTheory.Sequence

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: a finite product of elements outside a prime ideal remains outside
that prime ideal. -/
lemma finset_prod_notMem_prime (p : Ideal R) [p.IsPrime] {n : ℕ} (g : Fin n → R)
    (hg : ∀ i, g i ∉ p) : (∏ i, g i) ∉ p := by
  -- Use the prime complement multiplicative closure to keep the final denominator away from `p`.
  simpa using p.primeCompl.prod_mem fun i _ ↦ hg i

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: localizing a linear map is injective exactly when the localized
kernel module is trivial. -/
lemma localized_map_injective_iff_subsingleton_kernel {N : Type*}
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker φ)) := by
  let κ : LinearMap.ker φ →ₗ[R] LinearMap.ker (LocalizedModule.map S φ) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  -- Compare the localized kernel module with the actual kernel after localizing the map.
  constructor
  · intro hφ
    have hker :
        LinearMap.ker (LocalizedModule.map S φ) = ⊥ :=
      LinearMap.ker_eq_bot.2 hφ
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      Submodule.subsingleton_iff_eq_bot.2 hker
    exact ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).2 hsub
  · intro hker
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).1 hker
    exact LinearMap.ker_eq_bot.1 (Submodule.subsingleton_iff_eq_bot.1 hsub)

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: injectivity transports across a commuting square whose horizontal
maps are equivalences. -/
lemma injective_iff_of_equiv_conjugate
    {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
    (eSrc : α ≃ β) (eTgt : γ ≃ δ)
    (f : α → γ) (g : β → δ)
    (hcomm : eTgt ∘ f = g ∘ eSrc) :
    Function.Injective f ↔ Function.Injective g := by
  -- Move equalities through the source and target equivalences to compare injectivity on either
  -- side of the conjugation square.
  constructor
  · intro hf x y hxy
    apply eSrc.symm.injective
    apply hf
    apply eTgt.injective
    calc
      eTgt (f (eSrc.symm x)) = g x := by
        simpa [Function.comp] using congrFun hcomm (eSrc.symm x)
      _ = g y := hxy
      _ = eTgt (f (eSrc.symm y)) := by
        simpa [Function.comp] using (congrFun hcomm (eSrc.symm y)).symm
  · intro hg x y hxy
    apply eSrc.injective
    apply hg
    calc
      g (eSrc x) = eTgt (f x) := by
        simpa [Function.comp] using (congrFun hcomm x).symm
      _ = eTgt (f y) := by rw [hxy]
      _ = g (eSrc y) := by
        simpa [Function.comp] using congrFun hcomm y

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: if a module is finite over an `R`-algebra and vanishes at `p`, then
it already vanishes after inverting one element outside `p`. -/
lemma exists_subsingleton_away_of_finite_over_algebra (p : Ideal R) [p.IsPrime]
    {A : Type*} [CommRing A] [Algebra R A] {N : Type*}
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [Module.Finite A N] [Subsingleton (LocalizedModule p.primeCompl N)] :
    ∃ g : R, g ∉ p ∧ Subsingleton (LocalizedModule (.powers g) N) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  let generators : Fin n → N := fun i ↦ f (Pi.single i 1)
  have hkill_one :
      ∀ i : Fin n, ∃ s : R, s ∉ p ∧ s • generators i = 0 := by
    intro i
    -- The prime localization is trivial, so each chosen generator is killed by one denominator.
    obtain ⟨s, hs, hszero⟩ :=
      (LocalizedModule.subsingleton_iff.mp
        (show Subsingleton (LocalizedModule p.primeCompl N) from inferInstance))
        (generators i)
    exact ⟨s, hs, hszero⟩
  choose s hs_notMem hs_zero using hkill_one
  let g : R := ∏ i, s i
  have hg : g ∉ p := finset_prod_notMem_prime p s hs_notMem
  have hg_zero_generators : ∀ i : Fin n, g • generators i = 0 := by
    intro i
    -- Once one factor kills the `i`th generator, the full product does too.
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
    calc
      g • generators i = ((s i) * c) • generators i := by simp [g, hc]
      _ = (c * s i) • generators i := by rw [mul_comm]
      _ = c • (s i • generators i) := by
        simp [smul_smul]
      _ = 0 := by simp [hs_zero i]
  have hspan :
      Submodule.span A (Set.range generators) = ⊤ := by
    refine top_le_iff.mp ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hf x
    -- Expand a vector in the finite free source on the standard basis.
    have hy :
        y = ∑ i, y i • ((Pi.single i (1 : A)) : Fin n → A) := by
      ext i
      rw [Finset.sum_apply]
      symm
      simpa [Pi.smul_apply, Pi.single_apply] using
        (Finset.sum_eq_single i
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n ↦ y j * Pi.single j (1 : A) i)
          (fun j _ hj ↦ by simp [Pi.single_apply, hj])
          (fun hi ↦ by simp at hi))
    rw [hy, map_sum]
    refine Submodule.sum_mem (Submodule.span A (Set.range generators)) fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hg_zero_all : ∀ x : N, g • x = 0 := by
    intro x
    -- The product denominator kills the spanning family, hence the whole module.
    have hx :
        x ∈ Submodule.span A (Set.range generators) := by
      simpa [hspan]
    refine Submodule.span_induction (p := fun x _ ↦ g • x = 0) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hg_zero_generators i
    · simp
    · intro x y hx hy hx_zero hy_zero
      simp [smul_add, hx_zero, hy_zero]
    · intro a x hx hx_zero
      calc
        g • (a • x) = a • (g • x) := by
          simpa [smul_assoc] using (smul_comm g a x)
        _ = 0 := by simp [hx_zero]
  refine ⟨g, hg, ?_⟩
  -- Now one power of `g` already annihilates every element, so the away localization is trivial.
  rw [LocalizedModule.subsingleton_iff]
  intro x
  exact ⟨g, ⟨1, by simp⟩, hg_zero_all x⟩

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the kernel of the associated-graded map carries the ambient
`R`-module structure by restricting scalars from the polynomial ring. -/
noncomputable instance quasiRegularSequenceAssociatedGraded_kernel_module (xs : List R) :
    Module R (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)) :=
  Module.restrictScalars R
    (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
    (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the restricted `R`-action on the kernel is compatible with the
ambient polynomial-ring action. -/
instance quasiRegularSequenceAssociatedGraded_kernel_isScalarTower (xs : List R) :
    IsScalarTower R (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)) := by
  refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
  change ((algebraMap R (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))) r) • x =
    ((algebraMap R (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))) r) • x
  rfl

/-- Helper for Lemma 10.69.4: the kernel of the associated-graded comparison map is finite over
the polynomial ring. -/
lemma quasiRegularSequenceAssociatedGraded_kernel_finite (xs : List R) :
    Module.Finite (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)) := by
  let J : Ideal R := Ideal.ofList xs
  let A : Type u := MvPolynomial (Fin xs.length) (R ⧸ J)
  let Q : Type v := M ⧸ (J • ⊤ : Submodule R M)
  -- The quotient `M / JM` is finite over `R / J`, so its polynomial base change is finite over
  -- `A = (R / J)[X₁, ..., X_c]`.
  have hQ : Module.Finite (R ⧸ J) Q := by
    let _ : Module.Finite R Q := inferInstance
    simpa [Q] using (Module.Finite.of_restrictScalars_finite R (R ⧸ J) Q)
  let _ : Module.Finite (R ⧸ J) Q := hQ
  let _ : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  let _ : IsNoetherianRing A := inferInstance
  let _ : Module A (A ⊗[R ⧸ J] Q) := TensorProduct.leftModule
  let _ : Module A (Q ⊗[R ⧸ J] A) :=
    (TensorProduct.comm (R ⧸ J) Q A).toAddEquiv.module A
  let _ : Module.Finite A (A ⊗[R ⧸ J] Q) :=
    Module.Finite.base_change (R := R ⧸ J) (A := A) (M := Q)
  let eComm : (A ⊗[R ⧸ J] Q) ≃ₗ[A] (Q ⊗[R ⧸ J] A) :=
    (((TensorProduct.comm (R ⧸ J) Q A).toAddEquiv).linearEquiv A).symm
  have hTextbookFinite : Module.Finite A (Q ⊗[R ⧸ J] A) := by
    exact Module.Finite.equiv eComm
  let _ : Module.Finite A (Q ⊗[R ⧸ J] A) := hTextbookFinite
  have hNoetherianTextbook : IsNoetherian A (Q ⊗[R ⧸ J] A) := by
    infer_instance
  let _ : IsNoetherian A (Q ⊗[R ⧸ J] A) := hNoetherianTextbook
  have hfg :
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)).FG := by
    -- Over a Noetherian polynomial ring, every submodule of the finite source is finitely
    -- generated, so in particular the kernel is finite.
    simpa [J, A, Q] using
      (IsNoetherian.noetherian
        (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)))
  exact Module.Finite.of_fg hfg


end RingTheory.Sequence

end
