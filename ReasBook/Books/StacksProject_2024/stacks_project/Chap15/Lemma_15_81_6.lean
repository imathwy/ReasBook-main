import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import StacksProject_2024.Chap10.Lemma_10_36_23
import StacksProject_2024.Chap15.Definition_15_81_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open TensorProduct

universe u v w x

section

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- Domain-style sampling:
- primary domain: relative finite presentation of modules over finite type / finitely presented
  algebra maps;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`,
  `Module.FinitePresentation.trans`,
  the tensor-product base-change instance for `Module.FinitePresentation`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: a single surjective polynomial presentation of `A` over `R` over which `M` is
  finitely presented;
- derived API: finite type of `A` over `R`, ordinary finite-presentation consequences, the
  algebra finite-presentation restriction-of-scalars bridge, transitivity of module finite
  presentation, and tensor-product base change for finitely presented modules.

Source/core/bridge triage:
- `source-facing`: `Module.FinitePresentationRelativeTo R A M`;
- `core/canonical`: `Module.FinitePresentation`, `Algebra.FinitePresentation`, and the canonical
  base-change / scalar-restriction theorems for finitely presented modules;
- `bridge/view`: the theorem below, which upgrades the source-facing relative statement along a
  finitely presented algebra map using those canonical owners. -/

variable {R : Type u} {A : Type v} {A' : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [CommRing A']
variable [Algebra R A] [Algebra A A']
variable [AddCommGroup M] [Module A M]

/-- Helper for Lemma 15.81.6: relative finite presentation ascends across a finitely presented
intermediate algebra in a tower. -/
theorem Module.FinitePresentationRelativeTo.trans_of_finitePresentation
    {S : Type*} [CommRing S] [Algebra R S] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
    [Algebra.FinitePresentation R S] [Module A' M]
    (hM : Module.FinitePresentationRelativeTo S A' M) :
    Module.FinitePresentationRelativeTo R A' M := by
  rcases hM with ⟨n, α, hα, hM⟩
  let P := MvPolynomial (Fin n) S
  letI : Module P M := Module.compHom M α.toRingHom
  -- Present the polynomial cover itself over `R`, then descend finite presentation along it.
  have hP : Algebra.FinitePresentation R P := by
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := R) (A := S) (Fin n))
  letI : Algebra.FinitePresentation R P := hP
  obtain ⟨m, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation R P).out
  let Q := MvPolynomial (Fin m) R
  letI : Algebra Q P := β.toRingHom.toAlgebra
  letI : Module Q P := Module.compHom P β.toRingHom
  have hQP : Module.FinitePresentation Q P := by
    -- The finitely generated kernel of the polynomial cover gives a finitely presented module cover.
    refine Module.finitePresentation_of_surjective (Algebra.linearMap Q P) hβ ?_
    simpa using hkerβ
  letI : Module.FinitePresentation Q P := hQP
  letI : Module Q M := Module.compHom M ((α.restrictScalars R).comp β).toRingHom
  letI : IsScalarTower Q P M := IsScalarTower.of_compHom Q P M
  have hαR : Function.Surjective (α.restrictScalars R) := by
    simpa using hα
  have hcomp : Function.Surjective ((α.restrictScalars R).comp β) := by
    intro x
    rcases hαR x with ⟨y, rfl⟩
    rcases hβ y with ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  -- Compose the two surjective polynomial presentations.
  refine ⟨m, (α.restrictScalars R).comp β, hcomp, ?_⟩
  exact (Module.FinitePresentation.trans Q M P : Module.FinitePresentation Q M)

/-- Helper for Lemma 15.81.6: the tensor-cover map `B ⊗[A] M → A' ⊗[A] M` is naturally
`B`-linear. -/
theorem exists_tensor_cover_linearMap {B : Type*} [CommRing B] [Algebra A B]
    (β : B →ₐ[A] A') :
    let _ : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) β.toRingHom
    ∃ ψ : (B ⊗[A] M) →ₗ[B] (A' ⊗[A] M),
      ∀ b : B, ∀ m : M, ψ (b ⊗ₜ[A] m) = β b ⊗ₜ[A] m := by
  letI : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) β.toRingHom
  let ψA : (B ⊗[A] M) →ₗ[A] (A' ⊗[A] M) :=
    TensorProduct.map β.toLinearMap (LinearMap.id : M →ₗ[A] M)
  have hsmul :
      ∀ b : B, ∀ x : B ⊗[A] M, ψA (b • x) = b • ψA x := by
    intro b x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro b' m
      calc
        ψA (b • (b' ⊗ₜ[A] m)) = ψA ((b • b') ⊗ₜ[A] m) := by
          rw [TensorProduct.smul_tmul']
        _ = ψA ((b * b') ⊗ₜ[A] m) := by
          simp [smul_eq_mul]
        _ = β (b * b') ⊗ₜ[A] m := rfl
        _ = (β b * β b') ⊗ₜ[A] m := by
          rw [map_mul]
        _ = (β b • β b') ⊗ₜ[A] m := by
          simp [smul_eq_mul]
        _ = b • (β b' ⊗ₜ[A] m) := by
          rw [← TensorProduct.smul_tmul']
          rfl
    · intro x y hx hy
      simp [hx, hy]
  refine ⟨
    { toFun := ψA
      map_add' := ψA.map_add
      map_smul' := hsmul },
    ?_⟩
  intro b m
  rfl

/-- Helper for Lemma 15.81.6: the chosen `B`-linear tensor-cover map sends pure tensors to the
expected pure tensors. -/
noncomputable abbrev tensor_cover_linearMap {B : Type*} [CommRing B] [Algebra A B]
    (β : B →ₐ[A] A') :
    let _ : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) β.toRingHom
    (B ⊗[A] M) →ₗ[B] (A' ⊗[A] M) :=
  letI : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) β.toRingHom
  Classical.choose (exists_tensor_cover_linearMap (A := A) (A' := A') (M := M) β)

/-- Helper for Lemma 15.81.6: on pure tensors, the chosen `B`-linear tensor-cover map is the
obvious coefficientwise map. -/
theorem tensor_cover_linearMap_apply_tmul {B : Type*} [CommRing B] [Algebra A B]
    (β : B →ₐ[A] A') (b : B) (m : M) :
    tensor_cover_linearMap (A := A) (A' := A') (M := M) β (b ⊗ₜ[A] m) = β b ⊗ₜ[A] m :=
  by
    letI : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) β.toRingHom
    simpa using
      (Classical.choose_spec (exists_tensor_cover_linearMap (A := A) (A' := A') (M := M) β) b m)

/-- Helper for Lemma 15.81.6: tensoring a surjective coefficient map with the identity on `M`
stays surjective. -/
theorem tensor_cover_linearMap_surjective {B : Type*} [CommRing B] [Algebra A B]
    (β : B →ₐ[A] A') (hβ : Function.Surjective β) :
    Function.Surjective (tensor_cover_linearMap (A := A) (A' := A') (M := M) β) := by
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp [tensor_cover_linearMap]⟩
  · intro a' m
    rcases hβ a' with ⟨b, rfl⟩
    exact ⟨b ⊗ₜ[A] m, tensor_cover_linearMap_apply_tmul (A := A) (A' := A') (M := M) β b m⟩
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨x₁, rfl⟩
    rcases hz₂ with ⟨x₂, rfl⟩
    exact ⟨x₁ + x₂, by simp⟩

/-- Helper for Lemma 15.81.6: after restricting scalars along an algebra map `Q → B`, every
`B`-linear map is automatically compatible with the induced `Q`-action. -/
private theorem linearMap_compHom_compatibleSmul
    {Q : Type*} {B : Type*} [CommRing Q] [CommRing B] [Algebra Q B]
    {X : Type*} {Y : Type*}
    [AddCommMonoid X] [AddCommMonoid Y]
    [Module B X] [Module B Y] :
    let _ : Module Q X := Module.compHom X (algebraMap Q B)
    let _ : Module Q Y := Module.compHom Y (algebraMap Q B)
    LinearMap.CompatibleSMul X Y Q B := by
  let _ : Module Q X := Module.compHom X (algebraMap Q B)
  let _ : Module Q Y := Module.compHom Y (algebraMap Q B)
  refine ⟨?_⟩
  intro f q x
  exact f.map_smul ((algebraMap Q B) q) x

/-- Helper for Lemma 15.81.6: the target tensor module is finitely presented over `B` once the
coefficient cover `β : B →ₐ[A] A'` is surjective with finitely generated kernel. -/
private theorem tensor_cover_target_finitePresentation_of_surjective
    {B : Type*} [CommRing B] [Algebra A B]
    (β : B →ₐ[A] A') (hβ : Function.Surjective β) (hkerβ : (RingHom.ker β.toRingHom).FG)
    (hAM : Module.FinitePresentation A M) :
    let _ : Algebra B A' := β.toRingHom.toAlgebra
    let _ : Module B A' := Module.compHom A' (algebraMap B A')
    let _ : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) (algebraMap B A')
    let _ : IsScalarTower B A' (A' ⊗[A] M) := IsScalarTower.of_compHom B A' (A' ⊗[A] M)
    Module.FinitePresentation B (A' ⊗[A] M) := by
  letI : Algebra B A' := β.toRingHom.toAlgebra
  letI : Module B A' := Module.compHom A' (algebraMap B A')
  letI : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) (algebraMap B A')
  letI : IsScalarTower B A' (A' ⊗[A] M) := IsScalarTower.of_compHom B A' (A' ⊗[A] M)
  letI : Module.FinitePresentation A M := hAM
  letI : Module.FinitePresentation A' (A' ⊗[A] M) := by
    infer_instance
  have hBA'finite : Module.Finite B A' := Module.Finite.of_surjective (Algebra.linearMap B A') <| by
    change Function.Surjective β
    simpa using hβ
  have hBA'fp : Algebra.FinitePresentation B A' := by
    let g : B →ₐ[B] A' := Algebra.ofId B A'
    have hg : Function.Surjective g := by
      simpa [g] using hβ
    have hgker : (RingHom.ker g.toRingHom).FG := by
      simpa [g] using hkerβ
    exact Algebra.FinitePresentation.of_surjective (f := g) hg hgker
  have hA'tensor : Module.FinitePresentation A' (A' ⊗[A] M) := inferInstance
  exact
    (@Module.FinitePresentation.iff_of_finite_finitePresentation
      B A' (A' ⊗[A] M) _ _ _ _ _ _ _ hBA'finite hBA'fp).mpr hA'tensor

/-- Helper for Lemma 15.81.6: the kernel of the `B`-linear tensor-cover map is finitely generated
once the ring-theoretic kernel ideal is finitely generated. -/
theorem tensor_cover_linearMap_kernel_fg {B : Type*} [CommRing B] [Algebra A B]
    (β : B →ₐ[A] A') (hβ : Function.Surjective β) (hkerβ : (RingHom.ker β.toRingHom).FG)
    (hAM : Module.FinitePresentation A M) :
    let _ : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) β.toRingHom
    (LinearMap.ker (tensor_cover_linearMap (A := A) (A' := A') (M := M) β)).FG := by
  letI : Module.FinitePresentation A M := hAM
  letI : Module.FinitePresentation B (B ⊗[A] M) := by
    infer_instance
  letI : Algebra B A' := β.toRingHom.toAlgebra
  letI : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) (algebraMap B A')
  letI : IsScalarTower B A' (A' ⊗[A] M) := IsScalarTower.of_compHom B A' (A' ⊗[A] M)
  have htarget : Module.FinitePresentation B (A' ⊗[A] M) :=
    tensor_cover_target_finitePresentation_of_surjective
      (A := A) (A' := A') (M := M) β hβ hkerβ hAM
  exact
    @Module.FinitePresentation.fg_ker B (B ⊗[A] M) (A' ⊗[A] M)
      _ _ inferInstance _ _ inferInstance htarget
      (tensor_cover_linearMap (A := A) (A' := A') (M := M) β)
      (tensor_cover_linearMap_surjective (A := A) (A' := A') (M := M) β hβ)

/-- Helper for Lemma 15.81.6: after restricting scalars along a surjective algebra map and then
pulling back through a linear equivalence, finite generation of a kernel is preserved. -/
theorem kernel_fg_of_comp_restrictScalars_linearEquiv
    {Q : Type*} {B : Type*} [CommRing Q] [CommRing B] [Algebra Q B]
    {U : Type*} {X : Type*} {Y : Type*}
    [AddCommGroup U] [AddCommGroup X] [AddCommGroup Y]
    [Module Q U] [Module B X] [Module B Y]
    [Module Q X] [IsScalarTower Q B X]
    [Module Q Y] [IsScalarTower Q B Y]
    [LinearMap.CompatibleSMul X Y Q B]
    (hq : Function.Surjective (algebraMap Q B))
    (e : U ≃ₗ[Q] X) (ψ : X →ₗ[B] Y)
    (hker : (LinearMap.ker ψ).FG) :
    (LinearMap.ker ((ψ.restrictScalars Q).comp e.toLinearMap)).FG := by
  have hkerQ₀ : (Submodule.restrictScalars Q (LinearMap.ker ψ)).FG := by
    -- Restrict finite generation of the kernel along the surjective algebra map `Q → B`.
    exact Submodule.FG.restrictScalars_of_surjective hker hq
  have hkerQ : (LinearMap.ker (ψ.restrictScalars Q)).FG := by
    simpa [LinearMap.ker_restrictScalars Q ψ] using hkerQ₀
  have hpull :
      Submodule.map e.symm.toLinearMap (LinearMap.ker (ψ.restrictScalars Q)) =
        LinearMap.ker ((ψ.restrictScalars Q).comp e.toLinearMap) := by
    -- Pulling back the kernel across the linear equivalence is just the standard map/comap
    -- description of kernels of composites.
    calc
      Submodule.map e.symm.toLinearMap (LinearMap.ker (ψ.restrictScalars Q)) =
          Submodule.comap e.toLinearMap (LinearMap.ker (ψ.restrictScalars Q)) := by
            simpa using
              (Submodule.map_equiv_eq_comap_symm e.symm (LinearMap.ker (ψ.restrictScalars Q)))
      _ = LinearMap.ker ((ψ.restrictScalars Q).comp e.toLinearMap) := by
            rw [LinearMap.ker_comp]
  -- Map the already finitely generated kernel across the inverse equivalence, then rewrite it as
  -- the kernel of the composite.
  exact hpull ▸ Submodule.FG.map e.symm.toLinearMap hkerQ

/-- Helper for Lemma 15.81.6: if a `Q`-linear map is identified with the scalar restriction of a
`B`-linear map, then pulling its kernel back across a `Q`-linear equivalence preserves finite
generation. -/
theorem kernel_fg_of_comp_linearMap_of_eq_restrictScalars
    {Q : Type*} {B : Type*} [CommRing Q] [CommRing B] [Algebra Q B]
    {U : Type*} {X : Type*} {Y : Type*}
    [AddCommGroup U] [AddCommGroup X] [AddCommGroup Y]
    [Module Q U] [Module B X] [Module B Y]
    [Module Q X] [IsScalarTower Q B X]
    [Module Q Y] [IsScalarTower Q B Y]
    [LinearMap.CompatibleSMul X Y Q B]
    (hq : Function.Surjective (algebraMap Q B))
    (e : U ≃ₗ[Q] X) (ψ : X →ₗ[B] Y) (ψQ : X →ₗ[Q] Y)
    (hψQ : ψQ = ψ.restrictScalars Q)
    (hker : (LinearMap.ker ψ).FG) :
    (LinearMap.ker (ψQ.comp e.toLinearMap)).FG := by
  simpa [hψQ] using
    kernel_fg_of_comp_restrictScalars_linearEquiv
      (Q := Q) (B := B) (U := U) (X := X) (Y := Y) hq e ψ hker

/-- Helper for Lemma 15.81.6: a `Q`-linear map with the same underlying function as the scalar
restriction of a `B`-linear map has the same kernel pullback across a `Q`-linear equivalence. -/
theorem kernel_fg_of_comp_linearMap_of_toFun_eq
    {Q : Type*} {B : Type*} [CommRing Q] [CommRing B] [Algebra Q B]
    {U : Type*} {X : Type*} {Y : Type*}
    [AddCommGroup U] [AddCommGroup X] [AddCommGroup Y]
    [Module Q U] [Module B X] [Module B Y]
    [Module Q X] [IsScalarTower Q B X]
    [Module Q Y] [IsScalarTower Q B Y]
    [LinearMap.CompatibleSMul X Y Q B]
    (hq : Function.Surjective (algebraMap Q B))
    (e : U ≃ₗ[Q] X) (ψ : X →ₗ[B] Y) (ψQ : X →ₗ[Q] Y)
    (hψQ : ∀ x, ψQ x = ψ x)
    (hker : (LinearMap.ker ψ).FG) :
    (LinearMap.ker (ψQ.comp e.toLinearMap)).FG := by
  have hψQ' : ψQ = ψ.restrictScalars Q := by
    ext x
    exact hψQ x
  exact
    kernel_fg_of_comp_linearMap_of_eq_restrictScalars
      (Q := Q) (B := B) (U := U) (X := X) (Y := Y) hq e ψ ψQ hψQ' hker

/-- Helper for Lemma 15.81.6: finite presentation over one surjective polynomial cover already
descends to finite presentation over the target algebra. -/
theorem finitePresentation_of_surjective_polynomial_cover
    {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (hPM :
      let P := MvPolynomial (Fin n) R
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M) :
    Module.FinitePresentation A M := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : Algebra.FiniteType P A := by
    -- The surjective polynomial presentation exhibits `A` as finite type over `P`.
    have hα' : Function.Surjective (algebraMap P A) := by
      change Function.Surjective α
      simpa using hα
    rw [← RingHom.finiteType_algebraMap]
    exact RingHom.FiniteType.of_surjective (algebraMap P A) hα'
  letI : Module.FinitePresentation P M := by
    simpa [P] using hPM
  -- Descend finite presentation along the finite type algebra `P → A`.
  exact Module.FinitePresentation.of_restrictScalars_finiteType P

/-- Helper for Lemma 15.81.6: once the source module is finitely presented over the actual
algebra `A`, base change along the finitely presented map `A → A'` keeps it finitely presented. -/
theorem tensor_baseChange_finitePresentation_of_surjective_polynomial_cover
    {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (hPM :
      let P := MvPolynomial (Fin n) R
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M) :
    Module.FinitePresentation A' (A' ⊗[A] M) := by
  letI : Module.FinitePresentation A M :=
    finitePresentation_of_surjective_polynomial_cover (R := R) (A := A) (M := M) α hα hPM
  -- The standard tensor-product instance handles base change along a finitely presented algebra.
  infer_instance

/-- Helper for Lemma 15.81.6: adjoining the presentation variables for `A'` over `A` and then
composing with a polynomial presentation of `A` over `R` still gives a surjective polynomial
presentation of `A'` over `R`. -/
theorem iterated_polynomial_tensor_cover_surjective
    {n m : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (β : MvPolynomial (Fin m) A →ₐ[A] A') (hβ : Function.Surjective β) :
    let P := MvPolynomial (Fin n) R
    let _ : Algebra P A := α.toAlgebra
    let _ : Algebra P A' := ((algebraMap A A').comp α.toRingHom).toAlgebra
    let _ : IsScalarTower P A A' := IsScalarTower.of_algebraMap_eq' rfl
    let Q := MvPolynomial (Fin m) P
    let qR : Q →ₐ[P] MvPolynomial (Fin m) A := MvPolynomial.mapAlgHom (Algebra.ofId P A)
    Function.Surjective ((β.restrictScalars P).comp qR) := by
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin m) P
  letI : Algebra P A := α.toAlgebra
  letI : Algebra P A' := ((algebraMap A A').comp α.toRingHom).toAlgebra
  letI : IsScalarTower P A A' := IsScalarTower.of_algebraMap_eq' rfl
  let qR : Q →ₐ[P] MvPolynomial (Fin m) A := MvPolynomial.mapAlgHom (Algebra.ofId P A)
  -- Lift first through the finitely presented polynomial cover of `A'`, then through the
  -- polynomial pushout cover of `MvPolynomial (Fin m) A`.
  change Function.Surjective ((β.restrictScalars P).comp qR)
  intro t
  rcases hβ t with ⟨y, rfl⟩
  rcases (show Function.Surjective qR by
      simpa [qR, Algebra.ofId] using
        MvPolynomial.map_surjective (Algebra.ofId P A).toRingHom hα) y with ⟨z, rfl⟩
  exact ⟨z, rfl⟩

/-- Helper for Lemma 15.81.6: adjoining new polynomial variables to the chosen presentation
`P → A` gives the canonical pushout square `P → A`, `P → Q`, `A → B`, `Q → B`. -/
theorem iterated_polynomial_pushout_isPushout
    {n m : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    let P := MvPolynomial (Fin n) R
    let Q := MvPolynomial (Fin m) P
    let B := MvPolynomial (Fin m) A
    let _ : Algebra P A := α.toAlgebra
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R A r = α (algebraMap R P r)
      exact (α.commutes r).symm
    Algebra.IsPushout P A Q B := by
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin m) P
  let B := MvPolynomial (Fin m) A
  letI : Algebra P A := α.toAlgebra
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  -- `Mathlib` already identifies polynomial extension with the pushout of the coefficient ring.
  infer_instance

/-- Helper for Lemma 15.81.6: the polynomial pushout square identifies the abstract base change
`Q ⊗[P] M` with the genuine coefficient-extension module `B ⊗[A] M`. -/
noncomputable def iterated_polynomial_pushout_module_equiv_qlinear
    {n m : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) :
    let P := MvPolynomial (Fin n) R
    let Q := MvPolynomial (Fin m) P
    let B := MvPolynomial (Fin m) A
    let _ : Algebra P A := α.toAlgebra
    let _ : Module P M := Module.compHom M α.toRingHom
    let _ : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R A r = α (algebraMap R P r)
      exact (α.commutes r).symm
    let _ : IsScalarTower P A M := IsScalarTower.of_compHom P A M
    let _ : Algebra.IsPushout P A Q B := iterated_polynomial_pushout_isPushout α
    (Q ⊗[P] M) ≃ₗ[Q] (B ⊗[A] M) := by
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin m) P
  let B := MvPolynomial (Fin m) A
  letI : Algebra P A := α.toAlgebra
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A r = α (algebraMap R P r)
    exact (α.commutes r).symm
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  letI : Algebra.IsPushout P A Q B := iterated_polynomial_pushout_isPushout α
  -- Use the built-in `cancelBaseChange` equivalence for the actual pushout square.
  simpa [Q, B] using
    ((Algebra.IsPushout.cancelBaseChange (R := P) (S := Q) (A := A) (B := B) M).symm)

/-- Helper for Lemma 15.81.6: after adjoining the presentation variables for `A'` over `A`,
the induced polynomial cover over `P := R[x_1, ..., x_n]` should give the relative finite
presentation witness for `A' ⊗[A] M`. This isolates the remaining tensor-kernel transport step
from the final transitivity packaging back to `R`. -/
theorem iterated_polynomial_tensor_cover_relativeTo_polynomial
    {n m : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] A) (hα : Function.Surjective α)
    (β : MvPolynomial (Fin m) A →ₐ[A] A') (hβ : Function.Surjective β)
    (hkerβ : (RingHom.ker β.toRingHom).FG)
    (hPM :
      let P := MvPolynomial (Fin n) R
      let _ : Module P M := Module.compHom M α.toRingHom
      Module.FinitePresentation P M) :
    let P := MvPolynomial (Fin n) R
    let _ : Algebra P A := α.toAlgebra
    let _ : Algebra P A' := ((algebraMap A A').comp α.toRingHom).toAlgebra
    let _ : IsScalarTower P A A' := IsScalarTower.of_algebraMap_eq' rfl
    Module.FinitePresentationRelativeTo P A' (A' ⊗[A] M) := by
  let P := MvPolynomial (Fin n) R
  let Q := MvPolynomial (Fin m) P
  let B := MvPolynomial (Fin m) A
  letI : Algebra P A := α.toAlgebra
  letI : Algebra P A' := ((algebraMap A A').comp α.toRingHom).toAlgebra
  letI : IsScalarTower P A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module P M := Module.compHom M α.toRingHom
  letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  let qR : Q →ₐ[P] B := MvPolynomial.mapAlgHom (Algebra.ofId P A)
  letI : Module Q (A' ⊗[A] M) := Module.compHom _ (((β.restrictScalars P).comp qR).toRingHom)
  have hAM : Module.FinitePresentation A M := by
    letI : Algebra.FiniteType P A := by
      -- The chosen surjection `P → A` makes `A` finite type over the polynomial base `P`.
      have hα' : Function.Surjective (algebraMap P A) := by
        change Function.Surjective α
        simpa using hα
      rw [← RingHom.finiteType_algebraMap]
      exact RingHom.FiniteType.of_surjective (algebraMap P A) hα'
    letI : Module.FinitePresentation P M := by
      simpa [P] using hPM
    -- Forget the relative packaging and descend to the actual algebra `A`.
    exact Module.FinitePresentation.of_restrictScalars_finiteType P
  have hA'M : Module.FinitePresentation A' (A' ⊗[A] M) := by
    -- Before handling the relative `P`-presentation, record the ordinary finite-presentation
    -- statement over the actual algebra `A'`.
    letI : Module.FinitePresentation A M := hAM
    infer_instance
  --
  refine ⟨m, (β.restrictScalars P).comp qR, ?_, ?_⟩
  · -- The source-faithful polynomial pushout cover is surjective by successive lifting.
    simpa using iterated_polynomial_tensor_cover_surjective α hα β hβ
  · -- The remaining blocker is exactly the kernel computation/transport for this `Q`-linear map.
    letI : Algebra Q B := qR.toRingHom.toAlgebra
    letI : Module Q (B ⊗[A] M) := Module.compHom (B ⊗[A] M) qR.toRingHom
    letI : IsScalarTower Q B (B ⊗[A] M) := IsScalarTower.of_compHom Q B (B ⊗[A] M)
    letI : Algebra B A' := β.toRingHom.toAlgebra
    letI : Module B (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) (algebraMap B A')
    letI : Module Q (A' ⊗[A] M) := Module.compHom (A' ⊗[A] M) (algebraMap Q B)
    letI : IsScalarTower B A' (A' ⊗[A] M) := IsScalarTower.of_compHom B A' (A' ⊗[A] M)
    letI : IsScalarTower Q B (A' ⊗[A] M) := IsScalarTower.of_compHom Q B (A' ⊗[A] M)
    letI : LinearMap.CompatibleSMul (B ⊗[A] M) (A' ⊗[A] M) Q B :=
      linearMap_compHom_compatibleSmul
        (Q := Q) (B := B) (X := B ⊗[A] M) (Y := A' ⊗[A] M)
    let eQ := iterated_polynomial_pushout_module_equiv_qlinear
      (R := R) (A := A) (M := M) (m := m) α
    have hqR : Function.Surjective (algebraMap Q B) := by
      -- The polynomial pushout map is surjective because it acts coefficientwise via `α`.
      change Function.Surjective qR
      simpa [qR, Algebra.ofId] using
        MvPolynomial.map_surjective (Algebra.ofId P A).toRingHom hα
    have hQTensorSource : Module.FinitePresentation Q (Q ⊗[P] M) := by
      letI : Module.FinitePresentation P M := by
        simpa [P] using hPM
      -- Adjoining the extra polynomial variables keeps the source tensor module finitely
      -- presented over `Q`.
      infer_instance
    letI : Module.FinitePresentation Q (Q ⊗[P] M) := hQTensorSource
    let ψ : (B ⊗[A] M) →ₗ[B] (A' ⊗[A] M) :=
      tensor_cover_linearMap (A := A) (A' := A') (M := M) β
    let ψQ : (B ⊗[A] M) →ₗ[Q] (A' ⊗[A] M) :=
      { toFun := ψ
        map_add' := ψ.map_add
        map_smul' := by
          intro q x
          change ψ ((algebraMap Q B q) • x) = q • ψ x
          rw [ψ.map_smul]
          rfl }
    let π : (Q ⊗[P] M) →ₗ[Q] (A' ⊗[A] M) := ψQ.comp eQ.toLinearMap
    have hψsurj : Function.Surjective ψ := by
      -- Tensoring the surjective cover `β` with the identity on `M` stays surjective.
      exact tensor_cover_linearMap_surjective β hβ
    have hψker : (LinearMap.ker ψ).FG := by
      -- Both the source and the target are finitely presented over `B`, so the kernel of the
      -- surjective tensor-cover map is finitely generated.
      simpa [ψ] using
        tensor_cover_linearMap_kernel_fg (A := A) (A' := A') (M := M) β hβ hkerβ hAM
    have hπsurj : Function.Surjective π := by
      -- First solve on the `B`-side, then pull the preimage back through the pushout
      -- equivalence `eQ`.
      intro z
      rcases hψsurj z with ⟨x, rfl⟩
      refine ⟨eQ.symm x, ?_⟩
      change ψQ (eQ (eQ.symm x)) = ψ x
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hπker : (LinearMap.ker π).FG := by
      -- Restrict the finitely generated `B`-side kernel along the surjective `Q → B` and pull it
      -- back across the canonical pushout equivalence.
      simpa [π] using
        @kernel_fg_of_comp_linearMap_of_toFun_eq
          Q B _ _ _ (Q ⊗[P] M) (B ⊗[A] M) (A' ⊗[A] M)
          _ _ _ inferInstance inferInstance inferInstance
          (Module.compHom (B ⊗[A] M) qR.toRingHom)
          (IsScalarTower.of_compHom Q B (B ⊗[A] M))
          (Module.compHom (A' ⊗[A] M) (algebraMap Q B))
          (IsScalarTower.of_compHom Q B (A' ⊗[A] M))
          (linearMap_compHom_compatibleSmul
            (Q := Q) (B := B) (X := B ⊗[A] M) (Y := A' ⊗[A] M))
          hqR eQ ψ ψQ (fun z ↦ rfl) hψker
    -- Route correction: build the `Q`-presentation map directly from the pushout equivalence and
    -- the genuine tensor cover over `β`, then apply the standard finitely presented quotient
    -- criterion.
    simpa [π] using
      (@Module.finitePresentation_of_surjective Q (Q ⊗[P] M) (A' ⊗[A] M)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        π hπsurj hπker :
          Module.FinitePresentation Q (A' ⊗[A] M))

variable [Algebra R A'] [IsScalarTower R A A'] [Algebra.FinitePresentation A A']

-- Proof sketch: start from the owner predicate
-- `Module.FinitePresentationRelativeTo R A M`, derive the finite-type `R`-algebra structure on
-- `A` from that witness, then compare the chosen polynomial presentation with a finitely
-- presented polynomial presentation of `A'` over `A`. The module-theoretic input should stay on
-- the canonical owners `Module.FinitePresentation` and `Algebra.FinitePresentation`, using the
-- standard tensor-product finite-presentation instance and the scalar-restriction/transitivity
-- bridges from Chapter 10 rather than any parallel local wrapper. The only new mathematical
-- content here is the source-facing relative reformulation over `R`, not a new owner for finite
-- presentation.
/-- Lemma 15.81.6: let `M` be an `A`-module finitely presented relative to `R`, and let
`A → A'` be a ring map of finite presentation. Then the base-changed `A'`-module `A' ⊗[A] M`,
canonically identified with the textbook module `M ⊗[A] A'`, is finitely presented relative to
`R`. -/
theorem Module.finitePresentationRelativeTo_baseChange_of_finitePresentation
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R A' (A' ⊗[A] M) := by
  rcases hM with ⟨n, α, hα, hPM⟩
  -- Choose a finitely presented polynomial cover of `A'` over `A`.
  obtain ⟨m, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation A A').out
  let P := MvPolynomial (Fin n) R
  letI : Algebra P A := α.toAlgebra
  letI : Algebra P A' := ((algebraMap A A').comp α.toRingHom).toAlgebra
  letI : IsScalarTower R P A' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R A' r = algebraMap A A' (α (algebraMap R P r))
    rw [α.commutes, IsScalarTower.algebraMap_apply R A A' r]
  letI : IsScalarTower P A A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FinitePresentation R P := by
    -- The polynomial presentation ring `P` is finitely presented over `R`.
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := R) (A := R) (Fin n))
  have hPbase :
      Module.FinitePresentationRelativeTo P A' (A' ⊗[A] M) := by
    -- Route correction: isolate the genuine `P`-relative tensor-presentation step first, and
    -- only then compose back to the original base `R`.
    simpa [P] using
      iterated_polynomial_tensor_cover_relativeTo_polynomial α hα β hβ hkerβ hPM
  exact Module.FinitePresentationRelativeTo.trans_of_finitePresentation
    (R := R) (S := P) (A' := A') (M := A' ⊗[A] M) hPbase

end
