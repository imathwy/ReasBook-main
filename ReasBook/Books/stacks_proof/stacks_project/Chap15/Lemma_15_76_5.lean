import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_3_1
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_3_2
import StacksProject_2024.Chap15.Lemma_15_3_3
import StacksProject_2024.Chap15.Lemma_15_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "FiniteProjectiveClass" => finiteProjectiveModuleProperty R
local notation "FiniteStablyFreeClass" => finiteStablyFreeModuleProperty R
local notation "FiniteStablyFreeClassModI" => finiteStablyFreeModuleProperty (R ⧸ I)
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "ReduceCpx" =>
  (Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
    (ComplexShape.up ℤ))

/-- Helper for Lemma 15.76.5: finite stably free modules are finite projective after forgetting
stable freeness. -/
lemma finite_projective_of_finite_stably_free
    {A : Type*} [CommRing A] {M : ModuleCat A}
    (hM : finiteStablyFreeModuleProperty A M) :
    finiteProjectiveModuleProperty A M := by
  let _ : Module.StablyFree A M := hM.2
  -- Proof comment: stable freeness gives projectivity, and the finite-generation witness is
  -- already part of the finite-stably-free datum.
  exact ⟨hM.1, CategoryTheory.ShortComplex.stablyFree_projective (R := A) (M := M)⟩

/-- Helper for Lemma 15.76.5: a termwise finite free complex is termwise finite projective. -/
lemma finite_projective_of_termwise_finite_free
    {E : CpxR} (hE : E.IsTermwiseFiniteFree) (i : ℤ) :
    FiniteProjectiveClass (E.X i) := by
  rcases hE.out i with ⟨hfree, hfinite⟩
  -- Proof comment: forget freeness down to projectivity and keep the finite-generation witness.
  let _ : Module.Free R (E.X i) := hfree
  exact ⟨hfinite, inferInstance⟩

/-- Helper for Lemma 15.76.5: stable freeness transports across a linear equivalence once the
target module is finite stably free. -/
lemma stablyFree_of_linearEquiv
    {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N)
    [Module.Finite A N] [Module.StablyFree A N] :
    Module.StablyFree A M := by
  have hN :
      ∃ m n : ℕ, Nonempty ((N × (Fin m → A)) ≃ₗ[A] (Fin n → A)) :=
    CategoryTheory.ShortComplex.finite_stablyFree_exists_fin_stabilization (R := A) (M := N)
  have hM :
      ∃ m n : ℕ, Nonempty ((M × (Fin m → A)) ≃ₗ[A] (Fin n → A)) :=
    CategoryTheory.ShortComplex.fin_stabilization_of_equiv (R := A) (M := M) (N := N) e hN
  -- Proof comment: move the finite stabilization witness from the target back along `e`.
  exact CategoryTheory.ShortComplex.stablyFree_of_fin_stabilization (R := A) (M := M) hM

/-- Lemma 15.76.5: let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `E^•` be a
bounded-above complex of finite stably free `R/I`-modules, and let `K` be an object of `D(R)`.
Assume `K \otimes_R^{\mathbf L} R/I` is represented by `E^•`, `K` is pseudo-coherent, and
`I ⊆ \operatorname{Jac}(R)` (equivalently, every element of `1 + I` is invertible). Then there
exists a bounded-above complex `P^•` of finite stably free `R`-modules representing `K` whose
reduction modulo `I` is isomorphic to `E^•`; moreover, if `E^i` is free, then `P^i` is free. -/
@[stacks 0BCB]
theorem exists_boundedAbove_finiteStablyFree_representative_lifting_derivedReduction
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn FiniteStablyFreeClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hK : K.IsPseudoCoherent)
    (hI : I ≤ Ring.jacobson R) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteStablyFreeClass,
      ∃ eK : K ≅ DerivedCategory.Q.obj (P : CpxR),
        ∃ eE :
          ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
              (ComplexShape.up ℤ)).obj (P : CpxR)) ≅ (E : CpxRI),
          ∀ i : ℤ, Module.Free (R ⧸ I) ((E : CpxRI).X i) → Module.Free R ((P : CpxR).X i) := by
  -- Route correction: the source-faithful proof specializes Lemma `15.76.2` to
  -- `FiniteProjectiveClass`, then upgrades the lifted terms degreewise by Jacobson-radical
  -- lifting lemmas.
  --
  -- TODO: once the upstream `Lemma_15_76_1`/`Lemma_15_76_2` import chain compiles again,
  -- instantiate the generic lifting theorem with `FiniteProjectiveClass`, feed it a bounded-above
  -- finite-projective representative coming from pseudo-coherence, and then perform the
  -- degreewise Jacobson-radical upgrades back to finite stably free and free terms.
  sorry

end

end CategoryTheory
