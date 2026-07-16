import StacksProject_2024.stacks_project.Chap13.Definition_13_37_1
import StacksProject_2024.stacks_project.Chap22.Lemma_22_28_2
import StacksProject_2024.stacks_project.Chap22.Lemma_22_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uA vA uB vB

section

variable {R : Type uR} [CommRing R]
variable {DA : Type uA} {DB : Type uB}
variable [Category.{vA} DA] [Category.{vB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [Linear R DA] [Linear R DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]

variable (e : DA ≌ DB)
variable [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
variable [e.functor.IsTriangulated] [e.inverse.IsTriangulated]
variable [e.functor.Linear R] [e.inverse.Linear R]
variable (Aunit : DA)

-- Semantic recall hits: `Functor.IsEquivalence` and `Equivalence.IsTriangulated` are the
-- canonical equivalence owners, while local Chapter 22 precedent states generation through
-- shifted-Hom zero detection and compatible DG actions through `CompatibleDGBimoduleStructure`.

/-- Remark 22.37.5 (1): let `R` be a ring, let `(A, d)` and `(B, d)` be differential
graded `R`-algebras, and let `F : D(A, d) ⥤ D(B, d)` be an `R`-linear equivalence of
triangulated categories. If the regular object `A` is compact in `D(A, d)`, then
`N = F(A)` is compact in `D(B, d)`. -/
@[stacks 09S9]
theorem image_compact_of_rLinearTriangulatedEquivalence
    (hACompact : IsCompactObject Aunit) :
    IsCompactObject (e.functor.obj Aunit) := sorry

/-- Remark 22.37.5 (2): under the same `R`-linear triangulated equivalence, if the regular
object `A` generates `D(A, d)` in the shifted-Hom zero-detection sense, then `N = F(A)`
generates `D(B, d)` in the corresponding sense. -/
@[stacks 09S9]
theorem image_generates_of_rLinearTriangulatedEquivalence
    (hAGenerates :
      ∀ X : DA,
        (∀ k : ℤ, ∀ f : Aunit ⟶ X⟦k⟧, f = 0) → IsZero X) :
    ∀ X : DB,
      (∀ k : ℤ, ∀ f : e.functor.obj Aunit ⟶ X⟦k⟧, f = 0) →
        IsZero X := sorry

/-- Remark 22.37.5 (3): the equivalence identifies the shifted self-Ext groups of the
regular object `A` with the shifted self-Homs of `N = F(A)`. The displayed map is the
categorical form of the source isomorphism
`H^k(A) = Hom_{D(B,d)}(N, N[k])`, using the canonical shift comparison induced by
`e.functor.commShiftIso` and `hN`. -/
@[stacks 09S9]
theorem selfExt_bijective_of_rLinearTriangulatedEquivalence
    (N : DB) (hN : e.functor.obj Aunit ≅ N) :
    ∀ k : ℤ,
      Function.Bijective
        (derivedTensorWithN_selfExtMap e.functor Aunit N hN k) := sorry

/- Remark 22.37.5 (4): to obtain an equivalence from the construction of Lemma 22.37.2, it
suffices, after replacing `N` by a quasi-isomorphic differential graded right `B`-module if
necessary, to have a compatible left differential graded `A`-module structure commuting with
the given right `B`-module structure. In the current project API, that source-facing payload is
already owned by `CompatibleDGBimoduleStructure`; the theorem below exposes its defining
commutation formula directly for downstream use. -/
@[stacks 09S9]
theorem compatibleDGBimoduleStructure_iff
    (A B : CochainDGAlgebra R)
    (M : ℤ → ModuleCat.{uR} R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1))
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A M dM)
    :
    CompatibleDGBimoduleStructure rhoB rho ↔
      ∀ (i p q : ℤ) (a : A.X i) (x : M p) (b : B.X q),
        cast (dgModuleAddAssocTargetEq M i p q)
            (rho i (p + q) a (rhoB.smul p q x b)) =
          rhoB.smul (i + p) q (rho i p a x) b :=
  Iff.rfl

/- Companion projection: a compatible DG bimodule structure acts degreewise by the commuting
left action formula. -/
theorem compatibleDGBimoduleStructure_apply
    (A B : CochainDGAlgebra R)
    (M : ℤ → ModuleCat.{uR} R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1))
    (rhoB : DifferentialGradedModule.WithFixedUnderlying B M dM)
    (rho : LeftDifferentialGradedModule.WithFixedUnderlying A M dM)
    (hcompat : CompatibleDGBimoduleStructure rhoB rho)
    (i p q : ℤ) (a : A.X i) (x : M p) (b : B.X q) :
    cast (dgModuleAddAssocTargetEq M i p q) (rho i (p + q) a (rhoB.smul p q x b)) =
      rhoB.smul (i + p) q (rho i p a x) b :=
  hcompat i p q a x b

end
