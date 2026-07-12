import StacksProject_2024.Chap20.Lemma_20_35_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

noncomputable section

universe u

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A) (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
variable (idealPowerCohomology : ℕ → Type u)

-- Route correction: use the canonical Chapter 20 kernel-filtration API directly rather than a
-- theorem-local fallback copy. The source-faithful route is still the short Noetherian-transfer
-- argument from the source graded object to the intrinsic associated graded of the limit.
-- Proof sketch: transfer the Noetherian hypothesis from the source cohomological graded object
-- `⨁ n, idealPowerCohomology n` to the intrinsic kernel associated graded of
-- `limit cohomologySystem` via the surjective comparison map, then invoke the Chapter 20 owner
-- theorem on the kernel filtration.
/-- Lemma 21.22.3: let `idealPowerCohomology n` denote the source cohomological graded piece in
degree `n`, and assume the graded direct sum `⨁ n : ℕ, idealPowerCohomology n` is Noetherian
over the associated graded ring `idealAssociatedGradedRing I`, whose degree-`n` piece is
`I ^ n ⧸ I ^ (n + 1)`. If the kernel filtration on
`limit cohomologySystem` is `I`-compatible and a surjective `gr_I(A)`-linear comparison map from
`⨁ n : ℕ, idealPowerCohomology n` to the intrinsic graded module
`inverseLimitKernelAssociatedGraded I cohomologySystem hI` is given, and the target carries the
canonical homogeneous-action instance
`[SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
  (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]`, then the
inverse-limit topology on `inverseLimitModule cohomologySystem` is the `I`-adic topology. -/
@[stacks 0GYS]
lemma cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded
    [∀ n, AddCommGroup (idealPowerCohomology n)]
    [Module (idealAssociatedGradedRing I)
      (⨁ n : ℕ, idealPowerCohomology n)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (⨁ n : ℕ, idealPowerCohomology n)]
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]
    (idealPowerCohomologyToKernelAssociatedGraded :
      inverseLimitKernelAssociatedGradedHom I cohomologySystem hI
        (⨁ n : ℕ, idealPowerCohomology n))
    (hSurj : Function.Surjective idealPowerCohomologyToKernelAssociatedGraded) :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I (inverseLimitModule cohomologySystem) := by
  -- The surjective comparison identifies the intrinsic associated graded as a Noetherian quotient
  -- of the source direct sum.
  let _ : IsNoetherian (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI) :=
    isNoetherian_of_surjective idealPowerCohomologyToKernelAssociatedGraded
      (LinearMap.range_eq_top.2 hSurj)
  -- Once the intrinsic associated graded is Noetherian, the topology comparison is exactly the
  -- Chapter 20 owner theorem.
  exact inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded
    I cohomologySystem hI

end

end CategoryTheory
