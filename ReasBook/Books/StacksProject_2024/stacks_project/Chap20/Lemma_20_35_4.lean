import StacksProject_2024.Chap21.Lemma_21_22_2
import StacksProject_2024.Chap21.Lemma_21_22_3

open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u}}
variable {A : Type u} [CommRing A]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ (ModuleCat A) AddCommGrpCat)]

local notation "ModSheaf" => Sheaf (Opens.grothendieckTopology X) (ModuleCat A)

/-
Domain-style sampling for Lemma 20.35.4:
- primary domain: inverse-limit topologies on cohomology towers of sheaves of `A`-modules,
  compared with the `I`-adic topology through the eventual-range pieces `N_n`;
- sampled owner declarations:
  * `siteModuleCohomologyTower`;
  * `siteModuleCohomologyIdealPowerEventualRange`;
  * `siteModuleCohomologyIdealPowerEventualRangeDirectSum`;
  * `inverseLimitTopology`;
  * `inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded`.
- source/core/bridge triage:
  * `source-facing`: the eventual-range graded object `⨁ n, N_n`, with
    `N_n = siteModuleCohomologyIdealPowerEventualRange powSheaf p n`;
  * `core/canonical`: the Chapter 20 owners `inverseLimitTopology`,
    `inverseLimitKernelIdealFiltration I cohomologySystem hI` with its graded module, and the
    intrinsic topology comparison theorem
    `inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded`;
  * `bridge/view`: this topological-space specialization from the source eventual-range object to
    the intrinsic kernel-associated-graded criterion.
-/

-- Proof sketch: this Chapter 20 source-facing statement is the eventual-range specialization of
-- the canonical Chapter 21 bridge theorem on a Noetherian source associated graded.
/-- Lemma 20.35.4: let `N_n` be the eventual-range pieces from Lemma `20.35.2`, and suppose the
graded direct sum `⨁ n, N_n` is Noetherian over the associated graded ring `⨁ n, I^n / I^(n + 1)`.
If the kernel filtration on the inverse limit of `cohomologySystem = (M_n)_n` is `I`-compatible,
and if a surjective `gr_I(A)`-linear comparison map from the canonical source direct sum
`siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p` to the intrinsic associated
graded object `inverseLimitKernelAssociatedGraded I cohomologySystem hI` of that kernel
filtration is given, and the target carries the canonical homogeneous-action instance
`[SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
  (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]`, then the inverse-limit
topology on `inverseLimitModule cohomologySystem` is the `I`-adic topology. This is the
source-facing bridge from the eventual-range object to the intrinsic kernel-associated-graded
criterion. -/
@[stacks 0GYN]
theorem topologicalSpace_moduleCohomology_inverseLimitTopology_eq_adicModuleTopology_of_idealPower_eventualRange_ascending_chain_condition
    (I : Ideal A)
    (cohomologySystem : SequentialInverseSystem (ModuleCat.{u} A))
    (powSheaf : ℕ → SequentialInverseSystem ModSheaf)
    (p : ℕ)
    [Module (idealAssociatedGradedRing I)
      (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p)]
    (hI : inverseLimitKernelFiltrationIdealCompatible I cohomologySystem)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded I cohomologySystem hI)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (inverseLimitKernelAssociatedGradedGrading I cohomologySystem hI)]
    (eventualRangeToKernelAssociatedGraded :
      inverseLimitKernelAssociatedGradedHom I cohomologySystem hI
        (siteModuleCohomologyIdealPowerEventualRangeDirectSum powSheaf p))
    (hSurj : Function.Surjective eventualRangeToKernelAssociatedGraded) :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I (inverseLimitModule cohomologySystem) := by
  simpa [siteModuleCohomologyIdealPowerEventualRangeDirectSum] using
    (cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_associatedGraded
      I cohomologySystem
      (fun n ↦ siteModuleCohomologyIdealPowerEventualRange powSheaf p n)
      hI eventualRangeToKernelAssociatedGraded hSurj)

end

end CategoryTheory
