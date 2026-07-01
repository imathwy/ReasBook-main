import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-- The quotient-Rees model of the associated graded ring `⊕_{n ≥ 0} I^n / I^(n + 1)` of an
ideal `I`. -/
abbrev idealAssociatedGradedRing (I : Ideal A) : Type u :=
  (reesAlgebra I) ⧸ Ideal.map (algebraMap A (reesAlgebra I)) I

/-- The topology on the inverse limit of a sequential system of `A`-modules induced from the
product of the discrete quotient modules. -/
abbrev inverseLimitTopology (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) :
    TopologicalSpace ↥(limit cohomologySystem) :=
  let _ : (n : ℕ) → TopologicalSpace ↥(cohomologySystem.obj (op n)) := fun _ ↦ ⊥
  TopologicalSpace.induced
    (fun x : ↥(limit cohomologySystem) ↦
      fun n : ℕ ↦ ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)))
    inferInstance

/-- For a fixed `n`, this is the submodule
`⋂_{m ≥ n} \operatorname{Im}(H^p(\mathcal C, I^n \mathcal F_{m + 1}) → H^p(\mathcal C, I^n \mathcal F_{n + 1}))`
attached to the inverse system `idealPowerTower n`. -/
abbrev cohomologyIdealPowerEventualImageSubmodule
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    Submodule A ((idealPowerTower n).obj (op n)) :=
  ⨅ m : Set.Ici n,
    LinearMap.range (((idealPowerTower n).map (homOfLE m.2).op).hom)

/-- The graded direct sum `⊕_n N_n` of the eventual-image submodules attached to the tower
`idealPowerTower`. -/
abbrev cohomologyIdealPowerEventualImageDirectSum
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A) : Type u :=
  DirectSum ℕ fun n ↦ cohomologyIdealPowerEventualImageSubmodule idealPowerTower n

-- Proof sketch: apply Lemma `21.22.3` to the kernel filtration on
-- `lim_n H^p(\mathcal C, \mathcal F_n)`. The hypothesis that `⊕_n N_n` is Noetherian over the
-- associated graded ring provides the graded ACC input, while
-- `hKernelFiltrationControlledByEventualImages` records the source argument that the graded pieces
-- of the kernel filtration are controlled by the images of the `N_n`.
/-- Lemma 21.22.4: let `cohomologySystem` model the inverse system
`n ↦ H^p(\mathcal C, \mathcal F_n)` and let `idealPowerTower n` model the fixed-`n` tower
`m ↦ H^p(\mathcal C, I^n \mathcal F_{m + 1})`. For each `n`, write
`N_n = cohomologyIdealPowerEventualImageSubmodule idealPowerTower n`, i.e. the intersection of
the images of the transition maps into stage `n`. If the graded direct sum `⊕_n N_n` is
Noetherian over the associated graded ring `⊕_{n \ge 0} I^n / I^{n + 1}`, and if the source
comparison between the kernel filtration on `lim_n H^p(\mathcal C, \mathcal F_n)` and the images
of the `N_n` is encoded by the hypothesis
`hKernelFiltrationControlledByEventualImages`, then the inverse-limit topology on
`lim_n H^p(\mathcal C, \mathcal F_n)` is the `I`-adic topology. -/
lemma cohomology_inverseLimitTopology_eq_adicModuleTopology_of_noetherian_eventualImages
    (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    (idealPowerTower : ℕ → ℕᵒᵖ ⥤ ModuleCat A)
    (hKernelFiltrationControlledByEventualImages : Prop)
    [Module (idealAssociatedGradedRing I)
      (cohomologyIdealPowerEventualImageDirectSum idealPowerTower)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (cohomologyIdealPowerEventualImageDirectSum idealPowerTower)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

end
