import Mathlib
import StacksProject_2024.Chap10.«10_69_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 20.35.3:
- primary domain: inverse-limit topologies on sequential systems of `A`-modules, compared with
  `I`-adic module topologies via the kernel filtration on the limit;
- sampled owner declarations:
  * `_root_.idealAssociatedGradedRing`;
  * `Ideal.adicModuleTopology`;
  * `LinearMap.ker`;
  * `TopologicalSpace.induced`;
  * `CategoryTheory.Limits.limit.π`.
- owner choice:
  * `source-facing`: the cohomological topology statement proved downstream from this abstract
    module lemma;
  * `core/canonical`: `CategoryTheory.inverseLimitTopology`, defined below from
    `TopologicalSpace.induced` and `limit.π`, together with the intrinsic kernel filtration on
    `limit cohomologySystem`;
  * `bridge/view`: the downstream comparison from source cohomology groups
    `H^p(X, I^n \mathcal F_{n + 1})` or their eventual images to the associated graded of that
    kernel filtration.
- primitive data: the ideal `I` and the inverse system `cohomologySystem`;
- derived API: `CategoryTheory.inverseLimitTopology cohomologySystem`,
  `inverseLimitKernelFiltration cohomologySystem`, and
  `inverseLimitKernelAssociatedGraded cohomologySystem`.
-/

noncomputable section

universe u

namespace CategoryTheory

open Limits Opposite
open scoped DirectSum

section

variable {A : Type u} [CommRing A]

/-- The topology on the inverse limit of a sequential system of `A`-modules induced from the
product of the discrete quotient modules. -/
abbrev inverseLimitTopology (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) :
    TopologicalSpace ↥(limit cohomologySystem) :=
  let _ : (n : ℕ) → TopologicalSpace ↥(cohomologySystem.obj (op n)) := fun _ ↦ ⊥
  TopologicalSpace.induced
    (fun x : ↥(limit cohomologySystem) ↦
      fun n : ℕ ↦ ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)))
    inferInstance

/-- The `n`-th step of the kernel filtration on the inverse limit, given by the kernel of the
projection to stage `n`. -/
abbrev inverseLimitKernelFiltration (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    Submodule A ↥(limit cohomologySystem) :=
  LinearMap.ker ((limit.π cohomologySystem (op n)).hom)

/-- The kernel filtration is decreasing: the kernel of the projection to stage `n + 1` lies in the
kernel of the projection to stage `n`. -/
theorem inverseLimitKernelFiltration_succ_le
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    inverseLimitKernelFiltration cohomologySystem (n + 1) ≤
      inverseLimitKernelFiltration cohomologySystem n := by
  intro x hx
  have hx' : ((limit.π cohomologySystem (op (n + 1))).hom x :
      cohomologySystem.obj (op (n + 1))) = 0 := by
    simpa [inverseLimitKernelFiltration] using hx
  have hw :
      ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n)) =
        (cohomologySystem.map (homOfLE (Nat.le_succ n)).op).hom
          ((limit.π cohomologySystem (op (n + 1))).hom x) := by
    simpa using congrArg
      (fun f : limit cohomologySystem ⟶ cohomologySystem.obj (op n) ↦ f x)
      ((limit.w cohomologySystem ((homOfLE (Nat.le_succ n)).op)).symm)
  calc
    ((limit.π cohomologySystem (op n)).hom x : cohomologySystem.obj (op n))
        = (cohomologySystem.map (homOfLE (Nat.le_succ n)).op).hom
            ((limit.π cohomologySystem (op (n + 1))).hom x) := hw
    _ = 0 := by simp [hx']

/-- The degree-`n` quotient `F^n / F^{n + 1}` of the kernel filtration on the inverse limit. -/
abbrev inverseLimitKernelFiltrationPiece (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) (n : ℕ) :
    Type u :=
  ↥(inverseLimitKernelFiltration cohomologySystem n) ⧸
    (inverseLimitKernelFiltration cohomologySystem (n + 1)).submoduleOf
      (inverseLimitKernelFiltration cohomologySystem n)

/-- The associated graded direct sum `⊕_n F^n / F^{n + 1}` of the kernel filtration on the inverse
limit. This is the intrinsic graded module that the source compares to ideal-power cohomology in
later lemmas. -/
abbrev inverseLimitKernelAssociatedGraded
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A) : Type u :=
  DirectSum ℕ fun n ↦ inverseLimitKernelFiltrationPiece cohomologySystem n

-- Proof sketch: let `F^n` be the kernel of the projection from `lim_n M_n` to `M_n`. If the
-- associated graded module `⊕_n F^n / F^{n + 1}` is Noetherian over the associated graded ring of
-- `I`, then the kernel filtration satisfies the stabilization required in the source argument, so
-- the neighborhoods defined by the inverse-limit topology agree with the `I`-power neighborhoods.
-- The downstream cohomological lemmas are responsible for constructing the comparison from source
-- cohomology groups to this intrinsic associated graded module.
/-- Lemma 20.35.3: let `F^n` be the kernel of the projection
`lim_n M_n → M_n` for a sequential inverse system `cohomologySystem = (M_n)_n` of `A`-modules. If
the associated graded module `⊕_{n ≥ 0} F^n / F^{n + 1}` is Noetherian over the associated graded
ring `⊕_{n ≥ 0} I^n / I^(n + 1)`, then the inverse-limit topology on `lim_n M_n` is the
`I`-adic topology. In later source-facing applications, the relevant cohomology groups
`H^p(X, I^n \mathcal F_{n + 1})` are used only through a comparison with this intrinsic associated
graded module. -/
lemma inverseLimitTopology_eq_adicModuleTopology_of_noetherian_kernelAssociatedGraded
    (I : Ideal A)
    (cohomologySystem : ℕᵒᵖ ⥤ ModuleCat A)
    [Module (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded cohomologySystem)]
    [IsNoetherian (idealAssociatedGradedRing I)
      (inverseLimitKernelAssociatedGraded cohomologySystem)] :
    inverseLimitTopology cohomologySystem =
      Ideal.adicModuleTopology I ↥(limit cohomologySystem) := sorry

end

end CategoryTheory
