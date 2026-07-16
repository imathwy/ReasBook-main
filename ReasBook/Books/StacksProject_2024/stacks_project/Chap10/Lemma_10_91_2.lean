import Mathlib
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

-- Proof sketch: for the forward implication, apply Lemma `10.89.6` to obtain the smallest
-- supporting submodule for each tensor in a finite free source. For the converse, use Lazard's
-- theorem to write `M` as a directed colimit of finite free modules, apply Remark `10.88.8` to
-- reduce to the dual inverse system, and identify the eventual images in the duals with the
-- smallest supporting submodules supplied by the hypothesis.
/-- Lemma 10.91.2: for a flat `R`-module `M`, the module `M` is Mittag-Leffler if and only if,
for every finite free `R`-module `F` and every tensor `x : F ⊗[R] M`, there exists a smallest
submodule `F' ≤ F` such that `x` lies in the image of `F' ⊗[R] M → F ⊗[R] M`. -/
theorem flat_mittagLeffler_iff_exists_smallest_supporting_submodule :
    MittagLeffler R M ↔
      ∀ (F : ModuleCat.{w} R) [Module.Free R F] [Module.Finite R F] (x : F ⊗[R] M),
        ∃ F' : Submodule R F,
          IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' := sorry

namespace MittagLeffler

/-- For a flat Mittag-Leffler module, every tensor over a finite free source has a smallest
supporting submodule. -/
theorem exists_smallest_supporting_submodule [MittagLeffler R M]
    (F : ModuleCat.{w} R) [Module.Free R F] [Module.Finite R F] (x : F ⊗[R] M) :
    ∃ F' : Submodule R F,
      IsLeast { F'' : Submodule R F | x ∈ LinearMap.range (F''.subtype.rTensor M) } F' :=
  flat_mittagLeffler_iff_exists_smallest_supporting_submodule.mp
    (inferInstance : MittagLeffler R M) F x

end MittagLeffler

end

end Module
