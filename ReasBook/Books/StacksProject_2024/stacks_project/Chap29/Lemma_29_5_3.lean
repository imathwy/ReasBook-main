import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

-- Semantic recall: `lean_leansearch` surfaced the algebraic owners
-- `Module.isClosed_support` and
-- `Module.mem_support_iff_nontrivial_residueField_tensorProduct`; local Chapter 17/29 precedent
-- fixes the scheme-module support owner as `moduleSupport`, so the source-facing statements below
-- stay on scheme modules and their stalks/pullbacks.

/-- Lemma 29.5.3 (1): if `\mathcal F` is a finite type quasi-coherent `\mathcal O_X`-module on a
scheme `X`, then the support of `\mathcal F` is closed. -/
@[stacks 056J]
theorem isClosed_moduleSupport :
    IsClosed (moduleSupport ℱ) := sorry

/-- Lemma 29.5.3 (2): for a point `x : X`, membership in the support of a finite type
quasi-coherent `\mathcal O_X`-module `\mathcal F` is equivalent to the stalk `\mathcal F_x`
having a nonzero element. -/
@[stacks 056J]
theorem mem_moduleSupport_iff_exists_stalk_ne_zero (x : X) :
    x ∈ moduleSupport ℱ ↔ ∃ m : RingedSpace.stalkModuleCat ℱ x, m ≠ 0 := sorry

/-- Lemma 29.5.3 (3): for a point `x : X`, membership in the support of a finite type
quasi-coherent `\mathcal O_X`-module `\mathcal F` is equivalent to the residue-field tensor of
the stalk `\mathcal F_x` being nontrivial. -/
@[stacks 056J]
theorem mem_moduleSupport_iff_nontrivial_residueField_tensor (x : X) :
    x ∈ moduleSupport ℱ ↔
      Nontrivial ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[X.presheaf.stalk x]
        RingedSpace.stalkModuleCat ℱ x) := sorry

/-- Lemma 29.5.3 (4): for a morphism of schemes `f : Y ⟶ X`, the pullback `f^*\mathcal F` of a
finite type quasi-coherent `\mathcal O_X`-module `\mathcal F` is again of finite type. -/
@[stacks 056J]
theorem isFiniteType_pullback (f : Y ⟶ X) :
    ((Scheme.Modules.pullback f).obj ℱ).IsFiniteType := sorry

/-- Lemma 29.5.3 (5): for a morphism of schemes `f : Y ⟶ X`, the support of the pullback
`f^*\mathcal F` is the inverse image of the support of a finite type quasi-coherent
`\mathcal O_X`-module `\mathcal F`. -/
@[stacks 056J]
theorem moduleSupport_pullback_eq_preimage (f : Y ⟶ X) :
    moduleSupport ((Scheme.Modules.pullback f).obj ℱ) = f.base ⁻¹' moduleSupport ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
