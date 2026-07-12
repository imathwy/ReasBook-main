import StacksProject_2024.Chap31.TorsionSectionImage

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the ring-level owner `Module.IsTorsionFree`.
-- Definition 31.11.2 is source-facing: it defines torsion sections and then torsion-free
-- `\mathcal O_X`-modules by the vanishing of every torsion local section.

/-- Definition 31.11.2 (1): let `X` be an integral scheme and let `ℱ` be an
`\mathcal O_X`-module. A local section `s ∈ \mathcal F(U)` is torsion if, for every `x ∈ U`, its
image in the stalk `\mathcal F_x` is torsion. The source states this for quasi-coherent modules,
but the pointwise stalk condition itself is independent of quasi-coherence. -/
def isTorsionSection
    (ℱ : X.Modules) {U : X.Opens} (s : ℱ.val.obj (op U)) : Prop :=
  ∀ x : U, sectionImageIsTorsionAt ℱ s x

/-- On a nonempty open of an integral scheme, a local section is torsion exactly when its image in
the generic stalk vanishes. -/
theorem isTorsionSection_iff_genericSectionImage_eq_zero
    (ℱ : X.Modules) [IsIntegral X] [ℱ.IsQuasicoherent]
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X))
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    isTorsionSection ℱ s ↔ genericSectionImage ℱ η hη hU s = 0 := sorry

/-- Definition 31.11.2 (2): let `X` be an integral scheme and let `ℱ` be an
`\mathcal O_X`-module. The module `ℱ` is torsion free if every torsion local section is zero. The
source applies this to quasi-coherent modules, but the vanishing condition itself is defined for an
arbitrary module sheaf. -/
class IsTorsionFree (ℱ : X.Modules) : Prop where
  /-- Every torsion local section vanishes. -/
  eq_zero_of_isTorsionSection :
    ∀ ⦃U : X.Opens⦄ (s : ℱ.val.obj (op U)), isTorsionSection ℱ s → s = 0

/-- Definition 31.11.2 (2): an `\mathcal O_X`-module is torsion free if every torsion local
section is zero. -/
theorem isTorsionFree_iff_forall_torsionSection_eq_zero
    (ℱ : X.Modules) :
    IsTorsionFree ℱ ↔
      ∀ ⦃U : X.Opens⦄ (s : ℱ.val.obj (op U)), isTorsionSection ℱ s → s = 0 := by
  constructor
  · intro hℱ
    simpa using hℱ.eq_zero_of_isTorsionSection
  · intro hℱ
    exact ⟨hℱ⟩

end AlgebraicGeometry.Scheme.Modules
