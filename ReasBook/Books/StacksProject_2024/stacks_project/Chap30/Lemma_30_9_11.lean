import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

-- Semantic recall note: the source-facing support condition is stated through the canonical owner
-- `moduleSupportedOn`, with coherence from `SheafOfModules.IsCoherent` and pushforward along the
-- open immersion `U.ι`. The source's containment hypothesis `T ⊆ U` is redundant here, since the
-- support condition is expressed on the induced subset `Subtype.val ⁻¹' (T : Set X)` of `U`.

/-- Lemma 30.9.11: let `X` be a scheme, let `U ⊆ X` be open with inclusion `j : U ⟶ X`, and let
`T ⊆ X` be closed. If `ℱ` is a coherent `\mathcal O_U`-module whose support is contained in the
induced closed subset `Subtype.val ⁻¹' T ⊆ U`, then `j_* ℱ` is a coherent
`\mathcal O_X`-module. This is the source statement with the redundant containment `T ⊆ U`
absorbed into the canonical support hypothesis on `U`. -/
@[stacks 0CYJ]
theorem pushforward_obj_isCoherent_of_support_subset
    (U : X.Opens) (T : Closeds X)
    (ℱ : (U : Scheme).Modules)
    [ℱ.IsCoherent]
    (hSupp :
      moduleSupportedOn (U : Scheme).toRingedSpace (Subtype.val ⁻¹' (T : Set X)) ℱ) :
    ((pushforward U.ι).obj ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
