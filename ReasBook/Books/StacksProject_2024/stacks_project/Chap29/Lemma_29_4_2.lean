import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- The source item is source-facing: it characterizes the maximal quasi-coherent submodule of a
-- given submodule by its universal property against quasi-coherent modules. The canonical public
-- owner is therefore still a subobject of `ℱ`, while the testing objects should use the canonical
-- full subcategory of quasi-coherent modules rather than a bare module together with a separate
-- quasi-coherence hypothesis.

/-- Lemma 29.4.2: if `ℱ` is a quasi-coherent `\mathcal O_X`-module on a scheme `X` and
`G \subset ℱ` is an `\mathcal O_X`-submodule, then there exists a unique quasi-coherent
submodule `G' \subset ℱ` contained in `G` such that, for every quasi-coherent
`\mathcal O_X`-module `ℋ`, the induced map `Hom(ℋ, G') → Hom(ℋ, G)` is bijective; in
particular `G'` is the largest quasi-coherent `\mathcal O_X`-submodule of `ℱ` contained in `G`.
-/
theorem existsUnique_largestQuasiCoherentSubobject
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (G : Subobject ℱ) :
    ∃! G' : Subobject ℱ,
      ∃ hG' : G' ≤ G,
        (G' : X.Modules).IsQuasicoherent ∧
        ∀ ℋ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
          Function.Bijective
            (fun φ : ℋ.obj ⟶ (G' : X.Modules) ↦ φ ≫ Subobject.ofLE G' G hG') := sorry

end AlgebraicGeometry.Scheme.Modules
