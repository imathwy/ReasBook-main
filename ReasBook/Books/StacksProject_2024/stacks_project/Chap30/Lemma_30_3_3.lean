import Mathlib
import StacksProject_2024.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced the canonical `Scheme.Modules`,
`SheafOfModules.IsQuasicoherent`, and ideal-sheaf owners. Local Chapter 28/30 precedent represents
ampleness by `Scheme.Modules.IsAmple`, tensor powers by the `Invertible` interface, ideal sheaves
as subobjects of `\mathcal O_X`, and cohomology as `Sheaf.H'` on the top open. -/

variable {X : Scheme.{u}} [CompactSpace X.carrier] [MonoidalCategory X.Modules]

/-- Lemma 30.3.3: let `X` be a quasi-compact scheme and let `L` be an invertible
`\mathcal O_X`-module. If for every quasi-coherent sheaf of ideals
`I \subset \mathcal O_X` there exists `n ≥ 1` such that
`H^1(X, I \otimes_{\mathcal O_X} L^{\otimes n}) = 0`, then `L` is ample. -/
@[stacks 0B5P]
theorem isAmple_of_H1_vanishes_for_quasiCoherent_idealSheaf_tensorPowers
    (L : X.Modules) [hL : Invertible L]
    (hH1 : ∀ I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules),
      (Subobject.underlying.obj I).IsQuasicoherent →
        ∃ n : ℕ, 0 < n ∧
          IsZero
            (((SheafOfModules.toSheaf X.ringCatSheaf).obj
              (((Subobject.underlying.obj I : X.Modules) ⊗ hL n : X.Modules))).H' 1 (⊤ : X.Opens))) :
    IsAmple L := sorry

end AlgebraicGeometry.Scheme.Modules
