import Mathlib
import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules on a ringed space and their
  stability under sequential colimits;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `AB5 (SheafOfModules ((RingedSpace.ringCatSheaf X)))`;
- best owner abstraction: the core owner is the predicate `K.IsKFlat` on the cochain complex
  itself. The ringed-space statement is a source-facing specialization of that owner to
  `(RingedSpace.Modules X)`, together with the chapter-level exactness of filtered colimits in
  `SheafOfModules ((RingedSpace.ringCatSheaf X))`;
- primitive vs derived: the primitive data are only the sequential diagram `F` and the K-flatness
  hypotheses on its stages. The sequential colimit object and its K-flatness are derived from the
  ambient colimit and owner predicate, so no extra wrapper data belongs in the public API.

Source/core/bridge triage:
- `source-facing`: Lemma 20.26.10, the ringed-space closure of K-flatness under sequential
  colimits;
- `core/canonical`: `CochainComplex.IsKFlat` together with the ambient colimit in
  `CochainComplex (RingedSpace.Modules X) ℤ`;
- `bridge/view`: none. This file should state the ringed-space specialization directly in terms of
  the canonical K-flat owner rather than introduce a parallel local notion. -/

-- Proof sketch: tensor an arbitrary acyclic complex `\mathcal F^\bullet` with the sequential
-- diagram `F`. Termwise tensor products commute with the colimit, so
-- `Tot(\mathcal F^\bullet \otimes \operatorname{colim}_i \mathcal K_i^\bullet)` identifies with
-- the colimit of the acyclic tensor complexes `Tot(\mathcal F^\bullet \otimes \mathcal K_i^\bullet)`.
-- Exactness of filtered colimits in sheaves of modules then shows that the resulting tensor
-- complex is acyclic.
/-- Lemma 20.26.10: for a system `\mathcal K_1^\bullet \to \mathcal K_2^\bullet \to \cdots` of
K-flat complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, the sequential
colimit `\mathop{\mathrm{colim}}_i \mathcal K_i^\bullet` is K-flat. -/
theorem sequentialColimit_isKFlat
    (F : ℕ ⥤ CochainComplex (RingedSpace.Modules X) ℤ)
    [HasColimit F]
    (hF : ∀ i : ℕ, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end AlgebraicGeometry.RingedSpace
