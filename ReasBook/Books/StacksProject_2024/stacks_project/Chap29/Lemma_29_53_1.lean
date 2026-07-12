import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Tactic.Recall

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 29.53.1: for a quasi-compact and quasi-separated affine morphism `f : Y ⟶ X`
representing a quasi-coherent `\mathcal O_X`-algebra on `X`, the subsheaf obtained by taking the
integral closure of `\mathcal O_X` in that algebra is the canonical normalization presheaf
`normalizationDiagram f`. -/
recall normalizationDiagram

/- The affine-local localization compatibility expressing the quasi-coherent and stalkwise content
of Lemma 29.53.1 is carried by the canonical map `normalizationDiagramMap` and its coequifibered
property. -/
recall normalizationDiagramMap
recall coequifibered_normalizationDiagramMap

end AlgebraicGeometry.Scheme.Hom
