import Mathlib.AlgebraicGeometry.Normalization
import StacksProject_2024.Chap29.«29_54_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- `lean_leansearch` recalled the canonical relative-normalization API
-- `Scheme.Hom.normalization` and `Scheme.Hom.fromNormalization`. The source-specific input
-- morphism is the generic-point residue-field coproduct map `genericPointSpectrumCoproductTo X`
-- from `29.54.0.1`, and the normalization owners therefore keep only the canonical ambient
-- quasi-compactness and quasi-separatedness assumptions required by that API.

namespace Scheme

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The underlying scheme `X^ν` of the normalization of `X`, realized as the relative
normalization of the generic-point residue-field coproduct morphism. -/
noncomputable abbrev normalization : Scheme.{u} :=
  (genericPointSpectrumCoproductTo X).normalization

/-- Definition 29.54.1: the normalization of `X` is the morphism
`ν : X.normalization ⟶ X` obtained by taking the normalization of `X` in the canonical morphism
`genericPointSpectrumCoproductTo X` from `29.54.0.1`. In the Stacks-project setting, the
finiteness hypothesis on irreducible components is used elsewhere only to supply the
quasi-compactness and quasi-separatedness assumptions on this map, not as part of the public
normalization owner itself. -/
@[stacks 035N]
noncomputable abbrev normalizationTo :
    X.normalization ⟶ X :=
  (genericPointSpectrumCoproductTo X).fromNormalization

/-- The absolute normalization owner is the relative normalization of the generic-point residue
field coproduct morphism. -/
@[simp]
theorem normalization_eq :
    X.normalization = (genericPointSpectrumCoproductTo X).normalization := rfl

/-- The absolute normalization morphism is the relative normalization morphism of the
generic-point residue-field coproduct map. -/
@[simp]
theorem normalizationTo_eq :
    X.normalizationTo = (genericPointSpectrumCoproductTo X).fromNormalization := rfl

end Scheme

end AlgebraicGeometry
