import Mathlib
import StacksProject_2024.Chap20.Definition_20_26_2
import StacksProject_2024.Chap20.Definition_20_46_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Abelian (Modules X)]
variable [HasProducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [SymmetricCategory (Modules X)]
variable [MonoidalClosed (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (K L : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (Modules X))]
variable [MonoidalPreadditive (Modules X)]

local notation "ModX" => Modules X
local notation "CpxX" => CochainComplex ModX ℤ

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O_X`-modules on a ringed space. -/
noncomputable def moduleComplexInternalHomDegree
    (K L : CpxX) (n : ℤ) : ModX :=
  Limits.piObj (fun p : ℤ ↦ (ihom (K.X p)).obj (L.X (n + p)))

-- Proof sketch: if `j` is the successor of `i` in the cochain-complex shape, then `j = i + 1`,
-- and both sides reduce to the same degree after reassociating addition on `ℤ`.
/-- Reindexing the target degree in the differential of the internal-Hom complex on a ringed
space. -/
theorem moduleComplexInternalHom_succIndexEq
    {i j p : ℤ} (hij : (up ℤ).Rel i j) :
    i + (p + 1) = j + p := sorry

/-- The postcomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPostcompose
    (K L : CpxX) (i j p : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPrecompose
    (K L : CpxX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (moduleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential on a ringed space. -/
noncomputable def moduleComplexInternalHomDComponent
    (K L : CpxX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  if Even i then
    moduleComplexInternalHomPostcompose K L i j p -
      moduleComplexInternalHomPrecompose K L i j p hij
  else
    moduleComplexInternalHomPostcompose K L i j p +
      moduleComplexInternalHomPrecompose K L i j p hij

/-- The differential on the internal-Hom complex of two cochain complexes of `\mathcal O_X`-
modules on a ringed space. -/
noncomputable def moduleComplexInternalHomD
    (K L : CpxX) (i j : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      moduleComplexInternalHomDegree K L j :=
  if hij : (up ℤ).Rel i j then
    Pi.lift (fun p : ℤ ↦ moduleComplexInternalHomDComponent K L i j p hij)
  else
    0

-- Proof sketch: by definition, the internal-Hom differential is zero unless `j = i + 1`.
/-- The internal-Hom differential on a ringed space vanishes away from adjacent cohomological
degrees. -/
theorem moduleComplexInternalHom_shape
    (K L : CpxX) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    moduleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms with the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex on a ringed space compose to zero. -/
theorem moduleComplexInternalHom_dCompD
    (K L : CpxX) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    moduleComplexInternalHomD K L i j ≫ moduleComplexInternalHomD K L j k = 0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O_X`-modules on a ringed
space. -/
noncomputable def moduleComplexInternalHom
    (K L : CpxX) : CpxX where
  X := moduleComplexInternalHomDegree K L
  d := moduleComplexInternalHomD K L
  shape := fun i j hij ↦ moduleComplexInternalHom_shape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦ moduleComplexInternalHom_dCompD K L i j k hij hjk

-- Proof sketch: this is exactly Lemma `20.46.9` specialized to the explicit internal-Hom complex
-- defined above. For every acyclic `K^\bullet`, compare
-- `Tot(K^\bullet \otimes \mathcal H^\bullet)` with
-- `\mathcal H\!\mathit{om}^\bullet(E^\bullet, Tot(K^\bullet \otimes F^\bullet))` via the
-- tensor-Hom comparison map; K-flatness of `F^\bullet` makes the target acyclic, and the local
-- acyclicity criterion for strictly perfect sources then gives the source acyclic.
/-- Lemma 20.46.10: in the situation of Lemma `20.46.9`, if `\mathcal F^\bullet` is K-flat, then
the internal-Hom complex
`\mathcal H^\bullet = \mathcal H\!\mathit{om}^\bullet(\mathcal E^\bullet, \mathcal F^\bullet)`
with `\mathcal E^\bullet` strictly perfect is K-flat. -/
theorem moduleComplexInternalHom_isKFlat_of_isStrictlyPerfect
    (E F : CpxX)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hF : CochainComplex.IsKFlat F) :
    CochainComplex.IsKFlat (moduleComplexInternalHom E F) := sorry

end AlgebraicGeometry.RingedSpace
