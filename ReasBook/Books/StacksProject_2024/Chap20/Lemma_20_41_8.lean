import Mathlib
import StacksProject_2024.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [Abelian (RingedSpace.Modules X)]
variable [HasProducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ K L : CochainComplex (RingedSpace.Modules X) ℤ,
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSpace.Modules X))]

/-- Use the preadditive structure induced by the ambient abelian category so the standard
cochain-complex APIs use a single local instance. -/
local instance : Preadditive (RingedSpace.Modules X) :=
  Abelian.toPreadditive

local notation "CpxOX" => CochainComplex (RingedSpace.Modules X) ℤ

/-- The degree-`n` term of the internal-Hom complex of two cochain complexes of
`\mathcal O_X`-modules on a ringed space. -/
noncomputable def moduleComplexInternalHomDegree
    (K L : CpxOX) (n : ℤ) : (RingedSpace.Modules X) :=
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
    (K L : CpxOX) (i j p : ℤ) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) p ≫
    (ihom (K.X p)).map (L.d (i + p) (j + p))

/-- The precomposition contribution to the internal-Hom differential in degree `(i,j,p)` on a
ringed space. -/
noncomputable def moduleComplexInternalHomPrecompose
    (K L : CpxOX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
    moduleComplexInternalHomDegree K L i ⟶
      (ihom (K.X p)).obj (L.X (j + p)) :=
  Pi.π (fun q : ℤ ↦ (ihom (K.X q)).obj (L.X (i + q))) (p + 1) ≫
    (ihom (K.X (p + 1))).map
      (eqToHom (congrArg (fun q : ℤ ↦ L.X q)
        (moduleComplexInternalHom_succIndexEq hij))) ≫
    (MonoidalClosed.pre (K.d p (p + 1))).app (L.X (j + p))

/-- The degree-`(i,j,p)` component of the internal-Hom differential on a ringed space. -/
noncomputable def moduleComplexInternalHomDComponent
    (K L : CpxOX) (i j p : ℤ) (hij : (up ℤ).Rel i j) :
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
    (K L : CpxOX) (i j : ℤ) :
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
    (K L : CpxOX) (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    moduleComplexInternalHomD K L i j = 0 := sorry

-- Proof sketch: expand the two successive internal-Hom differentials, use `d ≫ d = 0` in both
-- source and target complexes, and cancel the mixed terms with the standard cochain sign
-- convention.
/-- Two consecutive differentials in the internal-Hom complex on a ringed space compose to zero. -/
theorem moduleComplexInternalHom_dCompD
    (K L : CpxOX) (i j k : ℤ)
    (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    moduleComplexInternalHomD K L i j ≫ moduleComplexInternalHomD K L j k = 0 := sorry

/-- The internal-Hom complex of two cochain complexes of `\mathcal O_X`-modules on a ringed
space. -/
noncomputable def moduleComplexInternalHom
    (K L : CpxOX) : CpxOX where
  X := moduleComplexInternalHomDegree K L
  d := moduleComplexInternalHomD K L
  shape := fun i j hij ↦ moduleComplexInternalHom_shape K L i j hij
  d_comp_d' := fun i j k hij hjk ↦ moduleComplexInternalHom_dCompD K L i j k hij hjk

-- Proof sketch: use the right-orthogonal characterization of K-injective complexes. For an
-- acyclic complex `K`, identify morphisms `K ⟶ \mathcal H\!\mathit{om}^\bullet(L, I)` in the
-- homotopy category with degree-zero cohomology classes in the internal-Hom complex, then use the
-- tensor-Hom currying comparison to rewrite them as morphisms `Tot(K \otimes L) ⟶ I`. Since `L`
-- is K-flat, the total tensor complex is acyclic, and these morphisms vanish because `I` is
-- K-injective.
set_option maxHeartbeats 1000000 in
/-- Lemma 20.41.8: if `\mathcal I^\bullet` is a K-injective complex of `\mathcal O_X`-modules on
a ringed space `(X, \mathcal O_X)` and `\mathcal L^\bullet` is K-flat, then the internal-Hom
complex `\mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal I^\bullet)` is
K-injective. -/
theorem moduleComplexInternalHom_isKInjective_of_isKFlat
    (L I : CpxOX) (hL : L.IsKFlat) [I.IsKInjective] :
    ((moduleComplexInternalHom L I : CpxOX)).IsKInjective := sorry

end AlgebraicGeometry.RingedSpace
