import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open PrimeSpectrum
open scoped AlgebraicGeometry PrimeSpectrum

namespace AlgebraicGeometry

noncomputable section

universe u

variable (k : Type u) [Field k]

-- Semantic recall: `lean_leansearch` surfaced `IsAffineOpen`, `Scheme.ΓSpecIso`, and
-- `Scheme.isoSpec` as the canonical affine-scheme owners.  Local Chapter 26 precedent models
-- open subspaces by `X.Opens.toScheme` and source basic opens by `PrimeSpectrum.basicOpen`.

/-- The coordinate ring `k[x,y]` of the affine plane over `k`. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneCoordinateRing : Type u :=
  MvPolynomial (Fin 2) k

/-- The affine plane `Spec(k[x,y])`. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneSpectrum : Scheme.{u} :=
  Spec (CommRingCat.of (puncturedAffinePlaneCoordinateRing k))

/-- The coordinate function `x` on `Spec(k[x,y])`. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneX : puncturedAffinePlaneCoordinateRing k :=
  MvPolynomial.X 0

/-- The coordinate function `y` on `Spec(k[x,y])`. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneY : puncturedAffinePlaneCoordinateRing k :=
  MvPolynomial.X 1

/-- Evaluation at the origin `(0,0)` of the affine plane. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneEvalAtOrigin :
    puncturedAffinePlaneCoordinateRing k →+* k :=
  MvPolynomial.eval₂Hom (algebraMap k k) (fun _ : Fin 2 ↦ (0 : k))

/-- The maximal ideal of functions vanishing at the origin. -/
@[stacks 01IL]
def puncturedAffinePlaneOriginIdeal : Ideal (puncturedAffinePlaneCoordinateRing k) :=
  RingHom.ker (puncturedAffinePlaneEvalAtOrigin k)

/-- The origin point of `Spec(k[x,y])`, corresponding to the ideal `(x,y)`. -/
@[stacks 01IL]
def puncturedAffinePlaneOrigin :
    PrimeSpectrum (puncturedAffinePlaneCoordinateRing k) :=
  PrimeSpectrum.comap (puncturedAffinePlaneEvalAtOrigin k) (IsLocalRing.closedPoint k)

/-- The kernel description of the origin is the ideal `(x,y)`. -/
@[stacks 01IL]
theorem puncturedAffinePlaneOriginIdeal_eq_span :
    puncturedAffinePlaneOriginIdeal k =
      Ideal.span
        ({puncturedAffinePlaneX k, puncturedAffinePlaneY k} :
          Set (puncturedAffinePlaneCoordinateRing k)) := sorry

/-- The basic open `D(x)` in the affine plane. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneChartX : (puncturedAffinePlaneSpectrum k).Opens :=
  PrimeSpectrum.basicOpen (puncturedAffinePlaneX k)

/-- The basic open `D(y)` in the affine plane. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneChartY : (puncturedAffinePlaneSpectrum k).Opens :=
  PrimeSpectrum.basicOpen (puncturedAffinePlaneY k)

/-- The basic open `D(xy)`, the intersection of `D(x)` and `D(y)`. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneChartXY : (puncturedAffinePlaneSpectrum k).Opens :=
  PrimeSpectrum.basicOpen (puncturedAffinePlaneX k * puncturedAffinePlaneY k)

/-- The open subscheme `Spec(k[x,y]) \ { (x,y) }`, represented by the cover `D(x) ∪ D(y)`. -/
@[stacks 01IL]
abbrev puncturedAffinePlaneOpen : (puncturedAffinePlaneSpectrum k).Opens :=
  puncturedAffinePlaneChartX k ⊔ puncturedAffinePlaneChartY k

/-- The open `D(x) ∪ D(y)` is the complement of the origin point. -/
@[stacks 01IL]
theorem puncturedAffinePlaneOpen_carrier_eq_compl_origin :
    (puncturedAffinePlaneOpen k : Set (puncturedAffinePlaneSpectrum k)) =
      ({puncturedAffinePlaneOrigin k} : Set (puncturedAffinePlaneSpectrum k))ᶜ := sorry

/-- The punctured affine plane is covered by the two basic opens `D(x)` and `D(y)`. -/
@[stacks 01IL]
theorem puncturedAffinePlaneOpen_eq_chartX_sup_chartY :
    puncturedAffinePlaneOpen k =
      puncturedAffinePlaneChartX k ⊔ puncturedAffinePlaneChartY k := sorry

/-- The basic open `D(x)` is affine. -/
@[stacks 01IL]
theorem puncturedAffinePlaneChartX_isAffineOpen :
    IsAffineOpen (puncturedAffinePlaneChartX k) := sorry

/-- The basic open `D(y)` is affine. -/
@[stacks 01IL]
theorem puncturedAffinePlaneChartY_isAffineOpen :
    IsAffineOpen (puncturedAffinePlaneChartY k) := sorry

/-- The intersection `D(x) ∩ D(y)` is the basic open `D(xy)`. -/
@[stacks 01IL]
theorem puncturedAffinePlaneChartX_inf_chartY :
    puncturedAffinePlaneChartX k ⊓ puncturedAffinePlaneChartY k =
      puncturedAffinePlaneChartXY k := sorry

/-- The basic open `D(xy)` is affine. -/
@[stacks 01IL]
theorem puncturedAffinePlaneChartXY_isAffineOpen :
    IsAffineOpen (puncturedAffinePlaneChartXY k) := sorry

/-- The morphism from the punctured affine plane to `Spec(k[x,y])` induces an isomorphism on
global sections after identifying `Γ(Spec(k[x,y]), 𝒪)` with `k[x,y]`. -/
@[stacks 01IL]
theorem puncturedAffinePlane_globalSections_isIso :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of (puncturedAffinePlaneCoordinateRing k))).inv ≫
      Scheme.Γ.map (puncturedAffinePlaneOpen k).ι.op) := sorry

/-- Example 26.9.3: for a field `k`, the open subscheme
`Spec(k[x,y]) \ { (x,y) }` is not affine. -/
@[stacks 01IL]
theorem puncturedAffinePlane_not_isAffine :
    ¬ IsAffine (puncturedAffinePlaneOpen k).toScheme := sorry

end

end AlgebraicGeometry
