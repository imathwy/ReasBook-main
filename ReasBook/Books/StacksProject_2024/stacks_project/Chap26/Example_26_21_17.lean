import Mathlib
import StacksProject_2024.stacks_project.Chap26.Example_26_9_3
import StacksProject_2024.stacks_project.Chap26.Example_26_14_4_Projective_line

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry PrimeSpectrum

namespace AlgebraicGeometry

noncomputable section

universe u

variable (k : Type u) [Field k]

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.Surjective`,
-- `AlgebraicGeometry.IsImmersion`, and the affine-open/scheme owners. Local Chapter 26 precedent
-- supplies the punctured affine plane from Example 26.9.3 and the `Proj` model of `P^1_k`.

/-- The polynomial ring `k[a,b,c,d]` used to define `GL2`. -/
@[stacks 01KX]
abbrev glTwoPolynomialRing : Type u :=
  MvPolynomial (Fin 4) k

/-- The coordinate `a` on `GL2`. -/
@[stacks 01KX]
abbrev glTwoA : glTwoPolynomialRing k :=
  MvPolynomial.X 0

/-- The coordinate `b` on `GL2`. -/
@[stacks 01KX]
abbrev glTwoB : glTwoPolynomialRing k :=
  MvPolynomial.X 1

/-- The coordinate `c` on `GL2`. -/
@[stacks 01KX]
abbrev glTwoC : glTwoPolynomialRing k :=
  MvPolynomial.X 2

/-- The coordinate `d` on `GL2`. -/
@[stacks 01KX]
abbrev glTwoD : glTwoPolynomialRing k :=
  MvPolynomial.X 3

/-- The determinant `ad - bc` in `k[a,b,c,d]`. -/
@[stacks 01KX]
abbrev glTwoDet : glTwoPolynomialRing k :=
  glTwoA k * glTwoD k - glTwoB k * glTwoC k

/-- The coordinate ring `k[a,b,c,d, 1/(ad-bc)]` of `GL2`. -/
@[stacks 01KX]
abbrev glTwoCoordinateRing : Type u :=
  Localization.Away (glTwoDet k)

/-- The coordinate `a` after localizing at `ad - bc`. -/
@[stacks 01KX]
abbrev glTwoLocalizedA : glTwoCoordinateRing k :=
  algebraMap (glTwoPolynomialRing k) (glTwoCoordinateRing k) (glTwoA k)

/-- The coordinate `b` after localizing at `ad - bc`. -/
@[stacks 01KX]
abbrev glTwoLocalizedB : glTwoCoordinateRing k :=
  algebraMap (glTwoPolynomialRing k) (glTwoCoordinateRing k) (glTwoB k)

/-- The ring map `k[x,y] -> k[a,b,c,d,1/(ad-bc)]` sending `x` to `a` and `y` to `b`. -/
@[stacks 01KX]
abbrev glTwoToAffinePlaneComap :
    puncturedAffinePlaneCoordinateRing k →+* glTwoCoordinateRing k :=
  MvPolynomial.eval₂Hom (algebraMap k (glTwoCoordinateRing k))
    (fun i : Fin 2 ↦ if i = 0 then glTwoLocalizedA k else glTwoLocalizedB k)

/-- The affine scheme `GL2,k = Spec(k[a,b,c,d,1/(ad-bc)])`. -/
@[stacks 01KX]
abbrev glTwoScheme : Scheme.{u} :=
  Spec (CommRingCat.of (glTwoCoordinateRing k))

/-- The morphism `GL2,k -> Spec(k[x,y])` induced by `x |-> a`, `y |-> b`. -/
@[stacks 01KX]
abbrev glTwoToAffinePlane : glTwoScheme k ⟶ puncturedAffinePlaneSpectrum k :=
  Spec.map (CommRingCat.ofHom (glTwoToAffinePlaneComap k))

/-- The comorphism of `glTwoToAffinePlane` sends `x` to `a`. -/
@[stacks 01KX]
theorem glTwoToAffinePlaneComap_x :
    glTwoToAffinePlaneComap k (puncturedAffinePlaneX k) = glTwoLocalizedA k := sorry

/-- The comorphism of `glTwoToAffinePlane` sends `y` to `b`. -/
@[stacks 01KX]
theorem glTwoToAffinePlaneComap_y :
    glTwoToAffinePlaneComap k (puncturedAffinePlaneY k) = glTwoLocalizedB k := sorry

/-- Example 26.21.17 (1): the morphism `GL2,k -> Spec(k[x,y])` determined by
`x |-> a`, `y |-> b` factors through the punctured affine plane and gives a surjective morphism
`GL2,k -> Spec(k[x,y]) \ { (x,y) }`. -/
@[stacks 01KX]
theorem exists_surjective_glTwoToPuncturedAffinePlane :
    ∃ f : glTwoScheme k ⟶ (puncturedAffinePlaneOpen k).toScheme,
      f ≫ (puncturedAffinePlaneOpen k).ι = glTwoToAffinePlane k ∧
        AlgebraicGeometry.Surjective f := sorry

/-- Example 26.21.17 (2): the image of the surjective `GL2,k` morphism to the punctured
affine plane induced by `x |-> a`, `y |-> b` is not contained in an affine open of the punctured
affine plane. -/
@[stacks 01KX]
theorem glTwoToPuncturedAffinePlane_image_not_contained_in_affineOpen
    (f : glTwoScheme k ⟶ (puncturedAffinePlaneOpen k).toScheme)
    (hf_map : f ≫ (puncturedAffinePlaneOpen k).ι = glTwoToAffinePlane k)
    (hf : AlgebraicGeometry.Surjective f) :
    ¬ ∃ V : ((puncturedAffinePlaneOpen k).toScheme).Opens,
      IsAffineOpen V ∧ Set.range f.base ≤ (V : Set ((puncturedAffinePlaneOpen k).toScheme)) := sorry

/-- Example 26.21.17 (3): the affine scheme `GL2,k` also admits a surjective morphism onto
`P^1_k`. -/
@[stacks 01KX]
theorem exists_surjective_glTwoToProjectiveLine :
    ∃ f : glTwoScheme k ⟶ projectiveLine k, AlgebraicGeometry.Surjective f := sorry

/-- Example 26.21.17 (4): the projective line over `k` has no immersion into any affine scheme. -/
@[stacks 01KX]
theorem projectiveLine_no_immersion_to_affine (Y : Scheme.{u}) [IsAffine Y]
    (f : projectiveLine k ⟶ Y) :
    ¬ IsImmersion f := sorry

end

end AlgebraicGeometry
