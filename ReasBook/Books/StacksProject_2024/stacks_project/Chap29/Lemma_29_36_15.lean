import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_34_14
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_14
import StacksProject_2024.stacks_project.Chap29.Lemma_29_36_14

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the scheme-side owners `Scheme.Hom.stalkMap`, `IsEtale`,
  `Scheme.fromSpecStalk`, and the affine standard-etale owner `Algebra.IsStandardEtale`.
- Local Chapter 29 precedent fixes pointwise owners as `f.EtaleAt x`, `f.UnramifiedAt x`,
  `f.fiberToSpecResidueField (f x)`, `f.asFiber x`, and the differential sheaf `Ω[f.toShHom]`.
- The source tag evidence is consistent: Stacks tag `02GU` is the URL tag for
  `Lemma 29.36.15`.
-/

/-- The local flatness plus etale-fibre condition at `x`. -/
private def flatStalkMapAndEtaleFiberAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    (f.fiberToSpecResidueField (f x)).EtaleAt (f.asFiber x)

/-- The local flatness plus unramified-fibre condition at `x`. -/
private def flatStalkMapAndUnramifiedFiberAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x)

/-- The local flatness plus vanishing relative-differentials-stalk condition at `x`. -/
private def flatStalkMapAndDifferentialsVanishAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)

/-- The local flatness plus vanishing cotangent-space condition, recording both sides of the
displayed base-change identification at `x`. -/
private def flatStalkMapAndCotangentSpacesVanishAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    Subsingleton
      ((IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) ⊗[
          ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
        (RingedSpace.stalkModuleCat
          (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x))) ∧
    Subsingleton
      ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[X.presheaf.stalk x]
        (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x))

/-- The local flatness plus maximal-ideal and finite-separable residue-field condition at `x`. -/
private def flatStalkMapAndMaximalIdealResidueFieldAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧
    MaximalIdealResidueFieldUnramifiedAtCriterion f x

/-- Affine neighbourhoods around `x` and `f x` on which the coordinate-ring map is standard
smooth of relative dimension zero. -/
private def existsAffineOpenStandardSmoothRelativeDimensionZeroAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ V : S.affineOpens,
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        RingHom.IsStandardSmoothOfRelativeDimension 0
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom

/-- Affine neighbourhoods with a square Jacobian presentation whose determinant avoids the prime
corresponding to `x`. -/
private def existsAffineOpenJacobianPresentationRelativeDimensionZeroAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
    ∃ V : S.affineOpens,
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        let R := Γ(S, (V : S.Opens))
        let A := Γ(X, (U : X.Opens))
        letI : Algebra R A := (f.appLE (V : S.Opens) (U : X.Opens) e).hom.toAlgebra
        ∃ n : ℕ, ∃ P : Algebra.PreSubmersivePresentation R A (Fin n) (Fin n),
          P.jacobian ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- Affine neighbourhoods carrying a one-variable standard-etale presentation whose derivative
avoids the prime corresponding to `x`. -/
private def existsAffineOpenStandardEtalePresentationAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
    ∃ V : S.affineOpens,
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        let R := Γ(S, (V : S.Opens))
        let A := Γ(X, (U : X.Opens))
        letI : Algebra R A := (f.appLE (V : S.Opens) (U : X.Opens) e).hom.toAlgebra
        ∃ P : StandardEtalePresentation R A,
          Polynomial.aeval P.x P.f.derivative ∉ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- Lemma 29.36.15: for a locally finitely presented morphism of schemes `f : X ⟶ S`
and a point `x : X`, the following are equivalent: `f` is etale at `x`; the stalk map
`𝒪_{S,f x} → 𝒪_{X,x}` is flat and the fibre over `f x` is etale at the corresponding point; the
same flatness holds and that fibre is unramified; the same flatness holds and `Ω[X/S]_x`
vanishes; the same flatness holds and the two cotangent spaces in the displayed base-change
identification vanish; the same flatness holds together with the maximal-ideal equality and
finite separable residue-field extension; and equivalently there are affine neighbourhoods with
standard smooth relative-dimension-zero, square Jacobian, standard etale, or one-variable
standard-etale presentations at `x`. -/
@[stacks 02GU]
theorem etaleAt_tfae_flat_stalkMap_fiber_differentials_standardEtale
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    List.TFAE
      [ f.EtaleAt x
      , flatStalkMapAndEtaleFiberAt f x
      , flatStalkMapAndUnramifiedFiberAt f x
      , flatStalkMapAndDifferentialsVanishAt f x
      , flatStalkMapAndCotangentSpacesVanishAt f x
      , flatStalkMapAndMaximalIdealResidueFieldAt f x
      , existsAffineOpenStandardSmoothRelativeDimensionZeroAt f x
      , existsAffineOpenJacobianPresentationRelativeDimensionZeroAt f x
      , ∃ V : S.affineOpens, f x ∈ (V : S.Opens) ∧
          ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
            f.IsStandardEtaleOver V U
      , existsAffineOpenStandardEtalePresentationAt f x
      ] := sorry

end AlgebraicGeometry
