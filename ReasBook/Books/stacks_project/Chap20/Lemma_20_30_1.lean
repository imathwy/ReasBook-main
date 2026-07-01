import Mathlib
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap06.Definition_6_27_1
import stacks_project.Chap14.Example_14_33_1
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The pointwise family of module-sheaf categories on the one-point ringed spaces
`({x}, \mathcal O_{X, x})`. -/
private abbrev PointwiseSheafModules (X : RingedSpace.{u}) :=
  (x : X) → (RingedSpace.Modules (pointRingedSpace x))

/-- Pull an `\mathcal O_X`-module back to the family of its pointwise pullbacks to the one-point
ringed spaces `({x}, \mathcal O_{X, x})`. -/
private abbrev godementPullback (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ PointwiseSheafModules X where
  obj ℱ x := ((pointInclusion x)^*).obj ℱ
  map φ x := ((pointInclusion x)^*).map φ

/-- Push a family of pointwise module sheaves forward and take their product on `X`. This is the
library-facing avatar of the functor `f_*` from the discrete ringed space over `X`. -/
private def godementPushforward (X : RingedSpace.{u}) :
    PointwiseSheafModules X ⥤ (RingedSpace.Modules X) where
  obj A := ∏ᶜ fun x : X ↦ ((pointInclusion x) _*).obj (A x)
  map φ := Limits.Pi.map (fun x : X ↦ ((pointInclusion x) _*).map (φ x))
  map_id A := by
    simpa only [Functor.map_id] using
      (CategoryTheory.Limits.Pi.map_id
        (f := fun x : X ↦ ((pointInclusion x) _*).obj (A x)))
  map_comp φ ψ := by
    simpa only [Functor.map_comp] using
      (CategoryTheory.Limits.Pi.map_comp_map
        (q := fun x : X ↦ ((pointInclusion x) _*).map (φ x))
        (q' := fun x : X ↦ ((pointInclusion x) _*).map (ψ x))).symm

/-- The Godement step functor `f_* f^*` on `\mathcal O_X`-modules, modeled via the family of
pointwise pullbacks and the product of their pushforwards. -/
abbrev godementStep (X : RingedSpace.{u}) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules X) :=
  godementPullback X ⋙ godementPushforward X

/-- A functorial Godement resolution on a ringed space `X`: an augmentation
`ℱ[0] ⟶ G^\bullet(ℱ)` whose `n`-th term is the explicit iterate of `f_* f^*`, whose terms are
flasque, and whose pullback to each one-point ringed space is homotopy equivalent to the complex
concentrated in degree `0`. -/
structure FunctorialGodementResolution (X : RingedSpace.{u}) where
  /-- The cochain-complex-valued functor underlying the resolution. -/
  cochain : (RingedSpace.Modules X) ⥤ CochainComplex (RingedSpace.Modules X) ℕ
  /-- The augmentation `ℱ[0] ⟶ G^\bullet(ℱ)`. -/
  augmentation : CochainComplex.single₀ (RingedSpace.Modules X) ⟶ cochain
  /-- The `n`-th term is the explicit `(n + 1)`-fold iterate of `f_* f^*`. -/
  termEq :
      ∀ n : ℕ,
        cochain ⋙ HomologicalComplex.eval (RingedSpace.Modules X) (ComplexShape.up ℕ) n =
          iteratedEndofunctor (godementStep X) n
  /-- The augmentation is a quasi-isomorphism, i.e. the augmented Godement complex is a
  resolution of the input sheaf. -/
  augmentation_quasiIso :
      ∀ ℱ : (RingedSpace.Modules X), QuasiIso (augmentation.app ℱ)
  /-- Every term of the resolution is flasque as an `\mathcal O_X`-module sheaf. -/
  termwise_flasque :
      ∀ (n : ℕ) (ℱ : (RingedSpace.Modules X)),
        TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X))).obj ((cochain.obj ℱ).X n))
  /-- After pulling back to the one-point ringed space `({x}, \mathcal O_{X, x})`, the
  augmentation becomes a homotopy equivalence of cochain complexes. This is the library-facing
  form of the stalkwise homotopy-equivalence statement in the textbook. -/
  pointwise_homotopy :
      ∀ (ℱ : (RingedSpace.Modules X)) (x : X),
        (HomologicalComplex.homotopyEquivalences
          (RingedSpace.Modules (pointRingedSpace x))
          (ComplexShape.up ℕ))
          ((((pointInclusion x)^*).mapHomologicalComplex
              (ComplexShape.up ℕ)).map (augmentation.app ℱ))

-- Proof sketch: let `f : X_{disc} ⟶ X` be the canonical morphism from the discrete ringed space.
-- The standard cosimplicial Godement construction on the monad `f_* f^*` yields a functorial
-- cochain complex whose `n`-th term is `(f_* f^*)^{n+1} ℱ`. Each term is flasque because
-- pullback to the discrete space is exact and pushforward from a discrete space preserves
-- flasqueness. Pulling back to each one-point ringed space identifies the augmented complex with
-- the adjunction resolution attached to `f^* ⊣ f_*`, hence with a homotopy-equivalent copy of the
-- degree-`0` complex.
/-- Lemma 20.30.1: for a ringed space `(X, \mathcal O_X)`, there exists a functorial Godement
resolution of `\mathcal O_X`-modules whose `n`-th term is the explicit iterate
`(f_* f^*)^{n+1}`, whose terms are flasque, and whose pullback to each one-point ringed space
`({x}, \mathcal O_{X, x})` is homotopy equivalent to the complex concentrated in degree `0`
at the pulled-back module; equivalently, the associated stalk complex at `x` is homotopy
equivalent to `\mathcal F_x[0]`. -/
theorem exists_functorial_godement_resolution (X : RingedSpace.{u}) :
    Nonempty (FunctorialGodementResolution X) := sorry

end AlgebraicGeometry.RingedSpace
