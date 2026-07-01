import stacks_project.Chap09.Example_9_3_6
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold
open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

section

set_option autoImplicit false

/-- A compact connected Riemann surface, modeled as a Hausdorff second-countable complex
one-manifold. The nontriviality needed for the category of nonconstant holomorphic maps is a
derived fact, not part of the object data. -/
structure CompactRiemannSurface where
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [chartedSpace : ChartedSpace ℂ carrier]
  [isManifold : IsManifold 𝓘(ℂ) 1 carrier]
  [compactSpace : CompactSpace carrier]
  [connectedSpace : ConnectedSpace carrier]

attribute [instance] CompactRiemannSurface.topologicalSpace CompactRiemannSurface.t2Space
  CompactRiemannSurface.secondCountableTopology CompactRiemannSurface.chartedSpace
  CompactRiemannSurface.isManifold CompactRiemannSurface.compactSpace
  CompactRiemannSurface.connectedSpace

instance : CoeSort CompactRiemannSurface (Type u) := ⟨CompactRiemannSurface.carrier⟩

instance (X : CompactRiemannSurface.{u}) : Nontrivial X := by
  sorry

/-- A holomorphic map of compact Riemann surfaces, formalized as a complex
manifold-differentiable map. -/
structure CompactRiemannSurfaceHom (X Y : CompactRiemannSurface.{u}) where
  toFun : X → Y
  mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun

instance (X Y : CompactRiemannSurface.{u}) : FunLike (CompactRiemannSurfaceHom X Y) X Y where
  coe f := f.toFun
  coe_injective' := by
    intro f g h
    cases f
    cases g
    cases h
    rfl

@[ext]
lemma CompactRiemannSurfaceHom.ext {X Y : CompactRiemannSurface.{u}}
    {f g : CompactRiemannSurfaceHom X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

instance : Category CompactRiemannSurface where
  Hom X Y := CompactRiemannSurfaceHom X Y
  id X :=
    { toFun := id
      mdifferentiable := by
        simpa using
          (mdifferentiable_id : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : X ↦ x)) }
  comp f g :=
    { toFun := g ∘ f
      mdifferentiable := g.mdifferentiable.comp f.mdifferentiable }
  id_comp f := by
    ext x
    rfl
  comp_id f := by
    ext x
    rfl
  assoc f g h := by
    ext x
    rfl

/-- A holomorphic map of compact Riemann surfaces is nonconstant if it separates two points. -/
def CompactRiemannSurfaceHom.IsNonconstant {X Y : CompactRiemannSurface.{u}}
    (f : CompactRiemannSurfaceHom X Y) : Prop :=
  ∃ x y, f x ≠ f y

/-- The morphism property cutting out nonconstant holomorphic maps of compact Riemann surfaces. -/
def CompactRiemannSurface.nonconstantHom :
    MorphismProperty CompactRiemannSurface :=
  fun _ _ f ↦ f.IsNonconstant

instance : CompactRiemannSurface.nonconstantHom.IsMultiplicative where
  id_mem X := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨x, y, hxy⟩
  comp_mem f g hf hg := by
    sorry

/-- The category of compact Riemann surfaces with nonconstant holomorphic maps, realized as the
wide subcategory of holomorphic maps cut out by the nonconstancy property. -/
abbrev CompactRiemannSurfaceCat :=
  WideSubcategory CompactRiemannSurface.nonconstantHom

/-- The property cutting out one-dimensional function fields over `k` inside `CommAlgCat k`.
This is a derived categorical view on the algebraic side of Example 9.26.8, not a new owner:
the primitive object remains the underlying field extension, while the field/finite-type/
transcendence-degree conditions are the atomic defining properties. -/
def IsOneDimensionalFunctionField (k : Type v) [Field k] (K : CommAlgCat k) : Prop :=
  IsField K ∧ Algebra.EssFiniteType k K ∧ Algebra.trdeg k K = 1

/-- The category of one-dimensional function fields over `k`. -/
abbrev OneDimensionalFunctionFieldCat (k : Type v) [Field k] :=
  ObjectProperty.FullSubcategory (IsOneDimensionalFunctionField k)

/-- Example 9.26.8 (1): if `X` is a compact Riemann surface, then its meromorphic function field
`ℂ(X)` has transcendence degree `1` over `ℂ`. -/
theorem compactRiemannSurface_functionField
    (X : CompactRiemannSurface.{u}) :
    Algebra.trdeg ℂ (ℂ(X)) = 1 := by
  sorry

/-- The meromorphic function field `ℂ(X)` of a compact Riemann surface is finitely generated
over `ℂ`. -/
noncomputable instance (X : CompactRiemannSurface.{u}) :
    Algebra.EssFiniteType ℂ (ℂ(X)) := by
  sorry

/-- The meromorphic function field of a compact Riemann surface is a one-dimensional function
field over `ℂ`. -/
theorem compactRiemannSurface_isOneDimensionalFunctionField
    (X : CompactRiemannSurface.{u}) :
    IsOneDimensionalFunctionField ℂ (CommAlgCat.of ℂ (ℂ(X))) :=
  ⟨Field.toIsField (ℂ(X)), inferInstance, compactRiemannSurface_functionField X⟩

/-- Example 9.26.8 (2): every finitely generated extension of `ℂ` of transcendence degree one is
the meromorphic function field of some compact Riemann surface. The canonical algebraic content is
the resulting `ℂ`-algebra equivalence. -/
theorem exists_compactRiemannSurface_with_functionField
    (K : Type v) [Field K] [Algebra ℂ K] [Algebra.EssFiniteType ℂ K]
    (hK : Algebra.trdeg ℂ K = 1) :
    ∃ X : CompactRiemannSurface.{u}, Nonempty (ℂ(X) ≃ₐ[ℂ] K) := by
  sorry

section Algebraic

variable (k : Type v) [Field k]

/-- A smooth projective curve over `k`, formalized in the current library by the equivalent
scheme-theoretic condition that the structural morphism to `Spec k` is smooth of relative
dimension `1`, proper, and has integral source. -/
class SmoothProjectiveCurveOver (X : Over (Spec (CommRingCat.of k))) : Prop where
  isIntegral : IsIntegral X.left
  smooth : SmoothOfRelativeDimension 1 X.hom
  proper : IsProper X.hom

attribute [instance] SmoothProjectiveCurveOver.isIntegral
attribute [instance] SmoothProjectiveCurveOver.smooth
attribute [instance] SmoothProjectiveCurveOver.proper

/- On the algebraic side, the owner-level bridges are `Scheme.functionField` and
`Scheme.RationalMap.equivFunctionFieldOver`. This file uses those canonical declarations
directly rather than keeping parallel exact-interface abbreviations. -/

/-- The dominant morphisms between smooth projective curves over `k`. -/
abbrev smoothProjectiveCurveDominantHom (k : Type v) [Field k] :
    MorphismProperty (ObjectProperty.FullSubcategory (SmoothProjectiveCurveOver k)) :=
  MorphismProperty.inverseImage (@IsDominant)
    (ObjectProperty.ι (SmoothProjectiveCurveOver k) ⋙ Over.forget _)

instance (k : Type v) [Field k] : (smoothProjectiveCurveDominantHom k).IsMultiplicative :=
  inferInstance

/-- The category of smooth projective curves over `k` with nonconstant morphisms, formalized by
restricting morphisms to the equivalent dominant-over-`Spec k` condition. -/
abbrev SmoothProjectiveCurveCat (k : Type v) [Field k] :=
  WideSubcategory (smoothProjectiveCurveDominantHom k)

instance {X Y : SmoothProjectiveCurveCat k} (f : X ⟶ Y) :
    IsDominant ((ObjectProperty.ι (SmoothProjectiveCurveOver k) ⋙ Over.forget _).map f.hom) := by
  exact f.property

/-- Example 9.26.8 (3): compact Riemann surfaces with nonconstant holomorphic maps are
anti-equivalent to the category of finitely generated extensions of `ℂ` of transcendence degree
`1`. Since the source statement is existential rather than a specified canonical construction, the
formalized output is the existence of an equivalence with the opposite function-field category. -/
theorem compactRiemannSurfaces_antiEquivalent_functionFields :
    Nonempty (CompactRiemannSurfaceCat ≌ (OneDimensionalFunctionFieldCat ℂ)ᵒᵖ) := by
  sorry

/-- Example 9.26.8 (4): over an algebraically closed field, smooth projective curves over `k`
with nonconstant morphisms are anti-equivalent to the category of one-dimensional function
fields over `k`. The present formalization realizes the source curve category by the equivalent
library-facing model `SmoothProjectiveCurveCat k`, and the conclusion as existence of an
equivalence with the opposite function-field category. -/
theorem smoothProjectiveCurves_antiEquivalent_functionFields [IsAlgClosed k] :
    Nonempty (SmoothProjectiveCurveCat k ≌ (OneDimensionalFunctionFieldCat k)ᵒᵖ) := by
  sorry

end Algebraic

end
