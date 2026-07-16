import StacksProject_2024.stacks_project.Chap17.Definition_17_31_6

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` was attempted for the conormal-sheaf owner on this turn, but
-- the MCP endpoint returned HTTP 429. The owner/API choice was verified locally against
-- `Chap17/Definition_17_31_6.lean` and the existing `Scheme.Modules.pullback` convention.

section

variable {Z X Z' X' : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z') (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z') CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z').HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z').HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z') AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z').WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z') CommRingCat.{u})]

/-- The conormal sheaf of an immersion, viewed as the degree `-1` term of its naive cotangent
complex. -/
abbrev immersionConormalSheaf (i : Z ⟶ X) : Z.Modules :=
  (NL[i.toShHom]).X (-1)

/-- Companion bridge: the conormal sheaf of an immersion is the degree `-1` term of its naive
cotangent complex. -/
theorem immersionConormalSheaf_def (i : Z ⟶ X) :
    immersionConormalSheaf i = (NL[i.toShHom]).X (-1) :=
  rfl

/-- The pulled-back naive cotangent complex `f^* NL_{Z'/X'}` attached to the upper immersion in a
commutative square. -/
abbrev immersionNaiveCotangentPullback
    (f : Z ⟶ Z') (i' : Z' ⟶ X') [IsImmersion i'] :
    CochainComplex Z.Modules ℤ :=
  ((RingedSpace.Hom.pullback f.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (NL[i'.toShHom])

/-- A conormal comparison morphism for a commutative square of immersions is a morphism
`f^* \mathcal C_{Z'/X'} \to \mathcal C_{Z/X}` arising as the degree `-1` component of a map from
the pulled-back naive cotangent complex. -/
def IsImmersionConormalMap
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') [IsImmersion i'] [IsImmersion i]
    (φ : (Scheme.Modules.pullback f).obj (immersionConormalSheaf i') ⟶ immersionConormalSheaf i) :
    Prop :=
  ∃ ψ : immersionNaiveCotangentPullback f i' ⟶ NL[i.toShHom], ψ.f (-1) = φ

/-- Lemma 29.31.3: for a commutative square of schemes
`Z ⟶ X`, `Z' ⟶ X'` with vertical maps `f : Z ⟶ Z'`, `g : X ⟶ X'` and immersions
`i : Z ⟶ X`, `i' : Z' ⟶ X'`, there is a unique canonical map of `\mathcal O_Z`-modules
`f^* \mathcal C_{Z'/X'} \to \mathcal C_{Z/X}` characterized by coming from degree `-1` of a map
from the pulled-back naive cotangent complex. In Lean, the conormal sheaf is formalized as the
degree `-1` term of the naive cotangent complex. -/
theorem existsUnique_immersionConormalMap
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (sq : CommSq f i i' g) :
    ∃! φ :
      (Scheme.Modules.pullback f).obj (immersionConormalSheaf i') ⟶
        immersionConormalSheaf i,
      IsImmersionConormalMap f i i' φ := sorry

/-- Companion existence form of Lemma 29.31.3. -/
theorem exists_immersionConormalMap
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (sq : CommSq f i i' g) :
    ∃ φ :
      (Scheme.Modules.pullback f).obj (immersionConormalSheaf i') ⟶
        immersionConormalSheaf i,
      IsImmersionConormalMap f i i' φ := by
  exact (existsUnique_immersionConormalMap f i i' g sq).exists

/-- Source-facing companion form of Lemma 29.31.3: the canonical conormal comparison map is the
degree `-1` component of a morphism from the pulled-back naive cotangent complex. -/
theorem exists_immersionConormalMap_eq_f_negOne
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (sq : CommSq f i i' g) :
    ∃ φ :
      (Scheme.Modules.pullback f).obj (immersionConormalSheaf i') ⟶
        immersionConormalSheaf i,
      ∃ ψ : immersionNaiveCotangentPullback f i' ⟶ NL[i.toShHom], ψ.f (-1) = φ := by
  simpa [IsImmersionConormalMap] using exists_immersionConormalMap f i i' g sq

end

end AlgebraicGeometry
