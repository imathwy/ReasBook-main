import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_54_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` is not exposed in this Codex session. Local Chapter 29
-- precedent provides the relevant owners: `Scheme.normalization`, `Scheme.normalizationTo`,
-- `Scheme.Hom.fromNormalization`, and the chapter-local `IsBirational` predicate.

namespace Hom

/-- A morphism is birational on quasi-compact opens if, for every quasi-compact open `U` of the
target, the inverse image has finitely many irreducible components and the restricted morphism to
`U` is birational. -/
def IsBirationalOnCompactOpens
    {X' X : Scheme.{u}} (α : X' ⟶ X) : Prop :=
  ∀ (U : X.Opens) (hU : IsCompact (U : Set X)),
    ∃ (hsource : Finite (irreducibleComponents (α ⁻¹ᵁ U)))
      (htarget : Finite (irreducibleComponents U)),
      letI : Finite (irreducibleComponents (α ⁻¹ᵁ U)) := hsource
      letI : Finite (irreducibleComponents U) := htarget
      IsBirational (α ∣_ U)

/-- Unfold the quasi-compact-open birationality condition for a scheme morphism. -/
theorem isBirationalOnCompactOpens_iff
    {X' X : Scheme.{u}} (α : X' ⟶ X) :
    α.IsBirationalOnCompactOpens ↔
      ∀ (U : X.Opens) (hU : IsCompact (U : Set X)),
        ∃ (hsource : Finite (irreducibleComponents (α ⁻¹ᵁ U)))
          (htarget : Finite (irreducibleComponents U)),
          letI : Finite (irreducibleComponents (α ⁻¹ᵁ U)) := hsource
          letI : Finite (irreducibleComponents U) := htarget
          IsBirational (α ∣_ U) := sorry

end Hom

/-- Lemma 29.54.5 (1): if every quasi-compact open of `X` has finitely many irreducible
components, then the normalization `X^ν`, formalized as `X.normalization`, is a disjoint union of
integral normal schemes. -/
@[stacks 035Q]
theorem normalization_exists_pairwiseDisjoint_openCover_integral_normal
    (X : Scheme.{u}) (hX : HasFiniteIrreducibleComponentsOnCompactOpens X)
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    ∃ (ι : Type u) (U : ι → X.normalization.Opens),
      ∃ (hpair : Pairwise (fun i j ↦
            Disjoint (U i : Set X.normalization) (U j : Set X.normalization))),
        ∃ (hcover : (⋃ i, (U i : Set X.normalization)) = Set.univ),
          ∀ i, IsIntegral (U i).toScheme ∧ (U i).toScheme.isNormal := sorry

/-- Lemma 29.54.5 (2): the normalization morphism
`ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is integral. -/
@[stacks 035Q]
theorem isIntegralHom_normalizationTo
    (X : Scheme.{u}) (hX : HasFiniteIrreducibleComponentsOnCompactOpens X)
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    IsIntegralHom X.normalizationTo := sorry

/-- Lemma 29.54.5 (3): the normalization morphism
`ν : X^ν ⟶ X`, formalized as `X.normalizationTo`, is surjective. -/
@[stacks 035Q]
theorem surjective_normalizationTo
    (X : Scheme.{u}) (hX : HasFiniteIrreducibleComponentsOnCompactOpens X)
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    Surjective X.normalizationTo := sorry

/-- Lemma 29.54.5 (4): the normalization morphism induces a bijection on irreducible components,
expressed as a bijection on the generic points of irreducible components. -/
@[stacks 035Q]
theorem normalizationTo_bijOn_genericPointsOfIrreducibleComponents
    (X : Scheme.{u}) (hX : HasFiniteIrreducibleComponentsOnCompactOpens X)
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)] :
    Set.BijOn X.normalizationTo
      (genericPointsOfIrreducibleComponents X.normalization)
      (genericPointsOfIrreducibleComponents X) := sorry

/-- Lemma 29.54.5 (5): for an integral morphism `α : X' ⟶ X` whose restrictions over
quasi-compact opens are birational and have finitely many irreducible components, the
normalization of `X` factors through `X'`; moreover the factor map
`X.normalization ⟶ X'` identifies `X.normalization` with the normalization of `X'`. -/
@[stacks 035Q]
theorem exists_normalization_factorization_of_isIntegralHom_isBirationalOnCompactOpens
    (X : Scheme.{u}) (hX : HasFiniteIrreducibleComponentsOnCompactOpens X)
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    {X' : Scheme.{u}} (α : X' ⟶ X) [IsIntegralHom α]
    [QuasiCompact (genericPointSpectrumCoproductTo X')]
    [QuasiSeparated (genericPointSpectrumCoproductTo X')]
    (hα : α.IsBirationalOnCompactOpens) :
    ∃ hX' : HasFiniteIrreducibleComponentsOnCompactOpens X',
      ∃ β : X.normalization ⟶ X',
        β ≫ α = X.normalizationTo ∧
          ∃ e : X.normalization ≅ X'.normalization,
            β = e.hom ≫ X'.normalizationTo := sorry

/-- Lemma 29.54.5 (6): if `Z` is normal and every irreducible component of `Z` dominates an
irreducible component of `X`, then every morphism `Z ⟶ X` factors uniquely through the
normalization morphism `X.normalizationTo`. -/
@[stacks 035Q]
theorem existsUnique_lift_normalizationTo_of_isNormal
    (X : Scheme.{u}) (hX : HasFiniteIrreducibleComponentsOnCompactOpens X)
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    {Z : Scheme.{u}} (g : Z ⟶ X) (hZ : Z.isNormal)
    (hcomponents : Set.MapsTo g
      (genericPointsOfIrreducibleComponents Z)
      (genericPointsOfIrreducibleComponents X)) :
    ∃! h : Z ⟶ X.normalization, h ≫ X.normalizationTo = g := sorry

end Scheme
end AlgebraicGeometry
