import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
`LocallyOfFiniteType` and `IsFinite`; nearby Chapter 29 files use
`genericPointsOfIrreducibleComponents` for generic points of irreducible components and
`f.resLE V U e` / `f ∣_ V` for the restricted morphisms. The source tag evidence agrees on
`02NW`. -/

/-- Lemma 29.51.1 (1): for a locally finite type morphism `f : X ⟶ Y` and a generic point `η`
of an irreducible component of `Y`, the fiber over `η` is finite if and only if it is covered by
finitely many affine opens over one affine neighborhood of `η` on which the restrictions of `f`
are finite. -/
@[stacks 02NW]
theorem Scheme.Hom.tfae_finite_fiber_exists_finite_affineOpenCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {η : Y}
    (hη : η ∈ genericPointsOfIrreducibleComponents Y) :
    List.TFAE
      [ ({x : X | f.base x = η} : Set X).Finite
      , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
            (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
            (_ : ∀ x : X, f.base x = η → ∃ i : Fin n, x ∈ U i),
          ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
      ] := sorry

/-- Lemma 29.51.1 (2): if the locally finite type morphism `f : X ⟶ Y` is quasi-separated, then
the finite-fiber condition over a generic point `η` of an irreducible component of `Y`, the finite
affine-open-cover condition, and the existence of one affine open `U` over an affine neighborhood
of `η` with finite restriction are equivalent. -/
@[stacks 02NW]
theorem Scheme.Hom.tfae_finite_fiber_exists_finite_affineOpenCover_exists_finite_affineOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiSeparated f] {η : Y}
    (hη : η ∈ genericPointsOfIrreducibleComponents Y) :
    List.TFAE
      [ ({x : X | f.base x = η} : Set X).Finite
      , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
            (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
            (_ : ∀ x : X, f.base x = η → ∃ i : Fin n, x ∈ U i),
          ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
      , (∃ (U : X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : η ∈ V)
            (hUV : U ≤ f ⁻¹ᵁ V) (_ : ∀ x : X, f.base x = η → x ∈ U),
          IsFinite (f.resLE V U hUV))
      ] := sorry

/-- Lemma 29.51.1 (3): if the locally finite type morphism `f : X ⟶ Y` is quasi-compact and
quasi-separated, then the finite-fiber condition over a generic point `η`, the finite affine cover
condition, the one-affine-open finite restriction condition, and finite restriction over some
affine neighborhood of `η` in the target are equivalent. -/
@[stacks 02NW]
theorem Scheme.Hom.tfae_finite_fiber_exists_finite_affineOpenCover_exists_finite_preimage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    {η : Y} (hη : η ∈ genericPointsOfIrreducibleComponents Y) :
    List.TFAE
      [ ({x : X | f.base x = η} : Set X).Finite
      , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
            (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
            (_ : ∀ x : X, f.base x = η → ∃ i : Fin n, x ∈ U i),
          ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
      , (∃ (U : X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : η ∈ V)
            (hUV : U ≤ f ⁻¹ᵁ V) (_ : ∀ x : X, f.base x = η → x ∈ U),
          IsFinite (f.resLE V U hUV))
      , (∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : η ∈ V), IsFinite (f ∣_ V))
      ] := sorry

end AlgebraicGeometry
