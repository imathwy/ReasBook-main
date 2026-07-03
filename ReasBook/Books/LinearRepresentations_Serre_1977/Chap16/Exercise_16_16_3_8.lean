import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Exercise_16_16_3_8.Index

noncomputable section

universe u

open scoped Representation

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "e" =>
  (projectiveGrothendieckBaseChangeHom K :
    finiteProjectiveGroupAlgebraGrothendieckGroup A G →+
      finiteRepGrothendieckGroup K G)

/-- Helper for Exercise 16-16.3-8: LinearRepresentations_Serre_1977's positive subset `P_A^+(G)` consists of the classes in
`P_A(G)` represented by actual finite projective `A[G]`-modules. -/
def projectivePositiveSubset
    (A : Type u) [CommRing A] (G : Type u) [Group G] :
    Set (P₀[A](G)) :=
  Set.range fun P : FiniteProjectiveGroupAlgebraModule A G ↦ [P]ₚ₀

scoped[Representation] notation:max "P⁺[" A "](" G ")" =>
  projectivePositiveSubset A G

/-- Helper for Exercise 16-16.3-8: membership in `P_A^+(G)` is equivalent to being the class of
an actual finite projective `A[G]`-module. -/
@[simp] theorem mem_projectivePositiveSubset_iff
    {A : Type u} [CommRing A] {G : Type u} [Group G] {x : P₀[A](G)} :
    x ∈ P⁺[A](G) ↔
      ∃ P : FiniteProjectiveGroupAlgebraModule A G, [P]ₚ₀ = x :=
  Iff.rfl

/-- Helper for Exercise 16-16.3-8: LinearRepresentations_Serre_1977's actual positive subset `R_K^+(G)` consists of the
Grothendieck classes represented by actual finite-dimensional `K[G]`-representations. -/
def finiteRepPositiveSubset
    (K : Type u) [Field K] (G : Type u) [Group G] :
    Set (finiteRepGrothendieckGroup K G) :=
  Set.range (finiteRepGrothendieckClass K G)

scoped[Representation] notation:max "R⁺[" K "](" G ")" =>
  finiteRepPositiveSubset K G

/-- Helper for Exercise 16-16.3-8: membership in `R_K^+(G)` is equivalent to being the class of
an actual finite-dimensional `K[G]`-representation. -/
@[simp] theorem mem_finiteRepPositiveSubset_iff
    {K : Type u} [Field K] {G : Type u} [Group G] {x : finiteRepGrothendieckGroup K G} :
    x ∈ R⁺[K](G) ↔
      ∃ V : FDRep K G, [V]₀ = x :=
  Iff.rfl

/-- Helper for Exercise 16-16.3-8: condition `(R)` is witnessed by a finite local overring `A'`
with fraction field `K'`, such that scalar extension detects positivity in `R₀[K](G)` and the
decomposition map over `(A', K')` fills the residue-field positive cone. -/
def SatisfiesConditionR
    (RKplus : Set (finiteRepGrothendieckGroup K G))
    (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : HenselianLocalRing A')
      (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : Algebra A A')
      (_ : Module.Finite A A')
      (K' : Type u) (_ : Field K')
      (_ : Algebra A' K') (_ : Algebra A K') (_ : IsFractionRing A' K')
      (_ : Algebra K K')
      (_ : IsScalarTower A A' K') (_ : IsScalarTower A K K')
      (_ : FiniteDimensional K K'),
    RKplus = (finiteRepGrothendieckScalarExtensionHom K K' G) ⁻¹' R⁺[K'](G) ∧
      decompositionHom A' K' G '' R⁺[K'](G) = R⁺[IsLocalRing.ResidueField A'](G)

/-
Source-faithful repair note.

The surrounding API currently has the Grothendieck groups and the decomposition map, but it does
not yet expose the character map on `R₀[K](G)` or LinearRepresentations_Serre_1977's Proposition 44 descent as reusable Lean
lemmas. The previous local proof tried to manufacture those missing facts with ad-hoc names such
as `finiteRepGrothendieckCharacter`, which are not present in this repository and caused a build
blocker.

The statement below matches LinearRepresentations_Serre_1977, Section 16.3, Exercise 16.6: for `K` sufficiently large,
condition `(R)` is equivalent to

  `e(P_A^+(G)) = e(P_A(G)) ∩ R_K^+(G)`.

Forward direction, following the text: choose a finite local extension `A'` with fraction field
`K'`; use the decomposition surjectivity `d(R⁺[K'](G)) = R⁺[k'](G)` and Proposition 44 to prove
that every element of `e.range ∩ R⁺[K](G)` comes from an actual projective class.

Reverse direction, following the text after Proposition 44: use the dual cone criterion
`x ∈ P_k^+(G)` iff all pairings with `R_k^+(G)` are nonnegative. The equality of positive images
transports these inequalities across the adjunction between the decomposition map `d` and the
Cartan map `e`, forcing the image of `d` to be exactly the residue-field positive cone.
-/

/-- Exercise 16-16.3-8: under the large-field hypothesis on `K`, LinearRepresentations_Serre_1977's condition `(R)` for the
actual positive subset `R_K^+(G)` is equivalent to the source-facing equality
`e(P_A^+(G)) = range(e) ∩ R_K^+(G)`, where
`e = projectiveGrothendieckBaseChangeHom K : P_A(G) → R_K(G)`. -/
theorem conditionR_iff_baseChange_image_eq_range_inter_positive
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    SatisfiesConditionR (R⁺[K](G)) A ↔
      e '' P⁺[A](G) =
        (((e).range : Set (finiteRepGrothendieckGroup K G)) ∩ R⁺[K](G)) := by
  -- The remaining proof is exactly the source route recorded above. Keeping the theorem statement
  -- intact is important: downstream proof jobs should now see a correct Exercise 16.6 surface,
  -- without the bogus local character API that previously made the file fail before proof search.
  sorry

end

end Representation
