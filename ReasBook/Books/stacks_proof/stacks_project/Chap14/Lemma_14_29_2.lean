import Mathlib
import stacks_proof.stacks_project.Chap12.Lemma_12_14_4
import stacks_proof.stacks_project.Chap14.Lemma_14_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits
open HomologicalComplex
open ChainComplex

universe u v

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable [HasBinaryBiproducts 𝒜]

noncomputable section

private abbrev downRel (n : ℤ) : (ComplexShape.down ℤ).Rel n (n - 1) :=
  ComplexShape.down_mk n (n - 1) (sub_add_cancel n 1)

/-
Domain-style sampling:
- primary domain: the Stacks cylinder object `\diamond A` as a degreewise split short exact
  sequence of chain complexes;
- sampled owner declarations:
  `HomologicalComplex.cylinder`,
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.homMk`,
  `ChainComplex.homOfDegreewiseSplit`,
  `HomologicalComplex.homotopyCofiber.inr`,
  `HomologicalComplex.cylinder.inlX`,
  `HomologicalComplex.homotopyCofiber.sndX`;
- best owner abstraction: the source-facing short complex built from the canonical cylinder
  owner `A.cylinder`;
- source/core/bridge triage:
  * `source-facing`: `◇A`, the short complex `A ⊞ A ⟶ ◇A ⟶ A⟦-1⟧`,
    its canonical degreewise splitting, and the induced boundary map;
  * `core/canonical`: the short-complex owner `diamondShortComplex A` and morphisms
    `S ⟶ diamondShortComplex A`;
  * `bridge/view`: the identification of `homOfDegreewiseSplit A.diamondShortComplex
    A.diamondSplitting` with the shifted difference map `(1, -1)⟦-1⟧'`.
- primitive data: the source-facing short complex `diamondShortComplex A`;
- derived API: its canonical inclusion and projection maps, the boundary map, the middle-object
  lift characterized by the two commutative squares, and the equivalent `ShortComplex.Hom`
  formulation. -/

/-- The explicit short complex `A ⊞ A ⟶ ◇A ⟶ A[-1]`. -/
noncomputable def diamondShortComplex (A : ChainComplex 𝒜 ℤ) :
    ShortComplex (ChainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (homotopyCofiber.inr (biprod.lift (𝟙 A) (-𝟙 A)))
    { f := fun n ↦
        homotopyCofiber.fstX (biprod.lift (𝟙 A) (-𝟙 A)) n (n - 1) (downRel n) ≫
          (A.shiftMinusOneXIso n).inv
      comm' n m hnm := by
        sorry }
    (by
      sorry)

/-- The canonical degreewise splitting of `A ⊞ A ⟶ ◇A ⟶ A[-1]`. -/
noncomputable def diamondSplitting (A : ChainComplex 𝒜 ℤ) (n : ℤ) :
    (degreewiseShortComplex (diamondShortComplex A) n).Splitting where
  r := homotopyCofiber.sndX (biprod.lift (𝟙 A) (-𝟙 A)) n
  s := (A.shiftMinusOneXIso n).hom ≫ cylinder.inlX A (n - 1) n (downRel n)
  f_r := by
    sorry
  s_g := by
    sorry
  id := by
    sorry

-- Proof sketch: expand `ChainComplex.homOfDegreewiseSplit_f` on `A.diamondShortComplex` using the
-- explicit section `A.diamondSplitting n`. The right map `(A.diamondShortComplex).g` is given by
-- `fstX`, the retraction by `sndX`, and the resulting degreewise formula simplifies to `(1, -1)`
-- in shifted degree.
/-- The boundary map of the Stacks short exact sequence for `◇A` is the shifted difference
map `(1, -1) : A[-1] ⟶ (A ⊞ A)[-1]`. -/
theorem homOfDegreewiseSplit_diamondShortComplex_eq (A : ChainComplex 𝒜 ℤ) :
    homOfDegreewiseSplit A.diamondShortComplex A.diamondSplitting =
      (biprod.lift (𝟙 A) (-𝟙 A))⟦(-1 : ℤ)⟧' := by
  sorry

end

end ChainComplex

namespace CategoryTheory
namespace ShortComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable [HasBinaryBiproducts 𝒜]
variable {A B C : ChainComplex 𝒜 ℤ}
variable (ι : A ⊞ A ⟶ B) (ρ : B ⟶ C) (w : ι ≫ ρ = 0)
local notation "S" => ShortComplex.mk ι ρ w
variable (f : C ⟶ A⟦(-1 : ℤ)⟧)

noncomputable section

-- Proof sketch: package the unique middle-object lift from Lemma 14.29.2 together with the fixed
-- left identity and right map `f`. The two commutativity conditions are then exactly the fields of
-- `ShortComplex.Hom`.
/-- Canonical `ShortComplex.Hom` formulation of Lemma 14.29.2. The source-facing lift theorem is
the middle-object view of this morphism of short complexes. -/
@[stacks 01A3]
theorem existsUnique_hom_to_diamondShortComplex_of_degreewise_split_factorization
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    (hfactor :
      homOfDegreewiseSplit S σ = f ≫ (biprod.lift (𝟙 A) (-𝟙 A))⟦(-1 : ℤ)⟧') :
    ∃! φ : S ⟶ A.diamondShortComplex, φ.τ₁ = 𝟙 (A ⊞ A) ∧ φ.τ₃ = f := by
  sorry

-- Proof sketch: extract the middle component from the canonical `ShortComplex.Hom` lift. The two
-- commuting-square identities are exactly the `comm₁₂` and `comm₂₃` fields once the outer
-- components are fixed to `𝟙` and `f`.
/-- Lemma 14.29.2: if a degreewise split short exact sequence
`0 ⟶ A ⊞ A ⟶ B ⟶ C ⟶ 0` has connecting morphism factoring through the boundary map of the
canonical Stacks sequence
`0 ⟶ A ⊞ A ⟶ ◇A ⟶ A[-1] ⟶ 0`,
then there is a unique morphism `B ⟶ ◇A` making the two obvious squares commute. -/
@[stacks 01A3]
theorem existsUnique_lift_to_diamond_of_degreewise_split_factorization
    (σ : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)
    (hfactor :
      homOfDegreewiseSplit S σ = f ≫ (biprod.lift (𝟙 A) (-𝟙 A))⟦(-1 : ℤ)⟧') :
    ∃! l : B ⟶ ◇A,
      ι ≫ l = A.diamondShortComplex.f ∧
        l ≫ A.diamondShortComplex.g = ρ ≫ f := by
  sorry

end

end ShortComplex
end CategoryTheory
