import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_29_1 (from Chap14) -/
open CategoryTheory
open Limits
open HomologicalComplex

universe v u

prefix:max "◇" => HomologicalComplex.cylinder

noncomputable section

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

open HomologicalComplex.cylinder

private abbrev downRel : ∀ j : ℕ, ∃ i, (ComplexShape.down ℕ).Rel i j :=
  fun j ↦ ⟨j + 1, rfl⟩

/-
Domain-style sampling:
- primary domain: chain-complex cylinders and the homotopy-cofiber universal property;
- sampled owner declarations: `HomologicalComplex.cylinder`,
  `HomologicalComplex.cylinder.desc`, `HomologicalComplex.cylinder.ι₀_desc`,
  `HomologicalComplex.cylinder.ι₁_desc`,
  `Functor.CorepresentableBy`, and `Functor.CorepresentableBy.homEquiv_symm_comp`;
- best owner abstraction: the source-facing Stacks cylinder `◇A`, written directly with the
  canonical mathlib owner `HomologicalComplex.cylinder`, with its universal property expressed by
  the canonical cylinder owner `cylinder.desc` and packaged by `Functor.CorepresentableBy`;
  mathlib does not provide a separate cylinder endofunctor owner here, so the public functoriality
  statement remains source-facing and should be derived from that owner data rather than replaced
  by a parallel local wrapper API;
- owner assumption layer: these owners live at the preadditive plus binary-biproduct level, so
  `[Abelian C]` would be redundant here.

Primitive-vs-derived split:
- primitive data: two chain maps `a, b : A ⟶ B` and a homotopy `Homotopy a b`;
- derived API: the resulting corepresentability witness and the induced cylinder map attached to a
  morphism `f : A ⟶ B`.

Source/core/bridge triage:
- `source-facing`: the homotopy functor represented by maps out of `◇A` and the functoriality of
  the Stacks cylinder construction `A ↦ ◇A`;
- `core/canonical`: `HomologicalComplex.cylinder`, `HomologicalComplex.cylinder.desc`,
  and `Functor.CorepresentableBy`;
- `bridge/view`: the corepresentability witness and the private map extracted from it.
-/

/-- The covariant functor sending `B` to triples `(a, b, h)` of maps `a, b : A ⟶ B` equipped
with a homotopy `h : Homotopy a b`. -/
noncomputable def homotopyFunctor
    (A : ChainComplex C ℕ) :
    ChainComplex C ℕ ⥤ Type v where
  obj B := Σ' a : A ⟶ B, Σ' b : A ⟶ B, Homotopy a b
  map {_ B₂} f x := ⟨x.1 ≫ f, x.2.1 ≫ f, x.2.2.compRight f⟩
  map_id B := by
    sorry
  map_comp f g := by
    sorry

/-- Lemma 14.29.1 (1): the Stacks cylinder `◇A` corepresents the functor sending a chain complex
`B` to triples `(a, b, h)` consisting of two maps `a, b : A ⟶ B` and a homotopy
`h : Homotopy a b`. -/
noncomputable def diamondCorepresentableByHomotopyFunctor
    (A : ChainComplex C ℕ) :
    (homotopyFunctor A).CorepresentableBy ◇A where
  homEquiv := fun {B} ↦
    { toFun := fun f ↦ ⟨ι₀ A ≫ f, ι₁ A ≫ f, (homotopy₀₁ A downRel).compRight f⟩
      invFun := fun x ↦ desc x.1 x.2.1 x.2.2
      left_inv := by
        sorry
      right_inv := by
        sorry }
  homEquiv_comp g f := by
    sorry

private noncomputable abbrev diamondMap {A B : ChainComplex C ℕ} (f : A ⟶ B) : ◇A ⟶ ◇B :=
  (diamondCorepresentableByHomotopyFunctor A).homEquiv.symm
    ⟨f ≫ ι₀ B, f ≫ ι₁ B, (homotopy₀₁ B downRel).compLeft f⟩

-- Proof sketch: apply the injectivity of the owner equivalence
-- `diamondCorepresentableByHomotopyFunctor A`. Under `homEquiv`, both
-- `diamondMap (𝟙 A)` and `𝟙 (◇A)` correspond to the canonical triple
-- `(ι₀ A, ι₁ A, homotopy₀₁ A downRel)`.
/-- The cylinder construction sends identity maps to identity maps. -/
private theorem diamondFunctor_map_id
    (A : ChainComplex C ℕ) :
    diamondMap (𝟙 A) = 𝟙 (◇A) := by
  sorry

-- Proof sketch: again use the injectivity of
-- `diamondCorepresentableByHomotopyFunctor A`. The two maps have the same `homEquiv` image,
-- namely the transported triple
-- `(f ≫ g ≫ ι₀ D, f ≫ g ≫ ι₁ D, ((homotopy₀₁ D downRel).compLeft g).compLeft f)`.
/-- The cylinder construction sends compositions to compositions. -/
private theorem diamondFunctor_map_comp
    {A B D : ChainComplex C ℕ} (f : A ⟶ B) (g : B ⟶ D) :
    diamondMap (f ≫ g) = diamondMap f ≫ diamondMap g := by
  sorry

/-- Lemma 14.29.1 (2): the Stacks cylinder construction `A ↦ ◇A` is functorial on `ℕ`-indexed
chain complexes in a preadditive category with binary biproducts. -/
noncomputable def diamondFunctor : ChainComplex C ℕ ⥤ ChainComplex C ℕ where
  obj A := ◇A
  map {_ _} f := diamondMap f
  map_id A := diamondFunctor_map_id A
  map_comp f g := diamondFunctor_map_comp f g

end ChainComplex

/-! ### Lemma_14_29_2 (from Chap14) -/
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

/-! ### Lemma_14_29_3 (from Chap14) -/
open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

/-
Domain-style sampling:
- primary domain: simplicial homotopies and their image on normalized Moore complexes under the
  Dold-Kan comparison;
- sampled owner declarations:
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `CategoryTheory.SimplicialObject.Homotopy.toNormalizedMooreComplexHomotopy`,
  `inclusionOfMooreComplexMap`,
  `PInftyToNormalizedMooreComplex`;
- best owner abstraction: the canonical owner abstraction for the derived normalized-Moore chain
  homotopy is `Homotopy.toNormalizedMooreComplexHomotopy`, built from the core owner
  `Homotopy.toChainHomotopy` and the Dold-Kan comparison maps;
- primitive data: a simplicial homotopy `H : Homotopy a b`;
- derived API: the induced normalized-Moore chain homotopy
  `H.toNormalizedMooreComplexHomotopy`, with its degreewise comparison formula.

Source/core/bridge triage:
- `source-facing`: existence of a simplicial homotopy lifting a prescribed normalized-Moore chain
  homotopy;
- `core/canonical`: `Homotopy.toChainHomotopy`;
- `bridge/view`: `Homotopy.toNormalizedMooreComplexHomotopy`.
-/

-- Proof sketch: form the Stacks cylinder object for `N(U)` as in Lemma 14.29.1 and use the
-- factorization result of Lemma 14.29.2 to lift the given chain homotopy to a simplicial homotopy
-- `H : Homotopy a b`. The lifted homotopy is then identified with the prescribed normalized-Moore
-- chain homotopy through the canonical bridge owner
-- `Homotopy.toNormalizedMooreComplexHomotopy`.
/-- Lemma 14.29.3: every chain homotopy between the normalized Moore maps `N(a)` and `N(b)` comes
from a simplicial homotopy `H : a ⟶ b`, and the given chain homotopy is exactly the canonical
normalized-Moore homotopy induced by `H`. -/
theorem exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      N = H.toNormalizedMooreComplexHomotopy := sorry

/-- Degreewise reformulation of Lemma 14.29.3 via the canonical owner
`Homotopy.toNormalizedMooreComplexHomotopy`. -/
theorem exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy_hom
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      ∀ n : ℕ,
        N.hom n (n + 1) =
          (inclusionOfMooreComplexMap U).f n ≫ H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) := by
  rcases exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy N with ⟨H, hH⟩
  refine ⟨H, fun n ↦ ?_⟩
  rw [hH]
  simpa using H.toNormalizedMooreComplexHomotopy_hom n

end CategoryTheory.SimplicialObject
