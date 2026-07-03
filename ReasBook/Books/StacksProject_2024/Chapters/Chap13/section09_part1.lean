import Mathlib
import Mathlib.Algebra.Homology.Factorizations.CM5b
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_9_1 (from Chap13) -/
open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

/- Source/core/bridge triage for Definition 13.9.1:
- primary domain: mapping cones and their standard triangles for cochain complexes in an additive
  category;
- inspected owner declarations:
  `CochainComplex.mappingCone`,
  `CochainComplex.mappingCone.inr`,
  `CochainComplex.mappingCone.fst`,
  `CochainComplex.mappingCone.triangle`;
- best owner abstraction: the upstream namespace owner `CochainComplex.mappingCone`, with the cone
  object as owner, the canonical inclusion `inr` and cocycle `fst` as atomic comparison data, and
  the standard triangle as derived API;
- layer: `core/canonical`; the item recalls canonical mathlib declarations rather than introducing
  a new source-facing wrapper;
- primitive data: a morphism of cochain complexes `f : K^• ⟶ L^•`;
- derived API: the cone object `CochainComplex.mappingCone f`, the canonical inclusion
  `CochainComplex.mappingCone.inr f`, the canonical cocycle
  `CochainComplex.mappingCone.fst f`, and the standard triangle
  `CochainComplex.mappingCone.triangle f`, whose third morphism is induced by `-fst f`.
-/

/- Definition 13.9.1: for a morphism `f : K^• ⟶ L^•` of cochain complexes in an additive
category, the cone is the canonical mathlib complex `CochainComplex.mappingCone f`. Degreewise it
is canonically the biproduct `K.X (n + 1) ⊞ L.X n`, with the standard mapping-cone differential
whose components are `-d_K`, `f`, and `d_L` relative to that decomposition. The canonical maps are
`CochainComplex.mappingCone.inr f : L ⟶ CochainComplex.mappingCone f`, the right inclusion of the
`L`-summand, and
`CochainComplex.mappingCone.fst f : Cocycle (CochainComplex.mappingCone f) K 1`, the first
projection to the shifted `K` summand; the latter induces the third morphism of the standard
mapping-cone triangle from `CochainComplex.mappingCone f` to `K⟦(1 : ℤ)⟧`. -/
recall CochainComplex.mappingCone

/- The canonical inclusion of the target complex into the mapping cone is
`CochainComplex.mappingCone.inr`. -/
recall CochainComplex.mappingCone.inr

/- The canonical degree-`1` cocycle on the mapping cone projecting to the shifted source is
`CochainComplex.mappingCone.fst`. -/
recall CochainComplex.mappingCone.fst

/- The canonical morphism from the mapping cone to the shift of the source is the third morphism
in the standard mapping-cone triangle `CochainComplex.mappingCone.triangle`, induced by
`-CochainComplex.mappingCone.fst`. -/
recall CochainComplex.mappingCone.triangle

/-! ### Lemma_13_9_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CochainComplex

universe v u

/- Domain-style sampling for Lemma 13.9.2:
- primary domain: mapping-cone triangles in the cochain homotopy category and the functoriality
  of the cone construction under homotopy-commutative squares;
- inspected owner declarations:
  `CochainComplex.mappingCone.mapOfHomotopy`,
  `CochainComplex.mappingCone.triangleMapOfHomotopy_comm₃`,
  `CochainComplex.mappingCone.trianglehMapOfHomotopy`,
  `CochainComplex.mappingCone.map`;
- source/core/bridge triage:
  `source-facing`: a square of cochain-complex morphisms commuting up to homotopy;
  `core/canonical`: the induced triangle morphism
    `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
  `bridge/view`: the underlying cone map `CochainComplex.mappingCone.mapOfHomotopy` and the
    component commutativity lemmas feeding the triangle-level owner;
- primitive data: only a homotopy `H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)`;
- derived API: the induced map on mapping cones and the resulting morphism between the standard
  mapping-cone triangles in the homotopy category;
- best owner abstraction: `CochainComplex.mappingCone.trianglehMapOfHomotopy`, whose interface
  already matches the source statement exactly, so no chapter-local wrapper theorem should remain.
-/

/- Lemma 13.9.2: for a square of cochain complexes that commutes up to homotopy, the induced
morphism between the standard mapping-cone triangles in the homotopy category `K(𝒜)` is exactly
the canonical mathlib construction `CochainComplex.mappingCone.trianglehMapOfHomotopy`. -/
recall CochainComplex.mappingCone.trianglehMapOfHomotopy

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜] [Preadditive 𝒜]
  [HasBinaryBiproducts 𝒜]
variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
variable {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/- Source-facing type specialization: a homotopy-commutative square of cochain maps induces a
morphism between the standard mapping-cone triangles in `K(𝒜)`. -/
#check (mappingCone.trianglehMapOfHomotopy H :
  mappingCone.triangleh φ₁ ⟶ mappingCone.triangleh φ₂)

end

/-! ### Lemma_13_9_3 (from Chap13) -/
noncomputable section

open CategoryTheory Limits

universe v u

namespace CochainComplex

open HomComplex

/- Domain-style sampling for Lemma 13.9.3:
- primary domain: homological algebra of cochain complexes, null-homotopies, and the
  mapping-cone / mapping-cocone factorization owners;
- inspected owner declarations:
  `HomologicalComplex.homotopyCofiber.desc`,
  `HomologicalComplex.homotopyCofiber.descEquiv`,
  `CochainComplex.mappingCone.desc`,
  `CochainComplex.mappingCocone.lift`;
- best owner abstraction: the canonical homotopy-cofiber factorization API, specialized in the
  cochain-complex model by `mappingCone.desc` and `mappingCocone.lift`;
- primitive data: a chosen null-homotopy `H : Homotopy (f ≫ g) 0`;
- derived API: direct use of the canonical factorization constructors
  `mappingCone.desc` and `mappingCocone.lift`, together with the source-facing existential
  consequences below.

Source/core/bridge triage:
- `source-facing`: the two existential factorization statements below, matching the textbook lemma;
- `core/canonical`: `homotopyCofiber.desc`, `homotopyCofiber.descEquiv`, `mappingCone.desc`, and
  `mappingCocone.lift`;
- `bridge/view`: the direct specialization of `mappingCone.desc` and `mappingCocone.lift` to a
  null-homotopy of `f ≫ g`, producing maps with source/target the textbook objects `C(f)^•` and
  `C(g)^•[-1]`.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L M : CochainComplex C ℤ}

/-- Lemma 13.9.3 (1): if the composite `f ≫ g` is homotopic to zero, then `g` factors through a
morphism from the mapping cone `C(f)^• = CochainComplex.mappingCone f` to `M^•`. -/
theorem comp_homotopic_to_zero_factors_through_mapping_cone
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    ∃ γ : mappingCone f ⟶ M, mappingCone.inr f ≫ γ = g := by
  refine ⟨mappingCone.desc f (Cochain.ofHomotopy H) g (by simp [δ_ofHomotopy H]), by simp⟩

/-- Lemma 13.9.3 (2): if the composite `f ≫ g` is homotopic to zero, then `f` factors through a
morphism `K^• ⟶ C(g)^•[-1]`, expressed canonically as a morphism to
`CochainComplex.mappingCocone g = (CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧`. -/
theorem comp_homotopic_to_zero_factors_through_mapping_cocone
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    ∃ γ : K ⟶ mappingCocone g, γ ≫ mappingCocone.fst g = f := by
  refine ⟨mappingCocone.lift g f (Cochain.ofHomotopy H.symm) (by
    rw [δ_ofHomotopy H.symm]
    simp), by simp⟩

end

end CochainComplex

/-! ### Definition_13_9_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]
variable {A B C : CochainComplex V ℤ}
variable (α : A ⟶ B) (β : B ⟶ C)

/- Source/core/bridge triage for Definition 13.9.4:
- primary domain: morphisms of cochain complexes and the split mono/epi structure on their
  components;
- inspected owner declarations:
  `HomologicalComplex.Hom.f`,
  `CategoryTheory.IsSplitMono`,
  `CategoryTheory.retraction`,
  `CategoryTheory.IsSplitEpi`,
  `CategoryTheory.section_`;
- best owner abstraction: the per-component owner classes `IsSplitMono` and `IsSplitEpi`; there
  is no separate canonical project/mathlib owner for the extra word “termwise”, so the correct
  public surface is the direct componentwise predicate on a complex morphism;
- layer: `bridge/view`; the numbered item only translates the textbook phrase “termwise split
  injection/surjection” into the canonical upstream owner classes, and should not introduce a new
  wrapper predicate.

Primitive data lives upstream inside `IsSplitMono (α.f n)` and `IsSplitEpi (β.f n)` for each
degree `n`. The chosen retractions/sections are derived API through `retraction` and `section_`,
while the component maps themselves come from the canonical owner projection `HomologicalComplex.Hom.f`.
Accordingly, the file only needs `[HasZeroMorphisms V]`: neither the component map projection nor
the split mono/epi owners use the stronger additive structure. This file should therefore reuse
those owners directly instead of packaging a parallel “termwise split” structure.
-/

/- Companion recalls: the relevant owner classes and their canonical chosen splitting maps. -/
recall IsSplitMono
recall retraction
recall IsSplitEpi
recall section_

/- Definition 13.9.4 (1): the source phrases this for cochain complexes in an additive category,
but the recalled componentwise split-monomorphism predicate already lives canonically in any
category with zero morphisms. Thus a morphism `α : A^• ⟶ B^•` is termwise split injective exactly
when each component `α.f n : A.X n ⟶ B.X n` is a split monomorphism. The canonical Lean
expression is the direct componentwise predicate below. -/
#check (∀ n : ℤ, IsSplitMono (α.f n))

/- Definition 13.9.4 (2): likewise, the componentwise split-epimorphism predicate only needs zero
morphisms. A morphism `β : B^• ⟶ C^•` is termwise split surjective exactly when each component
`β.f n : B.X n ⟶ C.X n` is a split epimorphism. The canonical Lean expression is the direct
componentwise predicate below. -/
#check (∀ n : ℤ, IsSplitEpi (β.f n))

end

end CochainComplex

/-! ### Lemma_13_9_5 (from Chap13) -/
noncomputable section

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory

universe v u

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {A B C D : CochainComplex V ℤ}
variable {f : A ⟶ B} {a : A ⟶ C} {b : B ⟶ D} {g : C ⟶ D}

local notation "Q" => quotient V (up ℤ)

/- Domain-style sampling for Lemma 13.9.5:
- primary domain: homotopy-commutative squares of cochain-complex morphisms together with
  termwise split mono/epi hypotheses on one side of the square;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `HomotopyCategory.quotient`,
  `HomotopyCategory.homotopyOfEq`,
  `CategoryTheory.IsSplitMono`,
  `CategoryTheory.IsSplitEpi`;
- best owner abstraction: the source-facing compatibility datum is a homotopy
  `Homotopy (f ≫ b) (a ≫ g)` between the two composites; the canonical core/view of that datum is
  the square `CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g)` in the homotopy category,
  while the termwise splitting assumptions remain the direct componentwise owners from
  `Definition_13_9_4`;
- primitive data: the four maps `f`, `a`, `b`, `g`, together with the componentwise split
  structure on `f.f n` or `g.f n`, and the chosen homotopy witnessing up-to-homotopy
  commutativity;
- derived API: the quotient-square reformulation of “commutes up to homotopy” via
  `HomotopyCategory.homotopyOfEq`, and equality of quotient classes of a replacement map via
  `HomotopyCategory.eq_of_homotopy`.

Source/core/bridge triage:
- `source-facing`: the two strictification existence lemmas below, phrased as existence of a
  homotopic strictifying replacement with a chosen homotopy
  `Homotopy (f ≫ b) (a ≫ g)`;
- `core/canonical`: `CommSq` for square-shaped compatibility in the homotopy category and the
  per-component owners `IsSplitMono` / `IsSplitEpi`;
- `bridge/view`: the `CommSq` above, formed using the canonical quotient functor `Q`, as the
  homotopy-category reformulation of the source hypothesis, and
  equality of quotient classes via `eq_of_homotopy`.
-/

-- Proof sketch: choose degreewise retractions of the split monomorphism `f`, pick a homotopy
-- between `f ≫ b` and `a ≫ g`, and compose its components with those retractions to obtain a
-- correction term on `B`. Subtracting the associated null-homotopic map from `b` gives a map
-- homotopic to `b` whose composite with `f` is exactly `a ≫ g`.
/-- Lemma 13.9.5 (1): if a square of morphisms of cochain complexes commutes up to homotopy and
the top map is termwise split monic, then the right map is homotopic to a morphism making the
square commute strictly. -/
theorem exists_homotopic_rightMap_of_termwiseSplitMono
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ (b' : B ⟶ D) (hbb' : Homotopy b b'), CommSq f a b' g := sorry

/-- Bridge/view form of Lemma 13.9.5 (1): if the square commutes in the homotopy category, then
the strictifying replacement may be chosen to represent the same morphism as `b` there. -/
theorem exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
    (sq : CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g))
    (hSplitMono : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ b' : B ⟶ D, (Q).map b = (Q).map b' ∧ CommSq f a b' g := by
  obtain ⟨b', hbb', hsq⟩ :=
    exists_homotopic_rightMap_of_termwiseSplitMono
      (homotopyOfEq _ _ (by simpa [Functor.map_comp] using sq.w)) hSplitMono
  exact ⟨b', eq_of_homotopy _ _ hbb', hsq⟩

-- Proof sketch: choose degreewise sections of the split epimorphism `g`, pick a homotopy
-- between `f ≫ b` and `a ≫ g`, and compose its components with those sections to obtain a
-- correction term on `A`. Adding the associated null-homotopic map to `a` gives a map homotopic
-- to `a` whose composite with `g` is exactly `f ≫ b`.
/-- Lemma 13.9.5 (2): if a square of morphisms of cochain complexes commutes up to homotopy and
the bottom map is termwise split epi, then the left map is homotopic to a morphism making the
square commute strictly. -/
theorem exists_homotopic_leftMap_of_termwiseSplitEpi
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ (a' : A ⟶ C) (haa' : Homotopy a a'), CommSq f a' b g := sorry

/-- Bridge/view form of Lemma 13.9.5 (2): if the square commutes in the homotopy category, then
the strictifying replacement may be chosen to represent the same morphism as `a` there. -/
theorem exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi
    (sq : CommSq ((Q).map f) ((Q).map a) ((Q).map b) ((Q).map g))
    (hSplitEpi : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ a' : A ⟶ C, (Q).map a = (Q).map a' ∧ CommSq f a' b g := by
  obtain ⟨a', haa', hsq⟩ :=
    exists_homotopic_leftMap_of_termwiseSplitEpi
      (homotopyOfEq _ _ (by simpa [Functor.map_comp] using sq.w)) hSplitEpi
  exact ⟨a', eq_of_homotopy _ _ haa', hsq⟩

end CochainComplex

/-! ### Lemma_13_9_6 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

/- Domain-style sampling for Lemma 13.9.6:
- primary domain: homological algebra of cochain complexes, mapping cones, homotopies, and
  boundedness conditions on cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCone`,
  `CochainComplex.mappingCone.homotopyToZeroOfId`,
  `HomotopyEquiv`,
  `ShortComplex`,
  `ShortComplex.Splitting`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`;
- best owner abstraction: the source-facing middle object is the canonical biproduct
  `L ⊞ mappingCone (𝟙 K)`, and the boundedness statements should reuse the canonical bounded-above
  and bounded owners `CochainComplex.minus` and `CochainComplex.bounded` rather than restating
  them as raw existential or conjunction predicates. The degreewise split short complex attached to
  the factorization should also be exposed directly as a `ShortComplex` together with its
  canonical `ShortComplex.Splitting`, rather than recreated downstream from raw maps;
- layer: `source-facing` for the factorization statement, with `HomotopyEquiv`,
  `ShortComplex`, `ShortComplex.Splitting`, `CochainComplex.minus`, and
  `CochainComplex.bounded` providing the `core/canonical` owners;
- primitive data: the canonical middle complex `L ⊞ mappingCone (𝟙 K)` and the morphism
  `biprod.lift α (mappingCone.inr (𝟙 K)) : K ⟶ L ⊞ mappingCone (𝟙 K)`;
- derived API: the projection `biprod.fst`, the section `biprod.inl`, the induced homotopy
  equivalence to `L`, the canonical short complex
  `K ⟶ splitMonoFactorizationObj K L ⟶ mappingCone α`, its degreewise splitting, and boundedness
  properties inherited from `mappingCone` and biproducts.
-/

/-- The canonical middle complex `L^• ⊞ C(1_{K^•})` used in the split-monomorphic factorization
of a morphism `α : K^• ⟶ L^•`. -/
abbrev splitMonoFactorizationObj (K L : CochainComplex C ℤ) : CochainComplex C ℤ :=
  L ⊞ mappingCone (𝟙 K)

/-- The canonical map `K^• ⟶ L^• ⊞ C(1_{K^•})` used in the split-monomorphic factorization of
`α : K^• ⟶ L^•`. -/
abbrev splitMonoFactorizationι (α : K ⟶ L) : K ⟶ splitMonoFactorizationObj K L :=
  biprod.lift α (mappingCone.inr (𝟙 K))

/-- The canonical map from `L^• ⊞ C(1_{K^•})` to the mapping cone `C(α)^•`. Together with
`splitMonoFactorizationι α`, it forms the degreewise split short complex attached to `α`. -/
def splitMonoFactorizationπ (α : K ⟶ L) :
    splitMonoFactorizationObj K L ⟶ mappingCone α :=
  biprod.desc (mappingCone.inr α)
    (-mappingCone.map (𝟙 K) α (𝟙 K) α (by simp))

@[simp] theorem splitMonoFactorizationι_comp_π (α : K ⟶ L) :
    splitMonoFactorizationι α ≫ splitMonoFactorizationπ α = 0 := by
  rw [splitMonoFactorizationπ, splitMonoFactorizationι]
  simp only [biprod.lift_desc, add_eq_zero_iff_eq_neg]
  rw [← neg_inj, neg_neg, mappingCone.map_eq_mapOfHomotopy]
  simpa using (mappingCone.triangleMapOfHomotopy_comm₂
    (Homotopy.ofEq (by simp : (𝟙 K) ≫ α = (𝟙 K) ≫ α))).symm

/-- The canonical short complex `K^• ⟶ L^• ⊞ C(1_{K^•}) ⟶ C(α)^•` attached to a morphism
`α : K^• ⟶ L^•`. -/
abbrev splitMonoFactorizationShortComplex (α : K ⟶ L) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (splitMonoFactorizationι α)
    (splitMonoFactorizationπ α)
    (splitMonoFactorizationι_comp_π α)

/-- The projection `L^• ⊞ C(1_{K^•}) ⟶ L^•` is a homotopy equivalence, with inverse the left
biproduct inclusion. -/
noncomputable def splitMonoFactorizationProjectionHomotopyEquiv (K L : CochainComplex C ℤ) :
    HomotopyEquiv (splitMonoFactorizationObj K L) L :=
  let p : splitMonoFactorizationObj K L ⟶ L := biprod.fst
  let i : L ⟶ splitMonoFactorizationObj K L := biprod.inl
  let q : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K) := biprod.snd
  let j : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L := biprod.inr
  { hom := p
    inv := i
    homotopyHomInvId := by
      let h₀ : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 := mappingCone.homotopyToZeroOfId K
      let h₁ : Homotopy (q ≫ j) 0 := by
        simpa using (h₀.compRight j).compLeft q
      let h₂ : Homotopy (p ≫ i + q ≫ j) (p ≫ i) := by
        simpa using Homotopy.add (Homotopy.refl (p ≫ i)) h₁
      exact h₂.symm.trans (Homotopy.ofEq (by simp [p, i, q, j]))
    homotopyInvHomId := by
      simpa [p, i] using Homotopy.refl (𝟙 L : L ⟶ L) }

/-- Each component of the canonical factorization map `K^• ⟶ L^• ⊞ C(1_{K^•})` is a split
monomorphism. -/
theorem splitMonoFactorizationι_f_isSplitMono (α : K ⟶ L) (n : ℤ) :
    IsSplitMono ((splitMonoFactorizationι α).f n) := by
  refine IsSplitMono.mk' ⟨(biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
      (mappingCone.snd (𝟙 K)).v n n (add_zero n), ?_⟩
  simp [splitMonoFactorizationι]

@[simp] theorem splitMonoFactorizationι_comp_fst (α : K ⟶ L) :
    splitMonoFactorizationι α ≫ (biprod.fst : splitMonoFactorizationObj K L ⟶ L) = α := by
  simp [splitMonoFactorizationObj, splitMonoFactorizationι]

private def splitTriangleSection (α : K ⟶ L) (n : ℤ) :
    (mappingCone α).X n ⟶ (splitMonoFactorizationObj K L).X n :=
  (mappingCone.snd α).v n n (add_zero n) ≫
      (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n -
    (mappingCone.fst α).1.v n (n + 1) rfl ≫
      (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫
        (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n

private lemma splitTriangleMap_to_mappingCone_inl (α : K ⟶ L) (n : ℤ) :
    (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫
      (mappingCone.map (𝟙 K) α (𝟙 K) α (by simp)).f n =
    (mappingCone.inl α).v (n + 1) n (by lia) := by
  simp [mappingCone.map]

private lemma splitTriangleMap_to_mappingCone_snd (α : K ⟶ L) (n : ℤ) :
    (mappingCone.map (𝟙 K) α (𝟙 K) α (by simp)).f n ≫
      (mappingCone.snd α).v n n (add_zero n) =
    (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n := by
  rw [mappingCone.ext_from_iff (𝟙 K) (n + 1) n rfl]
  constructor
  · simp [mappingCone.map]
  · have h :
        mappingCone.inr (𝟙 K) ≫ mappingCone.map (𝟙 K) α (𝟙 K) α (by simp) =
          α ≫ mappingCone.inr α := by
      rw [mappingCone.map_eq_mapOfHomotopy, mappingCone.triangleMapOfHomotopy_comm₂]
    have h' := congrArg (fun k ↦ k.f n) h
    simpa [Category.assoc] using congrArg
      (fun m ↦ m ≫ (mappingCone.snd α).v n n (add_zero n)) h'

private lemma splitTriangleMap_to_mappingCone_fst (α : K ⟶ L) (n : ℤ) :
    (mappingCone.map (𝟙 K) α (𝟙 K) α (by simp)).f n ≫
      (mappingCone.fst α).1.v n (n + 1) rfl =
    (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl := by
  rw [mappingCone.ext_from_iff (𝟙 K) (n + 1) n rfl]
  constructor
  · have h := splitTriangleMap_to_mappingCone_inl α n
    simpa [Category.assoc] using congrArg
      (fun m ↦ m ≫ (mappingCone.fst α).1.v n (n + 1) rfl) h
  · have h :
        mappingCone.inr (𝟙 K) ≫ mappingCone.map (𝟙 K) α (𝟙 K) α (by simp) =
          α ≫ mappingCone.inr α := by
      rw [mappingCone.map_eq_mapOfHomotopy, mappingCone.triangleMapOfHomotopy_comm₂]
    have h' := congrArg (fun k ↦ k.f n) h
    simpa [Category.assoc] using congrArg
      (fun m ↦ m ≫ (mappingCone.fst α).1.v n (n + 1) rfl) h'

/-- The canonical degreewise splitting of the short complex
`K^• ⟶ splitMonoFactorizationObj K L ⟶ C(α)^•`. -/
def splitMonoFactorizationSplitting (α : K ⟶ L) (n : ℤ) :
    ((splitMonoFactorizationShortComplex α).map (eval C _ n)).Splitting where
  r := (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
    (mappingCone.snd (𝟙 K)).v n n (add_zero n)
  s := splitTriangleSection α n
  f_r := by
    simp [splitMonoFactorizationι]
  s_g := by
    change splitTriangleSection α n ≫ (splitMonoFactorizationπ α).f n =
      𝟙 ((mappingCone α).X n)
    rw [show splitTriangleSection α n ≫ (splitMonoFactorizationπ α).f n =
        𝟙 ((mappingCone α).X n) by
      rw [mappingCone.ext_to_iff α n (n + 1) rfl]
      constructor
      · have h := splitTriangleMap_to_mappingCone_fst α n
        simpa [splitTriangleSection, splitMonoFactorizationπ, Category.assoc] using congrArg
          (fun m ↦ (mappingCone.fst α).1.v n (n + 1) rfl ≫
            (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫ m) h
      · simp [splitTriangleSection, splitMonoFactorizationπ, Category.assoc,
          splitTriangleMap_to_mappingCone_snd]]
  id := by
    let r' :
        (splitMonoFactorizationObj K L).X n ⟶ K.X n :=
      (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
        (mappingCone.snd (𝟙 K)).v n n (add_zero n)
    let s' :
        (mappingCone α).X n ⟶ (splitMonoFactorizationObj K L).X n :=
      splitTriangleSection α n
    have hsnd :
        (splitMonoFactorizationπ α).f n ≫ (mappingCone.snd α).v n n (add_zero n) =
          (biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n -
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n := by
      refine (isColimitOfPreserves (eval C (ComplexShape.up ℤ) n)
        (BinaryBiproduct.isColimit L (mappingCone (𝟙 K)))).hom_ext ?_
      intro j
      fin_cases j
      · change
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫
            (mappingCone.snd α).v n n (add_zero n) =
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
            ((biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n -
              (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
                (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n)
        simp [splitMonoFactorizationπ]
      · change
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫ (mappingCone.snd α).v n n (add_zero n) =
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
            ((biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n -
              (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
                (mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ α.f n)
        simp [splitMonoFactorizationπ, splitTriangleMap_to_mappingCone_snd, sub_eq_add_neg]
    have hfst :
        (splitMonoFactorizationπ α).f n ≫ (mappingCone.fst α).1.v n (n + 1) rfl =
          -((biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
            (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl) := by
      refine (isColimitOfPreserves (eval C (ComplexShape.up ℤ) n)
        (BinaryBiproduct.isColimit L (mappingCone (𝟙 K)))).hom_ext ?_
      intro j
      fin_cases j
      · change
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫
            (mappingCone.fst α).1.v n (n + 1) rfl =
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L).f n ≫
            (-((biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl))
        simp [splitMonoFactorizationπ]
      · change
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
              (splitMonoFactorizationπ α).f n ≫ (mappingCone.fst α).1.v n (n + 1) rfl =
          (biprod.inr : mappingCone (𝟙 K) ⟶ splitMonoFactorizationObj K L).f n ≫
            (-((biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl))
        simp [splitMonoFactorizationπ, splitTriangleMap_to_mappingCone_fst]
    refine (isLimitOfPreserves (eval C (ComplexShape.up ℤ) n)
      (BinaryBiproduct.isLimit L (mappingCone (𝟙 K)))).hom_ext ?_
    intro j
    fin_cases j
    · change
        ((r' ≫ (splitMonoFactorizationι α).f n) + (splitMonoFactorizationπ α).f n ≫ s') ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n =
          (𝟙 ((splitMonoFactorizationObj K L).X n)) ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L).f n
      dsimp [r', s', splitTriangleSection]
      simp [Preadditive.add_comp, splitMonoFactorizationι, hsnd, Category.assoc, sub_eq_add_neg]
    · change
        ((r' ≫ (splitMonoFactorizationι α).f n) + (splitMonoFactorizationπ α).f n ≫ s') ≫
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n =
          (𝟙 ((splitMonoFactorizationObj K L).X n)) ≫
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n
      dsimp [r', s', splitTriangleSection]
      simp only [Category.assoc, Int.reduceNeg, Preadditive.comp_sub, Preadditive.add_comp,
        biprod_lift_snd_f, Preadditive.sub_comp, biprod_inl_snd_f, comp_zero,
        biprod_inr_snd_f, Category.comp_id, zero_sub, Category.id_comp]
      have hfst' := congrArg
        (fun m ↦ -m ≫ (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia)) hfst
      have hfst'' :
          -(splitMonoFactorizationπ α).f n ≫
              (mappingCone.fst α).1.v n (n + 1) rfl ≫
              (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) =
            (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
              (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl ≫
              (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) := by
        simpa only [Category.assoc, Preadditive.neg_comp, neg_neg] using hfst'
      rw [hfst'']
      change
        (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
            ((mappingCone.snd (𝟙 K)).v n n (add_zero n) ≫ (mappingCone.inr (𝟙 K)).f n) +
          (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫
            ((mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl ≫
              (mappingCone.inl (𝟙 K)).v (n + 1) n (by lia)) =
          (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n
      rw [← Preadditive.comp_add]
      simpa [add_comm] using congrArg
        (fun m ↦
          (biprod.snd : splitMonoFactorizationObj K L ⟶ mappingCone (𝟙 K)).f n ≫ m)
        (mappingCone.id_X (𝟙 K) n (n + 1) rfl)

-- Proof sketch: take `\tilde L^• = L^• ⊞ C(1_{K^•})`, let `\tilde α` be the pair consisting of
-- `α` and the canonical cone inclusion `mappingCone.inr (𝟙 K)`. The termwise split monomorphism
-- is witnessed degreewise by the cone projection `mappingCone.snd (𝟙 K)`, while the projection
-- `biprod.fst : L ⊞ mappingCone (𝟙 K) ⟶ L` has section `biprod.inl`, with
-- `biprod.fst ≫ biprod.inl` homotopic to the identity because the cone summand is contractible
-- by `mappingCone.homotopyToZeroOfId`.
/-- Lemma 13.9.6: every morphism `α : K^• ⟶ L^•` factors through the canonical complex
`L^• ⊞ C(1_{K^•})` by a termwise split injection, and the projection to `L^•` has a section whose
composite with that projection is homotopic to the identity. -/
theorem splitMono_factorization_through_biproduct_mappingCone_id
    (α : K ⟶ L) :
    ∃ _ : Homotopy
        ((biprod.fst : splitMonoFactorizationObj K L ⟶ L) ≫
          (biprod.inl : L ⟶ splitMonoFactorizationObj K L))
        (𝟙 (splitMonoFactorizationObj K L)),
      (∀ n : ℤ, IsSplitMono ((splitMonoFactorizationι α).f n)) ∧
        splitMonoFactorizationι α ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L) = α ∧
        (biprod.inl : L ⟶ splitMonoFactorizationObj K L) ≫
            (biprod.fst : splitMonoFactorizationObj K L ⟶ L) = 𝟙 L := by
  refine ⟨(splitMonoFactorizationProjectionHomotopyEquiv K L).homotopyHomInvId, ?_⟩
  refine ⟨splitMonoFactorizationι_f_isSplitMono α, ?_, ?_⟩
  · exact splitMonoFactorizationι_comp_fst α
  · simp

lemma mappingCone_id_plus (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (mappingCone (𝟙 K)) := by
  obtain ⟨n, hn⟩ := (CochainComplex.plus_iff C K).1 hK
  refine (CochainComplex.plus_iff C (mappingCone (𝟙 K))).2 ⟨n - 1, ?_⟩
  rw [isStrictlyGE_iff]
  intro i hi
  letI := hn
  rw [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n (i + 1) (by lia), K.isZero_of_isStrictlyGE n i (by lia)⟩

lemma mappingCone_id_boundedAbove (hK : CochainComplex.minus C K) :
    CochainComplex.minus C (mappingCone (𝟙 K)) := by
  obtain ⟨n, hn⟩ := (CochainComplex.minus_iff C K).1 hK
  refine (CochainComplex.minus_iff C (mappingCone (𝟙 K))).2 ⟨n, ?_⟩
  rw [isStrictlyLE_iff]
  intro i hi
  letI := hn
  rw [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE n (i + 1) (by lia), K.isZero_of_isStrictlyLE n i (by lia)⟩

-- Proof sketch: if `K` and `L` are bounded below, choose lower bounds for both; the cone of the
-- identity on `K` is again bounded below, and binary biproducts of bounded-below complexes remain
-- bounded below.
/-- The canonical factorization object is bounded below whenever both source and target complexes
are bounded below. -/
theorem splitMonoFactorizationObj_plus
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (splitMonoFactorizationObj K L) := by
  simpa [splitMonoFactorizationObj] using
    (CochainComplex.plus C).prop_of_isColimit_binaryCofan
      (BinaryBiproduct.isColimit L (mappingCone (𝟙 K))) hL (mappingCone_id_plus hK)

-- Proof sketch: choose upper bounds for `K` and `L`; the mapping cone of the identity on `K` is
-- still bounded above, and the biproduct with `L` preserves this bounded-above property.
/-- The canonical factorization object is bounded above whenever both source and target complexes
are bounded above. -/
theorem splitMonoFactorizationObj_boundedAbove
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (splitMonoFactorizationObj K L) := by
  simpa [splitMonoFactorizationObj] using
    (CochainComplex.minus C).prop_of_isLimit_binaryFan
      (BinaryBiproduct.isLimit L (mappingCone (𝟙 K))) hL
      (mappingCone_id_boundedAbove hK)

-- Proof sketch: combine the bounded-below statement for `K^+` with the bounded-above statement
-- for `K^-`; this gives the boundedness assertion for the canonical factorization object.
/-- The canonical factorization object is bounded whenever both source and target complexes are
bounded. -/
theorem splitMonoFactorizationObj_bounded
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (splitMonoFactorizationObj K L) := by
  rcases (CochainComplex.bounded_iff C K).1 hK with ⟨hKplus, hKminus⟩
  rcases (CochainComplex.bounded_iff C L).1 hL with ⟨hLplus, hLminus⟩
  exact (CochainComplex.bounded_iff C (splitMonoFactorizationObj K L)).2
    ⟨splitMonoFactorizationObj_plus hKplus hLplus,
      splitMonoFactorizationObj_boundedAbove hKminus hLminus⟩

end CochainComplex

/-! ### Remark_13_9_7 (from Chap13) -/
universe v u

open CategoryTheory
open CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable (K L : CochainComplex C ℤ)

/- Domain-style sampling for Remark 13.9.7:
- primary domain: CM5b factorization of morphisms of cochain complexes, viewed through homotopy
  equivalences of mapping-cone-based factorization objects;
- sampled canonical declarations:
  `HomotopyEquiv`,
  `HomotopyEquiv.homotopyHomInvId`,
  `cm5b.p`,
  `cm5b.homotopyEquiv`;
- source/core/bridge triage:
  `core/canonical`: `HomotopyEquiv`,
  `bridge/view`: `cm5b.homotopyEquiv K L` and its field
    `(cm5b.homotopyEquiv K L).homotopyHomInvId`.

The primitive data are already owned by `HomotopyEquiv`: the two comparison morphisms and the two
homotopies from their composites to the identities. The CM5b construction in mathlib packages the
relevant factorization object and the projection `cm5b.p` into the canonical homotopy equivalence
`cm5b.homotopyEquiv`, so this remark should recall that owner rather than introduce a parallel
chapter-local wrapper for the same homotopy. -/

/- Remark 13.9.7: the elementwise computation of the proof above is the explicit verification that,
for the standard CM5b factorization `mappingCone (𝟙 (cm5b.I K)) ⊞ L`, the projection-section
composite is homotopic to the identity on the factorization object, equivalently
`id - π ≫ s = d h + h d`. This is the canonical owner `cm5b.homotopyEquiv`, whose relevant
component is the field `homotopyHomInvId`. -/
recall cm5b.homotopyEquiv

/- Companion check: the homotopy asserted in the remark is exactly the `homotopyHomInvId` field of
the canonical CM5b homotopy equivalence. -/
#check (cm5b.homotopyEquiv K L).homotopyHomInvId

/-! ### Lemma_13_9_8 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

/- Domain-style sampling for Lemma 13.9.8:
- primary domain: homological algebra of cochain complexes, mapping cocones, homotopies, and
  boundedness conditions on cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCocone`,
  `HomotopyEquiv`,
  `CategoryTheory.IsSplitEpi`,
  `CochainComplex.splitMonoFactorizationProjectionHomotopyEquiv`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`;
- best owner abstraction: the source-facing middle object is the canonical biproduct
  `K ⊞ mappingCocone (𝟙 L)`, while the reusable retract data should be organized around the
  canonical owner `HomotopyEquiv (K ⊞ mappingCocone (𝟙 L)) K`, and split-epimorphicity and
  boundedness should reuse the canonical owners `IsSplitEpi`, `CochainComplex.minus`, and
  `CochainComplex.bounded` instead of a conjunction-heavy existential package;
- layer: `source-facing` for the factorization statement, with `HomotopyEquiv`, `IsSplitEpi`,
  `CochainComplex.minus`, and `CochainComplex.bounded` providing the `core/canonical` owners;
- primitive data: the canonical middle complex `K ⊞ mappingCocone (𝟙 L)` and the canonical map
  `biprod.desc α (mappingCocone.fst (𝟙 L)) : K ⊞ mappingCocone (𝟙 L) ⟶ L`;
- derived API: the homotopy equivalence from the middle object to `K`, the termwise
  split-epimorphicity of `biprod.desc α (mappingCocone.fst (𝟙 L))`, the factorization identity
  `biprod.inl ≫ biprod.desc α (mappingCocone.fst (𝟙 L)) = α`, and boundedness inherited from the
  cocone summand and the biproduct.
-/

/-- The projection `K^• ⊞ C(1_{L^•[-1]}) ⟶ K^•` is a homotopy equivalence, with inverse the left
biproduct inclusion. -/
noncomputable def splitEpiFactorizationProjectionHomotopyEquiv (K L : CochainComplex C ℤ) :
    HomotopyEquiv (K ⊞ mappingCocone (𝟙 L)) K :=
  let p : K ⊞ mappingCocone (𝟙 L) ⟶ K := biprod.fst
  let i : K ⟶ K ⊞ mappingCocone (𝟙 L) := biprod.inl
  let q : K ⊞ mappingCocone (𝟙 L) ⟶ mappingCocone (𝟙 L) := biprod.snd
  let j : mappingCocone (𝟙 L) ⟶ K ⊞ mappingCocone (𝟙 L) := biprod.inr
  { hom := p
    inv := i
    homotopyHomInvId := by
      let h₀ : Homotopy (𝟙 (mappingCocone (𝟙 L))) 0 := by
        let hCone :
            Homotopy
              (𝟙 (mappingCone (𝟙 L)))
              (0 : mappingCone (𝟙 L) ⟶ mappingCone (𝟙 L)) :=
          mappingCone.homotopyToZeroOfId L
        simpa [mappingCocone] using hCone.shift (-1)
      let h₁ : Homotopy (q ≫ j) 0 := by
        simpa using (h₀.compRight j).compLeft q
      let h₂ : Homotopy (p ≫ i + q ≫ j) (p ≫ i) := by
        simpa using Homotopy.add (Homotopy.refl (p ≫ i)) h₁
      exact h₂.symm.trans (Homotopy.ofEq (by simp [p, i, q, j]))
    homotopyInvHomId := by
      simpa [p, i] using Homotopy.refl (𝟙 K : K ⟶ K) }

/-- Each component of the canonical factorization map
`K^• ⊞ C(1_{L^•[-1]}) ⟶ L^•` is a split epimorphism. -/
theorem splitEpiFactorizationDesc_f_isSplitEpi (α : K ⟶ L) (n : ℤ) :
    IsSplitEpi ((biprod.desc α (mappingCocone.fst (𝟙 L))).f n) := by
  refine IsSplitEpi.mk' ⟨(mappingCocone.inl (𝟙 L)).v n n (add_zero n) ≫
      (biprod.inr : mappingCocone (𝟙 L) ⟶ K ⊞ mappingCocone (𝟙 L)).f n, ?_⟩
  simp

@[simp] theorem splitEpiFactorizationInl_comp_desc (α : K ⟶ L) :
    (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
        biprod.desc α (mappingCocone.fst (𝟙 L)) = α := by
  simp

@[simp] theorem splitEpiFactorizationInl_comp_fst :
    (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
        (biprod.fst : K ⊞ mappingCocone (𝟙 L) ⟶ K) = 𝟙 K := by
  simp

-- Proof sketch: take `\tilde K^• = K^• ⊞ mappingCocone (𝟙 L)`, where `mappingCocone (𝟙 L)` is the
-- shifted cone `C(1_{L^•[-1]})`. Let `i` be the left biproduct inclusion, `s` the left biproduct
-- projection, and let `\tilde α` be the biproduct descendent of `α` and
-- `mappingCocone.fst (𝟙 L)`. Degreewise split epimorphy is witnessed by the right biproduct
-- inclusion composed with `mappingCocone.inl (𝟙 L)`, and the cocone summand is contractible
-- because `mappingCone (𝟙 L)` is contractible, so `s ≫ i` is homotopic to the identity.
/-- Lemma 13.9.8: every morphism `α : K^• ⟶ L^•` factors through the canonical complex
`K^• ⊞ C(1_{L^•[-1]})` by a termwise split epimorphism, and the projection to `K^•` has a section
whose composite with that section is homotopic to the identity. -/
theorem splitEpi_factorization_through_biproduct_mappingCocone_id
    (α : K ⟶ L) :
    ∃ _ : Homotopy
        ((biprod.fst : K ⊞ mappingCocone (𝟙 L) ⟶ K) ≫
          (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)))
        (𝟙 (K ⊞ mappingCocone (𝟙 L))),
      (∀ n : ℤ, IsSplitEpi ((biprod.desc α (mappingCocone.fst (𝟙 L))).f n)) ∧
        (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
            biprod.desc α (mappingCocone.fst (𝟙 L)) = α ∧
        (biprod.inl : K ⟶ K ⊞ mappingCocone (𝟙 L)) ≫
            (biprod.fst : K ⊞ mappingCocone (𝟙 L) ⟶ K) = 𝟙 K := by
  refine ⟨(splitEpiFactorizationProjectionHomotopyEquiv K L).homotopyHomInvId, ?_⟩
  refine ⟨splitEpiFactorizationDesc_f_isSplitEpi α, ?_, ?_⟩
  · exact splitEpiFactorizationInl_comp_desc α
  · exact splitEpiFactorizationInl_comp_fst

lemma mappingCocone_id_plus (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (mappingCocone (𝟙 L)) := by
  have hCone : CochainComplex.plus C (mappingCone (𝟙 L)) := mappingCone_id_plus hL
  simpa [mappingCocone] using (CochainComplex.plus C).le_shift (-1) (mappingCone (𝟙 L)) hCone

lemma mappingCocone_id_boundedAbove (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (mappingCocone (𝟙 L)) := by
  have hCone : CochainComplex.minus C (mappingCone (𝟙 L)) := mappingCone_id_boundedAbove hL
  simpa [mappingCocone] using (CochainComplex.minus C).le_shift (-1) (mappingCone (𝟙 L)) hCone

-- Proof sketch: if `K` and `L` are bounded below, then `mappingCone (𝟙 L)` is bounded below, so
-- its shift `mappingCocone (𝟙 L)` is still bounded below. Binary biproducts of bounded-below
-- cochain complexes remain bounded below.
/-- The canonical split-epimorphic factorization object is bounded below whenever both source and
target complexes are bounded below. -/
theorem splitEpiFactorization_plus
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (K ⊞ mappingCocone (𝟙 L)) := by
  simpa using
    (CochainComplex.plus C).prop_of_isColimit_binaryCofan
      (BinaryBiproduct.isColimit K (mappingCocone (𝟙 L))) hK (mappingCocone_id_plus hL)

-- Proof sketch: choose upper bounds for `K` and `L`. The mapping cone of the identity on `L` is
-- bounded above, hence so is the shifted cocone `mappingCocone (𝟙 L)`, and binary biproducts
-- preserve bounded-above cochain complexes.
/-- The canonical split-epimorphic factorization object is bounded above whenever both source and
target complexes are bounded above. -/
theorem splitEpiFactorization_boundedAbove
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (K ⊞ mappingCocone (𝟙 L)) := by
  simpa using
    (CochainComplex.minus C).prop_of_isLimit_binaryFan
      (BinaryBiproduct.isLimit K (mappingCocone (𝟙 L))) hK (mappingCocone_id_boundedAbove hL)

-- Proof sketch: combine the bounded-below and bounded-above statements for the canonical
-- split-epimorphic factorization object.
/-- The canonical split-epimorphic factorization object is bounded whenever both source and target
complexes are bounded. -/
theorem splitEpiFactorization_bounded
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (K ⊞ mappingCocone (𝟙 L)) := by
  rcases (CochainComplex.bounded_iff C K).1 hK with ⟨hKplus, hKminus⟩
  rcases (CochainComplex.bounded_iff C L).1 hL with ⟨hLplus, hLminus⟩
  exact (CochainComplex.bounded_iff C (K ⊞ mappingCocone (𝟙 L))).2
    ⟨splitEpiFactorization_plus hKplus hLplus,
      splitEpiFactorization_boundedAbove hKminus hLminus⟩

end CochainComplex

/-! ### Definition_13_9_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape HomologicalComplex

variable {C : Type*} [Category C] [Preadditive C]
variable (S : ShortComplex (CochainComplex C ℤ))

/- Source/core/bridge triage for Definition 13.9.9:
- primary domain: termwise split exact sequences of cochain complexes and the induced connecting
  morphism and associated triangle.
- inspected declarations in this domain:
  `ShortComplex.map`,
  `HomologicalComplex.eval`,
  `ShortComplex.Splitting`,
  `ShortComplex.Splitting.shortExact`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.trianglehOfDegreewiseSplit`.
- best owner abstraction: the source-facing notion is a short complex
  `S : ShortComplex (CochainComplex C ℤ)` whose evaluation in each degree,
  `S.map (eval C (up ℤ) n)`, admits a splitting, expressed canonically as the existence property
  `∀ n : ℤ, Nonempty ((S.map (eval C (up ℤ) n)).Splitting)`. This direct `ShortComplex.map` view
  is the owner-level way the mathlib degreewise-split constructions are stated, so no parallel
  chapter alias is needed here. After choosing a witness
  `σ : ∀ n : ℤ, (S.map (eval C (up ℤ) n)).Splitting`, mathlib derives the connecting morphism
  `CochainComplex.homOfDegreewiseSplit S σ` and the associated triangle
  `CochainComplex.triangleOfDegreewiseSplit S σ`. Passing this triangle to the homotopy category
  gives the bridge/view `CochainComplex.trianglehOfDegreewiseSplit S σ`.
- layer:
  `source-facing`: the short complex `S` together with degreewise splitness as an existence
    property;
  `core/canonical`: `ShortComplex`, degreewise `ShortComplex.Splitting`,
    `CochainComplex.homOfDegreewiseSplit`, and `CochainComplex.triangleOfDegreewiseSplit`;
  `bridge/view`: `CochainComplex.trianglehOfDegreewiseSplit`.
- primitive data: exactly the short complex `S` and the degreewise splitness condition
  `∀ n : ℤ, Nonempty ((S.map (eval C (up ℤ) n)).Splitting)`.
- derived API: after choosing a splitting family `σ`, one gets
  exactness in each degree from `ShortComplex.Splitting.shortExact` when `C` has a zero object,
  `CochainComplex.homOfDegreewiseSplit S σ`,
  `CochainComplex.triangleOfDegreewiseSplit S σ`, and its homotopy-category image
  `CochainComplex.trianglehOfDegreewiseSplit S σ`. The dependence on that choice is handled
  separately in Lemma 13.9.10.
-/

/- Definition 13.9.9: a termwise split exact sequence of cochain complexes is a short complex
whose degreewise short complex in each degree admits a splitting. -/
#check (∀ n : ℤ, Nonempty ((S.map (eval C (up ℤ) n)).Splitting))

/- Companion recall: a chosen splitting in one degree is the canonical owner
`ShortComplex.Splitting`. -/
recall ShortComplex.Splitting

section

variable [HasZeroObject C]

/- Companion recall: when `C` has a zero object, exactness in each degree is derived from a
chosen splitting via
`ShortComplex.Splitting.shortExact`; it is not extra primitive data in Definition 13.9.9. -/
recall ShortComplex.Splitting.shortExact

end

section

variable (σ : ∀ n : ℤ, (S.map (eval C (up ℤ) n)).Splitting)

/- Companion check: after choosing a degreewise splitting family `σ`, mathlib constructs the
canonical connecting morphism `CochainComplex.homOfDegreewiseSplit S σ :
S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧`. The independence of this choice is deferred to Lemma 13.9.10. -/
recall CochainComplex.homOfDegreewiseSplit

/- Companion check: the associated triangle of cochain complexes is the canonical owner
`CochainComplex.triangleOfDegreewiseSplit S σ`. -/
recall CochainComplex.triangleOfDegreewiseSplit

/- Downstream bridge check: applying the quotient functor from cochain complexes to the homotopy
category sends `CochainComplex.triangleOfDegreewiseSplit S σ` to
`CochainComplex.trianglehOfDegreewiseSplit S σ`, used in Definition 13.10.1. -/
recall CochainComplex.trianglehOfDegreewiseSplit

end

/-! ### Lemma_13_9_10 (from Chap13) -/
open CategoryTheory CategoryTheory.Pretriangulated ComplexShape HomologicalComplex
open CategoryTheory.CochainComplex

universe u v

namespace CochainComplex

section

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable (S : ShortComplex (CochainComplex V ℤ))
variable (σ σ' : ∀ n : ℤ, (degreewiseShortComplex S n).Splitting)

local notation "Q" => HomotopyCategory.quotient V (up ℤ)

/- Domain-style sampling for Lemma 13.9.10:
- primary domain: degreewise split short complexes of cochain complexes and the induced triangles
  in the homotopy category;
- inspected owner declarations:
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.homOfDegreewiseSplit`,
  `CochainComplex.sectionDifference`,
  `CochainComplex.homOfDegreewiseSplit_homotopy_of_splitting_difference`,
  `Triangle.isoMk`;
- best owner abstraction: the bridge/view owner is
  `CochainComplex.trianglehOfDegreewiseSplit S σ`, so the comparison for two splittings of the
  same short complex should be a thin triangle isomorphism built from identities on objects and
  the Chapter 12 owner homotopy theorem for the connecting morphisms;
- primitive data: the short complex `S` and the two degreewise splitting families `σ`, `σ'`;
- derived API: the induced identity-on-objects triangle isomorphism. The three commutativity
  equalities are proof data for that isomorphism, not standalone public API.

Source/core/bridge triage:
- `source-facing`: the comparison between the triangles attached to the same termwise split short
  complex with two splitting choices;
- `core/canonical`: `trianglehOfDegreewiseSplit`, `homOfDegreewiseSplit`,
  `sectionDifference`, `homOfDegreewiseSplit_homotopy_of_splitting_difference`, and
  `Triangle.isoMk`;
- `bridge/view`: the resulting identity-on-objects triangle isomorphism.
-/

-- Proof sketch: the first two arrows in `trianglehOfDegreewiseSplit S σ` depend only on `S.f` and
-- `S.g`, so the corresponding squares commute by `simp`. For the third arrow, the canonical
-- section-difference family `hⁿ = s'ⁿ ≫ rⁿ` satisfies
-- `(σ' n).s = (σ n).s + hⁿ ≫ fⁿ`; Lemma 12.14.12 then shows that the two connecting morphisms are
-- homotopic, hence equal in the homotopy category.
/-- Lemma 13.9.10: for two choices of degreewise splittings of the same termwise split exact
sequence of cochain complexes, the associated triangles in the homotopy category are isomorphic by
the identity on all three terms. -/
noncomputable def trianglehOfDegreewiseSplit_iso_of_splittings :
    trianglehOfDegreewiseSplit S σ ≅ trianglehOfDegreewiseSplit S σ' :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [triangleOfDegreewiseSplit])
    (by simp [triangleOfDegreewiseSplit])
    (by
      let h :
          ∀ n : ℤ, (degreewiseShortComplex S n).X₃ ⟶ (degreewiseShortComplex S n).X₁ :=
        fun n ↦ (σ' n).s ≫ (σ n).r
      have hs : sectionDifference S σ σ' h := by
        intro n
        change (σ' n).s = (σ n).s + ((σ' n).s ≫ (σ n).r) ≫
          (degreewiseShortComplex S n).f
        rw [Category.assoc, (σ n).r_f, Preadditive.comp_sub, Category.comp_id,
          (σ' n).s_g_assoc]
        abel
      simpa [triangleOfDegreewiseSplit] using
        congrArg
          (fun k ↦ k ≫ (Functor.commShiftIso Q 1).hom.app S.X₁)
          (HomotopyCategory.eq_of_homotopy _ _
            (homOfDegreewiseSplit_homotopy_of_splitting_difference S σ σ' h hs)).symm)

end

end CochainComplex

/-! ### Remark_13_9_11 (from Chap13) -/
open CategoryTheory ComplexShape HomologicalComplex
open CochainComplex

local notation "Cpx" => CochainComplex AddCommGrpCat ℤ

/- Domain-style sampling:
- primary domain: cochain complexes, degreewise split short complexes, and homotopy-category
  commutative squares;
- relevant owner declarations inspected:
  `ShortComplex.map`,
  `HomologicalComplex.eval`,
  `ShortComplex.Splitting`,
  `ShortComplex.Hom`,
  `exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono`,
  `exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi`,
  `comp_eq_zero_in_homotopyCategory_of_termwiseSplit`;
- best owner abstraction: the rows are canonically `ShortComplex` objects, while their termwise
  split exactness is the Chapter `13` owner existence property
  `∀ n, Nonempty ((S.map (eval AddCommGrpCat (up ℤ) n)).Splitting)`
  rather than chosen public splitting data; the homotopy-category compatibility data are
  canonically `CommSq`, while any strict replacement should be expressed by the row-morphism owner
  `ShortComplex.Hom` with fixed outer components rather than by a bespoke package of two squares;
- source/core/bridge triage:
  `source-facing`: the existence of a counterexample to strictifying a homotopy-commutative
    diagram between termwise split exact sequences of cochain complexes;
  `core/canonical`: `ShortComplex`, degreewise `ShortComplex.Splitting`, `CommSq`, and
    `ShortComplex.Hom`;
  `bridge/view`: equality in the homotopy category via the quotient functor `Q`.

Primitive data here is the pair of short complexes and the three vertical maps between their
terms. The termwise split condition is a genuine existence property and should therefore stay as
`Nonempty`-valued degreewise splitness rather than exposing a chosen family of splittings. The
homotopy-commutativity assumptions are expressed directly through `CommSq`, while the claim that a
strict replacement exists is expressed by the canonical owner `S₁ ⟶ S₂` together with fixed outer
components and equality of the middle quotient class, without packaging them into local wrapper
structures.
-/

-- Proof sketch: use the counterexample from Examples, Equation `(110.64.0.1)`, whose two rows are
-- degreewise split short exact sequences of complexes and whose outer squares commute only in the
-- homotopy category. If a homotopic replacement `b'` of the middle map existed making both
-- squares commute strictly, the induced trace computation would become additive, contradicting the
-- example.
/-- Remark 13.9.11: there exists a counterexample in `AddCommGrpCat` showing that a morphism
between the middle terms of two termwise split exact sequences of cochain complexes cannot in
general be replaced by a homotopic morphism making the homotopy-commutative diagram strictly
commutative in the category of complexes. -/
theorem exists_termwiseSplit_counterexample_to_middleMap_strictification :
    let Q := HomotopyCategory.quotient AddCommGrpCat (up ℤ)
    ∃ (S₁ S₂ : ShortComplex Cpx) (a : S₁.X₁ ⟶ S₂.X₁) (b : S₁.X₂ ⟶ S₂.X₂)
      (c : S₁.X₃ ⟶ S₂.X₃),
      (∀ n : ℤ, Nonempty ((S₁.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      (∀ n : ℤ, Nonempty ((S₂.map (eval AddCommGrpCat (up ℤ) n)).Splitting)) ∧
      CommSq (Q.map S₁.f) (Q.map a) (Q.map b) (Q.map S₂.f) ∧
      CommSq (Q.map S₁.g) (Q.map b) (Q.map c) (Q.map S₂.g) ∧
      ¬ ∃ φ : S₁ ⟶ S₂, φ.τ₁ = a ∧ φ.τ₃ = c ∧ Q.map φ.τ₂ = Q.map b := sorry

/-! ### Lemma_13_9_12 (from Chap13) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex
open CategoryTheory.Pretriangulated

universe v u

section

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V] [HasBinaryBiproducts V]

local notation "Q" => HomotopyCategory.quotient V (up ℤ)

/- Domain-style sampling:
- primary domain: degreewise split short complexes of cochain complexes, their canonical
  distinguished triangles in the homotopy category, and the exact Hom-sequence segment that forces
  a middle composite to vanish;
- sampled owner declarations:
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`;
- best owner abstraction: the distinguished triangle
  `CochainComplex.trianglehOfDegreewiseSplit S₂ σ₂` attached to a chosen degreewise splitting of
  the middle termwise split exact sequence; the public source-facing owner data are only `S₂`
  together with the existence property `∀ n : ℤ, Nonempty ((S₂.map (eval V (up ℤ) n)).Splitting)`,
  as established in `Definition_13_9_9`;
- primitive data: the middle short complex `S₂`, its degreewise split existence property,
  arbitrary source and target cochain complexes for the maps into and out of `S₂.X₂`, and the two
  vanishing
  composites
  `(HomotopyCategory.quotient V (up ℤ)).map b ≫ (HomotopyCategory.quotient V (up ℤ)).map S₂.g = 0`
  and
  `(HomotopyCategory.quotient V (up ℤ)).map S₂.f ≫ (HomotopyCategory.quotient V (up ℤ)).map b' = 0`;
- derived API: any ambient outer split short complexes from the textbook diagram are unnecessary
  for this exactness argument once the middle row is expressed through its owner triangle. A chosen
  splitting family `σ₂` is bridge-level proof data, not part of the public vanishing statement.

Source/core/bridge triage:
- `source-facing`: the Stacks-project vanishing statement for the composite of the two middle maps;
- `core/canonical`: the middle distinguished triangle and the exactness owners
  `Triangle.coyoneda_exact₂` and `Triangle.yoneda_exact₂`;
- `bridge/view`: the passage from a termwise split short complex to its distinguished triangle via
  `trianglehOfDegreewiseSplit`.
-/

-- Proof sketch: view the middle termwise split short complex `S₂` through its canonical
-- distinguished triangle in the homotopy category. Exactness of `Hom(Q.obj X, -)` at the middle
-- term factors `Q.map b` through `Q.map S₂.f`, while exactness of `Hom(-, Q.obj Y)` factors
-- `Q.map b'` through `Q.map S₂.g`.
-- Their composite is therefore a multiple of
-- `Q.map S₂.f ≫ Q.map S₂.g = 0`.
/-- Lemma 13.9.12: let `S₂` be a termwise split exact sequence of cochain complexes in an additive
category, encoded as a short complex with a splitting after evaluation in every degree. If
`b : X ⟶ S₂.X₂` and `b' : S₂.X₂ ⟶ Y` become composable maps in the homotopy category `K(V)` with
`Q(b) ≫ Q(S₂.g) = 0` and `Q(S₂.f) ≫ Q(b') = 0`, then `Q(b) ≫ Q(b') = 0`. -/
theorem comp_eq_zero_in_homotopyCategory_of_termwiseSplit
    {S₂ : ShortComplex (CochainComplex V ℤ)}
    (hσ₂ : ∀ n : ℤ, Nonempty ((S₂.map (eval V (up ℤ) n)).Splitting))
    {X Y : CochainComplex V ℤ}
    {b : X ⟶ S₂.X₂} {b' : S₂.X₂ ⟶ Y}
    (hb_right : (Q).map b ≫ (Q).map S₂.g = 0)
    (hb'_left : (Q).map S₂.f ≫ (Q).map b' = 0) :
    (Q).map b ≫ (Q).map b' = 0 := by
  classical
  let σ₂ : ∀ n : ℤ, (S₂.map (eval V (up ℤ) n)).Splitting := fun n ↦ Classical.choice (hσ₂ n)
  let T := CochainComplex.trianglehOfDegreewiseSplit S₂ σ₂
  have hT : T ∈ distTriang (HomotopyCategory V (up ℤ)) :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S₂, σ₂, ⟨Iso.refl _⟩⟩
  obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT ((Q).map b) (by simpa [T] using hb_right)
  obtain ⟨c, hc⟩ := T.yoneda_exact₂ hT ((Q).map b') (by simpa [T] using hb'_left)
  calc
    (Q).map b ≫ (Q).map b' = (a ≫ T.mor₁) ≫ (Q).map b' := by
      exact congrArg (fun f ↦ f ≫ (Q).map b') ha
    _ = (a ≫ T.mor₁) ≫ (T.mor₂ ≫ c) := by
      exact congrArg (fun f ↦ (a ≫ T.mor₁) ≫ f) hc
    _ = a ≫ (T.mor₁ ≫ T.mor₂) ≫ c := by simp [Category.assoc]
    _ = 0 := by rw [comp_distTriang_mor_zero₁₂ _ hT, zero_comp, comp_zero]

end

/-! ### Lemma_13_9_13 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open CochainComplex HomotopyCategory

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Limits.HasZeroObject 𝒜] [Preadditive 𝒜]
  [Limits.HasBinaryBiproducts 𝒜]
variable {K₁ L₁ K₂ L₂ : CochainComplex 𝒜 ℤ}
variable {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}

/- Domain-style sampling for Lemma 13.9.13:
- primary domain: distinguished mapping-cone triangles in the homotopy category and the
  pretriangulated two-out-of-three isomorphism theorem for triangle morphisms;
- sampled owner declarations:
  `CochainComplex.mappingCone.triangleh`,
  `HomotopyCategory.mappingCone_triangleh_distinguished`,
  `CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`,
  `CochainComplex.mappingCone.trianglehMapOfHomotopy`;
- best owner abstraction:
  `source-facing`: a morphism between the two standard mapping-cone triangles attached to `f₁`
    and `f₂` in `K(𝒜)`;
  `core/canonical`: the owner theorem `Pretriangulated.isIso₃_of_isIso₁₂` on distinguished
    triangles;
  `bridge/view`: the canonical fact that each standard mapping-cone triangle is distinguished,
    namely `HomotopyCategory.mappingCone_triangleh_distinguished`.

Primitive data are only the triangle morphism `φ` and the isomorphism assumptions on `φ.hom₁` and
`φ.hom₂`. The conclusion that `φ.hom₃` is an isomorphism is derived API from the canonical owner
theorem, so this file should keep only the thin source-facing specialization and not a parallel
triangle-level wrapper.
-/

-- Proof sketch: the standard mapping-cone triangles of `f₁` and `f₂` are distinguished in
-- `K(𝒜)` by `HomotopyCategory.mappingCone_triangleh_distinguished`. Apply the triangulated
-- two-out-of-three theorem `Pretriangulated.isIso₃_of_isIso₁₂` to the given morphism of
-- triangles.
/-- Lemma 13.9.13: for a morphism of the standard mapping-cone triangles in the homotopy category
`K(\mathcal A)`, if the first two components are isomorphisms, then the third component is also
an isomorphism. This is the canonical `K(\mathcal A)` formulation of the statement that if the
maps on `K_1^\bullet` and `L_1^\bullet` are homotopy equivalences, then so is the induced map on
cones. -/
theorem mappingCone_triangleh_isIso₃_of_isIso₁₂
    (φ : mappingCone.triangleh f₁ ⟶ mappingCone.triangleh f₂)
    [IsIso φ.hom₁] [IsIso φ.hom₂] :
    IsIso φ.hom₃ := by
  simpa using
    (isIso₃_of_isIso₁₂ φ
      (mappingCone_triangleh_distinguished f₁)
      (mappingCone_triangleh_distinguished f₂)
      inferInstance inferInstance : IsIso φ.hom₃)

end

end CategoryTheory

/-! ### Lemma_13_9_14 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.9.14:
- primary domain: homotopy-category triangles of cochain complexes, mapping cones, and
  degreewise split short complexes;
- sampled owner declarations:
  `CochainComplex.mappingCone.triangleh`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.splitMonoFactorizationShortComplex`,
  `CochainComplex.splitMonoFactorizationSplitting`,
  `CategoryTheory.exists_distinguished_triangle_unique_up_to_iso`,
  `CategoryTheory.exists_iso_of_arrow_iso`,
  `HomotopyCategory.isoOfHomotopyEquiv`;
- best owner abstraction: the source-facing public content is the existence of a comparison
  isomorphism between the owner triangles `mappingCone.triangleh S.f` and
  `trianglehOfDegreewiseSplit S σ`, with identity first two components; that comparison should be
  exposed through the chapter-level uniqueness theorem for distinguished triangles with fixed first
  morphism, not as a chosen public witness. For part (2), the primitive source-facing data are the
  canonical split-mono factorization short complex and its degreewise splitting from
  Lemma 13.9.6, not a second local recreation of that owner-level data;
- source/core/bridge triage:
  `source-facing`: the comparison between the mapping-cone triangle of `f` and a triangle coming
    from a degreewise split short complex;
  `core/canonical`: the owner triangles `mappingCone.triangleh S.f` and
    `trianglehOfDegreewiseSplit S σ`;
  `bridge/view`: the existence statement for the owner triangle comparison in part (1), and the
    specialization in part (2) of the canonical distinguished-triangle bridge to a mapping-cone
    triangle.
- primitive data: for part (1), the short complex `S` and its degreewise splitting family `σ`;
  for part (2), the short complex `splitMonoFactorizationShortComplex f` together with
  `splitMonoFactorizationSplitting f`;
- derived API: any concrete witness for the comparison in part (1), used only internally, and the
  resulting triangle comparison in part (2). -/

-- Proof sketch: both triangles are distinguished and have the same first morphism, so the
-- comparison follows from the chapter-level uniqueness theorem for distinguished triangles with
-- fixed first morphism. Any homotopy equivalence between `mappingCone S.f` and `S.X₃` is then
-- derived from a locally chosen witness, not exported as public data.
/-- Lemma 13.9.14 (1): for a degreewise split short complex of cochain complexes, the standard
mapping-cone triangle of its first map is isomorphic to the triangle in `K(\mathcal A)` attached
to the degreewise split sequence, through the identity on the first two vertices. -/
theorem exists_mappingCone_triangleh_iso_of_degreewiseSplit
    (S : ShortComplex (CochainComplex 𝒜 ℤ))
    (σ : ∀ n, (S.map (eval 𝒜 _ n)).Splitting) :
    ∃ e : mappingCone.triangleh S.f ≅ trianglehOfDegreewiseSplit S σ,
      e.hom.hom₁ = 𝟙 ((Q).obj S.X₁) ∧
        e.hom.hom₂ = 𝟙 ((Q).obj S.X₂) := by
  simpa [CochainComplex.triangleOfDegreewiseSplit] using
    (CategoryTheory.exists_distinguished_triangle_unique_up_to_iso
      (HomotopyCategory.mappingCone_triangleh_distinguished S.f)
      (by
        rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
        exact ⟨S, σ, ⟨Iso.refl _⟩⟩))

-- Proof sketch: apply part (1) to the canonical short complex
-- `splitMonoFactorizationShortComplex f` and then compare
-- `mappingCone.triangleh (splitMonoFactorizationι f)` with `mappingCone.triangleh f` using the
-- projection homotopy equivalence from Lemma 13.9.6.
/-- Companion clause (2): the canonical degreewise split short complex
`splitMonoFactorizationShortComplex f` yields a triangle in `K(\mathcal A)` isomorphic to
the standard mapping-cone triangle of `f`, through the identity on the first vertex. -/
theorem exists_degreewiseSplit_triangleh_iso_mappingCone
    {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) :
    ∃ e :
        trianglehOfDegreewiseSplit
          (splitMonoFactorizationShortComplex f)
          (splitMonoFactorizationSplitting f) ≅
        mappingCone.triangleh f,
      e.hom.hom₁ = 𝟙 ((Q).obj K) := by
  obtain ⟨eSplit, heSplit₁, _heSplit₂⟩ :=
    exists_mappingCone_triangleh_iso_of_degreewiseSplit
      (splitMonoFactorizationShortComplex f)
      (splitMonoFactorizationSplitting f)
  let pIso :
      (Q).obj (splitMonoFactorizationObj K L) ≅ (Q).obj L :=
    HomotopyCategory.isoOfHomotopyEquiv (splitMonoFactorizationProjectionHomotopyEquiv K L)
  obtain ⟨eMap, heMap₁, _heMap₂⟩ :=
    exists_iso_of_arrow_iso
      (mappingCone.triangleh (splitMonoFactorizationι f))
      (mappingCone.triangleh f)
      (HomotopyCategory.mappingCone_triangleh_distinguished (splitMonoFactorizationι f))
      (HomotopyCategory.mappingCone_triangleh_distinguished f)
      (Arrow.isoMk (Iso.refl _) pIso (by
        dsimp [pIso, splitMonoFactorizationProjectionHomotopyEquiv]
        simp only [Category.id_comp]
        rw [← Functor.map_comp, splitMonoFactorizationι_comp_fst]))
  refine ⟨eSplit.symm ≪≫ eMap, ?_⟩
  change eSplit.inv.hom₁ ≫ eMap.hom.hom₁ = 𝟙 ((Q).obj K)
  have hInv : eSplit.inv.hom₁ = 𝟙 ((Q).obj K) := by
    simpa [heSplit₁] using Iso.inv_hom_id_triangle_hom₁ eSplit
  simpa [hInv, heMap₁]

end CochainComplex

/-! ### Lemma_13_9_15 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

section

variable [HasBinaryBiproducts 𝒜]

/- Domain-style sampling for Lemma 13.9.15:
- primary domain: finite composable rows of cochain complexes and commutative ladders whose
  horizontal maps are termwise split monomorphisms and whose vertical maps are homotopy
  equivalences;
- sampled owner declarations:
  `CategoryTheory.ComposableArrows`,
  `CategoryTheory.ComposableArrows.arrow`,
  `CochainComplex.splitMono_factorization_through_biproduct_mappingCone_id`,
  `HomologicalComplex.homotopyEquivalences`;
- best owner abstraction: the ladder data already lives canonically as a morphism
  `φ : T ⟶ S` in `ComposableArrows`, and the horizontal edges are canonically indexed by `Fin n`;
  the split-mono and homotopy-equivalence conditions are theorem-side properties expressed
  componentwise by the canonical owners `IsSplitMono` and `homotopyEquivalences`; the boundedness
  clauses likewise belong directly to the existing owners `CochainComplex.plus`,
  `CochainComplex.minus`, and `CochainComplex.bounded`;
- source/core/bridge triage:
  `source-facing`: existence of a replacement row with split-monomorphic horizontal maps and
    homotopy-equivalent vertical comparison maps;
  `core/canonical`: `ComposableArrows`, `IsSplitMono`, `homotopyEquivalences`, and the
    cochain-complex boundedness owners;
  `bridge/view`: the componentwise predicates imposed on the existing ladder morphism `φ`.
- primitive data: only the replacement row `T` and comparison morphism `φ : T ⟶ S`;
- derived API: the componentwise split-mono, homotopy-equivalence, and boundedness-preservation
  clauses.

This theorem should therefore quantify directly over the canonical owner `φ : T ⟶ S` instead of
introducing a separate wrapper class for these theorem-side properties.
-/

-- Proof sketch: argue by induction on the length of the composable sequence. The case of a single
-- object is trivial. For the induction step, first construct the replacement up to the penultimate
-- complex, then apply Lemma 13.9.6 to the composite from the last replacement complex to the final
-- complex to extend the diagram by one more term. The boundedness assertions are propagated at
-- each step using the corresponding boundedness clauses in Lemma 13.9.6.
/-- Lemma 13.9.15: every finite composable sequence of cochain complexes in an additive category
admits a commutative diagram from another sequence whose successive maps are termwise split
injections and whose vertical maps to the original sequence are homotopy equivalences; moreover,
if the original sequence is termwise bounded below, bounded above, or bounded, then the replacing
sequence has the same property termwise. -/
theorem exists_splitMono_homotopyReplacement
    {n : ℕ} (S : ComposableArrows (Comp(𝒜)) n) :
    ∃ (T : ComposableArrows (Comp(𝒜)) n) (φ : T ⟶ S),
      (∀ i : Fin n, ∀ k : ℤ, IsSplitMono ((T.map' i.1 (i.1 + 1)).f k)) ∧
      (∀ i : Fin (n + 1), homotopyEquivalences 𝒜 (up ℤ) (φ.app i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.plus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.minus 𝒜 (T.obj i)) ∧
      ((∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (S.obj i)) →
        ∀ i : Fin (n + 1), CochainComplex.bounded 𝒜 (T.obj i)) := by
  sorry

end

end ComposableArrows

end CategoryTheory

/-! ### Lemma_13_9_16 (from Chap13) -/
/- Source/core/bridge triage for Lemma 13.9.16:
- primary domain: triangles in the homotopy category of cochain complexes arising from degreewise
  split short exact sequences, and their comparison with the standard mapping-cone triangle of the
  connecting morphism;
- inspected owner declarations:
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.mappingCone.triangleh`;
- best owner abstraction: for the chapter statement, the main public entry is the existing
  homotopy-category bridge
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`; the cochain-level comparison
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso` remains the upstream core owner and is
  not duplicated locally;
- source/core/bridge triage:
  `source-facing`: the comparison in `K(𝒜)` between the doubly rotated triangle attached to a
    degreewise split short complex and the mapping-cone triangle of its connecting morphism;
  `core/canonical`: the cochain-level owner
    `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`;
  `bridge/view`: the induced homotopy-category isomorphism
    `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`;
- primitive data: a short complex `S : ShortComplex (CochainComplex 𝒜 ℤ)` and a degreewise
  splitting family `σ`;
- derived API: the connecting morphism `CochainComplex.homOfDegreewiseSplit S σ`, the homotopy
  triangle `CochainComplex.trianglehOfDegreewiseSplit S σ`, and the canonical bridge to the
  standard mapping-cone triangle all remain upstream and are reused directly here.
-/

/- Lemma 13.9.16: for a degreewise split short exact sequence of cochain complexes in an additive
category with binary biproducts, the doubly rotated triangle in `K(𝒜)` attached to that split
sequence is canonically isomorphic to the standard mapping-cone triangle of the connecting
morphism. This is exactly the upstream bridge
`CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`. -/
recall CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso

/-! ### Lemma_13_9_17 (from Chap13) -/
/- Domain-style sampling for Lemma 13.9.17:
- primary domain: mapping-cone triangles and triangles attached to degreewise split short
  complexes of cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCone.triangle`,
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- best owner abstraction: the upstream mapping-cone owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- primitive data: a morphism of cochain complexes `f : K^• ⟶ L^•`;
- derived API: the rotated standard mapping-cone triangle, the canonical degreewise split short
  complex `triangleRotateShortComplex f`, its degreewise splitting, and the resulting triangle
  comparison all remain upstream and are reused directly here.
-/

/- Source/core/bridge triage:
- `source-facing`: the textbook identification of the triangle
  `(L^•, C(f)^•, K^•[1], i, p, f[1])`;
- `core/canonical`: the cochain-level owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- `bridge/view`: no extra bridge is needed in this file, because the numbered lemma is already a
  direct recall of the core owner rather than a new wrapper.
-/

/- Lemma 13.9.17: for a morphism of cochain complexes `f : K^• ⟶ L^•` in an additive category,
the termwise split short complex
`0 ⟶ L^• ⟶ C(f)^• ⟶ K^•[1] ⟶ 0` coming from the definition of the cone has associated triangle
the rotated mapping-cone triangle; this is the mathlib formalization of the book's triangle
`(L^•, C(f)^•, K^•[1], i, p, f[1])`. The canonical identification is
`CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`. -/
recall CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit
