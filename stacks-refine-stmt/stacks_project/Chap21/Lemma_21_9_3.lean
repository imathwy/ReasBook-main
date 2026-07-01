import stacks_project.Chap21.Lemma_21_9_4
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Opposite
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe w u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C]
variable [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Limits.HasProducts AddCommGrpCat.{u}]
variable {ι : Type w}

/- Domain-style sampling for Lemma 21.9.3:
- primary domain: Čech complexes of additive presheaves and the canonical `Hom(K,-)` cochain
  functor attached to a chain complex of free-abelian representables;
- sampled owner declarations:
  `CategoryTheory.cechComplexFunctor`,
  `CategoryTheory.cechCoverSimplicialObject`,
  `CategoryTheory.preadditiveCoyoneda`,
  `HomologicalComplex.asFunctor`;
- best owner abstraction: the source-facing comparison is between the canonical Čech cochain owner
  `cechComplexFunctor U` and the canonical Hom-complex owner obtained from the chain complex
  attached to `cechCoverSimplicialObject U`.

Source/core/bridge triage:
- `source-facing`: the comparison between the Hom complex of the free-abelian Čech cover complex
  and the usual Čech complex of an abelian presheaf;
- `core/canonical`: `cechComplexFunctor U`, `cechCoverSimplicialObject U`,
  `preadditiveCoyoneda.mapHomologicalComplex`, and `HomologicalComplex.asFunctor`;
- `bridge/view`: the degreewise comparison maps obtained from the free-abelian/Yoneda adjunction.

Primitive data versus derived API:
- primitive data: the family `U : ι → C`;
- derived API: the cover chain complex, the Hom-complex functor `cechCoverHomFunctor U`, and the
  degreewise component comparisons. -/

private abbrev cechCoverChainComplex (U : ι → C) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (alternatingFaceMapComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj (cechCoverSimplicialObject U)

/-- The canonical cochain-complex functor `Hom(K(U)_\bullet,-)` attached to the free-abelian Čech
cover chain complex of the family `U`. -/
abbrev cechCoverHomFunctor (U : ι → C) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  (((preadditiveCoyoneda.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (HomologicalComplex.op (cechCoverChainComplex U))).asFunctor)

private abbrev cechPowerObject (U : ι → C) (n : ℕ) : FormalCoproduct.{w} C :=
  ((FormalCoproduct.mk ι U).cech).obj (op (SimplexCategory.mk n))

private abbrev cechPowerIndex (U : ι → C) (n : ℕ) :=
  (cechPowerObject U n).I

private abbrev cechPowerComponent (U : ι → C) (n : ℕ) (i : cechPowerIndex U n) : C :=
  (cechPowerObject U n).obj i

private abbrev cechCoverSummand (U : ι → C) (n : ℕ) (i : cechPowerIndex U n) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj (cechPowerComponent U n i) ⋙ AddCommGrpCat.free.{u}

/-- The component of the canonical comparison map corresponding to the intersection indexed by `i`.
It sends a morphism from the degree-`n` free-abelian Čech cover term to the corresponding section
of `F`. -/
def cechCoverDegreeComparisonComponentToFun (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) (i : cechPowerIndex U n) :
    ((cechCoverChainComplex U).X n ⟶ F) → F.obj (op (cechPowerComponent U n i)) :=
  fun α ↦
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj (cechPowerComponent U n i)) F).trans
      yonedaEquiv) (Sigma.ι (cechCoverSummand U n) i ≫ α)

-- Proof sketch: composition with the coproduct injection and the Yoneda/free-abelian equivalence
-- are both additive, so their composite sends zero to zero.
/-- The component comparison map sends the zero morphism to the zero section. -/
theorem cechCoverDegreeComparisonComponentToFun_map_zero (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n) :
    cechCoverDegreeComparisonComponentToFun U F n i 0 = 0 := sorry

-- Proof sketch: composition with the coproduct injection and the Yoneda/free-abelian equivalence
-- are both additive, so their composite preserves addition.
/-- The component comparison map is additive in the source morphism. -/
theorem cechCoverDegreeComparisonComponentToFun_map_add (U : ι → C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (i : cechPowerIndex U n)
    (α β : (cechCoverChainComplex U).X n ⟶ F) :
    cechCoverDegreeComparisonComponentToFun U F n i (α + β) =
      cechCoverDegreeComparisonComponentToFun U F n i α +
        cechCoverDegreeComparisonComponentToFun U F n i β := sorry

/-- The additive map from degree-`n` morphisms out of the free-abelian Čech cover complex to the
`i`-th Čech cochain component. -/
abbrev cechCoverDegreeComparisonComponent (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) (i : cechPowerIndex U n) :
    AddCommGrpCat.of ((cechCoverChainComplex U).X n ⟶ F) ⟶ F.obj (op (cechPowerComponent U n i)) :=
  AddCommGrpCat.ofHom
    { toFun := cechCoverDegreeComparisonComponentToFun U F n i
      map_zero' := cechCoverDegreeComparisonComponentToFun_map_zero U F n i
      map_add' := cechCoverDegreeComparisonComponentToFun_map_add U F n i }

/-- The canonical degree-`n` comparison map from the degree-`n` part of the Hom complex of the
free-abelian Čech cover complex into the degree-`n` Čech cochains of `F`. -/
abbrev cechCoverDegreeComparison (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) :
    AddCommGrpCat.of ((cechCoverChainComplex U).X n ⟶ F) ⟶ ((cechComplexFunctor U).obj F).X n :=
  Pi.lift (fun i : cechPowerIndex U n ↦ cechCoverDegreeComparisonComponent U F n i)

-- Proof sketch: the source degree-`n` term is a coproduct of free abelian representables indexed
-- by the Čech `n`-simplices; the adjunction `AddCommGrpCat.free ⊣ forget` together with Yoneda
-- identifies each summand map with the corresponding section of `F`, and the product universal
-- property assembles these componentwise identifications into an isomorphism.
/-- Lemma 21.9.3 (1): in each degree, morphisms from the free-abelian Čech cover complex to `F`
identify with the degree-`n` Čech cochains of `F`. -/
theorem cechCoverDegreeComparison_isIso (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (cechCoverDegreeComparison U F n) := sorry

-- Proof sketch: both differentials are alternating sums over the coface maps induced by forgetting
-- one index. On each summand, the comparison map is the adjunction-plus-Yoneda identification from
-- Lemma `18.4.2`, and `FormalCoproduct.mapPower_π` identifies the induced restriction maps, so the
-- two alternating sums agree.
/-- Lemma 21.9.3 (2): the degreewise comparison maps intertwine the Hom differential on the
free-abelian Čech cover complex with the usual Čech differential. -/
theorem cechCoverDegreeComparison_comm_d (U : ι → C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechCoverDegreeComparison U F n ≫ ((cechComplexFunctor U).obj F).d n (n + 1) =
      ((cechCoverHomFunctor U).obj F).d n (n + 1) ≫ cechCoverDegreeComparison U F (n + 1) := sorry

-- Proof sketch: the source map is the degree-`n` component of `cechCoverHomFunctor U` applied to
-- `φ`, while the target map is the degree-`n` component of `cechComplexFunctor U` applied to `φ`.
-- Componentwise, both sides send a morphism out of the corresponding summand to the same
-- transported section of `G`.
/-- Lemma 21.9.3 (3): the comparison maps are natural in the abelian presheaf `F`. -/
theorem cechCoverDegreeComparison_natural (U : ι → C) {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) :
    cechCoverDegreeComparison U F n ≫ ((cechComplexFunctor U).map φ).f n =
      ((cechCoverHomFunctor U).map φ).f n ≫ cechCoverDegreeComparison U G n := sorry

/-- The degreewise comparison maps assemble to a morphism of cochain-complex functors from the
canonical Hom-complex owner attached to the free-abelian Čech cover complex to the canonical Čech
complex functor. -/
abbrev cechCoverComparison (U : ι → C) :
    cechCoverHomFunctor U ⟶ cechComplexFunctor U where
  app F :=
    { f := fun n ↦ cechCoverDegreeComparison U F n
      comm' := fun n m hnm ↦ by
        have hm : n + 1 = m := by simpa using hnm
        subst hm
        simpa using cechCoverDegreeComparison_comm_d U F n }
  naturality := fun F G φ ↦ by
    ext n x
    simpa using
      congrArg (fun f ↦ (AddCommGrpCat.Hom.hom f) x)
        ((cechCoverDegreeComparison_natural U φ n).symm)

-- Proof sketch: Lemma `21.9.3 (1)` gives an isomorphism in every degree, and Lemma `21.9.3 (2)`
-- says these degreewise isomorphisms commute with the differentials, so they assemble to an
-- isomorphism of cochain complexes functorially in `F`.
/-- Lemma 21.9.3: the canonical comparison from the Hom complex of the free-abelian Čech cover
complex to the usual Čech complex functor is an isomorphism of cochain-complex functors. -/
theorem cechCoverComparison_isIso (U : ι → C) :
    IsIso (cechCoverComparison U) := sorry

end CategoryTheory
