import Mathlib
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_9_1 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

/-- Lemma 21.9.1: for a family `U : ι → C`, the functor of (21.9.0.1), namely
`cechComplexFunctor U : (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ CochainComplex AddCommGrpCat ℕ`, is an exact
functor. -/
-- Proof sketch: in degree `p`, the Čech complex is a product of evaluation functors
-- `ℱ ↦ ℱ.obj (op W)`, and evaluation is exact on abelian presheaves. Exactness of finite limits
-- and finite colimits in cochain complexes is checked degreewise, so the whole Čech complex
-- functor is exact.
theorem cechComplexFunctor_exact
    {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C) :
    exactFunctor (Cᵒᵖ ⥤ AddCommGrpCat) (CochainComplex AddCommGrpCat ℕ) (cechComplexFunctor U) :=
  sorry

end CategoryTheory

/-! ### Lemma_21_9_2 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

/-- The Čech-complex functor on abelian presheaves on `C`, obtained by restriction to `Over U`
and then applying the Čech complex attached to `family`. -/
abbrev cechComplexOnPresheaves :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ CochainComplex AddCommGrpCat ℕ :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat).obj (Over.forget U).op ⋙
    cechComplexFunctor family

-- Proof sketch: evaluate `cechComplexOnPresheaves` on `F`, unfold the composite, and compare with
-- the definition of `cechComplex U family F` from Definition 21.8.1.
/-- The composite restriction-plus-Čech functor evaluates to the Čech complex `cechComplex`. -/
theorem cechComplexOnPresheaves_obj (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    (cechComplexOnPresheaves U family).obj F = cechComplex U family F := sorry

/-- The composite restriction-plus-Čech complex functor is additive. -/
noncomputable instance cechComplexOnPresheaves_additive :
    (cechComplexOnPresheaves U family).Additive := sorry

-- Proof sketch: restriction to `Over U` is exact because limits and colimits in functor
-- categories are computed pointwise, and Lemma 21.9.1 says the Čech complex functor on `Over U`
-- is exact. Therefore a short exact sequence of abelian presheaves maps to a short exact
-- sequence of Čech complexes.
/-- A short exact sequence of abelian presheaves induces a short exact sequence of Čech
complexes. -/
theorem cechComplexOnPresheaves_map_shortExact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) :
    (S.map (cechComplexOnPresheaves U family)).ShortExact := sorry

/-- The degree-`n` Čech cohomology functor associated to `family`. -/
abbrev cechCohomologyDegree (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤+ AddCommGrpCat :=
  AdditiveFunctor.of
    (cechComplexOnPresheaves U family ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n)

-- Proof sketch: `cechCohomologyDegree` is defined by composing `cechComplexOnPresheaves` with the
-- degree-`n` homology functor, whereas `cechCohomology` is the objectwise version of the same
-- construction from Definition 21.8.1.
/-- The degree-`n` functor evaluates to the Čech cohomology group `cechCohomology`. -/
theorem cechCohomologyDegree_obj (n : ℕ) (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    (cechCohomologyDegree U family n).obj.obj F = cechCohomology U family F n := sorry

/-- The connecting morphism in degree `n` attached to a short exact sequence of abelian
presheaves. -/
noncomputable def cechCohomologyConnectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (cechCohomologyDegree U family n).obj.obj S.X₃ ⟶
      (cechCohomologyDegree U family (n + 1)).obj.obj S.X₁ :=
  (cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

-- Proof sketch: unfold `cechCohomologyConnectingMorphism`; it is defined to be the standard
-- connecting morphism in the homology sequence of the mapped short exact sequence of Čech
-- complexes.
/-- The Čech cohomology connecting morphism is the canonical homology-sequence boundary map of the
mapped short exact sequence of Čech complexes. -/
theorem cechCohomologyConnectingMorphism_def
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomologyConnectingMorphism U family hS n =
      (cechComplexOnPresheaves_map_shortExact U family hS).δ n (n + 1)
        (ComplexShape.up_mk n (n + 1) rfl) := sorry

-- Proof sketch: apply the first exactness statement in the homology sequence of the short exact
-- sequence of Čech complexes attached to `hS`.
/-- In degree `0`, the induced map on Čech cohomology is a monomorphism. -/
theorem cechCohomology_mono_map_f_zero
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) :
    Mono ((cechCohomologyDegree U family 0).obj.map S.f) := sorry

-- Proof sketch: this is the relation `H^n(S.X₂) ⟶ H^n(S.X₃) ⟶ H^{n+1}(S.X₁) = 0` in the
-- homology sequence of the short exact sequence of Čech complexes attached to `hS`.
/-- The Čech cohomology connecting morphism kills the image of the middle map. -/
theorem cechCohomology_map_g_comp_connectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (cechCohomologyDegree U family n).obj.map S.g ≫
        cechCohomologyConnectingMorphism U family hS n =
      0 := sorry

-- Proof sketch: this is the next relation in the homology sequence of the mapped short exact
-- sequence of Čech complexes.
/-- The Čech cohomology connecting morphism factors through the kernel of the next `f`-map. -/
theorem cechCohomologyConnectingMorphism_comp_map_f
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    cechCohomologyConnectingMorphism U family hS n ≫
        (cechCohomologyDegree U family (n + 1)).obj.map S.f =
      0 := sorry

-- Proof sketch: exactness of the three-term segment
-- `H^n(S.X₁) ⟶ H^n(S.X₂) ⟶ H^n(S.X₃)` in the homology sequence of the short exact sequence of
-- Čech complexes yields the claim.
/-- In every degree, the mapped short complex on Čech cohomology is exact. -/
theorem cechCohomology_map_exact
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (cechCohomologyDegree U family n).obj).Exact := sorry

-- Proof sketch: this is exactness at `\check H^n(\mathcal U, \mathcal F_3)` in the long exact
-- sequence obtained from the short exact sequence of Čech complexes.
/-- The sequence
`\check H^n(\mathcal U, \mathcal F_2) ⟶ \check H^n(\mathcal U, \mathcal F_3) ⟶
\check H^{n+1}(\mathcal U, \mathcal F_1)` is exact. -/
theorem cechCohomology_exact_map_g_connectingMorphism
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk
      ((cechCohomologyDegree U family n).obj.map S.g)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomology_map_g_comp_connectingMorphism U family hS n)).Exact := sorry

-- Proof sketch: this is exactness at `\check H^{n+1}(\mathcal U, \mathcal F_1)` in the same long
-- exact sequence.
/-- The sequence
`\check H^n(\mathcal U, \mathcal F_3) ⟶ \check H^{n+1}(\mathcal U, \mathcal F_1) ⟶
\check H^{n+1}(\mathcal U, \mathcal F_2)` is exact. -/
theorem cechCohomology_exact_connectingMorphism_map_f
    {S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk
      (cechCohomologyConnectingMorphism U family hS n)
      ((cechCohomologyDegree U family (n + 1)).obj.map S.f)
      (cechCohomologyConnectingMorphism_comp_map_f U family hS n)).Exact := sorry

-- Proof sketch: a morphism of short exact sequences of abelian presheaves maps to a morphism of
-- short exact sequences of Čech complexes, and the naturality of the homology-sequence connecting
-- morphism gives the commutative square.
/-- The Čech cohomology connecting morphisms are natural in morphisms of short exact sequences of
abelian presheaves. -/
theorem cechCohomologyConnectingMorphism_naturality
    {S T : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) :
    CommSq
      ((cechCohomologyDegree U family n).obj.map φ.τ₃)
      (cechCohomologyConnectingMorphism U family hS n)
      (cechCohomologyConnectingMorphism U family hT n)
      ((cechCohomologyDegree U family (n + 1)).obj.map φ.τ₁) := sorry

/-- Lemma 21.9.2: for a family `family : ι → Over U`, the Čech cohomology functors
`F ↦ \check H^n(family, F)` form a cohomological `δ`-functor from the abelian category of
abelian presheaves on `C` to `AddCommGrpCat`, i.e. to the category of `\mathbf Z`-modules. -/
noncomputable def cechCohomologyDeltaFunctor :
    CohomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat) AddCommGrpCat where
  F := cechCohomologyDegree U family
  δ := fun {_} hS n ↦ cechCohomologyConnectingMorphism U family hS n
  mono_map_f_zero := fun {_} hS ↦ cechCohomology_mono_map_f_zero U family hS
  exact₅ := fun {_} hS n ↦
    CohomologicalDeltaFunctor.exact₅_of_adjacent_exactness
      (fun {_} hS n ↦ cechCohomology_map_g_comp_connectingMorphism U family hS n)
      (fun {_} hS n ↦ cechCohomologyConnectingMorphism_comp_map_f U family hS n)
      (fun {_} hS n ↦ cechCohomology_map_exact U family hS n)
      (fun {_} hS n ↦ cechCohomology_exact_map_g_connectingMorphism U family hS n)
      (fun {_} hS n ↦ cechCohomology_exact_connectingMorphism_map_f U family hS n)
      hS n
  δ_naturality := fun {_ _} hS hT φ n ↦
    cechCohomologyConnectingMorphism_naturality U family hS hT φ n

-- Proof sketch: unfold `cechCohomologyDeltaFunctor`; its degree-`n` term is defined to be
-- `cechCohomologyDegree U family n`.
/-- The degree-`n` term of the Čech cohomology `δ`-functor is `cechCohomologyDegree U family n`. -/
theorem cechCohomologyDeltaFunctor_F_eq (n : ℕ) :
    (cechCohomologyDeltaFunctor U family n).obj = (cechCohomologyDegree U family n).obj := sorry

end CategoryTheory

/-! ### Lemma_21_9_3 (from Chap21) -/
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

/-! ### Lemma_21_9_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open Opposite

noncomputable section

universe w u

namespace CategoryTheory

/-- The functor from formal coproducts in `C` to abelian presheaves sending a family to the
coproduct of the free abelian representables of its components. -/
abbrev freeAbelianRepresentableFormalCoproductFunctor {C : Type u} [Category.{u} C]
    [HasFiniteProducts C] [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}] :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (FormalCoproduct.eval.{w} C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free.{u})

/-- The simplicial abelian presheaf whose degree-`n` term is the coproduct of the free abelian
representables on the `(n + 1)`-fold Čech intersections of the family `family`. -/
abbrev cechCoverSimplicialObject {C : Type u} [Category.{u} C] [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → C) : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ((SimplicialObject.whiskering (FormalCoproduct.{w} C) (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    freeAbelianRepresentableFormalCoproductFunctor).obj ((FormalCoproduct.mk ι family).cech)

/-- The chain complex of abelian presheaves on `Over U` obtained by applying the alternating face
map construction to the simplicial free-abelian representable Čech object attached to `family`. -/
abbrev freeAbelianCechCoverChainComplex {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)] [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}] {ι : Type w} (family : ι → Over U) :
    ChainComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (alternatingFaceMapComplex ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (cechCoverSimplicialObject family)

-- Proof sketch: evaluate the chain complex on an object `V ⟶ U` of `Over U` and decompose the
-- resulting complex as a direct sum over maps `V ⟶ U` of bar-resolution complexes on the sets of
-- lifts to the cover. For each summand, choose a lift when the indexing set is nonempty and use
-- the induced extra degeneracy, equivalently the standard contracting homotopy on
-- `ℤ[S^{\bullet + 1}]`, to kill positive homology.
/-- Lemma 21.9.4: the free-abelian Čech cover chain complex of a family with fixed target has zero
homology presheaves in every positive degree. -/
theorem freeAbelianCechCoverChainComplex_homology_isZero_of_pos {C : Type u} [Category.{u} C]
    (U : C) [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})] [Limits.HasProducts AddCommGrpCat.{u}]
    [CategoryWithHomology ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    {ι : Type w} (family : ι → Over U) :
    ∀ i : ℕ, 0 < i →
      IsZero (((HomologicalComplex.homologyFunctor ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
        (ComplexShape.down ℕ) i).obj (freeAbelianCechCoverChainComplex U family))) := sorry

end CategoryTheory

/-! ### Lemma_21_9_5 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u w

namespace CategoryTheory

/-- The functor from formal coproducts in `C` to abelian presheaves sending a family to the
coproduct of the free abelian representables of its components. -/
abbrev sliceFreeAbelianRepresentableFormalCoproductFunctor {C : Type u} [Category.{u} C]
    [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}] :
    FormalCoproduct.{w} C ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (FormalCoproduct.eval.{w} C (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj
      AddCommGrpCat.free.{u})

/-- The simplicial abelian presheaf on the slice category whose degree-`n` term is the coproduct
of the free abelian representables on the `(n + 1)`-fold Čech intersections of the family
`family`. -/
abbrev sliceCechCoverSimplicialObject {C : Type u} [Category.{u} C]
    [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → C) :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ((SimplicialObject.whiskering (FormalCoproduct.{w} C) (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    sliceFreeAbelianRepresentableFormalCoproductFunctor).obj
      ((FormalCoproduct.mk ι family).cech)

/-- The chain complex of free abelian representable presheaves attached to a Čech family. -/
abbrev sliceFreeAbelianCechCoverChainComplex {C : Type u} [Category.{u} C]
    [HasFiniteProducts C]
    [Limits.HasCoproducts (Cᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → C) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
    (sliceCechCoverSimplicialObject family)

/-- The restriction of a commutative-ring-valued presheaf on `C` to the slice category
`Over U`. -/
abbrev restrictedCommRingPresheaf {C : Type u} [Category.{u} C] (U : C)
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) : (Over U)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget U).op ⋙ 𝒪

/-- The equivalence inverse sending an additive commutative group to the corresponding
`ℤ`-module. -/
abbrev addCommGrpToIntModule : AddCommGrpCat.{u} ⥤ ModuleCat.{u, 0} ℤ :=
  (forget₂ (ModuleCat.{u, 0} ℤ) AddCommGrpCat.{u}).asEquivalence.inverse

/-- The chain complex of `ℤ`-modules obtained by evaluating the free-abelian Čech cover chain
complex at `V : Over U`. -/
abbrev cechCoverSectionChainComplex {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → Over U) (V : Over U) :
    ChainComplex (ModuleCat.{u, 0} ℤ) ℕ :=
  (((CategoryTheory.evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) ⋙
      addCommGrpToIntModule).mapHomologicalComplex (ComplexShape.down ℕ) |>.obj
    (sliceFreeAbelianCechCoverChainComplex family)

/-- The sectionwise tensor of the evaluated free-abelian Čech cover chain complex with the
commutative ring of sections of `𝒪` over `V`, realized as extension of scalars from `ℤ`. -/
abbrev cechCoverSectionTensorChainComplex {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) {ι : Type w} (family : ι → Over U) (V : Over U) :
    ChainComplex (ModuleCat ((restrictedCommRingPresheaf U 𝒪).obj (op V))) ℕ :=
  ((ModuleCat.extendScalars
      (Int.castRingHom ((restrictedCommRingPresheaf U 𝒪).obj (op V)))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cechCoverSectionChainComplex U family V)

-- Proof sketch: for each `V : Over U`, evaluate Lemma `21.9.4` at `V` and identify the resulting
-- complex with a direct sum of bar-resolution summands. Tensoring that evaluated complex over `ℤ`
-- with the section ring `𝒪(V)` preserves exactness in positive degrees by the flatness argument of
-- Lemma `18.28.11`, exactly as in the textbook proof.
/-- Lemma 21.9.5: after restricting a ring-valued presheaf `\mathcal O` to `Over U`, tensoring
the evaluated free-abelian Čech cover chain complex with the ring of sections over any object
`V : Over U` yields a complex with zero homology in every positive degree. -/
theorem cechCoverSectionTensorChainComplex_homology_isZero_of_pos
    {C : Type u} [Category.{u} C] (U : C)
    [HasFiniteProducts (Over U)]
    [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
    [Limits.HasProducts AddCommGrpCat.{u}]
    {ι : Type w} (family : ι → Over U) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) :
    ∀ V : Over U, ∀ i : ℕ, 0 < i →
      IsZero (((HomologicalComplex.homologyFunctor
        (ModuleCat ((restrictedCommRingPresheaf U 𝒪).obj (op V)))
        (ComplexShape.down ℕ) i).obj
          (cechCoverSectionTensorChainComplex U 𝒪 family V))) := sorry

end CategoryTheory

/-! ### Lemma_21_9_6 (from Chap21) -/
open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

-- Proof sketch: Lemma `21.9.2` gives the cohomological `δ`-functor structure on Čech
-- cohomology. For an injective abelian presheaf `I`, Lemmas `21.9.3` and `21.9.4` identify the
-- Čech complex with a Hom complex out of an exact positive-degree resolution, so
-- `\check H^p(\mathcal U, I) = 0` for every `p > 0`. Thus the positive degrees are weakly
-- effaceable, and Lemma `12.12.4` implies universality.
/-- Lemma 21.9.6 (1): the Čech cohomology functors attached to `family` form a universal
cohomological `δ`-functor on abelian presheaves on `C`. -/
theorem cechCohomologyDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (cechCohomologyDeltaFunctor U family) := sorry

end

section

variable {C : Type u} [Category.{v} C]
variable (U : C) [Limits.HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

variable [HasInjectiveResolutions (Cᵒᵖ ⥤ AddCommGrpCat)]

/-- The degree-zero Čech cohomology functor attached to `family`. -/
abbrev cechH0Functor : (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ AddCommGrpCat :=
  (cechCohomologyDegree U family 0).obj

-- Proof sketch: the degree-zero term of the universal `δ`-functor is `\check H^0`, while
-- part (1) shows that Čech cohomology is itself universal. Lemma `13.20.4` gives the universal
-- `δ`-functor built from the higher right derived functors of `\check H^0`, and Lemma `12.12.5`
-- identifies the two universal `δ`-functors uniquely. In positive degree this yields the stated
-- canonical functor isomorphism.
/-- Lemma 21.9.6 (2): for each `p`, the higher Čech cohomology functor
`\check H^{p+1}(\mathcal U, -)` is canonically isomorphic to the `(p + 1)`-st right derived
functor of `\check H^0(\mathcal U, -)`. -/
theorem higherCechCohomologyFunctor_isomorphic_rightDerived (p : ℕ) :
    IsIsomorphic ((cechCohomologyDegree U family (p + 1)).obj)
      ((cechH0Functor U family).rightDerived (p + 1)) := sorry

-- Proof sketch: choose the canonical injective resolution of `F`, form the double complex whose
-- `q`-th column is the Čech complex of the `q`-th injective term, and compare both
-- `\check{\mathcal C}^\bullet(\mathcal U, F)` and the complex computing
-- `R\check H^0(\mathcal U, F)` to the corresponding total complex using Lemma `12.25.4`. The
-- chosen injective-resolution complex on the right computes the derived value by the standard
-- `InjectiveResolution.isoRightDerivedObj` comparison.
/-- Lemma 21.9.6 (3): for an abelian presheaf `F`, the chosen injective-resolution complex
obtained by applying `\check H^0(\mathcal U, -)` termwise computes the right derived functors of
`\check H^0(\mathcal U, -)` at `F`. This is the canonical complex model that appears on the
right-hand side of the source functorial quasi-isomorphism. -/
theorem rightDerivedCechH0_obj_isomorphic_homology_chosenInjectiveResolution
    (F : Cᵒᵖ ⥤ AddCommGrpCat) :
    ∀ p : ℕ,
      IsIsomorphic (((cechH0Functor U family).rightDerived p).obj F)
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
          (((cechH0Functor U family).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution F).cocomplex)) := sorry

end

end CategoryTheory
