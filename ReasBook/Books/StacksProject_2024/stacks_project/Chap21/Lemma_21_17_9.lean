import StacksProject_2024.stacks_project.Chap04.Definition_4_22_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_35_7
import StacksProject_2024.stacks_project.Chap12.Lemma_12_25_3
import StacksProject_2024.stacks_project.Chap21.Definition_21_17_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_6
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_7
import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

attribute [local instance] HasDerivedCategory.standard

open SheafOfModules.RingedSite.CochainComplex
open scoped SheafOfModules.RingedSite HomologicalComplex₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site and their
  stability under sequential colimits;
- sampled owner declarations:
  `Mod(𝒪)`,
  `CochainComplex.IsKFlat`,
  `AB5 (Mod(𝒪))`,
  `PreservesColimits (tensorLeft ℱ : Mod(𝒪) ⥤ Mod(𝒪))`;
- best owner abstraction: the ambient owner category is `Mod(𝒪)`, the
  K-flatness predicate is the generic owner `(K : CochainComplex (Mod(𝒪)) ℤ).IsKFlat`, and the
  proof infrastructure for sequential colimits lives at the owner level through exact filtered
  colimits in `Mod(𝒪)`;
- primitive vs derived: the primitive data are only the sequential diagram `F` and the K-flatness
  hypotheses on its stages. The colimit complex, its tensor comparison maps, and the exactness of
  that colimit are derived from the ambient colimit and owner-level exactness/preservation API, so
  this file should not keep a parallel local module-category alias or a local K-flat wrapper in the
  theorem surface.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of sequential-colimit stability for K-flat
  complexes;
- `core/canonical`: `Mod(𝒪)`, `CochainComplex.IsKFlat`, `AB5 (Mod(𝒪))`, and
  `PreservesColimits (tensorLeft ℱ : Mod(𝒪) ⥤ Mod(𝒪))`;
- `bridge/view`: none. This file should state the ringed-site theorem directly using those owners.

The present file therefore keeps the genuinely new ringed-site sequential specialization rather
than a duplicate local wrapper around the ambient category or predicate. -/

-- Proof sketch: tensor an arbitrary acyclic complex `ℱ^•` with the sequential diagram `F`.
-- Termwise tensor products commute with the colimit, so
-- `Tot(ℱ^• ⊗ colim_i K_i^•)` is identified with the colimit of the acyclic tensor complexes
-- `Tot(ℱ^• ⊗ K_i^•)`. Exactness of filtered colimits on sheaves of modules then implies that the
-- resulting colimit tensor complex is acyclic.
--
-- The site hypotheses `[HasWeakSheafify J AddCommGrpCat.{max u v}]` and
-- `[J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]` only provide owner-level exactness and
-- colimit-preservation infrastructure on `Mod(𝒪)`; they are not source-facing inputs of the
-- K-flat sequential-colimit statement and should not appear in its public theorem surface.

/-- Helper for Lemma 21.17.9: module sheaves on a ringed site form an abelian category. -/
private instance instAbelianMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    Abelian (Mod(𝒪)) :=
  SheafOfModules.instAbelian (ringSheaf J 𝒪)

/-- Helper for Lemma 21.17.9: the ambient category `Mod(𝒪)` carries homology. -/
private instance instCategoryWithHomologyMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    CategoryWithHomology (Mod(𝒪)) := by
  -- Route correction: the dead biproduct/zero-object layer was removed, but this file still
  -- needs a direct owner bridge exposing the ambient homology structure on `Mod(𝒪)`.
  sorry

/-- Helper for Lemma 21.17.9: the ambient category `Mod(𝒪)` has all colimits. -/
private instance instHasColimitsMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    HasColimits (Mod(𝒪)) := by
  -- Proof comment: later tensor and sequential-colimit constructions only need the standard
  -- colimits on module sheaves.
  -- Route correction: keep the owner normalized to `SheafOfModules (ringSheaf J 𝒪)`, but the
  -- imported Chapter 18 colimit owner is still not visible here without an additional bridge.
  sorry

/-- Helper for Lemma 21.17.9: the ambient module-sheaf category has a zero object. -/
private instance instHasZeroObjectMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    HasZeroObject (Mod(𝒪)) := by
  -- Proof comment: this should be the canonical zero object on module sheaves once the owner
  -- normalization is repaired.
  sorry

/-- Helper for Lemma 21.17.9: the evaluation functors jointly reflect isomorphisms on sequential
module diagrams. -/
private theorem evaluationJointlyReflectsIsomorphismsMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    JointlyReflectIsomorphisms
      ((_root_.CategoryTheory.evaluation ℕ (Mod(𝒪))).obj :
        ℕ → (ℕ ⥤ Mod(𝒪)) ⥤ Mod(𝒪)) := by
  refine ⟨fun {X Y} f _ ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  simpa using
    (inferInstance :
      IsIso (((_root_.CategoryTheory.evaluation ℕ (Mod(𝒪))).obj n).map f))

/-- Helper for Lemma 21.17.9: once the ambient homology owner is available, sequential module
diagrams inherit the canonical pointwise homology structure. -/
private instance instCategoryWithHomologyFunctorMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    CategoryWithHomology (ℕ ⥤ Mod(𝒪)) := by
  -- Proof comment: the functor-category homology owner is the pointwise lift of the ambient one.
  sorry

/-- Helper for Lemma 21.17.9: sequential diagrams of module sheaves have a zero object
pointwise. -/
private instance instHasZeroObjectFunctorMod
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    HasZeroObject (ℕ ⥤ Mod(𝒪)) := by
  -- Proof comment: the zero object in the functor category is the pointwise zero diagram.
  infer_instance

section SequentialColimitIsKFlat

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]

/-- Helper for Lemma 21.17.9: keep tensor graded-piece colimit search explicit so later tensor
identity lemmas do not spend their budget rebuilding the same `HasTensor` owner. -/
private instance instHasTensorMod
    (M K : CochainComplex (Mod(𝒪)) ℤ) :
    HomologicalComplex.HasTensor M K := by
  -- Route correction: the sibling file can infer this directly, but in this file the owner-level
  -- search still times out repeatedly unless we isolate it behind one bridge instance.
  sorry

/-- Helper for Lemma 21.17.9: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclicOfIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    {K L : CochainComplex (Mod(𝒪)) ℤ}
    (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Proof comment: move the degreewise exactness witnesses across the complex isomorphism.
  intro i
  exact HomologicalComplex.ExactAt.of_iso (hK i) e

/-- Helper for Lemma 21.17.9: the previous differential in a sequential diagram is natural on
the degreewise module diagrams. -/
private theorem prevDNatTransNaturality
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) {n m : ℕ} (f : n ⟶ m) :
    (S.map f).f (i - 1) ≫ (S.obj m).d (i - 1) i =
      (S.obj n).d (i - 1) i ≫ (S.map f).f i := by
  -- Proof comment: this is exactly the chain-map compatibility with the previous differential.
  simpa using (S.map f).comm (i - 1) i

/-- Helper for Lemma 21.17.9: the previous differential defines a natural transformation on the
degreewise module diagrams of a sequential complex diagram. -/
private def prevDNatTrans
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) :
    S ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i - 1) ⟶
      S ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i where
  app n := (S.obj n).d (i - 1) i
  naturality _ _ f := prevDNatTransNaturality S i f

/-- Helper for Lemma 21.17.9: the next differential in a sequential diagram is natural on the
degreewise module diagrams. -/
private theorem nextDNatTransNaturality
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) {n m : ℕ} (f : n ⟶ m) :
    (S.map f).f i ≫ (S.obj m).d i (i + 1) =
      (S.obj n).d i (i + 1) ≫ (S.map f).f (i + 1) := by
  -- Proof comment: this is the same chain-map compatibility one degree higher.
  simpa using (S.map f).comm i (i + 1)

/-- Helper for Lemma 21.17.9: the next differential defines a natural transformation on the
degreewise module diagrams of a sequential complex diagram. -/
private def nextDNatTrans
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) :
    S ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i ⟶
      S ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i + 1) where
  app n := (S.obj n).d i (i + 1)
  naturality _ _ f := nextDNatTransNaturality S i f

/-- Helper for Lemma 21.17.9: the consecutive degreewise differentials in the functor category
still compose to zero. -/
private theorem degreeDCompEqZero
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) :
    prevDNatTrans S i ≫ nextDNatTrans S i = 0 := by
  -- Route correction: use the stagewise `d ≫ d = 0` identity rather than a definitional `rfl`
  -- proof, since the natural-transformation composite is not definitionally zero.
  -- Proof comment: after evaluating at a stage and a section, the two consecutive differentials
  -- reduce to the sectionwise `d ≫ d = 0` identity.
  ext n X x
  have hSection :
      (ModuleCat.Hom.hom
          ((((S.obj n).d (i - 1) i ≫ (S.obj n).d i (i + 1)).val.app X))) x =
        (ModuleCat.Hom.hom (((0 : (S.obj n).X (i - 1) ⟶ (S.obj n).X (i + 1)).val.app X))) x :=
    congrArg (fun f ↦ (ModuleCat.Hom.hom (f.val.app X)) x)
      ((S.obj n).d_comp_d (i - 1) i (i + 1))
  simpa only [prevDNatTrans, nextDNatTrans] using hSection

/-- Helper for Lemma 21.17.9: the degree-`i` short complex of a sequential diagram of cochain
complexes, formed in the functor category `ℕ ⥤ Mod(𝒪)`. -/
private def degreeShortComplex
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) :
    ShortComplex (ℕ ⥤ Mod(𝒪)) :=
  ShortComplex.mk
    (prevDNatTrans S i)
    (nextDNatTrans S i)
    (degreeDCompEqZero S i)

/-- Helper for Lemma 21.17.9: evaluating the functor-category degree-`i` short complex at a
stage recovers the ordinary degree-`i` short complex of that stage. -/
private def degreeShortComplexAppIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) (n : ℕ) :
    (degreeShortComplex S i).map ((_root_.CategoryTheory.evaluation ℕ (Mod(𝒪))).obj n) ≅
      (S.obj n).sc i :=
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)) ≪≫
    ((S.obj n).isoSc' (i - 1) i (i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Lemma 21.17.9: exactness of a short complex of sequential module systems can be
checked after evaluation at each stage. -/
private theorem shortComplexExactIffExactApp
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    (S : ShortComplex (ℕ ⥤ Mod(𝒪))) :
    S.Exact ↔ ∀ n : ℕ, (S.map ((_root_.CategoryTheory.evaluation ℕ (Mod(𝒪))).obj n)).Exact := by
  -- Route correction: exactness in the functor category is reflected directly by the evaluation
  -- family, so no separate functor-category homology scaffold is needed here.
  exact evaluationJointlyReflectsIsomorphismsMod.exact_iff S

/-- Helper for Lemma 21.17.9: AB5 on `Mod(𝒪)` supplies exact sequential colimits. -/
private instance ringedSiteModuleHasSequentialColimits
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    HasColimitsOfShape ℕ (Mod(𝒪)) := by
  -- Proof comment: Chapter 18 already installs all colimits on `Mod(𝒪)`, so the sequential
  -- case is an immediate instance.
  let _ : HasColimits (Mod(𝒪)) := instHasColimitsMod
  infer_instance

/-- Helper for Lemma 21.17.9: AB5 on `Mod(𝒪)` supplies exact sequential colimits. -/
private instance ringedSiteModuleHasExactSequentialColimits
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    HasExactColimitsOfShape ℕ (Mod(𝒪)) := by
  -- Proof comment: after normalizing `Mod(𝒪)` to the canonical owner spelling, the Chapter 18
  -- `AB5` instance gives exact sequential colimits directly.
  -- Route correction: the exact-colimit owner should come from Chapter 18 `AB5`, but this file
  -- still needs the owner bridge made explicit before instance search can close it.
  sorry

/-- Helper for Lemma 21.17.9: the first `mapShortComplex` compatibility condition for the
degree-`i` surface is the canonical colimit relation for the previous differential. -/
private theorem degreeShortComplexColimitMapPrev
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degreeShortComplex S i).X₁ n ≫
        colim.map (prevDNatTrans S i) =
      (degreeShortComplex S i).f.app n ≫
        colimit.ι (degreeShortComplex S i).X₂ n := by
  -- Proof comment: this is exactly `colimit.ι_map`, rewritten on the chosen short-complex shape.
  simpa [degreeShortComplex] using
    (colimit.ι_map (prevDNatTrans S i) n)

/-- Helper for Lemma 21.17.9: the second `mapShortComplex` compatibility condition for the
degree-`i` surface is the canonical colimit relation for the next differential. -/
private theorem degreeShortComplexColimitMapNext
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (i : ℤ) (n : ℕ) :
    colimit.ι (degreeShortComplex S i).X₂ n ≫
        colim.map (nextDNatTrans S i) =
      (degreeShortComplex S i).g.app n ≫
        colimit.ι (degreeShortComplex S i).X₃ n := by
  -- Proof comment: this is the same cocone-leg identity for the next differential.
  simpa [degreeShortComplex] using
    (colimit.ι_map (nextDNatTrans S i) n)

/-- Helper for Lemma 21.17.9: if each stage of a sequential diagram is acyclic, then the induced
degree-`i` short complex in the functor category is exact. -/
private theorem degreeShortComplexExact
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (G : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    (hG : ∀ n : ℕ, (G.obj n).Acyclic) (i : ℤ) :
    (degreeShortComplex G i).Exact := by
  -- Proof comment: reflect exactness through evaluation, where the short complex becomes the
  -- stagewise short complex of an acyclic complex.
  rw [shortComplexExactIffExactApp (degreeShortComplex G i)]
  intro n
  have hExactAt : (G.obj n).ExactAt i := by
    exact (HomologicalComplex.acyclic_iff (G.obj n)).mp (hG n) i
  have hExactSc : ((G.obj n).sc i).Exact := by
    exact (HomologicalComplex.exactAt_iff (G.obj n) i).mp hExactAt
  exact (ShortComplex.exact_iff_of_iso
    (degreeShortComplexAppIso G i n)).mpr hExactSc

/-- Helper for Lemma 21.17.9: evaluating the chosen sequential colimit cocone at degree `i`
gives the canonical cocone on the degree-`i` module diagram. -/
private def colimitDegreeTermCocone
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) :
    Cocone (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) :=
  (HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i).mapCocone (colimit.cocone F)

/-- Helper for Lemma 21.17.9: evaluation preserves the chosen sequential colimit, so the
degree-`i` evaluated cocone is colimiting. -/
private def colimitDegreeTermIsColimit
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) :
    IsColimit (colimitDegreeTermCocone F i) :=
  Limits.isColimitOfPreserves
    (HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i)
    (colimit.isColimit F)

/-- Helper for Lemma 21.17.9: the colimit of the degree-`i` terms is canonically the degree-`i`
term of the colimit complex. -/
private noncomputable def colimitDegreeTermIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) :
    colimit (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) ≅
      (colimit F).X i :=
  ((colimitDegreeTermIsColimit F i).coconePointUniqueUpToIso
    (colimit.isColimit (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i))).symm

/-- Helper for Lemma 21.17.9: on each cocone leg, the degreewise colimit comparison is the
canonical degree-`i` map into the colimit complex. -/
private theorem colimitDegreeTermIsoHomIota
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) (n : ℕ) :
    colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
        (colimitDegreeTermIso F i).hom =
      (colimit.ι F n).f i := by
  let e :
      (colimit F).X i ≅
        colimit (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) :=
    (colimitDegreeTermIsColimit F i).coconePointUniqueUpToIso
      (colimit.isColimit (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i))
  have h :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimitDegreeTermIsColimit F i)
      (colimit.isColimit (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i)) n
  -- Proof comment: compose the cocone-leg formula with the inverse comparison to recover the
  -- chosen direction of the degreewise colimit identification.
  simpa [colimitDegreeTermIso, colimitDegreeTermCocone, e] using
    (congrArg (fun f ↦ f ≫ e.inv) h).symm

/-- Helper for Lemma 21.17.9: the degreewise colimit comparison intertwines the previous
differential with the colimit of the previous-differential natural transformation. -/
private theorem colimitDegreeTermIsoPrevComm
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) :
    (colimitDegreeTermIso F (i - 1)).hom ≫ (colimit F).d (i - 1) i =
      colim.map (prevDNatTrans F i) ≫
        (colimitDegreeTermIso F i).hom := by
  -- Proof comment: compare both morphisms after precomposing with each universal cocone leg.
  apply colimit.hom_ext
  intro n
  have h1 :
      colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i - 1)) n ≫
          (colimitDegreeTermIso F (i - 1)).hom ≫ (colimit F).d (i - 1) i =
        (colimit.ι F n).f (i - 1) ≫ (colimit F).d (i - 1) i := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (colimit F).d (i - 1) i)
        (colimitDegreeTermIsoHomIota F (i - 1) n)
  have h2 :
      (colimit.ι F n).f (i - 1) ≫ (colimit F).d (i - 1) i =
        (F.obj n).d (i - 1) i ≫ (colimit.ι F n).f i := by
    simpa using (colimit.ι F n).comm (i - 1) i
  have h3 :
      (F.obj n).d (i - 1) i ≫ (colimit.ι F n).f i =
        (prevDNatTrans F i).app n ≫
          (colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
            (colimitDegreeTermIso F i).hom) := by
    simpa [prevDNatTrans, Category.assoc] using
      (congrArg
        (fun k ↦ (prevDNatTrans F i).app n ≫ k)
        (colimitDegreeTermIsoHomIota F i n)).symm
  have h4 :
      (prevDNatTrans F i).app n ≫
          (colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
            (colimitDegreeTermIso F i).hom) =
        ((prevDNatTrans F i).app n ≫
          colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n) ≫
            (colimitDegreeTermIso F i).hom := by
    simp [Category.assoc]
  have h5 :
      ((prevDNatTrans F i).app n ≫
          colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n) ≫
            (colimitDegreeTermIso F i).hom =
        (colimit.ι
            (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i - 1)) n ≫
          colim.map (prevDNatTrans F i)) ≫
            (colimitDegreeTermIso F i).hom := by
    rw [colimit.ι_map]
    simp [Category.assoc]
  have h6 :
      (colimit.ι
          (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i - 1)) n ≫
        colim.map (prevDNatTrans F i)) ≫
          (colimitDegreeTermIso F i).hom =
        colimit.ι
          (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i - 1)) n ≫
          (colim.map (prevDNatTrans F i) ≫
            (colimitDegreeTermIso F i).hom) := by
    simp [Category.assoc]
  exact h1.trans <| h2.trans <| h3.trans <| h4.trans <| h5.trans h6

/-- Helper for Lemma 21.17.9: the degreewise colimit comparison intertwines the next
differential with the colimit of the next-differential natural transformation. -/
private theorem colimitDegreeTermIsoNextComm
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) :
    (colimitDegreeTermIso F i).hom ≫ (colimit F).d i (i + 1) =
      colim.map (nextDNatTrans F i) ≫
        (colimitDegreeTermIso F (i + 1)).hom := by
  -- Proof comment: the same cocone-leg calculation identifies the next differential after
  -- passing to colimits.
  apply colimit.hom_ext
  intro n
  have h1 :
      colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
          (colimitDegreeTermIso F i).hom ≫ (colimit F).d i (i + 1) =
        (colimit.ι F n).f i ≫ (colimit F).d i (i + 1) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ (colimit F).d i (i + 1))
        (colimitDegreeTermIsoHomIota F i n)
  have h2 :
      (colimit.ι F n).f i ≫ (colimit F).d i (i + 1) =
        (F.obj n).d i (i + 1) ≫ (colimit.ι F n).f (i + 1) := by
    simpa using (colimit.ι F n).comm i (i + 1)
  have h3 :
      (F.obj n).d i (i + 1) ≫ (colimit.ι F n).f (i + 1) =
        (nextDNatTrans F i).app n ≫
          (colimit.ι
              (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i + 1)) n ≫
            (colimitDegreeTermIso F (i + 1)).hom) := by
    simpa [nextDNatTrans, Category.assoc] using
      (congrArg
        (fun k ↦ (nextDNatTrans F i).app n ≫ k)
        (colimitDegreeTermIsoHomIota F (i + 1) n)).symm
  have h4 :
      (nextDNatTrans F i).app n ≫
          (colimit.ι
              (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i + 1)) n ≫
            (colimitDegreeTermIso F (i + 1)).hom) =
        ((nextDNatTrans F i).app n ≫
          colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i + 1)) n) ≫
            (colimitDegreeTermIso F (i + 1)).hom := by
    simp [Category.assoc]
  have h5 :
      ((nextDNatTrans F i).app n ≫
          colimit.ι (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) (i + 1)) n) ≫
            (colimitDegreeTermIso F (i + 1)).hom =
        (colimit.ι
            (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
          colim.map (nextDNatTrans F i)) ≫
            (colimitDegreeTermIso F (i + 1)).hom := by
    rw [colimit.ι_map]
    simp [Category.assoc]
  have h6 :
      (colimit.ι
          (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
        colim.map (nextDNatTrans F i)) ≫
          (colimitDegreeTermIso F (i + 1)).hom =
        colimit.ι
          (F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) i) n ≫
          (colim.map (nextDNatTrans F i) ≫
            (colimitDegreeTermIso F (i + 1)).hom) := by
    simp [Category.assoc]
  exact h1.trans <| h2.trans <| h3.trans <| h4.trans <| h5.trans h6

/-- Helper for Lemma 21.17.9: the canonical colimit short complex of the degree-`i` sequential
surface identifies with the degree-`i` short complex of the colimit complex. -/
private noncomputable def colimitDegreeShortComplexIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] (i : ℤ) :
    colim.mapShortComplex (degreeShortComplex F i)
      (colimit.isColimit _)
      (colimit.cocone _)
      (colimit.cocone _)
      (colim.map (prevDNatTrans F i))
      (colim.map (nextDNatTrans F i))
      (degreeShortComplexColimitMapPrev F i)
      (degreeShortComplexColimitMapNext F i) ≅
        (colimit F).sc i :=
  (ShortComplex.isoMk
      (colimitDegreeTermIso F (i - 1))
      (colimitDegreeTermIso F i)
      (colimitDegreeTermIso F (i + 1))
      (colimitDegreeTermIsoPrevComm F i)
      (colimitDegreeTermIsoNextComm F i)) ≪≫
    ((colimit F).isoSc' (i - 1) i (i + 1)
      (CochainComplex.prev ℤ i) (CochainComplex.next ℤ i)).symm

/-- Helper for Lemma 21.17.9: a sequential colimit of acyclic cochain complexes of `𝒪`-modules
is acyclic. -/
private theorem colimitMapShortComplexExactOfSequential
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (S : ShortComplex (ℕ ⥤ Mod(𝒪))) (hS : S.Exact) :
    (colim.mapShortComplex S
      (colimit.isColimit S.X₁)
      (colimit.cocone S.X₂)
      (colimit.cocone S.X₃)
      (colim.map S.f)
      (colim.map S.g)
      (fun n ↦ colimit.ι_map S.f n)
      (fun n ↦ colimit.ι_map S.g n)).Exact := by
  have hf :
      ∀ n : ℕ,
        colimit.ι S.X₁ n ≫ colim.map S.f = S.f.app n ≫ colimit.ι S.X₂ n := by
    -- Proof comment: the first short-complex compatibility is the universal `ι_map` identity.
    intro n
    simpa using (colimit.ι_map S.f n)
  have hg :
      ∀ n : ℕ,
        colimit.ι S.X₂ n ≫ colim.map S.g = S.g.app n ≫ colimit.ι S.X₃ n := by
    -- Proof comment: the second compatibility is the same universal colimit relation.
    intro n
    simpa using (colimit.ι_map S.g n)
  -- Proof comment: exact sequential colimits turn an exact short-complex diagram into an exact
  -- short complex on the termwise colimits.
  exact Limits.colim.exact_mapShortComplex hS
    (colimit.isColimit S.X₁)
    (colimit.isColimit S.X₂)
    (colimit.isColimit S.X₃)
    (colim.map S.f)
    (colim.map S.g)
    hf
    hg

/-- Helper for Lemma 21.17.9: a sequential colimit of acyclic cochain complexes of `𝒪`-modules
is acyclic. -/
private theorem acyclicColimitOfSequential
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    (G : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    [HasColimit G]
    (hG : ∀ n : ℕ, (G.obj n).Acyclic) :
    (colimit G).Acyclic := by
  -- Proof comment: prove exactness degreewise on the colimit short complexes, then rebuild
  -- acyclicity from those exactness statements.
  rw [HomologicalComplex.acyclic_iff]
  intro i
  have hExactSource :
      (colim.mapShortComplex (degreeShortComplex G i)
        (colimit.isColimit _)
        (colimit.cocone _)
        (colimit.cocone _)
        (colim.map (prevDNatTrans G i))
        (colim.map (nextDNatTrans G i))
        (degreeShortComplexColimitMapPrev G i)
        (degreeShortComplexColimitMapNext G i)).Exact := by
    -- Proof comment: first establish exactness in the functor category, then pass to colimits.
    exact colimitMapShortComplexExactOfSequential
      (degreeShortComplex G i)
      (degreeShortComplexExact G hG i)
  have hExactTarget : ((colimit G).sc i).Exact := by
    -- Proof comment: the canonical short-complex comparison identifies the colimit surface with
    -- the degree-`i` short complex of the colimit complex.
    exact (ShortComplex.exact_iff_of_iso (colimitDegreeShortComplexIso G i)).mp hExactSource
  exact (HomologicalComplex.exactAt_iff (colimit G) i).mpr hExactTarget

/-- Helper for Lemma 21.17.9: tensoring on the left by a fixed complex preserves identity maps in
the right factor. -/
private theorem tensorHomIdRight
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M K : CochainComplex (Mod(𝒪)) ℤ)
    [HomologicalComplex.HasTensor M K] :
    HomologicalComplex.tensorHom (𝟙 M) (𝟙 K) = 𝟙 (HomologicalComplex.tensorObj M K) := by
  -- Proof comment: evaluate the tensor map on each `(p,q)` summand and use the canonical
  -- `ι_mapBifunctorMap` formula for the identity pair.
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom, HomologicalComplex.id_f] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := K)
      (f₁ := 𝟙 M) (f₂ := 𝟙 K) (F := curriedTensor (Mod(𝒪)))
      (c := ComplexShape.up ℤ) p q n h)

/-- Helper for Lemma 21.17.9: tensoring on the left by a fixed complex preserves compositions in
the right factor. -/
private theorem tensorHomCompRight
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    {K L P : CochainComplex (Mod(𝒪)) ℤ}
    [HomologicalComplex.HasTensor M K]
    [HomologicalComplex.HasTensor M L]
    [HomologicalComplex.HasTensor M P]
    (f : K ⟶ L) (g : L ⟶ P) :
    HomologicalComplex.tensorHom (𝟙 M) (f ≫ g) =
      HomologicalComplex.tensorHom (𝟙 M) f ≫ HomologicalComplex.tensorHom (𝟙 M) g := by
  -- Proof comment: compare both sides on each tensor summand and use the canonical whiskered
  -- formulas for `f`, `g`, and `f ≫ g`.
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hfg :
      HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) (f ≫ g)).f n =
        (M.X p ◁ ((f ≫ g).f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := P)
        (f₁ := 𝟙 M) (f₂ := f ≫ g) (F := curriedTensor (Mod(𝒪)))
        (c := ComplexShape.up ℤ) p q n h)
  have hf :
      HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) f).f n =
        (M.X p ◁ f.f q) ≫ HomologicalComplex.ιTensorObj M L p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := K) (L₁ := M) (L₂ := L)
        (f₁ := 𝟙 M) (f₂ := f) (F := curriedTensor (Mod(𝒪)))
        (c := ComplexShape.up ℤ) p q n h)
  have hg :
      HomologicalComplex.ιTensorObj M L p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) g).f n =
        (M.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
    simpa [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,
      HomologicalComplex.id_f] using
      (HomologicalComplex.ι_mapBifunctorMap
        (K₁ := M) (K₂ := L) (L₁ := M) (L₂ := P)
        (f₁ := 𝟙 M) (f₂ := g) (F := curriedTensor (Mod(𝒪)))
        (c := ComplexShape.up ℤ) p q n h)
  calc
    HomologicalComplex.ιTensorObj M K p q n h ≫
        (HomologicalComplex.tensorHom (𝟙 M) (f ≫ g)).f n
      = (M.X p ◁ ((f ≫ g).f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := hfg
    _ = (M.X p ◁ (f.f q ≫ g.f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
          simp [HomologicalComplex.comp_f]
    _ = ((M.X p ◁ f.f q) ≫ (M.X p ◁ g.f q)) ≫ HomologicalComplex.ιTensorObj M P p q n h := by
          rw [← whiskerLeft_comp]
    _ = (M.X p ◁ f.f q) ≫ ((M.X p ◁ g.f q) ≫ HomologicalComplex.ιTensorObj M P p q n h) := by
          simp [Category.assoc]
    _ = (M.X p ◁ f.f q) ≫
          (HomologicalComplex.ιTensorObj M L p q n h ≫
            (HomologicalComplex.tensorHom (𝟙 M) g).f n) := by
          rw [← hg]
    _ = (HomologicalComplex.ιTensorObj M K p q n h ≫
          (HomologicalComplex.tensorHom (𝟙 M) f).f n) ≫
            (HomologicalComplex.tensorHom (𝟙 M) g).f n := by
          rw [hf]
          simp [Category.assoc]
    _ = HomologicalComplex.ιTensorObj M K p q n h ≫
          ((HomologicalComplex.tensorHom (𝟙 M) f ≫
            HomologicalComplex.tensorHom (𝟙 M) g).f n) := by
          simp [HomologicalComplex.comp_f, Category.assoc]

/-- Helper for Lemma 21.17.9: the explicit sequential diagram obtained by tensoring each stage of
`F` on the left with the fixed acyclic test complex `M`. -/
private theorem tensorizedSequentialDiagramMapId
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) (n : ℕ) :
    HomologicalComplex.tensorHom (𝟙 M) (F.map (𝟙 n)) =
      𝟙 (HomologicalComplex.tensorObj M (F.obj n)) := by
  simpa using tensorHomIdRight M (F.obj n)

/-- Helper for Lemma 21.17.9: the tensorized sequential diagram respects composition because
`tensorHom (𝟙 M)` respects composition in the right factor. -/
private theorem tensorizedSequentialDiagramMapComp
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    {i j k : ℕ} (f : i ⟶ j) (g : j ⟶ k) :
    HomologicalComplex.tensorHom (𝟙 M) (F.map (f ≫ g)) =
      HomologicalComplex.tensorHom (𝟙 M) (F.map f) ≫
        HomologicalComplex.tensorHom (𝟙 M) (F.map g) := by
  simpa using tensorHomCompRight M (F.map f) (F.map g)

/-- Helper for Lemma 21.17.9: the canonical legs `tensorHom (𝟙 M) (colimit.ι F i)` satisfy the
cocone naturality relation for the explicit tensorized sequential diagram. -/
private theorem tensorizedSequentialCoconeNaturality
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    {i j : ℕ} (f : i ⟶ j) :
    HomologicalComplex.tensorHom (𝟙 M) (F.map f) ≫
        HomologicalComplex.tensorHom (𝟙 M) (colimit.ι F j) =
      HomologicalComplex.tensorHom (𝟙 M) (colimit.ι F i) := by
  -- Proof comment: first rewrite tensoring through the composition in the right factor, then use
  -- the colimit cocone relation `F.map f ≫ ι_j = ι_i`.
  rw [← tensorHomCompRight]
  simpa using congrArg (HomologicalComplex.tensorHom (𝟙 M)) (colimit.w F f)

/-- Helper for Lemma 21.17.9: the explicit sequential diagram obtained by tensoring each stage of
`F` on the left with the fixed acyclic test complex `M`. -/
private def tensorizedSequentialDiagram
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) :
    ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ where
  obj n := HomologicalComplex.tensorObj M (F.obj n)
  map f := HomologicalComplex.tensorHom (𝟙 M) (F.map f)
  map_id n := tensorizedSequentialDiagramMapId M F n
  map_comp f g := tensorizedSequentialDiagramMapComp M F f g

/-- Helper for Lemma 21.17.9: the canonical cocone from the explicit tensorized sequential diagram
to the tensor product with the colimit complex. -/
private def tensorizedSequentialCocone
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] :
    Cocone (tensorizedSequentialDiagram M F) where
  pt := HomologicalComplex.tensorObj M (colimit F)
  ι.app n := HomologicalComplex.tensorHom (𝟙 M) (colimit.ι F n)
  ι.naturality _ _ f := tensorizedSequentialCoconeNaturality M F f

/-- Helper for Lemma 21.17.9: tensoring the degree-`q` colimit cocone on the left by `M.X p`
gives the canonical cocone on the `(p,q)` summand system. -/
private def tensorizedSequentialSummandCocone
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (p q : ℤ) :
    Cocone
      (((F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) q) ⋙
        MonoidalCategory.tensorLeft (M.X p))) :=
  (MonoidalCategory.tensorLeft (M.X p)).mapCocone (colimitDegreeTermCocone F q)

/-- Helper for Lemma 21.17.9: the `(p,q)` summand cocone is colimiting because left tensoring by
`M.X p` preserves colimits of module-sheaf diagrams. -/
private def tensorizedSequentialSummandIsColimit
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (p q : ℤ) :
    IsColimit (tensorizedSequentialSummandCocone M F p q) :=
  by
    -- Route correction: the intended proof is still `isColimitOfPreserves` on `tensorLeft`.
    -- The remaining blocker is structural, not computational: this file does not currently expose
    -- the `Closed (M.X p)` / `PreservesColimits (tensorLeft (M.X p))` owner bridge.
    sorry

/-- Helper for Lemma 21.17.9: on each `(p,q)` summand, the map induced by a morphism in the
tensorized sequential diagram is the expected whiskered degree map. -/
@[reassoc] private theorem tensorizedSequentialDiagramMapCompιTensorObj
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    {i j : ℕ} (f : i ⟶ j) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
        ((tensorizedSequentialDiagram M F).map f).f n =
      (M.X p ◁ (F.map f).f q) ≫ HomologicalComplex.ιTensorObj M (F.obj j) p q n h := by
  -- Proof comment: this is the owner-level `ι_mapBifunctorMap` formula specialized to tensoring
  -- with the identity on the left factor.
  simpa [tensorizedSequentialDiagram, HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := F.obj i) (L₁ := M) (L₂ := F.obj j)
      (f₁ := 𝟙 M) (f₂ := F.map f) (F := curriedTensor (Mod(𝒪)))
      (c := ComplexShape.up ℤ) p q n h)

/-- Helper for Lemma 21.17.9: on each `(p,q)` summand, the `i`-th leg of the explicit tensorized
cocone is given by whiskering the degree-`q` colimit map and then including that summand. -/
@[reassoc] private theorem tensorizedSequentialCoconeLegCompιTensorObj
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (i : ℕ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
        ((tensorizedSequentialCocone M F).ι.app i).f n =
      (M.X p ◁ (colimit.ι F i).f q) ≫ HomologicalComplex.ιTensorObj M (colimit F) p q n h := by
  -- Proof comment: this is the same summand formula, now specialized to the colimit cocone leg.
  simpa [tensorizedSequentialCocone, HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorMap
      (K₁ := M) (K₂ := F.obj i) (L₁ := M) (L₂ := colimit F)
      (f₁ := 𝟙 M) (f₂ := colimit.ι F i) (F := curriedTensor (Mod(𝒪)))
      (c := ComplexShape.up ℤ) p q n h)

/-- Helper for Lemma 21.17.9: a cocone over the evaluated tensorized diagram induces, for each
`(p,q)` summand of total degree `n`, a cocone over the corresponding tensorized degree system. -/
private theorem tensorizedSequentialBranchCoconeNaturality
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    (n : ℤ)
    (s : Cocone
      ((tensorizedSequentialDiagram M F) ⋙
        HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n))
    (p q : ℤ) (h : p + q = n) :
    ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      (((F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) q) ⋙
          MonoidalCategory.tensorLeft (M.X p)).map f) ≫
          (HomologicalComplex.ιTensorObj M (F.obj j) p q n h ≫ s.ι.app j) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
  intro i j f
  have hmap :
      (((F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) q) ⋙
          MonoidalCategory.tensorLeft (M.X p)).map f) ≫
          (HomologicalComplex.ιTensorObj M (F.obj j) p q n h ≫ s.ι.app j) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
          (((tensorizedSequentialDiagram M F).map f).f n ≫ s.ι.app j) := by
    simpa [tensorizedSequentialDiagram, Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ k ≫ s.ι.app j)
        (tensorizedSequentialDiagramMapCompιTensorObj M F f p q n h).symm
  have hs :
      HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
          (((tensorizedSequentialDiagram M F).map f).f n ≫ s.ι.app j) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
    simpa [tensorizedSequentialDiagram, Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ k) (s.w f)
  exact hmap.trans hs

/-- Helper for Lemma 21.17.9: the branch maps coming from an evaluated cocone assemble to a cocone
on the `(p,q)` summand diagram. -/
private def tensorizedSequentialBranchCocone
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    (n : ℤ)
    (s : Cocone
      ((tensorizedSequentialDiagram M F) ⋙
        HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n))
    (p q : ℤ) (h : p + q = n) :
    Cocone
      (((F ⋙ HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) q) ⋙
        MonoidalCategory.tensorLeft (M.X p))) where
  pt := s.pt
  ι.app i := HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i
  ι.naturality := tensorizedSequentialBranchCoconeNaturality M F n s p q h

/-- Helper for Lemma 21.17.9: after evaluation at degree `n`, the explicit tensorized cocone
admits the canonical descender built from the branch colimits. -/
private def tensorizedSequentialEvalDesc
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorizedSequentialDiagram M F) ⋙
        HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n)) :
    (HomologicalComplex.tensorObj M (colimit F)).X n ⟶ s.pt :=
  HomologicalComplex.mapBifunctorDesc
    (fun p q h ↦
      (tensorizedSequentialSummandIsColimit M F p q).desc
        (tensorizedSequentialBranchCocone M F n s p q h))

/-- Helper for Lemma 21.17.9: restricting the evaluated descender to one `(p,q)` summand recovers
the descended map from the corresponding summand colimit cocone. -/
@[reassoc] private theorem iTensorObjTensorizedSequentialEvalDescAssoc
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorizedSequentialDiagram M F) ⋙
        HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n))
    (p q : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫
        tensorizedSequentialEvalDesc M F n s =
      (tensorizedSequentialSummandIsColimit M F p q).desc
        (tensorizedSequentialBranchCocone M F n s p q h) := by
  -- Proof comment: evaluate `mapBifunctorDesc` on the chosen summand using the owner universal
  -- property `ι_mapBifunctorDesc`.
  simpa [tensorizedSequentialEvalDesc, HomologicalComplex.ιTensorObj] using
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := M) (K₂ := colimit F) (F := curriedTensor (Mod(𝒪)))
      (c := ComplexShape.up ℤ) (A := s.pt) (j := n)
      (f := fun p q h ↦
        (tensorizedSequentialSummandIsColimit M F p q).desc
          (tensorizedSequentialBranchCocone M F n s p q h))
      p q h)

/-- Helper for Lemma 21.17.9: the branchwise descender from the tensorized summand colimits
commutes with each cocone leg after evaluation in degree `n`. -/
private theorem tensorizedSequentialEvalDescFac
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorizedSequentialDiagram M F) ⋙
        HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n))
    (i : ℕ) :
    ((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
        (tensorizedSequentialCocone M F)).ι.app i ≫
        tensorizedSequentialEvalDesc M F n s =
      s.ι.app i := by
  -- Proof comment: test the equality on each `(p,q)` summand of total degree `n`.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hleg :
      HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
          (((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
            (tensorizedSequentialCocone M F)).ι.app i ≫
              tensorizedSequentialEvalDesc M F n s) =
        (M.X p ◁ (colimit.ι F i).f q) ≫
          (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫
            tensorizedSequentialEvalDesc M F n s) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ tensorizedSequentialEvalDesc M F n s)
        (tensorizedSequentialCoconeLegCompιTensorObj M F i p q n h)
  have hdesc :
      (M.X p ◁ (colimit.ι F i).f q) ≫
          (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫
            tensorizedSequentialEvalDesc M F n s) =
        (M.X p ◁ (colimit.ι F i).f q) ≫
          (tensorizedSequentialSummandIsColimit M F p q).desc
            (tensorizedSequentialBranchCocone M F n s p q h) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ (M.X p ◁ (colimit.ι F i).f q) ≫ k)
        (iTensorObjTensorizedSequentialEvalDescAssoc M F n s p q h)
  have hfac :
      (M.X p ◁ (colimit.ι F i).f q) ≫
          (tensorizedSequentialSummandIsColimit M F p q).desc
            (tensorizedSequentialBranchCocone M F n s p q h) =
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
    simpa [tensorizedSequentialSummandCocone, tensorizedSequentialBranchCocone,
      Category.assoc] using
      (tensorizedSequentialSummandIsColimit M F p q).fac
        (tensorizedSequentialBranchCocone M F n s p q h) i
  exact hleg.trans (hdesc.trans hfac)

/-- Helper for Lemma 21.17.9: the branchwise descender on the evaluated tensorized cocone is the
unique morphism compatible with all cocone legs. -/
private theorem tensorizedSequentialEvalDescUniq
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (n : ℤ)
    (s : Cocone
      ((tensorizedSequentialDiagram M F) ⋙
        HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n))
    (m : ((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
        (tensorizedSequentialCocone M F)).pt ⟶ s.pt)
    (hm : ∀ i : ℕ,
      ((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
          (tensorizedSequentialCocone M F)).ι.app i ≫ m =
        s.ι.app i) :
    m = tensorizedSequentialEvalDesc M F n s := by
  -- Proof comment: descend the equality to every `(p,q)` summand, where uniqueness comes from
  -- the colimit universal property on that summand diagram.
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hbranch :
      ∀ i : ℕ,
        (tensorizedSequentialSummandCocone M F p q).ι.app i ≫
            (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m) =
          (tensorizedSequentialBranchCocone M F n s p q h).ι.app i := by
    intro i
    have hleg :
        (tensorizedSequentialSummandCocone M F p q).ι.app i ≫
            (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m) =
          HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
            (((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
              (tensorizedSequentialCocone M F)).ι.app i ≫ m) := by
      simpa [tensorizedSequentialSummandCocone, Category.assoc] using
        congrArg (fun k ↦ k ≫ m)
          (tensorizedSequentialCoconeLegCompιTensorObj M F i p q n h).symm
    have hm' :
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫
            (((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
              (tensorizedSequentialCocone M F)).ι.app i ≫ m) =
          HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ k) (hm i)
    have hbranchLeg :
        HomologicalComplex.ιTensorObj M (F.obj i) p q n h ≫ s.ι.app i =
          (tensorizedSequentialBranchCocone M F n s p q h).ι.app i := by
      rfl
    exact hleg.trans (hm'.trans hbranchLeg)
  have hdesc :
      HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m =
        (tensorizedSequentialSummandIsColimit M F p q).desc
          (tensorizedSequentialBranchCocone M F n s p q h) := by
    exact (tensorizedSequentialSummandIsColimit M F p q).uniq
      (tensorizedSequentialBranchCocone M F n s p q h)
      (HomologicalComplex.ιTensorObj M (colimit F) p q n h ≫ m)
      hbranch
  exact hdesc.trans (iTensorObjTensorizedSequentialEvalDescAssoc M F n s p q h).symm

/-- Helper for Lemma 21.17.9: after evaluation at degree `n`, the explicit tensorized cocone is
colimiting. -/
private def tensorizedSequentialEvalIsColimit
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    (n : ℤ) :
    IsColimit
      ((HomologicalComplex.eval (Mod(𝒪)) (ComplexShape.up ℤ) n).mapCocone
        (tensorizedSequentialCocone M F)) :=
  { desc := tensorizedSequentialEvalDesc M F n
    fac := tensorizedSequentialEvalDescFac M F n
    uniq := tensorizedSequentialEvalDescUniq M F n }

/-- Helper for Lemma 21.17.9: the explicit tensorized cocone is colimiting. -/
private noncomputable def tensorizedSequentialIsColimit
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F] :
    IsColimit (tensorizedSequentialCocone M F) :=
  HomologicalComplex.isColimitOfEval
    (F := tensorizedSequentialDiagram M F)
    (s := tensorizedSequentialCocone M F)
    (fun n ↦ tensorizedSequentialEvalIsColimit M F n)

/-- Helper for Lemma 21.17.9: once the explicit tensorized cocone is known to be colimiting, the
colimit of the tensorized sequential diagram identifies with `M ⊗ colimit F`. -/
private noncomputable def tensorizedSequentialDiagramColimitIso
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (M : CochainComplex (Mod(𝒪)) ℤ)
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ) [HasColimit F]
    [HasColimit (tensorizedSequentialDiagram M F)] :
    colimit (tensorizedSequentialDiagram M F) ≅
      HomologicalComplex.tensorObj M (colimit F) :=
  let hcolim := tensorizedSequentialIsColimit M F
  (hcolim.coconePointUniqueUpToIso (colimit.isColimit (tensorizedSequentialDiagram M F))).symm

/-- Helper for Lemma 21.17.9: a sequential colimit of K-flat cochain complexes of `𝒪`-modules is
K-flat. -/
private theorem sequentialColimitIsKFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    [HasColimit F]
    (hF : ∀ n : ℕ, (F.obj n).IsKFlat) :
    (colimit F).IsKFlat := by
  -- Route correction: avoid the blocked cochain-level `tensorLeft` owner search by building the
  -- tensorized sequential diagram explicitly and checking its colimit degreewise.
  rw [CochainComplex.isKFlat_iff]
  intro M _ hM
  let _ : HasColimit (tensorizedSequentialDiagram M F) :=
    HasColimit.mk ⟨tensorizedSequentialCocone M F, tensorizedSequentialIsColimit M F⟩
  have hTensorAcyclic :
      (colimit (tensorizedSequentialDiagram M F)).Acyclic := by
    -- Proof comment: every stage of the explicit tensorized diagram is acyclic, so its
    -- sequential colimit is acyclic by the lemma proved above.
    refine acyclicColimitOfSequential (G := tensorizedSequentialDiagram M F) ?_
    intro n
    exact CochainComplex.acyclic_tensorObj_of_isKFlat (hF n) hM
  -- Proof comment: transport that acyclicity across the explicit tensor/colimit comparison
  -- isomorphism.
  exact
    acyclicOfIso
      (tensorizedSequentialDiagramColimitIso M F)
      hTensorAcyclic

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Lemma 21.17.9: for a system `𝒦₁^• ⟶ 𝒦₂^• ⟶ ⋯` of K-flat cochain complexes of `𝒪`-modules on
a ringed site `(C, 𝒪)`, the sequential colimit `colim_i 𝒦_i^•` is K-flat. -/
@[stacks 06YR]
theorem sequentialColimit_isKFlat
    {𝒪 : Sheaf J CommRingCat.{max u v}}
    [MonoidalCategory (Mod(𝒪))]
    [MonoidalPreadditive (Mod(𝒪))]
    [(curriedTensor (Mod(𝒪))).Additive]
    [∀ ℱ : Mod(𝒪), ((curriedTensor (Mod(𝒪))).obj ℱ).Additive]
    (F : ℕ ⥤ CochainComplex (Mod(𝒪)) ℤ)
    [HasColimit F]
    (hF : ∀ i : ℕ, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := by
  exact sequentialColimitIsKFlat F hF

end SequentialColimitIsKFlat

end SheafOfModules.RingedSite
