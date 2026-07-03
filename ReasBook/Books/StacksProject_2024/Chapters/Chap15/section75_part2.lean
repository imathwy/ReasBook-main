import Mathlib
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.LinearAlgebra.Dimension.Finite

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_75_18 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for filtered-colimit descent of perfect derived complexes:
- primary domain: derived scalar extension of perfect objects over filtered colimits of
  commutative rings;
- owner declarations inspected in this domain:
  - `DerivedCategory.IsPerfect` from `Definition_15_75_1`;
  - the scalar-extension owner `derivedTensorWithAlgebra` and its notation
    `K ⊗[R]^L[A]` from `Lemma_15_60_1`;
  - the owner comparison `derivedTensorWithAlgebraCompIso` for iterated-vs-direct derived scalar
    extension from `Lemma_15_60_1`;
  - the source-facing filtered-colimit comparison for stagewise Hom-sets, whose public content is
    the factorization, transition-compatibility, and eventual-equality trio rather than a
    packaged colimit witness;
- best owner abstraction: the public surface here should be organized around the stagewise and
  colimit base-change owners together with the source-facing factorization and eventual-equality
  theorems, while the filtered-cocone packaging remains only an internal proof model if needed;
- primitive vs. derived:
  - primitive data are the filtered ring diagram `F`, the chosen base stage `i₀`, and the
    canonical ring maps `F.obj i₀ → F.obj j` and `F.obj j → colimit F`;
  - the stagewise transition maps and comparison morphisms into the colimit ring are primitive
    data for the explicit Hom-colimit construction;
  - the factorization, transition-compatibility, and eventual-equality assertions are the public
    source-facing API for part `(2)`, rather than a separate public `Functor` / `Cocone` /
    `IsColimit` package.

Source/core/bridge triage:
- `source-facing`: the perfect-complex descent theorem together with the stagewise factorization
  and eventual-equality statements for Homs after base change;
- `core/canonical`: `DerivedCategory.IsPerfect`, `derivedTensorWithAlgebra`, and the canonical
  iterated-scalar-extension owner `derivedTensorWithAlgebraCompIso`;
- `bridge/view`: the canonical comparison between iterated scalar extension through a stage and
  direct scalar extension to the colimit, used to define the source-facing transition maps on Hom
  sets without introducing a parallel public functor owner. -/

variable {I : Type v} [Preorder I] [IsFiltered I]
variable (F : I ⥤ CommRingCat.{u}) [HasColimit F]

/-- The filtered colimit ring `\operatorname{colim}_i R_i`. -/
private abbrev ringColimit : CommRingCat.{u} :=
  colimit F

/-- Base change from the stage ring `R_i` to the filtered colimit ring. -/
private abbrev baseChangeToColimit (i : I) :
    DerivedCategory (ModuleCat (F.obj i)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  derivedTensorWithAlgebra (colimit.ι F i).hom

-- Proof sketch: represent `K` by a bounded complex of finite projective modules over the colimit
-- ring, descend the finitely many finite projective terms to some stage using the filtered-colimit
-- results for finitely presented modules, and then descend the whole bounded complex.
/-- Lemma 15.75.18 (1): any perfect complex over a filtered colimit of commutative rings descends
to a perfect complex over some stage. -/
theorem exists_perfectComplex_stage_of_isPerfect
    (K : DerivedCategory (ModuleCat (ringColimit F)))
    (hK : K.IsPerfect) :
    ∃ (i : I) (Ki : DerivedCategory (ModuleCat (F.obj i))),
      Ki.IsPerfect ∧
        IsIsomorphic K ((baseChangeToColimit F i).obj Ki) := sorry

section

variable (i₀ : I)

/-- Base change from the fixed stage `R₀` to a later stage `R_j`. -/
private abbrev stageBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (F.obj i₀)) ⥤
      DerivedCategory (ModuleCat (F.obj j.1)) :=
  derivedTensorWithAlgebra (F.map (homOfLE j.2)).hom

/-- Base change from `R₀` to the filtered colimit ring. -/
private abbrev colimitBaseChange :
    DerivedCategory (ModuleCat (F.obj i₀)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  baseChangeToColimit F i₀

/-- Base change from a stage `R_j` to the filtered colimit ring. -/
private abbrev stageToColimitBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (ringColimit F)) :=
  baseChangeToColimit F j.1

/-- Base change along a transition map `R_j → R_k`. -/
private abbrev stageTransitionBaseChange {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    DerivedCategory (ModuleCat (F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (F.obj k.1)) :=
  derivedTensorWithAlgebra (F.map hjk).hom

omit [IsFiltered I] in
private theorem stageToColimitBaseChange_comp_eq (j : Set.Ici i₀) :
    (colimit.ι F j.1).hom.comp (F.map (homOfLE j.2)).hom = (colimit.ι F i₀).hom := by
  rw [← CommRingCat.hom_comp]
  simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.2))

omit [IsFiltered I] in
private theorem stageTransitionBaseChange_comp_eq {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    (F.map hjk).hom.comp (F.map (homOfLE j.2)).hom = (F.map (homOfLE k.2)).hom := by
  sorry

/-- The canonical comparison between base change `R₀ → R_j → \operatorname{colim} R_i` and
direct base change `R₀ → \operatorname{colim} R_i`. -/
private noncomputable abbrev stageToColimitBaseChangeIso (j : Set.Ici i₀) :
    stageBaseChange F i₀ j ⋙ stageToColimitBaseChange F i₀ j ≅ colimitBaseChange F i₀ :=
  derivedTensorWithAlgebraCompIso
    (F.map (homOfLE j.2)).hom
    (colimit.ι F j.1).hom
    (colimit.ι F i₀).hom
    (stageToColimitBaseChange_comp_eq F i₀ j)

/-- The canonical comparison between base change `R₀ → R_j → R_k` and direct base change
`R₀ → R_k`. -/
private noncomputable abbrev stageTransitionBaseChangeIso {j k : Set.Ici i₀} (hjk : j ⟶ k) :
    stageBaseChange F i₀ j ⋙ stageTransitionBaseChange F i₀ hjk ≅ stageBaseChange F i₀ k :=
  derivedTensorWithAlgebraCompIso
    (F.map (homOfLE j.2)).hom
    (F.map hjk).hom
    (F.map (homOfLE k.2)).hom
    (stageTransitionBaseChange_comp_eq F i₀ hjk)

/-- The canonical image in the colimit Hom-set of a stagewise morphism. -/
noncomputable def stageToColimitHomMap (j : Set.Ici i₀)
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    (colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀ :=
  let e := stageToColimitBaseChangeIso F i₀ j
  (e.app K₀).inv ≫ (stageToColimitBaseChange F i₀ j).map β ≫ (e.app L₀).hom

/-- The canonical image in a later-stage Hom-set of a stagewise morphism. -/
noncomputable def stageTransitionHomMap {j k : Set.Ici i₀} (hjk : j ⟶ k)
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    (stageBaseChange F i₀ k).obj K₀ ⟶ (stageBaseChange F i₀ k).obj L₀ :=
  let e := stageTransitionBaseChangeIso F i₀ hjk
  (e.app K₀).inv ≫ (stageTransitionBaseChange F i₀ hjk).map β ≫ (e.app L₀).hom

-- Proof sketch: the colimit cocone relation `R_j → R_k → colim F = R_j → colim F` gives a
-- canonical comparison between the two iterated scalar-extension functors from stage `j` to the
-- colimit. Naturality of the comparison isomorphisms then shows that passing from stage `j`
-- directly to the colimit agrees with first base-changing to a later stage `k` and then to the
-- colimit.
/-- The canonical images in the colimit Hom-set are compatible with the transition maps between
stages. This is the coherence needed for the source-facing filtered Hom-colimit comparison in
Lemma `15.75.18 (2)`. -/
theorem stageToColimitHomMap_transition
    {K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))}
    {j k : Set.Ici i₀} (hjk : j ⟶ k)
    (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀) :
    stageToColimitHomMap F i₀ k (stageTransitionHomMap F i₀ hjk β) =
      stageToColimitHomMap F i₀ j β := by
  sorry

-- Proof sketch: represent `K₀` by a bounded complex of finite projective modules over `R_{i₀}`,
-- compute the target morphism in the derived category by a bounded Hom complex after base change
-- to the colimit ring, and descend the finitely many terms of that calculation to a sufficiently
-- large stage `R_j`.
/-- Lemma 15.75.18 (2), surjectivity part: every morphism after base change from `R_{i₀}` to the
filtered colimit ring comes from some later stage. -/
theorem exists_stage_factorization_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect)
    (α : (colimitBaseChange F i₀).obj K₀ ⟶ (colimitBaseChange F i₀).obj L₀) :
    ∃ (j : Set.Ici i₀)
      (β : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀),
      α = stageToColimitHomMap F i₀ j β := sorry

-- Proof sketch: represent equality in the colimit Hom group by the same bounded Hom-complex
-- calculation as in part `(2)`; exactness of filtered colimits then implies that two stage
-- morphisms with the same image in the colimit already agree after further base change to a later
-- stage.
/-- Lemma 15.75.18 (2), injectivity part: if two stagewise morphisms have the same image after
base change to the filtered colimit ring, then they agree after further base change to a common
later stage. -/
theorem eventually_eq_of_stage_morphisms_with_equal_colimit_images_of_isPerfect
    (K₀ L₀ : DerivedCategory (ModuleCat (F.obj i₀))) (hK₀ : K₀.IsPerfect)
    (j : Set.Ici i₀)
    (β₁ β₂ : (stageBaseChange F i₀ j).obj K₀ ⟶ (stageBaseChange F i₀ j).obj L₀)
    (hβ : stageToColimitHomMap F i₀ j β₁ = stageToColimitHomMap F i₀ j β₂) :
    ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
      stageTransitionHomMap F i₀ hjk β₁ =
        stageTransitionHomMap F i₀ hjk β₂ := sorry

/- The declarations above give the essential-surjectivity and filtered Hom-colimit description for
perfect complexes over a filtered colimit of commutative rings, with part `(2)` exposed directly
through the source-facing stage-factorization, transition-compatibility, and eventual-equality
theorems rather than through wrapper names for stagewise Hom-sets or a public `Functor` /
`Cocone` / `IsColimit` package. -/

end

end

end CategoryTheory
