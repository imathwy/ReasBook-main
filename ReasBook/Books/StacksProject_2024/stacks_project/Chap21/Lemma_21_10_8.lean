import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheaf
import StacksProject_2024.Chap07.Definition_7_8_2
import StacksProject_2024.Chap21.Definition_21_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section

variable (U : C) [HasFiniteProducts (Over U)] [HasProducts AddCommGrpCat.{v}]

/- Domain-style sampling for Lemma 21.10.8:
- primary domain: Čech cohomology of abelian presheaves on the slice site `(C / U, J.over U)` and
  its interaction with short exact sequences of abelian sheaves;
- sampled owner declarations:
  `cechComplex`,
  `cechCohomology`,
  `GrothendieckTopology.CoversTop`,
  `SemiRepresentableFamily.Over.Refines`,
  `SemiRepresentableFamily.Over.ofArrows`;
- best owner abstraction:
  `source-facing`: the cofinal Čech-vanishing predicate for fixed-target covering families over
    `U`;
  `core/canonical`: the degree-`1` Čech cohomology owner `cechCohomology U family F 1`;
  `bridge/view`: the slice-site cover owner `GrothendieckTopology.CoversTop` together with
    the same-target family owner `Refines`, applied to indexed `Over U` families through
    `ofArrows`.
- primitive data: the site `(C, J)`, the object `U`, an explicit covering family
  `family : ι → Over U`, and the underlying abelian presheaf `F`;
- derived API here: the cofinal-refinement predicate and the surjectivity consequence for a short
  exact sequence of abelian sheaves.

Source/core/bridge triage:
- `source-facing`: `HasVanishingFirstCechOnCofinalCoverings` and the surjectivity lemma;
- `core/canonical`: `cechComplexFunctor` and the chapter owner `cechCohomology`;
- `bridge/view`: restriction along `(Over.forget U).op` from presheaves on `C` to presheaves on
  `Over U`, together with `GrothendieckTopology.CoversTop` and the fixed-target family owner
  `Refines`.

The refinement therefore keeps the source-facing predicate, but rewrites its payload to the owner
`cechCohomology U family F 1` and the canonical slice-site cover owner `CoversTop`; refinement is
expressed through the chapter owner `Refines` rather than by a raw morphism witness between
formal coproducts.
-/
-- Semantic search check: no existing mathlib/project theorem matched this cofinal Čech-vanishing
-- to surjectivity statement, and nearby Chapter 21 files use the same `CoversTop`/`Refines` API.

/-- A presheaf has vanishing first Čech cohomology on a cofinal collection of coverings of `U` if
every covering family of `U` admits a refinement whose first Čech cohomology vanishes. -/
@[stacks 03F8]
def HasVanishingFirstCechOnCofinalCoverings
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ {ι : Type w} (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        IsZero (cechCohomology U W F 1)

namespace Sheaf

/-- An abelian sheaf has vanishing first Čech cohomology on a cofinal collection of coverings of
`U` if its underlying abelian presheaf does. -/
@[stacks 03F8]
abbrev HasVanishingFirstCechOnCofinalCoverings
    (F : Sheaf J AddCommGrpCat.{v}) : Prop :=
  CategoryTheory.HasVanishingFirstCechOnCofinalCoverings U J
    ((sheafToPresheaf J AddCommGrpCat.{v}).obj F)

-- Proof sketch: this is the presheaf-level unpacking theorem specialized to the underlying
-- abelian presheaf of `F`.
/-- Unfolding the cofinal Čech-vanishing hypothesis for a sheaf yields a refining covering of `U`
with trivial first Čech cohomology for the underlying abelian presheaf. -/
@[stacks 03F8]
theorem hasVanishingFirstCechOnCofinalCoverings_exists_refinement
    {F : Sheaf J AddCommGrpCat.{v}}
    (hF : F.HasVanishingFirstCechOnCofinalCoverings U)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        IsZero (cechCohomology U W ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) 1) := sorry

end Sheaf

-- Proof sketch: this is just the defining expansion of
-- `HasVanishingFirstCechOnCofinalCoverings`; apply the hypothesis to the chosen covering family.
/-- Unfolding the cofinal Čech-vanishing hypothesis yields a refining covering of `U` with trivial
first Čech cohomology. -/
@[stacks 03F8]
theorem hasVanishingFirstCechOnCofinalCoverings_exists_refinement
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hF : HasVanishingFirstCechOnCofinalCoverings U J F)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        IsZero (cechCohomology U W F 1) := sorry

omit [HasFiniteProducts (Over U)] [HasProducts AddCommGrpCat.{v}] in
/-- Helper for Lemma 21.10.8: a covering sieve on `U` induces a covering family in the slice site
`(C / U, J.over U)`. -/
private theorem coverArrowObjects_overSieve_eq
    (S : J.Cover U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun a : S.Arrow ↦ Over.mk a.f) (Over.mk (𝟙 U))) =
      (S : Sieve U) := sorry

omit [HasFiniteProducts (Over U)] [HasProducts AddCommGrpCat.{v}] in
/-- Helper for Lemma 21.10.8: a covering sieve on `U` induces a covering family in the slice site
`(C / U, J.over U)`. -/
private theorem coverArrows_coversTop
    (S : J.Cover U) :
    (J.over U).CoversTop (fun a : S.Arrow ↦ Over.mk a.f) := sorry

/-- Helper for Lemma 21.10.8: once a small-index covering family of `U` carries local lifts of
`s`, the cofinal Čech-vanishing hypothesis refines it to a cover on which `S.X₁` has vanishing
first Čech cohomology while preserving explicit local lifts. -/
private theorem existsVanishingRefinedLiftFamily
    (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (_hS : S.ShortExact)
    (hcech : S.X₁.HasVanishingFirstCechOnCofinalCoverings U)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V)
    (s : S.X₃.1.obj (op U))
    (τ : ∀ i, S.X₂.1.obj (op (V i).left))
    (hτ : ∀ i, S.g.1.app (op (V i).left) (τ i) = S.X₃.1.map (V i).hom.op s) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        IsZero (cechCohomology U W S.X₁.1 1) ∧
          ∃ σ : ∀ i, S.X₂.1.obj (op (W i).left),
            ∀ i, S.g.1.app (op (W i).left) (σ i) = S.X₃.1.map (W i).hom.op s := sorry

omit [HasFiniteProducts (Over U)] [HasProducts AddCommGrpCat.{v}] in
/-- Helper for Lemma 21.10.8: two local lifts of the same global section have difference mapping
to zero after restricting to any common test object. -/
private theorem localLiftDifferenceMapsToZero
    {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {κ : Type w} {W : κ → Over U}
    {s : S.X₃.1.obj (op U)}
    {σ : ∀ i, S.X₂.1.obj (op (W i).left)}
    (hσ : ∀ i, S.g.1.app (op (W i).left) (σ i) = S.X₃.1.map (W i).hom.op s)
    {T : C} {i j : κ} (a : T ⟶ (W i).left) (b : T ⟶ (W j).left)
    (hab : a ≫ (W i).hom = b ≫ (W j).hom) :
    S.g.1.app (op T) (S.X₂.1.map a.op (σ i) - S.X₂.1.map b.op (σ j)) = 0 := sorry

end

-- Proof sketch: use exactness to identify local lifts of a section of `S.X₃` as a Čech
-- `1`-cocycle with values in `S.X₁`; then refine the chosen cover so that the first Čech
-- cohomology of `S.X₁` vanishes, making the cocycle a coboundary. Correct the local lifts by this
-- coboundary and glue the resulting compatible sections of `S.X₂` to a global lift over `U`.
-- The surjectivity conclusion is stated on the canonical sections owner `Γ(U, -)`, namely
-- `((sheafSections J AddCommGrpCat).obj (op U)).map S.g`, rather than on the raw underlying
-- presheaf evaluation map.
/-- Lemma 21.10.8: if `0 ⟶ 𝒜 ⟶ ℬ ⟶ 𝒞 ⟶ 0` is a short exact sequence
of abelian sheaves on a site, if `U` is an object whose slice `C / U` has finite products so that
the relevant Čech intersections are defined, and the left term has vanishing first Čech
cohomology on a cofinal collection of coverings of `U`, then the canonical sections map
`Γ(U, ℬ) ⟶ Γ(U, 𝒞)` is surjective. -/
@[stacks 03F8]
theorem shortExact_right_map_surjective_of_vanishingFirstCech_on_cofinal_coverings
    (U : C) [HasFiniteProducts (Over U)]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact)
    (hcech : S.X₁.HasVanishingFirstCechOnCofinalCoverings U) :
    Function.Surjective (((sheafSections J AddCommGrpCat.{v}).obj (op U)).map S.g) := sorry

end CategoryTheory
