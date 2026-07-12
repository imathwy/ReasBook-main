import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.Sites.Pretopology

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry

-- Semantic recall: the canonical scheme-side owner used here is
-- `Scheme.Cover Scheme.zariskiPrecoverage`. This item is
-- the source-facing chosen-presentation notion of a big Zariski site, not the canonical big
-- Zariski site of a fixed scheme, so the seed schemes and seed coverings are kept explicit while
-- the cover-preservation condition is stated through the canonical Zariski-cover owner and then
-- bridged back to the chosen site pretopology.

/-- A chosen Zariski covering together with its target scheme. -/
abbrev ChosenZariskiCover : Type (u + 1) :=
  Σ T : Scheme.{u}, Scheme.Cover Scheme.zariskiPrecoverage T

/-- Definition 34.3.5: a big Zariski site consists of a chosen set `S_0` of schemes, a chosen set
`Cov_0` of Zariski coverings among them, and a site whose underlying category is a chosen category
of schemes equipped with covering families that map to Zariski coverings. -/
@[stacks 020S]
structure BigZariskiSite where
  /-- The chosen set `S_0` of schemes used to seed the construction. -/
  seedSchemes : Set Scheme.{u}
  /-- The chosen set `Cov_0` of Zariski coverings among the seed schemes. -/
  seedCoverings : Set ChosenZariskiCover
  /-- Every chosen seed covering is a Zariski covering between seed schemes. -/
  seedCoverings_mem_seedSchemes :
      ∀ ⦃𝒰 : ChosenZariskiCover⦄, 𝒰 ∈ seedCoverings →
        𝒰.1 ∈ seedSchemes ∧ ∀ i : 𝒰.2.I₀, 𝒰.2.X i ∈ seedSchemes
  /-- The underlying category `Sch_α` of the chosen big Zariski site. -/
  carrier : Type u
  /-- The category structure on the chosen underlying category of schemes. -/
  [categoryCarrier : Category.{v} carrier]
  /-- The chosen underlying category has pullbacks, as required to speak about a pretopology. -/
  [hasPullbacksCarrier : Limits.HasPullbacks carrier]
  /-- The functor identifying the objects and morphisms of `Sch_α` with schemes. -/
  toScheme : carrier ⥤ Scheme.{u}
  /-- The chosen site structure on `Sch_α`. -/
  pretopology : Pretopology carrier
  /-- Every site covering presieve is represented, after forgetting to `Scheme`, by a Zariski
  covering family of the target scheme. -/
  siteCovering_exists_zariskiCover :
      ∀ ⦃T : carrier⦄ (R : Presieve T), R ∈ pretopology T →
        ∃ 𝒰 : Scheme.Cover Scheme.zariskiPrecoverage (toScheme.obj T),
          R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f

/-- A big Zariski site coerces to its chosen underlying category of schemes. -/
instance : CoeSort BigZariskiSite (Type u) where
  coe X := X.carrier

namespace BigZariskiSite

variable (X : BigZariskiSite.{u, v})

/-- A big Zariski site carries the category structure of its chosen underlying category. -/
instance instCategoryCarrier : Category.{v} X :=
  X.categoryCarrier

/-- A big Zariski site carries pullbacks on its chosen underlying category. -/
instance instHasPullbacksCarrier : Limits.HasPullbacks X :=
  X.hasPullbacksCarrier

/-- The Grothendieck topology associated to the chosen pretopology of a big Zariski site. -/
abbrev toGrothendieck : GrothendieckTopology X :=
  X.pretopology.toGrothendieck

/-- Every chosen seed covering in a big Zariski site has target in the chosen seed set. -/
theorem seedCovering_target_mem {𝒰 : ChosenZariskiCover} (h𝒰 : 𝒰 ∈ X.seedCoverings) :
    𝒰.1 ∈ X.seedSchemes :=
  (X.seedCoverings_mem_seedSchemes h𝒰).1

/-- Every source scheme in a chosen seed covering of a big Zariski site belongs to the chosen seed
set. -/
theorem seedCovering_source_mem {𝒰 : ChosenZariskiCover} (h𝒰 : 𝒰 ∈ X.seedCoverings)
    (i : 𝒰.2.I₀) :
    𝒰.2.X i ∈ X.seedSchemes :=
  (X.seedCoverings_mem_seedSchemes h𝒰).2 i

/-- Every covering presieve in a big Zariski site is represented, after forgetting to `Scheme`,
by a Zariski covering family of the underlying target scheme. -/
theorem covering_exists_zariskiCover {T : X} (R : Presieve T) (hR : R ∈ X.pretopology T) :
    ∃ 𝒰 : Scheme.Cover Scheme.zariskiPrecoverage (X.toScheme.obj T),
      R.map X.toScheme = Presieve.ofArrows 𝒰.X 𝒰.f :=
  X.siteCovering_exists_zariskiCover R hR

/-- Every covering presieve in a big Zariski site maps to a Zariski covering presieve of schemes. -/
theorem mem_zariskiPrecoverage {T : X} (R : Presieve T) (hR : R ∈ X.pretopology T) :
    R.map X.toScheme ∈ Scheme.zariskiPrecoverage.coverings (X.toScheme.obj T) := by
  rcases X.covering_exists_zariskiCover R hR with ⟨𝒰, h𝒰⟩
  simpa [h𝒰] using 𝒰.mem₀

/-- A big Zariski site is contained in another when the larger site contains its chosen seed
schemes and chosen seed coverings. -/
def IsContainedIn (X Y : BigZariskiSite.{u, v}) : Prop :=
  X.seedSchemes ⊆ Y.seedSchemes ∧ X.seedCoverings ⊆ Y.seedCoverings

end BigZariskiSite

end AlgebraicGeometry
