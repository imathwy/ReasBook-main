import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.Sites.Pretopology

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `Scheme.zariskiPrecoverage`, `Scheme.etalePrecoverage`, and
-- `Scheme.fppfPrecoverage` are the canonical covering-family owners on schemes. This lemma keeps
-- the source-facing chosen small-site presentations, but factors their common site data through a
-- single owner parameterized by the chosen scheme precoverage.

/-- A chosen covering for a scheme precoverage, together with its target scheme. -/
abbrev ChosenCover (P : Pretopology Scheme.{u}) : Type (u + 1) :=
  Σ T : Scheme.{u}, Scheme.Cover P T

/-- A chosen big site for a scheme precoverage consists of a chosen set of schemes, a chosen set
of coverings among them, and a site whose covering families map to coverings for that precoverage.
-/
structure BigSite (P : Pretopology Scheme.{u}) where
  /-- The chosen set `S_0` of schemes used to seed the construction. -/
  seedSchemes : Set Scheme.{u}
  /-- The chosen set `Cov_0` of coverings among the seed schemes. -/
  seedCoverings : Set (ChosenCover P)
  /-- Every chosen seed covering lies between seed schemes. -/
  seedCoverings_mem_seedSchemes :
      ∀ ⦃𝒰 : ChosenCover P⦄, 𝒰 ∈ seedCoverings →
        𝒰.1 ∈ seedSchemes ∧ ∀ i : 𝒰.2.I₀, 𝒰.2.X i ∈ seedSchemes
  /-- The underlying category `Sch_α` of the chosen big site. -/
  carrier : Type u
  /-- The category structure on the chosen underlying category of schemes. -/
  [categoryCarrier : Category.{v} carrier]
  /-- The chosen underlying category has pullbacks, as required to speak about a pretopology. -/
  [hasPullbacksCarrier : Limits.HasPullbacks carrier]
  /-- The functor identifying the objects and morphisms of `Sch_α` with schemes. -/
  toScheme : carrier ⥤ Scheme.{u}
  /-- The chosen site structure on `Sch_α`. -/
  pretopology : Pretopology carrier
  /-- Every site covering presieve is represented, after forgetting to `Scheme`, by a covering of
  the target scheme for the chosen precoverage. -/
  siteCovering_exists_cover :
      ∀ ⦃T : carrier⦄ (R : Presieve T), R ∈ pretopology T →
        ∃ 𝒰 : Scheme.Cover P (toScheme.obj T),
          R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f

/-- A big site coerces to its chosen underlying category of schemes. -/
instance (P : Pretopology Scheme.{u}) : CoeSort (BigSite P) (Type u) where
  coe X := X.carrier

namespace BigSite

variable {P : Pretopology Scheme.{u}} (X : BigSite P)

/-- A big site carries the category structure of its chosen underlying category. -/
instance instCategoryCarrier : Category.{v} X :=
  X.categoryCarrier

/-- A big site carries pullbacks on its chosen underlying category. -/
instance instHasPullbacksCarrier : Limits.HasPullbacks X :=
  X.hasPullbacksCarrier

/-- The Grothendieck topology associated to the chosen pretopology of a big site. -/
abbrev toGrothendieck : GrothendieckTopology X :=
  X.pretopology.toGrothendieck

/-- Every covering presieve in a big site is represented, after forgetting to `Scheme`, by a
covering of the underlying target scheme. -/
theorem covering_exists_cover {T : X} (R : Presieve T) (hR : R ∈ X.pretopology T) :
    ∃ 𝒰 : Scheme.Cover P (X.toScheme.obj T),
      R.map X.toScheme = Presieve.ofArrows 𝒰.X 𝒰.f :=
  X.siteCovering_exists_cover R hR

/-- Every covering presieve in a big site maps to a covering presieve of schemes for the chosen
precoverage. -/
theorem mem_coverings {T : X} (R : Presieve T) (hR : R ∈ X.pretopology T) :
    R.map X.toScheme ∈ P.coverings (X.toScheme.obj T) := by
  rcases X.covering_exists_cover R hR with ⟨𝒰, h𝒰⟩
  simpa [h𝒰] using 𝒰.mem₀

/-- Every chosen seed covering in a big site has target in the chosen seed set. -/
theorem seedCovering_target_mem {𝒰 : ChosenCover P} (h𝒰 : 𝒰 ∈ X.seedCoverings) :
    𝒰.1 ∈ X.seedSchemes :=
  (X.seedCoverings_mem_seedSchemes h𝒰).1

/-- Every source scheme in a chosen seed covering of a big site belongs to the chosen seed set. -/
theorem seedCovering_source_mem {𝒰 : ChosenCover P} (h𝒰 : 𝒰 ∈ X.seedCoverings)
    (i : 𝒰.2.I₀) :
    𝒰.2.X i ∈ X.seedSchemes :=
  (X.seedCoverings_mem_seedSchemes h𝒰).2 i

/-- A big site is contained in another when the larger site contains its chosen seed schemes and
chosen seed coverings. -/
def IsContainedIn (X Y : BigSite P) : Prop :=
  X.seedSchemes ⊆ Y.seedSchemes ∧ X.seedCoverings ⊆ Y.seedCoverings

end BigSite

/-- A chosen Zariski covering together with its target scheme. -/
abbrev ChosenZariskiCover : Type (u + 1) :=
  ChosenCover Scheme.zariskiPrecoverage

/-- A chosen big Zariski site. -/
abbrev BigZariskiSite : Type (max (u + 1) v) :=
  BigSite Scheme.zariskiPrecoverage

namespace BigZariskiSite

/-- The containment relation for big Zariski sites. -/
abbrev IsContainedIn (X Y : BigZariskiSite.{u, v}) : Prop :=
  BigSite.IsContainedIn X Y

/-- The Grothendieck topology associated to the chosen pretopology of a big Zariski site. -/
abbrev toGrothendieck (X : BigZariskiSite.{u, v}) : GrothendieckTopology X :=
  BigSite.toGrothendieck X

/-- Every covering presieve in a big Zariski site is represented, after forgetting to `Scheme`, by
a Zariski covering of the underlying target scheme. -/
theorem covering_exists_zariskiCover (X : BigZariskiSite.{u, v}) {T : X} (R : Presieve T)
    (hR : R ∈ X.pretopology T) :
    ∃ 𝒰 : Scheme.Cover Scheme.zariskiPrecoverage (X.toScheme.obj T),
      R.map X.toScheme = Presieve.ofArrows 𝒰.X 𝒰.f :=
  X.covering_exists_cover R hR

/-- Every covering presieve in a big Zariski site maps to a Zariski covering presieve of schemes. -/
theorem mem_zariskiPrecoverage (X : BigZariskiSite.{u, v}) {T : X} (R : Presieve T)
    (hR : R ∈ X.pretopology T) :
    R.map X.toScheme ∈ Scheme.zariskiPrecoverage.coverings (X.toScheme.obj T) :=
  X.mem_coverings R hR

/-- Every chosen seed covering in a big Zariski site has target in the chosen seed set. -/
theorem seedCovering_target_mem (X : BigZariskiSite.{u, v}) {𝒰 : ChosenZariskiCover}
    (h𝒰 : 𝒰 ∈ X.seedCoverings) :
    𝒰.1 ∈ X.seedSchemes :=
  @BigSite.seedCovering_target_mem u v Scheme.zariskiPrecoverage X 𝒰 h𝒰

/-- Every source scheme in a chosen seed covering of a big Zariski site belongs to the chosen seed
set. -/
theorem seedCovering_source_mem (X : BigZariskiSite.{u, v}) {𝒰 : ChosenZariskiCover}
    (h𝒰 : 𝒰 ∈ X.seedCoverings) (i : 𝒰.2.I₀) :
    𝒰.2.X i ∈ X.seedSchemes :=
  @BigSite.seedCovering_source_mem u v Scheme.zariskiPrecoverage X 𝒰 h𝒰 i

end BigZariskiSite

/-- A chosen étale covering together with its target scheme. -/
abbrev ChosenEtaleCover : Type (u + 1) :=
  ChosenCover Scheme.etalePrecoverage

/-- A chosen big étale site. -/
abbrev BigEtaleSite : Type (max (u + 1) v) :=
  BigSite Scheme.etalePrecoverage

namespace BigEtaleSite

/-- The containment relation for big étale sites. -/
abbrev IsContainedIn (X Y : BigEtaleSite.{u, v}) : Prop :=
  BigSite.IsContainedIn X Y

/-- The Grothendieck topology associated to the chosen pretopology of a big étale site. -/
abbrev toGrothendieck (X : BigEtaleSite.{u, v}) : GrothendieckTopology X :=
  BigSite.toGrothendieck X

/-- Every covering presieve in a big étale site is represented, after forgetting to `Scheme`, by
an étale covering of the underlying target scheme. -/
theorem covering_exists_etaleCover (X : BigEtaleSite.{u, v}) {T : X} (R : Presieve T)
    (hR : R ∈ X.pretopology T) :
    ∃ 𝒰 : Scheme.Cover Scheme.etalePrecoverage (X.toScheme.obj T),
      R.map X.toScheme = Presieve.ofArrows 𝒰.X 𝒰.f :=
  X.covering_exists_cover R hR

/-- Every covering presieve in a big étale site maps to an étale covering presieve of schemes. -/
theorem mem_etalePrecoverage (X : BigEtaleSite.{u, v}) {T : X} (R : Presieve T)
    (hR : R ∈ X.pretopology T) :
    R.map X.toScheme ∈ Scheme.etalePrecoverage.coverings (X.toScheme.obj T) :=
  X.mem_coverings R hR

/-- Every chosen seed covering in a big étale site has target in the chosen seed set. -/
theorem seedCovering_target_mem (X : BigEtaleSite.{u, v}) {𝒰 : ChosenEtaleCover}
    (h𝒰 : 𝒰 ∈ X.seedCoverings) :
    𝒰.1 ∈ X.seedSchemes :=
  @BigSite.seedCovering_target_mem u v Scheme.etalePrecoverage X 𝒰 h𝒰

/-- Every source scheme in a chosen seed covering of a big étale site belongs to the chosen seed
set. -/
theorem seedCovering_source_mem (X : BigEtaleSite.{u, v}) {𝒰 : ChosenEtaleCover}
    (h𝒰 : 𝒰 ∈ X.seedCoverings) (i : 𝒰.2.I₀) :
    𝒰.2.X i ∈ X.seedSchemes :=
  @BigSite.seedCovering_source_mem u v Scheme.etalePrecoverage X 𝒰 h𝒰 i

end BigEtaleSite

/-- A chosen fppf covering together with its target scheme. -/
abbrev ChosenFppfCover : Type (u + 1) :=
  ChosenCover Scheme.fppfPrecoverage

/-- A chosen big fppf site. -/
abbrev BigFppfSite : Type (max (u + 1) v) :=
  BigSite Scheme.fppfPrecoverage

namespace BigFppfSite

/-- The containment relation for big fppf sites. -/
abbrev IsContainedIn (X Y : BigFppfSite.{u, v}) : Prop :=
  BigSite.IsContainedIn X Y

/-- The Grothendieck topology associated to the chosen pretopology of a big fppf site. -/
abbrev toGrothendieck (X : BigFppfSite.{u, v}) : GrothendieckTopology X :=
  BigSite.toGrothendieck X

/-- Every covering presieve in a big fppf site is represented, after forgetting to `Scheme`, by
an fppf covering of the underlying target scheme. -/
theorem covering_exists_fppfCover (X : BigFppfSite.{u, v}) {T : X} (R : Presieve T)
    (hR : R ∈ X.pretopology T) :
    ∃ 𝒰 : Scheme.Cover Scheme.fppfPrecoverage (X.toScheme.obj T),
      R.map X.toScheme = Presieve.ofArrows 𝒰.X 𝒰.f :=
  X.covering_exists_cover R hR

/-- Every covering presieve in a big fppf site maps to an fppf covering presieve of schemes. -/
theorem mem_fppfPrecoverage (X : BigFppfSite.{u, v}) {T : X} (R : Presieve T)
    (hR : R ∈ X.pretopology T) :
    R.map X.toScheme ∈ Scheme.fppfPrecoverage.coverings (X.toScheme.obj T) :=
  X.mem_coverings R hR

/-- Every chosen seed covering in a big fppf site has target in the chosen seed set. -/
theorem seedCovering_target_mem (X : BigFppfSite.{u, v}) {𝒰 : ChosenFppfCover}
    (h𝒰 : 𝒰 ∈ X.seedCoverings) :
    𝒰.1 ∈ X.seedSchemes :=
  @BigSite.seedCovering_target_mem u v Scheme.fppfPrecoverage X 𝒰 h𝒰

/-- Every source scheme in a chosen seed covering of a big fppf site belongs to the chosen seed
set. -/
theorem seedCovering_source_mem (X : BigFppfSite.{u, v}) {𝒰 : ChosenFppfCover}
    (h𝒰 : 𝒰 ∈ X.seedCoverings) (i : 𝒰.2.I₀) :
    𝒰.2.X i ∈ X.seedSchemes :=
  @BigSite.seedCovering_source_mem u v Scheme.fppfPrecoverage X 𝒰 h𝒰 i

end BigFppfSite

/-- Lemma 34.12.1 (1): any set of big Zariski sites is contained in a common big Zariski site. -/
@[stacks 022J]
theorem exists_commonBigZariskiSite (A : Set BigZariskiSite.{u, v}) :
    ∃ Y : BigZariskiSite.{u, v},
      ∀ ⦃X : BigZariskiSite.{u, v}⦄, X ∈ A → X.IsContainedIn Y := sorry

/-- Lemma 34.12.1 (2): any set of big fppf sites is contained in a common big fppf site. -/
@[stacks 022J]
theorem exists_commonBigFppfSite (A : Set BigFppfSite.{u, v}) :
    ∃ Y : BigFppfSite.{u, v},
      ∀ ⦃X : BigFppfSite.{u, v}⦄, X ∈ A → X.IsContainedIn Y := sorry

/-- Lemma 34.12.1 (3): any set of big étale sites is contained in a common big étale site. -/
@[stacks 022J]
theorem exists_commonBigEtaleSite (A : Set BigEtaleSite.{u, v}) :
    ∃ Y : BigEtaleSite.{u, v},
      ∀ ⦃X : BigEtaleSite.{u, v}⦄, X ∈ A → X.IsContainedIn Y := sorry

end AlgebraicGeometry
