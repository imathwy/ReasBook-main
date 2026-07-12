import StacksProject_2024.Chap21.Definition_21_8_1
import StacksProject_2024.Chap21.Lemma_21_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open Opposite

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})]
variable {U : C} [HasFiniteProducts (Over U)]
variable {ι : Type u}

/- Domain-style sampling for Lemma 21.10.7:
- primary domain: Čech cohomology versus sheaf cohomology for abelian sheaves on a site, together
  with the iterated Čech intersections of a covering family;
- sampled canonical/project declarations:
  `cechCohomologyOnSheaves`,
  `IsCechCohomologyToSiteCohomologySucc`,
  `cechCoverIntersectionIndex`,
  `cechCoverIntersectionObject`,
  `Sheaf.H'`,
  `exists_cechToSheafCohomologySpectralSequence`;
- best owner abstraction: the iterated-intersection data should be expressed through the shared
  Čech-intersection owners on `FormalCoproduct (Over U)`, while the public comparison statement
  should be phrased for a positive-degree comparison morphism
  `f : Čech H^(p + 1)(𝒰, F) ⟶ H^(p + 1)(U, F)` together with
  `IsCechCohomologyToSiteCohomologySucc J U family p F f`;
- primitive data: the covering family `family`, the cover proof `hfamily`, the sheaf `F`, and
  the vanishing of positive
  cohomology objects `F.H' q _` on the Čech intersections of `FormalCoproduct.mk ι family`;
- derived API: the resulting `IsIso` statement for the chosen positive-degree Čech comparison
  morphism, viewed on the canonical site-cohomology target `F.H' (p + 1) U`.

Source/core/bridge triage:
- `source-facing`: the positive-degree acyclic-intersection criterion saying the resulting
  Čech-to-site comparison is an isomorphism over `U`;
- `core/canonical`: `Sheaf.H'`, `IsCechCohomologyToSiteCohomologySucc`, and the shared
  Čech-intersection owners `cechCoverIntersectionIndex` / `cechCoverIntersectionObject`;
- `bridge/view`: the family `family : ι → Over U` viewed as the formal coproduct
  `FormalCoproduct.mk ι family`, together with the induced higher-degree comparison
  predicate `IsCechCohomologyToSiteCohomologySucc ... p F f`.
-/

/-- The covering family `family` has acyclic iterated Čech intersections for `F` if every
positive-degree cohomology object `F.H' q _` vanishes on every iterated Čech intersection of
`FormalCoproduct.mk ι family`. -/
def HasAcyclicCechIntersections
    (family : ι → Over U) (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  ∀ (q : ℕ+) (n : ℕ)
    (i : cechCoverIntersectionIndex (FormalCoproduct.mk ι family) n),
      IsZero (F.H' q.1 (cechCoverIntersectionObject (FormalCoproduct.mk ι family) n i))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})] in
/-- Companion projection from `HasAcyclicCechIntersections family F` to a specific iterated Čech
intersection. -/
theorem HasAcyclicCechIntersections.isZero
    {family : ι → Over U} {F : Sheaf J AddCommGrpCat.{u}}
    (hacyclic : HasAcyclicCechIntersections family F)
    {q : ℕ} (hq : 0 < q) (n : ℕ)
    (i : cechCoverIntersectionIndex (FormalCoproduct.mk ι family) n) :
    IsZero (F.H' q (cechCoverIntersectionObject (FormalCoproduct.mk ι family) n i)) :=
  hacyclic ⟨q, hq⟩ n i

omit [HasWeakSheafify J AddCommGrpCat.{u}] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})] in
/-- Typeclass form of `HasAcyclicCechIntersections.isZero`, using `Fact (0 < q)` for the
positivity input. -/
instance HasAcyclicCechIntersections.instIsZeroHPrimeCechCoverIntersection
    {family : ι → Over U} {F : Sheaf J AddCommGrpCat.{u}}
    (hacyclic : HasAcyclicCechIntersections family F)
    (q : ℕ) [Fact (0 < q)] (n : ℕ)
    (i : cechCoverIntersectionIndex (FormalCoproduct.mk ι family) n) :
    IsZero (F.H' q (cechCoverIntersectionObject (FormalCoproduct.mk ι family) n i)) :=
  hacyclic.isZero Fact.out n i

-- Proof sketch: apply the spectral sequence of Lemma `21.10.6`. The hypothesis says that every
-- positive objectwise cohomology group `F.H' q _` with `q > 0` vanishes on each term of the Čech
-- nerve of `family`, so its associated Čech complex is zero and the `E₂`-page is concentrated on
-- the `q = 0` row. The spectral sequence therefore degenerates at `E₂`, and the remaining row
-- identifies `Čech H^(p + 1)(𝒰, F)` with `H^(p + 1)(U, F)`.
/-- Lemma 21.10.7: if every positive-degree cohomology group of `F` vanishes on every iterated
Čech intersection of the covering family `family`, then any positive-degree comparison morphism
`f : Čech H^(p + 1)(𝒰, F) ⟶ H^(p + 1)(U, F)` satisfying
`IsCechCohomologyToSiteCohomologySucc J U family p F f` is an isomorphism. The iterated
intersections are formalized by
`HasAcyclicCechIntersections family F`. -/
@[stacks 03F7]
theorem cechCohomology_iso_siteCohomology_of_acyclic_intersections
    (family : ι → Over U) (hfamily : (J.over U).CoversTop family)
    (p : ℕ)
    (F : Sheaf J AddCommGrpCat.{u})
    (hacyclic : HasAcyclicCechIntersections family F)
    (f : ((cechCohomologyOnSheaves J family (p + 1)).obj F) ⟶ F.H' (p + 1) U)
    (hf : IsCechCohomologyToSiteCohomologySucc J U family p F f) :
    IsIso f := by
  sorry

/-- Companion API: a positive-degree Čech-to-site comparison map is an isomorphism as soon as
its covering family has acyclic iterated Čech intersections. -/
theorem IsCechCohomologyToSiteCohomologySucc.isIso_of_acyclic_intersections
    {family : ι → Over U} {p : ℕ} {F : Sheaf J AddCommGrpCat.{u}}
    {f : ((cechCohomologyOnSheaves J family (p + 1)).obj F) ⟶ F.H' (p + 1) U}
    (hf : IsCechCohomologyToSiteCohomologySucc J U family p F f)
    (hfamily : (J.over U).CoversTop family)
    (hacyclic : HasAcyclicCechIntersections family F) :
    IsIso f := by
  exact
    cechCohomology_iso_siteCohomology_of_acyclic_intersections
      family hfamily p F hacyclic f hf

omit [HasWeakSheafify J AddCommGrpCat.{u}] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})] in
/-- Canonical instance companion: a positive-degree Čech-to-site comparison map is an isomorphism
once its covering family has acyclic iterated Čech intersections. -/
instance IsCechCohomologyToSiteCohomologySucc.instIsIsoOfAcyclicIntersections
    {family : ι → Over U} {p : ℕ} {F : Sheaf J AddCommGrpCat.{u}}
    {f : ((cechCohomologyOnSheaves J family (p + 1)).obj F) ⟶ F.H' (p + 1) U}
    (hf : IsCechCohomologyToSiteCohomologySucc J U family p F f)
    (hfamily : (J.over U).CoversTop family)
    (hacyclic : HasAcyclicCechIntersections family F) :
    IsIso f :=
  hf.isIso_of_acyclic_intersections hfamily hacyclic

end CategoryTheory
