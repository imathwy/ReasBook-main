import Mathlib.Algebra.Category.Grp.Limits
import StacksProject_2024.Chap20.Lemma_20_4_3
import StacksProject_2024.Chap20.Definition_20_9_1

open CategoryTheory TopologicalSpace
open TopCat.Presheaf

noncomputable section

universe u

namespace CategoryTheory

section

variable {X : TopCat.{u + 1}} {ι : Type u}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 2} (X.Sheaf AddCommGrpCat.{u + 1})]

/- Domain-style sampling for Lemma 20.11.3:
- primary domain: degree-one Čech cohomology for an indexed open cover of `X`, together with the
  torsor interpretation of `H¹(X, ℋ)`;
- sampled owner declarations:
  `TopCat.Presheaf.cechCohomology`,
  `abelianSheafTorsor_isoClasses_to_H1`,
  `Sheaf.Torsor.IsoClasses.IsTrivialOnCover`;
- best owner abstraction:
  `source-facing`: the existence of a degree-one comparison morphism
    `TopCat.Presheaf.cechCohomology U ℋ.presheaf 1 ⟶ H¹(X, ℋ)` attached to an open cover
    `U : ι → Opens X`;
  `core/canonical`: `TopCat.Presheaf.cechCohomology U ℋ.presheaf 1` and the torsor/H¹
    comparison map `abelianSheafTorsor_isoClasses_to_H1 ℋ` on the opens site;
  `bridge/view`: the torsor-triviality predicate `Sheaf.Torsor.IsoClasses.IsTrivialOnCover U`
    together with the canonical image description through
    `abelianSheafTorsor_isoClasses_to_H1 ℋ`.

The target file keeps the source-facing degree-one comparison at the level of a predicate on a
candidate morphism rather than as a new chosen definition. The main entry records that there is a
comparison map with the required injectivity and torsor-image description, and the existing
predicate packages those source-visible properties through the Chapter 20 specialization of the
canonical torsor-to-`H¹` classification. -/
-- Semantic search note: no closer mathlib owner surfaced; the relevant comparison API is the
-- Chapter 21 Čech-to-site comparison machinery specialized to `Opens.grothendieckTopology X`.

/-- A morphism `τ : Čech H¹(U, ℋ) ⟶ H¹(X, ℋ)` is a Čech-to-`H¹` comparison for the family `U` if
it is injective and its image is exactly the classes in `H¹(X, ℋ)` represented by `ℋ`-torsors
that become trivial on `U`, measured through the canonical map
`abelianSheafTorsor_isoClasses_to_H1 ℋ`. -/
@[stacks 0B8R]
def IsCechH1ComparisonToH1OfIsOpenCover
    (U : ι → Opens X) (ℋ : X.Sheaf AddCommGrpCat.{u + 1})
    (τ : cechCohomology U ℋ.presheaf 1 ⟶ AddCommGrpCat.of (ℋ.H 1)) : Prop :=
  Function.Injective τ ∧
    ∀ c : ℋ.H 1, c ∈ Set.range τ ↔
      ∃ P : Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups ℋ),
        P.IsTrivialOnCover U ∧ abelianSheafTorsor_isoClasses_to_H1 ℋ P = c

omit [HasExt.{u + 2} (X.Sheaf AddCommGrpCat.{u + 1})] in
/-- The injectivity part of a Čech-to-`H¹` comparison morphism. -/
theorem IsCechH1ComparisonToH1OfIsOpenCover.injective
    {U : ι → Opens X} {ℋ : X.Sheaf AddCommGrpCat.{u + 1}}
    {τ : cechCohomology U ℋ.presheaf 1 ⟶ AddCommGrpCat.of (ℋ.H 1)}
    (hτ : IsCechH1ComparisonToH1OfIsOpenCover U ℋ τ) :
    Function.Injective τ :=
  hτ.1

omit [HasExt.{u + 2} (X.Sheaf AddCommGrpCat.{u + 1})] in
/-- The image of a Čech-to-`H¹` comparison is exactly the set of classes represented by torsors
trivial on the chosen cover. -/
theorem IsCechH1ComparisonToH1OfIsOpenCover.mem_range_iff
    {U : ι → Opens X} {ℋ : X.Sheaf AddCommGrpCat.{u + 1}}
    {τ : cechCohomology U ℋ.presheaf 1 ⟶ AddCommGrpCat.of (ℋ.H 1)}
    (hτ : IsCechH1ComparisonToH1OfIsOpenCover U ℋ τ) (c : ℋ.H 1) :
    c ∈ Set.range τ ↔
      ∃ P : Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups ℋ),
        P.IsTrivialOnCover U ∧ abelianSheafTorsor_isoClasses_to_H1 ℋ P = c :=
  hτ.2 c

/-- Lemma 20.11.3: if `U : ι → Opens X` is an open covering of `X`, then there exists a unique
comparison map `Čech H¹(U, ℋ) ⟶ H¹(X, ℋ)` whose source-facing specification is the predicate
`IsCechH1ComparisonToH1OfIsOpenCover U ℋ τ`. This records injectivity and the fact that, via the
bijection of Lemma `20.4.3`, the image consists exactly of the isomorphism classes of `ℋ`-torsors
that restrict to trivial torsors on the members of the cover. The companion theorems
`IsCechH1ComparisonToH1OfIsOpenCover.injective` and
`IsCechH1ComparisonToH1OfIsOpenCover.mem_range_iff` expose those two source-style components for
downstream reuse. -/
@[stacks 0B8R]
theorem exists_cech_H1_comparison_to_H1_of_isOpenCover
    (U : ι → Opens X) (hU : IsOpenCover U) (ℋ : X.Sheaf AddCommGrpCat.{u + 1}) :
    ∃! τ : cechCohomology U ℋ.presheaf 1 ⟶ AddCommGrpCat.of (ℋ.H 1),
      IsCechH1ComparisonToH1OfIsOpenCover U ℋ τ := sorry

end

end CategoryTheory
