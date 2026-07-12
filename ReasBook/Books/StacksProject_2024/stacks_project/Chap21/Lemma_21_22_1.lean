import StacksProject_2024.Chap10.«10_69_0_1»
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap20.SiteModuleCohomologyTower

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open scoped DirectSum

noncomputable section

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

local notation "ModSheaf" => Sheaf J (ModuleCat A)

/- Domain-style sampling for Lemma 21.22.1:
- primary domain: site cohomology of sequential inverse systems of sheaves of `A`-modules with
  ideal-power quotients `𝓕_n = 𝓕_{n + 1} / I^n 𝓕_{n + 1}`, together
  with the boundary-image graded module
  `⨁ n, im(H^p(𝒞, 𝓕_n) → H^{p + 1}(𝒞, I^n 𝓕_{n + 1}))`;
- sampled owner declarations:
  * `CategoryTheory.SequentialInverseSystem`;
  * `CategoryTheory.SequentialInverseSystem.IsMittagLeffler`;
  * `CategoryTheory.ShortComplex`;
  * `CategoryTheory.Abelian.Ext.covariantSequence`;
  * `idealAssociatedGradedRing`;
  * `idealAssociatedGradedRingGrade`;
  * `DirectSum.Decomposition`;
  * `SetLike.GradedSMul`;
  * `DirectSum`;
  * `IsNoetherian`;
  * `CategoryTheory.Sheaf.cohomologyFunctor`.
- source/core/bridge triage:
  * `source-facing`: the ideal-power rows
    `0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0` and the graded direct
    sum `⨁ n, im(δ_n)` of the resulting connecting-image pieces;
  * `core/canonical`: `SequentialInverseSystem`, `SequentialInverseSystem.IsMittagLeffler`,
    `ShortComplex`, `ShortComplex.ShortExact.extClass`, `idealAssociatedGradedRing`,
    `idealAssociatedGradedRingGrade`, `DirectSum.Decomposition`, `SetLike.GradedSMul`,
    `DirectSum`, `IsNoetherian`, and `Sheaf.cohomologyFunctor`;
  * `bridge/view`: the underlying-additive cohomology tower `siteModuleCohomologyTower ℱ p`.
- primitive data: the ideal `I`, the module-sheaf tower `ℱ`, the source models
  `idealPowerSheaf n` for `I^n 𝓕_{n + 1}`, and the short exact rows built from the
  canonical transition maps `ℱ.stepMap n`;
- derived API: the cohomology tower `siteModuleCohomologyTower ℱ p`, the connecting-image pieces
  `idealPowerConnectingRange ... p n`, the homogeneous grading
  `idealPowerConnectingGrading ... p n`, and their direct sum `⨁ n, im(δ_n)`.

The main public theorem therefore stays at the source-facing ideal/module-sheaf layer. The
underlying additive cohomology tower is only the canonical bridge used in the conclusion, while
the boundary maps are taken from the canonical `Ext` long exact sequence for
`Sheaf.cohomologyFunctor`.
-/

/-- The forgetful sheaf-composition functor from `A`-module sheaves to additive sheaves preserves
zero morphisms. This lets the ideal-power short exact rows be mapped to additive sheaves without
reintroducing file-local instance plumbing in downstream cohomology arguments. -/
instance sheafCompose_moduleToAdd_preservesZeroMorphisms :
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).PreservesZeroMorphisms where
  map_zero X Y := by
    apply (sheafToPresheaf J AddCommGrpCat.{max u v w}).map_injective
    ext U x
    rfl

/-- The source short exact row
`0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0`. -/
abbrev idealPowerRow
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf)
    (idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1)))
    (idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0) (n : ℕ) :
    ShortComplex ModSheaf :=
  ShortComplex.mk (idealPowerι n) (ℱ.stepMap n) (idealPower_comp_zero n)

/-- The underlying additive-sheaf row of
`0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0`. -/
abbrev idealPowerUnderlyingRow
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf)
    (idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1)))
    (idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0)
    (n : ℕ) :=
  (idealPowerRow ℱ idealPowerSheaf idealPowerι idealPower_comp_zero n).map
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat))

/-- A family `δ_n` of site-cohomology boundary maps is the canonical connecting family for the
ideal-power rows if each `δ_n` is induced by the underlying additive-sheaf short exact row
`0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0`. -/
def IsIdealPowerConnectingFamily
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf)
    (idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1)))
    (idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0)
    (p : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n))) : Prop :=
  ∀ n : ℕ,
    ∃ hshort : (idealPowerUnderlyingRow
      ℱ idealPowerSheaf idealPowerι idealPower_comp_zero n).ShortExact,
      δ n = AddCommGrpCat.ofHom
        (hshort.extClass.postcomp
          ((constantSheaf J AddCommGrpCat.{max u v w}).obj (AddCommGrpCat.of (ULift ℤ))) rfl)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] in
/-- A canonical connecting family carries the short exactness witness for each underlying
ideal-power row. -/
theorem IsIdealPowerConnectingFamily.shortExact
    {ℱ : SequentialInverseSystem ModSheaf} {idealPowerSheaf : ℕ → ModSheaf}
    {idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1))}
    {idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0}
    {p : ℕ}
    {δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n))}
    (hδ : IsIdealPowerConnectingFamily
      ℱ idealPowerSheaf idealPowerι idealPower_comp_zero p δ)
    (n : ℕ) :
    (idealPowerUnderlyingRow
      ℱ idealPowerSheaf idealPowerι idealPower_comp_zero n).ShortExact :=
  Classical.choose (hδ n)

omit [HasWeakSheafify J (ModuleCat.{max u v w} A)] in
/-- A canonical connecting family identifies each `δ_n` with the connecting map of the
corresponding underlying short exact row. -/
theorem IsIdealPowerConnectingFamily.shortExact_spec
    {ℱ : SequentialInverseSystem ModSheaf} {idealPowerSheaf : ℕ → ModSheaf}
    {idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1))}
    {idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0}
    {p : ℕ}
    {δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n))}
    (hδ : IsIdealPowerConnectingFamily
      ℱ idealPowerSheaf idealPowerι idealPower_comp_zero p δ)
    (n : ℕ) :
    δ n = AddCommGrpCat.ofHom
      ((hδ.shortExact n).extClass.postcomp
        ((constantSheaf J AddCommGrpCat.{max u v w}).obj (AddCommGrpCat.of (ULift ℤ))) rfl) :=
  Classical.choose_spec (hδ n)

/-- The degree-`n` cohomology term `H^{p + 1}(𝒞, I^n 𝓕_{n + 1})` attached to the chosen
ideal-power sheaf `idealPowerSheaf n`. -/
abbrev idealPowerCohomologyPiece
    (idealPowerSheaf : ℕ → ModSheaf) (p n : ℕ) : Type (max u v w) :=
  (((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n)) : Type (max u v w))

/-- The source graded module
`⨁ n ≥ 0, H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`. -/
abbrev idealPowerCohomologyDirectSum
    (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ) : Type (max u v w) :=
  ⨁ n : ℕ, idealPowerCohomologyPiece idealPowerSheaf p n

/-- The degree-`n` homogeneous subgroup of
`⨁ n ≥ 0, H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`. -/
abbrev idealPowerCohomologyGrading
    (idealPowerSheaf : ℕ → ModSheaf) (p n : ℕ) :
    AddSubgroup (idealPowerCohomologyDirectSum idealPowerSheaf p) :=
  AddMonoidHom.range
    (DirectSum.of (fun n ↦ idealPowerCohomologyPiece idealPowerSheaf p n) n)

/-- The ambient cohomology direct sum inherits its scalar action from any
`idealAssociatedGradedRing I`-module structure. -/
instance idealPowerCohomologyDirectSum_smul
    (I : Ideal A) (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ)
    [hModule : Module (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p)] :
    SMul (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p) :=
  hModule.toSMul

/-- Source-level compatibility for Lemma 21.22.1: multiplication by a homogeneous element of
`gr_I(A)` acts on the degree-`p` cohomology tower, is compatible with the connecting maps on the
ambient direct sum `⨁ n, H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`, and every degree-`m` correction term dies
after passing to any stage `q ≤ m`.

This packages exactly the multiplication-by-`f` argument used in the Stacks proof, without
replacing it by an abstract module structure on `⨁ n, im(δ_n)` alone. -/
class IsIdealPowerConnectingAction
    (I : Ideal A)
    (ℱ : SequentialInverseSystem ModSheaf)
    (idealPowerSheaf : ℕ → ModSheaf)
    (p : ℕ)
    [SMul (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p)]
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n))) where
  smulCohomology :
    ∀ n m : ℕ,
      idealAssociatedGradedRingGrade I m →
        ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) →
        ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op (n + m))))
  smul_boundary :
    ∀ n m : ℕ, ∀ f : idealAssociatedGradedRingGrade I m,
      ∀ s : ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))),
        DirectSum.of (fun k ↦ idealPowerCohomologyPiece idealPowerSheaf p k) (n + m)
            ((δ (n + m)).hom (smulCohomology n m f s)) =
          (f : idealAssociatedGradedRing I) •
            DirectSum.of (fun k ↦ idealPowerCohomologyPiece idealPowerSheaf p k) n ((δ n).hom s)
  smul_transition_zero :
      ∀ n m q : ℕ, ∀ hq : q ≤ m,
      ∀ f : idealAssociatedGradedRingGrade I m,
      ∀ s : ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))),
        (((siteModuleCohomologyTower ℱ p).transitionMap
          (le_trans hq (Nat.le_add_left m n))).hom
          (smulCohomology n m f s)) = 0

/-- The image subgroup of the canonical connecting morphism
`H^p(𝒞, 𝓕_n) → H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`
attached to the row `0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0`. -/
abbrev idealPowerConnectingRange
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n)))
    (n : ℕ) :
    AddSubgroup (idealPowerCohomologyPiece idealPowerSheaf p n) :=
  AddMonoidHom.range ((δ n).hom)

/-- The graded direct sum `⨁ n, im(δ_n)` of the connecting-image pieces attached to the ideal-power
rows. -/
abbrev idealPowerConnectingDirectSum
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n))) :
    Type (max u v w) :=
  ⨁ n : ℕ,
    idealPowerConnectingRange ℱ idealPowerSheaf p δ n

/-- The degree-`n` homogeneous subgroup of the boundary-image direct sum `⨁ n, im(δ_n)`. -/
abbrev idealPowerConnectingGrading
    (ℱ : SequentialInverseSystem ModSheaf) (idealPowerSheaf : ℕ → ModSheaf) (p : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n)))
    (n : ℕ) :
    AddSubgroup
      (idealPowerConnectingDirectSum ℱ idealPowerSheaf p δ) :=
  AddMonoidHom.range
    (DirectSum.of
      (fun n ↦ idealPowerConnectingRange ℱ idealPowerSheaf p δ n)
      n)

-- Proof sketch: for each `n`, the short exact row
-- `0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0`,
-- modeled here by `idealPowerRow ℱ idealPowerSheaf idealPowerι idealPower_comp_zero n`,
-- let `δ_n` be the connecting morphism in site cohomology produced by the covariant long exact
-- `Ext` sequence defining `Sheaf.cohomologyFunctor J` for the underlying additive-sheaf row:
-- `H^p(𝒞, 𝓕_n) → H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`.
-- Exactness of the cohomology sequence identifies `im(δ_n)` with the obstruction to lifting from
-- `H^p(𝒞, 𝓕_n)` to `H^p(𝒞, 𝓕_{n + 1})`. The source hypothesis, however, is Noetherianity of the
-- full graded direct sum `⨁ n, H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`, formalized by
-- `idealPowerCohomologyDirectSum idealPowerSheaf p`; the boundary-image direct sum
-- `idealPowerConnectingDirectSum ℱ idealPowerSheaf p δ` is only an internal bridge used to pass
-- from that source input to stabilization of the images of the transition maps in
-- `n ↦ H^p(𝒞, 𝓕_n)`, i.e. the Mittag-Leffler condition.

-- Semantic search only surfaced generic graded-module infrastructure, so the source-facing owner
-- below follows the verified Chapter 20 precedent rather than introducing a new canonical package.

/-- Lemma 21.22.1: let `I` be an ideal of `A`, and let `(𝓕_n)_n` be a sequential inverse system
of sheaves of `A`-modules on `(C, J)`. Suppose `idealPowerSheaf n` models `I^n 𝓕_{n + 1}`, with
a short exact row `0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0` whose right map is the canonical
transition morphism `𝓕_{n + 1} → 𝓕_n`.
Assume the source graded module `⨁ n ≥ 0, H^{p + 1}(𝒞, I^n 𝓕_{n + 1})`, formalized by
`idealPowerCohomologyDirectSum idealPowerSheaf p`, carries the graded `gr_I(A)`-module structure
coming from multiplication on ideal powers, formalized by
`SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
  (idealPowerCohomologyGrading idealPowerSheaf p)`, and let `δ_n` be the canonical connecting
maps attached to the rows `0 → I^n 𝓕_{n + 1} → 𝓕_{n + 1} → 𝓕_n → 0`.
Assume moreover that these connecting maps are compatible with multiplication by homogeneous
elements of `gr_I(A)` in the source sense packaged by
`IsIdealPowerConnectingAction I ℱ idealPowerSheaf p δ`,
and is Noetherian over the associated graded ring `⨁ n ≥ 0, I^n / I^{n + 1}`.
Then the canonical site-cohomology tower `n ↦ H^p(𝒞, 𝓕_n)`, formalized by
`siteModuleCohomologyTower ℱ p`, satisfies the Mittag-Leffler condition. -/
@[stacks 0GYQ]
theorem siteModuleCohomologyTower_isMittagLeffler_of_noetherian_associatedGraded
    (I : Ideal A)
    (ℱ : SequentialInverseSystem ModSheaf)
    (idealPowerSheaf : ℕ → ModSheaf)
    (idealPowerι : ∀ n : ℕ, idealPowerSheaf n ⟶ ℱ.obj (op (n + 1)))
    (idealPower_comp_zero : ∀ n : ℕ, idealPowerι n ≫ ℱ.stepMap n = 0)
    (p : ℕ)
    (δ : ∀ n : ℕ, ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op n))) ⟶
      ((siteModuleCohomologyFunctor (p + 1)).obj (idealPowerSheaf n)))
    (hδ : IsIdealPowerConnectingFamily
      ℱ idealPowerSheaf idealPowerι idealPower_comp_zero p δ)
    [Module (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p)]
    [SetLike.GradedSMul (idealAssociatedGradedRingGrade I)
      (idealPowerCohomologyGrading idealPowerSheaf p)]
    [IsIdealPowerConnectingAction I ℱ idealPowerSheaf p δ]
    [IsNoetherian (idealAssociatedGradedRing I)
      (idealPowerCohomologyDirectSum idealPowerSheaf p)] :
    SequentialInverseSystem.IsMittagLeffler (siteModuleCohomologyTower ℱ p) := sorry

end

end CategoryTheory
