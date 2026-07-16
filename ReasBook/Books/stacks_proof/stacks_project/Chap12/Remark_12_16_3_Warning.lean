import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Convex.MetricSpace
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Topology.UniformSpace.Real
import stacks_proof.stacks_project.Chap12.Definition_12_16_1
import stacks_proof.stacks_project.Chap12.Lemma_12_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open TopologicalSpace
open scoped CategoryTheory

universe w v u

namespace CategoryTheory

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory
attribute [local instance] uliftCategory
attribute [local instance] Classical.propDecidable

/-- Helper for Chap12 Remark 12 16 3 Warning: membership of `0` in an open of `ℝ` is decided
classically when forming skyscraper sheaves. -/
noncomputable local instance realZeroMemDecidable :
    ∀ U : Opens (TopCat.of ℝ), Decidable ((0 : ℝ) ∈ U) :=
  Classical.decPred fun U : Opens (TopCat.of ℝ) ↦ (0 : ℝ) ∈ U

/- Domain-style note: this file is a `bridge/view` item in the category-theoretic domain of graded
objects and exact coproducts. The source-facing owner is `GradedObject.total`, and the sampled
core/canonical declarations are `piEquivalenceFunctorDiscrete β C`, `Sigma.isoColimit`,
`HasExactColimitsOfShape`, and functor-category `evaluation`. There is no new primitive data to
package here: the only local bridge is the natural isomorphism identifying
`GradedObject.total` with the colimit functor on `Discrete β ⥤ C`, and the degreewise kernel claim
is then the standard evaluation-functor fact transported back to graded objects. -/

-- Proof sketch: use the standard counterexample cited in the remark, namely the opposite of the
-- category of abelian sheaves on `ℝ`; countable products there are not exact, so after passing to
-- the opposite category countable coproducts are not exact.
/-- Helper for Chap12 Remark 12 16 3 Warning: `CountableAB4 Dᵒᵖ` supplies the specific nat-shaped
exact coproduct instance needed for the opposite-category bridge. -/
private theorem hasExactColimitsOfShapeDiscreteNatOfCountableAB4Op
    (D : Type u) [Category.{v} D] [HasCountableCoproducts Dᵒᵖ] [CountableAB4 Dᵒᵖ] :
    HasExactColimitsOfShape (Discrete ℕ) Dᵒᵖ := by
  -- Proof comment: specialize the `CountableAB4` owner to the concrete countable shape `ℕ`.
  exact CountableAB4.ofShape ℕ

/-- Helper for Chap12 Remark 12 16 3 Warning: countable products in `D` give the opposite-shaped
limit owner needed before transporting exactness across `Discrete.opposite ℕ`. -/
private noncomputable def discreteNatOpFunctorEquiv
    (D : Type u) [Category.{v} D] :
    (Discrete ℕ ⥤ D) ≌ ((Discrete ℕ)ᵒᵖ ⥤ Dᵒᵖ)ᵒᵖ :=
  -- Proof comment: the standard functor-category equivalence already has the right source; taking
  -- its right opposite lands directly in the opposite functor category we need.
  Equivalence.rightOp (Functor.opUnopEquiv (Discrete ℕ) D)

/-- Helper for Chap12 Remark 12 16 3 Warning: the opposite-category transport functor sending an
`ℕ`-indexed diagram in `D` to the unopposite of the colimit of its opposite diagram. -/
private noncomputable abbrev discreteNatOpColimFunctor
    (D : Type u) [Category.{v} D] [HasColimitsOfShape (Discrete ℕ)ᵒᵖ Dᵒᵖ] :
    (Discrete ℕ ⥤ D) ⥤ D :=
  (discreteNatOpFunctorEquiv D).functor ⋙
    (show (((Discrete ℕ)ᵒᵖ ⥤ Dᵒᵖ)ᵒᵖ ⥤ D) from
      (colim : ((Discrete ℕ)ᵒᵖ ⥤ Dᵒᵖ) ⥤ Dᵒᵖ).leftOp)

/-- Helper for Chap12 Remark 12 16 3 Warning: the componentwise opposite-colimit comparison is
natural in the `ℕ`-indexed diagram. -/
private theorem limIsoDiscreteNatViaOpColim_naturality
    (D : Type u) [Category.{v} D] [HasCountableProducts D]
    [HasColimitsOfShape (Discrete ℕ)ᵒᵖ Dᵒᵖ] {F G : Discrete ℕ ⥤ D} (α : F ⟶ G) :
    (discreteNatOpColimFunctor D).map α ≫
        (((limitUnopIsoUnopColimit G.op).symm ≪≫
          HasLimit.isoOfNatIso (Functor.opUnopIso G)).hom) =
      (((limitUnopIsoUnopColimit F.op).symm ≪≫
        HasLimit.isoOfNatIso (Functor.opUnopIso F)).hom) ≫
        (lim : (Discrete ℕ ⥤ D) ⥤ D).map α := by
  -- Proof comment: postcompose with the standard limit projections, so both sides reduce to the
  -- same componentwise formula coming from `colimit.ι_map` and `limMap_π`.
  apply limit.hom_ext
  intro j
  dsimp [discreteNatOpColimFunctor, discreteNatOpFunctorEquiv, Equivalence.rightOp]
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π, Functor.unop_obj, Functor.op_obj,
    Functor.opUnopIso_hom_app, Category.comp_id, limMap_π, HasLimit.isoOfNatIso_hom_π_assoc,
    Category.id_comp]
  have hι :
      (colimit.cocone G.op).ι.app (Opposite.op j) ≫
          (colimit.isColimit G.op).map (colimit.cocone F.op)
            ((Functor.opHom (Discrete ℕ) D).map α.op) =
        ((Functor.opHom (Discrete ℕ) D).map α.op).app (Opposite.op j) ≫
          (colimit.cocone F.op).ι.app (Opposite.op j) :=
    IsColimit.ι_map (colimit.isColimit G.op) (colimit.cocone F.op)
      ((Functor.opHom (Discrete ℕ) D).map α.op) (Opposite.op j)
  have hG :
      (limitUnopIsoUnopColimit G.op).inv ≫ limit.π G.op.unop j =
        (colimit.ι G.op (Opposite.op j)).unop :=
    limitUnopIsoUnopColimit_inv_comp_π G.op j
  have hF :
      (limitUnopIsoUnopColimit F.op).inv ≫ limit.π F.op.unop j =
        (colimit.ι F.op (Opposite.op j)).unop :=
    limitUnopIsoUnopColimit_inv_comp_π F.op j
  have hleft :
      ((colimit.isColimit G.op).map (colimit.cocone F.op)
            ((Functor.opHom (Discrete ℕ) D).map α.op)).unop ≫
          (limitUnopIsoUnopColimit G.op).inv ≫ limit.π G.op.unop j =
        ((colimit.isColimit G.op).map (colimit.cocone F.op)
            ((Functor.opHom (Discrete ℕ) D).map α.op)).unop ≫
          (colimit.ι G.op (Opposite.op j)).unop := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          ((colimit.isColimit G.op).map (colimit.cocone F.op)
              ((Functor.opHom (Discrete ℕ) D).map α.op)).unop ≫ k)
        hG
  have hmid :
      ((colimit.isColimit G.op).map (colimit.cocone F.op)
            ((Functor.opHom (Discrete ℕ) D).map α.op)).unop ≫
          (colimit.ι G.op (Opposite.op j)).unop =
        (colimit.ι F.op (Opposite.op j)).unop ≫ α.app j := by
    simpa [Category.assoc] using congrArg Quiver.Hom.unop hι
  have hright :
      (colimit.ι F.op (Opposite.op j)).unop ≫ α.app j =
        (limitUnopIsoUnopColimit F.op).inv ≫ limit.π F.op.unop j ≫ α.app j := by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ α.app j) hF.symm
  exact hleft.trans (hmid.trans hright)

/-- Helper for Chap12 Remark 12 16 3 Warning: the ordinary `ℕ`-indexed limit functor on `D`
identifies with the left-opposite of the `ℕᵒᵖ`-indexed colimit functor on `Dᵒᵖ` after the
canonical functor-category equivalence. -/
private noncomputable def limIsoDiscreteNatViaOpColim
    (D : Type u) [Category.{v} D] [HasCountableProducts D]
    [HasColimitsOfShape (Discrete ℕ)ᵒᵖ Dᵒᵖ] :
    discreteNatOpColimFunctor D ≅
      (lim : (Discrete ℕ ⥤ D) ⥤ D) := by
  -- Route correction: package the componentwise opposite-colimit comparison as a single
  -- functor-level isomorphism, with the `F.op.unop ≅ F` transport handled once here.
  exact NatIso.ofComponents
    (fun F ↦
      (limitUnopIsoUnopColimit F.op).symm ≪≫
        HasLimit.isoOfNatIso (Functor.opUnopIso F))
    (limIsoDiscreteNatViaOpColim_naturality D)

/-- Helper for Chap12 Remark 12 16 3 Warning: transporting the nat-shaped exact coproduct instance
on `Dᵒᵖ` to the corresponding exact product instance on `D` reduces to the single canonical
functor-category comparison `limIsoDiscreteNatViaOpColim`. -/
private theorem hasExactLimitsOfShapeDiscreteNatOfHasExactColimitsOfShapeDiscreteNatOp
    (D : Type u) [Category.{v} D] [Abelian D] [HasCountableProducts D]
    [HasCountableCoproducts Dᵒᵖ] [CountableAB4 Dᵒᵖ] :
    HasExactLimitsOfShape (Discrete ℕ) D := by
  letI : HasColimitsOfShape (Discrete ℕ)ᵒᵖ Dᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite ℕ).symm
  letI : HasExactColimitsOfShape (Discrete ℕ) Dᵒᵖ :=
    hasExactColimitsOfShapeDiscreteNatOfCountableAB4Op D
  letI : HasExactColimitsOfShape (Discrete ℕ)ᵒᵖ Dᵒᵖ :=
    HasExactColimitsOfShape.of_domain_equivalence Dᵒᵖ (Discrete.opposite ℕ).symm
  letI : PreservesFiniteColimits
      (show (((Discrete ℕ)ᵒᵖ ⥤ Dᵒᵖ)ᵒᵖ ⥤ D) from
        (colim : ((Discrete ℕ)ᵒᵖ ⥤ Dᵒᵖ) ⥤ Dᵒᵖ).leftOp) :=
    Limits.preservesFiniteColimits_leftOp
      (colim : ((Discrete ℕ)ᵒᵖ ⥤ Dᵒᵖ) ⥤ Dᵒᵖ)
  let H : (Discrete ℕ ⥤ D) ⥤ D := discreteNatOpColimFunctor D
  letI : PreservesFiniteColimits H := comp_preservesFiniteColimits _ _
  -- Proof comment: exactness now lives on the canonical opposite colimit functor; the nat-iso
  -- adapter moves that exactness back to the ordinary `lim`.
  exact ⟨preservesFiniteColimits_of_natIso (limIsoDiscreteNatViaOpColim D)⟩

/-- Helper for Chap12 Remark 12 16 3 Warning: exact countable coproducts in `Dᵒᵖ` induce exact
countable products in `D`. -/
private theorem countableAB4StarOfCountableAB4Op
    (D : Type u) [Category.{v} D] [Abelian D] [HasCountableProducts D]
    [HasCountableCoproducts Dᵒᵖ] [CountableAB4 Dᵒᵖ] :
    CountableAB4Star D := by
  letI : HasExactLimitsOfShape (Discrete ℕ) D :=
    hasExactLimitsOfShapeDiscreteNatOfHasExactColimitsOfShapeDiscreteNatOp D
  letI : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  -- Proof comment: once the nat-shaped opposite bridge is available, the standard Grothendieck
  -- axiom constructor upgrades it to exact countable products.
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat D

/-- Helper for Chap12 Remark 12 16 3 Warning: a failure of exact countable products in `D`
forces a failure of exact countable coproducts in `Dᵒᵖ`. -/
private theorem notCountableAB4OpOfNotCountableAB4Star
    (D : Type u) [Category.{v} D] [Abelian D] [HasCountableProducts D]
    [HasCountableCoproducts Dᵒᵖ]
    (hD : ¬ CountableAB4Star D) :
    ¬ CountableAB4 Dᵒᵖ := by
  -- Contrapose the canonical opposite-category transport.
  intro hOp
  let _ : CountableAB4 Dᵒᵖ := hOp
  exact hD (countableAB4StarOfCountableAB4Op D)

/-- Helper for Chap12 Remark 12 16 3 Warning: the standard small-opposite-cover criterion gives
sheafification for abelian-group-valued sheaves on the real line. -/
@[reducible] private def addCommGrpSheafifyReal :
    HasSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} := by
  let K := Opens.grothendieckTopology (TopCat.of ℝ)
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget AddCommGrpCat.{u})
  letI : ∀ V : Opens (TopCat.of ℝ), IsCofiltered (K.Cover V) :=
    fun V ↦ CategoryTheory.isCofiltered_of_directed_ge_nonempty (K.Cover V)
  letI : ∀ V : Opens (TopCat.of ℝ), IsFiltered (K.Cover V)ᵒᵖ :=
    fun V ↦ CategoryTheory.isFiltered_op_of_isCofiltered (K.Cover V)
  letI :
      ∀ V : Opens (TopCat.of ℝ),
        PreservesColimitsOfShape (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{u}) :=
    fun _ ↦ by
      infer_instance
  -- Proof comment: filtered colimits of abelian groups are available on every cover category, so
  -- the generic sheafification constructor from the Chapter 6 route applies verbatim.
  exact
    CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
      K AddCommGrpCat.{u}

/-- Helper for Chap12 Remark 12 16 3 Warning: failure of exact countable products transports
across an equivalence once both sides are abelian and have countable products. -/
private theorem notCountableAB4Star_of_equivalence
    {C : Type u} {D : Type w} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D] (e : C ≌ D)
    (hC : ¬ CountableAB4Star C) :
    ¬ CountableAB4Star D := by
  intro hD
  letI : HasExactLimitsOfShape (Discrete ℕ) D := CountableAB4Star.ofShape ℕ
  letI : HasExactLimitsOfShape (Discrete ℕ) C :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) e.symm
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  -- Proof comment: exactness of the nat-indexed product functor is invariant under equivalence,
  -- so the owner constructor would rebuild `CountableAB4Star C`, contradicting `hC`.
  exact hC (CountableAB4Star.of_hasExactLimitsOfShape_nat C)

private local instance realLineAbelianSheafifyLarge :
    HasSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} :=
  addCommGrpSheafifyReal

/-- Helper for Chap12 Remark 12 16 3 Warning: sheafification on the real-line site induces the
corresponding weak sheafification for `AddCommGrpCat.{u}`. -/
private local instance realLineAbelianWeakSheafifyLarge :
    HasWeakSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} :=
  CategoryTheory.instHasWeakSheafifyOfHasSheafify
    (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u}

/-- Helper for Chap12 Remark 12 16 3 Warning: the real-line site admits sheaf composition for the
forgetful functor on `AddCommGrpCat.{u}`. -/
private local instance realLineAddCommGrpHasSheafComposeLarge :
    (Opens.grothendieckTopology (TopCat.of ℝ)).HasSheafCompose
      (forget AddCommGrpCat.{u}) :=
  CategoryTheory.hasSheafCompose_of_preservesMulticospan
    (Opens.grothendieckTopology (TopCat.of ℝ)) (forget AddCommGrpCat.{u})

/-- Helper for Chap12 Remark 12 16 3 Warning: sheafification on the real-line site is preserved by
the forgetful functor on `AddCommGrpCat.{u}`. -/
private local instance realLineAddCommGrpPreservesSheafificationLarge :
    (Opens.grothendieckTopology (TopCat.of ℝ)).PreservesSheafification
      (forget AddCommGrpCat.{u}) := by
  let K := Opens.grothendieckTopology (TopCat.of ℝ)
  -- Proof comment: use the standard site-level constructor with the real-line topology bound once
  -- as `K`, so the large-universe forgetful functor stays on the canonical owner API.
  exact
    CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfPreservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLimitsOfShapeWalkingMulticospanOfReflectsIsomorphisms
      K

/-- Helper for Chap12 Remark 12 16 3 Warning: on the real-line site, local bijectivity agrees with
the `W`-class for `AddCommGrpCat.{u}`. -/
private local instance realLineAddCommGrpWEqualsLocallyBijectiveLarge :
    (Opens.grothendieckTopology (TopCat.of ℝ)).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  let K := Opens.grothendieckTopology (TopCat.of ℝ)
  -- Proof comment: once the large-universe sheafification and sheaf-compose owners are installed,
  -- the generic comparison between `W` and local bijectivity applies directly on the site `K`.
  exact
    CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeakSheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget
      K

/-- Helper for Chap12 Remark 12 16 3 Warning: the opposite of the real-line abelian sheaf
category has countable coproducts because the sheaf category has countable products. -/
private theorem sheafCategoryReal_hasCountableCoproductsOpposite :
    HasCountableCoproducts.{u} (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))ᵒᵖ := by
  let _ : HasSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} :=
    addCommGrpSheafifyReal
  let D := TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)
  -- Proof comment: sheaf categories inherit countable products from `AddCommGrpCat`, and the
  -- opposite-category owner turns those into countable coproducts.
  letI : HasCountableProducts D := by
    dsimp [D]
    infer_instance
  exact inferInstance

/-- Helper for Chap12 Remark 12 16 3 Warning: the shrinking neighborhood basis at `0` used in the
standard sheaf counterexample. -/
private def realShrinkingOpen (n : ℕ) : Opens (TopCat.of ℝ) :=
  ⟨Metric.ball (0 : ℝ) (((n + 1 : ℕ) : ℝ)⁻¹), Metric.isOpen_ball⟩

/-- Helper for Chap12 Remark 12 16 3 Warning: the origin belongs to every shrinking open. -/
private theorem zero_mem_realShrinkingOpen (n : ℕ) :
    (0 : ℝ) ∈ realShrinkingOpen n := by
  -- Proof comment: each shrinking open is a positive-radius ball around `0`.
  simpa [realShrinkingOpen] using
    (show dist (0 : ℝ) 0 < (((n + 1 : ℕ) : ℝ)⁻¹) by
      simpa [Real.dist_eq] using (show (0 : ℝ) < (((n + 1 : ℕ) : ℝ)⁻¹) by positivity))

/-- Helper for Chap12 Remark 12 16 3 Warning: every open neighborhood of `0` contains a point
outside some sufficiently small shrinking ball around `0`. -/
private theorem realNeighborhoodMissesSomeShrinkingOpen
    (W : Opens (TopCat.of ℝ)) (hW : (0 : ℝ) ∈ W) :
    ∃ n : ℕ, ¬ W ≤ realShrinkingOpen n := by
  -- Proof comment: openness at `0` gives a radius `ε`; taking a much smaller shrinking ball,
  -- the midpoint `ε / 2` still lies in `W` but no longer lies in that shrinking ball.
  obtain ⟨ε, hεpos, hεW⟩ := Metric.isOpen_iff.mp W.2 0 hW
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
  refine ⟨n, ?_⟩
  intro hle
  have hmid_mem : (ε / 2 : ℝ) ∈ W := by
    apply hεW
    have hdist : dist (ε / 2 : ℝ) 0 < ε := by
      rw [Real.dist_eq]
      have hhalf_nonneg : (0 : ℝ) ≤ ε / 2 := by positivity
      have hhalf : (ε / 2 : ℝ) < ε := by linarith
      simpa [abs_of_nonneg hhalf_nonneg] using hhalf
    simpa [dist_comm] using hdist
  have hmid_not_mem : (ε / 2 : ℝ) ∉ realShrinkingOpen n := by
    intro hmid_in
    have hball : dist (ε / 2 : ℝ) 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by
      simpa [realShrinkingOpen] using hmid_in
    have hball' : ε / 2 < 1 / (↑n + 1) := by
      simpa [Real.dist_eq, one_div, abs_of_pos hεpos] using hball
    exact not_lt_of_ge hn.le hball'
  exact hmid_not_mem (hle hmid_mem)

/-- Helper for Chap12 Remark 12 16 3 Warning: exact `ℕ`-indexed products send objectwise
epimorphisms of diagrams to an epimorphism on the induced limit map. -/
private theorem discreteNatLimitMap_epi_of_objectwise_epi
    {C : Type w} [Category.{0} C] [Abelian C] [HasCountableProducts C]
    {F G : Discrete ℕ ⥤ C} (α : F ⟶ G)
    [PreservesFiniteColimits (lim : (Discrete ℕ ⥤ C) ⥤ C)] [∀ j, Epi (α.app j)] :
    Epi ((lim : (Discrete ℕ ⥤ C) ⥤ C).map α) := by
  -- Proof comment: exact limits map short exact sequences to exact sequences, so the generic
  -- abelian-category lemma upgrades that exactness to preservation of epimorphisms.
  let hExact : ∀ S : ShortComplex (Discrete ℕ ⥤ C), S.Exact → (S.map (lim : _)).Exact :=
    fun _ hS ↦ hS.map (lim : (Discrete ℕ ⥤ C) ⥤ C)
  letI : Epi α := NatTrans.epi_of_epi_app α
  letI : (lim : (Discrete ℕ ⥤ C) ⥤ C).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_map_exact (lim : (Discrete ℕ ⥤ C) ⥤ C) hExact
  infer_instance

/-- Helper for Chap12 Remark 12 16 3 Warning: the real open ball `ball 0 r` is preconnected. -/
private theorem realBall_isPreconnected (r : ℝ) :
    _root_.IsPreconnected ((Metric.ball (0 : ℝ) r : Set ℝ)) := by
  -- Proof comment: real balls are convex, hence preconnected by the standard metric-space lemma.
  simpa using (convex_ball (0 : ℝ) r).isPreconnected

/-- Helper for Chap12 Remark 12 16 3 Warning: the origin lies in every positive-radius real ball
centered at `0`. -/
private theorem zero_mem_realBall (r : ℝ) (hr : 0 < r) :
    (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := by
  -- Proof comment: the distance from `0` to itself is `0`, so positivity of the radius is enough.
  simpa [Metric.mem_ball, Real.dist_eq] using hr

/-- Helper for Chap12 Remark 12 16 3 Warning: the origin viewed as a point of a positive-radius
ball around `0`. -/
private def zeroPointInRealBall (r : ℝ) (hr : 0 < r) : Metric.ball (0 : ℝ) r :=
  ⟨0, zero_mem_realBall r hr⟩

/-- Helper for Chap12 Remark 12 16 3 Warning: a continuous `ℤ`-valued section on a real ball that
vanishes outside `realShrinkingOpen n` cannot take the value `1` at `0` unless the whole ball lies
inside `realShrinkingOpen n`. -/
private theorem continuousZeroOutsideBall_forcesShrinkingSubset
    (n : ℕ) {r : ℝ} (hr : 0 < r) {f : Metric.ball (0 : ℝ) r → ℤ}
    (hcont : Continuous f)
    (hzero : ∀ x : Metric.ball (0 : ℝ) r, x.1 ∉ realShrinkingOpen n → f x = 0)
    (hone : f (zeroPointInRealBall r hr) = 1) :
    (⟨Metric.ball (0 : ℝ) r, Metric.isOpen_ball⟩ : Opens (TopCat.of ℝ)) ≤ realShrinkingOpen n := by
  -- Proof comment: continuity to the discrete space `ℤ` forces `f` to be constant on the
  -- preconnected ball, so every point has the same value as the section at `0`.
  intro x hx
  let xBall : Metric.ball (0 : ℝ) r := ⟨x, hx⟩
  letI : PreconnectedSpace (Metric.ball (0 : ℝ) r) :=
    Subtype.preconnectedSpace (realBall_isPreconnected r)
  have hconst : f xBall = f (zeroPointInRealBall r hr) := by
    exact PreconnectedSpace.constant inferInstance hcont
  by_contra hxnot
  have hxzero : f xBall = 0 := hzero xBall hxnot
  have hxone : f xBall = 1 := hconst.trans hone
  exact zero_ne_one (hxzero.symm.trans hxone)

/-- Helper for Chap12 Remark 12 16 3 Warning: the vanishing-outside condition is preserved by
restriction to a smaller open set. -/
private theorem zeroOutsidePred_res
    (n : ℕ) {U V : Opens (TopCat.of ℝ)} (i : U ⟶ V) {f : V → ℤ}
    (hf : ∀ x : V, x.1 ∉ realShrinkingOpen n → f x = 0) :
    ∀ x : U, x.1 ∉ realShrinkingOpen n → f ⟨x.1, leOfHom i x.2⟩ = 0 := by
  -- Proof comment: restriction only changes the proof that a point lies in the open, not the
  -- underlying point of `ℝ`, so the same vanishing hypothesis applies verbatim.
  intro x hx
  exact hf ⟨x.1, leOfHom i x.2⟩ hx

/-- Helper for Chap12 Remark 12 16 3 Warning: if the vanishing-outside condition holds locally near
every point of an open set, then it holds on the whole open set. -/
private theorem zeroOutsidePred_locality
    (n : ℕ) {U : Opens (TopCat.of ℝ)} {f : U → ℤ}
    (hf :
      ∀ x : U, ∃ (V : Opens (TopCat.of ℝ)) (_ : x.1 ∈ V) (i : V ⟶ U),
        ∀ y : V, y.1 ∉ realShrinkingOpen n → f ⟨y.1, leOfHom i y.2⟩ = 0) :
    ∀ x : U, x.1 ∉ realShrinkingOpen n → f x = 0 := by
  -- Proof comment: evaluate the local witness at the original point, viewed inside its chosen
  -- neighborhood, to recover the desired global vanishing statement.
  intro x hx
  rcases hf x with ⟨V, hxV, i, hi⟩
  simpa using hi ⟨x.1, hxV⟩ hx

/-- Helper for Chap12 Remark 12 16 3 Warning: the pointwise condition "a section vanishes outside
`realShrinkingOpen n`" is a genuine local predicate on `ℤ`-valued functions. -/
private def zeroOutsideLocal (n : ℕ) :
    TopCat.LocalPredicate fun _ : TopCat.of ℝ ↦ ℤ :=
  { pred := fun {U} f ↦ ∀ x : U, x.1 ∉ realShrinkingOpen n → f x = 0
    res := fun i _ hf ↦ zeroOutsidePred_res n i hf
    locality := fun _ hf ↦ zeroOutsidePred_locality n hf }

/-- Helper for Chap12 Remark 12 16 3 Warning: continuity together with vanishing outside the
shrinking open defines the ambient local-predicate sheaf used in the counterexample. -/
private def continuousZeroOutsideLocal (n : ℕ) :
    TopCat.LocalPredicate fun _ : TopCat.of ℝ ↦ ℤ :=
  (TopCat.continuousLocal (TopCat.of ℝ) ℤ).and (zeroOutsideLocal n)

/-- Helper for Chap12 Remark 12 16 3 Warning: the zero-outside local predicate is viewed through
its canonical `Type`-valued subsheaf owner. -/
private abbrev continuousZeroOutsideTypeSheaf (n : ℕ) :
    TopCat.Sheaf (Type _) (TopCat.of ℝ) :=
  TopCat.subsheafToTypes (continuousZeroOutsideLocal n)

/-- Helper for Chap12 Remark 12 16 3 Warning: sections of the canonical zero-outside subsheaf over
an open set form an additive subgroup of all `ℤ`-valued functions on that open. -/
private def continuousZeroOutsideAddSubgroup (n : ℕ) (U : Opens (TopCat.of ℝ)) :
    AddSubgroup (U → ℤ) :=
  -- Route correction: use the local-predicate subsheaf as the sole carrier, and package the
  -- pointwise additive structure only as a thin bridge back to `AddSubgroup`.
  { carrier := { f | (continuousZeroOutsideLocal n).pred f }
    zero_mem' := by
      -- The zero section is continuous and vanishes everywhere outside the shrinking open.
      constructor
      · simpa using (continuous_const : Continuous fun _ : U ↦ (0 : ℤ))
      · intro x hx
        rfl
    add_mem' := by
      intro f g hf hg
      rcases hf with ⟨hfcont, hfzero⟩
      rcases hg with ⟨hgcont, hgzero⟩
      constructor
      · -- Continuity is preserved under pointwise addition in the discrete target `ℤ`.
        simpa using hfcont.add hgcont
      · -- Outside the shrinking open, both summands vanish, so their sum does as well.
        intro x hx
        rw [Pi.add_apply, hfzero x hx, hgzero x hx, zero_add]
    neg_mem' := by
      intro f hf
      rcases hf with ⟨hfcont, hfzero⟩
      constructor
      · -- Continuity is preserved under pointwise negation.
        simpa using hfcont.neg
      · -- Negating a zero value keeps the section zero off the shrinking open.
        intro x hx
        rw [Pi.neg_apply, hfzero x hx, neg_zero] }

/-- Helper for Chap12 Remark 12 16 3 Warning: the canonical subtype sections inherit the ambient
pointwise additive-group structure. -/
private noncomputable instance continuousZeroOutsideSubtypeAddCommGroup
    (n : ℕ) (U : (Opens (TopCat.of ℝ))ᵒᵖ) :
    AddCommGroup ((continuousZeroOutsideTypeSheaf n).1.obj U) := by
  -- Proof comment: the subsheaf sections are definitionally the same subtype as the subgroup
  -- carrier above, so we import the additive structure from that subgroup once and for all.
  simpa using
    (show AddCommGroup ((continuousZeroOutsideTypeSheaf n).1.obj (Opposite.op (Opposite.unop U))) from by
      change AddCommGroup ↥(continuousZeroOutsideAddSubgroup n (Opposite.unop U))
      infer_instance)

/-- Helper for Chap12 Remark 12 16 3 Warning: restriction along an inclusion of opens is additive
on zero-outside sections because it acts pointwise. -/
private def continuousZeroOutsideRestriction
    (n : ℕ) {U V : Opens (TopCat.of ℝ)} (i : U ⟶ V) :
    ((continuousZeroOutsideTypeSheaf n).1.obj (Opposite.op V)) →+
      ((continuousZeroOutsideTypeSheaf n).1.obj (Opposite.op U)) where
  toFun := (continuousZeroOutsideTypeSheaf n).1.map i.op
  map_zero' := by
    -- Restricting the zero section stays pointwise zero.
    apply Subtype.ext
    funext x
    change (0 : ℤ) = 0
    rfl
  map_add' := by
    -- Restriction commutes with pointwise addition on the subtype sections.
    intro f g
    apply Subtype.ext
    funext x
    change f.1 ⟨x.1, leOfHom i x.2⟩ + g.1 ⟨x.1, leOfHom i x.2⟩ =
      (f.1 ⟨x.1, leOfHom i x.2⟩ + g.1 ⟨x.1, leOfHom i x.2⟩)
    rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: the `AddCommGrpCat`-valued presheaf of continuous
`ℤ`-valued sections vanishing outside `realShrinkingOpen n`. -/
private noncomputable def continuousZeroOutsidePresheaf (n : ℕ) :
    TopCat.Presheaf AddCommGrpCat (TopCat.of ℝ) :=
  -- Proof comment: wrap the canonical subtype carrier in `AddCommGrpCat.of`, so forgetting back
  -- to `Type` recovers the same local-predicate presheaf without extra transport.
  { obj := fun U ↦ AddCommGrpCat.of ((continuousZeroOutsideTypeSheaf n).1.obj U)
    map := fun i ↦ AddCommGrpCat.ofHom (continuousZeroOutsideRestriction n i.unop)
    map_id := by
      intro U
      ext f
      rfl
    map_comp := by
      intro U V W i j
      ext f
      rfl }

/-- Helper for Chap12 Remark 12 16 3 Warning: forgetting the additive zero-outside presheaf to
types recovers the canonical local-predicate subsheaf objectwise. -/
private noncomputable def continuousZeroOutsideUnderlyingIso (n : ℕ) :
    continuousZeroOutsidePresheaf n ⋙ CategoryTheory.forget AddCommGrpCat ≅
      (continuousZeroOutsideTypeSheaf n).1 :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso (Equiv.refl _))
    (by
      intro U V i
      ext f
      rfl)

/-- Helper for Chap12 Remark 12 16 3 Warning: the additive zero-outside presheaf is already a
sheaf because its underlying presheaf of types is the standard local-predicate subsheaf. -/
private noncomputable def continuousZeroOutsideSheaf (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) :=
  -- Proof comment: the only sheaf check needed is the single forgetful comparison back to the
  -- local-predicate subsheaf of types.
  { obj := continuousZeroOutsidePresheaf n
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)]
      exact TopCat.Presheaf.isSheaf_of_iso (continuousZeroOutsideUnderlyingIso n)
        (continuousZeroOutsideTypeSheaf n).2 }

/-- Helper for Chap12 Remark 12 16 3 Warning: on any open containing `0`, evaluation at `0`
defines an additive morphism from zero-outside sections to `ℤ`. -/
private noncomputable def continuousZeroOutsideEvalAtZero
    (n : ℕ) {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    (continuousZeroOutsidePresheaf n).obj (Opposite.op U) ⟶ AddCommGrpCat.of ℤ :=
  -- Proof comment: evaluation at the support point is additive because all section operations are
  -- pointwise on the canonical subtype carrier.
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ f.1 ⟨0, hU⟩
      map_zero' := by
        change (0 : ℤ) = 0
        rfl
      map_add' := by
        intro f g
        change f.1 ⟨0, hU⟩ + g.1 ⟨0, hU⟩ = (f.1 ⟨0, hU⟩ + g.1 ⟨0, hU⟩)
        rfl }

/-- Helper for Chap12 Remark 12 16 3 Warning: the evaluation maps on neighborhoods of `0`
assemble into a cocone computing the stalk map to `ℤ`. -/
private noncomputable def continuousZeroOutsideStalkToIntCocone (n : ℕ) :
    Cocone (((OpenNhds.inclusion (0 : TopCat.of ℝ)).op) ⋙ (continuousZeroOutsideSheaf n).1) where
  pt := AddCommGrpCat.of ℤ
  ι :=
    { app := fun U ↦ continuousZeroOutsideEvalAtZero n U.unop.2
      naturality := fun U V i ↦ by
        -- Proof comment: restricting a section to a smaller neighborhood does not change its
        -- value at `0`.
        ext f
        rfl }

/-- Helper for Chap12 Remark 12 16 3 Warning: the zero-outside stalk at `0` maps to `ℤ` by
evaluating representatives at the support point. -/
private noncomputable def continuousZeroOutsideStalkToInt (n : ℕ) :
    TopCat.Presheaf.stalk ((continuousZeroOutsideSheaf n).1)
      (0 : TopCat.of ℝ) ⟶
      AddCommGrpCat.of ℤ :=
  colimit.desc _ (continuousZeroOutsideStalkToIntCocone n)

/-- Helper for Chap12 Remark 12 16 3 Warning: the stalk-to-`ℤ` map reads a germ by evaluating the
chosen representative at `0`. -/
@[reassoc (attr := simp)]
private theorem germ_continuousZeroOutsideStalkToInt
    (n : ℕ) {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1)
        U (0 : TopCat.of ℝ) hU ≫
        continuousZeroOutsideStalkToInt n =
      continuousZeroOutsideEvalAtZero n hU := by
  -- Proof comment: this is the defining colimit equation for the cocone above.
  simpa [continuousZeroOutsideStalkToInt] using
    (colimit.ι_desc (continuousZeroOutsideStalkToIntCocone n) (Opposite.op ⟨U, hU⟩))

/-- Helper for Chap12 Remark 12 16 3 Warning: the constant `ℤ`-valued section on the shrinking
ball belongs to the zero-outside local predicate. -/
private theorem continuousZeroOutsideConstantSection_mem (n : ℕ) (z : ℤ) :
    (continuousZeroOutsideLocal n).pred (fun _ : realShrinkingOpen n ↦ z) := by
  -- Proof comment: the constant section is continuous, and the outside-vanishing clause is
  -- vacuous because the shrinking open is its own support.
  constructor
  · simpa using (continuous_const : Continuous fun _ : realShrinkingOpen n ↦ z)
  · intro x hx
    exact (hx x.2).elim

/-- Helper for Chap12 Remark 12 16 3 Warning: the constant section on `realShrinkingOpen n`
provides any prescribed integer value at `0`. -/
private noncomputable def continuousZeroOutsideConstantSection (n : ℕ) (z : ℤ) :
    (continuousZeroOutsidePresheaf n).obj (Opposite.op (realShrinkingOpen n)) :=
  ⟨fun _ ↦ z, continuousZeroOutsideConstantSection_mem n z⟩

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating the constant shrinking-open section at
`0` returns the chosen integer. -/
private theorem continuousZeroOutsideEvalAtZero_constantSection (n : ℕ) (z : ℤ) :
    continuousZeroOutsideEvalAtZero n (zero_mem_realShrinkingOpen n)
        (continuousZeroOutsideConstantSection n z) =
      z := by
  -- Proof comment: the section is pointwise constant by construction.
  rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: every integer is realized by a germ in the
zero-outside stalk at `0`. -/
private theorem continuousZeroOutsideStalkToInt_surjective (n : ℕ) :
    Function.Surjective (continuousZeroOutsideStalkToInt n) := by
  intro z
  refine ⟨TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1)
      (realShrinkingOpen n) (0 : TopCat.of ℝ) (zero_mem_realShrinkingOpen n)
      (continuousZeroOutsideConstantSection n z), ?_⟩
  -- Proof comment: taking the germ of the constant section and then evaluating at `0`
  -- recovers the chosen integer.
  rw [← ConcreteCategory.comp_apply, germ_continuousZeroOutsideStalkToInt]
  exact continuousZeroOutsideEvalAtZero_constantSection n z

/-- Helper for Chap12 Remark 12 16 3 Warning: each zero-outside sheaf maps to the skyscraper sheaf
at `0` by evaluation at the support point. -/
private noncomputable def continuousZeroOutsideToSkyscraper (n : ℕ) :
    continuousZeroOutsideSheaf n ⟶
      skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) :=
  -- Proof comment: delegate the branch-by-branch skyscraper naturality to mathlib's canonical
  -- `toSkyscraperPresheaf` construction and then repackage it as a sheaf morphism.
  ObjectProperty.homMk <|
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf
      (0 : TopCat.of ℝ) (continuousZeroOutsideStalkToInt n)

/-- Helper for Chap12 Remark 12 16 3 Warning: the skyscraper transpose used to define
`continuousZeroOutsideToSkyscraper` recovers the original stalk evaluation map. -/
private theorem continuousZeroOutsideToSkyscraper_fromStalk (n : ℕ) :
    StalkSkyscraperPresheafAdjunctionAuxs.fromStalk
        (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom =
      continuousZeroOutsideStalkToInt n := by
  -- Proof comment: `continuousZeroOutsideToSkyscraper` was defined as the skyscraper transpose of
  -- `continuousZeroOutsideStalkToInt`, so the adjunction counit computes back to that map.
  simpa [continuousZeroOutsideToSkyscraper] using
    (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk_to_skyscraper
      (0 : TopCat.of ℝ) (continuousZeroOutsideStalkToInt n))

/-- Helper for Chap12 Remark 12 16 3 Warning: on the stalk at `0`, the skyscraper comparison map
composed with the standard skyscraper-stalk isomorphism is exactly evaluation to `ℤ`. -/
private theorem continuousZeroOutsideToSkyscraper_stalk_zero_comp_hom (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat (0 : TopCat.of ℝ)).map
        (continuousZeroOutsideToSkyscraper n).hom ≫
      (skyscraperPresheafStalkOfSpecializes
        (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl).hom =
    continuousZeroOutsideStalkToInt n := by
  -- Proof comment: compare both morphisms on every germ into the stalk at `0`; the skyscraper
  -- side reduces to the canonical `fromStalk` computation.
  have hfrom :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat (0 : TopCat.of ℝ)).map
          (continuousZeroOutsideToSkyscraper n).hom ≫
        (skyscraperPresheafStalkOfSpecializes
          (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl).hom =
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk
        (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hU
    calc
      TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1) U
          (0 : TopCat.of ℝ) hU ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat (0 : TopCat.of ℝ)).map
              (continuousZeroOutsideToSkyscraper n).hom ≫
            (skyscraperPresheafStalkOfSpecializes
              (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl).hom =
          (continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U) ≫
            TopCat.Presheaf.germ
              ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1) U
              (0 : TopCat.of ℝ) hU ≫
            (skyscraperPresheafStalkOfSpecializes
              (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl).hom := by
            simpa [Category.assoc] using
              (TopCat.Presheaf.stalkFunctor_map_germ
                U (0 : TopCat.of ℝ) hU (continuousZeroOutsideToSkyscraper n).hom)
      _ = TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1) U
            (0 : TopCat.of ℝ) hU ≫
            StalkSkyscraperPresheafAdjunctionAuxs.fromStalk
              (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom := by
            calc
              (continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U) ≫
                  TopCat.Presheaf.germ
                    ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1) U
                    (0 : TopCat.of ℝ) hU ≫
                  (skyscraperPresheafStalkOfSpecializes
                    (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl).hom =
              (continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U) ≫
                  eqToHom (if_pos hU) := by
                    exact congrArg
                      (fun k ↦ (continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U) ≫ k)
                      (germ_skyscraperPresheafStalkOfSpecializes_hom
                        (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl U hU)
              _ = TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1) U
                    (0 : TopCat.of ℝ) hU ≫
                  StalkSkyscraperPresheafAdjunctionAuxs.fromStalk
                    (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom := by
                    symm
                    exact StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
                      (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom U hU
  have hbase :
      StalkSkyscraperPresheafAdjunctionAuxs.fromStalk
          (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom =
        continuousZeroOutsideStalkToInt n := by
    -- Proof comment: invoke the standalone transpose-computation lemma to avoid replaying the
    -- skyscraper adjunction normalization inside this larger stalk comparison.
    exact continuousZeroOutsideToSkyscraper_fromStalk n
  exact hfrom.trans hbase

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluation at `0` is locally surjective, hence epi,
for the zero-outside sheaf on each shrinking open. -/
private theorem continuousZeroOutsideToSkyscraper_epi (n : ℕ) :
    Epi (continuousZeroOutsideToSkyscraper n) := by
  -- Proof comment: local surjectivity is checked stalkwise; at `0` we use the explicit
  -- evaluation map above, and away from `0` the skyscraper stalk is terminal.
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x
  by_cases hx : x = (0 : TopCat.of ℝ)
  · subst hx
    let e :
        TopCat.Presheaf.stalk
            ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1)
            (0 : TopCat.of ℝ) ≅
          AddCommGrpCat.of ℤ :=
      skyscraperPresheafStalkOfSpecializes
        (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) specializes_rfl
    intro t
    obtain ⟨s, hs : continuousZeroOutsideStalkToInt n s = e.hom t⟩ :=
      continuousZeroOutsideStalkToInt_surjective n (e.hom t)
    refine ⟨s, ?_⟩
    have hcomp := congrArg (fun k ↦ k s) (continuousZeroOutsideToSkyscraper_stalk_zero_comp_hom n)
    have hgoal : e.hom
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat (0 : TopCat.of ℝ)).map
          (continuousZeroOutsideToSkyscraper n).hom) s) =
        e.hom t := by
      rw [← hs]
      simpa [e, ConcreteCategory.comp_apply] using hcomp
    simpa using congrArg e.inv hgoal
  · have hnotSpec : ¬ (0 : TopCat.of ℝ) ⤳ x := by
      simpa [specializes_iff_eq, eq_comm] using hx
    let e :
        TopCat.Presheaf.stalk
            ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1) x ≅
          ⊤_ AddCommGrpCat :=
      skyscraperPresheafStalkOfNotSpecializes
        (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ) hnotSpec
    intro t
    have hsurjTerminal :
        Function.Surjective
          (fun s : (continuousZeroOutsideSheaf n).presheaf.stalk x ↦
            e.hom
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
                (continuousZeroOutsideToSkyscraper n).hom) s)) := by
      have hsub : Subsingleton (⊤_ AddCommGrpCat) :=
        AddCommGrpCat.subsingleton_of_isZero terminalIsTerminal.isZero
      intro y
      refine ⟨0, hsub.elim _ _⟩
    rcases hsurjTerminal (e.hom t) with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have hgoal : e.hom
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (continuousZeroOutsideToSkyscraper n).hom) s) =
        e.hom t := by
      simpa [ConcreteCategory.comp_apply] using hs
    simpa using congrArg e.inv hgoal

/-- Helper for Chap12 Remark 12 16 3 Warning: the shrinking-family diagram of zero-outside source
sheaves indexed by `ℕ`. -/
private noncomputable def continuousZeroOutsideDiagram :
    Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) :=
  Discrete.functor continuousZeroOutsideSheaf

/-- Helper for Chap12 Remark 12 16 3 Warning: the constant `ℕ`-indexed diagram at the skyscraper
sheaf supported at `0`. -/
private noncomputable def realSkyscraperDiagram :
    Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) :=
  Discrete.functor (fun _ : ℕ ↦
    skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ))

/-- Helper for Chap12 Remark 12 16 3 Warning: the componentwise evaluation maps assemble into the
natural transformation used in the countable-product obstruction. -/
private noncomputable def continuousZeroOutsideNatTrans :
    continuousZeroOutsideDiagram ⟶ realSkyscraperDiagram :=
  Discrete.natTrans fun i ↦ by
    simpa [continuousZeroOutsideDiagram, realSkyscraperDiagram] using
      continuousZeroOutsideToSkyscraper i.as

/-- Helper for Chap12 Remark 12 16 3 Warning: every component of the shrinking-family natural
transformation is epi. -/
private instance continuousZeroOutsideNatTrans_epi (j : Discrete ℕ) :
    Epi ((continuousZeroOutsideNatTrans).app j) :=
  by
    simpa [continuousZeroOutsideNatTrans] using continuousZeroOutsideToSkyscraper_epi j.as

/-- Helper for Chap12 Remark 12 16 3 Warning: the sheaf-level universe lift from the small real
sheaf category into the `u`-large one. -/
private noncomputable abbrev realSheafUliftFunctor :
    TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) :=
  @CategoryTheory.sheafCompose _ _ _ _ _ _
    (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.uliftFunctor.{u, 0}
    (CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (TopCat.of ℝ)))

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating a sheaf on a fixed open set gives the
section group functor used to compare limits with coordinate sections. -/
private noncomputable abbrev sheafSectionFunctor (U : Opens (TopCat.of ℝ)) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) ⥤ AddCommGrpCat :=
  TopCat.Sheaf.forget AddCommGrpCat (TopCat.of ℝ) ⋙
    (evaluation (Opens (TopCat.of ℝ))ᵒᵖ AddCommGrpCat).obj (Opposite.op U)

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating a sheaf morphism on sections is just its
component at the chosen open. -/
@[simp] private theorem sheafSectionFunctor_map_apply
    (U : Opens (TopCat.of ℝ)) {F G : TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ)} (φ : F ⟶ G)
    (s : (sheafSectionFunctor U).obj F) :
    (sheafSectionFunctor U).map φ s = φ.hom.app (Opposite.op U) s := rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: the discrete skyscraper diagram evaluated on a fixed
open set. -/
private noncomputable abbrev realSkyscraperSectionDiagram (U : Opens (TopCat.of ℝ)) :
    Discrete ℕ ⥤ AddCommGrpCat :=
  realSkyscraperDiagram ⋙ sheafSectionFunctor U

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating a sheaf on a fixed open preserves the
limit of the discrete skyscraper diagram. -/
private noncomputable instance sheafSectionFunctorPreservesLimitRealSkyscraperDiagram
    (U : Opens (TopCat.of ℝ)) :
    PreservesLimit realSkyscraperDiagram (sheafSectionFunctor U) := by
  -- Proof comment: `Sheaf.forget` creates limits and evaluation preserves them, so the specific
  -- discrete-skyscraper limit needed later is preserved by the section functor.
  let G : TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ) ⥤ TopCat.Presheaf AddCommGrpCat (TopCat.of ℝ) :=
    TopCat.Sheaf.forget AddCommGrpCat (TopCat.of ℝ)
  let H :
      TopCat.Presheaf AddCommGrpCat (TopCat.of ℝ) ⥤ AddCommGrpCat :=
    (evaluation (Opens (TopCat.of ℝ))ᵒᵖ AddCommGrpCat).obj (Opposite.op U)
  change PreservesLimit realSkyscraperDiagram (G ⋙ H)
  letI :
      PreservesLimit realSkyscraperDiagram G :=
    preservesLimit_of_createsLimit_and_hasLimit realSkyscraperDiagram G
  letI : PreservesLimits H := by
    exact CategoryTheory.Limits.evaluationPreservesLimits (Opposite.op U)
  exact CategoryTheory.Limits.comp_preservesLimit G H

/-- Helper for Chap12 Remark 12 16 3 Warning: the section `1 : ℤ` viewed in the skyscraper sheaf
over an open containing `0`. -/
private noncomputable def realSkyscraperSectionOne
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U)) :=
  (ConcreteCategory.hom
    (eqToHom (if_pos hU).symm :
      AddCommGrpCat.of ℤ ⟶
        (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U)))
    (1 : ℤ)

/-- Helper for Chap12 Remark 12 16 3 Warning: on an open neighborhood of `0`, the skyscraper map
coming from the stalk adjunction is just evaluation at `0`. -/
private theorem continuousZeroOutsideToSkyscraper_app_mem
    (n : ℕ) {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U)
    (s : (continuousZeroOutsideSheaf n).1.obj (Opposite.op U)) :
    (ConcreteCategory.hom
        (eqToHom (if_pos hU) :
          (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U) ⟶
            AddCommGrpCat.of ℤ))
        (((continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U)) s) =
      continuousZeroOutsideEvalAtZero n hU s := by
  -- Proof comment: first rewrite the skyscraper comparison map at `U` to the explicit
  -- `germ ≫ continuousZeroOutsideStalkToInt ≫ eqToHom` formula.
  have happ :
      ((continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U)) ≫
          eqToHom (if_pos hU) =
        TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1)
          U (0 : TopCat.of ℝ) hU ≫
          continuousZeroOutsideStalkToInt n := by
    calc
      ((continuousZeroOutsideToSkyscraper n).hom.app (Opposite.op U)) ≫
          eqToHom (if_pos hU) =
        TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1)
          U (0 : TopCat.of ℝ) hU ≫
          StalkSkyscraperPresheafAdjunctionAuxs.fromStalk
            (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom := by
          symm
          exact StalkSkyscraperPresheafAdjunctionAuxs.germ_fromStalk
            (0 : TopCat.of ℝ) (continuousZeroOutsideToSkyscraper n).hom U hU
      _ =
        TopCat.Presheaf.germ ((continuousZeroOutsideSheaf n).1)
          U (0 : TopCat.of ℝ) hU ≫
          continuousZeroOutsideStalkToInt n := by
          rw [continuousZeroOutsideToSkyscraper_fromStalk]
  -- Proof comment: apply both sides to the chosen section, then use the defining germ equation.
  have happ_apply := congrArg (fun k ↦ k s) happ
  have hgerm_apply := congrArg (fun k ↦ k s) (germ_continuousZeroOutsideStalkToInt n hU)
  exact (by simpa [ConcreteCategory.comp_apply, Category.assoc] using happ_apply.trans hgerm_apply)

/-- Helper for Chap12 Remark 12 16 3 Warning: a compatible family in the underlying `Type`-valued
diagram of abelian groups determines a point of the categorical limit. -/
private noncomputable def limitOfUnderlyingSections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)]
    (s : (F ⋙ forget AddCommGrpCat).sections) :
    ↑(limit F) :=
  -- Proof comment: transport the underlying compatible family across the preserved-limit
  -- comparison for `forget AddCommGrpCat`.
  (preservesLimitIso (forget AddCommGrpCat) F).inv
    ((Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s)

/-- Helper for Chap12 Remark 12 16 3 Warning: the limit point built from a compatible underlying
family has the expected coordinate at every index. -/
private theorem limit_π_limitOfUnderlyingSections
    {J : Type*} [Category J] (F : J ⥤ AddCommGrpCat)
    [HasLimit F] [HasLimit (F ⋙ forget AddCommGrpCat)]
    (s : (F ⋙ forget AddCommGrpCat).sections) (j : J) :
    limit.π F j (limitOfUnderlyingSections F s) = s.val j := by
  -- Proof comment: first move to the underlying `Type`-valued limit, then read off the chosen
  -- compatible family through `Types.limitEquivSections`.
  let t : limit (F ⋙ forget AddCommGrpCat) :=
    (Types.limitEquivSections (F ⋙ forget AddCommGrpCat)).symm s
  have hπ :
      limit.π F j ((preservesLimitIso (forget AddCommGrpCat) F).inv t) =
        limit.π (F ⋙ forget AddCommGrpCat) j t := by
    exact congrArg (fun k ↦ k t) (preservesLimitIso_inv_π (forget AddCommGrpCat) F j)
  simpa [limitOfUnderlyingSections, t] using
    hπ.trans (Types.limitEquivSections_symm_apply (F ⋙ forget AddCommGrpCat) s j)

/-- Helper for Chap12 Remark 12 16 3 Warning: restricting the skyscraper section `1 : ℤ` along a
smaller neighborhood of `0` leaves the section unchanged. -/
private theorem realSkyscraperSectionOne_restrict
    {U V : Opens (TopCat.of ℝ)} (i : U ⟶ V) (hV : (0 : ℝ) ∈ V) (hU : (0 : ℝ) ∈ U) :
    TopCat.Presheaf.restrictOpen (realSkyscraperSectionOne hV) U (leOfHom i) =
      realSkyscraperSectionOne hU := by
  -- Proof comment: on opens containing `0`, the skyscraper restriction map is the positive
  -- `eqToHom` branch, so after unfolding once the remaining transports act trivially on `1 : ℤ`.
  change
    (ConcreteCategory.hom
      ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.map i.op))
      ((ConcreteCategory.hom
        (eqToHom (if_pos hV).symm :
          AddCommGrpCat.of ℤ ⟶
            (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op V))) 1) =
      (ConcreteCategory.hom
        (eqToHom (if_pos hU).symm :
          AddCommGrpCat.of ℤ ⟶
            (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U))) 1
  have hVU :
      (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op V) =
        (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U) := by
    simp [skyscraperSheaf, hU, hV]
  have hmap :
      ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.map i.op) =
        eqToHom hVU := by
    simpa [hVU, skyscraperSheaf, hU, hV] using
      (skyscraperPresheaf_map (p₀ := (0 : TopCat.of ℝ)) (A := AddCommGrpCat.of ℤ) i.op)
  have hmor :
      (eqToHom (if_pos hV).symm :
          AddCommGrpCat.of ℤ ⟶
            (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op V)) ≫
        ((skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.map i.op) =
      (eqToHom (if_pos hU).symm :
        AddCommGrpCat.of ℤ ⟶
          (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U)) := by
    rw [hmap]
    simpa [hVU] using
      (rfl :
        (eqToHom (if_pos hV).symm :
            AddCommGrpCat.of ℤ ⟶
              (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj
                (Opposite.op V)) ≫
          eqToHom hVU =
        (eqToHom (if_pos hV).symm :
            AddCommGrpCat.of ℤ ⟶
              (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj
                (Opposite.op V)) ≫
          eqToHom hVU)
  exact
    congrArg
      (fun k :
        AddCommGrpCat.of ℤ ⟶
          (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op U) ↦
        k (1 : ℤ))
      hmor

/-- Helper for Chap12 Remark 12 16 3 Warning: the constant family with value `1 : ℤ` is a
compatible section of the discrete skyscraper diagram evaluated on any neighborhood of `0`. -/
private theorem realSkyscraperConstantOneSections_property
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) {i j : Discrete ℕ} (f : i ⟶ j) :
    ((realSkyscraperSectionDiagram U) ⋙ forget AddCommGrpCat).map f
        (realSkyscraperSectionOne hU) =
      realSkyscraperSectionOne hU := by
  -- Proof comment: every morphism in `Discrete ℕ` is an identity, so the constant family is
  -- automatically compatible.
  cases i with
  | mk i =>
      cases j with
      | mk j =>
          obtain rfl : i = j := Discrete.eq_of_hom f
          obtain rfl : f = 𝟙 _ := rfl
          simp

/-- Helper for Chap12 Remark 12 16 3 Warning: the constant family with value `1 : ℤ` is a
compatible section of the top-evaluated discrete skyscraper diagram. -/
private theorem realSkyscraperTopConstantOneSections_property
    {i j : Discrete ℕ} (f : i ⟶ j) :
    ((realSkyscraperDiagram ⋙ sheafSectionFunctor ⊤) ⋙ forget AddCommGrpCat).map f
        (realSkyscraperSectionOne
          (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ)))) =
      realSkyscraperSectionOne
        (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ))) := by
  -- Proof comment: this is the top-open specialization of the neighborhood-wise constant-family
  -- compatibility lemma.
  simpa using realSkyscraperConstantOneSections_property
    (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ))) f

/-- Helper for Chap12 Remark 12 16 3 Warning: the compatible family whose every coordinate is
`1 : ℤ` in the `U`-evaluated real skyscraper diagram. -/
private noncomputable def realSkyscraperConstantOneSections
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    ((realSkyscraperSectionDiagram U) ⋙ forget AddCommGrpCat).sections :=
  { val := fun _ ↦ realSkyscraperSectionOne hU
    property := fun {_i _j} f ↦ realSkyscraperConstantOneSections_property hU f }

/-- Helper for Chap12 Remark 12 16 3 Warning: the compatible family whose every coordinate is
`1 : ℤ` in the top-evaluated real skyscraper diagram. -/
private noncomputable def realSkyscraperTopConstantOneSections :
    ((realSkyscraperDiagram ⋙ sheafSectionFunctor ⊤) ⋙ forget AddCommGrpCat).sections :=
  realSkyscraperConstantOneSections
    (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ)))

/-- Helper for Chap12 Remark 12 16 3 Warning: over any neighborhood of `0`, the evaluated limit of
the discrete skyscraper diagram has a canonical section whose every coordinate is `1 : ℤ`. -/
private noncomputable def realSkyscraperLimitSectionOne
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    ((sheafSectionFunctor U).obj (limit realSkyscraperDiagram)) :=
  -- Route correction: build the target section directly on each neighborhood of `0`, so later
  -- restriction arguments only compare coordinates and never transport whole top sections.
  (preservesLimitIso (sheafSectionFunctor U) realSkyscraperDiagram).inv
    (limitOfUnderlyingSections (realSkyscraperSectionDiagram U)
      (realSkyscraperConstantOneSections hU))

/-- Helper for Chap12 Remark 12 16 3 Warning: the top section of the limit of the real skyscraper
diagram whose every coordinate is `1 : ℤ`. -/
private noncomputable def realSkyscraperLimitTopConstantOne :
    ((sheafSectionFunctor ⊤).obj (limit realSkyscraperDiagram)) :=
  realSkyscraperLimitSectionOne
    (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ)))

/-- Helper for Chap12 Remark 12 16 3 Warning: every coordinate of the neighborhood-wise limit
section `realSkyscraperLimitSectionOne` is the constant skyscraper section `1 : ℤ`. -/
private theorem realSkyscraperLimitSectionOne_proj
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) (j : Discrete ℕ) :
    ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op U))
        (realSkyscraperLimitSectionOne hU) =
      realSkyscraperSectionOne hU := by
  -- Proof comment: apply the projection formula for `preservesLimitIso`, then read off the chosen
  -- compatible underlying family at coordinate `j`.
  have hπ :
      ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op U))
          (realSkyscraperLimitSectionOne hU) =
        limit.π (realSkyscraperSectionDiagram U) j
          (limitOfUnderlyingSections (realSkyscraperSectionDiagram U)
            (realSkyscraperConstantOneSections hU)) := by
    simpa [realSkyscraperLimitSectionOne, realSkyscraperSectionDiagram] using
      congrArg
        (fun k ↦
          k (limitOfUnderlyingSections (realSkyscraperSectionDiagram U)
            (realSkyscraperConstantOneSections hU)))
        (preservesLimitIso_inv_π (sheafSectionFunctor U) realSkyscraperDiagram j)
  exact hπ.trans <| by
    simpa using
    (limit_π_limitOfUnderlyingSections
      (realSkyscraperSectionDiagram U)
      (realSkyscraperConstantOneSections hU) j)

/-- Helper for Chap12 Remark 12 16 3 Warning: every coordinate of the top limit section
`realSkyscraperLimitTopConstantOne` is `1 : ℤ`. -/
private theorem realSkyscraperLimitTopConstantOne_proj (j : Discrete ℕ) :
    ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op ⊤))
        realSkyscraperLimitTopConstantOne =
      realSkyscraperSectionOne
        (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ))) := by
  -- Proof comment: this is the top-open specialization of the neighborhood-wise projection
  -- formula.
  simpa [realSkyscraperLimitTopConstantOne] using
    realSkyscraperLimitSectionOne_proj
      (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ))) j

/-- Helper for Chap12 Remark 12 16 3 Warning: after restricting a neighborhood-wise limit section
to a smaller neighborhood of `0`, each skyscraper coordinate is still the constant section
`1 : ℤ`. -/
private theorem realSkyscraperLimitSectionOne_restrict_proj
    {U V : Opens (TopCat.of ℝ)} (i : V ⟶ U) (hU : (0 : ℝ) ∈ U) (hV : (0 : ℝ) ∈ V)
    (j : Discrete ℕ) :
    ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op V))
        (TopCat.Presheaf.restrictOpen (realSkyscraperLimitSectionOne hU) V (leOfHom i)) =
      realSkyscraperSectionOne hV := by
  -- Proof comment: project after restricting, rewrite the unrestricted coordinate by the
  -- canonical constant-one formula, and then simplify the remaining skyscraper restriction.
  have hrestrict :
      ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op V))
          (TopCat.Presheaf.restrictOpen (realSkyscraperLimitSectionOne hU) V (leOfHom i)) =
        TopCat.Presheaf.restrictOpen
          (((limit.π realSkyscraperDiagram j).hom.app (Opposite.op U))
            (realSkyscraperLimitSectionOne hU))
          V (leOfHom i) := by
    simpa using
      (TopCat.Presheaf.map_restrict ((limit.π realSkyscraperDiagram j).hom)
        (leOfHom i) (realSkyscraperLimitSectionOne hU))
  have hproj_restrict :
      TopCat.Presheaf.restrictOpen
          (((limit.π realSkyscraperDiagram j).hom.app (Opposite.op U))
            (realSkyscraperLimitSectionOne hU))
          V (leOfHom i) =
        TopCat.Presheaf.restrictOpen (realSkyscraperSectionOne hU) V (leOfHom i) := by
    exact congrArg (fun s ↦ TopCat.Presheaf.restrictOpen s V (leOfHom i))
      (realSkyscraperLimitSectionOne_proj hU j)
  calc
    ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op V))
        (TopCat.Presheaf.restrictOpen (realSkyscraperLimitSectionOne hU) V (leOfHom i)) =
      TopCat.Presheaf.restrictOpen
        (((limit.π realSkyscraperDiagram j).hom.app (Opposite.op U))
          (realSkyscraperLimitSectionOne hU))
        V (leOfHom i) := hrestrict
    _ =
      TopCat.Presheaf.restrictOpen (realSkyscraperSectionOne hU) V (leOfHom i) := by
      exact hproj_restrict
    _ = realSkyscraperSectionOne hV := by
      simpa using realSkyscraperSectionOne_restrict i hU hV

/-- Helper for Chap12 Remark 12 16 3 Warning: after restricting the top constant-one limit section
to any open containing `0`, every skyscraper coordinate is still `1 : ℤ`. -/
private theorem realSkyscraperLimitTopConstantOne_restrict_proj
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) (j : Discrete ℕ) :
    ((limit.π realSkyscraperDiagram j).hom.app (Opposite.op U))
        (TopCat.Presheaf.restrictOpen realSkyscraperLimitTopConstantOne U
          (show U ≤ ⊤ by simp)) =
      realSkyscraperSectionOne hU := by
  -- Proof comment: this is the top-open specialization of the neighborhood-wise restriction
  -- projection formula.
  simpa [realSkyscraperLimitTopConstantOne] using
    realSkyscraperLimitSectionOne_restrict_proj
      (homOfLE (show U ≤ ⊤ by
        intro x hx
        simp))
      (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ))) hU j

/-- Helper for Chap12 Remark 12 16 3 Warning: `realSheafUliftFunctor` preserves local
surjectivity by lifting every local preimage section with `ULift.up`. -/
private theorem realSheafUliftFunctor_obj_map_app
    (F : TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ))
    {U V : Opens (TopCat.of ℝ)} (i : U ⟶ V)
    (s : F.1.obj (Opposite.op V)) :
    ((realSheafUliftFunctor.obj F).1.map i.op) (ULift.up s) =
      ULift.up (F.1.map i.op s) := by
  -- Proof comment: the sheaf-level universe lift is defined by whiskering with
  -- `AddCommGrpCat.uliftFunctor`, so on sections every restriction map is just `ULift.up`.
  rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: the lifted map on sections is sectionwise
`ULift.up` of the original map. -/
private theorem realSheafUliftFunctor_map_app
    {F G : TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ)} (φ : F ⟶ G)
    {U : Opens (TopCat.of ℝ)} (s : F.1.obj (Opposite.op U)) :
    ((realSheafUliftFunctor.map φ).hom.app (Opposite.op U)) (ULift.up s) =
      ULift.up (φ.hom.app (Opposite.op U) s) := by
  -- Proof comment: after unfolding the whiskered sheaf map, the component function is the
  -- universe-lifted additive hom on sections.
  rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: on the real-line site, local surjectivity for
large additive presheaves is equivalent to sectionwise local solvability on neighborhoods. -/
private theorem realPresheaf_isLocallySurjective_iff
    {ℱ 𝒢 : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of ℝ)} (T : ℱ ⟶ 𝒢) :
    CategoryTheory.Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (TopCat.of ℝ)) T ↔
      ∀ (U : Opens (TopCat.of ℝ)) (t : 𝒢.obj (Opposite.op U)),
        ∀ x ∈ U, ∃ (V : Opens (TopCat.of ℝ)) (hVU : V ≤ U),
          (∃ s : ℱ.obj (Opposite.op V),
            (T.app (Opposite.op V)) s = TopCat.Presheaf.restrictOpen t V hVU) ∧ x ∈ V :=
by
  -- Route correction: copy the topological-site proof directly, because the small-universe helper
  -- `TopCat.Presheaf.isLocallySurjective_iff` is specialized to coefficient categories with
  -- `Category.{0}` homs and therefore does not apply to `AddCommGrpCat.{u}`.
  refine ⟨fun h _ t x hx ↦ ?_, fun h => ⟨fun s x hx ↦ ?_⟩⟩
  · obtain ⟨V, i, hi⟩ := h.imageSieve_mem t x hx
    exact ⟨V, leOfHom i, hi⟩
  · obtain ⟨V, Vle, hV⟩ := h _ s x hx
    exact ⟨V, homOfLE Vle, hV⟩

/-- Helper for Chap12 Remark 12 16 3 Warning: local surjectivity of a sheaf morphism survives the
sectionwise universe lift. -/
private theorem realSheafUliftFunctor_map_isLocallySurjective
    {F G : TopCat.Sheaf AddCommGrpCat (TopCat.of ℝ)} {φ : F ⟶ G}
    (hφ : TopCat.Presheaf.IsLocallySurjective (C := AddCommGrpCat) (X := TopCat.of ℝ) φ.hom) :
    CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (TopCat.of ℝ)) (realSheafUliftFunctor.map φ).hom :=
by
  -- Route correction: rewrite both local-surjectivity predicates with the neighborhood-wise
  -- criterion, then lift each small witness sectionwise through `ULift.up`.
  rw [TopCat.Presheaf.isLocallySurjective_iff
    (C := AddCommGrpCat) (X := TopCat.of ℝ)] at hφ
  rw [realPresheaf_isLocallySurjective_iff]
  intro U t x hx
  rcases hφ U (ULift.down t) x hx with ⟨V, hVU, ⟨s, hs⟩, hxV⟩
  refine ⟨V, hVU, ⟨ULift.up s, ?_⟩, hxV⟩
  -- Proof comment: the lifted map and lifted restriction are both computed by `ULift.up` on the
  -- underlying small sections, so the original local equation transports directly.
  have hrestrict :
      TopCat.Presheaf.restrictOpen t V hVU =
        ULift.up (TopCat.Presheaf.restrictOpen (ULift.down t) V hVU) := by
    simpa [TopCat.Presheaf.restrictOpen, ULift.up_down] using
      (realSheafUliftFunctor_obj_map_app G (homOfLE hVU) (ULift.down t))
  have hmap :
      ((realSheafUliftFunctor.map φ).hom.app (Opposite.op V)) (ULift.up s) =
        ULift.up ((φ.hom.app (Opposite.op V)) s) := by
    rw [realSheafUliftFunctor_map_app]
  have hmid :
      ULift.up ((φ.hom.app (Opposite.op V)) s) =
        ULift.up (TopCat.Presheaf.restrictOpen (ULift.down t) V hVU) := by
    simpa [hs]
  exact hmap.trans (hmid.trans hrestrict.symm)

/-- Helper for Chap12 Remark 12 16 3 Warning: every component of the universe-lifted
`continuousZeroOutsideNatTrans` remains locally surjective. -/
private theorem continuousZeroOutsideNatTransUliftApp_locallySurjective (j : Discrete ℕ) :
    CategoryTheory.Sheaf.IsLocallySurjective
      (J := Opens.grothendieckTopology (TopCat.of ℝ))
      (A := AddCommGrpCat.{u})
      ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j) :=
by
  -- Route correction: convert the small sheaf component epi to sheaf local surjectivity once, then
  -- transport that sectionwise local-surjectivity data through `realSheafUliftFunctor`.
  have hSmall :
      CategoryTheory.Sheaf.IsLocallySurjective
        (J := Opens.grothendieckTopology (TopCat.of ℝ))
        (A := AddCommGrpCat)
        ((continuousZeroOutsideNatTrans).app j) :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      (J := Opens.grothendieckTopology (TopCat.of ℝ))
      (A := AddCommGrpCat)
      ((continuousZeroOutsideNatTrans).app j)).2 (continuousZeroOutsideNatTrans_epi j)
  exact realSheafUliftFunctor_map_isLocallySurjective (φ := (continuousZeroOutsideNatTrans).app j)
    (show TopCat.Presheaf.IsLocallySurjective (C := AddCommGrpCat) (X := TopCat.of ℝ)
      ((continuousZeroOutsideNatTrans).app j).hom from hSmall)

/-- Helper for Chap12 Remark 12 16 3 Warning: exact `ℕ`-indexed products in the large real sheaf
category send objectwise epimorphisms of diagrams to an epimorphism on the induced limit map. -/
private theorem discreteNatLargeRealSheafLimitMap_epi_of_objectwise_epi
    {F G : Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)} (α : F ⟶ G)
    [HasCountableProducts (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))]
    [PreservesFiniteColimits
      (lim : (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _)]
    [∀ j, Epi (α.app j)] :
    Epi
      ((lim :
        (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _).map α) := by
  -- Proof comment: exact limits map short exact sequences to exact sequences, so the generic
  -- abelian-category lemma upgrades that exactness to preservation of epimorphisms.
  let hExact :
      ∀ S : ShortComplex (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)),
        S.Exact →
          ((S.map
              (lim :
                (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _)).Exact) :=
    fun _ hS ↦
      hS.map
        (lim :
          (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _)
  letI : Epi α := NatTrans.epi_of_epi_app α
  letI :
      (lim :
        (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_map_exact
      (lim :
        (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _)
      hExact
  infer_instance

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating a large real sheaf on a fixed open set
gives the section group functor used for the lifted contradiction. -/
private noncomputable abbrev sheafSectionFunctorLarge (U : Opens (TopCat.of ℝ)) :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) ⥤ AddCommGrpCat.{u} :=
  show TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) ⥤ AddCommGrpCat.{u} from
    TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of ℝ) ⋙
      (evaluation (Opens (TopCat.of ℝ))ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating a large sheaf morphism on sections is
just its component at the chosen open. -/
@[simp] private theorem sheafSectionFunctorLarge_map_apply
    (U : Opens (TopCat.of ℝ))
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)} (φ : F ⟶ G)
    (s : (sheafSectionFunctorLarge U).obj F) :
    (sheafSectionFunctorLarge U).map φ s = φ.hom.app (Opposite.op U) s := rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: the lifted discrete skyscraper diagram evaluated on a
fixed open set. -/
private noncomputable abbrev realSkyscraperUliftSectionDiagram (U : Opens (TopCat.of ℝ)) :
    Discrete ℕ ⥤ AddCommGrpCat.{u} :=
  (realSkyscraperDiagram ⋙ realSheafUliftFunctor) ⋙ sheafSectionFunctorLarge U

/-- Helper for Chap12 Remark 12 16 3 Warning: the lifted limit sheaf of the shrinking-family
diagram. -/
private noncomputable abbrev continuousZeroOutsideUliftLimitSheaf :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) :=
  limit (continuousZeroOutsideDiagram ⋙ realSheafUliftFunctor)

/-- Helper for Chap12 Remark 12 16 3 Warning: the lifted limit sheaf of the constant skyscraper
diagram. -/
private noncomputable abbrev realSkyscraperUliftLimitSheaf :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) :=
  limit (realSkyscraperDiagram ⋙ realSheafUliftFunctor)

/-- Helper for Chap12 Remark 12 16 3 Warning: the induced map from the lifted zero-outside limit
sheaf to the lifted skyscraper limit sheaf. -/
private noncomputable abbrev continuousZeroOutsideUliftLimitMap :
    continuousZeroOutsideUliftLimitSheaf ⟶ realSkyscraperUliftLimitSheaf :=
  (lim : (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _).map
    (Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor)

/-- Helper for Chap12 Remark 12 16 3 Warning: exact countable products in the large real sheaf
category make the raw lifted `continuousZeroOutside` limit map an epimorphism. -/
private theorem continuousZeroOutsideUliftLimitMapRaw_epi
    [CountableAB4Star (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))] :
    Epi
      ((lim : (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _).map
        (Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor)) := by
  -- Route correction: keep the argument at the sheaf-morphism `Epi` level until the final
  -- conversion to local surjectivity, so the exact-product bridge only sees canonical owners.
  letI : HasCountableProducts (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) := inferInstance
  letI : HasExactLimitsOfShape (Discrete ℕ) (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) :=
    CountableAB4Star.ofShape ℕ
  letI :
      PreservesFiniteColimits
        (lim : (Discrete ℕ ⥤ TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) ⥤ _) :=
    inferInstance
  letI :
      ∀ j,
        Epi ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j) :=
    fun j ↦ by
      let _ :
          CategoryTheory.Sheaf.IsLocallySurjective
            (J := Opens.grothendieckTopology (TopCat.of ℝ))
            (A := AddCommGrpCat.{u})
            ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j) :=
        continuousZeroOutsideNatTransUliftApp_locallySurjective j
      exact CategoryTheory.Sheaf.epi_of_isLocallySurjective
        ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j)
  exact
    discreteNatLargeRealSheafLimitMap_epi_of_objectwise_epi
      (Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor)

/-- Helper for Chap12 Remark 12 16 3 Warning: on the real-line site, an epimorphic additive-sheaf
map is locally surjective on the underlying presheaf. -/
private theorem largeRealAdditiveSheaf_isLocallySurjective_of_epi
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)} (φ : F ⟶ G) (hφ : Epi φ) :
    CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (TopCat.of ℝ)) φ.hom :=
by
  -- Route correction: the generic site-level sheaf API already identifies epimorphisms with local
  -- surjectivity, and that predicate is definitionally the underlying presheaf statement.
  exact
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      (J := Opens.grothendieckTopology (TopCat.of ℝ))
      (A := AddCommGrpCat.{u})
      φ).2 hφ

/-- Helper for Chap12 Remark 12 16 3 Warning: exact countable products in the large real sheaf
category make the lifted `continuousZeroOutside` limit map locally surjective. -/
private theorem continuousZeroOutsideUliftLimitMap_locallySurjective
    (hAB4Star : CountableAB4Star (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))) :
    CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (TopCat.of ℝ)) continuousZeroOutsideUliftLimitMap.hom :=
by
  -- Proof comment: first obtain the lifted limit-map epi from exact countable products, then
  -- convert that epi to local surjectivity using the generic sheaf-site bridge above.
  let _ : CountableAB4Star (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) := hAB4Star
  have hEpi : Epi continuousZeroOutsideUliftLimitMap := by
    -- Proof comment: unfold the named lifted limit map once so the previously proved raw epi
    -- theorem matches the same morphism syntactically.
    dsimp [continuousZeroOutsideUliftLimitMap]
    exact continuousZeroOutsideUliftLimitMapRaw_epi
  exact
    largeRealAdditiveSheaf_isLocallySurjective_of_epi
      continuousZeroOutsideUliftLimitMap hEpi

/-- Helper for Chap12 Remark 12 16 3 Warning: evaluating the lifted skyscraper diagram on a fixed
open preserves its limit. -/
private noncomputable instance sheafSectionFunctorLargePreservesLimitRealSkyscraperDiagram
    (U : Opens (TopCat.of ℝ)) :
    PreservesLimit (realSkyscraperDiagram ⋙ realSheafUliftFunctor)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of ℝ) ⋙
        (evaluation (Opens (TopCat.of ℝ))ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)) := by
  -- Route correction: pin the large-universe forget and evaluation functors explicitly, so Lean
  -- keeps the proof in `AddCommGrpCat.{u}` instead of collapsing back to the small universe.
  let G :
      TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) ⥤
        TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of ℝ) :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of ℝ)
  let H :
      TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of ℝ) ⥤ AddCommGrpCat.{u} :=
    (evaluation (Opens (TopCat.of ℝ))ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U)
  change PreservesLimit (realSkyscraperDiagram ⋙ realSheafUliftFunctor) (G ⋙ H)
  letI :
      PreservesLimit (realSkyscraperDiagram ⋙ realSheafUliftFunctor) G :=
    preservesLimit_of_createsLimit_and_hasLimit (realSkyscraperDiagram ⋙ realSheafUliftFunctor) G
  letI : PreservesLimitsOfShape (Discrete ℕ) H := by
    change
      PreservesLimitsOfShape (Discrete ℕ)
        ((evaluation (Opens (TopCat.of ℝ))ᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op U))
    infer_instance
  letI : PreservesLimit ((realSkyscraperDiagram ⋙ realSheafUliftFunctor) ⋙ G) H :=
    PreservesLimitsOfShape.preservesLimit
  exact CategoryTheory.Limits.comp_preservesLimit G H

/-- Helper for Chap12 Remark 12 16 3 Warning: the lifted skyscraper section `1 : ℤ` over an open
containing `0`. -/
private noncomputable def realSkyscraperUliftSectionOne
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    (((realSheafUliftFunctor.obj
        (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ))).1).obj (Opposite.op U)) :=
  ULift.up (realSkyscraperSectionOne hU)

/-- Helper for Chap12 Remark 12 16 3 Warning: the lifted skyscraper section `1 : ℤ` restricts to
the same lifted section on smaller neighborhoods of `0`. -/
private theorem realSkyscraperUliftSectionOne_restrict
    {U V : Opens (TopCat.of ℝ)} (i : U ⟶ V) (hV : (0 : ℝ) ∈ V) (hU : (0 : ℝ) ∈ U) :
    TopCat.Presheaf.restrictOpen
        (realSkyscraperUliftSectionOne hV)
        U (leOfHom i) =
      realSkyscraperUliftSectionOne hU := by
  -- Proof comment: restriction in the lifted sheaf is still computed sectionwise, so the small
  -- skyscraper restriction formula lifts directly through `ULift.up`.
  change
      ((realSheafUliftFunctor.obj
          (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ))).1.map i.op)
          (ULift.up (realSkyscraperSectionOne hV)) =
        ULift.up (realSkyscraperSectionOne hU)
  rw [realSheafUliftFunctor_obj_map_app]
  exact congrArg ULift.up (realSkyscraperSectionOne_restrict i hV hU)

/-- Helper for Chap12 Remark 12 16 3 Warning: the constant family with value the lifted skyscraper
section `1 : ℤ` is compatible on every neighborhood of `0`. -/
private theorem realSkyscraperUliftConstantOneSections_property
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) {i j : Discrete ℕ} (f : i ⟶ j) :
    (((realSkyscraperUliftSectionDiagram U) ⋙
        forget AddCommGrpCat.{u}).map f)
        (realSkyscraperUliftSectionOne hU) =
      realSkyscraperUliftSectionOne hU := by
  -- Proof comment: the lifted skyscraper diagram is still discrete, so every transition map is
  -- an identity and the constant family is automatically compatible.
  cases i with
  | mk i =>
      cases j with
      | mk j =>
          obtain rfl : i = j := Discrete.eq_of_hom f
          obtain rfl : f = 𝟙 _ := rfl
          rfl

/-- Helper for Chap12 Remark 12 16 3 Warning: the compatible family whose every coordinate is the
lifted constant skyscraper section `1 : ℤ`. -/
private noncomputable def realSkyscraperUliftConstantOneSections
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    (((realSkyscraperUliftSectionDiagram U) ⋙
        forget AddCommGrpCat.{u}).sections) :=
  { val := fun _ ↦ realSkyscraperUliftSectionOne hU
    property := fun {_i _j} f ↦ realSkyscraperUliftConstantOneSections_property hU f }

/-- Helper for Chap12 Remark 12 16 3 Warning: over any neighborhood of `0`, the lifted target
limit has a canonical section whose every coordinate is the lifted constant section `1 : ℤ`. -/
private noncomputable def realSkyscraperUliftLimitSectionOne
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) :
    (realSkyscraperUliftLimitSheaf.1.obj (Opposite.op U)) :=
  -- Route correction: build the constant-one target section directly upstairs, so the later local
  -- witness never needs a global comparison with the small limit object.
  letI := sheafSectionFunctorLargePreservesLimitRealSkyscraperDiagram U
  (preservesLimitIso (sheafSectionFunctorLarge U)
      (realSkyscraperDiagram ⋙ realSheafUliftFunctor)).inv
    (limitOfUnderlyingSections
      (realSkyscraperUliftSectionDiagram U)
      (realSkyscraperUliftConstantOneSections hU))

/-- Helper for Chap12 Remark 12 16 3 Warning: every coordinate of the lifted neighborhood-wise
target limit section is the lifted constant skyscraper section `1 : ℤ`. -/
private theorem realSkyscraperUliftLimitSectionOne_proj
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) (j : Discrete ℕ) :
    ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op U))
        (realSkyscraperUliftLimitSectionOne hU) =
      realSkyscraperUliftSectionOne hU := by
  -- Proof comment: exactly as in the small proof, first rewrite the chosen limit point through
  -- `preservesLimitIso`, then read off the underlying compatible family at coordinate `j`.
  letI := sheafSectionFunctorLargePreservesLimitRealSkyscraperDiagram U
  have hπ :
      ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op U))
          (realSkyscraperUliftLimitSectionOne hU) =
        limit.π (realSkyscraperUliftSectionDiagram U) j
          (limitOfUnderlyingSections
            (realSkyscraperUliftSectionDiagram U)
            (realSkyscraperUliftConstantOneSections hU)) := by
    simpa [realSkyscraperUliftLimitSectionOne, realSkyscraperUliftSectionDiagram] using
      congrArg
        (fun k ↦
          k (limitOfUnderlyingSections
            (realSkyscraperUliftSectionDiagram U)
            (realSkyscraperUliftConstantOneSections hU)))
        (preservesLimitIso_inv_π (sheafSectionFunctorLarge U)
          (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j)
  exact hπ.trans <| by
    simpa using
    (limit_π_limitOfUnderlyingSections
      (realSkyscraperUliftSectionDiagram U)
      (realSkyscraperUliftConstantOneSections hU) j)

/-- Helper for Chap12 Remark 12 16 3 Warning: the top section of the lifted target limit whose
every coordinate is the lifted constant section `1 : ℤ`. -/
private noncomputable def realSkyscraperUliftLimitTopConstantOne :
    (realSkyscraperUliftLimitSheaf.1.obj (Opposite.op ⊤)) :=
  realSkyscraperUliftLimitSectionOne
    (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ)))

/-- Helper for Chap12 Remark 12 16 3 Warning: after restricting a lifted neighborhood-wise target
limit section to a smaller open around `0`, each coordinate is still the lifted constant section
`1 : ℤ`. -/
private theorem realSkyscraperUliftLimitSectionOne_restrict_proj
    {U V : Opens (TopCat.of ℝ)} (i : V ⟶ U) (hU : (0 : ℝ) ∈ U) (hV : (0 : ℝ) ∈ V)
    (j : Discrete ℕ) :
    ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op V))
        (TopCat.Presheaf.restrictOpen (realSkyscraperUliftLimitSectionOne hU) V (leOfHom i)) =
      realSkyscraperUliftSectionOne hV := by
  -- Proof comment: project after restricting, replace the unrestricted coordinate by the
  -- constant-one coordinate formula, and then simplify the lifted skyscraper restriction.
  have hrestrict :
      ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op V))
          (TopCat.Presheaf.restrictOpen (realSkyscraperUliftLimitSectionOne hU) V (leOfHom i)) =
        TopCat.Presheaf.restrictOpen
          (((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app
              (Opposite.op U)) (realSkyscraperUliftLimitSectionOne hU))
          V (leOfHom i) := by
    simpa using
      (TopCat.Presheaf.map_restrict ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom)
        (leOfHom i) (realSkyscraperUliftLimitSectionOne hU))
  have hproj_restrict :
      TopCat.Presheaf.restrictOpen
          (((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op U))
            (realSkyscraperUliftLimitSectionOne hU))
          V (leOfHom i) =
        TopCat.Presheaf.restrictOpen (realSkyscraperUliftSectionOne hU) V (leOfHom i) := by
    exact congrArg (fun s ↦ TopCat.Presheaf.restrictOpen s V (leOfHom i))
      (realSkyscraperUliftLimitSectionOne_proj hU j)
  calc
    ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op V))
        (TopCat.Presheaf.restrictOpen (realSkyscraperUliftLimitSectionOne hU) V (leOfHom i)) =
      TopCat.Presheaf.restrictOpen
        (((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op U))
          (realSkyscraperUliftLimitSectionOne hU))
        V (leOfHom i) := hrestrict
    _ =
      TopCat.Presheaf.restrictOpen (realSkyscraperUliftSectionOne hU) V (leOfHom i) := by
      exact hproj_restrict
    _ = realSkyscraperUliftSectionOne hV := by
      simpa using realSkyscraperUliftSectionOne_restrict i hU hV

/-- Helper for Chap12 Remark 12 16 3 Warning: after restricting the lifted top constant-one target
limit section to any open containing `0`, every coordinate is still the lifted constant section
`1 : ℤ`. -/
private theorem realSkyscraperUliftLimitTopConstantOne_restrict_proj
    {U : Opens (TopCat.of ℝ)} (hU : (0 : ℝ) ∈ U) (j : Discrete ℕ) :
    ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op U))
        (TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne U
          (show U ≤ ⊤ by simp)) =
      realSkyscraperUliftSectionOne hU := by
  -- Proof comment: this is the top-open specialization of the lifted restriction projection
  -- formula.
  simpa [realSkyscraperUliftLimitTopConstantOne] using
    realSkyscraperUliftLimitSectionOne_restrict_proj
      (homOfLE (show U ≤ ⊤ by
        intro x hx
        simp))
      (by simp : (0 : ℝ) ∈ (⊤ : Opens (TopCat.of ℝ))) hU j

/-- Helper for Chap12 Remark 12 16 3 Warning: exact countable products in the large real sheaf
category yield a local lifted preimage of the top constant-one target section. -/
private theorem realSkyscraperUliftLimitTopConstantOne_localLift
    (hAB4Star : CountableAB4Star (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))) :
    ∃ (V : Opens (TopCat.of ℝ)) (_ : (0 : ℝ) ∈ V)
      (sUp : continuousZeroOutsideUliftLimitSheaf.1.obj (Opposite.op V)),
      (continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op V)) sUp =
        TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne V
          (show V ≤ ⊤ by simp) := by
  -- Route correction: convert the single lifted limit-map epi to a local-surjectivity witness,
  -- instead of reproving surjectivity stalkwise.
  have hLocal :
      CategoryTheory.Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology (TopCat.of ℝ)) continuousZeroOutsideUliftLimitMap.hom := by
    exact continuousZeroOutsideUliftLimitMap_locallySurjective hAB4Star
  rw [realPresheaf_isLocallySurjective_iff] at hLocal
  rcases hLocal ⊤ realSkyscraperUliftLimitTopConstantOne 0 (by simp) with
    ⟨V, hVTop, hsurj, h0V⟩
  rcases hsurj with ⟨sUp, hsUp⟩
  refine ⟨V, h0V, sUp, ?_⟩
  simpa using hsUp

/-- Helper for Chap12 Remark 12 16 3 Warning: once the lifted top constant-one section lifts over
a neighborhood of `0`, every positive-radius ball inside that neighborhood lies in each shrinking
open after projecting to a coordinate and applying `ULift.down`. -/
private theorem ballSubset_realShrinkingOpen_of_uliftLocalLift
    {V : Opens (TopCat.of ℝ)}
    {sUp : (continuousZeroOutsideUliftLimitSheaf.1.obj (Opposite.op V))}
    (hsUp :
      (continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op V)) sUp =
        TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne V
          (show V ≤ ⊤ by simp))
    {r : ℝ} (hr : 0 < r)
    (hBall :
      (⟨Metric.ball (0 : ℝ) r, Metric.isOpen_ball⟩ : Opens (TopCat.of ℝ)) ≤ V)
    (n : ℕ) :
    (⟨Metric.ball (0 : ℝ) r, Metric.isOpen_ball⟩ : Opens (TopCat.of ℝ)) ≤ realShrinkingOpen n := by
  -- Route correction: restrict the local lifted witness to the ball, project a single coordinate,
  -- descend with `ULift.down`, and then invoke the existing small-ball contradiction lemma.
  let B : Opens (TopCat.of ℝ) := ⟨Metric.ball (0 : ℝ) r, Metric.isOpen_ball⟩
  have hBTop : B ≤ ⊤ := by
    intro x hx
    simp
  have hLiftOnBall :
      (continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op B))
          (TopCat.Presheaf.restrictOpen sUp B hBall) =
        TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne B hBTop := by
    calc
      (continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op B))
          (TopCat.Presheaf.restrictOpen sUp B hBall) =
        TopCat.Presheaf.restrictOpen
          ((continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op V)) sUp)
          B hBall := by
            simpa using
              (TopCat.Presheaf.map_restrict
                continuousZeroOutsideUliftLimitMap.hom
                hBall sUp)
      _ =
        TopCat.Presheaf.restrictOpen
          (TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne V
            (show V ≤ ⊤ by
              intro x hx
              simp))
          B hBall := by
            rw [hsUp]
      _ = TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne B hBTop := by
            simpa [B] using
              (TopCat.Presheaf.restrict_restrict hBall
                (show V ≤ ⊤ by
                  intro x hx
                  simp)
                realSkyscraperUliftLimitTopConstantOne)
  let j : Discrete ℕ := Discrete.mk n
  have hProjectedUp :
      ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op B))
          ((continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op B))
              (TopCat.Presheaf.restrictOpen sUp B hBall)) =
        ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op B))
          (TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne B hBTop) := by
    exact congrArg
      (fun t ↦ ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app
        (Opposite.op B)) t)
      hLiftOnBall
  have hProjectedTarget :
      ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op B))
          (TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne B hBTop) =
        realSkyscraperUliftSectionOne (zero_mem_realBall r hr) := by
    simpa [B] using realSkyscraperUliftLimitTopConstantOne_restrict_proj
      (zero_mem_realBall r hr) j
  have hProjectedSource :
      ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op B))
          ((continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op B))
              (TopCat.Presheaf.restrictOpen sUp B hBall)) =
        ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j).hom.app
          (Opposite.op B)
          (((limit.π (continuousZeroOutsideDiagram ⋙ realSheafUliftFunctor) j).hom.app
              (Opposite.op B))
            (TopCat.Presheaf.restrictOpen sUp B hBall)) := by
    simpa [Category.assoc, ConcreteCategory.comp_apply] using
      congrArg
        (fun k ↦ k (TopCat.Presheaf.restrictOpen sUp B hBall))
        (congrArg (fun f ↦ f.hom.app (Opposite.op B))
          (limMap_π (Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor) j))
  let sBallUp :
      ((realSheafUliftFunctor.obj (continuousZeroOutsideSheaf n)).1.obj (Opposite.op B)) :=
    ((limit.π (continuousZeroOutsideDiagram ⋙ realSheafUliftFunctor) j).hom.app
      (Opposite.op B))
      (TopCat.Presheaf.restrictOpen sUp B hBall)
  let sBall : (continuousZeroOutsideSheaf n).1.obj (Opposite.op B) := ULift.down sBallUp
  have hSmallLift :
      ((continuousZeroOutsideNatTrans).app j).hom.app (Opposite.op B) sBall =
        realSkyscraperSectionOne (zero_mem_realBall r hr) := by
    have hUp :
        ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j).hom.app
            (Opposite.op B) sBallUp =
          realSkyscraperUliftSectionOne (zero_mem_realBall r hr) := by
      calc
        ((Functor.whiskerRight continuousZeroOutsideNatTrans realSheafUliftFunctor).app j).hom.app
            (Opposite.op B) sBallUp =
          ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op B))
            ((continuousZeroOutsideUliftLimitMap.hom.app (Opposite.op B))
                (TopCat.Presheaf.restrictOpen sUp B hBall)) := by
              symm
              exact hProjectedSource
        _ =
          ((limit.π (realSkyscraperDiagram ⋙ realSheafUliftFunctor) j).hom.app (Opposite.op B))
            (TopCat.Presheaf.restrictOpen realSkyscraperUliftLimitTopConstantOne B hBTop) := by
              exact hProjectedUp
        _ = realSkyscraperUliftSectionOne (zero_mem_realBall r hr) := hProjectedTarget
    have hUp' :
        ULift.up (((continuousZeroOutsideNatTrans).app j).hom.app (Opposite.op B) sBall) =
          realSkyscraperUliftSectionOne (zero_mem_realBall r hr) := by
      simpa [sBall, sBallUp, realSheafUliftFunctor_map_app, ULift.up_down] using hUp
    exact congrArg ULift.down hUp'
  have hone :
      continuousZeroOutsideEvalAtZero n (zero_mem_realBall r hr) sBall = 1 := by
    have hEvalSection :
        (ConcreteCategory.hom
          (eqToHom (if_pos (zero_mem_realBall r hr)) :
            (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op B) ⟶
              AddCommGrpCat.of ℤ))
          (realSkyscraperSectionOne (zero_mem_realBall r hr)) = 1 := by
      change
        (ConcreteCategory.hom
            ((eqToHom (if_pos (zero_mem_realBall r hr)).symm :
                AddCommGrpCat.of ℤ ⟶
                  (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj
                    (Opposite.op B)) ≫
              (eqToHom (if_pos (zero_mem_realBall r hr)) :
                (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj
                    (Opposite.op B) ⟶
                  AddCommGrpCat.of ℤ)))
            (1 : ℤ) = 1
      simp
    have hEval :
        (ConcreteCategory.hom
          (eqToHom (if_pos (zero_mem_realBall r hr)) :
            (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op B) ⟶
              AddCommGrpCat.of ℤ))
          (((continuousZeroOutsideNatTrans).app j).hom.app (Opposite.op B) sBall) = 1 := by
      exact (congrArg
        (ConcreteCategory.hom
          (eqToHom (if_pos (zero_mem_realBall r hr)) :
            (skyscraperSheaf (0 : TopCat.of ℝ) (AddCommGrpCat.of ℤ)).1.obj (Opposite.op B) ⟶
              AddCommGrpCat.of ℤ))
        hSmallLift).trans hEvalSection
    exact (continuousZeroOutsideToSkyscraper_app_mem n (zero_mem_realBall r hr) sBall).symm.trans
      hEval
  -- Proof comment: the projected source section still satisfies the zero-outside condition on the
  -- ball, so the small contradiction lemma now forces the whole ball into `realShrinkingOpen n`.
  exact continuousZeroOutsideBall_forcesShrinkingSubset n hr sBall.2.1 sBall.2.2 hone

private theorem abelianSheavesReal_not_countableAB4Star :
    ¬ CountableAB4Star (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)) :=
by
  -- Route correction: extract one local lifted preimage of the top constant-one section, shrink to
  -- a positive ball around `0`, then project a single coordinate back to the existing ball
  -- contradiction.
  intro hAB4Star
  rcases realSkyscraperUliftLimitTopConstantOne_localLift hAB4Star with ⟨V, h0V, sUp, hsUp⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp V.2 0 h0V
  let B : Opens (TopCat.of ℝ) := ⟨Metric.ball (0 : ℝ) r, Metric.isOpen_ball⟩
  have hB0 : (0 : ℝ) ∈ B := by
    simpa [B] using zero_mem_realBall r hr
  have hBall : B ≤ V := by
    intro x hx
    exact hrV hx
  rcases realNeighborhoodMissesSomeShrinkingOpen B hB0 with ⟨n, hn⟩
  exact hn (ballSubset_realShrinkingOpen_of_uliftLocalLift hsUp hr hBall n)

/-- Helper for Chap12 Remark 12 16 3 Warning: a concrete abelian category with products whose
countable products are not exact. -/
private theorem badCountableAB4StarWitness :
    ∃ (D : Type (u + 1)) (_ : Category.{u} D) (_ : Abelian D) (_ : HasCountableProducts D)
      (_ : HasCountableCoproducts.{u} Dᵒᵖ) (_ : HasCoproducts.{u} Dᵒᵖ),
      ¬ CountableAB4Star D :=
by
  let _ : HasSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} :=
    addCommGrpSheafifyReal
  let D := TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)
  let _ : HasCountableProducts D := by
    dsimp [D]
    infer_instance
  let _ : HasProducts D := by
    dsimp [D]
    infer_instance
  let _ : HasCountableCoproducts Dᵒᵖ := sheafCategoryReal_hasCountableCoproductsOpposite
  let hCoproductsDop : HasCoproducts Dᵒᵖ := by
    infer_instance
  -- Proof comment: the real sheaf category already supplies the concrete witness; its objects live
  -- one universe level above the coefficient category, so the existential packaging must reflect
  -- that ambient object universe exactly.
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, hCoproductsDop,
    abelianSheavesReal_not_countableAB4Star⟩

/-- Helper for Chap12 Remark 12 16 3 Warning: the explicit combined object/hom lift of the real
sheaf category, used to isolate the remaining small-model packaging issue. -/
private abbrev realSheafCounterexampleUlift : Type (u + 1) :=
  ULiftHom.{0} (ULift.{0} (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)))

/-- Helper for Chap12 Remark 12 16 3 Warning: the real-line sheaf category is canonically
equivalent to its combined object/hom lift, so the only missing packaging step is a genuinely
small representative of that lifted category. -/
private noncomputable def realSheafCounterexampleUliftEquiv :
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ) ≌ realSheafCounterexampleUlift :=
  ULiftHomULiftCategory.equiv (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))

/-- Helper for Chap12 Remark 12 16 3 Warning: a large-universe coproduct owner restricts to the
small coproduct universe needed by `GradedObject.total`. -/
private theorem smallestCoproductsOfHasCoproducts
    (C : Type (u + 1)) [Category.{u} C] [HasCoproducts.{u} C] :
    HasCoproducts.{0} C :=
  has_smallest_coproducts_of_hasCoproducts

/-- Supporting counterexample for Remark 12.16.3: there exists an abelian category with coproducts
in which countable coproducts are not exact. -/
private theorem exists_abelian_category_with_coproducts_not_countableAB4 :
    ∃ (C : Type (u + 1)) (_ : Category.{u} C) (_ : Abelian C) (_ : HasCoproducts.{u} C),
      ¬ CountableAB4 C := by
  -- Reduce the coproduct counterexample to a product counterexample in the opposite category.
  rcases badCountableAB4StarWitness with ⟨D, hCat, hAb, hProducts, hCountableCoproducts,
      hCoproducts, hD⟩
  let _ : Category.{u} D := hCat
  let _ : Abelian D := hAb
  let _ : HasCountableProducts D := hProducts
  let _ : HasCountableCoproducts.{u} Dᵒᵖ := hCountableCoproducts
  let _ : HasCoproducts.{u} Dᵒᵖ := hCoproducts
  let _ : HasCoproducts.{0} Dᵒᵖ := smallestCoproductsOfHasCoproducts Dᵒᵖ
  refine ⟨Dᵒᵖ, inferInstance, inferInstance, inferInstance, ?_⟩
  exact notCountableAB4OpOfNotCountableAB4Star D hD

private noncomputable def gradedObjectTotalIsoColim (β : Type) (C : Type u) [Category.{v} C]
    [HasCoproducts C] :
    (piEquivalenceFunctorDiscrete β C).inverse ⋙ GradedObject.total β C ≅
      (colim : (Discrete β ⥤ C) ⥤ C) :=
  NatIso.ofComponents (fun F ↦ Sigma.isoColimit F) <| by
    intro F G α
    apply Sigma.hom_ext
    intro i
    dsimp [GradedObject.total]
    rw [Sigma.ι_map_assoc, Sigma.ι_isoColimit_hom_assoc, Sigma.ι_isoColimit_hom]
    exact (colimit.ι_map α (Discrete.mk i)).symm

private theorem hasExactColimitsOfShape_discrete_int_of_leftExact_gradedObject_total
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts C]
    (h : leftExactFunctor (Gr(C)) C (GradedObject.total ℤ C)) :
    HasExactColimitsOfShape (Discrete ℤ) C := by
  let E := piEquivalenceFunctorDiscrete ℤ C
  let htotal : PreservesFiniteLimits (GradedObject.total ℤ C) :=
    (leftExactFunctor_iff (GradedObject.total ℤ C)).1 h
  letI : PreservesFiniteLimits (E.inverse ⋙ GradedObject.total ℤ C) :=
    ⟨fun J _ _ ↦
      let hE : PreservesLimitsOfShape J E.inverse := by
        infer_instance
      let hshape : PreservesLimitsOfShape J (GradedObject.total ℤ C) :=
        @CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits _ _ _ _
          (GradedObject.total ℤ C) htotal J _ _
      @CategoryTheory.Limits.comp_preservesLimitsOfShape _ _ _ _ J _ _ _ E.inverse
        (GradedObject.total ℤ C) hE hshape⟩
  exact ⟨preservesFiniteLimits_of_natIso (gradedObjectTotalIsoColim ℤ C)⟩

-- Proof sketch: `GradedObject.total ℤ C` identifies with the colimit functor on
-- `Discrete ℤ ⥤ C`; if it were left exact, then exactness of `ℤ`-indexed coproducts would follow.
-- Transporting along `Equiv.intEquivNat` gives exactness of `ℕ`-indexed coproducts, hence
-- `CountableAB4 C`.
/-- If the total functor on `Gr(C)` is left exact, then countable coproducts in the ambient
abelian category are exact. -/
theorem countableAB4_of_leftExact_gradedObject_total {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts C]
    (h : leftExactFunctor (Gr(C)) C (GradedObject.total ℤ C)) : CountableAB4 C := by
  letI : HasExactColimitsOfShape (Discrete ℤ) C :=
    hasExactColimitsOfShape_discrete_int_of_leftExact_gradedObject_total h
  letI : HasExactColimitsOfShape (Discrete ℕ) C :=
    HasExactColimitsOfShape.of_domain_equivalence C (Discrete.equivalence Equiv.intEquivNat)
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  exact CountableAB4.of_hasExactColimitsOfShape_nat C

private local instance realLineAbelianSheafify :
    HasSheafify (Opens.grothendieckTopology (TopCat.of ℝ)) AddCommGrpCat.{u} :=
  addCommGrpSheafifyReal

private abbrev realLineAbelianSheaf : Type (u + 1) :=
  TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ)

private abbrev realLineAbelianSheafOpposite : Type (u + 1) :=
  realLineAbelianSheafᵒᵖ

private local instance realLineAbelianSheaf_hasCountableProducts :
    HasCountableProducts realLineAbelianSheaf := by
  dsimp [realLineAbelianSheaf]
  infer_instance

private local instance realLineAbelianSheaf_hasSmallProducts :
    HasProducts.{0} realLineAbelianSheaf := by
  dsimp [realLineAbelianSheaf]
  infer_instance

private local instance realLineAbelianSheafOpposite_hasCountableCoproducts :
    HasCountableCoproducts.{u} realLineAbelianSheafOpposite :=
  sheafCategoryReal_hasCountableCoproductsOpposite

private local instance realLineAbelianSheafOpposite_hasSmallestCoproducts :
    HasCoproducts.{0} realLineAbelianSheafOpposite := by
  infer_instance

private theorem realLineAbelianSheafOpposite_not_countableAB4 :
    ¬ CountableAB4 realLineAbelianSheafOpposite := by
  exact notCountableAB4OpOfNotCountableAB4Star realLineAbelianSheaf
    abelianSheavesReal_not_countableAB4Star

-- Proof sketch: exactness implies left exactness. Hence, if countable coproducts in `C` were not
-- exact, exactness of `GradedObject.total ℤ C` would force `CountableAB4 C`, contradiction.
/-- Helper for Remark 12.16.3 (Warning): under full coproduct hypotheses, failure of
`CountableAB4` forces the graded total functor to be nonexact. -/
theorem gradedObject_total_not_exact_of_not_countableAB4 {C : Type u} [Category.{v} C]
    [Abelian C] [HasCoproducts C] (hC : ¬ CountableAB4 C) :
    ¬ exactFunctor (Gr(C)) C (GradedObject.total ℤ C) := by
  intro hExact
  have hLeft :
      leftExactFunctor (Gr(C)) C (GradedObject.total ℤ C) := by
    -- Proof comment: exact functors preserve finite limits, hence are left exact.
    simpa [leftExactFunctor_iff] using
      ((exactFunctor_iff (GradedObject.total ℤ C)).1 hExact).1
  exact hC (countableAB4_of_leftExact_gradedObject_total hLeft)

-- The source's explicit counterexample is the opposite of the category of abelian sheaves on `ℝ`.
/- Remark 12.16.3 (Warning) splits into two source-facing clauses: the explicit real-line
counterexample for nonexactness of the graded total functor, and the degreewise kernel
description. -/
/-- Remark 12.16.3 (Warning) (1): for the opposite of the category of abelian sheaves on `ℝ`,
the total functor `Gr(𝒜) ⥤ 𝒜`, `A ↦ ∐ fun i : ℤ ↦ A i`, is not exact. -/
@[stacks 0AMH]
theorem realLineAbelianSheafOpposite_gradedObject_total_not_exact :
    ¬ exactFunctor
      (Gr(((TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))ᵒᵖ)))
      ((TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))ᵒᵖ)
      (GradedObject.total ℤ ((TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of ℝ))ᵒᵖ)) :=
  gradedObject_total_not_exact_of_not_countableAB4
    realLineAbelianSheafOpposite_not_countableAB4

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

local instance gradedObjectEvalPreservesZeroMorphisms (i : ℤ) :
    Functor.PreservesZeroMorphisms (GradedObject.eval i : Gr(C) ⥤ C) where
  map_zero _ _ := rfl

/-- Remark 12.16.3 (Warning) (2): kernels in `Gr(C)` are computed degreewise. In
particular, for a morphism `φ`, evaluating the kernel object at degree `i` recovers the kernel of
the degree-`i` map, rather than an ambient `kernel φ` merely endowed with a direct-sum
decomposition. -/
@[stacks 0AMH]
theorem gradedObject_kernel_degreewise [Abelian C] {A B : Gr(C)} (φ : A ⟶ B) (i : ℤ) :
    IsIso (kernelComparison φ (GradedObject.eval i : Gr(C) ⥤ C)) := by
  let E := piEquivalenceFunctorDiscrete ℤ C
  letI : PreservesLimit (parallelPair φ 0) (GradedObject.eval i : Gr(C) ⥤ C) := by
    simpa [E, GradedObject.eval] using
      (inferInstance : PreservesLimit (parallelPair φ 0)
        (E.functor ⋙ (evaluation (Discrete ℤ) C).obj (Discrete.mk i)))
  infer_instance

end CategoryTheory
