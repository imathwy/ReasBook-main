import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import StacksProject_2024.stacks_project.Chap07.Definition_7_17_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_14_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_19_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_30_1
import StacksProject_2024.stacks_project.Chap18.Situation_18_30_5

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

local instance : HasColimits (ringedSiteModuleCategory J 𝒪) := by
  dsimp [ringedSiteModuleCategory]
  infer_instance

local instance : HasLimits (ringedSiteModuleCategory J 𝒪) := by
  dsimp [ringedSiteModuleCategory]
  infer_instance

/-- Helper for Lemma 18.30.9: module sheaves on a ringed site admit all discrete coproducts used
in the finite-index constructions below. -/
local instance (ι : Type w) :
    HasColimitsOfShape (Discrete ι) (ringedSiteModuleCategory J 𝒪) := by
  infer_instance

/-- The module `j_{U!}\mathcal O_U` on a commutative ringed site. -/
private abbrev extensionByZeroStructureModule (U : C) :
    ringedSiteModuleCategory J 𝒪 :=
  localizedStructureModuleExtensionByZero J 𝒪 U

/-- Helper for Lemma 18.30.9: restriction of sections along `f`. -/
private def sectionMap
    {U V : C} (f : V ⟶ U) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ →
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).obj ℱ :=
  ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op

/-- Helper for Lemma 18.30.9: restriction commutes with applying a morphism of module sheaves. -/
private theorem sectionMap_naturality
    {U V : C} {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪}
    (f : V ⟶ U) (α : ℱ ⟶ 𝒢)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) :
    ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α)
        (sectionMap (J := J) (𝒪 := 𝒪) f ℱ s) =
      sectionMap (J := J) (𝒪 := 𝒪) f 𝒢
        (((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α) s) := by
  -- Restriction is the underlying presheaf action, so naturality is pointwise naturality.
  change ConcreteCategory.hom (α.val.app (op V))
      (ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op) s) =
    ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj 𝒢).1.map f.op)
      (ConcreteCategory.hom (α.val.app (op U)) s)
  simpa using ConcreteCategory.congr_hom (α.val.naturality f.op) s

/-- Helper for Lemma 18.30.9: sections on the slice site over `U` are equivalent to ordinary
sections over `U`. -/
private noncomputable def overSectionsEquivEvaluation
    (U : C) (ℱ : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.over ℱ U).sections ≃
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (SheafOfModules.over ℱ U).val.sectionsMk
      (fun X ↦ (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun (X Y : (Over U)ᵒᵖ) (f : X ⟶ Y) ↦ by
        -- Every slice arrow to the terminal object is the canonical one.
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- A slice-site section is determined by the maps from each object to the terminal one.
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    -- Evaluating the reconstructed section at the terminal object recovers the original section.
    change
      (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (SheafOfModules.over ℱ U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.30.9: evaluating the reconstructed slice-site section on a cover arrow
recovers ordinary restriction along that arrow. -/
private theorem overSectionsEquivEvaluation_symm_apply_cover
    {U V : C} (f : V ⟶ U) (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj ℱ) :
    ((overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) U ℱ).symm s).1
        (op (Over.mk f)) =
      sectionMap (J := J) (𝒪 := 𝒪) f ℱ s := by
  -- The slice terminal comparison out of `Over.mk f` is the arrow `f` itself.
  have h : Over.mkIdTerminal.from (Over.mk f) = Over.homMk f := by
    exact Over.mkIdTerminal.hom_ext _ _
  change ConcreteCategory.hom ((SheafOfModules.over ℱ U).val.map
      ((Over.mkIdTerminal.from (Over.mk f)).op)) s =
    ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op) s
  rw [h]
  rfl

/-- Helper for Lemma 18.30.9: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    {U : C} {ℱ 𝒢 : ringedSiteModuleCategory J 𝒪}
    (β : extensionByZeroStructureModule J 𝒪 U ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
  -- The owner equivalence is assembled from target-functorial constructions.
  rfl

/-- Helper for Lemma 18.30.9: precomposition by `localizedStructureModuleExtensionByZeroMap`
becomes restriction of sections. -/
private theorem localizedStructureModuleExtensionByZeroMap_homEquiv
    {V W : C} (f : V ⟶ W) (ℱ : ringedSiteModuleCategory J 𝒪)
    (α : extensionByZeroStructureModule J 𝒪 W ⟶ ℱ) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ
        (localizedStructureModuleExtensionByZeroMap J 𝒪 f ≫ α) =
      sectionMap (J := J) (𝒪 := 𝒪) f ℱ
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α) := by
  -- Route correction: reuse the public owner naturality instead of unfolding the adjunction.
  have hα : localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W
          (extensionByZeroStructureModule J 𝒪 W) (𝟙 _)) := by
    simpa using
      localizedStructureModuleExtensionByZero_homEquiv_naturality_right
        (J := J) (𝒪 := 𝒪) (β := 𝟙 (extensionByZeroStructureModule J 𝒪 W)) (α := α)
  rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    (J := J) (𝒪 := 𝒪) (β := localizedStructureModuleExtensionByZeroMap J 𝒪 f) (α := α)]
  rw [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroMap]
  rw [Equiv.apply_symm_apply]
  rw [hα]
  exact sectionMap_naturality (J := J) (𝒪 := 𝒪) f α _

/-- The index type obtained by summing the selected finite subfamilies of the covers of the `U_i`.
-/
private abbrev selectedCoverIndex {n : ℕ} (r : Fin n → ℕ) :=
  Σ i : Fin n, Fin (r i)

/-- The object in the selected finite subfamily corresponding to an index in `selectedCoverIndex`.
-/
private abbrev selectedCoverObject {n : ℕ} {K : Fin n → Type _}
    (r : Fin n → ℕ) (κ : ∀ i : Fin n, Fin (r i) → K i)
    (Ucover : ∀ i : Fin n, K i → C) :
    selectedCoverIndex r → C
  | ⟨i, a⟩ => Ucover i (κ i a)

/-- Helper for Lemma 18.30.9: the index type of pairwise overlaps inside a selected finite
subcover. -/
private abbrev selectedOverlapIndex {n : ℕ} (r : Fin n → ℕ) :=
  Σ i : Fin n, Fin (r i) × Fin (r i)

/-- Helper for Lemma 18.30.9: the selected finite cover of `U i` as an explicit family over the
slice object `Over (U i)`. -/
private abbrev selectedCoverFamily {n : ℕ} {K : Fin n → Type _}
    (U : Fin n → C)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (i : Fin n) :
    SemiRepresentableFamily.Over (U i) :=
  SemiRepresentableFamily.Over.ofArrows
    (fun a : Fin (r i) ↦ Ucover i (κ i a))
    (fun a ↦ π i (κ i a))

/-- Helper for Lemma 18.30.9: every selected finite basis cover has the pairwise pullbacks
required to form its canonical overlap objects. -/
private theorem selectedCoverPairwisePullbacks
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a)))) :
    ∀ i : Fin n, (selectedCoverFamily U κ Ucover π i).toPresieve.HasPairwisePullbacks := by
  intro i
  let 𝒰 : SemiRepresentableFamily.Over (U i) := selectedCoverFamily U κ Ucover π i
  have h𝒰 : 𝒰.toSieve ∈ J (U i) := by
    exact coveringSieve_of_coversTopOver (J := J)
      (Uᵢ := fun a : Fin (r i) ↦ Ucover i (κ i a))
      (π := fun a ↦ π i (κ i a))
      (hcoverFin i)
  let hBasis : J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B := inferInstance
  obtain ⟨hpair, _⟩ :=
    hBasis.hasQuasiCompactPairwiseOverlaps
      (hU i) 𝒰 h𝒰 (fun a ↦ hUcover i (κ i a))
  exact hpair

/-- Helper for Lemma 18.30.9: the raw overlap object attached to a selected-cover pair. -/
private abbrev selectedOverlapObject {n : ℕ} {K : Fin n → Type _}
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a)))) :
    selectedOverlapIndex r → C
  | ⟨i, a, b⟩ =>
      let 𝒰 : SemiRepresentableFamily.Over (U i) := selectedCoverFamily U κ Ucover π i
      let _ : 𝒰.toPresieve.HasPairwisePullbacks :=
        selectedCoverPairwisePullbacks (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin i
      Limits.pullback (𝒰.obj a).hom (𝒰.obj b).hom

/-- Helper for Lemma 18.30.9: the slice-site family attached to `fun i ↦ Over.mk (π i)` generates
the same base-site sieve as the arrows `π i`. -/
private theorem overSieveOfObjectsEqOfArrows
    {ι : Type w} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun i : ι ↦ Over.mk (π i)) (Over.mk (𝟙 U))) =
      Sieve.ofArrows Uᵢ π := by
  -- A factorization in `Over U` is exactly the same factorization in the base site.
  ext V f
  constructor
  · intro hf
    rw [Sieve.overEquiv_iff] at hf
    rw [Sieve.mem_ofObjects_iff] at hf
    rcases hf with ⟨i, ⟨g⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, g.left, by simpa using g.w.symm⟩
  · intro hf
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hf
    rcases hf with ⟨i, g, hg⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk g (by simpa using hg.symm)⟩⟩

/-- Helper for Lemma 18.30.9: a slice-site `CoversTop` hypothesis yields the corresponding
covering sieve on the base object. -/
private theorem coveringSieve_of_coversTopOver
    {ι : Type w} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : (J.over U).CoversTop (fun i : ι ↦ Over.mk (π i))) :
    Sieve.ofArrows Uᵢ π ∈ J U := by
  -- Rewrite the slice cover of the terminal object into the corresponding base-site sieve.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)] at hcover
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows
    (Uᵢ := Uᵢ) (π := π)] at hcover
  exact hcover

/-- Helper for Lemma 18.30.9: a covering refinement landing in a subfamily indexed by the image
of the refinement map still covers the base object. -/
private theorem restrictedRangeFamilyCovering
    {ι : Type w} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    {𝒱 : SemiRepresentableFamily.Over U}
    (h𝒱 : 𝒱.toSieve ∈ J U)
    (φ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows Uᵢ π) :
    Sieve.ofArrows (fun i : Set.range φ.α ↦ Uᵢ i.1) (fun i ↦ π i.1) ∈ J U := by
  -- The restricted subtype family covers because the refining family factors through it.
  let ψ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows
      (fun i : Set.range φ.α ↦ Uᵢ i.1) (fun i ↦ π i.1) :=
    { α := fun i ↦ ⟨φ.α i, ⟨i, rfl⟩⟩
      f := fun i ↦ φ.f i }
  have hrestricted :
      (SemiRepresentableFamily.Over.ofArrows
        (fun i : Set.range φ.α ↦ Uᵢ i.1) (fun i ↦ π i.1)).toSieve ∈ J U := by
    exact J.superset_covering (SemiRepresentableFamily.Over.toSieve_le_of_hom ψ) h𝒱
  simpa using hrestricted

/-- Helper for Lemma 18.30.9: a covering sieve on a subfamily converts back to the corresponding
slice-site `CoversTop` statement. -/
private theorem coversTopOver_of_coveringSieve
    {ι : Type w} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    {S : Set ι}
    (hcover : Sieve.ofArrows (fun i : S ↦ Uᵢ i.1) (fun i ↦ π i.1) ∈ J U) :
    (J.over U).CoversTop (fun i : S ↦ Over.mk (π i.1)) := by
  -- Rewrite the ordinary covering sieve back into the slice-site terminal covering condition.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows
    (Uᵢ := fun i : S ↦ Uᵢ i.1) (π := fun i ↦ π i.1)]
  exact hcover

/-- Helper for Lemma 18.30.9: reindexing a covering family by an equivalence does not change the
generated covering sieve. -/
private theorem coversTopOver_reindexEquiv
    {ι ι' : Type w} {U : C}
    (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U) (e : ι ≃ ι')
    (hcover : (J.over U).CoversTop (fun i : ι ↦ Over.mk (π i))) :
    (J.over U).CoversTop (fun i : ι' ↦ Over.mk (π (e.symm i))) := by
  -- The reindexed family generates the same base-site sieve, so it is again a slice-site cover.
  refine coversTopOver_of_coveringSieve (J := J)
    (Uᵢ := fun i : ι' ↦ Uᵢ (e.symm i)) (π := fun i ↦ π (e.symm i)) ?_
  rw [show
      Sieve.ofArrows (fun i : ι' ↦ Uᵢ (e.symm i)) (fun i ↦ π (e.symm i)) =
        Sieve.ofArrows Uᵢ π by
          ext V f
          constructor
          · intro hf
            rw [Sieve.mem_ofArrows_iff] at hf ⊢
            rcases hf with ⟨i, g, hg⟩
            exact ⟨e.symm i, g, hg⟩
          · intro hf
            rw [Sieve.mem_ofArrows_iff] at hf ⊢
            rcases hf with ⟨i, g, hg⟩
            exact ⟨e i, g, hg⟩]
  exact coveringSieve_of_coversTopOver (J := J) (Uᵢ := Uᵢ) (π := π) hcover

/-- Helper for Lemma 18.30.9: composing a slice-site cover of `U` with slice-site covers of its
members yields a sigma-indexed slice-site cover of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {ι : Type w} {X : ι → Over U}
    (hX : (J.over U).CoversTop X)
    {κ : ι → Type w} {Y : ∀ i : ι, κ i → Over (X i).left}
    (hY : ∀ i : ι, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Sigma κ ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- First rewrite every slice cover into the corresponding ordinary covering sieve.
  refine coversTopOver_of_coveringSieve (J := J)
    (Uᵢ := fun a : Sigma κ ↦ (Y a.1 a.2).left)
    (π := fun a ↦ (Y a.1 a.2).hom ≫ (X a.1).hom) ?_
  have hSX :
      Sieve.ofArrows (fun i : ι ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    exact coveringSieve_of_coversTopOver (J := J)
      (Uᵢ := fun i : ι ↦ (X i).left) (π := fun i ↦ (X i).hom) hX
  have hSY :
      ∀ i : ι,
        Sieve.ofArrows (fun a : κ i ↦ (Y i a).left) (fun a ↦ (Y i a).hom) ∈ J ((X i).left) := by
    intro i
    exact coveringSieve_of_coversTopOver (J := J)
      (Uᵢ := fun a : κ i ↦ (Y i a).left) (π := fun a ↦ (Y i a).hom) (hY i)
  let R : Sieve U :=
    Sieve.ofArrows
      (fun a : Sigma κ ↦ (Y a.1 a.2).left)
      (fun a ↦ (Y a.1 a.2).hom ≫ (X a.1).hom)
  -- The composite sieve is covering by the transitivity axiom, because over each member of the
  -- first cover it contains the pullback of the second chosen cover.
  have hR : R ∈ J U := by
    refine J.transitive hSX ?_
    intro V f hf
    let I : Over U := Over.mk f
    let i : Sieve.ofArrows (fun i : ι ↦ (X i).left) (fun i ↦ (X i).hom) f := hf
    rcases (Sieve.mem_ofArrows_iff.mp i) with ⟨j, g, hg⟩
    have hpull :
        Sieve.ofArrows (fun a : κ j ↦ (Y j a).left) (fun a ↦ (Y j a).hom) ≤ R.pullback f := by
      intro Z hZ hz
      rw [Sieve.mem_pullback_iff]
      rw [Sieve.mem_ofArrows_iff] at hz
      rcases hz with ⟨a, k, hk⟩
      refine ⟨⟨j, a⟩, k, ?_⟩
      dsimp [R]
      simp [hg, hk, Category.assoc]
    exact J.superset_covering hpull (hSY j)
  simpa [R] using hR

/-- Helper for Lemma 18.30.9: the arrows of a cover form a `CoversTop` family on the same base
object. -/
private theorem coverArrows_coversTop
    {U : C} (S : J.Cover U) :
    (J.over U).CoversTop (fun I : S.Arrow ↦ Over.mk I.f) := by
  -- Rewrite the slice-site terminal cover into the ordinary covering sieve of `S`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows
    (Uᵢ := fun I : S.Arrow ↦ I.Y) (π := fun I ↦ I.f)]
  simpa using S.property

/-- Helper for Lemma 18.30.9: successive restriction maps compose as restriction along the
composite arrow. -/
private theorem sectionMap_comp
    {V W X : C} (f : V ⟶ W) (g : W ⟶ X) (ℱ : ringedSiteModuleCategory J 𝒪)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op X)).obj ℱ) :
    sectionMap (J := J) (𝒪 := 𝒪) f ℱ (sectionMap (J := J) (𝒪 := 𝒪) g ℱ s) =
      sectionMap (J := J) (𝒪 := 𝒪) (f ≫ g) ℱ s := by
  -- Restriction is the underlying presheaf action, so composition is functoriality of `map`.
  let F := ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1
  change ConcreteCategory.hom (F.map f.op) (ConcreteCategory.hom (F.map g.op) s) =
    ConcreteCategory.hom (F.map ((f ≫ g).op)) s
  rw [op_comp, Functor.map_comp]
  rfl

/-- Helper for Lemma 18.30.9: an epimorphism of module sheaves yields an image-sieve cover with
explicit local lifts of any chosen section. -/
private theorem existsCoverLiftOfEpiSection
    {M N : ringedSiteModuleCategory J 𝒪} (p : M ⟶ N) [Epi p]
    (U : C)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj N) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ t : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op I.Y)).obj M,
        ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op I.Y)).map p) t =
          sectionMap (J := J) (𝒪 := 𝒪) I.f N s := by
  let p' := (SheafOfModules.toSheaf (ringSheaf J 𝒪)).map p
  letI : Sheaf.IsLocallySurjective p' :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} p').2 inferInstance
  let T : J.Cover U := ⟨Presheaf.imageSieve p'.hom s, Presheaf.imageSieve_mem (J := J) p'.hom s⟩
  refine ⟨T, ?_⟩
  intro I
  refine ⟨Presheaf.localPreimage p'.hom s I.f I.hf, ?_⟩
  -- The chosen local preimage maps to the requested restricted section by construction.
  simpa [sectionMap] using Presheaf.app_localPreimage p'.hom s I.f I.hf

/-- Witness data for a finite basis refinement whose induced map on cokernels is an
isomorphism. -/
structure FiniteBasisRefinementInducingCokernelIsoWitness
    {n m : ℕ} {K : Fin n → Type w}
    (B : Set C) (U : Fin n → C) (V : Fin m → C)
    (Ucover : ∀ i : Fin n, K i → C)
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))) where
  /-- The number of chosen cover members retained over each `U i`. -/
  r : Fin n → ℕ
  /-- An injective enumeration of the chosen finite subset of each index set `K i`. -/
  κ : ∀ i : Fin n, Fin (r i) → K i
  /-- The selected enumerations are injective. -/
  κ_injective : ∀ i : Fin n, Function.Injective (κ i)
  /-- The number of basis objects used to refine the overlaps. -/
  ℓ : ℕ
  /-- The refining family of basis objects. -/
  W : Fin ℓ → C
  /-- Each refining object lies in the basis `B`. -/
  hW : ∀ l : Fin ℓ, W l ∈ B
  /-- The top horizontal map from the overlap refinement to the selected cover family. -/
  top :
    (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪
          (selectedCoverObject r κ Ucover a))
  /-- The left vertical map from the overlap refinement to the original source family. -/
  left :
    (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j))
  /-- The right vertical map from the selected finite subcovers to the family `U`. -/
  right :
    (∐ fun a : selectedCoverIndex r ↦
      extensionByZeroStructureModule J 𝒪
        (selectedCoverObject r κ Ucover a)) ⟶
      (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))
  /-- The refinement square commutes with the given morphism `f`. -/
  comm : top ≫ right = left ≫ f
  /-- The induced map on cokernels is an isomorphism. -/
  isIso_cokernel_map : IsIso (cokernel.map top f left right comm)

/-- Helper for Lemma 18.30.9: an epimorphic map into the kernel of
`right ≫ cokernel.π f` packages the induced cokernel comparison as an isomorphism. -/
private theorem isIso_cokernelMap_of_epiKernelCover
    {W R S T : ringedSiteModuleCategory J 𝒪}
    {f : S ⟶ T} {right : R ⟶ T}
    (ψ : W ⟶ kernel (right ≫ cokernel.π f)) (left : W ⟶ S)
    [Epi right] [Epi ψ]
    (hcomm : (ψ ≫ kernel.ι (right ≫ cokernel.π f)) ≫ right = left ≫ f) :
    IsIso
      (cokernel.map
        (ψ ≫ kernel.ι (right ≫ cokernel.π f)) f left right hcomm) := by
  let S₁ : ShortComplex (ringedSiteModuleCategory J 𝒪) :=
    ShortComplex.mk
      (ψ ≫ kernel.ι (right ≫ cokernel.π f))
      (right ≫ cokernel.π f)
      (by simp [Category.assoc, hcomm])
  let S₂ : ShortComplex (ringedSiteModuleCategory J 𝒪) :=
    ShortComplex.mk
      (kernel.ι (right ≫ cokernel.π f))
      (right ≫ cokernel.π f)
      (by simp)
  have hS₂Exact : S₂.Exact := by
    -- The canonical kernel row is exact by the kernel universal property.
    simpa [S₂] using
      (ShortComplex.exact_of_f_is_kernel S₂
        (kernelIsKernel (right ≫ cokernel.π f)))
  let η : S₁ ⟶ S₂ :=
    { τ₁ := ψ
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S₁, S₂, Category.assoc]
      comm₂₃ := by simp [S₁, S₂] }
  have hS₁Exact : S₁.Exact := by
    -- Exactness descends across the epimorphic comparison from the chosen kernel cover.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono η).2 hS₂Exact
  let cofork :
      CokernelCofork (ψ ≫ kernel.ι (right ≫ cokernel.π f)) :=
    CokernelCofork.ofπ
      (right ≫ cokernel.π f)
      (by simp [Category.assoc, hcomm])
  have hcofork : IsColimit cofork := by
    -- Exactness and epimorphicity identify `right ≫ cokernel.π f` as a cokernel of the top map.
    have : Epi (right ≫ cokernel.π f) := by infer_instance
    obtain ⟨hcolim⟩ := (S₁.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hS₁Exact, inferInstance⟩
    simpa [cofork] using hcolim
  let e :
      cokernel (ψ ≫ kernel.ι (right ≫ cokernel.π f)) ≅
        cokernel f :=
    IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (ψ ≫ kernel.ι (right ≫ cokernel.π f))) hcofork
  -- The chosen uniqueness isomorphism is the canonical cokernel comparison map.
  have he :
      e.hom =
        cokernel.map
          (ψ ≫ kernel.ι (right ≫ cokernel.π f)) f left right hcomm := by
    apply (cancel_epi (cokernel.π (ψ ≫ kernel.ι (right ≫ cokernel.π f)))).1
    simp [e, cofork, Category.assoc]
  rw [← he]
  infer_instance

/-- Helper for Lemma 18.30.9: the augmentation attached to any chosen cover family is epic. -/
private theorem coverAugmentationEpi
    {ι : Type w} {U : C}
    (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : (J.over U).CoversTop (fun i : ι ↦ Over.mk (π i))) :
    Epi
      (Sigma.desc
        (fun i : ι ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 (π i)) :
        (∐ fun i : ι ↦ extensionByZeroStructureModule J 𝒪 (Uᵢ i)) ⟶
          extensionByZeroStructureModule J 𝒪 U) := by
  let δ :
      (∐ fun i : ι ↦ extensionByZeroStructureModule J 𝒪 (Uᵢ i)) ⟶
        extensionByZeroStructureModule J 𝒪 U :=
    Sigma.desc (fun i : ι ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 (π i))
  refine ⟨?_⟩
  intro ℱ α β hαβ
  let F :=
    ((sheafForget (J.over U)).obj
      ((SheafOfModules.toSheaf ((ringSheaf J 𝒪).over U)).obj (SheafOfModules.over ℱ U)))
  have hs :
      (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) U ℱ).symm
          (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α) =
        (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) U ℱ).symm
          (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β) := by
    -- Equality on the chosen covering family forces equality of the global slice section.
    apply hcover.sections_ext F
    intro i
    rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
      (f := π i) (ℱ := ℱ)
      (s := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α)]
    rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
      (f := π i) (ℱ := ℱ)
      (s := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β)]
    have hcomp := congrArg
      (fun γ ↦ Sigma.ι (fun j : ι ↦ extensionByZeroStructureModule J 𝒪 (Uᵢ j)) i ≫ γ)
      hαβ
    rw [δ, Category.assoc, Category.assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc] at hcomp
    have hsec := congrArg
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Uᵢ i) ℱ) hcomp
    rw [localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := π i) (ℱ := ℱ) (α := α),
      localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := π i) (ℱ := ℱ) (α := β)] at hsec
    exact hsec
  have hsec :
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α =
        localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β := by
    exact (overSectionsEquivEvaluation (J := J) (𝒪 := 𝒪) U ℱ).injective hs
  exact (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ).injective hsec

/-- Helper for Lemma 18.30.9: selecting a finite subcover of each given target cover yields a
global epimorphic right vertical map indexed by `Fin`. -/
private theorem existsFiniteSelectedCoverEpi
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type _}
    (U : Fin n → C)
    (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hcover : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun k : K i ↦ Over.mk (π i k))) :
    ∃ (r : Fin n → ℕ) (κ : ∀ i : Fin n, Fin (r i) → K i)
      (κ_injective : ∀ i : Fin n, Function.Injective (κ i))
      (right :
        (∐ fun a : selectedCoverIndex r ↦
          extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) ⟶
          (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))),
        Epi right ∧
          (∀ i : Fin n,
            (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a)))) ∧
          ∀ a : selectedCoverIndex r,
            Sigma.ι
                (fun b : selectedCoverIndex r ↦
                  extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
                a ≫ right =
              localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 (κ a.1 a.2)) ≫
                Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) a.1 := by
  let hqc : ∀ i : Fin n, J.QuasiCompactObject (U i) := fun i ↦
    HasQuasiCompactBasisWithQuasiCompactFiberProducts.quasiCompactObject
      (J := J) (B := B) (hU i)
  choose S hSfinite hScover using
    (fun i : Fin n ↦ by
      have hsieve :
          Sieve.ofArrows (Ucover i) (π i) ∈ J (U i) :=
        coveringSieve_of_coversTopOver (J := J) (Uᵢ := Ucover i) (π := π i) (hcover i)
      obtain ⟨𝒱, h𝒱, φ, hfinite⟩ :=
        GrothendieckTopology.quasiCompactObject_finite_image_refinement_ofArrows
          (hU := hqc i) (Uᵢ := Ucover i) (π := π i) hsieve
      refine ⟨Set.range φ.α, hfinite, ?_⟩
      apply coversTopOver_of_coveringSieve (J := J) (Uᵢ := Ucover i) (π := π i)
      exact restrictedRangeFamilyCovering (J := J) (Uᵢ := Ucover i) (π := π i) h𝒱 φ)
  let r : Fin n → ℕ := fun i ↦ Fintype.card (S i)
  let κ : ∀ i : Fin n, Fin (r i) → K i := fun i a ↦ ((Fintype.equivFin (S i)).symm a).1
  have hκ : ∀ i : Fin n, Function.Injective (κ i) := by
    intro i a b hab
    apply (Fintype.equivFin (S i)).symm.injective
    apply Subtype.ext
    simpa [κ] using hab
  have hcoverFin :
      ∀ i : Fin n,
        (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a))) := by
    intro i
    simpa [r, κ] using
      coversTopOver_reindexEquiv (J := J)
        (Uᵢ := fun k : S i ↦ Ucover i k.1)
        (π := fun k : S i ↦ π i k.1)
        (e := Fintype.equivFin (S i))
        (hcover := hScover i)
  let right :
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) :=
    Sigma.desc (fun a : selectedCoverIndex r ↦
      localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 (κ a.1 a.2)) ≫
        Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) a.1)
  have hright : Epi right := by
    refine ⟨?_⟩
    intro Z α β hαβ
    apply Limits.Sigma.hom_ext
    intro i
    let δi :
        (∐ fun a : Fin (r i) ↦ extensionByZeroStructureModule J 𝒪 (Ucover i (κ i a))) ⟶
          extensionByZeroStructureModule J 𝒪 (U i) :=
      Sigma.desc (fun a : Fin (r i) ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 (π i (κ i a)))
    have hδi : Epi δi := by
      -- Each selected finite subfamily still covers `U i`, so its augmentation is epic.
      exact coverAugmentationEpi (J := J) (𝒪 := 𝒪)
        (Uᵢ := fun a : Fin (r i) ↦ Ucover i (κ i a))
        (π := fun a ↦ π i (κ i a))
        (hcover := hcoverFin i)
    apply (cancel_epi δi).1
    apply Limits.Sigma.hom_ext
    intro a
    have hcomp := congrArg
      (fun γ ↦
        Sigma.ι
            (fun b : selectedCoverIndex r ↦
              extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
            ⟨i, a⟩ ≫ γ)
      hαβ
    simpa [right, δi, Category.assoc] using hcomp
  have hright_ι :
      ∀ a : selectedCoverIndex r,
        Sigma.ι
            (fun b : selectedCoverIndex r ↦
              extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
            a ≫ right =
          localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 (κ a.1 a.2)) ≫
            Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) a.1 := by
    intro a
    dsimp [right]
    rw [Limits.Sigma.ι_desc]
  exact ⟨r, κ, hκ, right, hright, hcoverFin, hright_ι⟩

/-- Helper for Lemma 18.30.9: every quasi-compact object admits an epimorphic finite cover by
basis objects. -/
private theorem existsFiniteBasisCoverEpiOfQuasiCompact
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {W : C} (hW : J.QuasiCompactObject W) :
    ∃ (ℓ : ℕ) (Z : Fin ℓ → C) (hZ : ∀ l : Fin ℓ, Z l ∈ B)
      (δ : (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (Z l)) ⟶
        extensionByZeroStructureModule J 𝒪 W),
        Epi δ := by
  let hEnough :
      J.HasEnoughObjectsWithProperty (· ∈ B) :=
    (inferInstance : J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B)
      .hasEnoughObjectsWithProperty
  obtain ⟨S, hS⟩ := hEnough W
  let Uᵢ : S.Arrow → C := fun a ↦ a.Y
  let π : ∀ a : S.Arrow, Uᵢ a ⟶ W := fun a ↦ a.f
  have hsieve : Sieve.ofArrows Uᵢ π ∈ J W := by
    -- The basis cover returned by `hasEnoughObjectsWithProperty` is already covering.
    simpa [Uᵢ, π] using S.property
  obtain ⟨𝒱, h𝒱, φ, hfinite⟩ :=
    GrothendieckTopology.quasiCompactObject_finite_image_refinement_ofArrows
      (J := J) (U := W) hW Uᵢ π hsieve
  let T : Set S.Arrow := Set.range φ.α
  let ℓ : ℕ := Fintype.card T
  let e : Fin ℓ ≃ T := (Fintype.equivFin T).symm
  let Z : Fin ℓ → C := fun l ↦ Uᵢ (e.symm l).1
  have hZ : ∀ l : Fin ℓ, Z l ∈ B := by
    intro l
    exact hS (e.symm l).1
  have hcoverT :
      (J.over W).CoversTop (fun t : T ↦ Over.mk (π t.1)) := by
    -- The finite image subfamily still covers `W`.
    apply coversTopOver_of_coveringSieve (J := J)
      (Uᵢ := fun t : T ↦ Uᵢ t.1) (π := fun t ↦ π t.1)
    exact restrictedRangeFamilyCovering (J := J) (Uᵢ := Uᵢ) (π := π) h𝒱 φ
  have hcoverFin :
      (J.over W).CoversTop (fun l : Fin ℓ ↦ Over.mk (π (e.symm l).1)) := by
    -- Reindex the finite subtype cover by `Fin`.
    simpa [ℓ, e, Z] using
      coversTopOver_reindexEquiv (J := J)
        (Uᵢ := fun t : T ↦ Uᵢ t.1)
        (π := fun t : T ↦ π t.1)
        (e := e)
        (hcover := hcoverT)
  let δ :
      (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (Z l)) ⟶
        extensionByZeroStructureModule J 𝒪 W :=
    Sigma.desc (fun l : Fin ℓ ↦
      localizedStructureModuleExtensionByZeroMap J 𝒪 (π (e.symm l).1))
  have hδ : Epi δ := by
    -- The selected finite basis family still covers `W`, so its augmentation is epic.
    exact coverAugmentationEpi (J := J) (𝒪 := 𝒪)
      (Uᵢ := Z)
      (π := fun l ↦ π (e.symm l).1)
      (hcover := hcoverFin)
  exact ⟨ℓ, Z, hZ, δ, hδ⟩

/-- Helper for Lemma 18.30.9: after fixing an epimorphic target refinement `right`, the finite
source family `V` admits a finite basis cover whose summands already lift through `right`. -/
private theorem existsFiniteSourceLiftCover
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {m : ℕ}
    (V : Fin m → C)
    (hV : ∀ j : Fin m, V j ∈ B)
    {R T : ringedSiteModuleCategory J 𝒪}
    (right : R ⟶ T)
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶ T)
    [Epi right] :
    ∃ (s : Fin m → ℕ) (W : selectedCoverIndex s → C) (hW : ∀ a : selectedCoverIndex s, W a ∈ B)
      (leftSource :
        (∐ fun a : selectedCoverIndex s ↦ extensionByZeroStructureModule J 𝒪 (W a)) ⟶
          (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)))
      (topSource :
        (∐ fun a : selectedCoverIndex s ↦ extensionByZeroStructureModule J 𝒪 (W a)) ⟶ R),
        Epi leftSource ∧ topSource ≫ right = leftSource ≫ f := by
  let σ : ∀ j : Fin m,
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (V j))).obj T := fun j ↦
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (V j) T
      (Sigma.ι (fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) j ≫ f)
  choose sourceCover hsourceCover using
    fun j : Fin m ↦ existsCoverLiftOfEpiSection (J := J) (𝒪 := 𝒪) right (V j) (σ j)
  choose localLift hlocalLift using fun j : Fin m ↦ fun I : (sourceCover j).Arrow ↦ hsourceCover j I
  let hEnough : J.HasEnoughObjectsWithProperty (· ∈ B) :=
    (inferInstance : J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B)
      .hasEnoughObjectsWithProperty
  choose basisCover hbasisCover using
    fun j : Fin m ↦ fun I : (sourceCover j).Arrow ↦ hEnough I.Y
  let sourceBasisObject :
      ∀ j : Fin m, (Σ I : (sourceCover j).Arrow, (basisCover j I).Arrow) → C :=
    fun _ a ↦ a.2.Y
  let sourceBasisMap :
      ∀ j : Fin m, ∀ a : Σ I : (sourceCover j).Arrow, (basisCover j I).Arrow,
        sourceBasisObject j a ⟶ V j :=
    fun _ a ↦ a.2.f ≫ a.1.f
  have hsourceBasisObject :
      ∀ j : Fin m,
        ∀ a : Σ I : (sourceCover j).Arrow, (basisCover j I).Arrow,
          sourceBasisObject j a ∈ B := by
    intro j a
    exact hbasisCover j a.1 a.2
  have hbasisCovers :
      ∀ j : Fin m,
        ∀ I : (sourceCover j).Arrow,
          (J.over I.Y).CoversTop (fun A : (basisCover j I).Arrow ↦ Over.mk A.f) := by
    intro j I
    exact coverArrows_coversTop (J := J) (basisCover j I)
  have hsourceBasisCover :
      ∀ j : Fin m,
        (J.over (V j)).CoversTop
          (fun a : Σ I : (sourceCover j).Arrow, (basisCover j I).Arrow ↦
            Over.mk (sourceBasisMap j a)) := by
    intro j
    exact coversTopSigmaComp (J := J)
      (X := fun I : (sourceCover j).Arrow ↦ Over.mk I.f)
      (hX := coverArrows_coversTop (J := J) (sourceCover j))
      (Y := fun I : (sourceCover j).Arrow ↦ fun A : (basisCover j I).Arrow ↦ Over.mk A.f)
      (hY := hbasisCovers j)
  obtain ⟨s, κ, κ_injective, leftSource, hleftSource, hleftSource_ι⟩ :=
    by
      obtain ⟨s, κ, κ_injective, leftSource, hleftSource⟩ :=
        existsFiniteSelectedCoverEpi (J := J) (𝒪 := 𝒪) (B := B)
          (U := V) hV sourceBasisObject sourceBasisMap hsourceBasisCover
      exact ⟨s, κ, κ_injective, leftSource, hleftSource.1, hleftSource.2.2⟩
  let W : selectedCoverIndex s → C := selectedCoverObject s κ sourceBasisObject
  have hW : ∀ a : selectedCoverIndex s, W a ∈ B := by
    intro a
    exact hsourceBasisObject a.1 (κ a.1 a.2)
  let topLift :
      ∀ j : Fin m,
        ∀ a : Σ I : (sourceCover j).Arrow, (basisCover j I).Arrow,
          extensionByZeroStructureModule J 𝒪 (sourceBasisObject j a) ⟶ R :=
    fun j a ↦
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (sourceBasisObject j a) R).symm
        (sectionMap (J := J) (𝒪 := 𝒪) a.2.f R (localLift j a.1))
  have htopLift :
      ∀ j : Fin m,
        ∀ a : Σ I : (sourceCover j).Arrow, (basisCover j I).Arrow,
          topLift j a ≫ right =
            localizedStructureModuleExtensionByZeroMap J 𝒪 (sourceBasisMap j a) ≫
              Sigma.ι (fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) j ≫ f := by
    intro j a
    apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (sourceBasisObject j a) T).injective
    rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
      (J := J) (𝒪 := 𝒪) (β := topLift j a) (α := right)]
    dsimp [topLift]
    rw [Equiv.apply_symm_apply]
    rw [sectionMap_naturality (J := J) (𝒪 := 𝒪) (f := a.2.f) (α := right)
      (s := localLift j a.1)]
    rw [hlocalLift j a.1]
    rw [sectionMap_comp (J := J) (𝒪 := 𝒪) a.2.f a.1.f T (σ j)]
    simpa [sourceBasisMap, σ] using
      localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := sourceBasisMap j a) (ℱ := T)
        (α := Sigma.ι (fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) j ≫ f)
  let topSource :
      (∐ fun a : selectedCoverIndex s ↦ extensionByZeroStructureModule J 𝒪 (W a)) ⟶ R :=
    Sigma.desc (fun a : selectedCoverIndex s ↦ topLift a.1 (κ a.1 a.2))
  have hcomm : topSource ≫ right = leftSource ≫ f := by
    apply Limits.Sigma.hom_ext
    intro a
    dsimp [topSource]
    rw [Category.assoc, Limits.Sigma.ι_desc]
    rw [hleftSource_ι a, Category.assoc]
    exact htopLift a.1 (κ a.1 a.2)
  exact ⟨s, W, hW, leftSource, topSource, hleftSource, hcomm⟩

/-- Helper for Lemma 18.30.9: overlaps in a basis cover of a basis object are quasi-compact. -/
private theorem quasiCompactSelectedCoverOverlap
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {U₀ : C} (hU₀ : U₀ ∈ B)
    {r : ℕ} (Z : Fin r → C) (hZ : ∀ a : Fin r, Z a ∈ B)
    (π : ∀ a : Fin r, Z a ⟶ U₀)
    (hcover : (J.over U₀).CoversTop (fun a : Fin r ↦ Over.mk (π a)))
    (a b : Fin r) :
    J.QuasiCompactObject (Limits.pullback (π a) (π b)) := by
  let 𝒰 : SemiRepresentableFamily.Over U₀ := SemiRepresentableFamily.Over.ofArrows Z π
  have h𝒰 : 𝒰.toSieve ∈ J U₀ := by
    -- The slice-site covering condition is the same as the base-site covering sieve.
    exact coveringSieve_of_coversTopOver (J := J) (Uᵢ := Z) (π := π) hcover
  obtain ⟨hpair, hqcpair⟩ :=
    (inferInstance : J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B)
      .hasQuasiCompactPairwiseOverlaps hU₀ 𝒰 h𝒰 hZ
  letI : 𝒰.toPresieve.HasPairwisePullbacks := hpair
  -- The situation hypothesis already records quasi-compactness of these canonical overlaps.
  simpa [𝒰, SemiRepresentableFamily.Over.ofArrows] using hqcpair a b

/-- Helper for Lemma 18.30.9: every raw overlap in the selected finite target cover admits a
finite basis cover by basis objects. -/
private theorem existsFiniteBasisRefinementOfSelectedOverlaps
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a)))) :
    ∃ (s : selectedOverlapIndex r → ℕ)
      (Z : ∀ p : selectedOverlapIndex r, Fin (s p) → C)
      (hZ : ∀ p : selectedOverlapIndex r, ∀ l : Fin (s p), Z p l ∈ B)
      (δ : ∀ p : selectedOverlapIndex r,
        (∐ fun l : Fin (s p) ↦ extensionByZeroStructureModule J 𝒪 (Z p l)) ⟶
          extensionByZeroStructureModule J 𝒪
            (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p)),
        ∀ p : selectedOverlapIndex r, Epi (δ p) := by
  have hqc :
      ∀ p : selectedOverlapIndex r,
        J.QuasiCompactObject
          (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p) := by
    intro p
    rcases p with ⟨i, a, b⟩
    -- Each chosen overlap is quasi-compact by the basis hypothesis for the selected finite cover.
    exact quasiCompactSelectedCoverOverlap (J := J) (𝒪 := 𝒪) (B := B)
      (hU₀ := hU i)
      (Z := fun c : Fin (r i) ↦ Ucover i (κ i c))
      (hZ := fun c ↦ hUcover i (κ i c))
      (π := fun c ↦ π i (κ i c))
      (hcover := hcoverFin i)
      a b
  choose s Z hZ δ hδ using
    fun p : selectedOverlapIndex r ↦
      existsFiniteBasisCoverEpiOfQuasiCompact (J := J) (𝒪 := 𝒪) (B := B) (hW := hqc p)
  exact ⟨s, Z, hZ, δ, hδ⟩

/-- Helper for Lemma 18.30.9: the finite basis refinements of the raw overlaps assemble into one
epimorphism onto the raw overlap coproduct. -/
private theorem selectedOverlapRefinementEpi
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a))))
    (s : selectedOverlapIndex r → ℕ)
    (Z : ∀ p : selectedOverlapIndex r, Fin (s p) → C)
    (δ : ∀ p : selectedOverlapIndex r,
      (∐ fun l : Fin (s p) ↦ extensionByZeroStructureModule J 𝒪 (Z p l)) ⟶
        extensionByZeroStructureModule J 𝒪
          (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p))
    (hδ : ∀ p : selectedOverlapIndex r, Epi (δ p)) :
    ∃ (ρ :
      (∐ fun a : Σ p : selectedOverlapIndex r, Fin (s p) ↦
        extensionByZeroStructureModule J 𝒪 (Z a.1 a.2)) ⟶
          (∐ fun p : selectedOverlapIndex r ↦ extensionByZeroStructureModule J 𝒪
            (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p))),
      Epi ρ ∧
        ∀ a : Σ p : selectedOverlapIndex r, Fin (s p),
          Sigma.ι
              (fun b : Σ p : selectedOverlapIndex r, Fin (s p) ↦
                extensionByZeroStructureModule J 𝒪 (Z b.1 b.2))
              a ≫ ρ =
            δ a.1 ≫
              Sigma.ι
                (fun p : selectedOverlapIndex r ↦ extensionByZeroStructureModule J 𝒪
                  (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p))
                a.1 := by
  let ρ :
      (∐ fun a : Σ p : selectedOverlapIndex r, Fin (s p) ↦
        extensionByZeroStructureModule J 𝒪 (Z a.1 a.2)) ⟶
          (∐ fun p : selectedOverlapIndex r ↦ extensionByZeroStructureModule J 𝒪
            (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p)) :=
    Sigma.desc (fun a : Σ p : selectedOverlapIndex r, Fin (s p) ↦
      δ a.1 ≫
        Sigma.ι
          (fun p : selectedOverlapIndex r ↦ extensionByZeroStructureModule J 𝒪
            (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p))
          a.1)
  have hρ : Epi ρ := by
    refine ⟨?_⟩
    intro W α β hαβ
    apply Limits.Sigma.hom_ext
    intro p
    apply (cancel_epi (δ p)).1
    apply Limits.Sigma.hom_ext
    intro l
    have hcomp := congrArg
      (fun γ ↦
        Sigma.ι
            (fun a : Σ p : selectedOverlapIndex r, Fin (s p) ↦
              extensionByZeroStructureModule J 𝒪 (Z a.1 a.2))
            ⟨p, l⟩ ≫ γ)
      hαβ
    simpa [ρ, Category.assoc] using hcomp
  have hρ_ι :
      ∀ a : Σ p : selectedOverlapIndex r, Fin (s p),
        Sigma.ι
            (fun b : Σ p : selectedOverlapIndex r, Fin (s p) ↦
              extensionByZeroStructureModule J 𝒪 (Z b.1 b.2))
            a ≫ ρ =
          δ a.1 ≫
              Sigma.ι
                (fun p : selectedOverlapIndex r ↦ extensionByZeroStructureModule J 𝒪
                  (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p))
                a.1 := by
    intro a
    dsimp [ρ]
    rw [Limits.Sigma.ι_desc]
  exact ⟨ρ, hρ, hρ_ι⟩

/-- Helper for Lemma 18.30.9: the raw overlap component for a selected finite target cover is the
Čech difference between the two restrictions to the chosen pair of cover members. -/
private def selectedCoverRawOverlapTopComponent
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a))))
    (p : selectedOverlapIndex r) :
    extensionByZeroStructureModule J 𝒪
        (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p) ⟶
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) :=
  let _ :
      (selectedCoverFamily U κ Ucover π p.1).toPresieve.HasPairwisePullbacks :=
    selectedCoverPairwisePullbacks (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p.1
  localizedStructureModuleExtensionByZeroMap J 𝒪
      (Limits.pullback.fst (π p.1 (κ p.1 p.2.1)) (π p.1 (κ p.1 p.2.2))) ≫
    Sigma.ι
      (fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a))
      ⟨p.1, p.2.1⟩ -
    localizedStructureModuleExtensionByZeroMap J 𝒪
      (Limits.pullback.snd (π p.1 (κ p.1 p.2.1)) (π p.1 (κ p.1 p.2.2))) ≫
    Sigma.ι
      (fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a))
      ⟨p.1, p.2.2⟩

/-- Helper for Lemma 18.30.9: the raw overlap coproduct maps to the selected finite target cover by
the block-diagonal Čech differential. -/
private def selectedCoverRawOverlapTop
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a)))) :
    (∐ fun p : selectedOverlapIndex r ↦
      extensionByZeroStructureModule J 𝒪
        (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p)) ⟶
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) :=
  Sigma.desc (selectedCoverRawOverlapTopComponent (J := J) (𝒪 := 𝒪)
    (B := B) U hU Ucover π hUcover κ hcoverFin)

/-- Helper for Lemma 18.30.9: the raw overlap Čech differential lands in the kernel of the
selected finite augmentation `right`. -/
private theorem selectedCoverRawOverlapTop_comp_right
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a))))
    (right :
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)))
    (hright_ι :
      ∀ a : selectedCoverIndex r,
        Sigma.ι
            (fun b : selectedCoverIndex r ↦
              extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
            a ≫ right =
          localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 (κ a.1 a.2)) ≫
            Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) a.1) :
    selectedCoverRawOverlapTop (J := J) (𝒪 := 𝒪) (B := B) U hU Ucover π hUcover κ hcoverFin ≫
      right = 0 := by
  -- Each raw overlap component is the standard Čech difference, so its image under `right`
  -- cancels by the pullback condition.
  apply Limits.Sigma.hom_ext
  intro p
  rw [selectedCoverRawOverlapTop, Limits.Sigma.ι_desc_assoc]
  rw [selectedCoverRawOverlapTopComponent, Preadditive.sub_comp, sub_eq_zero]
  rcases p with ⟨i, a, b⟩
  let _ :
      (selectedCoverFamily U κ Ucover π i).toPresieve.HasPairwisePullbacks :=
    selectedCoverPairwisePullbacks (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin i
  calc
    localizedStructureModuleExtensionByZeroMap J 𝒪
        (Limits.pullback.fst (π i (κ i a)) (π i (κ i b))) ≫
          Sigma.ι
            (fun a : selectedCoverIndex r ↦
              extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a))
            ⟨i, a⟩ ≫
          right
        =
      localizedStructureModuleExtensionByZeroMap J 𝒪
          (Limits.pullback.fst (π i (κ i a)) (π i (κ i b))) ≫
        localizedStructureModuleExtensionByZeroMap J 𝒪 (π i (κ i a)) ≫
          Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) i := by
            rw [Category.assoc, hright_ι ⟨i, a⟩]
    _ =
      localizedStructureModuleExtensionByZeroMap J 𝒪
          (Limits.pullback.fst (π i (κ i a)) (π i (κ i b)) ≫ π i (κ i a)) ≫
        Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) i := by
          simp [Category.assoc]
    _ =
      localizedStructureModuleExtensionByZeroMap J 𝒪
          (Limits.pullback.snd (π i (κ i a)) (π i (κ i b)) ≫ π i (κ i b)) ≫
        Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) i := by
          rw [Limits.pullback.condition]
    _ =
      localizedStructureModuleExtensionByZeroMap J 𝒪
          (Limits.pullback.snd (π i (κ i a)) (π i (κ i b))) ≫
        localizedStructureModuleExtensionByZeroMap J 𝒪 (π i (κ i b)) ≫
          Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) i := by
          simp [Category.assoc]
    _ =
      localizedStructureModuleExtensionByZeroMap J 𝒪
          (Limits.pullback.snd (π i (κ i a)) (π i (κ i b))) ≫
        Sigma.ι
          (fun a : selectedCoverIndex r ↦
            extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a))
          ⟨i, b⟩ ≫
        right := by
          rw [Category.assoc, hright_ι ⟨i, b⟩]

/-- Helper for Lemma 18.30.9: if a morphism out of the selected finite target cover agrees on all
selected overlaps, then it factors through the selected augmentation `right`. -/
private theorem selectedCoverFactorThroughRight
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ} {K : Fin n → Type w}
    (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    {r : Fin n → ℕ} (κ : ∀ i : Fin n, Fin (r i) → K i)
    (right :
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) ⟶
          (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)))
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i (κ i a))))
    (hright_ι :
      ∀ a : selectedCoverIndex r,
        Sigma.ι
            (fun b : selectedCoverIndex r ↦
              extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
            a ≫ right =
          localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 (κ a.1 a.2)) ≫
            Sigma.ι (fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) a.1)
    {N : ringedSiteModuleCategory J 𝒪}
    (β :
      (∐ fun a : selectedCoverIndex r ↦
        extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) ⟶ N)
    (hβ :
      selectedCoverRawOverlapTop (J := J) (𝒪 := 𝒪) (B := B) U hU Ucover π hUcover κ hcoverFin ≫
        β = 0) :
    ∃ α : (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) ⟶ N,
      right ≫ α = β := by
  let sectionFamily :
      ∀ i : Fin n, ∀ a : Fin (r i),
        (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (Ucover i (κ i a)))).obj N :=
    fun i a ↦
      localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Ucover i (κ i a)) N
        (Sigma.ι
            (fun b : selectedCoverIndex r ↦
              extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
            ⟨i, a⟩ ≫
          β)
  have hcompat :
      ∀ i : Fin n,
        SheafOfModules.RingedSite.coverSectionCompatibility J 𝒪
            (fun a : Fin (r i) ↦ Ucover i (κ i a))
            (fun a ↦ π i (κ i a))
            N
            (sectionFamily i) = 0 := by
    intro i
    let _ :
        (selectedCoverFamily U κ Ucover π i).toPresieve.HasPairwisePullbacks :=
      selectedCoverPairwisePullbacks (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin i
    ext a b
    -- Evaluate the vanishing of the raw overlap map on the component `(i,a,b)`.
    have hcomp := congrArg
      (fun γ ↦
        Sigma.ι
            (fun p : selectedOverlapIndex r ↦
              extensionByZeroStructureModule J 𝒪
                (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin p))
            ⟨i, a, b⟩ ≫
          γ)
      hβ
    rw [selectedCoverRawOverlapTop, Limits.Sigma.ι_desc_assoc,
      selectedCoverRawOverlapTopComponent, Preadditive.sub_comp, sub_eq_zero] at hcomp
    have hsec := congrArg
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪
        (selectedOverlapObject (J := J) (B := B) U hU Ucover π hUcover κ hcoverFin ⟨i, a, b⟩) N)
      hcomp
    rw [localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := Limits.pullback.fst (π i (κ i a)) (π i (κ i b))) (ℱ := N)
        (α := Sigma.ι
          (fun b : selectedCoverIndex r ↦
            extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
          ⟨i, a⟩ ≫ β),
      localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := Limits.pullback.snd (π i (κ i a)) (π i (κ i b))) (ℱ := N)
        (α := Sigma.ι
          (fun b : selectedCoverIndex r ↦
            extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
          ⟨i, b⟩ ≫ β)] at hsec
    change
      sectionMap (J := J) (𝒪 := 𝒪)
          (Limits.pullback.fst (π i (κ i a)) (π i (κ i b))) N (sectionFamily i a) -
        sectionMap (J := J) (𝒪 := 𝒪)
          (Limits.pullback.snd (π i (κ i a)) (π i (κ i b))) N (sectionFamily i b) = 0
    exact sub_eq_zero.mpr hsec
  choose t ht using fun i : Fin n ↦ by
    rcases SheafOfModules.RingedSite.coverSectionCechExact (J := J) (𝒪 := 𝒪)
      (U := U i)
      (Uᵢ := fun a : Fin (r i) ↦ Ucover i (κ i a))
      (π := fun a ↦ π i (κ i a))
      (hcoverFin i)
      N with ⟨_, hexact⟩
    exact hexact (hcompat i)
  let αi :
      ∀ i : Fin n, extensionByZeroStructureModule J 𝒪 (U i) ⟶ N :=
    fun i ↦ (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) N).symm (t i)
  have hαi :
      ∀ i : Fin n, ∀ a : Fin (r i),
        localizedStructureModuleExtensionByZeroMap J 𝒪 (π i (κ i a)) ≫ αi i =
          Sigma.ι
              (fun b : selectedCoverIndex r ↦
                extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover b))
              ⟨i, a⟩ ≫
            β := by
    intro i a
    apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (Ucover i (κ i a)) N).injective
    rw [localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
      (f := π i (κ i a)) (ℱ := N) (α := αi i)]
    dsimp [αi]
    rw [Equiv.apply_symm_apply]
    exact congrFun (ht i) a
  let α :
      (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i)) ⟶ N :=
    Sigma.desc αi
  refine ⟨α, ?_⟩
  -- Check the factorization on each selected summand of the finite cover.
  apply Limits.Sigma.hom_ext
  intro a
  rw [Category.assoc, hright_ι a, Category.assoc, Limits.Sigma.ι_desc]
  exact hαi a.1 a.2

-- Proof sketch: apply Lemma `18.30.2` to each quasi-compact `U_i` to choose finite subcovers of
-- the given coverings. Use surjectivity of the resulting right vertical map to lift the given
-- morphism from `\bigoplus_j j_{V_j!}\mathcal O_{V_j}` after refining the `V_j` by basis covers,
-- then use the exact sequences from Lemma `18.30.2` for the chosen `U_i`- and `V_j`-covers.
-- Finally refine the quasi-compact overlaps once more by basis objects to obtain the top row with
-- all `W_l` in `B`; the induced map on cokernels is then an isomorphism.
/-- Lemma 18.30.9: in Situation `18.30.5`, a morphism
`\bigoplus_j j_{V_j!}\mathcal O_{V_j} \to \bigoplus_i j_{U_i!}\mathcal O_{U_i}` with `U_i, V_j ∈ B`
and coverings `\{U_{ik} \to U_i\}` by objects of `B` admits finite selected subfamilies of the
given covers and a finite family `W_l ∈ B` fitting into a commutative square whose induced map on
cokernels is an isomorphism. Here `κ i : Fin (r i) → K i` is an injective enumeration of the
selected finite subset of the index set `K i`. -/
theorem exists_finite_basis_refinement_inducing_cokernel_iso
    (B : Set C)
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n m : ℕ}
    (U : Fin n → C) (V : Fin m → C)
    (hU : ∀ i : Fin n, U i ∈ B)
    (hV : ∀ j : Fin m, V j ∈ B)
    {K : Fin n → Type w}
    (Ucover : ∀ i : Fin n, K i → C)
    (π : ∀ i : Fin n, ∀ k : K i, Ucover i k ⟶ U i)
    (hUcover : ∀ i : Fin n, ∀ k : K i, Ucover i k ∈ B)
    (hcover : ∀ i : Fin n,
      (J.over (U i)).CoversTop (fun k : K i ↦ Over.mk (π i k)))
    (f :
      (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ extensionByZeroStructureModule J 𝒪 (U i))) :
    Nonempty
      (FiniteBasisRefinementInducingCokernelIsoWitness J 𝒪 B U V Ucover f) := by
  -- Route correction: the first missing premise from the previous attempt was the actual
  -- epimorphic finite target refinement. We now construct that `right` map directly from finite
  -- selected subcovers of the given `Ucover i`.
  obtain ⟨r, κ, κ_injective, right, hright, hcoverFin, hright_ι⟩ := by
    obtain ⟨r, κ, κ_injective, right, hright⟩ :=
      existsFiniteSelectedCoverEpi (J := J) (𝒪 := 𝒪) (B := B)
        (U := U) hU Ucover π hcover
    exact ⟨r, κ, κ_injective, right, hright.1, hright.2.1, hright.2.2⟩
  letI : Epi right := hright
  -- The selected finite right-hand refinement is in place. We also now have the finite source
  -- basis cover that already lifts through `right`.
  obtain ⟨s, Wsource, hWsource, leftSource, topSource, hleftSource, hsourceComm⟩ :=
    existsFiniteSourceLiftCover (J := J) (𝒪 := 𝒪) (B := B)
      (V := V) hV right f
  -- The raw overlaps in the selected finite target cover can now be refined once more by a
  -- finite family of basis objects.
  obtain ⟨soverlap, Zoverlap, hZoverlap, δoverlap, hδoverlap⟩ :=
    existsFiniteBasisRefinementOfSelectedOverlaps (J := J) (𝒪 := 𝒪) (B := B)
      (U := U) hU Ucover π hUcover κ hcoverFin
  -- Package the individual overlap refinements into one epimorphism onto the full raw overlap
  -- coproduct; this isolates the remaining blocker to the exactness bridge from overlaps to the
  -- kernel of `right`.
  obtain ⟨ρoverlap, hρoverlap, hρoverlap_ι⟩ :=
    selectedOverlapRefinementEpi (J := J) (𝒪 := 𝒪)
      (B := B) U hU Ucover π hUcover κ hcoverFin soverlap Zoverlap δoverlap hδoverlap
  letI : Epi leftSource := hleftSource
  letI : Epi ρoverlap := hρoverlap
  let rawOverlapTop :=
    selectedCoverRawOverlapTop (J := J) (𝒪 := 𝒪) (B := B) U hU Ucover π hUcover κ hcoverFin
  have hrawComm : rawOverlapTop ≫ right = 0 := by
    -- The raw selected-overlap Čech differential lands in the kernel of the finite augmentation.
    exact selectedCoverRawOverlapTop_comp_right (J := J) (𝒪 := 𝒪)
      (B := B) U hU Ucover π hUcover κ hcoverFin right hright_ι
  let overlapBasisTop := ρoverlap ≫ rawOverlapTop
  have hoverlapBasisComm : overlapBasisTop ≫ right = 0 := by
    -- Refining the raw overlaps by basis objects preserves the kernel relation.
    simpa [overlapBasisTop, Category.assoc] using congrArg (fun γ ↦ ρoverlap ≫ γ) hrawComm
  let finalIndex := Sum (selectedCoverIndex s) (Σ p : selectedOverlapIndex r, Fin (soverlap p))
  let Wsum : finalIndex → C := fun x ↦
    match x with
    | Sum.inl a => Wsource a
    | Sum.inr b => Zoverlap b.1 b.2
  let topSum :
      (∐ fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) ⟶
        (∐ fun a : selectedCoverIndex r ↦
          extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) :=
    Sigma.desc (fun x : finalIndex ↦
      match x with
      | Sum.inl a =>
          Sigma.ι (fun a : selectedCoverIndex s ↦ extensionByZeroStructureModule J 𝒪 (Wsource a)) a ≫
            topSource
      | Sum.inr b =>
          Sigma.ι
              (fun b : Σ p : selectedOverlapIndex r, Fin (soverlap p) ↦
                extensionByZeroStructureModule J 𝒪 (Zoverlap b.1 b.2))
              b ≫
            overlapBasisTop)
  let leftSum :
      (∐ fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) ⟶
        (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) :=
    Sigma.desc (fun x : finalIndex ↦
      match x with
      | Sum.inl a =>
          Sigma.ι (fun a : selectedCoverIndex s ↦ extensionByZeroStructureModule J 𝒪 (Wsource a)) a ≫
            leftSource
      | Sum.inr _ => 0)
  have htopSumComm : topSum ≫ right = leftSum ≫ f := by
    -- The source branch commutes by construction, while the overlap branch maps trivially through
    -- `right`.
    apply Limits.Sigma.hom_ext
    intro x
    cases x with
    | inl a =>
        have hcomp := congrArg
          (fun γ ↦
            Sigma.ι (fun a : selectedCoverIndex s ↦ extensionByZeroStructureModule J 𝒪 (Wsource a))
              a ≫ γ)
          hsourceComm
        simpa [topSum, leftSum, Category.assoc] using hcomp
    | inr b =>
        simp [topSum, leftSum, overlapBasisTop, hoverlapBasisComm, Category.assoc]
  let g := right ≫ cokernel.π f
  have htopSumZero : topSum ≫ g = 0 := by
    -- The final top row lands in the kernel of `right ≫ cokernel.π f`.
    rw [g, Category.assoc, htopSumComm, Category.assoc, cokernel.condition]
  let S : ShortComplex (ringedSiteModuleCategory J 𝒪) :=
    ShortComplex.mk topSum g htopSumZero
  have hSExact : S.Exact := by
    -- Check exactness after applying `Hom(-, N)` to reduce the proof to explicit factorization.
    refine (CategoryTheory.epi_exact_iff_hom_into_exact S).2 ?_
    intro N
    constructor
    · let T : ShortComplex AddCommGrpCat := S.op.map (preadditiveYoneda.obj N)
      refine (CategoryTheory.ShortComplex.ab_exact_iff_function_exact T).2 ?_
      intro β hβ
      have hsourceβ : topSource ≫ β = 0 := by
        apply Limits.Sigma.hom_ext
        intro a
        have hcomp := congrArg
          (fun γ ↦
            Sigma.ι
                (fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x))
                (Sum.inl a) ≫
              γ)
          hβ
        simpa [topSum, Category.assoc] using hcomp
      have hoverlapβ : overlapBasisTop ≫ β = 0 := by
        apply Limits.Sigma.hom_ext
        intro b
        have hcomp := congrArg
          (fun γ ↦
            Sigma.ι
                (fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x))
                (Sum.inr b) ≫
              γ)
          hβ
        simpa [topSum, Category.assoc] using hcomp
      have hrawβ : rawOverlapTop ≫ β = 0 := by
        apply (cancel_epi ρoverlap).1
        simpa [overlapBasisTop, Category.assoc] using hoverlapβ
      obtain ⟨θ, hθ⟩ :=
        selectedCoverFactorThroughRight (J := J) (𝒪 := 𝒪)
          (B := B) U hU Ucover π hUcover κ right hcoverFin hright_ι β hrawβ
      have hfθ : f ≫ θ = 0 := by
        apply (cancel_epi leftSource).1
        calc
          leftSource ≫ f ≫ θ = topSource ≫ right ≫ θ := by
            rw [← hsourceComm]
            simp [Category.assoc]
          _ = topSource ≫ β := by rw [hθ]
          _ = 0 := hsourceβ
      refine ⟨cokernel.desc f θ hfθ, ?_⟩
      calc
        g ≫ cokernel.desc f θ hfθ = right ≫ (cokernel.π f ≫ cokernel.desc f θ hfθ) := by
          simp [g, Category.assoc]
        _ = right ≫ θ := by rw [cokernel.π_desc]
        _ = β := hθ
    · let T : ShortComplex AddCommGrpCat := S.op.map (preadditiveYoneda.obj N)
      refine (AddCommGrpCat.mono_iff_injective T.f).2 ?_
      intro χ₁ χ₂ hχ
      change g ≫ χ₁ = g ≫ χ₂ at hχ
      exact (cancel_epi g).1 hχ
  have hkernelLiftEpi : Epi (kernel.lift g topSum htopSumZero) := by
    -- Exactness of the final short complex identifies the kernel lift as an epimorphism.
    simpa [S] using (ShortComplex.exact_iff_epi_kernel_lift (S := S)).1 hSExact
  let ℓ : ℕ := Fintype.card finalIndex
  let e : finalIndex ≃ Fin ℓ := Fintype.equivFin finalIndex
  let W : Fin ℓ → C := fun l ↦ Wsum (e.symm l)
  have hW : ∀ l : Fin ℓ, W l ∈ B := by
    intro l
    rcases e.symm l with a | b
    · exact hWsource a
    · exact hZoverlap b.1 b.2
  let reindexHom :
      (∐ fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) ⟶
        (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) :=
    Sigma.map' e (fun x ↦ 𝟙 _)
  let reindexInv :
      (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
        (∐ fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) :=
    Sigma.map' e.symm (fun l ↦ 𝟙 _)
  let reindexIso :
      (∐ fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) ≅
        (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) :=
    { hom := reindexHom
      inv := reindexInv
      hom_inv_id := by
        apply Limits.Sigma.hom_ext
        intro x
        calc
          Sigma.ι (fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) x ≫
              reindexHom ≫ reindexInv =
            Sigma.ι (fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) (e x) ≫
              reindexInv := by
                simpa [reindexHom, Category.assoc] using
                  congrArg (fun γ ↦ γ ≫ reindexInv)
                    (Sigma.ι_comp_map' (p := e) (q := fun x ↦ 𝟙 _) x)
          _ =
            Sigma.ι (fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x))
              (e.symm (e x)) := by
                simpa [reindexInv, W, Category.assoc] using
                  (Sigma.ι_comp_map' (p := e.symm) (q := fun l ↦ 𝟙 _) (e x))
          _ =
            Sigma.ι (fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x)) x := by
              simp
      inv_hom_id := by
        apply Limits.Sigma.hom_ext
        intro l
        calc
          Sigma.ι (fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) l ≫
              reindexInv ≫ reindexHom =
            Sigma.ι (fun x : finalIndex ↦ extensionByZeroStructureModule J 𝒪 (Wsum x))
              (e.symm l) ≫
              reindexHom := by
                simpa [reindexInv, W, Category.assoc] using
                  congrArg (fun γ ↦ γ ≫ reindexHom)
                    (Sigma.ι_comp_map' (p := e.symm) (q := fun l ↦ 𝟙 _) l)
          _ =
            Sigma.ι (fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l))
              (e (e.symm l)) := by
                simpa [reindexHom, W, Category.assoc] using
                  (Sigma.ι_comp_map' (p := e) (q := fun x ↦ 𝟙 _) (e.symm l))
          _ = Sigma.ι (fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) l := by
              simp }
  let top :
      (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
        (∐ fun a : selectedCoverIndex r ↦
          extensionByZeroStructureModule J 𝒪 (selectedCoverObject r κ Ucover a)) :=
    reindexInv ≫ topSum
  let left :
      (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
        (∐ fun j : Fin m ↦ extensionByZeroStructureModule J 𝒪 (V j)) :=
    reindexInv ≫ leftSum
  have htopComm : top ≫ right = left ≫ f := by
    -- Reindexing the domain does not change the commutative square.
    simpa [top, left, Category.assoc] using congrArg (fun γ ↦ reindexInv ≫ γ) htopSumComm
  let ψ :
      (∐ fun l : Fin ℓ ↦ extensionByZeroStructureModule J 𝒪 (W l)) ⟶
        kernel (right ≫ cokernel.π f) :=
    reindexInv ≫ kernel.lift g topSum htopSumZero
  letI : Epi ψ := by
    dsimp [ψ]
    infer_instance
  have hψComm : (ψ ≫ kernel.ι (right ≫ cokernel.π f)) ≫ right = left ≫ f := by
    -- The reindexed kernel cover has the same top map into the selected target refinement.
    calc
      (ψ ≫ kernel.ι (right ≫ cokernel.π f)) ≫ right =
          reindexInv ≫ topSum ≫ right := by
            simp [ψ, g, Category.assoc]
      _ = left ≫ f := htopComm
  have hiso :
      IsIso (cokernel.map top f left right htopComm) := by
    -- The final reindexed kernel cover is epi, so the induced cokernel comparison is an
    -- isomorphism by the standard kernel-cover argument.
    exact isIso_cokernelMap_of_epiKernelCover (J := J) (𝒪 := 𝒪)
      (f := f) (right := right) (ψ := ψ) (left := left) hψComm
  exact ⟨{
    r := r
    κ := κ
    κ_injective := κ_injective
    ℓ := ℓ
    W := W
    hW := hW
    top := top
    left := left
    right := right
    comm := htopComm
    isIso_cokernel_map := hiso
  }⟩

end SheafOfModules.RingedSite
