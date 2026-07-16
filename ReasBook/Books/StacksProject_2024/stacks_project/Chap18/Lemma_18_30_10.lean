import Mathlib
import StacksProject_2024.stacks_project.Chap18.Lemma_18_28_7
import StacksProject_2024.stacks_project.Chap18.Lemma_18_30_9
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.stacks_project.Chap18.Situation_18_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open _root_.SheafOfModules.RingedSite
  (ringedSiteModuleCategory localizedStructureModuleExtensionByZero)

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Helper for Lemma 18.30.10: local fallback owner for the finite basis cokernel-presentation
predicate while the upstream owner file `Lemma_18_30_7` is not importable in this workspace. -/
abbrev HasFiniteBasisConstructibleModuleCokernelPresentation
    (ℱ : Mod) : Prop :=
  ∃ (n m : ℕ) (U : Fin n → C) (V : Fin m → C),
    ∃ (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
      (_ : ℱ ≅ cokernel f),
        (∀ i, U i ∈ B) ∧
          ∀ j, V j ∈ B

/-- Helper for Lemma 18.30.10: an epimorphism together with an epimorphic cover of its kernel
packages the target as the cokernel of the composite map. This is the local fallback copy of the
standard `18.30.7` owner theorem needed by this item. -/
lemma cokernelIso_of_epi_kernelCover
    {A K X : Mod} (φ : A ⟶ X) (ψ : K ⟶ kernel φ)
    [Epi φ] [Epi ψ] :
    X ≅ cokernel (ψ ≫ kernel.ι φ) := by
  let S : ShortComplex Mod :=
    ShortComplex.mk (ψ ≫ kernel.ι φ) φ (by simp [Category.assoc, kernel.condition])
  let T : ShortComplex Mod :=
    ShortComplex.mk (kernel.ι φ) φ (by simp)
  have hTExact : T.Exact := by
    -- The canonical kernel row is exact by the kernel universal property.
    simpa [T] using ShortComplex.exact_of_f_is_kernel T (kernelIsKernel φ)
  let η : S ⟶ T :=
    { τ₁ := ψ
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, T, Category.assoc]
      comm₂₃ := by simp [S, T] }
  have hSExact : S.Exact := by
    -- Exactness descends across the epimorphic left comparison `ψ`.
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono η).2 hTExact
  obtain ⟨hcolim⟩ := (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hSExact, inferInstance⟩
  -- Compare the explicit cokernel point with the chosen cokernel of `ψ ≫ kernel.ι φ`.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (ψ ≫ kernel.ι φ)) hcolim

/-- Helper for Lemma 18.30.10: an epimorphism of module sheaves yields a covering family on which
any chosen section lifts locally. -/
lemma existsCoverLiftOfEpiSection
    {M N : Mod} (p : M ⟶ N) [Epi p]
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
  -- The chosen local preimage restricts to the requested section by construction of the image
  -- sieve cover.
  simpa [sectionMap] using Presheaf.app_localPreimage p'.hom s I.f I.hf

/-- Helper for Lemma 18.30.10: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    {W : C} {ℱ 𝒢 : Mod}
    (β : localizedStructureModuleExtensionByZero 𝒪 W ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ β) := by
  -- The owner equivalence is defined by target-functorial constructions, so this naturality is
  -- definitional.
  rfl

/-- Helper for Lemma 18.30.10: restriction of sections commutes with applying a module morphism.
-/
private theorem sectionMap_naturality
    {V W : C} {ℱ 𝒢 : Mod}
    (f : V ⟶ W) (α : ℱ ⟶ 𝒢)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).obj ℱ) :
    ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α) (sectionMap J 𝒪 f ℱ s) =
      sectionMap J 𝒪 f 𝒢
        (((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α) s) := by
  -- Naturality of `α` on the underlying sheaf gives the commutative restriction square.
  change ConcreteCategory.hom (α.val.app (op V))
      (ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1.map f.op) s) =
    ConcreteCategory.hom (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj 𝒢).1.map f.op)
      (ConcreteCategory.hom (α.val.app (op W)) s)
  simpa using ConcreteCategory.congr_hom (α.val.naturality f.op) s

/-- Helper for Lemma 18.30.10: precomposing with `localizedStructureModuleExtensionByZeroMap`
corresponds to restricting the associated section. -/
private theorem localizedStructureModuleExtensionByZeroMap_homEquiv
    {V W : C} (f : V ⟶ W) (ℱ : Mod)
    (α : localizedStructureModuleExtensionByZero 𝒪 W ⟶ ℱ) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ
        (localizedStructureModuleExtensionByZeroMap J 𝒪 f ≫ α) =
      sectionMap J 𝒪 f ℱ
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α) := by
  have hα : localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W ℱ α =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op W)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 W
          (localizedStructureModuleExtensionByZero 𝒪 W) (𝟙 _)) := by
    -- The owner equivalence is natural in the target, so the universal section transports
    -- directly across `α`.
    simpa using
      localizedStructureModuleExtensionByZero_homEquiv_naturality_right (J := J) (𝒪 := 𝒪)
        (β := 𝟙 (localizedStructureModuleExtensionByZero 𝒪 W)) (α := α)
  -- Route correction: reuse target-functoriality of the owner equivalence instead of unfolding
  -- the slice-site adjunction by hand.
  rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right (J := J) (𝒪 := 𝒪)
    (β := localizedStructureModuleExtensionByZeroMap J 𝒪 f) (α := α)]
  rw [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroMap]
  rw [Equiv.apply_symm_apply]
  rw [hα]
  exact sectionMap_naturality (J := J) (𝒪 := 𝒪) f α _

/-- Helper for Lemma 18.30.10: a slice-site cover of the terminal object is the same as the base
covering sieve generated by the underlying arrows. -/
private theorem overSieveOfObjectsEqOfArrows
    {ι : Type u} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U) :
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

/-- Helper for Lemma 18.30.10: a slice-site `CoversTop` hypothesis yields the corresponding
covering sieve on the base object. -/
private theorem coveringSieve_of_coversTopOver
    {ι : Type u} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : (J.over U).CoversTop (fun i : ι ↦ Over.mk (π i))) :
    Sieve.ofArrows Uᵢ π ∈ J U := by
  -- Rewrite the slice cover of the terminal object into the corresponding base-site sieve.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)] at hcover
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows
    (Uᵢ := Uᵢ) (π := π)] at hcover
  exact hcover

/-- Helper for Lemma 18.30.10: a covering refinement landing in a finite-image subfamily still
covers the base object. -/
private theorem restrictedRangeFamilyCovering
    {ι : Type u} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    {𝒱 : SemiRepresentableFamily.Over U}
    (h𝒱 : 𝒱.toSieve ∈ J U)
    (φ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows Uᵢ π) :
    Sieve.ofArrows (fun i : Set.range φ.α ↦ Uᵢ i.1) (fun i ↦ π i.1) ∈ J U := by
  let ψ : 𝒱 ⟶ SemiRepresentableFamily.Over.ofArrows
      (fun i : Set.range φ.α ↦ Uᵢ i.1) (fun i ↦ π i.1) :=
    { α := fun i ↦ ⟨φ.α i, ⟨i, rfl⟩⟩
      f := fun i ↦ φ.f i }
  -- The restricted subtype family covers because the refining family factors through it.
  have hrestricted :
      (SemiRepresentableFamily.Over.ofArrows
        (fun i : Set.range φ.α ↦ Uᵢ i.1) (fun i ↦ π i.1)).toSieve ∈ J U := by
    exact J.superset_covering (SemiRepresentableFamily.Over.toSieve_le_of_hom ψ) h𝒱
  simpa using hrestricted

/-- Helper for Lemma 18.30.10: a covering sieve on a family converts back to the corresponding
slice-site `CoversTop` statement. -/
private theorem coversTopOver_of_coveringSieve
    {ι : Type u} {U : C} (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    {S : Set ι}
    (hcover : Sieve.ofArrows (fun i : S ↦ Uᵢ i.1) (fun i ↦ π i.1) ∈ J U) :
    (J.over U).CoversTop (fun i : S ↦ Over.mk (π i.1)) := by
  -- Rewrite the ordinary covering sieve back into the slice-site terminal cover.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows
    (Uᵢ := fun i : S ↦ Uᵢ i.1) (π := fun i ↦ π i.1)]
  exact hcover

/-- Helper for Lemma 18.30.10: reindexing a covering family by an equivalence preserves the
resulting slice-site cover. -/
private theorem coversTopOver_reindexEquiv
    {ι ι' : Type u} {U : C}
    (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U) (e : ι ≃ ι')
    (hcover : (J.over U).CoversTop (fun i : ι ↦ Over.mk (π i))) :
    (J.over U).CoversTop (fun i : ι' ↦ Over.mk (π (e.symm i))) := by
  -- Reindexing does not change the underlying covering sieve.
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

/-- Helper for Lemma 18.30.10: the arrows of a cover form a `CoversTop` family on the same base
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

/-- Helper for Lemma 18.30.10: composing a slice-site cover with covers of its members yields a
sigma-indexed slice-site cover of the base object. -/
private theorem coversTopSigmaComp
    {U : C} {ι : Type u} {X : ι → Over U}
    (hX : (J.over U).CoversTop X)
    {κ : ι → Type u} {Y : ∀ i : ι, κ i → Over (X i).left}
    (hY : ∀ i : ι, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Sigma κ ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Pass to ordinary covering sieves and use transitivity there.
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
  have hR : R ∈ J U := by
    refine J.transitive hSX ?_
    intro V f hf
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

/-- Helper for Lemma 18.30.10: successive restriction maps compose as restriction along the
composite arrow. -/
private theorem sectionMap_comp
    {V W X : C} (f : V ⟶ W) (g : W ⟶ X) (ℱ : Mod)
    (s : (SheafOfModules.evaluation (ringSheaf J 𝒪) (op X)).obj ℱ) :
    sectionMap (J := J) (𝒪 := 𝒪) f ℱ (sectionMap (J := J) (𝒪 := 𝒪) g ℱ s) =
      sectionMap (J := J) (𝒪 := 𝒪) (f ≫ g) ℱ s := by
  -- Restriction is just the presheaf action, so composition is functoriality of `map`.
  let F := ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).1
  change ConcreteCategory.hom (F.map f.op) (ConcreteCategory.hom (F.map g.op) s) =
    ConcreteCategory.hom (F.map ((f ≫ g).op)) s
  rw [op_comp, Functor.map_comp]
  rfl

/-- Helper for Lemma 18.30.10: the augmentation map attached to a covering family of basis
objects is epic. -/
private theorem coverAugmentationEpi
    {ι : Type u} {U : C}
    (Uᵢ : ι → C) (π : ∀ i : ι, Uᵢ i ⟶ U)
    (hcover : (J.over U).CoversTop (fun i : ι ↦ Over.mk (π i))) :
    Epi
      (Sigma.desc
        (fun i : ι ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 (π i)) :
        (∐ fun i : ι ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) ⟶
          localizedStructureModuleExtensionByZero 𝒪 U) := by
  let δ :
      (∐ fun i : ι ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ i)) ⟶
        localizedStructureModuleExtensionByZero 𝒪 U :=
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
    -- Equality on a covering family forces equality of the corresponding global slice section.
    apply hcover.sections_ext F
    intro i
    rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
      (f := π i) (ℱ := ℱ)
      (s := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ α)]
    rw [overSectionsEquivEvaluation_symm_apply_cover (J := J) (𝒪 := 𝒪)
      (f := π i) (ℱ := ℱ)
      (s := localizedStructureModuleExtensionByZero_homEquiv J 𝒪 U ℱ β)]
    have hcomp := congrArg
      (fun γ ↦ Sigma.ι (fun j : ι ↦ localizedStructureModuleExtensionByZero 𝒪 (Uᵢ j)) i ≫ γ)
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

/-- Helper for Lemma 18.30.10: a morphism from a finite coproduct of basis generators can be
refined to a finite basis cover on which it lifts through any epimorphism, and the selected finite
cover still covers each original basis object. -/
lemma existsFiniteBasisLiftCoverOfEpi
    [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]
    {n : ℕ}
    (U : Fin n → C)
    (hU : ∀ i : Fin n, U i ∈ B)
    {R T : Mod}
    (q :
      (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ T)
    (e : R ⟶ T) [Epi e] :
    ∃ (r : Fin n → ℕ)
      (W : ∀ i : Fin n, Fin (r i) → C)
      (π : ∀ i : Fin n, ∀ a : Fin (r i), W i a ⟶ U i)
      (hW : ∀ i : Fin n, ∀ a : Fin (r i), W i a ∈ B)
      (hcoverFin : ∀ i : Fin n,
        (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i a)))
      (left :
        (∐ fun a : Σ i : Fin n, Fin (r i) ↦
          localizedStructureModuleExtensionByZero 𝒪 (W a.1 a.2)) ⟶
          (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
      (lift :
        (∐ fun a : Σ i : Fin n, Fin (r i) ↦
          localizedStructureModuleExtensionByZero 𝒪 (W a.1 a.2)) ⟶
          R),
        Epi left ∧
          (∀ a : Σ i : Fin n, Fin (r i),
            Sigma.ι
                (fun b : Σ i : Fin n, Fin (r i) ↦
                  localizedStructureModuleExtensionByZero 𝒪 (W b.1 b.2))
                a ≫
              left =
                localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 a.2) ≫
                  Sigma.ι
                    (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
                    a.1) ∧
          lift ≫ e = left ≫ q := by
  let σ : ∀ i : Fin n,
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).obj T := fun i ↦
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (U i) T
      (Sigma.ι (fun j : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U j)) i ≫ q)
  choose sourceCover hsourceCover using
    fun i : Fin n ↦ existsCoverLiftOfEpiSection (J := J) (𝒪 := 𝒪) e (U i) (σ i)
  choose localLift hlocalLift using
    fun i : Fin n ↦ fun I : (sourceCover i).Arrow ↦ hsourceCover i I
  let hEnough : J.HasEnoughObjectsWithProperty (· ∈ B) :=
    (inferInstance : J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B)
      .hasEnoughObjectsWithProperty
  choose basisCover hbasisCover using
    fun i : Fin n ↦ fun I : (sourceCover i).Arrow ↦ hEnough I.Y
  let sourceBasisObject :
      ∀ i : Fin n, (Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow) → C :=
    fun _ a ↦ a.2.Y
  let sourceBasisMap :
      ∀ i : Fin n,
        ∀ a : Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow,
          sourceBasisObject i a ⟶ U i :=
    fun _ a ↦ a.2.f ≫ a.1.f
  have hsourceBasisObject :
      ∀ i : Fin n,
        ∀ a : Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow,
          sourceBasisObject i a ∈ B := by
    intro i a
    exact hbasisCover i a.1 a.2
  have hsourceBasisCover :
      ∀ i : Fin n,
        (J.over (U i)).CoversTop
          (fun a : Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow ↦
            Over.mk (sourceBasisMap i a)) := by
    intro i
    -- Compose the chosen cover of `U i` with basis covers of each member.
    exact coversTopSigmaComp (J := J)
      (X := fun I : (sourceCover i).Arrow ↦ Over.mk I.f)
      (hX := coverArrows_coversTop (J := J) (sourceCover i))
      (Y := fun I : (sourceCover i).Arrow ↦ fun A : (basisCover i I).Arrow ↦ Over.mk A.f)
      (hY := fun I ↦ coverArrows_coversTop (J := J) (basisCover i I))
  let hqc : ∀ i : Fin n, J.QuasiCompactObject (U i) := fun i ↦
    HasQuasiCompactBasisWithQuasiCompactFiberProducts.quasiCompactObject
      (J := J) (B := B) (hU i)
  choose S hSfinite hScover using
    fun i : Fin n ↦ by
      have hsieve :
          Sieve.ofArrows (sourceBasisObject i) (sourceBasisMap i) ∈ J (U i) :=
        coveringSieve_of_coversTopOver (J := J)
          (Uᵢ := sourceBasisObject i) (π := sourceBasisMap i) (hsourceBasisCover i)
      obtain ⟨𝒱, h𝒱, φ, hfinite⟩ :=
        GrothendieckTopology.quasiCompactObject_finite_image_refinement_ofArrows
          (hU := hqc i) (Uᵢ := sourceBasisObject i) (π := sourceBasisMap i) hsieve
      refine ⟨Set.range φ.α, hfinite, ?_⟩
      apply coversTopOver_of_coveringSieve (J := J)
        (Uᵢ := sourceBasisObject i) (π := sourceBasisMap i)
      exact restrictedRangeFamilyCovering (J := J)
        (Uᵢ := sourceBasisObject i) (π := sourceBasisMap i) h𝒱 φ
  let r : Fin n → ℕ := fun i ↦ Fintype.card (S i)
  let κ :
      ∀ i : Fin n, Fin (r i) →
        Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow :=
    fun i a ↦ ((Fintype.equivFin (S i)).symm a).1
  let W : ∀ i : Fin n, Fin (r i) → C := fun i a ↦ sourceBasisObject i (κ i a)
  let π : ∀ i : Fin n, ∀ a : Fin (r i), W i a ⟶ U i := fun i a ↦ sourceBasisMap i (κ i a)
  have hW : ∀ i : Fin n, ∀ a : Fin (r i), W i a ∈ B := by
    intro i a
    exact hsourceBasisObject i (κ i a)
  have hcoverFin :
      ∀ i : Fin n,
        (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i a)) := by
    intro i
    simpa [r, κ, W, π] using
      coversTopOver_reindexEquiv (J := J)
        (Uᵢ := fun k : S i ↦ sourceBasisObject i k.1)
        (π := fun k : S i ↦ sourceBasisMap i k.1)
        (e := Fintype.equivFin (S i))
        (hcover := hScover i)
  let left :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (W a.1 a.2)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    Sigma.desc (fun a : Σ i : Fin n, Fin (r i) ↦
      localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 a.2) ≫
        Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) a.1)
  have hleft : Epi left := by
    refine ⟨?_⟩
    intro Z α β hαβ
    apply Limits.Sigma.hom_ext
    intro i
    let δi :
        (∐ fun a : Fin (r i) ↦ localizedStructureModuleExtensionByZero 𝒪 (W i a)) ⟶
          localizedStructureModuleExtensionByZero 𝒪 (U i) :=
      Sigma.desc (fun a : Fin (r i) ↦ localizedStructureModuleExtensionByZeroMap J 𝒪 (π i a))
    have hδi : Epi δi := by
      -- Each selected finite basis subfamily still covers `U i`, so its augmentation is epic.
      exact coverAugmentationEpi (J := J) (𝒪 := 𝒪)
        (Uᵢ := W i)
        (π := π i)
        (hcover := hcoverFin i)
    apply (cancel_epi δi).1
    apply Limits.Sigma.hom_ext
    intro a
    have hcomp := congrArg
      (fun γ ↦
        Sigma.ι
            (fun b : Σ i : Fin n, Fin (r i) ↦
              localizedStructureModuleExtensionByZero 𝒪 (W b.1 b.2))
            ⟨i, a⟩ ≫
          γ)
      hαβ
    simpa [left, δi, Category.assoc] using hcomp
  have hleft_ι :
      ∀ a : Σ i : Fin n, Fin (r i),
        Sigma.ι
            (fun b : Σ i : Fin n, Fin (r i) ↦
              localizedStructureModuleExtensionByZero 𝒪 (W b.1 b.2))
            a ≫
          left =
            localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 a.2) ≫
              Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) a.1 := by
    intro a
    dsimp [left]
    rw [Limits.Sigma.ι_desc]
  let liftSummand :
      ∀ i : Fin n, ∀ a : Fin (r i),
        localizedStructureModuleExtensionByZero 𝒪 (W i a) ⟶ R :=
    fun i a ↦
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (W i a) R).symm
        (sectionMap (J := J) (𝒪 := 𝒪) (κ i a).2.f R (localLift i (κ i a).1))
  have hliftSummand :
      ∀ i : Fin n, ∀ a : Fin (r i),
        liftSummand i a ≫ e =
          localizedStructureModuleExtensionByZeroMap J 𝒪 (π i a) ≫
            Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫ q := by
    intro i a
    apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (W i a) T).injective
    rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
      (J := J) (𝒪 := 𝒪) (β := liftSummand i a) (α := e)]
    dsimp [liftSummand]
    rw [Equiv.apply_symm_apply]
    rw [sectionMap_naturality (J := J) (𝒪 := 𝒪) (f := (κ i a).2.f) (α := e)
      (s := localLift i (κ i a).1)]
    rw [hlocalLift i (κ i a).1]
    rw [sectionMap_comp (J := J) (𝒪 := 𝒪) (κ i a).2.f (κ i a).1.f T (σ i)]
    simpa [W, π, sourceBasisMap, σ] using
      localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := π i a) (ℱ := T)
        (α := Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫ q)
  let lift :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (W a.1 a.2)) ⟶
        R :=
    Sigma.desc (fun a : Σ i : Fin n, Fin (r i) ↦ liftSummand a.1 a.2)
  have hcomm : lift ≫ e = left ≫ q := by
    apply Limits.Sigma.hom_ext
    intro a
    dsimp [lift]
    rw [Category.assoc, Limits.Sigma.ι_desc, hleft_ι a, Category.assoc]
    exact hliftSummand a.1 a.2
  exact ⟨r, W, π, hW, hcoverFin, left, lift, hleft, hleft_ι, hcomm⟩

end

end SheafOfModules.RingedSite

open _root_.SheafOfModules.RingedSite
  (HasFiniteBasisConstructibleModuleCokernelPresentation cokernelIso_of_epi_kernelCover)

namespace CategoryTheory.ShortComplex

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable {S : ShortComplex Mod}

/-- Helper for Lemma 18.30.10: transport a finite basis cokernel presentation across an
isomorphism. -/
lemma hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
    {X Y : Mod} (e : X ≅ Y)
    (hX : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B Y := by
  rcases hX with ⟨n, m, U, V, f, i, hU, hV⟩
  -- Reuse the same finite presentation data and postcompose the identifying isomorphism.
  exact ⟨n, m, U, V, f, e.symm ≪≫ i, hU, hV⟩

/-- Helper for Lemma 18.30.10: precomposing a morphism with the chosen cokernel projection does
not change its cokernel. -/
lemma cokernelIso_of_cokernelProjectionComp
    {A B Y : Mod} (f : A ⟶ B) (ψ : cokernel f ⟶ Y) :
    cokernel (cokernel.π f ≫ ψ) ≅ cokernel ψ := by
  let cofork : CokernelCofork (cokernel.π f ≫ ψ) :=
    CokernelCofork.ofπ (cokernel.π ψ) (by simp)
  have hcofork : IsColimit cofork := by
    -- The universal property of `cokernel ψ` already solves the cokernel problem after the
    -- cokernel projection `cokernel.π f`.
    refine CokernelCofork.IsColimit.ofπ' (cokernel.π ψ) (by simp) ?_
    intro Z k hk
    refine ⟨cokernel.desc ψ k ?_, by simp⟩
    apply (cancel_epi (cokernel.π f)).1
    simpa [Category.assoc] using hk
  -- Compare the explicit colimit above with the chosen cokernel of `ψ`.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (cokernel.π f ≫ ψ)) hcofork

/-- Helper for Lemma 18.30.10: the cokernel of a morphism from a finitely presented module into a
finite basis coproduct again has a finite basis cokernel presentation. -/
lemma hasFiniteBasisConstructibleModuleCokernelPresentation_of_map_to_basisCoproduct
    {K : Mod}
    (hK : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B K)
    {n : ℕ} (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (α : K ⟶ ∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (cokernel α) := by
  rcases hK with ⟨nK, mK, UK, VK, fK, eK, hUK, hVK⟩
  let α' :
      (∐ fun i : Fin nK ↦ localizedStructureModuleExtensionByZero 𝒪 (UK i)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    cokernel.π fK ≫ eK.inv ≫ α
  let eπ : cokernel α' ≅ cokernel (eK.inv ≫ α) :=
    cokernelIso_of_cokernelProjectionComp (J := J) (𝒪 := 𝒪) (B := B) fK (eK.inv ≫ α)
  let eα : cokernel (eK.inv ≫ α) ≅ cokernel α :=
    cokernel.mapIso (eK.inv ≫ α) α eK.symm (Iso.refl _) (by
      -- The normalized map is the conjugate of `α` through the presentation isomorphism of `K`.
      simp [Category.assoc])
  -- Use the normalized map from the chosen finite presentation source of `K`.
  exact
    hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B) (eπ ≪≫ eα)
      ⟨n, nK, U, UK, α', eπ.symm, hU, hUK⟩

/-- Helper for Lemma 18.30.10: once a module is the cokernel of an epimorphism from a finite
basis coproduct and the kernel has a finite basis cokernel presentation, the target does as well.
-/
lemma hasFiniteBasisConstructibleModuleCokernelPresentation_of_epi_from_basisCoproduct
    {K X : Mod}
    {n : ℕ} (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B)
    (φ : (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ X)
    (ψ : K ⟶ kernel φ) [Epi φ] [Epi ψ]
    (hK : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B K) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X := by
  let α : K ⟶ (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    ψ ≫ kernel.ι φ
  have hα :
      HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (cokernel α) :=
    hasFiniteBasisConstructibleModuleCokernelPresentation_of_map_to_basisCoproduct
      (J := J) (𝒪 := 𝒪) (B := B) hK U hU α
  -- The standard epi-kernel-cover package identifies `X` with this cokernel.
  exact
    hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
      (J := J) (𝒪 := 𝒪) (B := B)
      (cokernelIso_of_epi_kernelCover (𝒪 := 𝒪) (φ := φ) (ψ := ψ)).symm hα

/-- Helper for Lemma 18.30.10: the source of a cokernel presentation maps epimorphically onto
the kernel of the quotient map. -/
lemma presentationKernelCoverEpi
    {A K : Mod} (f : K ⟶ A) :
    Epi (kernel.lift (cokernel.π f) f (by simp)) := by
  let T : ShortComplex Mod := ShortComplex.mk f (cokernel.π f) (by simp)
  have hT : T.Exact := by
    -- The cokernel row is exact by the universal property of `cokernel.π`.
    simpa [T] using ShortComplex.exact_of_g_is_cokernel T (cokernelIsCokernel f)
  -- Rewrite exactness to the standard epimorphicity criterion for the kernel lift.
  simpa [T] using (ShortComplex.exact_iff_epi_kernel_lift (S := T)).1 hT

/-- Helper for Lemma 18.30.10: a finite coproduct of basis extension-by-zero modules already has
the required finite basis cokernel presentation, using the zero-source cokernel presentation. -/
lemma hasFiniteBasisConstructibleModuleCokernelPresentation_of_basisCoproduct
    {n : ℕ} (U : Fin n → C) (hU : ∀ i : Fin n, U i ∈ B) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B
      (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) := by
  let e :
      cokernel
          (0 :
            (∐ fun j : Fin 0 ↦ localizedStructureModuleExtensionByZero 𝒪 (Fin.elim0 j)) ⟶
              (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))) ≅
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    CategoryTheory.Limits.cokernelZeroIsoTarget
  -- The zero relation map presents the finite coproduct itself as a cokernel.
  exact ⟨n, 0, U, Fin.elim0, 0, e.symm, hU, Fin.elim0⟩

/-- Helper for Lemma 18.30.10: if the left presentation quotient and the lifted right quotient are
epic, then the assembled map onto the middle term is epic. -/
lemma middlePresentationEpi
    {A₁ A₃' : Mod}
    {q₁ : A₁ ⟶ S.X₁} {q₃' : A₃' ⟶ S.X₃} {a₃ : A₃' ⟶ S.X₂}
    [Epi q₁] [Epi q₃']
    (hS : S.ShortExact)
    (ha₃ : a₃ ≫ S.g = q₃') :
    Epi (coprod.desc (q₁ ≫ S.f) a₃ : A₁ ⨿ A₃' ⟶ S.X₂) := by
  refine ⟨?_⟩
  intro Z u v huv
  have hf : S.f ≫ u = S.f ≫ v := by
    -- Restrict the equality to the left summand and cancel the epimorphic quotient map `q₁`.
    apply (cancel_epi q₁).1
    have hcomp := congrArg (fun γ ↦ coprod.inl ≫ γ) huv
    simpa [Category.assoc] using hcomp
  have ha : a₃ ≫ u = a₃ ≫ v := by
    -- Restrict the equality to the lifted right summand.
    have hcomp := congrArg (fun γ ↦ coprod.inr ≫ γ) huv
    simpa [Category.assoc] using hcomp
  let d : S.X₂ ⟶ Z := u - v
  have hfd : S.f ≫ d = 0 := by
    -- The difference `u - v` kills the image of `S.f`, so it descends across the cokernel `S.g`.
    simp [d, Category.assoc, hf]
  let z : S.X₃ ⟶ Z :=
    hS.gIsCokernel.desc (CokernelCofork.ofπ d hfd)
  have hz : S.g ≫ z = d := by
    simpa [z] using hS.gIsCokernel.fac (CokernelCofork.ofπ d hfd) WalkingParallelPair.one
  have hq₃' : q₃' ≫ z = 0 := by
    -- The lifted right branch also kills `u - v`, and the right quotient map is epic.
    calc
      q₃' ≫ z = (a₃ ≫ S.g) ≫ z := by rw [← ha₃]
      _ = a₃ ≫ (S.g ≫ z) := by simp [Category.assoc]
      _ = a₃ ≫ d := by rw [hz]
      _ = 0 := by simp [d, Category.assoc, ha]
  have hz0 : z = 0 := by
    apply (cancel_epi q₃').1
    simpa using hq₃'
  have hd0 : d = 0 := by
    rw [← hz]
    simp [hz0]
  -- The cokernel descent shows the original two maps are equal.
  exact sub_eq_zero.mp (by simpa [d] using hd0)

/-- Helper for Lemma 18.30.10: a refinement witness from Lemma `18.30.9` transports the original
quotient presentation to the refined top map. -/
lemma refinedCokernelIsoOfWitness
    {n m : ℕ} {K : Fin n → Type*}
    (U : Fin n → C) (V : Fin m → C)
    {Ucover : ∀ i : Fin n, K i → C}
    (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    {X : Mod} (e : X ≅ cokernel f)
    (w :
      SheafOfModules.RingedSite.FiniteBasisRefinementInducingCokernelIsoWitness
        (J := J) (𝒪 := 𝒪) (B := B) U V Ucover f) :
    X ≅ cokernel w.top := by
  let eMap : cokernel w.top ≅ cokernel f :=
    asIso (cokernel.map w.top f w.left w.right w.comm)
  -- Transport the original quotient identification across the refined witness isomorphism.
  exact e ≪≫ eMap.symm

/-- Helper for Lemma 18.30.10: the quotient map attached to a refinement witness is the original
quotient map precomposed with the witness right-hand refinement map. -/
lemma refinedCokernelQuotientMap_eq_ofWitness
    {n m : ℕ} {K : Fin n → Type*}
    (U : Fin n → C) (V : Fin m → C)
    {Ucover : ∀ i : Fin n, K i → C}
    (f :
      (∐ fun j : Fin m ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    {X : Mod} (e : X ≅ cokernel f)
    (w :
      SheafOfModules.RingedSite.FiniteBasisRefinementInducingCokernelIsoWitness
        (J := J) (𝒪 := 𝒪) (B := B) U V Ucover f) :
    cokernel.π w.top ≫
        (refinedCokernelIsoOfWitness (J := J) (𝒪 := 𝒪) (B := B) U V f e w).inv =
      w.right ≫ cokernel.π f ≫ e.inv := by
  let eMap : cokernel w.top ≅ cokernel f :=
    asIso (cokernel.map w.top f w.left w.right w.comm)
  -- Normalize the refined quotient map through the witness cokernel comparison.
  change cokernel.π w.top ≫ eMap.hom ≫ e.inv = w.right ≫ cokernel.π f ≫ e.inv
  simp [eMap, Category.assoc, cokernel.map]

/-- Helper for Lemma 18.30.10: restricting a lifted finite cover to a selected subfamily preserves
the commutative square with the ambient quotient map. -/
lemma selectedSubfamilyLift_comp
    {n : ℕ} (U : Fin n → C)
    {r s : Fin n → ℕ}
    (W : ∀ i : Fin n, Fin (r i) → C)
    (π : ∀ i : Fin n, ∀ a : Fin (r i), W i a ⟶ U i)
    (κ : ∀ i : Fin n, Fin (s i) → Fin (r i))
    {R T : Mod}
    (q :
      (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ T)
    (g : R ⟶ T)
    (a :
      (∐ fun b : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (W b.1 b.2)) ⟶
        R)
    (ha :
      a ≫ g =
        (Sigma.desc
          (fun b : Σ i : Fin n, Fin (r i) ↦
            localizedStructureModuleExtensionByZeroMap J 𝒪 (π b.1 b.2) ≫
              Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
                b.1)) ≫
          q) :
    let a' :
        (∐ fun b : Σ i : Fin n, Fin (s i) ↦
          localizedStructureModuleExtensionByZero 𝒪 (W b.1 (κ b.1 b.2))) ⟶
          R :=
      Sigma.desc
        (fun b : Σ i : Fin n, Fin (s i) ↦
          Sigma.ι
              (fun c : Σ i : Fin n, Fin (r i) ↦
                localizedStructureModuleExtensionByZero 𝒪 (W c.1 c.2))
              ⟨b.1, κ b.1 b.2⟩ ≫
            a)
    a' ≫ g =
      (Sigma.desc
        (fun b : Σ i : Fin n, Fin (s i) ↦
          localizedStructureModuleExtensionByZeroMap J 𝒪 (π b.1 (κ b.1 b.2)) ≫
            Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
              b.1)) ≫
        q := by
  -- The selected lift is obtained by composing each chosen summand inclusion with the original
  -- lift `a`, so the original commutative square restricts summandwise.
  dsimp
  apply Limits.Sigma.hom_ext
  intro b
  rw [Category.assoc, Limits.Sigma.ι_desc, ha, Category.assoc, Limits.Sigma.ι_desc]

/-- Helper for Lemma 18.30.10: an epimorphic cover of `kernel (right ≫ cokernel.π f)` upgrades
the induced cokernel comparison to an isomorphism. -/
private theorem isIso_cokernelMap_of_epiKernelCover
    {W R S T : Mod}
    {f : S ⟶ T} {right : R ⟶ T}
    (ψ : W ⟶ kernel (right ≫ cokernel.π f)) (left : W ⟶ S)
    [Epi right] [Epi ψ]
    (hcomm : (ψ ≫ kernel.ι (right ≫ cokernel.π f)) ≫ right = left ≫ f) :
    IsIso
      (cokernel.map
        (ψ ≫ kernel.ι (right ≫ cokernel.π f)) f left right hcomm) := by
  let S₁ : ShortComplex Mod :=
    ShortComplex.mk
      (ψ ≫ kernel.ι (right ≫ cokernel.π f))
      (right ≫ cokernel.π f)
      (by simp [Category.assoc, hcomm])
  let S₂ : ShortComplex Mod :=
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
  have he :
      e.hom =
        cokernel.map
          (ψ ≫ kernel.ι (right ≫ cokernel.π f)) f left right hcomm := by
    -- Compare the universal uniqueness isomorphism with the explicit descended cokernel map.
    apply (cancel_epi (cokernel.π (ψ ≫ kernel.ι (right ≫ cokernel.π f)))).1
    simp [e, cofork, Category.assoc]
  rw [← he]
  infer_instance

/-- Helper for Lemma 18.30.10: postcomposing by an epimorphism does not change the kernel
object. -/
private lemma kernelIsoOfCompRightEpi
    {A B C : Mod} (u : A ⟶ B) (v : B ⟶ C) [Epi v] :
    kernel u ≅ kernel (u ≫ v) := by
  let hom : kernel u ⟶ kernel (u ≫ v) :=
    kernel.map u (u ≫ v) (𝟙 A) v (by simp)
  let inv : kernel (u ≫ v) ⟶ kernel u :=
    kernel.lift u (kernel.ι (u ≫ v)) (by
      apply (cancel_epi v).1
      simpa [Category.assoc] using kernel.condition (u ≫ v))
  refine
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · -- Compare both endomorphisms after postcomposing with the kernel inclusion of `u`.
    apply (cancel_mono (kernel.ι u)).1
    simp [hom, inv, Category.assoc, kernel.map]
  · -- Compare both endomorphisms after postcomposing with the kernel inclusion of `u ≫ v`.
    apply (cancel_mono (kernel.ι (u ≫ v))).1
    simp [hom, inv, Category.assoc, kernel.map]

-- Proof sketch: choose explicit `18.30.7.2` presentations for `S.X₁` and `S.X₃`. Lift the
-- generators of the right presentation through the epimorphism `S.g` after a finite basis
-- refinement using Lemma `18.30.9`, then compare kernels via the snake lemma and refine the
-- resulting kernel presentation using Lemma `18.30.2`. This produces a finite basis presentation
-- of the middle term `S.X₂`.
/-- Lemma 18.30.10: in Situation `18.30.5`, extensions of `\mathcal O`-modules admitting finite
basis cokernel presentations as in `18.30.7.2` again admit such a presentation. -/
theorem ringedSite_hasFiniteBasisConstructibleModuleCokernelPresentation_X2_of_shortExact
    (hS : S.ShortExact)
    (hX₁ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₁)
    (hX₃ : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₃) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B S.X₂ := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  rcases hX₁ with ⟨n₁, m₁, U₁, V₁, f₁, e₁, hU₁, hV₁⟩
  rcases hX₃ with ⟨n₃, m₃, U₃, V₃, f₃, e₃, hU₃, hV₃⟩
  let q₁ :
      (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ⟶ S.X₁ :=
    cokernel.π f₁ ≫ e₁.inv
  let q₃ :
      (∐ fun i : Fin n₃ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₃ i)) ⟶ S.X₃ :=
    cokernel.π f₃ ≫ e₃.inv
  letI : Epi q₁ := by
    dsimp [q₁]
    infer_instance
  letI : Epi q₃ := by
    dsimp [q₃]
    infer_instance
  obtain ⟨r₃, W₃, π₃, hW₃, hcover₃, right₃, a₃, hright₃, hright₃_ι, ha₃⟩ :=
    SheafOfModules.RingedSite.existsFiniteBasisLiftCoverOfEpi
      (J := J) (𝒪 := 𝒪) (B := B) U₃ hU₃ q₃ S.g
  letI : Epi right₃ := hright₃
  obtain ⟨ℓ₃, Z₃, hZ₃, f₃', e₃', ha₃'⟩ :=
    existsRefinedRightPresentationOnLiftedCover
      (J := J) (𝒪 := 𝒪) (B := B)
      U₃ V₃ hU₃ hV₃ f₃ e₃ S.g W₃ π₃ hW₃ hcover₃ right₃ hright₃_ι a₃
      (by simpa [q₃, Category.assoc] using ha₃)
  let q₃' :
      (∐ fun b : Σ i : Fin n₃, Fin (r₃ i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (W₃ b.1 b.2)) ⟶
        S.X₃ :=
    cokernel.π f₃' ≫ e₃'.inv
  let p :
      (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ⨿
        (∐ fun b : Σ i : Fin n₃, Fin (r₃ i) ↦
          localizedStructureModuleExtensionByZero 𝒪 (W₃ b.1 b.2)) ⟶
        S.X₂ :=
    coprod.desc (q₁ ≫ S.f) a₃
  letI : Epi p :=
    middlePresentationEpi (J := J) (𝒪 := 𝒪) (B := B) (S := S)
      (q₁ := q₁) (q₃' := q₃') (a₃ := a₃) hS ha₃'
  let ψ₁ :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        kernel q₁ :=
    kernel.lift q₁ f₁ (by simp [q₁, Category.assoc])
  letI : Epi ψ₁ := presentationKernelCoverEpi (J := J) (𝒪 := 𝒪) (B := B) f₁
  let ψ₃ :
      (∐ fun l : Fin ℓ₃ ↦ localizedStructureModuleExtensionByZero 𝒪 (Z₃ l)) ⟶
        kernel q₃' :=
    kernel.lift q₃' f₃' (by simp [q₃', Category.assoc])
  letI : Epi ψ₃ := presentationKernelCoverEpi (J := J) (𝒪 := 𝒪) (B := B) f₃'
  -- Route correction: the right-refinement blocker is now isolated behind the theorem-local
  -- helper above, and the main proof has advanced to the kernel row of
  -- `kernel q₁ → kernel p → kernel q₃'`.
  --
  -- TODO: construct the canonical epi `kernel p ⟶ kernel q₃'` from the split top row
  -- `A₁ → A₁ ⨿ A₃' → A₃'`, package the snake-lemma short exact sequence
  -- `0 ⟶ kernel q₁ ⟶ kernel p ⟶ kernel q₃' ⟶ 0`, lift `ψ₃` through that epi, and then apply
  -- `middlePresentationEpi` to the kernel row with the left cover `ψ₁`.
  sorry

end

end CategoryTheory.ShortComplex
