import Mathlib
import stacks_proof.stacks_project.Chap18.Lemma_18_19_2
import stacks_proof.stacks_project.Chap18.Lemma_18_28_7
import stacks_proof.stacks_project.Chap18.Lemma_18_30_4
import stacks_proof.stacks_project.Chap18.Lemma_18_30_7
import stacks_proof.stacks_project.Chap18.Situation_18_30_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})
variable (B : Set C)
variable [J.HasQuasiCompactBasisWithQuasiCompactFiberProducts B]

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)

/-- Helper for Lemma 18.30.8: transport a finite basis cokernel presentation across an
isomorphism of module sheaves. -/
private theorem hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
    {X Y : SheafOfModules (ringSheaf J 𝒪)} (e : X ≅ Y)
    (hX : HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B Y := by
  rcases hX with ⟨n, m, U, V, f, i, hU, hV⟩
  -- Reuse the same finite presentation data and postcompose the identifying isomorphism.
  exact ⟨n, m, U, V, f, e.symm ≪≫ i, hU, hV⟩

/-- Helper for Lemma 18.30.8: precomposing a morphism with the canonical cokernel projection does
not change its cokernel. -/
private theorem cokernelIso_of_cokernelProjectionComp
    {A B Y : SheafOfModules (ringSheaf J 𝒪)}
    (f : A ⟶ B) (ψ : cokernel f ⟶ Y) :
    cokernel (cokernel.π f ≫ ψ) ≅ cokernel ψ := by
  let cofork : CokernelCofork (cokernel.π f ≫ ψ) :=
    CokernelCofork.ofπ (cokernel.π ψ) (by simp)
  have hcofork : IsColimit cofork := by
    -- The universal property of `cokernel ψ` already solves the cokernel problem for
    -- `cokernel.π f ≫ ψ`; only the vanishing condition needs cancellation through the epi
    -- `cokernel.π f`.
    refine CokernelCofork.IsColimit.ofπ' (cokernel.π ψ) (by simp) ?_
    intro Z k hk
    refine ⟨cokernel.desc ψ k ?_, by simp⟩
    apply (cancel_epi (cokernel.π f)).1
    simpa [Category.assoc] using hk
  -- Compare the explicit universal property above with the canonical chosen cokernel.
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (cokernel.π f ≫ ψ)) hcofork

/-- Helper for Lemma 18.30.8: `localizedStructureModuleExtensionByZero_homEquiv` is natural in
the target module sheaf. -/
private theorem localizedStructureModuleExtensionByZero_homEquiv_naturality_right
    {V : C} {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
    (β : localizedStructureModuleExtensionByZero 𝒪 V ⟶ ℱ) (α : ℱ ⟶ 𝒢) :
    localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V 𝒢 (β ≫ α) =
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op V)).map α)
        (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 V ℱ β) := by
  -- The owner equivalence is defined by target-functorial constructions, so this naturality is
  -- definitional.
  rfl

/-- Helper for Lemma 18.30.8: restriction of sections commutes with applying a module morphism. -/
private theorem sectionMap_naturality
    {V W : C} {ℱ 𝒢 : SheafOfModules (ringSheaf J 𝒪)}
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

/-- Helper for Lemma 18.30.8: precomposing with `localizedStructureModuleExtensionByZeroMap`
corresponds to restricting the associated section. -/
private theorem localizedStructureModuleExtensionByZeroMap_homEquiv
    {V W : C} (f : V ⟶ W) (ℱ : SheafOfModules (ringSheaf J 𝒪))
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
  -- Route correction: reuse the owner naturality statement instead of unfolding the slice-site
  -- adjunction by hand.
  rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right (J := J) (𝒪 := 𝒪)
    (β := localizedStructureModuleExtensionByZeroMap J 𝒪 f) (α := α)]
  rw [SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroMap]
  rw [Equiv.apply_symm_apply]
  rw [hα]
  exact sectionMap_naturality (J := J) (𝒪 := 𝒪) f α _

/-- Helper for Lemma 18.30.8: an epimorphism of module sheaves yields a covering family on which
any chosen section lifts locally. -/
private theorem existsCoverLiftOfEpiSection
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

/-- Helper for Lemma 18.30.8: a slice-site cover of the terminal object is the same as the base
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

/-- Helper for Lemma 18.30.8: a slice-site `CoversTop` hypothesis yields the corresponding
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

/-- Helper for Lemma 18.30.8: a covering refinement landing in a finite-image subfamily still
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

/-- Helper for Lemma 18.30.8: a covering sieve on a family converts back to the corresponding
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

/-- Helper for Lemma 18.30.8: reindexing a covering family by an equivalence preserves the
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

/-- Helper for Lemma 18.30.8: the arrows of a cover form a `CoversTop` family on the same base
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

/-- Helper for Lemma 18.30.8: composing a slice-site cover with covers of its members yields a
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

/-- Helper for Lemma 18.30.8: successive restriction maps compose as restriction along the
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

/-- Helper for Lemma 18.30.8: the augmentation map attached to a covering family of basis
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

/-- Helper for Lemma 18.30.8: choose a finite subfamily of the composite local-lift cover that
still covers each basis object. -/
private theorem finiteBasisRefinementOfCompositeLiftCover
    {n : ℕ}
    (U : Fin n → C)
    (hU : ∀ i : Fin n, U i ∈ B)
    (sourceCover : ∀ i : Fin n, J.Cover (U i))
    (basisCover : ∀ i : Fin n, (sourceCover i).Arrow → J.Cover _)
    (hbasisCover : ∀ i : Fin n, ∀ I : (sourceCover i).Arrow,
      ∀ A : (basisCover i I).Arrow, A.Y ∈ B) :
    ∃ (r : Fin n → ℕ)
      (κ : ∀ i : Fin n, Fin (r i) → Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow),
        (∀ i : Fin n, ∀ a : Fin (r i), ((κ i a).2).Y ∈ B) ∧
        (∀ i : Fin n,
          (J.over (U i)).CoversTop
            (fun a : Fin (r i) ↦ Over.mk ((κ i a).2.f ≫ (κ i a).1.f))) := by
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
    -- Each second-stage cover object already lies in the chosen basis.
    intro i a
    exact hbasisCover i a.1 a.2
  have hsourceBasisCover :
      ∀ i : Fin n,
        (J.over (U i)).CoversTop
          (fun a : Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow ↦
            Over.mk (sourceBasisMap i a)) := by
    intro i
    -- Compose the local lift cover with the basis covers of its members.
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
  have hκ :
      ∀ i : Fin n, ∀ a : Fin (r i), ((κ i a).2).Y ∈ B := by
    -- The finite refinement only keeps objects already known to lie in the basis.
    intro i a
    simpa [κ, sourceBasisObject] using hsourceBasisObject i (κ i a)
  have hcoverFin :
      ∀ i : Fin n,
        (J.over (U i)).CoversTop
          (fun a : Fin (r i) ↦ Over.mk ((κ i a).2.f ≫ (κ i a).1.f)) := by
    intro i
    -- Reindex the selected finite-image family by `Fin (r i)`.
    simpa [r, κ, sourceBasisMap] using
      coversTopOver_reindexEquiv (J := J)
        (Uᵢ := fun k : S i ↦ sourceBasisObject i k.1)
        (π := fun k : S i ↦ sourceBasisMap i k.1)
        (e := Fintype.equivFin (S i))
        (hcover := hScover i)
  exact ⟨r, κ, hκ, hcoverFin⟩

/-- Helper for Lemma 18.30.8: the finite selected basis family gives an explicit epic
augmentation map into the original finite coproduct. -/
private theorem finiteBasisAugmentationOfCompositeLiftCover
    {n : ℕ}
    (U : Fin n → C)
    {sourceCover : ∀ i : Fin n, J.Cover (U i)}
    {basisCover : ∀ i : Fin n, (sourceCover i).Arrow → J.Cover _}
    {r : Fin n → ℕ}
    (κ : ∀ i : Fin n, Fin (r i) → Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow)
    (hcoverFin : ∀ i : Fin n,
      (J.over (U i)).CoversTop
        (fun a : Fin (r i) ↦ Over.mk ((κ i a).2.f ≫ (κ i a).1.f))) :
    ∃ (left :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (((κ a.1 a.2).2).Y)) ⟶
          (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))),
        Epi left ∧
          (∀ a : Σ i : Fin n, Fin (r i),
            Sigma.ι
                (fun b : Σ i : Fin n, Fin (r i) ↦
                  localizedStructureModuleExtensionByZero 𝒪 (((κ b.1 b.2).2).Y))
                a ≫
              left =
                localizedStructureModuleExtensionByZeroMap J 𝒪
                  ((κ a.1 a.2).2.f ≫ (κ a.1 a.2).1.f) ≫
                  Sigma.ι
                    (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
                    a.1) := by
  let left :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (((κ a.1 a.2).2).Y)) ⟶
        (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    Sigma.desc (fun a : Σ i : Fin n, Fin (r i) ↦
      localizedStructureModuleExtensionByZeroMap J 𝒪
          ((κ a.1 a.2).2.f ≫ (κ a.1 a.2).1.f) ≫
        Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) a.1)
  have hleft : Epi left := by
    refine ⟨?_⟩
    intro Z α β hαβ
    apply Limits.Sigma.hom_ext
    intro i
    let δi :
        (∐ fun a : Fin (r i) ↦ localizedStructureModuleExtensionByZero 𝒪 (((κ i a).2).Y)) ⟶
          localizedStructureModuleExtensionByZero 𝒪 (U i) :=
      Sigma.desc (fun a : Fin (r i) ↦
        localizedStructureModuleExtensionByZeroMap J 𝒪 ((κ i a).2.f ≫ (κ i a).1.f))
    have hδi : Epi δi := by
      -- The selected finite basis arrows still cover `U i`, so the augmentation is epic.
      exact coverAugmentationEpi (J := J) (𝒪 := 𝒪)
        (Uᵢ := fun a : Fin (r i) ↦ ((κ i a).2).Y)
        (π := fun a : Fin (r i) ↦ (κ i a).2.f ≫ (κ i a).1.f)
        (hcover := hcoverFin i)
    -- Compare after restricting to the `i`-th finite covering augmentation.
    apply (cancel_epi δi).1
    apply Limits.Sigma.hom_ext
    intro a
    have hcomp := congrArg
      (fun γ ↦
        Sigma.ι
            (fun b : Σ i : Fin n, Fin (r i) ↦
              localizedStructureModuleExtensionByZero 𝒪 (((κ b.1 b.2).2).Y))
            ⟨i, a⟩ ≫
          γ)
      hαβ
    simpa [left, δi, Category.assoc] using hcomp
  have hleft_ι :
      ∀ a : Σ i : Fin n, Fin (r i),
        Sigma.ι
            (fun b : Σ i : Fin n, Fin (r i) ↦
              localizedStructureModuleExtensionByZero 𝒪 (((κ b.1 b.2).2).Y))
            a ≫
          left =
            localizedStructureModuleExtensionByZeroMap J 𝒪
              ((κ a.1 a.2).2.f ≫ (κ a.1 a.2).1.f) ≫
              Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
                a.1 := by
    intro a
    -- Each summand of the `Sigma.desc` augmentation is explicit.
    dsimp [left]
    rw [Limits.Sigma.ι_desc]
  exact ⟨left, hleft, hleft_ι⟩

/-- Helper for Lemma 18.30.8: assemble the global lift from the finite selected basis family and
the local section lifts. -/
private theorem assembledFiniteLiftCoverOfEpi
    {n : ℕ}
    (U : Fin n → C)
    {R T : Mod}
    (q :
      (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ T)
    (e : R ⟶ T) [Epi e]
    (σ : ∀ i : Fin n,
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op (U i))).obj T)
    {sourceCover : ∀ i : Fin n, J.Cover (U i)}
    {basisCover : ∀ i : Fin n, (sourceCover i).Arrow → J.Cover _}
    {r : Fin n → ℕ}
    (κ : ∀ i : Fin n, Fin (r i) → Σ I : (sourceCover i).Arrow, (basisCover i I).Arrow)
    (localLift : ∀ i : Fin n, ∀ I : (sourceCover i).Arrow,
      (SheafOfModules.evaluation (ringSheaf J 𝒪) (op I.Y)).obj R)
    (hlocalLift : ∀ i : Fin n, ∀ I : (sourceCover i).Arrow,
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) (op I.Y)).map e) (localLift i I) =
        sectionMap (J := J) (𝒪 := 𝒪) I.f T (σ i))
    (left :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (((κ a.1 a.2).2).Y)) ⟶
          (∐ fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (hleft_ι : ∀ a : Σ i : Fin n, Fin (r i),
      Sigma.ι
          (fun b : Σ i : Fin n, Fin (r i) ↦
            localizedStructureModuleExtensionByZero 𝒪 (((κ b.1 b.2).2).Y))
          a ≫
        left =
          localizedStructureModuleExtensionByZeroMap J 𝒪
            ((κ a.1 a.2).2.f ≫ (κ a.1 a.2).1.f) ≫
            Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) a.1) :
    ∃ (lift :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (((κ a.1 a.2).2).Y)) ⟶
          R),
        lift ≫ e = left ≫ q := by
  let liftSummand :
      ∀ i : Fin n, ∀ a : Fin (r i),
        localizedStructureModuleExtensionByZero 𝒪 (((κ i a).2).Y) ⟶ R :=
    fun i a ↦
      (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (((κ i a).2).Y) R).symm
        (sectionMap (J := J) (𝒪 := 𝒪) (κ i a).2.f R (localLift i (κ i a).1))
  have hliftSummand :
      ∀ i : Fin n, ∀ a : Fin (r i),
        liftSummand i a ≫ e =
          localizedStructureModuleExtensionByZeroMap J 𝒪
            ((κ i a).2.f ≫ (κ i a).1.f) ≫
            Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫ q := by
    intro i a
    -- Convert the morphism identity into equality of the corresponding restricted sections.
    apply (localizedStructureModuleExtensionByZero_homEquiv J 𝒪 (((κ i a).2).Y) T).injective
    rw [localizedStructureModuleExtensionByZero_homEquiv_naturality_right
      (J := J) (𝒪 := 𝒪) (β := liftSummand i a) (α := e)]
    dsimp [liftSummand]
    rw [Equiv.apply_symm_apply]
    rw [sectionMap_naturality (J := J) (𝒪 := 𝒪) (f := (κ i a).2.f) (α := e)
      (s := localLift i (κ i a).1)]
    rw [hlocalLift i (κ i a).1]
    rw [sectionMap_comp (J := J) (𝒪 := 𝒪) (κ i a).2.f (κ i a).1.f T (σ i)]
    simpa using
      localizedStructureModuleExtensionByZeroMap_homEquiv (J := J) (𝒪 := 𝒪)
        (f := (κ i a).2.f ≫ (κ i a).1.f) (ℱ := T)
        (α := Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) i ≫ q)
  let lift :
      (∐ fun a : Σ i : Fin n, Fin (r i) ↦
        localizedStructureModuleExtensionByZero 𝒪 (((κ a.1 a.2).2).Y)) ⟶
        R :=
    Sigma.desc (fun a : Σ i : Fin n, Fin (r i) ↦ liftSummand a.1 a.2)
  have hcomm : lift ≫ e = left ≫ q := by
    -- Compare both composites on each summand of the finite selected cover.
    apply Limits.Sigma.hom_ext
    intro a
    dsimp [lift]
    rw [Category.assoc, Limits.Sigma.ι_desc, hleft_ι a, Category.assoc]
    exact hliftSummand a.1 a.2
  exact ⟨lift, hcomm⟩

/-- Helper for Lemma 18.30.8: a morphism from a finite coproduct of basis generators can be
refined to a finite basis cover on which it lifts through any epimorphism, and the selected finite
cover still covers each original basis object. -/
private theorem existsFiniteBasisLiftCoverOfEpi
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
  obtain ⟨r, κ, hκ, hcoverκ⟩ :=
    finiteBasisRefinementOfCompositeLiftCover (J := J) (𝒪 := 𝒪) (B := B)
      U hU sourceCover basisCover hbasisCover
  let W : ∀ i : Fin n, Fin (r i) → C := fun i a ↦ ((κ i a).2).Y
  let π : ∀ i : Fin n, ∀ a : Fin (r i), W i a ⟶ U i :=
    fun i a ↦ (κ i a).2.f ≫ (κ i a).1.f
  have hW : ∀ i : Fin n, ∀ a : Fin (r i), W i a ∈ B := by
    -- Unpack the basis membership from the finite refinement helper.
    intro i a
    simpa [W] using hκ i a
  have hcoverFin :
      ∀ i : Fin n,
        (J.over (U i)).CoversTop (fun a : Fin (r i) ↦ Over.mk (π i a)) := by
    -- Rewrite the finite refinement cover in the `W`/`π` notation used by the public helper.
    intro i
    simpa [π] using hcoverκ i
  obtain ⟨left, hleft, hleft_κ⟩ :=
    finiteBasisAugmentationOfCompositeLiftCover (J := J) (𝒪 := 𝒪) (U := U) κ hcoverκ
  have hleft_ι :
      ∀ a : Σ i : Fin n, Fin (r i),
        Sigma.ι
            (fun b : Σ i : Fin n, Fin (r i) ↦
              localizedStructureModuleExtensionByZero 𝒪 (W b.1 b.2))
            a ≫
          left =
            localizedStructureModuleExtensionByZeroMap J 𝒪 (π a.1 a.2) ≫
              Sigma.ι (fun i : Fin n ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) a.1 := by
    -- The component formula from the augmentation helper is exactly the public statement after
    -- expanding the local abbreviations `W` and `π`.
    intro a
    simpa [W, π] using hleft_κ a
  obtain ⟨lift, hcomm⟩ :=
    assembledFiniteLiftCoverOfEpi (J := J) (𝒪 := 𝒪) (U := U) q e σ κ localLift hlocalLift
      left hleft_κ
  exact ⟨r, W, π, hW, hcoverFin, left, lift, hleft, hleft_ι, hcomm⟩
/-- Helper for Lemma 18.30.8: once a finite cover-lift datum for `α` is available, adjoining it
to the original presentation map `g` presents `cokernel α`. -/
private theorem cokernelIso_of_appendedFiniteLift
    {R S T C' : SheafOfModules (ringSheaf J 𝒪)}
    (g : R ⟶ T) (α : S ⟶ cokernel g) (δ : C' ⟶ S) (β : C' ⟶ T)
    [Epi δ]
    (hcomm : δ ≫ α = β ≫ cokernel.π g) :
    cokernel (coprod.desc β g) ≅ cokernel α := by
  let l : cokernel g ⟶ cokernel (coprod.desc β g) :=
    cokernel.desc g (cokernel.π (coprod.desc β g)) (by simp)
  have hl : α ≫ l = 0 := by
    -- The added relation kills `α` after cancellation through the epimorphic cover `δ`.
    apply (cancel_epi δ).1
    rw [Category.assoc, hcomm, Category.assoc]
    simp [l, Category.assoc]
  let cofork : CokernelCofork α := CokernelCofork.ofπ l hl
  have hcofork : IsColimit cofork := by
    refine CokernelCofork.IsColimit.ofπ' l hl ?_
    intro Z k hk
    refine ⟨cokernel.desc (coprod.desc β g) (cokernel.π g ≫ k) ?_, by
      simp [l, Category.assoc]⟩
    -- The universal morphism out of the appended presentation is determined on the two summands.
    apply coprod.hom_ext
    · rw [Category.assoc, hcomm, Category.assoc, cokernel.π_desc, hk]
    · simp [Category.assoc]
  -- Compare the explicit cokernel above with the canonical chosen cokernel of `α`.
  exact (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel α) hcofork).symm

/-- Helper for Lemma 18.30.8: a finite-index cokernel presentation over arbitrary finite index
types can be reindexed into the `Fin n` form used by the public predicate. -/
private theorem hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteTypes
    {X : Mod}
    {A K : Type u} [Fintype A] [Fintype K]
    (U : A → C) (V : K → C)
    (f :
      (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) ⟶
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)))
    (e : X ≅ cokernel f)
    (hU : ∀ i, U i ∈ B) (hV : ∀ j, V j ∈ B) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B X := by
  let _ : HasColimitsOfShape (Discrete A) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) A
  let _ : HasColimitsOfShape (Discrete K) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) K
  let _ : HasColimitsOfShape (Discrete (Fin (Fintype.card A))) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) (Fin (Fintype.card A))
  let _ : HasColimitsOfShape (Discrete (Fin (Fintype.card K))) Mod :=
    Limits.hasColimitsOfShape_discrete (C := Mod) (Fin (Fintype.card K))
  let eA : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let eK : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let sourceIso :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ≅
        (∐ fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j)) :=
    Limits.Sigma.reindex eK (fun j : K ↦ localizedStructureModuleExtensionByZero 𝒪 (V j))
  let targetIso :
      (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) ≅
        (∐ fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :=
    Limits.Sigma.reindex eA (fun i : A ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))
  let f' :
      (∐ fun j : Fin (Fintype.card K) ↦ localizedStructureModuleExtensionByZero 𝒪 (V (eK j))) ⟶
        (∐ fun i : Fin (Fintype.card A) ↦ localizedStructureModuleExtensionByZero 𝒪 (U (eA i))) :=
    sourceIso.hom ≫ f ≫ targetIso.inv
  let ecoker : cokernel f ≅ cokernel f' :=
    cokernel.mapIso f f' sourceIso.symm targetIso.symm (by simp [f'])
  -- Reindex both finite direct sums to `Fin` and transport the identified cokernel across the
  -- resulting conjugation isomorphism.
  refine
    ⟨Fintype.card A, Fintype.card K,
      fun i ↦ U (eA i), fun j ↦ V (eK j), f', e ≪≫ ecoker, ?_, ?_⟩
  · intro i
    exact hU (eA i)
  · intro j
    exact hV (eK j)

/-- Helper for Lemma 18.30.8: after reducing along the source cokernel projection, the remaining
task is to show that any map from a finite coproduct of basis summands into a finitely presented
target cokernel again has finitely presented cokernel. -/
private theorem hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteSourceMap
    {n₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (g :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (α :
      (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)) ⟶
        cokernel g) :
    HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (cokernel α) := by
  obtain ⟨r, W, _, hW, _, left, lift, _, _, hcomm⟩ :=
    existsFiniteBasisLiftCoverOfEpi (J := J) (𝒪 := 𝒪) (B := B)
      U₁ hU₁ α (cokernel.π g)
  let leftIndex : Type u := Σ i : Fin n₁, Fin (r i)
  let leftFamily : leftIndex → C := fun a ↦ W a.1 a.2
  let flatIndex : Type u := Σ t : WalkingPair, WalkingPair.casesOn t leftIndex (Fin m₂)
  let flatFamily : flatIndex → C := fun a ↦
    WalkingPair.casesOn a.1 leftFamily V₂ a.2
  let binarySourceIso :
      ((∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a)) ⨿
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) ≅
        (∐ fun t : WalkingPair ↦
          WalkingPair.casesOn t
            (∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
            (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) := by
    -- Rewrite the binary coproduct as the coproduct of the walking-pair diagram.
    simpa using
      (Sigma.isoColimit
        (pair
          (∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)))).symm
  let flattenIso :
      (∐ fun t : WalkingPair ↦
        WalkingPair.casesOn t
          (∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) ≅
        (∐ fun a : flatIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (flatFamily a)) := by
    -- Flatten the two-stage coproduct into one coproduct over the sigma index.
    simpa [leftIndex, leftFamily, flatIndex, flatFamily] using
      (sigmaSigmaIso
        (fun t : WalkingPair ↦ WalkingPair.casesOn t leftIndex (Fin m₂))
        (fun t ↦ WalkingPair.casesOn t
          (fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a))
          (fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))))
  let sourceIso :
      ((∐ fun a : leftIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (leftFamily a)) ⨿
          (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j))) ≅
        (∐ fun a : flatIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (flatFamily a)) :=
    binarySourceIso ≪≫ flattenIso
  let f :
      (∐ fun a : flatIndex ↦ localizedStructureModuleExtensionByZero 𝒪 (flatFamily a)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)) :=
    sourceIso.inv ≫ coprod.desc lift g
  let ecoker :
      cokernel (coprod.desc lift g) ≅ cokernel f :=
    cokernel.mapIso (coprod.desc lift g) f sourceIso (Iso.refl _) (by simp [f])
  let e :
      cokernel α ≅ cokernel f :=
    (cokernelIso_of_appendedFiniteLift
      (J := J) (𝒪 := 𝒪) g α left lift hcomm.symm).symm ≪≫ ecoker
  have hFlat : ∀ a : flatIndex, flatFamily a ∈ B := by
    intro a
    cases a with
    | mk t x =>
        cases t with
        | left =>
            exact hW x.1 x.2
        | right =>
            exact hV₂ x
  -- Package the explicit flattened finite source map as the required finite cokernel
  -- presentation of `cokernel α`.
  exact hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteTypes
    (J := J) (𝒪 := 𝒪) (B := B)
    U₂ flatFamily f e hU₂ hFlat

-- Proof sketch: write the source module as an iterated cokernel of maps from summands
-- `j_{W!}\mathcal O_W` with `W ∈ B`, reduce to a single such summand mapping into the target
-- presentation, represent the corresponding section locally using the covering families supplied by
-- Situation `18.30.5`, use quasi-compactness of the basis objects to replace the local cover by a
-- finite one, and fold the resulting finite family into a new presentation of the cokernel.
/-- Lemma 18.30.8: in Situation `18.30.5`, the cokernel of any morphism between modules
presented as in `18.30.7.2` by basis objects again admits a finite basis cokernel presentation. -/
@[stacks 093E]
theorem ringedSite_constructibleModule_cokernel_of_morphism
    {n₁ m₁ n₂ m₂ : ℕ}
    (U₁ : Fin n₁ → C) (V₁ : Fin m₁ → C)
    (U₂ : Fin n₂ → C) (V₂ : Fin m₂ → C)
    (hU₁ : ∀ i, U₁ i ∈ B) (hV₁ : ∀ j, V₁ j ∈ B)
    (hU₂ : ∀ i, U₂ i ∈ B) (hV₂ : ∀ j, V₂ j ∈ B)
    (f :
      (∐ fun j : Fin m₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₁ j)) ⟶
        (∐ fun i : Fin n₁ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₁ i)))
    (g :
      (∐ fun j : Fin m₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (V₂ j)) ⟶
        (∐ fun i : Fin n₂ ↦ localizedStructureModuleExtensionByZero 𝒪 (U₂ i)))
    (φ : cokernel f ⟶ cokernel g) :
    SheafOfModules.RingedSite.HasFiniteBasisConstructibleModuleCokernelPresentation
      𝒪 B (cokernel φ) := by
  let α := cokernel.π f ≫ φ
  have hα :
      HasFiniteBasisConstructibleModuleCokernelPresentation 𝒪 B (cokernel α) :=
    hasFiniteBasisConstructibleModuleCokernelPresentation_of_finiteSourceMap
      (J := J) (𝒪 := 𝒪) (B := B) U₁ U₂ V₂ hU₁ hU₂ hV₂ g α
  let e : cokernel α ≅ cokernel φ :=
    cokernelIso_of_cokernelProjectionComp (J := J) (𝒪 := 𝒪) f φ
  -- Step 1 of the source proof is now verified: the source relation map contributes only through
  -- the canonical cokernel comparison isomorphism above.
  exact hasFiniteBasisConstructibleModuleCokernelPresentation_of_iso
    (J := J) (𝒪 := 𝒪) (B := B) e hα

end
