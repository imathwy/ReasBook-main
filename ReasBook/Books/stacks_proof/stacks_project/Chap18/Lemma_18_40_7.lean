import Mathlib
import StacksProject_2024.Chap04.Lemma_4_43_3
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_23_3
import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.Lemma_18_32_2
import StacksProject_2024.Chap18.Lemma_18_32_4
import StacksProject_2024.Chap18.Lemma_18_40_1
import StacksProject_2024.Chap18.Definition_18_40_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/-- Helper for Lemma 18.40.7: local rank-`r` trivializations already exhibit a module as a local
direct summand of a finite free module. -/
private theorem isLocallyDirectSummandOfFiniteFree_of_isFiniteLocallyFreeOfRank
    (r : ℕ) (ℱ : Mod)
    [IsFiniteLocallyFreeOfRank r ℱ] :
    IsLocallyDirectSummandOfFiniteFree ℱ := by
  -- Proof comment: on each cover member from `exists_iso_free_over`, the chosen local
  -- trivialization already provides the split inclusion and retraction maps.
  rw [isLocallyDirectSummandOfFiniteFree_iff]
  intro U
  rcases (inferInstance : IsFiniteLocallyFreeOfRank r ℱ).exists_iso_free_over U with
    ⟨I, X, hX, hfree⟩
  refine ⟨I, X, hX, ?_⟩
  intro i
  rcases hfree i with ⟨e⟩
  refine ⟨ULift.{max u v} (Fin r), inferInstance, e.hom, e.inv, ?_⟩
  simp

/-- Helper for Lemma 18.40.7: the local unit dichotomy on `(\mathcal C, \mathcal O)` restricts
to every slice site `(\mathcal C/U, \mathcal O_U)`. -/
private theorem hasLocalUnitDichotomy_over
    [HasLocalUnitDichotomy J 𝒪]
    (U : C) :
    HasLocalUnitDichotomy (J.over U) (𝒪.over U) := by
  refine
    { local_unit_dichotomy := fun X f ↦ ?_ }
  -- Proof comment: pull back the covering on `X.left` to the slice site and read the localized
  -- restriction maps as the original restriction maps in `𝒪`.
  obtain ⟨S, hS⟩ := HasLocalUnitDichotomy.local_unit_dichotomy (J := J) (𝒪 := 𝒪) X.left f
  let SOver : (J.over U).Cover X :=
    ⟨(Sieve.overEquiv X).symm (S : Sieve X.left), by
      rw [GrothendieckTopology.mem_over_iff]
      simpa using S.property⟩
  refine ⟨SOver, ?_⟩
  intro I
  let iOver : I.Y ⟶ X := I.f
  have hI : ((S : Sieve X.left).arrows iOver.left) := by
    have hIOver : ((Sieve.overEquiv X) SOver.1).arrows iOver.left := by
      rw [Sieve.overEquiv_iff]
      exact I.hf
    simpa [SOver] using hIOver
  let IBase : S.Arrow := ⟨I.Y.left, iOver.left, hI⟩
  simpa [Sheaf.over, GrothendieckTopology.overPullback] using hS IBase

/-- Helper for Lemma 18.40.7: on any ringed site, the free module on one generator is the
structure sheaf module. -/
private theorem freeSingletonIsoUnit
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {ℛ : Sheaf K CommRingCat.{max u v}} :
    Nonempty
      ((SheafOfModules.free (ULift.{max u v} (Fin 1)) :
          ringedSiteModuleCategory K ℛ) ≅
        (unitModule K ℛ : ringedSiteModuleCategory K ℛ)) := by
  let c : Cofan (fun _ : ULift.{max u v} (Fin 1) ↦
      (unitModule K ℛ : ringedSiteModuleCategory K ℛ)) :=
    Cofan.mk
      (P := (unitModule K ℛ : ringedSiteModuleCategory K ℛ))
      (fun _ ↦ 𝟙 _)
  let hc : IsColimit c :=
    mkCofanColimit c
      (fun t ↦ t.inj (default : ULift.{max u v} (Fin 1)))
      (fun t j ↦ by
        simpa [c, Subsingleton.elim j (default : ULift.{max u v} (Fin 1))])
      (fun t m hm ↦ by
        simpa [c] using hm (default : ULift.{max u v} (Fin 1)))
  -- Proof comment: the structure sheaf module is the coproduct of one copy of itself, so it
  -- matches the free singleton module by the universal property of the coproduct.
  refine ⟨?_⟩
  exact
    (IsColimit.coconePointUniqueUpToIso hc
      (SheafOfModules.isColimitFreeCofan
        (R := ringSheaf K ℛ) (ULift.{max u v} (Fin 1)))).symm

/-- Helper for Lemma 18.40.7: the free singleton module is invertible because it is isomorphic to
the structure sheaf module. -/
private theorem freeSingletonIsInvertible
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {ℛ : Sheaf K CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory K ℛ)] :
    Functor.IsEquivalence
      (tensorRight
        (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
          ringedSiteModuleCategory K ℛ)) := by
  rcases freeSingletonIsoUnit (K := K) (ℛ := ℛ) with ⟨e⟩
  letI :
      Functor.IsEquivalence
        (tensorRight (unitModule K ℛ : ringedSiteModuleCategory K ℛ)) := by
    infer_instance
  -- Proof comment: tensoring by isomorphic modules gives isomorphic tensor-right functors, so the
  -- unit-module equivalence transports directly across the singleton-free normalization.
  exact Functor.isEquivalence_of_iso ((tensoringRight _).mapIso e)

/-- Helper for Lemma 18.40.7: any module identified with the singleton free module is invertible.
-/
private theorem isInvertible_of_iso_freeSingleton
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {ℛ : Sheaf K CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory K ℛ)]
    (M : ringedSiteModuleCategory K ℛ)
    (e :
      M ≅
        (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
          ringedSiteModuleCategory K ℛ)) :
    Functor.IsEquivalence (tensorRight M) := by
  letI :
      Functor.IsEquivalence
        (tensorRight
          (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
            ringedSiteModuleCategory K ℛ)) :=
    freeSingletonIsInvertible (K := K) (ℛ := ℛ)
  -- Proof comment: invertibility is invariant under isomorphism because tensor-right functors
  -- transport across `tensoringRight`.
  exact Functor.isEquivalence_of_iso ((tensoringRight _).mapIso e)

/-- Helper for Lemma 18.40.7: restricting an invertible module to a slice site preserves
invertibility. -/
private theorem restrictionIsInvertible_over
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {ℛ : Sheaf K CommRingCat.{max u v}}
    [MonoidalCategory (ringedSiteModuleCategory K ℛ)]
    (M : ringedSiteModuleCategory K ℛ)
    [Functor.IsEquivalence (tensorRight M)]
    (U : D) :
    Functor.IsEquivalence
      (tensorRight ((M.over U) : ringedSiteModuleCategory (K.over U) (ℛ.over U))) := by
  let hRestricted :
      Functor.IsEquivalence
        (tensorRight
          (((ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U).obj M) :
            ringedSiteModuleCategory (K.over U) (ℛ.over U))) := by
    rcases (tensorRight_isEquivalence_iff_exists_tensor_inverse M).1 inferInstance with
      ⟨N, ⟨⟨eLeft⟩, ⟨eRight⟩⟩⟩
    -- Proof comment: the localized restriction functor is monoidal, so it carries a chosen
    -- tensor inverse of `M` to a tensor inverse of the restricted module.
    exact
      (tensorRight_isEquivalence_iff_exists_tensor_inverse
        (((ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U).obj M) :
          ringedSiteModuleCategory (K.over U) (ℛ.over U))).2
        ⟨((ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U).obj N), ⟨
          ⟨(Functor.Monoidal.μIso
              (ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U) M N) ≪≫
            (ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U).mapIso eLeft ≪≫
            (Functor.Monoidal.εIso
              (ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U)).symm⟩,
          ⟨(Functor.Monoidal.μIso
              (ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U) N M) ≪≫
            (ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U).mapIso eRight ≪≫
            (Functor.Monoidal.εIso
              (ringedSiteLocalizedRestriction (J := K) (𝒪 := ℛ) U)).symm⟩⟩⟩
  simpa [ringedSiteLocalizedRestriction, SheafOfModules.over] using hRestricted

/-- Helper for Lemma 18.40.7: a rank-one local trivialization makes every slice-cover member
invertible. -/
private theorem exists_cover_isInvertible_over_of_isFiniteLocallyFreeOfRank_one
    (ℒ : Mod)
    [IsFiniteLocallyFreeOfRank 1 ℒ]
    (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I,
        Functor.IsEquivalence
          (tensorRight
            (((ℒ.over U).over (X i)) :
              ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i)))) := by
  rcases (inferInstance : IsFiniteLocallyFreeOfRank 1 ℒ).exists_iso_free_over U with
    ⟨I, X, hX, hfree⟩
  refine ⟨I, X, hX, ?_⟩
  intro i
  rcases hfree i with ⟨e⟩
  -- Proof comment: each chosen local chart is literally the singleton free module, so its
  -- invertibility follows by transport from the singleton-free model.
  exact isInvertible_of_iso_freeSingleton _ e

/-- Helper for Lemma 18.40.7: a finite free chart whose chosen basis is equivalent to a singleton
basis is itself the singleton free module. -/
private theorem iso_freeSingleton_of_isFiniteFree_of_basisEquiv
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [HasWeakSheafify K AddCommGrpCat.{max u v}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [K.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{max u v})]
    {ℛ : Sheaf K CommRingCat.{max u v}}
    (M : ringedSiteModuleCategory K ℛ)
    [SheafOfModules.IsFiniteFree M]
    {α : Type (max u v)} (e : M ≅ SheafOfModules.free α)
    (hα : α ≃ ULift.{max u v} (Fin 1)) :
    Nonempty
      (M ≅
        (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
          ringedSiteModuleCategory K ℛ)) := by
  -- Proof comment: reindex the chosen finite free model along the equivalence `hα`, then compose
  -- with the original finite free trivialization of `M`.
  refine ⟨e ≪≫ ?_⟩
  exact (SheafOfModules.freeFunctor (R := ringSheaf K ℛ)).mapIso (Equiv.toIso hα)

/-- Helper for Lemma 18.40.7: if the canonical evaluation map against the internal-Hom dual is an
isomorphism, then the module is invertible. -/
private theorem isInvertible_of_evaluationIso
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
    (ℒ : Mod)
    (hEval : IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪)))) :
    Functor.IsEquivalence (tensorRight ℒ) := by
  letI : IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) := hEval
  let D : Mod := (ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))
  let e :
      (ℒ ⊗ D) ≅ (𝟙_ Mod : Mod) :=
    { hom :=
        ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) ≫
          (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).hom
      inv :=
        (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv ≫
          inv ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪)))
      hom_inv_id := by
        simp [Category.assoc]
      inv_hom_id := by
        simp [Category.assoc] }
  -- Proof comment: the evaluation isomorphism exhibits the internal-Hom dual as a one-sided
  -- tensor inverse, and the symmetric braiding supplies the opposite trivialization required by
  -- the owner equivalence criterion.
  exact
    (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).2
      ⟨D, ⟨⟨e⟩, ⟨(β_ D ℒ) ≪≫ e⟩⟩⟩

/-- Helper for Lemma 18.40.7: objectwise evaluation detects isomorphisms of sheaf modules. -/
private theorem module_isIso_of_evaluation_isIso
    {M N : Mod} (f : M ⟶ N)
    (hf : ∀ U : Cᵒᵖ, IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f)) :
    IsIso f := by
  have hIsoPresheaf :
      IsIso
        ((sheafToPresheaf J AddCommGrpCat).map
          ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f)) := by
    -- Proof comment: after forgetting module structure and then the sheaf condition, the
    -- evaluation hypothesis says every presheaf component is an isomorphism.
    refine (NatTrans.isIso_iff_isIso_app _).2 ?_
    intro U
    let _ : IsIso ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f) := hf U
    let _ := Functor.map_isIso
      (forget₂ (ModuleCat ((ringSheaf J 𝒪).1.obj U)) AddCommGrpCat)
      ((SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f)
    simpa [SheafOfModules.evaluation, SheafOfModules.toSheaf]
  have hIsoToSheaf :
      IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f) := by
    -- Proof comment: the underlying additive-sheaf functor reflects isomorphisms from the
    -- objectwise presheaf comparison.
    letI :
        IsIso
          ((sheafToPresheaf J AddCommGrpCat).map
            ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f)) :=
      hIsoPresheaf
    exact isIso_of_reflects_iso
      ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f)
      (sheafToPresheaf J AddCommGrpCat)
  -- Proof comment: the module-sheaf forgetful functor now reflects the remaining isomorphism.
  letI : IsIso ((SheafOfModules.toSheaf (ringSheaf J 𝒪)).map f) := hIsoToSheaf
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf (ringSheaf J 𝒪))

/-- Helper for Lemma 18.40.7: objectwise evaluation of a morphism agrees definitionally with
terminal evaluation after restricting to the slice site over the chosen object. -/
private theorem evaluation_over_terminal_map_eq
    (U : Cᵒᵖ) {M N : Mod} (f : M ⟶ N) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) U).map f =
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
          (Opposite.op (Over.mk (𝟙 U.unop)))).map
        ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U.unop))).map f) := by
  -- Proof comment: both sides are the same terminal component of the restricted morphism.
  rfl

/-- Helper for Lemma 18.40.7: a rank-one locally free module has an evaluation map that is
objectwise an isomorphism after passing to the slice over each object. -/
private theorem evaluationIso_of_isFiniteLocallyFreeOfRank_one
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]
    (ℒ : Mod)
    [IsFiniteLocallyFreeOfRank 1 ℒ] :
    IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) := by
  let f : ℒ ⟶
      (ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪)) ⟶[ModuleCat _]
        SheafOfModules.unit (ringSheaf J 𝒪) :=
    (ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))
  -- Route correction: instead of descending from a chartwise cover, evaluate `f` at each object,
  -- identify that evaluation with terminal evaluation on the slice over that object, and use the
  -- slice-site invertibility theorem there.
  refine module_isIso_of_evaluation_isIso (J := J) (𝒪 := 𝒪) f ?_
  intro U
  letI :
      Functor.IsEquivalence
        (tensorRight
          ((ℒ.over U.unop) : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop))) :=
    restrictionIsInvertible_over (K := J) (ℛ := 𝒪) ℒ U.unop
  have hRestricted :
      IsIso
        ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U.unop))).map f) := by
    -- Proof comment: on the slice site over `U`, the restricted module is invertible, so the
    -- standard internal-Hom evaluation map is an isomorphism there.
    simpa [f] using
      (SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible
        (J := J.over U.unop) (𝒪 := 𝒪.over U.unop)
        ((ℒ.over U.unop) : ringedSiteModuleCategory (J.over U.unop) (𝒪.over U.unop)))
  have hTerminal :
      IsIso
        ((SheafOfModules.evaluation ((ringSheaf J 𝒪).over U.unop)
            (Opposite.op (Over.mk (𝟙 U.unop)))).map
          ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U.unop))).map f)) := by
    -- Proof comment: evaluation at the terminal object of the slice preserves the slice
    -- evaluation isomorphism.
    letI : IsIso ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U.unop))).map f) :=
      hRestricted
    infer_instance
  simpa [evaluation_over_terminal_map_eq (J := J) (𝒪 := 𝒪) U f] using hTerminal

/-- Helper for Lemma 18.40.7: forgetting the slice structure on a family of objects over `U`
identifies the induced covering sieve on the terminal slice object with the ordinary sieve
generated by the underlying arrows. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {ι : Type (max u v)} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  -- Proof comment: a factorization in the slice category is exactly the same data as a
  -- factorization of the underlying arrows in the base category.
  ext W g
  constructor
  · intro hg
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 18.40.7: composing a slice cover of `U` with slice covers of each member
gives a sigma-indexed slice cover of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {I : Type (max u v)} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    {K : I → Type (max u v)} {Y : ∀ i : I, K i → Over (X i).left}
    (hY : ∀ i : I, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Sigma K ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Proof comment: first translate both slice-cover hypotheses into covering sieves downstairs,
  -- then apply the transitivity axiom `bindOfArrows` and repackage the result upstairs.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)).1 hX
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hXTerminal
    exact hXTerminal
  have hY' :
      ∀ i : I,
        Sieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom) ∈ J (X i).left := by
    intro i
    have hYTerminal :
        Sieve.ofObjects (Y i) (Over.mk (𝟙 (X i).left)) ∈
          (J.over (X i).left) (Over.mk (𝟙 (X i).left)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over (X i).left) (X := Over.mk (𝟙 (X i).left))
        (hX := Over.mkIdTerminal)).1 (hY i)
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hYTerminal
    exact hYTerminal
  simpa [Presieve.bindOfArrows_ofArrows] using
    J.bindOfArrows
      (h := hX')
      (R := fun i ↦
        Presieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom))
      (fun i ↦ by simpa using hY' i)

/-- Helper for Chap18 Lemma 18 40 7: finite global generation persists after one more slice
restriction. -/
private theorem isFiniteGloballyGenerated_of_retract_free_on_slice
    {U : C} {X : Over U} {α : Type (max u v)} [Finite α]
    {M : ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)}
    (ι : M ⟶ (SheafOfModules.free α))
    (π : (SheafOfModules.free α) ⟶ M)
    (hιπ : ι ≫ π = 𝟙 M) :
    SheafOfModules.IsFiniteGloballyGenerated M := by
  let σFree :
      (SheafOfModules.free α :
        ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)).GeneratingSections :=
    { I := α
      s := SheafOfModules.freeSection
        (R := ringSheaf ((J.over U).over X) ((𝒪.over U).over X))
      epi := SheafOfModules.free_tautological_sections_epi
        (𝒪 := ringSheaf ((J.over U).over X) ((𝒪.over U).over X)) α }
  let _ : Epi π := ⟨⟨ι, hιπ⟩⟩
  let σ : M.GeneratingSections := σFree.ofEpi π
  have hσ : σ.IsFiniteType := by
    -- Proof comment: `ofEpi` keeps the same finite index type as the tautological basis family.
    change Finite σ.I
    simpa [σ, σFree, SheafOfModules.GeneratingSections.ofEpi] using
      (inferInstance : Finite α)
  -- Proof comment: the split surjection from a finite free module pushes its finite basis
  -- generators forward to a finite generating family of `M`.
  exact
    (SheafOfModules.isFiniteGloballyGenerated_iff_nonempty_finiteGeneratingSections
      (𝒪 := ringSheaf ((J.over U).over X) ((𝒪.over U).over X)) M).2
      ⟨⟨σ, hσ⟩⟩

/-- Helper for Chap18 Lemma 18 40 7: restricting a terminal value along the unique maps from the
slice terminal object is compatible with all restriction maps. -/
private theorem overSectionsFromTerminalNaturality
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    ∀ V Y : (Over U)ᵒᵖ, ∀ f : V ⟶ Y,
      M.val.map f (M.val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        M.val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of the slice admits a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Chap18 Lemma 18 40 7: a terminal value determines a section on the slice site by
restriction from the terminal object. -/
private noncomputable def overSectionsFromTerminal
    {U : C} (M : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (m : M.val.obj (op (Over.mk (𝟙 U)))) : M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (overSectionsFromTerminalNaturality (M := M) m)

/-- Helper for Chap18 Lemma 18 40 7: a slice section is determined by its value at the terminal
object. -/
private theorem overSectionsEquivTerminalLeftInv
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (s : M.sections) :
    overSectionsFromTerminal M (s.1 (op (Over.mk (𝟙 U)))) = s := by
  -- Proof comment: every slice component is the restriction of the terminal component.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Chap18 Lemma 18 40 7: evaluating the reconstructed section at the terminal object
recovers the original terminal value. -/
private theorem overSectionsEquivTerminalRightInv
    {U : C} {M : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    (overSectionsFromTerminal M m).1 (op (Over.mk (𝟙 U))) = m := by
  -- Proof comment: the terminal object only maps to itself by the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Chap18 Lemma 18 40 7: evaluating at the terminal object gives an equivalence
between slice sections and terminal values. -/
private noncomputable def overSectionsEquivTerminal
    {U : C} (M : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
    invFun := overSectionsFromTerminal M
    left_inv := overSectionsEquivTerminalLeftInv (M := M)
    right_inv := overSectionsEquivTerminalRightInv (M := M) }

/-- Helper for Chap18 Lemma 18 40 7: under terminal evaluation, a section map is exactly the
terminal component of the underlying sheaf morphism. -/
private theorem overSectionsEquivTerminalSectionsMap
    {U : C} {M N : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivTerminal N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (op (Over.mk (𝟙 U)))) (overSectionsEquivTerminal M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Chap18 Lemma 18 40 7: the inverse terminal-evaluation equivalence is natural in
the module-sheaf morphism. -/
private theorem sectionsMap_overSectionsEquivTerminal_symm
    {U : C} {M N : ringedSiteModuleCategory (J.over U) (𝒪.over U)}
    (ψ : M ⟶ N) (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((overSectionsEquivTerminal M).symm m) =
      (overSectionsEquivTerminal N).symm ((ψ.val.app (op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation.
  apply (overSectionsEquivTerminal N).injective
  rw [overSectionsEquivTerminalSectionsMap]
  simp

/-- Helper for Chap18 Lemma 18 40 7: on a slice site, sections of an internal-Hom sheaf are
naturally equivalent to morphisms from the source sheaf. -/
private noncomputable def overSectionsEquivHom
    {U : C} (M N : ringedSiteModuleCategory (J.over U) (𝒪.over U)) :
    (((ihom M).obj N).sections) ≃ (M ⟶ N) :=
  (overSectionsEquivTerminal ((ihom M).obj N)).symm.trans <|
    ((((ihom M).obj N).unitHomEquiv).symm.trans <|
      ((((ihom.adjunction M).homEquiv
          (SheafOfModules.unit (ringSheaf (J.over U) (𝒪.over U))) N).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N)))))

/-- Helper for Chap18 Lemma 18 40 7: under `overSectionsEquivHom`, mapping sections of internal
Hom by a target morphism is postcomposition on the corresponding sheaf morphisms. -/
private theorem sectionsMap_overSectionsEquivHom_symm
    {U : C} (M : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    {N₁ N₂ : ringedSiteModuleCategory (J.over U) (𝒪.over U)} (f : N₁ ⟶ N₂) (g : M ⟶ N₁) :
    SheafOfModules.sectionsMap ((ihom M).map f) ((overSectionsEquivHom M N₁).symm g) =
      (overSectionsEquivHom M N₂).symm (g ≫ f) := by
  -- Proof comment: compare both sides after translating slice internal-Hom sections to actual
  -- morphisms by the terminal-evaluation/Hom bridge.
  apply (overSectionsEquivHom M N₂).injective
  rw [overSectionsEquivTerminalSectionsMap]
  change (((ihom M).obj N₂).unitHomEquiv
      (((((ihom.adjunction M).homEquiv
          (SheafOfModules.unit (ringSheaf (J.over U) (𝒪.over U))) N₁).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N₁)))).symm g ≫
          (ihom M).map f)) =
    (((ihom M).obj N₂).unitHomEquiv
      (((((ihom.adjunction M).homEquiv
          (SheafOfModules.unit (ringSheaf (J.over U) (𝒪.over U))) N₂).symm).trans
        (((λ_ M).symm.homCongr (Iso.refl N₂)))).symm (g ≫ f)))
  congr 1
  dsimp
  rw [(ihom.adjunction M).homEquiv_naturality_right_symm]
  simp

/-- Helper for Chap18 Lemma 18 40 7: finite global generation persists after one more slice
restriction. -/
private theorem isFiniteGloballyGenerated_over_of_isFiniteGloballyGenerated
    {U : C}
    (M : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    [SheafOfModules.IsFiniteGloballyGenerated M]
    (X : Over U) :
    SheafOfModules.IsFiniteGloballyGenerated
      ((M.over X) :
        ringedSiteModuleCategory ((J.over U).over X) ((𝒪.over U).over X)) := by
  let hRestricted :
      SheafOfModules.IsFiniteGloballyGenerated
        (((ringedSiteLocalizedRestriction (J := J.over U) (𝒪 := 𝒪.over U) X.left).obj M) :
          ringedSiteModuleCategory ((J.over U).over X.left) ((𝒪.over U).over X.left)) := by
    -- Proof comment: finite global generation is preserved by pullback along the localized
    -- restriction functor.
    infer_instance
  -- Proof comment: `M.over X` is definitionaly the localized restriction to the iterated slice.
  simpa [ringedSiteLocalizedRestriction, SheafOfModules.over] using hRestricted

/-- Helper for Chap18 Lemma 18 40 7: on a slice site, `unitHomEquiv` is computed by evaluating
the corresponding unit morphism at the terminal section `1`. -/
private theorem unitHomEquiv_apply_terminal
    {U : C} (M : ringedSiteModuleCategory (J.over U) (𝒪.over U))
    (φ : SheafOfModules.unit (ringSheaf (J.over U) (𝒪.over U)) ⟶ M) :
    (SheafOfModules.unitHomEquiv M φ).1 (op (Over.mk (𝟙 U))) =
      (φ.val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit (ringSheaf (J.over U) (𝒪.over U))).val.obj
            (op (Over.mk (𝟙 U)))) from
          (1 : (ringSheaf (J.over U) (𝒪.over U)).obj (op (Over.mk (𝟙 U))))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluating the unit morphism on the terminal
  -- section `1`.
  rfl

/-- Helper for Lemma 18.40.7: on each slice site, invertibility plus local unit dichotomy should
refine the existing direct-summand finite-free cover to a singleton free cover. -/
private theorem exists_iso_freeSingleton_over_of_isInvertible_of_local_unit_dichotomy
    [HasLocalUnitDichotomy J 𝒪]
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          Nonempty
            ((((ℒ.over U).over (X i)) :
                ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i))) ≅
              (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
                ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i)))) := by
  intro U
  have hOver : HasLocalUnitDichotomy (J.over U) (𝒪.over U) :=
    hasLocalUnitDichotomy_over (J := J) (𝒪 := 𝒪) U
  have hRestrictedInv :
      Functor.IsEquivalence
        (tensorRight ((ℒ.over U) : ringedSiteModuleCategory (J.over U) (𝒪.over U))) :=
    restrictionIsInvertible_over (K := J) (ℛ := 𝒪) ℒ U
  have hDirectSummand :
      IsLocallyDirectSummandOfFiniteFree
        ((ℒ.over U) : ringedSiteModuleCategory (J.over U) (𝒪.over U)) := by
    -- Proof comment: invertibility on the slice over `U` gives the standard direct-summand cover.
    exact
      SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible
        (J := J.over U) (𝒪 := 𝒪.over U)
        ((ℒ.over U) : ringedSiteModuleCategory (J.over U) (𝒪.over U))
  rcases
      (isLocallyDirectSummandOfFiniteFree_iff
        ((ℒ.over U) : ringedSiteModuleCategory (J.over U) (𝒪.over U))).1
        hDirectSummand (Over.mk (𝟙 U)) with
    ⟨I, X, hX, hsplit⟩
  choose α hα ι π hιπ using hsplit
  have hChartInv :
      ∀ i : I,
        Functor.IsEquivalence
          (tensorRight
            ((((ℒ.over U).over (X i)) :
              ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i))))) := by
    intro i
    -- Proof comment: each iterated slice restriction of an invertible module is still invertible.
    exact
      restrictionIsInvertible_over (K := J.over U) (ℛ := 𝒪.over U)
        ((ℒ.over U) : ringedSiteModuleCategory (J.over U) (𝒪.over U)) (X i)
  -- Route correction: the slice-site dichotomy and restriction-of-invertibility bridges are both
  -- explicit, and the proof is now reduced to the chartwise problem on the direct-summand cover
  -- `X`: each restricted chart is invertible and split off from a finite free module.
  have hChartFGG :
      ∀ i : I,
        SheafOfModules.IsFiniteGloballyGenerated
          ((((ℒ.over U).over (X i)) :
            ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i)))) := by
    intro i
    -- Proof comment: the chosen split surjection from the finite free chart immediately gives a
    -- finite global generating family for the chart module.
    exact isFiniteGloballyGenerated_of_retract_free_on_slice
      (J := J) (𝒪 := 𝒪) (ι i) (π i) (hιπ i)
  choose K Y hY hDualFGG using
    fun i : I ↦ by
      let M :
          ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i)) :=
        ((ℒ.over U).over (X i))
      let D :
          ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i)) :=
        (ihom M).obj (unitModule ((J.over U).over (X i)) ((𝒪.over U).over (X i)))
      let _ : Functor.IsEquivalence (tensorRight M) := hChartInv i
      let _ : Functor.IsEquivalence (tensorRight D) :=
        SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible
          (J := (J.over U).over (X i)) (𝒪 := (𝒪.over U).over (X i)) M
      let _ : SheafOfModules.IsFinitePresentation D :=
        SheafOfModules.RingedSite.isFinitePresentation_of_isInvertible
          (J := (J.over U).over (X i)) (𝒪 := (𝒪.over U).over (X i)) D
      have hD :
          SheafOfModules.IsFiniteType D := by
        infer_instance
      exact
        (SheafOfModules.RingedSite.isFiniteType_iff_exists_cover_isFiniteGloballyGenerated_over
          (J := (J.over U).over (X i)) (𝒪 := (𝒪.over U).over (X i)) D).1 hD
  refine ⟨Sigma K, fun a ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom),
    coversTopSigmaComp (J := J) (U := U) hX hY, ?_⟩
  intro a
  let M :
      ringedSiteModuleCategory ((J.over U).over (X a.1)) ((𝒪.over U).over (X a.1)) :=
    ((ℒ.over U).over (X a.1))
  let D :
      ringedSiteModuleCategory ((J.over U).over (X a.1)) ((𝒪.over U).over (X a.1)) :=
    (ihom M).obj (unitModule ((J.over U).over (X a.1)) ((𝒪.over U).over (X a.1)))
  have hMRefined :
      SheafOfModules.IsFiniteGloballyGenerated
        ((M.over (Y a.1 a.2)) :
          ringedSiteModuleCategory
            (((J.over U).over (X a.1)).over (Y a.1 a.2))
            (((𝒪.over U).over (X a.1)).over (Y a.1 a.2))) := by
    -- Proof comment: the chartwise finite generating family survives one more slice restriction.
    exact isFiniteGloballyGenerated_over_of_isFiniteGloballyGenerated
      (J := (J.over U).over (X a.1)) (𝒪 := (𝒪.over U).over (X a.1)) M (Y a.1 a.2)
  have hDRefined :
      SheafOfModules.IsFiniteGloballyGenerated
        ((D.over (Y a.1 a.2)) :
          ringedSiteModuleCategory
            (((J.over U).over (X a.1)).over (Y a.1 a.2))
            (((𝒪.over U).over (X a.1)).over (Y a.1 a.2))) := by
    simpa [D] using hDualFGG a.1 a.2
  -- TODO: use `hMRefined` and `hDRefined` to build a finite generating family of the refined
  -- `unitModule`, apply local unit dichotomy on the iterated slice to pick a unit coefficient,
  -- convert the selected dual section to a morphism via `overSectionsEquivHom`, and then
  -- trivialize the refined chart with the resulting unit evaluation coefficient.
  sorry

/-- Helper for Lemma 18.40.7: a cover by singleton free local charts is exactly the data required
for rank-one local freeness. -/
private theorem isFiniteLocallyFreeOfRank_one_of_exists_iso_freeSingleton_over
    (ℒ : Mod)
    (h :
      ∀ U : C,
        ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
          ∀ i : I,
            Nonempty
              ((((ℒ.over U).over (X i)) :
                  ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i))) ≅
                (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
                  ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i)))) ) :
    IsFiniteLocallyFreeOfRank 1 ℒ := by
  -- Proof comment: this helper just repackages the chartwise singleton-free data into the owner
  -- class `IsFiniteLocallyFreeOfRank 1`.
  exact ⟨h⟩

/- Domain-style sampling for Lemma 18.40.7:
- primary domain: rank-one finite locally free modules and invertible modules on a ringed site;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFiniteLocallyFreeOfRank`,
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `CategoryTheory.HasLocalUnitDichotomy`,
  `CategoryTheory.IsLocallyRingedSite`;
- best owner abstractions:
  the source-facing clauses should be expressed directly in terms of the Chapter 18 owners
  `IsFiniteLocallyFreeOfRank`, `Functor.IsEquivalence (tensorRight ℒ)`, and the local-dichotomy
  owner
  `HasLocalUnitDichotomy`, rather than by repeating the latter as an ad hoc quantified hypothesis;
- primitive data:
  the module `ℒ` and the ambient local unit dichotomy on the structure sheaf;
- derived API:
  the invertibility instance for rank-one locally free modules and the converse rank-one local
  freeness statement under the local unit dichotomy.

Source/core/bridge triage:
- `source-facing`: the two clauses of Stacks Lemma 18.40.7;
- `core/canonical`: `IsFiniteLocallyFreeOfRank`,
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `CategoryTheory.HasLocalUnitDichotomy`;
- `bridge/view`: the local unit dichotomy is reused through its chapter owner, not restated as a
  parallel quantified parameter.
-/

-- Proof sketch: for a rank-one local trivialization, the evaluation map
-- `\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)
-- \to \mathcal O` is locally identified with the standard evaluation map for
-- `\mathcal O_U`, hence is an isomorphism on a cover; Lemma `18.32.2` then gives invertibility.
/-- Lemma 18.40.7 (1): on a ringed site, a locally free `\mathcal O`-module of rank `1` is
invertible. -/
@[stacks 0B8Q]
instance isInvertible_of_isFiniteLocallyFreeOfRank_one
    (ℒ : Mod)
    [IsFiniteLocallyFreeOfRank 1 ℒ] :
    Functor.IsEquivalence (tensorRight ℒ) := by
  have hEval :
      IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) := by
    exact evaluationIso_of_isFiniteLocallyFreeOfRank_one (J := J) (𝒪 := 𝒪) ℒ
  -- Proof comment: once the evaluation map is globally an isomorphism, the internal-Hom dual is a
  -- tensor inverse by the closing helper above.
  exact isInvertible_of_evaluationIso (J := J) (𝒪 := 𝒪) ℒ hEval

-- Proof sketch: by Lemma `18.32.2`, an invertible module is locally a direct summand of a finite
-- free module. Over a cover satisfying the local unit-dichotomy for the structure sheaf, the
-- corresponding idempotent matrices split as finite locally free modules of constant rank, and
-- invertibility forces that local rank to be `1`.
/-- Lemma 18.40.7 (2): if every section of the structure sheaf is locally either invertible or has
invertible complement, then every invertible `\mathcal O`-module is locally free of rank `1`. -/
@[stacks 0B8Q]
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_local_unit_dichotomy
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [HasLocalUnitDichotomy J 𝒪] :
    IsFiniteLocallyFreeOfRank 1 ℒ := by
  refine
    isFiniteLocallyFreeOfRank_one_of_exists_iso_freeSingleton_over
      (J := J) (𝒪 := 𝒪) ℒ ?_
  exact exists_iso_freeSingleton_over_of_isInvertible_of_local_unit_dichotomy
    (J := J) (𝒪 := 𝒪) ℒ

end SheafOfModules.RingedSite
