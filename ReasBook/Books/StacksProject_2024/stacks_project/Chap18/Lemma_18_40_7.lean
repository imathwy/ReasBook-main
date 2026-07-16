import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_43_3
import StacksProject_2024.stacks_project.Chap18.Definition_18_28_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_32_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_40_4

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
instance isInvertible_of_isFiniteLocallyFreeOfRank_one
    (ℒ : Mod)
    [IsFiniteLocallyFreeOfRank 1 ℒ] :
    Functor.IsEquivalence (tensorRight ℒ) := by
  let hLocalInv :
      ∀ U : C,
        ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
          ∀ i : I,
            Functor.IsEquivalence
              (tensorRight
                (((ℒ.over U).over (X i)) :
                  ringedSiteModuleCategory ((J.over U).over (X i))
                    ((𝒪.over U).over (X i)))) :=
    exists_cover_isInvertible_over_of_isFiniteLocallyFreeOfRank_one (J := J) (𝒪 := 𝒪) ℒ
  -- Proof comment: the remaining blocker is the rank-one evaluation descent. On each
  -- trivializing slice cover member, `ℒ` identifies with the singleton free module, so the
  -- evaluation map to `𝒪` is an isomorphism there. The verified frontier is the cover
  -- `hLocalInv`; what remains is the sheaf-level descent from those local evaluations to a global
  -- tensor-inverse witness.
  -- TODO: compare the canonical evaluation map on each chart from `hLocalInv` with the singleton
  -- free evaluation map, then descend the resulting local isomorphism of
  -- `ℒ ⊗ (ℒ ⟶[Mod] 𝟙)` to a global isomorphism and finish with
  -- `isInvertible_iff_exists_tensor_inverse`.
  sorry

-- Proof sketch: by Lemma `18.32.2`, an invertible module is locally a direct summand of a finite
-- free module. Over a cover satisfying the local unit-dichotomy for the structure sheaf, the
-- corresponding idempotent matrices split as finite locally free modules of constant rank, and
-- invertibility forces that local rank to be `1`.
/-- Lemma 18.40.7 (2): if every section of the structure sheaf is locally either invertible or has
invertible complement, then every invertible `\mathcal O`-module is locally free of rank `1`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_of_local_unit_dichotomy
    (ℒ : Mod)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [HasLocalUnitDichotomy J 𝒪] :
    IsFiniteLocallyFreeOfRank 1 ℒ := by
  have hOver : ∀ U : C, HasLocalUnitDichotomy (J.over U) (𝒪.over U) :=
    fun U ↦ hasLocalUnitDichotomy_over (J := J) (𝒪 := 𝒪) U
  have hRestrictedInv :
      ∀ U : C,
        Functor.IsEquivalence
          (tensorRight ((ℒ.over U) : ringedSiteModuleCategory (J.over U) (𝒪.over U))) :=
    fun U ↦ restrictionIsInvertible_over (K := J) (ℛ := 𝒪) ℒ U
  -- Route correction: the slice-site dichotomy bridge is explicit and the theorem-local closing
  -- helper `iso_freeSingleton_of_isFiniteFree_of_basisEquiv` is ready. The remaining blocker is
  -- the missing dependency-closed bridge from restricted invertibility plus local unit dichotomy
  -- to a finite-free chart cover whose chosen basis can be proved singleton.
  -- TODO: produce a finite-free cover of each slice from `hRestrictedInv` and `hOver`, extract the
  -- singleton basis equivalence on every such chart, and then finish with the new closing helper.
  sorry

end SheafOfModules.RingedSite
