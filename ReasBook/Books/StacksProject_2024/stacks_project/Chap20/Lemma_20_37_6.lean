import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap13.Remark_13_34_5
import StacksProject_2024.stacks_project.Chap20.AddCommGrpCatHasDerivedCategory
import StacksProject_2024.stacks_project.Chap20.RingedSpaceModuleHasDerivedCategory
import StacksProject_2024.stacks_project.Chap20.Lemma_20_37_5
import StacksProject_2024.stacks_project.Chap20.«20_11_0_1»

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open DerivedCategory
open DerivedCategory.TStructure
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry.RingedSpaceCohomology
open scoped RingedSpaceDerivedSectionsAtOpenToAb

noncomputable section

universe u v w

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})

local notation "ModX" => RingedSpace.Modules X
local notation "H" => DerivedCategory.homologyFunctor ModX

/-
Domain-style sampling for Lemma 20.37.6:
- primary domain: compatible truncation-limit comparisons in `D(𝒪_X)` and local vanishing of
  the cohomology sheaves of a derived `𝒪_X`-module on a ringed space;
- sampled owner declarations:
  `𝓗[q](X, E)`,
  `moduleUnderlyingSheaf`,
  `TopCat.Presheaf.stalkFunctor`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`,
  `sheafModules_isGrothendieckAbelian`;
- best owner abstraction: the chapter owner predicate
  `IsTruncationDerivedLimitComparison` for the comparison morphism together with the Chapter 20
  cohomology-sheaf notation `𝓗[q](X, E)` for the local values, the direct canonical map
  `((moduleUnderlyingSheaf X).map ((H q).map f))`, and its stalk map via
  `TopCat.Presheaf.stalkFunctor`; the present file should keep only the source-facing
  eventual-vanishing condition and the bridge theorem proving that a compatible truncation-limit
  comparison is an isomorphism;
- primitive data: `E`, `L`, `c`, the comparison hypothesis `hc`, and the pointwise shrinking
  vanishing condition `EventualCohomologySheafVanishingNear X E`;
- derived API: the isomorphism criterion for `c`; the Grothendieck-abelian structure on
  `X.Modules` is proof support supplied canonically by `sheafModules_isGrothendieckAbelian X`,
  not part of the source-facing statement.

Source/core/bridge triage:
- `source-facing`: `EventualCohomologySheafVanishingNear`;
- `core/canonical`: `𝓗[q](X, E)`, `moduleUnderlyingSheaf`,
  `TopCat.Presheaf.stalkFunctor`, `DerivedCategory.homologyFunctor`,
  `IsTruncationDerivedLimitComparison`, and `sheafModules_isGrothendieckAbelian`;
- `bridge/view`:
  `isIso_of_truncationDerivedLimitComparison_of_eventualCohomologySheafVanishingNear`.
-/

/-- A derived `𝒪_X`-module has eventually vanishing local cohomology of its cohomology
sheaves near each point if, after shrinking inside any neighborhood of `x`, one gets a uniform
bound in each total degree beyond which the groups `H^p(U, H^{m-p}(E))` vanish. -/
def EventualCohomologySheafVanishingNear
    (E : DerivedCategory ModX) : Prop :=
  ∀ x : X, ∃ px : ℤ → ℤ,
    ∀ W : Opens X.carrier, x ∈ W →
          ∃ U : Opens X.carrier,
        x ∈ U ∧ U ≤ W ∧
          ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
            IsZero ((𝓗[m - (p : ℤ)](X, E)).H' p U)

-- Proof sketch: this is just the defining neighborhood-shrinking form of
-- `EventualCohomologySheafVanishingNear`.
/-- The local vanishing hypothesis can be used on any chosen neighborhood of a point. -/
theorem EventualCohomologySheafVanishingNear.exists_shrunk_open
    {E : DerivedCategory ModX}
    (hE : EventualCohomologySheafVanishingNear X E)
    (x : X) :
    ∃ px : ℤ → ℤ,
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧ U ≤ W ∧
            ∀ m : ℤ, ∀ p : ℕ, px m < (p : ℤ) →
              IsZero ((𝓗[m - (p : ℤ)](X, E)).H' p U) := by
  simpa using hE x

/-- Helper for Lemma 20.37.6: the canonical map `E ⟶ τ_{\ge m} E` induces an isomorphism on
`H^m`. -/
private theorem homology_map_truncGEπ_isIso
    (E : DerivedCategory ModX) (m : ℤ) :
    IsIso ((H m).map ((t.truncGEπ m).app E)) := by
  let T : Triangle (DerivedCategory ModX) := (t.triangleLTGE m).obj E
  have hT : T ∈ distTriang (DerivedCategory ModX) := by
    simpa [T] using t.triangleLTGE_distinguished m E
  have h₁ : T.obj₁.IsLE (m - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H m).map T.mor₁ = 0 := by
    let _ : T.obj₁.IsLE (m - 1) := h₁
    exact (isZero_of_isLE T.obj₁ (m - 1) m (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T m (m + 1) rfl = 0 := by
    let _ : T.obj₁.IsLE (m - 1) := h₁
    exact (isZero_of_isLE T.obj₁ (m - 1) (m + 1) (by omega)).eq_of_tgt _ _
  let _ : Epi ((H m).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT m (m + 1) rfl).2 hδ_zero
  let _ : Mono ((H m).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT m).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H m).map T.mor₂)

/-- Helper for Lemma 20.37.6: once `-n ≤ m`, the canonical map
`E ⟶ τ_{\ge -n} E` induces an isomorphism on `H^m`. -/
private theorem homology_map_derivedTruncationGEToStage_isIso
    (E : DerivedCategory ModX) (m : ℤ) (n : ℕ)
    (hmn : -((n : ℕ) : ℤ) ≤ m) :
    IsIso ((H m).map (CategoryTheory.derivedTruncationGEToStage E n)) := by
  let f := CategoryTheory.derivedTruncationGEToStage E n
  let Y := (CategoryTheory.derivedTruncationGETower E).obj (Opposite.op n)
  have hEiso : IsIso ((H m).map ((t.truncGEπ m).app E)) :=
    homology_map_truncGEπ_isIso X E m
  have hYiso : IsIso ((H m).map ((t.truncGEπ m).app Y)) :=
    homology_map_truncGEπ_isIso X Y m
  let eE :
      (H m).obj E ≅ (H m).obj ((t.truncGE m).obj E) :=
    @asIso _ _ _ _ ((H m).map ((t.truncGEπ m).app E)) hEiso
  let eY :
      (H m).obj Y ≅ (H m).obj ((t.truncGE m).obj Y) :=
    @asIso _ _ _ _ ((H m).map ((t.truncGEπ m).app Y)) hYiso
  -- Compare the desired map with its image under `τ_{\ge m}` by naturality of `truncGEπ`.
  have hf :
      (H m).map f ≫ eY.hom =
        eE.hom ≫ (H m).map ((t.truncGE m).map f) := by
    simpa [eE, eY, Functor.map_comp, CategoryTheory.derivedTruncationGEToStage, Y] using
      congrArg ((H m).map) (NatTrans.naturality (t.truncGEπ m) f)
  have hmiddle : IsIso ((H m).map ((t.truncGE m).map f)) := by
    -- Above degree `m`, the truncation stage map is already an isomorphism in the `t`-structure.
    haveI : IsIso ((t.truncGE m).map f) :=
      t.isIso_truncGE_map_truncGEπ_app m (-((n : ℕ) : ℤ)) hmn E
    exact Functor.map_isIso (H m) ((t.truncGE m).map f)
  have hcomp : IsIso ((H m).map f ≫ eY.hom) := by
    rw [hf]
    let _ : IsIso ((H m).map ((t.truncGE m).map f)) := hmiddle
    change IsIso (eE.hom ≫ (H m).map ((t.truncGE m).map f))
    infer_instance
  let _ : IsIso ((H m).map f ≫ eY.hom) := hcomp
  exact IsIso.of_isIso_comp_right ((H m).map f) eY.hom

/-- Helper for Lemma 20.37.6: composing with an epimorphism does not change the image
subobject. -/
private theorem imageSubobject_comp_eq_of_epi
    {C : Type*} [Category C] [HasImages C] [HasPullbacks C] [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  -- Rewrite the image of the composite through the image inclusion of `f`.
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ g) := by
      simpa using
        congrArg
          (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ g))
          (Limits.imageSubobject_eq_top_of_epi f)
    _ = imageSubobject g := by
      simpa using
        (CategoryTheory.Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) g)

/-- Helper for Lemma 20.37.6: a longer transition map factors through the final successor map. -/
private theorem transitionMap_succ_factor
    {C : Type*} [Category C] (F : SequentialInverseSystem C)
    {i k : ℕ} (hik : i ≤ k) :
    F.transitionMap (Nat.le_succ_of_le hik) =
      F.stepMap k ≫ F.transitionMap hik := by
  -- In `ℕᵒᵖ`, the unique map to stage `i` factors through the last successor map.
  have hh :
      (homOfLE (Nat.le_succ_of_le hik)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE hik).op := by
    subsingleton
  simpa [SequentialInverseSystem.transitionMap, SequentialInverseSystem.stepMap] using
    congrArg F.map hh

/-- Helper for Lemma 20.37.6: after the stage where all successor maps are isomorphisms, every
later transition map is epic. -/
private theorem transitionMap_epi_of_eventually_isIso_stepMap
    {C : Type*} [Category C] (F : SequentialInverseSystem C)
    {N k : ℕ} (hk : N ≤ k)
    (hF : ∀ n : ℕ, N ≤ n → IsIso (F.stepMap n)) :
    Epi (F.transitionMap hk) := by
  -- Induct along the factorization of longer transition maps through the final successor map.
  induction hk with
  | refl =>
      simpa [SequentialInverseSystem.transitionMap] using
        (inferInstance : Epi (𝟙 (F.obj (Opposite.op N))))
  | @step k hk ih =>
      rw [transitionMap_succ_factor F hk]
      haveI : IsIso (F.stepMap k) := hF k hk
      haveI : Epi (F.stepMap k) := by infer_instance
      letI : Epi (F.transitionMap hk) := ih
      infer_instance

/-- Helper for Lemma 20.37.6: after the stage where all successor maps are isomorphisms, every
later transition map is monic. -/
private theorem transitionMap_mono_of_eventually_isIso_stepMap
    {C : Type*} [Category C] (F : SequentialInverseSystem C)
    {N k : ℕ} (hk : N ≤ k)
    (hF : ∀ n : ℕ, N ≤ n → IsIso (F.stepMap n)) :
    Mono (F.transitionMap hk) := by
  -- Induct along the factorization of longer transition maps through the final successor map.
  induction hk with
  | refl =>
      simpa [SequentialInverseSystem.transitionMap] using
        (inferInstance : Mono (𝟙 (F.obj (Opposite.op N))))
  | @step k hk ih =>
      rw [transitionMap_succ_factor F hk]
      haveI : IsIso (F.stepMap k) := hF k hk
      haveI : Mono (F.stepMap k) := by infer_instance
      letI : Mono (F.transitionMap hk) := ih
      infer_instance

/-- Helper for Lemma 20.37.6: eventual isomorphisms of successor maps force the
Mittag-Leffler condition. -/
private theorem isMittagLeffler_of_eventually_isIso_stepMap
    (F : SequentialInverseSystem AddCommGrpCat.{u})
    (hF : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsIso (F.stepMap n)) :
    F.IsMittagLeffler := by
  rcases hF with ⟨N, hN⟩
  intro i
  have hic : i ≤ max i N := le_max_left i N
  refine ⟨max i N, hic, ?_⟩
  intro k hk
  have hfactor :
      F.transitionMap (hic.trans hk) =
        F.transitionMap hk ≫ F.transitionMap hic := by
    -- The composite transition to stage `i` factors through the stabilized stage `max i N`.
    have hh :
        (homOfLE (hic.trans hk)).op =
          (homOfLE hk).op ≫ (homOfLE hic).op := by
      subsingleton
    simpa [SequentialInverseSystem.transitionMap] using congrArg F.map hh
  have htail : ∀ n : ℕ, max i N ≤ n → IsIso (F.stepMap n) := by
    intro n hn
    exact hN n (le_trans (le_max_right i N) hn)
  haveI : Epi (F.transitionMap hk) :=
    transitionMap_epi_of_eventually_isIso_stepMap F hk htail
  -- The epi tail map leaves the image in stage `i` unchanged.
  simpa [hfactor] using
    (imageSubobject_comp_eq_of_epi (F.transitionMap hk) (F.transitionMap hic))

/-- Helper for Lemma 20.37.6: if `g ∘ f` is bijective and `g` is injective, then `f` is
bijective. -/
private theorem bijective_of_comp_right_injective
    {α β γ : Type*} {f : α → β} {g : β → γ}
    (hcomp : Function.Bijective (fun a ↦ g (f a)))
    (hg : Function.Injective g) :
    Function.Bijective f := by
  refine ⟨?_, ?_⟩
  · intro a₁ a₂ hfa
    apply hcomp.1
    simpa [hfa]
  · intro b
    rcases hcomp.2 (g b) with ⟨a, ha⟩
    refine ⟨a, hg ?_⟩
    simpa using ha

/-- Helper for Lemma 20.37.6: the local eventual-vanishing hypothesis produces the eventual-stage
stalk injectivity statement of Lemma `20.37.5` for the canonical Milnor presentation of the
truncation tower. -/
private theorem exists_eventual_stage_stalkMap_injective_of_eventualCohomologySheafVanishingNear
    (E : DerivedCategory ModX)
    {L : DerivedCategory ModX}
    [HasProduct (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))]
    (ι : L ⟶ ∏ᶜ inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
    (hι : HasMilnorTriangle.WithMap (CategoryTheory.derivedTruncationGETower E) ι)
    (hE : EventualCohomologySheafVanishingNear X E)
    (m : ℤ) (x : X) :
    ∃ nx : ℕ,
      -((nx : ℕ) : ℤ) ≤ m ∧
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (cohomologySheafStageMap
              X (CategoryTheory.derivedTruncationGETower E) L m nx ι).hom) := by
  rcases EventualCohomologySheafVanishingNear.exists_shrunk_open X hE x with ⟨px, hpx⟩
  let nx : ℕ := Int.natAbs (px (m - 1)) + Int.natAbs (px m) + Int.natAbs m + 1
  have hnxm : -((nx : ℕ) : ℤ) ≤ m := by
    omega
  have hlocal :
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧
            U ≤ W ∧
            IsZero
              (SequentialInverseSystem.firstDerivedLimit
                (((CategoryTheory.derivedTruncationGETower E) ⋙ RΓ[U]) ⋙
                  DerivedCategory.homologyFunctor AddCommGrpCat (m - 1))) ∧
            ∀ n : ℕ, ∀ hn : nx ≤ n,
              Mono
                (SequentialInverseSystem.transitionMap
                  ((((CategoryTheory.derivedTruncationGETower E) ⋙ RΓ[U]) ⋙
                    DerivedCategory.homologyFunctor AddCommGrpCat m)) hn) := by
    -- The source-faithful remaining work is exactly to package the shrinking vanishing data
    -- `hpx` into the Milnor hypotheses of Lemma `20.37.5`.
    let _ := hpx
    sorry
  refine ⟨nx, hnxm, ?_⟩
  exact
    cohomologyStalkMap_injective_to_eventual_stage_of_local_milnor_conditions
      X (CategoryTheory.derivedTruncationGETower E) L x m nx ι hι hlocal

/-- Helper for Lemma 20.37.6: once the Milnor neighborhood argument injects into a sufficiently
high truncation stage, the induced map on degree-`m` cohomology stalks is bijective. -/
private theorem cohomology_stalk_bijective_of_eventual_stage_injective
    (E : DerivedCategory ModX)
    {L : DerivedCategory ModX} (c : E ⟶ L)
    (hc : IsTruncationDerivedLimitComparison E L c)
    (hE : EventualCohomologySheafVanishingNear X E)
    (m : ℤ) (x : X) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((moduleUnderlyingSheaf X).map ((H m).map c)).hom)) := by
  rcases hc with ⟨hP, ι, hι, hcomp⟩
  let _ : HasProduct (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E)) := hP
  let x' : X.carrier := x
  let stalkMap := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x'
  -- Route correction: the previous attempt stopped at the compatible comparison data. The source
  -- proof first injects the Milnor model into one high truncation stage, and only then splices
  -- that injectivity with the stagewise isomorphism `H^m(E) ≅ H^m(τ_{\ge -n} E)`.
  have hstage :
      ∃ nx : ℕ,
        -((nx : ℕ) : ℤ) ≤ m ∧
        Function.Injective
          (stalkMap.map
            (cohomologySheafStageMap
              X (CategoryTheory.derivedTruncationGETower E) L m nx ι).hom) := by
    exact
      exists_eventual_stage_stalkMap_injective_of_eventualCohomologySheafVanishingNear
        X E ι hι hE m x
  rcases hstage with ⟨nx, hnxm, hnx⟩
  let fstalk :=
    stalkMap.map (((moduleUnderlyingSheaf X).map ((H m).map c)).hom)
  let gstalk :=
    stalkMap.map
      (((moduleUnderlyingSheaf X).map
        ((H m).map
          (ι ≫
            Pi.π
              (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
              nx))).hom)
  have hnx' : Function.Injective ⇑gstalk := by
    simpa [gstalk, cohomologySheafStageMap] using hnx
  -- The compatible comparison identity identifies the composite with the canonical stage map.
  have hfactor :
      fstalk ≫ gstalk =
        stalkMap.map
          (((moduleUnderlyingSheaf X).map
            ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx))).hom) := by
    let sheafStageMap :
        (moduleUnderlyingSheaf X).obj ((H m).obj L) ⟶
          (moduleUnderlyingSheaf X).obj
            ((H m).obj ((CategoryTheory.derivedTruncationGETower E).obj (Opposite.op nx))) :=
      (moduleUnderlyingSheaf X).map
        ((H m).map
          (ι ≫
            Pi.π
              (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
              nx))
    have hcomp' :
        c ≫
            (ι ≫
              Pi.π
                (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
                nx) =
          CategoryTheory.derivedTruncationGEToStage E nx := by
      simpa [Category.assoc] using hcomp nx
    have hcompH :
        (H m).map c ≫
            (H m).map
              (ι ≫
                Pi.π
                  (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
                  nx) =
          (H m).map (CategoryTheory.derivedTruncationGEToStage E nx) := by
      simpa [Functor.map_comp] using congrArg ((H m).map) hcomp'
    have hcompSheaf :
        (moduleUnderlyingSheaf X).map ((H m).map c) ≫
            (moduleUnderlyingSheaf X).map
              ((H m).map
                (ι ≫
                  Pi.π
                    (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
                    nx)) =
          (moduleUnderlyingSheaf X).map
            ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx)) := by
      simpa [Functor.map_comp] using congrArg ((moduleUnderlyingSheaf X).map) hcompH
    calc
      fstalk ≫ gstalk =
          stalkMap.map (((moduleUnderlyingSheaf X).map ((H m).map c)).hom) ≫
            stalkMap.map sheafStageMap.hom := by
            simp [fstalk, gstalk, sheafStageMap]
      _ =
          stalkMap.map
            ((((moduleUnderlyingSheaf X).map ((H m).map c)) ≫ sheafStageMap).hom) := by
            exact
              (Functor.map_comp
                stalkMap
                (((moduleUnderlyingSheaf X).map ((H m).map c)).hom)
                sheafStageMap.hom).symm
      _ =
          stalkMap.map
            (((moduleUnderlyingSheaf X).map ((H m).map c) ≫
                (moduleUnderlyingSheaf X).map
                  ((H m).map
                    (ι ≫
                      Pi.π
                        (inverseSystemFamily (CategoryTheory.derivedTruncationGETower E))
                        nx))).hom) := by
            simp [sheafStageMap]
      _ =
          stalkMap.map
            (((moduleUnderlyingSheaf X).map
              ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx))).hom) := by
            exact congrArg (fun f ↦ stalkMap.map f.hom) hcompSheaf
  have hstageIso :
      IsIso ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx)) :=
    homology_map_derivedTruncationGEToStage_isIso X E m nx hnxm
  -- Apply the known stagewise isomorphism, then transport it through the underlying sheaf and
  -- stalk functors to get a bijective composite on stalks.
  have hstageBij :
      Function.Bijective
        (stalkMap.map
          (((moduleUnderlyingSheaf X).map
            ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx))).hom)) := by
    let _ : IsIso ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx)) := hstageIso
    have hSheafIso :
        IsIso
          ((moduleUnderlyingSheaf X).map
            ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx))) := by
      exact
        Functor.map_isIso
          (moduleUnderlyingSheaf X)
          ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx))
    have hStalkIso :
        IsIso
          (stalkMap.map
            (((moduleUnderlyingSheaf X).map
              ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx))).hom)) := by
      exact
        (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso
          ((moduleUnderlyingSheaf X).map
            ((H m).map (CategoryTheory.derivedTruncationGEToStage E nx)))).1
          hSheafIso x'
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).1 hStalkIso
  have hcompBij : Function.Bijective ⇑(fstalk ≫ gstalk) := by
    rw [hfactor]
    simpa using hstageBij
  exact
    bijective_of_comp_right_injective
      (by simpa using hcompBij)
      hnx'

-- Proof sketch: for each degree `m` and point `x`, choose `n(x)` from the local bounds in the
-- hypothesis so that the truncation triangles of Remark `13.12.4` force eventual stability of
-- the maps on `H^{m-1}(U,-)` and `H^m(U,-)` over a cofinal system of neighborhoods of `x`.
-- Lemma `20.37.5` then gives injectivity on stalks of the map
-- `H^m(L)_x → H^m(τ_{\ge -n(x)} E)_x`; since `H^m(E) → H^m(τ_{\ge -n(x)} E)` is an
-- isomorphism for `n(x) ≥ -m`, the induced stalk map `H^m(E)_x → H^m(L)_x` is bijective. Thus
-- every cohomology sheaf map induced by `c` is an isomorphism, so `c` is an isomorphism in the
-- derived category.
/-- Lemma 20.37.6: let `(X, 𝒪_X)` be a ringed space and let `E ∈ D(𝒪_X)`. Assume that for every
point `x ∈ X` there is a function `p(x,-) : ℤ → ℤ` such that, after shrinking inside any
neighborhood of `x`, one has `H^p(U, H^{m-p}(E)) = 0` for all `p > p(x,m)`. Then any compatible
comparison morphism from `E` to the right-derived inverse limit of the truncation tower
`τ_{\ge -n} E` from Remark `13.34.5` is an isomorphism in `D(𝒪_X)`. -/
@[stacks 0D62]
theorem isIso_of_truncationDerivedLimitComparison_of_eventualCohomologySheafVanishingNear
    (E : DerivedCategory ModX)
    {L : DerivedCategory ModX} (c : E ⟶ L)
    (hc : IsTruncationDerivedLimitComparison E L c)
    (hE : EventualCohomologySheafVanishingNear X E) :
    IsIso c := by
  -- Reduce the comparison to degreewise cohomology isomorphisms in the derived category.
  rw [CategoryTheory.derivedCategory_isIso_iff_homology_map_isIso c]
  intro m
  have hUnderlying :
      IsIso ((moduleUnderlyingSheaf X).map ((H m).map c)) := by
    -- The cohomology sheaf map is an isomorphism once all of its stalk maps are bijections.
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    exact
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
        (cohomology_stalk_bijective_of_eventual_stage_injective X E c hc hE m x)
  let _ : IsIso ((moduleUnderlyingSheaf X).map ((H m).map c)) := hUnderlying
  -- Reflect the underlying sheaf isomorphism back to the module-valued cohomology map.
  exact isIso_of_reflects_iso ((H m).map c) (moduleUnderlyingSheaf X)

end

end AlgebraicGeometry.RingedSpace
