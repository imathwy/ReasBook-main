import Mathlib
import stacks_proof.stacks_project.Chap04.Definition_4_22_2
import stacks_proof.stacks_project.Chap04.Lemma_4_22_3
import stacks_proof.stacks_project.Chap04.Lemma_4_22_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe uI vI uA vA

namespace CategoryTheory

section Filtered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

/- Domain-style sampling for Lemma 12.30.1 in the filtered/cofiltered additive-diagram domain:
- sampled owner-level declarations:
  * `IsEssentiallyConstantFilteredDiagram`
  * `essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone`
  * `essentiallyConstantFilteredDiagram_iff_comp_final`
  * `essentiallyConstantCofilteredDiagram_iff_comp_initial`
- best owner abstraction: the chapter owner
  `IsEssentiallyConstantFilteredDiagram M` from `Definition_4_22_2`.

Primitive-vs-derived split:
- primitive source-facing data: for a fixed colimit cocone `c`, each stage `M.obj i` splits into a
  stable summand that maps isomorphically to the colimit value and a complementary summand that
  eventually dies under some transition map.
- derived source-facing bridge criterion: a cofinal filtered full subcategory on which this
  pointwise stable-splitting condition holds.
- derived API: the dual cofiltered criterion `HasEventuallySplitLimit`, obtained by applying the
  filtered statement to the opposite diagram.

Source/core/bridge triage:
- `source-facing`: `HasEventuallySplitColimit` and its dual `HasEventuallySplitLimit`.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram`,
  `IsEssentiallyConstantCofilteredDiagram`, and the actual colimit owner `ColimitCocone`.
- `bridge/view`: restriction to a cofinal filtered full subcategory, and passage to the opposite
  diagram for the cofiltered dual.

The colimit witness should therefore use the canonical owner `ColimitCocone M`, not a duplicated
pair `(c : Cocone M)` together with a separate `IsColimit c`. -/

private def stableSplitStage {M : I ⥤ A} (c : ColimitCocone M) (i : I) : Prop :=
  ∃ (X Z : A) (f : X ⟶ M.obj i) (g : M.obj i ⟶ Z) (zero : f ≫ g = 0)
    (s : (ShortComplex.mk f g zero).Splitting),
      IsIso (f ≫ c.cocone.ι.app i) ∧
        ∃ (j : I) (h : i ⟶ j), s.s ≫ M.map h = 0

-- Internal stable-splitting criterion used to define the source-facing bridge
-- `HasEventuallySplitColimit`.
private def hasStableSplitColimit (M : I ⥤ A) : Prop :=
  ∃ c : ColimitCocone M,
    ∀ i : I, stableSplitStage c i

/-- Helper for Lemma 12.30.1: `reachableFrom i` is the full subcategory of objects receiving a map
from the distinguished stage `i`. -/
private def reachableFrom (i : I) : ObjectProperty I := fun j ↦ Nonempty (i ⟶ j)

/-- Helper for Lemma 12.30.1: transporting a chosen section of a colimit leg along a transition
map again gives a section of the later colimit leg. -/
private theorem transportedColimitSection
    {M : I ⥤ A} {c : ColimitCocone M} {i j : I} (σ : c.cocone.pt ⟶ M.obj i)
    (hσ : σ ≫ c.cocone.ι.app i = 𝟙 c.cocone.pt) (h : i ⟶ j) :
    (σ ≫ M.map h) ≫ c.cocone.ι.app j = 𝟙 c.cocone.pt := by
  -- Proof comment: the cocone relation moves the later leg back to the original stage where `σ`
  -- is already a section.
  have hw : σ ≫ M.map h ≫ c.cocone.ι.app j = σ ≫ c.cocone.ι.app i := by
    simpa [Category.assoc] using congrArg (fun f ↦ σ ≫ f) (c.cocone.w h)
  simpa [Category.assoc] using hw.trans hσ

/-- Helper for Lemma 12.30.1: once a transition map factors through the projector attached to one
section of a colimit leg, any other section of that same leg gives the same comparison map after
that transition. -/
private theorem colimitSectionsAgreeAfterFactor
    {M : I ⥤ A} {c : ColimitCocone M} {j k l : I}
    (σ₁ : c.cocone.pt ⟶ M.obj k)
    (hσ₁ : σ₁ ≫ c.cocone.ι.app k = 𝟙 c.cocone.pt)
    (σ₂ : c.cocone.pt ⟶ M.obj k)
    {u : k ⟶ l} (hu : M.map u = c.cocone.ι.app k ≫ σ₂ ≫ M.map u) :
    c.cocone.ι.app j ≫ σ₁ ≫ M.map u = c.cocone.ι.app j ≫ σ₂ ≫ M.map u := by
  -- Proof comment: insert the projector coming from `σ₂`, then collapse the extra section-leg
  -- pair using the section identity for `σ₁`.
  have hu' :
      c.cocone.ι.app j ≫ σ₁ ≫ M.map u =
        c.cocone.ι.app j ≫ σ₁ ≫ (c.cocone.ι.app k ≫ σ₂ ≫ M.map u) := by
    simpa [Category.assoc] using congrArg (fun t ↦ c.cocone.ι.app j ≫ σ₁ ≫ t) hu
  have hcollapse :
      c.cocone.ι.app j ≫ σ₁ ≫ (c.cocone.ι.app k ≫ σ₂ ≫ M.map u) =
        c.cocone.ι.app j ≫ σ₂ ≫ M.map u := by
    simpa [Category.assoc] using
      congrArg (fun f ↦ c.cocone.ι.app j ≫ f ≫ σ₂ ≫ M.map u) hσ₁
  calc
    c.cocone.ι.app j ≫ σ₁ ≫ M.map u
        = c.cocone.ι.app j ≫ σ₁ ≫ (c.cocone.ι.app k ≫ σ₂ ≫ M.map u) := hu'
    _ = c.cocone.ι.app j ≫ σ₂ ≫ M.map u := hcollapse

/-- Helper for Lemma 12.30.1: on a reachable stage of an essentially constant colimit cocone,
the eventual transition map factors through the projector defined by the chosen colimit section. -/
private theorem eventuallyFactorsThroughReachableProjector [IsFiltered I]
    {M : I ⥤ A} {c : ColimitCocone M} {i : I} {s : c.cocone.pt ⟶ M.obj i}
    (hs : s ≫ c.cocone.ι.app i = 𝟙 c.cocone.pt)
    (hfac : ∀ j : I,
      ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
        M.map jk = c.cocone.ι.app j ≫ s ≫ M.map ik)
    {j : I} (fij : i ⟶ j) :
    ∃ (k : I) (h : j ⟶ k),
      (c.cocone.ι.app j ≫ s ≫ M.map fij) ≫ M.map h = M.map h := by
  rcases hfac j with ⟨k, ik, jk, hjk⟩
  let t : k ⟶ IsFiltered.coeq ik (fij ≫ jk) := IsFiltered.coeqHom ik (fij ≫ jk)
  refine ⟨_, jk ≫ t, ?_⟩
  -- Proof comment: coequalizing `ik` and `fij ≫ jk` forces the eventual map to land in the image
  -- of the projector `ι_j ≫ s ≫ M.map fij`.
  calc
    (c.cocone.ι.app j ≫ s ≫ M.map fij) ≫ M.map (jk ≫ t)
        = c.cocone.ι.app j ≫ s ≫ M.map (fij ≫ jk ≫ t) := by
            simp [Functor.map_comp, Category.assoc]
    _ = c.cocone.ι.app j ≫ s ≫ M.map (ik ≫ t) := by
          simpa [t, Category.assoc] using congrArg (fun f ↦ c.cocone.ι.app j ≫ s ≫ M.map f)
            (IsFiltered.coeq_condition ik (fij ≫ jk)).symm
    _ = (c.cocone.ι.app j ≫ s ≫ M.map ik) ≫ M.map t := by
          simp [Functor.map_comp, Category.assoc]
    _ = M.map jk ≫ M.map t := by
          rw [hjk]
    _ = M.map (jk ≫ t) := by
          simp [Functor.map_comp]

/-- Helper for Lemma 12.30.1: if a section of a colimit leg has eventually vanishing complementary
projector, then that stage yields the stable-splitting data required in `stableSplitStage`. -/
private theorem stableSplitStageOfSplitProjector [IsIdempotentComplete A]
    {M : I ⥤ A} (c : ColimitCocone M) (i : I) (σ : c.cocone.pt ⟶ M.obj i)
    (hσ : σ ≫ c.cocone.ι.app i = 𝟙 c.cocone.pt)
    {j : I} (h : i ⟶ j)
    (hkill : (𝟙 (M.obj i) - c.cocone.ι.app i ≫ σ) ≫ M.map h = 0) :
    stableSplitStage c i := by
  let p : M.obj i ⟶ M.obj i := c.cocone.ι.app i ≫ σ
  let q : M.obj i ⟶ M.obj i := 𝟙 (M.obj i) - p
  have hp : p ≫ p = p := by
    -- Proof comment: `p` is idempotent because `σ` is a section of the colimit leg.
    dsimp [p]
    calc
      (c.cocone.ι.app i ≫ σ) ≫ (c.cocone.ι.app i ≫ σ)
          = c.cocone.ι.app i ≫ (σ ≫ c.cocone.ι.app i) ≫ σ := by
              simp [Category.assoc]
      _ = c.cocone.ι.app i ≫ 𝟙 c.cocone.pt ≫ σ := by
            simpa [Category.assoc] using congrArg (fun f ↦ c.cocone.ι.app i ≫ f ≫ σ) hσ
      _ = c.cocone.ι.app i ≫ σ := by
            simp
  rcases IsIdempotentComplete.idempotents_split (M.obj i) q
      (Idempotents.idem_of_id_sub_idem p hp) with
    ⟨Z, s, g, hs, hq⟩
  have hσq : σ ≫ q = 0 := by
    -- Proof comment: the complementary projector vanishes on the chosen stable section.
    calc
      σ ≫ q = σ ≫ (𝟙 (M.obj i) - p) := by
            rfl
      _ = σ ≫ 𝟙 (M.obj i) - σ ≫ p := by
            rw [Preadditive.comp_sub]
      _ = σ - σ ≫ p := by
            simp
      _ = σ - σ := by
            dsimp [p]
            have hσσ : σ ≫ c.cocone.ι.app i ≫ σ = σ := by
              simpa [Category.assoc] using congrArg (fun f ↦ f ≫ σ) hσ
            simpa using congrArg (fun t ↦ σ - t) hσσ
      _ = 0 := by
            simp
  have hzero : σ ≫ g = 0 := by
    -- Proof comment: `σ ≫ g` vanishes because the complement projector already vanishes on `σ`.
    calc
      σ ≫ g = (σ ≫ g) ≫ (s ≫ g) := by
            rw [hs]
            simp [Category.assoc]
      _ = σ ≫ (g ≫ s) ≫ g := by
            simp [Category.assoc]
      _ = σ ≫ q ≫ g := by
            rw [hq]
      _ = 0 := by
            simpa [Category.assoc] using congrArg (fun f ↦ f ≫ g) hσq
  have hqkill : q ≫ M.map h = 0 := by
    simpa [q, p] using hkill
  have hsKill : s ≫ M.map h = 0 := by
    -- Proof comment: precomposing the vanishing complementary projector with the split section
    -- gives the desired eventual vanishing on the complementary summand.
    calc
      s ≫ M.map h = (s ≫ g) ≫ (s ≫ M.map h) := by
            rw [hs]
            simp [Category.assoc]
      _ = s ≫ (g ≫ s) ≫ M.map h := by
            simp [Category.assoc]
      _ = s ≫ q ≫ M.map h := by
            rw [hq]
      _ = 0 := by
            simpa [Category.assoc] using congrArg (fun f ↦ s ≫ f) hqkill
  have hid : p + q = 𝟙 (M.obj i) := by
    dsimp [q]
    abel
  have hσIso : IsIso (σ ≫ c.cocone.ι.app i) := by
    rw [hσ]
    exact ⟨⟨𝟙 c.cocone.pt, by simp, by simp⟩⟩
  refine ⟨c.cocone.pt, Z, σ, g, hzero, ?_, ?_⟩
  · refine
      { r := c.cocone.ι.app i
        s := s
        f_r := hσ
        s_g := hs
        id := by
          simpa [p, hq] using hid }
  · refine ⟨hσIso, ⟨j, h, hsKill⟩⟩

-- Route correction: the old statement omitted the premise that the complementary summand maps to
-- zero in the colimit leg. The repaired route proves that vanishing first, then compares the
-- split retraction against the colimit retraction before postcomposing by `f`.
/-- Helper for Lemma 12.30.1: if the complementary summand is eventually killed by a transition
map, then it also maps to zero under the colimit leg at the source stage. -/
private theorem splitComplementMapsToZero
    {M : I ⥤ A} {c : Cocone M} {i j : I}
    {X Z : A} {f : X ⟶ M.obj i} {g : M.obj i ⟶ Z} {zero : f ≫ g = 0}
    (spl : (ShortComplex.mk f g zero).Splitting)
    {h : i ⟶ j} (hkill : spl.s ≫ M.map h = 0) :
    spl.s ≫ c.ι.app i = 0 := by
  -- Proof comment: the cocone relation rewrites the colimit leg at `i` through the transition
  -- `h`, so the assumed vanishing after `h` forces vanishing in the cocone as well.
  rw [← c.w h]
  simpa [Category.assoc] using congrArg (fun t ↦ t ≫ c.ι.app j) hkill

/-- Helper for Lemma 12.30.1: once the complementary summand maps to zero in the colimit leg, the
split retraction coincides with the retraction coming from the induced colimit isomorphism. -/
private theorem stableSplitRetraction_eq_colimitRetraction
    {M : I ⥤ A} {c : ColimitCocone M} {i : I}
    {X Z : A} {f : X ⟶ M.obj i} {g : M.obj i ⟶ Z} {zero : f ≫ g = 0}
    (spl : (ShortComplex.mk f g zero).Splitting)
    [hf : IsIso (f ≫ c.cocone.ι.app i)]
    (hzero : spl.s ≫ c.cocone.ι.app i = 0) :
    spl.r = c.cocone.ι.app i ≫ inv (f ≫ c.cocone.ι.app i) := by
  -- Proof comment: postcompose the splitting identity with the colimit leg, kill the
  -- complementary summand, and cancel the resulting isomorphism on the right.
  have hsplit :
      spl.r ≫ (f ≫ c.cocone.ι.app i) = c.cocone.ι.app i := by
    have hzero' : g ≫ spl.s ≫ c.cocone.ι.app i = 0 := by
      calc
        g ≫ spl.s ≫ c.cocone.ι.app i = g ≫ 0 := by
          simpa [Category.assoc] using congrArg (fun t ↦ g ≫ t) hzero
        _ = 0 := by rw [comp_zero]
    have hid := congrArg (fun t ↦ t ≫ c.cocone.ι.app i) spl.id
    have hid' :
        spl.r ≫ f ≫ c.cocone.ι.app i + g ≫ spl.s ≫ c.cocone.ι.app i = c.cocone.ι.app i := by
      simpa [Category.assoc, Preadditive.add_comp] using hid
    rw [hzero', add_zero] at hid'
    simpa [Category.assoc] using hid'
  rw [← cancel_mono (f ≫ c.cocone.ι.app i)]
  calc
    spl.r ≫ (f ≫ c.cocone.ι.app i) = c.cocone.ι.app i := hsplit
    _ = (c.cocone.ι.app i ≫ inv (f ≫ c.cocone.ι.app i)) ≫ (f ≫ c.cocone.ι.app i) := by
          simp [Category.assoc]

/-- Helper for Lemma 12.30.1: the stable projector of a split stage agrees with the projector
coming from the induced section of the colimit leg once the complementary summand vanishes in the
colimit. -/
private theorem stableSplitProjector_eq_colimitSectionProjector
    {M : I ⥤ A} {c : ColimitCocone M} {i : I}
    {X Z : A} {f : X ⟶ M.obj i} {g : M.obj i ⟶ Z} {zero : f ≫ g = 0}
    (spl : (ShortComplex.mk f g zero).Splitting)
    [hf : IsIso (f ≫ c.cocone.ι.app i)]
    (hzero : spl.s ≫ c.cocone.ι.app i = 0) :
    spl.r ≫ f = c.cocone.ι.app i ≫ inv (f ≫ c.cocone.ι.app i) ≫ f := by
  -- Proof comment: the retraction comparison is the real bridge; the projector identity is just
  -- that equality postcomposed by the stable inclusion `f`.
  simpa [Category.assoc] using congrArg (fun t ↦ t ≫ f)
    (stableSplitRetraction_eq_colimitRetraction (c := c) (i := i) spl hzero)

/-- Helper for Lemma 12.30.1: a stable split stage provides a genuine section of the colimit leg,
and after some transition the stage map factors through the corresponding projector. -/
private theorem stableSplitStage_sectionAndFactor
    {M : I ⥤ A} {c : ColimitCocone M} {i : I}
    (hi : stableSplitStage c i) :
    ∃ σ : c.cocone.pt ⟶ M.obj i,
      σ ≫ c.cocone.ι.app i = 𝟙 c.cocone.pt ∧
        ∃ (j : I) (h : i ⟶ j), M.map h = c.cocone.ι.app i ≫ σ ≫ M.map h := by
  rcases hi with ⟨X, Z, f, g, zero, spl, hf, ⟨j, h, hkill⟩⟩
  letI : IsIso (f ≫ c.cocone.ι.app i) := hf
  let σ : c.cocone.pt ⟶ M.obj i := (asIso (f ≫ c.cocone.ι.app i)).inv ≫ f
  refine ⟨σ, ?_, j, h, ?_⟩
  · -- Proof comment: the chosen section is inverse to the stable summand map into the colimit.
    dsimp [σ]
    calc
      ((asIso (f ≫ c.cocone.ι.app i)).inv ≫ f) ≫ c.cocone.ι.app i
          = (asIso (f ≫ c.cocone.ι.app i)).inv ≫ (f ≫ c.cocone.ι.app i) := by
              simp [Category.assoc]
      _ = 𝟙 c.cocone.pt := by
            simp
  · -- Proof comment: once the complementary summand is killed, the transition map is entirely
    -- controlled by the stable projector.
    have hzero : spl.s ≫ c.cocone.ι.app i = 0 := by
      exact splitComplementMapsToZero (c := c.cocone) spl hkill
    have hproj :
        spl.r ≫ f = c.cocone.ι.app i ≫ σ := by
      simpa [σ, Category.assoc] using
        stableSplitProjector_eq_colimitSectionProjector (c := c) (i := i) spl hzero
    calc
      M.map h = (𝟙 _) ≫ M.map h := by simp
      _ = (spl.r ≫ f + g ≫ spl.s) ≫ M.map h := by
            rw [← spl.id]
      _ = spl.r ≫ f ≫ M.map h + g ≫ (spl.s ≫ M.map h) := by
            simp [Category.assoc, Preadditive.add_comp]
      _ = spl.r ≫ f ≫ M.map h := by
            simp [hkill]
      _ = c.cocone.ι.app i ≫ σ ≫ M.map h := by
            simpa [Category.assoc] using congrArg (fun t ↦ t ≫ M.map h) hproj

/-- Helper for Lemma 12.30.1: if every stage of a colimit cocone splits into a stable summand
mapping isomorphically to the colimit and a complementary summand eventually killed by transition
maps, then the cocone is essentially constant. -/
private theorem isEssentiallyConstantFilteredCocone_of_stableSplitStages [IsFiltered I]
    {M : I ⥤ A} (c : ColimitCocone M) (hc : ∀ i : I, stableSplitStage c i) :
    IsEssentiallyConstantFilteredCocone c.cocone := by
  classical
  let i₀ : I := Classical.choice (IsFiltered.nonempty (C := I))
  rcases stableSplitStage_sectionAndFactor (hc i₀) with ⟨σ₀, hσ₀, _, _, _⟩
  rw [isEssentiallyConstantFilteredCocone_iff]
  refine ⟨i₀, σ₀, hσ₀, ?_⟩
  intro j
  rcases stableSplitStage_sectionAndFactor (hc j) with ⟨σⱼ, hσⱼ, k₁, h₁, hk₁⟩
  let k := IsFiltered.max i₀ k₁
  let i₀k : i₀ ⟶ k := IsFiltered.leftToMax i₀ k₁
  let k₁k : k₁ ⟶ k := IsFiltered.rightToMax i₀ k₁
  have hk₁' :
      M.map (h₁ ≫ k₁k) = c.cocone.ι.app j ≫ σⱼ ≫ M.map (h₁ ≫ k₁k) := by
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ f ≫ M.map k₁k) hk₁
  rcases stableSplitStage_sectionAndFactor (hc k) with ⟨σₖ, hσₖ, l, h₂, hk₂⟩
  refine ⟨l, i₀k ≫ h₂, h₁ ≫ k₁k ≫ h₂, ?_⟩
  -- Proof comment: after first killing `Zⱼ`, both comparison maps into `M.obj k` become sections
  -- of the same colimit leg; after killing `Zₖ`, every such section collapses to the stable
  -- summand at stage `k`.
  let τⱼ : c.cocone.pt ⟶ M.obj k := σⱼ ≫ M.map (h₁ ≫ k₁k)
  have hτⱼ : τⱼ ≫ c.cocone.ι.app k = 𝟙 c.cocone.pt := by
    exact transportedColimitSection (c := c) σⱼ hσⱼ (h₁ ≫ k₁k)
  let τ₀ : c.cocone.pt ⟶ M.obj k := σ₀ ≫ M.map i₀k
  have hτ₀ : τ₀ ≫ c.cocone.ι.app k = 𝟙 c.cocone.pt := by
    exact transportedColimitSection (c := c) σ₀ hσ₀ i₀k
  calc
    M.map (h₁ ≫ k₁k ≫ h₂) = M.map (h₁ ≫ k₁k) ≫ M.map h₂ := by
      simp [Functor.map_comp]
    _ = c.cocone.ι.app j ≫ τⱼ ≫ M.map h₂ := by
          rw [hk₁']
          simp [τⱼ, Category.assoc]
    _ = c.cocone.ι.app j ≫ σₖ ≫ M.map h₂ := by
          exact colimitSectionsAgreeAfterFactor (c := c) (j := j) (k := k) (l := l) τⱼ hτⱼ σₖ hk₂
    _ = c.cocone.ι.app j ≫ τ₀ ≫ M.map h₂ := by
          exact (colimitSectionsAgreeAfterFactor
            (c := c) (j := j) (k := k) (l := l) τ₀ hτ₀ σₖ hk₂).symm
    _ = c.cocone.ι.app j ≫ σ₀ ≫ M.map (i₀k ≫ h₂) := by
          simp [τ₀, Functor.map_comp, Category.assoc]

/-- A diagram has an eventual split colimit if, after restricting along the inclusion of some
cofinal filtered full subcategory, the restricted diagram has a stable split colimit. In Lemma
12.30.1 this is the source-facing bridge criterion for filtered diagrams. -/
@[stacks 0A2E]
def HasEventuallySplitColimit (M : I ⥤ A) : Prop :=
  ∃ P : ObjectProperty I,
    ∃ _ : IsFiltered P.FullSubcategory,
      ∃ _ : Functor.Final P.ι,
        hasStableSplitColimit (P.ι ⋙ M)

/-- Helper for Lemma 12.30.1: the full subcategory of objects reachable from a fixed stage in a
filtered category is itself filtered. -/
private theorem reachableFrom_isFiltered [IsFiltered I] (i : I) :
    IsFiltered (reachableFrom (I := I) i).FullSubcategory := by
  let P : ObjectProperty I := reachableFrom (I := I) i
  classical
  refine
    { cocone_objs := ?_
      cocone_maps := ?_
      nonempty := ?_ }
  · intro X Y
    let Z : P.FullSubcategory :=
      ⟨IsFiltered.max X.obj Y.obj, ⟨Classical.choice X.property ≫ IsFiltered.leftToMax X.obj Y.obj⟩⟩
    refine ⟨Z, ObjectProperty.homMk (IsFiltered.leftToMax X.obj Y.obj),
      ObjectProperty.homMk (IsFiltered.rightToMax X.obj Y.obj), trivial⟩
  · intro X Y f g
    let Z : P.FullSubcategory :=
      ⟨IsFiltered.coeq f.hom g.hom,
        ⟨Classical.choice Y.property ≫ IsFiltered.coeqHom f.hom g.hom⟩⟩
    refine ⟨Z, ObjectProperty.homMk (IsFiltered.coeqHom f.hom g.hom), ?_⟩
    apply ObjectProperty.hom_ext
    simpa using IsFiltered.coeq_condition f.hom g.hom
  · exact ⟨⟨i, ⟨𝟙 i⟩⟩⟩

/-- Helper for Lemma 12.30.1: the inclusion of the reachable full subcategory is final. -/
private theorem reachableFrom_final [IsFiltered I] (i : I) :
    Functor.Final (reachableFrom (I := I) i).ι := by
  let P : ObjectProperty I := reachableFrom (I := I) i
  letI : IsFiltered P.FullSubcategory := reachableFrom_isFiltered (I := I) i
  exact Functor.final_of_exists_of_isFiltered (F := P.ι)
    (fun j ↦ by
      let k : P.FullSubcategory := ⟨IsFiltered.max i j, ⟨IsFiltered.leftToMax i j⟩⟩
      exact ⟨k, ⟨IsFiltered.rightToMax i j⟩⟩)
    (fun {j} {c} s s' ↦ by
      classical
      let k : P.FullSubcategory :=
        ⟨IsFiltered.coeq s s', ⟨Classical.choice c.property ≫ IsFiltered.coeqHom s s'⟩⟩
      refine ⟨k, ObjectProperty.homMk (IsFiltered.coeqHom s s'), ?_⟩
      simpa using IsFiltered.coeq_condition s s')

/-- Helper for Lemma 12.30.1: an essentially constant filtered diagram yields an eventual split
colimit after restricting to the reachable full subcategory of a distinguished stage. -/
private theorem hasEventuallySplitColimit_of_essentiallyConstant
    [IsFiltered I] [IsIdempotentComplete A] {M : I ⥤ A}
    (hM : IsEssentiallyConstantFilteredDiagram M) :
    HasEventuallySplitColimit M := by
  classical
  rcases essentiallyConstantFilteredDiagram_exists_essentiallyConstant_colimitCocone M hM with
    ⟨c, hc⟩
  rw [isEssentiallyConstantFilteredCocone_iff] at hc
  rcases hc with ⟨i, s, hs, hfac⟩
  let P : ObjectProperty I := reachableFrom (I := I) i
  have hP : IsFiltered P.FullSubcategory := reachableFrom_isFiltered (I := I) i
  have hFinal : Functor.Final P.ι := reachableFrom_final (I := I) i
  letI : IsFiltered P.FullSubcategory := hP
  letI : Functor.Final P.ι := hFinal
  let cP : ColimitCocone (P.ι ⋙ M) := Functor.Final.colimitCoconeComp P.ι c
  have hι (j : P.FullSubcategory) : cP.cocone.ι.app j = c.cocone.ι.app j.obj := rfl
  have hmap {j k : P.FullSubcategory} (f : j ⟶ k) : (P.ι ⋙ M).map f = M.map f.hom := rfl
  have hcP : ∀ j : P.FullSubcategory, stableSplitStage cP j := by
    intro j
    let fij : i ⟶ j.obj := Classical.choice j.property
    rcases eventuallyFactorsThroughReachableProjector
        (c := c) (i := i) (s := s) hs hfac fij with ⟨k, hjk, hproj⟩
    let kP : P.FullSubcategory := ⟨k, ⟨fij ≫ hjk⟩⟩
    let hjkP : j ⟶ kP := ObjectProperty.homMk hjk
    let σj : cP.cocone.pt ⟶ (P.ι ⋙ M).obj j := s ≫ M.map fij
    have hσj : σj ≫ cP.cocone.ι.app j = 𝟙 cP.cocone.pt := by
      -- The section at `j` is the chosen section at `i` transported along the reachability map.
      rw [hι j]
      exact transportedColimitSection (c := c) s hs fij
    have hkill :
        (𝟙 ((P.ι ⋙ M).obj j) - cP.cocone.ι.app j ≫ σj) ≫ (P.ι ⋙ M).map hjkP = 0 := by
      -- After passing to the eventual stage `k`, the complementary projector vanishes.
      rw [hι j, hmap hjkP]
      calc
        (𝟙 ((P.ι ⋙ M).obj j) - cP.cocone.ι.app j ≫ σj) ≫ (P.ι ⋙ M).map hjkP
            = M.map hjk - (c.cocone.ι.app j.obj ≫ s ≫ M.map fij) ≫ M.map hjk := by
                change (𝟙 (M.obj j.obj) - c.cocone.ι.app j.obj ≫ s ≫ M.map fij) ≫ M.map hjk = _
                rw [Preadditive.sub_comp]
                simp [σj, Category.assoc]
        _ = M.map hjk - M.map hjk := by
              rw [hproj]
        _ = 0 := by
              simp
    -- The transported section and the vanishing complement data now match the stable-split API.
    exact stableSplitStageOfSplitProjector (c := cP) (i := j) σj hσj (h := hjkP) hkill
  -- The final inclusion packages the stable split data into the source-facing bridge criterion.
  exact ⟨P, hP, hFinal, ⟨cP, hcP⟩⟩

/-- Helper for Lemma 12.30.1: an eventual split colimit on a cofinal filtered restriction
reflects back to essential constancy of the ambient filtered diagram. -/
private theorem essentiallyConstantFilteredDiagram_of_hasEventuallySplitColimit
    [IsFiltered I] {M : I ⥤ A} (hM : HasEventuallySplitColimit M) :
    IsEssentiallyConstantFilteredDiagram M := by
  rcases hM with ⟨P, hP, hFinal, c, hc⟩
  letI : IsFiltered P.FullSubcategory := hP
  letI : Functor.Final P.ι := hFinal
  have hcomp : IsEssentiallyConstantFilteredDiagram (P.ι ⋙ M) := by
    -- The restricted cocone is essentially constant because every stage admits stable split data.
    exact ⟨c.cocone, isEssentiallyConstantFilteredCocone_of_stableSplitStages c hc⟩
  -- Finality of the inclusion reflects essential constancy from the restricted diagram.
  exact (essentiallyConstantFilteredDiagram_iff_comp_final P.ι M).mpr hcomp

-- Proof sketch: from an essentially constant filtered cocone, take its colimit value, pass to the
-- cofinal full subcategory of stages receiving a map from the chosen index, and split the induced
-- idempotent at each such stage using idempotent completeness.
/-- Lemma 12.30.1 (1): for a filtered diagram in a preadditive Karoubian category, being
essentially constant is equivalent to admitting a cofinal filtered full subcategory whose stages
split into a stable summand mapping isomorphically to a colimit value and a complementary summand
that eventually becomes zero. -/
@[stacks 0A2E]
theorem essentiallyConstantFilteredDiagram_iff_hasEventuallySplitColimit
    [IsFiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantFilteredDiagram M ↔
      HasEventuallySplitColimit M := by
  -- Route correction: the helper layer now isolates the forward projector splitting and the
  -- reverse two-stage comparison. The remaining work is the main assembly through the reachable
  -- final subcategory and these helpers.
  constructor
  · -- Assemble the forward implication from the restricted stable-splitting package.
    exact hasEventuallySplitColimit_of_essentiallyConstant (M := M)
  · -- Reflect the restricted stable-splitting package back along the final inclusion.
    exact essentiallyConstantFilteredDiagram_of_hasEventuallySplitColimit (M := M)

end Filtered

section Cofiltered

variable {I : Type uI} [Category.{vI} I]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

/-- A diagram has an eventual split limit if, after passing to the opposite diagram, it has an
eventual split colimit. In Lemma 12.30.1 this is the cofiltered dual of
`HasEventuallySplitColimit`, applied to cofiltered diagrams. -/
abbrev HasEventuallySplitLimit (M : I ⥤ A) : Prop :=
  HasEventuallySplitColimit M.op

-- Proof sketch: apply the filtered statement to the opposite diagram `M.op`, translate the split
-- decomposition data across `op`/`unop`, and rewrite essential constancy using the dual
-- characterization of essentially constant cofiltered cones.
/-- Lemma 12.30.1 (2): for a cofiltered diagram in a preadditive Karoubian category, being
essentially constant is equivalent to admitting an initial cofiltered full subcategory whose stages
split into a stable summand receiving the limit isomorphically and a complementary summand killed
by some earlier transition map. -/
@[stacks 0A2E]
theorem essentiallyConstantCofilteredDiagram_iff_hasEventuallySplitLimit
    [IsCofiltered I] [IsIdempotentComplete A] (M : I ⥤ A) :
    IsEssentiallyConstantCofilteredDiagram M ↔
      HasEventuallySplitLimit M := by
  rw [isEssentiallyConstantCofilteredDiagram_iff_op]
  simpa [HasEventuallySplitLimit] using
    essentiallyConstantFilteredDiagram_iff_hasEventuallySplitColimit M.op

end Cofiltered

end CategoryTheory
