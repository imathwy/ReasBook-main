import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_27_14
import stacks_proof.stacks_project.Chap08.Lemma_8_12_5
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6.Index
import stacks_proof.stacks_project.Chap08.Lemma_8_12_6_Support.RightComponentDescent

open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

open scoped Functor

variable (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: for the identity-chart section object over `Y`, the raw precomposition lift already lies over the strict composite projection without any transported source comparison. -/
theorem pushforwardProjectionIsoComma_section_precompose_isStronglyCartesian
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj
        ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
          ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y))) :
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsStronglyCartesian g
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g) := by
  dsimp
  simpa using
    (pushforwardProjectionIsoCommaProjection_precompose_isStronglyCartesian
      (u := u) (p := p)
      ((pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y))
      g)
/-- Helper for Lemma 8.12.6 Support: a raw section factor whose left component has
the transported source-chart form is a strict composite hom-lift over the underlying base map. -/
theorem pushforwardProjectionIsoComma_raw_section_factor_to_q_lift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {W : pushforwardProjectionIsoComma (u := u) (p := p)}
      (h : q.obj W ⟶ q.obj T) (χ : W ⟶ T),
      r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom) χ →
      q.IsHomLift h χ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro W h χ hχ
  letI : IsIso W.obj.hom := W.property
  have hmap_left :
      W.obj.hom ≫ q.map χ = W.obj.hom ≫ h := by
    simpa [q, r, Ysec, T, eX] using
      pushforwardProjectionIsoComma_raw_section_factor_map_eq
        (u := u) (p := p) Y g h χ hχ
  have hmap : q.map χ = h := by
    exact (cancel_epi W.obj.hom).1 hmap_left
  refine IsHomLift.of_fac' q h χ rfl rfl ?_
  simpa [q] using hmap
/-- Helper for Lemma 8.12.6 Support: a strict-side `q`-lift into the precomposition object becomes the raw lift required by the source-faithful section universal property after re-inserting the source chart `eX.hom`. -/
theorem pushforwardProjectionIsoComma_q_lift_to_raw_section_factor
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {W : pushforwardProjectionIsoComma (u := u) (p := p)}
      (h : q.obj W ⟶ q.obj T) (χ : W ⟶ T),
      q.IsHomLift h χ →
      r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom) χ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro W h χ hχ
  letI : q.IsHomLift h χ := hχ
  have hmap : q.map χ = h := by
    simpa [q] using (IsHomLift.fac' q h χ)
  have hleft_comp :
      χ.hom.left ≫ T.obj.hom = W.obj.hom ≫ h := by
    simpa [q, T, Category.assoc, hmap] using
      pushforwardProjectionIsoComma_precomposeObj_lift_left_comp_hom_of_map_eq
        (u := u) (p := p) Y g h χ hmap
  have hchart :
      T.obj.hom ≫ eX.hom = 𝟙 V := by
    simpa [Ysec, T, eX] using
      pushforwardProjectionIsoComma_precomposeObj_hom_comp_baseIso_hom
        (u := u) (p := p) Y g
  have hpost :
      χ.hom.left ≫ T.obj.hom ≫ eX.hom = (W.obj.hom ≫ h) ≫ eX.hom := by
    have hpost0 :
        (χ.hom.left ≫ T.obj.hom) ≫ eX.hom = (W.obj.hom ≫ h) ≫ eX.hom := by
      exact congrArg (fun k ↦ k ≫ eX.hom) hleft_comp
    simpa [Category.assoc] using hpost0
  have hleft :
      χ.hom.left = W.obj.hom ≫ h ≫ eX.hom := by
    calc
      χ.hom.left = χ.hom.left ≫ (T.obj.hom ≫ eX.hom) := by
        simpa [Category.assoc] using congrArg (fun k ↦ χ.hom.left ≫ k) hchart.symm
      _ = χ.hom.left ≫ T.obj.hom ≫ eX.hom := by simp
      _ = (W.obj.hom ≫ h) ≫ eX.hom := hpost
      _ = W.obj.hom ≫ h ≫ eX.hom := by simp [Category.assoc]
  exact
    IsHomLift.of_fac' r (W.obj.hom ≫ h ≫ eX.hom) χ rfl rfl <|
      by simpa [r, pushforwardProjectionIsoCommaProjection, Category.assoc] using hleft
/-- Helper for Lemma 8.12.6 Support: once the strict composite projection equation is fixed, the raw section-object universal property produces a unique factor and the source chart on the precomposition object cancels to show that factor is literally a `q`-lift over `h`. -/
theorem pushforwardProjectionIsoComma_raw_section_preunit_factor_of_map_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {W : pushforwardProjectionIsoComma (u := u) (p := p)}
      (h : q.obj W ⟶ q.obj T) (τ : W ⟶ Ysec),
      q.map τ = h ≫ eX.hom ≫ g →
      ∃! χ : W ⟶ T, q.IsHomLift h χ ∧ χ ≫
        pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g = τ := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro W h τ hτq
  let α := pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g
  letI : r.IsStronglyCartesian g α :=
    pushforwardProjectionIsoComma_section_precompose_isStronglyCartesian
      (u := u) (p := p) Y g
  have hτraw :
      r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom ≫ g) τ := by
    simpa [q, r, Ysec, T, eX, Category.assoc] using
      pushforwardProjectionIsoComma_raw_section_tau_isHomLift
        (u := u) (p := p) Y g h τ hτq
  have hχraw :
      ∃! χ : W ⟶ T, r.IsHomLift (W.obj.hom ≫ h ≫ eX.hom) χ ∧ χ ≫ α = τ := by
    exact
      @Functor.IsStronglyCartesian.universal_property' _ _ _ _ r _ _ _ _ g α inferInstance
        _ (W.obj.hom ≫ h ≫ eX.hom) τ (by simpa [Category.assoc] using hτraw)
  obtain ⟨χ, hχ, hχuniq⟩ := hχraw
  refine ⟨χ, ?_, ?_⟩
  · refine ⟨?_, hχ.2⟩
    exact
      pushforwardProjectionIsoComma_raw_section_factor_to_q_lift
        (u := u) (p := p) Y g h χ hχ.1
  · intro π hπ
    apply hχuniq π
    refine ⟨?_, hπ.2⟩
    exact
      pushforwardProjectionIsoComma_q_lift_to_raw_section_factor
        (u := u) (p := p) Y g h π hπ.1
/-- Helper for Lemma 8.12.6 Support: the transported raw-section lift is the strict-side object that should be shown strongly cartesian before any source replacement is attempted. -/
theorem pushforwardProjectionIsoComma_raw_section_lift_preunit_isStronglyCartesian
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    q.IsStronglyCartesian
      (eX.hom ≫ g)
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g) := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The preunit morphism already has the transported base map before the final unit inverse.
    simpa [q, Ysec, eX] using
      pushforwardProjectionIsoComma_section_precompose_isHomLift_transported
        (u := u) (p := p) Y g
  · intro W h τ hτ
    have hτq :
        q.map τ = h ≫ eX.hom ≫ g := by
      simpa [q, Ysec, eX, Category.assoc] using
        (IsHomLift.fac' q (h ≫ (eX.hom ≫ g)) τ)
    simpa [q, Ysec, eX] using
      pushforwardProjectionIsoComma_raw_section_preunit_factor_of_map_eq
        (u := u) (p := p) Y g h τ hτq
/-- Helper for Lemma 8.12.6 Support: the transported raw-section lift is the strict-side object that should be shown strongly cartesian before any source replacement is attempted. -/
theorem pushforwardProjectionIsoComma_raw_section_lift_isStronglyCartesian_transported
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    q.IsStronglyCartesian
      (eX.hom ≫ g)
      (pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g ≫
        ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y)) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let α :=
    pushforwardProjectionIsoComma_precomposeHom (u := u) (p := p) Ysec g
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app Y)
  let ε := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).hom.app Y)
  let e := (pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).app Y
  have hpre :
      q.IsStronglyCartesian (eX.hom ≫ g) α := by
    simpa [q, Ysec, eX, α] using
      pushforwardProjectionIsoComma_raw_section_lift_preunit_isStronglyCartesian
        (u := u) (p := p) Y g
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The composite lift has already been recorded at the hom-lift level.
    simpa [q, Ysec, eX, α, η] using
      pushforwardProjectionIsoComma_raw_section_lift_isHomLift_transported
        (u := u) (p := p) Y g
  · intro W h τ hτ
    letI : q.IsStronglyCartesian (eX.hom ≫ g) α := hpre
    have hε :
        q.IsHomLift (𝟙 (q.obj Y)) ε := by
      simpa [q, ε] using
        pushforwardProjectionIsoComma_unitIso_hom_app_isHomLift
          (u := u) (p := p) Y
    letI : q.IsHomLift (h ≫ (eX.hom ≫ g)) τ := hτ
    letI : q.IsHomLift (𝟙 (q.obj Y)) ε := hε
    have hτε :
        q.IsHomLift (h ≫ (eX.hom ≫ g)) (τ ≫ ε) := by
      have hτε' :
          q.IsHomLift ((h ≫ (eX.hom ≫ g)) ≫ 𝟙 (q.obj Y)) (τ ≫ ε) := by
        exact
          @CategoryTheory.IsHomLift.comp _ _ _ _ q _ _ _ _ _ _
            (h ≫ (eX.hom ≫ g)) (𝟙 (q.obj Y)) τ ε hτ hε
      simpa [q, Ysec, eX, ε, Category.assoc] using
        hτε'
    have hχex :
        ∃! χ : W ⟶ _,
          q.IsHomLift h χ ∧ χ ≫ α = τ ≫ ε := by
      exact
        @Functor.IsStronglyCartesian.universal_property' _ _ _ _ q
          _ _ _ _ (eX.hom ≫ g) α hpre _ h (τ ≫ ε) hτε
    obtain ⟨χ, hχ, hχuniq⟩ := hχex
    refine ⟨χ, ⟨hχ.1, ?_⟩, ?_⟩
    · -- Cancel the unit comparison after factoring through the raw preunit lift.
      have hχη : (χ ≫ α) ≫ η = (τ ≫ ε) ≫ η := by
        exact congrArg (fun k ↦ k ≫ η) hχ.2
      have hεη : (τ ≫ ε) ≫ η = τ := by
        simpa [e, ε, η, Category.assoc] using
          congrArg (fun k ↦ τ ≫ k) e.hom_inv_id
      calc
        χ ≫ α ≫ η = (χ ≫ α) ≫ η := by simp [Category.assoc]
        _ = (τ ≫ ε) ≫ η := hχη
        _ = τ := hεη
    · intro π hπ
      apply hχuniq π
      refine ⟨hπ.1, ?_⟩
      have hπ' := congrArg (fun k ↦ k ≫ ε) hπ.2
      have hπε :
          ((π ≫ α) ≫ η) ≫ ε = τ ≫ ε := by
        simpa [Ysec, α, ε, η, Category.assoc] using hπ'
      have hηε :
          ((π ≫ α) ≫ η) ≫ ε = π ≫ α := by
        simpa [e, Ysec, α, ε, η, Category.assoc] using
          congrArg (fun k ↦ (π ≫ α) ≫ k) e.inv_hom_id
      calc
        π ≫ α = ((π ≫ α) ≫ η) ≫ ε := hηε.symm
        _ = τ ≫ ε := hπε
/-- Helper for Lemma 8.12.6 Support: the final strict source replacement begins by choosing a raw strongly cartesian lift of the inverse source chart into the identity-chart section over the transported source object. -/
theorem pushforwardProjectionIsoComma_raw_section_source_chart_lift
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∃ X : pushforwardProjectionIsoComma (u := u) (p := p),
      ∃ α : X ⟶ Tsec,
        (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsStronglyCartesian eX.inv α := by
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  letI : r.IsFibered :=
    pushforwardProjectionIsoCommaProjection_isFibered (u := u) (p := p)
  obtain ⟨X, α, hαcart⟩ := IsPreFibered.exists_isCartesian (p := r) (a := Tsec) rfl eX.inv
  letI : r.IsCartesian eX.inv α := hαcart
  refine ⟨X, α, ?_⟩
  exact Functor.IsFibered.isStronglyCartesian_of_isCartesian r eX.inv α
/-- Helper for Lemma 8.12.6 Support: the comma square for a raw source-chart lift and the vertical
unit comparison identify the strict-side map after postcomposition by the unit inverse. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_map_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      (α : X ⟶ Tsec),
      r.IsStronglyCartesian eX.inv α →
      X.obj.hom ≫ q.map (α ≫ η) = α.hom.left := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
  intro X α _hα
  have hη : q.map η = 𝟙 (q.obj T) := by
    -- The unit inverse is vertical for the strict composite projection.
    letI : q.IsHomLift (𝟙 (q.obj T)) η := by
      simpa [q, η] using
        pushforwardProjectionIsoComma_unitIso_inv_app_isHomLift (u := u) (p := p) T
    simpa [q] using (IsHomLift.fac' q (𝟙 (q.obj T)) η)
  have hα : X.obj.hom ≫ q.map α = α.hom.left := by
    -- The target of `α` is an identity-chart section object, so its comma square has no
    -- remaining target chart on the left.
    simpa [q, Tsec, pushforwardProjectionIsoCommaForget,
      pushforwardProjectionIsoCommaSection, pushforwardProjectionIsoCommaSectionObj,
      Category.assoc] using α.hom.w.symm
  have hmap : q.map (α ≫ η) = q.map α := by
    -- Postcomposition by the vertical unit inverse does not change the strict base map.
    have hη' : q.map η = 𝟙 (q.obj Tsec) := by
      simpa [q, Tsec, η] using hη
    rw [Functor.map_comp]
    exact (congrArg (fun k ↦ q.map α ≫ k) hη').trans (Category.comp_id (q.map α))
  simpa [hmap] using hα
/-- Helper for Lemma 8.12.6 Support: a raw source-chart lift over `eX.inv` fixes the left object of its domain to be the literal source object `V`. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_domain_eq
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      (α : X ⟶ Tsec),
      r.IsStronglyCartesian eX.inv α →
      X.obj.left = V := by
  dsimp
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro X α hα
  letI : r.IsHomLift eX.inv α := hα.toIsHomLift
  -- A raw lift over `eX.inv : V ⟶ _` has source object exactly `V`.
  simpa [r, pushforwardProjectionIsoCommaProjection] using
    (IsHomLift.domain_eq r eX.inv α)
/-- Helper for Lemma 8.12.6 Support: once the domain object is identified with `V`, the raw hom-lift equation forces the left comma component of `α` to be the transported inverse chart. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_fac_left
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      (α : X ⟶ Tsec),
      (hα : r.IsStronglyCartesian eX.inv α) →
      let hX : X.obj.left = V :=
        pushforwardProjectionIsoComma_raw_source_chart_domain_eq
          (u := u) (p := p) Y g α hα
      α.hom.left = eqToHom hX ≫ eX.inv := by
  dsimp
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  intro X α hα
  let hX : X.obj.left = V :=
    pushforwardProjectionIsoComma_raw_source_chart_domain_eq
      (u := u) (p := p) Y g α hα
  letI : r.IsHomLift eX.inv α := hα.toIsHomLift
  have hdom : IsHomLift.domain_eq r eX.inv α = hX := by
    apply Subsingleton.elim
  have hcod : (IsHomLift.codomain_eq r eX.inv α).symm = rfl := by
    apply Subsingleton.elim
  -- Normalize the generic hom-lift formula by replacing its domain/codomain transports with the
  -- named domain equality and the definitional identity-chart target equality.
  have hfac := IsHomLift.fac' r eX.inv α
  rw [hdom, hcod] at hfac
  simpa [r, Ysec, T, Tsec, eX, pushforwardProjectionIsoCommaProjection,
    pushforwardProjectionIsoCommaSection, pushforwardProjectionIsoCommaSectionObj,
    pushforwardProjectionIsoCommaForget, hX, Category.assoc] using hfac
/-- Helper for Lemma 8.12.6 Support: after canceling the stored source chart on the domain object, the strict-side map of `α ≫ η` is literally the inverse chart followed by the transported domain identification and the fixed inverse source chart. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_inverse_base_map
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      [IsIso X.obj.hom]
      (α : X ⟶ Tsec),
      (hα : r.IsStronglyCartesian eX.inv α) →
      let hX : X.obj.left = V :=
        pushforwardProjectionIsoComma_raw_source_chart_domain_eq
          (u := u) (p := p) Y g α hα
      q.map (α ≫ η) = (asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
  intro X hXiso α hα
  letI : IsIso X.obj.hom := hXiso
  let hX : X.obj.left = V :=
    pushforwardProjectionIsoComma_raw_source_chart_domain_eq
      (u := u) (p := p) Y g α hα
  have hleft :
      X.obj.hom ≫ q.map (α ≫ η) = eqToHom hX ≫ eX.inv := by
    -- The comma square gives the left side as `α.hom.left`; the raw lift equation then
    -- identifies that component with the transported inverse chart.
    have hmap :
        X.obj.hom ≫ q.map (α ≫ η) = α.hom.left := by
      simpa [q, r, Ysec, T, Tsec, eX, η] using
        pushforwardProjectionIsoComma_raw_source_chart_map_eq
          (u := u) (p := p) Y g α hα
    have hfac :=
      pushforwardProjectionIsoComma_raw_source_chart_fac_left
        (u := u) (p := p) Y g α hα
    have hfacDomain :
        (pushforwardProjectionIsoComma_raw_source_chart_domain_eq
          (u := u) (p := p) Y g α hα) = hX := by
      apply Subsingleton.elim
    rw [hfacDomain] at hfac
    exact hmap.trans hfac
  -- Cancel the source chart isomorphism by comparing after precomposition with `X.obj.hom`.
  apply (cancel_epi X.obj.hom).1
  have hright :
      X.obj.hom ≫ ((asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv) =
        eqToHom hX ≫ eX.inv := by
    simp
  exact hleft.trans hright.symm
/-- Helper for Lemma 8.12.6 Support: after canceling the stored source chart on the domain object, the raw source-chart lift becomes a strict `q`-hom-lift over the normalized inverse-chart base map `X.obj.hom⁻¹ ≫ α.hom.left`. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_to_q_homLift_over_inverse_chart
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      [IsIso X.obj.hom]
      (α : X ⟶ Tsec),
      (hα : r.IsStronglyCartesian eX.inv α) →
      let hX : X.obj.left = V :=
        pushforwardProjectionIsoComma_raw_source_chart_domain_eq
          (u := u) (p := p) Y g α hα
      q.IsHomLift ((asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv) (α ≫ η) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
  intro X hXiso α hα
  letI : IsIso X.obj.hom := hXiso
  let hX : X.obj.left = V :=
    pushforwardProjectionIsoComma_raw_source_chart_domain_eq
      (u := u) (p := p) Y g α hα
  -- Package the normalized map equality as the strict composite hom-lift over the inverse chart.
  refine
    IsHomLift.of_fac' q ((asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv)
      (α ≫ η) rfl rfl ?_
  simpa [q, r, Ysec, T, Tsec, eX, η, hX] using
    pushforwardProjectionIsoComma_raw_source_chart_inverse_base_map
      (u := u) (p := p) Y g α hα

section

omit [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
  [PreservesLimitsOfShape WalkingCospan u]
  [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.6 Support: a strict `q`-hom-lift into an iso-comma object can be rewritten as the corresponding raw lift after re-inserting the codomain chart. -/
theorem pushforwardProjectionIsoComma_q_homLift_to_raw_factor
    {R : D}
    {B W : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso B.obj.hom]
    (hB : B.obj.left = R)
    (h :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj W ⟶
        (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
          u.pushforwardProjection p).obj B)
    (τ : W ⟶ B)
    (hτ :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
        h τ) :
    (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift
      (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB)
      τ := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  letI : q.IsHomLift h τ := hτ
  have hmap : q.map τ = h := by
    simpa [q] using (IsHomLift.fac' q h τ)
  have hw : τ.hom.left ≫ B.obj.hom = W.obj.hom ≫ h := by
    -- The comma square for `τ` turns the strict map equation into a charted raw equation.
    have hw0 : τ.hom.left ≫ B.obj.hom = W.obj.hom ≫ q.map τ := by
      simpa [q, pushforwardProjectionIsoCommaForget, Category.assoc] using τ.hom.w
    exact hw0.trans (by simpa [Category.assoc] using congrArg (fun k ↦ W.obj.hom ≫ k) hmap)
  have hleft : τ.hom.left = W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv := by
    -- Cancel the target chart of `B` to recover the raw left component.
    apply (cancel_mono B.obj.hom).1
    have hright :
        (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv) ≫ B.obj.hom =
          W.obj.hom ≫ h := by
      simp [Category.assoc]
    exact hw.trans hright.symm
  refine
    IsHomLift.of_fac' r
      (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB) τ rfl hB ?_
  simpa [r, pushforwardProjectionIsoCommaProjection, hleft, Category.assoc]
/-- Helper for Lemma 8.12.6 Support: once the raw factor through `X` is normalized by the explicit codomain equality `hB`, the stored charts on source and target cancel and recover a literal strict `q`-hom-lift. -/
theorem pushforwardProjectionIsoComma_raw_factor_to_q_homLift
    {R : D}
    {B W : pushforwardProjectionIsoComma (u := u) (p := p)}
    [IsIso W.obj.hom] [IsIso B.obj.hom]
    (hB : B.obj.left = R)
    (h :
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj W ⟶
        (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙
          u.pushforwardProjection p).obj B)
    (χ : W ⟶ B)
    (hχ :
      (pushforwardProjectionIsoCommaProjection (u := u) (p := p)).IsHomLift
        (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB)
        χ) :
    (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).IsHomLift
      h χ := by
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  letI :
      r.IsHomLift (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB) χ :=
    hχ
  have hraw :=
    IsHomLift.fac' r (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB) χ
  have hdom :
      IsHomLift.domain_eq r
        (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB) χ = rfl := by
    apply Subsingleton.elim
  have hcod :
      (IsHomLift.codomain_eq r
        (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv ≫ eqToHom hB) χ).symm =
        hB.symm := by
    apply Subsingleton.elim
  rw [hdom, hcod] at hraw
  have hleft : χ.hom.left = W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv := by
    -- Normalize the raw hom-lift equation, canceling the target equality transport `hB`.
    simpa [r, pushforwardProjectionIsoCommaProjection, Category.assoc] using hraw
  have hw : χ.hom.left ≫ B.obj.hom = W.obj.hom ≫ q.map χ := by
    -- The comma square relates the raw left component to the strict map of `χ`.
    simpa [q, pushforwardProjectionIsoCommaForget, Category.assoc] using χ.hom.w
  have hmap_left : W.obj.hom ≫ q.map χ = W.obj.hom ≫ h := by
    have hleft_post :
        χ.hom.left ≫ B.obj.hom =
          (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv) ≫ B.obj.hom := by
      exact congrArg (fun k ↦ k ≫ B.obj.hom) hleft
    have htarget :
        (W.obj.hom ≫ h ≫ (asIso B.obj.hom).inv) ≫ B.obj.hom =
          W.obj.hom ≫ h := by
      simp [Category.assoc]
    exact hw.symm.trans (hleft_post.trans htarget)
  have hmap : q.map χ = h := by
    -- The source chart of `W` is an isomorphism, hence epi.
    exact (cancel_epi W.obj.hom).1 hmap_left
  refine IsHomLift.of_fac' q h χ rfl rfl ?_
  simpa [q] using hmap

end

/-- Helper for Lemma 8.12.6 Support: the normalized inverse-chart lift is already strongly cartesian for the strict composite projection, before the final source replacement step. -/
theorem pushforwardProjectionIsoComma_raw_source_chart_to_q_isStronglyCartesian_over_inverse_chart
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      [IsIso X.obj.hom]
      (α : X ⟶ Tsec),
      (hα : r.IsStronglyCartesian eX.inv α) →
      let hX : X.obj.left = V :=
        pushforwardProjectionIsoComma_raw_source_chart_domain_eq
          (u := u) (p := p) Y g α hα
      q.IsStronglyCartesian ((asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv) (α ≫ η) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
  intro X hXiso α hα
  letI : IsIso X.obj.hom := hXiso
  let hX : X.obj.left = V :=
    pushforwardProjectionIsoComma_raw_source_chart_domain_eq
      (u := u) (p := p) Y g α hα
  let f := (asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv
  refine
    { toIsHomLift := ?_
      universal_property' := ?_ }
  · -- The normalized map computation gives the hom-lift part of strong cartesianness.
    simpa [q, r, Ysec, T, Tsec, eX, η, hX, f] using
      pushforwardProjectionIsoComma_raw_source_chart_to_q_homLift_over_inverse_chart
        (u := u) (p := p) Y g α hα
  · intro W h τ hτ
    let ε := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).hom.app T)
    let e := (pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).app T
    letI : IsIso W.obj.hom := W.property
    letI : IsIso Tsec.obj.hom := Tsec.property
    have hε :
        q.IsHomLift (𝟙 (q.obj T)) ε := by
      -- The unit hom is vertical for the strict composite projection.
      simpa [q, ε] using
        pushforwardProjectionIsoComma_unitIso_hom_app_isHomLift
          (u := u) (p := p) T
    have hτε :
        q.IsHomLift (h ≫ f) (τ ≫ ε) := by
      -- Postcompose the competitor with the vertical unit hom so it targets `Tsec`.
      letI : q.IsHomLift (h ≫ f) τ := hτ
      letI : q.IsHomLift (𝟙 (q.obj T)) ε := hε
      have hcomp :
          q.IsHomLift ((h ≫ f) ≫ 𝟙 (q.obj T)) (τ ≫ ε) := by
        exact
          @CategoryTheory.IsHomLift.comp _ _ _ _ q _ _ _ _ _ _
            (h ≫ f) (𝟙 (q.obj T)) τ ε hτ hε
      have hbase : (h ≫ f) ≫ 𝟙 (q.obj T) = h ≫ f := by
        exact Category.comp_id (h ≫ f)
      rw [hbase] at hcomp
      exact hcomp
    have hτraw :
        r.IsHomLift ((W.obj.hom ≫ h ≫ (asIso X.obj.hom).inv ≫ eqToHom hX) ≫ eX.inv)
          (τ ≫ ε) := by
      -- Reinsert the source chart of `W` and the identity target chart of `Tsec` to obtain the
      -- raw competitor needed by the strong-cartesian universal property of `α`.
      simpa [q, r, Ysec, T, Tsec, eX, η, ε, f, Category.assoc] using
        pushforwardProjectionIsoComma_q_homLift_to_raw_factor
          (u := u) (p := p) (R := q.obj T) (B := Tsec) (W := W)
          (hB := rfl) (h := h ≫ f) (τ := τ ≫ ε) hτε
    have hχex :
        ∃! χ : W ⟶ X,
          r.IsHomLift (W.obj.hom ≫ h ≫ (asIso X.obj.hom).inv ≫ eqToHom hX) χ ∧
            χ ≫ α = τ ≫ ε := by
      exact
        @Functor.IsStronglyCartesian.universal_property' _ _ _ _ r
          _ _ _ _ eX.inv α hα _
          (W.obj.hom ≫ h ≫ (asIso X.obj.hom).inv ≫ eqToHom hX)
          (τ ≫ ε) (by simpa [Category.assoc] using hτraw)
    obtain ⟨χ, hχ, hχuniq⟩ := hχex
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · -- Translate the raw factor back to a strict q-hom-lift over `h`.
      exact
        pushforwardProjectionIsoComma_raw_factor_to_q_homLift
          (u := u) (p := p) (R := V) (B := X) (W := W)
          (hB := hX) (h := h) (χ := χ) hχ.1
    · -- Cancel `ε ≫ η = 𝟙` after the raw factorization through `α`.
      have hχη : (χ ≫ α) ≫ η = (τ ≫ ε) ≫ η := by
        exact congrArg (fun k ↦ k ≫ η) hχ.2
      have hεη : (τ ≫ ε) ≫ η = τ := by
        have hεη0 :
            τ ≫ (ε ≫ η) = τ ≫ 𝟙 T := by
          simpa [e, ε, η] using congrArg (fun k ↦ τ ≫ k) e.hom_inv_id
        have hassoc : (τ ≫ ε) ≫ η = τ ≫ (ε ≫ η) := by
          simp [Category.assoc]
        exact hassoc.trans (hεη0.trans (Category.comp_id τ))
      calc
        χ ≫ α ≫ η = (χ ≫ α) ≫ η := by
          simp [Category.assoc]
        _ = (τ ≫ ε) ≫ η := hχη
        _ = τ := hεη
    · intro π hπ
      apply hχuniq π
      refine ⟨?_, ?_⟩
      · -- A competing strict q-lift over `h` is also a raw factor for `α`.
        exact
          pushforwardProjectionIsoComma_q_homLift_to_raw_factor
            (u := u) (p := p) (R := V) (B := X) (W := W)
            (hB := hX) (h := h) (τ := π) hπ.1
      · -- Postcompose the strict equality by `ε` and cancel `η ≫ ε = 𝟙`.
        have hπ' := congrArg (fun k ↦ k ≫ ε) hπ.2
        have hπη :
            ((π ≫ α) ≫ η) ≫ ε = τ ≫ ε := by
          simpa [Ysec, T, Tsec, eX, η, ε, Category.assoc] using hπ'
        have hηε :
            ((π ≫ α) ≫ η) ≫ ε = π ≫ α := by
          have hηε0 :
              (π ≫ α) ≫ (η ≫ ε) = (π ≫ α) ≫ 𝟙 Tsec := by
            simpa [e, η, ε] using
              congrArg (fun k ↦ (π ≫ α) ≫ k) e.inv_hom_id
          have hassoc : ((π ≫ α) ≫ η) ≫ ε = (π ≫ α) ≫ (η ≫ ε) := by
            simp [Category.assoc]
          exact hassoc.trans (hηε0.trans (Category.comp_id (π ≫ α)))
        calc
          π ≫ α = ((π ≫ α) ≫ η) ≫ ε := hηε.symm
          _ = τ ≫ ε := hπη
/-- Helper for Lemma 8.12.6 Support: once the source chart of the raw domain object has been replaced by the literal source object `V`, composing that strict source replacement with the normalized inverse-chart lift produces a strict strongly cartesian morphism lying literally over `eX.inv`. -/
theorem pushforwardProjectionIsoComma_source_chart_replacement_to_q_isStronglyCartesian
    (Y : pushforwardProjectionIsoComma (u := u) (p := p))
    {V : D}
    (g : V ⟶
      (pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p).obj Y) :
    let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
    let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
    let Ysec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
    let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
    let Tsec :=
      (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
        ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
    let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
      Ysec.obj.right (g ≫ Ysec.obj.hom)
    let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
    ∀ {X : pushforwardProjectionIsoComma (u := u) (p := p)}
      [IsIso X.obj.hom]
      (α : X ⟶ Tsec),
      (hα : r.IsStronglyCartesian eX.inv α) →
      let hX : X.obj.left = V :=
        pushforwardProjectionIsoComma_raw_source_chart_domain_eq
          (u := u) (p := p) Y g α hα
      ∀ {X' : pushforwardProjectionIsoComma (u := u) (p := p)}
        (δ : X' ⟶ X),
        q.IsStronglyCartesian (eqToHom hX.symm ≫ X.obj.hom) δ →
        q.IsStronglyCartesian eX.inv (δ ≫ α ≫ η) := by
  dsimp
  let q := pushforwardProjectionIsoCommaForget (u := u) (p := p) ⋙ u.pushforwardProjection p
  let r := pushforwardProjectionIsoCommaProjection (u := u) (p := p)
  let Ysec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj Y)
  let T := pushforwardProjectionIsoComma_precomposeObj (u := u) (p := p) Ysec g
  let Tsec :=
    (pushforwardProjectionIsoCommaSection (u := u) (p := p)).obj
      ((pushforwardProjectionIsoCommaForget (u := u) (p := p)).obj T)
  let eX := pushforwardProjection_precompose_modelBaseIso (u := u) (p := p)
    Ysec.obj.right (g ≫ Ysec.obj.hom)
  let η := ((pushforwardProjectionIsoComma_unitIso (u := u) (p := p)).inv.app T)
  intro X hXiso α hα
  letI : IsIso X.obj.hom := hXiso
  let hX : X.obj.left = V :=
    pushforwardProjectionIsoComma_raw_source_chart_domain_eq
      (u := u) (p := p) Y g α hα
  intro X' δ hδ
  let f := (asIso X.obj.hom).inv ≫ eqToHom hX ≫ eX.inv
  have hαq : q.IsStronglyCartesian f (α ≫ η) := by
    -- The previous adapter makes `α ≫ η` strongly cartesian over the normalized inverse chart.
    simpa [q, r, Ysec, T, Tsec, eX, η, hX, f] using
      pushforwardProjectionIsoComma_raw_source_chart_to_q_isStronglyCartesian_over_inverse_chart
        (u := u) (p := p) Y g α hα
  letI : q.IsStronglyCartesian (eqToHom hX.symm ≫ X.obj.hom) δ := hδ
  letI : q.IsStronglyCartesian f (α ≫ η) := hαq
  have hcomp :
      q.IsStronglyCartesian ((eqToHom hX.symm ≫ X.obj.hom) ≫ f)
        (δ ≫ (α ≫ η)) := by
    infer_instance
  -- The source replacement base followed by the normalized inverse-chart base cancels to `eX.inv`.
  simpa [q, f, Category.assoc] using hcomp

end Functor

end

end CategoryTheory
