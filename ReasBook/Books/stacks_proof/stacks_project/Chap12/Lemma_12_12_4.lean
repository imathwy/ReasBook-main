import stacks_proof.stacks_project.Chap12.Definition_12_12_1

universe vA vB uA uB

/-
Domain-style sampling:
- primary domain: cohomological `δ`-functors on abelian categories, with weak effaceability as the
  degreewise hypothesis used to prove universality.
- declarations inspected in the nearby owner API and supporting mathlib object-property API:
  `CohomologicalDeltaFunctor`,
  `CohomologicalDeltaFunctor.IsUniversal`,
  `CohomologicalDeltaFunctor.Hom`,
  `CohomologicalDeltaFunctor.universal_delta_functor_unique_up_to_unique_iso`.
- best owner abstraction in this file: `CohomologicalDeltaFunctor.IsUniversal` for the conclusion;
  the weak-effaceability assumption is source-facing data and should stay spelled out directly.
- `source-facing`: the positive-degree effaceability criterion
  `∀ n > 0, ∀ X, ∃ Y, ∃ u : X ⟶ Y, Mono u ∧ Fⁿ(u) = 0`.
- `core/canonical`: `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: none needed in the public API of this lemma; the additive-functor-to-functor
  forgetful view stays internal to the theorem statement.
- primitive data vs derived API: the primitive datum is the source-level existence, for each
  positive degree and each object, of a monomorphism annihilated by that degree functor; the
  universality conclusion is the derived canonical property.
-/

namespace CategoryTheory

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

open Limits

/-- Helper for Lemma 12.12.4: in the short exact sequence
`0 ⟶ X ⟶ Y ⟶ cokernel u ⟶ 0` coming from a monomorphism `u`, if `Fⁿ⁺¹(u) = 0` then the
connecting morphism `Fⁿ(cokernel u) ⟶ Fⁿ⁺¹(X)` is the cokernel of `Fⁿ(Y) ⟶ Fⁿ(cokernel u)`. -/
lemma effacement_connecting_is_cokernel
    (F : CohomologicalDeltaFunctor A B)
    {n : ℕ} {X Y : A} (u : X ⟶ Y) [Mono u]
    (hkill : (F (n + 1)).obj.map u = 0) :
    Nonempty
      (IsColimit
        (Limits.CokernelCofork.ofπ
          (F.δ
            (ShortComplex.ShortExact.mk'
              (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
              (inferInstance : Epi (Limits.cokernel.π u)))
            n)
          (F.map_g_comp_δ
            (ShortComplex.ShortExact.mk'
              (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
              (inferInstance : Epi (Limits.cokernel.π u)))
            n))) := by
  let S : ShortComplex A := ShortComplex.cokernelSequence u
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
    (inferInstance : Epi (Limits.cokernel.π u))
  -- The long exact sequence already supplies exactness at the degree-`n` cokernel term.
  have hExact : (ShortComplex.mk ((F n).obj.map S.g) (F.δ hS n) (F.map_g_comp_δ hS n)).Exact :=
    F.exact_map_g_δ hS n
  -- The effacement hypothesis turns the next map into zero, so the connecting morphism is epi.
  have hEpi : Epi (F.δ hS n) := by
    let T : ShortComplex B :=
      ShortComplex.mk (F.δ hS n) ((F (n + 1)).obj.map S.f) (F.δ_comp_map_f hS n)
    have hT : T.Exact := F.exact_δ_map_f hS n
    have hzero : T.g = 0 := by
      simpa [T, S] using hkill
    rw [T.exact_iff_epi hzero] at hT
    simpa [T] using hT
  -- Exactness together with epimorphicity identifies the connecting morphism as the cokernel.
  simpa [S, hS] using (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).1 ⟨hExact, hEpi⟩

/-- Helper for Lemma 12.12.4: a degree-`n` natural transformation descends across the cokernel
presentation of the successor degree in any short exact sequence. -/
lemma effacement_degree_comparison_descends
    {F G : CohomologicalDeltaFunctor A B}
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (α : (F n).obj ⟶ (G n).obj) :
    (F n).obj.map S.g ≫ α.app S.X₃ ≫ G.δ hS n = 0 := by
  -- Naturality moves the degree-`n` comparison past `S.g`.
  calc
    (F n).obj.map S.g ≫ α.app S.X₃ ≫ G.δ hS n
        = α.app S.X₂ ≫ (G n).obj.map S.g ≫ G.δ hS n := by
            rw [NatTrans.naturality_assoc]
    _ = α.app S.X₂ ≫ 0 := by
      rw [G.map_g_comp_δ hS n]
    _ = 0 := by simp

/-- Helper for Lemma 12.12.4: once an effacement for `X` has been chosen, the degree-`n`
comparison uniquely determines the successor component at `X`. -/
lemma effacement_succ_component_existsUnique
    {F G : CohomologicalDeltaFunctor A B}
    {n : ℕ} {X Y : A} (u : X ⟶ Y) [Mono u]
    (hkill : (F (n + 1)).obj.map u = 0)
    (α : (F n).obj ⟶ (G n).obj) :
    let S : ShortComplex A := ShortComplex.cokernelSequence u
    let hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
      (inferInstance : Epi (Limits.cokernel.π u))
    ∃! ψ : (F (n + 1)).obj.obj X ⟶ (G (n + 1)).obj.obj X,
      F.δ hS n ≫ ψ = α.app (Limits.cokernel u) ≫ G.δ hS n := by
  let S : ShortComplex A := ShortComplex.cokernelSequence u
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
    (inferInstance : Epi (Limits.cokernel.π u))
  obtain ⟨hcolim⟩ := effacement_connecting_is_cokernel F u hkill
  -- The degree-`n` comparison kills the image term, so it factors uniquely through the cokernel.
  have hk0 : (F n).obj.map S.g ≫ α.app S.X₃ ≫ G.δ hS n = 0 :=
    effacement_degree_comparison_descends hS n α
  have hk :
      (F n).obj.map S.g ≫ (α.app S.X₃ ≫ G.δ hS n) =
        0 ≫ (α.app S.X₃ ≫ G.δ hS n) := by
    simp at hk0 ⊢
  -- The universal property of the cokernel produces the unique successor component.
  exact
    CategoryTheory.Limits.Cofork.IsColimit.existsUnique hcolim (α.app S.X₃ ≫ G.δ hS n) hk

/-- Helper for Lemma 12.12.4: an effacement of `X` also determines uniquely the successor map
into any short exact row reached by a row morphism from the cokernel sequence of the effacement. -/
lemma effacement_succ_component_existsUnique_over_row_hom
    {F G : CohomologicalDeltaFunctor A B}
    {n : ℕ} {X Y : A} (u : X ⟶ Y) [Mono u]
    (hkill : (F (n + 1)).obj.map u = 0)
    {T : ShortComplex A} (hT : T.ShortExact)
    (φ : ShortComplex.cokernelSequence u ⟶ T)
    (α : (F n).obj ⟶ (G n).obj) :
    let S : ShortComplex A := ShortComplex.cokernelSequence u
    let hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
      (inferInstance : Epi (Limits.cokernel.π u))
    ∃! ψ : (F (n + 1)).obj.obj X ⟶ (G (n + 1)).obj.obj T.X₁,
      F.δ hS n ≫ ψ = α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
  let S : ShortComplex A := ShortComplex.cokernelSequence u
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
    (inferInstance : Epi (Limits.cokernel.π u))
  obtain ⟨hcolim⟩ := effacement_connecting_is_cokernel F u hkill
  -- Naturality across the row morphism moves the target comparison to the degree-`n` cokernel.
  have hk0 :
      (F n).obj.map S.g ≫ α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n =
        0 := by
    calc
      (F n).obj.map S.g ≫ α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n
          = α.app S.X₂ ≫ (G n).obj.map S.g ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
              rw [NatTrans.naturality_assoc]
      _ = α.app S.X₂ ≫ ((G n).obj.map S.g ≫ (G n).obj.map φ.τ₃) ≫ G.δ hT n := by
            simp [Category.assoc]
      _ = α.app S.X₂ ≫ (G n).obj.map (S.g ≫ φ.τ₃) ≫ G.δ hT n := by
            rw [(G n).obj.map_comp]
      _ = α.app S.X₂ ≫ (G n).obj.map (φ.τ₂ ≫ T.g) ≫ G.δ hT n := by
            rw [φ.comm₂₃]
      _ = α.app S.X₂ ≫ ((G n).obj.map φ.τ₂ ≫ (G n).obj.map T.g) ≫ G.δ hT n := by
            rw [(G n).obj.map_comp]
      _ = α.app S.X₂ ≫ (G n).obj.map φ.τ₂ ≫ ((G n).obj.map T.g ≫ G.δ hT n) := by
            simp [Category.assoc]
      _ = α.app S.X₂ ≫ (G n).obj.map φ.τ₂ ≫ 0 := by
            rw [G.map_g_comp_δ hT n]
      _ = 0 := by
            simp
  have hk :
      (F n).obj.map S.g ≫ (α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n) =
        0 ≫ (α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n) := by
    calc
      (F n).obj.map S.g ≫ (α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n)
          = (F n).obj.map S.g ≫ α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
              rfl
      _ = 0 := hk0
      _ = 0 ≫ (α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n) := by
            simp
  -- The cokernel universal property now gives the unique comparison map into `T.X₁`.
  exact
    CategoryTheory.Limits.Cofork.IsColimit.existsUnique hcolim
      (α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n)
      hk

/-- Helper for Lemma 12.12.4: successor components agree when two effacements are related by a
row morphism that is the identity on the source object. -/
lemma effacement_succ_component_eq_of_row_hom
    {F G : CohomologicalDeltaFunctor A B}
    {n : ℕ} {X Y₁ Y₂ : A}
    (u₁ : X ⟶ Y₁) [Mono u₁] (hkill₁ : (F (n + 1)).obj.map u₁ = 0)
    (u₂ : X ⟶ Y₂) [Mono u₂] (hkill₂ : (F (n + 1)).obj.map u₂ = 0)
    (v : Y₁ ⟶ Y₂) (hfac : u₁ ≫ v = u₂)
    (α : (F n).obj ⟶ (G n).obj) :
    Classical.choose
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₁ hkill₁ α) =
      Classical.choose
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₂ hkill₂ α) := by
  classical
  let S₁ : ShortComplex A := ShortComplex.cokernelSequence u₁
  let hS₁ : S₁.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u₁) (inferInstance : Mono u₁)
    (inferInstance : Epi (Limits.cokernel.π u₁))
  let S₂ : ShortComplex A := ShortComplex.cokernelSequence u₂
  let hS₂ : S₂.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u₂) (inferInstance : Mono u₂)
    (inferInstance : Epi (Limits.cokernel.π u₂))
  let c : Limits.cokernel u₁ ⟶ Limits.cokernel u₂ :=
    Limits.cokernel.map u₁ u₂ (𝟙 X) v (by simpa using hfac)
  let φ : S₁ ⟶ S₂ := ShortComplex.Hom.mk (𝟙 X) v c
    (by simpa [S₁, S₂] using hfac.symm)
    (by simp [S₁, S₂, c, Limits.cokernel.map])
  -- The chosen component for `u₂` also satisfies the defining equation for `u₁`.
  have hδF' :
      (F n).obj.map c ≫ F.δ hS₂ n =
        F.δ hS₁ n ≫ (F (n + 1)).obj.map (𝟙 X) := by
    simpa [φ, c] using (F.δ_naturality hS₁ hS₂ φ n).w
  have hδG' :
      (G n).obj.map c ≫ G.δ hS₂ n =
        G.δ hS₁ n ≫ (G (n + 1)).obj.map (𝟙 X) := by
    simpa [φ, c] using (G.δ_naturality hS₁ hS₂ φ n).w
  have hψ₂ :
      F.δ hS₂ n ≫
          Classical.choose
            (effacement_succ_component_existsUnique
              (F := F) (G := G) (n := n) u₂ hkill₂ α) =
        α.app (Limits.cokernel u₂) ≫ G.δ hS₂ n := by
    simpa [S₂, hS₂] using
      (Classical.choose_spec
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₂ hkill₂ α)).1
  have hψ₂_as_u₁ :
      F.δ hS₁ n ≫
          Classical.choose
            (effacement_succ_component_existsUnique
              (F := F) (G := G) (n := n) u₂ hkill₂ α) =
        α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n := by
    let ψ₂ : (F (n + 1)).obj.obj X ⟶ (G (n + 1)).obj.obj X :=
      Classical.choose
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₂ hkill₂ α)
    have hψ₂' : F.δ hS₂ n ≫ ψ₂ = α.app (Limits.cokernel u₂) ≫ G.δ hS₂ n := by
      simpa [ψ₂] using hψ₂
    have hmapIdF :
        (F (n + 1)).obj.map (𝟙 X) = 𝟙 ((F (n + 1)).obj.obj X) := by
      simp
    have hmapIdG :
        (G (n + 1)).obj.map (𝟙 X) = 𝟙 ((G (n + 1)).obj.obj X) := by
      simp
    have hnat :
        (F n).obj.map c ≫ α.app (Limits.cokernel u₂) =
          α.app (Limits.cokernel u₁) ≫ (G n).obj.map c := by
      simpa using α.naturality c
    have h₁ :
        F.δ hS₁ n ≫ ψ₂ = ((F n).obj.map c ≫ F.δ hS₂ n) ≫ ψ₂ := by
      have hId :
          F.δ hS₁ n ≫ ψ₂ =
            (F.δ hS₁ n ≫ (F (n + 1)).obj.map (𝟙 X)) ≫ ψ₂ := by
        have hIdMap :
            (F.δ hS₁ n ≫ 𝟙 _) ≫ ψ₂ =
              (F.δ hS₁ n ≫ (F (n + 1)).obj.map (𝟙 X)) ≫ ψ₂ := by
          exact congrArg (fun k ↦ (F.δ hS₁ n ≫ k) ≫ ψ₂) hmapIdF.symm
        calc
          F.δ hS₁ n ≫ ψ₂ = (F.δ hS₁ n ≫ 𝟙 _) ≫ ψ₂ := by
            simp
          _ = (F.δ hS₁ n ≫ (F (n + 1)).obj.map (𝟙 X)) ≫ ψ₂ := hIdMap
      have hComp :
          (F.δ hS₁ n ≫ (F (n + 1)).obj.map (𝟙 X)) ≫ ψ₂ =
            ((F n).obj.map c ≫ F.δ hS₂ n) ≫ ψ₂ := by
        exact congrArg (fun k ↦ k ≫ ψ₂) hδF'.symm
      exact hId.trans hComp
    have h₂ :
        ((F n).obj.map c ≫ F.δ hS₂ n) ≫ ψ₂ =
          ((F n).obj.map c ≫ α.app (Limits.cokernel u₂)) ≫ G.δ hS₂ n := by
      have hComp :
          (F n).obj.map c ≫ (F.δ hS₂ n ≫ ψ₂) =
            (F n).obj.map c ≫ (α.app (Limits.cokernel u₂) ≫ G.δ hS₂ n) := by
        exact congrArg (fun k ↦ (F n).obj.map c ≫ k) hψ₂'
      have hAssocLeft :
          ((F n).obj.map c ≫ F.δ hS₂ n) ≫ ψ₂ =
            (F n).obj.map c ≫ (F.δ hS₂ n ≫ ψ₂) := by
        simp [Category.assoc]
      have hAssocRight :
          (F n).obj.map c ≫ (α.app (Limits.cokernel u₂) ≫ G.δ hS₂ n) =
            ((F n).obj.map c ≫ α.app (Limits.cokernel u₂)) ≫ G.δ hS₂ n := by
        simp [Category.assoc]
      exact hAssocLeft.trans (hComp.trans hAssocRight)
    have h₃ :
        ((F n).obj.map c ≫ α.app (Limits.cokernel u₂)) ≫ G.δ hS₂ n =
          (α.app (Limits.cokernel u₁) ≫ (G n).obj.map c) ≫ G.δ hS₂ n := by
      rw [hnat]
    have h₄ :
        (α.app (Limits.cokernel u₁) ≫ (G n).obj.map c) ≫ G.δ hS₂ n =
          α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n := by
      have hmapIdG₁ :
          (G (n + 1)).obj.map (𝟙 X) = 𝟙 ((G (n + 1)).obj.obj S₁.X₁) := by
        simpa [S₁] using hmapIdG
      have h₄' :
          α.app (Limits.cokernel u₁) ≫ ((G n).obj.map c ≫ G.δ hS₂ n) =
            α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n := by
        -- Rewrite the comparison map using δ-naturality, then collapse the identity map.
        rw [hδG']
        calc
          α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n ≫ (G (n + 1)).obj.map (𝟙 X)
              = α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n ≫ 𝟙 ((G (n + 1)).obj.obj S₁.X₁) := by
                  exact congrArg
                    (fun k ↦ α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n ≫ k) hmapIdG₁
          _ = α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n := by
                simpa [Category.assoc] using
                  (Category.comp_id (α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n))
      simpa [Category.assoc] using h₄'
    -- Naturality across the row morphism transports the `u₂` defining equation back to `u₁`.
    simpa [ψ₂] using show
        F.δ hS₁ n ≫ ψ₂ = α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n from by
      exact h₁.trans (h₂.trans (h₃.trans h₄))
  have huniq₁ :
      ∀ ψ : (F (n + 1)).obj.obj X ⟶ (G (n + 1)).obj.obj X,
        F.δ hS₁ n ≫ ψ = α.app (Limits.cokernel u₁) ≫ G.δ hS₁ n →
          ψ =
            Classical.choose
              (effacement_succ_component_existsUnique
                (F := F) (G := G) (n := n) u₁ hkill₁ α) := by
    intro ψ hψ
    exact
      (Classical.choose_spec
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₁ hkill₁ α)).2 ψ
        (by simpa [S₁, hS₁] using hψ)
  exact (huniq₁ _ hψ₂_as_u₁).symm

/-- Helper for Lemma 12.12.4: the successor component does not depend on which weak effacement of
`X` is chosen in degree `n + 1`. -/
lemma succ_component_eq_of_common_effacement
    {F G : CohomologicalDeltaFunctor A B}
    {n : ℕ} {X Y₁ Y₂ : A}
    (u₁ : X ⟶ Y₁) [Mono u₁] (hkill₁ : (F (n + 1)).obj.map u₁ = 0)
    (u₂ : X ⟶ Y₂) [Mono u₂] (hkill₂ : (F (n + 1)).obj.map u₂ = 0)
    (α : (F n).obj ⟶ (G n).obj) :
    Classical.choose
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₁ hkill₁ α) =
      Classical.choose
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₂ hkill₂ α) := by
  classical
  let w : X ⟶ Limits.pushout u₁ u₂ := u₁ ≫ Limits.pushout.inl u₁ u₂
  have hw₂ : u₂ ≫ Limits.pushout.inr u₁ u₂ = w := by
    simpa [w] using (Limits.pushout.condition (f := u₁) (g := u₂)).symm
  have hwkill :
      (F (n + 1)).obj.map w = 0 := by
    -- The common pushout refinement is still annihilated in degree `n + 1`.
    simp [w, hkill₁]
  have h₁ :
      Classical.choose
          (effacement_succ_component_existsUnique
            (F := F) (G := G) (n := n) u₁ hkill₁ α) =
        Classical.choose
          (effacement_succ_component_existsUnique
            (F := F) (G := G) (n := n) w hwkill α) :=
    effacement_succ_component_eq_of_row_hom
      (F := F) (G := G) (n := n) u₁ hkill₁ w hwkill
      (Limits.pushout.inl u₁ u₂) (by rfl) α
  have h₂ :
      Classical.choose
          (effacement_succ_component_existsUnique
            (F := F) (G := G) (n := n) u₂ hkill₂ α) =
        Classical.choose
          (effacement_succ_component_existsUnique
            (F := F) (G := G) (n := n) w hwkill α) :=
    effacement_succ_component_eq_of_row_hom
      (F := F) (G := G) (n := n) u₂ hkill₂ w hwkill
      (Limits.pushout.inr u₁ u₂) hw₂ α
  exact h₁.trans h₂.symm

/-- Helper for Lemma 12.12.4: choose a target object for a weak effacement of `X` in degree
`n + 1`. -/
noncomputable def chosen_weak_effacement_target
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (X : A) : A :=
  Classical.choose (hF (n + 1) (Nat.succ_pos n) X)

/-- Helper for Lemma 12.12.4: choose a weak-effacement monomorphism of `X` in degree `n + 1`. -/
noncomputable def chosen_weak_effacement_hom
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (X : A) :
    X ⟶ chosen_weak_effacement_target F hF n X :=
  Classical.choose (Classical.choose_spec (hF (n + 1) (Nat.succ_pos n) X))

/-- Helper for Lemma 12.12.4: the chosen weak-effacement morphism is monic. -/
lemma chosen_weak_effacement_mono
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (X : A) :
    Mono (chosen_weak_effacement_hom F hF n X) := by
  -- Read the monomorphism clause from the chosen weak-effacement witness.
  simpa [chosen_weak_effacement_hom] using
    (Classical.choose_spec (Classical.choose_spec (hF (n + 1) (Nat.succ_pos n) X))).1

/-- Helper for Lemma 12.12.4: the chosen weak effacement kills degree `n + 1`. -/
lemma chosen_weak_effacement_kills
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (X : A) :
    (F (n + 1)).obj.map (chosen_weak_effacement_hom F hF n X) = 0 := by
  -- Read the vanishing clause from the same chosen weak-effacement witness.
  simpa [chosen_weak_effacement_hom] using
    (Classical.choose_spec (Classical.choose_spec (hF (n + 1) (Nat.succ_pos n) X))).2

/-- Helper for Lemma 12.12.4: the source-faithful objectwise successor component obtained from the
chosen weak effacement of `X` in degree `n + 1`. -/
noncomputable def chosen_succ_component
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (α : (F n).obj ⟶ (G n).obj) (X : A) :
    (F (n + 1)).obj.obj X ⟶ (G (n + 1)).obj.obj X :=
  let u := chosen_weak_effacement_hom F hF n X
  letI : Mono u := chosen_weak_effacement_mono F hF n X
  Classical.choose
    (effacement_succ_component_existsUnique
      (F := F) (G := G) (n := n) u
      (chosen_weak_effacement_kills F hF n X) α)

/-- Helper for Lemma 12.12.4: the chosen successor component satisfies the defining cokernel
equation for the chosen weak effacement. -/
lemma chosen_succ_component_spec
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (α : (F n).obj ⟶ (G n).obj) (X : A) :
    let u := chosen_weak_effacement_hom F hF n X
    let S : ShortComplex A := ShortComplex.cokernelSequence u
    let hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact u) (chosen_weak_effacement_mono F hF n X)
      (inferInstance : Epi (Limits.cokernel.π u))
    F.δ hS n ≫ chosen_succ_component (F := F) (G := G) hF n α X =
      α.app (Limits.cokernel u) ≫ G.δ hS n := by
  classical
  let u := chosen_weak_effacement_hom F hF n X
  letI : Mono u := chosen_weak_effacement_mono F hF n X
  let S : ShortComplex A := ShortComplex.cokernelSequence u
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
    (inferInstance : Epi (Limits.cokernel.π u))
  -- Unpack the defining equation from the chosen cokernel factorization.
  simpa [chosen_succ_component, u, S, hS] using
    (Classical.choose_spec
      (effacement_succ_component_existsUnique
        (F := F) (G := G) (n := n) u
        (chosen_weak_effacement_kills F hF n X) α)).1

/-- Helper for Lemma 12.12.4: the chosen successor component agrees with the successor map built
from any other weak effacement of the same object. -/
lemma chosen_succ_component_eq_of_effacement
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    {n : ℕ} {X Y : A} (u : X ⟶ Y) [Mono u]
    (hkill : (F (n + 1)).obj.map u = 0)
    (α : (F n).obj ⟶ (G n).obj) :
    chosen_succ_component (F := F) (G := G) hF n α X =
      Classical.choose
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u hkill α) := by
  classical
  let u₀ := chosen_weak_effacement_hom F hF n X
  letI : Mono u₀ := chosen_weak_effacement_mono F hF n X
  -- Compare the chosen weak effacement with the arbitrary one through their common pushout.
  simpa [chosen_succ_component, u₀] using
    (succ_component_eq_of_common_effacement
      (F := F) (G := G) (n := n) u₀
      (chosen_weak_effacement_kills F hF n X) u hkill α)

/-- Helper for Lemma 12.12.4: pushing out the chosen weak effacement of `X` along `f` and then
weakly effacing the pushout object produces a genuine effacement of `Y`, together with a row
morphism from the cokernel sequence of the chosen effacement of `X`. -/
lemma pushout_refined_effacement_row_hom
    {F : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    {n : ℕ} {X Y : A} (f : X ⟶ Y) :
    let u := chosen_weak_effacement_hom F hF n X
    let P := Limits.pushout u f
    let e := chosen_weak_effacement_hom F hF n P
    let m : chosen_weak_effacement_target F hF n X ⟶ chosen_weak_effacement_target F hF n P :=
      Limits.pushout.inl u f ≫ e
    let w : Y ⟶ chosen_weak_effacement_target F hF n P :=
      Limits.pushout.inr u f ≫ e
    ∃ (_hw : Mono w) (_hkill : (F (n + 1)).obj.map w = 0)
      (φ : ShortComplex.cokernelSequence u ⟶ ShortComplex.cokernelSequence w),
        φ.τ₁ = f ∧ φ.τ₂ = m := by
  let u := chosen_weak_effacement_hom F hF n X
  let P := Limits.pushout u f
  let e := chosen_weak_effacement_hom F hF n P
  let m : chosen_weak_effacement_target F hF n X ⟶ chosen_weak_effacement_target F hF n P :=
    Limits.pushout.inl u f ≫ e
  let w : Y ⟶ chosen_weak_effacement_target F hF n P :=
    Limits.pushout.inr u f ≫ e
  have hu : Mono u := chosen_weak_effacement_mono F hF n X
  have he : Mono e := chosen_weak_effacement_mono F hF n P
  have hpush : Mono (Limits.pushout.inr u f) := by
    letI : Mono u := hu
    exact Abelian.mono_pushout_of_mono_f u f
  have hw : Mono w := by
    letI : Mono (Limits.pushout.inr u f) := hpush
    letI : Mono e := he
    -- The refined effacement is the composite of the monic pushout leg and the chosen effacement
    -- of the pushout object.
    simpa [w] using (show Mono (Limits.pushout.inr u f ≫ e) from mono_comp (Limits.pushout.inr u f) e)
  have hkill : (F (n + 1)).obj.map w = 0 := by
    -- The second chosen effacement kills the pushout object, hence also the composite `w`.
    calc
      (F (n + 1)).obj.map w
          = (F (n + 1)).obj.map (Limits.pushout.inr u f) ≫ (F (n + 1)).obj.map e := by
              simp [w]
      _ = 0 := by
            rw [chosen_weak_effacement_kills F hF n P]
            simp
  have hw_square : u ≫ m = f ≫ w := by
    -- This is the pushed-out square followed by the chosen effacement of the pushout object.
    dsimp [m, w]
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ e) (Limits.pushout.condition (f := u) (g := f))
  let c : Limits.cokernel u ⟶ Limits.cokernel w :=
    Limits.cokernel.map u w f m hw_square
  have hφ₁₂ : f ≫ w = u ≫ m := by
    simpa using hw_square.symm
  have hφ₂₃ : m ≫ Limits.cokernel.π w = Limits.cokernel.π u ≫ c := by
    -- The third component is the canonical map induced on cokernels.
    simp [c, Limits.cokernel.map]
  let φ : ShortComplex.cokernelSequence u ⟶ ShortComplex.cokernelSequence w :=
    ShortComplex.Hom.mk f m c hφ₁₂ hφ₂₃
  exact ⟨hw, hkill, φ, rfl, rfl⟩

/-- Helper for Lemma 12.12.4: the chosen successor component is natural in the source object. -/
lemma chosen_succ_component_naturality_app
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (α : (F n).obj ⟶ (G n).obj) {X Y : A} (f : X ⟶ Y) :
    (F (n + 1)).obj.map f ≫ chosen_succ_component (F := F) (G := G) hF n α Y =
      chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f := by
  classical
  let u := chosen_weak_effacement_hom F hF n X
  letI : Mono u := chosen_weak_effacement_mono F hF n X
  let P := Limits.pushout u f
  let e := chosen_weak_effacement_hom F hF n P
  let m : chosen_weak_effacement_target F hF n X ⟶ chosen_weak_effacement_target F hF n P :=
    Limits.pushout.inl u f ≫ e
  let w : Y ⟶ chosen_weak_effacement_target F hF n P :=
    Limits.pushout.inr u f ≫ e
  obtain ⟨hw, hkillw, φ, hφ₁, _⟩ :=
    pushout_refined_effacement_row_hom (F := F) hF (n := n) f
  letI : Mono w := hw
  let S : ShortComplex A := ShortComplex.cokernelSequence u
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
    (inferInstance : Epi (Limits.cokernel.π u))
  let T : ShortComplex A := ShortComplex.cokernelSequence w
  let hT : T.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact w) (inferInstance : Mono w)
    (inferInstance : Epi (Limits.cokernel.π w))
  let ψw : (F (n + 1)).obj.obj Y ⟶ (G (n + 1)).obj.obj Y :=
    Classical.choose
      (effacement_succ_component_existsUnique
        (F := F) (G := G) (n := n) w hkillw α)
  have hψw :
      F.δ hT n ≫ ψw = α.app (Limits.cokernel w) ≫ G.δ hT n := by
    -- This is the defining equation of the successor component attached to the refined effacement.
    simpa [T, hT, ψw] using
      (Classical.choose_spec
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) w hkillw α)).1
  have hδF :
      F.δ hS n ≫ (F (n + 1)).obj.map f =
        (F n).obj.map φ.τ₃ ≫ F.δ hT n := by
    -- Naturality of `δ` along the refined row rewrites the left successor square into the common
    -- target row.
    simpa [S, T, hS, hT, hφ₁, Category.assoc] using
      (F.δ_naturality hS hT φ n).w.symm
  have hδG :
      G.δ hS n ≫ (G (n + 1)).obj.map f =
        (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
    -- The same transport identity holds on the target `δ`-functor.
    simpa [S, T, hS, hT, hφ₁, Category.assoc] using
      (G.δ_naturality hS hT φ n).w.symm
  have hnatφ :
      (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel w) =
        α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ := by
    -- Naturality of `α` moves the comparison across the third component of the refined row.
    exact α.naturality φ.τ₃
  have htarget :
      F.δ hS n ≫ ((F (n + 1)).obj.map f ≫ ψw) =
        α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
    -- The refined-effacement component on `Y` satisfies the over-row universal property for `u`.
    have htarget₁ :
        F.δ hS n ≫ ((F (n + 1)).obj.map f ≫ ψw) =
          ((F n).obj.map φ.τ₃ ≫ F.δ hT n) ≫ ψw := by
      calc
        F.δ hS n ≫ ((F (n + 1)).obj.map f ≫ ψw)
            = (F.δ hS n ≫ (F (n + 1)).obj.map f) ≫ ψw := by
                simp [Category.assoc]
        _ = ((F n).obj.map φ.τ₃ ≫ F.δ hT n) ≫ ψw := by
              exact congrArg (fun k ↦ k ≫ ψw) hδF
    have htarget₂ :
        ((F n).obj.map φ.τ₃ ≫ F.δ hT n) ≫ ψw =
          (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel w) ≫ G.δ hT n := by
      calc
        ((F n).obj.map φ.τ₃ ≫ F.δ hT n) ≫ ψw
            = (F n).obj.map φ.τ₃ ≫ (F.δ hT n ≫ ψw) := by
                simp [Category.assoc]
        _ = (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel w) ≫ G.δ hT n := by
              simpa [Category.assoc] using congrArg (fun k ↦ (F n).obj.map φ.τ₃ ≫ k) hψw
    have htarget₃ :
        (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel w) ≫ G.δ hT n =
          α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
      calc
        (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel w) ≫ G.δ hT n
            = ((F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel w)) ≫ G.δ hT n := by
                simp [Category.assoc]
        _ = (α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃) ≫ G.δ hT n := by
              exact congrArg (fun k ↦ k ≫ G.δ hT n) hnatφ
        _ = α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
              simp [Category.assoc]
    exact htarget₁.trans (htarget₂.trans htarget₃)
  have hsource :
      F.δ hS n ≫
          (chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f) =
        α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
    -- The chosen component on `X` gives the same factorization after transporting by `δ`-naturality.
    have hsource₁ :
        F.δ hS n ≫
            (chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f) =
          (α.app (Limits.cokernel u) ≫ G.δ hS n) ≫ (G (n + 1)).obj.map f := by
      calc
        F.δ hS n ≫
            (chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f)
            = (F.δ hS n ≫ chosen_succ_component (F := F) (G := G) hF n α X) ≫
                (G (n + 1)).obj.map f := by
                  simp [Category.assoc]
        _ = (α.app (Limits.cokernel u) ≫ G.δ hS n) ≫ (G (n + 1)).obj.map f := by
              exact
                congrArg
                  (fun k ↦ k ≫ (G (n + 1)).obj.map f)
                  (chosen_succ_component_spec (F := F) (G := G) hF n α X)
    have hsource₂ :
        (α.app (Limits.cokernel u) ≫ G.δ hS n) ≫ (G (n + 1)).obj.map f =
          α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
      calc
        (α.app (Limits.cokernel u) ≫ G.δ hS n) ≫ (G (n + 1)).obj.map f
            = α.app (Limits.cokernel u) ≫ (G.δ hS n ≫ (G (n + 1)).obj.map f) := by
                simp [Category.assoc]
        _ = α.app (Limits.cokernel u) ≫ ((G n).obj.map φ.τ₃ ≫ G.δ hT n) := by
              exact congrArg (fun k ↦ α.app (Limits.cokernel u) ≫ k) hδG
        _ = α.app (Limits.cokernel u) ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
              simp
    exact hsource₁.trans hsource₂
  have hEqTarget :
      (F (n + 1)).obj.map f ≫ ψw =
        chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f := by
    -- The over-row cokernel universal property forces both candidates to coincide.
    have hEq₁ :
        (F (n + 1)).obj.map f ≫ ψw =
          Classical.choose
            (effacement_succ_component_existsUnique_over_row_hom
              (F := F) (G := G) (n := n) u
              (chosen_weak_effacement_kills F hF n X) hT φ α) := by
      exact
        (Classical.choose_spec
          (effacement_succ_component_existsUnique_over_row_hom
            (F := F) (G := G) (n := n) u
            (chosen_weak_effacement_kills F hF n X) hT φ α)).2
          ((F (n + 1)).obj.map f ≫ ψw)
          (by simpa [S, hS, T, hT, Category.assoc] using htarget)
    have hEq₂ :
        chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f =
          Classical.choose
            (effacement_succ_component_existsUnique_over_row_hom
              (F := F) (G := G) (n := n) u
              (chosen_weak_effacement_kills F hF n X) hT φ α) := by
      exact
        (Classical.choose_spec
          (effacement_succ_component_existsUnique_over_row_hom
            (F := F) (G := G) (n := n) u
            (chosen_weak_effacement_kills F hF n X) hT φ α)).2
          (chosen_succ_component (F := F) (G := G) hF n α X ≫ (G (n + 1)).obj.map f)
          (by simpa [S, hS, T, hT, Category.assoc] using hsource)
    exact hEq₁.trans hEq₂.symm
  -- Replace the refined-effacement successor map on `Y` by the chosen one.
  rw [chosen_succ_component_eq_of_effacement (F := F) (G := G) hF (n := n) w hkillw α]
  exact hEqTarget

/-- Helper for Lemma 12.12.4: the objectwise successor components assemble into a natural
transformation. -/
noncomputable def chosen_succ_component_natural
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (α : (F n).obj ⟶ (G n).obj) :
    (F (n + 1)).obj ⟶ (G (n + 1)).obj where
  app X := chosen_succ_component (F := F) (G := G) hF n α X
  naturality := fun {_ _} f ↦ chosen_succ_component_naturality_app (F := F) (G := G) hF n α f

/-- Helper for Lemma 12.12.4: if `u₂` weakly effaces the middle term of a short exact sequence,
then `u₁ := S.f ≫ u₂` weakly effaces the first term and the sequence maps to the cokernel row of
`u₁`. -/
lemma short_exact_to_composed_effacement_row_hom
    {F : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    {n : ℕ} {S : ShortComplex A} (hS : S.ShortExact) :
    let u₂ := chosen_weak_effacement_hom F hF n S.X₂
    let u₁ : S.X₁ ⟶ chosen_weak_effacement_target F hF n S.X₂ := S.f ≫ u₂
    ∃ (_hu₁ : Mono u₁) (_hkill : (F (n + 1)).obj.map u₁ = 0)
      (φ : S ⟶ ShortComplex.cokernelSequence u₁),
        φ.τ₁ = 𝟙 S.X₁ ∧ φ.τ₂ = u₂ := by
  let u₂ := chosen_weak_effacement_hom F hF n S.X₂
  let u₁ : S.X₁ ⟶ chosen_weak_effacement_target F hF n S.X₂ := S.f ≫ u₂
  have hu₂ : Mono u₂ := chosen_weak_effacement_mono F hF n S.X₂
  have hu₁ : Mono u₁ := by
    letI : Mono S.f := hS.mono_f
    letI : Mono u₂ := hu₂
    -- The composed effacement stays monic because both the short-exact inclusion and `u₂` are.
    simpa [u₁] using (show Mono (S.f ≫ u₂) from mono_comp S.f u₂)
  have hkill : (F (n + 1)).obj.map u₁ = 0 := by
    -- The higher-degree vanishing propagates along the composite `S.f ≫ u₂`.
    calc
      (F (n + 1)).obj.map u₁
          = (F (n + 1)).obj.map S.f ≫ (F (n + 1)).obj.map u₂ := by
              simp [u₁]
      _ = 0 := by
            rw [chosen_weak_effacement_kills F hF n S.X₂]
            simp
  obtain ⟨hcolim⟩ :=
    (S.exact_and_epi_g_iff_g_is_cokernel).1 ⟨hS.exact, hS.epi_g⟩
  have hdesc_zero :
      S.f ≫ (u₂ ≫ Limits.cokernel.π u₁) = 0 := by
    -- The target map annihilates `S.f` because it factors through the cokernel of `u₁`.
    calc
      S.f ≫ (u₂ ≫ Limits.cokernel.π u₁) = (S.f ≫ u₂) ≫ Limits.cokernel.π u₁ := by
        simp [Category.assoc]
      _ = 0 := by
        exact Limits.cokernel.condition u₁
  let τ₃ : S.X₃ ⟶ Limits.cokernel u₁ :=
    hcolim.desc (Limits.CokernelCofork.ofπ (u₂ ≫ Limits.cokernel.π u₁) hdesc_zero)
  have hτ₃ :
      S.g ≫ τ₃ = u₂ ≫ Limits.cokernel.π u₁ := by
    -- This is the defining computation rule of the descended cokernel map.
    simpa [τ₃] using
      hcolim.fac (Limits.CokernelCofork.ofπ (u₂ ≫ Limits.cokernel.π u₁) hdesc_zero)
        WalkingParallelPair.one
  have hφ₁₂ : 𝟙 S.X₁ ≫ u₁ = S.f ≫ u₂ := by
    simp [u₁]
  have hφ₂₃ : u₂ ≫ Limits.cokernel.π u₁ = S.g ≫ τ₃ := by
    simpa using hτ₃.symm
  let φ : S ⟶ ShortComplex.cokernelSequence u₁ :=
    ShortComplex.Hom.mk (𝟙 S.X₁) u₂ τ₃ hφ₁₂ hφ₂₃
  exact ⟨hu₁, hkill, φ, rfl, rfl⟩

/-- Helper for Lemma 12.12.4: the chosen successor transformation is compatible with the
connecting morphisms in degree `n`. -/
lemma chosen_succ_component_comm
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (α : (F n).obj ⟶ (G n).obj)
    {S : ShortComplex A} (hS : S.ShortExact) :
    CommSq
      (α.app S.X₃)
      (F.δ hS n)
      (G.δ hS n)
      ((chosen_succ_component_natural (F := F) (G := G) hF n α).app S.X₁) := by
  classical
  let u₂ := chosen_weak_effacement_hom F hF n S.X₂
  let u₁ : S.X₁ ⟶ chosen_weak_effacement_target F hF n S.X₂ := S.f ≫ u₂
  obtain ⟨hu₁, hkill, φ, hφ₁, _⟩ :=
    short_exact_to_composed_effacement_row_hom (F := F) hF (n := n) hS
  letI : Mono u₁ := hu₁
  let T : ShortComplex A := ShortComplex.cokernelSequence u₁
  let hT : T.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact u₁) (inferInstance : Mono u₁)
    (inferInstance : Epi (Limits.cokernel.π u₁))
  let ψ : (F (n + 1)).obj.obj S.X₁ ⟶ (G (n + 1)).obj.obj S.X₁ :=
    Classical.choose
      (effacement_succ_component_existsUnique
        (F := F) (G := G) (n := n) u₁ hkill α)
  have hψ :
      F.δ hT n ≫ ψ = α.app (Limits.cokernel u₁) ≫ G.δ hT n := by
    -- This is the defining equation for the successor map built from the composed effacement.
    simpa [T, hT, ψ] using
      (Classical.choose_spec
        (effacement_succ_component_existsUnique
          (F := F) (G := G) (n := n) u₁ hkill α)).1
  have hδF :
      (F n).obj.map φ.τ₃ ≫ F.δ hT n = F.δ hS n := by
    -- The row comparison has identity first component, so `δ`-naturality collapses to a direct
    -- comparison between `S` and the composed-effacement row.
    simpa [T, hT, hφ₁, Category.assoc] using (F.δ_naturality hS hT φ n).w
  have hδG :
      (G n).obj.map φ.τ₃ ≫ G.δ hT n = G.δ hS n := by
    -- The same identity-on-the-left simplification applies to the target `δ`-functor.
    simpa [T, hT, hφ₁, Category.assoc] using (G.δ_naturality hS hT φ n).w
  have hnatφ :
      (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel u₁) =
        α.app S.X₃ ≫ (G n).obj.map φ.τ₃ := by
    -- Naturality of `α` across the comparison map from `S.X₃` to `cokernel u₁`.
    exact α.naturality φ.τ₃
  refine CommSq.mk ?_
  change α.app S.X₃ ≫ G.δ hS n =
    F.δ hS n ≫ chosen_succ_component (F := F) (G := G) hF n α S.X₁
  rw [chosen_succ_component_eq_of_effacement (F := F) (G := G) hF (n := n) u₁ hkill α]
  -- Transport the defining equation for the effacement row back along the row morphism `φ`.
  symm
  have hcomm₁ :
      F.δ hS n ≫ ψ =
        (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel u₁) ≫ G.δ hT n := by
    calc
      F.δ hS n ≫ ψ = ((F n).obj.map φ.τ₃ ≫ F.δ hT n) ≫ ψ := by
        exact congrArg (fun k ↦ k ≫ ψ) hδF.symm
      _ = (F n).obj.map φ.τ₃ ≫ (F.δ hT n ≫ ψ) := by
            simp [Category.assoc]
      _ = (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel u₁) ≫ G.δ hT n := by
            simpa [Category.assoc] using congrArg (fun k ↦ (F n).obj.map φ.τ₃ ≫ k) hψ
  have hcomm₂ :
      (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel u₁) ≫ G.δ hT n =
        α.app S.X₃ ≫ G.δ hS n := by
    calc
      (F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel u₁) ≫ G.δ hT n
          = ((F n).obj.map φ.τ₃ ≫ α.app (Limits.cokernel u₁)) ≫ G.δ hT n := by
              simp [Category.assoc]
      _ = (α.app S.X₃ ≫ (G n).obj.map φ.τ₃) ≫ G.δ hT n := by
            exact congrArg (fun k ↦ k ≫ G.δ hT n) hnatφ
      _ = α.app S.X₃ ≫ (G n).obj.map φ.τ₃ ≫ G.δ hT n := by
            simp [Category.assoc]
      _ = α.app S.X₃ ≫ G.δ hS n := by
            simpa [Category.assoc] using congrArg (fun k ↦ α.app S.X₃ ≫ k) hδG
  exact hcomm₁.trans hcomm₂

/-- Helper for Lemma 12.12.4: the degree-`n` component of a morphism of `δ`-functors extends
uniquely to degree `n + 1`. -/
lemma succ_nat_trans_exists_unique
    {F G : CohomologicalDeltaFunctor A B}
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0)
    (n : ℕ) (α : (F n).obj ⟶ (G n).obj) :
    ∃! β : (F (n + 1)).obj ⟶ (G (n + 1)).obj,
      ∀ {S : ShortComplex A} (hS : S.ShortExact),
        CommSq (α.app S.X₃) (F.δ hS n) (G.δ hS n) (β.app S.X₁) := by
  classical
  refine ⟨chosen_succ_component_natural (F := F) (G := G) hF n α, ?_, ?_⟩
  · intro S hS
    -- Existence comes from the compatibility lemma proved for the chosen successor family.
    simpa using chosen_succ_component_comm (F := F) (G := G) hF n α hS
  · intro β hβ
    ext X
    let u := chosen_weak_effacement_hom F hF n X
    letI : Mono u := chosen_weak_effacement_mono F hF n X
    let S : ShortComplex A := ShortComplex.cokernelSequence u
    let hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact u) (inferInstance : Mono u)
      (inferInstance : Epi (Limits.cokernel.π u))
    have hβX :
        F.δ hS n ≫ β.app X = α.app (Limits.cokernel u) ≫ G.δ hS n := by
      -- Apply the compatibility hypothesis to the chosen effacement row of `X`.
      simpa [S, hS] using (hβ (S := S) hS).w.symm
    have huniqX :
        β.app X =
          Classical.choose
            (effacement_succ_component_existsUnique
              (F := F) (G := G) (n := n) u
              (chosen_weak_effacement_kills F hF n X) α) := by
      -- The effacement uniqueness lemma pins down every compatible degree-`n + 1` component.
      exact
        (Classical.choose_spec
          (effacement_succ_component_existsUnique
            (F := F) (G := G) (n := n) u
            (chosen_weak_effacement_kills F hF n X) α)).2
          (β.app X)
          (by simpa [S, hS] using hβX)
    calc
      β.app X
          = Classical.choose
              (effacement_succ_component_existsUnique
                (F := F) (G := G) (n := n) u
                (chosen_weak_effacement_kills F hF n X) α) := huniqX
      _ = chosen_succ_component (F := F) (G := G) hF n α X := by
            symm
            exact
              chosen_succ_component_eq_of_effacement
                (F := F) (G := G) hF
                (n := n) u (chosen_weak_effacement_kills F hF n X) α

/-- Lemma 12.12.4: if every positive degree of a cohomological `δ`-functor is weakly
effaceable, then the `δ`-functor is universal. -/
-- Proof sketch: extend a degree-zero morphism of `δ`-functors inductively on the degree. For the
-- inductive step, choose a monomorphism `u : X ⟶ Y` killing `F^(n+1)(u)`, use the long exact
-- sequence for `0 ⟶ X ⟶ Y ⟶ Y/X ⟶ 0` to identify `F^(n+1)(X)` with a cokernel built from degree
-- `n`, and define the next component by the universal property of that cokernel; uniqueness comes
-- from the same construction.
theorem isUniversal_of_higherDegreesWeaklyEffaceable
    (F : CohomologicalDeltaFunctor A B)
    (hF : ∀ n : ℕ, n > 0 → ∀ X : A, ∃ (Y : A) (u : X ⟶ Y), Mono u ∧ (F n).obj.map u = 0) :
    F.IsUniversal := by
  classical
  refine ⟨?_⟩
  intro G t
  let apps : ∀ n : ℕ, (F n).obj ⟶ (G n).obj :=
    Nat.rec t
      (fun n α ↦
        Classical.choose
          (succ_nat_trans_exists_unique (F := F) (G := G) hF n α))
  have happs_comm :
      ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
        CommSq ((apps n).app S.X₃) (F.δ hS n) (G.δ hS n) ((apps (n + 1)).app S.X₁) := by
    intro S hS n
    -- Each successor stage is chosen from the unique compatible extension in degree `n + 1`.
    exact
      (Classical.choose_spec
        (succ_nat_trans_exists_unique (F := F) (G := G) hF n (apps n))).1 hS
  let τ : F ⟶ G :=
    { app := apps
      comm := fun {_} hS n ↦ happs_comm hS n }
  have hτ₀ : τ.app 0 = t := by
    -- The recursive family starts with the prescribed degree-zero map.
    rfl
  refine ⟨τ, hτ₀, ?_⟩
  intro σ hσ₀
  have hσ : ∀ n : ℕ, σ.app n = apps n := by
    intro n
    induction n with
    | zero =>
        -- The base degree is fixed by the prescribed initial comparison.
        simpa [apps] using hσ₀
    | succ n ihn =>
        have hcompat :
            ∀ {S : ShortComplex A} (hS : S.ShortExact),
              CommSq ((apps n).app S.X₃) (F.δ hS n) (G.δ hS n) ((σ.app (n + 1)).app S.X₁) := by
          intro S hS
          -- The induction hypothesis identifies degree `n`, so `σ.app (n + 1)` is another
          -- compatible successor for the same predecessor map.
          simpa [ihn] using σ.comm hS n
        -- Uniqueness of the one-step extension forces `σ.app (n + 1)` to be the chosen one.
        exact
          (Classical.choose_spec
            (succ_nat_trans_exists_unique (F := F) (G := G) hF n (apps n))).2
            (σ.app (n + 1)) hcompat
  apply CohomologicalDeltaFunctor.Hom.ext
  funext n
  exact hσ n

end CohomologicalDeltaFunctor

end CategoryTheory
