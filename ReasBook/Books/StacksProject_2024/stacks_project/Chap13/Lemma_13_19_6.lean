import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import StacksProject_2024.stacks_project.Chap13.Definition_13_19_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory HomotopyCategory
open HomologicalComplex
open scoped ZeroObject

universe v u

namespace CochainComplex

open HomComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

local notation "KQ" => quotient 𝒜 (up ℤ)

/- Domain-style sampling:
- primary domain: homotopy lifting along quasi-isomorphisms from bounded-above projective
  cochain complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.Lifting.hasLift`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for the bounded-above
  projective source complex; the present lifting statements are bridge/view results derived from
  that owner, the homotopy-category bijectivity theorem, and for the strict statement the
  canonical cochain lifting engine;
- primitive data: a projective-minus source complex `P`, a quasi-isomorphism `α : L ⟶ K`, and a
  map `γ : P ⟶ K`;
- derived API: existence of a lift `β : P ⟶ L` up to homotopy, and the stricter exact lift under
  termwise epimorphy.

Source/core/bridge triage:
- `source-facing`: the two lifting statements below;
- `core/canonical`: `ProjectiveMinus 𝒜` and its induced `IsKProjective` instance;
- `bridge/view`: the factorization results obtained from the owner-level K-projective comparison
  API.
-/

-- Route correction: avoid importing `Remark_13_19_5` directly here. In the current Lake state
-- that module fails before its own proof on a stale `Lemma_13_15_4.olean`, so we reproduce only
-- its source-faithful bridge argument locally from the already-frozen dependency
-- `Lemma_13_19_8`.
/-- Helper for Lemma 13.19.6: postcomposition with a quasi-isomorphism is bijective on
homotopy-category morphisms out of a bounded-above projective complex. -/
theorem postcomp_bijective_of_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α] :
    Function.Bijective
      (fun g : (KQ).obj P ⟶ (KQ).obj L ↦
        g ≫ (KQ).map α) := by
  let Q := KQ
  -- Transport the quasi-isomorphism to an isomorphism in the derived category.
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  -- Postcomposition with an isomorphism is bijective in the derived category.
  have hpostD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L) ↦ g ≫ Qh.map (Q.map α)) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_mono (Qh.map (Q.map α))).1 h
    · intro g
      refine ⟨g ≫ inv (Qh.map (Q.map α)), ?_⟩
      simp [Category.assoc]
  -- Compare homotopy and derived morphisms using K-projectivity of the source owner.
  have hL := homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L
  have hK := homotopyCategory_to_derived_bijective_of_boundedAbove_projective P K
  have hcomp :
      ((Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) ∘
        fun g : Q.obj P ⟶ Q.obj L ↦ g ≫ Q.map α) =
      (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L) ↦ g ≫ Qh.map (Q.map α)) ∘
        (Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) := by
    funext g
    simp [Functor.map_comp]
  have hbijcomp :
      Function.Bijective
        (((Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) ∘
          fun g : Q.obj P ⟶ Q.obj L ↦ g ≫ Q.map α)) := by
    rw [hcomp]
    exact hpostD.comp hL
  exact (Function.Bijective.of_comp_iff' hK _).mp hbijcomp

-- Proof sketch: the owner `MinusWithTermsIn (isProjective 𝒜)` already packages the
-- bounded-above/projective hypothesis and carries the canonical `IsKProjective` instance. Remark
-- `13.19.5` then identifies postcomposition with the quasi-isomorphism `α` as a bijection on
-- morphisms out of `P` in the homotopy category. Apply surjectivity to the class of `γ`, and
-- unpack equality in the homotopy category as a homotopy between `β ≫ α` and `γ`.
/-- Lemma 13.19.6: if `α : L^• ⟶ K^•` is a quasi-isomorphism and `P^•` is a bounded-above
cochain complex of projective objects, then every morphism `γ : P^• ⟶ K^•` factors through `α`
up to homotopy. -/
theorem exists_homotopy_factor_through_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K) :
    ∃ β : (P : CochainComplex 𝒜 ℤ) ⟶ L, Nonempty (Homotopy (β ≫ α) γ) := by
  let Q := KQ
  obtain ⟨β, hβ⟩ :=
    (postcomp_bijective_of_quasiIso_from_boundedAbove_projective P α).surjective
      (Q.map γ)
  obtain ⟨β, rfl⟩ := Q.map_surjective β
  exact ⟨β, ⟨homotopyOfEq _ _ (by simpa [Q, Functor.map_comp] using hβ)⟩⟩

theorem kernel_acyclic_of_termwiseEpi_quasiIso
    (α : L ⟶ K) [QuasiIso α] (hα : ∀ n : ℤ, Epi (α.f n)) :
    (kernel α).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S := ShortComplex.kernelSequence α
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance
      (HomologicalComplex.epi_of_epi_f α hα)
    exact ShortComplex.kernelSequence_exact α
  refine ((hS.homology_exact₁ (n - 1) n (by simp)).isZero_X₂ ?_ ?_)
  · rw [← (hS.homology_exact₃ (n - 1) n (by simp)).epi_f_iff]
    have : Epi (homologyMap α (n - 1)) := by infer_instance
    simpa [S] using this
  · rw [← (hS.homology_exact₂ n).mono_g_iff]
    have : Mono (homologyMap α n) := by infer_instance
    simpa [S] using this

-- Proof sketch: start with degreewise projective lifts of the components `γ.f n` across the
-- epimorphisms `α.f n`, producing a commutative square against the zero map. The failure of these
-- degreewise lifts to define a chain map is measured by the canonical obstruction cocycle for
-- `CochainComplex.Lifting`; since the kernel complex of a termwise-epimorphic quasi-isomorphism is
-- acyclic, the bounded-above projective owner `P` kills that obstruction, and
-- `CochainComplex.Lifting.hasLift` strictifies the homotopy lift to an exact factorization.
/-- If the quasi-isomorphism `α` is termwise epimorphic, the factorization of a map from a
bounded-above projective complex can be chosen to commute strictly. -/
theorem exists_strict_factor_through_termwiseEpi_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (hα : ∀ n : ℤ, Epi (α.f n)) :
    ∃ β : (P : CochainComplex 𝒜 ℤ) ⟶ L, β ≫ α = γ := by
  let P' : CochainComplex 𝒜 ℤ := P
  let Z := (0 : CochainComplex 𝒜 ℤ)
  let sq : CommSq (0 : Z ⟶ L) (0 : Z ⟶ P') α γ := CommSq.mk (by simp)
  let hsq : ∀ n : ℤ, (sq.map (eval 𝒜 (up ℤ) n)).LiftStruct := by
    intro n
    let _ : Projective (P'.X n) := by
      simpa [P'] using P.term_mem n
    refine
      { l := show P'.X n ⟶ L.X n from Projective.factorThru (γ.f n) (α.f n)
        fac_left := by simp
        fac_right := by exact Projective.factorThru_comp (γ.f n) (α.f n) }
  have hQ : IsColimit (CokernelCofork.ofπ (𝟙 P') (show (0 : Z ⟶ P') ≫ 𝟙 P' = 0 by simp)) :=
    CokernelCofork.IsColimit.ofId (0 : Z ⟶ P') rfl
  have hK :
      IsLimit
        (KernelFork.ofι (kernel.ι α) (kernel.condition α)) :=
    KernelFork.IsLimit.ofι' (kernel.ι α) (kernel.condition α) (fun k hk ↦ kernel.lift' α k hk)
  let obstruction : Cocycle P' (kernel α) 1 :=
    CochainComplex.Lifting.cocycle₁ sq hsq hQ hK
  have hac : (kernel α).Acyclic :=
    kernel_acyclic_of_termwiseEpi_quasiIso α hα
  have hacShift : ((kernel α)⟦(1 : ℤ)⟧).Acyclic := by
    rw [HomologicalComplex.acyclic_iff]
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hk : IsZero ((kernel α).homology (1 + n)) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hac (1 + n)
    exact IsZero.of_iso hk
      (((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) (0 : ℤ)).shiftIso 1 n _ rfl).app
        (kernel α))
  let hnull :
      Homotopy
        (Cocycle.equivHomShift.symm obstruction)
        0 :=
    IsKProjective.homotopyZero (Cocycle.equivHomShift.symm obstruction) hacShift
  obtain ⟨cochainShift, hcochainShift⟩ :=
    Cochain.equivHomotopy (Cocycle.equivHomShift.symm obstruction) 0 hnull
  have hcochainShift :
      Cochain.ofHom (Cocycle.equivHomShift.symm obstruction) =
        δ (-1) 0 cochainShift := by
    simpa using hcochainShift
  have hobstruction :
      (Cochain.ofHom (Cocycle.equivHomShift.symm obstruction)).rightUnshift 1 (by simp) =
        obstruction.1 := by
    change
      (Cocycle.equivHomShift (Cocycle.equivHomShift.symm obstruction)).1 = obstruction.1
    exact
      congrArg
        (fun z : Cocycle P' (kernel α) 1 ↦ z.1)
        (Cocycle.equivHomShift.apply_symm_apply obstruction)
  let cochain : Cochain P' (kernel α) 0 :=
    (-cochainShift).rightUnshift 0 (by simp)
  have hδ : δ 0 1 cochain = obstruction.1 := by
    dsimp [cochain]
    rw [Cochain.δ_rightUnshift (-cochainShift) 0 (by simp) 1 0 (by simp)]
    simp only [Int.negOnePow_one, Int.reduceNeg, δ_neg, Cochain.rightUnshift_neg, smul_neg,
      Units.neg_smul, one_smul, neg_neg]
    rw [← hcochainShift]
    exact hobstruction
  letI : sq.HasLift := CochainComplex.Lifting.hasLift sq hsq hQ hK cochain hδ
  exact ⟨sq.lift, sq.fac_right⟩

end CochainComplex
