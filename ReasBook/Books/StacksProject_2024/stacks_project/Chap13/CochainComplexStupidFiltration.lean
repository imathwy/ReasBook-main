import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Tactic
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_11

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex

noncomputable section

universe v u

namespace CategoryTheory
namespace CochainComplex

section Filtrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

private def stupidFiltrationSubobject (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Subobject (K.X n) :=
  if p ≤ n then ⊤ else ⊥

private theorem stupidFiltration_decreasing (K : CochainComplex 𝒜 ℤ) {p q n : ℤ}
    (hpq : p ≤ q) :
    stupidFiltrationSubobject K q n ≤ stupidFiltrationSubobject K p n := by
  by_cases hqn : q ≤ n
  · have hpn : p ≤ n := le_trans hpq hqn
    simp [stupidFiltrationSubobject, hqn, hpn]
  · simp [stupidFiltrationSubobject, hqn]

private theorem stupidFiltration_d_preserves (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    stupidFiltrationSubobject K p i ≤
      (Subobject.pullback (K.d i j)).obj (stupidFiltrationSubobject K p j) := by
  by_cases hpi : p ≤ i
  · by_cases hij : j = i + 1
    · have hpj : p ≤ j := by omega
      simp [stupidFiltrationSubobject, hpi, hpj, Subobject.pullback_top]
    · apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      have hd : K.d i j = 0 := by
        have hshape : ¬ (ComplexShape.up ℤ).Rel i j := by
          simpa [ComplexShape.up, eq_comm] using hij
        exact K.shape i j hshape
      simpa [stupidFiltrationSubobject, hpi, hd] using
        (Subobject.factors_zero :
          (stupidFiltrationSubobject K p j).Factors
            (0 : (stupidFiltrationSubobject K p i : 𝒜) ⟶ K.X j))
  · simp [stupidFiltrationSubobject, hpi]

/-- The filtered complex with stages `F^p(K^•) = σ≥p(K^•)`. -/
def stupidFiltration (K : CochainComplex 𝒜 ℤ) : FilteredComplex 𝒜 where
  X n :=
    { obj := K.X n
      filtration :=
        { toFun := fun p ↦ stupidFiltrationSubobject K p n
          monotone' := fun _ _ hpq ↦ stupidFiltration_decreasing K hpq } }
  d i j :=
    { hom := K.d i j
      preserves := fun p ↦
        (pullback_factors_iff (K.d i j) (stupidFiltrationSubobject K p j)
          (stupidFiltrationSubobject K p i).arrow).1 <|
          (Subobject.factors_iff _ _).2
            ⟨Subobject.ofLE _ _ (stupidFiltration_d_preserves K p i j),
              Subobject.ofLE_arrow (stupidFiltration_d_preserves K p i j)⟩ }
  shape := fun i j hij ↦ FilteredObject.forget.map_injective (K.shape i j hij)
  d_comp_d' := fun i j k hij hjk ↦
    FilteredObject.forget.map_injective (K.d_comp_d' i j k hij hjk)

/-- The stupid filtration has finite filtrations in every degree. -/
theorem stupidFiltration_hasFiniteFiltrations (K : CochainComplex 𝒜 ℤ) :
    (stupidFiltration K).HasFiniteFiltrations := by
  intro n
  refine ⟨n, n + 1, ?_, ?_⟩
  · change stupidFiltrationSubobject K n n = ⊤
    simp [stupidFiltrationSubobject]
  · change stupidFiltrationSubobject K (n + 1) n = ⊥
    simp [stupidFiltrationSubobject]

private theorem stupid_filtration_stage_term_iso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    ∃ e : ((K.stupidFiltration).stage p).X n ≅ K.X n,
      e.hom = ((K.stupidFiltration).stageInclusion p).f n := by
  change ∃ e : ((stupidFiltrationSubobject K p n : 𝒜) ≅ K.X n),
      e.hom = (stupidFiltrationSubobject K p n).arrow
  rw [stupidFiltrationSubobject, if_pos hpn]
  rw [Subobject.top_eq_id]
  refine ⟨Subobject.underlyingIso (𝟙 (K.X n)), ?_⟩
  simpa using (Subobject.underlyingIso_hom_comp_eq_mk (𝟙 (K.X n)))

private noncomputable def stupid_filtration_stage_active_iso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    ((K.stupidFiltration).stage p).X n ≅ K.X n :=
  Classical.choose (stupid_filtration_stage_term_iso K p n hpn)

private theorem stupid_filtration_stage_active_iso_hom
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    (stupid_filtration_stage_active_iso K p n hpn).hom =
      ((K.stupidFiltration).stageInclusion p).f n :=
  Classical.choose_spec (stupid_filtration_stage_term_iso K p n hpn)

private theorem stupid_filtration_stage_active_iso_inv_stageInclusion
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    (stupid_filtration_stage_active_iso K p n hpn).inv ≫
      ((K.stupidFiltration).stageInclusion p).f n =
        𝟙 (K.X n) := by
  rw [← stupid_filtration_stage_active_iso_hom K p n hpn]
  exact (stupid_filtration_stage_active_iso K p n hpn).inv_hom_id

private theorem stupid_filtration_stage_term_isZero_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hnp : n < p) :
    IsZero (((K.stupidFiltration).stage p).X n) := by
  change IsZero ((stupidFiltrationSubobject K p n : 𝒜))
  rw [stupidFiltrationSubobject, if_neg (not_le_of_gt hnp)]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

private theorem embeddingUpIntGE_toNat_sub_eq
    (p n : ℤ) (hpn : p ≤ n) :
    (embeddingUpIntGE p).f (Int.toNat (n - p)) = n := by
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

private noncomputable def stupid_trunc_active_iso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    (K.stupidTrunc (embeddingUpIntGE p)).X n ≅ K.X n :=
  K.stupidTruncXIso (embeddingUpIntGE p) (embeddingUpIntGE_toNat_sub_eq p n hpn)

private theorem stupid_trunc_term_isZero_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hnp : n < p) :
    IsZero ((K.stupidTrunc (embeddingUpIntGE p)).X n) := by
  refine K.isZero_stupidTrunc_X (embeddingUpIntGE p) n ?_
  simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hnp

private theorem stupid_trunc_d_via_x_iso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ}
    (hpi : p ≤ i) (hpj : p ≤ j) :
    (stupid_trunc_active_iso K p i hpi).inv ≫
      (K.stupidTrunc (embeddingUpIntGE p)).d i j ≫
      (stupid_trunc_active_iso K p j hpj).hom =
        K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) := embeddingUpIntGE p
  let i₀ : ℕ := Int.toNat (i - p)
  let j₀ : ℕ := Int.toNat (j - p)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq p i hpi
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq p j hpj
  change (stupid_trunc_active_iso K p i hpi).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (stupid_trunc_active_iso K p j hpj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [stupid_trunc_active_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

private theorem stupid_filtration_stage_d_comp_stageInclusion
    (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    ((K.stupidFiltration).stage p).d i j ≫
      ((K.stupidFiltration).stageInclusion p).f j =
        ((K.stupidFiltration).stageInclusion p).f i ≫ K.d i j := by
  change FilteredObject.Hom.stageMap ((K.stupidFiltration).d i j) p ≫
      (FilteredObject.stageFunctorToForget p).app ((K.stupidFiltration).X j) =
    (FilteredObject.stageFunctorToForget p).app ((K.stupidFiltration).X i) ≫
      ((K.stupidFiltration).d i j).hom
  exact FilteredObject.Hom.stageMap_comm ((K.stupidFiltration).d i j) p

private theorem stupid_filtration_stage_d_via_term_iso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ}
    (hpi : p ≤ i) (hpj : p ≤ j) (_ : (ComplexShape.up ℤ).Rel i j) :
    (stupid_filtration_stage_active_iso K p i hpi).inv ≫
      ((K.stupidFiltration).stage p).d i j ≫
      (stupid_filtration_stage_active_iso K p j hpj).hom =
        K.d i j := by
  rw [stupid_filtration_stage_active_iso_hom K p j hpj]
  change (stupid_filtration_stage_active_iso K p i hpi).inv ≫
      (((K.stupidFiltration).stage p).d i j ≫ ((K.stupidFiltration).stageInclusion p).f j) =
    K.d i j
  rw [stupid_filtration_stage_d_comp_stageInclusion K p i j]
  have hcomp :
      ((stupid_filtration_stage_active_iso K p i hpi).inv ≫
          ((K.stupidFiltration).stageInclusion p).f i) ≫ K.d i j =
        𝟙 (K.X i) ≫ K.d i j :=
    congrArg
      (fun f ↦ f ≫ K.d i j)
      (stupid_filtration_stage_active_iso_inv_stageInclusion K p i hpi)
  simpa [Category.assoc] using hcomp.trans (by simp)

/-- The `p`-th stage of the stupid filtration is the brutal truncation `σ≥p(K^•)`. -/
def stupidFiltration_stage_iso_stupidTrunc
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.stupidFiltration).stage p ≅ K.stupidTrunc (embeddingUpIntGE p) :=
  let e :
      ∀ n : ℤ, ((K.stupidFiltration).stage p).X n ≅
        (K.stupidTrunc (embeddingUpIntGE p)).X n := fun n ↦
    if hpn : p ≤ n then
      stupid_filtration_stage_active_iso K p n hpn ≪≫
        (stupid_trunc_active_iso K p n hpn).symm
    else
      let hnp : n < p := lt_of_not_ge hpn
      (stupid_filtration_stage_term_isZero_of_lt K p n hnp).isoZero ≪≫
        (stupid_trunc_term_isZero_of_lt K p n hnp).isoZero.symm
  HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    by_cases hpi : p ≤ i
    · have hpj : p ≤ j := by
        have hij' : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      let eStageI : ((K.stupidFiltration).stage p).X i ≅ K.X i :=
        stupid_filtration_stage_active_iso K p i hpi
      let eStageJ : ((K.stupidFiltration).stage p).X j ≅ K.X j :=
        stupid_filtration_stage_active_iso K p j hpj
      let eTruncI : (K.stupidTrunc (embeddingUpIntGE p)).X i ≅ K.X i :=
        stupid_trunc_active_iso K p i hpi
      let eTruncJ : (K.stupidTrunc (embeddingUpIntGE p)).X j ≅ K.X j :=
        stupid_trunc_active_iso K p j hpj
      have he_i : (e i).hom = eStageI.hom ≫ eTruncI.inv := by
        simp [e, hpi, eStageI, eTruncI]
      have he_j : (e j).hom = eStageJ.hom ≫ eTruncJ.inv := by
        simp [e, hpj, eStageJ, eTruncJ]
      apply (cancel_mono eTruncJ.hom).1
      rw [he_i, he_j]
      simp_rw [Category.assoc]
      calc
        eStageI.hom ≫ eTruncI.inv ≫
            (K.stupidTrunc (embeddingUpIntGE p)).d i j ≫ eTruncJ.hom
          = eStageI.hom ≫ K.d i j := by
              rw [stupid_trunc_d_via_x_iso K p hpi hpj]
        _ = eStageI.hom ≫
            (eStageI.inv ≫ ((K.stupidFiltration).stage p).d i j ≫ eStageJ.hom) := by
              rw [stupid_filtration_stage_d_via_term_iso K p hpi hpj hij]
        _ = ((K.stupidFiltration).stage p).d i j ≫ eStageJ.hom := by
              simp
        _ = ((K.stupidFiltration).stage p).d i j ≫ eStageJ.hom ≫ eTruncJ.inv ≫ eTruncJ.hom := by
              simp
    · exact (stupid_filtration_stage_term_isZero_of_lt K p i (lt_of_not_ge hpi)).eq_of_src _ _)

end Filtrations

end CochainComplex
end CategoryTheory
