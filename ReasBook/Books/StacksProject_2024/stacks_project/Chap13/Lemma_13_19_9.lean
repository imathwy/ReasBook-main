import Mathlib
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open scoped ZeroObject

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

local notation "projMinusι" => MinusWithTermsIn.ι (isProjective 𝒜)

section

variable [EnoughProjectives 𝒜]

/-- Helper for Lemma 13.19.9: the comparison map of a projective resolution is a quasi-isomorphism
by definition. -/
private theorem projectiveResolution_map_quasiIso {K : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) : QuasiIso P.π := by
  infer_instance

/-- Helper for Lemma 13.19.9: in a morphism between short exact rows of cochain complexes,
quasi-isomorphisms on the outer vertical maps force a quasi-isomorphism on the middle map. -/
private theorem quasiIso_tau₂_of_shortExact
    {S T : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (hτ₁ : QuasiIso φ.τ₁) (hτ₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  let φQ := triangleOfSES.map hS hT φ
  have hSQ : triangleOfSES hS ∈ distTriang (DerivedCategory 𝒜) := by
    simpa using triangleOfSES_distinguished hS
  have hTQ : triangleOfSES hT ∈ distTriang (DerivedCategory 𝒜) := by
    simpa using triangleOfSES_distinguished hT
  have hQ₁ : IsIso φQ.hom₁ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso 𝒜 φ.τ₁).2 hτ₁)
  have hQ₃ : IsIso φQ.hom₃ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso 𝒜 φ.τ₃).2 hτ₃)
  have hQ₂ : IsIso φQ.hom₂ := by
    simpa [φQ] using (isIso₂_of_isIso₁₃ φQ hSQ hTQ hQ₁ hQ₃ : IsIso φQ.hom₂)
  exact (isIso_Q_map_iff_quasiIso 𝒜 φ.τ₂).1 (by simpa [φQ] using hQ₂)

/-- Given a chosen projective resolution of the right complex, the diagram can be built with that
resolution as its right column, provided the left term of the short exact row is bounded above;
the right bounded-above hypothesis is already supplied by the chosen projective resolution. The
middle term is then bounded above by short exactness. -/
theorem exists_projectiveResolutionDiagram_of_shortExact_with_rightResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.minus 𝒜 S.X₁) (P : ProjectiveResolution S.X₃) :
    ∃ (Q R : ProjectiveMinus 𝒜) (f : Q ⟶ R) (g : R ⟶ P.complex) (hfg : f ≫ g = 0)
      (φ : (ShortComplex.mk f g hfg).map projMinusι ⟶ S),
        φ.τ₃ = P.π ∧
          ((ShortComplex.mk f g hfg).map projMinusι).ShortExact ∧
          QuasiIso φ.τ₁ ∧
          QuasiIso φ.τ₂ := by
  obtain ⟨a, hA'⟩ := (CochainComplex.minus_iff 𝒜 S.X₁).1 hA
  obtain ⟨Q, hQ, hQepi⟩ :=
    exists_projectiveResolution_strictlyLE_with_termwise_epi
      (𝒜 := 𝒜) (K := S.X₁) a hA'
  let QC : CochainComplex 𝒜 ℤ := Q
  let PC : CochainComplex 𝒜 ℤ := P
  let evalShort (n : ℤ) : ShortComplex 𝒜 :=
    S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  have hEvalShort (n : ℤ) : (evalShort n).ShortExact := by
    simpa [evalShort] using hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
  let rightLift (n : ℤ) : PC.X n ⟶ S.X₂.X n :=
    let _ : Epi (S.g.f n) := by
      simpa [evalShort] using (hEvalShort n).epi_g
    Projective.factorThru (P.π.f n) (S.g.f n)
  have rightLift_comp (n : ℤ) : rightLift n ≫ S.g.f n = P.π.f n := by
    dsimp [rightLift]
    exact Projective.factorThru_comp (P.π.f n) (S.g.f n)
  let obstruction (n : ℤ) : PC.X n ⟶ S.X₂.X (n + 1) :=
    rightLift n ≫ S.X₂.d n (n + 1) - PC.d n (n + 1) ≫ rightLift (n + 1)
  have obstruction_comp_zero (n : ℤ) : obstruction n ≫ S.g.f (n + 1) = 0 := by
    dsimp [obstruction]
    rw [sub_comp, Category.assoc, S.g.comm, Category.assoc, rightLift_comp, P.π.comm,
      Category.assoc, rightLift_comp]
    simp
  let delta (n : ℤ) : PC.X n ⟶ S.X₁.X (n + 1) :=
    (hEvalShort (n + 1)).fIsKernel.lift
      (KernelFork.ofι (obstruction n) (obstruction_comp_zero n))
  have delta_fac (n : ℤ) : delta n ≫ S.f.f (n + 1) = obstruction n := by
    simpa [delta] using
      (hEvalShort (n + 1)).fIsKernel.fac
        (KernelFork.ofι (obstruction n) (obstruction_comp_zero n))
        WalkingParallelPair.zero
  let gamma (n : ℤ) : PC.X n ⟶ QC.X (n + 1) :=
    let _ : Epi (Q.π.f (n + 1)) := hQepi (n + 1)
    Projective.factorThru (delta n) (Q.π.f (n + 1))
  have gamma_fac (n : ℤ) : gamma n ≫ Q.π.f (n + 1) = delta n := by
    dsimp [gamma]
    exact Projective.factorThru_comp (delta n) (Q.π.f (n + 1))
  let middleX : ℤ → 𝒜 := fun n ↦ QC.X n ⊞ PC.X n
  let middleD : ∀ n : ℤ, middleX n ⟶ middleX (n + 1) := fun n ↦
    biprod.lift
      (biprod.desc (QC.d n (n + 1)) (gamma n))
      (biprod.desc 0 (PC.d n (n + 1)))
  have middle_cross (n : ℤ) :
      gamma n ≫ QC.d (n + 1) (n + 2) + PC.d n (n + 1) ≫ gamma (n + 1) = 0 := by
    let _ : Epi (Q.π.f (n + 2)) := hQepi (n + 2)
    apply (cancel_epi (Q.π.f (n + 2))).1
    rw [add_comp, Category.assoc, Q.π.comm, Category.assoc, gamma_fac, Category.assoc, gamma_fac]
    let _ : Mono (S.f.f (n + 2)) := by
      simpa [evalShort] using (hEvalShort (n + 2)).mono_f
    apply (cancel_mono (S.f.f (n + 2))).1
    rw [add_comp, Category.assoc, ← S.f.comm_assoc, delta_fac, Category.assoc, delta_fac]
    dsimp [obstruction]
    simp [sub_comp, add_comp, Category.assoc]
  have middleSq : ∀ n : ℤ, middleD n ≫ middleD (n + 1) = 0 := by
    intro n
    apply biprod.hom_ext
    · simp [middleD, middle_cross, Category.assoc]
    · simp [middleD, Category.assoc]
  let R' : CochainComplex 𝒜 ℤ := CochainComplex.of middleX middleD middleSq
  have left_comm :
      ∀ n : ℤ, (biprod.inl : QC.X n ⟶ middleX n) ≫ middleD n =
        QC.d n (n + 1) ≫ (biprod.inl : QC.X (n + 1) ⟶ middleX (n + 1)) := by
    intro n
    simp [middleD, Category.assoc]
  let f' : QC ⟶ R' :=
    CochainComplex.ofHom
      (fun n ↦ QC.X n) (fun n ↦ QC.d n (n + 1)) (fun n ↦ QC.d_comp_d _ _ _)
      middleX middleD middleSq
      (fun n ↦ biprod.inl) left_comm
  have right_comm :
      ∀ n : ℤ, (biprod.snd : middleX n ⟶ PC.X n) ≫ PC.d n (n + 1) =
        middleD n ≫ (biprod.snd : middleX (n + 1) ⟶ PC.X (n + 1)) := by
    intro n
    simp [middleD, Category.assoc]
  let g' : R' ⟶ PC :=
    CochainComplex.ofHom
      middleX middleD middleSq
      (fun n ↦ PC.X n) (fun n ↦ PC.d n (n + 1)) (fun n ↦ PC.d_comp_d _ _ _)
      (fun n ↦ biprod.snd) right_comm
  have hfg' : f' ≫ g' = 0 := by
    ext n
    simp [f', g']
  have middle_map_comm :
      ∀ n : ℤ,
        (biprod.desc (Q.π.f n ≫ S.f.f n) (rightLift n)) ≫ S.X₂.d n (n + 1) =
          middleD n ≫ biprod.desc (Q.π.f (n + 1) ≫ S.f.f (n + 1)) (rightLift (n + 1)) := by
    intro n
    apply biprod.hom_ext
    · simp [middleD, Category.assoc]
    · rw [biprod.inr_desc, Category.assoc, delta_fac]
      simp [middleD, obstruction, Category.assoc]
  let middleMap : R' ⟶ S.X₂ :=
    CochainComplex.ofHom
      middleX middleD middleSq
      (fun n ↦ S.X₂.X n) (fun n ↦ S.X₂.d n (n + 1)) (fun n ↦ S.X₂.d_comp_d _ _ _)
      (fun n ↦ biprod.desc (Q.π.f n ≫ S.f.f n) (rightLift n)) middle_map_comm
  obtain ⟨bQ, hbQ⟩ := Q.exists_isStrictlyLE
  obtain ⟨bP, hbP⟩ := P.exists_isStrictlyLE
  have hRstrict : R'.IsStrictlyLE (max bQ bP) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hQi : IsZero (QC.X i) :=
      hbQ.isZero_of_isStrictlyLE _ _ (lt_of_le_of_lt (le_max_left _ _) hi)
    have hPi : IsZero (PC.X i) :=
      hbP.isZero_of_isStrictlyLE _ _ (lt_of_le_of_lt (le_max_right _ _) hi)
    simpa [R', middleX] using (biprod_isZero_iff (QC.X i) (PC.X i)).2 ⟨hQi, hPi⟩
  have hRproj : ∀ n : ℤ, Projective (R'.X n) := by
    intro n
    dsimp [R', middleX]
    infer_instance
  let R : ProjectiveMinus 𝒜 :=
    ⟨⟨R', (CochainComplex.minus_iff 𝒜 R').2 ⟨max bQ bP, hRstrict⟩⟩, hRproj⟩
  let f : Q.complex ⟶ R := f'
  let g : R ⟶ P.complex := g'
  have hrow_eval :
      ∀ n : ℤ,
        ((ShortComplex.mk f g hfg').map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).ShortExact := by
    intro n
    simpa [f, g, f', g', R, R', middleX] using
      (ShortComplex.Splitting.shortExact
        (ShortComplex.Splitting.ofHasBinaryBiproduct (QC.X n) (PC.X n)))
  have hrow : ((ShortComplex.mk f g hfg').map projMinusι).ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact ?_
    intro n
    simpa [projMinusι] using hrow_eval n
  have hφ₁₂ : Q.π ≫ S.f = f' ≫ middleMap := by
    ext n
    simp [f', middleMap, Category.assoc]
  have hφ₂₃ : middleMap ≫ S.g = g' ≫ P.π := by
    ext n
    simp [middleMap, g', rightLift_comp, Category.assoc]
  let φ : (ShortComplex.mk f g hfg').map projMinusι ⟶ S :=
    ShortComplex.homMk Q.π middleMap P.π hφ₁₂ hφ₂₃
  have hφ₁ : QuasiIso φ.τ₁ := by
    simpa [φ] using projectiveResolution_map_quasiIso Q
  have hφ₃ : QuasiIso φ.τ₃ := by
    simpa [φ] using projectiveResolution_map_quasiIso P
  have hφ₂ : QuasiIso φ.τ₂ := quasiIso_tau₂_of_shortExact hrow hS φ hφ₁ hφ₃
  exact ⟨Q.complex, R, f, g, hfg', φ, rfl, hrow, hφ₁, hφ₂⟩

/-- Lemma 13.19.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
in an abelian category with enough projectives whose outer terms are bounded above, then it
extends to a commutative diagram whose vertical maps are projective resolutions and whose upper
row is again a short exact sequence of complexes. The middle term is bounded above because
bounded-above cochain complexes are closed under extensions. -/
theorem exists_projectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.minus 𝒜 S.X₁) (hC : CochainComplex.minus 𝒜 S.X₃) :
    ∃ row : ShortComplex (ProjectiveMinus 𝒜), ∃ hom : row.map projMinusι ⟶ S,
      (row.map projMinusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ := by
  obtain ⟨c, hC'⟩ := (CochainComplex.minus_iff 𝒜 S.X₃).1 hC
  obtain ⟨P, -, -⟩ :=
    exists_projectiveResolution_strictlyLE_with_termwise_epi
      (𝒜 := 𝒜) (K := S.X₃) c hC'
  obtain ⟨Q, R, f, g, hfg, φ, hφ₃, hrow, hφ₁, hφ₂⟩ :=
    exists_projectiveResolutionDiagram_of_shortExact_with_rightResolution
      (S := S) hS hA P
  refine ⟨ShortComplex.mk f g hfg, φ, hrow, hφ₁, hφ₂, ?_⟩
  simpa [hφ₃] using projectiveResolution_map_quasiIso P

end

end CochainComplex
