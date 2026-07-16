import Mathlib
import StacksProject_2024.stacks_project.Chap14.Definition_14_22_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for Lemma 14.22.4:
- primary domain: Dold-Kan images of two-term chain complexes and the induced short complexes of
  simplicial objects.
- inspected owner declarations:
  `eilenbergMacLaneObjectIsoDoldKanSingle`,
  `HomologicalComplex.double`,
  `ShortComplex.ShortExact`,
  `ShortComplex.Splitting.shortExact`.
- best owner abstraction: the source-facing short complex
  `eilenberg_maclane_object A k ⟶ E ⟶ eilenberg_maclane_object A (k + 1)`.
  The two-term `double (𝟙 A)` chain complex and its Dold-Kan image are bridge/model data for that
  owner, while `ShortComplex`, `ShortComplex.ShortExact`, and
  `ShortComplex.Splitting.shortExact` provide the core API.
- layer: `source-facing`; the lemma constructs the extension short complex itself, rather than
  merely recalling a pre-existing exactness theorem.
- primitive data: the two-term chain complex `double (𝟙 A) ...`, its inclusion/projection chain
  maps, the Dold-Kan image `E`, and the comparison theorem from `eilenberg_maclane_object` to
  the Dold-Kan model of the single complex.
- derived API: short exactness and canonical termwise splittings of the associated simplicial
  short complex.
-/

open CategoryTheory Category Limits ZeroObject Abelian.DoldKan HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

private instance gammaPreservesZeroMorphisms :
    (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜).PreservesZeroMorphisms where
  map_zero K L := by
    ext Δ
    apply (AlgebraicTopology.DoldKan.Γ₀.splitting K).hom_ext'
    intro B
    calc
      (((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj B ≫
          (AlgebraicTopology.DoldKan.Γ₀.splitting K).desc Δ
            (fun A ↦
              (0 : K.X A.1.unop.len ⟶ L.X A.1.unop.len) ≫
                ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj A)) =
          0 ≫ ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj B := by
            simpa using
              (AlgebraicTopology.DoldKan.Γ₀.splitting K).ι_desc Δ
                (fun A ↦
                  (0 : K.X A.1.unop.len ⟶ L.X A.1.unop.len) ≫
                    ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj A)
                B
      _ = 0 := by exact zero_comp
      _ = ((AlgebraicTopology.DoldKan.Γ₀.splitting K).cofan Δ).inj B ≫ 0 := by
            rw [comp_zero]

private abbrev eilenbergMacLaneExtensionRel (k : ℕ) : (ComplexShape.down ℕ).Rel (k + 1) k := rfl

/-- The two-term chain complex with `A` in degrees `k + 1` and `k`, and differential `𝟙 A`
from degree `k + 1` to degree `k`. -/
abbrev eilenbergMacLaneExtensionComplex (A : 𝒜) (k : ℕ) : ChainComplex 𝒜 ℕ :=
  double (𝟙 A) (eilenbergMacLaneExtensionRel k)

/-- The simplicial object `E` obtained from the two-term identity complex by the Dold-Kan
equivalence; degreewise this matches the textbook direct-sum construction. -/
abbrev eilenbergMacLaneExtension (A : 𝒜) (k : ℕ) : SimplicialObject 𝒜 :=
  Γ.obj (eilenbergMacLaneExtensionComplex A k)

private noncomputable def eilenbergMacLaneExtensionComplexDiffIso (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).X (k + 1) ≅
      (eilenbergMacLaneExtensionComplex A k).X k :=
  (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)) ≪≫ (Iso.refl A) ≪≫
    (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k) (Nat.succ_ne_self k)).symm

private lemma eilenbergMacLaneExtensionComplex_d_eq
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).d (k + 1) k =
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom := by
  simp [eilenbergMacLaneExtensionComplex, eilenbergMacLaneExtensionComplexDiffIso,
    HomologicalComplex.double_d]

private lemma eilenbergMacLaneExtensionComplex_left_g_eq_zero
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).d k ((ComplexShape.down ℕ).next k) = 0 := by
  cases k with
  | zero =>
      rw [ChainComplex.next_nat_zero]
      change (double (𝟙 A) (eilenbergMacLaneExtensionRel 0)).d 0 0 = 0
      exact HomologicalComplex.double_d_eq_zero₀
        (𝟙 A) (eilenbergMacLaneExtensionRel 0) 0 0 Nat.zero_ne_one
  | succ n =>
      rw [ChainComplex.next_nat_succ]
      simpa [eilenbergMacLaneExtensionComplex] using
        (HomologicalComplex.double_d_eq_zero₁
          (𝟙 A) (eilenbergMacLaneExtensionRel (n + 1)) (n + 1) n (by simp : n ≠ n + 1))

private lemma eilenbergMacLaneExtensionComplex_right_f_eq_zero
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).d (k + 2) (k + 1) = 0 := by
  simpa [eilenbergMacLaneExtensionComplex] using
    (HomologicalComplex.double_d_eq_zero₀
      (𝟙 A) (eilenbergMacLaneExtensionRel k) (k + 2) (k + 1) (by omega : k + 2 ≠ k + 1))

private lemma eilenbergMacLaneExtensionComplex_isZero_X
    (A : 𝒜) (k n : ℕ) (hk : n ≠ k) (hk1 : n ≠ k + 1) :
    IsZero ((eilenbergMacLaneExtensionComplex A k).X n) := by
  simpa [eilenbergMacLaneExtensionComplex] using
    (HomologicalComplex.isZero_double_X
      (𝟙 A) (eilenbergMacLaneExtensionRel k) n hk1 hk)

private lemma eilenbergMacLaneExtensionComplex_leftShortComplex_exact
    (A : 𝒜) (k : ℕ) :
    (ShortComplex.mk
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom
      (0 : (eilenbergMacLaneExtensionComplex A k).X k ⟶
        (eilenbergMacLaneExtensionComplex A k).X ((ComplexShape.down ℕ).next k))
      (by simp)).Exact := by
  let w :
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom ≫
        (0 : (eilenbergMacLaneExtensionComplex A k).X k ⟶
          (eilenbergMacLaneExtensionComplex A k).X ((ComplexShape.down ℕ).next k)) = 0 := by
    simp
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι'
    ((eilenbergMacLaneExtensionComplexDiffIso A k).hom) w
    (fun {Z} g hg ↦ ⟨g ≫ (eilenbergMacLaneExtensionComplexDiffIso A k).inv, by simp⟩)

private lemma eilenbergMacLaneExtensionComplex_rightShortComplex_exact
    (A : 𝒜) (k : ℕ) :
    (ShortComplex.mk
      (0 : (eilenbergMacLaneExtensionComplex A k).X (k + 2) ⟶
        (eilenbergMacLaneExtensionComplex A k).X (k + 1))
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom
      (by simp)).Exact := by
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk
      (0 : (eilenbergMacLaneExtensionComplex A k).X (k + 2) ⟶
        (eilenbergMacLaneExtensionComplex A k).X (k + 1))
      (eilenbergMacLaneExtensionComplexDiffIso A k).hom
      (by simp)
  have hS : S.Splitting :=
    ShortComplex.Splitting.ofIsZeroOfIsIso S
      (eilenbergMacLaneExtensionComplex_isZero_X A k (k + 2) (by omega) (by omega))
      inferInstance
  exact
    hS.shortExact.exact

private lemma eilenbergMacLaneExtensionComplex_exactAt
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).ExactAt k := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 1) k ((ComplexShape.down ℕ).next k)]
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (eilenbergMacLaneExtensionComplex_leftShortComplex_exact A k)
    refine ShortComplex.isoMk
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simpa using eilenbergMacLaneExtensionComplex_d_eq A k
    · simpa using
        eilenbergMacLaneExtensionComplex_left_g_eq_zero A k
  · simp [ChainComplex.prev]
  · rfl

private lemma eilenbergMacLaneExtensionComplex_exactAt_succ
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k]
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (eilenbergMacLaneExtensionComplex_rightShortComplex_exact A k)
    refine ShortComplex.isoMk
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simpa using
        eilenbergMacLaneExtensionComplex_right_f_eq_zero A k
    · simpa using
        eilenbergMacLaneExtensionComplex_d_eq A k
  · simp [ChainComplex.prev]
  · exact ChainComplex.next_nat_succ k

-- Proof sketch: the model complex is the two-term identity complex `A --𝟙--> A` in degrees
-- `k + 1` and `k`; exactness at the two nonzero degrees comes from the differential being an
-- isomorphism, and all other degrees vanish.
/-- The two-term chain-complex model underlying `eilenbergMacLaneExtension A k` is acyclic. -/
theorem eilenbergMacLaneExtensionComplex_acyclic (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionComplex A k).Acyclic := by
  intro i
  by_cases hk : i = k
  · simpa [hk] using eilenbergMacLaneExtensionComplex_exactAt A k
  by_cases hk1 : i = k + 1
  · simpa [hk1] using eilenbergMacLaneExtensionComplex_exactAt_succ A k
  · rw [HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ <| by
      exact eilenbergMacLaneExtensionComplex_isZero_X A k i hk hk1

-- Proof sketch: the double complex has only one nonzero differential, from degree `k + 1` to
-- degree `k`; every differential out of degree `k` is therefore zero.
/-- The degree-`k` component of the double complex gives a chain map from the single complex in
degree `k` into the two-term extension complex. -/
private theorem eilenbergMacLaneExtensionInclusionChainMap_comm (A : 𝒜) (k i : ℕ)
    (hi : (ComplexShape.down ℕ).Rel k i) :
    (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k)
      (Nat.succ_ne_self k)).inv ≫
      (eilenbergMacLaneExtensionComplex A k).d k i = 0 := by
  have hi' : i ≠ k := by
    intro h
    subst h
    simp at hi
  simpa [eilenbergMacLaneExtensionComplex] using
    show
      (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k) (Nat.succ_ne_self k)).inv ≫
        (double (𝟙 A) (eilenbergMacLaneExtensionRel k)).d k i = 0 by
      rw [HomologicalComplex.double_d_eq_zero₁ (𝟙 A) (eilenbergMacLaneExtensionRel k) k i hi']
      simp

/-- The chain map from the complex concentrated in degree `k` into the two-term extension
complex. -/
private noncomputable abbrev eilenbergMacLaneExtensionInclusionChainMap (A : 𝒜) (k : ℕ) :
    (single 𝒜 (ComplexShape.down ℕ) k).obj A ⟶
      eilenbergMacLaneExtensionComplex A k :=
  mkHomFromSingle
    ((doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k)
      (Nat.succ_ne_self k)).inv)
    (eilenbergMacLaneExtensionInclusionChainMap_comm A k)

-- Proof sketch: the only nonzero differential of the double complex ends in degree `k`, so every
-- differential landing in degree `k + 1` is zero.
/-- The degree-`k + 1` component of the double complex gives a chain map from the two-term
extension complex to the single complex in degree `k + 1`. -/
private theorem eilenbergMacLaneExtensionProjectionChainMap_comm (A : 𝒜) (k i : ℕ)
    (hi : (ComplexShape.down ℕ).Rel i (k + 1)) :
    (eilenbergMacLaneExtensionComplex A k).d i (k + 1) ≫
      (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom = 0 :=
  by
    have hi' : i ≠ k + 1 := by
      intro h
      subst h
      simp at hi
    simpa [eilenbergMacLaneExtensionComplex] using
      show
        (double (𝟙 A) (eilenbergMacLaneExtensionRel k)).d i (k + 1) ≫
          (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom = 0 by
        rw [HomologicalComplex.double_d_eq_zero₀ (𝟙 A) (eilenbergMacLaneExtensionRel k) i
          (k + 1) hi']
        simp

/-- The chain map from the two-term extension complex to the complex concentrated in degree
`k + 1`. -/
private noncomputable abbrev eilenbergMacLaneExtensionProjectionChainMap (A : 𝒜) (k : ℕ) :
    eilenbergMacLaneExtensionComplex A k ⟶
      (single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A :=
  mkHomToSingle
    ((doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom)
    (eilenbergMacLaneExtensionProjectionChainMap_comm A k)

private lemma eilenbergMacLaneExtensionProjectionChainMap_f_eq_zero
    (A : 𝒜) (k n : ℕ) (hk1 : n ≠ k + 1) :
    (eilenbergMacLaneExtensionProjectionChainMap A k).f n = 0 := by
  dsimp [eilenbergMacLaneExtensionProjectionChainMap, HomologicalComplex.mkHomToSingle]
  simp [hk1]

private lemma eilenbergMacLaneExtensionInclusionChainMap_component_isIso
    (A : 𝒜) (k n : ℕ) (h : n = k) :
    IsIso ((eilenbergMacLaneExtensionInclusionChainMap A k).f n) := by
  subst n
  dsimp [eilenbergMacLaneExtensionInclusionChainMap, HomologicalComplex.mkHomFromSingle]
  split_ifs with hi
  · infer_instance
  · exact (hi rfl).elim

private lemma eilenbergMacLaneExtensionProjectionChainMap_component_isIso
    (A : 𝒜) (k n : ℕ) (h : n = k + 1) :
    IsIso ((eilenbergMacLaneExtensionProjectionChainMap A k).f n) := by
  subst n
  dsimp [eilenbergMacLaneExtensionProjectionChainMap, HomologicalComplex.mkHomToSingle]
  split_ifs with hi
  · infer_instance
  · exact (hi rfl).elim

-- Proof sketch: in the two-term model, the projection kills the `k`-summand and the inclusion
-- lands entirely in that summand.
/-- The inclusion and projection chain maps for the two-term model compose to zero. -/
private theorem eilenbergMacLaneExtensionModel_comp_zero (A : 𝒜) (k : ℕ) :
    eilenbergMacLaneExtensionInclusionChainMap A k ≫
      eilenbergMacLaneExtensionProjectionChainMap A k = 0 := by
  refine HomologicalComplex.from_single_hom_ext ?_
  dsimp [eilenbergMacLaneExtensionInclusionChainMap,
    eilenbergMacLaneExtensionProjectionChainMap, HomologicalComplex.mkHomFromSingle,
    HomologicalComplex.mkHomToSingle]
  simp

/-- The short complex on chain complexes whose Dold-Kan image gives the extension sequence. -/
private noncomputable abbrev eilenbergMacLaneExtensionModelShortComplex
    (A : 𝒜) (k : ℕ) : ShortComplex (ChainComplex 𝒜 ℕ) :=
  ShortComplex.mk
    (eilenbergMacLaneExtensionInclusionChainMap A k)
    (eilenbergMacLaneExtensionProjectionChainMap A k)
    (eilenbergMacLaneExtensionModel_comp_zero A k)

private noncomputable def gammaSplitting (K : ChainComplex 𝒜 ℕ) :
    SimplicialObject.Splitting (Γ.obj K) := by
  simpa [Abelian.DoldKan.Γ, Idempotents.DoldKan.Γ, AlgebraicTopology.DoldKan.Γ₀] using
    (AlgebraicTopology.DoldKan.Γ₀.splitting K)

private lemma gammaCofanInj_comp_app {K L : ChainComplex 𝒜 ℕ} (f : K ⟶ L)
    (Δ : SimplexCategoryᵒᵖ) (B : SimplicialObject.Splitting.IndexSet Δ) :
    ((gammaSplitting K).cofan Δ).inj B ≫ (Γ.map f).app Δ =
      f.f B.1.unop.len ≫ ((gammaSplitting L).cofan Δ).inj B := by
  simpa [gammaSplitting, Abelian.DoldKan.Γ, Idempotents.DoldKan.Γ, AlgebraicTopology.DoldKan.Γ₀]
    using
      (AlgebraicTopology.DoldKan.Γ₀.splitting K).ι_desc Δ
        (fun A ↦ f.f A.1.unop.len ≫ ((AlgebraicTopology.DoldKan.Γ₀.splitting L).cofan Δ).inj A)
        B

private lemma gammaSingleCofanInj_eq_zero
    (A : 𝒜) (k : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (B : SimplicialObject.Splitting.IndexSet Δ) (h : B.1.unop.len ≠ k) :
    ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) k).obj A)).cofan Δ).inj B = 0 := by
  let hzero :=
    isZero_single_obj_X (ComplexShape.down ℕ) k A B.1.unop.len h
  exact hzero.eq_of_src _ _

private lemma gammaExtensionCofanInj_eq_zero
    (A : 𝒜) (k : ℕ) {Δ : SimplexCategoryᵒᵖ}
    (B : SimplicialObject.Splitting.IndexSet Δ)
    (hk : B.1.unop.len ≠ k) (hk1 : B.1.unop.len ≠ k + 1) :
    ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B = 0 := by
  let hzero := eilenbergMacLaneExtensionComplex_isZero_X A k B.1.unop.len hk hk1
  exact hzero.eq_of_src _ _

/-- The short complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` attached to the Eilenberg-MacLane extension. -/
abbrev eilenbergMacLaneExtensionShortComplex (A : 𝒜) (k : ℕ) :
    ShortComplex (SimplicialObject 𝒜) :=
  let e₁ := eilenbergMacLaneObjectIsoDoldKanSingle A k
  let e₃ := eilenbergMacLaneObjectIsoDoldKanSingle A (k + 1)
  { X₁ := K(A, k)
    X₂ := eilenbergMacLaneExtension A k
    X₃ := K(A, k + 1)
    f := e₁.hom ≫ ((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).f
    g := ((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).g ≫ e₃.inv
    zero := by
      let S := (eilenbergMacLaneExtensionModelShortComplex A k).map Γ
      have h :
          e₁.hom ≫ (S.f ≫ S.g) ≫ e₃.inv = e₁.hom ≫ 0 ≫ e₃.inv := by
        exact congrArg (fun t ↦ e₁.hom ≫ t ≫ e₃.inv) S.zero
      have h' : e₁.hom ≫ 0 ≫ e₃.inv = 0 := by simp
      exact (by simpa [Category.assoc] using h.trans h') }

private noncomputable def eilenbergMacLaneExtensionModelShortComplexGammaIso
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionModelShortComplex A k).map Γ ≅
      eilenbergMacLaneExtensionShortComplex A k :=
  ShortComplex.isoMk
    (eilenbergMacLaneObjectIsoDoldKanSingle A k).symm
    (Iso.refl _)
    (eilenbergMacLaneObjectIsoDoldKanSingle A (k + 1)).symm
    (by
      simp [eilenbergMacLaneExtensionShortComplex, eilenbergMacLaneExtensionModelShortComplex])
    (by
      simp [eilenbergMacLaneExtensionShortComplex, eilenbergMacLaneExtensionModelShortComplex])

-- Proof sketch: after evaluating the chain-level model at any degree, one gets one of the three
-- canonical split shapes `A ⟶ A ⟶ 0`, `0 ⟶ A ⟶ A`, or `0 ⟶ 0 ⟶ 0`, so the splitting is obtained
-- from the owner constructors `ShortComplex.Splitting.ofIsIsoOfIsZero` and
-- `ShortComplex.Splitting.ofIsZeroOfIsIso`.
/-- The degree-`n` evaluation of the chain-level short complex modeling the extension carries a
canonical splitting. -/
private noncomputable def eilenbergMacLaneExtensionModelShortComplex_degreewiseSplitting
    (A : 𝒜) (k n : ℕ) :
    ((eilenbergMacLaneExtensionModelShortComplex A k).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) n)).Splitting := by
  by_cases hk : n = k
  · subst n
    let S : ShortComplex 𝒜 :=
      (eilenbergMacLaneExtensionModelShortComplex A k).map
        (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) k)
    change S.Splitting
    have hf : IsIso S.f := by
      dsimp [S]
      simpa [eilenbergMacLaneExtensionModelShortComplex,
        eilenbergMacLaneExtensionInclusionChainMap,
        HomologicalComplex.mkHomFromSingle_f] using
        (show IsIso
          ((singleObjXSelf (ComplexShape.down ℕ) k A).hom ≫
            (doubleXIso₁ (𝟙 A) (eilenbergMacLaneExtensionRel k)
              (Nat.succ_ne_self k)).inv) from inferInstance)
    exact ShortComplex.Splitting.ofIsIsoOfIsZero S
      hf
      (by
        simpa [eilenbergMacLaneExtensionModelShortComplex] using
          (isZero_single_obj_X (ComplexShape.down ℕ) (k + 1) A k (by omega)))
  · by_cases hk1 : n = k + 1
    · subst n
      let S : ShortComplex 𝒜 :=
        (eilenbergMacLaneExtensionModelShortComplex A k).map
          (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) (k + 1))
      change S.Splitting
      have hg : IsIso S.g := by
        dsimp [S]
        simpa [eilenbergMacLaneExtensionModelShortComplex,
          eilenbergMacLaneExtensionProjectionChainMap,
          HomologicalComplex.mkHomToSingle_f] using
          (show IsIso
            ((doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).hom ≫
              (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).inv) from inferInstance)
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S
        (by
          simpa [eilenbergMacLaneExtensionModelShortComplex] using
            (isZero_single_obj_X (ComplexShape.down ℕ) k A (k + 1) (Nat.succ_ne_self k)))
        hg
    · let S : ShortComplex 𝒜 :=
        (eilenbergMacLaneExtensionModelShortComplex A k).map
          (HomologicalComplex.eval 𝒜 (ComplexShape.down ℕ) n)
      change S.Splitting
      have hg : IsIso S.g := by
        dsimp [S]
        have hX₂ :
            IsZero ((eilenbergMacLaneExtensionComplex A k).X n) := by
          exact eilenbergMacLaneExtensionComplex_isZero_X A k n hk hk1
        have hX₃ :
            IsZero (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X n) := by
          simpa [eilenbergMacLaneExtensionModelShortComplex] using
            (isZero_single_obj_X (ComplexShape.down ℕ) (k + 1) A n hk1)
        simpa [eilenbergMacLaneExtensionModelShortComplex,
          eilenbergMacLaneExtensionProjectionChainMap_f_eq_zero A k n hk1] using
          (show IsIso
            (0 : (eilenbergMacLaneExtensionComplex A k).X n ⟶
              ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X n) from
            hX₂.isIso hX₃ 0)
      exact ShortComplex.Splitting.ofIsZeroOfIsIso S
        (by
          simpa [eilenbergMacLaneExtensionModelShortComplex] using
            (isZero_single_obj_X (ComplexShape.down ℕ) k A n hk))
        hg

-- Proof sketch: apply `HomologicalComplex.shortExact_of_degreewise_shortExact` to the chain-level
-- model, using the degreewise splittings and the owner lemma `ShortComplex.Splitting.shortExact`.
/-- The chain-level short complex modeling the extension is short exact. -/
private theorem eilenbergMacLaneExtensionModelShortComplex_shortExact
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionModelShortComplex A k).ShortExact := by
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦
      (eilenbergMacLaneExtensionModelShortComplex_degreewiseSplitting A k n).shortExact)

-- Proof sketch: identify `eilenbergMacLaneExtension A k` with the Dold-Kan image of the two-term
-- complex `A --𝟙--> A` in degrees `k + 1` and `k`; transport the chain-level short exact model
-- along `Γ` and the endpoint identifications with `K(A, k)` and `K(A, k + 1)`.
/-- The extension short complex `K(A, k) ⟶ E ⟶ K(A, k + 1)` is short exact. -/
theorem eilenbergMacLaneExtensionShortComplex_shortExact (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionShortComplex A k).ShortExact := by
  letI : PreservesFiniteLimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteLimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  letI : PreservesFiniteColimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteColimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  exact ShortComplex.shortExact_of_iso
    (eilenbergMacLaneExtensionModelShortComplexGammaIso A k)
    (by
      simpa using
        (eilenbergMacLaneExtensionModelShortComplex_shortExact A k).map_of_exact Γ)

private theorem eilenbergMacLaneExtensionModelShortComplex_termwiseShortExact
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
      ((evaluation _ _).obj Δ)).ShortExact := by
  letI : PreservesFiniteLimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteLimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  letI : PreservesFiniteColimits (Γ : ChainComplex 𝒜 ℕ ⥤ SimplicialObject 𝒜) := by
    simpa [Abelian.DoldKan.equivalence_inverse] using
      (inferInstance :
        PreservesFiniteColimits
          ((Abelian.DoldKan.equivalence : SimplicialObject 𝒜 ≌ ChainComplex 𝒜 ℕ).inverse))
  simpa [ShortComplex.map_comp] using
    (eilenbergMacLaneExtensionModelShortComplex_shortExact A k).map_of_exact
      (Γ ⋙ (evaluation _ _).obj Δ)

private noncomputable def eilenbergMacLaneExtensionModelShortComplex_termwiseSection
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
      ((evaluation _ _).obj Δ))).X₃ ⟶
        ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
          ((evaluation _ _).obj Δ))).X₂ := by
  let S := (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
    ((evaluation _ _).obj Δ))
  change S.X₃ ⟶ S.X₂
  exact
    (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).desc Δ
      (fun B ↦
        if h : B.1.unop.len = k + 1 then
          ((((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq h).hom) ≫
            (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).hom ≫
            (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).inv ≫
            ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq h).inv ≫
            ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B
        else 0)

private lemma eilenbergMacLaneExtensionModelShortComplex_termwiseSection_s_g
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ ≫
      ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
        ((evaluation _ _).obj Δ))).g =
      𝟙 _ := by
  let F : ∀ B : SimplicialObject.Splitting.IndexSet Δ,
      (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X B.1.unop.len) ⟶
        ((((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
          ((evaluation _ _).obj Δ))).X₂ :=
    fun B ↦
      if h : B.1.unop.len = k + 1 then
        ((((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq h).hom) ≫
          (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).hom ≫
          (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).inv ≫
          ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq h).inv ≫
          ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B
      else 0
  let S := (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
    ((evaluation _ _).obj Δ))
  change
    eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ ≫ S.g = 𝟙 S.X₃
  apply (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).hom_ext'
  intro B
  have hdesc :
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
        eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ =
      F B := by
    dsimp [eilenbergMacLaneExtensionModelShortComplex_termwiseSection, F]
    simpa using
      (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).ι_desc Δ F B
  have hcomp :
      (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
          eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ) ≫
        S.g =
      F B ≫ S.g := congrArg (fun t ↦ t ≫ S.g) hdesc
  have hFg :
      F B ≫ S.g =
        ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B := by
    by_cases hB : B.1.unop.len = k + 1
    · dsimp [F]
      rw [dif_pos hB]
      let p :
          (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).X B.1.unop.len) ⟶
            (eilenbergMacLaneExtensionComplex A k).X B.1.unop.len :=
        (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq hB).hom ≫
          (singleObjXSelf (ComplexShape.down ℕ) (k + 1) A).hom ≫
            (doubleXIso₀ (𝟙 A) (eilenbergMacLaneExtensionRel k)).inv ≫
              ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq hB).inv
      have hgamma :
          ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B ≫ S.g =
            (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
              ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by
        simpa [S, eilenbergMacLaneExtensionModelShortComplex] using
          (gammaCofanInj_comp_app
            (eilenbergMacLaneExtensionProjectionChainMap A k) Δ B)
      have hgamma' : p ≫
          (((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B ≫ S.g) =
            p ≫
              ((eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B) := by
        exact congrArg (fun t ↦ p ≫ t) hgamma
      have hnat :
          ((eilenbergMacLaneExtensionComplex A k).XIsoOfEq hB).inv ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len =
            (eilenbergMacLaneExtensionProjectionChainMap A k).f (k + 1) ≫
              (((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A).XIsoOfEq hB).inv := by
        simpa using
          (HomologicalComplex.XIsoOfEq_inv_naturality
            (eilenbergMacLaneExtensionProjectionChainMap A k) hB).symm
      have hgamma'' :
          p ≫ ((gammaSplitting (eilenbergMacLaneExtensionComplex A k)).cofan Δ).inj B ≫ S.g =
            p ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B := by
        simpa [Category.assoc] using hgamma'
      have hstep :
          p ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B =
            ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B := by
        have hp :
            p ≫ (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len = 𝟙 _ := by
          dsimp [p]
          repeat rw [Category.assoc]
          rw [hnat]
          simp [eilenbergMacLaneExtensionProjectionChainMap, Category.assoc]
        calc
          p ≫
              (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len ≫
                ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                  B =
            (p ≫ (eilenbergMacLaneExtensionProjectionChainMap A k).f B.1.unop.len) ≫
              ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by simp [Category.assoc]
          _ = 𝟙 (SimplicialObject.Splitting.summand
                (gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).N Δ B) ≫
              ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by
                  rw [hp]
                  simp [SimplicialObject.Splitting.summand]
          _ = ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
                B := by
                  simp
      simpa [p, Category.assoc] using hgamma''.trans hstep
    · dsimp [F]
      rw [dif_neg hB]
      rw [gammaSingleCofanInj_eq_zero A (k + 1) B hB]
      exact zero_comp
  have hfinal :
      (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
          eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ) ≫
        S.g =
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B := by
    exact hcomp.trans hFg
  have hfinal' :
      (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
          eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ) ≫
        S.g =
      ((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj B ≫
        𝟙 S.X₃ := by
    exact hfinal.trans
      ((comp_id
        (((gammaSplitting ((single 𝒜 (ComplexShape.down ℕ) (k + 1)).obj A)).cofan Δ).inj
          B)).symm)
  simpa [Category.assoc] using hfinal'

-- Proof sketch: evaluate the Dold-Kan model of the extension at a simplicial degree; the
-- resulting object is a direct sum of copies of `A`, and the distinguished two-term summands
-- provide the retraction and section.
/-- After evaluating at any simplicial degree, the extension short complex carries a canonical
splitting. -/
noncomputable def eilenbergMacLaneExtensionShortComplex_termwiseSplit
    (A : 𝒜) (k : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    ((eilenbergMacLaneExtensionShortComplex A k).map ((evaluation _ _).obj Δ)).Splitting := by
  let e :=
    (((evaluation _ _).obj Δ).mapShortComplex).mapIso
      (eilenbergMacLaneExtensionModelShortComplexGammaIso A k)
  let S := (((eilenbergMacLaneExtensionModelShortComplex A k).map Γ).map
    ((evaluation _ _).obj Δ))
  have h : S.Splitting := by
    exact ShortComplex.Splitting.ofExactOfSection S
      (eilenbergMacLaneExtensionModelShortComplex_termwiseShortExact A k Δ).exact
      (eilenbergMacLaneExtensionModelShortComplex_termwiseSection A k Δ)
      (eilenbergMacLaneExtensionModelShortComplex_termwiseSection_s_g A k Δ)
      (eilenbergMacLaneExtensionModelShortComplex_termwiseShortExact A k Δ).mono_f
  exact ShortComplex.Splitting.ofIso h e

-- Proof sketch: use the constructed short complex, combine its short exactness theorem with the
-- degreewise splitting API, and package both source-facing conclusions into one textbook entry.
/-- Lemma 14.22.4: for an object `A` of an abelian category and `k ≥ 0`, the simplicial object
`eilenbergMacLaneExtension A k` fits into a short exact sequence
`0 ⟶ K(A, k) ⟶ E ⟶ K(A, k + 1) ⟶ 0`, and this sequence is term by term split exact. -/
theorem eilenbergMacLaneExtension_shortExact_and_termwiseSplit
    (A : 𝒜) (k : ℕ) :
    (eilenbergMacLaneExtensionShortComplex A k).ShortExact ∧
      ∀ Δ : SimplexCategoryᵒᵖ,
        Nonempty
          (((eilenbergMacLaneExtensionShortComplex A k).map ((evaluation _ _).obj Δ)).Splitting) := by
  constructor
  · exact eilenbergMacLaneExtensionShortComplex_shortExact A k
  · intro Δ
    exact ⟨eilenbergMacLaneExtensionShortComplex_termwiseSplit A k Δ⟩

end CategoryTheory
