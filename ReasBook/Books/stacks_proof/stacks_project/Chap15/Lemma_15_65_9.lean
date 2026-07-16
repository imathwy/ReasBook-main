import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_35_7
import stacks_proof.stacks_project.Chap15.Lemma_15_65_2
import stacks_proof.stacks_project.Chap15.Lemma_15_65_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/- Domain-style sampling for Lemma 15.65.9:
- primary domain: pseudo-coherence of bounded-above cochain complexes of `R`-modules, with the
  source-facing hypotheses stated termwise on the underlying modules;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsMPseudoCoherent`,
  `ModuleCat.IsMPseudoCoherent`,
  `CochainComplex.minus`;
- best owner abstraction: the chapter owners remain the existing predicates
  `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`; this file is the
  source-facing bridge from termwise module pseudo-coherence plus the canonical bounded-above
  owner `CochainComplex.minus (ModuleCat R) K` to those owner predicates, and should not
  introduce any extra bounded-above wrapper or parallel pseudo-coherence API;
- primitive vs. derived:
  primitive data are the cochain complex `K`, the bounded-above hypothesis
  `CochainComplex.minus (ModuleCat R) K`,
  and the degreewise module hypotheses on `K.X i`;
  derived API is the resulting owner-level pseudo-coherence of `K`;
- source/core/bridge triage:
  `source-facing`: the two theorems below about bounded-above cochain complexes with termwise
    pseudo-coherent terms;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent`, `DerivedCategory.IsPseudoCoherent`,
    `CochainComplex.IsMPseudoCoherent`, `CochainComplex.IsPseudoCoherent`, and
    `CochainComplex.minus`;
  `bridge/view`: passage from the termwise module hypotheses on `K.X i` to the cochain-complex
    owner predicates. -/

-- Proof sketch: truncate the bounded-above complex far enough above degree `m` to reduce to a
-- bounded complex, then induct on the number of nonzero terms using stupid truncation triangles.
-- Apply Lemma `15.65.2` at each step, observing that the shifted single-term complex `K.X i[-i]`
-- is `m`-pseudo-coherent exactly when `K.X i` is `(m - i)`-pseudo-coherent.
/-- Helper for Lemma 15.65.9: any zero object of `D(R)` is `m`-pseudo-coherent. -/
private theorem derived_isMPseudoCoherent_of_isZero {K : DMod} (m : ℤ)
    (hK : IsZero K) :
    K.IsMPseudoCoherent m := by
  let E0 : Cpx := 0
  let α : Q.obj E0 ⟶ K := 0
  have hzeroCpx : IsZero (0 : Cpx) := isZero_zero Cpx
  have hE0free : E0.IsTermwiseFiniteFree := by
    refine ⟨fun i ↦ ?_⟩
    let hzero : IsZero (E0.X i) := by
      simpa [E0] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero _)
    let _ : Subsingleton (((E0.X i : ModuleCat R))) := ModuleCat.subsingleton_of_isZero hzero
    let eZero :
        (((E0.X i : ModuleCat R))) ≃ₗ[R] (Fin 0 → R) :=
      LinearEquiv.ofSubsingleton _ _
    refine
      ⟨Module.Free.of_equiv eZero.symm,
        Module.Finite.of_surjective
          (0 : (Fin 0 → R) →ₗ[R] (E0.X i)) ?_⟩
    intro x
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  have hE0ge : E0.IsStrictlyGE m := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    simpa [E0] using
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
        hzeroCpx
  have hE0le : E0.IsStrictlyLE m := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simpa [E0] using
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
        hzeroCpx
  refine ⟨E0, ⟨m, m, hE0ge, hE0le⟩, hE0free, α, ?_, ?_⟩
  · intro i hi
    let hsrc : IsZero ((H i).obj (Q.obj E0)) := by
      simpa [E0] using (H i).map_isZero ((Q).map_isZero (isZero_zero _))
    let htgt : IsZero ((H i).obj K) := (H i).map_isZero hK
    -- Proof comment: both source and target homology vanish, so the comparison map is an
    -- isomorphism.
    exact hsrc.isIso htgt ((H i).map α)
  · let hsrc : IsZero ((H m).obj (Q.obj E0)) := by
      simpa [E0] using (H m).map_isZero ((Q).map_isZero (isZero_zero _))
    let htgt : IsZero ((H m).obj K) := (H m).map_isZero hK
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    -- Proof comment: the same zero-object argument makes the cutoff homology map an epimorphism.
    infer_instance

/-- Helper for Lemma 15.65.9: module-level `m`-pseudo-coherence transports across module
isomorphisms. -/
private theorem moduleCat_isMPseudoCoherent_of_iso
    {M N : ModuleCat R} (e : M ≅ N) (m : ℤ)
    (hM : M.IsMPseudoCoherent m) :
    N.IsMPseudoCoherent m := by
  -- Proof comment: the degree-zero derived embedding turns a module isomorphism into an
  -- isomorphism in `D(R)`, so the owner predicate transports directly.
  rw [ModuleCat.IsMPseudoCoherent] at hM ⊢
  exact isMPseudoCoherent_of_iso
    ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).mapIso e) m hM

/-- Helper for Lemma 15.65.9: a module that is `(m - n)`-pseudo-coherent yields an
`m`-pseudo-coherent single object in degree `n`. -/
private theorem singleFunctor_isMPseudoCoherent_of_module
    (M : ModuleCat R) (n m : ℤ)
    (hM : M.IsMPseudoCoherent (m - n)) :
    ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M).IsMPseudoCoherent m := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        (((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M)) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso n 0 n (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧).IsMPseudoCoherent (m - n) := by
    -- Proof comment: after shifting by `n`, the degree-`n` single object becomes the
    -- degree-zero single object on the same module.
    rw [ModuleCat.IsMPseudoCoherent] at hM
    exact isMPseudoCoherent_of_iso e.symm (m - n) hM
  -- Proof comment: the shift comparison from Lemma `15.65.2` translates the bound back to the
  -- original unshifted single object.
  exact
    (isMPseudoCoherent_shift_iff
      ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) n m).1 hShift

/-- Helper for Lemma 15.65.9: if `c ≤ i`, then the retained degree `i` lies in the image of the
embedding `n ↦ c + n`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (c i : ℤ) (hci : c ≤ i) :
    (ComplexShape.embeddingUpIntGE c).f (Int.toNat (i - c)) = i := by
  -- Proof comment: the integer difference `i - c` is nonnegative exactly on the retained side of
  -- the lower brutal truncation.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.65.9: in a retained degree, the lower brutal truncation term is
canonically the original term. -/
private noncomputable def lower_stupid_truncation_x_iso
    (E : Cpx) (c i : ℤ) (hci : c ≤ i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i ≅ E.X i :=
  E.stupidTruncXIso (ComplexShape.embeddingUpIntGE c)
    (embeddingUpIntGE_toNat_sub_eq c i hci)

/-- Helper for Lemma 15.65.9: the chosen proof `c ≤ i` does not affect the retained-term
identification. -/
private theorem lower_stupid_truncation_x_iso_hom_eq
    (E : Cpx) (c i : ℤ) {h h' : c ≤ i} :
    (lower_stupid_truncation_x_iso E c i h).hom =
      (lower_stupid_truncation_x_iso E c i h').hom := by
  -- Proof comment: the retained-term identification depends only on the degree, not on the proof
  -- that the degree lies above the cutoff.
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 15.65.9: transporting the lower brutal truncation differential along the
retained-term identifications recovers the original differential. -/
private theorem lower_stupid_truncation_d_via_x_iso
    (E : Cpx) (c : ℤ) {i j : ℤ}
    (hci : c ≤ i) (hcj : c ≤ j) :
    (lower_stupid_truncation_x_iso E c i hci).inv ≫
      (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
      (lower_stupid_truncation_x_iso E c j hcj).hom =
        E.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE c
  let i₀ : ℕ := Int.toNat (i - c)
  let j₀ : ℕ := Int.toNat (j - c)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq c i hci
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq c j hcj
  -- Proof comment: expose the brutal truncation as `restriction` followed by `extend`, then
  -- rewrite both differentials to the ambient complex.
  change (lower_stupid_truncation_x_iso E c i hci).inv ≫
      ((E.restriction e).extend e).d i j ≫
      (lower_stupid_truncation_x_iso E c j hcj).hom =
        E.d i j
  rw [HomologicalComplex.extend_d_eq (K := E.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := E) (e := e) hi₀ hj₀]
  simp [lower_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

/-- Helper for Lemma 15.65.9: the component maps of the canonical inclusion from the lower brutal
truncation into the original complex. -/
private noncomputable def lower_stupid_truncation_inclusion_f
    (E : Cpx) (c i : ℤ) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i ⟶ E.X i :=
  if hci : c ≤ i then
    (lower_stupid_truncation_x_iso E c i hci).hom
  else
    0

/-- Helper for Lemma 15.65.9: on retained degrees, the lower-truncation inclusion is the
transported identity map. -/
private theorem lower_stupid_truncation_inclusion_f_of_ge
    (E : Cpx) (c : ℤ) {i : ℤ} (hci : c ≤ i) :
    lower_stupid_truncation_inclusion_f E c i =
      (lower_stupid_truncation_x_iso E c i hci).hom := by
  -- Proof comment: only the retained-degree branch of the component formula survives.
  simp [lower_stupid_truncation_inclusion_f, hci]

/-- Helper for Lemma 15.65.9: on retained degrees, the lower-truncation inclusion component is an
isomorphism. -/
private theorem lower_stupid_truncation_inclusion_f_isIso_of_ge
    (E : Cpx) (c : ℤ) {i : ℤ} (hci : c ≤ i) :
    IsIso (lower_stupid_truncation_inclusion_f E c i) := by
  -- Proof comment: in a retained degree, the inclusion component is exactly the retained-term
  -- identification.
  rw [lower_stupid_truncation_inclusion_f_of_ge E c hci]
  infer_instance

/-- Helper for Lemma 15.65.9: the canonical lower-truncation inclusion is a chain map. -/
private theorem lower_stupid_truncation_inclusion_comm
    (E : Cpx) (c : ℤ) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      lower_stupid_truncation_inclusion_f E c i ≫ E.d i j =
        (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
          lower_stupid_truncation_inclusion_f E c j := by
  intro i j hij
  by_cases hci : c ≤ i
  · have hcj : c ≤ j := by
      have hij' : j = i + 1 := by
        simpa [ComplexShape.up, eq_comm] using hij
      omega
    -- Proof comment: once both degrees are retained, the inclusion square becomes the original
    -- differential square after transporting through the retained-term identifications.
    rw [lower_stupid_truncation_inclusion_f_of_ge E c hci,
      lower_stupid_truncation_inclusion_f_of_ge E c hcj]
    calc
      (lower_stupid_truncation_x_iso E c i hci).hom ≫ E.d i j =
          (lower_stupid_truncation_x_iso E c i hci).hom ≫
            ((lower_stupid_truncation_x_iso E c i hci).inv ≫
              (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
                (lower_stupid_truncation_x_iso E c j hcj).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hci hcj]
      _ = (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
            (lower_stupid_truncation_x_iso E c j hcj).hom := by
              simp [Category.assoc]
  · have hzero :
        IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      -- Proof comment: below the cutoff, the lower brutal truncation vanishes by construction.
      exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci)
    by_cases hcj : c ≤ j
    · have hsrczero :
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j = 0 :=
        hzero.eq_of_src ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j) 0
      simp [lower_stupid_truncation_inclusion_f, hci, hcj, hsrczero]
    · simp [lower_stupid_truncation_inclusion_f, hci, hcj]

/-- Helper for Lemma 15.65.9: the lower brutal truncation carries its canonical inclusion into
the ambient complex. -/
private noncomputable def lower_stupid_truncation_inclusion
    (E : Cpx) (c : ℤ) :
    E.stupidTrunc (ComplexShape.embeddingUpIntGE c) ⟶ E :=
  { f := fun i ↦ lower_stupid_truncation_inclusion_f E c i
    comm' := lower_stupid_truncation_inclusion_comm E c }

/-- Helper for Lemma 15.65.9: the predecessor in the cochain shape is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.65.9: the successor in the cochain shape is `i + 1`. -/
private theorem cochain_next_eq (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 :=
  ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.65.9: above the cutoff, the first object of the lower brutal truncation
short complex identifies with the original first object. -/
private noncomputable def lower_stupid_truncation_sc_X₁_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₁ ≅ (E.sc i).X₁ :=
  lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i)
    (by
      have hi_prev : c ≤ i - 1 := by omega
      simpa [cochain_prev_eq i] using hi_prev)

/-- Helper for Lemma 15.65.9: above the cutoff, the middle object of the lower brutal truncation
short complex identifies with the original middle object. -/
private noncomputable def lower_stupid_truncation_sc_X₂_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₂ ≅ (E.sc i).X₂ := by
  -- Proof comment: the middle object is exactly the retained degree-`i` term.
  have hmid : c ≤ i := by omega
  simpa [HomologicalComplex.sc] using lower_stupid_truncation_x_iso E c i hmid

/-- Helper for Lemma 15.65.9: above the cutoff, the third object of the lower brutal truncation
short complex identifies with the original third object. -/
private noncomputable def lower_stupid_truncation_sc_X₃_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₃ ≅ (E.sc i).X₃ :=
  lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i)
    (by
      have hi_next : c ≤ i + 1 := by omega
      simpa [cochain_next_eq i] using hi_next)

/-- Helper for Lemma 15.65.9: above the cutoff, the first square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_f_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom ≫ (E.sc i).f =
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).f ≫
        (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom := by
  have hi_prev : c ≤ (ComplexShape.up ℤ).prev i := by
    rw [cochain_prev_eq i]
    omega
  have hi_mid : c ≤ i := by
    omega
  have hX₁ :
      (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom := by
    exact lower_stupid_truncation_x_iso_hom_eq E c ((ComplexShape.up ℤ).prev i)
  have hX₂ :
      (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c i hi_mid).hom := by
    have hmid' : c ≤ i := by omega
    exact lower_stupid_truncation_x_iso_hom_eq E c i (h := hmid') (h' := hi_mid)
  rw [hX₁, hX₂]
  -- Proof comment: after transport, the left short-complex map is the predecessor differential.
  calc
    (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom ≫
        E.d ((ComplexShape.up ℤ).prev i) i =
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom ≫
        ((lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d ((ComplexShape.up ℤ).prev i) i ≫
            (lower_stupid_truncation_x_iso E c i hi_mid).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hi_prev hi_mid]
    _ = ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).f ≫
          (lower_stupid_truncation_x_iso E c i hi_mid).hom := by
            simp [HomologicalComplex.sc]

/-- Helper for Lemma 15.65.9: above the cutoff, the second square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_g_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom ≫ (E.sc i).g =
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).g ≫
        (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom := by
  have hi_mid : c ≤ i := by
    omega
  have hi_next : c ≤ (ComplexShape.up ℤ).next i := by
    rw [cochain_next_eq i]
    omega
  have hX₂ :
      (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c i hi_mid).hom := by
    have hmid' : c ≤ i := by omega
    exact lower_stupid_truncation_x_iso_hom_eq E c i (h := hmid' ) (h' := hi_mid)
  have hX₃ :
      (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom := by
    exact lower_stupid_truncation_x_iso_hom_eq E c ((ComplexShape.up ℤ).next i)
  rw [hX₂, hX₃]
  -- Proof comment: after transport, the right short-complex map is the successor differential.
  calc
    (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
        E.d i ((ComplexShape.up ℤ).next i) =
      (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
        ((lower_stupid_truncation_x_iso E c i hi_mid).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i ((ComplexShape.up ℤ).next i) ≫
            (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hi_mid hi_next]
    _ = ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).g ≫
          (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom := by
            simp [HomologicalComplex.sc]

/-- Helper for Lemma 15.65.9: above the cutoff, the lower brutal truncation and the ambient
complex have canonically isomorphic degree-`i` short complexes. -/
private noncomputable def lower_stupid_truncation_sc_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i ≅ E.sc i :=
  ShortComplex.isoMk
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_f_comm_of_gt E c i hci)
    (lower_stupid_truncation_sc_g_comm_of_gt E c i hci)

/-- Helper for Lemma 15.65.9: above the cutoff, the lower brutal truncation inclusion induces an
isomorphism on cochain homology. -/
private theorem homologyMap_lower_stupid_truncation_inclusion_isIso_above
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    IsIso (HomologicalComplex.homologyMap (lower_stupid_truncation_inclusion E c) i) := by
  let φ :
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i) ⟶ E.sc i :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map
      (lower_stupid_truncation_inclusion E c))
  have hi_prev : c ≤ i - 1 := by omega
  have hi_mid : c ≤ i := by omega
  have hi_next : c ≤ i + 1 := by omega
  have hφ : φ = (lower_stupid_truncation_sc_iso_of_gt E c i hci).hom := by
    -- Proof comment: all three components are the retained-degree inclusion maps.
    ext
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₁_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge, hi_prev]
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₂_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge, hi_mid]
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₃_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge, hi_next]
  -- Proof comment: transport invertibility along the canonical short-complex isomorphism.
  change IsIso (CategoryTheory.ShortComplex.homologyMap φ)
  rw [hφ]
  exact
    (show IsIso
      (CategoryTheory.ShortComplex.homologyMap
        (lower_stupid_truncation_sc_iso_of_gt E c i hci).hom) by
          infer_instance)

/-- Helper for Lemma 15.65.9: at the cutoff degree, the lower brutal truncation inclusion induces
an epimorphism on cycles. -/
private theorem lower_stupid_truncation_cyclesMap_epi_at_cutoff
    (E : Cpx) (c : ℤ) :
    Epi (HomologicalComplex.cyclesMap (lower_stupid_truncation_inclusion E c) c) := by
  change Epi
    (ShortComplex.cyclesMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
        (lower_stupid_truncation_inclusion E c)))
  let φ :
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc c) ⟶ E.sc c :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
      (lower_stupid_truncation_inclusion E c))
  have hcc : c ≤ c := by simp
  have hτ₂ : IsIso φ.τ₂ := by
    -- Proof comment: degree `c` itself is retained by the lower brutal truncation.
    simpa [φ, HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge] using
      (lower_stupid_truncation_inclusion_f_isIso_of_ge E c hcc)
  have hcnext : c ≤ (ComplexShape.up ℤ).next c := by
    rw [cochain_next_eq c]
    omega
  have hτ₃ : IsIso φ.τ₃ := by
    -- Proof comment: degree `c + 1` is retained as well, so the right component is an isomorphism.
    simpa [φ, HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge, ComplexShape.up]
      using (lower_stupid_truncation_inclusion_f_isIso_of_ge E c hcnext)
  letI : IsIso φ.τ₂ := hτ₂
  letI : Mono φ.τ₃ := by infer_instance
  letI : IsIso (ShortComplex.cyclesMap φ) := by infer_instance
  infer_instance

/-- Helper for Lemma 15.65.9: at the cutoff degree, the lower brutal truncation inclusion induces
an epimorphism on homology. -/
private theorem homologyMap_lower_stupid_truncation_inclusion_epi_at_cutoff
    (E : Cpx) (c : ℤ) :
    Epi (HomologicalComplex.homologyMap (lower_stupid_truncation_inclusion E c) c) := by
  -- Proof comment: descend the cycles epimorphism through the canonical homology quotient.
  simpa [HomologicalComplex.homologyMap, HomologicalComplex.cyclesMap] using
    (ShortComplex.epi_homologyMap_of_epi_cyclesMap'
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
        (lower_stupid_truncation_inclusion E c))
      (show Epi
        (ShortComplex.cyclesMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
            (lower_stupid_truncation_inclusion E c))) by
          simpa [HomologicalComplex.cyclesMap] using
            lower_stupid_truncation_cyclesMap_epi_at_cutoff (R := R) E c))

/-- Helper for Lemma 15.65.9: the lower brutal truncation is concentrated in degrees `≥ c`. -/
private theorem lower_stupid_truncation_isStrictlyGE
    (E : Cpx) (c : ℤ) :
    CochainComplex.IsStrictlyGE ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) c := by
  -- Proof comment: every degree below the cutoff vanishes by construction of the lower brutal
  -- truncation.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i
    (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi)

/-- Helper for Lemma 15.65.9: a lower brutal truncation inherits any upper support bound from the
ambient complex. -/
private theorem lower_stupid_truncation_isStrictlyLE
    (E : Cpx) (c b : ℤ) [E.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) b := by
  -- Proof comment: above the ambient upper bound, the retained terms are canonically those of
  -- the original complex, hence still zero.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hci : c ≤ i
  · let hEi : IsZero (E.X i) := E.isZero_of_isStrictlyLE b i hi
    exact hEi.of_iso (lower_stupid_truncation_x_iso E c i hci)
  · exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i
      (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci)

/-- Helper for Lemma 15.65.9: if the lower brutal truncation at degree `m - 1` is
`m`-pseudo-coherent, then the original complex is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_stupidTruncGE
    (K : Cpx) (m : ℤ)
    (htrunc :
      CochainComplex.IsMPseudoCoherent
        ((K.stupidTrunc (ComplexShape.embeddingUpIntGE (m - 1)) : Cpx)) m) :
    K.IsMPseudoCoherent m := by
  rcases htrunc with ⟨E, hEbounds, hEfree, α, hαgt, hαm⟩
  let β : Q.obj
        ((K.stupidTrunc (ComplexShape.embeddingUpIntGE (m - 1)) : Cpx)) ⟶
          Q.obj K :=
    Q.map (lower_stupid_truncation_inclusion K (m - 1))
  refine ⟨E, hEbounds, hEfree, α ≫ β, ?_, ?_⟩
  · intro i hi
    have hβi_chain :
        IsIso (HomologicalComplex.homologyMap
          (lower_stupid_truncation_inclusion K (m - 1)) i) := by
      have hcut : m - 1 < i := by omega
      exact homologyMap_lower_stupid_truncation_inclusion_isIso_above K (m - 1) i hcut
    have hβi : IsIso ((H i).map β) := by
      exact
        (homologyMap_isIso_iff_homologyFunctor_map_Q_isIso
          (R := R) (lower_stupid_truncation_inclusion K (m - 1)) i).1 hβi_chain
    letI : IsIso ((H i).map α) := hαgt i hi
    letI : IsIso ((H i).map β) := hβi
    -- Proof comment: above degree `m`, both the original witness and the truncation comparison
    -- are homology isomorphisms, so their composite is too.
    simpa [β, Functor.map_comp] using
      (show IsIso ((H i).map α ≫ (H i).map β) by infer_instance)
  · have hβm_chain :
      IsIso (HomologicalComplex.homologyMap
        (lower_stupid_truncation_inclusion K (m - 1)) m) := by
      have hcut : m - 1 < m := by omega
      exact homologyMap_lower_stupid_truncation_inclusion_isIso_above K (m - 1) m hcut
    have hβmIso : IsIso ((H m).map β) := by
      exact
        (homologyMap_isIso_iff_homologyFunctor_map_Q_isIso
          (R := R) (lower_stupid_truncation_inclusion K (m - 1)) m).1 hβm_chain
    letI : Epi ((H m).map α) := hαm
    letI : IsIso ((H m).map β) := hβmIso
    -- Proof comment: at degree `m`, the truncation comparison stays epi and preserves the
    -- witness epimorphism.
    simpa [β, Functor.map_comp] using
      (show Epi ((H m).map α ≫ (H m).map β) by infer_instance)

/-- Helper for Lemma 15.65.9: after shifting back the smaller brutal stage, the termwise
`(m - i)`-pseudo-coherence hypotheses restrict to the tail interval `[c + 1, d]`. -/
private theorem shifted_brutal_stage_shift_back_termwise_isMPseudoCoherent
    {L : Cpx} {c d m : ℤ} {n : ℕ}
    (hn : Int.toNat (d - c) = n + 1)
    (hterm :
      ∀ i : Set.Icc c d, (L.X i.1).IsMPseudoCoherent (m - i.1)) :
    ∀ i : Set.Icc (c + 1) d,
      ((shifted_brutal_left_stage (A := ModuleCat R) (L⟦d⟧) n)⟦-d⟧).X i.1 |>.IsMPseudoCoherent
        (m - i.1) := by
  have hcd : c ≤ d := by
    by_contra hcd
    have hnonpos : d - c ≤ 0 := by omega
    rw [Int.toNat_of_nonpos hnonpos] at hn
    omega
  have hwidth : d - c = ((n + 1 : ℕ) : ℤ) := by
    rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hcd)]
    exact congrArg (fun k : ℕ ↦ (k : ℤ)) hn
  have hc1 : c + 1 = d - (n : ℤ) := by
    omega
  intro i
  have hi_stage : -((n : ℕ) : ℤ) ≤ i.1 - d := by
    simpa [hc1] using i.2.1
  have hi_nonneg : 0 ≤ i.1 - d + (n : ℤ) := by
    omega
  have hShiftObj : i.1 + -d = i.1 - d := by
    omega
  have hShiftTerm : i.1 = i.1 - d + d := by
    omega
  let eShift :
      (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦d⟧) n)⟦-d⟧).X i.1) ≅
        (shifted_brutal_left_stage (A := ModuleCat R) (L⟦d⟧) n).X (i.1 - d) :=
    (shifted_brutal_left_stage (A := ModuleCat R) (L⟦d⟧) n).shiftFunctorObjXIso
      (-d) i.1 (i.1 - d) hShiftObj
  let eStage :
      (shifted_brutal_left_stage (A := ModuleCat R) (L⟦d⟧) n).X (i.1 - d) ≅
        (L⟦d⟧).X (i.1 - d) :=
    (L⟦d⟧).stupidTruncXIso (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) (by
      refine Eq.symm ?_
      dsimp [ComplexShape.embeddingUpIntGE]
      rw [Int.toNat_of_nonneg hi_nonneg]
      omega)
  let eTerm :
      (L⟦d⟧).X (i.1 - d) ≅ L.X i.1 :=
    L.shiftFunctorObjXIso d (i.1 - d) i.1 hShiftTerm
  let eModule :
      (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦d⟧) n)⟦-d⟧).X i.1) ≅ L.X i.1 :=
    eShift ≪≫ eStage ≪≫ eTerm
  have hci : c ≤ i.1 := by
    omega
  have hOrig : (L.X i.1).IsMPseudoCoherent (m - i.1) := hterm ⟨i.1, ⟨hci, i.2.2⟩⟩
  -- Proof comment: the shifted-back smaller brutal stage has the same degree-`i` term as `L`.
  exact moduleCat_isMPseudoCoherent_of_iso (R := R) eModule.symm (m - i.1) hOrig

/-- Helper for Lemma 15.65.9: a strictly bounded representative whose degree-`i` term is
`(m - i)`-pseudo-coherent is itself `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_strict_bounds_of_termwise
    (m : ℤ) :
    ∀ n : ℕ, ∀ {c d : ℤ} (L : Cpx),
      Int.toNat (d - c) = n →
      L.IsStrictlyGE c →
      L.IsStrictlyLE d →
      (∀ i : Set.Icc c d, (L.X i.1).IsMPseudoCoherent (m - i.1)) →
      L.IsMPseudoCoherent m := by
  intro n
  induction n with
  | zero =>
      intro c d L hn hGE hLE hterm
      by_cases hcd : c ≤ d
      · have hdc : d ≤ c := by
          have hsub : d - c = 0 := by
            calc
              d - c = (Int.toNat (d - c) : ℤ) := by
                symm
                exact Int.toNat_of_nonneg (sub_nonneg.mpr hcd)
              _ = 0 := by
                simpa using congrArg (fun k : ℕ ↦ (k : ℤ)) hn
          omega
        have hdc_eq : d = c := by
          omega
        subst d
        letI : L.IsStrictlyGE c := hGE
        letI : L.IsStrictlyLE c := hLE
        let eSingle : Q.obj L ≅ (DerivedCategory.singleFunctor (ModuleCat R) c).obj (L.X c) :=
          representative_single_iso_of_strict_bounds (A := ModuleCat R) L c
        have hsingle :
            ((DerivedCategory.singleFunctor (ModuleCat R) c).obj (L.X c)).IsMPseudoCoherent m := by
          -- Proof comment: a singleton-support complex is exactly the shifted single object on its
          -- unique surviving term.
          exact singleFunctor_isMPseudoCoherent_of_module (L.X c) c m (hterm ⟨c, by simp⟩)
        exact isMPseudoCoherent_of_iso eSingle.symm m hsingle
      · have hlt : d < c := by
          omega
        letI : L.IsStrictlyLE d := hLE
        letI : L.IsStrictlyGE c := hGE
        letI : (Q.obj L).IsLE d := by
          rw [DerivedCategory.isLE_Q_obj_iff]
          infer_instance
        letI : (Q.obj L).IsGE c := by
          rw [DerivedCategory.isGE_Q_obj_iff]
          infer_instance
        -- Proof comment: if the support interval is empty, the derived object is zero.
        exact derived_isMPseudoCoherent_of_isZero (R := R) m (t.isZero (Q.obj L) d c hlt)
  | succ n ih =>
      intro c d L hn hGE hLE hterm
      have hcd : c ≤ d := by
        by_contra hcd
        have hnonpos : d - c ≤ 0 := by
          omega
        have hzero : Int.toNat (d - c) = 0 := by
          rw [Int.toNat_of_nonpos hnonpos]
        omega
      have hwidth : d - c = ((n + 1 : ℕ) : ℤ) := by
        rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hcd)]
        exact congrArg (fun k : ℕ ↦ (k : ℤ)) hn
      have hc1 : c + 1 = d - (n : ℤ) := by
        omega
      have hn' : Int.toNat (d - (c + 1)) = n := by
        rw [show d - (c + 1) = (n : ℤ) by omega]
        simp
      let K : Cpx := L⟦d⟧
      let L1 : Cpx := (shifted_brutal_left_stage (A := ModuleCat R) K n)⟦-d⟧
      have hKGE : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := by
        simpa [K] using
          shifted_representative_isStrictlyGE_left_endpoint (A := ModuleCat R)
            (L := L) (a := c) (b := d) (n := n) hn hGE
      have hKLE : K.IsStrictlyLE 0 := by
        simpa [K] using
          shifted_representative_isStrictlyLE_zero (A := ModuleCat R) (L := L) (b := d) hLE
      have hL1GE : L1.IsStrictlyGE (c + 1) := by
        letI : K.IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := hKGE
        letI : (shifted_brutal_left_stage (A := ModuleCat R) K n).IsStrictlyGE
            (-((n : ℕ) : ℤ)) := inferInstance
        simpa [L1, hc1] using
          CochainComplex.isStrictlyGE_shift
            (K := shifted_brutal_left_stage (A := ModuleCat R) K n)
            (-((n : ℕ) : ℤ)) (-d) (c + 1) (by omega)
      have hL1LE : L1.IsStrictlyLE d := by
        letI : K.IsStrictlyLE 0 := hKLE
        letI : (shifted_brutal_left_stage (A := ModuleCat R) K n).IsStrictlyLE 0 := inferInstance
        simpa [L1] using
          CochainComplex.isStrictlyLE_shift
            (K := shifted_brutal_left_stage (A := ModuleCat R) K n)
            0 (-d) d (by omega)
      have hL1Terms :
          ∀ i : Set.Icc (c + 1) d, (L1.X i.1).IsMPseudoCoherent (m - i.1) := by
        -- Proof comment: the smaller brutal stage inherits the tail interval hypotheses.
        simpa [L1] using
          shifted_brutal_stage_shift_back_termwise_isMPseudoCoherent
            (R := R) (L := L) (c := c) (d := d) (m := m) (n := n) hn hterm
      have hIH : L1.IsMPseudoCoherent m := by
        -- Proof comment: apply the induction hypothesis to the shorter interval `[c + 1, d]`.
        exact ih (c := c + 1) (d := d) L1 hn' hL1GE hL1LE hL1Terms
      let S :=
        (shifted_brutal_left_stage_short_complex_sign_corrected (A := ModuleCat R) K n).map
          (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat R) ℤ) (-d))
      have hS : S.ShortExact := by
        -- Proof comment: the brutal-stage short exact sequence remains short exact after shifting.
        exact
          (shifted_brutal_left_stage_short_exact_sign_corrected (A := ModuleCat R) K n).map_of_exact
            (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat R) ℤ) (-d))
      let T : Triangle DMod :=
        Triangle.mk (Q.map S.f) (Q.map S.g) (DerivedCategory.triangleOfSESδ hS)
      have hT : T ∈ distTriang DMod := by
        simpa [T] using DerivedCategory.triangleOfSES_distinguished hS
      have h₁ : T.obj₁.IsMPseudoCoherent m := by
        simpa [T, S, L1] using hIH
      have hcc : c ∈ Set.Icc c d := by
        exact ⟨le_rfl, hcd⟩
      have h₃ : T.obj₃.IsMPseudoCoherent m := by
        let eQuot :
            Q.obj S.X₃ ≅ (DerivedCategory.singleFunctor (ModuleCat R) c).obj (L.X c) := by
          dsimp [S, K, shifted_brutal_left_stage_short_complex_sign_corrected]
          exact
            shifted_brutal_single_shift_back_iso (A := ModuleCat R)
              (L := L) (a := c) (b := d) (n := n) hn
        have hQuot :
            ((DerivedCategory.singleFunctor (ModuleCat R) c).obj (L.X c)).IsMPseudoCoherent m := by
          exact singleFunctor_isMPseudoCoherent_of_module (L.X c) c m (hterm ⟨c, hcc⟩)
        -- Proof comment: the quotient term is the leftmost surviving degree of `L`.
        exact isMPseudoCoherent_of_iso eQuot.symm m hQuot
      have h₂ : T.obj₂.IsMPseudoCoherent m :=
        isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT h₁ h₃
      let eMid :
          Q.obj S.X₂ ≅ Q.obj L := by
        let eStage : S.X₂ ≅ L := by
          dsimp [S, L1, K, shifted_brutal_left_stage_short_complex_sign_corrected]
          exact
            ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat R) ℤ) (-d)).mapIso
              (shifted_brutal_full_stage_iso_of_isStrictlyGE (A := ModuleCat R) K n)).trans
              (shiftShiftNeg L d)
        exact Q.mapIso eStage
      -- Proof comment: replace the middle brutal stage by the original representative.
      exact isMPseudoCoherent_of_iso eMid m h₂

/-- Lemma 15.65.9: a bounded-above cochain complex of `R`-modules whose term in degree `i` is
`(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
@[stacks 064Y]
theorem isMPseudoCoherent_of_boundedAbove_of_termwise
    (K : Cpx) (m : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsMPseudoCoherent (m - i)) :
    K.IsMPseudoCoherent m := by
  obtain ⟨d, hLE⟩ := (CochainComplex.minus_iff (ModuleCat R) K).1 hbounded
  let T : Cpx := K.stupidTrunc (ComplexShape.embeddingUpIntGE (m - 1))
  have hTGE : T.IsStrictlyGE (m - 1) := by
    simpa [T] using lower_stupid_truncation_isStrictlyGE (R := R) K (m - 1)
  have hTLE : T.IsStrictlyLE d := by
    letI : K.IsStrictlyLE d := hLE
    simpa [T] using lower_stupid_truncation_isStrictlyLE (R := R) K (m - 1) d
  have hTterm :
      ∀ i : Set.Icc (m - 1) d, (T.X i.1).IsMPseudoCoherent (m - i.1) := by
    intro i
    let e : (T.X i.1) ≅ K.X i.1 := by
      dsimp [T]
      exact K.stupidTruncXIso (ComplexShape.embeddingUpIntGE (m - 1))
        (embeddingUpIntGE_toNat_sub_eq (m - 1) i.1 i.2.1)
    -- Proof comment: every retained term of the lower brutal truncation is canonically the
    -- original term in the same degree, so the interval hypothesis comes directly from `hterm`.
    exact moduleCat_isMPseudoCoherent_of_iso (R := R) e.symm (m - i.1) (hterm i.1)
  have hT : T.IsMPseudoCoherent m := by
    -- Proof comment: once the bounded-above complex is truncated below `m - 1`, it becomes
    -- bounded and the brutal-stage induction applies on the finite support interval `[m - 1, d]`.
    exact isMPseudoCoherent_of_strict_bounds_of_termwise (R := R) m
      (Int.toNat (d - (m - 1))) (c := m - 1) (d := d) T rfl hTGE hTLE hTterm
  -- Proof comment: the lower brutal truncation agrees with the original complex on cohomology in
  -- every degree `≥ m`, so the `m`-pseudo-coherent witness lifts back to `K`.
  exact isMPseudoCoherent_of_stupidTruncGE (R := R) K m hT

-- Proof sketch: rewrite module pseudo-coherence as the statement that the degree-zero derived
-- object is `a`-pseudo-coherent for every `a`, then specialize the universal statement.
/-- Helper for Lemma 15.65.9: a pseudo-coherent `R`-module is `a`-pseudo-coherent for every
integer `a`. -/
private theorem module_isMPseudoCoherent_of_isPseudoCoherent_local
    (M : ModuleCat R) (a : ℤ) (hM : M.IsPseudoCoherent) :
    M.IsMPseudoCoherent a := by
  -- Proof comment: `Lemma 15.65.6` is the canonical bridge from total pseudo-coherence to all
  -- fixed-degree pseudo-coherence statements.
  rw [ModuleCat.IsPseudoCoherent, CategoryTheory.isPseudoCoherent_iff_forall_isMPseudoCoherent] at hM
  simpa [ModuleCat.IsMPseudoCoherent] using hM a

-- Proof sketch: for each fixed `m`, use the first theorem and the hypothesis that every term of
-- `K` is pseudo-coherent, hence `(m - i)`-pseudo-coherent for every `i`, and then invoke Lemma
-- `15.65.5` to pass from `m`-pseudo-coherence for all `m` to pseudo-coherence.
/-- A bounded-above cochain complex of pseudo-coherent `R`-modules is pseudo-coherent. -/
theorem isPseudoCoherent_of_boundedAbove_of_termwise
    (K : Cpx)
    (hbounded : CochainComplex.minus (ModuleCat R) K)
    (hterm : ∀ i : ℤ, (K.X i).IsPseudoCoherent) :
    K.IsPseudoCoherent := by
  -- Route correction: use the canonical bridge from Lemma `15.65.6` rather than rebuilding a
  -- local cochain-level TFAE argument in this file.
  rw [CochainComplex.IsPseudoCoherent, CategoryTheory.isPseudoCoherent_iff_forall_isMPseudoCoherent]
  intro m
  -- Proof comment: the fixed-`m` theorem proved above is exactly the source argument for the
  -- first sentence of the lemma, once each term hypothesis is specialized to `m - i`.
  refine isMPseudoCoherent_of_boundedAbove_of_termwise K m hbounded ?_
  intro i
  exact module_isMPseudoCoherent_of_isPseudoCoherent_local (R := R) (K.X i) (m - i) (hterm i)

end

end CochainComplex
