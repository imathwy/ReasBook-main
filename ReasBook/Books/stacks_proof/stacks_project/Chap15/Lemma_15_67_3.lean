import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Projective
import StacksProject_2024.Chap13.Lemma_13_15_5
import StacksProject_2024.Chap13.Lemma_13_19_3
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open DerivedCategory
open DerivedCategory.TStructure
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Q" => DerivedCategory.Q
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
private abbrev zeroCpx : Cpx := HomologicalComplex.zero

/- Domain-style sampling:
- primary domain: tor-amplitude in the derived category of modules, expressed through bounded flat
  cochain representatives;
- sampled owner declarations:
  `CategoryTheory.HasTorAmplitudeIn`,
  `CochainComplex.IsTermwiseFlat`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.HasInjectiveAmplitudeIn`;
- best owner abstraction: `HasTorAmplitudeIn` is the source-facing/core predicate in this chapter,
  while existence of a bounded flat representative is bridge data describing that owner through a
  concrete model in `CochainComplex (ModuleCat R) ℤ`;
- primitive data: the representative complex `E`, its support conditions `E.IsStrictlyGE a` and
  `E.IsStrictlyLE b`, its termwise flatness `E.IsTermwiseFlat`, and an isomorphism
  `K ≅ DerivedCategory.Q.obj E`;
- derived API: the existential representative criterion for `HasTorAmplitudeIn`. The flat
  representative data should not be promoted to a parallel public owner, since the chapter already
  organizes the domain around tor-amplitude/projective-amplitude/injective-amplitude predicates.

Source/core/bridge triage:
- `source-facing`: tor-amplitude in `[a, b]` for an object of `D(R)`;
- `core/canonical`: `HasTorAmplitudeIn`;
- `bridge/view`: existence of a bounded termwise-flat cochain representative.
-/

-- Proof sketch: for the forward implication, use the tor-amplitude hypothesis together with the
-- bounded-above replacement from Derived Categories, Lemma `13.19.3`, then truncate below `a`
-- and apply Lemma `15.67.2` to identify the new degree-`a` term as flat. For the reverse
-- implication, compute derived tensor products using the flat representative and read off the
-- vanishing of homology outside `[a, b]` from the strict support of the representative complex.
/-- Helper for Lemma 15.67.3: tor-amplitude in a fixed interval is invariant under isomorphism in
`D(R)`. -/
lemma hasTorAmplitudeIn_of_iso_local {K L : DMod} {a b : ℤ} (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro h M i hi
    -- Proof comment: transport the test homology object along the induced derived-tensor
    -- isomorphism.
    exact
      (h M i hi).of_iso
        ((H i).mapIso ((derivedTensorProduct ((single₀).obj M)).mapIso e.symm))
  · intro h M i hi
    -- Proof comment: the converse direction uses the inverse derived-tensor transport.
    exact
      (h M i hi).of_iso
        ((H i).mapIso ((derivedTensorProduct ((single₀).obj M)).mapIso e))

/-- Helper for Lemma 15.67.3: tensoring with the degree-zero complex on `R` is canonically the
identity on `D(R)`. -/
noncomputable def regular_single0_derivedTensor_iso_local
    (L : DMod) :
    L ⊗[R]^L (single₀).obj (ModuleCat.of R R) ≅ L := by
  let eUnit :
      (single₀).obj (ModuleCat.of R R) ≅ 𝟙_ DMod :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
        (ModuleCat.of R R)) ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
            (ModuleCat.of R R))).symm
  -- Proof comment: commute the derived tensor factors, identify the right factor with the tensor
  -- unit, and then apply the left unitor.
  exact
    (derivedTensorProduct_comm L ((single₀).obj (ModuleCat.of R R))) ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        ((single₀).obj (ModuleCat.of R R)) L).symm ≪≫
        whiskerRightIso eUnit L ≪≫
          λ_ L

/-- Helper for Lemma 15.67.3: testing tor-amplitude against the tensor unit detects the vanishing
of the chosen representative homology above `b`. -/
lemma obj_preimage_homology_isZero_of_hasTorAmplitudeIn_above
    (K : DMod) (a b i : ℤ) (hK : HasTorAmplitudeIn K a b) (hi : b < i) :
    IsZero ((DerivedCategory.Q.objPreimage K).homology i) := by
  have hzero_tensor :
      IsZero ((H i).obj (K ⊗[R]^L (single₀).obj (ModuleCat.of R R))) := by
    -- Proof comment: degrees above `b` lie outside the test interval `[a, b]`.
    exact hK (ModuleCat.of R R) i (by
      intro hmem
      exact (not_lt_of_ge hmem.2 hi).elim)
  have hzero_K : IsZero ((H i).obj K) :=
    hzero_tensor.of_iso
      ((H i).mapIso (regular_single0_derivedTensor_iso_local (R := R) K).symm)
  have hzero_Qpre : IsZero ((H i).obj (Q.obj (DerivedCategory.Q.objPreimage K))) :=
    hzero_K.of_iso ((H i).mapIso (DerivedCategory.Q.objObjPreimageIso K))
  -- Proof comment: compute the chosen representative homology via `homologyFunctorFactors`.
  exact
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      (DerivedCategory.Q.objPreimage K)).isZero_iff.1 hzero_Qpre

/-- Helper for Lemma 15.67.3: testing tor-amplitude against the tensor unit also detects the
vanishing of the homology of `K` itself below the lower bound. -/
lemma homology_isZero_of_hasTorAmplitudeIn_below
    (K : DMod) (a b i : ℤ) (hK : HasTorAmplitudeIn K a b) (hi : i < a) :
    IsZero ((H i).obj K) := by
  have hzero_tensor :
      IsZero ((H i).obj (K ⊗[R]^L (single₀).obj (ModuleCat.of R R))) := by
    -- Proof comment: degrees below `a` lie outside the interval `[a, b]`.
    exact hK (ModuleCat.of R R) i (by
      intro hmem
      exact (not_lt_of_ge hmem.1 hi).elim)
  -- Proof comment: tensoring with `R[0]` is the identity, so the test homology is just `H^i(K)`.
  exact hzero_tensor.of_iso
    ((H i).mapIso (regular_single0_derivedTensor_iso_local (R := R) K).symm)

/-- Helper for Lemma 15.67.3: testing tor-amplitude against the tensor unit detects the vanishing
of the homology of `K` itself above the upper bound. -/
lemma homology_isZero_of_hasTorAmplitudeIn_above
    (K : DMod) (a b i : ℤ) (hK : HasTorAmplitudeIn K a b) (hi : b < i) :
    IsZero ((H i).obj K) := by
  have hzero_tensor :
      IsZero ((H i).obj (K ⊗[R]^L (single₀).obj (ModuleCat.of R R))) := by
    -- Proof comment: degrees above `b` also lie outside the test interval.
    exact hK (ModuleCat.of R R) i (by
      intro hmem
      exact (not_lt_of_ge hmem.2 hi).elim)
  -- Proof comment: again identify tensoring with `R[0]` with the identity functor.
  exact hzero_tensor.of_iso
    ((H i).mapIso (regular_single0_derivedTensor_iso_local (R := R) K).symm)

/-- Helper for Lemma 15.67.3: the chosen representative of `K` has no homology below `a` when
`K` has tor-amplitude in `[a, b]`. -/
lemma obj_preimage_homology_isZero_of_hasTorAmplitudeIn_below
    (K : DMod) (a b i : ℤ) (hK : HasTorAmplitudeIn K a b) (hi : i < a) :
    IsZero ((DerivedCategory.Q.objPreimage K).homology i) := by
  have hzero_K : IsZero ((H i).obj K) :=
    homology_isZero_of_hasTorAmplitudeIn_below (R := R) K a b i hK hi
  have hzero_Qpre : IsZero ((H i).obj (Q.obj (DerivedCategory.Q.objPreimage K))) :=
    hzero_K.of_iso ((H i).mapIso (DerivedCategory.Q.objObjPreimageIso K))
  -- Proof comment: compute homology on the chosen representative through `homologyFunctorFactors`.
  exact
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      (DerivedCategory.Q.objPreimage K)).isZero_iff.1 hzero_Qpre

/-- Helper for Lemma 15.67.3: on the retained range, the lower-truncation embedding
`n ↦ a + n` hits the original degree. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: the lower-truncation embedding is affine on the surviving indices.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.67.3: above the cutoff, smart lower truncation keeps the original term. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : Cpx) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n := by
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n :=
    embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  -- Proof comment: the core truncation API gives the surviving term isomorphism once the retained
  -- index and the non-boundary condition are identified.
  exact K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.67.3: smart lower truncation of a bounded-above complex remains bounded
above. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE_local
    (K : Cpx) (a b : ℤ) (ha_le_b : a ≤ b) (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE b := by
  -- Proof comment: for `n > b`, the truncation term agrees with the original term because
  -- `a ≤ b < n`, and the original term is already zero.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have han : a < n := lt_of_le_of_lt ha_le_b hn
  exact ((truncGE_term_iso_of_gt (K := K) a n han).isZero_iff).2 (by
    rw [CochainComplex.isStrictlyLE_iff] at hK
    exact hK n hn)

/-- Helper for Lemma 15.67.3: tor-amplitude in `[a, b]` yields a bounded-above projective model
whose derived image is still `K`. -/
lemma exists_bounded_projective_model_of_hasTorAmplitudeIn
    (K : DMod) (a b : ℤ) (hK : HasTorAmplitudeIn K a b) :
    ∃ (P : Cpx) (_ : K ≅ Q.obj P), P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i) := by
  let C : Cpx := DerivedCategory.Q.objPreimage K
  have hCup : ∀ i : ℤ, b < i → IsZero (C.homology i) := by
    intro i hi
    simpa [C] using
      obj_preimage_homology_isZero_of_hasTorAmplitudeIn_above (R := R) K a b i hK hi
  have hCLE : C.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hCup i hi
  letI : C.IsLE b := hCLE
  obtain ⟨P, hPLE, _⟩ :=
    exists_projectiveResolution_strictlyLE_with_termwise_epi
      (𝒜 := ModuleCat R) (K := C.truncLE b) b inferInstance
  let eRep : K ≅ Q.obj (P : Cpx) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (C.ιTruncLE b))).symm ≪≫
        (asIso (DerivedCategory.Q.map P.π)).symm
  -- Proof comment: the unit test gives the upper homology bound, then the canonical upper
  -- truncation and projective-resolution lemma supply a bounded-above projective representative.
  exact ⟨P, eRep, hPLE, fun i ↦ inferInstance⟩

/-- Helper for Lemma 15.67.3: a zero object of `ModuleCat R` is flat. -/
private theorem flat_of_isZero_moduleCat_local
    (M : ModuleCat R) (hM : IsZero M) :
    Module.Flat R M := by
  -- Proof comment: every zero object is linearly equivalent to the literal zero module, which is
  -- flat by the standard instance.
  let Z : ModuleCat R := ModuleCat.of R PUnit
  have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton Z
  letI : Subsingleton ↥Z := ModuleCat.subsingleton_of_isZero hZ
  letI : Module.Free R ↥Z := Module.Free.of_subsingleton (R := R) (N := ↥Z)
  let _ : Module.Flat R Z := Module.Flat.of_free
  let e : M ≅ Z := hM.iso hZ
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Lemma 15.67.3: tor-amplitude in an empty interval forces the derived object to be
zero. -/
private theorem isZero_of_hasTorAmplitudeIn_empty_interval
    (K : DMod) (a b : ℤ) (hK : HasTorAmplitudeIn K a b) (hba : b < a) :
    IsZero K := by
  have hGE : K.IsGE a := by
    -- Proof comment: the tensor-unit test kills the homology of `K` below `a`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact homology_isZero_of_hasTorAmplitudeIn_below (R := R) K a b i hK hi
  have hLE : K.IsLE b := by
    -- Proof comment: the same test kills the homology of `K` above `b`.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact homology_isZero_of_hasTorAmplitudeIn_above (R := R) K a b i hK hi
  -- Proof comment: this is the standard t-structure emptiness criterion for `D^{≥ a} ∩ D^{≤ b}`
  -- when `b < a`.
  letI : K.IsGE a := hGE
  letI : K.IsLE b := hLE
  exact t.isZero K b a hba

/-- Helper for Lemma 15.67.3: in cochain indexing, the predecessor of degree `i` is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.67.3: in cochain indexing, the successor of degree `i` is `i + 1`. -/
private theorem cochain_next_eq (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 :=
  ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.67.3: the cutoff term of the smart lower truncation is the incoming
differential cokernel. -/
private noncomputable def truncGE_cutoff_term_iso_cokernel
    (P : Cpx) (a : ℤ) :
    (P.truncGE a).X a ≅ cokernel (P.dFrom (a - 1)) := by
  sorry

/-- Helper for Lemma 15.67.3: once the cutoff cokernel is flat, the smart lower truncation is
termwise flat. -/
private theorem truncGE_isTermwiseFlat_of_flat_cokernel_local
    (P : Cpx) (a : ℤ) (hFlat : P.IsTermwiseFlat)
    (hCutFlat : Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R))) :
    (P.truncGE a).IsTermwiseFlat := by
  sorry

/-- Helper for Lemma 15.67.3: lower tor-amplitude forces flatness of the cutoff cokernel for a
bounded-above termwise-flat representative. -/
private theorem flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE_local
    (P : Cpx) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) P)
    (hFlat : P.IsTermwiseFlat)
    (hTor : HasTorAmplitudeGE (Q.obj P) a) :
    Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R)) := by
  sorry

/-- Helper for Lemma 15.67.3: ordinary tensor homology with `N[0]` matches the corresponding
derived tensor homology. -/
private noncomputable def tensorObj_single0_homology_iso_derivedTensor_local
    (E : Cpx) (i : ℤ) (N : ModuleCat R) :
    (HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i ≅
      (H i).obj ((Q.obj E) ⊗[R]^L (single₀).obj N) := by
  sorry

/-- Helper for Lemma 15.67.3: if `E` is strictly supported in degrees `≥ a`, then tensoring
with a degree-zero module has zero homology below `a`. -/
private theorem tensorObj_single0_homology_isZero_of_isStrictlyGE_local
    (E : Cpx) (N : ModuleCat R) (a i : ℤ) (hGE : E.IsStrictlyGE a) (hi : i < a) :
    IsZero ((HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i) := by
  sorry

/-- Helper for Lemma 15.67.3: if `E` is strictly supported in degrees `≤ b`, then tensoring
with a degree-zero module has zero homology above `b`. -/
private theorem tensorObj_single0_homology_isZero_of_isStrictlyLE_local
    (E : Cpx) (N : ModuleCat R) (b i : ℤ) (hLE : E.IsStrictlyLE b) (hi : b < i) :
    IsZero ((HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i) := by
  sorry

/-- Helper for Lemma 15.67.3: outside the support interval of a bounded representative, the
ordinary tensor complex with `N[0]` has zero homology. -/
private theorem tensorObj_single0_homology_isZero_of_outside_interval
    (E : Cpx) (N : ModuleCat R) (a b i : ℤ)
    (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((HomologicalComplex.tensorObj E
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i) := by
  have hi' : i < a ∨ b < i := by
    by_cases hia : i < a
    · exact Or.inl hia
    · right
      have hai : a ≤ i := le_of_not_gt hia
      by_contra hbi
      exact hi ⟨hai, le_of_not_gt hbi⟩
  rcases hi' with hi' | hi'
  · exact tensorObj_single0_homology_isZero_of_isStrictlyGE_local (R := R) E N a i hGE hi'
  · exact tensorObj_single0_homology_isZero_of_isStrictlyLE_local (R := R) E N b i hLE hi'

/-- Helper for Lemma 15.67.3: a bounded termwise-flat representative of `K` supported in
`[a, b]` realizes tor-amplitude in the same interval. -/
private theorem hasTorAmplitudeIn_of_flat_representative_local
    {K : DMod} {E : Cpx} {a b : ℤ}
    (e : K ≅ DerivedCategory.Q.obj E)
    (hGE : E.IsStrictlyGE a) (hLE : E.IsStrictlyLE b)
    (_hFlat : E.IsTermwiseFlat) :
    CategoryTheory.HasTorAmplitudeIn K a b := by
  -- Proof comment: prove vanishing on the ordinary tensor model, then transport it to the
  -- derived tensor product and finally across the chosen representative isomorphism.
  apply (hasTorAmplitudeIn_of_iso_local (R := R) e).2
  intro N i hi
  have hOrdinary :
      IsZero ((HomologicalComplex.tensorObj E
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).homology i) :=
    tensorObj_single0_homology_isZero_of_outside_interval
      (R := R) E N a b i hGE hLE hi
  exact hOrdinary.of_iso
    (tensorObj_single0_homology_iso_derivedTensor_local (R := R) E i N).symm

/-- Lemma 15.67.3: an object `K^•` of `D(R)` has tor-amplitude in `[a, b]` if and only if it is
isomorphic in `D(R)` to a cochain complex `E^•` of flat `R`-modules with `E^i = 0` for
`i ∉ [a, b]`. -/
@[stacks 0654]
theorem hasTorAmplitudeIn_iff_exists_flat_representative
    (K : DMod) (a b : ℤ) :
    HasTorAmplitudeIn K a b ↔
      ∃ (E : Cpx) (_ : K ≅ DerivedCategory.Q.obj E),
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ E.IsTermwiseFlat := by
  constructor
  · intro hK
    by_cases hab : a ≤ b
    · obtain ⟨P, eP, hPLE, hProj⟩ :=
        exists_bounded_projective_model_of_hasTorAmplitudeIn (R := R) K a b hK
      let E : Cpx := P.truncGE a
      have hPbelow : ∀ i : ℤ, i < a → IsZero (P.homology i) := by
        intro i hi
        have hzeroK : IsZero ((H i).obj K) :=
          homology_isZero_of_hasTorAmplitudeIn_below (R := R) K a b i hK hi
        have hzeroQP : IsZero ((H i).obj (Q.obj P)) :=
          hzeroK.of_iso ((H i).mapIso eP.symm)
        -- Proof comment: compute the homology of `Q.obj P` on the representative `P`.
        exact ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app P).isZero_iff.1 hzeroQP
      have hπ : QuasiIso (P.πTruncGE a) := by
        -- Proof comment: the homology vanishing below `a` makes the smart lower truncation map a
        -- quasi-isomorphism.
        exact quasiIso_piTruncGE_of_isZero_homology_below a P hPbelow
      let eE : K ≅ Q.obj E :=
        eP ≪≫ asIso (Q.map (P.πTruncGE a))
      have hEGE : E.IsStrictlyGE a := by
        infer_instance
      have hELE : E.IsStrictlyLE b :=
        truncGE_isStrictlyLE_of_isStrictlyLE_local (K := P) a b hab hPLE
      have hPbounded : CochainComplex.minus (ModuleCat R) P := by
        exact (CochainComplex.minus_iff (ModuleCat R) P).2 ⟨b, hPLE⟩
      have hPFlat : P.IsTermwiseFlat := by
        intro i
        let _ : Projective (P.X i) := hProj i
        exact Module.Flat.of_projective
      have hPtor : HasTorAmplitudeIn (Q.obj P) a b :=
        (hasTorAmplitudeIn_of_iso_local (R := R) eP).1 hK
      have hCutFlat :
          Module.Flat R ↑((cokernel (P.dFrom (a - 1)) : ModuleCat R)) := by
        -- Proof comment: this is the cited Lemma `15.67.2` step in the source proof.
        exact
          flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE_local
            (R := R) P a hPbounded hPFlat hPtor.hasTorAmplitudeGE
      have hEFlat : E.IsTermwiseFlat :=
        truncGE_isTermwiseFlat_of_flat_cokernel_local (R := R) P a hPFlat hCutFlat
      exact ⟨E, eE, hEGE, hELE, hEFlat⟩
    · have hba : b < a := by omega
      have hZeroK : IsZero K :=
        isZero_of_hasTorAmplitudeIn_empty_interval (R := R) K a b hK hba
      let E0 : Cpx := zeroCpx
      have hZeroQ0 : IsZero (Q.obj E0) := by
        simpa [E0, zeroCpx] using
          Q.map_isZero (HomologicalComplex.isZero_zero : IsZero (HomologicalComplex.zero : Cpx))
      have hZeroFlat : E0.IsTermwiseFlat := by
        intro i
        let hzeroXi : IsZero (E0.X i) := by
          simpa [E0, zeroCpx] using
            (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
              (HomologicalComplex.isZero_zero : IsZero (HomologicalComplex.zero : Cpx))
        exact flat_of_isZero_moduleCat_local (R := R) (E0.X i) hzeroXi
      have hZeroGE : E0.IsStrictlyGE a := by
        rw [CochainComplex.isStrictlyGE_iff]
        intro i hi
        simpa [E0, zeroCpx] using
          (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
            (HomologicalComplex.isZero_zero : IsZero (HomologicalComplex.zero : Cpx))
      have hZeroLE : E0.IsStrictlyLE b := by
        rw [CochainComplex.isStrictlyLE_iff]
        intro i hi
        simpa [E0, zeroCpx] using
          (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
            (HomologicalComplex.isZero_zero : IsZero (HomologicalComplex.zero : Cpx))
      -- Proof comment: for an empty support interval, `K` is zero and the zero complex is the
      -- required flat representative.
      exact ⟨E0, hZeroK.iso hZeroQ0, hZeroGE, hZeroLE, hZeroFlat⟩
  · rintro ⟨E, e, hGE, hLE, _hFlat⟩
    -- Proof comment: a bounded termwise-flat representative computes the derived tensor directly,
    -- so the support bound on the ordinary tensor complex gives tor-amplitude.
    exact hasTorAmplitudeIn_of_flat_representative_local
      (R := R) (K := K) e hGE hLE _hFlat

end

end CategoryTheory
