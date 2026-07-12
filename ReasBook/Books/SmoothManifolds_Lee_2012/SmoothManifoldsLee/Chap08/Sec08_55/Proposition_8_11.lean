import SmoothManifolds_Lee_2012.Chap08.Sec08_54.Lemma_8_6
import SmoothManifolds_Lee_2012.Chap08.Sec08_55.Definition_8_55_extra_1

open scoped ContDiff Manifold

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Unbundled tangent vector fields on `M`, used here because the source data are only assumed
smooth on a specified subset or along a closed subset. -/
abbrev RoughVectorField := (p : M) → TangentSpace I p
local notation "FrameIndex" => Fin (Module.finrank ℝ E)

-- Domain sampling pass:
-- * primary domain: completion of partial smooth tangent-space data to local frames;
-- * semantic recall: `lean_leansearch` points to mathlib's canonical owner `IsLocalFrameOn`;
-- * source-facing layer here: explicit extension statements for partial frames, tangent vectors at
--   one point, and smooth fields given only along a closed subset.

namespace VectorField

/-- A `FrameIndex`-tuple of vector fields along `A ⊆ M` is smooth along `A` when every component
admits a smooth ambient extension on a neighborhood of each point of `A`. -/
def TupleSmoothAlong (A : Set M)
    (X : FrameIndex → (p : A) → TangentSpace I p.1) : Prop :=
  ∀ i : FrameIndex, ∀ p : A, ∃ U : Set M, IsOpen U ∧ p.1 ∈ U ∧
    ∃ Y : RoughVectorField,
      ContMDiffOn I I.tangent ∞ (T% Y) U ∧
        ∀ q : A, q.1 ∈ U → Y q.1 = X i q

end VectorField

/-- Helper for Proposition 8.11: a linearly independent `Fin k`-family in a finite-dimensional
real vector space extends to a basis indexed by `Fin (Module.finrank ℝ V)`. -/
theorem exists_finBasis_extension
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {k : ℕ} (hk1 : 1 ≤ k) (hkle : k ≤ Module.finrank ℝ V) {v : Fin k → V}
    (hv : LinearIndependent ℝ v) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i : Fin k, b (Fin.castLE hkle i) = v i := by
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range v)
  let w : Fin k → W := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  -- First regard the prescribed family as a basis of its span.
  have hw : LinearIndependent ℝ w := by
    simpa [w, W] using linearIndependent_span hv
  have hWcard : Fintype.card (Fin k) = Module.finrank ℝ W := by
    simpa [W] using (linearIndependent_iff_card_eq_finrank_span.mp hv)
  letI : Nonempty (Fin k) := ⟨⟨0, hk1⟩⟩
  let bW : Module.Basis (Fin k) ℝ W := basisOfLinearIndependentOfCardEqFinrank hw hWcard
  -- Then choose a complementary subspace and append any basis of that complement.
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  have hWfin : Module.finrank ℝ W = k := by
    simpa using hWcard.symm
  have hQfin : Module.finrank ℝ Q = Module.finrank ℝ V - k := by
    have hsum : Module.finrank ℝ W + Module.finrank ℝ Q = Module.finrank ℝ V := by
      simpa using (Submodule.finrank_add_eq_of_isCompl hQ)
    rw [hWfin] at hsum
    omega
  let bQ : Module.Basis (Fin (Module.finrank ℝ V - k)) ℝ Q := Module.finBasisOfFinrankEq ℝ Q hQfin
  let bSum : Module.Basis (Fin k ⊕ Fin (Module.finrank ℝ V - k)) ℝ V :=
    (bW.prod bQ).map (W.prodEquivOfIsCompl Q hQ)
  let eFin : (Fin k ⊕ Fin (Module.finrank ℝ V - k)) ≃ Fin (Module.finrank ℝ V) :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkle))
  refine ⟨bSum.reindex eFin, ?_⟩
  intro i
  -- The left summand of the direct-sum basis records the original vectors verbatim.
  have hcast :
      Fin.castLE hkle i =
        finCongr (Nat.add_sub_of_le hkle) (Fin.castAdd (Module.finrank ℝ V - k) i) := by
    ext
    rfl
  rw [hcast, Module.Basis.reindex_apply]
  simp [bSum, eFin, bW, w]

/-- Helper for Proposition 8.11: a smooth `FrameIndex`-tuple of vector fields that is linearly
independent at one point is a smooth local frame on a smaller neighborhood of that point. -/
theorem exists_localFrame_near_of_contMDiffOn_and_linearIndependentAt
    {U : Set M} (hU : IsOpen U) {e : FrameIndex → (p : M) → TangentSpace I p}
    (heSmooth : ∀ i : FrameIndex, ContMDiffOn I I.tangent ∞ (T% (e i)) U)
    {p : M} (hp : p ∈ U) (heLin : LinearIndependent ℝ (e · p)) :
    ∃ V : { V : TopologicalSpace.Opens M // p ∈ V ∧ (V : Set M) ⊆ U },
      IsLocalFrameOn I E ∞ e (V : Set M) := by
  let τ := trivializationAt E (TangentSpace I) p
  have hpτ : p ∈ τ.baseSet := by
    simp [τ]
  haveI : FiniteDimensional ℝ (TangentSpace I p) :=
    (τ.linearEquivAt (R := ℝ) p hpτ).symm.finiteDimensional
  have hUτopen : IsOpen (U ∩ τ.baseSet) := hU.inter τ.open_baseSet
  have hpUτ : p ∈ U ∩ τ.baseSet := ⟨hp, hpτ⟩
  have hcard : Fintype.card FrameIndex = Module.finrank ℝ (TangentSpace I p) := by
    simpa only [Fintype.card_fin] using (τ.linearEquivAt (R := ℝ) p hpτ).symm.finrank_eq
  have hspan : Submodule.span ℝ (Set.range (e · p)) = ⊤ := by
    simpa using heLin.span_eq_top_of_card_eq_finrank' hcard
  let bExt : Module.Basis FrameIndex ℝ (TangentSpace I p) := Module.Basis.mk heLin hspan.ge
  let c : Module.Basis FrameIndex ℝ E := bExt.map (τ.linearEquivAt (R := ℝ) p hpτ)
  let A : M → Matrix FrameIndex FrameIndex ℝ := fun q i j ↦
    τ.localFrame_coeff I c i q (e j q)
  have hCoeffCont (i j : FrameIndex) :
      Continuous fun q : ↥(U ∩ τ.baseSet) ↦ A q i j := by
    exact continuousOn_iff_continuous_restrict.mp <|
      (contMDiffOn_localFrame_coeff (I := I) (e := τ) (b := c)
        hUτopen (by
          intro q hq
          exact hq.2) ((heSmooth j).mono (by
          intro q hq
          exact hq.1)) i).continuousOn
  have hACont : Continuous fun q : ↥(U ∩ τ.baseSet) ↦ A q := by
    refine continuous_matrix ?_
    intro i j
    exact hCoeffCont i j
  have hdetCont : ContinuousOn (fun q ↦ (A q).det) (U ∩ τ.baseSet) := by
    rw [continuousOn_iff_continuous_restrict]
    exact hACont.matrix_det
  let W : Set M := (U ∩ τ.baseSet) ∩ (fun q ↦ (A q).det) ⁻¹' ({0}ᶜ : Set ℝ)
  have hWopen : IsOpen W := by
    simpa [W] using hdetCont.isOpen_inter_preimage hUτopen isOpen_compl_singleton
  have hbasis : τ.basisAt c hpτ = bExt := by
    ext j
    change
      (τ.linearEquivAt (R := ℝ) p hpτ).symm
          ((τ.linearEquivAt (R := ℝ) p hpτ) (bExt j)) =
        bExt j
    exact (τ.linearEquivAt (R := ℝ) p hpτ).symm_apply_apply (bExt j)
  have hAat : A p = 1 := by
    ext i j
    change τ.localFrame_coeff I c i p (e j p) = if i = j then 1 else 0
    rw [Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
      (I := I) (e := τ) (b := c) (x := p) (hx := hpτ) (s := e j)]
    rw [hbasis]
    have hej : e j p = bExt j := by
      exact (Module.Basis.mk_apply heLin hspan.ge j).symm
    rw [hej]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hpW : p ∈ W := by
    refine ⟨hpUτ, ?_⟩
    simp [hAat]
  refine ⟨⟨⟨W, hWopen⟩, hpW, by
    intro q hq
    exact hq.1.1⟩, ?_⟩
  refine
    { linearIndependent := ?_, generating := ?_, contMDiffOn := ?_ }
  · intro q hq
    have hqτ : q ∈ τ.baseSet := hq.1.2
    let bq := τ.basisAt c hqτ
    have hMatrix : bq.toMatrix (e · q) = A q := by
      ext i j
      symm
      exact Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
        (I := I) (e := τ) (b := c) (x := q) (hx := hqτ) (s := e j) (i := i)
    have hunit : IsUnit (bq.det (e · q)) := by
      rw [Module.Basis.det_apply, hMatrix]
      exact isUnit_iff_ne_zero.mpr hq.2
    exact (Module.Basis.is_basis_iff_det bq).2 hunit |>.1
  · intro q hq
    have hqτ : q ∈ τ.baseSet := hq.1.2
    let bq := τ.basisAt c hqτ
    have hMatrix : bq.toMatrix (e · q) = A q := by
      ext i j
      symm
      exact Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
        (I := I) (e := τ) (b := c) (x := q) (hx := hqτ) (s := e j) (i := i)
    have hunit : IsUnit (bq.det (e · q)) := by
      rw [Module.Basis.det_apply, hMatrix]
      exact isUnit_iff_ne_zero.mpr hq.2
    exact ((Module.Basis.is_basis_iff_det bq).2 hunit |>.2).ge
  · intro i
    exact (heSmooth i).mono (by
      intro q hq
      exact hq.1.1)

/-- Proposition 8.11 (1): a linearly independent smooth `k`-tuple of vector fields on an open set
extends near any chosen point to a smooth local frame of the whole tangent bundle. -/
theorem exists_localFrame_completion_at_of_linearlyIndependentOn
    {k : ℕ} (hk1 : 1 ≤ k) (hklt : k < Module.finrank ℝ E)
    {U : Set M} (hU : IsOpen U) {X : Fin k → (p : M) → TangentSpace I p}
    (hXsmooth : ∀ i : Fin k, ContMDiffOn I I.tangent ∞ (T% (X i)) U)
    (hXlin : VectorField.LinearlyIndependentOn U X) {p : M} (hp : p ∈ U) :
    ∃ V : { V : TopologicalSpace.Opens M // p ∈ V },
      ∃ e : FrameIndex → (p : M) → TangentSpace I p,
        (∀ i : Fin k, ∀ q ∈ U ∩ (V : Set M),
          e (Fin.castLE (Nat.le_of_lt hklt) i) q = X i q) ∧
        IsLocalFrameOn I E ∞ e (U ∩ (V : Set M)) := by
  let τ := trivializationAt E (TangentSpace I) p
  have hpτ : p ∈ τ.baseSet := by
    simp [τ]
  have hUτopen : IsOpen (U ∩ τ.baseSet) := hU.inter τ.open_baseSet
  have hpUτ : p ∈ U ∩ τ.baseSet := ⟨hp, hpτ⟩
  haveI : FiniteDimensional ℝ (TangentSpace I p) := by
    exact (τ.linearEquivAt (R := ℝ) p hpτ).symm.finiteDimensional
  have hkleT : k ≤ Module.finrank ℝ (TangentSpace I p) := by
    simpa [TangentSpace] using Nat.le_of_lt hklt
  obtain ⟨bExt, hbExt⟩ :=
    exists_finBasis_extension (V := TangentSpace I p) hk1 hkleT (hXlin p hp)
  let c : Module.Basis FrameIndex ℝ E := bExt.map (τ.linearEquivAt (R := ℝ) p hpτ)
  let e : FrameIndex → (q : M) → TangentSpace I q := fun j q ↦
    if hj : j.1 < k then X ⟨j.1, hj⟩ q else τ.localFrame c j q
  have hbasis : τ.basisAt c hpτ = bExt := by
    ext j
    change
      (τ.linearEquivAt (R := ℝ) p hpτ).symm
          ((τ.linearEquivAt (R := ℝ) p hpτ) (bExt j)) =
        bExt j
    exact (τ.linearEquivAt (R := ℝ) p hpτ).symm_apply_apply (bExt j)
  have hep : (fun j : FrameIndex ↦ e j p) = bExt := by
    funext j
    by_cases hj : j.1 < k
    · calc
        e j p = X ⟨j.1, hj⟩ p := by simp [e, hj]
        _ = bExt (Fin.castLE hkleT ⟨j.1, hj⟩) := (hbExt ⟨j.1, hj⟩).symm
        _ = bExt j := by rfl
    · simpa [e, hj, hbasis] using
        (Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := τ) (b := c) hpτ :
          τ.localFrame c j p = (τ.basisAt c hpτ) j)
  have heLin : LinearIndependent ℝ (fun j : FrameIndex ↦ e j p) := by
    simpa [hep] using bExt.linearIndependent
  have heSmooth :
      ∀ i : FrameIndex, ContMDiffOn I I.tangent ∞ (T% (e i)) (U ∩ τ.baseSet) := by
    intro i
    by_cases hi : i.1 < k
    · simpa [e, hi] using (hXsmooth ⟨i.1, hi⟩).mono (by
        intro q hq
        exact hq.1)
    · simpa [e, hi] using
        (Bundle.Trivialization.contMDiffOn_localFrame_baseSet
          (I := I) (e := τ) (n := ∞) (b := c) i).mono (by
        intro q hq
        exact hq.2)
  obtain ⟨V, hFrame⟩ :=
    exists_localFrame_near_of_contMDiffOn_and_linearIndependentAt
      hUτopen heSmooth hpUτ heLin
  refine ⟨⟨V.1, V.2.1⟩, e, ?_, ?_⟩
  · intro i q hq
    simp [e]
  · have hVU : (V : Set M) ⊆ U := by
      intro q hqV
      exact (V.2.2 hqV).1
    have hUV : U ∩ (V : Set M) = (V : Set M) := by
      ext q
      constructor
      · intro hq
        exact hq.2
      · intro hqV
        exact ⟨hVU hqV, hqV⟩
    convert hFrame using 1

/-- Proposition 8.11 (2): a linearly independent `k`-tuple of tangent vectors at one point extends
to a smooth local frame on some neighborhood of that point. -/
theorem exists_localFrame_extending_tangentVectors
    {k : ℕ} (hk1 : 1 ≤ k) (hkle : k ≤ Module.finrank ℝ E)
    {p : M} {v : Fin k → TangentSpace I p} (hv : LinearIndependent ℝ v) :
    ∃ V : { V : TopologicalSpace.Opens M // p ∈ V },
      ∃ e : FrameIndex → (p : M) → TangentSpace I p,
        (∀ i : Fin k, e (Fin.castLE hkle i) p = v i) ∧
        IsLocalFrameOn I E ∞ e (V : Set M) := by
  -- Route correction: use the canonical tangent-bundle trivialization at `p`, not the
  -- Euclidean-only chart-coordinate frame from Example 8.10.
  let τ := trivializationAt E (TangentSpace I) p
  let b := Module.finBasis ℝ E
  have hpτ : p ∈ τ.baseSet := by
    simp [τ]
  haveI : FiniteDimensional ℝ (TangentSpace I p) := by
    simpa [TangentSpace] using (inferInstance : FiniteDimensional ℝ E)
  have hkleT : k ≤ Module.finrank ℝ (TangentSpace I p) := by
    simpa [TangentSpace] using hkle
  obtain ⟨bExt, hbExt⟩ :=
    exists_finBasis_extension (V := TangentSpace I p) hk1 hkleT hv
  let c : Module.Basis FrameIndex ℝ E := bExt.map (τ.linearEquivAt (R := ℝ) p hpτ)
  refine ⟨⟨⟨τ.baseSet, τ.open_baseSet⟩, hpτ⟩, τ.localFrame c, ?_, ?_⟩
  · intro i
    -- The transported basis agrees with the prescribed tangent vectors at the base point.
    have hbasis : τ.basisAt c hpτ = bExt := by
      ext j
      change
        (τ.linearEquivAt (R := ℝ) p hpτ).symm
            ((τ.linearEquivAt (R := ℝ) p hpτ) (bExt j)) =
          bExt j
      exact (τ.linearEquivAt (R := ℝ) p hpτ).symm_apply_apply (bExt j)
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := τ) (b := c) hpτ, hbasis]
    exact hbExt i
  · -- The induced local frame is smooth and pointwise a basis on the trivialization domain.
    simpa [c] using τ.isLocalFrameOn_localFrame_baseSet I ∞ c

/-- Proposition 8.11 (3): a linearly independent smooth `n`-tuple of vector fields along a closed
subset extends to a smooth local frame on some open neighborhood of that closed subset. -/
theorem exists_localFrame_extension_of_closed
    {A : Set M} (hA : IsClosed A)
    {X : FrameIndex → (p : A) → TangentSpace I p.1}
    (hXsmooth : VectorField.TupleSmoothAlong A X)
    (hXlin : ∀ p : A, LinearIndependent ℝ (fun i : FrameIndex ↦ X i p)) :
    ∃ V : { V : TopologicalSpace.Opens M // A ⊆ V },
      ∃ e : FrameIndex → (p : M) → TangentSpace I p,
        (∀ i : FrameIndex, ∀ p : A, e i p.1 = X i p) ∧
        IsLocalFrameOn I E ∞ e (V : Set M) := by
  classical
  haveI : T2Space M := inferInstance
  haveI : SigmaCompactSpace M := inferInstance
  let Xi : FrameIndex → (p : A) → TangentSpace I p.1 := X
  choose W hWopen hpW Yloc hYsmoothLocal hYeqLocal using hXsmooth
  have hExt :
      ∀ i : FrameIndex, ∃ Y : RoughVectorField,
        ContMDiff I I.tangent ∞ (T% Y) ∧ ∀ p : A, Y p.1 = Xi i p := by
    intro i
    have hLocal :
        ∀ p : A, ContMDiffVectorFieldLocalExtension (Xi i) p := by
      intro p
      exact ⟨W i p, hWopen i p, hpW i p, Yloc i p, hYsmoothLocal i p, hYeqLocal i p⟩
    obtain ⟨Y, hY⟩ :=
      exists_supported_contMDiff_vectorField_extension_of_isClosed
        (I := I) (A := A) (U := Set.univ) hA isOpen_univ (by
          intro p hp
          simp) (Xi i) hLocal
    exact ⟨Y, hY.contMDiff, hY.eq_source⟩
  choose Y hYsmooth hYeq using hExt
  have hYlin : ∀ p : A, LinearIndependent ℝ (fun i : FrameIndex ↦ Y i p.1) := by
    intro p
    simpa [hYeq] using hXlin p
  have hLocalFrame :
      ∀ p : A, ∃ V : { V : TopologicalSpace.Opens M // p.1 ∈ V },
        IsLocalFrameOn I E ∞ Y (V : Set M) := by
    intro p
    obtain ⟨V, hFrame⟩ :=
      exists_localFrame_near_of_contMDiffOn_and_linearIndependentAt
        (U := Set.univ) isOpen_univ (fun i ↦ (hYsmooth i).contMDiffOn) (by simp) (hYlin p)
    exact ⟨⟨V.1, V.2.1⟩, hFrame⟩
  let Vsub : ∀ p : A, { V : TopologicalSpace.Opens M // p.1 ∈ V } :=
    fun p ↦ Classical.choose (hLocalFrame p)
  let V : A → TopologicalSpace.Opens M := fun p ↦ (Vsub p).1
  have hVmem : ∀ p : A, p.1 ∈ V p := by
    intro p
    exact (Vsub p).2
  have hVframe : ∀ p : A, IsLocalFrameOn I E ∞ Y (V p : Set M) := by
    intro p
    exact (Classical.choose_spec (hLocalFrame p))
  let Vset : Set M := ⋃ p : A, (V p : Set M)
  have hVopen : IsOpen Vset := by
    simpa [Vset] using isOpen_iUnion (fun p : A ↦ (V p).isOpen)
  have hAV : A ⊆ Vset := by
    intro p hp
    simpa [Vset] using (show ∃ q : A, p ∈ V q from ⟨⟨p, hp⟩, hVmem ⟨p, hp⟩⟩)
  refine ⟨⟨⟨Vset, hVopen⟩, hAV⟩, Y, hYeq, ?_⟩
  refine
    { linearIndependent := ?_, generating := ?_, contMDiffOn := ?_ }
  · intro q hq
    rcases (show ∃ p : A, q ∈ V p from by simpa [Vset] using hq) with ⟨pA, hqV⟩
    exact (hVframe pA).linearIndependent hqV
  · intro q hq
    rcases (show ∃ p : A, q ∈ V p from by simpa [Vset] using hq) with ⟨pA, hqV⟩
    exact (hVframe pA).generating hqV
  · intro i
    exact (hYsmooth i).contMDiffOn

end
