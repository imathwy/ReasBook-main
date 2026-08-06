import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Lemma_22_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Mathlib.Topology.Homotopy.HomotopyGroup

universe u

open scoped Topology.Homotopy
open scoped unitInterval

-- Semantic recall: `lean_leansearch` surfaced mathlib's canonical `LoopSpace`/`Ω` notation and
-- the ambient `HSpace` API on paths, so this item is stated directly in that language.

noncomputable section

variable {Y : Type u} [TopologicalSpace Y]

/-- Path reversal as a self-map of the loop space `Ω Y y`. -/
abbrev loopSpaceInverse (y : Y) : C(Ω Y y, Ω Y y) :=
  ⟨Path.symm, Path.continuous_symm⟩

@[simp]
theorem loopSpaceInverse_apply (y : Y) (γ : Ω Y y) : loopSpaceInverse y γ = γ.symm :=
  rfl

/-- Helper for Lemma 22.2.4: delaying the constant loop on the right does not change it. -/
theorem delayReflRight_refl (y : Y) (θ : I) :
    Path.delayReflRight θ (Path.refl y) = Path.refl y := by
  -- The defining formula is pointwise constant when the input loop is constant.
  ext t
  simp [Path.delayReflRight]

/-- Helper for Lemma 22.2.4: delaying the constant loop on the left does not change it. -/
theorem delayReflLeft_refl (y : Y) (θ : I) :
    Path.delayReflLeft θ (Path.refl y) = Path.refl y := by
  -- Rewrite the left-delay through the right-delay formula on the reversed constant loop.
  ext t
  simp [Path.delayReflLeft, Path.delayReflRight]

/-- Helper for Lemma 22.2.4: path associativity packages into a homotopy of loop-space
multiplication maps. -/
theorem loopSpaceAssocHomotopy (y : Y) :
    ContinuousMap.Homotopic
      (hSpaceAssocLeft (Ω Y y))
      (hSpaceAssocRight (Ω Y y)) := by
  -- Reparameterize the right-associated loop family and then reverse the resulting map homotopy.
  refine ContinuousMap.Homotopic.symm ?_
  have hAssocReparam : Continuous fun t : I ↦
      (⟨Path.Homotopy.transAssocReparamAux t,
        Path.Homotopy.transAssocReparamAux_mem_I t⟩ : I) := by
    exact Continuous.subtype_mk Path.Homotopy.continuous_transAssocReparamAux
      (fun t ↦ Path.Homotopy.transAssocReparamAux_mem_I t)
  let F : C((Ω Y y × (Ω Y y × Ω Y y)) × I, Ω Y y) :=
    ⟨fun p ↦
      (Path.Homotopy.reparam
          (hSpaceAssocRight (Ω Y y) p.1)
          (fun t ↦ ⟨Path.Homotopy.transAssocReparamAux t,
            Path.Homotopy.transAssocReparamAux_mem_I t⟩)
          hAssocReparam
          (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_one)).eval p.2,
      by
        -- Continuity into the loop space is checked after uncurrying to a map into `Y`.
        apply Path.continuous_uncurry_iff.mp
        let rawInterp :
            (((Ω Y y × (Ω Y y × Ω Y y)) × I) × I) → ℝ :=
          fun q ↦ (σ q.1.2 : ℝ) * (q.2 : ℝ) +
            (q.1.2 : ℝ) * ((⟨Path.Homotopy.transAssocReparamAux q.2,
              Path.Homotopy.transAssocReparamAux_mem_I q.2⟩ : I) : ℝ)
        have hRawInterp : Continuous rawInterp := by
          fun_prop
        have hInterpMem :
            ∀ q : (((Ω Y y × (Ω Y y × Ω Y y)) × I) × I), rawInterp q ∈ I := by
          intro q
          have hσ : 0 ≤ (((σ q.1.2 : I) : ℝ)) := (σ q.1.2).2.1
          have hθ : 0 ≤ ((q.1.2 : I) : ℝ) := q.1.2.2.1
          exact convex_Icc _ _ q.2.2
            (Path.Homotopy.transAssocReparamAux_mem_I q.2)
            hσ hθ (by simp)
        have hInterp : Continuous fun q : (((Ω Y y × (Ω Y y × Ω Y y)) × I) × I) ↦
            (⟨rawInterp q, hInterpMem q⟩ : I) := by
          exact Continuous.subtype_mk hRawInterp hInterpMem
        have hRight :
            Continuous fun q : (((Ω Y y × (Ω Y y × Ω Y y)) × I) × I) ↦
              hSpaceAssocRight (Ω Y y) q.1.1 := by
          exact (hSpaceAssocRight (Ω Y y)).continuous.comp (continuous_fst.comp continuous_fst)
        change Continuous fun q : (((Ω Y y × (Ω Y y × Ω Y y)) × I) × I) ↦
          hSpaceAssocRight (Ω Y y) q.1.1 (⟨rawInterp q, hInterpMem q⟩ : I)
        exact continuous_eval.comp (hRight.prodMk hInterp)⟩
  refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
  · intro x
    -- At time `0`, the reparameterization homotopy starts at the right-associated loop.
    simp [F]
  · intro x
    -- At time `1`, the reparameterized right-associated loop is the left-associated loop.
    simpa [F, hSpaceAssocLeft, hSpaceAssocRight] using
      (Path.Homotopy.trans_assoc_reparam x.1 x.2.1 x.2.2).symm

/-- Helper for Lemma 22.2.4: path reversal is a left homotopy inverse on the loop space. -/
theorem loopSpaceLeftInverseHomotopy (y : Y) :
    ContinuousMap.Homotopic
      (hSpaceLeftInverseMap (Ω Y y) (loopSpaceInverse y))
      (ContinuousMap.const (Ω Y y) (Path.refl y)) := by
  -- Package the standard contraction of `γ.symm.trans γ` and then reverse its direction.
  refine ContinuousMap.Homotopic.symm ?_
  let F : C(Ω Y y × I, Ω Y y) :=
    ⟨fun p ↦ (Path.Homotopy.reflSymmTrans p.1).eval p.2,
      by
        -- Route correction: unfold the standard contraction once so the continuity proof is
        -- reduced to the explicit `reflTransSymm` formula.
        apply Path.continuous_uncurry_iff.mp
        have hAux : Continuous fun p : I × I ↦
            (⟨Path.Homotopy.reflTransSymmAux p,
              Path.Homotopy.reflTransSymmAux_mem_I p⟩ : I) := by
          exact Continuous.subtype_mk Path.Homotopy.continuous_reflTransSymmAux
            (fun p ↦ Path.Homotopy.reflTransSymmAux_mem_I p)
        have hPath : Continuous fun q : ((Ω Y y × I) × I) ↦ q.1.1.symm := by
          exact Path.continuous_symm.comp (continuous_fst.comp continuous_fst)
        have hTime : Continuous fun q : ((Ω Y y × I) × I) ↦
            (⟨Path.Homotopy.reflTransSymmAux (q.1.2, q.2),
              Path.Homotopy.reflTransSymmAux_mem_I (q.1.2, q.2)⟩ : I) := by
          exact hAux.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
        change Continuous fun q : ((Ω Y y × I) × I) ↦
          q.1.1.symm
            (⟨Path.Homotopy.reflTransSymmAux (q.1.2, q.2),
              Path.Homotopy.reflTransSymmAux_mem_I (q.1.2, q.2)⟩ : I)
        exact continuous_eval.comp (hPath.prodMk hTime)⟩
  refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
  · intro γ
    -- At time `0`, the contraction starts at the constant loop.
    simp [F]
  · intro γ
    -- At time `1`, the contraction reaches `γ.symm.trans γ`.
    simp [F, hSpaceLeftInverseMap, loopSpaceInverse]
    rfl

/-- Helper for Lemma 22.2.4: path reversal is a right homotopy inverse on the loop space. -/
theorem loopSpaceRightInverseHomotopy (y : Y) :
    ContinuousMap.Homotopic
      (hSpaceRightInverseMap (Ω Y y) (loopSpaceInverse y))
      (ContinuousMap.const (Ω Y y) (Path.refl y)) := by
  -- Package the standard contraction of `γ.trans γ.symm` and then reverse its direction.
  refine ContinuousMap.Homotopic.symm ?_
  let F : C(Ω Y y × I, Ω Y y) :=
    ⟨fun p ↦ (Path.Homotopy.reflTransSymm p.1).eval p.2,
      by
        -- Continuity again reduces to the uncurried map into `Y`.
        apply Path.continuous_uncurry_iff.mp
        have hAux : Continuous fun p : I × I ↦
            (⟨Path.Homotopy.reflTransSymmAux p,
              Path.Homotopy.reflTransSymmAux_mem_I p⟩ : I) := by
          exact Continuous.subtype_mk Path.Homotopy.continuous_reflTransSymmAux
            (fun p ↦ Path.Homotopy.reflTransSymmAux_mem_I p)
        have hPath : Continuous fun q : ((Ω Y y × I) × I) ↦ q.1.1 := by
          exact continuous_fst.comp continuous_fst
        have hTime : Continuous fun q : ((Ω Y y × I) × I) ↦
            (⟨Path.Homotopy.reflTransSymmAux (q.1.2, q.2),
              Path.Homotopy.reflTransSymmAux_mem_I (q.1.2, q.2)⟩ : I) := by
          exact hAux.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
        change Continuous fun q : ((Ω Y y × I) × I) ↦
          q.1.1
            (⟨Path.Homotopy.reflTransSymmAux (q.1.2, q.2),
              Path.Homotopy.reflTransSymmAux_mem_I (q.1.2, q.2)⟩ : I)
        exact continuous_eval.comp (hPath.prodMk hTime)⟩
  refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
  · intro γ
    -- At time `0`, the contraction starts at the constant loop.
    simp [F]
  · intro γ
    -- At time `1`, the contraction reaches `γ.trans γ.symm`.
    simp [F, hSpaceRightInverseMap, loopSpaceInverse]
    rfl

/-- For Lemma 22.2.4 (1): for every basepoint `y : Y`, the loop space `Ω Y y` is
homotopy-associative for the canonical `HSpace` multiplication given by path concatenation. -/
theorem loopSpace_homotopyAssociative (y : Y) :
    ContinuousMap.Homotopic
      (hSpaceAssocLeft (Ω Y y))
      (hSpaceAssocRight (Ω Y y)) :=
  by
    -- Use the packaged associator homotopy on triples of loops.
    exact loopSpaceAssocHomotopy y

/-- For Lemma 22.2.4 (2): for every basepoint `y : Y`, path reversal is a left homotopy inverse
for the canonical loop-space multiplication on `Ω Y y`. -/
theorem loopSpace_homotopyLeftInverse (y : Y) :
    ContinuousMap.Homotopic
      (hSpaceLeftInverseMap (Ω Y y) (loopSpaceInverse y))
      (ContinuousMap.const (Ω Y y) (Path.refl y)) :=
  by
    -- Use the packaged contraction of `γ.symm.trans γ`.
    exact loopSpaceLeftInverseHomotopy y

/-- For Lemma 22.2.4 (3): for every basepoint `y : Y`, path reversal is a right homotopy inverse
for the canonical loop-space multiplication on `Ω Y y`. -/
theorem loopSpace_homotopyRightInverse (y : Y) :
    ContinuousMap.Homotopic
      (hSpaceRightInverseMap (Ω Y y) (loopSpaceInverse y))
      (ContinuousMap.const (Ω Y y) (Path.refl y)) :=
  by
    -- Use the packaged contraction of `γ.trans γ.symm`.
    exact loopSpaceRightInverseHomotopy y

section DoubleLoopAux

variable {Z : Type u} [TopologicalSpace Z] [HSpace Z]

/-- Helper for Lemma 22.2.4: postcomposing a based loop by a self-map fixing the `HSpace` unit
still yields a based loop. -/
def loopPostcompose (f : C(Z, Z)) (hf : f HSpace.e = HSpace.e) :
    C(Ω Z HSpace.e, Ω Z HSpace.e) :=
  ⟨fun γ ↦ (γ.map f.continuous).cast hf.symm hf.symm,
    by
      -- Continuity into the loop space is checked after uncurrying to a map into `Z`.
      apply Path.continuous_uncurry_iff.mp
      change Continuous fun q : (Ω Z HSpace.e × I) ↦ f (q.1 q.2)
      exact f.continuous.comp (continuous_eval.comp (continuous_fst.prodMk continuous_snd))⟩

/-- Helper for Lemma 22.2.4: a relative homotopy from a self-map to the identity induces a
bundled homotopy on the loop space. -/
theorem loopPostcompose_homotopic_to_id_of_homotopyRel
    {f : C(Z, Z)} (H : f.HomotopyRel (ContinuousMap.id Z) ({HSpace.e} : Set Z)) :
    ContinuousMap.Homotopic
      (loopPostcompose f (H.fst_eq_snd (x := HSpace.e) (by simp)))
      (ContinuousMap.id (Ω Z HSpace.e)) := by
  let F : C(Ω Z HSpace.e × I, Ω Z HSpace.e) :=
    ⟨fun p ↦
      { toFun := fun t ↦ H (p.2, p.1 t)
        continuous_toFun := by
          -- The loop parameter is carried through the relative homotopy continuously.
          exact H.continuous.comp (continuous_const.prodMk p.1.continuous)
        source' := by
          -- The relative condition keeps the basepoint fixed at the left endpoint.
          calc
            H (p.2, p.1 0) = f (p.1 0) := by
              exact H.eq_fst p.2 (by simp [p.1.source] : p.1 0 ∈ ({HSpace.e} : Set Z))
            _ = f HSpace.e := by rw [p.1.source]
            _ = HSpace.e := H.fst_eq_snd (x := HSpace.e) (by simp)
        target' := by
          -- The same relative condition keeps the basepoint fixed at the right endpoint.
          calc
            H (p.2, p.1 1) = f (p.1 1) := by
              exact H.eq_fst p.2 (by simp [p.1.target] : p.1 1 ∈ ({HSpace.e} : Set Z))
            _ = f HSpace.e := by rw [p.1.target]
            _ = HSpace.e := H.fst_eq_snd (x := HSpace.e) (by simp) },
      by
        -- Continuity again reduces to the corresponding uncurried map into `Z`.
        apply Path.continuous_uncurry_iff.mp
        change Continuous fun q : ((Ω Z HSpace.e × I) × I) ↦ H (q.1.2, q.1.1 q.2)
        have hLoop :
            Continuous fun q : ((Ω Z HSpace.e × I) × I) ↦ q.1.1 q.2 := by
          exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
        exact H.continuous.comp ((continuous_snd.comp continuous_fst).prodMk hLoop)⟩
  refine ⟨ContinuousMap.Homotopy.ofProdSwap F ?_ ?_⟩
  · intro γ
    -- At time `0`, the loop family is postcomposition by `f₀`.
    ext t
    simp [F, loopPostcompose]
  · intro γ
    -- At time `1`, the loop family is the original loop.
    ext t
    simp [F]

/-- Helper for Lemma 22.2.4: pointwise `HSpace` multiplication on based loops. -/
def loopPointwiseMul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
  ⟨fun p ↦
      ((p.1.prod p.2).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm,
    by
      -- Continuity into the loop space is checked after uncurrying to a map into `Z`.
      apply Path.continuous_uncurry_iff.mp
      change Continuous fun q : ((Ω Z HSpace.e × Ω Z HSpace.e) × I) ↦
        HSpace.hmul (q.1.1 q.2, q.1.2 q.2)
      have hLeft :
          Continuous fun q : ((Ω Z HSpace.e × Ω Z HSpace.e) × I) ↦ q.1.1 q.2 := by
        exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
      have hRight :
          Continuous fun q : ((Ω Z HSpace.e × Ω Z HSpace.e) × I) ↦ q.1.2 q.2 := by
        exact continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
      exact HSpace.hmul.continuous.comp (hLeft.prodMk hRight)⟩

/-- Helper for Lemma 22.2.4: right multiplication by the constant loop is homotopic to the
identity for pointwise `HSpace` multiplication on loops. -/
theorem loopPointwiseMul_rightUnitHomotopy :
    ContinuousMap.Homotopic
      ((loopPointwiseMul (Z := Z)).comp
        ((ContinuousMap.id (Ω Z HSpace.e)).prodMk
          (ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e))))
      (ContinuousMap.id (Ω Z HSpace.e)) := by
  -- Repackage the ambient right-unit relative homotopy as a homotopy of loop maps.
  simpa [loopPointwiseMul, loopPostcompose] using
    (loopPostcompose_homotopic_to_id_of_homotopyRel
      (Z := Z)
      (H := HSpace.hmulE))

/-- Helper for Lemma 22.2.4: left multiplication by the constant loop is homotopic to the
identity for pointwise `HSpace` multiplication on loops. -/
theorem loopPointwiseMul_leftUnitHomotopy :
    ContinuousMap.Homotopic
      ((loopPointwiseMul (Z := Z)).comp
        ((ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e)).prodMk
          (ContinuousMap.id (Ω Z HSpace.e))))
      (ContinuousMap.id (Ω Z HSpace.e)) := by
  -- Repackage the ambient left-unit relative homotopy as a homotopy of loop maps.
  simpa [loopPointwiseMul, loopPostcompose] using
    (loopPostcompose_homotopic_to_id_of_homotopyRel
      (Z := Z)
      (H := HSpace.eHmul))

/-- Helper for Lemma 22.2.4: pointwise `HSpace` multiplication on loops satisfies the strict
interchange law with loop concatenation. -/
  theorem loopPointwiseMul_interchange
    (α β γ δ : Ω Z HSpace.e) :
    HSpace.hmul
      ((loopPointwiseMul (Z := Z) (α, β)), (loopPointwiseMul (Z := Z) (γ, δ))) =
    loopPointwiseMul (Z := Z) (HSpace.hmul (α, γ), HSpace.hmul (β, δ)) := by
  -- Compare the two product paths before mapping by the ambient multiplication.
  change
      ((((α.prod β).map HSpace.hmul.continuous).cast
        HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm).trans
      (((γ.prod δ).map HSpace.hmul.continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm)) =
    (((α.trans γ).prod (β.trans δ)).map HSpace.hmul.continuous).cast
      HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm
  rw [← Path.cast_trans, ← Path.map_trans, Path.trans_prod_eq_prod_trans]

/-- Helper for Lemma 22.2.4: outer loop concatenation is homotopic to pointwise inner
`HSpace` multiplication. -/
theorem loopTransToPointwiseMulHomotopy :
    ContinuousMap.Homotopic
      (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e))
      (loopPointwiseMul (Z := Z)) := by
  let fstMap : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) := ⟨Prod.fst, continuous_fst⟩
  let sndMap : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) := ⟨Prod.snd, continuous_snd⟩
  let constMap : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    ContinuousMap.const _ (Path.refl HSpace.e)
  let innerRight : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (loopPointwiseMul (Z := Z)).comp (fstMap.prodMk constMap)
  let innerLeft : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (loopPointwiseMul (Z := Z)).comp (constMap.prodMk sndMap)
  let outerRight : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp (fstMap.prodMk constMap)
  let outerLeft : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp (constMap.prodMk sndMap)
  have hToInterchange :
      ContinuousMap.Homotopic
        (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e))
        ((HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
          (innerRight.prodMk innerLeft)) := by
    -- Replace each input by its pointwise-inner unit deformation.
    have hProd :
        ContinuousMap.Homotopic (fstMap.prodMk sndMap) (innerRight.prodMk innerLeft) :=
      ContinuousMap.Homotopic.prodMk
        (ContinuousMap.Homotopic.comp
          (loopPointwiseMul_rightUnitHomotopy (Z := Z)).symm
          (ContinuousMap.Homotopic.refl fstMap))
        (ContinuousMap.Homotopic.comp
          (loopPointwiseMul_leftUnitHomotopy (Z := Z)).symm
          (ContinuousMap.Homotopic.refl sndMap))
    have hRaw :=
      ContinuousMap.Homotopic.comp
        (ContinuousMap.Homotopic.refl
          (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)))
        hProd
    have hPairId : fstMap.prodMk sndMap = ContinuousMap.id (Ω Z HSpace.e × Ω Z HSpace.e) := by
      ext p <;> rfl
    simpa [hPairId, innerRight, innerLeft] using hRaw
  have hInterchange :
      (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
          (innerRight.prodMk innerLeft) =
        (loopPointwiseMul (Z := Z)).comp (outerRight.prodMk outerLeft) := by
    -- The strict interchange law identifies the middle two operations pointwise.
    ext p t
    simpa [fstMap, sndMap, constMap, innerRight, innerLeft, outerRight, outerLeft] using
      congrArg (fun η : Ω Z HSpace.e => η t)
        (loopPointwiseMul_interchange
          (Z := Z) p.1 (Path.refl HSpace.e) (Path.refl HSpace.e) p.2)
  have hFromInterchange :
      ContinuousMap.Homotopic
        ((loopPointwiseMul (Z := Z)).comp (outerRight.prodMk outerLeft))
        (loopPointwiseMul (Z := Z)) := by
    -- Collapse the outer unit factors after moving through interchange.
    simpa [fstMap, sndMap, outerRight, outerLeft] using
      ContinuousMap.Homotopic.comp
        (ContinuousMap.Homotopic.refl (loopPointwiseMul (Z := Z)))
        (ContinuousMap.Homotopic.prodMk
          (show ContinuousMap.Homotopic outerRight fstMap from
            by
              simpa [outerRight, fstMap] using
                ContinuousMap.Homotopic.comp
                  (show ContinuousMap.Homotopic
                      ((HSpace.hmul :
                        C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
                        ((ContinuousMap.id (Ω Z HSpace.e)).prodMk
                          (ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e))))
                      (ContinuousMap.id (Ω Z HSpace.e)) from
                    ⟨HSpace.hmulE.toHomotopy⟩)
                  (ContinuousMap.Homotopic.refl fstMap))
          (show ContinuousMap.Homotopic outerLeft sndMap from
            by
              simpa [outerLeft, sndMap] using
                ContinuousMap.Homotopic.comp
                  (show ContinuousMap.Homotopic
                      ((HSpace.hmul :
                        C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
                        ((ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e)).prodMk
                          (ContinuousMap.id (Ω Z HSpace.e))))
                      (ContinuousMap.id (Ω Z HSpace.e)) from
                    ⟨HSpace.eHmul.toHomotopy⟩)
                  (ContinuousMap.Homotopic.refl sndMap)))
  -- Compose the two unit reductions with the exact interchange identification.
  exact hToInterchange.trans (hInterchange ▸ hFromInterchange)

/-- Helper for Lemma 22.2.4: pointwise inner `HSpace` multiplication is homotopic to swapped
outer loop concatenation. -/
theorem loopPointwiseMulToSwapHomotopy :
    ContinuousMap.Homotopic
      (loopPointwiseMul (Z := Z))
      (hSpaceMulSwap (Ω Z HSpace.e)) := by
  let fstMap : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) := ⟨Prod.fst, continuous_fst⟩
  let sndMap : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) := ⟨Prod.snd, continuous_snd⟩
  let constMap : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    ContinuousMap.const _ (Path.refl HSpace.e)
  let outerLeftFst : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp (constMap.prodMk fstMap)
  let outerRightSnd : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp (sndMap.prodMk constMap)
  let innerLeftSnd : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (loopPointwiseMul (Z := Z)).comp (constMap.prodMk sndMap)
  let innerRightFst : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e) :=
    (loopPointwiseMul (Z := Z)).comp (fstMap.prodMk constMap)
  have hToInterchange :
      ContinuousMap.Homotopic
        (loopPointwiseMul (Z := Z))
        ((loopPointwiseMul (Z := Z)).comp (outerLeftFst.prodMk outerRightSnd)) := by
    -- Insert the outer unit homotopies on the two factors before applying interchange.
    have hOuterLeft :
        ContinuousMap.Homotopic fstMap outerLeftFst := by
      have hBasic :
          ContinuousMap.Homotopic
            (ContinuousMap.id (Ω Z HSpace.e))
            ((HSpace.hmul :
              C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
              ((ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e)).prodMk
                (ContinuousMap.id (Ω Z HSpace.e)))) :=
        (show ContinuousMap.Homotopic
            ((HSpace.hmul :
              C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
              ((ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e)).prodMk
                (ContinuousMap.id (Ω Z HSpace.e))))
            (ContinuousMap.id (Ω Z HSpace.e)) from
          ⟨HSpace.eHmul.toHomotopy⟩).symm
      simpa [outerLeftFst, fstMap] using
        ContinuousMap.Homotopic.comp hBasic (ContinuousMap.Homotopic.refl fstMap)
    have hOuterRight :
        ContinuousMap.Homotopic sndMap outerRightSnd := by
      have hBasic :
          ContinuousMap.Homotopic
            (ContinuousMap.id (Ω Z HSpace.e))
            ((HSpace.hmul :
              C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
              ((ContinuousMap.id (Ω Z HSpace.e)).prodMk
                (ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e)))) :=
        (show ContinuousMap.Homotopic
            ((HSpace.hmul :
              C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
              ((ContinuousMap.id (Ω Z HSpace.e)).prodMk
                (ContinuousMap.const (Ω Z HSpace.e) (Path.refl HSpace.e))))
            (ContinuousMap.id (Ω Z HSpace.e)) from
          ⟨HSpace.hmulE.toHomotopy⟩).symm
      simpa [outerRightSnd, sndMap] using
        ContinuousMap.Homotopic.comp hBasic (ContinuousMap.Homotopic.refl sndMap)
    have hProd :
        ContinuousMap.Homotopic (fstMap.prodMk sndMap) (outerLeftFst.prodMk outerRightSnd) :=
      ContinuousMap.Homotopic.prodMk hOuterLeft hOuterRight
    have hRaw :=
      ContinuousMap.Homotopic.comp
        (ContinuousMap.Homotopic.refl (loopPointwiseMul (Z := Z)))
        hProd
    have hPairId : fstMap.prodMk sndMap = ContinuousMap.id (Ω Z HSpace.e × Ω Z HSpace.e) := by
      ext p <;> rfl
    simpa [hPairId, outerLeftFst, outerRightSnd] using hRaw
  have hInterchange :
      (loopPointwiseMul (Z := Z)).comp (outerLeftFst.prodMk outerRightSnd) =
        (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
          (innerLeftSnd.prodMk innerRightFst) := by
    -- The strict interchange law turns the outer-unit factors into the swapped outer product.
    ext p t
    simpa [fstMap, sndMap, constMap, outerLeftFst, outerRightSnd, innerLeftSnd, innerRightFst] using
      congrArg (fun η : Ω Z HSpace.e => η t)
        (loopPointwiseMul_interchange
          (Z := Z) (Path.refl HSpace.e) p.2 p.1 (Path.refl HSpace.e)).symm
  have hFromInterchange :
      ContinuousMap.Homotopic
        ((HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)).comp
          (innerLeftSnd.prodMk innerRightFst))
        (hSpaceMulSwap (Ω Z HSpace.e)) := by
    -- Remove the inner unit factors to reach the swapped outer multiplication.
    simpa [hSpaceMulSwap, fstMap, sndMap, innerLeftSnd, innerRightFst] using
      ContinuousMap.Homotopic.comp
        (ContinuousMap.Homotopic.refl
          (HSpace.hmul : C(Ω Z HSpace.e × Ω Z HSpace.e, Ω Z HSpace.e)))
        (ContinuousMap.Homotopic.prodMk
          (show ContinuousMap.Homotopic innerLeftSnd sndMap from
            by
              simpa [innerLeftSnd, sndMap] using
                ContinuousMap.Homotopic.comp
                  (loopPointwiseMul_leftUnitHomotopy (Z := Z))
                  (ContinuousMap.Homotopic.refl sndMap))
          (show ContinuousMap.Homotopic innerRightFst fstMap from
            by
              simpa [innerRightFst, fstMap] using
                ContinuousMap.Homotopic.comp
                  (loopPointwiseMul_rightUnitHomotopy (Z := Z))
                  (ContinuousMap.Homotopic.refl fstMap)))
  -- Compose the outer-unit insertion, the exact interchange identity,
  -- and the final inner reduction.
  exact hToInterchange.trans (hInterchange ▸ hFromInterchange)

end DoubleLoopAux

/-- Lemma 22.2.4 (4): for every basepoint `y : Y`, the double loop space
`Ω (Ω Y y) (Path.refl y)` is homotopy-commutative for its canonical `HSpace` multiplication. -/
theorem doubleLoopSpace_homotopyCommutative (y : Y) :
    ContinuousMap.Homotopic
      (HSpace.hmul :
        C((Ω (Ω Y y) (Path.refl y)) × (Ω (Ω Y y) (Path.refl y)), Ω (Ω Y y) (Path.refl y)))
      (hSpaceMulSwap (Ω (Ω Y y) (Path.refl y))) :=
  by
    -- Route correction: use the abstract interchange square on the loop space `Ω Y y`, then
    -- compose the two bundled bridge homotopies through pointwise inner multiplication.
    exact
      (loopTransToPointwiseMulHomotopy (Z := Ω Y y)).trans
        (loopPointwiseMulToSwapHomotopy (Z := Ω Y y))
