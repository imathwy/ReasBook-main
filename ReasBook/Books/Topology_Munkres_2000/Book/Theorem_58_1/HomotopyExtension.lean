module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

public section

open scoped ContinuousMap
open unitInterval

namespace HomotopyExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Helper for Theorem 58.1: a homotopy followed by its reverse contracts to its
initial map while fixing the two ends of the path parameter. -/
lemma backtrackNullHomotopy {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    Nonempty <| ContinuousMap.HomotopyRel (H.trans H.symm).toContinuousMap
      (f.comp (ContinuousMap.snd : C(I × X, X)))
      {p : I × X | p.1 = 0 ∨ p.1 = 1} := by
  -- Reverse the standard tent contraction so that its zero face is the backtrack.
  have hNContinuous : Continuous (fun q : I × (I × X) ↦ H
      (⟨Path.Homotopy.reflTransSymmAux (σ q.1, q.2.1),
        Path.Homotopy.reflTransSymmAux_mem_I (σ q.1, q.2.1)⟩, q.2.2)) := by
    apply H.continuous.comp
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact Path.Homotopy.continuous_reflTransSymmAux.comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk
          (continuous_fst.comp continuous_snd))
    · exact continuous_snd.comp continuous_snd
  let N : C(I × (I × X), Y) :=
    ⟨fun q ↦ H
        (⟨Path.Homotopy.reflTransSymmAux (σ q.1, q.2.1),
          Path.Homotopy.reflTransSymmAux_mem_I (σ q.1, q.2.1)⟩, q.2.2),
      hNContinuous⟩
  refine ⟨
    { toFun := N
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
  · -- At outer time zero the tent parameter traverses `H` and then `H.symm`.
    intro p
    change N (0, p) = (H.trans H.symm) p
    rw [ContinuousMap.Homotopy.trans_apply]
    simp only [N, ContinuousMap.coe_mk]
    split_ifs with hp
    · apply congrArg H
      apply Prod.ext
      · apply Subtype.ext
        simp only [Path.Homotopy.reflTransSymmAux, coe_symm_eq,
          if_pos hp]
        norm_num
      · rfl
    · rw [ContinuousMap.Homotopy.symm_apply]
      apply congrArg H
      apply Prod.ext
      · apply Subtype.ext
        simp only [Path.Homotopy.reflTransSymmAux, coe_symm_eq,
          if_neg hp]
        norm_num
        ring
      · rfl
  · -- At outer time one the tent has collapsed to the initial endpoint of `H`.
    intro p
    change N (1, p) = f p.2
    have hParameter :
        (⟨Path.Homotopy.reflTransSymmAux (σ (1 : I), p.1),
          Path.Homotopy.reflTransSymmAux_mem_I (σ (1 : I), p.1)⟩ : I) = 0 := by
      apply Subtype.ext
      simp only [Path.Homotopy.reflTransSymmAux, coe_symm_eq]
      split_ifs <;> norm_num
    change H
      (⟨Path.Homotopy.reflTransSymmAux (σ (1 : I), p.1),
        Path.Homotopy.reflTransSymmAux_mem_I (σ (1 : I), p.1)⟩, p.2) = _
    rw [hParameter, H.apply_zero]
  · -- At either path endpoint the tent parameter is zero, so the contraction is fixed.
    intro u p hp
    rcases p with ⟨t, x⟩
    change N (u, (t, x)) = (H.trans H.symm) (t, x)
    rcases hp with hp | hp
    · change t = 0 at hp
      subst t
      have hParameter :
          (⟨Path.Homotopy.reflTransSymmAux (σ u, (0 : I)),
            Path.Homotopy.reflTransSymmAux_mem_I (σ u, (0 : I))⟩ : I) = 0 := by
        apply Subtype.ext
        simp only [Path.Homotopy.reflTransSymmAux, coe_symm_eq, Set.Icc.coe_zero]
        have hZeroHalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
        rw [if_pos hZeroHalf]
        norm_num
      change H
        (⟨Path.Homotopy.reflTransSymmAux (σ u, (0 : I)),
          Path.Homotopy.reflTransSymmAux_mem_I (σ u, (0 : I))⟩, x) = _
      rw [hParameter, H.apply_zero, (H.trans H.symm).apply_zero]
    · change t = 1 at hp
      subst t
      have hParameter :
          (⟨Path.Homotopy.reflTransSymmAux (σ u, (1 : I)),
            Path.Homotopy.reflTransSymmAux_mem_I (σ u, (1 : I))⟩ : I) = 0 := by
        apply Subtype.ext
        simp only [Path.Homotopy.reflTransSymmAux, coe_symm_eq, Set.Icc.coe_one]
        have hOneHalf : ¬ (1 : ℝ) ≤ 1 / 2 := by norm_num
        rw [if_neg hOneHalf]
        norm_num
      change H
        (⟨Path.Homotopy.reflTransSymmAux (σ u, (1 : I)),
          Path.Homotopy.reflTransSymmAux_mem_I (σ u, (1 : I))⟩, x) = _
      rw [hParameter, H.apply_zero, (H.trans H.symm).apply_one]

/-- Helper for Theorem 58.1: the ambient self-map of a retraction is idempotent. -/
lemma retractionAmbient_idempotent {A : Set X} (r : Set.Retraction A) :
    r.toAmbient.comp r.toAmbient = r.toAmbient := by
  -- Apply the retraction law to the already-retracted point.
  ext x
  exact congrArg Subtype.val (r.leftInverse (r.apply x))

/-- Helper for Theorem 58.1: modify an ordinary retraction homotopy so that its
restriction to the retract is a canonical backtrack with a relative contraction. -/
lemma existsRetractionBacktrack {A : Set X} (r : Set.Retraction A)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) r.toAmbient) :
    ∃ K : ContinuousMap.Homotopy (ContinuousMap.id X) r.toAmbient,
      ∃ N : ContinuousMap.HomotopyRel (H.trans H.symm).toContinuousMap
        ((ContinuousMap.id X).comp (ContinuousMap.snd : C(I × X, X)))
        {p : I × X | p.1 = 0 ∨ p.1 = 1},
        ∀ (t : I) (a : A), K (t, a) = N (0, (t, a)) := by
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hIdComp : (ContinuousMap.id X).comp r.toAmbient = r.toAmbient := by
    ext x
    rfl
  have hRetractionComp : r.toAmbient.comp r.toAmbient = r.toAmbient :=
    retractionAmbient_idempotent r
  let Q : ContinuousMap.Homotopy r.toAmbient r.toAmbient :=
    (H.compContinuousMap r.toAmbient).cast hIdComp hRetractionComp
  let K : ContinuousMap.Homotopy (ContinuousMap.id X) r.toAmbient := H.trans Q.symm
  have hRestriction (t : I) (a : A) :
      K (t, a) = (H.trans H.symm) (t, a) := by
    -- Both backtracks use `H`; on the second half use that `r` fixes every point of `A`.
    change (H.trans Q.symm) (t, i a) = (H.trans H.symm) (t, i a)
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · rfl
    · rw [ContinuousMap.Homotopy.symm_apply,
        ContinuousMap.Homotopy.symm_apply]
      change H (_, r.toAmbient (i a)) = H (_, i a)
      exact congrArg (fun x ↦ H (_, x))
        (congrArg Subtype.val (r.leftInverse a))
  -- The ambient tent contraction agrees with `K` on `A` at outer time zero.
  obtain ⟨N⟩ := backtrackNullHomotopy H
  refine ⟨K, N, ?_⟩
  intro t a
  calc
    K (t, a) = (H.trans H.symm) (t, a) := hRestriction t a
    _ = N (0, (t, a)) := (N.apply_zero (t, a)).symm

/-- Helper for Theorem 58.1: extend a contraction prescribed on the subspace face
and the original homotopy prescribed on the zero outer face. -/
lemma existsExtensionOfRestrictionContraction {f g : C(X, X)} (A : Set X)
    (hA : IsClosed A) (K : ContinuousMap.Homotopy f g)
    {n₀ n₁ : C(I × X, X)}
    (N : ContinuousMap.HomotopyRel n₀ n₁
      {p : I × X | p.1 = 0 ∨ p.1 = 1})
    (hAgree : ∀ (t : I) (a : A), K (t, a) = N (0, (t, a)))
    (hExtension : Set.IsRetract
      {q : (X × I) × I | q.2 = 0 ∨ q.1.1 ∈ A}) :
    ∃ F : C((X × I) × I, X),
      (∀ (z : X) (t : I), F ((z, t), 0) = K (t, z)) ∧
      ∀ (a : A) (t u : I), F ((a, t), u) = N (u, (t, a)) := by
  classical
  let S₀ : Set ((X × I) × I) := {q | q.2 = 0}
  let Sₐ : Set ((X × I) × I) := {q | q.1.1 ∈ A}
  let E : Set ((X × I) × I) := {q | q.2 = 0 ∨ q.1.1 ∈ A}
  let b : (X × I) × I → X := fun q ↦
    if q.2 = 0 then K (q.1.2, q.1.1) else N (q.2, (q.1.2, q.1.1))
  have hK : Continuous (fun q : (X × I) × I ↦ K (q.1.2, q.1.1)) :=
    K.continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_fst))
  have hN : Continuous (fun q : (X × I) × I ↦
      N (q.2, (q.1.2, q.1.1))) :=
    N.continuous.comp <| continuous_snd.prodMk
      ((continuous_snd.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_fst))
  have hb₀ : ContinuousOn b S₀ := by
    -- On the zero face the pasted function is exactly `K`.
    apply hK.continuousOn.congr
    intro q hq
    change q.2 = 0 at hq
    simp only [b]
    rw [if_pos hq]
  have hbₐ : ContinuousOn b Sₐ := by
    -- On the `A`-face the two branches agree at their common zero edge.
    apply hN.continuousOn.congr
    intro q hq
    simp only [b]
    split_ifs with hu
    · rw [hu]
      exact hAgree q.1.2 ⟨q.1.1, hq⟩
    · rfl
  have hS₀ : IsClosed S₀ := by
    exact isClosed_singleton.preimage continuous_snd
  have hSₐ : IsClosed Sₐ := by
    exact hA.preimage (continuous_fst.comp continuous_fst)
  have hbE : ContinuousOn b E := by
    -- Closed-set pasting gives continuity on the whole extension domain.
    have hbUnion := hb₀.union_of_isClosed hbₐ hS₀ hSₐ
    have hE : E = S₀ ∪ Sₐ := by
      ext q
      rfl
    rw [hE]
    exact hbUnion
  let B : C(E, X) := ⟨fun q ↦ b q, hbE.restrict⟩
  have hExtensionE : Set.IsRetract E := by
    simpa only [E] using hExtension
  obtain ⟨eMap, heMap⟩ := (Set.isRetract_iff E).mp hExtensionE
  let e : Set.Retraction E := Set.Retraction.ofContinuousMap eMap heMap
  let F : C((X × I) × I, X) := B.comp e.toContinuousMap
  have hF (q : (X × I) × I) (hq : q ∈ E) : F q = b q := by
    -- The supplied retraction fixes every point of the pasted boundary.
    change B (e.toContinuousMap q) = B ⟨q, hq⟩
    exact congrArg B (e.leftInverse ⟨q, hq⟩)
  refine ⟨F, ?_, ?_⟩
  · intro z t
    rw [hF ((z, t), 0) (Or.inl rfl)]
    simp only [b, if_pos rfl]
  · intro a t u
    rw [hF ((a, t), u) (Or.inr a.2)]
    simp only [b]
    split_ifs with hu
    · rw [hu]
      exact hAgree t a
    · rfl

/-- Helper for Theorem 58.1: the three remaining edges of an extension square
assemble to a homotopy fixed on the prescribed subspace. -/
lemma homotopyRel_of_extensionSquare {f g : C(X, X)} (A : Set X)
    (K : ContinuousMap.Homotopy f g)
    {n₀ : C(I × X, X)}
    (N : ContinuousMap.HomotopyRel n₀
      ((ContinuousMap.id X).comp (ContinuousMap.snd : C(I × X, X)))
      {p : I × X | p.1 = 0 ∨ p.1 = 1})
    (hAgree : ∀ (t : I) (a : A), K (t, a) = N (0, (t, a)))
    (F : C((X × I) × I, X))
    (hFzero : ∀ (z : X) (t : I), F ((z, t), 0) = K (t, z))
    (hFA : ∀ (a : A) (t u : I), F ((a, t), u) = N (u, (t, a))) :
    Nonempty <| ContinuousMap.HomotopyRel f g A := by
  have hfA (a : A) : f a = a := by
    -- The lower-left corner is fixed because `N` is relative to the path endpoints.
    calc
      f a = K (0, a) := (K.apply_zero a).symm
      _ = N (0, (0, a)) := hAgree 0 a
      _ = a := by
        simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply,
          ContinuousMap.snd_apply] using
            N.eq_snd 0 (x := ((0 : I), (a : X))) (Or.inl rfl)
  have hp₀Continuous : Continuous (fun z : X ↦ F ((z, 0), 1)) := by
    fun_prop
  let p₀ : C(X, X) := ⟨fun z ↦ F ((z, 0), 1), hp₀Continuous⟩
  have hp₁Continuous : Continuous (fun z : X ↦ F ((z, 1), 1)) := by
    fun_prop
  let p₁ : C(X, X) := ⟨fun z ↦ F ((z, 1), 1), hp₁Continuous⟩
  have hp₀A (a : A) : p₀ a = a := by
    change F ((a, 0), 1) = a
    rw [hFA a 0 1, N.apply_one]
    rfl
  have hp₁A (a : A) : p₁ a = a := by
    change F ((a, 1), 1) = a
    rw [hFA a 1 1, N.apply_one]
    rfl
  have hLowerContinuous : Continuous (fun q : I × X ↦ F ((q.2, 0), q.1)) := by
    fun_prop
  let lowerMap : C(I × X, X) :=
    ⟨fun q ↦ F ((q.2, 0), q.1), hLowerContinuous⟩
  have hLowerZero (z : X) : lowerMap (0, z) = f z := by
    change F ((z, 0), 0) = f z
    rw [hFzero z 0, K.apply_zero]
  have hLowerOne (z : X) : lowerMap (1, z) = p₀ z := by
    rfl
  have hLowerRelative (u : I) (z : X) (hz : z ∈ A) : lowerMap (u, z) = f z := by
    let a : A := ⟨z, hz⟩
    calc
      lowerMap (u, z) = F ((a, 0), u) := rfl
      _ = N (u, (0, a)) := hFA a 0 u
      _ = a := by
        simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply,
          ContinuousMap.snd_apply] using
            N.eq_snd u (x := ((0 : I), (a : X))) (Or.inl rfl)
      _ = f z := (hfA a).symm
  let lower : ContinuousMap.HomotopyRel f p₀ A :=
    { toFun := lowerMap
      map_zero_left := hLowerZero
      map_one_left := hLowerOne
      prop' := hLowerRelative }
  have hMiddleContinuous : Continuous (fun q : I × X ↦ F ((q.2, q.1), 1)) := by
    fun_prop
  let middleMap : C(I × X, X) :=
    ⟨fun q ↦ F ((q.2, q.1), 1), hMiddleContinuous⟩
  have hMiddleZero (z : X) : middleMap (0, z) = p₀ z := by
    rfl
  have hMiddleOne (z : X) : middleMap (1, z) = p₁ z := by
    rfl
  have hMiddleRelative (t : I) (z : X) (hz : z ∈ A) : middleMap (t, z) = p₀ z := by
    let a : A := ⟨z, hz⟩
    calc
      middleMap (t, z) = F ((a, t), 1) := rfl
      _ = N (1, (t, a)) := hFA a t 1
      _ = a := by
        rw [N.apply_one]
        rfl
      _ = p₀ z := (hp₀A a).symm
  let middle : ContinuousMap.HomotopyRel p₀ p₁ A :=
    { toFun := middleMap
      map_zero_left := hMiddleZero
      map_one_left := hMiddleOne
      prop' := hMiddleRelative }
  have hUpperContinuous : Continuous (fun q : I × X ↦ F ((q.2, 1), σ q.1)) := by
    fun_prop
  let upperMap : C(I × X, X) :=
    ⟨fun q ↦ F ((q.2, 1), σ q.1), hUpperContinuous⟩
  have hUpperZero (z : X) : upperMap (0, z) = p₁ z := by
    change F ((z, 1), σ (0 : I)) = F ((z, 1), 1)
    rw [unitInterval.symm_zero]
  have hUpperOne (z : X) : upperMap (1, z) = g z := by
    change F ((z, 1), σ (1 : I)) = g z
    rw [unitInterval.symm_one, hFzero z 1, K.apply_one]
  have hUpperRelative (u : I) (z : X) (hz : z ∈ A) : upperMap (u, z) = p₁ z := by
    let a : A := ⟨z, hz⟩
    calc
      upperMap (u, z) = F ((a, 1), σ u) := rfl
      _ = N (σ u, (1, a)) := hFA a 1 (σ u)
      _ = a := by
        simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply,
          ContinuousMap.snd_apply] using
            N.eq_snd (σ u) (x := ((1 : I), (a : X))) (Or.inr rfl)
      _ = p₁ z := (hp₁A a).symm
  let upper : ContinuousMap.HomotopyRel p₁ g A :=
    { toFun := upperMap
      map_zero_left := hUpperZero
      map_one_left := hUpperOne
      prop' := hUpperRelative }
  -- Concatenate the lower, final vertical, and reversed upper edges.
  exact ⟨(lower.trans middle).trans upper⟩

end HomotopyExtension
