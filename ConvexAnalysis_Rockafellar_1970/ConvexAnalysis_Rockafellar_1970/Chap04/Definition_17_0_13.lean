import ConvexAnalysis_Rockafellar_1970.Chap01.AffineDimension
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_9
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AffineSubspace
open Set Submodule
open scoped Pointwise
open scoped Rockafellar

attribute [local instance] Classical.propDecidable

variable {E : Type*}
variable {n m : ℕ}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.0.13 introduces affine independence for a finite mixed family of
  points and directions in a scalar module.
- `core/canonical`: the owner abstraction for the independence predicate is the homogenized
  `LinearIndependent` family in `𝕜 × E`; the chapter affine owner
  `mixedAffineHull 𝕜 (Set.range points) (Set.range directions)` and
  `AffineSubspace.affineDim` provide the canonical affine-dimension view of the same notion.
- `bridge/view`: the finite families enter the owner abstractions through the canonical sets
  `Set.range points` and `Set.range directions`; the theorem
  `mixedAffineIndependent_iff_affineDim_eq` then recovers the textbook affine-dimension criterion.
- Primitive data vs derived API: the primitive data are the two finite families `points` and
  `directions`; the source-facing predicate and the affine-hull dimension criterion are both
  derived from those data.
- owner shape: the scalar parameter is explicit in
  `mixedAffineIndependent 𝕜 points directions` because it is mathematically essential and not
  recoverable from the family arguments alone.

Domain-style sampling used here:
- `AffineSubspace.affineDim` from `Items/Chap01/AffineDimension.lean`;
- `finiteDimensional_direction_affineSpan_range` and `FiniteDimensional.span_of_finite` from
  mathlib's affine and linear finite-dimensional owner API for finite families;
- `AffineIndependent` and the affine-dimension bridge from `Items/Chap01/Text_1_9.lean`;
- the chapter owner abstraction `mixedAffineHull` from
  `Items/Chap04/Definition_17_0_12.lean`.
-/

section Independence

variable {𝕜 : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

variable (𝕜) in
/-- Definition 17.0.13: a finite mixed family of points and directions is affinely independent
when its homogenized point and direction vectors form a linearly independent family in `𝕜 × E`;
the affine-dimension criterion is recovered below as a bridge theorem. Since affine independence
still needs an actual point to anchor the affine hull, the zero-point case is allowed exactly for
the empty mixed family. -/
def mixedAffineIndependent {ι κ : Type*} (points : ι → E) (directions : κ → E) : Prop :=
  (Nonempty ι ∨ IsEmpty κ) ∧
    LinearIndependent 𝕜
      (Sum.elim (fun i ↦ ((1 : 𝕜), points i)) fun j ↦ ((0 : 𝕜), directions j))

/-- Textbook notation for mixed affine independence of a finite family of points and directions.
-/
scoped[Rockafellar] notation3:max "maffind[" 𝕜 "](" points " | " directions ")" =>
  mixedAffineIndependent 𝕜 points directions

-- Proof sketch: the guard in `mixedAffineIndependent` forces point nonemptiness whenever there is
-- at least one direction index.
/-- A mixed-affinely-independent family with a nonempty direction index has a nonempty point
index. -/
theorem mixedAffineIndependent_nonempty_points_of_nonempty_directions
    {ι κ : Type*} (points : ι → E) (directions : κ → E)
    (hκ : Nonempty κ) (hindep : maffind[𝕜](points | directions)) :
    Nonempty ι := by
  rcases hindep.1 with hi | hk
  · exact hi
  · exact False.elim (hk.false hκ.some)

-- Proof sketch: the owner predicate carries the guard `Nonempty ι ∨ IsEmpty κ`. If the total
-- mixed index `ι ⊕ κ` is nonempty, this guard forces `ι` itself to be nonempty.
/-- A nonempty mixed index for an affinely independent mixed family contains a point index. -/
theorem mixedAffineIndependent_nonempty_points_of_nonempty
    {ι κ : Type*} (points : ι → E) (directions : κ → E)
    (hne : Nonempty (ι ⊕ κ)) (hindep : maffind[𝕜](points | directions)) :
    Nonempty ι := by
  rcases hne with ⟨x⟩
  cases x with
  | inl i => exact ⟨i⟩
  | inr k =>
      exact mixedAffineIndependent_nonempty_points_of_nonempty_directions
        (𝕜 := 𝕜) points directions ⟨k⟩ hindep

-- Proof sketch: when the point index is nonempty, this is exactly the guard-specialized form of
-- the owner definition.
/-- With a nonempty point index, mixed affine independence is exactly linear independence of the
homogenized mixed family. -/
theorem mixedAffineIndependent_iff_linearIndependent_homogenized
    {ι κ : Type*} [Nonempty ι] (points : ι → E) (directions : κ → E) :
    maffind[𝕜](points | directions) ↔
      LinearIndependent 𝕜
        (Sum.elim (fun i ↦ ((1 : 𝕜), points i)) fun j ↦ ((0 : 𝕜), directions j)) := by
  constructor
  · intro hindep
    exact hindep.2
  · intro hlin
    exact ⟨Or.inl (inferInstance : Nonempty ι), hlin⟩

-- Proof sketch: this is the nonempty-point specialization of the owner definition, since the
-- guard `Nonempty (Fin (n + 1)) ∨ IsEmpty (Fin m)` is automatic.
/-- For a nonempty point family, mixed affine independence is equivalent to linear independence of
its homogenized point and direction vectors in `𝕜 × E`. -/
private theorem mixedAffineIndependent_iff_linearIndependent_homogenized_append
    (points : Fin (n + 1) → E) (directions : Fin m → E) :
    maffind[𝕜](points | directions) ↔
      LinearIndependent 𝕜
        (Fin.append (fun i ↦ ((1 : 𝕜), points i)) fun j ↦ ((0 : 𝕜), directions j)) := by
  let fFin : Fin (n + 1 + m) → 𝕜 × E :=
    Fin.append (fun i ↦ ((1 : 𝕜), points i)) (fun j ↦ ((0 : 𝕜), directions j))
  let fSum : Fin (n + 1) ⊕ Fin m → 𝕜 × E :=
    Sum.elim (fun i ↦ ((1 : 𝕜), points i)) (fun j ↦ ((0 : 𝕜), directions j))
  have hcomp : fFin ∘ (finSumFinEquiv : Fin (n + 1) ⊕ Fin m ≃ Fin (n + 1 + m)) = fSum := by
    funext x
    cases x <;> simp [fFin, fSum]
  have hli : LinearIndependent 𝕜 fSum ↔ LinearIndependent 𝕜 fFin := by
    simpa [hcomp] using
      (linearIndependent_equiv
        (finSumFinEquiv : Fin (n + 1) ⊕ Fin m ≃ Fin (n + 1 + m)) (f := fFin))
  have hsum :
      maffind[𝕜](points | directions) ↔ LinearIndependent 𝕜 fSum := by
    simpa [fSum] using
      (mixedAffineIndependent_iff_linearIndependent_homogenized
        (𝕜 := 𝕜) (points := points) (directions := directions))
  exact hsum.trans hli

end Independence

section AffineHullBridge

variable {𝕜 : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {P : Type*} [AddTorsor E P]

/-- The mixed affine hull is the affine span of the translates of the listed points by the span of
its listed directions. -/
theorem mixedAffineHull_eq_affineSpan_translates
    {ι κ : Type*} (points : ι → P) (directions : κ → E) :
    mixedAffineHull 𝕜 (range points) (range directions) =
      affineSpan 𝕜 ((span 𝕜 (range directions) : Set E) +ᵥ range points) := rfl

end AffineHullBridge

section AffineDim

variable {𝕜 : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

instance finiteDimensional_direction_mixedAffineHull_range
    {ι κ : Type*} [Finite ι] [Finite κ]
    (points : ι → E) (directions : κ → E) :
    FiniteDimensional 𝕜 (mixedAffineHull 𝕜 (range points) (range directions)).direction := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  let carrier : Submodule 𝕜 E := span 𝕜 (range points ∪ range directions)
  let A : AffineSubspace 𝕜 E := carrier.toAffineSubspace
  have hcarrier :
      ((span 𝕜 (range directions) : Set E) +ᵥ range points) ⊆
        (carrier : Set E) := by
    intro x hx
    rcases Set.mem_vadd.mp hx with ⟨v, hv, p, hp, rfl⟩
    rcases hp with ⟨i, rfl⟩
    simpa [vadd_eq_add] using carrier.add_mem
      ((span_mono fun _ hy ↦ Or.inr hy) hv)
      (Submodule.subset_span <| Or.inl ⟨i, rfl⟩)
  have hle : mixedAffineHull 𝕜 (range points) (range directions) ≤ A := by
    rw [mixedAffineHull_eq_affineSpan_translates]
    exact affineSpan_le_of_subset_coe hcarrier
  letI : FiniteDimensional 𝕜 carrier :=
    FiniteDimensional.span_of_finite 𝕜 <|
      (Set.finite_range points).union (Set.finite_range directions)
  letI : FiniteDimensional 𝕜 A.direction := by
    let hdir : A.direction = carrier := by
      simp [A, Submodule.toAffineSubspace_direction]
    exact hdir ▸ (inferInstance : FiniteDimensional 𝕜 carrier)
  exact FiniteDimensional.of_injective
    (Submodule.inclusion <| AffineSubspace.direction_le hle)
    (Submodule.inclusion_injective _)

private theorem linearIndependent_homogenized_iff_affineIndependent_append
    (points : Fin (n + 1) → E) (directions : Fin m → E) :
    LinearIndependent 𝕜
        (Fin.append (fun i ↦ ((1 : 𝕜), points i)) fun j ↦ ((0 : 𝕜), directions j)) ↔
      AffineIndependent 𝕜 (Fin.append points (fun j => points 0 + directions j)) := by
  let I : Type := Fin (n + 1) ⊕ Fin m
  let K : Type := Fin n ⊕ Fin m
  let hF : Fin (n + 1 + m) → 𝕜 × E :=
    Fin.append (fun i ↦ ((1 : 𝕜), points i)) (fun j => ((0 : 𝕜), directions j))
  let qF : Fin (n + 1 + m) → E :=
    Fin.append points (fun j => points 0 + directions j)
  let hS : I → 𝕜 × E := Sum.elim (fun i => ((1 : 𝕜), points i)) (fun j => ((0 : 𝕜), directions j))
  let qS : I → E := Sum.elim points (fun j => points 0 + directions j)
  have hh : hF ∘ (finSumFinEquiv : I ≃ Fin (n + 1 + m)) = hS := by
    funext x
    cases x <;> simp [hF, hS]
  have hq : qF ∘ (finSumFinEquiv : I ≃ Fin (n + 1 + m)) = qS := by
    funext x
    cases x <;> simp [qF, qS]
  have hli : LinearIndependent 𝕜 hF ↔ LinearIndependent 𝕜 hS := by
    simpa [hh] using (linearIndependent_equiv (finSumFinEquiv : I ≃ Fin (n + 1 + m)) (f := hF)).symm
  have hai : AffineIndependent 𝕜 qF ↔ AffineIndependent 𝕜 qS := by
    simpa [hq] using (affineIndependent_equiv (finSumFinEquiv : I ≃ Fin (n + 1 + m)) (p := qF)).symm
  let emb : K → I := Sum.elim (fun i => Sum.inl i.succ) Sum.inr
  let restE : K → E := Sum.elim (fun i => points i.succ - points 0) directions
  let J : Type := {x : I // x ≠ Sum.inl (0 : Fin (n + 1))}
  let dSub : J → E := fun i => qS i - qS (Sum.inl (0 : Fin (n + 1)))
  let eJK : K ≃ J := by
    refine
      { toFun := fun k => ⟨emb k, by
          cases k with
          | inl i =>
              intro h
              exact Fin.succ_ne_zero i (Sum.inl.inj h)
          | inr j => simp [emb]
        ⟩
        invFun := fun x => by
          rcases x with ⟨x, hx⟩
          cases x with
          | inl i =>
              exact Sum.inl (i.pred (by
                intro hi
                apply hx
                simp [hi]))
          | inr j => exact Sum.inr j
        left_inv := ?_
        right_inv := ?_ }
    · intro k
      cases k with
      | inl i => simp [emb]
      | inr j => rfl
    · intro x
      rcases x with ⟨x, hx⟩
      apply Subtype.ext
      cases x with
      | inl i =>
          simp [emb, Fin.succ_pred i (by
            intro hi
            apply hx
            simp [hi])]
      | inr j => rfl
  have hqS_core : AffineIndependent 𝕜 qS ↔ LinearIndependent 𝕜 restE := by
    have h1 : AffineIndependent 𝕜 qS ↔ LinearIndependent 𝕜 dSub := by
      simpa [dSub] using
        (affineIndependent_iff_linearIndependent_vsub 𝕜 qS (Sum.inl (0 : Fin (n + 1))))
    have hd : dSub ∘ eJK = restE := by
      funext k
      cases k with
      | inl i => simp [dSub, eJK, emb, restE, qS]
      | inr j => simp [dSub, eJK, emb, restE, qS]
    have h2 : LinearIndependent 𝕜 restE ↔ LinearIndependent 𝕜 dSub := by
      simpa [hd] using (linearIndependent_equiv eJK (f := dSub))
    exact h1.trans h2.symm
  let c : I → 𝕜 := Sum.elim (fun i => if i = 0 then 0 else -1) (fun _ => 0)
  let u : I → 𝕜 × E := hS + fun x => c x • hS (Sum.inl (0 : Fin (n + 1)))
  have hu_iff : LinearIndependent 𝕜 hS ↔ LinearIndependent 𝕜 u := by
    have h0 : c (Sum.inl (0 : Fin (n + 1))) = 0 := by simp [c]
    simpa [u, c] using
      (linearIndependent_add_smul_iff (v := hS) (c := c) (i := Sum.inl (0 : Fin (n + 1))) h0).symm
  let U : Type := Unit ⊕ K
  let eIK : U ≃ I :=
    { toFun := Sum.elim (fun _ => Sum.inl (0 : Fin (n + 1))) emb
      invFun := fun x => by
        cases x with
        | inl i =>
            by_cases hi : i = 0
            · exact Sum.inl ()
            · exact Sum.inr (Sum.inl (i.pred hi))
        | inr j => exact Sum.inr (Sum.inr j)
      left_inv := by
        intro x
        cases x with
        | inl u => rfl
        | inr k =>
            cases k with
            | inl i => simp [emb]
            | inr j => rfl
      right_inv := by
        intro x
        cases x with
        | inl i =>
            by_cases hi : i = 0
            · simp [hi, emb]
            · simp [hi, emb, Fin.succ_pred i hi]
        | inr j => rfl }
  let uUnit : U → 𝕜 × E := fun x => u (eIK x)
  let uRest : K → 𝕜 × E :=
    Sum.elim (fun i => (0, points i.succ - points 0)) (fun j => (0, directions j))
  have huUnit_shape : uUnit = Sum.elim (fun _ : Unit => (1, points 0)) uRest := by
    funext x
    cases x with
    | inl uu =>
        simp [uUnit, u, c, hS, eIK, uRest]
    | inr k =>
        cases k with
        | inl i =>
            simp [uUnit, u, c, hS, eIK, emb, uRest, sub_eq_add_neg]
        | inr j =>
            simp [uUnit, u, c, hS, eIK, emb, uRest]
  have hu_equiv : LinearIndependent 𝕜 u ↔ LinearIndependent 𝕜 uUnit := by
    simpa [uUnit] using (linearIndependent_equiv eIK (f := u)).symm
  have huUnit_iff_uRest : LinearIndependent 𝕜 uUnit ↔ LinearIndependent 𝕜 uRest := by
    rw [huUnit_shape]
    have hhead : LinearIndependent 𝕜 (fun _ : Unit => ((1 : 𝕜), points 0)) := by
      rw [linearIndependent_unique_iff]
      simp
    have hnotmem :
        ((1 : 𝕜), points 0) ∉ Submodule.span 𝕜 (Set.range uRest) := by
      intro hx
      have hspan :
          Submodule.span 𝕜 (Set.range uRest) ≤ LinearMap.ker (LinearMap.fst 𝕜 𝕜 E) := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨k, rfl⟩
        cases k <;> simp [uRest, LinearMap.mem_ker]
      have hx' : ((1 : 𝕜), points 0) ∈ LinearMap.ker (LinearMap.fst 𝕜 𝕜 E) := hspan hx
      have hfst : (LinearMap.fst 𝕜 𝕜 E) ((1 : 𝕜), points 0) = 0 := hx'
      have h1 : (1 : 𝕜) = 0 := hfst
      exact one_ne_zero h1
    have hdisj :
        Disjoint (Submodule.span 𝕜 (Set.range (fun _ : Unit => ((1 : 𝕜), points 0))))
          (Submodule.span 𝕜 (Set.range uRest)) := by
      simpa [Set.range_const] using
        (Submodule.disjoint_span_singleton_of_notMem (s := Submodule.span 𝕜 (Set.range uRest))
          hnotmem).symm
    constructor
    · intro h
      exact (linearIndependent_sum.mp h).2.1
    · intro h
      exact linearIndependent_sum.mpr ⟨hhead, h, hdisj⟩
  have huRest_iff_restE : LinearIndependent 𝕜 uRest ↔ LinearIndependent 𝕜 restE := by
    let inrL : E →ₗ[𝕜] (𝕜 × E) :=
      { toFun := fun x => (0, x)
        map_add' := by intro x y; simp
        map_smul' := by intro a x; simp }
    have hinr_ker : LinearMap.ker inrL = ⊥ := by
      apply LinearMap.ker_eq_bot.2
      intro x y hxy
      simpa [inrL] using congrArg Prod.snd hxy
    have huRest_def : uRest = inrL ∘ restE := by
      funext k
      cases k <;> simp [uRest, restE, inrL]
    simpa [huRest_def] using (inrL.linearIndependent_iff (v := restE) hinr_ker)
  have hlin_core : LinearIndependent 𝕜 hS ↔ LinearIndependent 𝕜 restE := by
    exact hu_iff.trans (hu_equiv.trans (huUnit_iff_uRest.trans huRest_iff_restE))
  have hcore : LinearIndependent 𝕜 hS ↔ AffineIndependent 𝕜 qS :=
    hlin_core.trans hqS_core.symm
  exact hli.trans (hcore.trans hai.symm)

private theorem mixedAffineHull_range_eq_affineSpan_append
    (points : Fin (n + 1) → E) (directions : Fin m → E) :
    mixedAffineHull 𝕜 (range points) (range directions) =
      affineSpan 𝕜 (Set.range (Fin.append points (fun j => points 0 + directions j))) := by
  let p0 : E := points 0
  let q : Fin (n + 1 + m) → E := Fin.append points (fun j => p0 + directions j)
  have hle1 : mixedAffineHull 𝕜 (range points) (range directions) ≤ affineSpan 𝕜 (Set.range q) := by
    refine mixedAffineHull_le 𝕜
      (points := Set.range points) (directions := Set.range directions) ?_ ?_
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact mem_affineSpan 𝕜 <| Set.mem_range.mpr ⟨Fin.castAdd m i, by
        simp [q]⟩
    · intro y hy
      rcases hy with ⟨j, rfl⟩
      have hp0 : p0 ∈ affineSpan 𝕜 (Set.range q) :=
        mem_affineSpan 𝕜 <| Set.mem_range.mpr ⟨Fin.castAdd m 0, by
          simp [q, p0]⟩
      have hpj : p0 + directions j ∈ affineSpan 𝕜 (Set.range q) :=
        mem_affineSpan 𝕜 <| Set.mem_range.mpr ⟨Fin.natAdd (n + 1) j, by
          simp [q]⟩
      have hdir : (p0 + directions j) -ᵥ p0 ∈ (affineSpan 𝕜 (Set.range q)).direction :=
        (affineSpan 𝕜 (Set.range q)).vsub_mem_direction hpj hp0
      simpa [vsub_eq_sub] using hdir
  have hle2 :
      affineSpan 𝕜 (Set.range q) ≤ mixedAffineHull 𝕜 (range points) (range directions) := by
    refine affineSpan_le.2 ?_
    intro x hx
    rcases hx with ⟨k, rfl⟩
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa [q] using
        (subset_mixedAffineHull 𝕜
          (points := Set.range points) (directions := Set.range directions) ⟨i, rfl⟩)
    · intro j
      have hp0 :
          p0 ∈ mixedAffineHull 𝕜 (range points) (range directions) := by
        exact
          subset_mixedAffineHull 𝕜
            (points := Set.range points) (directions := Set.range directions) ⟨0, by simp [p0]⟩
      have hdir :
          directions j ∈ (mixedAffineHull 𝕜 (range points) (range directions)).direction := by
        exact
          directions_subset_direction_mixedAffineHull 𝕜
            (points := Set.range points) (directions := Set.range directions)
            ⟨p0, ⟨0, by simp [p0]⟩⟩ ⟨j, rfl⟩
      have hpj :
          p0 + directions j ∈ mixedAffineHull 𝕜 (range points) (range directions) := by
        simpa [vadd_eq_add, add_comm] using
          (mixedAffineHull 𝕜 (range points) (range directions)).vadd_mem_of_mem_direction hdir hp0
      simpa [q] using hpj
  simpa [q, p0] using le_antisymm hle1 hle2

-- Proof sketch: for a nonempty point family, rewrite
-- `mixedAffineHull 𝕜 (Set.range points) (Set.range directions)` through one distinguished point
-- `points 0` as the affine span of the appended family. Then identify the affine-dimension
-- equation with linear independence of the homogenized family whose point entries are
-- `(1, points i)` and whose direction entries are `(0, directions j)`. If there are no points,
-- this mixed affine hull is `⊥`, so the affine-dimension equation reduces to `m = 0`.
/-- The source affine-dimension criterion for Definition 17.0.13 is equivalent to the canonical
homogenized `LinearIndependent` owner predicate `mixedAffineIndependent`. -/
private theorem mixedAffineIndependent_iff_affineDim_eq_fin
    (points : Fin n → E) (directions : Fin m → E) :
    maffind[𝕜](points | directions) ↔
      (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (n + m : ℤ) - 1 := by
  classical
  cases n with
  | zero =>
      have hbot0 : mixedAffineHull 𝕜 (∅ : Set E) (Set.range directions) = ⊥ := by
        rw [mixedAffineHull_eq_bot_iff_points_eq_empty
          (k := 𝕜) (P := E) (points := (∅ : Set E)) (directions := Set.range directions)]
      constructor
      · intro hmix
        rcases hmix with ⟨hguard, _⟩
        have hm0 : m = 0 := by
          rcases hguard with h0 | hm0
          · rcases h0 with ⟨i⟩
            exact False.elim (Fin.elim0 i)
          · by_cases hm : m = 0
            · exact hm
            · exfalso
              have hm_nonempty : ¬ Nonempty (Fin m) := by
                intro hm'
                exact hm0.false (Classical.choice hm')
              exact hm_nonempty ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
        have hdim_left :
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (-1 : ℤ) := by
          unfold AffineSubspace.affineDim
          simp [hbot0]
        calc
          (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (-1 : ℤ) := hdim_left
          _ = (0 + m : ℤ) - 1 := by omega
      · intro hdim
        have hm0 : m = 0 := by
          have hdim_left :
              (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (-1 : ℤ) := by
            unfold AffineSubspace.affineDim
            simp [hbot0]
          have hdim' : (-1 : ℤ) = (0 + m : ℤ) - 1 := by
            calc
              (-1 : ℤ) = (mixedAffineHull 𝕜 (range points) (range directions)).affineDim :=
                hdim_left.symm
              _ = (0 + m : ℤ) - 1 := hdim
          have hmz : (m : ℤ) = 0 := by omega
          exact Int.ofNat_eq_zero.mp hmz
        subst hm0
        refine ⟨Or.inr (by infer_instance), ?_⟩
        exact
          (linearIndependent_empty_type
            (R := 𝕜)
            (v := (Sum.elim (fun i : Fin 0 ↦ ((1 : 𝕜), points i))
              (fun j : Fin 0 ↦ ((0 : 𝕜), directions j)))))
  | succ n =>
      let q : Fin (n + 1 + m) → E := Fin.append points (fun j => points 0 + directions j)
      have hmix_hai :
          maffind[𝕜](points | directions) ↔ AffineIndependent 𝕜 q := by
        exact (mixedAffineIndependent_iff_linearIndependent_homogenized_append
            (𝕜 := 𝕜) (points := points) (directions := directions)).trans
          (linearIndependent_homogenized_iff_affineIndependent_append
            (𝕜 := 𝕜) (points := points) (directions := directions))
      have hai_dim :
          AffineIndependent 𝕜 q ↔
            Set.affineDim 𝕜 (Set.range q) = m + n := by
        simpa [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (AffineIndependent.iff_range_affineDim_eq_of_card_eq
            (𝕜 := 𝕜) (m := n + m) (b := q) (hcard := by
              simp [Nat.add_assoc, Nat.add_comm]))
      have hspan :
          mixedAffineHull 𝕜 (range points) (range directions) = affineSpan 𝕜 (Set.range q) := by
        simpa [q] using
          (mixedAffineHull_range_eq_affineSpan_append
            (𝕜 := 𝕜) (points := points) (directions := directions))
      have hdim' :
          maffind[𝕜](points | directions) ↔
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = m + n := by
        simpa [hspan, Set.affineDim] using hmix_hai.trans hai_dim
      have hdim :
          maffind[𝕜](points | directions) ↔
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = n + m := by
        constructor
        · intro h
          have hm :
              (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = m + n := hdim'.mp h
          calc
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (m + n : ℤ) := hm
            _ = (n + m : ℤ) := by omega
        · intro h
          have hm :
              (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (m + n : ℤ) := by
            omega
          exact hdim'.mpr hm
      constructor
      · intro h
        have h' :
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = n + m := hdim.mp h
        have :
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim =
              (Nat.succ n + m : ℤ) - 1 := by
          omega
        simpa using this
      · intro h
        have h' :
            (mixedAffineHull 𝕜 (range points) (range directions)).affineDim = (n + m : ℤ) := by
          omega
        exact hdim.mpr h'

private theorem mixedAffineIndependent_equiv
    {ι ι' κ κ' : Type*} (eι : ι ≃ ι') (eκ : κ ≃ κ')
    (points : ι → E) (directions : κ → E) :
    maffind[𝕜](points | directions) ↔
      maffind[𝕜](points ∘ eι.symm | directions ∘ eκ.symm) := by
  let e : ι' ⊕ κ' ≃ ι ⊕ κ := (Equiv.sumCongr eι eκ).symm
  let f : ι ⊕ κ → 𝕜 × E :=
    Sum.elim (fun i ↦ ((1 : 𝕜), points i)) (fun j ↦ ((0 : 𝕜), directions j))
  let g : ι' ⊕ κ' → 𝕜 × E :=
    Sum.elim (fun i ↦ ((1 : 𝕜), points (eι.symm i)))
      (fun j ↦ ((0 : 𝕜), directions (eκ.symm j)))
  have hcomp : f ∘ e = g := by
    funext x
    cases x <;> simp [e, f, g]
  have hli : LinearIndependent 𝕜 f ↔ LinearIndependent 𝕜 (f ∘ e) := by
    simpa [e] using
      (linearIndependent_equiv (R := 𝕜) (M := 𝕜 × E)
        e (f := f)).symm
  have hli' : LinearIndependent 𝕜 f ↔ LinearIndependent 𝕜 g := by
    simpa [hcomp] using hli
  have hguard : (Nonempty ι ∨ IsEmpty κ) ↔ (Nonempty ι' ∨ IsEmpty κ') := by
    constructor
    · intro h
      rcases h with hi | hk
      · exact Or.inl ⟨eι hi.some⟩
      · refine Or.inr ?_
        exact ⟨fun k' => hk.false (eκ.symm k')⟩
    · intro h
      rcases h with hi | hk
      · exact Or.inl ⟨eι.symm hi.some⟩
      · refine Or.inr ?_
        exact ⟨fun k => hk.false (eκ k)⟩
  simpa [mixedAffineIndependent, f, g] using hguard.and hli'

-- Proof sketch: pass to finite canonical index types `Fin (Nat.card ι)` and
-- `Fin (Nat.card κ)` by equivalence, apply the finite-index bridge theorem above, then transport
-- both sides back through `Set.range` invariance.
/-- The source affine-dimension criterion for Definition 17.0.13 at the canonical finite-index
layer: affine independence of mixed families indexed by finite types is equivalent to the affine
dimension formula `card(points) + card(directions) - 1`. -/
theorem mixedAffineIndependent_iff_affineDim_eq
    {ι κ : Type*} [Finite ι] [Finite κ]
    (points : ι → E) (directions : κ → E) :
    maffind[𝕜](points | directions) ↔
      (mixedAffineHull 𝕜 (range points) (range directions)).affineDim =
        (Nat.card ι + Nat.card κ : ℤ) - 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let pointsFin : Fin (Fintype.card ι) → E := points ∘ eι.symm
  let directionsFin : Fin (Fintype.card κ) → E := directions ∘ eκ.symm
  have hind :
      maffind[𝕜](points | directions) ↔
        maffind[𝕜](pointsFin | directionsFin) := by
    simpa [pointsFin, directionsFin] using
      (mixedAffineIndependent_equiv (𝕜 := 𝕜) eι eκ points directions)
  have hrange_points : Set.range pointsFin = Set.range points := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨eι.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨eι i, by simp [pointsFin]⟩
  have hrange_directions : Set.range directionsFin = Set.range directions := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨eκ.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨eκ i, by simp [directionsFin]⟩
  have hspan :
      mixedAffineHull 𝕜 (Set.range pointsFin) (Set.range directionsFin) =
        mixedAffineHull 𝕜 (Set.range points) (Set.range directions) := by
    simp [hrange_points, hrange_directions]
  have hfin :
      maffind[𝕜](pointsFin | directionsFin) ↔
        (mixedAffineHull 𝕜 (Set.range pointsFin) (Set.range directionsFin)).affineDim =
          (Fintype.card ι + Fintype.card κ : ℤ) - 1 := by
    simpa [pointsFin, directionsFin] using
      (mixedAffineIndependent_iff_affineDim_eq_fin
        (𝕜 := 𝕜) (n := Fintype.card ι) (m := Fintype.card κ) pointsFin directionsFin)
  exact hind.trans <| by
    simpa [Nat.card_eq_fintype_card, hspan] using hfin

end AffineDim
