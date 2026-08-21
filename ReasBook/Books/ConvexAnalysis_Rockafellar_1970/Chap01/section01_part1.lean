/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Pengfei Hao, Zaiwen Wen
-/

import Mathlib

section Chap01
section Section01

/-- Text 1.1: A subset `M` of `Real^n` is affine if for all `x, y ∈ M` and all `r : Real`,
`(1 - r) • x + r • y` is in `M`. -/
def IsAffineSet (n : Nat) (M : Set (Fin n -> Real)) : Prop :=
  ∀ x y : Fin n -> Real, x ∈ M -> y ∈ M -> ∀ r : Real, (1 - r) • x + r • y ∈ M

/-- Affine combinations of two points in an affine set are in the set, written as a line map. -/
lemma lineMap_mem_of_isAffineSet {n : Nat} {M : Set (Fin n → Real)}
    (hM : IsAffineSet n M) {x y : Fin n → Real} (hx : x ∈ M) (hy : y ∈ M) (r : Real) :
    AffineMap.lineMap x y r ∈ M := by
  simpa [AffineMap.lineMap_apply_module] using hM x y hx hy r

/-- A three-point affine combination as a line map of two line maps. -/
lemma affine_combo_three_as_double_lineMap {n : Nat} (c : Real) (x y z : Fin n → Real) :
    c • (x - y) + z =
      AffineMap.lineMap (AffineMap.lineMap z x (2 * c))
        (AffineMap.lineMap z y (-2 * c)) (1 / 2 : Real) := by
  ext i
  simp [AffineMap.lineMap_apply_module, sub_eq_add_neg, smul_add, add_smul, smul_smul, add_assoc,
    add_left_comm, add_comm, mul_add, mul_comm, mul_left_comm]
  ring

/-- An affine set is closed under expressions of the form `c • (x - y) + z`. -/
lemma smul_sub_add_mem_of_isAffineSet {n : Nat} {M : Set (Fin n → Real)}
    (hM : IsAffineSet n M) {x y z : Fin n → Real} (hx : x ∈ M) (hy : y ∈ M) (hz : z ∈ M)
    (c : Real) : c • (x - y) + z ∈ M := by
  have hx' : AffineMap.lineMap z x (2 * c) ∈ M :=
    lineMap_mem_of_isAffineSet (n:=n) (M:=M) hM hz hx (2 * c)
  have hy' : AffineMap.lineMap z y (-2 * c) ∈ M :=
    lineMap_mem_of_isAffineSet (n:=n) (M:=M) hM hz hy (-2 * c)
  have h := lineMap_mem_of_isAffineSet (n:=n) (M:=M) hM hx' hy' (1 / 2 : Real)
  simpa [affine_combo_three_as_double_lineMap (n:=n) (c:=c) (x:=x) (y:=y) (z:=z)] using h

/-- Helper lemma: an affine set is the carrier of some affine subspace. -/
theorem isAffineSet_iff_affineSubspace (n : Nat) (M : Set (Fin n -> Real)) :
    IsAffineSet n M ↔ ∃ s : AffineSubspace Real (Fin n -> Real), (s : Set (Fin n -> Real)) = M := by
  constructor
  · intro hM
    refine ⟨{ carrier := M, smul_vsub_vadd_mem := ?_ }, rfl⟩
    intro c p₁ p₂ p₃ hp₁ hp₂ hp₃
    simpa [vsub_eq_sub, vadd_eq_add] using
      (smul_sub_add_mem_of_isAffineSet (n:=n) (M:=M) hM hp₁ hp₂ hp₃ c)
  · rintro ⟨s, rfl⟩
    intro x y hx hy r
    have h := AffineMap.lineMap_mem (Q:=s) r hx hy
    simpa [AffineMap.lineMap_apply_module] using h

/-- Submodules are affine sets. -/
lemma isAffineSet_of_submodule (n : Nat) (S : Submodule Real (Fin n → Real)) :
    IsAffineSet n (S : Set (Fin n → Real)) := by
  intro x y hx hy r
  have hx' : x ∈ S := hx
  have hy' : y ∈ S := hy
  exact S.add_mem (S.smul_mem (1 - r) hx') (S.smul_mem r hy')

/-- An affine set containing the origin is closed under scalar multiplication. -/
lemma affineSet_smul_closed_of_origin {n : Nat} {M : Set (Fin n → Real)}
    (hM : IsAffineSet n M) (h0 : (0 : Fin n → Real) ∈ M) :
    ∀ x ∈ M, ∀ r : Real, r • x ∈ M := by
  intro x hx r
  have h := hM 0 x h0 hx r
  simpa using h

/-- An affine set containing the origin is closed under addition. -/
lemma affineSet_add_closed_of_origin {n : Nat} {M : Set (Fin n → Real)}
    (hM : IsAffineSet n M) (h0 : (0 : Fin n → Real) ∈ M) :
    ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M := by
  intro x hx y hy
  have hmid : (1 - (1 / 2 : Real)) • x + (1 / 2 : Real) • y ∈ M :=
    hM x y hx hy (1 / 2 : Real)
  have hsmul : (2 : Real) • ((1 - (1 / 2 : Real)) • x + (1 / 2 : Real) • y) ∈ M :=
    affineSet_smul_closed_of_origin (n:=n) (M:=M) hM h0 _ hmid (2 : Real)
  have hmul_left : (2 : Real) * (1 - (2⁻¹ : Real)) = (1 : Real) := by
    norm_num
  have hmul : (2 : Real) * (2⁻¹ : Real) = (1 : Real) := by
    norm_num
  simpa [smul_add, smul_smul, hmul_left, hmul] using hsmul

/-- An affine set containing the origin is the carrier of a submodule. -/
lemma submodule_of_affineSet_origin (n : Nat) (M : Set (Fin n → Real))
    (hM : IsAffineSet n M) (h0 : (0 : Fin n → Real) ∈ M) :
    ∃ S : Submodule Real (Fin n → Real), (S : Set (Fin n → Real)) = M := by
  refine ⟨{ carrier := M
          , zero_mem' := h0
          , add_mem' := ?_
          , smul_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    exact affineSet_add_closed_of_origin (n:=n) (M:=M) hM h0 x hx y hy
  · intro r x hx
    exact affineSet_smul_closed_of_origin (n:=n) (M:=M) hM h0 x hx r

/-- Theorem 1.1: The subspaces of `Real^n` are exactly the affine sets which contain the origin. -/
theorem subspace_iff_affineSet_and_origin (n : Nat) (M : Set (Fin n -> Real)) :
    (∃ S : Submodule Real (Fin n -> Real), (S : Set (Fin n -> Real)) = M) ↔
      IsAffineSet n M ∧ (0 : Fin n -> Real) ∈ M := by
  constructor
  · rintro ⟨S, rfl⟩
    refine ⟨isAffineSet_of_submodule n S, ?_⟩
    exact S.zero_mem
  · rintro ⟨hM, h0⟩
    exact submodule_of_affineSet_origin n M hM h0

/-- Text 1.2: For `M ⊆ Real^n` and `a ∈ Real^n`, the translate of `M` by `a` is the set
`M + a = {x + a | x ∈ M}`. -/
def SetTranslate (n : Nat) (M : Set (Fin n -> Real)) (a : Fin n -> Real) :
    Set (Fin n -> Real) :=
  (fun x => x + a) '' M

/-- Translation commutes with affine combinations. -/
lemma translate_affine_combo {n : Nat} (x y a : Fin n → Real) (r : Real) :
    (1 - r) • (x + a) + r • (y + a) = ((1 - r) • x + r • y) + a := by
  ext i
  simp
  ring

/-- Text 1.2.1: If `M ⊆ Real^n` is affine and `a ∈ Real^n`, then the translate `a + M`
is an affine set. -/
theorem isAffineSet_translate (n : Nat) (M : Set (Fin n -> Real)) (a : Fin n -> Real) :
    IsAffineSet n M → IsAffineSet n (SetTranslate n M a) := by
  intro hM x y hx hy r
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  refine ⟨(1 - r) • x' + r • y', hM x' y' hx' hy' r, ?_⟩
  simpa [translate_affine_combo] using
    (translate_affine_combo (x:=x') (y:=y') (a:=a) (r:=r)).symm

/-- Text 1.3: An affine set `M` is parallel to an affine set `L` if `M = L + a` for some `a`. -/
def IsParallelAffineSet (n : Nat) (M L : Set (Fin n -> Real)) : Prop :=
  ∃ a : Fin n -> Real, M = SetTranslate n L a

/-- Translating by `-y` gives the set of differences with `y`. -/
lemma setTranslate_eq_sub_single (n : Nat) (M : Set (Fin n → Real)) (y : Fin n → Real) :
    SetTranslate n M (-y) = {x | ∃ a ∈ M, x = a - y} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp [sub_eq_add_neg]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp [sub_eq_add_neg]⟩

/-- Translating a submodule by one of its elements gives the same set. -/
lemma setTranslate_submodule_eq_self (n : Nat) (L : Submodule Real (Fin n → Real))
    (v : Fin n → Real) (hv : v ∈ L) :
    SetTranslate n (L : Set (Fin n → Real)) v = (L : Set (Fin n → Real)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact L.add_mem hy hv
  · intro hx
    refine ⟨x - v, ?_, by simp⟩
    have : x + (-v) ∈ L := L.add_mem hx (L.neg_mem hv)
    simpa [sub_eq_add_neg] using this

/-- Parallel submodules to the same affine set are equal. -/
lemma parallel_submodule_unique (n : Nat) (M : Set (Fin n → Real))
    (L1 L2 : Submodule Real (Fin n → Real))
    (h1 : IsParallelAffineSet n M (L1 : Set (Fin n → Real)))
    (h2 : IsParallelAffineSet n M (L2 : Set (Fin n → Real))) :
    L1 = L2 := by
  rcases h1 with ⟨a1, hM1⟩
  rcases h2 with ⟨a2, hM2⟩
  have htrans : (L2 : Set (Fin n → Real)) =
      SetTranslate n (L1 : Set (Fin n → Real)) (a1 - a2) := by
    ext x
    constructor
    · intro hx
      have hxM : x + a2 ∈ M := by
        have : x + a2 ∈ SetTranslate n (L2 : Set (Fin n → Real)) a2 := ⟨x, hx, rfl⟩
        simpa [hM2] using this
      rcases (by simpa [hM1] using hxM) with ⟨y, hy, hxy⟩
      have hxy' : y + (a1 - a2) = x := by
        have h := congrArg (fun z => z - a2) hxy
        simpa [add_sub_assoc] using h
      exact ⟨y, hy, hxy'⟩
    · rintro ⟨y, hy, rfl⟩
      have hxM : y + a1 ∈ M := by
        have : y + a1 ∈ SetTranslate n (L1 : Set (Fin n → Real)) a1 := ⟨y, hy, rfl⟩
        simpa [hM1] using this
      have hxM' : (y + (a1 - a2)) + a2 ∈ M := by
        have h' : y + (a1 - a2) + a2 = y + a1 := by
          simp [add_assoc]
        simpa [h'] using hxM
      rcases (by simpa [hM2] using hxM') with ⟨z, hz, hzx⟩
      have hz' : z = y + a1 + -a2 := by
        have h := congrArg (fun t => t - a2) hzx
        simp [add_assoc] at h
        exact h
      simpa [sub_eq_add_neg, add_assoc, hz'] using hz
  have hmem : a1 - a2 ∈ L1 := by
    have hzero : (0 : Fin n → Real) ∈ (L2 : Set (Fin n → Real)) := L2.zero_mem
    have hzero' : (0 : Fin n → Real) ∈
        SetTranslate n (L1 : Set (Fin n → Real)) (a1 - a2) := by
      simpa [htrans] using hzero
    rcases hzero' with ⟨y, hy, hzero_eq⟩
    have hneg : a1 - a2 = -y := by
      have h := congrArg (fun z => z - y) hzero_eq
      simpa using h
    simpa [hneg] using (L1.neg_mem hy)
  have hset : (L2 : Set (Fin n → Real)) = (L1 : Set (Fin n → Real)) := by
    calc
      (L2 : Set (Fin n → Real)) =
          SetTranslate n (L1 : Set (Fin n → Real)) (a1 - a2) := htrans
      _ = (L1 : Set (Fin n → Real)) := by
          simpa using (setTranslate_submodule_eq_self n L1 (a1 - a2) hmem)
  ext x
  change x ∈ (L1 : Set (Fin n → Real)) ↔ x ∈ (L2 : Set (Fin n → Real))
  simp [hset]

/-- Theorem 1.2: Each non-empty affine set `M` is parallel to a unique subspace `L`;
this `L` is given by `L = M - M = {x - y | x ∈ M, y ∈ M}`. -/
theorem parallel_submodule_unique_of_affine (n : Nat) (M : Set (Fin n -> Real)) :
    IsAffineSet n M → Set.Nonempty M →
      ∃! L : Submodule Real (Fin n -> Real),
        IsParallelAffineSet n M (L : Set (Fin n -> Real)) ∧
          (L : Set (Fin n -> Real)) =
            {x | ∃ a ∈ M, ∃ b ∈ M, x = a - b} := by
  intro hM hne
  rcases hne with ⟨y, hy⟩
  have hMy_aff : IsAffineSet n (SetTranslate n M (-y)) :=
    isAffineSet_translate n M (-y) hM
  have hMy0 : (0 : Fin n → Real) ∈ SetTranslate n M (-y) := by
    exact ⟨y, hy, by simp⟩
  rcases (subspace_iff_affineSet_and_origin n (SetTranslate n M (-y))).2
      ⟨hMy_aff, hMy0⟩ with ⟨L, hL⟩
  have hparallel : IsParallelAffineSet n M (L : Set (Fin n → Real)) := by
    refine ⟨y, ?_⟩
    ext x
    constructor
    · intro hx
      have hx' : x - y ∈ L := by
        have : x - y ∈ SetTranslate n M (-y) := by
          refine ⟨x, hx, ?_⟩
          simp [sub_eq_add_neg]
        simpa [hL.symm] using this
      exact ⟨x - y, hx', by simp⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ SetTranslate n M (-y) := by
        simpa [hL] using hz
      rcases hz' with ⟨a, ha, hza⟩
      have hzay : z + y = a := by
        have h := congrArg (fun t => t + y) hza
        have h' : a = z + y := by
          simpa [add_assoc] using h
        exact h'.symm
      simpa [hzay] using ha
  have hL_eq : (L : Set (Fin n → Real)) =
      {x | ∃ a ∈ M, ∃ b ∈ M, x = a - b} := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ SetTranslate n M (-y) := by
        simpa [hL] using hx
      rcases hx' with ⟨a, ha, hxa⟩
      refine ⟨a, ha, y, hy, ?_⟩
      simpa [sub_eq_add_neg] using hxa.symm
    · rintro ⟨a, ha, b, hb, rfl⟩
      have haL : a - y ∈ L := by
        have : a - y ∈ SetTranslate n M (-y) := by
          refine ⟨a, ha, ?_⟩
          simp [sub_eq_add_neg]
        simpa [hL.symm] using this
      have hbL : b - y ∈ L := by
        have : b - y ∈ SetTranslate n M (-y) := by
          refine ⟨b, hb, ?_⟩
          simp [sub_eq_add_neg]
        simpa [hL.symm] using this
      have hsub : (a - y) - (b - y) ∈ L := by
        have hbL' : -(b - y) ∈ L := L.neg_mem hbL
        exact L.add_mem haL hbL'
      have hcalc : (a - y) - (b - y) = a - b := by
        abel
      simpa [hcalc] using hsub
  refine ⟨L, ⟨hparallel, hL_eq⟩, ?_⟩
  intro L' hL'
  exact (parallel_submodule_unique n M L L' hparallel hL'.1).symm

/-- Text 1.4: The dimension of a non-empty affine set is defined as the dimension of the
subspace parallel to it. (The dimension of `∅` is `-1` by convention.) -/
noncomputable def affineSetDim (n : Nat) (M : Set (Fin n -> Real)) (hM : IsAffineSet n M) :
    Int :=
by
  classical
  by_cases hne : Set.Nonempty M
  · let L : Submodule Real (Fin n -> Real) :=
      Classical.choose (parallel_submodule_unique_of_affine n M hM hne).exists
    exact Int.ofNat (Module.finrank Real L)
  · exact -1

/-- Text 1.5: An affine set of dimension `0` is called a point. -/
def IsPoint (n : Nat) (M : Set (Fin n -> Real)) : Prop :=
  ∃ hM : IsAffineSet n M, affineSetDim n M hM = 0

/-- Text 1.5: An affine set of dimension `1` is called a line. -/
def IsLine (n : Nat) (M : Set (Fin n -> Real)) : Prop :=
  ∃ hM : IsAffineSet n M, affineSetDim n M hM = 1

/-- Text 1.5: An affine set of dimension `2` is called a plane. -/
def IsPlane (n : Nat) (M : Set (Fin n -> Real)) : Prop :=
  ∃ hM : IsAffineSet n M, affineSetDim n M hM = 2

/-- Text 1.5: An `(n - 1)`-dimensional affine set in `Real^n` is called a hyperplane. -/
def IsHyperplane (n : Nat) (M : Set (Fin n -> Real)) : Prop :=
  ∃ hM : IsAffineSet n M, affineSetDim n M hM = Int.ofNat (n - 1)

/-- Text 1.6: Given a subspace `L` of `Real^n`, the orthogonal complement `L^⊥` is the set
of vectors `x` such that `x ⟂ y` for every `y ∈ L`. -/
def orthogonalComplement (n : Nat) (L : Submodule Real (Fin n -> Real)) :
    Submodule Real (Fin n -> Real) where
  carrier := {x | ∀ y ∈ L, x ⬝ᵥ y = 0}
  zero_mem' := by
    intro y hy
    simp
  add_mem' := by
    intro x y hx hy z hz
    simp [hx z hz, hy z hz]
  smul_mem' := by
    intro c x hx z hz
    simp [hx z hz]

/-- The linear functional `x ↦ x ⬝ᵥ b`. -/
def dotProductLinear (n : Nat) (b : Fin n → Real) : Module.Dual Real (Fin n → Real) :=
  { toFun := fun x => x ⬝ᵥ b
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro c x
      simp }

/-- The kernel of `dotProductLinear` is the zero dot-product set. -/
lemma dotProductLinear_ker_eq (n : Nat) (b : Fin n → Real) :
    ((LinearMap.ker (dotProductLinear n b)) : Set (Fin n → Real)) = {x | x ⬝ᵥ b = 0} := by
  ext x
  simp [dotProductLinear]

/-- A nonzero vector gives a nonzero dot-product functional. -/
lemma dotProductLinear_ne_zero (n : Nat) {b : Fin n → Real} (hb : b ≠ 0) :
    dotProductLinear n b ≠ 0 := by
  intro hzero
  have hbb : b ⬝ᵥ b = 0 := by
    have h := congrArg (fun f => f b) hzero
    simpa [dotProductLinear] using h
  have hb' : b = 0 := (dotProduct_self_eq_zero (v:=b)).1 hbb
  exact hb hb'

/-- Any nonzero linear functional on `Fin n → ℝ` is a dot-product functional. -/
lemma dual_eq_dotProductLinear (n : Nat) (f : Module.Dual Real (Fin n → Real)) (hf : f ≠ 0) :
    ∃ b : Fin n → Real, b ≠ 0 ∧ f = dotProductLinear n b := by
  classical
  let b : Fin n → Real := (Module.piEquiv (Fin n) Real Real).symm f
  have hf_eq : f = (Module.piEquiv (Fin n) Real Real) b := by
    simp [b]
  have hpi : (Module.piEquiv (Fin n) Real Real) b = dotProductLinear n b := by
    ext x
    simp [Module.piEquiv_apply_apply, dotProductLinear, dotProduct, smul_eq_mul]
  have hf_dot : f = dotProductLinear n b := by
    calc
      f = (Module.piEquiv (Fin n) Real Real) b := hf_eq
      _ = dotProductLinear n b := hpi
  have hb : b ≠ 0 := by
    intro hb0
    apply hf
    have : dotProductLinear n b = 0 := by
      ext x
      simp [hb0, dotProductLinear]
    simpa [hf_dot] using this
  exact ⟨b, hb, hf_dot⟩

/-- A dot-product level set is affine. -/
lemma dotProduct_levelset_isAffine (n : Nat) (β : Real) (b : Fin n → Real) :
    IsAffineSet n {x : Fin n → Real | x ⬝ᵥ b = β} := by
  intro x y hx hy r
  have hx' : x ⬝ᵥ b = β := hx
  have hy' : y ⬝ᵥ b = β := hy
  have hcalc :
      ((1 - r) • x + r • y) ⬝ᵥ b = (1 - r) • β + r • β := by
    calc
      ((1 - r) • x + r • y) ⬝ᵥ b
          = ((1 - r) • x) ⬝ᵥ b + (r • y) ⬝ᵥ b := by
              simp
      _ = (1 - r) • (x ⬝ᵥ b) + r • (y ⬝ᵥ b) := by
            simp [smul_dotProduct]
      _ = (1 - r) • β + r • β := by simp [hx', hy']
  have hβ : (1 - r) • β + r • β = β := by
    -- scalar algebra in `Real`
    have hβ' : (1 - r) * β + r * β = β := by ring
    simpa [smul_eq_mul] using hβ'
  calc
    ((1 - r) • x + r • y) ⬝ᵥ b = (1 - r) • β + r • β := hcalc
    _ = β := hβ

/-- A nonzero normal gives a point on the level set and a translation by the kernel. -/
lemma exists_point_and_translate_kernel (n : Nat) (β : Real) (b : Fin n → Real) (hb : b ≠ 0) :
    ∃ x0 : Fin n → Real,
      x0 ⬝ᵥ b = β ∧
        {x : Fin n → Real | x ⬝ᵥ b = β} =
          SetTranslate n {x : Fin n → Real | x ⬝ᵥ b = 0} x0 := by
  classical
  have hb' : ∃ i : Fin n, b i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hb
    funext i
    exact h i
  rcases hb' with ⟨i, hbi⟩
  let x0 : Fin n → Real := Pi.single i (β / b i)
  have hx0 : x0 ⬝ᵥ b = β := by
    have hx0' : x0 ⬝ᵥ b = (β / b i) * b i := by
      simp [x0]
    have hmul : (β / b i) * b i = β := by
      field_simp [hbi]
    simp [hx0', hmul]
  refine ⟨x0, hx0, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : x ⬝ᵥ b = β := by
      simpa using hx
    have hx' : (x - x0) ⬝ᵥ b = 0 := by
      calc
        (x - x0) ⬝ᵥ b = x ⬝ᵥ b - x0 ⬝ᵥ b := by
          simp
        _ = β - β := by simp [hx', hx0]
        _ = 0 := by ring
    refine ⟨x - x0, ?_, by simp⟩
    simpa using hx'
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ⬝ᵥ b = 0 := by simpa using hy
    calc
      (y + x0) ⬝ᵥ b = y ⬝ᵥ b + x0 ⬝ᵥ b := by
        simp
      _ = 0 + β := by simp [hy', hx0]
      _ = β := by simp

/-- The kernel of a nonzero dot-product functional has dimension `n - 1`. -/
lemma finrank_kernel_dotProduct (n : Nat) (b : Fin n → Real) (hb : b ≠ 0) :
    Module.finrank Real (LinearMap.ker (dotProductLinear n b)) = n - 1 := by
  have hf : dotProductLinear n b ≠ 0 := dotProductLinear_ne_zero (n:=n) hb
  have h :=
    (Module.Dual.finrank_ker_add_one_of_ne_zero (f:=dotProductLinear n b) hf)
  have h' : Module.finrank Real (LinearMap.ker (dotProductLinear n b)) + 1 = n := by
    simpa [Module.finrank_fin_fun (R:=Real) (n:=n)] using h
  have hnpos : 0 < n := by
    by_contra hn
    have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hzero
    have : b = 0 := by
      funext i
      exact (Fin.elim0 i)
    exact hb this
  have h1 : 1 ≤ n := by
    simpa using hnpos
  have h'' :
      Module.finrank Real (LinearMap.ker (dotProductLinear n b)) + 1 = (n - 1) + 1 := by
    calc
      Module.finrank Real (LinearMap.ker (dotProductLinear n b)) + 1 = n := h'
      _ = (n - 1) + 1 := by
        exact (Nat.sub_add_cancel h1).symm
  exact Nat.add_right_cancel h''

/-- Codimension-one submodules are dot-product kernels. -/
lemma codim_one_submodule_eq_dotProduct (n : Nat) (L : Submodule Real (Fin n → Real))
    (hL : Module.finrank Real L = n - 1) (hn : 0 < n) :
    ∃ b : Fin n → Real, b ≠ (0 : Fin n → Real) ∧
      (L : Set (Fin n → Real)) = {x : Fin n → Real | x ⬝ᵥ b = 0} := by
  have hlt : n - 1 < n := by
    cases n with
    | zero =>
        cases (Nat.lt_irrefl 0 hn)
    | succ n =>
        simp
  have htop_fin :
      Module.finrank Real (⊤ : Submodule Real (Fin n → Real)) = n := by
    simp [Module.finrank_fin_fun (R:=Real) (n:=n)]
  have hneq : L ≠ ⊤ := by
    intro htop
    have hL' :
        Module.finrank Real (⊤ : Submodule Real (Fin n → Real)) = n - 1 := by
      rw [← htop]
      exact hL
    have h' : n = n - 1 := by
      calc
        n = Module.finrank Real (⊤ : Submodule Real (Fin n → Real)) := by
          symm
          exact htop_fin
        _ = n - 1 := hL'
    exact (ne_of_lt hlt) h'.symm
  have hltop : L < ⊤ := lt_of_le_of_ne le_top hneq
  rcases Submodule.exists_le_ker_of_lt_top L hltop with ⟨f, hf, hle⟩
  rcases dual_eq_dotProductLinear n f hf with ⟨b, hb, hf_eq⟩
  have hker_fin : Module.finrank Real (LinearMap.ker f) = n - 1 := by
    have h :=
      (Module.Dual.finrank_ker_add_one_of_ne_zero (f:=f) hf)
    have h' : Module.finrank Real (LinearMap.ker f) + 1 = n := by
      simpa [Module.finrank_fin_fun (R:=Real) (n:=n)] using h
    have h1 : 1 ≤ n := hn
    have h'' :
        Module.finrank Real (LinearMap.ker f) + 1 = (n - 1) + 1 := by
      calc
        Module.finrank Real (LinearMap.ker f) + 1 = n := h'
        _ = (n - 1) + 1 := by exact (Nat.sub_add_cancel h1).symm
    exact Nat.add_right_cancel h''
  have hker_eq : L = LinearMap.ker f := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    calc
      Module.finrank Real L = n - 1 := hL
      _ = Module.finrank Real (LinearMap.ker f) := by symm; exact hker_fin
  have hker_set :
      (LinearMap.ker f : Set (Fin n → Real)) = {x : Fin n → Real | x ⬝ᵥ b = 0} := by
    simpa [hf_eq] using (dotProductLinear_ker_eq n b)
  have hL_set :
      (L : Set (Fin n → Real)) = {x : Fin n → Real | x ⬝ᵥ b = 0} := by
    simpa [hker_eq] using hker_set
  exact ⟨b, hb, hL_set⟩

/-- Equality of dot-product level sets gives equality of the zero-level kernels. -/
lemma hyperplane_kernels_eq (n : Nat) (b b' : Fin n → Real) (β β' : Real) (x0 : Fin n → Real)
    (hx0 : x0 ⬝ᵥ b = β)
    (hH : {x : Fin n → Real | x ⬝ᵥ b = β} = {x : Fin n → Real | x ⬝ᵥ b' = β'}) :
    {x : Fin n → Real | x ⬝ᵥ b = 0} = {x : Fin n → Real | x ⬝ᵥ b' = 0} := by
  have hx0' : x0 ⬝ᵥ b' = β' := by
    have hx0mem : x0 ∈ {x : Fin n → Real | x ⬝ᵥ b = β} := by
      simp [hx0]
    have hx0mem' : x0 ∈ {x : Fin n → Real | x ⬝ᵥ b' = β'} := by
      simpa [hH] using hx0mem
    simpa using hx0mem'
  ext x
  constructor
  · intro hx
    have hx' : x ⬝ᵥ b = 0 := by
      simpa using hx
    have hsum_mem : x + x0 ∈ {x : Fin n → Real | x ⬝ᵥ b = β} := by
      have : (x + x0) ⬝ᵥ b = β := by
        calc
          (x + x0) ⬝ᵥ b = x ⬝ᵥ b + x0 ⬝ᵥ b := by
            simp
          _ = 0 + β := by simp [hx', hx0]
          _ = β := by simp
      simp [this]
    have hsum_mem' : x + x0 ∈ {x : Fin n → Real | x ⬝ᵥ b' = β'} := by
      simpa [hH] using hsum_mem
    have hsum' : (x + x0) ⬝ᵥ b' = β' := by
      simpa using hsum_mem'
    have hcalc : (x + x0) ⬝ᵥ b' = x ⬝ᵥ b' + x0 ⬝ᵥ b' := by
      simp
    have : x ⬝ᵥ b' = 0 := by
      linarith [hsum', hcalc, hx0']
    simpa using this
  · intro hx
    have hx' : x ⬝ᵥ b' = 0 := by
      simpa using hx
    have hsum_mem : x + x0 ∈ {x : Fin n → Real | x ⬝ᵥ b' = β'} := by
      have : (x + x0) ⬝ᵥ b' = β' := by
        calc
          (x + x0) ⬝ᵥ b' = x ⬝ᵥ b' + x0 ⬝ᵥ b' := by
            simp
          _ = 0 + β' := by simp [hx', hx0']
          _ = β' := by simp
      simp [this]
    have hsum_mem' : x + x0 ∈ {x : Fin n → Real | x ⬝ᵥ b = β} := by
      simpa [hH.symm] using hsum_mem
    have hsum' : (x + x0) ⬝ᵥ b = β := by
      simpa using hsum_mem'
    have hcalc : (x + x0) ⬝ᵥ b = x ⬝ᵥ b + x0 ⬝ᵥ b := by
      simp
    have : x ⬝ᵥ b = 0 := by
      linarith [hsum', hcalc, hx0]
    simpa using this

/-- Nonzero linear functionals with the same kernel are scalar multiples. -/
lemma linear_functional_eq_smul_of_ker_eq (n : Nat)
    (f g : Module.Dual Real (Fin n → Real)) (hf : f ≠ 0) (hg : g ≠ 0)
    (hker : LinearMap.ker f = LinearMap.ker g) :
    ∃ c : Real, c ≠ 0 ∧ g = c • f := by
  classical
  have hx0 : ∃ x0 : Fin n → Real, f x0 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    apply LinearMap.ext
    intro x
    exact h x
  rcases hx0 with ⟨x0, hx0⟩
  let c : Real := g x0 / f x0
  have hcf : g = c • f := by
    apply LinearMap.ext
    intro x
    have hxker : x - (f x / f x0) • x0 ∈ LinearMap.ker f := by
      change f (x - (f x / f x0) • x0) = 0
      have hmul : (f x / f x0) * f x0 = f x := by
        field_simp [hx0]
      simp [smul_eq_mul, hmul]
    have hxker' : x - (f x / f x0) • x0 ∈ LinearMap.ker g := by
      simpa [hker] using hxker
    have hxg : g (x - (f x / f x0) • x0) = 0 := by
      simpa using hxker'
    have hxg' : g x - (f x / f x0) * g x0 = 0 := by
      simpa [smul_eq_mul] using hxg
    have hxg'' : g x = (f x / f x0) * g x0 := by
      linarith
    have hmul' : (f x / f x0) * g x0 = (g x0 / f x0) * f x := by
      field_simp [hx0]
    have hxg''' : g x = c * f x := by
      calc
        g x = (f x / f x0) * g x0 := hxg''
        _ = (g x0 / f x0) * f x := hmul'
        _ = c * f x := by simp [c]
    simp [LinearMap.smul_apply, smul_eq_mul, hxg''']
  have hc : c ≠ 0 := by
    intro hc
    apply hg
    have hzero : g = 0 := by
      calc
        g = c • f := hcf
        _ = 0 := by simp [hc]
    exact hzero
  exact ⟨c, hc, hcf⟩

/-- If two nonzero normals define the same hyperplane, they are scalar multiples. -/
lemma hyperplane_normal_unique (n : Nat) (b b' : Fin n → Real) (β β' : Real)
    (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hH : {x : Fin n → Real | x ⬝ᵥ b = β} = {x : Fin n → Real | x ⬝ᵥ b' = β'}) :
    ∃ c : Real, c ≠ 0 ∧ b' = c • b ∧ β' = c * β := by
  classical
  rcases exists_point_and_translate_kernel n β b hb with ⟨x0, hx0, -⟩
  have hx0' : x0 ⬝ᵥ b' = β' := by
    have hx0mem : x0 ∈ {x : Fin n → Real | x ⬝ᵥ b = β} := by
      simp [hx0]
    have hx0mem' : x0 ∈ {x : Fin n → Real | x ⬝ᵥ b' = β'} := by
      simpa [hH] using hx0mem
    simpa using hx0mem'
  have hker_set :
      {x : Fin n → Real | x ⬝ᵥ b = 0} = {x : Fin n → Real | x ⬝ᵥ b' = 0} :=
    hyperplane_kernels_eq n b b' β β' x0 hx0 hH
  have hker :
      LinearMap.ker (dotProductLinear n b) =
        LinearMap.ker (dotProductLinear n b') := by
    ext x
    have hx :
        x ∈ {x : Fin n → Real | x ⬝ᵥ b = 0} ↔
          x ∈ {x : Fin n → Real | x ⬝ᵥ b' = 0} := by
      have := congrArg (fun s => x ∈ s) hker_set
      simpa using this
    simpa [dotProductLinear_ker_eq] using hx
  have hf : dotProductLinear n b ≠ 0 := dotProductLinear_ne_zero (n:=n) hb
  have hg : dotProductLinear n b' ≠ 0 := dotProductLinear_ne_zero (n:=n) hb'
  rcases
      linear_functional_eq_smul_of_ker_eq n (dotProductLinear n b)
        (dotProductLinear n b') hf hg hker with ⟨c, hc, hsmul⟩
  have hb' : b' = c • b := by
    funext i
    have h := congrArg (fun f => f (Pi.single i 1)) hsmul
    simpa [dotProductLinear, smul_eq_mul, single_dotProduct] using h
  have hβ' : β' = c * β := by
    have h := congrArg (fun f => f x0) hsmul
    simpa [dotProductLinear, smul_eq_mul, hx0, hx0'] using h
  exact ⟨c, hc, hb', hβ'⟩

/-- Theorem 1.3: Given `β : Real` and non-zero `b : Real^n`, the set
`{x | ⟪x, b⟫ = β}` is a hyperplane in `Real^n`. Moreover, every hyperplane admits such
a representation, with `b` and `β` unique up to a common non-zero multiple. -/
theorem hyperplane_iff_eq_dotProduct (n : Nat) (hn : 0 < n) :
    (∀ (β : Real) (b : Fin n → Real), b ≠ 0 →
      IsHyperplane n {x : Fin n → Real | x ⬝ᵥ b = β}) ∧
    (∀ H : Set (Fin n → Real), IsHyperplane n H →
      ∃ b : Fin n → Real, ∃ β : Real,
        b ≠ 0 ∧ H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
          ∀ b' : Fin n → Real, ∀ β' : Real, b' ≠ 0 →
            H = {x : Fin n → Real | x ⬝ᵥ b' = β'} →
              ∃ c : Real, c ≠ 0 ∧ b' = c • b ∧ β' = c * β) := by
  classical
  constructor
  · intro β b hb
    let M : Set (Fin n → Real) := {x : Fin n → Real | x ⬝ᵥ b = β}
    have hM : IsAffineSet n M := dotProduct_levelset_isAffine n β b
    rcases exists_point_and_translate_kernel n β b hb with ⟨x0, hx0, htrans⟩
    have hne : Set.Nonempty M := ⟨x0, by simp [M, hx0]⟩
    have hparallel :
        IsParallelAffineSet n M ((LinearMap.ker (dotProductLinear n b)) : Set (Fin n → Real)) := by
      refine ⟨x0, ?_⟩
      simpa [M, dotProductLinear_ker_eq] using htrans
    let L0 : Submodule Real (Fin n → Real) :=
      Classical.choose (parallel_submodule_unique_of_affine n M hM hne).exists
    have hL0 :
        IsParallelAffineSet n M (L0 : Set (Fin n → Real)) := by
      exact (Classical.choose_spec (parallel_submodule_unique_of_affine n M hM hne).exists).1
    have hL0_eq :
        L0 = LinearMap.ker (dotProductLinear n b) := by
      exact parallel_submodule_unique n M L0 (LinearMap.ker (dotProductLinear n b)) hL0 hparallel
    have hfin : Module.finrank Real L0 = n - 1 := by
      rw [hL0_eq]
      exact finrank_kernel_dotProduct n b hb
    have hdim : affineSetDim n M hM = Int.ofNat (n - 1) := by
      simp [affineSetDim, hne, L0, hfin, M]
    exact ⟨hM, hdim⟩
  · intro H hH
    rcases hH with ⟨hHaff, hHdim⟩
    have hne : Set.Nonempty H := by
      by_contra hne
      have hdim' : affineSetDim n H hHaff = -1 := by
        simp [affineSetDim, hne] at *
      have hneg : (Int.ofNat (n - 1) : Int) = -1 := by
        have hdim'' : affineSetDim n H hHaff = -1 := hdim'
        rw [hHdim] at hdim''
        exact hdim''
      have hnonneg : (0 : Int) ≤ (Int.ofNat (n - 1)) := Int.natCast_nonneg (n - 1)
      have hbad : (0 : Int) ≤ (-1 : Int) := by
        have hbad' := hnonneg
        rw [hneg] at hbad'
        exact hbad'
      exact (by decide : ¬ (0 : Int) ≤ (-1 : Int)) hbad
    let L0 : Submodule Real (Fin n → Real) :=
      Classical.choose (parallel_submodule_unique_of_affine n H hHaff hne).exists
    have hL0 :
        IsParallelAffineSet n H (L0 : Set (Fin n → Real)) :=
      (Classical.choose_spec (parallel_submodule_unique_of_affine n H hHaff hne).exists).1
    have hL0dim : Module.finrank Real L0 = n - 1 := by
      have hdim' :
          affineSetDim n H hHaff = Int.ofNat (Module.finrank Real L0) := by
        simp [affineSetDim, hne, L0]
      have hdim'' : (Module.finrank Real L0) = n - 1 := by
        exact Int.ofNat.inj (by simpa [hHdim] using hdim'.symm)
      exact hdim''
    rcases hL0 with ⟨x0, hx0⟩
    rcases codim_one_submodule_eq_dotProduct n L0 hL0dim hn with ⟨b, hb, hL0ker⟩
    let β : Real := x0 ⬝ᵥ b
    have hH_eq : H = {x : Fin n → Real | x ⬝ᵥ b = β} := by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ SetTranslate n (L0 : Set (Fin n → Real)) x0 := by
          simpa [hx0] using hx
        rcases hx' with ⟨y, hy, rfl⟩
        have hy' : y ⬝ᵥ b = 0 := by
          have : y ∈ (L0 : Set (Fin n → Real)) := hy
          simpa [hL0ker] using this
        calc
        (y + x0) ⬝ᵥ b = y ⬝ᵥ b + x0 ⬝ᵥ b := by
            simp
          _ = 0 + β := by simp [hy', β]
          _ = β := by simp
      · intro hx
        have hx' : x ⬝ᵥ b = β := by
          simpa using hx
        have hx' : (x - x0) ⬝ᵥ b = 0 := by
          calc
          (x - x0) ⬝ᵥ b = x ⬝ᵥ b - x0 ⬝ᵥ b := by
              simp
            _ = β - β := by simp [hx', β]
            _ = 0 := by ring
        have hxL : x - x0 ∈ (L0 : Set (Fin n → Real)) := by
          simpa [hL0ker] using hx'
        have : x ∈ SetTranslate n (L0 : Set (Fin n → Real)) x0 := by
          refine ⟨x - x0, hxL, by simp⟩
        simpa [hx0] using this
    refine ⟨b, β, hb, hH_eq, ?_⟩
    intro b' β' hb' hH'
    have hH'' : {x : Fin n → Real | x ⬝ᵥ b = β} =
        {x : Fin n → Real | x ⬝ᵥ b' = β'} := by
      simpa [hH_eq] using hH'
    simpa [hH_eq] using
      (hyperplane_normal_unique n b b' β β' hb hb' hH'')

/-- Text 1.7: In Theorem 1.3, the vector `b` is called a normal to the hyperplane `H`. -/
def IsNormalToHyperplane (n : Nat) (H : Set (Fin n → Real)) (b : Fin n → Real) : Prop :=
  ∃ β : Real, b ≠ 0 ∧ H = {x : Fin n → Real | x ⬝ᵥ b = β}

/-- Text 1.8: For any `S ⊆ R^n` there is a unique smallest affine set containing `S`,
namely the intersection of all affine sets containing `S`. This set is called the affine
hull of `S` and is denoted `aff S`. -/
def affineHull (n : Nat) (S : Set (Fin n → Real)) : Set (Fin n → Real) :=
  (affineSpan Real S : Set (Fin n → Real))

/-- The affine hull is contained in any affine set that contains `S`. -/
lemma affineHull_subset_of_affineSet {n : Nat} {S M : Set (Fin n → Real)}
    (hM : IsAffineSet n M) (hS : S ⊆ M) : affineHull n S ⊆ M := by
  rcases (isAffineSet_iff_affineSubspace n M).1 hM with ⟨s, rfl⟩
  change (affineSpan Real S : Set (Fin n → Real)) ⊆ (s : Set (Fin n → Real))
  exact (affineSpan_le (s:=S) (Q:=s)).2 hS

/-- The affine hull of a set is itself affine. -/
lemma isAffineSet_affineHull (n : Nat) (S : Set (Fin n → Real)) :
    IsAffineSet n (affineHull n S) := by
  refine (isAffineSet_iff_affineSubspace n (affineHull n S)).2 ?_
  refine ⟨affineSpan Real S, ?_⟩
  rfl

/-- The affine hull is an affine set containing `S`. -/
lemma affineHull_mem_affineSets (n : Nat) (S : Set (Fin n → Real)) :
    affineHull n S ∈ {M : Set (Fin n → Real) | IsAffineSet n M ∧ S ⊆ M} := by
  refine ⟨isAffineSet_affineHull n S, ?_⟩
  simpa [affineHull] using (subset_affineSpan (k:=Real) (s:=S))

/-- Text 1.8: The affine hull is the intersection of all affine sets containing `S`. -/
theorem affineHull_eq_sInter_affineSets (n : Nat) (S : Set (Fin n → Real)) :
    affineHull n S =
      ⋂₀ {M : Set (Fin n → Real) | IsAffineSet n M ∧ S ⊆ M} := by
  refine le_antisymm ?_ ?_
  · refine Set.subset_sInter ?_
    intro M hM
    rcases hM with ⟨hMaff, hSM⟩
    exact affineHull_subset_of_affineSet (n:=n) (S:=S) hMaff hSM
  · refine Set.sInter_subset_of_mem ?_
    exact affineHull_mem_affineSets (n:=n) (S:=S)

/-- On `Fin m`, an affine combination with total weight `1` is just the sum of smuls. -/
lemma affineCombination_eq_linear_combination_univ {n m : Nat}
    (xs : Fin m → Fin n → Real) (w : Fin m → Real)
    (hw : Finset.sum Finset.univ (fun i => w i) = 1) :
    (Finset.univ : Finset (Fin m)).affineCombination Real xs w =
      Finset.sum Finset.univ (fun i => w i • xs i) := by
  have hw' : ∑ i ∈ (Finset.univ : Finset (Fin m)), w i = (1 : Real) := by
    simpa using hw
  simpa using
    (Finset.affineCombination_eq_linear_combination (s:=Finset.univ) (p:=xs) (w:=w) hw')

/-- If all points of a family lie in `S`, then the affine span of its range is contained in
the affine span of `S`. -/
lemma affineSpan_mono_range {n m : Nat} {S : Set (Fin n → Real)}
    (xs : Fin m → Fin n → Real) (hxs : ∀ i, xs i ∈ S) :
    affineSpan Real (Set.range xs) ≤ affineSpan Real S := by
  refine affineSpan_mono (k:=Real) (V:=Fin n → Real) (P:=Fin n → Real) ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact hxs i

/-- Reindex a finset affine combination into a `Fin m`-indexed one. -/
lemma exists_fin_family_of_finset_affineCombination {n : Nat} {S : Set (Fin n → Real)}
    {v : Fin n → Real} (fs : Finset {x // x ∈ S}) (w : {x // x ∈ S} → Real)
    (hw : ∑ i ∈ fs, w i = 1)
    (hv : v = fs.affineCombination Real (fun x : {x // x ∈ S} => (x : Fin n → Real)) w) :
    ∃ m : Nat, ∃ xs : Fin m → Fin n → Real, ∃ coeffs : Fin m → Real,
      (∀ i, xs i ∈ S) ∧
      Finset.sum Finset.univ (fun i => coeffs i) = 1 ∧
      Finset.sum Finset.univ (fun i => coeffs i • xs i) = v := by
  classical
  let m : Nat := Fintype.card fs
  let e : Fin m ≃ fs := (Fintype.equivFin fs).symm
  let xs : Fin m → Fin n → Real := fun i => (e i).1.1
  let coeffs : Fin m → Real := fun i => w (e i).1
  refine ⟨m, xs, coeffs, ?_, ?_, ?_⟩
  · intro i
    exact (e i).1.property
  · have hsum_type : (∑ i : Fin m, coeffs i) = ∑ x : fs, w x := by
      simpa [coeffs] using (Equiv.sum_comp e (fun x : fs => w x))
    have hsum_fs : (∑ x : fs, w x) = ∑ i ∈ fs, w i := by
      simpa [Finset.univ_eq_attach] using (Finset.sum_attach (s:=fs) (f:=w))
    have hsum : (∑ i : Fin m, coeffs i) = (1 : Real) := by
      calc
        (∑ i : Fin m, coeffs i) = ∑ x : fs, w x := hsum_type
        _ = ∑ i ∈ fs, w i := hsum_fs
        _ = 1 := hw
    simpa using hsum
  · have hsum_type :
        (∑ i : Fin m, coeffs i • xs i) = ∑ x : fs, w x • (x : Fin n → Real) := by
      simpa [coeffs, xs] using
        (Equiv.sum_comp e (fun x : fs => w x • (x : Fin n → Real)))
    have hsum_fs :
        (∑ x : fs, w x • (x : Fin n → Real)) = ∑ i ∈ fs, w i • (i : Fin n → Real) := by
      simpa [Finset.univ_eq_attach] using
        (Finset.sum_attach (s:=fs) (f:=fun x => w x • (x : Fin n → Real)))
    have hv' : v = ∑ i ∈ fs, w i • (i : Fin n → Real) := by
      have hlin :
          fs.affineCombination Real (fun x : {x // x ∈ S} => (x : Fin n → Real)) w =
            ∑ i ∈ fs, w i • (i : Fin n → Real) := by
        simpa using
          (Finset.affineCombination_eq_linear_combination (s:=fs)
            (p:=fun x : {x // x ∈ S} => (x : Fin n → Real)) (w:=w) hw)
      calc
        v = fs.affineCombination Real (fun x : {x // x ∈ S} => (x : Fin n → Real)) w := hv
        _ = ∑ i ∈ fs, w i • (i : Fin n → Real) := hlin
    have hsum : (∑ i : Fin m, coeffs i • xs i) = v := by
      calc
        (∑ i : Fin m, coeffs i • xs i) = ∑ x : fs, w x • (x : Fin n → Real) := hsum_type
        _ = ∑ i ∈ fs, w i • (i : Fin n → Real) := hsum_fs
        _ = v := hv'.symm
    simpa using hsum

/-- Text 1.8.1: `aff S` consists of all vectors of the form
`λ₁ x₁ + ⋯ + λₘ xₘ` with `xᵢ ∈ S` and `λ₁ + ⋯ + λₘ = 1`. -/
theorem mem_affineHull_iff_finset_affineCombination (n : Nat) (S : Set (Fin n → Real))
    (v : Fin n → Real) :
    v ∈ affineHull n S ↔
      ∃ m : Nat, ∃ xs : Fin m → Fin n → Real, ∃ coeffs : Fin m → Real,
        (∀ i, xs i ∈ S) ∧
        Finset.sum Finset.univ (fun i => coeffs i) = 1 ∧
        Finset.sum Finset.univ (fun i => coeffs i • xs i) = v := by
  classical
  constructor
  · intro hv
    let p : {x // x ∈ S} → Fin n → Real := fun x => x
    have hS : S = Set.range p := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x', rfl⟩
        exact x'.property
    have hv' : v ∈ affineSpan Real (Set.range p) := by
      simpa [affineHull, hS] using hv
    obtain ⟨fs, w, hw, hvcomb⟩ :=
      (eq_affineCombination_of_mem_affineSpan (k:=Real) (p1:=v) (p:=p) hv')
    simpa [p] using
      (exists_fin_family_of_finset_affineCombination (n:=n) (S:=S) (v:=v) fs w hw hvcomb)
  · rintro ⟨m, xs, coeffs, hxs, hsum, hcomb⟩
    have hsum' : ∑ i ∈ (Finset.univ : Finset (Fin m)), coeffs i = (1 : Real) := by
      simpa using hsum
    have hcomb' :
        (Finset.univ : Finset (Fin m)).affineCombination Real xs coeffs = v := by
      have hlin :=
        affineCombination_eq_linear_combination_univ (n:=n) (xs:=xs) (w:=coeffs) hsum
      calc
        (Finset.univ : Finset (Fin m)).affineCombination Real xs coeffs =
            Finset.sum Finset.univ (fun i => coeffs i • xs i) := hlin
        _ = v := by simpa using hcomb
    have hv_range : v ∈ affineSpan Real (Set.range xs) := by
      have hmem :=
        affineCombination_mem_affineSpan (k:=Real) (s:=Finset.univ) (w:=coeffs) hsum' xs
      simpa [hcomb'] using hmem
    have hvS : v ∈ affineSpan Real S :=
      (affineSpan_mono_range (n:=n) (S:=S) xs hxs) hv_range
    simpa [affineHull] using hvS

/-- A fiber of a matrix `mulVec` map is an affine set. -/
lemma isAffineSet_mulVec_eq (m n : Nat) (b : Fin m → Real)
    (B : Matrix (Fin m) (Fin n) Real) :
    IsAffineSet n {x : Fin n → Real | B.mulVec x = b} := by
  intro x y hx hy r
  have hx' : B.mulVec x = b := by
    simpa using hx
  have hy' : B.mulVec y = b := by
    simpa using hy
  calc
    B.mulVec ((1 - r) • x + r • y)
        = B.mulVec ((1 - r) • x) + B.mulVec (r • y) := by
            simp [Matrix.mulVec_add]
    _ = (1 - r) • B.mulVec x + r • B.mulVec y := by
            simp [Matrix.mulVec_smul]
    _ = (1 - r) • b + r • b := by simp [hx', hy']
    _ = b := by
      calc
        (1 - r) • b + r • b = ((1 - r) + r) • b := by
          simpa using (add_smul (1 - r) r b).symm
        _ = (1 : Real) • b := by
          simp
        _ = b := by simp

/-- A translate of a submodule is a fiber of a linear map with that kernel. -/
lemma translate_eq_linear_fiber {n m : Nat}
    (L : Submodule Real (Fin n → Real)) (a : Fin n → Real)
    (f : (Fin n → Real) →ₗ[Real] (Fin m → Real)) (hker : LinearMap.ker f = L) :
    SetTranslate n (L : Set (Fin n → Real)) a = {x : Fin n → Real | f x = f a} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : f y = 0 := by
      have : y ∈ LinearMap.ker f := by simpa [hker] using hy
      simpa [LinearMap.mem_ker] using this
    calc
      f (y + a) = f y + f a := by
        exact f.map_add y a
      _ = f a := by simp [hy0]
  · intro hx
    have hx' : f x = f a := by
      simpa using hx
    have hx0 : f (x - a) = 0 := by
      calc
        f (x - a) = f (x + (-a)) := by simp [sub_eq_add_neg]
        _ = f x + f (-a) := by
          exact f.map_add x (-a)
        _ = f x - f a := by simp [sub_eq_add_neg]
        _ = 0 := by
          calc
            f x - f a = f a - f a := by simp [hx']
            _ = 0 := by simp
    have hxker : x - a ∈ LinearMap.ker f := by
      simpa [LinearMap.mem_ker] using hx0
    have hxL : x - a ∈ L := by
      simpa [hker] using hxker
    refine ⟨x - a, hxL, ?_⟩
    exact sub_add_cancel x a

/-- Any submodule is the kernel of a linear map to `Fin m → Real`. -/
lemma exists_linearMap_with_ker (n : Nat) (L : Submodule Real (Fin n → Real)) :
    ∃ m : Nat, ∃ f : (Fin n → Real) →ₗ[Real] (Fin m → Real), LinearMap.ker f = L := by
  classical
  let Q := (Fin n → Real) ⧸ L
  let m : Nat := Module.finrank Real Q
  let b := Module.finBasis Real Q
  let e : Q ≃ₗ[Real] (Fin m → Real) := b.equivFun
  let f : (Fin n → Real) →ₗ[Real] (Fin m → Real) := e.toLinearMap.comp (Submodule.mkQ L)
  refine ⟨m, f, ?_⟩
  ext x
  constructor
  · intro hx
    have hx0 : f x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hx0' : e (Submodule.mkQ L x) = 0 := by
      simpa [f, LinearMap.comp_apply] using hx0
    have hx0'' : e (Submodule.mkQ L x) = e 0 := by
      simpa using hx0'
    have hx0''' : Submodule.mkQ L x = 0 := by
      exact e.injective hx0''
    have hxker : x ∈ LinearMap.ker (Submodule.mkQ L) := by
      simpa [LinearMap.mem_ker] using hx0'''
    simpa [Submodule.ker_mkQ] using hxker
  · intro hx
    have hxker : x ∈ LinearMap.ker (Submodule.mkQ L) := by
      simpa [Submodule.ker_mkQ] using hx
    have hx0 : Submodule.mkQ L x = 0 := by
      simpa [LinearMap.mem_ker] using hxker
    have hx0' : e (Submodule.mkQ L x) = 0 := by
      simp [hx0]
    have hx0'' : f x = 0 := by
      simpa [f, LinearMap.comp_apply] using hx0'
    simpa [LinearMap.mem_ker] using hx0''

/-- The matrix of a linear map acts by `mulVec` in the standard basis. -/
lemma linearMap_toMatrix_mulVec {m n : Nat}
    (f : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    ∀ x,
      (LinearMap.toMatrix (Pi.basisFun Real (Fin n)) (Pi.basisFun Real (Fin m)) f).mulVec x =
        f x := by
  intro x
  have h :=
    (LinearMap.toMatrix_mulVec_repr (v₁:=Pi.basisFun Real (Fin n))
      (v₂:=Pi.basisFun Real (Fin m)) f x)
  ext i
  have h' := congrArg (fun g => g i) h
  simpa [Pi.basisFun_repr] using h'


end Section01
end Chap01
