/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Pengfei Hao, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section01_part2

section Chap01
section Section01

/- Text 1.10: A single-valued mapping `T : Real^n → Real^m` is an affine transformation if
`T ((1 - λ) • x + λ • y) = (1 - λ) • T x + λ • T y` for all `x, y : Real^n` and
`λ : Real`. -/
def IsAffineTransformation (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) : Prop :=
  ∀ x y : Fin n → Real, ∀ r : Real,
    T ((1 - r) • x + r • y) = (1 - r) • T x + r • T y

/-- Text 1.10 (mathlib): The book's notion is equivalent to an `AffineMap` after coercion. -/
theorem isAffineTransformation_iff_exists_affineMap (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) :
    IsAffineTransformation n m T ↔
      ∃ f : AffineMap Real (Fin n → Real) (Fin m → Real),
        (f : (Fin n → Real) → (Fin m → Real)) = T := by
  constructor
  · intro hT
    have hsmul : ∀ (s : Real) (z : Fin n → Real),
        T (s • z) - T 0 = s • (T z - T 0) := by
      intro s z
      have h := hT z 0 (1 - s)
      simp at h
      ext i
      simp [h]
      ring_nf
    have hadd : ∀ x y : Fin n → Real,
        T (x + y) - T 0 = (T x - T 0) + (T y - T 0) := by
      intro x y
      have hhalf : (1 - (2 : Real)⁻¹) = (2 : Real)⁻¹ := by norm_num
      have hmid :
          T ((2 : Real)⁻¹ • x + (2 : Real)⁻¹ • y) =
            (2 : Real)⁻¹ • T x + (2 : Real)⁻¹ • T y := by
        have h := hT x y ((2 : Real)⁻¹)
        simpa [hhalf] using h
      have hxy :
          x + y = (2 : Real) • ((2 : Real)⁻¹ • x + (2 : Real)⁻¹ • y) := by
        ext i
        simp
        ring_nf
      calc
        T (x + y) - T 0 =
            T ((2 : Real) • ((2 : Real)⁻¹ • x + (2 : Real)⁻¹ • y)) - T 0 := by
              rw [hxy]
        _ = (2 : Real) • (T ((2 : Real)⁻¹ • x + (2 : Real)⁻¹ • y) - T 0) := by
              exact hsmul (2 : Real) ((2 : Real)⁻¹ • x + (2 : Real)⁻¹ • y)
        _ = (2 : Real) • ((2 : Real)⁻¹ • T x + (2 : Real)⁻¹ • T y - T 0) := by
              simp [hmid]
        _ = (T x - T 0) + (T y - T 0) := by
              ext i
              simp
              ring_nf
    let A : (Fin n → Real) →ₗ[Real] (Fin m → Real) :=
      { toFun := fun x => T x - T 0
        map_add' := by
          intro x y
          exact hadd x y
        map_smul' := by
          intro s x
          exact hsmul s x }
    let f : AffineMap Real (Fin n → Real) (Fin m → Real) :=
      AffineMap.mk' T A 0 (by
        intro x
        simp [A])
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩
    intro x y r
    simpa [AffineMap.lineMap_apply_module] using f.apply_lineMap x y r

/-- Decomposition of an affine map as a linear part plus a constant (pointwise). -/
lemma affineMap_decomp_point {n m : Nat}
    (f : (Fin n → Real) →ᵃ[Real] (Fin m → Real)) (x : Fin n → Real) :
    f x = f.linear x + f 0 := by
  have h := congrArg (fun g => g x) (AffineMap.decomp f)
  simpa [Pi.add_apply] using h

/-- Any affine transformation has a linear part plus a constant vector. -/
lemma affineTransformation_exists_linearMap_add (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) :
    IsAffineTransformation n m T →
      ∃ A : (Fin n → Real) →ₗ[Real] (Fin m → Real), ∃ a : Fin m → Real,
        ∀ x : Fin n → Real, T x = A x + a := by
  intro hT
  rcases (isAffineTransformation_iff_exists_affineMap n m T).1 hT with ⟨f, rfl⟩
  refine ⟨f.linear, f 0, ?_⟩
  intro x
  simpa using affineMap_decomp_point (f:=f) x

/-- Any map of the form `x ↦ A x + a` is an affine transformation. -/
lemma affineTransformation_of_linearMap_add (n m : Nat)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) (a : Fin m → Real) :
    IsAffineTransformation n m (fun x => A x + a) := by
  intro x y r
  have hlin : A ((1 - r) • x + r • y) = (1 - r) • A x + r • A y := by
    calc
      A ((1 - r) • x + r • y)
          = A ((1 - r) • x) + A (r • y) := by
              simp [A.map_add]
      _ = (1 - r) • A x + r • A y := by
              simp [A.map_smul]
  have hsmul : (1 - r) • (A x + a) + r • (A y + a)
      = (1 - r) • A x + r • A y + a := by
    calc
      (1 - r) • (A x + a) + r • (A y + a)
          = (1 - r) • A x + (1 - r) • a + (r • A y + r • a) := by
              simp [smul_add, add_assoc]
      _ = (1 - r) • A x + r • A y + ((1 - r) • a + r • a) := by
              abel
      _ = (1 - r) • A x + r • A y + ((1 - r) + r) • a := by
              simpa using (add_smul (1 - r) r a).symm
      _ = (1 - r) • A x + r • A y + a := by
              simp [sub_add_cancel]
  calc
    (fun x => A x + a) ((1 - r) • x + r • y)
        = A ((1 - r) • x + r • y) + a := rfl
    _ = (1 - r) • A x + r • A y + a := by simp [hlin]
    _ = (1 - r) • (A x + a) + r • (A y + a) := by
          exact hsmul.symm

/-- Theorem 1.5: The affine transformations from `Real^n` to `Real^m` are the mappings `T` of
the form `T x = A x + a`, where `A` is a linear transformation and `a ∈ Real^m`. -/
theorem affineTransformation_iff_eq_linearMap_add (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) :
    IsAffineTransformation n m T ↔
      ∃ A : (Fin n → Real) →ₗ[Real] (Fin m → Real), ∃ a : Fin m → Real,
        ∀ x : Fin n → Real, T x = A x + a := by
  constructor
  · exact affineTransformation_exists_linearMap_add n m T
  · rintro ⟨A, a, hT⟩
    have hAff : IsAffineTransformation n m (fun x => A x + a) :=
      affineTransformation_of_linearMap_add n m A a
    have hT' : T = fun x => A x + a := by
      funext x
      exact hT x
    simpa [hT'] using hAff

/-- `sumExtend` agrees with the original family on the left summand. -/
lemma sumExtend_apply_inl {ι : Type*} {K : Type*} {V : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    {v : ι → V} (hs : LinearIndependent K v) (i : ι) :
    (Module.Basis.sumExtend hs) (Sum.inl i) = v i := by
  classical
  simp [Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
  rfl

/-- Extend linearly independent families to bases and map one to the other. -/
lemma linearEquiv_exists_of_linearIndependent (m n : Nat)
    (v v' : Fin m → Fin n → Real) :
    LinearIndependent Real v → LinearIndependent Real v' →
      ∃ A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real),
        ∀ i : Fin m, A (v i) = v' i := by
  classical
  intro hv hv'
  let b : Module.Basis (Fin m ⊕ Module.Basis.sumExtendIndex hv) Real (Fin n → Real) :=
    Module.Basis.sumExtend hv
  let b' : Module.Basis (Fin m ⊕ Module.Basis.sumExtendIndex hv') Real (Fin n → Real) :=
    Module.Basis.sumExtend hv'
  haveI : Finite (Fin m ⊕ Module.Basis.sumExtendIndex hv) :=
    Module.Finite.finite_basis b
  haveI : Finite (Fin m ⊕ Module.Basis.sumExtendIndex hv') :=
    Module.Finite.finite_basis b'
  haveI : Finite (Module.Basis.sumExtendIndex hv) :=
    Finite.of_injective
      (fun x => (Sum.inr x : Fin m ⊕ Module.Basis.sumExtendIndex hv))
      (by intro a b h; cases h; rfl)
  haveI : Finite (Module.Basis.sumExtendIndex hv') :=
    Finite.of_injective
      (fun x => (Sum.inr x : Fin m ⊕ Module.Basis.sumExtendIndex hv'))
      (by intro a b h; cases h; rfl)
  let _ : Fintype (Module.Basis.sumExtendIndex hv) := Fintype.ofFinite _
  let _ : Fintype (Module.Basis.sumExtendIndex hv') := Fintype.ofFinite _
  have hsum :
      Fintype.card (Fin m ⊕ Module.Basis.sumExtendIndex hv) =
        Fintype.card (Fin m ⊕ Module.Basis.sumExtendIndex hv') := by
    calc
      Fintype.card (Fin m ⊕ Module.Basis.sumExtendIndex hv)
          = Module.finrank Real (Fin n → Real) := by
              simpa using (Module.finrank_eq_card_basis b).symm
      _ = Fintype.card (Fin m ⊕ Module.Basis.sumExtendIndex hv') := by
              symm
              simpa using (Module.finrank_eq_card_basis b').symm
  have hcard :
      Fintype.card (Module.Basis.sumExtendIndex hv) =
        Fintype.card (Module.Basis.sumExtendIndex hv') := by
    have hsum' :
        Fintype.card (Fin m) + Fintype.card (Module.Basis.sumExtendIndex hv) =
          Fintype.card (Fin m) + Fintype.card (Module.Basis.sumExtendIndex hv') := by
      simpa [Fintype.card_sum] using hsum
    exact Nat.add_left_cancel hsum'
  let e2 : Module.Basis.sumExtendIndex hv ≃ Module.Basis.sumExtendIndex hv' :=
    Fintype.equivOfCardEq hcard
  let e : Fin m ⊕ Module.Basis.sumExtendIndex hv ≃ Fin m ⊕ Module.Basis.sumExtendIndex hv' :=
    Equiv.sumCongr (Equiv.refl _) e2
  let A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real) := b.equiv b' e
  refine ⟨A, ?_⟩
  intro i
  have hb : b (Sum.inl i) = v i := by
    simp [b, sumExtend_apply_inl]
  have hb' : b' (Sum.inl i) = v' i := by
    simp [b', sumExtend_apply_inl]
  calc
    A (v i) = A (b (Sum.inl i)) := by simp [hb]
    _ = b' (e (Sum.inl i)) := by simp [A]
    _ = b' (Sum.inl i) := by simp [e, Equiv.sumCongr_apply]
    _ = v' i := by simp [hb']

/-- Construct a linear equivalence sending the difference vectors of two affinely independent
families to each other. -/
lemma linearEquiv_exists_map_differences (m n : Nat)
    (b b' : Fin (m + 1) → Fin n → Real) :
    IsAffinelyIndependent m n b → IsAffinelyIndependent m n b' →
      ∃ A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real),
        ∀ i : Fin m, A (b (Fin.succ i) - b 0) = b' (Fin.succ i) - b' 0 := by
  intro hb hb'
  have hb_cases : IsAffinelyIndependent m n
      (Fin.cases (b 0) (fun i : Fin m => b (Fin.succ i))) := by
    have hb_eq :
        (Fin.cases (b 0) (fun i : Fin m => b (Fin.succ i))) = b := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro i
        simp
    simpa [hb_eq] using hb
  have hb'_cases : IsAffinelyIndependent m n
      (Fin.cases (b' 0) (fun i : Fin m => b' (Fin.succ i))) := by
    have hb_eq :
        (Fin.cases (b' 0) (fun i : Fin m => b' (Fin.succ i))) = b' := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp
      · intro i
        simp
    simpa [hb_eq] using hb'
  have hlin : LinearIndependent Real (fun i : Fin m => b (Fin.succ i) - b 0) := by
    exact (affineIndependent_iff_linearIndependent_b0 (m:=m) (n:=n)
      (b0:=b 0) (b:=fun i : Fin m => b (Fin.succ i))).1 hb_cases
  have hlin' : LinearIndependent Real (fun i : Fin m => b' (Fin.succ i) - b' 0) := by
    exact (affineIndependent_iff_linearIndependent_b0 (m:=m) (n:=n)
      (b0:=b' 0) (b:=fun i : Fin m => b' (Fin.succ i))).1 hb'_cases
  rcases
      linearEquiv_exists_of_linearIndependent (m:=m) (n:=n)
        (v:=fun i : Fin m => b (Fin.succ i) - b 0)
        (v':=fun i : Fin m => b' (Fin.succ i) - b' 0)
        hlin hlin' with ⟨A, hA⟩
  exact ⟨A, hA⟩

/-- The affine map defined by a linear equivalence and a translation is affine and bijective. -/
lemma affineTransformation_bijective_of_linearEquiv_shift (n : Nat)
    (A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real)) (b0 b0' : Fin n → Real) :
    IsAffineTransformation n n (fun x => A (x - b0) + b0') ∧
      Function.Bijective (fun x => A (x - b0) + b0') := by
  let T : (Fin n → Real) → (Fin n → Real) := fun x => A (x - b0) + b0'
  have hT : T = fun x =>
      (A : (Fin n → Real) →ₗ[Real] (Fin n → Real)) x + (b0' - A b0) := by
    funext x
    calc
      A (x - b0) + b0' = (A : (Fin n → Real) →ₗ[Real] (Fin n → Real)) x + (-A b0) + b0' := by
        simp [sub_eq_add_neg, add_assoc]
      _ = (A : (Fin n → Real) →ₗ[Real] (Fin n → Real)) x + (b0' - A b0) := by
        abel
  have hAff :
      IsAffineTransformation n n
        (fun x => (A : (Fin n → Real) →ₗ[Real] (Fin n → Real)) x + (b0' - A b0)) :=
    affineTransformation_of_linearMap_add n n
      (A : (Fin n → Real) →ₗ[Real] (Fin n → Real)) (b0' - A b0)
  have hAffT : IsAffineTransformation n n T := by
    simpa [hT] using hAff
  let S : (Fin n → Real) → (Fin n → Real) := fun y => A.symm (y - b0') + b0
  have hleft : Function.LeftInverse S T := by
    intro x
    calc
      S (T x) = A.symm (A (x - b0) + b0' - b0') + b0 := by rfl
      _ = A.symm (A (x - b0)) + b0 := by simp
      _ = x := by simp
  have hright : Function.RightInverse S T := by
    intro x
    calc
      T (S x) = A (A.symm (x - b0') + b0 - b0) + b0' := by rfl
      _ = A (A.symm (x - b0')) + b0' := by simp
      _ = x := by simp
  have hbij : Function.Bijective T :=
    ⟨(Function.LeftInverse.injective hleft), (Function.RightInverse.surjective hright)⟩
  change IsAffineTransformation n n T ∧ Function.Bijective T
  exact ⟨hAffT, hbij⟩

/-- Affinely independent families of size `n + 1` in `Real^n` span the whole space. -/
lemma affineSpan_range_eq_top_of_isAffinelyIndependent_eq (n : Nat)
    (b : Fin (n + 1) → Fin n → Real) :
    IsAffinelyIndependent n n b → affineSpan Real (Set.range b) = ⊤ := by
  intro hb
  have hAI : AffineIndependent Real b :=
    (isAffinelyIndependent_iff_affineIndependent n n b).1 hb
  have hcard : Fintype.card (Fin (n + 1)) =
      Module.finrank Real (Fin n → Real) + 1 := by
    simp
  exact
    (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
        (k:=Real) (V:=Fin n → Real) (p:=b) hAI).2 hcard

/-- Theorem 1.6: Let `{b_0, b_1, ..., b_m}` and `{b'_0, b'_1, ..., b'_m}` be affinely
independent sets in `Real^n`. Then there exists a one-to-one affine transformation `T`
of `Real^n` onto itself such that `T b_i = b'_i` for `i = 0, ..., m`. If `m = n`, then
`T` is unique. -/
theorem affineTransformation_exists_of_affineIndependent (m n : Nat)
    (b b' : Fin (m + 1) → Fin n → Real) :
    IsAffinelyIndependent m n b → IsAffinelyIndependent m n b' →
      ∃ T : (Fin n → Real) → (Fin n → Real),
        IsAffineTransformation n n T ∧ Function.Bijective T ∧
          (∀ i : Fin (m + 1), T (b i) = b' i) ∧
          (m = n → ∀ T' : (Fin n → Real) → (Fin n → Real),
            IsAffineTransformation n n T' → Function.Bijective T' →
              (∀ i : Fin (m + 1), T' (b i) = b' i) → T' = T) := by
  intro hb hb'
  rcases linearEquiv_exists_map_differences (m:=m) (n:=n) b b' hb hb' with ⟨A, hA⟩
  let T : (Fin n → Real) → (Fin n → Real) := fun x => A (x - b 0) + b' 0
  have hAffBij :
      IsAffineTransformation n n T ∧ Function.Bijective T := by
    simpa [T] using
      (affineTransformation_bijective_of_linearEquiv_shift n A (b 0) (b' 0))
  have hTpoints : ∀ i : Fin (m + 1), T (b i) = b' i := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simp [T]
    · intro i
      calc
        T (b (Fin.succ i)) = A (b (Fin.succ i) - b 0) + b' 0 := by rfl
        _ = b' (Fin.succ i) - b' 0 + b' 0 := by simp [hA i]
        _ = b' (Fin.succ i) := by simp
  refine ⟨T, hAffBij.1, hAffBij.2, hTpoints, ?_⟩
  intro hm T' hAff' _ hT'points
  subst m
  have hbspan : affineSpan Real (Set.range b) = ⊤ := by
    simpa using
      (affineSpan_range_eq_top_of_isAffinelyIndependent_eq (n:=n) (b:=b) hb)
  rcases (isAffineTransformation_iff_exists_affineMap n n T).1 hAffBij.1 with ⟨f, hf⟩
  rcases (isAffineTransformation_iff_exists_affineMap n n T').1 hAff' with ⟨f', hf'⟩
  have hEq : f' = f := by
    apply AffineMap.ext_on (k:=Real) (s:=Set.range b) hbspan
    intro x hx
    rcases hx with ⟨i, rfl⟩
    simp [hf', hf, hT'points i, hTpoints i]
  have hEqfun :
      (f' : (Fin n → Real) → (Fin n → Real)) =
        (f : (Fin n → Real) → (Fin n → Real)) := by
    exact congrArg (fun g : (Fin n → Real) →ᵃ[Real] (Fin n → Real) =>
      (g : (Fin n → Real) → (Fin n → Real))) hEq
  calc
    T' = (f' : (Fin n → Real) → (Fin n → Real)) := hf'.symm
    _ = (f : (Fin n → Real) → (Fin n → Real)) := hEqfun
    _ = T := by simp [hf]

/-- An affine set has dimension `-1` if and only if it is empty. -/
lemma affineSetDim_eq_neg_one_iff_empty (n : Nat) (M : Set (Fin n → Real))
    (hM : IsAffineSet n M) :
    affineSetDim n M hM = -1 ↔ M = ∅ := by
  classical
  by_cases hne : Set.Nonempty M
  · have hnonneg : (0 : Int) ≤ affineSetDim n M hM := by
      simp [affineSetDim, hne]
    have hne' : M ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
    constructor
    · intro h
      exfalso
      have hneg : ¬ (0 : Int) ≤ (-1 : Int) := by decide
      have h' := hnonneg
      rw [h] at h'
      exact hneg h'
    · intro h
      exact (hne' h).elim
  · have hMempty : M = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact hne ⟨x, hx⟩
    constructor
    · intro _; exact hMempty
    · intro _; simp [affineSetDim, hne]

/-- For a nonempty affine set, the dimension equals the finrank of any parallel submodule. -/
lemma affineSetDim_eq_finrank_parallel (n : Nat) (M : Set (Fin n → Real))
    (hM : IsAffineSet n M) (hne : Set.Nonempty M)
    {L : Submodule Real (Fin n → Real)}
    (hL : IsParallelAffineSet n M (L : Set (Fin n → Real))) :
    affineSetDim n M hM = Int.ofNat (Module.finrank Real L) := by
  classical
  let L0 : Submodule Real (Fin n → Real) :=
    Classical.choose (parallel_submodule_unique_of_affine n M hM hne).exists
  have hL0 : IsParallelAffineSet n M (L0 : Set (Fin n → Real)) := by
    exact (Classical.choose_spec (parallel_submodule_unique_of_affine n M hM hne).exists).1
  have hEq : L0 = L := by
    exact parallel_submodule_unique n M L0 L hL0 hL
  have hdim : affineSetDim n M hM = Int.ofNat (Module.finrank Real L0) := by
    simp [affineSetDim, hne, L0]
  subst hEq
  simpa using hdim

/-- The range of `Fin.cases` is the union of the head and tail ranges. -/
lemma range_fin_cases {m : Nat} {α : Type*} (a : α) (b : Fin m → α) :
    Set.range (Fin.cases a b) = {a} ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ ?_ i
    · left; simp
    · intro i; right; exact ⟨i, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rcases hx with rfl
      exact ⟨0, by simp⟩
    · rcases hx with ⟨i, rfl⟩
      exact ⟨Fin.succ i, by simp⟩

/-- The affine hull of `{0}` together with a basis of a submodule is that submodule. -/
lemma affineHull_zero_union_range_eq_submodule (n m : Nat)
    (L : Submodule Real (Fin n → Real)) (v : Module.Basis (Fin m) Real L) :
    affineHull n ({0} ∪ Set.range (fun i : Fin m => (v i : Fin n → Real))) =
      (L : Set (Fin n → Real)) := by
  classical
  have hspan :
      Submodule.span Real (Set.range (fun i : Fin m => (v i : Fin n → Real))) = L := by
    have hspan' :
        Submodule.span Real (Set.range (fun i : Fin m => (v i : Fin n → Real))) =
          Submodule.map L.subtype (Submodule.span Real (Set.range v)) := by
      have hspan'' :
          Submodule.span Real ((fun a : L => (a : Fin n → Real)) '' Set.range v) =
            Submodule.map L.subtype (Submodule.span Real (Set.range v)) := by
        simpa using (Submodule.span_image' (f:=L.subtype) (s:=Set.range v))
      have hrange :
          (fun a : L => (a : Fin n → Real)) '' Set.range v =
            Set.range (fun i : Fin m => (v i : Fin n → Real)) := by
        simpa [Function.comp] using
          (Set.range_comp (g:=fun a : L => (a : Fin n → Real)) (f:=v)).symm
      simpa [hrange] using hspan''
    calc
      Submodule.span Real (Set.range (fun i : Fin m => (v i : Fin n → Real)))
          = Submodule.map L.subtype (Submodule.span Real (Set.range v)) := hspan'
      _ = Submodule.map L.subtype ⊤ := by simp [v.span_eq]
      _ = L := by
          simp
  have hset :
      insert (0 : Fin n → Real) (Set.range (fun i : Fin m => (v i : Fin n → Real))) =
        ({0} ∪ Set.range (fun i : Fin m => (v i : Fin n → Real))) := by
    ext x; simp
  have hspan_set :
      affineHull n ({0} ∪ Set.range (fun i : Fin m => (v i : Fin n → Real))) =
        (Submodule.span Real (Set.range (fun i : Fin m => (v i : Fin n → Real))) :
          Set (Fin n → Real)) := by
    dsimp [affineHull]
    rw [hset]
    simpa using
      (affineSpan_insert_zero (k:=Real)
        (s:=Set.range (fun i : Fin m => (v i : Fin n → Real))))
  simpa [hspan] using hspan_set

/-- From a basis of a submodule and a base point, build affinely independent points spanning
the translate. -/
lemma affinelyIndependent_family_of_basis (n m : Nat)
    (L : Submodule Real (Fin n → Real)) (v : Module.Basis (Fin m) Real L) (b0 : Fin n → Real) :
    ∃ b : Fin (m + 1) → Fin n → Real,
      IsAffinelyIndependent m n b ∧
      affineHull n (Set.range b) = SetTranslate n (L : Set (Fin n → Real)) b0 := by
  classical
  let b1 : Fin m → Fin n → Real := fun i => b0 + (v i : Fin n → Real)
  let b : Fin (m + 1) → Fin n → Real := Fin.cases b0 b1
  have hlin : LinearIndependent Real (fun i : Fin m => (v i : Fin n → Real)) := by
    simpa [Function.comp] using
      (v.linearIndependent.map' (f:=L.subtype) (by simp))
  have hdiff : (fun i : Fin m => b1 i - b0) = fun i => (v i : Fin n → Real) := by
    funext i
    simp [b1]
  have hlin' : LinearIndependent Real (fun i : Fin m => b1 i - b0) := by
    simpa [hdiff] using hlin
  have hHullAff :
      affineHull n ({b0} ∪ Set.range b1) =
        SetTranslate n (affineHull n ({0} ∪ Set.range (fun i : Fin m => b1 i - b0))) b0 ∧
      (IsAffinelyIndependent m n (Fin.cases b0 b1) ↔
        LinearIndependent Real (fun i : Fin m => b1 i - b0)) := by
    simpa using
      (affineHull_eq_translate_and_affineIndependent_iff_linearIndependent
        (m:=m) (n:=n) (b0:=b0) (b:=b1))
  have hAI : IsAffinelyIndependent m n b := (hHullAff.2).2 hlin'
  have hL :
      affineHull n (insert (0 : Fin n → Real)
        (Set.range (fun i : Fin m => b1 i - b0))) =
        (L : Set (Fin n → Real)) := by
    simpa [hdiff, Set.singleton_union] using
      (affineHull_zero_union_range_eq_submodule (n:=n) (m:=m) L v)
  have hRange : Set.range b = {b0} ∪ Set.range b1 := by
    simpa [b, b1] using (range_fin_cases (a:=b0) (b:=b1))
  have hHull :
      affineHull n (Set.range b) =
        SetTranslate n (L : Set (Fin n → Real)) b0 := by
    have h' :
        affineHull n (Set.range b) =
          SetTranslate n (affineHull n
            (insert (0 : Fin n → Real) (Set.range (fun i : Fin m => b1 i - b0)))) b0 := by
      simpa [hRange, Set.singleton_union] using hHullAff.1
    simpa [hL] using h'
  exact ⟨b, hAI, hHull⟩

/-- Affine transformations preserve full-index affine combinations. -/
lemma affineTransformation_map_affineCombination_univ {m n : Nat}
    (T : (Fin n → Real) → (Fin n → Real))
    (b : Fin (m + 1) → Fin n → Real) (coeffs : Fin (m + 1) → Real)
    (hT : IsAffineTransformation n n T)
    (hsum : Finset.sum Finset.univ (fun i => coeffs i) = 1) :
    T (Finset.sum Finset.univ (fun i => coeffs i • b i)) =
      Finset.sum Finset.univ (fun i => coeffs i • T (b i)) := by
  classical
  rcases (isAffineTransformation_iff_exists_affineMap n n T).1 hT with ⟨f, hf⟩
  have hsum' :
      (Finset.univ : Finset (Fin (m + 1))).sum coeffs = 1 := by
    simpa using hsum
  have hcomb :
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs =
        Finset.sum Finset.univ (fun i => coeffs i • b i) := by
    exact affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs) hsum
  have hcomb' :
      (Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => T (b i)) coeffs =
        Finset.sum Finset.univ (fun i => coeffs i • T (b i)) := by
    exact
      affineCombination_eq_linear_combination_univ (n:=n) (xs:=fun i => T (b i)) (w:=coeffs)
        hsum
  have hmap :=
    Finset.map_affineCombination (s:=Finset.univ) (p:=b) (w:=coeffs) hsum' f
  calc
    T (Finset.sum Finset.univ (fun i => coeffs i • b i)) =
        (f : (Fin n → Real) → (Fin n → Real))
          ((Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs) := by
          simp [hf, hcomb]
    _ = (Finset.univ : Finset (Fin (m + 1))).affineCombination Real (fun i => f (b i)) coeffs := by
          simpa using hmap
    _ = Finset.sum Finset.univ (fun i => coeffs i • T (b i)) := by
          simp [hf, hcomb']

/-- Corollary 1.6.1: Let `M_1` and `M_2` be affine sets in `Real^n` of the same
dimension. Then there exists a one-to-one affine transformation `T` of `Real^n` onto
itself such that `T '' M_1 = M_2`. -/
theorem affineTransformation_exists_of_affineSet_same_dim (n : Nat)
    (M1 M2 : Set (Fin n → Real)) (hM1 : IsAffineSet n M1) (hM2 : IsAffineSet n M2)
    (hDim : affineSetDim n M1 hM1 = affineSetDim n M2 hM2) :
    ∃ T : (Fin n → Real) → (Fin n → Real),
      IsAffineTransformation n n T ∧ Function.Bijective T ∧ T '' M1 = M2 := by
  classical
  by_cases hne1 : Set.Nonempty M1
  · have hne2 : Set.Nonempty M2 := by
      by_contra hne2
      have hM2empty : M2 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro x hx
        exact hne2 ⟨x, hx⟩
      have hdim1_ne : affineSetDim n M1 hM1 ≠ -1 := by
        intro hdim1
        have hM1empty : M1 = ∅ :=
          (affineSetDim_eq_neg_one_iff_empty n M1 hM1).1 hdim1
        exact (Set.nonempty_iff_ne_empty.mp hne1) hM1empty
      have hdim2 : affineSetDim n M2 hM2 = -1 :=
        (affineSetDim_eq_neg_one_iff_empty n M2 hM2).2 hM2empty
      exact hdim1_ne (by simpa [hdim2] using hDim)
    rcases (parallel_submodule_unique_of_affine n M1 hM1 hne1).exists with ⟨L1, hL1⟩
    rcases hL1.1 with ⟨b01, hM1trans⟩
    rcases (parallel_submodule_unique_of_affine n M2 hM2 hne2).exists with ⟨L2, hL2⟩
    rcases hL2.1 with ⟨b02, hM2trans⟩
    have hdim1 : affineSetDim n M1 hM1 = Int.ofNat (Module.finrank Real L1) :=
      affineSetDim_eq_finrank_parallel n M1 hM1 hne1 hL1.1
    have hdim2 : affineSetDim n M2 hM2 = Int.ofNat (Module.finrank Real L2) :=
      affineSetDim_eq_finrank_parallel n M2 hM2 hne2 hL2.1
    have hfin : Module.finrank Real L2 = Module.finrank Real L1 := by
      have hInt :
          (Int.ofNat (Module.finrank Real L1)) =
            (Int.ofNat (Module.finrank Real L2)) := by
        calc
          Int.ofNat (Module.finrank Real L1) = affineSetDim n M1 hM1 := hdim1.symm
          _ = affineSetDim n M2 hM2 := hDim
          _ = Int.ofNat (Module.finrank Real L2) := hdim2
      exact (Int.ofNat_inj.mp hInt).symm
    let m : Nat := Module.finrank Real L1
    have hfin' : Module.finrank Real L2 = m := by
      simpa [m] using hfin
    let v1 : Module.Basis (Fin m) Real L1 := Module.finBasis Real L1
    let v2 : Module.Basis (Fin m) Real L2 := Module.finBasisOfFinrankEq Real L2 hfin'
    rcases
        affinelyIndependent_family_of_basis (n:=n) (m:=m) (L:=L1) (v:=v1) (b0:=b01)
      with ⟨b, hAIb, hHullb⟩
    rcases
        affinelyIndependent_family_of_basis (n:=n) (m:=m) (L:=L2) (v:=v2) (b0:=b02)
      with ⟨b', hAIb', hHullb'⟩
    rcases
        affineTransformation_exists_of_affineIndependent (m:=m) (n:=n) b b' hAIb hAIb'
      with ⟨T, hTaff, hTbij, hTpoints, hTunique⟩
    have hHullM1 : affineHull n (Set.range b) = M1 := by
      simpa [hM1trans] using hHullb
    have hHullM2 : affineHull n (Set.range b') = M2 := by
      simpa [hM2trans] using hHullb'
    refine ⟨T, hTaff, hTbij, ?_⟩
    apply subset_antisymm
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx' : x ∈ affineHull n (Set.range b) := by
        simpa [hHullM1] using hx
      rcases (exists_coeffs_univ_of_mem_affineHull_range (m:=m) (n:=n) (b:=b) hx') with
        ⟨coeffs, hsum, hcomb⟩
      have hmap :=
        affineTransformation_map_affineCombination_univ (m:=m) (n:=n)
          (T:=T) (b:=b) (coeffs:=coeffs) hTaff hsum
      have hxT : T x = Finset.sum Finset.univ (fun i => coeffs i • T (b i)) := by
        simpa [hcomb] using hmap
      have hxT' : T x = Finset.sum Finset.univ (fun i => coeffs i • b' i) := by
        simpa [hTpoints] using hxT
      have hmem : Finset.sum Finset.univ (fun i => coeffs i • b' i) ∈
          affineHull n (Set.range b') := by
        have hsum' :
            (Finset.univ : Finset (Fin (m + 1))).sum coeffs = 1 := by
          simpa using hsum
        have hmem' :
            (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b' coeffs ∈
              affineSpan Real (Set.range b') := by
          exact affineCombination_mem_affineSpan (s:=Finset.univ) (p:=b') hsum'
        have hcomb' :
            (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b' coeffs =
              Finset.sum Finset.univ (fun i => coeffs i • b' i) := by
          exact affineCombination_eq_linear_combination_univ (n:=n) (xs:=b') (w:=coeffs) hsum
        simpa [affineHull, hcomb'] using hmem'
      have : Finset.sum Finset.univ (fun i => coeffs i • b' i) ∈ M2 := by
        simpa [hHullM2] using hmem
      simpa [hxT'] using this
    · intro y hy
      have hy' : y ∈ affineHull n (Set.range b') := by
        simpa [hHullM2] using hy
      rcases (exists_coeffs_univ_of_mem_affineHull_range (m:=m) (n:=n) (b:=b') hy') with
        ⟨coeffs, hsum, hcomb⟩
      let x : Fin n → Real := Finset.sum Finset.univ (fun i => coeffs i • b i)
      have hxmem : x ∈ affineHull n (Set.range b) := by
        have hsum' :
            (Finset.univ : Finset (Fin (m + 1))).sum coeffs = 1 := by
          simpa using hsum
        have hmem' :
            (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs ∈
              affineSpan Real (Set.range b) := by
          exact affineCombination_mem_affineSpan (s:=Finset.univ) (p:=b) hsum'
        have hcomb' :
            (Finset.univ : Finset (Fin (m + 1))).affineCombination Real b coeffs =
              Finset.sum Finset.univ (fun i => coeffs i • b i) := by
          exact affineCombination_eq_linear_combination_univ (n:=n) (xs:=b) (w:=coeffs) hsum
        simpa [affineHull, hcomb', x] using hmem'
      have hxmem' : x ∈ M1 := by
        simpa [hHullM1] using hxmem
      have hmap :=
        affineTransformation_map_affineCombination_univ (m:=m) (n:=n)
          (T:=T) (b:=b) (coeffs:=coeffs) hTaff hsum
      have hxT : T x = Finset.sum Finset.univ (fun i => coeffs i • b' i) := by
        simpa [x, hTpoints] using hmap
      have hxT' : T x = y := by
        simpa [hcomb] using hxT
      exact ⟨x, hxmem', hxT'⟩
  · have hM1empty : M1 = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact hne1 ⟨x, hx⟩
    have hdim1 : affineSetDim n M1 hM1 = -1 :=
      (affineSetDim_eq_neg_one_iff_empty n M1 hM1).2 hM1empty
    have hdim2 : affineSetDim n M2 hM2 = -1 := by
      simpa [hdim1] using hDim.symm
    have hM2empty : M2 = ∅ :=
      (affineSetDim_eq_neg_one_iff_empty n M2 hM2).1 hdim2
    refine ⟨id, ?_, ?_, ?_⟩
    · intro x y r
      simp
    · exact Function.bijective_id
    · simp [hM1empty, hM2empty]

/- Text 1.11: Let `T : Real^n → Real^n` be an affine transformation with
`T x = A x + a`. If `A` is invertible, then the inverse map
`x ↦ A.symm (x - a)` is also an affine transformation. -/
/-- Rewrite the inverse formula into linear-plus-constant form. -/
lemma affine_inverse_rewrite (n : Nat)
    (A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real)) (a : Fin n → Real) :
    (fun x => A.symm (x - a)) =
      (fun x => (A.symm : (Fin n → Real) →ₗ[Real] (Fin n → Real)) x + (-A.symm a)) := by
  funext x
  simp [sub_eq_add_neg]

/-- The inverse formula is affine as a linear map plus translation. -/
lemma affineTransformation_of_linearEquiv_symm_add (n : Nat)
    (A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real)) (a : Fin n → Real) :
    IsAffineTransformation n n
      (fun x => (A.symm : (Fin n → Real) →ₗ[Real] (Fin n → Real)) x + (-A.symm a)) := by
  simpa using
    (affineTransformation_of_linearMap_add n n
      (A.symm : (Fin n → Real) →ₗ[Real] (Fin n → Real)) (-A.symm a))

/-- The inverse of an affine map with linear part `A` is affine. -/
theorem inverse_affineTransformation_of_linearEquiv (n : Nat)
    (A : (Fin n → Real) ≃ₗ[Real] (Fin n → Real)) (a : Fin n → Real) :
    IsAffineTransformation n n (fun x => A x + a) →
      IsAffineTransformation n n (fun x => A.symm (x - a)) := by
  intro _
  simpa [affine_inverse_rewrite n A a] using
    (affineTransformation_of_linearEquiv_symm_add n A a)

/-- The image of an affine set under an affine transformation is affine. -/
lemma affineTransformation_image_affineSet (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) :
    IsAffineTransformation n m T →
      ∀ M : Set (Fin n → Real), IsAffineSet n M → IsAffineSet m (T '' M) := by
  intro hT M hM y1 y2 hy1 hy2 r
  rcases hy1 with ⟨x1, hx1, rfl⟩
  rcases hy2 with ⟨x2, hx2, rfl⟩
  refine ⟨(1 - r) • x1 + r • x2, hM x1 x2 hx1 hx2 r, ?_⟩
  exact hT x1 x2 r

/-- The preimage of an affine set under an affine transformation is affine. -/
lemma affineTransformation_preimage_affineSet (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) :
    IsAffineTransformation n m T →
      ∀ N : Set (Fin m → Real), IsAffineSet m N → IsAffineSet n (T ⁻¹' N) := by
  intro hT N hN x y hx hy r
  have hx' : T x ∈ N := by simpa using hx
  have hy' : T y ∈ N := by simpa using hy
  have hcomb : (1 - r) • T x + r • T y ∈ N := hN (T x) (T y) hx' hy' r
  simpa [hT x y r] using hcomb

/-- Text 1.12: Let `T : ℝ^n → ℝ^m` be an affine transformation. Then for every affine set
`M ⊆ ℝ^n`, the image `T '' M` is an affine set in `ℝ^m`. Consequently, for every set
`S ⊆ ℝ^n`, affine transformations preserve affine hulls:
`affineHull m (T '' S) = T '' affineHull n S`. -/
theorem affineTransformation_image_affineSet_and_affineHull (n m : Nat)
    (T : (Fin n → Real) → (Fin m → Real)) :
    IsAffineTransformation n m T →
      (∀ M : Set (Fin n → Real), IsAffineSet n M → IsAffineSet m (T '' M)) ∧
      (∀ S : Set (Fin n → Real),
        affineHull m (T '' S) = T '' affineHull n S) := by
  intro hT
  refine ⟨?_, ?_⟩
  · intro M hM
    exact affineTransformation_image_affineSet n m T hT M hM
  · intro S
    refine subset_antisymm ?_ ?_
    · have hAff : IsAffineSet m (T '' affineHull n S) :=
        affineTransformation_image_affineSet n m T hT _ (isAffineSet_affineHull n S)
      have hS : S ⊆ affineHull n S := by
        simpa [affineHull] using (subset_affineSpan (k:=Real) (s:=S))
      have hTS : T '' S ⊆ T '' affineHull n S := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨x, hS hx, rfl⟩
      exact affineHull_subset_of_affineSet hAff hTS
    · classical
      have hsubset :
          T '' affineHull n S ⊆
            ⋂₀ {N : Set (Fin m → Real) | IsAffineSet m N ∧ T '' S ⊆ N} := by
        refine Set.subset_sInter ?_
        intro N hN
        rcases hN with ⟨hN_aff, hN_cont⟩
        have hpre : IsAffineSet n (T ⁻¹' N) :=
          affineTransformation_preimage_affineSet n m T hT N hN_aff
        have hSpre : S ⊆ T ⁻¹' N := by
          intro x hx
          exact hN_cont ⟨x, hx, rfl⟩
        have hHull_sub : affineHull n S ⊆ T ⁻¹' N :=
          affineHull_subset_of_affineSet hpre hSpre
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact hHull_sub hx
      simpa [affineHull_eq_sInter_affineSets (n:=m) (S:=T '' S)] using hsubset

/-- Text 1.13: Let `M ⊆ ℝ^N` be an `n`-dimensional affine set with `0 < n < N` and set
`m := N - n`. A Tucker representation is a coordinate permutation so that `x ∈ M` iff
the last `m` coordinates are affine functions of the first `n`, equivalently `M` is the
graph of an affine map `ℝ^n → ℝ^m`; for linear subspaces the constants vanish. -/
def IsTuckerRepresentation (n m : Nat) (M : Set (Fin (n + m) → Real)) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (n + m)))
    (f : AffineMap Real (Fin n → Real) (Fin m → Real)),
    M =
      {x | let p := (Fin.appendEquiv n m).symm (x ∘ σ); p.2 = f p.1}

/-- A nonempty affine set is a translate of a submodule. -/
lemma affineSet_eq_translate_submodule (n : Nat) (C : Set (Fin n → Real))
    (hC : IsAffineSet n C) (hne : Set.Nonempty C) :
    ∃ (L : Submodule Real (Fin n → Real)) (x0 : Fin n → Real),
      C = SetTranslate n (L : Set (Fin n → Real)) x0 := by
  classical
  rcases (parallel_submodule_unique_of_affine n C hC hne).exists with ⟨L, hL⟩
  rcases hL.1 with ⟨x0, hx0⟩
  exact ⟨L, x0, hx0⟩

/-- Any submodule admits a complementary submodule. -/
lemma exists_isCompl_submodule (n : Nat) (L : Submodule Real (Fin n → Real)) :
    ∃ W : Submodule Real (Fin n → Real), IsCompl L W := by
  classical
  simpa using (Submodule.exists_isCompl (p:=L))

/-- In product coordinates given by a complement, a translate of `L` has constant `W`-part. -/
lemma image_translate_under_prod_equiv (n : Nat)
    (L W : Submodule Real (Fin n → Real)) (hLW : IsCompl L W) (x0 : Fin n → Real) :
    (Submodule.prodEquivOfIsCompl L W hLW).symm '' SetTranslate n (L : Set (Fin n → Real)) x0 =
      {p : L × W | p.2 = ((Submodule.prodEquivOfIsCompl L W hLW).symm x0).2} := by
  classical
  set Φ : (Fin n → Real) ≃ₗ[Real] (L × W) := (Submodule.prodEquivOfIsCompl L W hLW).symm
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨l, hl, rfl⟩
    have hΦ_l : (Φ l).2 = 0 := by
      have h :=
        (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero (p:=L) (q:=W) hLW (x:=l))
      exact (by simpa [Φ] using (h).2 hl)
    have hΦ_add : Φ (l + x0) = Φ l + Φ x0 := by
      simp
    have hΦ_snd : (Φ (l + x0)).2 = (Φ l).2 + (Φ x0).2 := by
      simp [hΦ_add]
    have hΦ_snd' : (Φ (l + x0)).2 = (Φ x0).2 := by
      calc
        (Φ (l + x0)).2 = (Φ l).2 + (Φ x0).2 := hΦ_snd
        _ = 0 + (Φ x0).2 := by simp [hΦ_l]
        _ = (Φ x0).2 := by simp
    simpa [Φ] using hΦ_snd'
  · intro hp
    refine ⟨Φ.symm p, ?_, by simp [Φ]⟩
    refine ⟨(p.1 : Fin n → Real) - (Φ x0).1, ?_, ?_⟩
    · exact L.sub_mem (show (p.1 : Fin n → Real) ∈ L from p.1.property)
        (show ((Φ x0).1 : Fin n → Real) ∈ L from (Φ x0).1.property)
    · have hp' : p.2 = (Φ x0).2 := by
        simpa using hp
      have hx0 : x0 = (Φ x0).1 + (Φ x0).2 := by
        calc
          x0 = Φ.symm (Φ x0) := (Φ.symm_apply_apply x0).symm
          _ = (Φ x0).1 + (Φ x0).2 := by
            simpa [Φ] using
              (Submodule.coe_prodEquivOfIsCompl' (p:=L) (q:=W) (h:=hLW) (Φ x0))
      have hcalc : Φ.symm p = (p.1 : Fin n → Real) - (Φ x0).1 + x0 := by
        calc
          Φ.symm p = (p.1 : Fin n → Real) + p.2 := by
            simp [Φ]
          _ = (p.1 : Fin n → Real) + (Φ x0).2 := by simp [hp']
          _ = (p.1 : Fin n → Real) - (Φ x0).1 + ((Φ x0).1 + (Φ x0).2) := by
            abel
          _ = (p.1 : Fin n → Real) - (Φ x0).1 + x0 := by
            rw [← hx0]
      exact hcalc.symm

/- Text 1.13.1: Theorem. Let `X` be a finite-dimensional real normed linear space and let
`C ⊂ X` be a nontrivial affine set, i.e., `C ≠ ∅` and `C ≠ X`. Then there exist finite-dimensional
real normed linear spaces `Y` and `Z`, a linear subspace `L ⊂ Y`, a continuous affine map
`T : Y → Z`, and a point `y0 ∈ Y` such that
`C = {x ∈ X : x = T(y), y ∈ L + y0}`. Equivalently, there exist a finite-dimensional real normed
linear space `Y`, a continuous linear map `A : Y → X` and a point `x0 ∈ X` such that
`C = x0 + A(Y)`, and, with respect to a suitable decomposition `Y = Y1 × Y2`, `C` can be written
as the graph of an affine mapping `f : Y1 → Y2`, i.e.,
`C = {(y1, f y1) : y1 ∈ Y1}`. In particular, every nontrivial affine set in a finite-dimensional
real normed linear space is (up to an isomorphism of the ambient space) the graph of an affine
transformation between two finite-dimensional real normed linear spaces. -/
theorem affineSet_is_graph_of_affineMap (n : Nat) (C : Set (Fin n → Real))
    (hC : IsAffineSet n C) (hne : Set.Nonempty C) :
    ∃ (L W : Submodule Real (Fin n → Real))
      (Φ : (Fin n → Real) ≃ₗ[Real] (L × W))
      (f : AffineMap Real L W),
      Φ '' C = {p : L × W | p.2 = f p.1} := by
  classical
  rcases affineSet_eq_translate_submodule n C hC hne with ⟨L, x0, hCeq⟩
  rcases exists_isCompl_submodule n L with ⟨W, hLW⟩
  refine ⟨L, W, (Submodule.prodEquivOfIsCompl L W hLW).symm,
    AffineMap.const Real L ((Submodule.prodEquivOfIsCompl L W hLW).symm x0).2, ?_⟩
  have himage :
      (Submodule.prodEquivOfIsCompl L W hLW).symm '' C =
        {p : L × W | p.2 = ((Submodule.prodEquivOfIsCompl L W hLW).symm x0).2} := by
    simpa [hCeq] using
      (image_translate_under_prod_equiv (n:=n) (L:=L) (W:=W) hLW x0)
  simpa [AffineMap.const_apply] using himage

end Section01
end Chap01
