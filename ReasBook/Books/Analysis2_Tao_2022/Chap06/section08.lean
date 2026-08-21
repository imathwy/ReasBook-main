/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib

section Chap06
section Section08

/-- Definition 6.16 (Graph of a function): for `f : ℝ^n → ℝ`, the graph of `f` is
the subset `{(x, f x) : x ∈ ℝ^n}` of `ℝ^(n+1)`. -/
def graphOfFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  Set.range (fun x => Fin.snoc x (f x))

/-- Definition 6.17 (Vertical line test): a subset `S ⊆ ℝ²` is the graph of some
function `f : ℝ → ℝ` if and only if for every `x : ℝ` there exists a unique
`y : ℝ` such that `(x, y) ∈ S`. -/
theorem verticalLineTest (S : Set (ℝ × ℝ)) :
    (∃ f : ℝ → ℝ, S = Set.range (fun x => (x, f x))) ↔
      ∀ x : ℝ, ∃! y : ℝ, (x, y) ∈ S := by
  constructor
  · rintro ⟨f, rfl⟩ x
    refine ⟨f x, ⟨x, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨x', hx'⟩
    have hx : x' = x := by
      simpa using congrArg Prod.fst hx'
    have hy' : f x' = y := by
      simpa using congrArg Prod.snd hx'
    simpa [hx] using hy'.symm
  · intro h
    classical
    let f : ℝ → ℝ := fun x => Classical.choose (ExistsUnique.exists (h x))
    have hf_mem : ∀ x : ℝ, (x, f x) ∈ S := by
      intro x
      exact Classical.choose_spec (ExistsUnique.exists (h x))
    have hf_unique : ∀ x y : ℝ, (x, y) ∈ S → y = f x := by
      intro x y hy
      exact (h x).unique hy (hf_mem x)
    refine ⟨f, Set.Subset.antisymm ?_ ?_⟩
    · rintro ⟨x, y⟩ hxy
      refine ⟨x, ?_⟩
      dsimp [f]
      exact Prod.ext rfl (hf_unique x y hxy).symm
    · intro p hp
      rcases hp with ⟨x, hx⟩
      rw [← hx]
      exact hf_mem x

/-- Definition 6.18 (Hypersurface defined by an equation): for g : ℝ^n → ℝ,
the hypersurface (level set) defined by g is Z(g) = {x ∈ ℝ^n | g x = 0}. -/
def hypersurfaceDefinedBy (n : ℕ) (g : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {x | g x = 0}

/-- Definition 6.19 (Critical point): for a differentiable function
`f : ℝ^n → ℝ`, a point `x₀` is a critical point of `f` when `∇ f(x₀) = 0`.
In finite-dimensional coordinates, this is expressed as differentiability at `x₀`
and vanishing Fréchet derivative there. -/
def IsCriticalPoint {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x₀ : Fin n → ℝ) : Prop :=
  DifferentiableAt ℝ f x₀ ∧ fderiv ℝ f x₀ = 0

/-- The coordinate-direction derivative of a scalar function on `ℝ^n` within a set. -/
noncomputable def partialDerivWithin {n : ℕ} (f : (Fin n → ℝ) → ℝ) (s : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (fderivWithin ℝ f s x) (Pi.single i 1)

/-- Helper for Theorem 6.11: a continuous linear map `ℝ →L[ℝ] ℝ` is bijective if it is nonzero
at `1`. -/
lemma helperForTheorem_6_11_realLinearMap_bijective_of_map_one_ne_zero
    (L : ℝ →L[ℝ] ℝ) (hL : L 1 ≠ 0) : Function.Bijective L := by
  constructor
  · intro x y hxy
    have hlin : L (x - y) = (x - y) * L 1 := by
      simpa [smul_eq_mul] using (L.map_smulₛₗ (x - y) 1)
    have hzero : L (x - y) = 0 := by
      simpa [map_sub, hxy]
    have hmul : (x - y) * L 1 = 0 := by
      simpa [hlin] using hzero
    have hxyeq : x - y = 0 := (mul_eq_zero.mp hmul).resolve_right hL
    exact sub_eq_zero.mp hxyeq
  · intro y
    refine ⟨y / L 1, ?_⟩
    have hlin : L (y / L 1) = (y / L 1) * L 1 := by
      simpa [smul_eq_mul] using (L.map_smulₛₗ (y / L 1) 1)
    calc
      L (y / L 1) = (y / L 1) * L 1 := hlin
      _ = y := by
        field_simp [hL]

/-- Helper for Theorem 6.11: convert the nonvanishing within-partial at the base point to the
ambient Fréchet derivative coordinate being nonzero. -/
lemma helperForTheorem_6_11_lastPartial_ne_zero_fderiv
    {n : ℕ}
    {E : Set (Fin (n + 1) → ℝ)}
    {f : (Fin (n + 1) → ℝ) → ℝ}
    {y' : Fin n → ℝ}
    {yLast : ℝ}
    (hEopen : IsOpen E)
    (hf : ContDiffOn ℝ 1 f E)
    (hy : Fin.snoc y' yLast ∈ E)
    (hpartial : partialDerivWithin f E (Fin.snoc y' yLast) (Fin.last n) ≠ 0) :
    (fderiv ℝ f (Fin.snoc y' yLast)) (Pi.single (Fin.last n) 1) ≠ 0 := by
  have hcontAt : ContDiffAt ℝ 1 f (Fin.snoc y' yLast) := hf.contDiffAt (hEopen.mem_nhds hy)
  have hdiffAt : DifferentiableAt ℝ f (Fin.snoc y' yLast) := hcontAt.differentiableAt (by norm_num)
  have hEq : fderivWithin ℝ f E (Fin.snoc y' yLast) = fderiv ℝ f (Fin.snoc y' yLast) :=
    fderivWithin_eq_fderiv (hEopen.uniqueDiffWithinAt hy) hdiffAt
  simpa [partialDerivWithin, hEq] using hpartial

/-- Helper for Theorem 6.11: graph equality determines the implicit function uniquely on `U`. -/
lemma helperForTheorem_6_11_uniqueness_from_graph_equality
    {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)}
    {V : Set (Fin (n + 1) → ℝ)}
    {g g2 : (Fin n → ℝ) → ℝ}
    (hA : {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g x')) '' U)
    (hA2 : {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g2 x')) '' U) :
    ∀ x' ∈ U, g2 x' = g x' := by
  intro x' hxU
  have hxZero : Fin.snoc x' (g2 x') ∈ {x | x ∈ V ∧ f x = 0} := by
    rw [hA2]
    exact ⟨x', hxU, rfl⟩
  rw [hA] at hxZero
  rcases hxZero with ⟨x0, -, hxEq⟩
  have hxEq' : (Fin.snoc x0 (g x0) : Fin (n + 1) → ℝ) = Fin.snoc x' (g2 x') := by
    simpa using hxEq
  have hx0Eq : x0 = x' := (Fin.snoc_injective2 hxEq').1
  have hlastEq : g x0 = g2 x' := (Fin.snoc_injective2 hxEq').2
  simpa [hx0Eq] using hlastEq.symm

/-- Theorem 6.11 (Implicit function theorem): in ambient coordinates
`(x', x_{n+1}) ∈ ℝ^(n+1)` (corresponding to the book's `ℝ^n` after reindexing), if
`E ⊆ ℝ^(n+1)` is open, `f` is continuously differentiable on `E`,
`f (y', yLast) = 0`, and `∂f/∂x_{n+1} (y', yLast) ≠ 0`, then there are open sets `U, V`
with `(y', yLast) ∈ V`, `y' ∈ U`, and a `C^1` function `g` whose graph over `U` cuts out
the zero set of `f` in `V`; moreover this `g` is unique on `U` and satisfies the usual
derivative quotient formula in each `x'`-direction. -/
theorem implicitFunctionTheorem
    (n : ℕ)
    (E : Set (Fin (n + 1) → ℝ))
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (y' : Fin n → ℝ)
    (yLast : ℝ)
    (hEopen : IsOpen E)
    (hf : ContDiffOn ℝ 1 f E)
    (hy : Fin.snoc y' yLast ∈ E)
    (hyZero : f (Fin.snoc y' yLast) = 0)
    (hpartial : partialDerivWithin f E (Fin.snoc y' yLast) (Fin.last n) ≠ 0) :
    ∃ U : Set (Fin n → ℝ),
      IsOpen U ∧ y' ∈ U ∧
        ∃ V : Set (Fin (n + 1) → ℝ),
          IsOpen V ∧ Fin.snoc y' yLast ∈ V ∧ V ⊆ E ∧
            let A : ((Fin n → ℝ) → ℝ) → Prop := fun g =>
              g y' = yLast ∧
                {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g x')) '' U;
            let B : ((Fin n → ℝ) → ℝ) → Prop := fun g =>
              ContDiffOn ℝ 1 g U ∧
                ∀ x' ∈ U, ∀ j : Fin n,
                  partialDerivWithin g U x' j =
                    -(
                      partialDerivWithin f E (Fin.snoc x' (g x')) (Fin.castSucc j) /
                        partialDerivWithin f E (Fin.snoc x' (g x')) (Fin.last n)
                    );
            ∃ g : (Fin n → ℝ) → ℝ,
              A g ∧ B g ∧
                ∀ g2 : (Fin n → ℝ) → ℝ,
                  A g2 → ∀ x' ∈ U, g2 x' = g x' := by
  classical
  have hpartialFderiv :
      (fderiv ℝ f (Fin.snoc y' yLast)) (Pi.single (Fin.last n) 1) ≠ 0 := by
    exact helperForTheorem_6_11_lastPartial_ne_zero_fderiv hEopen hf hy hpartial
  have huniqGraph :
      ∀ {U : Set (Fin n → ℝ)} {V : Set (Fin (n + 1) → ℝ)}
        {g g2 : (Fin n → ℝ) → ℝ},
        {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g x')) '' U →
          {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g2 x')) '' U →
            ∀ x' ∈ U, g2 x' = g x' := by
    intro U V g g2 hA hA2
    exact helperForTheorem_6_11_uniqueness_from_graph_equality hA hA2
  have hLinearBijectiveTemplate :
      ∀ L : ℝ →L[ℝ] ℝ, L 1 ≠ 0 → Function.Bijective L := by
    intro L hL
    exact helperForTheorem_6_11_realLinearMap_bijective_of_map_one_ne_zero L hL
  have hBuildIsContDiffImplicitAt :
      IsContDiffImplicitAt (𝕜 := ℝ) 1
        (fun p : (Fin n → ℝ) × ℝ => f (Fin.snoc p.1 p.2))
        (fderiv ℝ (fun p : (Fin n → ℝ) × ℝ => f (Fin.snoc p.1 p.2)) (y', yLast))
        (y', yLast) := by
    let F : (Fin n → ℝ) × ℝ → ℝ := fun p => f (Fin.snoc p.1 p.2)
    have hOneLe : (1 : WithTop ℕ∞) ≤ 1 := le_rfl
    have hcontAtf : ContDiffAt ℝ 1 f (Fin.snoc y' yLast) :=
      hf.contDiffAt (hEopen.mem_nhds hy)
    have hcontAtSnoc :
        ContDiffAt ℝ 1
          (fun p : (Fin n → ℝ) × ℝ =>
            (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ))
          (y', yLast) := by
      refine contDiffAt_pi.2 ?_
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa [Fin.snoc_last] using
          (contDiffAt_snd : ContDiffAt ℝ 1 (Prod.snd : (Fin n → ℝ) × ℝ → ℝ) (y', yLast))
      · intro j
        have hEval : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => x j) y' := by
          simpa using
            (contDiffAt_apply (𝕜 := ℝ) (n := (1 : WithTop ℕ∞)) (ι := Fin n) (E := ℝ) j y')
        simpa [Function.comp, Fin.snoc_castSucc] using
          (hEval.comp (y', yLast) contDiffAt_fst)
    have hcontAtF : ContDiffAt ℝ 1 F (y', yLast) := by
      simpa [F] using hcontAtf.comp (y', yLast) hcontAtSnoc
    have hdiffAtF : DifferentiableAt ℝ F (y', yLast) :=
      hcontAtF.differentiableAt hOneLe
    have hHasFDerivAtF : HasFDerivAt F (fderiv ℝ F (y', yLast)) (y', yLast) :=
      hdiffAtF.hasFDerivAt
    let L : ℝ →L[ℝ] ℝ :=
      (fderiv ℝ F (y', yLast)).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ)
    have hDerivLineFromF : HasFDerivAt (fun t : ℝ => F (y', t)) L yLast := by
      simpa [F, L, Function.comp] using
        hHasFDerivAtF.comp yLast
          ((hasFDerivAt_const (c := y') (x := yLast)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (x := yLast)))
    let M : ℝ →L[ℝ] (Fin (n + 1) → ℝ) :=
      ContinuousLinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases (ContinuousLinearMap.id ℝ ℝ) (fun _ : Fin n => (0 : ℝ →L[ℝ] ℝ)) i)
    have hDerivSnocLine : HasFDerivAt (fun t : ℝ => (Fin.snoc y' t : Fin (n + 1) → ℝ)) M yLast := by
      refine hasFDerivAt_pi.2 ?_
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa [M, Fin.snoc_last] using (hasFDerivAt_id (𝕜 := ℝ) (x := yLast))
      · intro j
        simpa [M, Fin.snoc_castSucc] using (hasFDerivAt_const (c := y' j) (x := yLast))
    have hdiffAtf : DifferentiableAt ℝ f (Fin.snoc y' yLast) :=
      hcontAtf.differentiableAt hOneLe
    have hDerivLineDirect :
        HasFDerivAt (fun t : ℝ => f (Fin.snoc y' t))
          ((fderiv ℝ f (Fin.snoc y' yLast)).comp M) yLast := by
      exact (hdiffAtf.hasFDerivAt.comp yLast hDerivSnocLine)
    have hDerivLineDirect' : HasFDerivAt (fun t : ℝ => F (y', t))
        ((fderiv ℝ f (Fin.snoc y' yLast)).comp M) yLast := by
      simpa [F] using hDerivLineDirect
    have hLMEq : L = (fderiv ℝ f (Fin.snoc y' yLast)).comp M :=
      hDerivLineFromF.unique hDerivLineDirect'
    have hMone : M 1 = Pi.single (Fin.last n) 1 := by
      ext i
      refine Fin.lastCases ?_ ?_ i
      · simp [M]
      · intro j
        simp [M, Fin.castSucc_ne_last]
    have hLone : L 1 = (fderiv ℝ f (Fin.snoc y' yLast)) (Pi.single (Fin.last n) 1) := by
      calc
        L 1 = ((fderiv ℝ f (Fin.snoc y' yLast)).comp M) 1 := by simpa [hLMEq]
        _ = (fderiv ℝ f (Fin.snoc y' yLast)) (M 1) := rfl
        _ = (fderiv ℝ f (Fin.snoc y' yLast)) (Pi.single (Fin.last n) 1) := by
          simp [hMone]
    have hLnonzero : L 1 ≠ 0 := by
      rw [hLone]
      exact hpartialFderiv
    have hBij : Function.Bijective L := by
      exact hLinearBijectiveTemplate L hLnonzero
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [F] using hHasFDerivAtF
    · simpa [F] using hcontAtF
    · simpa [F, L] using hBij
    · exact hOneLe
  have hMainData :
      ∃ U : Set (Fin n → ℝ),
        IsOpen U ∧ y' ∈ U ∧
          ∃ V : Set (Fin (n + 1) → ℝ),
            IsOpen V ∧ Fin.snoc y' yLast ∈ V ∧ V ⊆ E ∧
              ∃ g : (Fin n → ℝ) → ℝ,
                g y' = yLast ∧
                  {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g x')) '' U ∧
                    ContDiffOn ℝ 1 g U ∧
                      ∀ x' ∈ U, ∀ j : Fin n,
                        partialDerivWithin g U x' j =
                          -(
                            partialDerivWithin f E (Fin.snoc x' (g x')) (Fin.castSucc j) /
                              partialDerivWithin f E (Fin.snoc x' (g x')) (Fin.last n)
                          ) := by
    let hIF := hBuildIsContDiffImplicitAt
    let F : (Fin n → ℝ) × ℝ → ℝ := fun p => f (Fin.snoc p.1 p.2)
    let e0 : OpenPartialHomeomorph ((Fin n → ℝ) × ℝ) ((Fin n → ℝ) × ℝ) :=
      hIF.implicitFunctionData.toOpenPartialHomeomorph
    let s : Set ((Fin n → ℝ) × ℝ) := {p | Fin.snoc p.1 p.2 ∈ E}
    have hOneNeTop : (1 : WithTop ℕ∞) ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      simp
    have hsOpen : IsOpen s := by
      have hSnocCont :
          Continuous (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) := by
        exact (Continuous.finSnoc continuous_fst continuous_snd)
      simpa [s] using hEopen.preimage hSnocCont
    let e1 : OpenPartialHomeomorph ((Fin n → ℝ) × ℝ) ((Fin n → ℝ) × ℝ) :=
      e0.restrOpen s hsOpen
    have hApplyE0 : ∀ p : (Fin n → ℝ) × ℝ, e0 p = (p.1, f (Fin.snoc p.1 p.2)) := by
      intro p
      rfl
    have hySource1 : (y', yLast) ∈ e1.source := by
      have hySource0 : (y', yLast) ∈ e0.source := by
        exact hIF.implicitFunctionData.pt_mem_toOpenPartialHomeomorph_source
      have hyInS : (y', yLast) ∈ s := by
        simpa [s] using hy
      simpa [e1, OpenPartialHomeomorph.restrOpen_source] using And.intro hySource0 hyInS
    have hyMapEq1 : e1 (y', yLast) = (y', 0) := by
      calc
        e1 (y', yLast) = e0 (y', yLast) := by
          simp [e1]
        _ = (y', f (Fin.snoc y' yLast)) := hApplyE0 (y', yLast)
        _ = (y', 0) := by
          simp [hyZero]
    have hyTarget1 : (y', 0) ∈ e1.target := by
      have hyTarget1' : e1 (y', yLast) ∈ e1.target := e1.map_source hySource1
      simpa [hyMapEq1] using hyTarget1'
    let eDeriv : ((Fin n → ℝ) × ℝ) ≃L[ℝ] ((Fin n → ℝ) × ℝ) :=
      hIF.implicitFunctionData.leftDeriv.equivProdOfSurjectiveOfIsCompl
        hIF.implicitFunctionData.rightDeriv
        hIF.implicitFunctionData.range_leftDeriv
        hIF.implicitFunctionData.range_rightDeriv
        hIF.implicitFunctionData.isCompl_ker
    have hHasFDerivAtE0 : HasFDerivAt e0 (eDeriv : ((Fin n → ℝ) × ℝ) →L[ℝ] ((Fin n → ℝ) × ℝ))
        (y', yLast) := by
      have hStrictE0 :
          HasStrictFDerivAt e0 (eDeriv : ((Fin n → ℝ) × ℝ) →L[ℝ] ((Fin n → ℝ) × ℝ))
            (y', yLast) := by
        simpa [e0, eDeriv, F] using hIF.implicitFunctionData.hasStrictFDerivAt
      exact hStrictE0.hasFDerivAt
    have hContDiffAtE0 : ContDiffAt ℝ 1 e0 (y', yLast) := by
      have hContDiffAtF : ContDiffAt ℝ 1 F (y', yLast) := by
        simpa [F] using hIF.contDiffAt
      have hContDiffAtProd : ContDiffAt ℝ 1 (fun p : (Fin n → ℝ) × ℝ => (p.1, F p)) (y', yLast) :=
        contDiffAt_fst.prodMk hContDiffAtF
      simpa [e0] using hContDiffAtProd
    have hHasFDerivAtE1 : HasFDerivAt e1
        (eDeriv : ((Fin n → ℝ) × ℝ) →L[ℝ] ((Fin n → ℝ) × ℝ)) (y', yLast) := by
      simpa [e1] using hHasFDerivAtE0
    have hContDiffAtE1 : ContDiffAt ℝ 1 e1 (y', yLast) := by
      simpa [e1] using hContDiffAtE0
    have hySymm1 : e1.symm (y', 0) = (y', yLast) := by
      have hyLeft1 : e1.symm (e1 (y', yLast)) = (y', yLast) := e1.left_inv hySource1
      simpa [hyMapEq1] using hyLeft1
    have hHasFDerivAtE1AtSymm : HasFDerivAt e1
        (eDeriv : ((Fin n → ℝ) × ℝ) →L[ℝ] ((Fin n → ℝ) × ℝ)) (e1.symm (y', 0)) := by
      simpa [hySymm1] using hHasFDerivAtE1
    have hContDiffAtE1AtSymm : ContDiffAt ℝ 1 e1 (e1.symm (y', 0)) := by
      simpa [hySymm1] using hContDiffAtE1
    have hContDiffAtSymmE1 : ContDiffAt ℝ 1 e1.symm (y', 0) := by
      exact e1.contDiffAt_symm hyTarget1 hHasFDerivAtE1AtSymm hContDiffAtE1AtSymm
    let e : OpenPartialHomeomorph ((Fin n → ℝ) × ℝ) ((Fin n → ℝ) × ℝ) :=
      e1.restrContDiff ℝ 1 hOneNeTop
    have hySource : (y', yLast) ∈ e.source := by
      have hSymmAtImage : ContDiffAt ℝ 1 e1.symm (e1 (y', yLast)) := by
        simpa [hyMapEq1] using hContDiffAtSymmE1
      have hySourceAnd :
          (y', yLast) ∈ e1.source ∩ {x | ContDiffAt ℝ 1 e1 x ∧ ContDiffAt ℝ 1 e1.symm (e1 x)} := by
        exact And.intro hySource1 (And.intro hContDiffAtE1 hSymmAtImage)
      simpa [e, OpenPartialHomeomorph.restrContDiff_source] using hySourceAnd
    have hyMapEq : e (y', yLast) = (y', 0) := by
      calc
        e (y', yLast) = e1 (y', yLast) := by
          simp [e]
        _ = (y', 0) := hyMapEq1
    have hyTarget : (y', 0) ∈ e.target := by
      have hyTarget' : e (y', yLast) ∈ e.target := e.map_source hySource
      simpa [hyMapEq] using hyTarget'
    let U : Set (Fin n → ℝ) := {x' | (x', (0 : ℝ)) ∈ e.target}
    let V : Set (Fin (n + 1) → ℝ) := {x | (Fin.init x, x (Fin.last n)) ∈ e.source}
    let g : (Fin n → ℝ) → ℝ := fun x' => (e.symm (x', 0)).2
    have hUopen : IsOpen U := by
      have hEmbedCont : Continuous (fun x' : Fin n → ℝ => (x', (0 : ℝ))) := by
        exact contDiff_prodMk_left (𝕜 := ℝ) (n := (1 : WithTop ℕ∞)) (f₀ := (0 : ℝ)) |>.continuous
      simpa [U] using e.open_target.preimage hEmbedCont
    have hyU : y' ∈ U := by
      simpa [U] using hyTarget
    have hVopen : IsOpen V := by
      have hInitLastCont : Continuous (fun x : Fin (n + 1) → ℝ => (Fin.init x, x (Fin.last n))) := by
        exact (continuous_id.finInit).prodMk (continuous_apply (Fin.last n))
      simpa [V] using e.open_source.preimage hInitLastCont
    have hyV : Fin.snoc y' yLast ∈ V := by
      simpa [V] using hySource
    have hVE : V ⊆ E := by
      intro x hxV
      have hxSource : (Fin.init x, x (Fin.last n)) ∈ e.source := by
        simpa [V] using hxV
      have hxSourceAnd :
          (Fin.init x, x (Fin.last n)) ∈ e1.source ∩
            {p | ContDiffAt ℝ 1 e1 p ∧ ContDiffAt ℝ 1 e1.symm (e1 p)} := by
        simpa [e, OpenPartialHomeomorph.restrContDiff_source] using hxSource
      have hxSource1 : (Fin.init x, x (Fin.last n)) ∈ e1.source := hxSourceAnd.1
      have hxSource0And : (Fin.init x, x (Fin.last n)) ∈ e0.source ∩ s := by
        simpa [e1, OpenPartialHomeomorph.restrOpen_source] using hxSource1
      have hxInS : (Fin.init x, x (Fin.last n)) ∈ s := hxSource0And.2
      have hxInE : Fin.snoc (Fin.init x) (x (Fin.last n)) ∈ E := by
        simpa [s] using hxInS
      simpa using (show x ∈ E by simpa using hxInE)
    have hySymm : e.symm (y', 0) = (y', yLast) := by
      have hyLeft : e.symm (e (y', yLast)) = (y', yLast) := e.left_inv hySource
      simpa [hyMapEq] using hyLeft
    have hgy : g y' = yLast := by
      simpa [g] using congrArg Prod.snd hySymm
    have hGraphEq :
        {x | x ∈ V ∧ f x = 0} = (fun x' => Fin.snoc x' (g x')) '' U := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxV, hxZero⟩
        have hxSource : (Fin.init x, x (Fin.last n)) ∈ e.source := by
          simpa [V] using hxV
        have hxMapEq : e (Fin.init x, x (Fin.last n)) = (Fin.init x, 0) := by
          calc
            e (Fin.init x, x (Fin.last n))
                = e0 (Fin.init x, x (Fin.last n)) := by
                  simp [e, e1]
            _ = (Fin.init x, f (Fin.snoc (Fin.init x) (x (Fin.last n)))) := hApplyE0 _
            _ = (Fin.init x, f x) := by
              simp [Fin.snoc_init_self]
            _ = (Fin.init x, 0) := by
              simp [hxZero]
        have hxTarget : (Fin.init x, 0) ∈ e.target := by
          have hxTarget' : e (Fin.init x, x (Fin.last n)) ∈ e.target := e.map_source hxSource
          simpa [hxMapEq] using hxTarget'
        have hxU : Fin.init x ∈ U := by
          simpa [U] using hxTarget
        have hSymmEq : e.symm (Fin.init x, 0) = (Fin.init x, x (Fin.last n)) := by
          have hleft : e.symm (e (Fin.init x, x (Fin.last n))) = (Fin.init x, x (Fin.last n)) :=
            e.left_inv hxSource
          simpa [hxMapEq] using hleft
        have hgInit : g (Fin.init x) = x (Fin.last n) := by
          simpa [g] using congrArg Prod.snd hSymmEq
        refine ⟨Fin.init x, hxU, ?_⟩
        calc
          Fin.snoc (Fin.init x) (g (Fin.init x)) = Fin.snoc (Fin.init x) (x (Fin.last n)) := by
            simp [hgInit]
          _ = x := by
            simpa using (Fin.snoc_init_self x)
      · rintro ⟨x', hxU, rfl⟩
        have hxTarget : (x', 0) ∈ e.target := by
          simpa [U] using hxU
        have hxSource : e.symm (x', 0) ∈ e.source := e.map_target hxTarget
        have hxRight : e (e.symm (x', 0)) = (x', 0) := e.right_inv hxTarget
        have hPairEq :
            ((e.symm (x', 0)).1, f (Fin.snoc (e.symm (x', 0)).1 (e.symm (x', 0)).2)) = (x', 0) := by
          calc
            ((e.symm (x', 0)).1, f (Fin.snoc (e.symm (x', 0)).1 (e.symm (x', 0)).2))
                = e0 (e.symm (x', 0)) := by
                  simpa using (hApplyE0 (e.symm (x', 0))).symm
            _ = e (e.symm (x', 0)) := by
              simp [e, e1]
            _ = (x', 0) := hxRight
        have hPairEq' :
            (e.symm (x', 0)).1 = x' ∧ f (Fin.snoc (e.symm (x', 0)).1 (e.symm (x', 0)).2) = 0 := by
          simpa [Prod.mk.injEq] using hPairEq
        have hxFirst : (e.symm (x', 0)).1 = x' := hPairEq'.1
        have hxZero : f (Fin.snoc (e.symm (x', 0)).1 (e.symm (x', 0)).2) = 0 :=
          hPairEq'.2
        have hSymmEq : e.symm (x', 0) = (x', g x') := by
          apply Prod.ext
          · exact hxFirst
          · simp [g]
        have hxV : Fin.snoc x' (g x') ∈ V := by
          have hxSource' : (x', g x') ∈ e.source := by
            simpa [hSymmEq] using hxSource
          simpa [V] using hxSource'
        have hxZero' : f (Fin.snoc x' (g x')) = 0 := by
          simpa [hSymmEq] using hxZero
        exact And.intro hxV hxZero'
    have hSymmContDiffOn :
        ContDiffOn ℝ 1 e.symm e.target := by
      simpa [e] using
        (OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) (f := e1)
          (n := (1 : WithTop ℕ∞)) hOneNeTop)
    have hEmbedContDiffOn :
        ContDiffOn ℝ 1 (fun x' : Fin n → ℝ => (x', (0 : ℝ))) U := by
      exact
        (contDiff_prodMk_left (𝕜 := ℝ) (n := (1 : WithTop ℕ∞)) (f₀ := (0 : ℝ))).contDiffOn
    have hEmbedMapsTo : Set.MapsTo (fun x' : Fin n → ℝ => (x', (0 : ℝ))) U e.target := by
      intro x' hxU'
      simpa [U] using hxU'
    have hContDiffPair :
        ContDiffOn ℝ 1 (fun x' : Fin n → ℝ => e.symm (x', (0 : ℝ))) U := by
      simpa [Function.comp] using hSymmContDiffOn.comp hEmbedContDiffOn hEmbedMapsTo
    have hContDiff : ContDiffOn ℝ 1 g U := by
      simpa [g] using hContDiffPair.snd
    have hConstraintOnU : ∀ x' ∈ U, f (Fin.snoc x' (g x')) = 0 := by
      intro x' hxU'
      have hxGraph : Fin.snoc x' (g x') ∈ {x | x ∈ V ∧ f x = 0} := by
        rw [hGraphEq]
        exact ⟨x', hxU', rfl⟩
      exact hxGraph.2
    have hGraphPointInVOnU : ∀ x' ∈ U, Fin.snoc x' (g x') ∈ V := by
      intro x' hxU'
      have hxGraph : Fin.snoc x' (g x') ∈ {x | x ∈ V ∧ f x = 0} := by
        rw [hGraphEq]
        exact ⟨x', hxU', rfl⟩
      exact hxGraph.1
    let H : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun x' => Fin.snoc x' (g x')
    have hHMapsToE : Set.MapsTo H U E := by
      intro x' hxU'
      exact hVE (hGraphPointInVOnU x' hxU')
    have hHContinuousOnU : ContinuousOn H U := by
      have hIdCont : ContinuousOn (fun x' : Fin n → ℝ => x') U := continuousOn_id
      have hgCont : ContinuousOn g U := hContDiff.continuousOn
      simpa [H] using hIdCont.finSnoc hgCont
    let P : (Fin (n + 1) → ℝ) → ℝ := fun z => partialDerivWithin f E z (Fin.last n)
    have hPContinuousOnE : ContinuousOn P E := by
      have hcontApply :
          ContinuousOn
            (fun p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
              (fderivWithin ℝ f E p.1) p.2)
            (E ×ˢ Set.univ) := by
        exact hf.continuousOn_fderivWithin_apply hEopen.uniqueDiffOn (by norm_num)
      have hpairCont :
          ContinuousOn
            (fun z : Fin (n + 1) → ℝ =>
              (z, (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ)))
            E := by
        exact continuousOn_id.prodMk continuousOn_const
      have hpairMaps :
          Set.MapsTo
            (fun z : Fin (n + 1) → ℝ =>
              (z, (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ)))
            E (E ×ˢ Set.univ) := by
        intro z hz
        exact ⟨hz, by simp⟩
      simpa [P, partialDerivWithin] using hcontApply.comp hpairCont hpairMaps
    let D : (Fin n → ℝ) → ℝ := fun x' => P (H x')
    have hDContinuousWithinAt : ContinuousWithinAt D U y' := by
      have hyHE : H y' ∈ E := hHMapsToE hyU
      have hPContWithin : ContinuousWithinAt P E (H y') := hPContinuousOnE.continuousWithinAt hyHE
      have hHContWithin : ContinuousWithinAt H U y' := hHContinuousOnU.continuousWithinAt hyU
      exact hPContWithin.comp hHContWithin hHMapsToE
    have hDyNonzero : D y' ≠ 0 := by
      simpa [D, H, P, hgy] using hpartial
    let T : Set ℝ := {r | r ≠ 0}
    have hTopen : IsOpen T := by
      simpa [T] using (isOpen_ne : IsOpen ({r : ℝ | r ≠ (0 : ℝ)}))
    have hDpreimageMem : D ⁻¹' T ∈ nhdsWithin y' U := by
      exact hDContinuousWithinAt (hTopen.mem_nhds hDyNonzero)
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hDpreimageMem with ⟨N, hNnhds, hNsub⟩
    rcases mem_nhds_iff.mp hNnhds with ⟨O, hOsubN, hOopen, hyO⟩
    let U1 : Set (Fin n → ℝ) := O ∩ U
    have hU1open : IsOpen U1 := hOopen.inter hUopen
    have hyU1 : y' ∈ U1 := by
      exact ⟨hyO, hyU⟩
    have hU1subU : U1 ⊆ U := by
      intro x hx
      exact hx.2
    have hDenomNonzeroOnU1 :
        ∀ x' ∈ U1, partialDerivWithin f E (H x') (Fin.last n) ≠ 0 := by
      intro x' hxU1
      have hxN : x' ∈ N := hOsubN hxU1.1
      have hxPre : x' ∈ D ⁻¹' T := hNsub ⟨hxN, hxU1.2⟩
      simpa [D, P, T] using hxPre
    let V1 : Set (Fin (n + 1) → ℝ) := {x | x ∈ V ∧ Fin.init x ∈ U1}
    have hV1open : IsOpen V1 := by
      have hInitCont : Continuous (fun x : Fin (n + 1) → ℝ => Fin.init x) :=
        continuous_id.finInit
      exact hVopen.inter (hU1open.preimage hInitCont)
    have hyV1 : Fin.snoc y' yLast ∈ V1 := by
      refine ⟨hyV, ?_⟩
      simpa using hyU1
    have hV1E : V1 ⊆ E := by
      intro x hxV1
      exact hVE hxV1.1
    have hGraphEq1 :
        {x | x ∈ V1 ∧ f x = 0} = (fun x' => Fin.snoc x' (g x')) '' U1 := by
      ext x
      constructor
      · intro hx
        have hxVZero : x ∈ V ∧ f x = 0 := ⟨hx.1.1, hx.2⟩
        have hxGraph : x ∈ {x | x ∈ V ∧ f x = 0} := hxVZero
        rw [hGraphEq] at hxGraph
        rcases hxGraph with ⟨x', -, rfl⟩
        refine ⟨x', ?_, rfl⟩
        simpa using hx.1.2
      · rintro ⟨x', hxU1, rfl⟩
        have hxU : x' ∈ U := hU1subU hxU1
        have hxVZero : Fin.snoc x' (g x') ∈ V ∧ f (Fin.snoc x' (g x')) = 0 := by
          exact ⟨hGraphPointInVOnU x' hxU, hConstraintOnU x' hxU⟩
        exact ⟨⟨hxVZero.1, by simpa using hxU1⟩, hxVZero.2⟩
    have hContDiff1 : ContDiffOn ℝ 1 g U1 := hContDiff.mono hU1subU
    have hConstraintOnU1 : ∀ x' ∈ U1, f (H x') = 0 := by
      intro x' hxU1
      have hxGraph : H x' ∈ {x | x ∈ V1 ∧ f x = 0} := by
        rw [hGraphEq1]
        refine ⟨x', hxU1, ?_⟩
        simp [H]
      exact hxGraph.2
    have hHMapsToE1 : Set.MapsTo H U1 E := by
      intro x' hxU1
      have hxGraph : H x' ∈ {x | x ∈ V1 ∧ f x = 0} := by
        rw [hGraphEq1]
        refine ⟨x', hxU1, ?_⟩
        simp [H]
      exact hV1E hxGraph.1
    have hLinearIdentityOnU1 :
        ∀ x' ∈ U1, ∀ j : Fin n,
          partialDerivWithin f E (H x') (Fin.castSucc j) +
              partialDerivWithin f E (H x') (Fin.last n) * partialDerivWithin g U1 x' j =
            0 := by
      intro x' hxU1 j
      have hxHE : H x' ∈ E := hHMapsToE1 hxU1
      let eJ : Fin n → ℝ := (Pi.single j (1 : ℝ) : Fin n → ℝ)
      let eCastSucc : Fin (n + 1) → ℝ :=
        (Pi.single (Fin.castSucc j) (1 : ℝ) : Fin (n + 1) → ℝ)
      let eLast : Fin (n + 1) → ℝ :=
        (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ)
      have hfDiffWithin :
          DifferentiableWithinAt ℝ f E (H x') := by
        exact (hf.contDiffWithinAt hxHE).differentiableWithinAt (by norm_num)
      have hDerivF :
          HasFDerivWithinAt f (fderivWithin ℝ f E (H x')) E (H x') :=
        hfDiffWithin.hasFDerivWithinAt
      have hgDiffWithin :
          DifferentiableWithinAt ℝ g U1 x' := by
        exact (hContDiff1.contDiffWithinAt hxU1).differentiableWithinAt (by norm_num)
      let DG1 : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
        ContinuousLinearMap.pi (fun i : Fin (n + 1) =>
          Fin.lastCases (fderivWithin ℝ g U1 x') (fun k : Fin n => ContinuousLinearMap.proj k) i)
      have hDerivH : HasFDerivWithinAt H DG1 U1 x' := by
        refine hasFDerivWithinAt_pi.2 ?_
        intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [H, DG1] using hgDiffWithin.hasFDerivWithinAt
        · intro k
          simpa [H, DG1, Fin.snoc_castSucc] using
            (hasFDerivWithinAt_apply (i := k) (f := x') (s' := U1))
      have hDerivComp :
          HasFDerivWithinAt (fun z : Fin n → ℝ => f (H z))
            ((fderivWithin ℝ f E (H x')).comp DG1) U1 x' := by
        exact hDerivF.comp x' hDerivH hHMapsToE1
      have hConstraintEvent :
          (fun z : Fin n → ℝ => f (H z)) =ᶠ[nhdsWithin x' U1] (fun _ => (0 : ℝ)) := by
        have hMem : {z : Fin n → ℝ | f (H z) = 0} ∈ nhdsWithin x' U1 := by
          refine Filter.mem_of_superset self_mem_nhdsWithin ?_
          intro z hz
          exact hConstraintOnU1 z hz
        simpa [Filter.EventuallyEq, Filter.Eventually] using hMem
      have hDerivZeroConst :
          HasFDerivWithinAt (fun _ : Fin n → ℝ => (0 : ℝ))
            (0 : (Fin n → ℝ) →L[ℝ] ℝ) U1 x' := by
        simpa using (hasFDerivWithinAt_const (c := (0 : ℝ)) (x := x') (s := U1))
      have hDerivZero :
          HasFDerivWithinAt (fun z : Fin n → ℝ => f (H z))
            (0 : (Fin n → ℝ) →L[ℝ] ℝ) U1 x' := by
        exact hDerivZeroConst.congr_of_eventuallyEq hConstraintEvent (by
          simpa [hConstraintOnU1 x' hxU1])
      have hDerivCompEq :
          fderivWithin ℝ (fun z : Fin n → ℝ => f (H z)) U1 x' =
            (fderivWithin ℝ f E (H x')).comp DG1 :=
        hDerivComp.fderivWithin (hU1open.uniqueDiffWithinAt hxU1)
      have hDerivZeroEq :
          fderivWithin ℝ (fun z : Fin n → ℝ => f (H z)) U1 x' =
            (0 : (Fin n → ℝ) →L[ℝ] ℝ) :=
        hDerivZero.fderivWithin (hU1open.uniqueDiffWithinAt hxU1)
      have hCompEqZero :
          ((fderivWithin ℝ f E (H x')).comp DG1) = (0 : (Fin n → ℝ) →L[ℝ] ℝ) := by
        exact hDerivCompEq.symm.trans hDerivZeroEq
      have hEvalComp :
          ((fderivWithin ℝ f E (H x')).comp DG1) eJ = 0 := by
        simpa [eJ] using congrArg (fun L => L eJ) hCompEqZero
      have hDG1Apply :
          DG1 eJ = Fin.snoc eJ (partialDerivWithin g U1 x' j) := by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · simp [DG1, eJ, partialDerivWithin]
        · intro k
          simp [DG1, eJ]
      have hEvalSnoc :
          (fderivWithin ℝ f E (H x')) (Fin.snoc eJ (partialDerivWithin g U1 x' j)) = 0 := by
        simpa [ContinuousLinearMap.comp_apply, hDG1Apply] using hEvalComp
      have hSnocDecomp :
          Fin.snoc eJ (partialDerivWithin g U1 x' j) =
            eCastSucc + (partialDerivWithin g U1 x' j) • eLast := by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last, eCastSucc, eLast, Fin.castSucc_ne_last]
        · intro k
          by_cases hk : k = j
          · subst hk
            simp [Fin.snoc_castSucc, eJ, eCastSucc, eLast, Fin.castSucc_ne_last]
          · have hkCast : (Fin.castSucc k : Fin (n + 1)) ≠ Fin.castSucc j := by
              exact (Fin.castSucc_injective n).ne hk
            simp [Fin.snoc_castSucc, eJ, eCastSucc, eLast, hk, hkCast, Fin.castSucc_ne_last]
      have hEvalDecomp :
          (fderivWithin ℝ f E (H x')) (eCastSucc + (partialDerivWithin g U1 x' j) • eLast) = 0 := by
        simpa [hSnocDecomp] using hEvalSnoc
      simpa [partialDerivWithin, eJ, eCastSucc, eLast, map_add, map_smul, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc]
        using hEvalDecomp
    have hQuotient1 :
        ∀ x' ∈ U1, ∀ j : Fin n,
          partialDerivWithin g U1 x' j =
            -(
              partialDerivWithin f E (Fin.snoc x' (g x')) (Fin.castSucc j) /
                partialDerivWithin f E (Fin.snoc x' (g x')) (Fin.last n)
            ) := by
      intro x' hxU1 j
      have hLinear :
          partialDerivWithin f E (H x') (Fin.castSucc j) +
              partialDerivWithin f E (H x') (Fin.last n) * partialDerivWithin g U1 x' j =
            0 :=
        hLinearIdentityOnU1 x' hxU1 j
      have hDenom : partialDerivWithin f E (H x') (Fin.last n) ≠ 0 :=
        hDenomNonzeroOnU1 x' hxU1
      have hMul :
          partialDerivWithin f E (H x') (Fin.last n) * partialDerivWithin g U1 x' j =
            -partialDerivWithin f E (H x') (Fin.castSucc j) := by
        linarith [hLinear]
      have hDiv :
          partialDerivWithin g U1 x' j =
            (-partialDerivWithin f E (H x') (Fin.castSucc j)) /
              partialDerivWithin f E (H x') (Fin.last n) := by
        apply (eq_div_iff hDenom).2
        calc
          partialDerivWithin g U1 x' j * partialDerivWithin f E (H x') (Fin.last n)
              = partialDerivWithin f E (H x') (Fin.last n) * partialDerivWithin g U1 x' j := by
                ring
          _ = -partialDerivWithin f E (H x') (Fin.castSucc j) := hMul
      simpa [H, neg_div] using hDiv
    refine ⟨U1, hU1open, hyU1, V1, hV1open, hyV1, hV1E, g, hgy, hGraphEq1, hContDiff1, hQuotient1⟩
  rcases hMainData with ⟨U, hUopen, hyU, V, hVopen, hyV, hVE, g, hgy, hgraphEq, hContDiff, hQuotient⟩
  refine ⟨U, hUopen, hyU, V, hVopen, hyV, hVE, g, ?_, ?_, ?_⟩
  · exact ⟨hgy, hgraphEq⟩
  · exact ⟨hContDiff, hQuotient⟩
  · intro g2 hg2 x hx
    exact huniqGraph hgraphEq hg2.2 x hx

/-- Helper for Proposition 6.17: turn the pointwise constraint on `V` into an eventual
equality with the constant zero function within `V`. -/
lemma helperForProposition_6_17_constraintEventuallyEqZero
    {m : ℕ}
    {V : Set (Fin m → ℝ)}
    {f : (Fin (m + 1) → ℝ) → ℝ}
    {g : (Fin m → ℝ) → ℝ}
    {x : Fin m → ℝ}
    (hconstraint : ∀ z ∈ V, f (Fin.snoc z (g z)) = 0) :
    (fun z : Fin m → ℝ => f (Fin.snoc z (g z))) =ᶠ[nhdsWithin x V] (fun _ => (0 : ℝ)) := by
  have hMem : {z : Fin m → ℝ | f (Fin.snoc z (g z)) = 0} ∈ nhdsWithin x V := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro z hz
    exact hconstraint z hz
  simpa [Filter.EventuallyEq, Filter.Eventually] using hMem

/-- Helper for Proposition 6.17: the derivative of the map `z ↦ (z, g z)` within `V`. -/
noncomputable def helperForProposition_6_17_DGx
    {m : ℕ}
    (g : (Fin m → ℝ) → ℝ)
    (V : Set (Fin m → ℝ))
    (x : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin (m + 1) =>
    Fin.lastCases (fderivWithin ℝ g V x) (fun k : Fin m => ContinuousLinearMap.proj k) i)

/-- Helper for Proposition 6.17: chain-rule derivative for the constrained composition
`z ↦ f (z, g z)` within `V`. -/
lemma helperForProposition_6_17_compositionHasFDerivWithinAt
    {m : ℕ}
    {U : Set (Fin (m + 1) → ℝ)}
    {V : Set (Fin m → ℝ)}
    {f : (Fin (m + 1) → ℝ) → ℝ}
    {g : (Fin m → ℝ) → ℝ}
    {x : Fin m → ℝ}
    (hx : x ∈ V)
    (hf : DifferentiableOn ℝ f U)
    (hg : DifferentiableOn ℝ g V)
    (hgraph : ∀ z ∈ V, Fin.snoc z (g z) ∈ U) :
    HasFDerivWithinAt (fun z : Fin m → ℝ => f (Fin.snoc z (g z)))
      ((fderivWithin ℝ f U (Fin.snoc x (g x))).comp (helperForProposition_6_17_DGx g V x)) V x := by
  have hfDiffWithin : DifferentiableWithinAt ℝ f U (Fin.snoc x (g x)) := by
    exact hf (Fin.snoc x (g x)) (hgraph x hx)
  have hDerivF :
      HasFDerivWithinAt f (fderivWithin ℝ f U (Fin.snoc x (g x))) U (Fin.snoc x (g x)) :=
    hfDiffWithin.hasFDerivWithinAt
  have hgDiffWithin : DifferentiableWithinAt ℝ g V x := by
    exact hg x hx
  have hDerivSnoc :
      HasFDerivWithinAt (fun z : Fin m → ℝ => Fin.snoc z (g z))
        (helperForProposition_6_17_DGx g V x) V x := by
    refine hasFDerivWithinAt_pi.2 ?_
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [helperForProposition_6_17_DGx] using hgDiffWithin.hasFDerivWithinAt
    · intro k
      simpa [helperForProposition_6_17_DGx, Fin.snoc_castSucc] using
        (hasFDerivWithinAt_apply (i := k) (f := x) (s' := V))
  have hMapsto : Set.MapsTo (fun z : Fin m → ℝ => Fin.snoc z (g z)) V U := by
    intro z hz
    exact hgraph z hz
  exact hDerivF.comp x hDerivSnoc hMapsto

/-- Helper for Proposition 6.17: evaluate `DGx` on the `j`th basis vector. -/
lemma helperForProposition_6_17_DGxApplyBasis
    {m : ℕ}
    {V : Set (Fin m → ℝ)}
    {g : (Fin m → ℝ) → ℝ}
    {x : Fin m → ℝ}
    (j : Fin m) :
    helperForProposition_6_17_DGx g V x (Pi.single j (1 : ℝ)) =
      Fin.snoc (Pi.single j (1 : ℝ)) (partialDerivWithin g V x j) := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [helperForProposition_6_17_DGx, partialDerivWithin]
  · intro k
    simp [helperForProposition_6_17_DGx]

/-- Helper for Proposition 6.17: decompose `Fin.snoc` of a basis direction into the
`castSucc` and `last` coordinate basis vectors. -/
lemma helperForProposition_6_17_snocBasisDecomposition
    {m : ℕ}
    {V : Set (Fin m → ℝ)}
    {g : (Fin m → ℝ) → ℝ}
    {x : Fin m → ℝ}
    (j : Fin m) :
    Fin.snoc (Pi.single j (1 : ℝ)) (partialDerivWithin g V x j) =
      ((Pi.single (Fin.castSucc j) (1 : ℝ) : Fin (m + 1) → ℝ)) +
        (partialDerivWithin g V x j) •
          (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last, Fin.castSucc_ne_last]
  · intro k
    by_cases hk : k = j
    · subst hk
      simp [Fin.snoc_castSucc, Fin.castSucc_ne_last]
    · have hkCast : (Fin.castSucc k : Fin (m + 1)) ≠ Fin.castSucc j := by
        exact (Fin.castSucc_injective m).ne hk
      simp [Fin.snoc_castSucc, hk, hkCast, Fin.castSucc_ne_last]

/-- Helper for Proposition 6.17: linear identity obtained by differentiating the
constraint `f (x, g x) = 0` within `V`. -/
lemma helperForProposition_6_17_linearIdentity
    {m : ℕ}
    {U : Set (Fin (m + 1) → ℝ)}
    {V : Set (Fin m → ℝ)}
    {f : (Fin (m + 1) → ℝ) → ℝ}
    {g : (Fin m → ℝ) → ℝ}
    (hVopen : IsOpen V)
    (hf : DifferentiableOn ℝ f U)
    (hg : DifferentiableOn ℝ g V)
    (hgraph : ∀ z ∈ V, Fin.snoc z (g z) ∈ U)
    (hconstraint : ∀ z ∈ V, f (Fin.snoc z (g z)) = 0)
    (j : Fin m)
    (x : Fin m → ℝ)
    (hx : x ∈ V) :
    partialDerivWithin f U (Fin.snoc x (g x)) (Fin.castSucc j) +
        partialDerivWithin f U (Fin.snoc x (g x)) (Fin.last m) * partialDerivWithin g V x j =
      0 := by
  have hDerivComp :
      HasFDerivWithinAt (fun z : Fin m → ℝ => f (Fin.snoc z (g z)))
        ((fderivWithin ℝ f U (Fin.snoc x (g x))).comp (helperForProposition_6_17_DGx g V x)) V x :=
    helperForProposition_6_17_compositionHasFDerivWithinAt hx hf hg hgraph
  have hConstraintEvent :
      (fun z : Fin m → ℝ => f (Fin.snoc z (g z))) =ᶠ[nhdsWithin x V] (fun _ => (0 : ℝ)) :=
    helperForProposition_6_17_constraintEventuallyEqZero hconstraint
  have hDerivZeroConst :
      HasFDerivWithinAt (fun _ : Fin m → ℝ => (0 : ℝ)) (0 : (Fin m → ℝ) →L[ℝ] ℝ) V x := by
    simpa using (hasFDerivWithinAt_const (c := (0 : ℝ)) (x := x) (s := V))
  have hDerivZero :
      HasFDerivWithinAt (fun z : Fin m → ℝ => f (Fin.snoc z (g z)))
        (0 : (Fin m → ℝ) →L[ℝ] ℝ) V x := by
    exact hDerivZeroConst.congr_of_eventuallyEq hConstraintEvent (by simpa [hconstraint x hx])
  have hDerivCompEq :
      fderivWithin ℝ (fun z : Fin m → ℝ => f (Fin.snoc z (g z))) V x =
        (fderivWithin ℝ f U (Fin.snoc x (g x))).comp (helperForProposition_6_17_DGx g V x) :=
    hDerivComp.fderivWithin (hVopen.uniqueDiffWithinAt hx)
  have hDerivZeroEq :
      fderivWithin ℝ (fun z : Fin m → ℝ => f (Fin.snoc z (g z))) V x =
        (0 : (Fin m → ℝ) →L[ℝ] ℝ) :=
    hDerivZero.fderivWithin (hVopen.uniqueDiffWithinAt hx)
  have hCompEqZero :
      (fderivWithin ℝ f U (Fin.snoc x (g x))).comp (helperForProposition_6_17_DGx g V x) =
        (0 : (Fin m → ℝ) →L[ℝ] ℝ) := by
    exact hDerivCompEq.symm.trans hDerivZeroEq
  have hEvalComp :
      ((fderivWithin ℝ f U (Fin.snoc x (g x))).comp (helperForProposition_6_17_DGx g V x))
          (Pi.single j (1 : ℝ)) =
        0 := by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ))) hCompEqZero
  have hDGxApply :
      helperForProposition_6_17_DGx g V x (Pi.single j (1 : ℝ)) =
        Fin.snoc (Pi.single j (1 : ℝ)) (partialDerivWithin g V x j) :=
    helperForProposition_6_17_DGxApplyBasis j
  have hEvalSnoc :
      (fderivWithin ℝ f U (Fin.snoc x (g x)))
          (Fin.snoc (Pi.single j (1 : ℝ)) (partialDerivWithin g V x j)) =
        0 := by
    simpa [ContinuousLinearMap.comp_apply, hDGxApply] using hEvalComp
  have hSnocDecomp :
      Fin.snoc (Pi.single j (1 : ℝ)) (partialDerivWithin g V x j) =
        ((Pi.single (Fin.castSucc j) (1 : ℝ) : Fin (m + 1) → ℝ)) +
          (partialDerivWithin g V x j) •
            (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ) :=
    helperForProposition_6_17_snocBasisDecomposition j
  have hEvalDecomp :
      (fderivWithin ℝ f U (Fin.snoc x (g x)))
          (((Pi.single (Fin.castSucc j) (1 : ℝ) : Fin (m + 1) → ℝ)) +
            (partialDerivWithin g V x j) •
              (Pi.single (Fin.last m) (1 : ℝ) : Fin (m + 1) → ℝ)) =
        0 := by
    simpa [hSnocDecomp] using hEvalSnoc
  simpa [partialDerivWithin, map_add, map_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hEvalDecomp

/-- Helper for Proposition 6.17: solve `A + B*C = 0` for `C` when `B ≠ 0`. -/
lemma helperForProposition_6_17_solveForPartialG
    (A B C : ℝ)
    (hLinear : A + B * C = 0)
    (hB : B ≠ 0) :
    C = -A / B := by
  have hMul : B * C = -A := by
    linarith [hLinear]
  apply (eq_div_iff hB).2
  calc
    C * B = B * C := by ring
    _ = -A := hMul

/-- Proposition 6.17 (Implicit differentiation for an implicit constraint):
in ambient coordinates with `m` free variables and one dependent coordinate
(`book's n = m + 1`), if `f : ℝ^(m+1) → ℝ` and `g : ℝ^m → ℝ` are differentiable on
open sets `U` and `V`, `a ∈ U` satisfies `f a = 0` and nonvanishing last partial
derivative at `a`, and `f (x, g x) = 0` for all `x ∈ V` with `(x, g x) ∈ U`, then for
each coordinate `j` and each `x ∈ V` one has
`∂ⱼ f(x, g x) + ∂ₘ₊₁ f(x, g x) * ∂ⱼ g(x) = 0`; equivalently,
`∂ⱼ g(x) = -(∂ⱼ f(x, g x)) / (∂ₘ₊₁ f(x, g x))` whenever `∂ₘ₊₁ f(x, g x) ≠ 0`. -/
theorem implicitDifferentiationForImplicitConstraint
    (m : ℕ)
    (U : Set (Fin (m + 1) → ℝ))
    (f : (Fin (m + 1) → ℝ) → ℝ)
    (V : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → ℝ)
    (hf : DifferentiableOn ℝ f U)
    (hVopen : IsOpen V)
    (hg : DifferentiableOn ℝ g V)
    (hgraph : ∀ x ∈ V, Fin.snoc x (g x) ∈ U)
    (hconstraint : ∀ x ∈ V, f (Fin.snoc x (g x)) = 0) :
    (∀ j : Fin m, ∀ x ∈ V,
      partialDerivWithin f U (Fin.snoc x (g x)) (Fin.castSucc j) +
          partialDerivWithin f U (Fin.snoc x (g x)) (Fin.last m) *
            partialDerivWithin g V x j =
        0) ∧
      ∀ j : Fin m, ∀ x ∈ V,
        partialDerivWithin f U (Fin.snoc x (g x)) (Fin.last m) ≠ 0 →
          partialDerivWithin g V x j =
            -(partialDerivWithin f U (Fin.snoc x (g x)) (Fin.castSucc j)) /
              partialDerivWithin f U (Fin.snoc x (g x)) (Fin.last m) := by
  constructor
  · intro j x hx
    exact helperForProposition_6_17_linearIdentity hVopen hf hg hgraph hconstraint j x hx
  · intro j x hx hDenom
    have hLinear :
        partialDerivWithin f U (Fin.snoc x (g x)) (Fin.castSucc j) +
            partialDerivWithin f U (Fin.snoc x (g x)) (Fin.last m) * partialDerivWithin g V x j =
          0 :=
      helperForProposition_6_17_linearIdentity hVopen hf hg hgraph hconstraint j x hx
    exact helperForProposition_6_17_solveForPartialG
      (partialDerivWithin f U (Fin.snoc x (g x)) (Fin.castSucc j))
      (partialDerivWithin f U (Fin.snoc x (g x)) (Fin.last m))
      (partialDerivWithin g V x j)
      hLinear hDenom

/-- Definition 6.20 (Regular level set as a local graph): with ambient coordinates
`ℝ^(m+1)` (so the book's ambient dimension parameter is `n = m + 1`), let
`f : ℝ^(m+1) → ℝ` be continuously differentiable and let `x₀` satisfy `f x₀ = 0`.
If some coordinate partial derivative of `f` at `x₀` is nonzero, then locally
near `x₀` the zero level set `{x | f x = 0}` is the graph of a differentiable
function `g : ℝ^m → ℝ`, matching the book's `ℝ^(n-1)` parameter space. -/
theorem regularLevelSetAsLocalGraph
    (m : ℕ)
    (f : (Fin (m + 1) → ℝ) → ℝ)
    (x₀ : Fin (m + 1) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hx₀ : f x₀ = 0) :
    (∃ j : Fin (m + 1), partialDerivWithin f Set.univ x₀ j ≠ 0) →
      ∃ j : Fin (m + 1),
        partialDerivWithin f Set.univ x₀ j ≠ 0 ∧
          ∃ U : Set (Fin m → ℝ),
            IsOpen U ∧
              ∃ W : Set (Fin (m + 1) → ℝ),
                IsOpen W ∧ x₀ ∈ W ∧
                  ∃ g : (Fin m → ℝ) → ℝ,
                    DifferentiableOn ℝ g U ∧
                      {x | x ∈ W ∧ f x = 0} = (fun x' => j.insertNth (g x') x') '' U := by
  intro hReg
  rcases hReg with ⟨j, hj⟩
  have hOneLe : (1 : WithTop ℕ∞) ≤ 1 := le_rfl
  let Φ : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) :=
    fun y =>
      Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) j (y (Fin.last m))
        (fun i => y (Fin.castSucc i))
  let Ψ : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) :=
    fun x => Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) (j.removeNth x) (x j)
  let fTilde : (Fin (m + 1) → ℝ) → ℝ := fun y => f (Φ y)
  let y0 : Fin (m + 1) → ℝ :=
    Fin.snoc (α := fun _ : Fin (m + 1) => ℝ) (j.removeNth x₀) (x₀ j)
  have hΦΨ : ∀ x : Fin (m + 1) → ℝ, Φ (Ψ x) = x := by
    intro x
    simp [Φ, Ψ]
  have hΨΦ : ∀ y : Fin (m + 1) → ℝ, Ψ (Φ y) = y := by
    intro y
    ext i
    refine Fin.lastCases ?_ ?_ i
    · simp [Φ, Ψ]
    · intro k
      simp [Φ, Ψ, Fin.removeNth_apply]
  have hΦSnoc : ∀ x' : Fin m → ℝ, ∀ t : ℝ, Φ (Fin.snoc x' t) = j.insertNth t x' := by
    intro x' t
    simp [Φ]
  have hΦContDiff : ContDiff ℝ 1 Φ := by
    refine contDiff_pi.2 ?_
    intro i
    refine j.succAboveCases ?_ ?_ i
    · simpa [Φ] using
        (contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := (1 : WithTop ℕ∞)) (ι := Fin (m + 1))
          (Fin.last m))
    · intro k
      simpa [Φ, Fin.insertNth_apply_succAbove] using
        (contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := (1 : WithTop ℕ∞)) (ι := Fin (m + 1))
          (Fin.castSucc k))
  have hΦMapsUniv : Set.MapsTo Φ Set.univ Set.univ := by
    intro y hy
    simp
  have hfTilde : ContDiffOn ℝ 1 fTilde Set.univ := by
    simpa [fTilde] using (hf.contDiffOn.comp hΦContDiff.contDiffOn hΦMapsUniv)
  have hΦAty0 : Φ y0 = x₀ := by
    calc
      Φ y0 = Φ (Ψ x₀) := by simp [y0, Ψ]
      _ = x₀ := hΦΨ x₀
  have hyZero : fTilde y0 = 0 := by
    simpa [fTilde, hΦAty0] using hx₀
  let L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearMap.pi (fun i : Fin (m + 1) =>
      j.succAboveCases
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + 1)) (i := Fin.last m))
        (fun k : Fin m => ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + 1)) (i := Fin.castSucc k))
        i)
  have hΦDeriv : HasFDerivAt Φ L y0 := by
    refine hasFDerivAt_pi.2 ?_
    intro i
    refine j.succAboveCases ?_ ?_ i
    · simpa [Φ, L, Fin.insertNth_apply_same] using
        ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + 1)) (i := Fin.last m) :
          (Fin (m + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt)
    · intro k
      simpa [Φ, L, Fin.insertNth_apply_succAbove] using
        ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (m + 1)) (i := Fin.castSucc k) :
          (Fin (m + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt)
  have hfDiffAt : DifferentiableAt ℝ f x₀ := (hf.contDiffAt (x := x₀)).differentiableAt hOneLe
  have hfDerivAtX0 : HasFDerivAt f (fderiv ℝ f x₀) x₀ := hfDiffAt.hasFDerivAt
  have hfDerivAtΦy0 : HasFDerivAt f (fderiv ℝ f x₀) (Φ y0) := by
    simpa [hΦAty0] using hfDerivAtX0
  have hfTildeDeriv : HasFDerivAt fTilde ((fderiv ℝ f x₀).comp L) y0 := by
    have hComp : HasFDerivAt (f ∘ Φ) ((fderiv ℝ f x₀).comp L) y0 := hfDerivAtΦy0.comp y0 hΦDeriv
    simpa [fTilde, Function.comp] using hComp
  have hfTildeEq : fderiv ℝ fTilde y0 = ((fderiv ℝ f x₀).comp L) := hfTildeDeriv.fderiv
  have hLlast : L (Pi.single (Fin.last m) (1 : ℝ)) = Pi.single j 1 := by
    ext i
    refine j.succAboveCases ?_ ?_ i
    · simp [L]
    · intro k
      simp [L, Fin.succAbove_ne]
  have hPartialEq :
      partialDerivWithin fTilde Set.univ y0 (Fin.last m) = partialDerivWithin f Set.univ x₀ j := by
    calc
      partialDerivWithin fTilde Set.univ y0 (Fin.last m)
          = (fderivWithin ℝ fTilde Set.univ y0) (Pi.single (Fin.last m) 1) := by
              rfl
      _ = (fderiv ℝ fTilde y0) (Pi.single (Fin.last m) 1) := by
            simp [fderivWithin_univ]
      _ = (((fderiv ℝ f x₀).comp L) (Pi.single (Fin.last m) 1)) := by
            simp [hfTildeEq]
      _ = (fderiv ℝ f x₀) (Pi.single j 1) := by
            simp [ContinuousLinearMap.comp_apply, hLlast]
      _ = (fderivWithin ℝ f Set.univ x₀) (Pi.single j 1) := by
            simp [fderivWithin_univ]
      _ = partialDerivWithin f Set.univ x₀ j := by
            rfl
  have hPartialTilde :
      partialDerivWithin fTilde Set.univ y0 (Fin.last m) ≠ 0 := by
    rw [hPartialEq]
    exact hj
  have hyUniv : y0 ∈ (Set.univ : Set (Fin (m + 1) → ℝ)) := by
    simp
  have hIFT :=
    implicitFunctionTheorem m Set.univ fTilde (j.removeNth x₀) (x₀ j) isOpen_univ hfTilde hyUniv hyZero
      hPartialTilde
  rcases hIFT with ⟨U, hUopen, -, V, hVopen, hyV, -, g, hgA, hgB, -⟩
  have hGraphEqTilde : {y | y ∈ V ∧ fTilde y = 0} = (fun x' => Fin.snoc x' (g x')) '' U := hgA.2
  have hDiffOn : DifferentiableOn ℝ g U := hgB.1.differentiableOn hOneLe
  let W : Set (Fin (m + 1) → ℝ) := Ψ ⁻¹' V
  have hΨContDiff : ContDiff ℝ 1 Ψ := by
    refine contDiff_pi.2 ?_
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [Ψ, Fin.snoc_last] using
        (contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := (1 : WithTop ℕ∞)) (ι := Fin (m + 1)) j)
    · intro k
      simpa [Ψ, Fin.snoc_castSucc, Fin.removeNth_apply] using
        (contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := (1 : WithTop ℕ∞)) (ι := Fin (m + 1))
          (j.succAbove k))
  have hWopen : IsOpen W := by
    have hΨCont : Continuous Ψ := hΨContDiff.continuous
    simpa [W] using hVopen.preimage hΨCont
  have hx0W : x₀ ∈ W := by
    have hy0V : y0 ∈ V := by
      simpa [y0] using hyV
    simpa [W, y0, Ψ] using hy0V
  have hGraphEq : {x | x ∈ W ∧ f x = 0} = (fun x' => j.insertNth (g x') x') '' U := by
    ext x
    constructor
    · intro hx
      have hxW : x ∈ W := hx.1
      have hxZero : f x = 0 := hx.2
      have hΨxV : Ψ x ∈ V := by
        simpa [W] using hxW
      have hΨxZero : fTilde (Ψ x) = 0 := by
        simpa [fTilde, hΦΨ x] using hxZero
      have hΨxMem : Ψ x ∈ {y | y ∈ V ∧ fTilde y = 0} := And.intro hΨxV hΨxZero
      rw [hGraphEqTilde] at hΨxMem
      rcases hΨxMem with ⟨x', hxU, hsnocEq⟩
      refine ⟨x', hxU, ?_⟩
      have hCongr : Φ (Fin.snoc x' (g x')) = Φ (Ψ x) := congrArg Φ hsnocEq
      simpa [hΦSnoc x' (g x'), hΦΨ x] using hCongr
    · rintro ⟨x', hxU, rfl⟩
      have hyMem : Fin.snoc x' (g x') ∈ {y | y ∈ V ∧ fTilde y = 0} := by
        rw [hGraphEqTilde]
        exact ⟨x', hxU, rfl⟩
      have hyV' : Fin.snoc x' (g x') ∈ V := hyMem.1
      have hyZero' : fTilde (Fin.snoc x' (g x')) = 0 := hyMem.2
      have hΨEq : Ψ (j.insertNth (g x') x') = Fin.snoc x' (g x') := by
        calc
          Ψ (j.insertNth (g x') x') = Ψ (Φ (Fin.snoc x' (g x'))) := by
            simpa [hΦSnoc x' (g x')]
          _ = Fin.snoc x' (g x') := hΨΦ (Fin.snoc x' (g x'))
      have hxW : j.insertNth (g x') x' ∈ W := by
        simpa [W, hΨEq] using hyV'
      have hxZero : f (j.insertNth (g x') x') = 0 := by
        have hZeroPhi : f (Φ (Fin.snoc x' (g x'))) = 0 := by
          simpa [fTilde] using hyZero'
        simpa [hΦSnoc x' (g x')] using hZeroPhi
      exact ⟨hxW, hxZero⟩
  refine ⟨j, hj, U, hUopen, W, hWopen, hx0W, g, hDiffOn, hGraphEq⟩

end Section08
end Chap06
