import stacks_proof.stacks_project.LinearAlgebra.PowerOperations
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

/- Domain triage: this file lies in multilinear algebra of symmetric and exterior powers.
The owner abstractions are the canonical comparison maps
`SymmetricPower.leftTensorMap`, `SymmetricPower.map`, `exteriorPower.leftTensorMap`, and
`exteriorPower.map` from `stacks_project.LinearAlgebra.PowerOperations`, organized around the
canonical owner `S : ShortComplex (ModuleCat R)` with `hS : S.ShortExact`. The present results are
`source-facing` exactness statements expressed directly in those owner maps, while the
tensor-presentation exact sequences from Lemma `10.13.3` remain the lower `bridge/view` layer
used to justify them. -/

section

universe u v

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- Helper for Lemma 10.13.2: in a short exact sequence, two lifts with the same image under
`S.g.hom` differ by something in `range S.f.hom`. -/
private theorem sub_mem_range_of_same_image
    (hS : S.ShortExact) {x y : S.X₂} (hxy : S.g.hom x = S.g.hom y) :
    x - y ∈ LinearMap.range S.f.hom := by
  -- Exactness identifies `ker S.g.hom` with `range S.f.hom`, so the equal-image hypothesis
  -- turns the difference `x - y` into a canonical range element.
  have hker : LinearMap.ker S.g.hom = LinearMap.range S.f.hom := by
    exact LinearMap.exact_iff.mp
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  rw [← hker, LinearMap.mem_ker]
  simpa [LinearMap.map_sub] using sub_eq_zero.mpr hxy

/-- Helper for Lemma 10.13.2: the `surjInv` chosen lift of `S.g.hom x` differs from `x` by
something in `range S.f.hom`. -/
private theorem surjInv_sub_mem_range
    (hS : S.ShortExact) (x : S.X₂) :
    Function.surjInv hS.moduleCat_surjective_g (S.g.hom x) - x ∈
      LinearMap.range S.f.hom := by
  -- The chosen lift and the original element have the same image under `S.g.hom`.
  apply sub_mem_range_of_same_image (S := S) (hS := hS)
  simpa using Function.rightInverse_surjInv hS.moduleCat_surjective_g (S.g.hom x)

/-- Helper for Lemma 10.13.2: the additive defect of the chosen `surjInv` lifts lands in
`range S.f.hom`. -/
private theorem surjInv_add_sub_mem_range
    (hS : S.ShortExact) (x y : S.X₃) :
    Function.surjInv hS.moduleCat_surjective_g (x + y) -
        (Function.surjInv hS.moduleCat_surjective_g x +
          Function.surjInv hS.moduleCat_surjective_g y) ∈
      LinearMap.range S.f.hom := by
  -- Both lifts map to `x + y`, so exactness forces their difference into `range S.f.hom`.
  apply sub_mem_range_of_same_image (S := S) (hS := hS)
  calc
    S.g.hom (Function.surjInv hS.moduleCat_surjective_g (x + y)) = x + y := by
      exact Function.rightInverse_surjInv hS.moduleCat_surjective_g (x + y)
    _ = S.g.hom (Function.surjInv hS.moduleCat_surjective_g x) +
          S.g.hom (Function.surjInv hS.moduleCat_surjective_g y) := by
        rw [Function.rightInverse_surjInv hS.moduleCat_surjective_g x,
          Function.rightInverse_surjInv hS.moduleCat_surjective_g y]
    _ = S.g.hom
          (Function.surjInv hS.moduleCat_surjective_g x +
            Function.surjInv hS.moduleCat_surjective_g y) := by
        symm
        exact LinearMap.map_add _ _ _

/-- Helper for Lemma 10.13.2: the scalar defect of the chosen `surjInv` lifts lands in
`range S.f.hom`. -/
private theorem surjInv_smul_sub_mem_range
    (hS : S.ShortExact) (r : R) (x : S.X₃) :
    Function.surjInv hS.moduleCat_surjective_g (r • x) -
        r • Function.surjInv hS.moduleCat_surjective_g x ∈
      LinearMap.range S.f.hom := by
  -- The chosen lift of `r • x` and the scalar multiple of the chosen lift of `x` have the same
  -- image under `S.g.hom`, so their difference again belongs to `range S.f.hom`.
  apply sub_mem_range_of_same_image (S := S) (hS := hS)
  calc
    S.g.hom (Function.surjInv hS.moduleCat_surjective_g (r • x)) = r • x := by
      exact Function.rightInverse_surjInv hS.moduleCat_surjective_g (r • x)
    _ = r • S.g.hom (Function.surjInv hS.moduleCat_surjective_g x) := by
        rw [Function.rightInverse_surjInv hS.moduleCat_surjective_g x]
    _ = S.g.hom (r • Function.surjInv hS.moduleCat_surjective_g x) := by
        symm
        exact LinearMap.map_smulₛₗ _ _ _

-- Proof sketch: present `Sym[R]^(n + 1) M` as the quotient of the `(n + 1)`st tensor power by
-- permutation relations, use `TensorProduct.lTensor_exact` and `LinearMap.lTensor_surjective` on
-- the tensor-power presentation, and descend the resulting maps to the canonical owner maps
-- `SymmetricPower.leftTensorMap` and `SymmetricPower.map`.
/-- Helper for Lemma 10.13.2: a surjective linear map induces a surjective map on symmetric
powers. -/
theorem symmetric_power_map_surjective_of_surjective
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ) {g : M₁ →ₗ[R] M} (hg : Function.Surjective g) :
    Function.Surjective (SymmetricPower.map n g) := by
  classical
  rw [← LinearMap.range_eq_top]
  -- Pure symmetric tensors span the codomain, and each one comes from lifted entries.
  apply top_unique
  calc
    ⊤ = Submodule.span R (Set.range (SymmetricPower.tprod R
        (ι := SymmetricPower.UFin n) (M := M))) := by
          symm
          exact SymmetricPower.span_tprod_eq_top (R := R) (ι := SymmetricPower.UFin n) (M := M)
    _ ≤ LinearMap.range (SymmetricPower.map n g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨m, rfl⟩
      let m' : SymmetricPower.UFin n → M₁ := fun i ↦ Function.surjInv hg (m i)
      have hm' : g ∘ m' = m := by
        funext i
        exact Function.rightInverse_surjInv hg (m i)
      refine ⟨SymmetricPower.tprod R m', ?_⟩
      simpa [hm'] using SymmetricPower.map_tprod (R := R) (n := n) g m'

/-- Helper for Lemma 10.13.2: the symmetric-power map annihilates the range of the canonical
left tensor map. -/
private theorem symmetric_power_leftTensorMap_range_le_ker
    (hS : S.ShortExact) (n : ℕ) :
    LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom) ≤
      LinearMap.ker (SymmetricPower.map (n + 1) S.g.hom) := by
  have hfg : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  rw [LinearMap.range_le_ker_iff]
  ext x y
  let ψ : Sym[R] (SymmetricPower.UFin n) S.X₂ →ₗ[R] Sym[R] (SymmetricPower.UFin (n + 1)) S.X₃ :=
    (SymmetricPower.map (n + 1) S.g.hom).comp
      ((SymmetricPower.leftTensorMap n S.f.hom).comp
        (TensorProduct.mk R S.X₁ (Sym[R] (SymmetricPower.UFin n) S.X₂) x))
  have hψ : ψ = 0 := by
    -- Pure symmetric tensors span, so it is enough to check the composite on one generator.
    rw [Submodule.linearMap_eq_zero_iff_of_span_eq_top ψ
      (hM := SymmetricPower.span_tprod_eq_top
        (R := R) (ι := SymmetricPower.UFin n) (M := S.X₂))]
    rintro ⟨z, ⟨m, rfl⟩⟩
    -- The first factor becomes `S.g.hom (S.f.hom x) = 0`, so multilinearity kills the tensor.
    change
      SymmetricPower.map (n + 1) S.g.hom
        (SymmetricPower.leftTensorMap n S.f.hom (x ⊗ₜ SymmetricPower.tprod R m)) = 0
    rw [SymmetricPower.leftTensorMap_tmul_tprod, SymmetricPower.map_tprod]
    let i0 : SymmetricPower.UFin (n + 1) := ⟨0⟩
    exact (SymmetricPower.tprod R).map_coord_zero i0 (by
      change S.g.hom (S.f.hom x) = 0
      simpa using LinearMap.congr_fun (Function.Exact.linearMap_comp_eq_zero hfg) x)
  -- Apply the vanishing of the auxiliary linear map to the requested symmetric tensor.
  simpa [ψ, TensorProduct.mk_apply] using LinearMap.congr_fun hψ y

/-- Helper for Lemma 10.13.2: the quotient-descended symmetric-power map induced by
`SymmetricPower.map`. -/
private noncomputable def symmetric_power_range_desc
    (hS : S.ShortExact) (n : ℕ) :
    (Sym[R] (SymmetricPower.UFin (n + 1)) S.X₂) ⧸
        LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom) →ₗ[R]
      Sym[R] (SymmetricPower.UFin (n + 1)) S.X₃ :=
  (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)).liftQ
    (SymmetricPower.map (n + 1) S.g.hom)
    (symmetric_power_leftTensorMap_range_le_ker (hS := hS) (n := n))

/-- Helper for Lemma 10.13.2: the descended symmetric-power quotient map agrees with
`SymmetricPower.map` before passing to the quotient. -/
private theorem symmetric_power_range_desc_comp_mkQ
    (hS : S.ShortExact) (n : ℕ) :
    (symmetric_power_range_desc (hS := hS) (n := n)).comp
        (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom))) =
      SymmetricPower.map (n + 1) S.g.hom := by
  -- The quotient lift is characterized by agreeing with the original map on representatives.
  ext y
  simp [symmetric_power_range_desc]

/-- Helper for Lemma 10.13.2: the descended symmetric-power quotient map is surjective. -/
private theorem symmetric_power_range_desc_surjective
    (hS : S.ShortExact) (n : ℕ) :
    Function.Surjective (symmetric_power_range_desc (hS := hS) (n := n)) := by
  intro z
  -- Surjectivity survives quotient descent because the original map is already surjective.
  obtain ⟨y, rfl⟩ := symmetric_power_map_surjective_of_surjective
    (R := R) (n := n + 1) (g := S.g.hom) hS.moduleCat_surjective_g z
  refine ⟨(Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom))) y, ?_⟩
  simp [symmetric_power_range_desc]

/-- Helper for Lemma 10.13.2: quotient classes of pure symmetric tensors still span after
passing to the quotient by `range (leftTensorMap)`. -/
private theorem symmetric_power_mkQ_tprod_span_top (n : ℕ) :
    Submodule.span R
        (Set.range
          ((Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom))) ∘
            SymmetricPower.tprod R
              (ι := SymmetricPower.UFin (n + 1)) (M := S.X₂))) = ⊤ := by
  let Q := LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)
  let pureGenerators :=
    Set.range
      (SymmetricPower.tprod R
        (ι := SymmetricPower.UFin (n + 1)) (M := S.X₂))
  have himage :
      Set.range
          ((Submodule.mkQ Q) ∘
            SymmetricPower.tprod R
              (ι := SymmetricPower.UFin (n + 1)) (M := S.X₂)) =
        (Submodule.mkQ Q) '' pureGenerators := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨_, ⟨m, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
  -- The quotient map is surjective, so the image of the spanning pure tensors is still spanning.
  calc
    Submodule.span R
        (Set.range
          ((Submodule.mkQ Q) ∘
            SymmetricPower.tprod R
              (ι := SymmetricPower.UFin (n + 1)) (M := S.X₂))) =
        Submodule.span R ((Submodule.mkQ Q) '' pureGenerators) := by
          rw [himage]
    _ = Submodule.map (Submodule.mkQ Q) (Submodule.span R pureGenerators) := by
          rw [Submodule.map_span]
    _ = Submodule.map (Submodule.mkQ Q) ⊤ := by
          rw [SymmetricPower.span_tprod_eq_top
            (R := R) (ι := SymmetricPower.UFin (n + 1)) (M := S.X₂)]
    _ = ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]

/-- Helper for Lemma 10.13.2: if one symmetric tensor slot changes by something in
`range S.f.hom`, then the resulting pure symmetric tensors differ by something in
`range (SymmetricPower.leftTensorMap n S.f.hom)`. -/
private theorem symmetric_tprod_sub_mem_range_of_sub_mem_range
    (hS : S.ShortExact) (n : ℕ)
    {i : SymmetricPower.UFin (n + 1)} {m : SymmetricPower.UFin (n + 1) → S.X₂}
    {x y : S.X₂} (hxy : x - y ∈ LinearMap.range S.f.hom) :
    SymmetricPower.tprod R (Function.update m i x) -
        SymmetricPower.tprod R (Function.update m i y) ∈
      LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom) := by
  classical
  let e : Equiv.Perm (SymmetricPower.UFin (n + 1)) := {
    toFun := fun j ↦ ULift.up (i.down.cycleRange.symm j.down)
    invFun := fun j ↦ ULift.up (i.down.cycleRange j.down)
    left_inv := by
      intro j
      cases j
      simp
    right_inv := by
      intro j
      cases j
      simp
  }
  let mTail : SymmetricPower.UFin n → S.X₂ := fun j ↦ m ⟨i.down.succAbove j.down⟩
  obtain ⟨a, ha⟩ := hxy
  have hxperm :
      SymmetricPower.tprod R (Function.update m i x) =
        SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) x) := by
    -- Reindex the tuple so that the updated slot becomes the front coordinate.
    calc
      SymmetricPower.tprod R (Function.update m i x) =
          SymmetricPower.tprod R ((Function.update m i x) ∘ e) := by
            symm
            exact SymmetricPower.tprod_equiv (R := R) e (Function.update m i x)
      _ = SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) x) := by
            rw [Function.update_comp_equiv]
            simp [e]
  have hyperm :
      SymmetricPower.tprod R (Function.update m i y) =
        SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) y) := by
    -- The same front-slot normalization works for the second tuple as well.
    calc
      SymmetricPower.tprod R (Function.update m i y) =
          SymmetricPower.tprod R ((Function.update m i y) ∘ e) := by
            symm
            exact SymmetricPower.tprod_equiv (R := R) e (Function.update m i y)
      _ = SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) y) := by
            rw [Function.update_comp_equiv]
            simp [e]
  have hfront :
      SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) x) -
          SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) y) ∈
        LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom) := by
    have hsplit :
        SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) x) -
            SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) y) =
          SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) (x - y)) := by
      -- Multilinearity at the front coordinate isolates the difference term.
      rw [show x = (x - y) + y by abel]
      rw [(SymmetricPower.tprod R).map_update_add]
      abel
    have hbase :
        SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) (x - y)) ∈
          LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom) := by
      -- Once the modified coordinate is at the front, `leftTensorMap_tmul_tprod` provides the
      -- required explicit preimage.
      have hupdate :
          Function.update (m ∘ e) (ULift.up 0) (x - y) =
            fun j : SymmetricPower.UFin (n + 1) ↦
              Fin.cases (x - y) (fun k ↦ m ⟨i.down.succAbove k⟩) j.down := by
        funext j
        rcases j with ⟨j⟩
        cases j using Fin.cases with
        | zero =>
            simp [e]
        | succ j =>
            simp [e, Fin.cycleRange_symm_succ, Function.update_of_ne, Fin.succ_ne_zero]
      have hwit :
          SymmetricPower.leftTensorMap n S.f.hom (a ⊗ₜ SymmetricPower.tprod R mTail) =
            SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) (x - y)) := by
        calc
          SymmetricPower.leftTensorMap n S.f.hom (a ⊗ₜ SymmetricPower.tprod R mTail) =
              SymmetricPower.tprod R
                (fun j : SymmetricPower.UFin (n + 1) ↦
                  Fin.cases (x - y) (fun k ↦ m ⟨i.down.succAbove k⟩) j.down) := by
                    simpa only [mTail, ha] using
                      (SymmetricPower.leftTensorMap_tmul_tprod (R := R) (n := n) S.f.hom a mTail)
          _ = SymmetricPower.tprod R (Function.update (m ∘ e) (ULift.up 0) (x - y)) := by
                rw [hupdate]
      exact ⟨a ⊗ₜ SymmetricPower.tprod R mTail, hwit⟩
    rw [hsplit]
    exact hbase
  -- Transport the front-slot range element back through the symmetric reindexing.
  rw [hxperm, hyperm]
  exact hfront

/-- Helper for Lemma 10.13.2: the previous range-membership statement descends to equality in the
quotient by `range (SymmetricPower.leftTensorMap n S.f.hom)`. -/
private theorem symmetric_mkQ_tprod_eq_of_sub_mem_range
    (hS : S.ShortExact) (n : ℕ)
    {i : SymmetricPower.UFin (n + 1)} {m : SymmetricPower.UFin (n + 1) → S.X₂}
    {x y : S.X₂} (hxy : x - y ∈ LinearMap.range S.f.hom) :
    (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
        (SymmetricPower.tprod R (Function.update m i x)) =
      (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
        (SymmetricPower.tprod R (Function.update m i y)) := by
  -- Quotient equality is exactly the statement that the difference lands in the displayed range.
  exact (Submodule.Quotient.eq _).2
    (symmetric_tprod_sub_mem_range_of_sub_mem_range
      (R := R) (S := S) (hS := hS) (n := n) hxy)

/-- Helper for Lemma 10.13.2: pointwise replacement by elements of `range S.f.hom` does not change
the quotient class of a pure symmetric tensor. -/
private theorem symmetric_mkQ_tprod_eq_of_pointwise_sub_mem_range
    (hS : S.ShortExact) (n : ℕ)
    {m m' : SymmetricPower.UFin (n + 1) → S.X₂}
    (hmm' : ∀ i, m' i - m i ∈ LinearMap.range S.f.hom) :
    (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
        (SymmetricPower.tprod R m') =
      (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
        (SymmetricPower.tprod R m) := by
  classical
  let Q := LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)
  let current :
      Finset (SymmetricPower.UFin (n + 1)) → SymmetricPower.UFin (n + 1) → S.X₂ :=
    fun s j ↦ if j ∈ s then m' j else m j
  have hcurrent :
      ∀ s : Finset (SymmetricPower.UFin (n + 1)),
        (Submodule.mkQ Q) (SymmetricPower.tprod R (current s)) =
          (Submodule.mkQ Q) (SymmetricPower.tprod R m) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        -- With no coordinates replaced, we are looking at the original pure generator.
        simp [current, Q]
    | @insert i s hi hs =>
        have hinsert :
            current (insert i s) = Function.update (current s) i (m' i) := by
          -- Adding one more coordinate replacement is exactly a single `Function.update`.
          funext j
          by_cases hji : j = i
          · subst hji
            simp [current]
          · simp [current, hji, hi]
        have hvalue : current s i = m i := by
          simp [current, hi]
        calc
          (Submodule.mkQ Q) (SymmetricPower.tprod R (current (insert i s))) =
              (Submodule.mkQ Q) (SymmetricPower.tprod R (Function.update (current s) i (m' i))) := by
                rw [hinsert]
          _ =
              (Submodule.mkQ Q) (SymmetricPower.tprod R (Function.update (current s) i (m i))) := by
                have hsub : m' i - current s i ∈ LinearMap.range S.f.hom := by
                  simpa [hvalue] using hmm' i
                have hsub' : m' i - m i ∈ LinearMap.range S.f.hom := by
                  simpa [hvalue] using hsub
                exact symmetric_mkQ_tprod_eq_of_sub_mem_range
                  (R := R) (S := S) (hS := hS) (n := n)
                  (m := current s) (i := i) (x := m' i) (y := m i) (hxy := hsub')
          _ = (Submodule.mkQ Q) (SymmetricPower.tprod R (current s)) := by
                have hrestore : Function.update (current s) i (m i) = current s := by
                  funext j
                  by_cases hji : j = i
                  · subst hji
                    simp [hvalue]
                  · simp [Function.update_of_ne hji]
                rw [hrestore]
          _ = (Submodule.mkQ Q) (SymmetricPower.tprod R m) := hs
  -- Replacing all coordinates recovers `m'`, so the finite iteration closes the congruence.
  simpa [current, Q] using hcurrent (Finset.univ : Finset (SymmetricPower.UFin (n + 1)))

/-- Helper for Lemma 10.13.2: a section formula on pure symmetric generators already forces the
descended quotient map to be injective. -/
private theorem symmetric_power_range_desc_injective_of_generator_formula
    (hS : S.ShortExact) (n : ℕ)
    (sectionMap :
      Sym[R] (SymmetricPower.UFin (n + 1)) S.X₃ →ₗ[R]
        (Sym[R] (SymmetricPower.UFin (n + 1)) S.X₂) ⧸
          LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom))
    (hsection :
      ∀ m : SymmetricPower.UFin (n + 1) → S.X₂,
        sectionMap (SymmetricPower.tprod R (S.g.hom ∘ m)) =
          (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
            (SymmetricPower.tprod R m)) :
    Function.Injective (symmetric_power_range_desc (hS := hS) (n := n)) := by
  have hleft :
      sectionMap.comp (symmetric_power_range_desc (hS := hS) (n := n)) = LinearMap.id := by
    -- Pure quotient classes span the source quotient, so it is enough to check the composite
    -- on those generators.
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (symmetric_power_mkQ_tprod_span_top (R := R) (S := S) (n := n))]
    rintro ⟨_, ⟨m, rfl⟩⟩
    -- The generator formula is the only source-faithful input needed here.
    have hdesc := LinearMap.congr_fun
      (symmetric_power_range_desc_comp_mkQ (R := R) (S := S) (hS := hS) (n := n))
      (SymmetricPower.tprod R m)
    calc
      sectionMap
          ((symmetric_power_range_desc (hS := hS) (n := n))
            ((Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
              (SymmetricPower.tprod R m))) =
        sectionMap ((SymmetricPower.map (n + 1) S.g.hom) (SymmetricPower.tprod R m)) := by
          simpa [LinearMap.comp_apply] using congrArg sectionMap hdesc
      _ =
          (Submodule.mkQ (LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)))
            (SymmetricPower.tprod R m) := by
          simpa [SymmetricPower.map_tprod] using hsection m
  -- Once a left inverse exists, injectivity is formal.
  intro x y hxy
  have hxy' := congrArg sectionMap hxy
  have hx : sectionMap ((symmetric_power_range_desc (hS := hS) (n := n)) x) = x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft x
  have hy : sectionMap ((symmetric_power_range_desc (hS := hS) (n := n)) y) = y := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft y
  simpa [hx, hy] using hxy'

/-- Helper for Lemma 10.13.2: the descended symmetric-power quotient map is injective. -/
private theorem symmetric_power_range_desc_injective
    (hS : S.ShortExact) (n : ℕ) :
    Function.Injective (symmetric_power_range_desc (hS := hS) (n := n)) := by
  -- Route correction: the exactness proof now runs through the owner quotient row
  -- `leftTensorMap ⟶ mkQ (range leftTensorMap)`, so injectivity of the descended comparison map
  -- is the only remaining non-formal step.
  classical
  let Q := LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)
  let σ : S.X₃ → S.X₂ := Function.surjInv hS.moduleCat_surjective_g
  let rawSection :
      MultilinearMap R (fun _ : SymmetricPower.UFin (n + 1) ↦ S.X₃)
        ((Sym[R] (SymmetricPower.UFin (n + 1)) S.X₂) ⧸ Q) :=
    MultilinearMap.mk'
      (fun m ↦ (Submodule.mkQ Q) (SymmetricPower.tprod R (σ ∘ m)))
      (fun m i x y ↦ by
        -- Replace the chosen lift of `x + y` by the sum of the chosen lifts modulo the owner
        -- quotient, then use multilinearity of `SymmetricPower.tprod`.
        have hreplace :
            (Submodule.mkQ Q)
                (SymmetricPower.tprod R
                  (Function.update (σ ∘ m) i (σ (x + y)))) =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R
                  (Function.update (σ ∘ m) i (σ x + σ y))) := by
          exact symmetric_mkQ_tprod_eq_of_sub_mem_range
            (R := R) (S := S) (hS := hS) (n := n)
            (m := σ ∘ m) (i := i) (x := σ (x + y)) (y := σ x + σ y)
            (surjInv_add_sub_mem_range (R := R) (S := S) (hS := hS) x y)
        calc
          (Submodule.mkQ Q) (SymmetricPower.tprod R (σ ∘ Function.update m i (x + y))) =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ (x + y)))) := by
                  simp [Function.comp_update]
          _ =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ x + σ y))) := hreplace
          _ =
              (Submodule.mkQ Q)
                ((SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ x))) +
                  SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ y))) := by
                    rw [(SymmetricPower.tprod R).map_update_add]
          _ =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ x))) +
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ y))) := by
                    rw [LinearMap.map_add]
          _ =
              (Submodule.mkQ Q) (SymmetricPower.tprod R (σ ∘ Function.update m i x)) +
              (Submodule.mkQ Q) (SymmetricPower.tprod R (σ ∘ Function.update m i y)) := by
                    simp [Function.comp_update]
      )
      (fun m i r x ↦ by
        -- The same quotient congruence handles the scalar defect of the chosen lifts.
        have hreplace :
            (Submodule.mkQ Q)
                (SymmetricPower.tprod R
                  (Function.update (σ ∘ m) i (σ (r • x)))) =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R
                  (Function.update (σ ∘ m) i (r • σ x))) := by
          exact symmetric_mkQ_tprod_eq_of_sub_mem_range
            (R := R) (S := S) (hS := hS) (n := n)
            (m := σ ∘ m) (i := i) (x := σ (r • x)) (y := r • σ x)
            (surjInv_smul_sub_mem_range (R := R) (S := S) (hS := hS) r x)
        calc
          (Submodule.mkQ Q) (SymmetricPower.tprod R (σ ∘ Function.update m i (r • x))) =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ (r • x)))) := by
                  simp [Function.comp_update]
          _ =
              (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (r • σ x))) := hreplace
          _ =
              (Submodule.mkQ Q)
                (r • SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ x))) := by
                    rw [(SymmetricPower.tprod R).map_update_smul]
          _ =
              r • (Submodule.mkQ Q)
                (SymmetricPower.tprod R (Function.update (σ ∘ m) i (σ x))) := by
                    rw [LinearMap.map_smulₛₗ]
                    simp
          _ =
              r • (Submodule.mkQ Q) (SymmetricPower.tprod R (σ ∘ Function.update m i x)) := by
                    simp [Function.comp_update]
      )
  let rawTensor :
      (⨂[R] (_ : SymmetricPower.UFin (n + 1)), S.X₃) →ₗ[R]
        ((Sym[R] (SymmetricPower.UFin (n + 1)) S.X₂) ⧸ Q) :=
    PiTensorProduct.lift rawSection
  have hrel :
      ∀ {x y : ⨂[R] (_ : SymmetricPower.UFin (n + 1)), S.X₃},
        addConGen (SymmetricPower.Rel R (SymmetricPower.UFin (n + 1)) S.X₃) x y →
          rawTensor x = rawTensor y := by
    intro x y hxy
    induction hxy with
    | of _ _ h =>
        cases h with
        | perm e m =>
            -- The raw tensor map is invariant under permutations because symmetric pure tensors are.
            have ht :
                SymmetricPower.tprod R (fun j ↦ σ (m (e j))) =
                  SymmetricPower.tprod R (σ ∘ m) := by
              simpa [Function.comp_apply] using
                (SymmetricPower.tprod_equiv (R := R) e (σ ∘ m))
            simpa [rawTensor, rawSection, PiTensorProduct.lift.tprod, Function.comp_apply] using
              congrArg (Submodule.mkQ Q) ht.symm
    | refl =>
        rfl
    | symm _ ih =>
        exact ih.symm
    | trans _ _ ih₁ ih₂ =>
        exact ih₁.trans ih₂
    | add _ _ ih₁ ih₂ =>
        simpa [LinearMap.map_add] using congrArg₂ (· + ·) ih₁ ih₂
  let sectionMap :
      Sym[R] (SymmetricPower.UFin (n + 1)) S.X₃ →ₗ[R]
        ((Sym[R] (SymmetricPower.UFin (n + 1))S.X₂) ⧸ Q) := {
    __ := AddCon.lift _ rawTensor.toAddMonoidHom (fun x y h ↦ hrel h)
    map_smul' := by
      intro r q
      refine AddCon.induction_on q ?_
      intro x
      -- The tensor-level map is linear, so the descended quotient map is linear as well.
      change rawTensor (r • x) = r • rawTensor x
      simpa using rawTensor.map_smulₛₗ r x
  }
  have hsection :
      ∀ m : SymmetricPower.UFin (n + 1) → S.X₂,
        sectionMap (SymmetricPower.tprod R (S.g.hom ∘ m)) =
          (Submodule.mkQ Q) (SymmetricPower.tprod R m) := by
    intro m
    -- On pure generators, the chosen lifts differ from the original tuple pointwise by
    -- `range S.f.hom`, so the global quotient congruence closes the formula.
    change rawTensor (PiTensorProduct.tprod R (S.g.hom ∘ m)) =
      (Submodule.mkQ Q) (SymmetricPower.tprod R m)
    simp [rawTensor, rawSection, PiTensorProduct.lift.tprod]
    exact symmetric_mkQ_tprod_eq_of_pointwise_sub_mem_range
      (R := R) (S := S) (hS := hS) (n := n)
      (m := m) (m' := σ ∘ S.g.hom ∘ m)
      (fun j ↦ surjInv_sub_mem_range (R := R) (S := S) (hS := hS) (m j))
  exact symmetric_power_range_desc_injective_of_generator_formula
    (R := R) (S := S) (hS := hS) (n := n) sectionMap hsection

/-- Lemma 10.13.2 (1), stated in degree `n + 1`: for an exact sequence `M₂ ⟶ M₁ ⟶ M ⟶ 0`,
the canonical sequence
`M₂ ⊗[R] Sym[R]^n M₁ ⟶ Sym[R]^(n + 1) M₁ ⟶ Sym[R]^(n + 1) M ⟶ 0`
is exact. -/
@[stacks 00DO]
theorem symmetric_power_exact_of_exact (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (SymmetricPower.leftTensorMap n S.f.hom) (SymmetricPower.map (n + 1) S.g.hom) ∧
      Function.Surjective (SymmetricPower.map (n + 1) S.g.hom) := by
  refine ⟨?_, ?_⟩
  · -- Route correction: the exactness argument is now reduced to injectivity of the descended
    -- quotient map `symmetric_power_range_desc`, after which exactness transfers formally from
    -- `LinearMap.exact_map_mkQ_range`.
    let Q := LinearMap.range (SymmetricPower.leftTensorMap n S.f.hom)
    have hdesc_injective :
        Function.Injective (symmetric_power_range_desc (hS := hS) (n := n)) :=
      symmetric_power_range_desc_injective (hS := hS) (n := n)
    have hdesc_comp :
        (symmetric_power_range_desc (hS := hS) (n := n)).comp (Submodule.mkQ Q) =
          SymmetricPower.map (n + 1) S.g.hom :=
      symmetric_power_range_desc_comp_mkQ (hS := hS) (n := n)
    have hmkQ_zero :
        (Submodule.mkQ Q).comp (SymmetricPower.leftTensorMap n S.f.hom) = 0 := by
      simpa [Q] using Function.Exact.linearMap_comp_eq_zero
        (LinearMap.exact_map_mkQ_range (SymmetricPower.leftTensorMap n S.f.hom))
    -- First pass to the quotient by the displayed range, then use injectivity of the descended
    -- comparison map to pull `ker` back to that range.
    refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · apply LinearMap.ext
      intro t
      have hdesc_on :
          (symmetric_power_range_desc (hS := hS) (n := n))
              ((Submodule.mkQ Q) (SymmetricPower.leftTensorMap n S.f.hom t)) =
            SymmetricPower.map (n + 1) S.g.hom
              (SymmetricPower.leftTensorMap n S.f.hom t) := by
        simpa [Q, LinearMap.comp_apply] using
          LinearMap.congr_fun hdesc_comp (SymmetricPower.leftTensorMap n S.f.hom t)
      have hq :
          (Submodule.mkQ Q) (SymmetricPower.leftTensorMap n S.f.hom t) = 0 := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hmkQ_zero t
      calc
        SymmetricPower.map (n + 1) S.g.hom
            (SymmetricPower.leftTensorMap n S.f.hom t) =
          (symmetric_power_range_desc (hS := hS) (n := n))
            ((Submodule.mkQ Q) (SymmetricPower.leftTensorMap n S.f.hom t)) := hdesc_on.symm
        _ = (symmetric_power_range_desc (hS := hS) (n := n)) 0 := by
              rw [hq]
        _ = 0 := by simp
    · intro x hx
      have hxQ :
          (Submodule.mkQ Q) x = 0 := by
        apply hdesc_injective
        simpa [Q, hdesc_comp, LinearMap.comp_apply] using hx
      exact (Submodule.Quotient.mk_eq_zero Q).mp hxQ
  · -- Surjectivity is checked on pure symmetric tensors, which span the target.
    exact symmetric_power_map_surjective_of_surjective (R := R) (n := n + 1)
      (g := S.g.hom) hS.moduleCat_surjective_g

/-- Helper for Lemma 10.13.2: the exterior-power map annihilates the range of the canonical left
tensor map. -/
private theorem exterior_power_leftTensorMap_range_le_ker
    (hS : S.ShortExact) (n : ℕ) :
    LinearMap.range (exteriorPower.leftTensorMap n S.f.hom) ≤
      LinearMap.ker (exteriorPower.map (n + 1) S.g.hom) := by
  have hfg : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  rw [LinearMap.range_le_ker_iff]
  ext x y
  let ψ : ⋀[R]^n S.X₂ →ₗ[R] ⋀[R]^(n + 1) S.X₃ :=
    (exteriorPower.map (n + 1) S.g.hom).comp
      ((exteriorPower.leftTensorMap n S.f.hom).comp
        (TensorProduct.mk R S.X₁ (⋀[R]^n S.X₂) x))
  have hψ : ψ = 0 := by
    -- Pure wedges span, so it is enough to test the composite on `ιMulti`.
    rw [Submodule.linearMap_eq_zero_iff_of_span_eq_top ψ
      (hM := exteriorPower.ιMulti_span (R := R) (n := n) (M := S.X₂))]
    rintro ⟨z, ⟨m, rfl⟩⟩
    -- The first wedge factor becomes `S.g.hom (S.f.hom x) = 0`, so alternation kills it.
    change
      exteriorPower.map (n + 1) S.g.hom
        (exteriorPower.leftTensorMap n S.f.hom (x ⊗ₜ exteriorPower.ιMulti R n m)) = 0
    rw [exteriorPower.leftTensorMap_tmul_ιMulti, exteriorPower.map_apply_ιMulti]
    exact (exteriorPower.ιMulti R (n + 1)).map_coord_zero 0 (by
      simpa [Function.comp, Function.Exact.linearMap_comp_eq_zero hfg])
  -- Apply the vanishing of the auxiliary linear map to the requested exterior tensor.
  simpa [ψ, TensorProduct.mk_apply] using LinearMap.congr_fun hψ y

/-- Helper for Lemma 10.13.2: the quotient-descended exterior-power map induced by
`exteriorPower.map`. -/
private noncomputable def exterior_power_range_desc
    (hS : S.ShortExact) (n : ℕ) :
    (⋀[R]^(n + 1) S.X₂) ⧸ LinearMap.range (exteriorPower.leftTensorMap n S.f.hom) →ₗ[R]
      ⋀[R]^(n + 1) S.X₃ :=
  (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)).liftQ
    (exteriorPower.map (n + 1) S.g.hom)
    (exterior_power_leftTensorMap_range_le_ker (hS := hS) (n := n))

/-- Helper for Lemma 10.13.2: the descended exterior-power quotient map agrees with
`exteriorPower.map` before passing to the quotient. -/
private theorem exterior_power_range_desc_comp_mkQ
    (hS : S.ShortExact) (n : ℕ) :
    (exterior_power_range_desc (hS := hS) (n := n)).comp
        (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom))) =
      exteriorPower.map (n + 1) S.g.hom := by
  -- The quotient lift is characterized by agreeing with the original map on representatives.
  ext y
  simp [exterior_power_range_desc]

/-- Helper for Lemma 10.13.2: the descended exterior-power quotient map is surjective. -/
private theorem exterior_power_range_desc_surjective
    (hS : S.ShortExact) (n : ℕ) :
    Function.Surjective (exterior_power_range_desc (hS := hS) (n := n)) := by
  intro z
  -- Surjectivity survives quotient descent because `exteriorPower.map` is already surjective.
  obtain ⟨y, rfl⟩ := exteriorPower.map_surjective (n := n + 1) hS.moduleCat_surjective_g z
  refine ⟨(Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom))) y, ?_⟩
  simp [exterior_power_range_desc]

/-- Helper for Lemma 10.13.2: quotient classes of pure wedges still span after passing to the
quotient by `range (leftTensorMap)`. -/
private theorem exterior_power_mkQ_ιMulti_span_top (n : ℕ) :
    Submodule.span R
        (Set.range
          ((Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom))) ∘
            exteriorPower.ιMulti R (n + 1) (M := S.X₂))) = ⊤ := by
  let Q := LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)
  let pureGenerators := Set.range (exteriorPower.ιMulti R (n + 1) (M := S.X₂))
  have himage :
      Set.range
          ((Submodule.mkQ Q) ∘
            exteriorPower.ιMulti R (n + 1) (M := S.X₂)) =
        (Submodule.mkQ Q) '' pureGenerators := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨_, ⟨m, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
  -- The quotient map is surjective, so the images of the spanning wedge generators still span.
  calc
    Submodule.span R
        (Set.range
          ((Submodule.mkQ Q) ∘ exteriorPower.ιMulti R (n + 1) (M := S.X₂))) =
        Submodule.span R ((Submodule.mkQ Q) '' pureGenerators) := by
          rw [himage]
    _ = Submodule.map (Submodule.mkQ Q) (Submodule.span R pureGenerators) := by
          rw [Submodule.map_span]
    _ = Submodule.map (Submodule.mkQ Q) ⊤ := by
          rw [exteriorPower.ιMulti_span (R := R) (n := n + 1) (M := S.X₂)]
    _ = ⊤ := by
          rw [Submodule.map_top, Submodule.range_mkQ]

/-- Helper for Lemma 10.13.2: if one exterior tensor slot changes by something in
`range S.f.hom`, then the resulting pure wedges differ by something in
`range (exteriorPower.leftTensorMap n S.f.hom)`. -/
private theorem exterior_ιMulti_sub_mem_range_of_sub_mem_range
    (hS : S.ShortExact) (n : ℕ)
    {i : Fin (n + 1)} {m : Fin (n + 1) → S.X₂}
    {x y : S.X₂} (hxy : x - y ∈ LinearMap.range S.f.hom) :
    exteriorPower.ιMulti R (n + 1) (Function.update m i x) -
        exteriorPower.ιMulti R (n + 1) (Function.update m i y) ∈
      LinearMap.range (exteriorPower.leftTensorMap n S.f.hom) := by
  let mTail : Fin n → S.X₂ := Fin.removeNth i m
  obtain ⟨a, ha⟩ := hxy
  have hdiff :
      exteriorPower.ιMulti R (n + 1) (Function.update m i x) -
          exteriorPower.ιMulti R (n + 1) (Function.update m i y) =
        exteriorPower.ιMulti R (n + 1) (Function.update m i (S.f.hom a)) := by
    -- Expand the changed slot as `(x - y) + y`, then isolate the first summand.
    rw [show x = (x - y) + y by abel, (exteriorPower.ιMulti R (n + 1)).map_update_add]
    rw [ha]
    abel
  have hinsert :
      Function.update m i (S.f.hom a) = i.insertNth (S.f.hom a) mTail := by
    -- Rewrite the updated family via `Fin.insertNth/removeNth` so the first-slot owner map applies.
    simpa [mTail] using (Fin.insertNth_removeNth i (S.f.hom a) m).symm
  have hsign :
      exteriorPower.ιMulti R (n + 1) (Function.update m i (S.f.hom a)) =
        (-1) ^ (i : ℕ) • exteriorPower.ιMulti R (n + 1) (Fin.cons (S.f.hom a) mTail) := by
    rw [hinsert]
    simpa [Matrix.vecCons] using
      (AlternatingMap.map_insertNth (f := exteriorPower.ιMulti R (n + 1))
        (p := i) (x := S.f.hom a) (v := mTail))
  have hbase :
      exteriorPower.ιMulti R (n + 1) (Fin.cons (S.f.hom a) mTail) ∈
        LinearMap.range (exteriorPower.leftTensorMap n S.f.hom) := by
    -- With the changed slot at the front, `leftTensorMap_tmul_ιMulti` gives the explicit preimage.
    refine ⟨a ⊗ₜ exteriorPower.ιMulti R n mTail, ?_⟩
    simpa using exteriorPower.leftTensorMap_tmul_ιMulti (R := R) (n := n) S.f.hom a mTail
  have hsmul :
      (-1) ^ (i : ℕ) • exteriorPower.ιMulti R (n + 1) (Fin.cons (S.f.hom a) mTail) ∈
        LinearMap.range (exteriorPower.leftTensorMap n S.f.hom) := by
    exact Submodule.smul_mem _ _ hbase
  -- Transport the explicit range element back through the sign and additivity steps.
  rw [hdiff, hsign]
  exact hsmul

/-- Helper for Lemma 10.13.2: the previous exterior range-membership statement descends to
equality in the quotient by `range (exteriorPower.leftTensorMap n S.f.hom)`. -/
private theorem exterior_mkQ_ιMulti_eq_of_sub_mem_range
    (hS : S.ShortExact) (n : ℕ)
    {i : Fin (n + 1)} {m : Fin (n + 1) → S.X₂}
    {x y : S.X₂} (hxy : x - y ∈ LinearMap.range S.f.hom) :
    (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
        (exteriorPower.ιMulti R (n + 1) (Function.update m i x)) =
      (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
        (exteriorPower.ιMulti R (n + 1) (Function.update m i y)) := by
  -- Quotient equality is equivalent to the corresponding difference lying in the displayed range.
  exact (Submodule.Quotient.eq _).2
    (exterior_ιMulti_sub_mem_range_of_sub_mem_range
      (R := R) (S := S) (hS := hS) (n := n) hxy)

/-- Helper for Lemma 10.13.2: if two coordinates have the same image in `S.X₃`, then the quotient
class of the corresponding pure wedge is zero. -/
private theorem exterior_mkQ_ιMulti_eq_zero_of_same_image
    (hS : S.ShortExact) (n : ℕ)
    {m : Fin (n + 1) → S.X₂} {i j : Fin (n + 1)}
    (hij : i ≠ j) (himg : S.g.hom (m i) = S.g.hom (m j)) :
    (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
      (exteriorPower.ιMulti R (n + 1) m) = 0 := by
  let Qext := LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)
  have hreplace :
      (Submodule.mkQ Qext) (exteriorPower.ιMulti R (n + 1) m) =
        (Submodule.mkQ Qext) (exteriorPower.ιMulti R (n + 1) (Function.update m i (m j))) := by
    -- Replace one coordinate by the other modulo the displayed range.
    simpa [Qext, Function.update_eq_self] using
      exterior_mkQ_ιMulti_eq_of_sub_mem_range
        (R := R) (S := S) (hS := hS) (n := n)
        (m := m) (i := i) (x := m i) (y := m j)
        (sub_mem_range_of_same_image (S := S) (hS := hS) himg)
  have hzero :
      (Submodule.mkQ Qext) (exteriorPower.ιMulti R (n + 1) (Function.update m i (m j))) = 0 := by
    -- The updated family has a repeated coordinate, so the exterior generator already vanishes.
    have hrepeat :
        (Function.update m i (m j)) i = (Function.update m i (m j)) j := by
      rw [Function.update_self, Function.update_of_ne hij.symm]
    rw [(exteriorPower.ιMulti R (n + 1)).map_eq_zero_of_eq _ hrepeat hij, map_zero]
  exact hreplace.trans hzero

/-- Helper for Lemma 10.13.2: pointwise replacement by elements of `range S.f.hom` does not change
the quotient class of a pure exterior generator. -/
private theorem exterior_mkQ_ιMulti_eq_of_pointwise_sub_mem_range
    (hS : S.ShortExact) (n : ℕ)
    {m m' : Fin (n + 1) → S.X₂}
    (hmm' : ∀ i, m' i - m i ∈ LinearMap.range S.f.hom) :
    (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
        (exteriorPower.ιMulti R (n + 1) m') =
      (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
        (exteriorPower.ιMulti R (n + 1) m) := by
  classical
  let Q := LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)
  let current : Finset (Fin (n + 1)) → Fin (n + 1) → S.X₂ :=
    fun s j ↦ if j ∈ s then m' j else m j
  have hcurrent :
      ∀ s : Finset (Fin (n + 1)),
        (Submodule.mkQ Q) (exteriorPower.ιMulti R (n + 1) (current s)) =
          (Submodule.mkQ Q) (exteriorPower.ιMulti R (n + 1) m) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        -- With no coordinates replaced, we are still at the original wedge generator.
        simp [current, Q]
    | @insert i s hi hs =>
        have hinsert :
            current (insert i s) = Function.update (current s) i (m' i) := by
          -- Inserting one index into the replacement set is again just a single `Function.update`.
          funext j
          by_cases hji : j = i
          · subst hji
            simp [current]
          · simp [current, hji, hi]
        have hvalue : current s i = m i := by
          simp [current, hi]
        calc
          (Submodule.mkQ Q) (exteriorPower.ιMulti R (n + 1) (current (insert i s))) =
              (Submodule.mkQ Q)
                (exteriorPower.ιMulti R (n + 1) (Function.update (current s) i (m' i))) := by
                  rw [hinsert]
          _ =
              (Submodule.mkQ Q)
                (exteriorPower.ιMulti R (n + 1) (Function.update (current s) i (m i))) := by
                  have hsub : m' i - current s i ∈ LinearMap.range S.f.hom := by
                    simpa [hvalue] using hmm' i
                  have hsub' : m' i - m i ∈ LinearMap.range S.f.hom := by
                    simpa [hvalue] using hsub
                  exact exterior_mkQ_ιMulti_eq_of_sub_mem_range
                    (R := R) (S := S) (hS := hS) (n := n)
                    (m := current s) (i := i) (x := m' i) (y := m i) (hxy := hsub')
          _ = (Submodule.mkQ Q) (exteriorPower.ιMulti R (n + 1) (current s)) := by
                have hrestore : Function.update (current s) i (m i) = current s := by
                  funext j
                  by_cases hji : j = i
                  · subst hji
                    simp [hvalue]
                  · simp [Function.update_of_ne hji]
                rw [hrestore]
          _ = (Submodule.mkQ Q) (exteriorPower.ιMulti R (n + 1) m) := hs
  -- Replacing all coordinates recovers `m'`, so the finite iteration gives the desired equality.
  simpa [current, Q] using hcurrent (Finset.univ : Finset (Fin (n + 1)))

/-- Helper for Lemma 10.13.2: a section formula on pure exterior generators already forces the
descended quotient map to be injective. -/
private theorem exterior_power_range_desc_injective_of_generator_formula
    (hS : S.ShortExact) (n : ℕ)
    (sectionMap :
      ⋀[R]^(n + 1) S.X₃ →ₗ[R]
        (⋀[R]^(n + 1) S.X₂) ⧸ LinearMap.range (exteriorPower.leftTensorMap n S.f.hom))
    (hsection :
      ∀ m : Fin (n + 1) → S.X₂,
        sectionMap (exteriorPower.ιMulti R (n + 1) (S.g.hom ∘ m)) =
          (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
            (exteriorPower.ιMulti R (n + 1) m)) :
    Function.Injective (exterior_power_range_desc (hS := hS) (n := n)) := by
  have hleft :
      sectionMap.comp (exterior_power_range_desc (hS := hS) (n := n)) = LinearMap.id := by
    -- Pure wedge classes span the source quotient, so the composite is determined there.
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (exterior_power_mkQ_ιMulti_span_top (R := R) (S := S) (n := n))]
    rintro ⟨_, ⟨m, rfl⟩⟩
    -- The generator formula is the only source-faithful input needed here.
    have hdesc := LinearMap.congr_fun
      (exterior_power_range_desc_comp_mkQ (R := R) (S := S) (hS := hS) (n := n))
      (exteriorPower.ιMulti R (n + 1) m)
    calc
      sectionMap
          ((exterior_power_range_desc (hS := hS) (n := n))
            ((Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
              (exteriorPower.ιMulti R (n + 1) m))) =
        sectionMap ((exteriorPower.map (n + 1) S.g.hom) (exteriorPower.ιMulti R (n + 1) m)) := by
          simpa [LinearMap.comp_apply] using congrArg sectionMap hdesc
      _ =
          (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
            (exteriorPower.ιMulti R (n + 1) m) := by
          simpa [exteriorPower.map_apply_ιMulti] using hsection m
  -- Once a left inverse exists, injectivity is formal.
  intro x y hxy
  have hxy' := congrArg sectionMap hxy
  have hx : sectionMap ((exterior_power_range_desc (hS := hS) (n := n)) x) = x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft x
  have hy : sectionMap ((exterior_power_range_desc (hS := hS) (n := n)) y) = y := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft y
  simpa [hx, hy] using hxy'

/-- Helper for Lemma 10.13.2: the raw quotient-valued exterior section on tuples, built from the
chosen `surjInv` lifts along `S.g.hom`. -/
private noncomputable def exterior_power_section_alt_aux
    (hS : S.ShortExact) (n : ℕ) :
    (Fin (n + 1) → S.X₃) →
      (⋀[R]^(n + 1) S.X₂) ⧸ LinearMap.range (exteriorPower.leftTensorMap n S.f.hom) :=
  fun m ↦
    (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
      (exteriorPower.ιMulti R (n + 1) (Function.surjInv hS.moduleCat_surjective_g ∘ m))

/-- Helper for Lemma 10.13.2: updating a finite tuple does not depend on which `DecidableEq`
instance on `Fin (n + 1)` is used to define `Function.update`. -/
private theorem fin_update_eq_canonical
    {α : Type*} {n : ℕ} [h : DecidableEq (Fin (n + 1))]
    (m : Fin (n + 1) → α) (i : Fin (n + 1)) (x : α) :
    @Function.update (Fin (n + 1)) (fun _ ↦ α) h m i x =
      @Function.update (Fin (n + 1)) (fun _ ↦ α) (instDecidableEqFin (n + 1)) m i x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [Function.update]
  · simp [Function.update, hji]

/-- Helper for Lemma 10.13.2: the raw exterior section is additive in each coordinate modulo the
owner quotient by `range (exteriorPower.leftTensorMap n S.f.hom)`. -/
private theorem exterior_power_section_alt_map_update_add
    (hS : S.ShortExact) (n : ℕ) [DecidableEq (Fin (n + 1))] :
    ∀ (m : Fin (n + 1) → S.X₃) (i : Fin (n + 1)) (x y : S.X₃),
      exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
          (Function.update m i (x + y)) =
        exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
          (Function.update m i x) +
        exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
          (Function.update m i y) := by
  intro m i x y
  let Q := LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)
  let σ : S.X₃ → S.X₂ := Function.surjInv hS.moduleCat_surjective_g
  have hreplace :
      (Submodule.mkQ Q)
          (exteriorPower.ιMulti R (n + 1)
            (Function.update (σ ∘ m) i (σ (x + y)))) =
        (Submodule.mkQ Q)
          (exteriorPower.ιMulti R (n + 1)
            (Function.update (σ ∘ m) i (σ x + σ y))) := by
    -- Replace the chosen lift of `x + y` by the sum of the chosen lifts modulo `Q`.
    simpa [Q,
      fin_update_eq_canonical (m := σ ∘ m) (i := i) (x := σ (x + y)),
      fin_update_eq_canonical (m := σ ∘ m) (i := i) (x := σ x + σ y)] using
      (exterior_mkQ_ιMulti_eq_of_sub_mem_range
        (R := R) (S := S) (hS := hS) (n := n)
        (m := σ ∘ m) (i := i) (x := σ (x + y)) (y := σ x + σ y)
        (surjInv_add_sub_mem_range (R := R) (S := S) (hS := hS) x y))
  calc
    exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
        (Function.update m i (x + y)) =
      (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1)
          (Function.update (σ ∘ m) i (σ (x + y)))) := by
            simp [exterior_power_section_alt_aux, Q, σ, Function.comp_update]
    _ =
      (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1)
          (Function.update (σ ∘ m) i (σ x + σ y))) := hreplace
    _ =
      (Submodule.mkQ Q)
        ((exteriorPower.ιMulti R (n + 1) (Function.update (σ ∘ m) i (σ x))) +
          exteriorPower.ιMulti R (n + 1) (Function.update (σ ∘ m) i (σ y))) := by
            rw [(exteriorPower.ιMulti R (n + 1)).map_update_add]
    _ =
      (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1) (Function.update (σ ∘ m) i (σ x))) +
      (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1) (Function.update (σ ∘ m) i (σ y))) := by
            rw [LinearMap.map_add]
    _ =
      exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
        (Function.update m i x) +
      exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
        (Function.update m i y) := by
            simp [exterior_power_section_alt_aux, Q, σ, Function.comp_update]

/-- Helper for Lemma 10.13.2: the raw exterior section is homogeneous in each coordinate modulo
the owner quotient by `range (exteriorPower.leftTensorMap n S.f.hom)`. -/
private theorem exterior_power_section_alt_map_update_smul
    (hS : S.ShortExact) (n : ℕ) [DecidableEq (Fin (n + 1))] :
    ∀ (m : Fin (n + 1) → S.X₃) (i : Fin (n + 1)) (r : R) (x : S.X₃),
      exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
          (Function.update m i (r • x)) =
        r • exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
          (Function.update m i x) := by
  intro m i r x
  let Q := LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)
  let σ : S.X₃ → S.X₂ := Function.surjInv hS.moduleCat_surjective_g
  have hreplace :
      (Submodule.mkQ Q)
          (exteriorPower.ιMulti R (n + 1)
            (Function.update (σ ∘ m) i (σ (r • x)))) =
        (Submodule.mkQ Q)
          (exteriorPower.ιMulti R (n + 1)
            (Function.update (σ ∘ m) i (r • σ x))) := by
    -- Replace the chosen lift of `r • x` by `r • σ x` modulo `Q`.
    simpa [Q,
      fin_update_eq_canonical (m := σ ∘ m) (i := i) (x := σ (r • x)),
      fin_update_eq_canonical (m := σ ∘ m) (i := i) (x := r • σ x)] using
      (exterior_mkQ_ιMulti_eq_of_sub_mem_range
        (R := R) (S := S) (hS := hS) (n := n)
        (m := σ ∘ m) (i := i) (x := σ (r • x)) (y := r • σ x)
        (surjInv_smul_sub_mem_range (R := R) (S := S) (hS := hS) r x))
  calc
    exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
        (Function.update m i (r • x)) =
      (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1)
          (Function.update (σ ∘ m) i (σ (r • x)))) := by
            simp [exterior_power_section_alt_aux, Q, σ, Function.comp_update]
    _ =
      (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1)
          (Function.update (σ ∘ m) i (r • σ x))) := hreplace
    _ =
      (Submodule.mkQ Q)
        (r • exteriorPower.ιMulti R (n + 1) (Function.update (σ ∘ m) i (σ x))) := by
            rw [(exteriorPower.ιMulti R (n + 1)).map_update_smul]
    _ =
      r • (Submodule.mkQ Q)
        (exteriorPower.ιMulti R (n + 1) (Function.update (σ ∘ m) i (σ x))) := by
            rw [LinearMap.map_smulₛₗ]
            simp
    _ =
      r • exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
        (Function.update m i x) := by
            simp [exterior_power_section_alt_aux, Q, σ, Function.comp_update]

/-- Helper for Lemma 10.13.2: the raw exterior section vanishes when two coordinates coincide,
so it is alternating. -/
private theorem exterior_power_section_alt_map_eq_zero_of_eq
    (hS : S.ShortExact) (n : ℕ) :
    ∀ (m : Fin (n + 1) → S.X₃) (i j : Fin (n + 1)),
      m i = m j → i ≠ j →
        exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n) m = 0 := by
  intro m i j hm hij
  let σ : S.X₃ → S.X₂ := Function.surjInv hS.moduleCat_surjective_g
  have hsame :
      S.g.hom ((σ ∘ m) i) = S.g.hom ((σ ∘ m) j) := by
    -- Applying `S.g.hom` to the chosen lifts recovers the original tuple in `S.X₃`.
    simp [σ, hm]
  -- Two equal images force the corresponding quotient class of the pure wedge to vanish.
  simpa [exterior_power_section_alt_aux, σ] using
    exterior_mkQ_ιMulti_eq_zero_of_same_image
      (R := R) (S := S) (hS := hS) (n := n)
      (m := σ ∘ m) (i := i) (j := j) hij hsame

/-- Helper for Lemma 10.13.2: the quotient-valued alternating section on exterior generators
coming from chosen lifts along `S.g.hom`. -/
private noncomputable def exterior_power_section_alt
    (hS : S.ShortExact) (n : ℕ) :
    S.X₃ [⋀^Fin (n + 1)]→ₗ[R]
      ((⋀[R]^(n + 1) S.X₂) ⧸ LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)) where
  toFun := exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n)
  map_update_add' := fun m i x y ↦
    exterior_power_section_alt_map_update_add
      (R := R) (S := S) (hS := hS) (n := n) m i x y
  map_update_smul' := fun m i r x ↦
    exterior_power_section_alt_map_update_smul
      (R := R) (S := S) (hS := hS) (n := n) m i r x
  map_eq_zero_of_eq' := fun m i j hm hij ↦
    exterior_power_section_alt_map_eq_zero_of_eq
      (R := R) (S := S) (hS := hS) (n := n) m i j hm hij

/-- Helper for Lemma 10.13.2: evaluating the alternating section on a tuple just returns the
quotient class of the wedge of the chosen `surjInv` lifts. -/
private theorem exterior_power_section_alt_apply
    (hS : S.ShortExact) (n : ℕ) (m : Fin (n + 1) → S.X₃) :
    exterior_power_section_alt (R := R) (S := S) (hS := hS) (n := n) m =
      exterior_power_section_alt_aux (R := R) (S := S) (hS := hS) (n := n) m :=
  rfl

/-- Helper for Lemma 10.13.2: the quotient-valued section on exterior powers obtained from the
alternating universal property. -/
private noncomputable def exterior_power_section
    (hS : S.ShortExact) (n : ℕ) :
    ⋀[R]^(n + 1) S.X₃ →ₗ[R]
      ((⋀[R]^(n + 1) S.X₂) ⧸ LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)) :=
  exteriorPower.alternatingMapLinearEquiv
    (exterior_power_section_alt (R := R) (S := S) (hS := hS) (n := n))

/-- Helper for Lemma 10.13.2: the descended exterior section sends pure generators from `S.X₂`
to their quotient classes. -/
private theorem exterior_power_section_ιMulti
    (hS : S.ShortExact) (n : ℕ) (m : Fin (n + 1) → S.X₂) :
    exterior_power_section (R := R) (S := S) (hS := hS) (n := n)
        (exteriorPower.ιMulti R (n + 1) (S.g.hom ∘ m)) =
      (Submodule.mkQ (LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)))
        (exteriorPower.ιMulti R (n + 1) m) := by
  let σ : S.X₃ → S.X₂ := Function.surjInv hS.moduleCat_surjective_g
  -- Evaluate the universal-property section on a pure wedge, then use pointwise quotient
  -- congruence because the chosen lifts differ from the original tuple by `range S.f.hom`.
  rw [exterior_power_section, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [exterior_power_section_alt_apply]
  -- The chosen lifts of `S.g.hom ∘ m` differ pointwise from `m` by `range S.f.hom`.
  simpa [exterior_power_section_alt_aux, σ] using
    exterior_mkQ_ιMulti_eq_of_pointwise_sub_mem_range
    (R := R) (S := S) (hS := hS) (n := n)
    (m := m) (m' := σ ∘ S.g.hom ∘ m)
    (fun i ↦ surjInv_sub_mem_range (R := R) (S := S) (hS := hS) (m i))

/-- Helper for Lemma 10.13.2: the descended exterior-power quotient map is injective. -/
private theorem exterior_power_range_desc_injective
    (hS : S.ShortExact) (n : ℕ) :
    Function.Injective (exterior_power_range_desc (hS := hS) (n := n)) := by
  -- Route correction: the exterior proof now uses the exact owner quotient row
  -- `leftTensorMap ⟶ mkQ (range leftTensorMap)`, so only injectivity of the descended comparison
  -- map remains to be shown.
  -- The factored section and its generator formula are the only source-faithful inputs needed.
  exact exterior_power_range_desc_injective_of_generator_formula
    (R := R) (S := S) (hS := hS) (n := n)
    (exterior_power_section (R := R) (S := S) (hS := hS) (n := n))
    (exterior_power_section_ιMulti (R := R) (S := S) (hS := hS) (n := n))

-- Proof sketch: combine `TensorProduct.lTensor_exact` and `LinearMap.lTensor_surjective` with the
-- standard exterior-power presentation by alternating tensors, then descend to the canonical owner
-- maps `exteriorPower.leftTensorMap` and `exteriorPower.map`.

/-- Lemma 10.13.2 (2), stated in degree `n + 1`: for an exact sequence `M₂ ⟶ M₁ ⟶ M ⟶ 0`,
the canonical sequence
`M₂ ⊗[R] ⋀[R]^n M₁ ⟶ ⋀[R]^(n + 1) M₁ ⟶ ⋀[R]^(n + 1) M ⟶ 0`
is exact. -/
@[stacks 00DO]
theorem exterior_power_exact_of_exact (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (exteriorPower.leftTensorMap n S.f.hom) (exteriorPower.map (n + 1) S.g.hom) ∧
      Function.Surjective (exteriorPower.map (n + 1) S.g.hom) := by
  refine ⟨?_, ?_⟩
  · -- Route correction: the exterior exactness proof is likewise reduced to injectivity of the
    -- descended quotient map `exterior_power_range_desc`, after which exactness transfers
    -- formally from `LinearMap.exact_map_mkQ_range`.
    let Q := LinearMap.range (exteriorPower.leftTensorMap n S.f.hom)
    have hdesc_injective :
        Function.Injective (exterior_power_range_desc (hS := hS) (n := n)) :=
      exterior_power_range_desc_injective (hS := hS) (n := n)
    have hdesc_comp :
        (exterior_power_range_desc (hS := hS) (n := n)).comp (Submodule.mkQ Q) =
          exteriorPower.map (n + 1) S.g.hom :=
      exterior_power_range_desc_comp_mkQ (hS := hS) (n := n)
    have hmkQ_zero :
        (Submodule.mkQ Q).comp (exteriorPower.leftTensorMap n S.f.hom) = 0 := by
      simpa [Q] using Function.Exact.linearMap_comp_eq_zero
        (LinearMap.exact_map_mkQ_range (exteriorPower.leftTensorMap n S.f.hom))
    -- As in the symmetric case, exactness is the formal consequence of exactness of
    -- `leftTensorMap ⟶ mkQ (range leftTensorMap)` plus injectivity of the descended comparison.
    refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · apply LinearMap.ext
      intro t
      have hdesc_on :
          (exterior_power_range_desc (hS := hS) (n := n))
              ((Submodule.mkQ Q) (exteriorPower.leftTensorMap n S.f.hom t)) =
            exteriorPower.map (n + 1) S.g.hom
              (exteriorPower.leftTensorMap n S.f.hom t) := by
        simpa [Q, LinearMap.comp_apply] using
          LinearMap.congr_fun hdesc_comp (exteriorPower.leftTensorMap n S.f.hom t)
      have hq :
          (Submodule.mkQ Q) (exteriorPower.leftTensorMap n S.f.hom t) = 0 := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hmkQ_zero t
      calc
        exteriorPower.map (n + 1) S.g.hom
            (exteriorPower.leftTensorMap n S.f.hom t) =
          (exterior_power_range_desc (hS := hS) (n := n))
            ((Submodule.mkQ Q) (exteriorPower.leftTensorMap n S.f.hom t)) := hdesc_on.symm
        _ = (exterior_power_range_desc (hS := hS) (n := n)) 0 := by
              rw [hq]
        _ = 0 := by simp
    · intro x hx
      have hxQ :
          (Submodule.mkQ Q) x = 0 := by
        apply hdesc_injective
        simpa [Q, hdesc_comp, LinearMap.comp_apply] using hx
      exact (Submodule.Quotient.mk_eq_zero Q).mp hxQ
  · -- Exterior powers already expose a surjectivity theorem for induced maps.
    exact exteriorPower.map_surjective (n := n + 1) hS.moduleCat_surjective_g

end
