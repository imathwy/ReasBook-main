/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Suwan Wu, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part1

open scoped Pointwise

section Chap03
section Section11

/-- Hard-case separation: in the quotient by a submodule, a convex relatively open set `C`
can be strictly separated from a point in the affine span of its image but outside the image. -/
lemma exists_strictSep_point_of_mem_affineSpan_openIn_convex
    (n : Nat) (C : Set (Fin n → ℝ)) (D : Submodule ℝ (Fin n → ℝ))
    (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (hCrelopen :
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ C = U ∩ (affineSpan ℝ C : Set (Fin n → ℝ)))
    {m0 : Fin n → ℝ}
    (hq0S : D.mkQ m0 ∉ (D.mkQ '' C)) (hq0A : D.mkQ m0 ∈ affineSpan ℝ (D.mkQ '' C)) :
    ∃ f : StrongDual ℝ ((Fin n → ℝ) ⧸ D), ∀ c ∈ C, f (D.mkQ c) < f (D.mkQ m0) := by
  classical
  let Q := (Fin n → ℝ) ⧸ D
  let π : (Fin n → ℝ) →ₗ[ℝ] Q := D.mkQ
  let q0 : Q := π m0
  let S : Set Q := π '' C
  have hq0S' : q0 ∉ S := by simpa [q0, S, π] using hq0S
  have hq0A' : q0 ∈ affineSpan ℝ S := by simpa [q0, S, π] using hq0A
  rcases hCne with ⟨c0, hc0C⟩
  let s0 : Q := π c0
  have hs0S : s0 ∈ S := ⟨c0, hc0C, rfl⟩
  let A : AffineSubspace ℝ Q := affineSpan ℝ S
  have hq0A_A : q0 ∈ A := by simpa [A] using hq0A'
  have hs0A_A : s0 ∈ A := subset_affineSpan ℝ S hs0S
  let A0 : AffineSubspace ℝ (Fin n → ℝ) := affineSpan ℝ C
  let V0 : Submodule ℝ (Fin n → ℝ) := A0.direction
  let f0 : V0 →ₗ[ℝ] Q := π.comp V0.subtype
  let V : Submodule ℝ Q := Submodule.map π V0
  have hdir : A.direction = V := by
    -- Use `AffineSubspace.map_span` and `AffineSubspace.map_direction`.
    have hmap : A0.map π.toAffineMap = A := by
      simpa [A0, A, S] using (AffineSubspace.map_span (k := ℝ) (s := C) (f := π.toAffineMap))
    -- Now compare directions.
    simpa [V, V0, hmap] using (AffineSubspace.map_direction (s := A0) (f := π.toAffineMap))
  have hv0mem : q0 - s0 ∈ V := by
    have : q0 -ᵥ s0 ∈ A.direction := AffineSubspace.vsub_mem_direction hq0A_A hs0A_A
    simpa [vsub_eq_sub, hdir] using this
  let v0 : V := ⟨q0 - s0, hv0mem⟩
  -- Translate `C` to an open convex set in `V0`.
  let O0 : Set V0 := {v : V0 | ((v : Fin n → ℝ) + c0) ∈ C}
  have hO0open : IsOpen O0 := by
    simpa [O0, A0, V0] using
      (isOpen_translate_in_direction_of_relOpen (E := Fin n → ℝ) (C := C) hCrelopen (c0 := c0) hc0C)
  have hO0conv : Convex ℝ O0 := by
    intro x hx y hy a b ha hb hab
    have hxC : ((x : Fin n → ℝ) + c0) ∈ C := hx
    have hyC : ((y : Fin n → ℝ) + c0) ∈ C := hy
    have : a • ((x : Fin n → ℝ) + c0) + b • ((y : Fin n → ℝ) + c0) ∈ C :=
      hCconv hxC hyC ha hb hab
    -- Rewrite the convex combination as `(a • x + b • y) + c0`.
    have hcalc :
        a • ((x : Fin n → ℝ) + c0) + b • ((y : Fin n → ℝ) + c0) =
          ((a • x + b • y : V0) : Fin n → ℝ) + c0 := by
      -- Expand, collect the `c0` terms using `add_smul`, then use `a + b = 1`.
      calc
        a • ((x : Fin n → ℝ) + c0) + b • ((y : Fin n → ℝ) + c0) =
            (a • (x : Fin n → ℝ) + b • (y : Fin n → ℝ)) + (a • c0 + b • c0) := by
              simp [smul_add, add_assoc, add_left_comm, add_comm]
        _ = (a • (x : Fin n → ℝ) + b • (y : Fin n → ℝ)) + (a + b) • c0 := by
              simp [add_smul]
        _ = (a • (x : Fin n → ℝ) + b • (y : Fin n → ℝ)) + c0 := by
              simp [hab]
        _ = ((a • x + b • y : V0) : Fin n → ℝ) + c0 := by
              simp [add_assoc]
    have : ((a • x + b • y : V0) : Fin n → ℝ) + c0 ∈ C := by
      -- Rewrite the membership along `hcalc`.
      exact (by
        simpa using (hcalc ▸ this))
    simpa [O0] using this
  -- Push `O0` forward to an open convex set in `V`.
  let g : V0 →ₗ[ℝ] V :=
    { toFun := fun v => ⟨f0 v, by exact ⟨(v : Fin n → ℝ), v.2, rfl⟩⟩
      map_add' := by
        intro x y
        ext
        simp [f0]
      map_smul' := by
        intro r x
        ext
        simp [f0] }
  let T : Set V :=
    ((fun v : V0 => (⟨f0 v, by exact ⟨(v : Fin n → ℝ), v.2, rfl⟩⟩ : V)) '' O0)
  have hTopen : IsOpen T := isOpen_image_direction_mkQ_of_isOpen (C := C) (D := D) O0 hO0open
  have hTconv : Convex ℝ T := by
    -- `T` is the linear image of the convex set `O0`.
    simpa [T, g] using (hO0conv.linear_image g)
  have hv0not : v0 ∉ T := by
    intro hv0T
    rcases hv0T with ⟨v, hvO0, hvEq⟩
    have hvEq' : f0 v = q0 - s0 := by
      simpa [g, v0] using congrArg Subtype.val hvEq
    have hcC : ((v : Fin n → ℝ) + c0) ∈ C := by simpa [O0] using hvO0
    have hq0mem : q0 ∈ S := by
      refine ⟨(v : Fin n → ℝ) + c0, hcC, ?_⟩
      calc
        π ((v : Fin n → ℝ) + c0) = π (v : Fin n → ℝ) + π c0 := by simp [π, map_add]
        _ = f0 v + s0 := by simp [f0, s0]
        _ = (q0 - s0) + s0 := by simp [hvEq']
        _ = q0 := sub_add_cancel q0 s0
    exact hq0S' hq0mem
  -- Separate the open convex set `T` from the point `v0`.
  obtain ⟨fV, hfV⟩ := geometric_hahn_banach_open_point (E := V) hTconv hTopen hv0not
  -- Extend `fV` from the submodule `V` to the whole quotient space `Q`.
  obtain ⟨gQ, hgQ⟩ := LinearMap.exists_extend (p := V) (f := fV.toLinearMap)
  haveI : IsModuleTopology ℝ Q := by infer_instance
  let f : StrongDual ℝ Q :=
    { toLinearMap := gQ
      cont := IsModuleTopology.continuous_of_linearMap gQ }
  refine ⟨f, ?_⟩
  intro c hcC
  -- Build the translated direction element corresponding to `c - c0`.
  have hcA0 : c ∈ A0 := subset_affineSpan ℝ C hcC
  have hc0A0 : c0 ∈ A0 := subset_affineSpan ℝ C hc0C
  have hsub : c - c0 ∈ V0 := by
    simpa [V0, vsub_eq_sub] using (AffineSubspace.vsub_mem_direction hcA0 hc0A0)
  let v : V0 := ⟨c - c0, hsub⟩
  have hvO0 : v ∈ O0 := by
    -- `v + c0 = c`.
    simpa [O0, v, sub_add_cancel] using hcC
  have hvT : g v ∈ T := ⟨v, hvO0, rfl⟩
  have hltV : fV (g v) < fV v0 := hfV (g v) hvT
  -- Transfer the inequality to `f` on `Q`.
  have hcomp : ∀ w : V, f w = fV w := by
    intro w
    -- `gQ` agrees with `fV` on `V`.
    have : gQ (V.subtype w) = fV w := by
      -- from `hgQ : gQ.comp V.subtype = fV.toLinearMap`
      simpa using congrArg (fun h : V →ₗ[ℝ] ℝ => h w) hgQ
    simpa [f] using this
  have hltQ : f ((g v : V) : Q) < f (v0 : Q) := by
    simpa [hcomp] using hltV
  -- Rewrite the translated inequality as `f (π c) < f q0`.
  have : f (π c) < f q0 := by
    have h' := add_lt_add_left hltQ (f s0)
    have hsum_left :
        f ((g v : V) : Q) + f s0 = f (((g v : V) : Q) + s0) := by
      simp
    have hsum_right :
        f (v0 : Q) + f s0 = f ((v0 : Q) + s0) := by
      simp
    have h'' : f (((g v : V) : Q) + s0) < f ((v0 : Q) + s0) := by
      have h'' := h'
      rw [hsum_left, hsum_right] at h''
      exact h''
    -- Simplify the translated points.
    have hgv : ((g v : V) : Q) + s0 = π c := by
      -- `g v` is `π (c - c0)` and `s0 = π c0`.
      simp [g, f0, π, s0, v, map_sub, sub_add_cancel]
    have hv0 : (v0 : Q) + s0 = q0 := by
      simp [v0, q0, s0, sub_add_cancel]
    simpa [hgv, hv0] using h''
  -- Return the desired strict inequality.
  simpa [q0, π] using this

/-- **Key separation lemma for Theorem 11.2** (to be filled): in the quotient by `M.direction`,
the convex relatively-open set `C` can be strictly separated from the point corresponding to `M`. -/
lemma exists_strictSep_point_image_mkQ_of_disjoint_convex_relativelyOpen
    (n : Nat) (C : Set (Fin n → ℝ)) (M : AffineSubspace ℝ (Fin n → ℝ))
    (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (hCrelopen :
      ∃ U : Set (Fin n → ℝ), IsOpen U ∧ C = U ∩ (affineSpan ℝ C : Set (Fin n → ℝ)))
    {m0 : Fin n → ℝ} (hm0 : m0 ∈ M) (hCM : Disjoint C (M : Set (Fin n → ℝ))) :
    ∃ f : StrongDual ℝ ((Fin n → ℝ) ⧸ M.direction),
      (∀ c ∈ C, f (M.direction.mkQ c) < f (M.direction.mkQ m0)) ∨
        (∀ c ∈ C, f (M.direction.mkQ m0) < f (M.direction.mkQ c)) := by
  classical
  let D : Submodule ℝ (Fin n → ℝ) := M.direction
  let Q := (Fin n → ℝ) ⧸ D
  let π : (Fin n → ℝ) →ₗ[ℝ] Q := D.mkQ
  let S : Set Q := π '' C
  let q0 : Q := π m0
  have hq0S : q0 ∉ S := by
    simpa [D, π, S, q0] using (quotient_point_not_mem_image_of_disjoint (C := C) M hm0 hCM)
  have hSnonempty : S.Nonempty := hCne.image π
  have hSconv : Convex ℝ S := hCconv.linear_image π
  let A : AffineSubspace ℝ Q := affineSpan ℝ S
  by_cases hq0A : q0 ∈ A
  ·
    /- Hard case (`q0 ∈ affineSpan ℝ (π '' C)`):
    the set `S := π '' C` is convex and *relatively open* in its affine span `A := affineSpan ℝ S`,
    and `q0 ∉ S`. One should translate to the direction submodule `A.direction`, show the
    translated set is open there, apply `geometric_hahn_banach_open_point` to separate `0`,
    and extend the resulting functional from `A.direction` to `Q`.
    -/
    obtain ⟨f, hf⟩ :=
      exists_strictSep_point_of_mem_affineSpan_openIn_convex n C D hCne hCconv hCrelopen hq0S
        (by simpa [A, S, π, q0] using hq0A)
    exact ⟨f, Or.inl hf⟩
  · -- If `q0` is outside `affineSpan ℝ S`, a functional constant on `affineSpan ℝ S` suffices.
    have hq0A' : q0 ∉ affineSpan ℝ S := by simpa [A] using hq0A
    obtain ⟨f, hf⟩ :=
      exists_strictSep_point_of_not_mem_affineSpan (E := Q) (S := S) hSnonempty hq0A'
    refine ⟨f, Or.inl ?_⟩
    intro c hcC
    exact hf (π c) ⟨c, hcC, rfl⟩

/-- A continuous linear functional on `ℝ^n` is determined by its values on the coordinate vectors. -/
lemma strongDual_apply_eq_sum_mul_single {n : Nat} (g : StrongDual ℝ (Fin n → ℝ))
    (x : Fin n → ℝ) :
    g x =
      ∑ i : Fin n,
        x i * g (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ)) := by
  classical
  have hx :
      (∑ i : Fin n, Pi.single (M := fun _ : Fin n => ℝ) i (x i)) = x := by
    simpa using
      (LinearMap.sum_single_apply (v := x) :
        (∑ i : Fin n, Pi.single (M := fun _ : Fin n => ℝ) i (x i)) = x)
  rw [← hx]
  simp only [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hsingle :
      Pi.single (M := fun _ : Fin n => ℝ) i (x i) =
        (x i) • Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ) := by
    ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.single, h]
  simp [hsingle, smul_eq_mul]

/-- Convert a continuous linear functional on `ℝ^n` into a dotProduct against a vector. -/
lemma strongDual_apply_eq_dotProduct {n : Nat} (g : StrongDual ℝ (Fin n → ℝ)) :
    ∀ x : Fin n → ℝ, g x = x ⬝ᵥ (fun i => g (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))) := by
  classical
  intro x
  -- both sides are the same coordinate sum
  simpa [dotProduct] using (strongDual_apply_eq_sum_mul_single g x)

/-- Theorem 11.2: Let `C` be a non-empty relatively open convex set in `R^n`, and let `M` be a
non-empty affine set in `R^n` not meeting `C`. Then there exists a hyperplane `H` containing
`M`, such that one of the open half-spaces associated with `H` contains `C`. -/
theorem exists_hyperplane_contains_affine_of_convex_relativelyOpen
    (n : Nat) (C : Set (Fin n → Real)) (M : AffineSubspace Real (Fin n → Real))
    (hCne : C.Nonempty) (hCconv : Convex Real C)
    (hCrelopen :
      ∃ U : Set (Fin n → Real), IsOpen U ∧ C = U ∩ (affineSpan Real C : Set (Fin n → Real)))
    (hMne : (M : Set (Fin n → Real)).Nonempty) (hCM : Disjoint C (M : Set (Fin n → Real))) :
    ∃ H : Set (Fin n → Real),
      (M : Set (Fin n → Real)) ⊆ H ∧
        ∃ (b : Fin n → Real) (β : Real),
          b ≠ 0 ∧
            H = {x : Fin n → Real | x ⬝ᵥ b = β} ∧
              (C ⊆ {x : Fin n → Real | x ⬝ᵥ b < β} ∨
                C ⊆ {x : Fin n → Real | β < x ⬝ᵥ b}) := by
  classical
  rcases hMne with ⟨m0, hm0⟩
  -- Work in the quotient by the direction of `M`, where `M` becomes a single point.
  let D : Submodule ℝ (Fin n → ℝ) := M.direction
  let Q := (Fin n → ℝ) ⧸ D
  let π : (Fin n → ℝ) →ₗ[ℝ] Q := D.mkQ
  have hπcont : Continuous π := π.continuous_of_finiteDimensional
  let πL : (Fin n → ℝ) →L[ℝ] Q := { toLinearMap := π, cont := hπcont }

  obtain ⟨f, hfsep⟩ :=
    exists_strictSep_point_image_mkQ_of_disjoint_convex_relativelyOpen n C M hCne hCconv hCrelopen
      hm0 hCM
  let g : StrongDual ℝ (Fin n → ℝ) := f.comp πL
  have hg_dot :
      ∀ x : Fin n → ℝ,
        g x = x ⬝ᵥ (fun i => g (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))) :=
    strongDual_apply_eq_dotProduct g
  let b : Fin n → ℝ := fun i => g (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
  let β : ℝ := g m0

  have hg_ne0 : g ≠ 0 := by
    intro hg0
    rcases hCne with ⟨c0, hc0⟩
    cases hfsep with
    | inl hlt =>
        have : g c0 < g m0 := by
          simpa [g, πL, π, Submodule.mkQ_apply] using hlt c0 hc0
        simp [hg0] at this
    | inr hgt =>
        have : g m0 < g c0 := by
          simpa [g, πL, π, Submodule.mkQ_apply] using hgt c0 hc0
        simp [hg0] at this

  have hb_ne0 : b ≠ 0 := by
    intro hb0
    apply hg_ne0
    ext x
    have : g x = x ⬝ᵥ b := by simpa [b] using (hg_dot x)
    simp [this, hb0]

  refine ⟨{x : Fin n → ℝ | x ⬝ᵥ b = β}, ?_, b, β, hb_ne0, rfl, ?_⟩
  · intro m hmM
    have hsub : m - m0 ∈ D := by
      simpa [D, vsub_eq_sub] using (AffineSubspace.vsub_mem_direction hmM hm0)
    have hEq' : (Submodule.Quotient.mk m : (Fin n → ℝ) ⧸ D) = Submodule.Quotient.mk m0 :=
      (Submodule.Quotient.eq (p := D)).2 hsub
    have hEq : π m = π m0 := by simpa [π, Submodule.mkQ_apply] using hEq'
    have hEqL : πL m = πL m0 := by
      simpa [πL] using hEq
    have : g m = g m0 := by
      -- `g` is `f ∘ π`
      simpa [g] using congrArg f hEqL
    -- rewrite `g` as dotProduct against `b`
    have hg_m : g m = m ⬝ᵥ b := by simpa [b] using (hg_dot m)
    have hg_m0 : g m0 = m0 ⬝ᵥ b := by simpa [b] using (hg_dot m0)
    -- finish
    simpa [β, hg_m, hg_m0, this]
  · cases hfsep with
    | inl hlt =>
        left
        intro c hcC
        have : g c < β := by
          -- transport the strict inequality from the quotient
          simpa [g, πL, π, β, Submodule.mkQ_apply] using hlt c hcC
        have hg_c : g c = c ⬝ᵥ b := by simpa [b] using (hg_dot c)
        simpa [hg_c, β] using this
    | inr hgt =>
        right
        intro c hcC
        have : β < g c := by
          simpa [g, πL, π, β, Submodule.mkQ_apply] using hgt c hcC
        have hg_c : g c = c ⬝ᵥ b := by simpa [b] using (hg_dot c)
        simpa [hg_c, β] using this

/-- Minkowski subtraction is Minkowski addition with pointwise negation. -/
lemma set_sub_eq_add_neg {E : Type*} [AddGroup E] (A B : Set E) : A - B = A + (-B) := by
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, -b, ?_, ?_⟩
    · simpa using hb
    · simp [sub_eq_add_neg]
  · rintro ⟨a, ha, c, hc, rfl⟩
    have hc' : -c ∈ B := by simpa using hc
    refine ⟨a, ha, -c, hc', ?_⟩
    simp [sub_eq_add_neg]

/-- Pointwise negation equals scalar multiplication by `-1`. -/
lemma neg_set_eq_smul {E : Type*} [AddCommGroup E] [Module Real E] (C : Set E) :
    -C = ((-1 : Real) • C) := by
  ext x
  constructor
  · intro hx
    have hx' : -x ∈ C := by simpa using hx
    refine ⟨-x, hx', ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/-- A continuous linear equivalence maps intrinsic interiors. -/
lemma ContinuousLinearEquiv.image_intrinsicInterior {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (s : Set E) :
    intrinsicInterior 𝕜 (e '' s) = e '' intrinsicInterior 𝕜 s := by
  classical
  -- Work in the affine spans, where `intrinsicInterior` is ordinary `interior`.
  let A : AffineSubspace 𝕜 E := affineSpan 𝕜 s
  let B : AffineSubspace 𝕜 F := affineSpan 𝕜 (e '' s)
  have hAB : ∀ x : E, x ∈ A ↔ e x ∈ B := by
    intro x
    -- Use `B = A.map e` and the injectivity of `e`.
    have hmap : A.map e.toAffineEquiv.toAffineMap = B := by
      simpa [A, B] using (AffineSubspace.map_span (k := 𝕜) (f := e.toAffineEquiv.toAffineMap) s)
    -- `x ∈ A ↔ e x ∈ A.map e`
    simpa [hmap] using
      (AffineSubspace.mem_map_iff_mem_of_injective (f := e.toAffineEquiv.toAffineMap) (x := x)
          (s := A) (hf := e.injective)).symm
  let f : A ≃ₜ B :=
    (e.toHomeomorph.subtype (p := fun x : E => x ∈ A) (q := fun y : F => y ∈ B) hAB)
  have hcoe : (fun y : B => (y : F)) = fun y => e ((f.symm y : A) : E) := by
    ext y
    -- `f.symm` is induced by `e.symm` on the underlying points.
    simp [f, Homeomorph.subtype]
  have hpre :
      ((↑) : B → F) ⁻¹' (e '' s) = f.symm ⁻¹' (((↑) : A → E) ⁻¹' s) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, hxy⟩
      -- `e (f.symm y) = y`, so `f.symm y` is `e.symm y`.
      have : (f.symm y : A) = ⟨x, by
          have hxA : x ∈ A := subset_affineSpan (k := 𝕜) (s := s) hx
          simpa [A] using hxA⟩ := by
        ext
        -- underlying point
        have : e x = (y : F) := by simp [hxy]
        -- apply `e.symm` on both sides
        simpa using (congrArg e.symm this).symm
      have hxpre : (f.symm y : E) ∈ s := by
        -- the underlying point of `f.symm y` is `x`
        simpa [this] using hx
      simpa [hcoe] using hxpre
    · intro hy
      -- `f.symm y ∈ s` implies `y = e (f.symm y) ∈ e '' s`.
      have : e ((f.symm y : A) : E) ∈ e '' s :=
        ⟨(f.symm y : E), by simpa using hy, rfl⟩
      simpa [hcoe] using this
  -- Now translate the definition of `intrinsicInterior` through `f`.
  calc
    intrinsicInterior 𝕜 (e '' s)
        = ((↑) : B → F) '' interior (((↑) : B → F) ⁻¹' (e '' s)) := by
            simp [intrinsicInterior, B]
    _ = (fun y : B => e ((f.symm y : A) : E)) '' interior (((↑) : B → F) ⁻¹' (e '' s)) := by
          simp [hcoe]
    _ = e '' (((↑) : A → E) '' (f.symm '' interior (((↑) : B → F) ⁻¹' (e '' s)))) := by
          simp [Set.image_image]
    _ = e '' (((↑) : A → E) '' interior (((↑) : A → E) ⁻¹' s)) := by
          -- Use that `f.symm` is a homeomorphism, and rewrite the pulled-back set via `hpre`.
          have :
              f.symm '' interior (((↑) : B → F) ⁻¹' (e '' s)) =
                interior (((↑) : A → E) ⁻¹' s) := by
            -- `f.symm` maps `interior` to `interior` of the image.
            have himage :
                f.symm '' interior (((↑) : B → F) ⁻¹' (e '' s)) =
                  interior (f.symm '' (((↑) : B → F) ⁻¹' (e '' s))) := by
              simpa using (f.symm.image_interior (((↑) : B → F) ⁻¹' (e '' s)))
            -- and `f.symm '' preimage = preimage` using `hpre`.
            have himage2 :
                f.symm '' (((↑) : B → F) ⁻¹' (e '' s)) = (((↑) : A → E) ⁻¹' s) := by
              -- since `f` is an equivalence, `f.symm '' t = f ⁻¹' t`
              -- and `hpre` is exactly that preimage.
              ext x
              constructor
              · rintro ⟨y, hy, rfl⟩
                simpa [hpre] using hy
              · intro hx
                refine ⟨f x, ?_, by simp⟩
                simpa [hpre] using hx
            simpa [himage2] using himage
          simp [this]
    _ = e '' intrinsicInterior 𝕜 s := by
          simp [intrinsicInterior, A]

end Section11
end Chap03
