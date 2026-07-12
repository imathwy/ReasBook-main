import Mathlib

noncomputable section

open scoped MatrixGroups

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-4: the alternating group `A₅` has order `60`. -/
theorem alternating_group_fin5_card_eq_sixty :
    Nat.card A5 = 60 := by
  -- Reduce to the computable cardinality of the finite subtype of even permutations.
  simpa using (show Fintype.card A5 = 60 by decide)

/-- Helper for Exercise 18-18.6-4: the quadratic roots of unity in `𝔽₅` are exactly `±1`, so
they form a two-element group. -/
theorem roots_of_unity_two_zmod_five_card_eq_two :
    Nat.card (rootsOfUnity 2 (ZMod 5)) = 2 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : NeZero (2 : ℕ) := ⟨by decide⟩
  -- In odd characteristic, `-1` is a primitive square root of unity.
  rw [Nat.card_eq_fintype_card]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.neg_one (p := 5) (by decide : 5 ≠ 2))

/-- Helper for Exercise 18-18.6-4: the special linear group `SL(2, 𝔽₅)` has order `120`. -/
theorem sl_two_zmod_five_card_eq_one_hundred_twenty :
    Nat.card (SL(2, ZMod 5)) = 120 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fintype (ZMod 5) := Fintype.ofFinite (ZMod 5)
  letI : DecidableEq (ZMod 5) := Classical.decEq _
  let detHom : GL (Fin 2) (ZMod 5) →* (ZMod 5)ˣ := Matrix.GeneralLinearGroup.det
  have hcard_gl : Nat.card (GL (Fin 2) (ZMod 5)) = 480 := by
    have hzmod_card : Fintype.card (ZMod 5) = 5 := ZMod.card 5
    calc
      Nat.card (GL (Fin 2) (ZMod 5))
          = ∏ i : Fin 2, (Fintype.card (ZMod 5) ^ 2 - Fintype.card (ZMod 5) ^ (i : ℕ)) := by
            simpa using Matrix.card_GL_field (𝔽 := ZMod 5) 2
      _ = ∏ i : Fin 2, (5 ^ 2 - 5 ^ (i : ℕ)) := by rw [hzmod_card]
      _ = 480 := by decide
  have hdet_surj : Function.Surjective detHom := by
    -- The diagonal matrix `diag(u,1)` has determinant `u`.
    intro u
    refine ⟨Matrix.GeneralLinearGroup.mk'' !![(u : ZMod 5), 0; 0, 1] ?_, ?_⟩
    · refine ⟨u, ?_⟩
      simp
    · apply Units.ext
      simp [detHom, Matrix.det_fin_two]
  have hcard_range : Nat.card detHom.range = 4 := by
    rw [MonoidHom.range_eq_top.2 hdet_surj]
    calc
      Nat.card ((⊤ : Subgroup (ZMod 5)ˣ)) = Nat.card ((ZMod 5)ˣ) := by
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = 4 := by
        simpa [Nat.card_eq_fintype_card] using
          (show Fintype.card (ZMod 5)ˣ = 4 by
            rw [ZMod.card_units_eq_totient 5, Nat.totient_prime (by decide : Nat.Prime 5)])
  have hcard_ker : Nat.card detHom.ker = Nat.card (SL(2, ZMod 5)) := by
    let e : detHom.ker ≃ SL(2, ZMod 5) :=
      { toFun := fun g ↦
          ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod 5)), by
            simpa [detHom] using congrArg Units.val g.2⟩
        invFun := fun g ↦
          ⟨(g : GL (Fin 2) (ZMod 5)), by
            simp [detHom]⟩
        left_inv := by
          intro g
          apply Subtype.ext
          exact Matrix.GeneralLinearGroup.ext fun i j ↦ rfl
        right_inv := by
          intro g
          apply Matrix.SpecialLinearGroup.ext
          intro i j
          rfl }
    exact Nat.card_congr e
  have hker_mul_range :
      Nat.card detHom.ker * Nat.card detHom.range = Nat.card (GL (Fin 2) (ZMod 5)) := by
    calc
      Nat.card detHom.ker * Nat.card detHom.range
          = Nat.card detHom.ker * detHom.ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card (GL (Fin 2) (ZMod 5)) := detHom.ker.card_mul_index
  have hcard_kernel : Nat.card detHom.ker = 120 := by
    have h : Nat.card detHom.ker * 4 = 480 := by
      rw [← hcard_range, hker_mul_range, hcard_gl]
    omega
  rw [← hcard_ker]
  exact hcard_kernel

/-- Helper for Exercise 18-18.6-4: the projective special linear group `PSL(2, 𝔽₅)` has order
`60`. -/
theorem psl_two_zmod_five_card_eq_sixty :
    Nat.card (PSL(2, ZMod 5)) = 60 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fintype (ZMod 5) := Fintype.ofFinite (ZMod 5)
  letI : DecidableEq (ZMod 5) := Classical.decEq _
  have hcenter : Nat.card (Subgroup.center (SL(2, ZMod 5))) = 2 := by
    let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := ZMod 5)
    calc
      Nat.card (Subgroup.center (SL(2, ZMod 5)))
          = Nat.card (rootsOfUnity (max (Fintype.card (Fin 2)) 1) (ZMod 5)) := by
              exact Nat.card_congr e.toEquiv
      _ = Nat.card (rootsOfUnity 2 (ZMod 5)) := by
            simp
      _ = 2 := roots_of_unity_two_zmod_five_card_eq_two
  have hmul :
      Nat.card (SL(2, ZMod 5)) =
        Nat.card (PSL(2, ZMod 5)) * Nat.card (Subgroup.center (SL(2, ZMod 5))) := by
    -- `PSL(2, 𝔽₅)` is the quotient of `SL(2, 𝔽₅)` by its center.
    simpa [Matrix.ProjectiveSpecialLinearGroup] using
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (SL(2, ZMod 5)))
  have h : Nat.card (PSL(2, ZMod 5)) * 2 = 120 := by
    rw [hcenter, sl_two_zmod_five_card_eq_one_hundred_twenty] at hmul
    simpa [mul_comm] using hmul.symm
  omega
