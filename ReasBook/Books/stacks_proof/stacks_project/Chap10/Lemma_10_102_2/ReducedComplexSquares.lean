import stacks_proof.stacks_project.Chap10.Lemma_10_102_2.ReducedComplexCore

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: the reduced differential still squares to zero. -/
theorem reduced_complex_of_normalized_middle_d_sq_upper_branch
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R)) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (i.1 + 2) ≫
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (i.1 + 1) = 0 := by
  -- Rewrite the two supported differentials and cancel the only transport at the interface.
  rw [reduced_complex_of_normalized_middle_d_eq_generic (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) (j := i.1 + 2)
    (by omega) (by omega) (by omega)]
  rw [reduced_complex_of_normalized_middle_d_eq_upper (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff)]
  simp_rw [Category.assoc]
  have htransport :
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_generic
            (R := R) (ns := ns) (nt := nt) D i
            (j := i.1 + 2) (by omega) (by omega)).symm ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) =
        𝟙 _ :=
    reduced_complex_of_normalized_middle_generic_upper_transport (R := R) (ns := ns) (nt := nt)
      D i
  have hrewrite :
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_generic
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
        D.toChainComplex.d (i.1 + 3) (i.1 + 2) ≫
          eqToHom
            (reduced_complex_of_normalized_middle_object_eq_target_of_generic
              (R := R) (ns := ns) (nt := nt) D i
              (j := i.1 + 2) (by omega) (by omega)).symm ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
              D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
                (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm =
        eqToHom
            (reduced_complex_of_normalized_middle_object_eq_source_of_generic
              (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
          D.toChainComplex.d (i.1 + 3) (i.1 + 2) ≫
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                    (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm := by
    calc
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_generic
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
        D.toChainComplex.d (i.1 + 3) (i.1 + 2) ≫
          eqToHom
            (reduced_complex_of_normalized_middle_object_eq_target_of_generic
              (R := R) (ns := ns) (nt := nt) D i
              (j := i.1 + 2) (by omega) (by omega)).symm ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
              D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
                (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_generic
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
            D.toChainComplex.d (i.1 + 3) (i.1 + 2) ≫
              (eqToHom
                (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                  (R := R) (ns := ns) (nt := nt) D i
                  (j := i.1 + 2) (by omega) (by omega)).symm ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                    (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl)) ≫
                D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
                  (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                    eqToHom
                      (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                        (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm := by
            simp [Category.assoc]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_generic
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
            D.toChainComplex.d (i.1 + 3) (i.1 + 2) ≫ 𝟙 _ ≫
              D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
                (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm := by
            rw [htransport]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_generic
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
            D.toChainComplex.d (i.1 + 3) (i.1 + 2) ≫
              D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
                (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm := by
            simp [Category.assoc]
  rw [hrewrite]
  -- What remains is the inherited `d ≫ d = 0`, postcomposed with the upper tail projection.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        eqToHom
            (reduced_complex_of_normalized_middle_object_eq_source_of_generic
              (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 2) (by omega) (by omega)) ≫
          k ≫ (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm)
      (D.toChainComplex.d_comp_d (i.1 + 3) (i.1 + 2) (i.1 + 1))

/-- Helper for Lemma 10.102.2: away from the four supported interfaces, the reduced differential
still squares to zero by inheritance from the original complex. -/
theorem reduced_complex_of_normalized_middle_d_sq_middle_branch
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _)) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (i.1 + 1) ≫
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff i.1 = 0 := by
  -- Rewrite the two supported branch formulas and isolate the only transport at their interface.
  rw [reduced_complex_of_normalized_middle_d_eq_upper (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff)]
  rw [reduced_complex_of_normalized_middle_d_eq_middle (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff)]
  simp_rw [Category.assoc]
  have htransport :
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_middle
            (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) =
        𝟙 _ :=
    reduced_complex_of_normalized_middle_upper_middle_transport (R := R) (ns := ns) (nt := nt)
      D i
  have hrewrite :
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
          (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm ≫
              eqToHom
                (reduced_complex_of_normalized_middle_object_eq_source_of_middle
                  (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) ≫
                tailDiff ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm =
        eqToHom
            (reduced_complex_of_normalized_middle_object_eq_source_of_upper
              (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
          D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
            D.toChainComplex.d (i.1 + 1) i.1 ≫
              (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                    (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
    calc
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
          (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm ≫
              eqToHom
                (reduced_complex_of_normalized_middle_object_eq_source_of_middle
                  (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) ≫
                tailDiff ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
                (eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_upper
                    (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_source_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl)) ≫
                  tailDiff ≫
                    eqToHom
                      (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                        (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
            simp [Category.assoc]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫ 𝟙 _ ≫
                tailDiff ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
            rw [htransport]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              (D.termIso i.succ).hom ≫
                (eSource.hom ≫ biprod.fst ≫ tailDiff) ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
            simp [Category.assoc]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              (D.termIso i.succ).hom ≫
                (ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.fst) ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
            rw [← normalized_middle_tail_projection (R := R) (D := D) (i := i)
              (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) hmid]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              D.toChainComplex.d (i.1 + 1) i.1 ≫
                (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                      (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  eqToHom
                      (reduced_complex_of_normalized_middle_object_eq_source_of_upper
                        (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
                    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
                      k ≫ eTarget.hom ≫ biprod.fst ≫
                        eqToHom
                          (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                            (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm)
                (termIso_hom_comp_diffAt (D := D) (i := i))
  rw [hrewrite]
  -- What remains is the inherited `d ≫ d = 0`, postcomposed with the target-tail projection.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        eqToHom
            (reduced_complex_of_normalized_middle_object_eq_source_of_upper
              (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
          k ≫ (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_middle
                (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm)
      (D.toChainComplex.d_comp_d (i.1 + 2) (i.1 + 1) i.1)

/-- Helper for Lemma 10.102.2: at the lower supported interface, the middle tail differential
followed by the lower inherited differential is zero. -/
theorem reduced_complex_of_normalized_middle_d_sq_lower_interface_branch
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _))
    {j : ℕ}
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (j + 1) ≫
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j = 0 := by
  have hSourceMiddle :
      reduced_complex_of_normalized_middle_object
          (R := R) (ns := ns) (nt := nt) (D := D) i (j + 2) =
        ModuleCat.of R (Fin ns → R) := by
    -- This is the source object of the middle branch, rewritten using `j + 1 = i`.
    simpa [Nat.add_assoc] using
      reduced_complex_of_normalized_middle_object_eq_source_of_middle
        (R := R) (ns := ns) (nt := nt) D i (j := j + 1) hLower
  have hTargetMiddle :
      reduced_complex_of_normalized_middle_object
          (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
        ModuleCat.of R (Fin nt → R) := by
    -- The target object of that same middle branch is the split target tail module.
    simpa using
      reduced_complex_of_normalized_middle_object_eq_target_of_middle
        (R := R) (ns := ns) (nt := nt) D i (j := j + 1) hLower
  have hUpperMid : j + 1 ≠ i.1 + 1 := by
    omega
  have hLowerMid : j + 2 ≠ i.1 := by
    omega
  have hMiddle :
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
          (eSource := eSource) (eTarget := eTarget) tailDiff (j + 1) =
        eqToHom hSourceMiddle ≫ tailDiff ≫ eqToHom hTargetMiddle.symm := by
    -- At index `j + 1`, the defining `if` picks the middle branch directly.
    simp [reduced_complex_of_normalized_middle_d, hUpperMid, hLower, hLowerMid,
      hSourceMiddle, hTargetMiddle, Nat.add_assoc]
  -- Rewrite the middle branch at index `j + 1` and the lower branch at index `j`, then cancel
  -- the unique transport sitting between the two supported formulas.
  rw [hMiddle]
  rw [reduced_complex_of_normalized_middle_d_eq_lower (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) (j := j) hLower]
  simp_rw [Category.assoc]
  have htransport :
      eqToHom hTargetMiddle.symm ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLower) =
        𝟙 _ := by
    -- The middle target and lower source are two descriptions of the same split target term.
    simpa using
      reduced_complex_of_normalized_middle_middle_lower_transport
        (R := R) (ns := ns) (nt := nt) D i hLower
  have hrewrite :
      eqToHom hSourceMiddle ≫
        tailDiff ≫
          eqToHom hTargetMiddle.symm ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                (R := R) (ns := ns) (nt := nt) D i hLower) ≫
              biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                D.toChainComplex.d i.1 j ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                      (R := R) (ns := ns) (nt := nt) D i hLower).symm =
        eqToHom hSourceMiddle ≫
          biprod.inl ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫
            D.toChainComplex.d (i.1 + 1) i.1 ≫
              D.toChainComplex.d i.1 j ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                    (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
    -- Convert the middle tail map back to the original differential and then expose `d ≫ d`.
    calc
      eqToHom hSourceMiddle ≫
        tailDiff ≫
          eqToHom hTargetMiddle.symm ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                (R := R) (ns := ns) (nt := nt) D i hLower) ≫
              biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                D.toChainComplex.d i.1 j ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                      (R := R) (ns := ns) (nt := nt) D i hLower).symm =
          eqToHom hSourceMiddle ≫
            tailDiff ≫
              (eqToHom hTargetMiddle.symm ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                    (R := R) (ns := ns) (nt := nt) D i hLower)) ≫
                biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                  D.toChainComplex.d i.1 j ≫
                    eqToHom
                      (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                        (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
            simp [Category.assoc]
      _ =
          eqToHom hSourceMiddle ≫
            tailDiff ≫ 𝟙 _ ≫
              biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                D.toChainComplex.d i.1 j ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                      (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
            rw [htransport]
      _ =
          eqToHom hSourceMiddle ≫
            tailDiff ≫ biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
              D.toChainComplex.d i.1 j ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                    (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
            simp [Category.assoc]
      _ =
          eqToHom hSourceMiddle ≫
            biprod.inl ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
              (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 j ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                    (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  eqToHom hSourceMiddle ≫ k ≫ (D.termIso i.castSucc).inv ≫
                    D.toChainComplex.d i.1 j ≫
                      eqToHom
                        (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                          (R := R) (ns := ns) (nt := nt) D i hLower).symm)
                (normalized_middle_tail_inclusion (R := R) (D := D) (i := i)
                  (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) hmid)
      _ =
          eqToHom hSourceMiddle ≫
            biprod.inl ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫
              D.toChainComplex.d (i.1 + 1) i.1 ≫ D.toChainComplex.d i.1 j ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                    (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  eqToHom hSourceMiddle ≫
                    biprod.inl ≫ eSource.inv ≫ k ≫ D.toChainComplex.d i.1 j ≫
                      eqToHom
                        (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                          (R := R) (ns := ns) (nt := nt) D i hLower).symm)
                (diffAt_comp_termIso_inv (D := D) (i := i))
  rw [hrewrite]
  -- The remaining composite is the original `d ≫ d = 0`, precomposed and postcomposed with the
  -- lower-interface splitting maps.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        eqToHom hSourceMiddle ≫
          biprod.inl ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫ k ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                (R := R) (ns := ns) (nt := nt) D i hLower).symm)
      (D.toChainComplex.d_comp_d (i.1 + 1) i.1 j)

/-- Helper for Lemma 10.102.2: below the supported interface, the reduced differential is just
the inherited differential of `D`, so the lower-to-generic composite is zero. -/
theorem reduced_complex_of_normalized_middle_d_sq_lower_generic_branch
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    {j : ℕ}
    (hLower : j + 2 = i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (j + 1) ≫
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j = 0 := by
  -- Rewrite the lower and generic branch formulas and cancel the only transport across the
  -- interface.
  have hLowerStep : (j + 1) + 1 = i.1 := by
    simpa [Nat.add_assoc] using hLower
  have hUpper : j ≠ i.1 + 1 := by
    omega
  have hMid : j ≠ i.1 := by
    omega
  have hNotLower : j + 1 ≠ i.1 := by
    omega
  rw [reduced_complex_of_normalized_middle_d_eq_lower (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) (j := j + 1) hLowerStep]
  rw [reduced_complex_of_normalized_middle_d_eq_generic (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) (j := j)
    hUpper hMid hNotLower]
  simp_rw [Category.assoc]
  have htransport :
      eqToHom
          ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
            (R := R) (ns := ns) (nt := nt) D i (j := j + 1)
            (by simpa [Nat.add_assoc] using hLower)).symm) ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_generic
            (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)) =
        𝟙 _ :=
    reduced_complex_of_normalized_middle_lower_generic_transport (R := R) (ns := ns)
      (nt := nt) D i hLower
  have hrewrite :
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
        biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 (j + 1) ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                (R := R) (ns := ns) (nt := nt) D i (j := j + 1)
                (by simpa [Nat.add_assoc] using hLower)).symm ≫
              eqToHom
                (reduced_complex_of_normalized_middle_object_eq_source_of_generic
                  (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)) ≫
                D.toChainComplex.d (j + 1) j ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                      (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm =
        eqToHom
            (reduced_complex_of_normalized_middle_object_eq_source_of_lower
              (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
          biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
            D.toChainComplex.d i.1 (j + 1) ≫
              D.toChainComplex.d (j + 1) j ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                    (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm := by
    calc
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
        biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 (j + 1) ≫
            eqToHom
              (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                (R := R) (ns := ns) (nt := nt) D i (j := j + 1)
                (by simpa [Nat.add_assoc] using hLower)).symm ≫
              eqToHom
                (reduced_complex_of_normalized_middle_object_eq_source_of_generic
                  (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)) ≫
                D.toChainComplex.d (j + 1) j ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                      (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
            biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
              D.toChainComplex.d i.1 (j + 1) ≫
                (eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                    (R := R) (ns := ns) (nt := nt) D i (j := j + 1)
                    (by simpa [Nat.add_assoc] using hLower)).symm ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_source_of_generic
                      (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega))) ≫
                  D.toChainComplex.d (j + 1) j ≫
                    eqToHom
                      (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                        (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm := by
            simp [Category.assoc]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
            biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
              D.toChainComplex.d i.1 (j + 1) ≫ 𝟙 _ ≫
                D.toChainComplex.d (j + 1) j ≫
                  eqToHom
                    (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                      (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm := by
            rw [htransport]
      _ =
          eqToHom
              (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
            biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
              D.toChainComplex.d i.1 (j + 1) ≫ D.toChainComplex.d (j + 1) j ≫
                eqToHom
                  (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                    (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm := by
            simp [Category.assoc]
  rw [hrewrite]
  -- The remaining composite is inherited from `D` below the support.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦
        eqToHom
            (reduced_complex_of_normalized_middle_object_eq_source_of_lower
              (R := R) (ns := ns) (nt := nt) D i hLowerStep) ≫
          biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
            k ≫
              eqToHom
                (reduced_complex_of_normalized_middle_object_eq_target_of_generic
                  (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)).symm)
      (by simpa [hLower] using D.toChainComplex.d_comp_d i.1 (j + 1) j)

/-- Helper for Lemma 10.102.2: away from the four supported interfaces, the reduced differential
still squares to zero by inheritance from the original complex. -/
theorem reduced_complex_of_normalized_middle_d_sq_generic_branch
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (j : ℕ)
    (hUpper : j ≠ i.1 + 1) (hMid : j ≠ i.1) (hLower : j + 1 ≠ i.1)
    (hLower' : j + 2 ≠ i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (j + 1) ≫
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j = 0 := by
  -- On the generic remainder, both reduced differentials are inherited unchanged from `D`.
  rw [reduced_complex_of_normalized_middle_d_eq_generic (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) (j := j + 1)
    (by omega) (by omega) hLower']
  rw [reduced_complex_of_normalized_middle_d_eq_generic (R := R) (ns := ns) (nt := nt) D i
    (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) (j := j)
    hUpper hMid hLower]
  simp_rw [Category.assoc]
  simpa [Category.assoc] using D.toChainComplex.d_comp_d (j + 2) (j + 1) j

/-- Helper for Lemma 10.102.2: the reduced differential still squares to zero. -/
theorem reduced_complex_of_normalized_middle_d_sq
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _))
    (j : ℕ) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (j + 1) ≫
      reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j = 0 := by
  -- Route correction: dispatch the four supported interfaces explicitly, then fall back to the
  -- generic inherited branch away from the support.
  by_cases hUpper : j = i.1 + 1
  · subst hUpper
    -- The top supported interface is exactly the generic-to-upper branch handled separately.
    exact reduced_complex_of_normalized_middle_d_sq_upper_branch
      (R := R) (ns := ns) (nt := nt) D i eSource eTarget tailDiff
  · by_cases hMid : j = i.1
    · subst hMid
      -- The middle supported interface is the upper-then-tail branch proved separately.
      exact reduced_complex_of_normalized_middle_d_sq_middle_branch
        (R := R) (ns := ns) (nt := nt) D i eSource eTarget tailDiff hmid
    · by_cases hLower : j + 1 = i.1
      · -- The lower supported interface is the tail-then-lower branch proved separately.
        exact reduced_complex_of_normalized_middle_d_sq_lower_interface_branch
          (R := R) (ns := ns) (nt := nt) D i eSource eTarget tailDiff hmid hLower
      · by_cases hLower' : j + 2 = i.1
        · -- The last supported interface below the split degrees is again handled separately.
          exact reduced_complex_of_normalized_middle_d_sq_lower_generic_branch
            (R := R) (ns := ns) (nt := nt) D i eSource eTarget tailDiff hLower'
        · -- Away from the four supported interfaces, both factors are inherited from `D`.
          exact reduced_complex_of_normalized_middle_d_sq_generic_branch
            (R := R) (ns := ns) (nt := nt) D i eSource eTarget tailDiff j
            hUpper hMid hLower hLower'

end FiniteFreeComplex

end
