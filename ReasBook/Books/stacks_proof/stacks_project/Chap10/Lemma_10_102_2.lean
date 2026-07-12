import StacksProject_2024.Chap10.Lemma_10_102_2.Index

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}

/-- Helper for Lemma 10.102.2: in a lower adjacent branch, the `fst` projection in source degree
`k + 1` transports to the supported `i`-degree target-tail projection. -/
private theorem normalized_middle_component_iso_hom_comp_fst_castSucc_comp_lower_source
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hsucc : D.rank i.succ = ns + 1)
    (hcast : D.rank i.castSucc = nt + 1)
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
    {k : ℕ}
    (hLower : k + 1 = i.1) :
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid (k + 1)).hom ≫
      (biprodChainFst
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).f (k + 1) ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower) =
    eqToHom (by rw [hLower] : D.toChainComplex.X (k + 1) = D.toChainComplex.X i.1) ≫
      (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst := by
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  let z : (j : ℕ) → D.toChainComplex.X j ⟶ C'.toChainComplex.X j := fun j =>
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
      eSource eTarget tailDiff hmid j).hom ≫
      (biprodChainFst C'.toChainComplex (identityDiskComplex (R := R) i)).f j
  -- Transport the whole projected component from degree `k + 1` to the supported degree `i`.
  have hnaturality := CategoryTheory.eqToHom_naturality z hLower
  have hcastProj := normalized_middle_component_iso_hom_comp_fst_castSucc (R := R) (D := D)
    (i := i) hsucc hcast eSource eTarget tailDiff hmid
  calc
    z (k + 1) ≫ eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower) =
      z (k + 1) ≫
        (eqToHom (by rw [hLower] : C'.toChainComplex.X (k + 1) = C'.toChainComplex.X i.1) ≫
          eqToHom (reduced_complex_of_normalized_middle_X_eq_castSucc (R := R) (D := D)
            (i := i) hsucc hcast eSource eTarget tailDiff hmid)) := by
        -- The lower source identification is the degree transport followed by the canonical
        -- target-tail identification.
        simp [CategoryTheory.eqToHom_trans]
    _ = (eqToHom (by rw [hLower] : D.toChainComplex.X (k + 1) = D.toChainComplex.X i.1) ≫
          z i.1) ≫
        eqToHom (reduced_complex_of_normalized_middle_X_eq_castSucc (R := R) (D := D)
          (i := i) hsucc hcast eSource eTarget tailDiff hmid) := by
        -- Naturality moves the source-side transport across the component map.
        simpa [Category.assoc, C', z] using
          congrArg
            (fun m => m ≫
              eqToHom (reduced_complex_of_normalized_middle_X_eq_castSucc (R := R)
                (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid))
            hnaturality
    _ = eqToHom (by rw [hLower] : D.toChainComplex.X (k + 1) = D.toChainComplex.X i.1) ≫
        (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst := by
        -- The supported `castSucc` projection then cancels its target-tail transport.
        simp only [z, C']
        rw [hcastProj]
        simp [Category.assoc]

/-- Helper for Lemma 10.102.2: after postcomposing with the reduced-complex projection, the
componentwise normalized split satisfies the chain-map naturality square. -/
private theorem normalized_middle_component_iso_comm_fst
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hsucc : D.rank i.succ = ns + 1)
    (hcast : D.rank i.castSucc = nt + 1)
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
    (j k : ℕ) :
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j).hom ≫
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).d j k ≫
      (biprodChainFst
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).f k =
      D.toChainComplex.d j k ≫
        (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid k).hom ≫
    (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f k := by
  -- First move the biproduct differential through the first chain projection; this leaves only
  -- the reduced differential to compare with the original differential of `D`.
  calc
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j).hom ≫
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).d j k ≫
      (biprodChainFst
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).f k =
        (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid j).hom ≫
          (biprodChainFst
            (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
              eSource eTarget tailDiff hmid).toChainComplex
            (identityDiskComplex (R := R) i)).f j ≫
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex.d j k := by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦
                (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
                  eSource eTarget tailDiff hmid j).hom ≫ m)
              ((biprodChainFst
                (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
                  eSource eTarget tailDiff hmid).toChainComplex
                (identityDiskComplex (R := R) i)).comm j k).symm
    _ = D.toChainComplex.d j k ≫
        (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid k).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f k := by
          -- Adjacent degrees use the four explicit reduced-differential branches; all other
          -- degrees are zero by the chain-complex shape condition.
          by_cases hrel : k + 1 = j
          · subst j
            by_cases hUpper : k = i.1 + 1
            · subst k
              -- In the upper branch, the source degree is off the two distinguished degrees
              -- while the target degree is the supported source degree.
              have hSourceSucc : i.1 + 1 + 1 ≠ i.1 + 1 := by
                omega
              have hSourceCast : i.1 + 1 + 1 ≠ i.1 := by
                omega
              rw [← Category.assoc]
              rw [normalized_middle_component_iso_hom_comp_fst_of_ne_support (R := R)
                (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
                (j := i.1 + 1 + 1) hSourceSucc hSourceCast]
              rw [normalized_middle_component_iso_hom_comp_fst_succ (R := R) (D := D)
                (i := i) hsucc hcast eSource eTarget tailDiff hmid]
              simp only [reduced_complex_of_normalized_middle, ChainComplex.of_d]
              rw [reduced_complex_of_normalized_middle_d_eq_upper (R := R) (ns := ns)
                (nt := nt) D i (eSource := eSource) (eTarget := eTarget)
                (tailDiff := tailDiff)]
              simp
            · by_cases hMid : k = i.1
              · subst k
                -- The middle branch is exactly the normalized tail projection, transported back
                -- to the original middle differential of `D`.
                rw [← Category.assoc]
                rw [normalized_middle_component_iso_hom_comp_fst_succ (R := R) (D := D)
                  (i := i) hsucc hcast eSource eTarget tailDiff hmid]
                rw [normalized_middle_component_iso_hom_comp_fst_castSucc (R := R) (D := D)
                  (i := i) hsucc hcast eSource eTarget tailDiff hmid]
                simp only [reduced_complex_of_normalized_middle, ChainComplex.of_d]
                rw [reduced_complex_of_normalized_middle_d_eq_middle (R := R) (ns := ns)
                  (nt := nt) D i (eSource := eSource) (eTarget := eTarget)
                  (tailDiff := tailDiff)]
                -- The two supported branch identifications meet on the same tail object, and
                -- the normalized tail projection identifies the remaining map with `D.diffAt`.
                simp only [of_x, Fin.val_succ, Category.assoc, eqToHom_trans_assoc,
                  eqToHom_refl, Category.id_comp, Fin.val_castSucc]
                have htailComp {Z : ModuleCat R} (q : ModuleCat.of R (Fin nt → R) = Z) :
                    (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫ tailDiff ≫
                        eqToHom q =
                      D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom ≫
                        eTarget.hom ≫ biprod.fst ≫ eqToHom q := by
                  calc
                    (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫ tailDiff ≫
                        eqToHom q =
                        (D.termIso i.succ).hom ≫ ModuleCat.ofHom (D.diffAt i) ≫
                          eTarget.hom ≫ biprod.fst ≫ eqToHom q := by
                          simpa [Category.assoc] using
                            congrArg
                              (fun m ↦ (D.termIso i.succ).hom ≫ m ≫ eqToHom q)
                              (normalized_middle_tail_projection (R := R) (D := D) (i := i)
                                (eSource := eSource) (eTarget := eTarget)
                                (tailDiff := tailDiff) hmid).symm
                    _ = D.toChainComplex.d (i.1 + 1) i.1 ≫
                          (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫
                            eqToHom q := by
                          simpa [Category.assoc] using
                            congrArg
                              (fun m ↦ m ≫ eTarget.hom ≫ biprod.fst ≫ eqToHom q)
                              (termIso_hom_comp_diffAt (R := R) D i)
                exact htailComp _
              · by_cases hLower : k + 1 = i.1
                · -- Below the middle differential, the source projection is the target-tail
                  -- projection and the reduced differential reinserts that tail into `D`.
                  -- Route correction: keep the source degree spelled as `k + 1` and only
                  -- normalize the two projected components before exposing the reduced lower
                  -- differential.
                  have hdLower :
                      (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i)
                        hsucc hcast eSource eTarget tailDiff hmid).toChainComplex.d
                          (k + 1) k =
                        eqToHom
                            (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                              (R := R) (ns := ns) (nt := nt) D i hLower) ≫
                          biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                            D.toChainComplex.d i.1 k ≫
                          eqToHom
                            (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                              (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
                    -- Expose only the differential field, keeping the component projection in
                    -- the canonical reduced-complex spelling used by the transport helper.
                    simp only [reduced_complex_of_normalized_middle, ChainComplex.of_d]
                    rw [reduced_complex_of_normalized_middle_d_eq_lower (R := R) (ns := ns)
                      (nt := nt) D i (eSource := eSource) (eTarget := eTarget)
                      (tailDiff := tailDiff) hLower]
                  rw [hdLower]
                  have hsource :=
                    normalized_middle_component_iso_hom_comp_fst_castSucc_comp_lower_source
                      (R := R) (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
                      hLower
                  have htarget :=
                    normalized_middle_component_iso_hom_comp_fst_of_ne_support (R := R)
                      (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
                      hUpper hMid
                  have htargetTransport :=
                    reduced_complex_of_normalized_middle_lower_target_off_support_eqToHom
                      (R := R) (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
                      hUpper hMid hLower
                  have htail :=
                    lower_adjacent_tail_projection_comp_eq (R := R) (D := D) (i := i)
                      (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) hmid
                      hLower
                  have hDsource :
                      eqToHom
                          (by rw [hLower] :
                            D.toChainComplex.X (k + 1) = D.toChainComplex.X i.1) ≫
                        D.toChainComplex.d i.1 k =
                      D.toChainComplex.d (k + 1) k := by
                    -- The remaining source transport on `D.d` is the uniqueness of the previous
                    -- degree in the down complex shape.
                    simpa [ComplexShape.down_Rel] using
                      HomologicalComplex.eqToHom_comp_d D.toChainComplex
                        (by simpa [ComplexShape.down_Rel])
                        (by simpa [ComplexShape.down_Rel, hLower])
                  calc
                      (((normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc
                            hcast eSource eTarget tailDiff hmid (k + 1)).hom ≫
                          (biprodChainFst
                            (reduced_complex_of_normalized_middle (R := R) (D := D)
                              (i := i) hsucc hcast eSource eTarget tailDiff hmid).toChainComplex
                            (identityDiskComplex (R := R) i)).f (k + 1) ≫
                          eqToHom
                            (reduced_complex_of_normalized_middle_object_eq_source_of_lower
                              (R := R) (ns := ns) (nt := nt) D i hLower)) ≫
                          biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                            D.toChainComplex.d i.1 k) ≫
                            eqToHom
                              ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
                                (R := R) (ns := ns) (nt := nt) D i hLower).symm) =
                          ((eqToHom
                                (by rw [hLower] :
                                  D.toChainComplex.X (k + 1) = D.toChainComplex.X i.1) ≫
                              (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst) ≫
                              biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
                                D.toChainComplex.d i.1 k) ≫
                              eqToHom
                                (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                                  (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
                            simpa [Category.assoc] using
                              congrArg
                                (fun m ↦
                                  m ≫ biprod.inl ≫ eTarget.inv ≫
                                    (D.termIso i.castSucc).inv ≫
                                D.toChainComplex.d i.1 k ≫
                                          eqToHom
                                            ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
                                              (R := R) (ns := ns) (nt := nt) D i hLower).symm))
                                hsource
                      _ = (eqToHom
                            (by rw [hLower] :
                              D.toChainComplex.X (k + 1) = D.toChainComplex.X i.1) ≫
                          D.toChainComplex.d i.1 k) ≫
                          eqToHom
                            (reduced_complex_of_normalized_middle_object_eq_target_of_lower
                              (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
                          simpa [Category.assoc] using
                            congrArg
                              (fun m ↦
                                eqToHom
                                    (by rw [hLower] :
                                      D.toChainComplex.X (k + 1) =
                                        D.toChainComplex.X i.1) ≫
                                  m ≫
                                    eqToHom
                                      ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
                                        (R := R) (ns := ns) (nt := nt) D i hLower).symm))
                              htail
                      _ = D.toChainComplex.d (k + 1) k ≫
                            eqToHom
                              ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
                                (R := R) (ns := ns) (nt := nt) D i hLower).symm) := by
                          rw [hDsource]
                      _ = D.toChainComplex.d (k + 1) k ≫
                            eqToHom
                              (reduced_complex_of_normalized_middle_X_eq_of_ne_support
                                (R := R) (D := D) (i := i) hsucc hcast eSource eTarget tailDiff
                                hmid hUpper hMid).symm := by
                            simpa using
                              congrArg
                                (fun m ↦ D.toChainComplex.d (k + 1) k ≫ m)
                                htargetTransport
                      _ = D.toChainComplex.d (k + 1) k ≫
                          (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc
                            hcast eSource eTarget tailDiff hmid k).hom ≫
                            (biprodChainFst
                              (reduced_complex_of_normalized_middle (R := R) (D := D)
                                (i := i) hsucc hcast eSource eTarget tailDiff hmid).toChainComplex
                              (identityDiskComplex (R := R) i)).f k := by
                          rw [htarget]
                · -- Away from all supported branches, both component projections are the
                  -- off-support formulas and the reduced differential is inherited from `D`.
                  have hSourceSucc : k + 1 ≠ i.1 + 1 := by
                    omega
                  rw [← Category.assoc]
                  rw [normalized_middle_component_iso_hom_comp_fst_of_ne_support (R := R)
                    (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
                    hSourceSucc hLower]
                  rw [normalized_middle_component_iso_hom_comp_fst_of_ne_support (R := R)
                    (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
                    hUpper hMid]
                  simp only [reduced_complex_of_normalized_middle, ChainComplex.of_d]
                  rw [reduced_complex_of_normalized_middle_d_eq_generic (R := R) (ns := ns)
                    (nt := nt) D i (eSource := eSource) (eTarget := eTarget)
                    (tailDiff := tailDiff) hUpper hMid hLower]
                  simp
          · have hshape : ¬ (ComplexShape.down ℕ).Rel j k := by
              simpa [ComplexShape.down_Rel] using hrel
            rw [HomologicalComplex.shape D.toChainComplex j k hshape]
            rw [HomologicalComplex.shape
              (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
                eSource eTarget tailDiff hmid).toChainComplex j k hshape]
            simp

/-- Helper for Lemma 10.102.2: after postcomposing with the identity-disk projection, the
componentwise normalized split satisfies the chain-map naturality square. -/
private theorem normalized_middle_component_iso_comm_snd
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hsucc : D.rank i.succ = ns + 1)
    (hcast : D.rank i.castSucc = nt + 1)
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
    (j k : ℕ) :
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j).hom ≫
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).d j k ≫
      (biprodChainSnd
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).f k =
      D.toChainComplex.d j k ≫
        (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid k).hom ≫
    (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f k := by
  -- First move the biproduct differential through the second chain projection; the remaining
  -- comparison is between the identity-disk differential and the second projected component.
  calc
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j).hom ≫
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).d j k ≫
      (biprodChainSnd
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).f k =
        (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid j).hom ≫
          (biprodChainSnd
            (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
              eSource eTarget tailDiff hmid).toChainComplex
            (identityDiskComplex (R := R) i)).f j ≫
          (identityDiskComplex (R := R) i).d j k := by
          simpa [Category.assoc] using
            congrArg
              (fun m ↦
                (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
                  eSource eTarget tailDiff hmid j).hom ≫ m)
              ((biprodChainSnd
                (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
                  eSource eTarget tailDiff hmid).toChainComplex
                (identityDiskComplex (R := R) i)).comm j k).symm
    _ = D.toChainComplex.d j k ≫
        (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid k).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f k := by
          -- Adjacent degrees contain the real identity-disk computation; non-adjacent maps are
          -- zero by the common chain-complex shape condition.
          by_cases hrel : k + 1 = j
          · subst j
            -- Split the adjacent square by the target degree.  Away from the middle degree the
            -- identity-disk differential or the off-support second projection kills the square.
            by_cases hUpper : k = i.1 + 1
            · subst k
              rw [identityDiskComplex_d_eq_zero_of_ne (R := R) (i := i)]
              · rw [normalized_middle_component_iso_hom_comp_snd_succ (R := R) (D := D)
                  (i := i) hsucc hcast eSource eTarget tailDiff hmid]
                have hzero :=
                  (adjacent_maps_respect_tail_split_of_normalized_middle (R := R) (D := D)
                    (i := i) (eSource := eSource) (eTarget := eTarget)
                    (tailDiff := tailDiff) hmid).1
                simpa [Category.assoc] using (congrArg
                  (fun m ↦
                    m ≫ eqToHom (identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm)
                  hzero).symm
              · omega
            · by_cases hMid : k = i.1
              · subst k
                -- In the middle branch the identity disk contributes its identity differential,
                -- and the normalized head projection matches the head component of `D.d`.
                rw [← Category.assoc]
                rw [normalized_middle_component_iso_hom_comp_snd_succ (R := R) (D := D)
                  (i := i) hsucc hcast eSource eTarget tailDiff hmid]
                calc
                  ((D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd ≫
                      eqToHom (identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm) ≫
                      (identityDiskComplex (R := R) i).d (i.1 + 1) i.1 =
                    (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd ≫
                      eqToHom (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
                      simpa [Category.assoc] using
                        congrArg
                          (fun m ↦ (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd ≫ m)
                          (identityDiskComplex_eqToHom_symm_comp_d (R := R) (i := i))
                  _ = D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom ≫
                      eTarget.hom ≫ biprod.snd ≫
                        eqToHom (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
                      simpa [Category.assoc] using
                        congrArg
                          (fun m ↦
                            m ≫ eqToHom
                              (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm)
                          (normalized_middle_head_projection_chain (R := R) (D := D) (i := i)
                            (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff)
                            hmid)
                  _ = D.toChainComplex.d (i.1 + 1) i.1 ≫
                      (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
                        eSource eTarget tailDiff hmid i.1).hom ≫
                        (biprodChainSnd
                          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i)
                            hsucc hcast eSource eTarget tailDiff hmid).toChainComplex
                          (identityDiskComplex (R := R) i)).f i.1 := by
                      rw [normalized_middle_component_iso_hom_comp_snd_castSucc (R := R)
                        (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid]
                      simp
              · rw [identityDiskComplex_d_eq_zero_of_ne (R := R) (i := i) hMid]
                rw [normalized_middle_component_iso_hom_comp_snd_of_ne_support (R := R)
                  (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid hUpper hMid]
                simp
          · have hshape : ¬ (ComplexShape.down ℕ).Rel j k := by
              simpa [ComplexShape.down_Rel] using hrel
            rw [HomologicalComplex.shape D.toChainComplex j k hshape]
            rw [HomologicalComplex.shape (identityDiskComplex (R := R) i) j k hshape]
            simp

/-- Helper for Lemma 10.102.2: once the middle differential has been normalized to fix the head
summand and to kill the head coordinate on tail basis vectors, the remaining chain-level work is
to split off the identity disk and package the tail summands into a reduced finite free complex. -/
private theorem exists_reduced_complex_and_biprod_iso_of_normalized_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hsucc : D.rank i.succ = ns + 1)
    (hcast : D.rank i.castSucc = nt + 1)
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
    ∃ C' : _root_.FiniteFreeComplex R e,
      C'.rank = splitRank D.rank i ∧
      Nonempty (D.toChainComplex ≅ biprod C'.toChainComplex (identityDiskComplex i)) := by
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  refine ⟨C', rfl, ?_⟩
  -- Package the degreewise split as a chain-complex isomorphism by checking the naturality square
  -- after postcomposing with the two biproduct projections.
  refine ⟨HomologicalComplex.Hom.isoOfComponents
      (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid) ?_⟩
  intro j k hjk
  apply (cancel_mono (HomologicalComplex.biprodXIso C'.toChainComplex
    (identityDiskComplex (R := R) i) k).hom).1
  apply biprod.hom_ext
  · simpa [Category.assoc] using
      normalized_middle_component_iso_comm_fst (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j k
  · simpa [Category.assoc] using
      normalized_middle_component_iso_comm_snd (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j k


/-- Helper for Lemma 10.102.2: after transporting the pivot data to explicit successor
coordinates, the recoordinated middle differential is already in the normalized block-diagonal
form required to split off the identity disk. -/
private theorem recoordinate_middle_diff_splitOff_conjugate
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (a : Fin (C.rank i.succ))
    (b : Fin (C.rank i.castSucc))
    (hu : IsUnit (C.diffEntry i a b)) :
    let sourceEq := moduleIso_of_eq (R := R) hsucc
    let targetEq := moduleIso_of_eq (R := R) hcast
    let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
    let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
    let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
    let hu' := diffAt_transport_to_successor_ranks_pivot (R := R) (C := C) (i := i)
      hsucc hcast a b hu
    let sourceSwap :=
      LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a')
    let uTargetExp := (target_head_normalization (R := R) f a' b' hu').toModuleIso
    let g :=
      (target_head_normalization (R := R) f a' b' hu').toLinearMap.comp
        (f.comp sourceSwap.symm.toLinearMap)
    let hg := target_head_normalization_map_head (R := R) f a' b' hu'
    let uCorrExp := (source_head_correction (R := R) g hg).toModuleIso
    let g' := g.comp (source_head_correction (R := R) g hg).symm.toLinearMap
    let uSuccExp := sourceSwap.toModuleIso ≪≫ uCorrExp
    let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
    let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
    let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
    let eSource := splitOffUnitModuleIso_of_eq (R := R) hsucc
    let eTarget := splitOffUnitModuleIso_of_eq (R := R) hcast
    eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
      (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
        (splitOffUnitModuleIso (R := R) nt).hom := by
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
  let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
  let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
  let hu' := diffAt_transport_to_successor_ranks_pivot (R := R) (C := C) (i := i)
    hsucc hcast a b hu
  let sourceSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a')
  let uTargetExp := (target_head_normalization (R := R) f a' b' hu').toModuleIso
  let g :=
    (target_head_normalization (R := R) f a' b' hu').toLinearMap.comp
      (f.comp sourceSwap.symm.toLinearMap)
  let hg := target_head_normalization_map_head (R := R) f a' b' hu'
  let uCorrExp := (source_head_correction (R := R) g hg).toModuleIso
  let g' := g.comp (source_head_correction (R := R) g hg).symm.toLinearMap
  let uSuccExp := sourceSwap.toModuleIso ≪≫ uCorrExp
  let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
  let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
  let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
  let eSource := splitOffUnitModuleIso_of_eq (R := R) hsucc
  let eTarget := splitOffUnitModuleIso_of_eq (R := R) hcast
  have hcancel := recoordinate_middle_diff_transport_cancel (R := R) (C := C) (i := i)
    hsucc hcast uSuccExp uTargetExp
  change eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
      (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
        (splitOffUnitModuleIso (R := R) nt).hom
  -- First strip the rank transports, then fold the remaining explicit basis-change composite
  -- into the normalized linear map `g'`.
  calc
    eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        (splitOffUnitModuleIso (R := R) ns).inv ≫
          (sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom) ≫
          (splitOffUnitModuleIso (R := R) nt).hom := by
          simp [eSource, eTarget, sourceEq, targetEq, splitOffUnitModuleIso_of_eq,
            Category.assoc]
          rfl
    _ = (splitOffUnitModuleIso (R := R) ns).inv ≫
          (uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom) ≫
          (splitOffUnitModuleIso (R := R) nt).hom := by
          rw [hcancel]
    _ = (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
          (splitOffUnitModuleIso (R := R) nt).hom := by
          simp [uSuccExp, uCorrExp, g', g, uTargetExp, Category.assoc, ModuleCat.ofHom_comp]

/-- Helper for Lemma 10.102.2: after transporting the pivot data to explicit successor
coordinates, the recoordinated middle differential is already in the normalized block-diagonal
form required to split off the identity disk. -/
private theorem recoordinate_middle_diff_eq_transported_normalized_map
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (a : Fin (C.rank i.succ))
    (b : Fin (C.rank i.castSucc))
    (hu : IsUnit (C.diffEntry i a b)) :
    let sourceEq := moduleIso_of_eq (R := R) hsucc
    let targetEq := moduleIso_of_eq (R := R) hcast
    let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
    let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
    let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
    let hu' := diffAt_transport_to_successor_ranks_pivot (R := R) (C := C) (i := i)
      hsucc hcast a b hu
    let sourceSwap :=
      LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a')
    let uTargetExp := (target_head_normalization (R := R) f a' b' hu').toModuleIso
    let g :=
      (target_head_normalization (R := R) f a' b' hu').toLinearMap.comp
        (f.comp sourceSwap.symm.toLinearMap)
    let hg := target_head_normalization_map_head (R := R) f a' b' hu'
    let uCorrExp := (source_head_correction (R := R) g hg).toModuleIso
    let uSuccExp := sourceSwap.toModuleIso ≪≫ uCorrExp
    let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
    let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
    let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
    let eSource := splitOffUnitModuleIso_of_eq (R := R) hsucc
    let eTarget := splitOffUnitModuleIso_of_eq (R := R) hcast
    let F := eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 _) := by
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
  let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
  let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
  let hu' := diffAt_transport_to_successor_ranks_pivot (R := R) (C := C) (i := i)
    hsucc hcast a b hu
  let sourceSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a')
  let uTargetExp := (target_head_normalization (R := R) f a' b' hu').toModuleIso
  let g :=
    (target_head_normalization (R := R) f a' b' hu').toLinearMap.comp
      (f.comp sourceSwap.symm.toLinearMap)
  let hg := target_head_normalization_map_head (R := R) f a' b' hu'
  let uCorrExp := (source_head_correction (R := R) g hg).toModuleIso
  let g' := g.comp (source_head_correction (R := R) g hg).symm.toLinearMap
  let uSuccExp := sourceSwap.toModuleIso ≪≫ uCorrExp
  let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
  let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
  let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
  let eSource := splitOffUnitModuleIso_of_eq (R := R) hsucc
  let eTarget := splitOffUnitModuleIso_of_eq (R := R) hcast
  let F := eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom
  have hconj : F =
      (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
        (splitOffUnitModuleIso (R := R) nt).hom := by
    change eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
      (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
        (splitOffUnitModuleIso (R := R) nt).hom
    exact recoordinate_middle_diff_splitOff_conjugate (R := R) (C := C) (i := i)
      hsucc hcast a b hu
  have hgtail := source_head_correction_zero_head_on_tail (R := R) g hg
  have hblock := normalized_middle_diff_is_biprod_map_tail_identity (R := R) g'
    hgtail.1 hgtail.2
  change F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 _)
  -- The previous conjugation identifies `F` with the abstract normalized block map, and the
  -- block lemma says precisely that such a map is diagonal with identity on the head summand.
  calc
    F = (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
          (splitOffUnitModuleIso (R := R) nt).hom := hconj
    _ = biprod.map
          (biprod.inl ≫
            ((splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom g' ≫
              (splitOffUnitModuleIso (R := R) nt).hom) ≫ biprod.fst) (𝟙 _) := hblock
    _ = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 _) := by
          rw [hconj]

-- Proof sketch: use elementary row and column operations in the chosen coordinates of `C.diffAt i`
-- to isolate a unit entry, split off the corresponding free rank-one summand in degrees `i + 1`
-- and `i`, and identify the resulting summand with `identityDiskComplex i`.
/-- Chap10 Lemma 10 102 2: if a differential `R^(n_{i + 1}) → R^(n_i)` in a bounded finite free complex
has a unit coordinate in the chosen standard bases, then the complex is isomorphic to the direct
sum of a reduced finite free complex and the two-term identity complex supported in degrees
`i + 1` and `i`. -/
@[stacks 00MT]
theorem exists_iso_biprod_identityDisk_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    ∃ C' : _root_.FiniteFreeComplex R e,
      C'.rank = splitRank C.rank i ∧
      Nonempty (C.toChainComplex ≅ biprod C'.toChainComplex (identityDiskComplex i)) :=
by
  rcases hunit with ⟨a, b, hu⟩
  rcases exists_rank_eq_succ_of_isUnit_diffEntry (R := R) (C := C) (i := i) ⟨a, b, hu⟩ with
    ⟨ns, nt, hsucc, hcast⟩
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
  let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
  let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
  let hu' := diffAt_transport_to_successor_ranks_pivot (R := R) (C := C) (i := i)
    hsucc hcast a b hu
  let sourceSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a')
  let uTargetExp := (target_head_normalization (R := R) f a' b' hu').toModuleIso
  let g :=
    (target_head_normalization (R := R) f a' b' hu').toLinearMap.comp
      (f.comp sourceSwap.symm.toLinearMap)
  let hg := target_head_normalization_map_head (R := R) f a' b' hu'
  let uCorrExp := (source_head_correction (R := R) g hg).toModuleIso
  let g' := g.comp (source_head_correction (R := R) g hg).symm.toLinearMap
  let uSuccExp := sourceSwap.toModuleIso ≪≫ uCorrExp
  let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
  let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
  let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
  let eSource := splitOffUnitModuleIso_of_eq (R := R) hsucc
  let eTarget := splitOffUnitModuleIso_of_eq (R := R) hcast
  let tailDiff := biprod.inl ≫
      (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom) ≫ biprod.fst
  have hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _) := by
    -- The normalized basis changes isolate the identity block on the split head summand.
    simpa [tailDiff] using
      recoordinate_middle_diff_eq_transported_normalized_map (R := R) (C := C) (i := i)
        hsucc hcast a b hu
  obtain ⟨C', hC'rank, hIso⟩ :=
    exists_reduced_complex_and_biprod_iso_of_normalized_middle (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid
  refine ⟨C', ?_, ?_⟩
  · -- The recoordinated complex keeps the same displayed rank function as the original complex.
    simpa [D] using hC'rank
  · -- The recoordinated complex also keeps the same underlying chain complex.
    simpa [D] using hIso

end FiniteFreeComplex

end
