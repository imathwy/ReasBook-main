import StacksProject_2024.Chap10.Lemma_10_102_2.ReducedFiniteFree

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: in `ModuleCat R`, a biproduct with zero right summand collapses
onto the left summand. -/
noncomputable def biprodFstIsoOfIsZero (X Y : ModuleCat R) [HasBinaryBiproduct X Y]
    (hY : IsZero Y) : X ⊞ Y ≅ X where
  hom := biprod.fst
  inv := biprod.inl
  hom_inv_id := by
    -- The right projection vanishes because the right summand is zero.
    apply biprod.hom_ext
    · simp
    · have hsnd : (biprod.snd : X ⊞ Y ⟶ Y) = 0 := by
        simpa using hY.eq_of_tgt (biprod.snd : X ⊞ Y ⟶ Y) 0
      simpa [Category.assoc, hsnd]
  inv_hom_id := by
    simp

/-- Helper for Lemma 10.102.2: the inverse of `biprodFstIsoOfIsZero` includes the left summand
back into the biproduct, so composing it with the first projection is the identity. -/
theorem biprodFstIsoOfIsZero_symm_hom_comp_fst
    (X Y : ModuleCat R) [HasBinaryBiproduct X Y] (hY : IsZero Y) :
    (biprodFstIsoOfIsZero (R := R) X Y hY).symm.hom ≫
        (biprod.fst : X ⊞ Y ⟶ X) =
      𝟙 X := by
  -- The inverse of the collapse is exactly `biprod.inl`.
  simp [biprodFstIsoOfIsZero]

/-- Helper for Lemma 10.102.2: the inverse of `biprodFstIsoOfIsZero` has zero composite with the
second projection, because the zero summand contributes nothing. -/
theorem biprodFstIsoOfIsZero_symm_hom_comp_snd
    (X Y : ModuleCat R) [HasBinaryBiproduct X Y] (hY : IsZero Y) :
    (biprodFstIsoOfIsZero (R := R) X Y hY).symm.hom ≫
        (biprod.snd : X ⊞ Y ⟶ Y) =
      0 := by
  -- Again the inverse is `biprod.inl`, and `biprod.inl ≫ biprod.snd = 0`.
  simp [biprodFstIsoOfIsZero]

/-- Helper for Lemma 10.102.2: the inverse objectwise biproduct comparison identifies the first
projection on the chain-level biproduct with the explicit first projection. -/
theorem biprodXIso_inv_fst
    (K L : ChainComplex (ModuleCat R) ℕ)
    [∀ j, HasBinaryBiproduct (K.X j) (L.X j)] (j : ℕ) :
    (HomologicalComplex.biprodXIso K L j).inv ≫
        (biprod.fst : biprod K L ⟶ K).f j =
      biprod.fst := by
  -- Compare both maps on the two objectwise biproduct summands, where the chain-level biproduct
  -- identities reduce immediately to the standard `fst` relations.
  refine biprod.hom_ext'
      ((HomologicalComplex.biprodXIso K L j).inv ≫ (biprod.fst : biprod K L ⟶ K).f j)
      biprod.fst ?_ ?_
  · simp [Category.assoc]
  · simp [Category.assoc]

/-- Helper for Lemma 10.102.2: the inverse objectwise biproduct comparison identifies the second
projection on the chain-level biproduct with the explicit second projection. -/
theorem biprodXIso_inv_snd
    (K L : ChainComplex (ModuleCat R) ℕ)
    [∀ j, HasBinaryBiproduct (K.X j) (L.X j)] (j : ℕ) :
    (HomologicalComplex.biprodXIso K L j).inv ≫
        (biprod.snd : biprod K L ⟶ L).f j =
      biprod.snd := by
  -- The same summandwise comparison works for the second projection.
  refine biprod.hom_ext'
      ((HomologicalComplex.biprodXIso K L j).inv ≫ (biprod.snd : biprod K L ⟶ L).f j)
      biprod.snd ?_ ?_
  · simp [Category.assoc]
  · simp [Category.assoc]

/-- Helper for Lemma 10.102.2: the forward objectwise biproduct comparison identifies the first
projection on the actual objectwise biproduct with the chain-level first projection. -/
theorem biprodXIso_hom_comp_fst
    (K L : ChainComplex (ModuleCat R) ℕ)
    [∀ j, HasBinaryBiproduct (K.X j) (L.X j)] (j : ℕ) :
    (HomologicalComplex.biprodXIso K L j).hom ≫ biprod.fst =
      (biprod.fst : biprod K L ⟶ K).f j := by
  -- Compose the inverse comparison formula with the forward isomorphism on the left.
  simpa [Category.assoc] using
    congrArg (fun k ↦ (HomologicalComplex.biprodXIso K L j).hom ≫ k)
      (biprodXIso_inv_fst (R := R) K L j)

/-- Helper for Lemma 10.102.2: the forward objectwise biproduct comparison identifies the second
projection on the actual objectwise biproduct with the chain-level second projection. -/
theorem biprodXIso_hom_comp_snd
    (K L : ChainComplex (ModuleCat R) ℕ)
    [∀ j, HasBinaryBiproduct (K.X j) (L.X j)] (j : ℕ) :
    (HomologicalComplex.biprodXIso K L j).hom ≫ biprod.snd =
      (biprod.snd : biprod K L ⟶ L).f j := by
  -- This is the same calculation for the second projection.
  simpa [Category.assoc] using
    congrArg (fun k ↦ (HomologicalComplex.biprodXIso K L j).hom ≫ k)
      (biprodXIso_inv_snd (R := R) K L j)

/-- Helper for Lemma 10.102.2: the first projection from a chain-level biproduct, named as a
chain map for use in later component formulas. -/
abbrev biprodChainFst (K L : ChainComplex (ModuleCat R) ℕ) : biprod K L ⟶ K :=
  biprod.fst

/-- Helper for Lemma 10.102.2: the second projection from a chain-level biproduct, named as a
chain map for use in later component formulas. -/
abbrev biprodChainSnd (K L : ChainComplex (ModuleCat R) ℕ) : biprod K L ⟶ L :=
  biprod.snd

/-- Helper for Lemma 10.102.2: the normalized split produces the degreewise component isomorphism
from `D` to the biproduct of the reduced complex and the identity disk. -/
noncomputable def normalized_middle_component_iso_off_support
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
    (j : ℕ)
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    D.toChainComplex.X j ≅
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).X j :=
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  (eqToIso
      (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
        hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm) ≪≫
    (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j) ((identityDiskComplex (R := R) i).X j)
      (identityDiskComplex_X_isZero_of_ne_support (R := R) (e := e) (i := i)
        (j := j) hjSucc hjCast)).symm ≪≫
    (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm

/-- Helper for Lemma 10.102.2: in degree `i + 1`, the normalized split is exactly the source
head-tail decomposition. -/
noncomputable def normalized_middle_component_iso_succ
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
    D.toChainComplex.X (i.1 + 1) ≅
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).X (i.1 + 1) :=
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  (D.termIso i.succ ≪≫ eSource) ≪≫
    biprod.mapIso
      (eqToIso
        (reduced_complex_of_normalized_middle_X_eq_succ (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid).symm)
      (eqToIso (identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm) ≪≫
    (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i)
      (i.1 + 1)).symm

/-- Helper for Lemma 10.102.2: in degree `i`, the normalized split is exactly the target
head-tail decomposition. -/
noncomputable def normalized_middle_component_iso_castSucc
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
    D.toChainComplex.X i.1 ≅
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).X i.1 :=
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  (D.termIso i.castSucc ≪≫ eTarget) ≪≫
    biprod.mapIso
      (eqToIso
        (reduced_complex_of_normalized_middle_X_eq_castSucc (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid).symm)
      (eqToIso (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm) ≪≫
    (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i)
      i.1).symm

/-- Helper for Lemma 10.102.2: the normalized split produces the degreewise component isomorphism
from `D` to the biproduct of the reduced complex and the identity disk. -/
noncomputable def normalized_middle_component_iso
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
    (j : ℕ) :
    D.toChainComplex.X j ≅
      (biprod
        (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
          eSource eTarget tailDiff hmid).toChainComplex
        (identityDiskComplex (R := R) i)).X j :=
  if hjSucc : j = i.1 + 1 then
    Eq.ndrec
      (motive := fun k : ℕ ↦
        D.toChainComplex.X k ≅
          (biprod
            (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
              eSource eTarget tailDiff hmid).toChainComplex
            (identityDiskComplex (R := R) i)).X k)
      (normalized_middle_component_iso_succ (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid)
      hjSucc.symm
  else if hjCast : j = i.1 then
    Eq.ndrec
      (motive := fun k : ℕ ↦
        D.toChainComplex.X k ≅
          (biprod
            (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
              eSource eTarget tailDiff hmid).toChainComplex
            (identityDiskComplex (R := R) i)).X k)
      (normalized_middle_component_iso_castSucc (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid)
      hjCast.symm
  else
    normalized_middle_component_iso_off_support (R := R) (D := D) (i := i) hsucc hcast
      eSource eTarget tailDiff hmid j hjSucc hjCast

/-- Helper for Lemma 10.102.2: away from the two supported degrees, the normalized component
isomorphism followed by the reduced-complex projection is just the inherited object
identification. -/
theorem normalized_middle_component_iso_off_support_hom_comp_fst
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
    {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    (normalized_middle_component_iso_off_support (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j hjSucc hjCast).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f j =
      eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm := by
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  let hZero := identityDiskComplex_X_isZero_of_ne_support (R := R) (e := e) (i := i)
    (j := j) hjSucc hjCast
  -- Put the off-support component into the explicit three-factor composite and then cancel the
  -- objectwise biproduct comparison and the zero-summand biproduct collapse in sequence.
  change
    eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
      (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
        ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
      (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm.hom ≫
      (biprod.fst :
          biprod C'.toChainComplex (identityDiskComplex (R := R) i) ⟶ C'.toChainComplex).f j =
    _
  have hX :
      (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm.hom ≫
          (biprod.fst :
            biprod C'.toChainComplex (identityDiskComplex (R := R) i) ⟶ C'.toChainComplex).f j =
        biprod.fst := by
    simpa using biprodXIso_inv_fst (R := R) C'.toChainComplex (identityDiskComplex (R := R) i) j
  have hCollapse :
      (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
          ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
        biprod.fst =
      𝟙 _ := by
    simpa using biprodFstIsoOfIsZero_symm_hom_comp_fst (R := R) (C'.toChainComplex.X j)
      ((identityDiskComplex (R := R) i).X j) hZero
  calc
    eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
      (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
        ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
      (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm.hom ≫
      (biprod.fst :
          biprod C'.toChainComplex (identityDiskComplex (R := R) i) ⟶ C'.toChainComplex).f j =
        eqToHom
          (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
          (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
            ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
          biprod.fst := by
            simpa [Category.assoc] using congrArg
              (fun k ↦
                eqToHom
                  (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D)
                    (i := i) hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
                  (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
                    ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
                  k) hX
    _ = eqToHom
          (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
          𝟙 _ := by
            simpa [Category.assoc] using congrArg
              (fun k ↦
                eqToHom
                  (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D)
                    (i := i) hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
                  k) hCollapse
    _ = _ := by
      simp [C', hZero]

/-- Helper for Lemma 10.102.2: away from the two supported degrees, the normalized component
isomorphism has zero composite with the identity-disk projection. -/
theorem normalized_middle_component_iso_off_support_hom_comp_snd
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
    {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    (normalized_middle_component_iso_off_support (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j hjSucc hjCast).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f j =
      0 := by
  let C' := reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
    eSource eTarget tailDiff hmid
  let hZero := identityDiskComplex_X_isZero_of_ne_support (R := R) (e := e) (i := i)
    (j := j) hjSucc hjCast
  -- The same explicit normal form shows that the second projection dies because the off-support
  -- identity-disk summand is zero.
  change
    eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
      (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
        ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
      (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm.hom ≫
      (biprod.snd :
          biprod C'.toChainComplex (identityDiskComplex (R := R) i) ⟶
            identityDiskComplex (R := R) i).f j =
    0
  have hX :
      (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm.hom ≫
          (biprod.snd :
            biprod C'.toChainComplex (identityDiskComplex (R := R) i) ⟶
              identityDiskComplex (R := R) i).f j =
        biprod.snd := by
    simpa using biprodXIso_inv_snd (R := R) C'.toChainComplex (identityDiskComplex (R := R) i) j
  have hCollapse :
      (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
          ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
        biprod.snd =
      0 := by
    simpa using biprodFstIsoOfIsZero_symm_hom_comp_snd (R := R) (C'.toChainComplex.X j)
      ((identityDiskComplex (R := R) i).X j) hZero
  calc
    eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
      (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
        ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
      (HomologicalComplex.biprodXIso C'.toChainComplex (identityDiskComplex (R := R) i) j).symm.hom ≫
      (biprod.snd :
          biprod C'.toChainComplex (identityDiskComplex (R := R) i) ⟶
            identityDiskComplex (R := R) i).f j =
        eqToHom
          (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
          (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
            ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
          biprod.snd := by
            simpa [Category.assoc] using congrArg
              (fun k ↦
                eqToHom
                  (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D)
                    (i := i) hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
                  (biprodFstIsoOfIsZero (R := R) (C'.toChainComplex.X j)
                    ((identityDiskComplex (R := R) i).X j) hZero).symm.hom ≫
                  k) hX
    _ = eqToHom
          (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
          0 := by
            simpa [Category.assoc] using congrArg
              (fun k ↦
                eqToHom
                  (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D)
                    (i := i) hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm ≫
                  k) hCollapse
    _ = 0 := by
      simp [C', hZero]

/-- Helper for Lemma 10.102.2: in degree `i + 1`, projecting the normalized component isomorphism
to the reduced complex recovers the source-side tail projection. -/
theorem normalized_middle_component_iso_succ_hom_comp_fst
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
    (normalized_middle_component_iso_succ (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f (i.1 + 1) =
      (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
        eqToHom
          (reduced_complex_of_normalized_middle_X_eq_succ (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid).symm := by
  -- Expand the supported comparison in degree `i + 1` and move the first projection across the
  -- objectwise biproduct comparison.
  simp [normalized_middle_component_iso_succ, Category.assoc, biprodXIso_inv_fst]

/-- Helper for Lemma 10.102.2: in degree `i + 1`, projecting the normalized component isomorphism
to the identity disk recovers the source-side head projection. -/
theorem normalized_middle_component_iso_succ_hom_comp_snd
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
    (normalized_middle_component_iso_succ (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f (i.1 + 1) =
      (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd ≫
        eqToHom (identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm := by
  -- The second projection in degree `i + 1` is the split-off head factor of the source term.
  simp [normalized_middle_component_iso_succ, Category.assoc, biprodXIso_inv_snd]

/-- Helper for Lemma 10.102.2: in degree `i`, projecting the normalized component isomorphism to
the reduced complex recovers the target-side tail projection. -/
theorem normalized_middle_component_iso_castSucc_hom_comp_fst
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
    (normalized_middle_component_iso_castSucc (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f i.1 =
      (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫
        eqToHom
          (reduced_complex_of_normalized_middle_X_eq_castSucc (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid).symm := by
  -- Expand the supported comparison in degree `i` and move the first projection across the
  -- objectwise biproduct comparison.
  simp [normalized_middle_component_iso_castSucc, Category.assoc, biprodXIso_inv_fst]

/-- Helper for Lemma 10.102.2: in degree `i`, projecting the normalized component isomorphism to
the identity disk recovers the target-side head projection. -/
theorem normalized_middle_component_iso_castSucc_hom_comp_snd
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
    (normalized_middle_component_iso_castSucc (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f i.1 =
      (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.snd ≫
        eqToHom (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
  -- The second projection in degree `i` is the split-off head factor of the target term.
  simp [normalized_middle_component_iso_castSucc, Category.assoc, biprodXIso_inv_snd]

/-- Helper for Lemma 10.102.2: projecting the normalized middle map to the split-off head
summand records the identity block on that summand. -/
theorem normalized_middle_head_projection
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
    ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd =
      eSource.hom ≫ biprod.snd := by
  -- Project the normalized middle block to the rank-one head summand and cancel `eSource`.
  calc
    ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd =
        eSource.hom ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom) ≫ biprod.snd := by
          simp [Category.assoc]
    _ = eSource.hom ≫ biprod.map tailDiff (𝟙 _) ≫ biprod.snd := by
          rw [hmid]
    _ = eSource.hom ≫ biprod.snd := by
          simp [Category.assoc]

/-- Helper for Lemma 10.102.2: the middle differential carries the source head projection to the
target head projection at the chain-complex level. -/
theorem normalized_middle_head_projection_chain
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
    (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd =
      D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom ≫
        eTarget.hom ≫ biprod.snd := by
  -- First replace the normalized head projection by the middle differential in `diffAt`
  -- coordinates, then rewrite `diffAt` back to the chain-complex differential of `D`.
  calc
    (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd =
        (D.termIso i.succ).hom ≫ ModuleCat.ofHom (D.diffAt i) ≫
          eTarget.hom ≫ biprod.snd := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ (D.termIso i.succ).hom ≫ m)
            (normalized_middle_head_projection (R := R) (D := D) (i := i)
              (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) hmid).symm
    _ = D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom ≫
          eTarget.hom ≫ biprod.snd := by
          simpa [Category.assoc] using congrArg
            (fun m ↦ m ≫ eTarget.hom ≫ biprod.snd)
            (termIso_hom_comp_diffAt (R := R) D i)

/-- Helper for Lemma 10.102.2: away from the two supported degrees, the top-level normalized
component isomorphism collapses to the off-support formula after postcomposing with the reduced
projection. -/
theorem normalized_middle_component_iso_hom_comp_fst_of_ne_support
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
    {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f j =
      eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support (R := R) (D := D) (i := i)
          hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast).symm := by
  -- Route correction: first collapse the top-level `if` wrapper, then reuse the off-support
  -- projection formula already proved for the specialized component isomorphism.
  simpa [normalized_middle_component_iso, hjSucc, hjCast] using
    normalized_middle_component_iso_off_support_hom_comp_fst (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast

/-- Helper for Lemma 10.102.2: in degree `i + 1`, the top-level normalized component isomorphism
collapses to the supported source-side formula after postcomposing with the reduced projection. -/
theorem normalized_middle_component_iso_hom_comp_fst_succ
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
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid (i.1 + 1)).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f (i.1 + 1) =
      (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
        eqToHom
          (reduced_complex_of_normalized_middle_X_eq_succ (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid).symm := by
  have hjCast : i.1 + 1 ≠ i.1 := by
    omega
  -- Collapse the top-level `if` to the supported degree `i + 1`.
  simpa [normalized_middle_component_iso, hjCast] using
    normalized_middle_component_iso_succ_hom_comp_fst (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid

/-- Helper for Lemma 10.102.2: in degree `i`, the top-level normalized component isomorphism
collapses to the supported target-side formula after postcomposing with the reduced projection. -/
theorem normalized_middle_component_iso_hom_comp_fst_castSucc
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
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid i.1).hom ≫
        (biprodChainFst
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f i.1 =
      (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.fst ≫
        eqToHom
          (reduced_complex_of_normalized_middle_X_eq_castSucc (R := R) (D := D) (i := i)
            hsucc hcast eSource eTarget tailDiff hmid).symm := by
  have hjSucc : i.1 ≠ i.1 + 1 := by
    omega
  -- Collapse the top-level `if` to the supported degree `i`.
  simpa [normalized_middle_component_iso, hjSucc] using
    normalized_middle_component_iso_castSucc_hom_comp_fst (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid

/-- Helper for Lemma 10.102.2: away from the two supported degrees, the top-level normalized
component isomorphism collapses to the off-support formula after postcomposing with the
identity-disk projection. -/
theorem normalized_middle_component_iso_hom_comp_snd_of_ne_support
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
    {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid j).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f j =
      0 := by
  -- Route correction: again collapse the top-level `if` wrapper before using the specialized
  -- off-support projection formula.
  simpa [normalized_middle_component_iso, hjSucc, hjCast] using
    normalized_middle_component_iso_off_support_hom_comp_snd (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid hjSucc hjCast

/-- Helper for Lemma 10.102.2: in degree `i + 1`, the top-level normalized component isomorphism
collapses to the supported source-side formula after postcomposing with the identity-disk
projection. -/
theorem normalized_middle_component_iso_hom_comp_snd_succ
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
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid (i.1 + 1)).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f (i.1 + 1) =
      (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd ≫
        eqToHom (identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm := by
  have hjCast : i.1 + 1 ≠ i.1 := by
    omega
  -- Collapse the top-level `if` to the supported degree `i + 1`.
  simpa [normalized_middle_component_iso, hjCast] using
    normalized_middle_component_iso_succ_hom_comp_snd (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid

/-- Helper for Lemma 10.102.2: in degree `i`, the top-level normalized component isomorphism
collapses to the supported target-side formula after postcomposing with the identity-disk
projection. -/
theorem normalized_middle_component_iso_hom_comp_snd_castSucc
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
    (normalized_middle_component_iso (R := R) (D := D) (i := i) hsucc hcast
        eSource eTarget tailDiff hmid i.1).hom ≫
        (biprodChainSnd
          (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
            eSource eTarget tailDiff hmid).toChainComplex
          (identityDiskComplex (R := R) i)).f i.1 =
      (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.snd ≫
        eqToHom (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
  have hjSucc : i.1 ≠ i.1 + 1 := by
    omega
  -- Collapse the top-level `if` to the supported degree `i`.
  simpa [normalized_middle_component_iso, hjSucc] using
    normalized_middle_component_iso_castSucc_hom_comp_snd (R := R) (D := D) (i := i)
      hsucc hcast eSource eTarget tailDiff hmid


end FiniteFreeComplex

end
