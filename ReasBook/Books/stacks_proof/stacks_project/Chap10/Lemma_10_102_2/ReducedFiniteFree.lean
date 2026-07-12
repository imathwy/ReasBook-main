import StacksProject_2024.Chap10.Lemma_10_102_2.ReducedComplexSquares

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: at degree `i + 1`, the reduced object is already the module with
the split rank function. -/
theorem reduced_complex_of_normalized_middle_object_eq_splitRank_succ
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hsucc : D.rank i.succ = ns + 1) :
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i i.succ =
      ModuleCat.of R (Fin (splitRank D.rank i i.succ) → R) := by
  -- At the source split degree, both the reduced object and the split rank collapse to `ns`.
  calc
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i i.succ =
        ModuleCat.of R (Fin ns → R) := by
          simpa using reduced_complex_of_normalized_middle_object_eq_succ
            (R := R) (ns := ns) (nt := nt) D i
    _ = ModuleCat.of R (Fin (splitRank D.rank i i.succ) → R) := by
      simpa using congrArg (fun n ↦ ModuleCat.of R (Fin n → R))
        (splitRank_succ_eq_of_eq (n := D.rank) (i := i) hsucc).symm

/-- Helper for Lemma 10.102.2: at degree `i`, the reduced object is already the module with the
split rank function. -/
theorem reduced_complex_of_normalized_middle_object_eq_splitRank_castSucc
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hcast : D.rank i.castSucc = nt + 1) :
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i i.castSucc =
      ModuleCat.of R (Fin (splitRank D.rank i i.castSucc) → R) := by
  -- At the target split degree, both the reduced object and the split rank collapse to `nt`.
  calc
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i i.castSucc =
        ModuleCat.of R (Fin nt → R) := by
          simpa using reduced_complex_of_normalized_middle_object_eq_castSucc
            (R := R) (ns := ns) (nt := nt) D i
    _ = ModuleCat.of R (Fin (splitRank D.rank i i.castSucc) → R) := by
      simpa using congrArg (fun n ↦ ModuleCat.of R (Fin n → R))
        (splitRank_castSucc_eq_of_eq (n := D.rank) (i := i) hcast).symm

/-- Helper for Lemma 10.102.2: away from the two adjacent split degrees, the reduced object is
the original term of `D`. -/
theorem reduced_complex_of_normalized_middle_object_eq_of_ne_adjacent
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (j : Fin (e + 1))
    (hjSucc : j ≠ i.succ)
    (hjCast : j ≠ i.castSucc) :
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i j =
      D.toChainComplex.X j := by
  -- Away from the support, the reduced object is unchanged.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support
    (R := R) (ns := ns) (nt := nt) D i
  · intro h
    exact hjSucc (Fin.ext h)
  · intro h
    exact hjCast (Fin.ext h)

/-- Helper for Lemma 10.102.2: away from the two adjacent split degrees, the reduced object and
the split rank are both inherited unchanged from `D`. -/
theorem splitRank_module_eq_of_ne_adjacent
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (j : Fin (e + 1))
    (hjSucc : j ≠ i.succ)
    (hjCast : j ≠ i.castSucc) :
    ModuleCat.of R (Fin (D.rank j) → R) =
      ModuleCat.of R (Fin (splitRank D.rank i j) → R) := by
  -- Away from the support, the split rank agrees with the original displayed rank.
  simpa using congrArg (fun n ↦ ModuleCat.of R (Fin n → R))
    (splitRank_eq_of_ne_adjacent (n := D.rank) (i := i) hjSucc hjCast).symm

/-- Helper for Lemma 10.102.2: in degree `i + 1`, the identity-disk term is the standard free
rank-one module. -/
theorem identityDiskComplex_X_eq_succ
    (i : Fin e) :
    (identityDiskComplex (R := R) i).X (i.1 + 1) =
      ModuleCat.of R (Fin 1 → R) := by
  -- The identity disk is supported with rank one in degree `i + 1`.
  rw [identityDiskComplex, ChainComplex.of_x, identityDiskRank_succ]

/-- Helper for Lemma 10.102.2: in degree `i`, the identity-disk term is again the standard free
rank-one module. -/
theorem identityDiskComplex_X_eq_castSucc
    (i : Fin e) :
    (identityDiskComplex (R := R) i).X i.1 =
      ModuleCat.of R (Fin 1 → R) := by
  -- The other supported degree carries the same rank-one term.
  rw [identityDiskComplex, ChainComplex.of_x, identityDiskRank_castSucc]

/-- Helper for Lemma 10.102.2: the identity-disk chain differential vanishes away from its
middle supported degree. -/
theorem identityDiskComplex_d_eq_zero_of_ne
    (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
    (identityDiskComplex (R := R) i).d (j + 1) j = 0 := by
  -- Reduce the chain differential to the matrix-level zero differential already proved in `Basic`.
  simp [identityDiskComplex, ChainComplex.of_d, identityDiskDifferential_eq_zero_of_ne (i := i) hj]
  rfl

/-- Helper for Lemma 10.102.2: at the supported degree, the identity-disk matrix differential is
heterogeneously the identity on the rank-one standard module. -/
private theorem identityDiskDifferential_heq_id
    (i : Fin e) :
    identityDiskDifferential (R := R) i i.1 ≍ 𝟙 (ModuleCat.of R (Fin 1 → R)) := by
  -- Expose the supported matrix while keeping the rank transports in one small proof.
  change ModuleCat.ofHom (Matrix.toLinearMapRight' (identityDiskMatrix (R := R) i i.1)) ≍
    𝟙 (ModuleCat.of R (Fin 1 → R))
  unfold identityDiskMatrix identityDiskRank
  rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
  -- Once both ranks are reduced to `1`, the single matrix entry acts as the identity.
  apply heq_of_eq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  ext j
  fin_cases j
  simp [Matrix.toLinearMapRight'_apply, Matrix.vecMul, dotProduct]

/-- Helper for Lemma 10.102.2: after identifying both supported identity-disk terms with the
standard rank-one module, the supported identity-disk differential is the identity. -/
theorem identityDiskComplex_eqToHom_symm_comp_d
    (i : Fin e) :
    eqToHom (identityDiskComplex_X_eq_succ (R := R) (e := e) i).symm ≫
        (identityDiskComplex (R := R) i).d (i.1 + 1) i.1 =
      eqToHom (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i).symm := by
  have hd_heq : (identityDiskComplex (R := R) i).d (i.1 + 1) i.1 ≍
      𝟙 (ModuleCat.of R (Fin 1 → R)) := by
    -- Unfold only the chain-complex wrapper, then reuse the matrix-level computation.
    simpa [identityDiskComplex, ChainComplex.of_d] using
      identityDiskDifferential_heq_id (R := R) (i := i)
  -- The two object identifications conjugate the heterogeneous identity into the required
  -- equality with `eqToHom` transports.
  rw [CategoryTheory.eqToHom_comp_iff]
  exact (CategoryTheory.conj_eqToHom_iff_heq
    ((identityDiskComplex (R := R) i).d (i.1 + 1) i.1)
    (𝟙 (ModuleCat.of R (Fin 1 → R)))
    (identityDiskComplex_X_eq_succ (R := R) (e := e) i)
    (identityDiskComplex_X_eq_castSucc (R := R) (e := e) i)).2 hd_heq

/-- Helper for Lemma 10.102.2: the reduced finite free complex has the expected displayed ranks
and term identifications. -/
noncomputable def reduced_complex_of_normalized_middle_termIso
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hsucc : D.rank i.succ = ns + 1)
    (hcast : D.rank i.castSucc = nt + 1)
    (j : Fin (e + 1)) :
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i j ≅
      ModuleCat.of R (Fin (splitRank D.rank i j) → R) :=
  if hjSucc : j = i.succ then
    Eq.ndrec
      (motive := fun k : Fin (e + 1) ↦
        reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i k ≅
          ModuleCat.of R (Fin (splitRank D.rank i k) → R))
      (eqToIso <|
        reduced_complex_of_normalized_middle_object_eq_splitRank_succ
          (R := R) (ns := ns) (nt := nt) D i hsucc)
      hjSucc.symm
  else if hjCast : j = i.castSucc then
    Eq.ndrec
      (motive := fun k : Fin (e + 1) ↦
        reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i k ≅
          ModuleCat.of R (Fin (splitRank D.rank i k) → R))
      (eqToIso <|
        reduced_complex_of_normalized_middle_object_eq_splitRank_castSucc
          (R := R) (ns := ns) (nt := nt) D i hcast)
      hjCast.symm
  else
    eqToIso
        (reduced_complex_of_normalized_middle_object_eq_of_ne_adjacent
          (R := R) (ns := ns) (nt := nt) D i j hjSucc hjCast) ≪≫
      D.termIso j ≪≫
      eqToIso
        (splitRank_module_eq_of_ne_adjacent
          (R := R) (ns := ns) (nt := nt) D i j hjSucc hjCast)

/-- Helper for Lemma 10.102.2: the normalized-middle data determines an explicit reduced finite
free complex with the split rank function. -/
noncomputable def reduced_complex_of_normalized_middle
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
    _root_.FiniteFreeComplex R e where
  toChainComplex :=
    ChainComplex.of
      (reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i)
      (reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff)
      (reduced_complex_of_normalized_middle_d_sq (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) (tailDiff := tailDiff) hmid)
  isZero_toChainComplex_X := fun j hj => by
    -- Above degree `e`, the reduced object is unchanged from `D`, so the original vanishing
    -- proof applies verbatim.
    have hjSucc : j ≠ i.1 + 1 := by omega
    have hjCast : j ≠ i.1 := by omega
    rw [ChainComplex.of_x]
    rw [reduced_complex_of_normalized_middle_object_eq_of_ne_support
      (R := R) (ns := ns) (nt := nt) D i hjSucc hjCast]
    exact D.isZero_toChainComplex_X j hj
  rank := splitRank D.rank i
  termIso := reduced_complex_of_normalized_middle_termIso
    (R := R) (ns := ns) (nt := nt) D i hsucc hcast

/-- Helper for Lemma 10.102.2: the reduced chain complex has the expected source tail term in
degree `i + 1`. -/
theorem reduced_complex_of_normalized_middle_X_eq_succ
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
    (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
      eSource eTarget tailDiff hmid).toChainComplex.X (i.1 + 1) =
      ModuleCat.of R (Fin ns → R) := by
  -- The chain-level source term is definitionally the reduced object in degree `i + 1`.
  change reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i (i.1 + 1) =
    ModuleCat.of R (Fin ns → R)
  exact reduced_complex_of_normalized_middle_object_eq_succ (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: the reduced chain complex has the expected target tail term in
degree `i`. -/
theorem reduced_complex_of_normalized_middle_X_eq_castSucc
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
    (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
      eSource eTarget tailDiff hmid).toChainComplex.X i.1 =
      ModuleCat.of R (Fin nt → R) := by
  -- The chain-level target term is definitionally the reduced object in degree `i`.
  change reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i i.1 =
    ModuleCat.of R (Fin nt → R)
  exact reduced_complex_of_normalized_middle_object_eq_castSucc (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: away from the two supported degrees, the reduced chain complex
keeps the original term of `D`. -/
theorem reduced_complex_of_normalized_middle_X_eq_of_ne_support
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
    (reduced_complex_of_normalized_middle (R := R) (D := D) (i := i) hsucc hcast
      eSource eTarget tailDiff hmid).toChainComplex.X j =
      D.toChainComplex.X j := by
  -- Off support, the reduced chain-complex object is the inherited object of `D`.
  change reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i j =
    D.toChainComplex.X j
  exact reduced_complex_of_normalized_middle_object_eq_of_ne_support
    (R := R) (ns := ns) (nt := nt) D i hjSucc hjCast

/-- Helper for Lemma 10.102.2: in the lower branch, the target transport agrees with the
off-support reduced-complex transport. -/
theorem reduced_complex_of_normalized_middle_lower_target_off_support_eqToHom
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
    (hUpper : j ≠ i.1 + 1) (hMid : j ≠ i.1) (hLower : j + 1 = i.1) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower).symm =
      eqToHom
        (reduced_complex_of_normalized_middle_X_eq_of_ne_support
          (R := R) (D := D) (i := i) hsucc hcast eSource eTarget tailDiff hmid
          hUpper hMid).symm := by
  -- Both proofs identify the same reduced target object with the inherited object of `D`;
  -- proof irrelevance lets the two resulting `eqToHom`s coincide.
  congr 1

end FiniteFreeComplex

end
