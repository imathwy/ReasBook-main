import Mathlib
import stacks_project.Chap10.Situation_10_102_1

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}

/-- The `a,b` coordinate of the differential `C_{i + 1} → C_i` in the chosen standard bases. -/
def diffEntry (C : _root_.FiniteFreeComplex R e) (i : Fin e)
    (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) : R :=
  C.diffAt i (Pi.single a 1) b

/-- The rank function obtained by removing one basis vector in degrees `i + 1` and `i`. -/
def splitRank (n : Fin (e + 1) → ℕ) (i : Fin e) : Fin (e + 1) → ℕ :=
  fun j ↦ if j = i.succ ∨ j = i.castSucc then n j - 1 else n j

private def identityDiskRank (i : Fin e) (j : ℕ) : ℕ :=
  if j = i.1 + 1 ∨ j = i.1 then 1 else 0

private def identityDiskMatrix (i : Fin e) (j : ℕ) :
    Matrix (Fin (identityDiskRank i (j + 1))) (Fin (identityDiskRank i j)) R :=
  fun _ _ ↦ if j = i.1 then 1 else 0

private abbrev identityDiskDifferential (i : Fin e) (j : ℕ) :
    ModuleCat.of R (Fin (identityDiskRank i (j + 1)) → R) ⟶
      ModuleCat.of R (Fin (identityDiskRank i j) → R) :=
  ModuleCat.ofHom ((identityDiskMatrix i j).toLinearMapRight')

/-- Helper for Lemma 10.102.2: the identity-disk differential vanishes away from the supported
degree `i`. -/
private theorem identityDiskDifferential_eq_zero_of_ne (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
    identityDiskDifferential i j =
      (0 :
        ModuleCat.of R (Fin (identityDiskRank i (j + 1)) → R) ⟶
          ModuleCat.of R (Fin (identityDiskRank i j) → R)) := by
  -- Outside degree `i`, the defining matrix is entrywise zero.
  have hMatrix :
      identityDiskMatrix i j =
        (0 : Matrix (Fin (identityDiskRank i (j + 1))) (Fin (identityDiskRank i j)) R) := by
    ext a b
    simp [identityDiskMatrix, hj]
  let M0 : Matrix (Fin (identityDiskRank i (j + 1))) (Fin (identityDiskRank i j)) R := 0
  have hLinear :
      M0.toLinearMapRight' =
        (0 :
          (Fin (identityDiskRank i (j + 1)) → R) →ₗ[R]
            Fin (identityDiskRank i j) → R) := by
    ext x y
    simp [M0]
  rw [identityDiskDifferential, hMatrix]
  change ModuleCat.ofHom (M0.toLinearMapRight') = 0
  rw [hLinear]
  rfl

private theorem identityDiskDifferential_sq (i : Fin e) (j : ℕ) :
    identityDiskDifferential i (j + 1) ≫ identityDiskDifferential i j =
      (0 :
        ModuleCat.of R (Fin (identityDiskRank i (j + 2)) → R) ⟶
          ModuleCat.of R (Fin (identityDiskRank i j) → R)) := by
  by_cases hj : j = i.1
  · -- In the supported degree, the next differential already vanishes.
    subst hj
    rw [identityDiskDifferential_eq_zero_of_ne (i := i) (j := i.1 + 1)]
    · simp
    · omega
  · -- Away from degree `i`, the current differential itself is zero.
    rw [identityDiskDifferential_eq_zero_of_ne (i := i) (j := j) hj, comp_zero]

/-- The two-term identity complex `… → 0 → R → R → 0 → …` supported in degrees `i + 1` and `i`.
-/
def identityDiskComplex (i : Fin e) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (fun j ↦ ModuleCat.of R (Fin (identityDiskRank i j) → R))
    (identityDiskDifferential i)
    (identityDiskDifferential_sq i)

/-- Helper for Lemma 10.102.2: away from the supported degrees `i + 1` and `i`, the identity-disk
rank function is zero. -/
private theorem identityDiskRank_eq_zero_of_ne_support
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    identityDiskRank i j = 0 := by
  -- Both support tests in the definition are false away from the two distinguished degrees.
  simp [identityDiskRank, hjSucc, hjCast]

/-- Helper for Lemma 10.102.2: away from the supported degrees `i + 1` and `i`, the identity-disk
complex has a zero term. -/
private theorem identityDiskComplex_X_isZero_of_ne_support
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    IsZero ((identityDiskComplex (R := R) i).X j) := by
  -- Rewrite the term to the empty free module and use that it is subsingleton.
  have hrank : identityDiskRank i j = 0 :=
    identityDiskRank_eq_zero_of_ne_support (e := e) (i := i) (j := j) hjSucc hjCast
  simpa [identityDiskComplex,
    hrank] using
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Fin 0 → R)))

/-- Helper for Lemma 10.102.2: at the supported source degree `i + 1`, the identity-disk rank is
`1`. -/
private theorem identityDiskRank_succ (i : Fin e) :
    identityDiskRank i (i.1 + 1) = 1 := by
  -- The support condition holds exactly in degree `i + 1`.
  simp [identityDiskRank]

/-- Helper for Lemma 10.102.2: at the supported target degree `i`, the identity-disk rank is
`1`. -/
private theorem identityDiskRank_castSucc (i : Fin e) :
    identityDiskRank i i.1 = 1 := by
  -- The support condition holds exactly in degree `i`.
  simp [identityDiskRank]

/-- Helper for Lemma 10.102.2: at the supported degree `i`, the identity-disk differential is the
identity map on the rank-one summand. -/
private theorem identityDiskDifferential_eq_id (i : Fin e) :
    identityDiskDifferential (R := R) i i.1 =
      eqToHom (by
        change ModuleCat.of R (Fin (identityDiskRank i (i.1 + 1)) → R) =
          ModuleCat.of R (Fin (identityDiskRank i i.1) → R)
        rw [identityDiskRank_succ, identityDiskRank_castSucc]) := by
  -- TODO: rewrite both ranks to `1`, then prove the resulting `1 × 1` matrix map agrees with the
  -- transported identity by extensionality on the unique basis coordinate.
  sorry

/-- Helper for Lemma 10.102.2: away from the two adjacent split degrees, the reduced rank agrees
with the original displayed rank. -/
private theorem splitRank_eq_of_ne_adjacent
    (n : Fin (e + 1) → ℕ) (i : Fin e) {j : Fin (e + 1)}
    (hjSucc : j ≠ i.succ) (hjCast : j ≠ i.castSucc) :
    splitRank n i j = n j := by
  -- Outside the two distinguished degrees, both tests in `splitRank` are false.
  simp [splitRank, hjSucc, hjCast]

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the reduced rank is the predecessor of the
original rank, hence equals `ns` under the successor decomposition. -/
private theorem splitRank_succ_eq_of_eq
    (n : Fin (e + 1) → ℕ) (i : Fin e) {ns : ℕ}
    (hsucc : n i.succ = ns + 1) :
    splitRank n i i.succ = ns := by
  -- The source degree is one of the two split degrees, so the definition subtracts exactly `1`.
  simp [splitRank, hsucc]

/-- Helper for Lemma 10.102.2: at degree `i`, the reduced rank is the predecessor of the original
rank, hence equals `nt` under the successor decomposition. -/
private theorem splitRank_castSucc_eq_of_eq
    (n : Fin (e + 1) → ℕ) (i : Fin e) {nt : ℕ}
    (hcast : n i.castSucc = nt + 1) :
    splitRank n i i.castSucc = nt := by
  -- The target degree is the other split degree, so the definition subtracts exactly `1`.
  simp [splitRank, hcast]

/-- Helper for Lemma 10.102.2: the standard free module on `Fin (n + 1)` splits as the tail
coordinates together with the distinguished head coordinate. -/
private noncomputable def splitOffUnitLinearEquiv (n : ℕ) :
    (Fin (n + 1) → R) ≃ₗ[R] (Fin n → R) × (Fin 1 → R) :=
  let e₀ : (Fin (n + 1) → R) ≃ₗ[R] (R × (Fin n → R)) :=
    (LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n)) ≪≫ₗ
      LinearEquiv.piOptionEquivProd R
  let e₁ : (R × (Fin n → R)) ≃ₗ[R] ((Fin n → R) × R) :=
    LinearEquiv.prodComm R R (Fin n → R)
  let e₂ : ((Fin n → R) × R) ≃ₗ[R] ((Fin n → R) × (Fin 1 → R)) :=
    LinearEquiv.prodCongr (LinearEquiv.refl R (Fin n → R))
      (LinearEquiv.funUnique (Fin 1) R R).symm
  e₀ ≪≫ₗ e₁ ≪≫ₗ e₂

/-- Helper for Lemma 10.102.2: the head-tail linear equivalence reads the tail coordinates as the
`Fin.succ` entries of the original vector. -/
private theorem splitOffUnitLinearEquiv_apply_tail (n : ℕ) (x : Fin (n + 1) → R) :
    (splitOffUnitLinearEquiv (R := R) n x).1 = fun k ↦ x k.succ := by
  -- Unfold the explicit equivalence and simplify the `Fin`-reindexing on the first factor.
  ext k
  change ((LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) x) (some k)) = x k.succ
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', finSuccEquiv_symm_some]

/-- Helper for Lemma 10.102.2: the head-tail linear equivalence records the distinguished head
coordinate in the rank-one factor. -/
private theorem splitOffUnitLinearEquiv_apply_head (n : ℕ) (x : Fin (n + 1) → R) :
    (splitOffUnitLinearEquiv (R := R) n x).2 = fun _ ↦ x 0 := by
  -- The second factor is the `none`/head coordinate, rewritten as a function on `Fin 1`.
  ext k
  fin_cases k
  change ((LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) x) none) = x 0
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', finSuccEquiv_symm_none]

/-- Helper for Lemma 10.102.2: the inverse head-tail linear equivalence reconstructs the original
vector by putting the rank-one factor in coordinate `0` and the tail factor in coordinates
`Fin.succ k`. -/
private theorem splitOffUnitLinearEquiv_symm_apply_head_tail
    (n : ℕ) (x : Fin n → R) (y : Fin 1 → R) :
    ((splitOffUnitLinearEquiv (R := R) n).symm (x, y)) 0 = y 0 ∧
      ∀ k : Fin n, ((splitOffUnitLinearEquiv (R := R) n).symm (x, y)) k.succ = x k := by
  let z := ((splitOffUnitLinearEquiv (R := R) n).symm (x, y))
  have hz : splitOffUnitLinearEquiv (R := R) n z = (x, y) := by
    -- Apply the left inverse of the explicit splitting equivalence to the chosen pair.
    simpa [z] using
      (LinearEquiv.apply_symm_apply (splitOffUnitLinearEquiv (R := R) n) (x, y))
  constructor
  · -- The head coordinate is recovered from the rank-one factor.
    have hhead :
        (splitOffUnitLinearEquiv (R := R) n z).2 = y := by
      simpa using congrArg Prod.snd hz
    have hhead_eval :
        ((splitOffUnitLinearEquiv (R := R) n z).2) 0 = z 0 := by
      simpa using
        congrArg (fun f : Fin 1 → R => f 0)
          (splitOffUnitLinearEquiv_apply_head (R := R) n z)
    calc
      z 0 = ((splitOffUnitLinearEquiv (R := R) n z).2) 0 := by
        symm
        exact hhead_eval
      _ = y 0 := by
        simpa using congrArg (fun f : Fin 1 → R => f 0) hhead
  · intro k
    -- Each tail coordinate is recovered from the first factor.
    have htail :
        (splitOffUnitLinearEquiv (R := R) n z).1 = x := by
      simpa using congrArg Prod.fst hz
    have htail_eval :
        ((splitOffUnitLinearEquiv (R := R) n z).1) k = z k.succ := by
      simpa using
        congrArg (fun f : Fin n → R => f k)
          (splitOffUnitLinearEquiv_apply_tail (R := R) n z)
    calc
      z k.succ = ((splitOffUnitLinearEquiv (R := R) n z).1) k := by
        symm
        exact htail_eval
      _ = x k := by
        simpa using congrArg (fun f : Fin n → R => f k) htail

/-- Helper for Lemma 10.102.2: reconstructing a vector from the head-tail splitting decomposes it
as the distinguished head basis vector together with the tail basis vectors. -/
private theorem split_off_unit_linear_equiv_symm_eq_head_tail_sum
    (n : ℕ) (x : Fin n → R) (y : Fin 1 → R) :
    (splitOffUnitLinearEquiv (R := R) n).symm (x, y) =
      (Pi.single 0 (y 0) : Fin (n + 1) → R) +
        ∑ k : Fin n, x k • (Pi.single k.succ (1 : R) : Fin (n + 1) → R) := by
  -- The inverse splitting is determined by its value on the head coordinate and on each tail
  -- coordinate, and those are already available from the previous helper.
  ext j
  obtain ⟨hhead, htail⟩ :=
    splitOffUnitLinearEquiv_symm_apply_head_tail (R := R) n x y
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · -- At coordinate `0`, only the distinguished head summand contributes.
    simp [hhead]
  · -- At a tail coordinate, only the matching `Pi.single k.succ 1` term survives.
    rw [htail]
    simp
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      have hne : j.succ ≠ k.succ := by
        intro h
        exact hj (by simpa using h)
      have hne' : k.succ ≠ j.succ := by
        simpa using hne.symm
      simp [Pi.single_eq_of_ne hne']
    · simp

/-- Helper for Lemma 10.102.2: evaluating the swapped coordinate system at the distinguished head
coordinate reads the original vector in coordinate `a`. -/
private theorem piCongrLeft_swap_apply_zero
    {n : ℕ} (a : Fin (n + 1)) (x : Fin (n + 1) → R) :
    (LinearEquiv.piCongrLeft R (fun _ : Fin (n + 1) ↦ R) (Equiv.swap 0 a) x) 0 = x a := by
  -- The head coordinate after swapping is exactly the original `a`-coordinate.
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', Equiv.swap_apply_left]

/-- Helper for Lemma 10.102.2: the inverse head-tail splitting sends the pure head vector in the
product model to the distinguished basis vector in `Fin (n + 1) → R`. -/
private theorem splitOffUnitLinearEquiv_symm_apply_pure_head
    (n : ℕ) :
    (splitOffUnitLinearEquiv (R := R) n).symm (0, fun _ ↦ (1 : R)) =
      (Pi.single 0 (1 : R) : Fin (n + 1) → R) := by
  -- The previous head-tail coordinate formula determines the inverse splitting on the head basis.
  ext j
  obtain ⟨hhead, htail⟩ :=
    splitOffUnitLinearEquiv_symm_apply_head_tail (R := R) n 0 (fun _ ↦ (1 : R))
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
  · simpa using hhead
  · simpa [htail k]

/-- Helper for Lemma 10.102.2: if a linear map fixes the distinguished head basis vector and sends
each tail basis vector to something with zero head coordinate, then it preserves the head
coordinate on every vector written in head-tail form. -/
private theorem map_head_coordinate_of_split_off_unit_decomposition
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hhead : f (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (f ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))) 0 = y 0 := by
  have hy :
      (Pi.single 0 (y 0) : Fin (ns + 1) → R) =
        (y 0) • (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
    -- Rewrite the head basis contribution as a scalar multiple of the standard basis vector.
    ext j
    by_cases hj : j = 0
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  -- Expand the source vector along the standard basis and read only coordinate `0` after applying
  -- the hypotheses on the head basis vector and the tail basis vectors.
  rw [split_off_unit_linear_equiv_symm_eq_head_tail_sum (R := R) ns x y, hy,
    map_add, map_sum, map_smul]
  simp [hhead, htail]

/-- Helper for Lemma 10.102.2: after splitting off the head coordinate, the normalized basis data
already forces the induced map on the rank-one summand to be the identity. -/
private theorem split_off_unit_linear_equiv_apply_head_of_normalized_map
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hhead : f (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (splitOffUnitLinearEquiv (R := R) nt
      (f ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y)))).2 = y := by
  -- The codomain head factor is a `Fin 1`-indexed function, so evaluating at the unique
  -- coordinate reduces the claim to the previous head-coordinate computation.
  ext j
  fin_cases j
  rw [splitOffUnitLinearEquiv_apply_head]
  simpa using
    map_head_coordinate_of_split_off_unit_decomposition
      (R := R) f hhead htail x y

/-- Helper for Lemma 10.102.2: under the normalized basis hypotheses, each tail basis vector has
zero component in the split-off head summand. -/
private theorem split_off_unit_linear_equiv_apply_head_of_tail_basis
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0)
    (j : Fin ns) :
    (splitOffUnitLinearEquiv (R := R) nt (f (Pi.single j.succ (1 : R)))).2 = 0 := by
  -- Read the head factor through the explicit splitting formula and apply the head-coordinate
  -- vanishing hypothesis on the chosen tail basis vector.
  ext k
  fin_cases k
  rw [splitOffUnitLinearEquiv_apply_head]
  simpa using htail j

/-- Helper for Lemma 10.102.2: turning the head-tail linear equivalence into a `ModuleCat`
isomorphism gives the canonical biproduct splitting used later in the chain-level argument. -/
private noncomputable def splitOffUnitModuleIso (n : ℕ) :
    ModuleCat.of R (Fin (n + 1) → R) ≅
      biprod (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R)) :=
  (splitOffUnitLinearEquiv (R := R) n).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R))).symm

/-- Helper for Lemma 10.102.2: replace the chosen coordinate identifications only in degrees
`i + 1` and `i` by postcomposing with the specified automorphisms of the displayed standard free
modules. -/
private noncomputable def recoordinateTermIsoAtAdjacentDegrees
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R))
    (j : Fin (e + 1)) :
    C.toChainComplex.X j ≅ ModuleCat.of R (Fin (C.rank j) → R) :=
  if h : j = i.succ then
    Eq.ndrec
      (motive := fun k : Fin (e + 1) ↦
        C.toChainComplex.X k ≅ ModuleCat.of R (Fin (C.rank k) → R))
      (C.termIso i.succ ≪≫ uSucc) h.symm
  else if h' : j = i.castSucc then
    Eq.ndrec
      (motive := fun k : Fin (e + 1) ↦
        C.toChainComplex.X k ≅ ModuleCat.of R (Fin (C.rank k) → R))
      (C.termIso i.castSucc ≪≫ uCast) h'.symm
  else
    C.termIso j

/-- Helper for Lemma 10.102.2: the owner-level recoordinated finite free complex keeps the same
underlying chain complex and rank function, changing only the two adjacent coordinate
identifications used in the source proof's basis changes. -/
private noncomputable def recoordinateAtAdjacentDegrees
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    _root_.FiniteFreeComplex R e where
  toChainComplex := C.toChainComplex
  isZero_toChainComplex_X := C.isZero_toChainComplex_X
  rank := C.rank
  termIso := recoordinateTermIsoAtAdjacentDegrees C i uSucc uCast

/-- Helper for Lemma 10.102.2: the recoordinated owner does not alter the underlying chain
complex. -/
@[simp] private theorem recoordinateAtAdjacentDegrees_toChainComplex
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).toChainComplex = C.toChainComplex := by
  -- The record update keeps the chain-complex owner unchanged.
  rfl

/-- Helper for Lemma 10.102.2: the recoordinated owner preserves the displayed rank function. -/
@[simp] private theorem recoordinateAtAdjacentDegrees_rank
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).rank = C.rank := by
  -- Only the coordinate identifications change; the displayed ranks do not.
  rfl

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the recoordinated owner uses the original
coordinate isomorphism followed by the chosen source automorphism. -/
@[simp] private theorem recoordinateAtAdjacentDegrees_termIso_succ
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).termIso i.succ =
      C.termIso i.succ ≪≫ uSucc := by
  -- The first branch of the record update is the source-degree basis change.
  simp only [recoordinateAtAdjacentDegrees, recoordinateTermIsoAtAdjacentDegrees, dite_true]

/-- Helper for Lemma 10.102.2: at degree `i`, the recoordinated owner uses the original
coordinate isomorphism followed by the chosen target automorphism. -/
@[simp] private theorem recoordinateAtAdjacentDegrees_termIso_castSucc
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).termIso i.castSucc =
      C.termIso i.castSucc ≪≫ uCast := by
  -- The `i` branch is selected after ruling out the impossible equality `i = i + 1`.
  have hne : i.castSucc ≠ i.succ := by
    intro h
    have hval : i.1 = i.1 + 1 := congrArg Fin.val h
    omega
  simp only [recoordinateAtAdjacentDegrees, recoordinateTermIsoAtAdjacentDegrees, hne, dite_false,
    dite_true]

/-- Helper for Lemma 10.102.2: away from degrees `i + 1` and `i`, the recoordinated owner keeps
the original coordinate isomorphism. -/
@[simp] private theorem recoordinateAtAdjacentDegrees_termIso_of_ne
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R))
    (j : Fin (e + 1))
    (hjSucc : j ≠ i.succ)
    (hjCast : j ≠ i.castSucc) :
    (recoordinateAtAdjacentDegrees C i uSucc uCast).termIso j = C.termIso j := by
  -- Outside the two adjacent degrees, both `if` branches collapse to the original coordinates.
  simp only [recoordinateAtAdjacentDegrees, recoordinateTermIsoAtAdjacentDegrees, hjSucc, hjCast,
    dite_false]

/-- Helper for Lemma 10.102.2: after recoordinating only in degrees `i + 1` and `i`, the middle
differential is conjugated by exactly those two chosen automorphisms. -/
@[simp] private theorem recoordinateAtAdjacentDegrees_diffAt
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (uSucc : ModuleCat.of R (Fin (C.rank i.succ) → R) ≅
      ModuleCat.of R (Fin (C.rank i.succ) → R))
    (uCast : ModuleCat.of R (Fin (C.rank i.castSucc) → R) ≅
      ModuleCat.of R (Fin (C.rank i.castSucc) → R)) :
    ModuleCat.ofHom ((recoordinateAtAdjacentDegrees C i uSucc uCast).diffAt i) =
      uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uCast.hom := by
  let D := recoordinateAtAdjacentDegrees C i uSucc uCast
  -- Put the recoordinated differential into the adjacent-degree normal form where the two
  -- modified `termIso`s are visible to rewriting.
  change ModuleCat.ofHom
      (((D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom).hom) =
    uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uCast.hom
  -- Expand the original differential in the same adjacent-degree coordinates.
  change (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom =
    uSucc.inv ≫ ((C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫ (C.termIso i.castSucc).hom) ≫
      uCast.hom
  -- After that normalization, the two updated coordinate isomorphisms rewrite directly.
  rw [recoordinateAtAdjacentDegrees_termIso_succ (C := C) (i := i) (uSucc := uSucc)
      (uCast := uCast)]
  rw [recoordinateAtAdjacentDegrees_termIso_castSucc (C := C) (i := i) (uSucc := uSucc)
      (uCast := uCast)]
  -- The recoordinated owner keeps the same underlying differential, so only associativity remains.
  change (uSucc.inv ≫ (C.termIso i.succ).inv) ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
      (C.termIso i.castSucc).hom ≫ uCast.hom =
    uSucc.inv ≫ (C.termIso i.succ).inv ≫ C.toChainComplex.d (i.1 + 1) i.1 ≫
      (C.termIso i.castSucc).hom ≫ uCast.hom
  simp [Category.assoc]

/-- Helper for Lemma 10.102.2: a unit coordinate in `C.diffAt i` forces the source rank
`rank(C_{i + 1})` to be positive. -/
private theorem rank_succ_pos_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    0 < C.rank i.succ := by
  -- Any witnessed source coordinate already gives a nonempty `Fin`, hence positive rank.
  rcases hunit with ⟨a, -, -⟩
  exact lt_of_le_of_lt (Nat.zero_le a.1) a.2

/-- Helper for Lemma 10.102.2: a unit coordinate in `C.diffAt i` forces the target rank
`rank(C_i)` to be positive. -/
private theorem rank_castSucc_pos_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    0 < C.rank i.castSucc := by
  -- Any witnessed target coordinate already gives a nonempty `Fin`, hence positive rank.
  rcases hunit with ⟨-, b, -⟩
  exact lt_of_le_of_lt (Nat.zero_le b.1) b.2

/-- Helper for Lemma 10.102.2: the two ranks adjacent to a unit differential entry can be written
as successors, so the distinguished coordinates can be moved to `0` and split off. -/
private theorem exists_rank_eq_succ_of_isUnit_diffEntry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (hunit :
      ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc), IsUnit (C.diffEntry i a b)) :
    ∃ ns nt : ℕ, C.rank i.succ = ns + 1 ∧ C.rank i.castSucc = nt + 1 := by
  -- Repackage the positivity forced by `hunit` into successor decompositions of the two ranks.
  obtain ⟨ns, hs⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (rank_succ_pos_of_isUnit_diffEntry (C := C) (i := i) hunit))
  obtain ⟨nt, ht⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (rank_castSucc_pos_of_isUnit_diffEntry (C := C) (i := i) hunit))
  exact ⟨ns, nt, hs, ht⟩

/-- Helper for Lemma 10.102.2: once the normalized middle differential has zero off-diagonal
components and identity on the distinguished rank-one summand, it is exactly the biproduct map
of its tail component and the identity. -/
private theorem eq_biprod_map_tail_identity_of_components
    {X₁ Y₁ Y₂ : ModuleCat R}
    (F : biprod X₁ Y₂ ⟶ biprod Y₁ Y₂)
    (h_inl_snd : biprod.inl ≫ F ≫ biprod.snd = 0)
    (h_inr_fst : biprod.inr ≫ F ≫ biprod.fst = 0)
    (h_inr_snd : biprod.inr ≫ F ≫ biprod.snd = 𝟙 Y₂) :
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 Y₂) := by
  -- Compare the two maps on the two source summands separately.
  refine biprod.hom_ext' F (biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 Y₂)) ?_ ?_
  · -- On the tail summand, the first component is tautological and the second vanishes.
    refine biprod.hom_ext _ _ ?_ ?_
    · simp
    · simpa [Category.assoc] using h_inl_snd
  · -- On the distinguished head summand, the tail component vanishes and the head is the identity.
    refine biprod.hom_ext _ _ ?_ ?_
    · simpa [Category.assoc] using h_inr_fst
    · simpa [Category.assoc] using h_inr_snd

/-- Helper for Lemma 10.102.2: the explicit `ModuleCat` product comparison sends the binary
biproduct to the usual first projection. -/
private theorem biprodIsoProd_hom_comp_fst (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst R M N) = biprod.fst := by
  -- This is the left component equation of the limit-point uniqueness isomorphism.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_left] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.left)

/-- Helper for Lemma 10.102.2: the explicit `ModuleCat` product comparison sends the binary
biproduct to the usual second projection. -/
private theorem biprodIsoProd_hom_comp_snd (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd R M N) = biprod.snd := by
  -- This is the right component equation of the same uniqueness isomorphism.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_right] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.right)

/-- Helper for Lemma 10.102.2: under the explicit product model of a biproduct, the left summand
is the usual product inclusion into the first factor. -/
private theorem biprodIsoProd_inl_hom (M N : ModuleCat R) :
    biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inl R M N) := by
  -- Compare the two maps after applying the explicit first and second projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change ((biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.fst R M N)).hom x) = x
    simp [biprodIsoProd_hom_comp_fst]
  · change ((biprod.inl ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.snd R M N)).hom x) = 0
    simp [biprodIsoProd_hom_comp_snd]

/-- Helper for Lemma 10.102.2: under the explicit product model of a biproduct, the right summand
is the usual product inclusion into the second factor. -/
private theorem biprodIsoProd_inr_hom (M N : ModuleCat R) :
    biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inr R M N) := by
  -- Again compare on the two explicit product projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  apply Prod.ext
  · change ((biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.fst R M N)).hom y) = 0
    simp [biprodIsoProd_hom_comp_fst]
  · change ((biprod.inr ≫ (ModuleCat.biprodIsoProd M N).hom ≫
        ModuleCat.ofHom (LinearMap.snd R M N)).hom y) = y
    simp [biprodIsoProd_hom_comp_snd]

/-- Helper for Lemma 10.102.2: the explicit product comparison sends an element of the left
biproduct summand to the corresponding pair with zero second component. -/
private theorem biprodIsoProd_hom_inl_apply (M N : ModuleCat R) (x : M) :
    ((ModuleCat.biprodIsoProd M N).hom.hom) ((biprod.inl : M ⟶ biprod M N).hom x) = (x, 0) := by
  -- Evaluate the morphism-level identification of `biprod.inl` with the usual product inclusion.
  simpa using congrArg (fun g : M ⟶ ModuleCat.of R (M × N) => g.hom x) (biprodIsoProd_inl_hom
    (R := R) M N)

/-- Helper for Lemma 10.102.2: the explicit product comparison sends an element of the right
biproduct summand to the corresponding pair with zero first component. -/
private theorem biprodIsoProd_hom_inr_apply (M N : ModuleCat R) (y : N) :
    ((ModuleCat.biprodIsoProd M N).hom.hom) ((biprod.inr : N ⟶ biprod M N).hom y) = (0, y) := by
  -- This is the pointwise form of the right-summand/product-inclusion compatibility.
  simpa using congrArg (fun g : N ⟶ ModuleCat.of R (M × N) => g.hom y) (biprodIsoProd_inr_hom
    (R := R) M N)

/-- Helper for Lemma 10.102.2: the inverse of the head-tail biproduct splitting sends an element
of the left summand to the explicit tail-plus-zero vector. -/
private theorem splitOffUnitModuleIso_inv_inl_apply
    (ns : ℕ) (x : Fin ns → R) :
    ((splitOffUnitModuleIso (R := R) ns).inv.hom)
        ((biprod.inl :
          ModuleCat.of R (Fin ns → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom x) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (x, 0) := by
  -- Unfold the composite isomorphism once so the explicit product comparison can be evaluated.
  change
    ((splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap)
      (((ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin ns → R))
          (ModuleCat.of R (Fin 1 → R))).hom.hom)
        ((biprod.inl :
          ModuleCat.of R (Fin ns → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom x)) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (x, 0)
  -- The left summand becomes the pair `(x, 0)` in the explicit product model.
  rw [biprodIsoProd_hom_inl_apply]
  rfl

/-- Helper for Lemma 10.102.2: the inverse of the head-tail biproduct splitting sends an element
of the right summand to the explicit zero-plus-head vector. -/
private theorem splitOffUnitModuleIso_inv_inr_apply
    (ns : ℕ) (y : Fin 1 → R) :
    ((splitOffUnitModuleIso (R := R) ns).inv.hom)
        ((biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (0, y) := by
  -- Unfold the same composite isomorphism and evaluate the right summand in the product model.
  change
    ((splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap)
      (((ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin ns → R))
          (ModuleCat.of R (Fin 1 → R))).hom.hom)
        ((biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y)) =
      (splitOffUnitLinearEquiv (R := R) ns).symm (0, y)
  -- The right summand becomes the pair `(0, y)`.
  rw [biprodIsoProd_hom_inr_apply]
  rfl

/-- Helper for Lemma 10.102.2: the inverse explicit product comparison identifies the first
projection from the biproduct with the ordinary product projection. -/
private theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.fst =
      ModuleCat.ofHom (LinearMap.fst R M N) := by
  -- Compose the known formula for the forward comparison with the inverse isomorphism on the left.
  simpa [Category.assoc] using
    congrArg (fun k ↦ (ModuleCat.biprodIsoProd M N).inv ≫ k)
      (biprodIsoProd_hom_comp_fst (R := R) M N)

/-- Helper for Lemma 10.102.2: the inverse explicit product comparison identifies the second
projection from the biproduct with the ordinary product projection. -/
private theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.snd =
      ModuleCat.ofHom (LinearMap.snd R M N) := by
  -- This is the same calculation for the second product projection.
  simpa [Category.assoc] using
    congrArg (fun k ↦ (ModuleCat.biprodIsoProd M N).inv ≫ k)
      (biprodIsoProd_hom_comp_snd (R := R) M N)

/-- Helper for Lemma 10.102.2: composing the head-tail biproduct splitting with the tail
projection just reads off the tail coordinates of the linear equivalence. -/
private theorem splitOffUnitModuleIso_hom_comp_fst (n : ℕ) :
    (splitOffUnitModuleIso (R := R) n).hom ≫ biprod.fst =
      ModuleCat.ofHom
        ((LinearMap.fst R (Fin n → R) (Fin 1 → R)).comp
          (splitOffUnitLinearEquiv (R := R) n).toLinearMap) := by
  -- Unfold the composite isomorphism and rewrite the biproduct projection via the explicit
  -- product model.
  change
    ((splitOffUnitLinearEquiv (R := R) n).toModuleIso.hom ≫
        (ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin n → R))
          (ModuleCat.of R (Fin 1 → R))).inv) ≫ biprod.fst =
      _
  rw [Category.assoc, biprodIsoProd_inv_comp_fst (R := R)]
  rfl

/-- Helper for Lemma 10.102.2: composing the head-tail biproduct splitting with the head
projection just reads off the distinguished head coordinate of the linear equivalence. -/
private theorem splitOffUnitModuleIso_hom_comp_snd (n : ℕ) :
    (splitOffUnitModuleIso (R := R) n).hom ≫ biprod.snd =
      ModuleCat.ofHom
        ((LinearMap.snd R (Fin n → R) (Fin 1 → R)).comp
          (splitOffUnitLinearEquiv (R := R) n).toLinearMap) := by
  -- The second projection is handled by the same explicit-product comparison.
  change
    ((splitOffUnitLinearEquiv (R := R) n).toModuleIso.hom ≫
        (ModuleCat.biprodIsoProd
          (ModuleCat.of R (Fin n → R))
          (ModuleCat.of R (Fin 1 → R))).inv) ≫ biprod.snd =
      _
  rw [Category.assoc, biprodIsoProd_inv_comp_snd (R := R)]
  rfl

/-- Helper for Lemma 10.102.2: after splitting off the distinguished head coordinates on source
and target, the normalized middle differential is already block diagonal with identity on the
rank-one head summand. -/
private theorem normalized_middle_diff_is_biprod_map_tail_identity
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hhead : f (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (htail : ∀ j : Fin ns, (f (Pi.single j.succ (1 : R))) 0 = 0) :
    let F :
      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) ⟶
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)) :=
      (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
        (splitOffUnitModuleIso (R := R) nt).hom
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 _) := by
  let F :
      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) ⟶
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)) :=
    (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
      (splitOffUnitModuleIso (R := R) nt).hom
  -- Compare the normalized map on the left and right summands separately.
  have h_inl_snd : biprod.inl ≫ F ≫ biprod.snd = 0 := by
    -- On the left summand, the source-side adapter reduces to a tail-plus-zero vector, so the
    -- head output vanishes by the normalized basis formula with `y = 0`.
    have hsnd :
        biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd =
          biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            ModuleCat.ofHom
              ((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
                (splitOffUnitLinearEquiv (R := R) nt).toLinearMap) := by
      -- Rewrite the target head projection through the explicit product model of the biproduct.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫ k)
          (splitOffUnitModuleIso_hom_comp_snd (R := R) nt)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    ext j
    fin_cases j
    change
      ((biprod.inl ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd).hom x) 0 = 0
    rw [hsnd]
    change
      (((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
            (splitOffUnitLinearEquiv (R := R) nt).toLinearMap)
          (f (((splitOffUnitModuleIso (R := R) ns).inv.hom)
            (((biprod.inl :
              ModuleCat.of R (Fin ns → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom x)))) ) 0 = 0
    rw [splitOffUnitModuleIso_inv_inl_apply (R := R) (ns := ns) (x := x)]
    simpa [LinearMap.comp_apply] using
      congrArg (fun g : Fin 1 → R => g 0)
        (split_off_unit_linear_equiv_apply_head_of_normalized_map
          (R := R) f hhead htail x 0)
  have h_inr_fst : biprod.inr ≫ F ≫ biprod.fst = 0 := by
    -- On the right summand, the source-side adapter is the pure head vector; after applying `f`
    -- and the head normalization, the codomain tail factor is therefore zero.
    have hfst :
        biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.fst =
          biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            ModuleCat.ofHom
              ((LinearMap.fst R (Fin nt → R) (Fin 1 → R)).comp
                (splitOffUnitLinearEquiv (R := R) nt).toLinearMap) := by
      -- Rewrite the target tail projection through the same explicit product comparison.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫ k)
          (splitOffUnitModuleIso_hom_comp_fst (R := R) nt)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    ext k
    change
      ((biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.fst).hom y) k = 0
    rw [hfst]
    change
      (((LinearMap.fst R (Fin nt → R) (Fin 1 → R)).comp
            (splitOffUnitLinearEquiv (R := R) nt).toLinearMap)
          (f (((splitOffUnitModuleIso (R := R) ns).inv.hom)
            (((biprod.inr :
              ModuleCat.of R (Fin 1 → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y)))) ) k = 0
    rw [splitOffUnitModuleIso_inv_inr_apply (R := R) (ns := ns) (y := y)]
    have hsource :
        (splitOffUnitLinearEquiv (R := R) ns).symm (0, y) = Pi.single 0 (y 0) := by
      -- With zero tail coordinates, the inverse splitting is the pure head basis vector.
      rw [split_off_unit_linear_equiv_symm_eq_head_tail_sum (R := R) ns 0 y]
      simp
    have hsource_smul :
        (Pi.single 0 (y 0) : Fin (ns + 1) → R) = (y 0) • (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
      ext j
      by_cases hj : j = 0
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    rw [hsource, hsource_smul, map_smul, hhead]
    simp [splitOffUnitLinearEquiv_apply_tail]
  have h_inr_snd : biprod.inr ≫ F ≫ biprod.snd = 𝟙 _ := by
    -- The same pure-head input keeps the rank-one summand unchanged under the normalized map.
    have hsnd :
        biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd =
          biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            ModuleCat.ofHom
              ((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
                (splitOffUnitLinearEquiv (R := R) nt).toLinearMap) := by
      -- Again rewrite the target head projection through the explicit product comparison.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫ k)
          (splitOffUnitModuleIso_hom_comp_snd (R := R) nt)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    ext j
    fin_cases j
    change
      ((biprod.inr ≫ (splitOffUnitModuleIso (R := R) ns).inv ≫ ModuleCat.ofHom f ≫
            (splitOffUnitModuleIso (R := R) nt).hom ≫ biprod.snd).hom y) 0 = y 0
    rw [hsnd]
    change
      (((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
            (splitOffUnitLinearEquiv (R := R) nt).toLinearMap)
          (f (((splitOffUnitModuleIso (R := R) ns).inv.hom)
            (((biprod.inr :
              ModuleCat.of R (Fin 1 → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))).hom y)))) ) 0 = y 0
    rw [splitOffUnitModuleIso_inv_inr_apply (R := R) (ns := ns) (y := y)]
    simpa [LinearMap.comp_apply] using
      congrArg (fun g : Fin 1 → R => g 0)
        (split_off_unit_linear_equiv_apply_head_of_normalized_map
          (R := R) f hhead htail 0 y)
  -- Those three component computations are exactly the hypotheses of the abstract biproduct
  -- packaging lemma.
  exact eq_biprod_map_tail_identity_of_components (R := R) F h_inl_snd h_inr_fst h_inr_snd

/-- Helper for Lemma 10.102.2: once the middle differential is block diagonal in the head-tail
coordinates, the upper adjacent differential lands in the source tail summand. -/
private theorem upper_adjacent_diff_factors_through_tail_of_split_middle
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
    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom =
      (D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom ≫
          biprod.fst) ≫
        biprod.inl := by
  let upper :=
    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom
  have hdiff :
      (D.termIso i.succ).hom ≫ ModuleCat.ofHom (D.diffAt i) =
        D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom := by
    -- Expand `diffAt` once and cancel the adjacent coordinate isomorphisms.
    change
      (D.termIso i.succ).hom ≫
          (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
            (D.termIso i.castSucc).hom =
        D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom
    simp [Category.assoc]
  have hmid_snd :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd = biprod.snd := by
    -- The block-diagonal middle differential acts as the identity on the split head summand.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ biprod.snd) hmid
  have hupper_snd : upper ≫ biprod.snd = 0 := by
    have hdd :
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
            (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.snd =
          0 := by
      -- This is exactly `d ≫ d = 0`, postcomposed with the remaining coordinate maps.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (D.termIso i.castSucc).hom ≫ eTarget.hom ≫ biprod.snd)
          (D.toChainComplex.d_comp_d (i.1 + 2) (i.1 + 1) i.1)
    have hupper_comp :
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫
            ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd =
          0 := by
      -- Rewrite the middle differential through `diffAt` before applying the previous `d ≫ d`.
      have hrewrite :
          D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫
              ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd =
            D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
              D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom ≫
                eTarget.hom ≫ biprod.snd := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ k ≫ eTarget.hom ≫ biprod.snd)
          hdiff
      exact hrewrite.trans hdd
    -- Reinsert the block-diagonal middle differential and then invoke `d ≫ d = 0`.
    calc
      upper ≫ biprod.snd =
          upper ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd) := by
            rw [hmid_snd]
      _ = D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫
            ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.snd := by
            simp [upper, Category.assoc]
      _ = 0 := hupper_comp
  -- Once the second component vanishes, the incoming map factors through the tail summand.
  apply biprod.hom_ext
  · simp [upper, Category.assoc]
  · simpa [upper, Category.assoc] using hupper_snd

/-- Helper for Lemma 10.102.2: once the middle differential is block diagonal in the head-tail
coordinates, the lower adjacent differential annihilates the target head summand. -/
private theorem lower_adjacent_diff_factors_through_tail_of_split_middle
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
    eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
      biprod.fst ≫
        (biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 (i.1 - 1)) := by
  let lower :=
    eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1)
  have hdiff :
      ModuleCat.ofHom (D.diffAt i) ≫ (D.termIso i.castSucc).inv =
        (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 := by
    -- Expand `diffAt` once and cancel the target-side coordinate isomorphism.
    change
      (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
          (D.termIso i.castSucc).hom ≫ (D.termIso i.castSucc).inv =
        (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1
    simp [Category.assoc]
  have hmid_inr :
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          eTarget.inv =
        biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) := by
    -- The split head basis vector on the target side comes from the split head basis vector on
    -- the source side because the head block of the middle differential is the identity.
    have hmid_inr_aux :
        biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) =
          (biprod.inr :
            ModuleCat.of R (Fin 1 → R) ⟶
              biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
            eTarget.inv := by
      calc
      biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) =
          biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫
            eTarget.inv := by
            simp [Category.assoc]
      _ = biprod.inr ≫ biprod.map tailDiff (𝟙 _) ≫ eTarget.inv := by
            simpa [Category.assoc] using congrArg
              (fun k :
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) ⟶
                  biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)) =>
                  (biprod.inr :
                    ModuleCat.of R (Fin 1 → R) ⟶
                      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))) ≫
                    k ≫ eTarget.inv)
              hmid
      _ = (biprod.inr :
            ModuleCat.of R (Fin 1 → R) ⟶
              biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
            eTarget.inv := by
            simp [Category.assoc]
    exact hmid_inr_aux.symm
  have hlower_inr :
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          lower = 0 := by
    have hdd :
        biprod.inr ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫
            D.toChainComplex.d (i.1 + 1) i.1 ≫ D.toChainComplex.d i.1 (i.1 - 1) =
          0 := by
      -- This is the same `d ≫ d = 0`, now precomposed with the split source-head injection.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (biprod.inr :
              ModuleCat.of R (Fin 1 → R) ⟶
                biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R))) ≫
              eSource.inv ≫ (D.termIso i.succ).inv ≫ k)
          (D.toChainComplex.d_comp_d (i.1 + 1) i.1 (i.1 - 1))
    have hlower_comp :
        biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
            (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
          0 := by
      -- Rewrite the middle differential through `diffAt` before invoking the precomposed
      -- `d ≫ d = 0` identity.
      have hrewrite :
          biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
              (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
            biprod.inr ≫ eSource.inv ≫ (D.termIso i.succ).inv ≫
              D.toChainComplex.d (i.1 + 1) i.1 ≫ D.toChainComplex.d i.1 (i.1 - 1) := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ biprod.inr ≫ eSource.inv ≫ k ≫ D.toChainComplex.d i.1 (i.1 - 1))
          hdiff
      exact hrewrite.trans hdd
    -- After rewriting the target head injection through the middle differential, `d ≫ d = 0`
    -- kills the resulting composite.
    calc
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          lower =
          biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫
            (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) := by
            change
              ((biprod.inr :
                  ModuleCat.of R (Fin 1 → R) ⟶
                    biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
                  eTarget.inv) ≫ (D.termIso i.castSucc).inv ≫
                D.toChainComplex.d i.1 (i.1 - 1) =
              (biprod.inr ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i)) ≫
                (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1)
            rw [hmid_inr]
      _ = 0 := hlower_comp
  -- Vanishing on the source-side head summand is equivalent to factoring through `biprod.fst`.
  apply biprod.hom_ext'
  · simp [lower, Category.assoc]
  · simpa [lower, Category.assoc] using hlower_inr

/-- Helper for Lemma 10.102.2: once the middle differential is block diagonal in the head-tail
coordinates, the upper adjacent differential lands in the source tail summand and the lower
adjacent differential annihilates the target head summand. -/
private theorem adjacent_maps_respect_tail_split_of_normalized_middle
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
    D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫ (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.snd =
        0 ∧
      (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫
          eTarget.inv ≫ (D.termIso i.castSucc).inv ≫ D.toChainComplex.d i.1 (i.1 - 1) =
        0 := by
  constructor
  · -- The upper factorization lemma packages the first vanishing component directly.
    have hupper :=
      upper_adjacent_diff_factors_through_tail_of_split_middle
        (R := R) (D := D) (i := i) (eSource := eSource) (eTarget := eTarget)
        (tailDiff := tailDiff) hmid
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ biprod.snd) hupper
  · -- The lower factorization lemma packages the second vanishing component directly.
    have hlower :=
      lower_adjacent_diff_factors_through_tail_of_split_middle
        (R := R) (D := D) (i := i) (eSource := eSource) (eTarget := eTarget)
        (tailDiff := tailDiff) hmid
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (biprod.inr :
          ModuleCat.of R (Fin 1 → R) ⟶
            biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R))) ≫ k)
      hlower

/-- Helper for Lemma 10.102.2: the unique-coordinate factor `Fin 1 → R` can be rescaled by a
unit through the canonical `funUnique` identification with `R`. -/
private noncomputable def headScaling (u : Units R) : (Fin 1 → R) ≃ₗ[R] (Fin 1 → R) :=
  LinearEquiv.funUnique (Fin 1) R R ≪≫ₗ
    (u⁻¹).mulRightLinearEquiv R ≪≫ₗ
    (LinearEquiv.funUnique (Fin 1) R R).symm

/-- Helper for Lemma 10.102.2: the head-scaling automorphism multiplies the unique coordinate by
the inverse unit. -/
private theorem headScaling_apply (u : Units R) (y : Fin 1 → R) :
    headScaling (R := R) u y = fun _ ↦ y 0 * (↑u⁻¹ : R) := by
  ext j
  fin_cases j
  simp [headScaling]

/-- Helper for Lemma 10.102.2: in head-tail product coordinates, subtracting the head coordinate
times a fixed tail vector is an explicit linear automorphism. -/
private noncomputable def targetTailShear {nt : ℕ} (tailPivot : Fin nt → R) :
    ((Fin nt → R) × (Fin 1 → R)) ≃ₗ[R] ((Fin nt → R) × (Fin 1 → R)) :=
  LinearEquiv.prodComm R (Fin nt → R) (Fin 1 → R) ≪≫ₗ
    (LinearEquiv.refl R (Fin 1 → R)).skewProd (LinearEquiv.refl R (Fin nt → R))
      (-((LinearMap.proj 0).smulRight tailPivot)) ≪≫ₗ
    LinearEquiv.prodComm R (Fin 1 → R) (Fin nt → R)

/-- Helper for Lemma 10.102.2: the target-side shear fixes the head factor and subtracts the head
coefficient times the chosen pivot tail vector from the tail factor. -/
private theorem targetTailShear_apply {nt : ℕ} (tailPivot : Fin nt → R)
    (x : Fin nt → R) (y : Fin 1 → R) :
    targetTailShear (R := R) tailPivot (x, y) = (x - y 0 • tailPivot, y) := by
  -- Rewrite the block-lower-diagonal map after commuting the product factors twice.
  simp [targetTailShear, sub_eq_add_neg, LinearMap.smulRight_apply, smul_eq_mul]

/-- Helper for Lemma 10.102.2: moving the chosen target coordinate to the head factor, rescaling
it to `1`, and then killing the remaining tail part gives the target-side basis change from the
source proof. -/
private noncomputable def target_head_normalization
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (a : Fin (ns + 1)) (b : Fin (nt + 1))
    (hu : IsUnit ((f (Pi.single a (1 : R))) b)) :
    (Fin (nt + 1) → R) ≃ₗ[R] (Fin (nt + 1) → R) :=
  let targetSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (nt + 1) ↦ R) (Equiv.swap 0 b)
  let tailPivot :=
    (splitOffUnitLinearEquiv (R := R) nt (targetSwap (f (Pi.single a (1 : R))))).1
  targetSwap ≪≫ₗ
    splitOffUnitLinearEquiv (R := R) nt ≪≫ₗ
    (LinearEquiv.refl R (Fin nt → R)).prodCongr (headScaling (R := R) hu.unit) ≪≫ₗ
    targetTailShear (R := R) tailPivot ≪≫ₗ
    (splitOffUnitLinearEquiv (R := R) nt).symm

/-- Helper for Lemma 10.102.2: swapping the chosen source coordinate into position `0` sends the
distinguished head basis vector to the original basis vector indexed by `a`. -/
private theorem source_swap_symm_apply_pure_head
    {n : ℕ} (a : Fin (n + 1)) :
    (LinearEquiv.piCongrLeft R (fun _ : Fin (n + 1) ↦ R) (Equiv.swap 0 a)).symm
        (Pi.single 0 (1 : R)) =
      (Pi.single a (1 : R) : Fin (n + 1) → R) := by
  -- Route correction: prove the swap-on-basis computation directly coordinatewise, instead of
  -- letting later transport goals absorb this elementary basis calculation.
  -- The inverse source swap evaluates at `Equiv.swap 0 a`, so only the cases `j = a`, `j = 0`,
  -- and `j ≠ 0,a` need to be checked.
  ext j
  change
    ((Pi.single 0 (1 : R) : Fin (n + 1) → R) ((Equiv.swap 0 a) j)) =
      ((Pi.single a (1 : R) : Fin (n + 1) → R) j)
  by_cases hja : j = a
  · subst j
    by_cases ha0 : a = 0
    · subst ha0
      change ((Pi.single 0 (1 : R) : Fin (n + 1) → R) 0) = 1
      simp
    · rw [Equiv.swap_apply_right]
      simp
  · by_cases hj0 : j = 0
    · subst j
      have ha0 : a ≠ 0 := by
        intro ha0
        exact hja ha0.symm
      rw [Equiv.swap_apply_left]
      have h0a : (0 : Fin (n + 1)) ≠ a := by
        simpa using ha0.symm
      rw [Pi.single_eq_of_ne ha0, Pi.single_eq_of_ne h0a]
    · rw [Equiv.swap_apply_of_ne_of_ne hj0 hja]
      simp [Pi.single_eq_of_ne hj0, Pi.single_eq_of_ne hja]

/-- Helper for Lemma 10.102.2: the explicit target normalization sends the chosen pivot basis
vector to the distinguished head basis vector. -/
private theorem target_head_normalization_map_pivot
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (a : Fin (ns + 1)) (b : Fin (nt + 1))
    (hu : IsUnit ((f (Pi.single a (1 : R))) b)) :
    target_head_normalization (R := R) f a b hu (f (Pi.single a (1 : R))) =
      (Pi.single 0 (1 : R) : Fin (nt + 1) → R) := by
  let targetSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (nt + 1) ↦ R) (Equiv.swap 0 b)
  let pivot := targetSwap (f (Pi.single a (1 : R)))
  let tailPivot := (splitOffUnitLinearEquiv (R := R) nt pivot).1
  -- Rewrite the normalization in the split head-tail coordinates and evaluate it on the pivot.
  change
    (splitOffUnitLinearEquiv (R := R) nt).symm
        (targetTailShear (R := R) tailPivot
          (((LinearEquiv.refl R (Fin nt → R)).prodCongr
            (headScaling (R := R) hu.unit))
            (splitOffUnitLinearEquiv (R := R) nt pivot))) =
      (Pi.single 0 (1 : R) : Fin (nt + 1) → R)
  have hscaled :
      headScaling (R := R) hu.unit ((splitOffUnitLinearEquiv (R := R) nt pivot).2) =
        (fun _ ↦ (1 : R)) := by
    ext j
    fin_cases j
    rw [headScaling_apply, splitOffUnitLinearEquiv_apply_head]
    change pivot 0 * (↑hu.unit⁻¹ : R) = 1
    dsimp [pivot, targetSwap]
    rw [piCongrLeft_swap_apply_zero]
    simpa [hu.unit_spec]
  rw [targetTailShear_apply]
  simp [LinearEquiv.prodCongr_apply, hscaled, tailPivot]
  simpa using splitOffUnitLinearEquiv_symm_apply_pure_head (R := R) nt

/-- Helper for Lemma 10.102.2: after swapping the source pivot into position `0`, the explicit
target normalization sends the head basis vector to the head basis vector. -/
private theorem target_head_normalization_map_head
    {ns nt : ℕ}
    (f : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (a : Fin (ns + 1)) (b : Fin (nt + 1))
    (hu : IsUnit ((f (Pi.single a (1 : R))) b)) :
    let sourceSwap :=
      LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a)
    let g :=
      (target_head_normalization (R := R) f a b hu).toLinearMap.comp
        (f.comp sourceSwap.symm.toLinearMap)
    g (Pi.single 0 (1 : R)) = Pi.single 0 1 := by
  let sourceSwap :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (ns + 1) ↦ R) (Equiv.swap 0 a)
  let g :=
    (target_head_normalization (R := R) f a b hu).toLinearMap.comp
      (f.comp sourceSwap.symm.toLinearMap)
  -- The source swap moves `e₀` to the chosen pivot coordinate `a`, where the previous lemma
  -- applies directly.
  have hswap :
      sourceSwap.symm (Pi.single 0 (1 : R)) = (Pi.single a (1 : R) : Fin (ns + 1) → R) := by
    simpa [sourceSwap] using source_swap_symm_apply_pure_head (R := R) a
  change
    target_head_normalization (R := R) f a b hu (f (sourceSwap.symm (Pi.single 0 (1 : R)))) =
      (Pi.single 0 (1 : R) : Fin (nt + 1) → R)
  rw [hswap]
  exact target_head_normalization_map_pivot (R := R) f a b hu

/-- Helper for Lemma 10.102.2: the inverse head-tail splitting sends a pure tail basis vector in
the product model to the corresponding basis vector `Pi.single j.succ 1`. -/
private theorem splitOffUnitLinearEquiv_symm_apply_pure_tail
    (n : ℕ) (j : Fin n) :
    (splitOffUnitLinearEquiv (R := R) n).symm (Pi.single j (1 : R), 0) =
      (Pi.single j.succ (1 : R) : Fin (n + 1) → R) := by
  -- The split head-tail coordinates determine the vector uniquely on coordinate `0` and on each
  -- successor coordinate.
  ext k
  obtain ⟨hhead, htail⟩ :=
    splitOffUnitLinearEquiv_symm_apply_head_tail (R := R) n (Pi.single j 1) 0
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨l, rfl⟩
  · simpa using hhead
  · by_cases hlj : l = j
    · subst l
      simpa using htail j
    · rw [htail l]
      simp [Pi.single_eq_of_ne, hlj]

/-- Helper for Lemma 10.102.2: for a source tail vector `x`, this records the head component of
`g` applied to the vector with tail part `x` and zero head part. -/
private noncomputable def source_head_coefficient
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R)) :
    (Fin ns → R) →ₗ[R] (Fin 1 → R) :=
  let sourceInl :
      (Fin ns → R) →ₗ[R] (Fin (ns + 1) → R) :=
    (splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap.comp
      (LinearMap.inl R (Fin ns → R) (Fin 1 → R))
  let targetHead :
      (Fin (nt + 1) → R) →ₗ[R] (Fin 1 → R) :=
    (LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
      (splitOffUnitLinearEquiv (R := R) nt).toLinearMap
  targetHead.comp (g.comp sourceInl)

/-- Helper for Lemma 10.102.2: the source-side column operation subtracts exactly the head
coefficient created by `g` on a tail input, while fixing the distinguished head summand. -/
private noncomputable def source_head_correction
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (_hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1) :
    (Fin (ns + 1) → R) ≃ₗ[R] (Fin (ns + 1) → R) :=
  splitOffUnitLinearEquiv (R := R) ns ≪≫ₗ
    (LinearEquiv.refl R (Fin ns → R)).skewProd
      (LinearEquiv.refl R (Fin 1 → R))
      (source_head_coefficient (R := R) g) ≪≫ₗ
    (splitOffUnitLinearEquiv (R := R) ns).symm

/-- Helper for Lemma 10.102.2: in head-tail product coordinates, the inverse source correction
keeps the tail part fixed and subtracts the recorded head coefficient from the head part. -/
private theorem source_head_correction_symm_apply_head_tail
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (splitOffUnitLinearEquiv (R := R) ns)
        ((source_head_correction (R := R) g hg).symm
          ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))) =
      (x, y - source_head_coefficient (R := R) g x) := by
  -- Unfold the conjugated skew-product once and read off its inverse formula in split
  -- coordinates.
  simp [source_head_correction, source_head_coefficient]

/-- Helper for Lemma 10.102.2: the inverse source correction fixes the distinguished head basis
vector. -/
private theorem source_head_correction_symm_apply_pure_head
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1) :
    (source_head_correction (R := R) g hg).symm (Pi.single 0 (1 : R)) =
      (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
  rw [← splitOffUnitLinearEquiv_symm_apply_pure_head (R := R) ns]
  have hcoeff_zero : source_head_coefficient (R := R) g 0 = 0 := by
    simpa using (source_head_coefficient (R := R) g).map_zero
  -- In split coordinates, the inverse correction sends `(0, 1)` to `(0, 1 - 0)`.
  apply (splitOffUnitLinearEquiv (R := R) ns).injective
  simpa [hcoeff_zero] using
    source_head_correction_symm_apply_head_tail
      (R := R) (g := g) (hg := hg) (x := 0) (y := fun _ ↦ (1 : R))

/-- Helper for Lemma 10.102.2: after the source-side correction, the codomain head coordinate is
exactly the chosen source head coordinate in split head-tail coordinates. -/
private theorem source_head_correction_preserves_split_head
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1)
    (x : Fin ns → R) (y : Fin 1 → R) :
    (splitOffUnitLinearEquiv (R := R) nt
      (g ((source_head_correction (R := R) g hg).symm
        ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))))).2 = y := by
  let pairHead :
      ((Fin ns → R) × (Fin 1 → R)) →ₗ[R] (Fin 1 → R) :=
    ((LinearMap.snd R (Fin nt → R) (Fin 1 → R)).comp
        (splitOffUnitLinearEquiv (R := R) nt).toLinearMap).comp
      (g.comp (splitOffUnitLinearEquiv (R := R) ns).symm.toLinearMap)
  have hcorrected :
      (source_head_correction (R := R) g hg).symm
          ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y)) =
        (splitOffUnitLinearEquiv (R := R) ns).symm
          (x, y - source_head_coefficient (R := R) g x) := by
    -- Rewrite the inverse correction in split coordinates and use injectivity of the splitter.
    apply (splitOffUnitLinearEquiv (R := R) ns).injective
    simpa using source_head_correction_symm_apply_head_tail
      (R := R) (g := g) (hg := hg) x y
  have hpair_inl :
      pairHead (x, 0) = source_head_coefficient (R := R) g x := by
    -- The `x`-only input is exactly the tail injection used in `source_head_coefficient`.
    ext j
    fin_cases j
    simp [pairHead, source_head_coefficient]
  have hpair_head (w : Fin 1 → R) :
      pairHead (0, w) = w := by
    -- The pure head input is a scalar multiple of the distinguished basis vector, which `g`
    -- sends to itself by `hg`.
    ext j
    fin_cases j
    have hpure :
        (splitOffUnitLinearEquiv (R := R) ns).symm (0, w) =
          (w 0) • (Pi.single 0 (1 : R) : Fin (ns + 1) → R) := by
      rw [split_off_unit_linear_equiv_symm_eq_head_tail_sum (R := R) ns 0 w]
      ext j
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · simp [Pi.single_eq_of_ne hj0]
    change
      ((splitOffUnitLinearEquiv (R := R) nt
          (g ((splitOffUnitLinearEquiv (R := R) ns).symm (0, w)))).2) 0 = w 0
    rw [hpure, map_smul, hg, splitOffUnitLinearEquiv_apply_head]
    simp
  have hpair_split :
      pairHead (x, y - source_head_coefficient (R := R) g x) =
        pairHead (x, 0) + pairHead (0, y - source_head_coefficient (R := R) g x) := by
    -- Split the corrected source coordinates into tail-only and head-only pieces.
    have hsum :
        (x, y - source_head_coefficient (R := R) g x) =
          (x, 0) + (0, y - source_head_coefficient (R := R) g x) := by
      apply Prod.ext
      · ext j
        simp
      · ext k
        fin_cases k
        simp
    rw [hsum, pairHead.map_add]
  -- After that split, the recorded head coefficient cancels with the correction term.
  calc
    (splitOffUnitLinearEquiv (R := R) nt
      (g ((source_head_correction (R := R) g hg).symm
        ((splitOffUnitLinearEquiv (R := R) ns).symm (x, y))))).2 =
        pairHead (x, y - source_head_coefficient (R := R) g x) := by
          rw [hcorrected]
          rfl
    _ = pairHead (x, 0) + pairHead (0, y - source_head_coefficient (R := R) g x) := hpair_split
    _ = source_head_coefficient (R := R) g x +
          (y - source_head_coefficient (R := R) g x) := by
          rw [hpair_inl, hpair_head]
    _ = y := by
          ext j
          fin_cases j
          simp

/-- Helper for Lemma 10.102.2: after precomposing with the source-side correction, the normalized
middle differential still fixes the head basis vector and has zero head coordinate on every tail
basis vector. -/
private theorem source_head_correction_zero_head_on_tail
    {ns nt : ℕ}
    (g : (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R))
    (hg : g (Pi.single 0 (1 : R)) = Pi.single 0 1) :
    let u := source_head_correction (R := R) g hg
    let g' := g.comp u.symm.toLinearMap
    g' (Pi.single 0 (1 : R)) = Pi.single 0 1 ∧
      ∀ j : Fin ns, (g' (Pi.single j.succ (1 : R))) 0 = 0 := by
  dsimp
  constructor
  · -- The source correction was designed to keep the distinguished head basis vector fixed.
    rw [source_head_correction_symm_apply_pure_head (R := R) (g := g) (hg := hg), hg]
  · intro j
    -- Rewrite the corrected tail basis vector through split coordinates and read its head output.
    have hsplit :
        (splitOffUnitLinearEquiv (R := R) nt
          (g ((source_head_correction (R := R) g hg).symm
            (Pi.single j.succ (1 : R))))).2 = 0 := by
      rw [← splitOffUnitLinearEquiv_symm_apply_pure_tail (R := R) ns j]
      simpa using source_head_correction_preserves_split_head
        (R := R) (g := g) (hg := hg) (x := Pi.single j (1 : R)) (y := 0)
    have hzero := congrArg (fun z : Fin 1 → R => z 0) hsplit
    rw [splitOffUnitLinearEquiv_apply_head] at hzero
    simpa using hzero

/-- Helper for Lemma 10.102.2: the reduced complex keeps the original terms away from the two
distinguished degrees and replaces degrees `i + 1` and `i` by the split tail modules. -/
private def reduced_complex_of_normalized_middle_object
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) (j : ℕ) : ModuleCat R :=
  if hSucc : j = i.1 + 1 then
    ModuleCat.of R (Fin ns → R)
  else if hCast : j = i.1 then
    ModuleCat.of R (Fin nt → R)
  else
    D.toChainComplex.X j

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the reduced object is the source tail module. -/
private theorem reduced_complex_of_normalized_middle_object_eq_succ
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) (i := i) (i.1 + 1) =
      ModuleCat.of R (Fin ns → R) := by
  -- The first branch of the definition is selected exactly in degree `i + 1`.
  simp [reduced_complex_of_normalized_middle_object]

/-- Helper for Lemma 10.102.2: at degree `i`, the reduced object is the target tail module. -/
private theorem reduced_complex_of_normalized_middle_object_eq_castSucc
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) (i := i) i.1 =
      ModuleCat.of R (Fin nt → R) := by
  -- The second branch of the definition is selected exactly in degree `i`.
  simp [reduced_complex_of_normalized_middle_object]

/-- Helper for Lemma 10.102.2: away from the two distinguished degrees, the reduced object agrees
with the original chain complex. -/
private theorem reduced_complex_of_normalized_middle_object_eq_of_ne_support
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j = D.toChainComplex.X j := by
  -- Outside the support, both conditional branches collapse to the inherited term.
  simp [reduced_complex_of_normalized_middle_object, hjSucc, hjCast]

/-- Helper for Lemma 10.102.2: in the upper adjacent branch, the target term is the split source
tail module. -/
private theorem reduced_complex_of_normalized_middle_object_eq_target_of_upper
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hUpper : j = i.1 + 1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      ModuleCat.of R (Fin ns → R) := by
  -- After substituting the branch index, this is the defining `i + 1` case.
  subst hUpper
  exact reduced_complex_of_normalized_middle_object_eq_succ (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: in the middle branch, the source term is the split source tail
module. -/
private theorem reduced_complex_of_normalized_middle_object_eq_source_of_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hMid : j = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      ModuleCat.of R (Fin ns → R) := by
  -- The source of the middle differential is the degree-`i + 1` tail term.
  subst hMid
  exact reduced_complex_of_normalized_middle_object_eq_succ (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: in the middle branch, the target term is the split target tail
module. -/
private theorem reduced_complex_of_normalized_middle_object_eq_target_of_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hMid : j = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      ModuleCat.of R (Fin nt → R) := by
  -- After substituting the branch index, this is the defining degree-`i` case.
  subst hMid
  exact reduced_complex_of_normalized_middle_object_eq_castSucc (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: in the lower adjacent branch, the source term is the split target
tail module. -/
private theorem reduced_complex_of_normalized_middle_object_eq_source_of_lower
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      ModuleCat.of R (Fin nt → R) := by
  -- The source of the lower adjacent differential is again the degree-`i` tail term.
  rw [hLower]
  exact reduced_complex_of_normalized_middle_object_eq_castSucc (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: the source term in the upper adjacent differential is inherited
unchanged from `D`. -/
private theorem reduced_complex_of_normalized_middle_object_eq_source_of_upper
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hUpper : j = i.1 + 1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      D.toChainComplex.X (j + 1) := by
  -- Once `j = i + 1`, the source degree `j + 1 = i + 2` is outside the two-point support.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support (R := R) (ns := ns) (nt := nt)
  · omega
  · omega

/-- Helper for Lemma 10.102.2: the target term in the lower adjacent differential is inherited
unchanged from `D`. -/
private theorem reduced_complex_of_normalized_middle_object_eq_target_of_lower
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      D.toChainComplex.X j := by
  -- The lower target degree satisfies `j = i - 1`, hence lies outside the supported degrees.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support (R := R) (ns := ns) (nt := nt)
  · omega
  · omega

/-- Helper for Lemma 10.102.2: in the generic branch, the source term remains the original source
term of `D`. -/
private theorem reduced_complex_of_normalized_middle_object_eq_source_of_generic
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hMid : j ≠ i.1) (hLower : j + 1 ≠ i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      D.toChainComplex.X (j + 1) := by
  -- If `j + 1 = i + 1`, then `j = i`, contradicting `hMid`; the other support point is excluded
  -- directly by `hLower`.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support (R := R) (ns := ns) (nt := nt)
  · intro h
    exact hMid (by simpa using Nat.succ.inj h)
  · exact hLower

/-- Helper for Lemma 10.102.2: in the generic branch, the target term remains the original target
term of `D`. -/
private theorem reduced_complex_of_normalized_middle_object_eq_target_of_generic
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hUpper : j ≠ i.1 + 1) (hMid : j ≠ i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      D.toChainComplex.X j := by
  -- The generic target index is outside both distinguished degrees by assumption.
  exact reduced_complex_of_normalized_middle_object_eq_of_ne_support
    (R := R) (ns := ns) (nt := nt) D i hUpper hMid

/-- Helper for Lemma 10.102.2: rewriting `diffAt` back into chain-complex coordinates on the
source side exposes the original middle differential. -/
private theorem termIso_hom_comp_diffAt
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    (D.termIso i.succ).hom ≫ ModuleCat.ofHom (D.diffAt i) =
      D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom := by
  -- Expanding `diffAt` cancels the source coordinate isomorphism.
  change
    (D.termIso i.succ).hom ≫
        (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
          (D.termIso i.castSucc).hom =
      D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom
  simp [Category.assoc]

/-- Helper for Lemma 10.102.2: rewriting `diffAt` back into chain-complex coordinates on the
target side exposes the original middle differential. -/
private theorem diffAt_comp_termIso_inv
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    ModuleCat.ofHom (D.diffAt i) ≫ (D.termIso i.castSucc).inv =
      (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 := by
  -- Expanding `diffAt` cancels the target coordinate isomorphism.
  change
    (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
        (D.termIso i.castSucc).hom ≫ (D.termIso i.castSucc).inv =
      (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1
  simp [Category.assoc]

/-- Helper for Lemma 10.102.2: the reduced differential keeps the original adjacent maps away
from the split head summands and replaces the middle map by its tail component. -/
private noncomputable def reduced_complex_of_normalized_middle_d
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
    (j : ℕ) :
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i (j + 1) ⟶
      reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i j :=
  if hUpper : j = i.1 + 1 then
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_upper
          (R := R) (ns := ns) (nt := nt) D i hUpper) ≫
      D.toChainComplex.d (j + 1) (i.1 + 1) ≫
      (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_upper
          (R := R) (ns := ns) (nt := nt) D i hUpper).symm
  else if hMid : j = i.1 then
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_middle
          (R := R) (ns := ns) (nt := nt) D i hMid) ≫
      tailDiff ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_middle
          (R := R) (ns := ns) (nt := nt) D i hMid).symm
  else if hLower : j + 1 = i.1 then
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower) ≫
      biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
        D.toChainComplex.d i.1 j ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower).symm
  else
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_generic
          (R := R) (ns := ns) (nt := nt) D i hMid hLower) ≫
      D.toChainComplex.d (j + 1) j ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_generic
          (R := R) (ns := ns) (nt := nt) D i hUpper hMid).symm

/-- Helper for Lemma 10.102.2: projecting the normalized middle differential to the target tail
summand records exactly `tailDiff`. -/
private theorem normalized_middle_tail_projection
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
    ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.fst =
      eSource.hom ≫ biprod.fst ≫ tailDiff := by
  -- Precompose the normalized middle block with `eSource.hom` and then project to the tail
  -- factor.
  calc
    ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.fst =
        eSource.hom ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom) ≫
          biprod.fst := by
            simp [Category.assoc]
    _ = eSource.hom ≫ biprod.map tailDiff (𝟙 _) ≫ biprod.fst := by
          rw [hmid]
    _ = eSource.hom ≫ biprod.fst ≫ tailDiff := by
          simp [Category.assoc]

/-- Helper for Lemma 10.102.2: including the source tail into the normalized middle block and
undoing the target splitting recovers the original middle differential on tail inputs. -/
private theorem normalized_middle_tail_inclusion
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
    tailDiff ≫ biprod.inl ≫ eTarget.inv =
      biprod.inl ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) := by
  -- Precompose the normalized middle block with the tail inclusion and then cancel `eTarget`.
  calc
    tailDiff ≫ biprod.inl ≫ eTarget.inv =
        biprod.inl ≫ biprod.map tailDiff (𝟙 _) ≫ eTarget.inv := by
          simp [Category.assoc]
    _ = biprod.inl ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom) ≫
          eTarget.inv := by
            rw [← hmid]
    _ = biprod.inl ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) := by
          simp [Category.assoc]

/-- Helper for Lemma 10.102.2: in the upper adjacent degree, the reduced differential is the
original upper differential followed by the source-tail projection. -/
private theorem reduced_complex_of_normalized_middle_d_eq_upper
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
        (eSource := eSource) (eTarget := eTarget) tailDiff (i.1 + 1) =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
        (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm := by
  -- This is exactly the `j = i + 1` branch of the reduced differential definition.
  simp [reduced_complex_of_normalized_middle_d]

/-- Helper for Lemma 10.102.2: in the middle degree, the reduced differential is the normalized
tail map. -/
private theorem reduced_complex_of_normalized_middle_d_eq_middle
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
        (eSource := eSource) (eTarget := eTarget) tailDiff i.1 =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_middle
            (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) ≫
        tailDiff ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_middle
            (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
  -- This is exactly the `j = i` branch of the reduced differential definition.
  simp [reduced_complex_of_normalized_middle_d]

/-- Helper for Lemma 10.102.2: in the lower adjacent degree, the reduced differential is the
original lower differential preceded by the target-tail inclusion. -/
private theorem reduced_complex_of_normalized_middle_d_eq_lower
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
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLower) ≫
        biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 j ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
  -- This is exactly the `j + 1 = i` branch of the reduced differential definition.
  have hUpper : j ≠ i.1 + 1 := by
    omega
  have hMid : j ≠ i.1 := by
    omega
  simp [reduced_complex_of_normalized_middle_d, hUpper, hMid, hLower]

/-- Helper for Lemma 10.102.2: away from the three supported branches, the reduced differential is
the inherited differential of `D`. -/
private theorem reduced_complex_of_normalized_middle_d_eq_generic
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
    (hUpper : j ≠ i.1 + 1) (hMid : j ≠ i.1) (hLower : j + 1 ≠ i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_generic
            (R := R) (ns := ns) (nt := nt) D i hMid hLower) ≫
        D.toChainComplex.d (j + 1) j ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_generic
            (R := R) (ns := ns) (nt := nt) D i hUpper hMid).symm := by
  -- Once the supported branches are excluded, the definition reduces to the generic case.
  simp [reduced_complex_of_normalized_middle_d, hUpper, hMid, hLower]

/-- Helper for Lemma 10.102.2: the transport between the upper and middle supported branches is
trivial, so the two consecutive branch formulas compose without an extra cast. -/
private theorem reduced_complex_of_normalized_middle_upper_middle_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_upper
          (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_middle
          (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `ModuleCat.of R (Fin ns → R)`.
  simp

/-- Helper for Lemma 10.102.2: the transport between the middle and lower supported branches is
trivial, so the two consecutive branch formulas compose without an extra cast. -/
private theorem reduced_complex_of_normalized_middle_middle_lower_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 1 = i.1) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_middle
          (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm ≫
      eqToHom
        (by
          simpa [hLower] using
            reduced_complex_of_normalized_middle_object_eq_source_of_lower
              (R := R) (ns := ns) (nt := nt) D i hLower) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `ModuleCat.of R (Fin nt → R)`.
  simp

/-- Helper for Lemma 10.102.2: the transport between the generic branch above the support and the
upper supported branch is trivial, so the two consecutive branch formulas compose without an
extra cast. -/
private theorem reduced_complex_of_normalized_middle_generic_upper_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_generic
          (R := R) (ns := ns) (nt := nt) D i
          (j := i.1 + 2) (by omega) (by omega)).symm ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_upper
          (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `D.X (i + 2)`.
  simp

/-- Helper for Lemma 10.102.2: the transport between the lower supported branch and the generic
branch below the support is trivial, so the two consecutive branch formulas compose without an
extra cast. -/
private theorem reduced_complex_of_normalized_middle_lower_generic_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 2 = i.1) :
    eqToHom
        ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
          (R := R) (ns := ns) (nt := nt) D i (j := j + 1)
          (by simpa [Nat.add_assoc] using hLower)).symm) ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_generic
          (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `D.X (j + 1)`.
  simp

/-- Helper for Lemma 10.102.2: the reduced differential still squares to zero. -/
private theorem reduced_complex_of_normalized_middle_d_sq_upper_branch
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
private theorem reduced_complex_of_normalized_middle_d_sq_middle_branch
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
private theorem reduced_complex_of_normalized_middle_d_sq_lower_interface_branch
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
private theorem reduced_complex_of_normalized_middle_d_sq_lower_generic_branch
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
private theorem reduced_complex_of_normalized_middle_d_sq_generic_branch
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
private theorem reduced_complex_of_normalized_middle_d_sq
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

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the reduced object is already the module with
the split rank function. -/
private theorem reduced_complex_of_normalized_middle_object_eq_splitRank_succ
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
private theorem reduced_complex_of_normalized_middle_object_eq_splitRank_castSucc
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
private theorem reduced_complex_of_normalized_middle_object_eq_of_ne_adjacent
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
private theorem splitRank_module_eq_of_ne_adjacent
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
private theorem identityDiskComplex_X_eq_succ
    (i : Fin e) :
    (identityDiskComplex (R := R) i).X (i.1 + 1) =
      ModuleCat.of R (Fin 1 → R) := by
  -- The identity disk is supported with rank one in degree `i + 1`.
  rw [identityDiskComplex, ChainComplex.of_x, identityDiskRank_succ]

/-- Helper for Lemma 10.102.2: in degree `i`, the identity-disk term is again the standard free
rank-one module. -/
private theorem identityDiskComplex_X_eq_castSucc
    (i : Fin e) :
    (identityDiskComplex (R := R) i).X i.1 =
      ModuleCat.of R (Fin 1 → R) := by
  -- The other supported degree carries the same rank-one term.
  rw [identityDiskComplex, ChainComplex.of_x, identityDiskRank_castSucc]

/-- Helper for Lemma 10.102.2: the reduced finite free complex has the expected displayed ranks
and term identifications. -/
private noncomputable def reduced_complex_of_normalized_middle_termIso
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
private noncomputable def reduced_complex_of_normalized_middle
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
private theorem reduced_complex_of_normalized_middle_X_eq_succ
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
private theorem reduced_complex_of_normalized_middle_X_eq_castSucc
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
private theorem reduced_complex_of_normalized_middle_X_eq_of_ne_support
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

/-- Helper for Lemma 10.102.2: in `ModuleCat R`, a biproduct with zero right summand collapses
onto the left summand. -/
private noncomputable def biprodFstIsoOfIsZero (X Y : ModuleCat R) [HasBinaryBiproduct X Y]
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
private theorem biprodFstIsoOfIsZero_symm_hom_comp_fst
    (X Y : ModuleCat R) [HasBinaryBiproduct X Y] (hY : IsZero Y) :
    (biprodFstIsoOfIsZero (R := R) X Y hY).symm.hom ≫
        (biprod.fst : X ⊞ Y ⟶ X) =
      𝟙 X := by
  -- The inverse of the collapse is exactly `biprod.inl`.
  simp [biprodFstIsoOfIsZero]

/-- Helper for Lemma 10.102.2: the inverse of `biprodFstIsoOfIsZero` has zero composite with the
second projection, because the zero summand contributes nothing. -/
private theorem biprodFstIsoOfIsZero_symm_hom_comp_snd
    (X Y : ModuleCat R) [HasBinaryBiproduct X Y] (hY : IsZero Y) :
    (biprodFstIsoOfIsZero (R := R) X Y hY).symm.hom ≫
        (biprod.snd : X ⊞ Y ⟶ Y) =
      0 := by
  -- Again the inverse is `biprod.inl`, and `biprod.inl ≫ biprod.snd = 0`.
  simp [biprodFstIsoOfIsZero]

/-- Helper for Lemma 10.102.2: the inverse objectwise biproduct comparison identifies the first
projection on the chain-level biproduct with the explicit first projection. -/
private theorem biprodXIso_inv_fst
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
private theorem biprodXIso_inv_snd
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
private theorem biprodXIso_hom_comp_fst
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
private theorem biprodXIso_hom_comp_snd
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
private abbrev biprodChainFst (K L : ChainComplex (ModuleCat R) ℕ) : biprod K L ⟶ K :=
  biprod.fst

/-- Helper for Lemma 10.102.2: the second projection from a chain-level biproduct, named as a
chain map for use in later component formulas. -/
private abbrev biprodChainSnd (K L : ChainComplex (ModuleCat R) ℕ) : biprod K L ⟶ L :=
  biprod.snd

/-- Helper for Lemma 10.102.2: the normalized split produces the degreewise component isomorphism
from `D` to the biproduct of the reduced complex and the identity disk. -/
private noncomputable def normalized_middle_component_iso_off_support
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
private noncomputable def normalized_middle_component_iso_succ
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
private noncomputable def normalized_middle_component_iso_castSucc
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
private noncomputable def normalized_middle_component_iso
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
private theorem normalized_middle_component_iso_off_support_hom_comp_fst
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
private theorem normalized_middle_component_iso_off_support_hom_comp_snd
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
private theorem normalized_middle_component_iso_succ_hom_comp_fst
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
private theorem normalized_middle_component_iso_succ_hom_comp_snd
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
private theorem normalized_middle_component_iso_castSucc_hom_comp_fst
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
private theorem normalized_middle_component_iso_castSucc_hom_comp_snd
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
private theorem normalized_middle_head_projection
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

/-- Helper for Lemma 10.102.2: away from the two supported degrees, the top-level normalized
component isomorphism collapses to the off-support formula after postcomposing with the reduced
projection. -/
private theorem normalized_middle_component_iso_hom_comp_fst_of_ne_support
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
private theorem normalized_middle_component_iso_hom_comp_fst_succ
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
private theorem normalized_middle_component_iso_hom_comp_fst_castSucc
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
private theorem normalized_middle_component_iso_hom_comp_snd_of_ne_support
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
private theorem normalized_middle_component_iso_hom_comp_snd_succ
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
private theorem normalized_middle_component_iso_hom_comp_snd_castSucc
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
  -- TODO: rewrite by `biprodChainFst.comm`, then split on `j = k + 1` and on the four
  -- source-faithful cases `k = i + 1`, `k = i`, `k + 1 = i`, and generic. Each branch should
  -- combine the corresponding `normalized_middle_component_iso_hom_comp_fst_*` lemma with the
  -- matching `reduced_complex_of_normalized_middle_d_eq_*` formula.
  sorry

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
  -- TODO: rewrite by `biprodChainSnd.comm`, then use the same four degree cases. The upper and
  -- lower supported branches should use the head-annihilation statements from
  -- `adjacent_maps_respect_tail_split_of_normalized_middle`, the middle branch should rewrite by
  -- `identityDiskDifferential_eq_id`, and the generic branch should use
  -- `identityDiskDifferential_eq_zero_of_ne`.
  sorry

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

/-- Helper for Lemma 10.102.2: an equality of adjacent ranks identifies the corresponding
standard free modules. -/
private theorem finArrow_eq_of_eq {m n : ℕ} (h : m = n) :
    (Fin m → R) = (Fin n → R) := by
  -- This is just the dependent rewrite on the finite indexing type.
  cases h
  rfl

/-- Helper for Lemma 10.102.2: transport the standard free module along an equality of ranks. -/
private noncomputable def moduleIso_of_eq {m n : ℕ} (h : m = n) :
    ModuleCat.of R (Fin m → R) ≅ ModuleCat.of R (Fin n → R) :=
  match h with
  | rfl => Iso.refl _

/-- Helper for Lemma 10.102.2: transporting along a rank equality does not change evaluation at
the corresponding casted coordinate. -/
private theorem moduleIso_of_eq_hom_apply_cast
    {m n : ℕ} (h : m = n) (x : Fin m → R) (b : Fin m) :
    ((moduleIso_of_eq (R := R) h).hom.hom x) (cast (congrArg Fin h) b) = x b := by
  cases h
  rfl

/-- Helper for Lemma 10.102.2: transporting the pure basis vector along a rank equality and then
pulling it back by the inverse transport recovers the original basis vector. -/
private theorem moduleIso_of_eq_inv_apply_single_cast
    {m n : ℕ} (h : m = n) (a : Fin m) :
    (moduleIso_of_eq (R := R) h).inv.hom (Pi.single (cast (congrArg Fin h) a) (1 : R)) =
      (Pi.single a (1 : R) : Fin m → R) := by
  cases h
  rfl

/-- Helper for Lemma 10.102.2: transport the middle differential to explicit successor-coordinate
modules once the adjacent ranks have been written as `ns + 1` and `nt + 1`. -/
private noncomputable def diffAt_transport_to_successor_ranks
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1) :
    (Fin (ns + 1) → R) →ₗ[R] (Fin (nt + 1) → R) :=
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  (sourceEq.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ targetEq.hom).hom

/-- Helper for Lemma 10.102.2: the transported middle differential is exactly the original middle
map conjugated by the rank-transport isomorphisms. -/
@[simp] private theorem diffAt_transport_to_successor_ranks_hom
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1) :
    ModuleCat.ofHom (diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast) =
      (moduleIso_of_eq (R := R) hsucc).inv ≫ ModuleCat.ofHom (C.diffAt i) ≫
        (moduleIso_of_eq (R := R) hcast).hom := by
  -- The transport definition was chosen precisely so that its `ModuleCat` morphism is this
  -- conjugated composite.
  rfl

/-- Helper for Lemma 10.102.2: evaluating the transported middle differential on the transported
pivot basis vector is exactly the original matrix coefficient. -/
private theorem diffAt_transport_to_successor_ranks_entry
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (a : Fin (C.rank i.succ))
    (b : Fin (C.rank i.castSucc)) :
    let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
    let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
    ((diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast)
      (Pi.single a' (1 : R))) b' = C.diffEntry i a b := by
  -- Expand the transported map and rewrite the source and target transports by the two cast
  -- compatibility lemmas.
  change
    ((moduleIso_of_eq (R := R) hcast).hom.hom
        (C.diffAt i
          (((moduleIso_of_eq (R := R) hsucc).inv.hom)
            (Pi.single (cast (congrArg Fin hsucc) a) (1 : R)))))
      (cast (congrArg Fin hcast) b) =
    C.diffEntry i a b
  rw [moduleIso_of_eq_inv_apply_single_cast (R := R) hsucc a,
    moduleIso_of_eq_hom_apply_cast (R := R) hcast (C.diffAt i (Pi.single a (1 : R))) b]
  rfl

/-- Helper for Lemma 10.102.2: transporting the chosen pivot coordinates to the explicit
successor-coordinate modules preserves the unit-entry witness. -/
private theorem diffAt_transport_to_successor_ranks_pivot
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (a : Fin (C.rank i.succ))
    (b : Fin (C.rank i.castSucc))
    (hu : IsUnit (C.diffEntry i a b)) :
    let a' : Fin (ns + 1) := cast (congrArg Fin hsucc) a
    let b' : Fin (nt + 1) := cast (congrArg Fin hcast) b
    IsUnit
      ((diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast)
        (Pi.single a' (1 : R)) b') := by
  -- Route correction: reduce the transported pivot entry to the original coefficient by the exact
  -- transported-entry formula, then reuse the given unit witness.
  dsimp
  rw [diffAt_transport_to_successor_ranks_entry (R := R) (C := C) (i := i) hsucc hcast a b]
  exact hu

/-- Helper for Lemma 10.102.2: the head-tail splitting can be transported across a rank equality
without changing its mathematical content. -/
private noncomputable def splitOffUnitModuleIso_of_eq
    {n ns : ℕ} (h : n = ns + 1) :
    ModuleCat.of R (Fin n → R) ≅
      biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)) :=
  moduleIso_of_eq (R := R) h ≪≫ splitOffUnitModuleIso (R := R) ns

/-- Helper for Lemma 10.102.2: after transporting to explicit successor-coordinate modules, the
adjacent-degree recoordination cancels the outer rank transports and leaves only the explicit
normalized basis changes. -/
private theorem recoordinate_middle_diff_transport_cancel
    (C : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    {ns nt : ℕ}
    (hsucc : C.rank i.succ = ns + 1)
    (hcast : C.rank i.castSucc = nt + 1)
    (uSuccExp :
      ModuleCat.of R (Fin (ns + 1) → R) ≅
        ModuleCat.of R (Fin (ns + 1) → R))
    (uTargetExp :
      ModuleCat.of R (Fin (nt + 1) → R) ≅
        ModuleCat.of R (Fin (nt + 1) → R)) :
    let sourceEq := moduleIso_of_eq (R := R) hsucc
    let targetEq := moduleIso_of_eq (R := R) hcast
    let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
    let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
    let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
    let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
    sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom =
      uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom := by
  -- Rewrite the recoordinated middle differential in adjacent-degree coordinates and cancel the
  -- two outer transports coming from `sourceEq` and `targetEq`.
  let sourceEq := moduleIso_of_eq (R := R) hsucc
  let targetEq := moduleIso_of_eq (R := R) hcast
  let f := diffAt_transport_to_successor_ranks (R := R) (C := C) (i := i) hsucc hcast
  let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
  let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
  let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
  change sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom =
      uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom
  have hD :
      ModuleCat.ofHom (D.diffAt i) =
        uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uTarget.hom := by
    simpa [D] using
      recoordinateAtAdjacentDegrees_diffAt (R := R) (C := C) (i := i) (uSucc := uSucc)
        (uCast := uTarget)
  calc
    sourceEq.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ targetEq.hom =
        sourceEq.inv ≫ (uSucc.inv ≫ ModuleCat.ofHom (C.diffAt i) ≫ uTarget.hom) ≫ targetEq.hom := by
          simpa [Category.assoc] using
            congrArg (fun m ↦ sourceEq.inv ≫ m ≫ targetEq.hom) hD
    _ =
        uSuccExp.inv ≫
          ((moduleIso_of_eq (R := R) hsucc).inv ≫ ModuleCat.ofHom (C.diffAt i) ≫
            (moduleIso_of_eq (R := R) hcast).hom) ≫
          uTargetExp.hom := by
          simp [sourceEq, targetEq, uSucc, uTarget, Category.assoc]
    _ = uSuccExp.inv ≫ ModuleCat.ofHom f ≫ uTargetExp.hom := by
          rw [diffAt_transport_to_successor_ranks_hom (R := R) (C := C) (i := i) hsucc hcast]

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
  -- TODO: reuse `recoordinate_middle_diff_transport_cancel` to strip the outer transports, then
  -- identify the remaining conjugate with `g'` by explicit unfolding of the source and target
  -- basis changes.
  sorry

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
    let g' := g.comp (source_head_correction (R := R) g hg).symm.toLinearMap
    let uSuccExp := sourceSwap.toModuleIso ≪≫ uCorrExp
    let uSucc := sourceEq ≪≫ uSuccExp ≪≫ sourceEq.symm
    let uTarget := targetEq ≪≫ uTargetExp ≪≫ targetEq.symm
    let D := recoordinateAtAdjacentDegrees C i uSucc uTarget
    let eSource := splitOffUnitModuleIso_of_eq (R := R) hsucc
    let eTarget := splitOffUnitModuleIso_of_eq (R := R) hcast
    let F := eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom
    F = biprod.map (biprod.inl ≫ F ≫ biprod.fst) (𝟙 _) := by
  -- TODO: rewrite `F` by `recoordinate_middle_diff_splitOff_conjugate`, apply
  -- `normalized_middle_diff_is_biprod_map_tail_identity` to `g'`, and transport the result back
  -- to `F`.
  sorry

-- Proof sketch: use elementary row and column operations in the chosen coordinates of `C.diffAt i`
-- to isolate a unit entry, split off the corresponding free rank-one summand in degrees `i + 1`
-- and `i`, and identify the resulting summand with `identityDiskComplex i`.
/-- Lemma 10.102.2: if a differential `R^(n_{i + 1}) → R^(n_i)` in a bounded finite free complex
has a unit coordinate in the chosen standard bases, then the complex is isomorphic to the direct
sum of a reduced finite free complex and the two-term identity complex supported in degrees
`i + 1` and `i`. -/
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
