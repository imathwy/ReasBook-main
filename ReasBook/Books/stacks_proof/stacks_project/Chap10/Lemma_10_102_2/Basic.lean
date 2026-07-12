import Mathlib
import StacksProject_2024.Chap10.Situation_10_102_1

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

def identityDiskRank (i : Fin e) (j : ℕ) : ℕ :=
  if j = i.1 + 1 ∨ j = i.1 then 1 else 0

def identityDiskMatrix (i : Fin e) (j : ℕ) :
    Matrix (Fin (identityDiskRank i (j + 1))) (Fin (identityDiskRank i j)) R :=
  fun _ _ ↦ if j = i.1 then 1 else 0

abbrev identityDiskDifferential (i : Fin e) (j : ℕ) :
    ModuleCat.of R (Fin (identityDiskRank i (j + 1)) → R) ⟶
      ModuleCat.of R (Fin (identityDiskRank i j) → R) :=
  ModuleCat.ofHom ((identityDiskMatrix i j).toLinearMapRight')

/-- Helper for Lemma 10.102.2: the identity-disk differential vanishes away from the supported
degree `i`. -/
theorem identityDiskDifferential_eq_zero_of_ne (i : Fin e) {j : ℕ} (hj : j ≠ i.1) :
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

theorem identityDiskDifferential_sq (i : Fin e) (j : ℕ) :
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
theorem identityDiskRank_eq_zero_of_ne_support
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    identityDiskRank i j = 0 := by
  -- Both support tests in the definition are false away from the two distinguished degrees.
  simp [identityDiskRank, hjSucc, hjCast]

/-- Helper for Lemma 10.102.2: away from the supported degrees `i + 1` and `i`, the identity-disk
complex has a zero term. -/
theorem identityDiskComplex_X_isZero_of_ne_support
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
theorem identityDiskRank_succ (i : Fin e) :
    identityDiskRank i (i.1 + 1) = 1 := by
  -- The support condition holds exactly in degree `i + 1`.
  simp [identityDiskRank]

/-- Helper for Lemma 10.102.2: at the supported target degree `i`, the identity-disk rank is
`1`. -/
theorem identityDiskRank_castSucc (i : Fin e) :
    identityDiskRank i i.1 = 1 := by
  -- The support condition holds exactly in degree `i`.
  simp [identityDiskRank]


/-- Helper for Lemma 10.102.2: away from the two adjacent split degrees, the reduced rank agrees
with the original displayed rank. -/
theorem splitRank_eq_of_ne_adjacent
    (n : Fin (e + 1) → ℕ) (i : Fin e) {j : Fin (e + 1)}
    (hjSucc : j ≠ i.succ) (hjCast : j ≠ i.castSucc) :
    splitRank n i j = n j := by
  -- Outside the two distinguished degrees, both tests in `splitRank` are false.
  simp [splitRank, hjSucc, hjCast]

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the reduced rank is the predecessor of the
original rank, hence equals `ns` under the successor decomposition. -/
theorem splitRank_succ_eq_of_eq
    (n : Fin (e + 1) → ℕ) (i : Fin e) {ns : ℕ}
    (hsucc : n i.succ = ns + 1) :
    splitRank n i i.succ = ns := by
  -- The source degree is one of the two split degrees, so the definition subtracts exactly `1`.
  simp [splitRank, hsucc]

/-- Helper for Lemma 10.102.2: at degree `i`, the reduced rank is the predecessor of the original
rank, hence equals `nt` under the successor decomposition. -/
theorem splitRank_castSucc_eq_of_eq
    (n : Fin (e + 1) → ℕ) (i : Fin e) {nt : ℕ}
    (hcast : n i.castSucc = nt + 1) :
    splitRank n i i.castSucc = nt := by
  -- The target degree is the other split degree, so the definition subtracts exactly `1`.
  simp [splitRank, hcast]

/-- Helper for Lemma 10.102.2: the standard free module on `Fin (n + 1)` splits as the tail
coordinates together with the distinguished head coordinate. -/
noncomputable def splitOffUnitLinearEquiv (n : ℕ) :
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
theorem splitOffUnitLinearEquiv_apply_tail (n : ℕ) (x : Fin (n + 1) → R) :
    (splitOffUnitLinearEquiv (R := R) n x).1 = fun k ↦ x k.succ := by
  -- Unfold the explicit equivalence and simplify the `Fin`-reindexing on the first factor.
  ext k
  change ((LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) x) (some k)) = x k.succ
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', finSuccEquiv_symm_some]

/-- Helper for Lemma 10.102.2: the head-tail linear equivalence records the distinguished head
coordinate in the rank-one factor. -/
theorem splitOffUnitLinearEquiv_apply_head (n : ℕ) (x : Fin (n + 1) → R) :
    (splitOffUnitLinearEquiv (R := R) n x).2 = fun _ ↦ x 0 := by
  -- The second factor is the `none`/head coordinate, rewritten as a function on `Fin 1`.
  ext k
  fin_cases k
  change ((LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) x) none) = x 0
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', finSuccEquiv_symm_none]

/-- Helper for Lemma 10.102.2: the inverse head-tail linear equivalence reconstructs the original
vector by putting the rank-one factor in coordinate `0` and the tail factor in coordinates
`Fin.succ k`. -/
theorem splitOffUnitLinearEquiv_symm_apply_head_tail
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
theorem split_off_unit_linear_equiv_symm_eq_head_tail_sum
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
theorem piCongrLeft_swap_apply_zero
    {n : ℕ} (a : Fin (n + 1)) (x : Fin (n + 1) → R) :
    (LinearEquiv.piCongrLeft R (fun _ : Fin (n + 1) ↦ R) (Equiv.swap 0 a) x) 0 = x a := by
  -- The head coordinate after swapping is exactly the original `a`-coordinate.
  simp [LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft', Equiv.swap_apply_left]

/-- Helper for Lemma 10.102.2: the inverse head-tail splitting sends the pure head vector in the
product model to the distinguished basis vector in `Fin (n + 1) → R`. -/
theorem splitOffUnitLinearEquiv_symm_apply_pure_head
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
theorem map_head_coordinate_of_split_off_unit_decomposition
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
theorem split_off_unit_linear_equiv_apply_head_of_normalized_map
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
theorem split_off_unit_linear_equiv_apply_head_of_tail_basis
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
noncomputable def splitOffUnitModuleIso (n : ℕ) :
    ModuleCat.of R (Fin (n + 1) → R) ≅
      biprod (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R)) :=
  (splitOffUnitLinearEquiv (R := R) n).toModuleIso ≪≫
    (ModuleCat.biprodIsoProd (ModuleCat.of R (Fin n → R)) (ModuleCat.of R (Fin 1 → R))).symm

end FiniteFreeComplex

end
