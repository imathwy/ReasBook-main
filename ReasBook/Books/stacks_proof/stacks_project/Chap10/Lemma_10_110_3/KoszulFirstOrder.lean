import StacksProject_2024.Chap10.Lemma_10_110_3.IdealCoordinate

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: cotangent-basis coordinates of scalar multiples of the
chosen maximal-ideal lifts are the expected residue coordinates. -/
private lemma cotangentBasis_repr_smul_lift
    {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R))
    (x : Fin n → maximalIdeal R)
    (hx : ∀ j, (maximalIdeal R).toCotangent (x j) = b j)
    (r : R) (a j : Fin n) :
    b.repr ((maximalIdeal R).toCotangent (r • x j)) a =
      if a = j then algebraMap R (ResidueField R) r else 0 := by
  -- Push the `R`-scalar through the cotangent quotient and then read the basis coordinate.
  rw [map_smul]
  rw [hx j]
  have hmap : b.repr (r • b j) = r • b.repr (b j) := by
    exact map_smul (b.repr.toLinearMap.restrictScalars R) r (b j)
  rw [hmap]
  by_cases h : a = j
  · subst h
    simp [Module.Basis.repr_self, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
  · simp [Module.Basis.repr_self, h]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: cotangent-basis coordinates of finite sums of scalar
multiples of the chosen maximal-ideal lifts are the expected residue coordinates. -/
private lemma cotangentBasis_repr_sum_smul_lift
    {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R))
    (x : Fin n → maximalIdeal R)
    (hx : ∀ j, (maximalIdeal R).toCotangent (x j) = b j)
    (c : Fin n → R) (j : Fin n)
    (hmem : (∑ a : Fin n, c a * (x a : R)) ∈ maximalIdeal R) :
    b.repr ((maximalIdeal R).toCotangent
      ⟨∑ a : Fin n, c a * (x a : R), hmem⟩) j =
      algebraMap R (ResidueField R) (c j) := by
  classical
  -- Identify the subtype-valued sum with the ordinary sum whose membership is recorded by `hmem`.
  have hsub :
      (⟨∑ a : Fin n, c a * (x a : R), hmem⟩ : maximalIdeal R) =
        ∑ a : Fin n, c a • x a := by
    ext
    simp
  rw [hsub]
  -- After applying the cotangent quotient, all off-diagonal basis coordinates vanish.
  rw [map_sum]
  rw [map_sum]
  rw [Finsupp.finset_sum_apply]
  simp_rw [cotangentBasis_repr_smul_lift (R := R) b x hx]
  simp

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a coordinate of the finite-family Koszul differential is
the corresponding finite sum of standard coordinate-function differentials. -/
private lemma localKoszulDifferential_coord_eq_sum_basisCoord
    {n i : ℕ} (x : Fin n → maximalIdeal R)
    (z : ⋀[R]^(i + 1) (Fin n → R))
    (T : Set.powersetCard (Fin n) i) :
    ((Pi.basisFun R (Fin n)).exteriorPower i).repr
      (localKoszulDifferentialLinearMap
        (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i
        z) T =
      ∑ j : Fin n, (x j : R) *
        ((Pi.basisFun R (Fin n)).exteriorPower i).repr
          (localKoszulDifferentialLinearMap ((Pi.basisFun R (Fin n)).coord j) i z) T := by
  classical
  let B := (Pi.basisFun R (Fin n)).exteriorPower i
  let coord : ⋀[R]^i (Fin n → R) →ₗ[R] R := Module.Basis.coord B T
  have hφ :
      localKoszulFamilyLinearMap (R := R) (fun j ↦ (x j : R)) =
        ∑ j : Fin n, (x j : R) • (Pi.basisFun R (Fin n)).coord j := by
    -- Expand the finite-family linear form in the dual basis of the standard finite free module.
    ext v
    rw [localKoszulFamilyLinearMap]
    simp [Module.piEquiv_apply_apply, mul_comm]
  have hmap :
      localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z =
        ∑ j : Fin n, (x j : R) •
          localKoszulDifferentialLinearMap ((Pi.basisFun R (Fin n)).coord j) i z := by
    -- Compare in the ambient exterior algebra so the linearity of `contractLeft` is explicit.
    apply Subtype.ext
    rw [hφ]
    simp [localKoszulDifferentialLinearMap_apply, map_sum, map_smul]
  -- Apply the fixed coordinate functional to the linearized differential.
  calc
    ((Pi.basisFun R (Fin n)).exteriorPower i).repr
        (localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) T =
        coord (localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) := rfl
    _ = coord (∑ j : Fin n, (x j : R) •
          localKoszulDifferentialLinearMap ((Pi.basisFun R (Fin n)).coord j) i z) := by
        rw [hmap]
    _ = ∑ j : Fin n, (x j : R) *
        ((Pi.basisFun R (Fin n)).exteriorPower i).repr
          (localKoszulDifferentialLinearMap ((Pi.basisFun R (Fin n)).coord j) i z) T := by
        simp [coord, B, map_sum, map_smul]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: every standard coordinate of the finite-family Koszul
differential lies in the maximal ideal. -/
private lemma localKoszulDifferential_coord_mem_maximalIdeal
    {n i : ℕ} (x : Fin n → maximalIdeal R)
    (z : ⋀[R]^(i + 1) (Fin n → R))
    (T : Set.powersetCard (Fin n) i) :
    ((Pi.basisFun R (Fin n)).exteriorPower i).repr
      (localKoszulDifferentialLinearMap
        (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) T ∈ maximalIdeal R := by
  classical
  -- Use the coordinate-sum normal form; each summand contains one chosen lift in `𝔪`.
  rw [localKoszulDifferential_coord_eq_sum_basisCoord (R := R) x z T]
  refine Ideal.sum_mem (maximalIdeal R) ?_
  intro j _
  exact Ideal.mul_mem_right _ _ (x j).property

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the erased coordinate of the Koszul differential, reduced
to the cotangent space, as a stable linear map. -/
private noncomputable def localKoszulDifferentialCotangentCoord
    {n i : ℕ} (x : Fin n → maximalIdeal R) (T : Set.powersetCard (Fin n) i) :
    ⋀[R]^(i + 1) (Fin n → R) →ₗ[R] CotangentSpace R :=
  (maximalIdeal R).toCotangent.comp
    (((Module.Basis.coord ((Pi.basisFun R (Fin n)).exteriorPower i) T).comp
      (localKoszulDifferentialLinearMap
        (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i)).codRestrict
        (maximalIdeal R)
        (fun z ↦ localKoszulDifferential_coord_mem_maximalIdeal (R := R) x z T))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the stable cotangent-coordinate map is the cotangent class
of the corresponding standard differential coordinate. -/
private lemma localKoszulDifferentialCotangentCoord_apply
    {n i : ℕ} (x : Fin n → maximalIdeal R) (T : Set.powersetCard (Fin n) i)
    (z : ⋀[R]^(i + 1) (Fin n → R)) :
    localKoszulDifferentialCotangentCoord (R := R) x T z =
      (maximalIdeal R).toCotangent
        ⟨((Pi.basisFun R (Fin n)).exteriorPower i).repr
          (localKoszulDifferentialLinearMap
            (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) T,
          localKoszulDifferential_coord_mem_maximalIdeal (R := R) x z T⟩ :=
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: erasing the same member from two unequal finite sets
that both contain it still gives unequal finite sets. -/
private lemma finset_erase_ne_erase_of_ne_of_mem
    {α : Type*} [DecidableEq α] {s t : Finset α} {a : α}
    (hst : s ≠ t) (has : a ∈ s) (hat : a ∈ t) :
    s.erase a ≠ t.erase a := by
  -- Reinsert the common erased element to recover the original sets.
  intro h
  apply hst
  calc
    s = insert a (s.erase a) := (Finset.insert_erase has).symm
    _ = insert a (t.erase a) := by rw [h]
    _ = t := Finset.insert_erase hat

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: contracting a standard exterior basis vector by the
coordinate of its minimum gives the basis vector indexed by the erased set. -/
private lemma standardBasisContract_eq_basis_min_erase
    {n i : ℕ}
    (U : Set.powersetCard (Fin n) (i + 1))
    (hU : (U : Finset (Fin n)).Nonempty)
    (hcard : ((U : Finset (Fin n)).erase ((U : Finset (Fin n)).min' hU)).card = i) :
    localKoszulDifferentialLinearMap
        ((Pi.basisFun R (Fin n)).coord ((U : Finset (Fin n)).min' hU)) i
        (((Pi.basisFun R (Fin n)).exteriorPower (i + 1)) U) =
      ((Pi.basisFun R (Fin n)).exteriorPower i) (Set.powersetCard.ofCard hcard) := by
  let j : Fin n := (U : Finset (Fin n)).min' hU
  let Bsrc := (Pi.basisFun R (Fin n)).exteriorPower (i + 1)
  let Btgt := (Pi.basisFun R (Fin n)).exteriorPower i
  let dmap := localKoszulDifferentialLinearMap ((Pi.basisFun R (Fin n)).coord j) i
  have hhead :
      ((U : Finset (Fin n)).orderEmbOfFin U.property) (0 : Fin (i + 1)) = j := by
    simpa [j] using
      (Finset.orderEmbOfFin_zero (s := (U : Finset (Fin n))) (k := i + 1)
        U.property (Nat.succ_pos i))
  have htailEmb :
      ((U : Finset (Fin n)).erase j).orderEmbOfFin hcard =
        (Fin.succOrderEmb i).trans ((U : Finset (Fin n)).orderEmbOfFin U.property) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro k
    simp only [Finset.mem_erase]
    constructor
    · intro heq
      have hne : (Fin.succOrderEmb i k) ≠ (0 : Fin (i + 1)) := by
        simpa using (Fin.succ_ne_zero k)
      exact hne (((U : Finset (Fin n)).orderEmbOfFin U.property).injective
        (by simpa [j, hhead] using heq))
    · exact Finset.orderEmbOfFin_mem (U : Finset (Fin n)) U.property ((Fin.succOrderEmb i) k)
  have htail :
      Matrix.vecTail ((Pi.basisFun R (Fin n)) ∘
          ((U : Finset (Fin n)).orderEmbOfFin U.property)) =
        (Pi.basisFun R (Fin n)) ∘
          (((U : Finset (Fin n)).erase j).orderEmbOfFin hcard) := by
    funext k
    rw [htailEmb]
    rfl
  have htail_zero :
      CliffordAlgebra.contractLeft ((Pi.basisFun R (Fin n)).coord j)
        ((ExteriorAlgebra.ιMulti R i)
          ((Pi.basisFun R (Fin n)) ∘
            (((U : Finset (Fin n)).erase j).orderEmbOfFin hcard))) = 0 := by
    -- After removing the minimum, no remaining factor has nonzero `j`-coordinate.
    apply contractLeft_ιMulti_eq_zero_of_apply_eq_zero
    intro k
    have hne : (((U : Finset (Fin n)).erase j).orderEmbOfFin hcard k) ≠ j := by
      exact (Finset.mem_erase.mp
        (Finset.orderEmbOfFin_mem ((U : Finset (Fin n)).erase j) hcard k)).1
    simp [hne]
  -- Expand the basis monomial at its minimum and use the contraction Leibniz rule.
  apply Subtype.ext
  dsimp [dmap, Bsrc, Btgt]
  rw [exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family_apply_coe]
  rw [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  simp only [Function.comp_apply]
  rw [hhead, htail]
  rw [htail_zero]
  simp [exteriorPower.basis_apply, ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, j]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: left multiplication by a standard basis vector sends
degree `i - 1` exterior elements into degree `i`. -/
private lemma standardExteriorPower_leftMulPred_mem
    {n i : ℕ} (hi : 0 < i) (a : Fin n)
    {y : ExteriorAlgebra R (Fin n → R)}
    (hy : y ∈ ⋀[R]^(i - 1) (Fin n → R)) :
    ExteriorAlgebra.ι R ((Pi.basisFun R (Fin n)) a) * y ∈
      ⋀[R]^i (Fin n → R) := by
  have ha : ExteriorAlgebra.ι R ((Pi.basisFun R (Fin n)) a) ∈
      ⋀[R]^1 (Fin n → R) := by
    simp [ExteriorAlgebra.exteriorPower]
  have hmul := SetLike.mul_mem_graded ha hy
  -- The graded product has degree `1 + (i - 1)`, which is `i` because `i` is positive.
  rw [ExteriorAlgebra.exteriorPower]
  rw [← Nat.succ_pred_eq_of_pos hi]
  simpa [ExteriorAlgebra.exteriorPower, Nat.add_comm] using hmul

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the linear map given by left multiplication by a standard
basis vector from degree `i - 1` to degree `i`. -/
private noncomputable def standardExteriorPower_leftMulPredMap
    {n i : ℕ} (hi : 0 < i) (a : Fin n) :
    ⋀[R]^(i - 1) (Fin n → R) →ₗ[R] ⋀[R]^i (Fin n → R) :=
  (LinearMap.mulLeft R (ExteriorAlgebra.ι R ((Pi.basisFun R (Fin n)) a))).restrict
    (fun _ hy => standardExteriorPower_leftMulPred_mem (R := R) hi a hy)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the left-multiplication map has the expected ambient
exterior-algebra value. -/
private lemma standardExteriorPower_leftMulPredMap_apply_coe
    {n i : ℕ} (hi : 0 < i) (a : Fin n)
    (y : ⋀[R]^(i - 1) (Fin n → R)) :
    (standardExteriorPower_leftMulPredMap (R := R) hi a y :
      ExteriorAlgebra R (Fin n → R)) =
      ExteriorAlgebra.ι R ((Pi.basisFun R (Fin n)) a) *
        (y : ExteriorAlgebra R (Fin n → R)) :=
  rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: on a standard exterior basis vector, the left-multiplication
map is the exterior product with the added first factor. -/
private lemma standardExteriorPower_leftMulPredMap_basis_apply
    {n q : ℕ} (hi : 0 < q + 1) (a : Fin n)
    (V : Set.powersetCard (Fin n) q) :
    standardExteriorPower_leftMulPredMap (R := R) (i := q + 1) hi a
        (((Pi.basisFun R (Fin n)).exteriorPower q) V) =
      exteriorPower.ιMulti R (q + 1)
        (Fin.cons ((Pi.basisFun R (Fin n)) a)
          ((Pi.basisFun R (Fin n)) ∘ (Set.powersetCard.ofFinEmbEquiv.symm V))) := by
  -- Compare in the ambient exterior algebra, where the statement is the recursive definition
  -- of `ιMulti`.
  apply Subtype.ext
  dsimp [standardExteriorPower_leftMulPredMap]
  rw [exteriorPower.basis_apply]
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  congr 1

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a left-multiple by the standard basis vector `a` has zero
coordinate on every standard exterior basis vector whose index omits `a`. -/
private lemma standardExteriorPower_coord_leftMulPredMap_eq_zero_of_not_mem
    {n i : ℕ} (hi : 0 < i) (a : Fin n)
    (T : Set.powersetCard (Fin n) i)
    (haT : a ∉ (T : Finset (Fin n)))
    (y : ⋀[R]^(i - 1) (Fin n → R)) :
    ((Pi.basisFun R (Fin n)).exteriorPower i).repr
      (standardExteriorPower_leftMulPredMap (R := R) hi a y) T = 0 := by
  classical
  -- It is enough to check the coordinate functional after precomposing with the basis of the
  -- source exterior power.
  cases i with
  | zero => omega
  | succ q =>
      let Bq := (Pi.basisFun R (Fin n)).exteriorPower q
      let Bt := (Pi.basisFun R (Fin n)).exteriorPower (q + 1)
      let F : ⋀[R]^q (Fin n → R) →ₗ[R] R :=
        (Module.Basis.coord Bt T).comp
          (standardExteriorPower_leftMulPredMap (R := R) (i := q + 1) hi a)
      have hF : F = 0 := by
        apply Bq.ext
        intro V
        have hbasis :=
          standardExteriorPower_leftMulPredMap_basis_apply (R := R) (q := q) hi a V
        dsimp [F, Bq, Bt]
        calc
          ((Module.Basis.exteriorPower (q + 1) (Pi.basisFun R (Fin n))).repr
              ((standardExteriorPower_leftMulPredMap (R := R) (i := q + 1) hi a)
                (((Pi.basisFun R (Fin n)).exteriorPower q) V))) T =
              ((Module.Basis.exteriorPower (q + 1) (Pi.basisFun R (Fin n))).repr
                (exteriorPower.ιMulti R (q + 1)
                  (Fin.cons ((Pi.basisFun R (Fin n)) a)
                    ((Pi.basisFun R (Fin n)) ∘
                      (Set.powersetCard.ofFinEmbEquiv.symm V))))) T := by
                exact congrArg (fun x =>
                  ((Module.Basis.exteriorPower (q + 1) (Pi.basisFun R (Fin n))).repr x) T)
                  hbasis
          _ = 0 := by
              rw [exteriorPower.basis_repr_apply]
              rw [exteriorPower.ιMultiDual_apply_ιMulti]
              apply Matrix.det_eq_zero_of_row_eq_zero 0
              intro j
              have hne : Set.powersetCard.ofFinEmbEquiv.symm T j ≠ a := by
                intro h
                exact haT (by
                  rw [← h]
                  simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
                    Finset.orderEmbOfFin_mem (T : Finset (Fin n)) T.property j)
              simp [Pi.basisFun_apply, hne]
      have := congrArg (fun f : ⋀[R]^q (Fin n → R) →ₗ[R] R => f y) hF
      simpa [F, Bt] using this

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: contraction by the minimum coordinate functional, followed
by the erased-target coordinate, recovers the source exterior coordinate. -/
private lemma standardBasisContractCoord_min_erase
    {n i : ℕ}
    (S : Set.powersetCard (Fin n) (i + 1))
    (hS : (S : Finset (Fin n)).Nonempty)
    (hcard : ((S : Finset (Fin n)).erase ((S : Finset (Fin n)).min' hS)).card = i)
    (z : ⋀[R]^(i + 1) (Fin n → R)) :
    ((Pi.basisFun R (Fin n)).exteriorPower i).repr
      (localKoszulDifferentialLinearMap
        ((Pi.basisFun R (Fin n)).coord ((S : Finset (Fin n)).min' hS)) i z)
      (Set.powersetCard.ofCard hcard) =
      ((Pi.basisFun R (Fin n)).exteriorPower (i + 1)).repr z S := by
  classical
  let Bsrc := (Pi.basisFun R (Fin n)).exteriorPower (i + 1)
  let Btgt := (Pi.basisFun R (Fin n)).exteriorPower i
  let coord : ⋀[R]^i (Fin n → R) →ₗ[R] R :=
    Module.Basis.coord Btgt (Set.powersetCard.ofCard hcard)
  let dmap := localKoszulDifferentialLinearMap
    ((Pi.basisFun R (Fin n)).coord ((S : Finset (Fin n)).min' hS)) i
  let L : ⋀[R]^(i + 1) (Fin n → R) →ₗ[R] R := coord.comp dmap
  have hzsum : z = ∑ U, Bsrc.repr z U • Bsrc U := by
    exact (Bsrc.sum_repr z).symm
  -- Reduce to exterior basis vectors, where the minimum-element contraction is a diagonal
  -- coordinate computation with sign `+1`.
  change coord (dmap z) = Bsrc.repr z S
  have hdiag : coord (dmap (Bsrc S)) = 1 := by
    have hcontract : dmap (Bsrc S) = Btgt (Set.powersetCard.ofCard hcard) := by
      simpa [dmap, Bsrc, Btgt] using
        standardBasisContract_eq_basis_min_erase (R := R) S hS hcard
    -- The diagonal contraction is exactly the erased target basis vector, whose coordinate is one.
    rw [hcontract]
    simp [coord, Btgt]
  have hoffdiag (U : Set.powersetCard (Fin n) (i + 1)) (hUS : U ≠ S) :
      coord (dmap (Bsrc U)) = 0 := by
    by_cases hjU : ((S : Finset (Fin n)).min' hS) ∈ (U : Finset (Fin n))
    · let j : Fin n := (S : Finset (Fin n)).min' hS
      have hjUj : j ∈ (U : Finset (Fin n)) := by
        simpa [j] using hjU
      have hjS : j ∈ (S : Finset (Fin n)) := by
        exact Finset.min'_mem _ _
      have hU : (U : Finset (Fin n)).Nonempty := ⟨j, hjUj⟩
      let a : Fin n := (U : Finset (Fin n)).min' hU
      have haU : a ∈ (U : Finset (Fin n)) := by
        exact Finset.min'_mem _ _
      have hUSfin : (U : Finset (Fin n)) ≠ (S : Finset (Fin n)) := by
        intro h
        exact hUS (Subtype.ext h)
      by_cases hamin : a = j
      · have hcardU : ((U : Finset (Fin n)).erase a).card = i := by
          rw [Finset.card_erase_of_mem haU, U.property]
          omega
        have hcontract : dmap (Bsrc U) = Btgt (Set.powersetCard.ofCard hcardU) := by
          simpa [dmap, Bsrc, Btgt, a, j, hamin] using
            standardBasisContract_eq_basis_min_erase (R := R) U hU hcardU
        have herase_ne_j :
            ((U : Finset (Fin n)).erase j) ≠ ((S : Finset (Fin n)).erase j) :=
          finset_erase_ne_erase_of_ne_of_mem hUSfin hjUj hjS
        have herase_ne :
            ((U : Finset (Fin n)).erase a) ≠ ((S : Finset (Fin n)).erase j) := by
          simpa [hamin] using herase_ne_j
        have hneT :
            Set.powersetCard.ofCard hcardU ≠ Set.powersetCard.ofCard hcard := by
          intro h
          exact herase_ne (by
            simpa using congrArg
              (fun T : Set.powersetCard (Fin n) i => (T : Finset (Fin n))) h)
        -- If the contracted basis vector is indexed by `U.erase j`, it has zero target
        -- coordinate because `U.erase j` is not `S.erase j`.
        rw [hcontract]
        simpa [coord, Btgt] using
          exteriorPower.basis_repr_ne (R := R) (n := i) (Pi.basisFun R (Fin n)) hneT
      · have hle_aj : a ≤ j := by
          exact Finset.min'_le (U : Finset (Fin n)) j hjUj
        have hlt_aj : a < j := lt_of_le_of_ne hle_aj hamin
        have hnot_a_target :
            a ∉ (Set.powersetCard.ofCard hcard : Finset (Fin n)) := by
          intro haT
          have haerase : a ∈ ((S : Finset (Fin n)).erase j) := by
            simpa using haT
          have haS : a ∈ (S : Finset (Fin n)) := (Finset.mem_erase.mp haerase).2
          have hle_ja : j ≤ a := Finset.min'_le (S : Finset (Fin n)) a haS
          exact (not_lt_of_ge hle_ja) hlt_aj
        have hi_pos : 0 < i := by
          by_contra hi
          have hi0 : i = 0 := Nat.eq_zero_of_not_pos hi
          have hcardU_one : (U : Finset (Fin n)).card = 1 := by
            simpa [hi0] using U.property
          obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcardU_one
          have hU_singleton_j : (U : Finset (Fin n)) = {j} := by
            rw [hx]
            have hjx : j = x := by
              simpa [hx] using hjUj
            simpa [hjx]
          have ha_eq_j : a = j := by
            have : a ∈ ({j} : Finset (Fin n)) := by
              simpa [hU_singleton_j] using haU
            simpa using this
          exact hamin ha_eq_j
        -- When the minimum of `U` is strictly below `j`, the recursive contraction formula
        -- exposes a left factor `e_a`; the target `S.erase j` omits `a`, so the support lemma
        -- kills this coordinate.
        cases i with
        | zero => omega
        | succ q =>
            let φ : (Fin n → R) →ₗ[R] R := (Pi.basisFun R (Fin n)).coord j
            have hcardTail : ((U : Finset (Fin n)).erase a).card = q + 1 := by
              rw [Finset.card_erase_of_mem haU, U.property]
              omega
            let Tail : ⋀[R]^(q + 1) (Fin n → R) :=
              ((Pi.basisFun R (Fin n)).exteriorPower (q + 1))
                (Set.powersetCard.ofCard hcardTail)
            let tailContract : ⋀[R]^q (Fin n → R) :=
              localKoszulDifferentialLinearMap φ q Tail
            have hheadU :
                ((U : Finset (Fin n)).orderEmbOfFin U.property) (0 : Fin (q + 2)) = a := by
              simpa [a] using
                (Finset.orderEmbOfFin_zero (s := (U : Finset (Fin n))) (k := q + 2)
                  U.property (Nat.succ_pos (q + 1)))
            have htailEmb :
                ((U : Finset (Fin n)).erase a).orderEmbOfFin hcardTail =
                  (Fin.succOrderEmb (q + 1)).trans
                    ((U : Finset (Fin n)).orderEmbOfFin U.property) := by
              symm
              apply Finset.orderEmbOfFin_unique'
              intro k
              simp only [Finset.mem_erase]
              constructor
              · intro heq
                have hne : (Fin.succOrderEmb (q + 1) k) ≠ (0 : Fin (q + 2)) := by
                  simpa using (Fin.succ_ne_zero k)
                exact hne (((U : Finset (Fin n)).orderEmbOfFin U.property).injective
                  (by simpa [a, hheadU] using heq))
              · exact Finset.orderEmbOfFin_mem (U : Finset (Fin n)) U.property
                  ((Fin.succOrderEmb (q + 1)) k)
            have htail :
                Matrix.vecTail ((Pi.basisFun R (Fin n)) ∘
                    ((U : Finset (Fin n)).orderEmbOfFin U.property)) =
                  (Pi.basisFun R (Fin n)) ∘
                    (((U : Finset (Fin n)).erase a).orderEmbOfFin hcardTail) := by
              funext k
              rw [htailEmb]
              rfl
            have hφa : φ ((Pi.basisFun R (Fin n)) a) = 0 := by
              simp [φ, Ne.symm hamin]
            have hcontract :
                dmap (Bsrc U) =
                  -standardExteriorPower_leftMulPredMap
                    (R := R) (i := q + 1) (Nat.succ_pos q) a tailContract := by
              apply Subtype.ext
              dsimp [dmap, Bsrc]
              rw [exteriorPower.basis_apply]
              simp only [exteriorPower.ιMulti_family_apply_coe]
              rw [ExteriorAlgebra.ιMulti_family]
              rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
              rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
              simp only [Function.comp_apply]
              rw [hheadU, htail, hφa]
              have hleft_coe :
                  ((standardExteriorPower_leftMulPredMap
                    (R := R) (i := q + 1) (Nat.succ_pos q) a tailContract :
                      ⋀[R]^(q + 1) (Fin n → R)) :
                    ExteriorAlgebra R (Fin n → R)) =
                    ExteriorAlgebra.ι R ((Pi.basisFun R (Fin n)) a) *
                      (tailContract : ExteriorAlgebra R (Fin n → R)) :=
                standardExteriorPower_leftMulPredMap_apply_coe
                  (R := R) (i := q + 1) (Nat.succ_pos q) a tailContract
              have htailContract_coe :
                  (tailContract : ExteriorAlgebra R (Fin n → R)) =
                    CliffordAlgebra.contractLeft
                      ((Pi.basisFun R (Fin n)).coord ((S : Finset (Fin n)).min' hS))
                      ((ExteriorAlgebra.ιMulti R (q + 1))
                        ((Pi.basisFun R (Fin n)) ∘
                          (((U : Finset (Fin n)).erase a).orderEmbOfFin hcardTail))) := by
                simp [tailContract, φ, Tail, localKoszulDifferentialLinearMap_apply,
                  exteriorPower.basis_apply, ExteriorAlgebra.ιMulti_family,
                  Set.powersetCard.ofFinEmbEquiv_symm_apply, j]
              rw [zero_smul, zero_sub]
              apply neg_inj.mpr
              exact (hleft_coe.trans
                (congrArg
                  (fun y : ExteriorAlgebra R (Fin n → R) =>
                    ExteriorAlgebra.ι R ((Pi.basisFun R (Fin n)) a) * y)
                  htailContract_coe)).symm
            have hsupport :
                coord (standardExteriorPower_leftMulPredMap
                  (R := R) (i := q + 1) (Nat.succ_pos q) a tailContract) = 0 := by
              simpa [coord, Btgt] using
                standardExteriorPower_coord_leftMulPredMap_eq_zero_of_not_mem
                  (R := R) (i := q + 1) (Nat.succ_pos q) a
                  (Set.powersetCard.ofCard hcard) hnot_a_target tailContract
            rw [hcontract, map_neg, hsupport, neg_zero]
    · have hzero : dmap (Bsrc U) = 0 := by
        apply Subtype.ext
        dsimp [dmap, Bsrc, localKoszulDifferentialLinearMap]
        rw [exteriorPower.basis_apply]
        simp only [exteriorPower.ιMulti_family_apply_coe]
        apply contractLeft_ιMulti_eq_zero_of_apply_eq_zero
        intro k
        have hnot :
            Set.powersetCard.ofFinEmbEquiv.symm U k ≠
              ((S : Finset (Fin n)).min' hS) := by
          intro hk
          exact hjU (by
            rw [← hk]
            simpa [Set.powersetCard.ofFinEmbEquiv_symm_apply] using
              Finset.orderEmbOfFin_mem (U : Finset (Fin n)) U.property k)
        simp [hnot]
      -- If the minimum does not occur in `U`, every factor is killed by the coordinate functional.
      rw [hzero]
      exact map_zero coord
  have hleft :
      coord (dmap z) = ∑ U, Bsrc.repr z U * coord (dmap (Bsrc U)) := by
    -- Expand `z` in the exterior basis and push the fixed coordinate functional
    -- through the finite linear combination.
    have hdmap_sum :
        dmap z = dmap (∑ U, Bsrc.repr z U • Bsrc U) := congrArg dmap hzsum
    have hdmap_linear :
        dmap (∑ U, Bsrc.repr z U • Bsrc U) =
          ∑ U, Bsrc.repr z U • dmap (Bsrc U) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro U _hU
      exact map_smul dmap (Bsrc.repr z U) (Bsrc U)
    calc
      coord (dmap z) = coord (dmap (∑ U, Bsrc.repr z U • Bsrc U)) := by
        rw [hdmap_sum]
      _ = coord (∑ U, Bsrc.repr z U • dmap (Bsrc U)) := by
        rw [hdmap_linear]
      _ = ∑ U, Bsrc.repr z U * coord (dmap (Bsrc U)) := by
        simp [map_sum, map_smul]
  rw [hleft]
  rw [Finset.sum_eq_single S]
  · rw [hdiag, mul_one]
  · intro U _ hUS
    rw [hoffdiag U hUS, mul_zero]
  · intro hnot
    simp at hnot

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the minimum erased cotangent coordinate of the Koszul
differential recovers the corresponding source exterior coordinate modulo `𝔪`. -/
private lemma localKoszulDifferential_cotangent_min_erase_coord
    {n i : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R))
    (x : Fin n → maximalIdeal R)
    (hx : ∀ j, (maximalIdeal R).toCotangent (x j) = b j)
    (S : Set.powersetCard (Fin n) (i + 1))
    (hS : (S : Finset (Fin n)).Nonempty)
    (hcard : ((S : Finset (Fin n)).erase ((S : Finset (Fin n)).min' hS)).card = i)
    (z : ⋀[R]^(i + 1) (Fin n → R)) :
      b.repr
        (localKoszulDifferentialCotangentCoord (R := R) x
          (Set.powersetCard.ofCard hcard) z) ((S : Finset (Fin n)).min' hS) =
        algebraMap R (ResidueField R)
          (((Pi.basisFun R (Fin n)).exteriorPower (i + 1)).repr z S) := by
  classical
  let T : Set.powersetCard (Fin n) i := Set.powersetCard.ofCard hcard
  let j : Fin n := (S : Finset (Fin n)).min' hS
  let c : Fin n → R := fun a ↦
    ((Pi.basisFun R (Fin n)).exteriorPower i).repr
      (localKoszulDifferentialLinearMap ((Pi.basisFun R (Fin n)).coord a) i z) T
  have hsum :
      ((Pi.basisFun R (Fin n)).exteriorPower i).repr
        (localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun a ↦ (x a : R))) i z) T =
        ∑ a : Fin n, c a * (x a : R) := by
    simpa [c, T, mul_comm] using
      localKoszulDifferential_coord_eq_sum_basisCoord (R := R) x z T
  have hmem_sum : (∑ a : Fin n, c a * (x a : R)) ∈ maximalIdeal R := by
    -- Transfer maximal-ideal membership from the actual differential coordinate to the sum form.
    rw [← hsum]
    exact localKoszulDifferential_coord_mem_maximalIdeal (R := R) x z T
  have hsub :
      (⟨((Pi.basisFun R (Fin n)).exteriorPower i).repr
        (localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun a ↦ (x a : R))) i z) T,
        localKoszulDifferential_coord_mem_maximalIdeal (R := R) x z T⟩ : maximalIdeal R) =
      ⟨∑ a : Fin n, c a * (x a : R), hmem_sum⟩ := by
    ext
    exact hsum
  -- Rewrite the stable cotangent coordinate as the cotangent class of the coordinate-sum.
  rw [localKoszulDifferentialCotangentCoord_apply, hsub]
  rw [cotangentBasis_repr_sum_smul_lift (R := R) b x hx c j hmem_sum]
  -- The minimum-coordinate contraction has sign `+1`, so no unit-sign cancellation is needed.
  simpa [c, j, T] using congrArg (algebraMap R (ResidueField R))
    (standardBasisContractCoord_min_erase (R := R) S hS hcard z)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: if the Koszul differential is in the square layer, then all
source exterior coordinates vanish modulo the maximal ideal. -/
private lemma localKoszulDifferential_firstOrder_coords_eq_zero
    {n i : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R))
    (x : Fin n → maximalIdeal R)
    (hx : ∀ j, (maximalIdeal R).toCotangent (x j) = b j)
    (z : ⋀[R]^(i + 1) (Fin n → R))
    (hz : localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z ∈
        (maximalIdeal R) ^ 2 •
          (⊤ : Submodule R (⋀[R]^i (Fin n → R))))
    (S : Set.powersetCard (Fin n) (i + 1)) :
    Ideal.Quotient.mk (maximalIdeal R)
      (((Pi.basisFun R (Fin n)).exteriorPower (i + 1)).repr z S) = 0 := by
  classical
  have hnonempty : (S : Finset (Fin n)).Nonempty := by
    apply Finset.card_pos.mp
    rw [S.prop]
    omega
  let j : Fin n := (S : Finset (Fin n)).min' hnonempty
  have hj : j ∈ (S : Finset (Fin n)) := by
    exact Finset.min'_mem _ _
  have hcard : ((S : Finset (Fin n)).erase j).card = i := by
    rw [Finset.card_erase_of_mem hj, S.prop]
    omega
  let T : Set.powersetCard (Fin n) i := Set.powersetCard.ofCard hcard
  -- The square-layer hypothesis gives square membership for the erased target coordinate.
  have hsq :
      ((Pi.basisFun R (Fin n)).exteriorPower i).repr
        (localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) T ∈
        (maximalIdeal R) ^ 2 := by
    exact ((standardExteriorPower_mem_ideal_smul_top_iff_coords
      (R := R) ((maximalIdeal R) ^ 2) n i
      (localKoszulDifferentialLinearMap
        (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z)).1 hz) T
  have hmem :
      ((Pi.basisFun R (Fin n)).exteriorPower i).repr
        (localKoszulDifferentialLinearMap
          (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) T ∈ maximalIdeal R :=
    localKoszulDifferential_coord_mem_maximalIdeal (R := R) x z T
  have hcot0 :
      (maximalIdeal R).toCotangent
        ⟨((Pi.basisFun R (Fin n)).exteriorPower i).repr
          (localKoszulDifferentialLinearMap
            (localKoszulFamilyLinearMap (fun j ↦ (x j : R))) i z) T, hmem⟩ = 0 := by
    exact (Ideal.toCotangent_eq_zero (maximalIdeal R) _).2 hsq
  have hrepr0 :
      b.repr
        (localKoszulDifferentialCotangentCoord (R := R) x T z) j = 0 := by
    rw [localKoszulDifferentialCotangentCoord_apply]
    rw [hcot0]
    simp
  -- The minimum erased-coordinate formula converts this zero cotangent coordinate into
  -- residue-zero for the original source coordinate.
  have hrepr :=
    localKoszulDifferential_cotangent_min_erase_coord (R := R) b x hx S hnonempty hcard z
  have hreprT :
      b.repr (localKoszulDifferentialCotangentCoord (R := R) x T z) j =
        algebraMap R (ResidueField R)
          (((Pi.basisFun R (Fin n)).exteriorPower (i + 1)).repr z S) := by
    simpa [T, j] using hrepr
  rw [hreprT] at hrepr0
  have hres :
      IsLocalRing.residue R
        (((Pi.basisFun R (Fin n)).exteriorPower (i + 1)).repr z S) = 0 := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using hrepr0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.residue_eq_zero_iff (R := R)
      (((Pi.basisFun R (Fin n)).exteriorPower (i + 1)).repr z S)).mp hres)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the first-order Koszul kernel for a cotangent-basis lift
is contained in the maximal-ideal multiple of the source term. -/
lemma localKoszulDifferential_firstOrder_kernel_of_cotangentBasis
    {n : ℕ}
    (b : Module.Basis (Fin n) (ResidueField R) (CotangentSpace R))
    (x : Fin n → maximalIdeal R)
    (hx : ∀ j, (maximalIdeal R).toCotangent (x j) = b j)
    {i : ℕ} (_hi : i < n)
    {z : (localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X (i + 1)}
    (hz :
      ((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).d (i + 1) i).hom z ∈
        (maximalIdeal R) ^ 2 •
          (⊤ : Submodule R
            ((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X i))) :
    z ∈ maximalIdeal R •
      (⊤ : Submodule R
        ((localKoszulComplexOn (R := R) (fun j ↦ (x j : R))).X (i + 1))) := by
  -- Move from chain-complex notation to the fixed standard exterior-power coordinate model.
  let z' : ⋀[R]^(i + 1) (Fin n → R) := z
  suffices z' ∈ maximalIdeal R •
      (⊤ : Submodule R (⋀[R]^(i + 1) (Fin n → R))) by
    simpa [z'] using this
  rw [standardExteriorPower_mem_ideal_smul_top_iff_coords]
  intro S
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  -- The coordinate lemma turns the square-layer hypothesis on `d_K z` into residue-zero
  -- for each source exterior coordinate.
  apply localKoszulDifferential_firstOrder_coords_eq_zero (R := R) b x hx z'
  simpa [z', localKoszulComplexOn, localKoszulComplex, localKoszulDifferential] using hz

end
