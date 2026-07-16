import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_6.ThompsonCanonicalBaseChange

noncomputable section

open LinearMap (BilinForm)
open scoped Pointwise TensorProduct

universe u v w

open LinearMap.BilinForm

local notation:max p " •ℤ " E => (Representation.primeIdeal p • (⊤ : Submodule ℤ E))

section ThompsonExercise

variable {G : Type u} [Group G]
variable {E : Type v} [AddCommGroup E] [Module ℤ E]

section IntegralLatticeAmbient

variable [Module.Free ℤ E] [Module.Finite ℤ E]

/-- Helper for Exercise 15-15.2-6: in the subsingleton branch, the rational-homothety owner is
automatic because every integral basis is empty. -/
theorem dualIntegralLatticeIsRationalHomothety_of_subsingleton
    [Subsingleton E] (B : BilinForm ℤ E) :
    B.DualIntegralLatticeIsRationalHomothety := by
  -- The determinant-one owner is already handled by the empty-basis argument.
  refine ⟨1, by decide, B, by simp, isSelfDualIntegralLattice_of_subsingleton (E := E) B⟩

/-- Helper for Exercise 15-15.2-6: the coordinate pairing map against a basis is injective for a
symmetric positive-definite form. This isolates the full-rank input needed for the later Smith
normal form step. -/
theorem pairingCoordinateMap_injective
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i)) :
    Function.Injective pairingMap := by
  have hB_nondegenerate : B.Nondegenerate :=
    nondegenerate_of_isSymm_of_posDef B hB_symm hB_pos
  intro x y hxy
  have hbasis :
      ∀ i : Fin n, B (x - y) (b i) = 0 := by
    intro i
    have hi : pairingMap x i = pairingMap y i := by
      simpa using congrArg (fun f : Fin n → ℤ ↦ f i) hxy
    -- Compare the pairing coordinates pointwise on the chosen basis.
    calc
      B (x - y) (b i) = pairingMap (x - y) i := by
        symm
        exact hpairing (x - y) i
      _ = pairingMap x i - pairingMap y i := by
        simp
      _ = 0 := by
        simpa [hi]
  have hsub : x - y = 0 := by
    -- Expand an arbitrary test vector in the basis and use the vanishing basis coordinates.
    apply hB_nondegenerate.left (x - y)
    intro z
    calc
      B (x - y) z = ∑ i, (b.repr z i : ℤ) * B (x - y) (b i) := by
        simpa using basisLinearForm_sum_repr (E := E) b (B (x - y)) z
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        rw [hbasis i, mul_zero]
  exact sub_eq_zero.mp hsub

/-- Helper for Exercise 15-15.2-6: the image of the coordinate pairing map has the same rank as
`E`. This is the finite-rank bridge from positive definiteness to the integral pairing image used
in the globalization step. -/
theorem pairingImage_range_finrank_eq
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) :
    Module.finrank ℤ
        ({ toFun := fun x i ↦ B x (b i)
           map_add' := by
             intro x y
             ext i
             simp
           map_smul' := by
             intro m x
             ext i
             simp } : E →ₗ[ℤ] (Fin n → ℤ)).range =
      Module.finrank ℤ E := by
  let pairingMap : E →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun x i ↦ B x (b i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro m x
        ext i
        simp }
  have hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i) := by
    intro x i
    rfl
  have hpairing_injective : Function.Injective pairingMap := by
    -- Reuse the basiswise nondegeneracy lemma so the rank computation is a pure linear-algebra
    -- consequence.
    exact
      pairingCoordinateMap_injective
        (E := E) (B := B) hB_symm hB_pos b pairingMap hpairing
  -- Full rank of the image is now the standard injective-range formula.
  simpa [pairingMap] using
    (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)

/-- Helper for Exercise 15-15.2-6: against any chosen basis, a symmetric positive-definite form
admits the canonical coordinate pairing map whose image already has full rank. -/
theorem exists_pairingCoordinateMap_range_finrank_eq
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) :
    ∃ pairingMap : E →ₗ[ℤ] (Fin n → ℤ),
      (∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i)) ∧
      Module.finrank ℤ pairingMap.range = Module.finrank ℤ E := by
  let pairingMap : E →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun x i ↦ B x (b i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro m x
        ext i
        simp }
  refine ⟨pairingMap, ?_, ?_⟩
  · -- Record the coordinate formula explicitly so the later Smith-normal-form step can reuse the
    -- same pairing map without rebuilding it.
    intro x i
    rfl
  · -- The full-rank image statement is exactly the packaged injective-range computation above.
    simpa [pairingMap] using
      pairingImage_range_finrank_eq (E := E) (B := B) hB_symm hB_pos b

/-- Helper for Exercise 15-15.2-6: against any chosen basis, the canonical coordinate pairing map
attached to a symmetric positive-definite form is injective. -/
theorem exists_pairingCoordinateMap_injective
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm) (hB_pos : B.toQuadraticMap.PosDef)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E) :
    ∃ pairingMap : E →ₗ[ℤ] (Fin n → ℤ),
      (∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i)) ∧
      Function.Injective pairingMap := by
  let pairingMap : E →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun x i ↦ B x (b i)
      map_add' := by
        intro x y
        ext i
        simp
      map_smul' := by
        intro m x
        ext i
        simp }
  refine ⟨pairingMap, ?_, ?_⟩
  · -- Record the coordinate formula explicitly so later globalization steps can keep one fixed
    -- pairing map instead of rebuilding it.
    intro x i
    rfl
  · -- Positive definiteness makes the basiswise coordinate pairing map injective.
    exact
      pairingCoordinateMap_injective
        (E := E) (B := B) hB_symm hB_pos b pairingMap (fun x i ↦ rfl)

/-- Helper for Exercise 15-15.2-6: Smith-normal-form coordinates send a full-rank submodule of a
free finite `ℤ`-module to the coordinatewise span of its Smith coefficients. -/
theorem smithNormalFormMapEqPiSpanCoeffs
    {ι : Type*} [Finite ι]
    {M : Type*} [AddCommGroup M]
    (N : Submodule ℤ M)
    (b : Module.Basis ι ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    N.map
        (((Submodule.smithNormalFormTopBasis (N := N) b h).equivFun :
            M ≃ₗ[ℤ] (ι → ℤ)).toLinearMap) =
      Submodule.pi Set.univ
        (fun i ↦
          Submodule.span ℤ
            ({Submodule.smithNormalFormCoeffs (N := N) b h i} : Set ℤ)) := by
  letI := Fintype.ofFinite ι
  let a : ι → ℤ := Submodule.smithNormalFormCoeffs (N := N) b h
  let b' : Module.Basis ι ℤ M := Submodule.smithNormalFormTopBasis (N := N) b h
  let ab : Module.Basis ι ℤ N := Submodule.smithNormalFormBotBasis (N := N) b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def (N := N) b h
  have mem_I_iff : ∀ x, x ∈ N ↔ ∀ i, a i ∣ b'.repr x i := by
    intro x
    simp_rw [ab.mem_submodule_iff', ab, ab_eq]
    have hrepr :
        ∀ (c : ι → ℤ) (i), b'.repr (∑ j : ι, c j • a j • b' j) i = a i * c i := by
      intro c i
      simp only [← SemigroupAction.mul_smul, b'.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, hrepr c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, b'.ext_elem fun i => Eq.trans (hc i) (hrepr c i).symm⟩
  let N' : Submodule ℤ (ι → ℤ) :=
    Submodule.pi Set.univ fun i ↦ Submodule.span ℤ ({a i} : Set ℤ)
  have hmap :
      Submodule.map (b'.equivFun : M →ₗ[ℤ] ι → ℤ) N = N' := by
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.1 hx with ⟨y, hy, rfl⟩
      have hy' := (mem_I_iff y).1 hy
      change b'.equivFun y ∈
        Submodule.pi Set.univ fun i ↦ Submodule.span ℤ ({a i} : Set ℤ)
      rw [Submodule.mem_pi]
      intro i _
      rw [Submodule.mem_span_singleton]
      rcases hy' i with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      change c * a i = b'.repr y i
      simpa [mul_comm] using hc.symm
    · intro hx
      have hx' :
          ∀ i, x i ∈ Submodule.span ℤ ({a i} : Set ℤ) := by
        simpa [N', Submodule.mem_pi, Set.mem_univ, forall_true_left] using hx
      refine Submodule.mem_map.2 ?_
      refine ⟨∑ i, x i • b' i, ?_, ?_⟩
      · -- The Smith divisibility criterion reconstructs an element of `N`.
        refine (mem_I_iff _).2 ?_
        intro i
        rw [b'.repr_sum_self]
        rcases Submodule.mem_span_singleton.1 (hx' i) with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        simpa [mul_comm] using hc.symm
      · -- The chosen preimage has the expected Smith coordinates by construction.
        ext i
        change b'.repr (∑ j, x j • b' j) i = x i
        simpa using congrFun (b'.repr_sum_self x) i
  simpa [a, N'] using hmap

/-- Helper for Exercise 15-15.2-6: once the Smith coefficients of a full-rank submodule are
known, the corresponding Smith-coordinate map identifies that submodule with the matching diagonal
lattice. -/
theorem existsCoordinateEquivWithDiagonalOfSmithCoeffs
    {ι : Type*} [Finite ι]
    {M : Type*} [AddCommGroup M]
    (N : Submodule ℤ M)
    (b : Module.Basis ι ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M)
    (d : ι → ℕ)
    (hcoeff :
      ∀ i,
        Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) = d i) :
    ∃ e : M ≃+ (ι → ℤ),
      N.toAddSubgroup.map e.toAddMonoidHom =
        (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)).toAddSubgroup := by
  let eLin : M ≃ₗ[ℤ] (ι → ℤ) :=
    (Submodule.smithNormalFormTopBasis (N := N) b h).equivFun
  refine ⟨eLin.toAddEquiv, ?_⟩
  apply AddSubgroup.toIntSubmodule.injective
  change N.map eLin.toLinearMap =
    Submodule.pi Set.univ fun i ↦ Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)
  have hmap := smithNormalFormMapEqPiSpanCoeffs (N := N) (b := b) (h := h)
  have hspan :
      (fun i ↦
        Submodule.span ℤ
          ({Submodule.smithNormalFormCoeffs (N := N) b h i} : Set ℤ)) =
      (fun i ↦ Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)) := by
    funext i
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨a * Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i), ?_⟩
      have hd : (d i : ℤ) = Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) := by
        exact_mod_cast (hcoeff i).symm
      calc
        (a * Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i)) • (d i : ℤ)
            = (a * Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i)) * (d i : ℤ) := by
                simp
        _ = a *
              (Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i) * (d i : ℤ)) := by
                ring
        _ = a *
              (Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i) *
                Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i)) := by
                rw [hd]
        _ = a * Submodule.smithNormalFormCoeffs (N := N) b h i := by
              rw [Int.sign_mul_natAbs]
        _ = a • Submodule.smithNormalFormCoeffs (N := N) b h i := by
              simp
    · intro hx
      rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨a * Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i), ?_⟩
      have hd : (d i : ℤ) = Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) := by
        exact_mod_cast (hcoeff i).symm
      calc
        (a * Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i)) •
            Submodule.smithNormalFormCoeffs (N := N) b h i
            = (a * Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i)) *
                Submodule.smithNormalFormCoeffs (N := N) b h i := by
                  simp
        _ = a *
              (Int.sign (Submodule.smithNormalFormCoeffs (N := N) b h i) *
                Submodule.smithNormalFormCoeffs (N := N) b h i) := by
                ring
        _ = a * Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) := by
              rw [Int.sign_mul_self_eq_natAbs]
        _ = a * (d i : ℤ) := by
              rw [← hd]
        _ = a • (d i : ℤ) := by
              simp
  simpa [hspan] using hmap

/-- Helper for Exercise 15-15.2-6: if the pairing-image submodule inside `Fin n → ℤ` has constant
Smith-coefficient absolute value, then a coordinate change identifies it with the diagonal lattice
`mℤ^n`. -/
theorem pairingImageExistsCoordinateEquivDiagonal
    {n : ℕ} (N : Submodule ℤ (Fin n → ℤ))
    (hNrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ))
    (m : ℕ)
    (hcoeff :
      ∀ i : Fin n,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) = m) :
    ∃ e : (Fin n → ℤ) ≃+ (Fin n → ℤ),
      N.toAddSubgroup.map e.toAddMonoidHom =
        (Submodule.pi Set.univ
          (fun _ ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))).toAddSubgroup := by
  -- Apply the local Smith-diagonal API at the standard coordinate basis of `Fin n → ℤ`.
  simpa using
    existsCoordinateEquivWithDiagonalOfSmithCoeffs
      (N := N)
      (b := Pi.basisFun ℤ (Fin n))
      (h := hNrank)
      (d := fun _ : Fin n ↦ m)
      hcoeff

/-- Helper for Exercise 15-15.2-6: additive automorphisms of `Fin n → ℤ` preserve the
coordinatewise lattice of multiples of `m`. -/
theorem diagonalPiSubmodule_map_eq_self
    {n : ℕ} (e : (Fin n → ℤ) ≃+ (Fin n → ℤ)) (m : ℕ) :
    (Submodule.pi Set.univ
        (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))).map
        e.toIntLinearEquiv.toLinearMap =
      Submodule.pi Set.univ
        (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ)) := by
  let M : Submodule ℤ (Fin n → ℤ) :=
    Submodule.pi Set.univ
      (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))
  apply le_antisymm
  · intro x hx
    rcases Submodule.mem_map.1 hx with ⟨y, hy, rfl⟩
    rw [Submodule.mem_pi] at hy ⊢
    let c : Fin n → ℤ := fun i ↦
      Classical.choose (Submodule.mem_span_singleton.mp (hy i (by simp)))
    have hc : y = (m : ℤ) • c := by
      ext i
      have hi := Classical.choose_spec (Submodule.mem_span_singleton.mp (hy i (by simp)))
      simpa [c, smul_eq_mul, mul_comm] using hi.symm
    intro i hi
    rw [Submodule.mem_span_singleton]
    refine ⟨(e c) i, ?_⟩
    calc
      ((e c) i : ℤ) • (m : ℤ) = (((m : ℤ) • e c) i) := by
            simp [smul_eq_mul, mul_comm]
      _ = e ((m : ℤ) • c) i := by
            -- The additive equivalence commutes with integer scalar multiplication.
            symm
            simpa using congrFun (map_zsmul e (m : ℤ) c) i
      _ = e y i := by simpa [hc]
  · intro x hx
    refine Submodule.mem_map.2 ?_
    refine ⟨e.symm x, ?_, ?_⟩
    · rw [Submodule.mem_pi] at hx ⊢
      let c : Fin n → ℤ := fun i ↦
        Classical.choose (Submodule.mem_span_singleton.mp (hx i (by simp)))
      have hc : x = (m : ℤ) • c := by
        ext i
        have hi := Classical.choose_spec (Submodule.mem_span_singleton.mp (hx i (by simp)))
        simpa [c, smul_eq_mul, mul_comm] using hi.symm
      intro i hi
      rw [Submodule.mem_span_singleton]
      refine ⟨(e.symm c) i, ?_⟩
      calc
        ((e.symm c) i : ℤ) • (m : ℤ) = (((m : ℤ) • e.symm c) i) := by
              simp [smul_eq_mul, mul_comm]
        _ = e.symm ((m : ℤ) • c) i := by
              -- The inverse additive equivalence has the same `ℤ`-linearity.
              symm
              simpa using congrFun (map_zsmul e.symm (m : ℤ) c) i
        _ = e.symm x i := by simpa [hc]
    · simp

/-- Helper for Exercise 15-15.2-6: if the pairing image has constant Smith-coefficient absolute
value `m`, then its Smith-diagonal identification collapses to the literal coordinatewise lattice
`mℤ^n` in the original coordinates. -/
theorem pairingImage_eq_diagonal_of_constantSmithCoeffs
    {n : ℕ} (N : Submodule ℤ (Fin n → ℤ))
    (hNrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ))
    (m : ℕ)
    (hcoeff :
      ∀ i : Fin n,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) = m) :
    N =
      Submodule.pi Set.univ
        (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ)) := by
  obtain ⟨e, he⟩ := pairingImageExistsCoordinateEquivDiagonal N hNrank m hcoeff
  let M : Submodule ℤ (Fin n → ℤ) :=
    Submodule.pi Set.univ
      (fun _ : Fin n ↦ Submodule.span ℤ ({(m : ℤ)} : Set ℤ))
  have hmap : N.map e.toIntLinearEquiv.toLinearMap = M := by
    simpa [M] using congrArg AddSubgroup.toIntSubmodule he
  have hMmap :
      M.map e.toIntLinearEquiv.toLinearMap = M := by
    simpa [M] using diagonalPiSubmodule_map_eq_self (e := e) m
  apply le_antisymm
  · intro x hx
    have hex : e x ∈ M := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    have hxmap : x ∈ M.map e.symm.toIntLinearEquiv.toLinearMap := by
      refine Submodule.mem_map.2 ?_
      refine ⟨e x, hex, ?_⟩
      simp
    have hMsymm :
        M.map e.symm.toIntLinearEquiv.toLinearMap = M := by
      simpa [M] using diagonalPiSubmodule_map_eq_self (e := e.symm) m
    rw [hMsymm] at hxmap
    exact hxmap
  · intro x hx
    have hex : e x ∈ M := by
      rw [← hMmap]
      exact Submodule.mem_map_of_mem hx
    rw [← hmap] at hex
    rcases Submodule.mem_map.1 hex with ⟨y, hy, hyx⟩
    exact e.toIntLinearEquiv.injective hyx ▸ hy

/-- Helper for Exercise 15-15.2-6: once the primewise valuations of the absolute values of the
Smith coefficients agree, those absolute values globalize to one positive integer. -/
theorem pairingImageSmithCoeffs_constantNatAbs
    {n : ℕ} (N : Submodule ℤ (Fin n → ℤ))
    (hNrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ))
    (hpadic :
      ∀ (p : ℕ) [Fact p.Prime] (i j : Fin n),
        padicValNat p
            (Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i)) =
          padicValNat p
            (Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := N) (Pi.basisFun ℤ (Fin n)) hNrank j))) :
    ∃ m : ℕ, 0 < m ∧
      ∀ i : Fin n,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) = m := by
  let coeff : Fin n → ℕ := fun i ↦
    Int.natAbs
      (Submodule.smithNormalFormCoeffs
        (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i)
  by_cases hnonempty : Nonempty (Fin n)
  · obtain ⟨i₀⟩ := hnonempty
    let m := coeff i₀
    have hm_pos : 0 < m := by
      -- Any chosen Smith coefficient is nonzero, so its absolute value is positive.
      refine Nat.pos_of_ne_zero ?_
      exact
        Int.natAbs_ne_zero.mpr
          (Submodule.smithNormalFormCoeffs_ne_zero
            (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i₀)
    refine ⟨m, hm_pos, ?_⟩
    intro i
    -- Equality of all prime factorizations upgrades the primewise valuation data to equality.
    apply Nat.eq_of_factorization_eq
    · exact
        Int.natAbs_ne_zero.mpr
          (Submodule.smithNormalFormCoeffs_ne_zero
            (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i)
    · exact Nat.ne_of_gt hm_pos
    · intro p
      by_cases hp : p.Prime
      · letI : Fact p.Prime := ⟨hp⟩
        -- On prime indices, `factorization` is exactly `padicValNat`.
        rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
        simpa [coeff, m] using hpadic p i i₀
      · -- On nonprime indices, both factorizations vanish by definition.
        simp [Nat.factorization, hp, coeff, m]
  · refine ⟨1, Nat.succ_pos _, ?_⟩
    intro i
    exact (hnonempty ⟨i⟩).elim

/-- Helper for Exercise 15-15.2-6: the quotient by a full-rank submodule of `Fin n → ℤ` has
cardinality equal to the product of the absolute values of its Smith coefficients. -/
theorem quotientCard_eq_prod_smithCoeffs
    {n : ℕ} (N : Submodule ℤ (Fin n → ℤ))
    (hNrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ)) :
    Nat.card ((Fin n → ℤ) ⧸ N) =
      ∏ i : Fin n,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) := by
  have hcard :
      Nat.card ((Fin n → ℤ) ⧸ N) =
        Nat.card
          (∀ i : Fin n,
            ZMod
              (Int.natAbs
                (Submodule.smithNormalFormCoeffs
                  (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i))) := by
    -- Smith normal form identifies the finite quotient with the product of cyclic quotients.
    exact
      Nat.card_congr
        (Submodule.quotientEquivPiZMod N (Pi.basisFun ℤ (Fin n)) hNrank).toEquiv
  calc
    Nat.card ((Fin n → ℤ) ⧸ N) =
        Nat.card
          (∀ i : Fin n,
            ZMod
              (Int.natAbs
                (Submodule.smithNormalFormCoeffs
                  (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i))) := hcard
    _ =
        ∏ i : Fin n,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) := by
          simpa using
            (Nat.card_pi (β := fun i : Fin n ↦
              ZMod
                (Int.natAbs
                  (Submodule.smithNormalFormCoeffs
                    (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i))))

/-- Helper for Exercise 15-15.2-6: if all Smith coefficients of a full-rank submodule of
`Fin n → ℤ` have the same absolute value `m`, then the quotient has cardinality `m ^ n`. -/
theorem quotientCard_eq_pow_of_constantSmithCoeffs
    {n : ℕ} (N : Submodule ℤ (Fin n → ℤ))
    (hNrank : Module.finrank ℤ N = Module.finrank ℤ (Fin n → ℤ))
    (m : ℕ)
    (hcoeff :
      ∀ i : Fin n,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) = m) :
    Nat.card ((Fin n → ℤ) ⧸ N) = m ^ n := by
  -- With constant Smith coefficients, the product cardinality is exactly `m ^ n`.
  calc
    Nat.card ((Fin n → ℤ) ⧸ N) =
        ∏ i : Fin n,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := N) (Pi.basisFun ℤ (Fin n)) hNrank i) :=
          quotientCard_eq_prod_smithCoeffs N hNrank
    _ = ∏ _i : Fin n, m := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact hcoeff i
    _ = m ^ n := by
          simp

/-- Helper for Exercise 15-15.2-6: the `p`-adic valuation of a finite product is the sum of the
`p`-adic valuations, in the nonzero range where Smith coefficients live. -/
theorem padicValNat_finset_prod
    {α : Type*} (s : Finset α) (f : α → ℕ)
    (p : ℕ) (hp : p.Prime)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    padicValNat p (∏ a ∈ s, f a) =
      ∑ a ∈ s, padicValNat p (f a) := by
  -- Convert the computation to prime factorizations, where products become sums.
  rw [← Nat.factorization_def _ hp]
  rw [Nat.factorization_prod_apply]
  · simp_rw [Nat.factorization_def _ hp]
  · intro a ha
    exact hf a ha

/-- Helper for Exercise 15-15.2-6: the `p`-adic valuation of a product over a finite type is the
sum of the `p`-adic valuations of its nonzero factors. -/
theorem padicValNat_univ_prod
    {α : Type*} [Fintype α] (f : α → ℕ)
    (p : ℕ) (hp : p.Prime)
    (hf : ∀ a, f a ≠ 0) :
    padicValNat p (∏ a, f a) =
      ∑ a, padicValNat p (f a) := by
  -- Specialize the finite-product formula to `Finset.univ`.
  simpa using
    padicValNat_finset_prod (s := Finset.univ) f p hp
      (by
        intro a _ha
        exact hf a)

/-- Helper for Exercise 15-15.2-6: constant Smith coefficients force the absolute value of the
Gram determinant to be `m ^ n`. This packages the quotient-cardinality endgame of part `(b)` once
the fixed-range valuation bridge has identified one common Smith coefficient. -/
theorem pairingMatrix_natAbs_det_eq_prod_smithCoeffs
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap) :
    Int.natAbs (Matrix.det (B.toMatrix b)) =
      ∏ i : Fin n,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n))
            (by
              simpa [Module.finrank_eq_card_basis b] using
                (LinearMap.finrank_range_of_inj
                  (R := ℤ) (f := pairingMap) hpairing_injective)) i) := by
  let hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ) := by
    -- Injectivity of the coordinate pairing map gives the full-rank hypothesis for its image.
    simpa [Module.finrank_eq_card_basis b] using
      (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)
  have hquot :
      Nat.card ((Fin n → ℤ) ⧸ pairingMap.range) =
        ∏ i : Fin n,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i) :=
    quotientCard_eq_prod_smithCoeffs pairingMap.range hNrank
  let eRange : (Fin n → ℤ) ≃ₗ[ℤ] pairingMap.range :=
    b.equivFun.symm.trans (LinearEquiv.ofInjective pairingMap hpairing_injective)
  have hdetEquiv :
      Int.natAbs
          (LinearMap.det
            (pairingMap.range.subtype ∘ₗ eRange.toLinearMap)) =
        Nat.card ((Fin n → ℤ) ⧸ pairingMap.range) :=
    Submodule.natAbs_det_equiv pairingMap.range eRange
  have hmap :
      pairingMap.range.subtype ∘ₗ eRange.toLinearMap =
        pairingMap ∘ₗ b.equivFun.symm.toLinearMap := by
    -- The chosen equivalence identifies the ambient coordinates with the range coordinates.
    ext x i
    rfl
  rw [hmap] at hdetEquiv
  have hmatrix :
      LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
          (pairingMap ∘ₗ b.equivFun.symm.toLinearMap) =
        Matrix.transpose (B.toMatrix b) := by
    ext i j
    -- On standard basis vectors, the coordinate pairing map records the Gram matrix entries.
    simp [LinearMap.toMatrix_apply, hpairing, hB_symm.eq]
  have hdetMap :
      Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) =
        ∏ i : Fin n,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i) := by
    calc
      Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) =
          Nat.card ((Fin n → ℤ) ⧸ pairingMap.range) := by
            simpa using hdetEquiv
      _ =
          ∏ i : Fin n,
            Int.natAbs
              (Submodule.smithNormalFormCoeffs
                (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i) := hquot
  have hdetToMatrix :
      Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) =
        Int.natAbs
          (Matrix.det
            (LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
              (pairingMap ∘ₗ b.equivFun.symm.toLinearMap))) := by
    rw [LinearMap.det_toMatrix]
  calc
    Int.natAbs (Matrix.det (B.toMatrix b)) =
        Int.natAbs (Matrix.det (Matrix.transpose (B.toMatrix b))) := by
          rw [Matrix.det_transpose]
    _ =
        Int.natAbs
          (Matrix.det
            (LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
              (pairingMap ∘ₗ b.equivFun.symm.toLinearMap))) := by
          rw [hmatrix]
    _ = Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) := by
          rw [hdetToMatrix]
    _ =
        ∏ i : Fin n,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i) := hdetMap

/-- Helper for Exercise 15-15.2-6: at a fixed prime, the valuation of the Gram determinant is the
sum of the valuations of the Smith coefficients of the pairing image. This is the numerical
invariant extracted from the Smith quotient computation before the prime-local rigidity step. -/
theorem pairingMatrix_padicValNat_det_eq_sum_smithCoeffPadicVal
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (p : ℕ) [Fact p.Prime] :
    padicValNat p (Int.natAbs (Matrix.det (B.toMatrix b))) =
      ∑ i : Fin n,
        padicValNat p
          (Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n))
              (by
                simpa [Module.finrank_eq_card_basis b] using
                  (LinearMap.finrank_range_of_inj
                    (R := ℤ) (f := pairingMap) hpairing_injective)) i)) := by
  let hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ) := by
    -- Freeze the full-rank hypothesis so the product formula and nonzero Smith coefficients
    -- use the same owner.
    simpa [Module.finrank_eq_card_basis b] using
      (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)
  have hprod :
      Int.natAbs (Matrix.det (B.toMatrix b)) =
        ∏ i : Fin n,
          Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i) :=
    pairingMatrix_natAbs_det_eq_prod_smithCoeffs
      (B := B) hB_symm (b := b) pairingMap hpairing hpairing_injective
  rw [hprod]
  -- The remaining step is the standard valuation-of-product formula; Smith coefficients are
  -- nonzero by full rank.
  exact
    padicValNat_univ_prod
      (fun i : Fin n ↦
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i))
      p Fact.out
      (by
        intro i
        exact
          Int.natAbs_ne_zero.mpr
            (Submodule.smithNormalFormCoeffs_ne_zero
              (N := pairingMap.range) (Pi.basisFun ℤ (Fin n)) hNrank i))

/-- Helper for Exercise 15-15.2-6: constant Smith coefficients force the absolute value of the
Gram determinant to be `m ^ n`. This packages the quotient-cardinality endgame of part `(b)` once
the fixed-range valuation bridge has identified one common Smith coefficient. -/
theorem pairingMatrix_natAbs_det_eq_pow_of_constantSmithCoeffs
    (B : BilinForm ℤ E) (hB_symm : B.IsSymm)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ E)
    (pairingMap : E →ₗ[ℤ] (Fin n → ℤ))
    (hpairing : ∀ x : E, ∀ i : Fin n, pairingMap x i = B x (b i))
    (hpairing_injective : Function.Injective pairingMap)
    (m : ℕ)
    (hcoeff :
      ∀ i : Fin n,
        Int.natAbs
          (Submodule.smithNormalFormCoeffs
            (N := pairingMap.range) (Pi.basisFun ℤ (Fin n))
            (by
              simpa [Module.finrank_eq_card_basis b] using
                (LinearMap.finrank_range_of_inj
                  (R := ℤ) (f := pairingMap) hpairing_injective)) i) = m) :
    Int.natAbs (Matrix.det (B.toMatrix b)) = m ^ n := by
  let hNrank : Module.finrank ℤ pairingMap.range = Module.finrank ℤ (Fin n → ℤ) := by
    -- Injectivity of the coordinate pairing map gives the full-rank hypothesis for its image.
    simpa [Module.finrank_eq_card_basis b] using
      (LinearMap.finrank_range_of_inj (R := ℤ) (f := pairingMap) hpairing_injective)
  have hquot : Nat.card ((Fin n → ℤ) ⧸ pairingMap.range) = m ^ n := by
    -- The Smith-normal-form package turns the constant coefficient hypothesis into a quotient
    -- cardinality computation.
    exact quotientCard_eq_pow_of_constantSmithCoeffs pairingMap.range hNrank m hcoeff
  let eRange : (Fin n → ℤ) ≃ₗ[ℤ] pairingMap.range :=
    b.equivFun.symm.trans (LinearEquiv.ofInjective pairingMap hpairing_injective)
  have hdetEquiv :
      Int.natAbs
          (LinearMap.det
            (pairingMap.range.subtype ∘ₗ eRange.toLinearMap)) =
        Nat.card ((Fin n → ℤ) ⧸ pairingMap.range) :=
    Submodule.natAbs_det_equiv pairingMap.range eRange
  have hmap :
      pairingMap.range.subtype ∘ₗ eRange.toLinearMap =
        pairingMap ∘ₗ b.equivFun.symm.toLinearMap := by
    -- The chosen equivalence identifies the ambient coordinates with the range coordinates.
    ext x i
    rfl
  rw [hmap] at hdetEquiv
  have hmatrix :
      LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
          (pairingMap ∘ₗ b.equivFun.symm.toLinearMap) =
        Matrix.transpose (B.toMatrix b) := by
    ext i j
    -- On standard basis vectors, the coordinate pairing map records the Gram matrix entries.
    simp [LinearMap.toMatrix_apply, hpairing, hB_symm.eq]
  have hdetMap :
      Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) = m ^ n := by
    calc
      Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) =
          Nat.card ((Fin n → ℤ) ⧸ pairingMap.range) := by
            simpa using hdetEquiv
      _ = m ^ n := hquot
  -- Rewrite the determinant of the coordinate pairing map back to the Gram determinant.
  have hdetToMatrix :
      Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) =
        Int.natAbs
          (Matrix.det
            (LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
              (pairingMap ∘ₗ b.equivFun.symm.toLinearMap))) := by
    rw [LinearMap.det_toMatrix]
  calc
    Int.natAbs (Matrix.det (B.toMatrix b)) =
        Int.natAbs (Matrix.det (Matrix.transpose (B.toMatrix b))) := by
          rw [Matrix.det_transpose]
    _ =
        Int.natAbs
          (Matrix.det
            (LinearMap.toMatrix (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℤ (Fin n))
              (pairingMap ∘ₗ b.equivFun.symm.toLinearMap))) := by
          rw [hmatrix]
    _ = Int.natAbs (LinearMap.det (pairingMap ∘ₗ b.equivFun.symm.toLinearMap)) := by
          rw [hdetToMatrix]
    _ = m ^ n := hdetMap


end IntegralLatticeAmbient

end ThompsonExercise
