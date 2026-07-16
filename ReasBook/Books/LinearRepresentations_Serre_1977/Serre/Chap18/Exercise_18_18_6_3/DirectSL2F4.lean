import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5

open scoped MatrixGroups LinearAlgebra.Projectivization

noncomputable section

open CategoryTheory
open Representation

local notation "A5" => alternatingGroup (Fin 5)
local notation "𝔽₄" => FiniteField.Extension (ZMod 2) 2 2
local notation "V2" => (Fin 2 → 𝔽₄)
local notation "P1" => Projectivization 𝔽₄ V2

/-- Helper for Exercise 18-18.6-3: the chosen model of `𝔽₄` has four elements. -/
private theorem finite_field_f4_card_eq_four :
    Nat.card 𝔽₄ = 4 := by
  -- The cardinality is the generic finite-field extension formula at degree `2` over `𝔽₂`.
  simpa using (FiniteField.natCard_extension (k := ZMod 2) (p := 2) (n := 2))

/-- Helper for Exercise 18-18.6-3: the field `𝔽₄` has characteristic `2`. -/
private theorem f4_two_eq_zero : (2 : 𝔽₄) = 0 := by
  -- Push the numeral through the structure map from `ZMod 2`.
  calc
    (2 : 𝔽₄) = algebraMap (ZMod 2) 𝔽₄ (2 : ZMod 2) :=
      (map_natCast (algebraMap (ZMod 2) 𝔽₄) 2).symm
    _ = algebraMap (ZMod 2) 𝔽₄ 0 := by
      have h : (2 : ZMod 2) = 0 := by decide
      rw [h]
    _ = 0 := map_zero _

/-- Helper for Exercise 18-18.6-3: in `𝔽₄`, `-1 = 1`. -/
private theorem f4_neg_one_eq_one : (-1 : 𝔽₄) = 1 := by
  -- Characteristic `2` turns the difference `-1 - 1` into zero.
  rw [← sub_eq_zero]
  calc
    (-1 : 𝔽₄) - 1 = -(2 : 𝔽₄) := by ring
    _ = 0 := by rw [f4_two_eq_zero, neg_zero]

/-- Helper for Exercise 18-18.6-3: the only square root of `1` in `𝔽₄` is `1`. -/
private theorem f4_sq_eq_one_iff_eq_one {a : 𝔽₄} (ha : a ^ 2 = 1) :
    a = 1 := by
  -- In a field, `a² = 1` gives `a = ±1`; characteristic `2` identifies the two signs.
  rcases mul_self_eq_one_iff.mp (by simpa [pow_two] using ha) with h | h
  · exact h
  · rw [h, f4_neg_one_eq_one]

/-- Helper for Exercise 18-18.6-3: the matrix special linear group `SL(2, 𝔽₄)` has order `60`. -/
private theorem specialLinearGroup_fin_two_f4_card_eq_sixty :
    Nat.card (SL(2, 𝔽₄)) = 60 := by
  letI : Fintype 𝔽₄ := Fintype.ofFinite 𝔽₄
  letI : DecidableEq 𝔽₄ := Classical.decEq 𝔽₄
  let detHom : GL (Fin 2) 𝔽₄ →* 𝔽₄ˣ := Matrix.GeneralLinearGroup.det
  have hcard_gl : Nat.card (GL (Fin 2) 𝔽₄) = 180 := by
    -- Compute `|GL(2, 𝔽₄)|` by the standard product formula.
    calc
      Nat.card (GL (Fin 2) 𝔽₄)
          = ∏ i : Fin 2, (Fintype.card 𝔽₄ ^ 2 - Fintype.card 𝔽₄ ^ (i : ℕ)) := by
            simpa using Matrix.card_GL_field (𝔽 := 𝔽₄) 2
      _ = ∏ i : Fin 2, (4 ^ 2 - 4 ^ (i : ℕ)) := by
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [← Nat.card_eq_fintype_card, finite_field_f4_card_eq_four]
      _ = 180 := by decide
  have hdet_surj : Function.Surjective detHom := by
    -- Diagonal matrices `diag(u, 1)` realize every unit as a determinant.
    intro u
    refine ⟨Matrix.GeneralLinearGroup.mk'' !![(u : 𝔽₄), 0; 0, 1] ?_, ?_⟩
    · refine ⟨u, ?_⟩
      simp
    · apply Units.ext
      simp [detHom, Matrix.det_fin_two]
  have hcard_range : Nat.card detHom.range = 3 := by
    -- The determinant range is all of `𝔽₄ˣ`, which has three elements.
    rw [MonoidHom.range_eq_top.2 hdet_surj]
    calc
      Nat.card ((⊤ : Subgroup 𝔽₄ˣ)) = Nat.card (𝔽₄ˣ) := by
        exact Nat.card_congr Subgroup.topEquiv.toEquiv
      _ = 3 := by
        rw [Nat.card_units, finite_field_f4_card_eq_four]
  have hcard_ker : Nat.card detHom.ker = Nat.card (SL(2, 𝔽₄)) := by
    -- Identify `SL₂` with the kernel of determinant on `GL₂`.
    let e : detHom.ker ≃ SL(2, 𝔽₄) :=
      { toFun := fun g ↦
          ⟨(g.1 : Matrix (Fin 2) (Fin 2) 𝔽₄), by
            simpa [detHom] using congrArg Units.val g.2⟩
        invFun := fun g ↦
          ⟨(g : GL (Fin 2) 𝔽₄), by
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
      Nat.card detHom.ker * Nat.card detHom.range = Nat.card (GL (Fin 2) 𝔽₄) := by
    -- The kernel-index formula computes the kernel order after the determinant range is known.
    calc
      Nat.card detHom.ker * Nat.card detHom.range
          = Nat.card detHom.ker * detHom.ker.index := by
              rw [Subgroup.index_ker]
      _ = Nat.card (GL (Fin 2) 𝔽₄) := detHom.ker.card_mul_index
  have hcard_kernel_sixty : Nat.card detHom.ker = 60 := by
    -- Divide `|GL₂(𝔽₄)| = 180` by `|𝔽₄ˣ| = 3`.
    have hker_eq : Nat.card detHom.ker * 3 = 180 := by
      rw [← hcard_range, hker_mul_range, hcard_gl]
    omega
  rw [← hcard_ker]
  exact hcard_kernel_sixty

/-- Helper for Exercise 18-18.6-3: the linear special linear group on `𝔽₄²` has order `60`. -/
private theorem specialLinearGroup_linear_f4_card_eq_sixty :
    Nat.card (SpecialLinearGroup 𝔽₄ V2) = 60 := by
  -- Transport the cardinality across the standard matrix/linear `SL₂` equivalence.
  calc
    Nat.card (SpecialLinearGroup 𝔽₄ V2) = Nat.card (SL(2, 𝔽₄)) := by
      exact Nat.card_congr
        (Matrix.SpecialLinearGroup.toLin'_equiv (R := 𝔽₄) (n := Fin 2)).symm.toEquiv
    _ = 60 := specialLinearGroup_fin_two_f4_card_eq_sixty

/-- Helper for Exercise 18-18.6-3: the projective line over `𝔽₄` has five points. -/
private theorem projectiveLine_f4_card_eq_five :
    Nat.card P1 = 5 := by
  -- A two-dimensional projective line over a finite field has `q + 1` points.
  have h := Projectivization.card_of_finrank_two
    (k := 𝔽₄) (V := V2) (by simp)
  rw [finite_field_f4_card_eq_four] at h
  omega

/-- Helper for Exercise 18-18.6-3: the permutation group of the projective line has order `120`. -/
private theorem perm_projectiveLine_f4_card_eq_one_twenty :
    Nat.card (Equiv.Perm P1) = 120 := by
  letI : Fintype P1 := Fintype.ofFinite P1
  letI : DecidableEq P1 := Classical.decEq P1
  have hP : Fintype.card P1 = 5 := by
    -- Convert the `Nat.card` computation to the local `Fintype.card`.
    rw [← Nat.card_eq_fintype_card]
    exact projectiveLine_f4_card_eq_five
  calc
    Nat.card (Equiv.Perm P1) = Fintype.card (Equiv.Perm P1) := by
      rw [Nat.card_eq_fintype_card]
    _ = (Fintype.card P1).factorial := Fintype.card_perm
    _ = 120 := by rw [hP]; decide

/-- Helper for Exercise 18-18.6-3: a projectively fixed nonzero vector is an eigenvector. -/
private theorem projective_fixed_line_scalar {g : SpecialLinearGroup 𝔽₄ V2}
    (hg : MulAction.toPermHom (SpecialLinearGroup 𝔽₄ V2) P1 g = 1)
    {v : V2} (hv : v ≠ 0) :
    ∃ a : 𝔽₄, a • v = (g : V2 →ₗ[𝔽₄] V2) v := by
  -- Read triviality of the projective permutation on the line spanned by `v`.
  have hfix : g • Projectivization.mk 𝔽₄ v hv = Projectivization.mk 𝔽₄ v hv := by
    have hperm := congrArg
      (fun f : Equiv.Perm P1 => f (Projectivization.mk 𝔽₄ v hv)) hg
    simpa using hperm
  have hmk : Projectivization.mk 𝔽₄ ((g : SpecialLinearGroup 𝔽₄ V2) • v)
      ((smul_ne_zero_iff_ne g).mpr hv) = Projectivization.mk 𝔽₄ v hv := by
    simpa [Projectivization.smul_mk] using hfix
  -- Equality of projective points is exactly equality up to a scalar.
  simpa [SpecialLinearGroup.smul_def] using
    (Projectivization.mk_eq_mk_iff' 𝔽₄ ((g : V2 →ₗ[𝔽₄] V2) v) v
      ((smul_ne_zero_iff_ne g).mpr hv) hv).1 hmk

/-- Helper for Exercise 18-18.6-3: the projective action of `SL(2, 𝔽₄)` has trivial kernel. -/
private theorem specialLinear_projectiveAction_eq_one_of_eq_one
    {g : SpecialLinearGroup 𝔽₄ V2}
    (hg : MulAction.toPermHom (SpecialLinearGroup 𝔽₄ V2) P1 g = 1) :
    g = 1 := by
  let e0 : V2 := Pi.single 0 1
  let e1 : V2 := Pi.single 1 1
  have he0 : e0 ≠ 0 := by
    intro h
    have : (1 : 𝔽₄) = 0 := by simpa [e0] using congrFun h 0
    exact one_ne_zero this
  have he1 : e1 ≠ 0 := by
    intro h
    have : (1 : 𝔽₄) = 0 := by simpa [e1] using congrFun h 1
    exact one_ne_zero this
  have he01 : e0 + e1 ≠ 0 := by
    intro h
    have : (1 : 𝔽₄) = 0 := by simpa [e0, e1] using congrFun h 0
    exact one_ne_zero this
  -- The three projectively fixed lines force the two coordinate eigenvalues to agree.
  rcases projective_fixed_line_scalar (g := g) hg he0 with ⟨a, ha⟩
  rcases projective_fixed_line_scalar (g := g) hg he1 with ⟨b, hb⟩
  rcases projective_fixed_line_scalar (g := g) hg he01 with ⟨c, hc⟩
  have hg_e0 : (g : V2 →ₗ[𝔽₄] V2) e0 = a • e0 := ha.symm
  have hg_e1 : (g : V2 →ₗ[𝔽₄] V2) e1 = b • e1 := hb.symm
  have hg_sum : (g : V2 →ₗ[𝔽₄] V2) (e0 + e1) = c • (e0 + e1) := hc.symm
  have hac : a = c := by
    -- Compare the first coordinate of the image of `e₀ + e₁`.
    simpa [map_add, hg_e0, hg_e1, e0, e1] using congrFun hg_sum 0
  have hbc : b = c := by
    -- Compare the second coordinate of the image of `e₀ + e₁`.
    simpa [map_add, hg_e0, hg_e1, e0, e1] using congrFun hg_sum 1
  have hvdecomp : ∀ v : V2, v = v 0 • e0 + v 1 • e1 := by
    intro v
    ext i
    · fin_cases i <;> simp [e0, e1]
  have hscalar : ∀ v : V2, (g : V2 →ₗ[𝔽₄] V2) v = c • v := by
    intro v
    rw [hvdecomp v]
    ext i
    · fin_cases i
      · simp [map_add, hg_e0, hg_e1, hac, hbc, e0, e1, mul_comm]
      · simp [map_add, hg_e0, hg_e1, hac, hbc, e0, e1, mul_comm]
  have hlin : (g : V2 →ₗ[𝔽₄] V2) = c • (1 : V2 →ₗ[𝔽₄] V2) := by
    apply LinearMap.ext
    intro v
    exact hscalar v
  have hdet_one : LinearMap.det (g : V2 →ₗ[𝔽₄] V2) = 1 := by
    -- The defining special-linear determinant gives determinant `1` on the underlying map.
    calc
      LinearMap.det (g : V2 →ₗ[𝔽₄] V2)
          = ↑(LinearEquiv.det (g : V2 ≃ₗ[𝔽₄] V2)) :=
            (LinearEquiv.coe_det (g : V2 ≃ₗ[𝔽₄] V2)).symm
      _ = 1 := by rw [SpecialLinearGroup.det_coe]; rfl
  have hdet_scalar : LinearMap.det (g : V2 →ₗ[𝔽₄] V2) = c ^ 2 := by
    -- The determinant of a scalar map on a two-dimensional space is the square of the scalar.
    rw [hlin, LinearMap.det_smul]
    simp
  have hc_sq : c ^ 2 = 1 := by
    rw [← hdet_scalar]
    exact hdet_one
  have hc1 : c = 1 := f4_sq_eq_one_iff_eq_one hc_sq
  -- The scalar is `1`, so the special-linear element is the identity.
  apply SpecialLinearGroup.ext
  intro v
  simpa [hc1] using hscalar v

/-- Helper for Exercise 18-18.6-3: `SL(2, 𝔽₄)` embeds in permutations of `ℙ¹(𝔽₄)`. -/
private theorem specialLinear_projectiveAction_injective :
    Function.Injective (MulAction.toPermHom (SpecialLinearGroup 𝔽₄ V2) P1) := by
  -- The kernel computation above is exactly injectivity of the permutation action.
  rw [← MonoidHom.ker_eq_bot_iff]
  ext g
  constructor
  · intro hg
    have hg_one : g = 1 := specialLinear_projectiveAction_eq_one_of_eq_one
      (by simpa [MonoidHom.mem_ker] using hg)
    simp [hg_one]
  · intro hg
    have hg_one : g = 1 := by simpa using hg
    simp [hg_one]

/-- Helper for Exercise 18-18.6-3: the projective action identifies `SL₂(𝔽₄)` with the
alternating group of the five-point projective line. -/
private theorem specialLinear_f4_mulEquiv_alternating_projectiveLine
    [Fintype P1] [DecidableEq P1] :
    Nonempty (SpecialLinearGroup 𝔽₄ V2 ≃* alternatingGroup P1) := by
  let φ : SpecialLinearGroup 𝔽₄ V2 →* Equiv.Perm P1 :=
    MulAction.toPermHom (SpecialLinearGroup 𝔽₄ V2) P1
  have hφ : Function.Injective φ := specialLinear_projectiveAction_injective
  have hcard_range : Nat.card φ.range = 60 := by
    -- The range has the same order as `SL₂(𝔽₄)` because the projective action is injective.
    calc
      Nat.card φ.range = Nat.card (SpecialLinearGroup 𝔽₄ V2) := by
        exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
      _ = 60 := specialLinearGroup_linear_f4_card_eq_sixty
  have hindex : φ.range.index = 2 := by
    -- Inside the permutation group on five points, a subgroup of order `60` has index `2`.
    have h := φ.range.index_mul_card
    rw [hcard_range, perm_projectiveLine_f4_card_eq_one_twenty] at h
    omega
  have hrange : φ.range = alternatingGroup P1 :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)⟩

/-- Helper for Exercise 18-18.6-3: the exceptional isomorphism `A₅ ≃ SL(2, 𝔽₄)` from the
projective action on `ℙ¹(𝔽₄)`. -/
theorem alternatingGroup_fin5_mulEquiv_sl2_f4_direct :
    Nonempty (A5 ≃* SL(2, 𝔽₄)) := by
  letI : Fintype P1 := Fintype.ofFinite P1
  letI : DecidableEq P1 := Classical.decEq P1
  have hP : Fintype.card P1 = 5 := by
    -- Choose an arbitrary numbering of the five projective points.
    rw [← Nat.card_eq_fintype_card]
    exact projectiveLine_f4_card_eq_five
  let eP : P1 ≃ Fin 5 := Fintype.equivFinOfCardEq hP
  rcases specialLinear_f4_mulEquiv_alternating_projectiveLine with ⟨eSLAlt⟩
  let eMatSL : SL(2, 𝔽₄) ≃* SpecialLinearGroup 𝔽₄ V2 :=
    Matrix.SpecialLinearGroup.toLin'_equiv (R := 𝔽₄) (n := Fin 2)
  let eMatA5 : SL(2, 𝔽₄) ≃* A5 :=
    eMatSL.trans (eSLAlt.trans (Equiv.altCongrHom eP))
  exact ⟨eMatA5.symm⟩

/-- Helper for Exercise 18-18.6-3: the exceptional isomorphism with the linear `SL` action
model on `𝔽₄²`. -/
private theorem alternatingGroup_fin5_mulEquiv_specialLinear_f4_direct :
    Nonempty (A5 ≃* SpecialLinearGroup 𝔽₄ V2) := by
  -- Compose the direct matrix isomorphism with the standard matrix-to-linear `SL₂` equivalence.
  rcases alternatingGroup_fin5_mulEquiv_sl2_f4_direct with ⟨e⟩
  exact ⟨e.trans (Matrix.SpecialLinearGroup.toLin'_equiv (R := 𝔽₄) (n := Fin 2))⟩

/-- Helper for Exercise 18-18.6-3: `SL₂(𝔽₄)` moves the first basis vector to any nonzero
vector of `𝔽₄²`. -/
private theorem exists_specialLinear_map_e0_eq {x : V2} (hx : x ≠ 0) :
    ∃ g : SpecialLinearGroup 𝔽₄ V2,
      (g : V2 →ₗ[𝔽₄] V2) (Pi.single 0 1) = x := by
  -- Build an explicit determinant-one matrix with first column `x`.
  by_cases hx0 : x 0 = 0
  · have hx1 : x 1 ≠ 0 := by
      intro hx1
      apply hx
      ext i
      fin_cases i
      · exact hx0
      · exact hx1
    have hdet : (!![(0 : 𝔽₄), - (x 1)⁻¹; x 1, 0] :
        Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
      rw [Matrix.det_fin_two_of]
      field_simp [hx1]
      ring
    let A : SL(2, 𝔽₄) :=
      ⟨!![(0 : 𝔽₄), - (x 1)⁻¹; x 1, 0], hdet⟩
    refine ⟨Matrix.SpecialLinearGroup.toLin'_equiv A, ?_⟩
    ext i
    fin_cases i
    · simp [A, Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, hx0]
    · simp [A, Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · have hdet : (!![x 0, 0; x 1, (x 0)⁻¹] :
        Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
      rw [Matrix.det_fin_two_of]
      field_simp [hx0]
      ring
    let A : SL(2, 𝔽₄) :=
      ⟨!![x 0, 0; x 1, (x 0)⁻¹], hdet⟩
    refine ⟨Matrix.SpecialLinearGroup.toLin'_equiv A, ?_⟩
    ext i
    fin_cases i
    · simp [A, Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    · simp [A, Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 18-18.6-3: a lower unipotent element sends `e₀` to `e₀ + e₁`. -/
private theorem lower_unipotent_map_e0 :
    ∃ u : SpecialLinearGroup 𝔽₄ V2,
      (u : V2 →ₗ[𝔽₄] V2) (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 := by
  -- Use the elementary matrix with lower-left entry `1`.
  have hdet : (!![(1 : 𝔽₄), 0; 1, 1] :
      Matrix (Fin 2) (Fin 2) 𝔽₄).det = 1 := by
    simp [Matrix.det_fin_two_of]
  let A : SL(2, 𝔽₄) :=
    ⟨!![(1 : 𝔽₄), 0; 1, 1], hdet⟩
  refine ⟨Matrix.SpecialLinearGroup.toLin'_equiv A, ?_⟩
  ext i
  fin_cases i
  · simp [A, Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  · simp [A, Matrix.SpecialLinearGroup.toLin'_equiv, Matrix.SpecialLinearGroup.toLin'_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 18-18.6-3: the natural two-dimensional `SL₂(𝔽₄)` representation is
irreducible. -/
private theorem natural_specialLinear_f4_isIrreducible :
    (Representation.ofDistribMulAction 𝔽₄ (SpecialLinearGroup 𝔽₄ V2) V2).IsIrreducible := by
  let ρ : Representation 𝔽₄ (SpecialLinearGroup 𝔽₄ V2) V2 :=
    Representation.ofDistribMulAction 𝔽₄ (SpecialLinearGroup 𝔽₄ V2) V2
  let e0 : V2 := Pi.single 0 1
  let e1 : V2 := Pi.single 1 1
  have he0_ne : e0 ≠ 0 := by
    intro h
    have : (1 : 𝔽₄) = 0 := by simpa [e0] using congrFun h 0
    exact one_ne_zero this
  change ρ.IsIrreducible
  rw [Representation.IsIrreducible]
  letI : Nontrivial (Subrepresentation ρ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro hbot_top
    have he0_mem : e0 ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
      rw [hbot_top]
      exact Submodule.mem_top
    have he0_zero : e0 = 0 := by simpa using he0_mem
    exact he0_ne he0_zero
  refine IsSimpleOrder.of_forall_eq_top fun W hW_ne_bot ↦ ?_
  have hWsub_ne_bot : W.toSubmodule ≠ ⊥ := by
    intro hsub
    apply hW_ne_bot
    apply Subrepresentation.toSubmodule_injective
    exact hsub
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hWsub_ne_bot with ⟨x, hxW, hxne⟩
  -- Move a nonzero vector in the stable subspace back to `e₀`.
  rcases exists_specialLinear_map_e0_eq hxne with ⟨g, hg⟩
  have he0W : e0 ∈ W.toSubmodule := by
    have hxW' : ρ g⁻¹ x ∈ W.toSubmodule := W.apply_mem_toSubmodule g⁻¹ hxW
    rw [← hg] at hxW'
    simpa [ρ, e0, SpecialLinearGroup.smul_def] using hxW'
  -- A lower unipotent then puts `e₀ + e₁` in the same subspace, hence also `e₁`.
  rcases lower_unipotent_map_e0 with ⟨u, hu⟩
  have hu_e0 : (u : V2 ≃ₗ[𝔽₄] V2) e0 = e0 + e1 := by
    simpa [e0, e1] using hu
  have he01W : e0 + e1 ∈ W.toSubmodule := by
    have h : ρ u e0 ∈ W.toSubmodule := W.apply_mem_toSubmodule u he0W
    have h' : (u : V2 ≃ₗ[𝔽₄] V2) e0 ∈ W.toSubmodule := by
      simpa [ρ, SpecialLinearGroup.smul_def] using h
    simpa [hu_e0] using h'
  have he1W : e1 ∈ W.toSubmodule := by
    have h := W.toSubmodule.sub_mem he01W he0W
    simpa [e0, e1] using h
  have hvdecomp : ∀ v : V2, v = v 0 • e0 + v 1 • e1 := by
    intro v
    ext i
    · fin_cases i <;> simp [e0, e1]
  -- Since the stable subspace contains the standard basis, it is the whole module.
  apply Subrepresentation.toSubmodule_injective
  change W.toSubmodule = (⊤ : Submodule 𝔽₄ V2)
  rw [eq_top_iff]
  intro v _
  rw [hvdecomp v]
  exact W.toSubmodule.add_mem (W.toSubmodule.smul_mem (v 0) he0W)
    (W.toSubmodule.smul_mem (v 1) he1W)

/-- Helper for Exercise 18-18.6-3: precomposing a representation with a group equivalence
preserves irreducibility. -/
private theorem isIrreducible_comp_of_mulEquiv
    {K : Type*} [Field K] {G H : Type*} [Group G] [Group H]
    {W : Type*} [AddCommGroup W] [Module K W]
    (e : G ≃* H) (σ : Representation K H W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  -- Transport each stable subspace across the equivalence and apply irreducibility upstairs.
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation σ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro h x hx
        simpa using W.apply_mem_toSubmodule (e.symm h) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

namespace Representation

/-- Helper for Exercise 18-18.6-3: a direct simple degree-`2` source model over `𝔽₄`, obtained
from the natural module of `SL(2, 𝔽₄)` and the projective-line isomorphism `A₅ ≃ SL(2, 𝔽₄)`. -/
theorem a5_natural_sl2_f4_source_slot :
    ∃ E2 : FDRep 𝔽₄ A5,
      Simple E2 ∧ Module.finrank 𝔽₄ E2.V = 2 := by
  -- Pull the natural `SL₂(𝔽₄)` action back along the direct exceptional isomorphism.
  rcases alternatingGroup_fin5_mulEquiv_specialLinear_f4_direct with ⟨eA5SL⟩
  let ρSL : Representation 𝔽₄ (SpecialLinearGroup 𝔽₄ V2) V2 :=
    Representation.ofDistribMulAction 𝔽₄ (SpecialLinearGroup 𝔽₄ V2) V2
  let ρA5 : Representation 𝔽₄ A5 V2 := ρSL.comp eA5SL.toMonoidHom
  have hρSL : ρSL.IsIrreducible := natural_specialLinear_f4_isIrreducible
  letI : ρSL.IsIrreducible := hρSL
  have hρA5 : ρA5.IsIrreducible := by
    exact isIrreducible_comp_of_mulEquiv eA5SL ρSL
  letI : ρA5.IsIrreducible := hρA5
  refine ⟨FDRep.of ρA5, ?_, ?_⟩
  · -- Convert irreducibility of the unbundled representation to simplicity of `FDRep.of`.
    letI : Representation.IsIrreducible (FDRep.of ρA5).ρ := by
      simpa using hρA5
    exact FDRep.simple_of_isIrreducible (FDRep.of ρA5)
  · -- The carrier is the standard two-dimensional function space.
    simp [ρA5]

end Representation
