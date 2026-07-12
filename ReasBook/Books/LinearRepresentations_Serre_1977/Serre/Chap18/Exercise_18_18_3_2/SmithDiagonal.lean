import Mathlib

noncomputable section

open scoped BigOperators

universe u x

namespace Representation

section SmithDiagonalHelpers

variable {ι : Type x}
variable {M : Type u} [AddCommGroup M]
variable [Finite ι]

/-- Helper for Exercise 18-18.3-2: an integer rank-one span is unchanged if its generator is
replaced by its absolute value. -/
theorem span_singleton_int_eq_natAbs (a : ℤ) :
    Submodule.span ℤ ({a} : Set ℤ) =
      Submodule.span ℤ ({((Int.natAbs a : ℕ) : ℤ)} : Set ℤ) := by
  -- Compare the two spans by writing each generator as a signed multiple of the other.
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨c * Int.sign a, ?_⟩
    calc
      (c * Int.sign a) • ((Int.natAbs a : ℕ) : ℤ) =
          (c * Int.sign a) * ((Int.natAbs a : ℕ) : ℤ) := by
            simp
      _ = c * (Int.sign a * ((Int.natAbs a : ℕ) : ℤ)) := by
            ring
      _ = c * a := by
            rw [Int.sign_mul_natAbs]
      _ = c • a := by
            simp
  · intro hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨c * Int.sign a, ?_⟩
    calc
      (c * Int.sign a) • a = (c * Int.sign a) * a := by
            simp
      _ = c * (Int.sign a * a) := by
            ring
      _ = c * ((Int.natAbs a : ℕ) : ℤ) := by
            rw [Int.sign_mul_self_eq_natAbs]
      _ = c • ((Int.natAbs a : ℕ) : ℤ) := by
            simp

omit [Finite ι] in
/-- Helper for Exercise 18-18.3-2: precomposing coordinates by a permutation sends a permuted
diagonal integer lattice back to the unpermuted diagonal lattice. -/
theorem pi_span_natCast_comp_equiv_map_funCongrLeft
    (d : ι → ℕ) (σ : ι ≃ ι) :
    (Submodule.pi Set.univ fun i : ι ↦
        Submodule.span ℤ ({(d (σ i) : ℤ)} : Set ℤ)).map
        (LinearEquiv.funCongrLeft ℤ ℤ σ.symm).toLinearMap =
      Submodule.pi Set.univ fun i : ι ↦
        Submodule.span ℤ ({(d i : ℤ)} : Set ℤ) := by
  -- Membership in a product diagonal lattice is checked coordinatewise, and the equivalence only
  -- reindexes those coordinates.
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rw [Submodule.mem_pi]
    intro i _
    have hyi : y (σ.symm i) ∈ Submodule.span ℤ ({(d i : ℤ)} : Set ℤ) := by
      rw [Submodule.mem_pi] at hy
      have h := hy (σ.symm i) (Set.mem_univ _)
      simpa using h
    simpa [LinearEquiv.funCongrLeft_apply] using hyi
  · intro hx
    rw [Submodule.mem_pi] at hx
    refine Submodule.mem_map.mpr
      ⟨(LinearEquiv.funCongrLeft ℤ ℤ σ.symm).symm x, ?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro i _
      have h := hx (σ i) (Set.mem_univ _)
      simpa [LinearEquiv.funCongrLeft_apply] using h
    · ext i
      simp [LinearEquiv.funCongrLeft_apply]

/-- Helper for Exercise 18-18.3-2: a full-rank additive subgroup of a free finite `ℤ`-module has
a quotient that decomposes as a product of cyclic groups determined by the corresponding Smith
coefficients. -/
theorem addSubgroup_exists_quotientEquivPiZMod_of_full_rank
    (N : AddSubgroup M)
    (b : Module.Basis ι ℤ M)
    (h : Module.finrank ℤ N.toIntSubmodule = Module.finrank ℤ M) :
    ∃ a : ι → ℤ, Nonempty (M ⧸ N ≃+ ((i : ι) → ZMod (a i).natAbs)) := by
  let a : ι → ℤ := Submodule.smithNormalFormCoeffs (N := N.toIntSubmodule) b h
  refine ⟨a, ?_⟩
  exact ⟨by simpa [a] using (Submodule.quotientEquivPiZMod N.toIntSubmodule b h)⟩

/-- Helper for Exercise 18-18.3-2: Smith-normal-form coordinates send a full-rank submodule of a
free finite `ℤ`-module to the coordinatewise span of its Smith coefficients. -/
theorem map_smithNormalFormTopBasis_equiv_eq_pi_span_smithNormalFormCoeffs
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
      · refine (mem_I_iff _).2 ?_
        intro i
        rw [b'.repr_sum_self]
        rcases Submodule.mem_span_singleton.1 (hx' i) with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        simpa [mul_comm] using hc.symm
      · ext i
        change b'.repr (∑ j, x j • b' j) i = x i
        simpa using congrFun (b'.repr_sum_self x) i
  simpa [a, N'] using hmap

/-- Helper for Exercise 18-18.3-2: once the Smith coefficients of a full-rank submodule are known,
the corresponding Smith-coordinate map identifies that submodule with the matching diagonal
lattice. -/
theorem exists_coordinate_equiv_with_diagonal_of_smith_coeffs
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
  have hmap :=
    map_smithNormalFormTopBasis_equiv_eq_pi_span_smithNormalFormCoeffs
      (N := N) (b := b) (h := h)
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

/-- Helper for Exercise 18-18.3-2: Smith coefficients determine the same diagonal lattice even
when they match the requested diagonal entries only after a permutation of the index set. -/
theorem exists_coordinate_equiv_with_diagonal_of_smith_coeffs_perm
    (N : Submodule ℤ M)
    (b : Module.Basis ι ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M)
    (d : ι → ℕ)
    (σ : ι ≃ ι)
    (hcoeff :
      ∀ i,
        Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) = d (σ i)) :
    ∃ e : M ≃+ (ι → ℤ),
      N.toAddSubgroup.map e.toAddMonoidHom =
        (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)).toAddSubgroup := by
  let eTop : M ≃ₗ[ℤ] (ι → ℤ) :=
    (Submodule.smithNormalFormTopBasis (N := N) b h).equivFun
  let ePerm : (ι → ℤ) ≃ₗ[ℤ] (ι → ℤ) :=
    LinearEquiv.funCongrLeft ℤ ℤ σ.symm
  refine ⟨(eTop.trans ePerm).toAddEquiv, ?_⟩
  apply AddSubgroup.toIntSubmodule.injective
  change N.map (eTop.trans ePerm).toLinearMap =
    Submodule.pi Set.univ fun i ↦ Submodule.span ℤ ({(d i : ℤ)} : Set ℤ)
  have hdiag :
      (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ
            ({Submodule.smithNormalFormCoeffs (N := N) b h i} : Set ℤ)) =
        Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d (σ i) : ℤ)} : Set ℤ) := by
    -- Replace each Smith generator by its absolute value, then by the requested permuted entry.
    ext x
    constructor
    · intro hx
      rw [Submodule.mem_pi] at hx ⊢
      intro i _
      have hspan :
          Submodule.span ℤ
              ({Submodule.smithNormalFormCoeffs (N := N) b h i} : Set ℤ) =
            Submodule.span ℤ ({(d (σ i) : ℤ)} : Set ℤ) := by
        rw [span_singleton_int_eq_natAbs]
        have hd : (d (σ i) : ℤ) =
            ((Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) : ℕ) : ℤ) := by
          exact_mod_cast (hcoeff i).symm
        rw [hd]
      simpa [hspan] using hx i (Set.mem_univ _)
    · intro hx
      rw [Submodule.mem_pi] at hx ⊢
      intro i _
      have hspan :
          Submodule.span ℤ
              ({Submodule.smithNormalFormCoeffs (N := N) b h i} : Set ℤ) =
            Submodule.span ℤ ({(d (σ i) : ℤ)} : Set ℤ) := by
        rw [span_singleton_int_eq_natAbs]
        have hd : (d (σ i) : ℤ) =
            ((Int.natAbs (Submodule.smithNormalFormCoeffs (N := N) b h i) : ℕ) : ℤ) := by
          exact_mod_cast (hcoeff i).symm
        rw [hd]
      simpa [hspan] using hx i (Set.mem_univ _)
  calc
    N.map (eTop.trans ePerm).toLinearMap =
        (N.map eTop.toLinearMap).map ePerm.toLinearMap := by
          ext x
          constructor
          · intro hx
            rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
            exact Submodule.mem_map.mpr
              ⟨eTop y, Submodule.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩
          · intro hx
            rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
            rcases Submodule.mem_map.mp hy with ⟨z, hz, hyz⟩
            exact Submodule.mem_map.mpr ⟨z, hz, congrArg ePerm hyz⟩
    _ = (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ
            ({Submodule.smithNormalFormCoeffs (N := N) b h i} : Set ℤ)).map
          ePerm.toLinearMap := by
          rw [map_smithNormalFormTopBasis_equiv_eq_pi_span_smithNormalFormCoeffs]
    _ = (Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d (σ i) : ℤ)} : Set ℤ)).map ePerm.toLinearMap := by
          rw [hdiag]
    _ = Submodule.pi Set.univ fun i ↦
          Submodule.span ℤ ({(d i : ℤ)} : Set ℤ) := by
          exact pi_span_natCast_comp_equiv_map_funCongrLeft d σ

end SmithDiagonalHelpers

end Representation
