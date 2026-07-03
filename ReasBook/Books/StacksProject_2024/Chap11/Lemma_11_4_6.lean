import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap11.Lemma_11_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w' w''

private noncomputable def module_double_centralizer_of_finite_end
    (A : Type v) (M : Type w) [Ring A] [IsSimpleRing A] [AddCommGroup M] [Module A M]
    [Nontrivial M] [IsSemisimpleModule A M] [Module.Finite (Module.End A M) M] :
    A ≃+* Module.End (Module.End A M) M :=
  RingEquiv.ofBijective (Module.toModuleEnd (Module.End A M) M)
    ⟨RingHom.injective _, Module.Finite.toModuleEnd_moduleEnd_surjective⟩

section SimpleAlgebra

open LinearMap

variable {k : Type u} {A : Type v}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]

-- Proof sketch: apply the earlier existence result for simple submodules of the regular module of
-- a finite-dimensional algebra to the regular left `A`-module.
/- Lemma 11.4.6 (1): a finite simple `k`-algebra admits a simple left module, realized as a
simple submodule of the regular module `A`; this is exactly the earlier regular-module
specialization, with `IsSimpleRing A` supplying the needed `Nontrivial A` hypothesis. -/
recall finite_algebra_exists_simple_submodule_regular

variable {M : Type w} {N : Type w'} {P : Type w''}
variable [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable [AddCommGroup P] [Module A P]

-- Proof sketch: identify `A` with a matrix algebra over a division ring, transport both simple
-- modules across the Morita equivalence to simple modules over that division ring, and use that a
-- simple module over a division ring is unique up to linear equivalence.
/-- Lemma 11.4.6 (2): any two simple left `A`-modules are isomorphic. -/
theorem simple_modules_unique_up_to_linear_equiv
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [IsSimpleModule A N] :
    Nonempty (M ≃ₗ[A] N) := by
  have hA : IsIsotypic A A := IsSimpleRing.isIsotypic A A
  have ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A M
  have ⟨J, ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A N
  let _ : IsSimpleModule A I := eM.isSimpleModule_iff.mp inferInstance
  let _ : IsSimpleModule A J := eN.isSimpleModule_iff.mp inferInstance
  have hJI : Nonempty (J ≃ₗ[A] I) := hA I J
  exact ⟨eM.trans hJI.some.symm |>.trans eN.symm⟩

-- Proof sketch: after identifying `A` with a matrix algebra over a division ring, transport `M`
-- and `N` across the matrix-ring equivalence; finite modules over a division ring are free of
-- finite rank, and transporting back identifies `N` with finitely many copies of the simple
-- module `M`.
/-- Lemma 11.4.6 (3): every finite left `A`-module is a finite direct sum of copies of a fixed
simple left `A`-module; here `Fin n → M` represents the finite direct sum of `n` copies of `M`. -/
theorem finite_module_equiv_pi_of_simple_module
    {A : Type v} [Ring A] [IsSimpleRing A] [IsArtinianRing A] {M : Type w} {N : Type w'}
    [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [IsSimpleModule A M] [Module.Finite A N] :
    ∃ n : ℕ, Nonempty (N ≃ₗ[A] (Fin n → M)) := by
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let hNM : IsIsotypicOfType A N M := fun S _ ↦ by
    let _ : IsSimpleModule A S := ‹_›
    exact simple_modules_unique_up_to_linear_equiv
  exact hNM.linearEquiv_fun

variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

-- Proof sketch: decompose both finite modules into finite direct sums of the unique simple
-- module, and compare the number of summands using the finite `k`-dimension of that simple
-- module.
/-- Lemma 11.4.6 (4): two finite left `A`-modules are isomorphic exactly when they have the same
dimension over `k`. -/
theorem finite_modules_linear_equiv_iff_finrank_eq [Module.Finite A M] [Module.Finite A N] :
    Nonempty (M ≃ₗ[A] N) ↔ Module.finrank k M = Module.finrank k N := sorry

end SimpleAlgebra

section MatrixModel

open scoped Matrix.Module

variable {K : Type v} [DivisionRing K]
variable {n : ℕ}

-- Proof sketch: transport the simple left `K`-module `K` across the canonical Morita equivalence
-- between `K` and `Matrix (Fin n) (Fin n) K`.
/-- Lemma 11.4.6 (5): if `A = Matrix (Fin n) (Fin n) K` with `n ≥ 1`, then the standard module
`K^{⊕ n}`, represented in Lean as `Fin n → K`, is simple. -/
theorem matrix_simple_module (hn : 1 ≤ n) :
    IsSimpleModule (Matrix (Fin n) (Fin n) K) (Fin n → K) := sorry

private noncomputable def endSelfToMatrixModuleEnd :
    Module.End K K →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun f := LinearMap.mapMatrixModule (Fin n) f
  map_one' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_mul' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_zero' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_add' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]

private noncomputable def scalarToMatrixModuleEnd :
    Kᵐᵒᵖ →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  endSelfToMatrixModuleEnd.comp (RingEquiv.moduleEndSelf K).toRingHom

private theorem scalarToMatrixModuleEnd_apply (x : Kᵐᵒᵖ) (v : Fin n → K) :
    scalarToMatrixModuleEnd x v = fun i ↦ v i * MulOpposite.unop x := by
  ext i
  simp [scalarToMatrixModuleEnd, endSelfToMatrixModuleEnd, LinearMap.mapMatrixModule_apply]

private noncomputable def matrixModuleEndScalar (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) : K :=
  f (Pi.single ⟨0, hn⟩ (1 : K)) ⟨0, hn⟩

private theorem matrixModuleEnd_basis_eq (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    ∀ i : Fin n,
      f (Pi.single i (1 : K)) = Pi.single i (matrixModuleEndScalar hn f) := by
  let i0 : Fin n := ⟨0, hn⟩
  have h0 : f (Pi.single i0 (1 : K)) = Pi.single i0 (matrixModuleEndScalar hn f) := by
    simpa [matrixModuleEndScalar, i0, Matrix.Module.single_smul] using
      (f.map_smul (Matrix.single i0 i0 (1 : K)) (Pi.single i0 (1 : K)))
  intro i
  simpa [i0, h0, Matrix.Module.single_smul] using
    (f.map_smul (Matrix.single i i0 (1 : K)) (Pi.single i0 (1 : K)))

private theorem scalarToMatrixModuleEnd_left_inv (hn : 1 ≤ n) (x : Kᵐᵒᵖ) :
    matrixModuleEndScalar hn (scalarToMatrixModuleEnd x) = MulOpposite.unop x := by
  simp [matrixModuleEndScalar, scalarToMatrixModuleEnd_apply]

private theorem scalarToMatrixModuleEnd_right_inv (hn : 1 ≤ n)
    (f : Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K)) :
    scalarToMatrixModuleEnd (MulOpposite.op (matrixModuleEndScalar hn f)) = f := by
  ext v i
  have hbasis := matrixModuleEnd_basis_eq hn f
  have hv : v = ∑ j : Fin n, v j • (Pi.single j (1 : K) : Fin n → K) := by
    ext j
    simp [Pi.single_apply]
  have hfv : f v = ∑ j : Fin n, v j • f (Pi.single j (1 : K)) := by
    ext i
    rw [hv, map_sum]
    simp [Pi.single_apply, f.map_smul_of_tower]
  calc
    scalarToMatrixModuleEnd (MulOpposite.op (matrixModuleEndScalar hn f)) v i
        = (fun j ↦ v j * matrixModuleEndScalar hn f) i := by
            simp [scalarToMatrixModuleEnd_apply]
    _ = (f v) i := by
      rw [hfv]
      simp [hbasis, Pi.single_apply]

private noncomputable def scalarToMatrixModuleEndEquiv (hn : 1 ≤ n) :
    Kᵐᵒᵖ ≃+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  RingEquiv.ofBijective scalarToMatrixModuleEnd <| by
    constructor
    · intro x y h
      apply MulOpposite.unop_injective
      rw [← scalarToMatrixModuleEnd_left_inv hn x, ← scalarToMatrixModuleEnd_left_inv hn y, h]
    · intro f
      exact ⟨MulOpposite.op (matrixModuleEndScalar hn f), scalarToMatrixModuleEnd_right_inv hn f⟩

section

variable {k : Type u} [Field k] [Algebra k K]

private noncomputable def endSelfToMatrixModuleEndAlgHom :
    Module.End K K →ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) where
  toFun f := LinearMap.mapMatrixModule (Fin n) f
  map_one' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_mul' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_zero' := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  map_add' f g := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply]
  commutes' c := by
    ext v i
    simp [LinearMap.mapMatrixModule_apply, Algebra.algebraMap_eq_smul_one]

private noncomputable def scalarToMatrixModuleEndAlgHom :
    Kᵐᵒᵖ →ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  endSelfToMatrixModuleEndAlgHom.comp
    (AlgEquiv.moduleEndSelf k : Kᵐᵒᵖ ≃ₐ[k] Module.End K K).toAlgHom

private noncomputable def scalarToMatrixModuleEndAlgEquiv (hn : 1 ≤ n) :
    Kᵐᵒᵖ ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
  AlgEquiv.ofBijective scalarToMatrixModuleEndAlgHom <| by
    constructor
    · intro x y h
      let φ : Kᵐᵒᵖ →+* Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) :=
        scalarToMatrixModuleEnd
      have h' : φ x = φ y := by
        simpa [scalarToMatrixModuleEndAlgHom, scalarToMatrixModuleEnd,
          endSelfToMatrixModuleEndAlgHom, endSelfToMatrixModuleEnd, φ] using h
      have hs : matrixModuleEndScalar hn (φ x) = matrixModuleEndScalar hn (φ y) :=
        congrArg (matrixModuleEndScalar hn) h'
      apply MulOpposite.unop_injective
      rw [← scalarToMatrixModuleEnd_left_inv hn x, ← scalarToMatrixModuleEnd_left_inv hn y]
      simpa [φ] using hs
    · intro f
      refine ⟨MulOpposite.op (matrixModuleEndScalar hn f), ?_⟩
      simpa [scalarToMatrixModuleEndAlgHom, scalarToMatrixModuleEnd,
        endSelfToMatrixModuleEndAlgHom, endSelfToMatrixModuleEnd] using
        scalarToMatrixModuleEnd_right_inv hn f

/-- Lemma 11.4.6 (6): for the standard simple module over `Matrix (Fin n) (Fin n) K`, the
endomorphism ring is `k`-algebra isomorphic to `Kᵐᵒᵖ`. -/
noncomputable def matrix_endomorphism_alg_equiv_op (hn : 1 ≤ n) :
    Module.End (Matrix (Fin n) (Fin n) K) (Fin n → K) ≃ₐ[k] Kᵐᵒᵖ :=
  (scalarToMatrixModuleEndAlgEquiv hn).symm

end

end MatrixModel

section SimpleModuleEndomorphisms

open Module.End

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]

-- Proof sketch: this is Schur's lemma for a simple module: a nonzero endomorphism is injective
-- and surjective, hence invertible.
/-- Lemma 11.4.6 (7): if `M` is a simple left `A`-module, then every nonzero `A`-endomorphism of
`M` is a unit, so `Module.End A M` is a skew field. -/
theorem simple_module_endomorphism_isUnit_of_ne_zero
    {A : Type v} {M : Type w} [Ring A] [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    (f : Module.End A M) (hf : f ≠ 0) :
    IsUnit f := by
  exact (Module.End.isUnit_iff f).2 (f.bijective_of_ne_zero hf)

variable [Module k M] [IsScalarTower k A M]

-- Proof sketch: reduce to the matrix-algebra description of `A` and the standard simple module,
-- where the endomorphism ring is the opposite of a finite-dimensional division algebra over `k`.
/-- Lemma 11.4.6 (8): for a simple left `A`-module `M`, the endomorphism skew field
`Module.End A M` is finite-dimensional over `k`. -/
theorem simple_module_endomorphism_finite_dimensional :
    FiniteDimensional k (Module.End A M) := sorry

private theorem simple_module_moduleFinite_over_end
    (A : Type v) (M : Type w)
    [Ring A] [IsSimpleRing A] [IsArtinianRing A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.Finite (Module.End A M) M := by
  let hA : IsIsotypic A A := IsSimpleRing.isIsotypic A A
  obtain ⟨n, _, S, _hS, ⟨e⟩⟩ := hA.linearEquiv_fun
  have hSM : Nonempty (S ≃ₗ[A] M) := simple_modules_unique_up_to_linear_equiv
  let eSM : S ≃ₗ[A] M := hSM.some
  let e' : A ≃ₗ[A] Fin n → M := e.trans <| .piCongrRight fun _ ↦ eSM
  let v : Fin n → M := e' (1 : A)
  have hspan : Submodule.span (Module.End A M) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let p : A →ₗ[A] M :=
      { toFun := fun a ↦ a • x
        map_add' := fun _ _ ↦ by simp [add_smul]
        map_smul' := fun a b ↦ by simp [mul_smul] }
    let g : (Fin n → M) →ₗ[A] M := p.comp e'.symm.toLinearMap
    refine (Submodule.mem_span_range_iff_exists_fun (Module.End A M)).2 ?_
    refine ⟨fun i ↦ g.comp (LinearMap.single A (fun _ : Fin n ↦ M) i), ?_⟩
    calc
      ∑ i, (g.comp (LinearMap.single A (fun _ : Fin n ↦ M) i) : Module.End A M) • v i
          = ∑ i, g (Pi.single i (v i)) := by
              simp [LinearMap.comp_apply]
      _ = g (∑ i, Pi.single i (v i)) := by rw [map_sum]
      _ = g (e' (1 : A)) := by
            congr
            ext i
            simp [v]
      _ = x := by simp [g, p]
  let _ : Module.Finite (Module.End A M) (Fin n → Module.End A M) :=
    Module.Finite.of_basis (Pi.basisFun (Module.End A M) (Fin n))
  exact Module.Finite.of_surjective
    (Fintype.linearCombination (Module.End A M) v)
    ((span_range_eq_top_iff_surjective_fintypeLinearCombination (Module.End A M) v).1
      hspan)

-- Proof sketch: this is the ring-theoretic bicommutant theorem in the simple-Artinian setting;
-- the later `k`-algebra formulation is just a thin bridge on top of this owner equivalence.
/-- Owner abstraction underlying Lemma 11.4.6 (9): for a simple left module over a simple
Artinian ring, the bicommutant recovers the original ring. -/
noncomputable def simple_module_double_centralizer [IsArtinianRing A] :
    A ≃+* Module.End (Module.End A M) M :=
  let _ : Nontrivial M := IsSimpleModule.nontrivial A M
  let _ : IsSemisimpleRing A := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr inferInstance
  let _ : Module.Finite (Module.End A M) M := simple_module_moduleFinite_over_end A M
  module_double_centralizer_of_finite_end A M

-- Proof sketch: this source-facing algebra statement is the ambient `k`-linear refinement of the
-- simple-Artinian owner equivalence `simple_module_double_centralizer`.
/-- Lemma 11.4.6 (9): if `M` is a simple left `A`-module over a finite-dimensional simple
`k`-algebra `A`, then `A` identifies with the
endomorphism `k`-algebra of `M` viewed as a left `Module.End A M`-module. -/
noncomputable def simple_module_double_centralizer_algEquiv [Module k M] [IsScalarTower k A M] :
    A ≃ₐ[k] Module.End (Module.End A M) M :=
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let e : A ≃+* Module.End (Module.End A M) M := simple_module_double_centralizer
  { __ := e
    commutes' c := by
      ext m
      simp [e, simple_module_double_centralizer, module_double_centralizer_of_finite_end,
        Algebra.algebraMap_eq_smul_one] }

private def centerToModuleEndCenter
    (R : Type v) (M : Type w) [DivisionRing R] [AddCommGroup M] [Module R M] :
    Subring.center R →+* Subring.center (Module.End R M) where
  toFun z := by
    let hz : (z : R) ∈ Set.center R := by
      rw [Semigroup.mem_center_iff]
      exact Subring.mem_center_iff.mp z.2
    exact ⟨Module.End.smulLeft z.1 hz, by
      change Module.End.smulLeft z.1 hz ∈ Set.center (Module.End R M)
      exact (Module.End.mem_center_iff).2 ⟨z.1, hz, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    ext m
    change (1 : R) • m = m
    simp
  map_mul' x y := by
    apply Subtype.ext
    ext m
    change ((x : R) * (y : R)) • m = (x : R) • ((y : R) • m)
    simp [mul_smul]
  map_zero' := by
    apply Subtype.ext
    ext m
    change (0 : R) • m = 0
    simp
  map_add' x y := by
    apply Subtype.ext
    ext m
    change ((x : R) + (y : R)) • m = (x : R) • m + (y : R) • m
    simp [add_smul]

private noncomputable def centerModuleEndEquiv
    (R : Type v) (M : Type w) [DivisionRing R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    Subring.center R ≃+* Subring.center (Module.End R M) :=
  RingEquiv.ofBijective (centerToModuleEndCenter R M) <| by
    constructor
    · intro x y hxy
      apply Subtype.ext
      obtain ⟨m, hm⟩ := exists_ne (0 : M)
      exact smul_left_injective R hm <| by
        simpa using congrArg (fun f : Module.End R M ↦ f m) (congrArg Subtype.val hxy)
    · intro f
      have hf : (f : Module.End R M) ∈ Set.center (Module.End R M) := by
        rw [Semigroup.mem_center_iff]
        exact Subring.mem_center_iff.mp f.2
      rcases (Module.End.mem_center_iff).1 hf with ⟨r, hr, hfr⟩
      refine ⟨⟨r, by
        rw [Subring.mem_center_iff]
        exact Semigroup.mem_center_iff.mp hr⟩, ?_⟩
      apply Subtype.ext
      simpa [centerToModuleEndCenter] using hfr.symm

-- Proof sketch: after identifying `A` with `Module.End (Module.End A M) M`, both centers become
-- the scalar endomorphisms of the simple module, giving a canonical ring equivalence.
/-- Lemma 11.4.6 (10): the centers of `A` and `Module.End A M` are canonically ring-isomorphic. -/
noncomputable def simple_module_center_equiv
    [IsArtinianRing A] :
    Subring.center A ≃+* Subring.center (Module.End A M) := by
  classical
  let _ : Nontrivial M := IsSimpleModule.nontrivial A M
  let _ : DecidableEq (Module.End A M) := Classical.decEq _
  let _ : DivisionRing (Module.End A M) := Module.End.instDivisionRing
  let e : A ≃+* Module.End (Module.End A M) M := simple_module_double_centralizer
  exact (Subring.centerCongr e).trans <|
    (centerModuleEndEquiv (Module.End A M) M).symm

-- Proof sketch: in the matrix-algebra model `A ≃ Matrix (Fin n) (Fin n) K` and
-- `Module.End A M ≃ Kᵐᵒᵖ`, so the stated formula is the usual matrix-dimension computation.
/-- Lemma 11.4.6 (11): if `M` is a simple left `A`-module and `L = Module.End A M`, then
`[A : k] [L : k] = dim_k(M)^2`. -/
theorem simple_module_finrank_formula :
    Module.finrank k A * Module.finrank k (Module.End A M) = (Module.finrank k M) ^ 2 := sorry

end SimpleModuleEndomorphisms

section FiniteModuleEndomorphisms

variable {k : Type u} {A : Type v} {M : Type w} {N : Type w'}
variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] [IsSimpleRing A]
variable [AddCommGroup M] [Module A M] [IsSimpleModule A M]
variable [AddCommGroup N] [Module A N] [Module.Finite A N]
variable [Module k M] [IsScalarTower k A M]
variable [Module k N] [IsScalarTower k A N]

-- Proof sketch: decompose `N` as a finite direct sum of copies of the unique simple module `M`,
-- then compute endomorphisms of that finite direct sum as matrices with entries in
-- `Module.End A M`.
/-- Lemma 11.4.6 (12): for a finite left `A`-module `N`, the endomorphism ring `Module.End A N`
is `k`-algebra isomorphic to a matrix algebra over the skew field `Module.End A M`, where `M` is
any simple left `A`-module. -/
theorem finite_module_endomorphism_ring_matrix :
    ∃ n : ℕ, Nonempty (Module.End A N ≃ₐ[k] Matrix (Fin n) (Fin n) (Module.End A M)) := sorry

-- Proof sketch: identify `N` with a finite direct sum of copies of a simple module and compute
-- the bicommutant explicitly for that matrix action; nontriviality rules out the zero module,
-- where the statement would fail.
/-- Lemma 11.4.6 (13): for a nonzero finite left `A`-module `N`, the bicommutant of `N` recovers
the original algebra `A`. -/
noncomputable def finite_module_double_centralizer [Nontrivial N] :
    A ≃ₐ[k] Module.End (Module.End A N) N :=
  let _ : IsSemisimpleRing A :=
    IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr (IsArtinianRing.of_finite k A)
  let _ : Module.Finite k N := Module.Finite.trans A N
  let _ : Module.Finite (Module.End A N) N :=
    Module.Finite.of_restrictScalars_finite k (Module.End A N) N
  let e : A ≃+* Module.End (Module.End A N) N := module_double_centralizer_of_finite_end A N
  { __ := e
    commutes' c := by
      ext n
      simp [e, module_double_centralizer_of_finite_end, Algebra.algebraMap_eq_smul_one] }

end FiniteModuleEndomorphisms
