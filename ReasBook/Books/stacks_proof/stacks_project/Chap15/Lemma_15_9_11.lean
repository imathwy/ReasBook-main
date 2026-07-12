import Mathlib
import StacksProject_2024.Chap10.Lemma_10_32_7
import StacksProject_2024.Chap10.Lemma_10_78_6
import StacksProject_2024.Chap15.Lemma_15_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

open Polynomial

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable {Pbar : Type v} [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]

/- Domain-style sampling:
- primary domain: étale lifting of finite projective modules across quotient rings;
- sampled owner declarations:
  `Module.FiniteProjective`,
  `Module.Projective.iff_split`,
  `Algebra.exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map`,
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`;
- best owner abstraction: the finite-projective owner is the canonical predicate
  `Module.FiniteProjective`, while the source-facing theorem here remains the étale lifting
  existence statement; the transported quotient-module structure on `Pbar` and the concrete
  quotient model of the reduction of `P'` are derived bridge data rather than primitive owners;
- primitive data: the ideal `I` and the finite projective `(A ⧸ I)`-module `Pbar`;
- derived API: the transported `A' ⧸ IA'`-module structure on `Pbar` via `eIso`, the reduction
  quotient `P' ⧸ IA' P'`, and the quotient/tensor identification supplied canonically by
  `TensorProduct.tensorQuotMapSMulEquivTensorQuot`.

Source/core/bridge triage:
- `source-facing`: the present étale lifting theorem for a finite projective quotient module;
- `core/canonical`: `Module.FiniteProjective`;
- `bridge/view`: the quotient-model identification of reduction modulo `IA'` and the transported
  scalar action on `Pbar`. -/

/-- Helper for Lemma 15.9.11: a split projector `iota ∘ pi` is idempotent. -/
lemma split_projector_isIdempotentElem
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ}
    (pi : (Fin n → R) →ₗ[R] M)
    (iota : M →ₗ[R] Fin n → R)
    (hpiiota : pi.comp iota = LinearMap.id) :
    IsIdempotentElem (iota.comp pi) := by
  -- Proof comment: inserting the splitting relation `pi ∘ iota = id` collapses one copy of the
  -- projector in the square `(iota ∘ pi)^2`.
  change (iota.comp pi) * (iota.comp pi) = iota.comp pi
  apply LinearMap.ext
  intro w
  ext i
  have hsplit : pi (iota (pi w)) = pi w := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : M →ₗ[R] M ↦ f (pi w)) hpiiota
  simp [hsplit, LinearMap.comp_apply]

/-- Helper for Lemma 15.9.11: the image of a split projector is linearly equivalent to the
original module. -/
theorem split_projector_range_nonempty_equiv
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ}
    (pi : (Fin n → R) →ₗ[R] M)
    (iota : M →ₗ[R] Fin n → R)
    (hpiiota : pi.comp iota = LinearMap.id)
    (hpisurj : Function.Surjective pi) :
    Nonempty (M ≃ₗ[R] LinearMap.range (iota.comp pi)) := by
  let eRangeIota : M ≃ₗ[R] LinearMap.range iota :=
    LinearEquiv.ofInjective iota <| by
      intro x y hxy
      calc
        x = (pi.comp iota) x := by
              simpa [LinearMap.comp_apply] using (DFunLike.congr_fun hpiiota x).symm
        _ = (pi.comp iota) y := by simpa [LinearMap.comp_apply, hxy]
        _ = y := by simpa [LinearMap.comp_apply] using (DFunLike.congr_fun hpiiota y)
  have hrange :
      LinearMap.range (iota.comp pi) = LinearMap.range iota := by
    rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hpisurj)]
  -- Proof comment: first identify `M` with the image of `iota`, then transport along the range
  -- equality induced by surjectivity of `pi`.
  exact ⟨eRangeIota.trans (LinearEquiv.ofEq _ _ hrange.symm)⟩

/-- Helper for Lemma 15.9.11: choose the equivalence between a split summand and the image of its
projector. -/
noncomputable def split_projector_range_equiv
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ}
    (pi : (Fin n → R) →ₗ[R] M)
    (iota : M →ₗ[R] Fin n → R)
    (hpiiota : pi.comp iota = LinearMap.id)
    (hpisurj : Function.Surjective pi) :
    M ≃ₗ[R] LinearMap.range (iota.comp pi) :=
  Classical.choice (split_projector_range_nonempty_equiv pi iota hpiiota hpisurj)

/-- Helper for Lemma 15.9.11: the range of an idempotent endomorphism of a finite free module is
finite projective. -/
lemma finiteProjective_range_of_isIdempotentElem
    {R : Type*} [CommRing R]
    {n : ℕ}
    (p : (Fin n → R) →ₗ[R] Fin n → R)
    (hp : IsIdempotentElem p) :
    Module.FiniteProjective R (LinearMap.range p) := by
  let π : (Fin n → R) →ₗ[R] LinearMap.range p :=
    p.codRestrict (LinearMap.range p) fun x ↦ LinearMap.mem_range_self p x
  have hπsurj : Function.Surjective π := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    refine ⟨x, rfl⟩
  have hπsplit : π.comp (LinearMap.range p).subtype = LinearMap.id := by
    -- Proof comment: an element already in the image of an idempotent projector is fixed by that
    -- projector, so the codomain restriction retracts along the subtype.
    ext y i
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    have hpp : p (p x) = p x := by
      simpa using DFunLike.congr_fun hp.eq x
    simp [π, LinearMap.comp_apply, hpp]
  constructor
  · -- Proof comment: the codomain-restricted projector is surjective onto its range.
    exact Module.Finite.of_surjective π hπsurj
  · -- Proof comment: the splitting `π ∘ subtype = id` exhibits the range as a retract of a free
    -- module, hence projective.
    letI : Module.Projective R (Fin n → R) := Module.Projective.of_free
    exact Module.Projective.of_split (LinearMap.range p).subtype π hπsplit

/-- Helper for Lemma 15.9.11: an endomorphism of the quotient finite free module lifts to an
endomorphism of the source finite free module after identifying reduction with the coordinatewise
quotient. -/
lemma free_endomorphism_lift_mod_ideal
    (n : ℕ)
    (pbar : (Fin n → A ⧸ I) →ₗ[A ⧸ I] Fin n → A ⧸ I) :
    ∃ φ : (Fin n → A) →ₗ[A] Fin n → A,
      φ.quotientMapByIdeal I =
        ((free_pi_quotient_equiv (R := A) (I := I) n).symm.toLinearMap).comp
          ((LinearMap.restrictScalars A pbar).comp
            (free_pi_quotient_equiv (R := A) (I := I) n).toLinearMap) := by
  let pbar0 :
      ((Fin n → A) ⧸ (I • (⊤ : Submodule A (Fin n → A)))) →ₗ[A]
        ((Fin n → A) ⧸ (I • (⊤ : Submodule A (Fin n → A)))) :=
    ((free_pi_quotient_equiv (R := A) (I := I) n).symm.toLinearMap).comp
      ((LinearMap.restrictScalars A pbar).comp
        (free_pi_quotient_equiv (R := A) (I := I) n).toLinearMap)
  -- Proof comment: the earlier quotient-lifting theorem from Lemma `15.3.3` applies directly to
  -- the conjugated quotient endomorphism `pbar0`.
  exact
    exists_lift_with_prescribed_quotientMapByIdeal
      (R := A) (I := I) (Q := Fin n → A) (M := Fin n → A) pbar0

/-- Helper for Lemma 15.9.11: the free quotient equivalence sends a quotient representative to
its coordinatewise residue classes. -/
private theorem free_pi_quotient_equiv_apply_mkQ
    (n : ℕ) (x : Fin n → A) :
    free_pi_quotient_equiv (R := A) (I := I) n ((I • (⊤ : Submodule A (Fin n → A))).mkQ x) =
      fun i ↦ Ideal.Quotient.mk I (x i) := by
  -- Proof comment: unfold the quotient comparison only on an explicit quotient representative.
  change free_pi_quotient_map (R := A) (I := I) n x = fun i ↦ Ideal.Quotient.mk I (x i)
  rfl

/-- Helper for Lemma 15.9.11: on the standard free basis, `toLin'` inverts `toMatrix`. -/
private theorem toLin'_toMatrix_basisFun
    (n : ℕ)
    (φ : (Fin n → A) →ₗ[A] Fin n → A) :
    (LinearMap.toMatrix (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin n)) φ).toLin' = φ := by
  -- Proof comment: specialize the general `Matrix.toLin_toMatrix` inverse relation to the
  -- coordinate basis and rewrite `toLin` as `toLin'`.
  simpa [Matrix.toLin_eq_toLin'] using
    (Matrix.toLin_toMatrix (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin n)) φ)

/-- Helper for Lemma 15.9.11: after identifying the quotient of a finite free module with
coordinatewise residues, the quotient map attached to a matrix is the coefficientwise quotient
matrix map. -/
private theorem closed_fiber_matrix_map_apply
    (n : ℕ)
    (B : Matrix (Fin n) (Fin n) A)
    (x : Fin n → A ⧸ I) :
    let e := free_pi_quotient_equiv (R := A) (I := I) n
    e ((B.toLin').quotientMapByIdeal I (e.symm x)) =
      ((B.map (Ideal.Quotient.mk I)).toLin') x := by
  let e := free_pi_quotient_equiv (R := A) (I := I) n
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A (Fin n → A))) (e.symm x)
  have hx :
      x = fun i ↦ Ideal.Quotient.mk I (y i) := by
    -- Proof comment: replace the abstract quotient point by a concrete coordinate representative.
    calc
      x = e (e.symm x) := by simp [e]
      _ = e ((I • (⊤ : Submodule A (Fin n → A))).mkQ y) := by rw [hy]
      _ = fun i ↦ Ideal.Quotient.mk I (y i) := by
            simpa [e] using free_pi_quotient_equiv_apply_mkQ (A := A) (I := I) n y
  -- Proof comment: after choosing coordinates, quotienting `B.toLin'` is the same as mapping the
  -- matrix entries to `A ⧸ I` and applying the resulting matrix to the residue vector.
  calc
    e ((B.toLin').quotientMapByIdeal I (e.symm x)) =
        e ((B.toLin').quotientMapByIdeal I ((I • (⊤ : Submodule A (Fin n → A))).mkQ y)) := by
          rw [hy]
    _ = e ((I • (⊤ : Submodule A (Fin n → A))).mkQ (B.toLin' y)) := by
          rw [quotientMapByIdeal_apply_mkQ]
    _ = fun i ↦ Ideal.Quotient.mk I ((B.toLin' y) i) := by
          simpa [e] using free_pi_quotient_equiv_apply_mkQ (A := A) (I := I) n (B.toLin' y)
    _ = ((B.map (Ideal.Quotient.mk I)).toLin') (fun i ↦ Ideal.Quotient.mk I (y i)) := by
          ext i
          rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
          change (Ideal.Quotient.mk I) (∑ j, B i j * y j) =
            ∑ j, (Ideal.Quotient.mk I) (B i j) * (Ideal.Quotient.mk I) (y j)
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp
    _ = ((B.map (Ideal.Quotient.mk I)).toLin') x := by rw [hx]

/-- Helper for Lemma 15.9.11: the coefficientwise quotient matrix has the mapped characteristic
polynomial. -/
private theorem charpoly_closed_fiber_matrix_map
    (n : ℕ)
    (φ : (Fin n → A) →ₗ[A] Fin n → A) :
    LinearMap.charpoly
      (((LinearMap.toMatrix (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin n)) φ).map
          (Ideal.Quotient.mk I)).toLin') =
      Polynomial.map (Ideal.Quotient.mk I) (LinearMap.charpoly φ) := by
  let bA : Module.Basis (Fin n) A (Fin n → A) := Pi.basisFun A (Fin n)
  let bQ : Module.Basis (Fin n) (A ⧸ I) (Fin n → A ⧸ I) := Pi.basisFun (A ⧸ I) (Fin n)
  -- Proof comment: convert the closed-fiber map to its matrix on the standard basis and then use
  -- the naturality of matrix characteristic polynomials under coefficient maps.
  calc
    LinearMap.charpoly
        (((LinearMap.toMatrix bA bA φ).map (Ideal.Quotient.mk I)).toLin') =
          LinearMap.charpoly
            ((Matrix.toLin bQ bQ) ((LinearMap.toMatrix bA bA φ).map (Ideal.Quotient.mk I))) := by
              simp [bQ, Matrix.toLin_eq_toLin']
    _ = ((LinearMap.toMatrix bA bA φ).map (Ideal.Quotient.mk I)).charpoly := by
          rw [← LinearMap.charpoly_toMatrix
            ((Matrix.toLin bQ bQ) ((LinearMap.toMatrix bA bA φ).map (Ideal.Quotient.mk I))) bQ,
            LinearMap.toMatrix_toLin]
    _ = Polynomial.map (Ideal.Quotient.mk I) ((LinearMap.toMatrix bA bA φ).charpoly) := by
          rw [Matrix.charpoly_map]
    _ = Polynomial.map (Ideal.Quotient.mk I) (LinearMap.charpoly φ) := by
          rw [LinearMap.charpoly_toMatrix φ bA]

/-- Helper for Lemma 15.9.11: the characteristic polynomial of a lift `φ` reduces to the
characteristic polynomial of the projector `pbar` on the closed fiber. -/
lemma charpoly_lift_maps_to_projector_charpoly
    (n : ℕ)
    (pbar : (Fin n → A ⧸ I) →ₗ[A ⧸ I] Fin n → A ⧸ I)
    {φ : (Fin n → A) →ₗ[A] Fin n → A}
    (hφ : φ.quotientMapByIdeal I =
      ((free_pi_quotient_equiv (R := A) (I := I) n).symm.toLinearMap).comp
        ((LinearMap.restrictScalars A pbar).comp
          (free_pi_quotient_equiv (R := A) (I := I) n).toLinearMap)) :
    Polynomial.map (Ideal.Quotient.mk I) (LinearMap.charpoly φ) = LinearMap.charpoly pbar := by
  let e := free_pi_quotient_equiv (R := A) (I := I) n
  let ψ : (Fin n → A ⧸ I) →ₗ[A ⧸ I] Fin n → A ⧸ I :=
    ((LinearMap.toMatrix (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin n)) φ).map
      (Ideal.Quotient.mk I)).toLin'
  have hclosed :
      LinearMap.restrictScalars A ψ =
        (e.toLinearMap.comp (φ.quotientMapByIdeal I)).comp e.symm.toLinearMap := by
    -- Proof comment: the conjugated quotient map is exactly the coordinatewise residue matrix map.
    apply LinearMap.ext
    intro x
    ext i
    simpa [ψ, e, toLin'_toMatrix_basisFun (A := A) n φ] using
      congrFun
        ((closed_fiber_matrix_map_apply (A := A) (I := I) n
          (LinearMap.toMatrix (Pi.basisFun A (Fin n)) (Pi.basisFun A (Fin n)) φ) x).symm) i
  have hAeq :
      LinearMap.restrictScalars A ψ = LinearMap.restrictScalars A pbar := by
    -- Proof comment: combine the concrete closed-fiber matrix formula with the prescribed
    -- quotient description of `φ`.
    have htransport :
        (e.toLinearMap.comp (φ.quotientMapByIdeal I)).comp e.symm.toLinearMap =
          LinearMap.restrictScalars A pbar := by
      -- Proof comment: conjugate the prescribed quotient formula for `φ` back across the free
      -- quotient equivalence to recover the actual closed-fiber projector.
      have htransport0 :=
        congrArg
          (fun T : ((Fin n → A) ⧸ I • (⊤ : Submodule A (Fin n → A))) →ₗ[A]
              ((Fin n → A) ⧸ I • (⊤ : Submodule A (Fin n → A))) ↦
            (e.toLinearMap.comp T).comp e.symm.toLinearMap) hφ
      simpa [LinearMap.comp_assoc, e] using htransport0
    exact hclosed.trans htransport
  have hψ : ψ = pbar := by
    -- Proof comment: equality of the underlying `A`-linear maps forces equality of the
    -- `(A ⧸ I)`-linear endomorphisms themselves.
    apply LinearMap.ext
    intro x
    simpa [ψ] using
      congrArg
        (fun T : (Fin n → A ⧸ I) →ₗ[A] Fin n → A ⧸ I ↦ T x) hAeq
  -- Proof comment: substitute the concrete closed-fiber matrix computation for `ψ`, then rewrite
  -- it back to the prescribed projector `pbar`.
  calc
    Polynomial.map (Ideal.Quotient.mk I) (LinearMap.charpoly φ) = LinearMap.charpoly ψ := by
      symm
      exact charpoly_closed_fiber_matrix_map (A := A) (I := I) n φ
    _ = LinearMap.charpoly pbar := by rw [hψ]

/-- Helper for Lemma 15.9.11: Cayley-Hamilton descends evaluation at `φ` to the characteristic
polynomial quotient `A[X] / (charpoly φ)`. -/
noncomputable def charpoly_quotient_aeval
    (n : ℕ)
    (φ : (Fin n → A) →ₗ[A] Fin n → A) :
    (A[X] ⧸ Ideal.span ({LinearMap.charpoly φ} : Set A[X])) →ₐ[A] Module.End A (Fin n → A) :=
  Ideal.Quotient.liftₐ
    (Ideal.span ({LinearMap.charpoly φ} : Set A[X]))
    (aeval φ)
    (fun p hp ↦ by
      -- Proof comment: it is enough to show the spanning generator `charpoly φ` lies in the kernel
      -- of `aeval φ`; then the entire span vanishes by ideal closure.
      have hker :
          Ideal.span ({LinearMap.charpoly φ} : Set A[X]) ≤
            RingHom.ker (aeval φ).toRingHom := by
        refine Ideal.span_le.2 ?_
        intro q hq
        have hq' : q = LinearMap.charpoly φ := by
          simpa using hq
        -- This is the linear-map form of Cayley-Hamilton on the unique spanning generator.
        subst hq'
        simpa [RingHom.mem_ker] using LinearMap.aeval_self_charpoly φ
      exact (show (aeval φ : A[X] →ₐ[A] Module.End A (Fin n → A)) p = 0 from hker hp))

/-- Helper for Lemma 15.9.11: the class of `X` in the characteristic-polynomial quotient acts by
the chosen endomorphism `φ`. -/
lemma charpoly_quotient_aeval_mk_X
    (n : ℕ)
    (φ : (Fin n → A) →ₗ[A] Fin n → A) :
    charpoly_quotient_aeval (A := A) n φ
        (Ideal.Quotient.mk (Ideal.span ({LinearMap.charpoly φ} : Set A[X])) X) = φ := by
  -- Proof comment: evaluate the quotient lift on the polynomial generator and unfold `aeval X`.
  rw [charpoly_quotient_aeval, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  simp

/-- Helper for Lemma 15.9.11: a nilpotent projector defect can be corrected to an idempotent in
the source ring without changing its image in any target ring where the chosen element is already
idempotent. -/
lemma idempotent_of_nilpotent_projector_defect
    {R : Type*} [CommRing R]
    {S : Type*} [Ring S]
    (x : R) (hx : IsNilpotent (x * (1 - x)))
    (ψ : R →+* S) (hψx : IsIdempotentElem (ψ x)) :
    ∃ e : R, IsIdempotentElem e ∧ ψ e = ψ x := by
  have hx' : IsNilpotent (x ^ 2 - x) := by
    -- Proof comment: the usual idempotency defect `x^2 - x` differs from `x * (1 - x)` by a sign.
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc] using hx.neg
  obtain ⟨q, hq⟩ :=
    exists_idempotent_eq_add_idempotency_defect_polynomial (A := R) x hx'
  refine ⟨x + (x ^ 2 - x) * aeval x q, hq, ?_⟩
  have hdefect : ψ (x ^ 2 - x) = 0 := by
    -- Proof comment: once `ψ x` is idempotent, its idempotency defect vanishes in the target.
    calc
      ψ (x ^ 2 - x) = (ψ x) ^ 2 - ψ x := by simp [pow_two]
      _ = 0 := by
            apply sub_eq_zero.mpr
            simpa [pow_two] using hψx.eq
  -- Proof comment: the polynomial correction term is killed by the vanished defect, so `ψ`
  -- sees the corrected idempotent as the original idempotent element `ψ x`.
  calc
    ψ (x + (x ^ 2 - x) * aeval x q)
        = ψ x + ψ (x ^ 2 - x) * ψ (aeval x q) := by
            simp
    _ = ψ x := by simp [hdefect]

/-- Helper for Lemma 15.9.11: once the universal root in the projector characteristic-polynomial
quotient has nilpotent projector defect, it can be corrected to an idempotent that still maps to
the projector `pbar`. -/
lemma residue_idempotent_of_universal_root_nilpotent_defect
    (n : ℕ)
    (pbar : (Fin n → A ⧸ I) →ₗ[A ⧸ I] Fin n → A ⧸ I)
    (hpbar : IsIdempotentElem pbar)
    (hxnil :
      IsNilpotent
        ((Ideal.Quotient.mk
            (Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])) X) *
          (1 - Ideal.Quotient.mk
            (Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])) X))) :
    ∃ ebar : ((A ⧸ I)[X] ⧸ Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])),
      IsIdempotentElem ebar ∧
        charpoly_quotient_aeval (A := A ⧸ I) n pbar ebar = pbar := by
  let xbar : ((A ⧸ I)[X] ⧸ Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])) :=
    Ideal.Quotient.mk (Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])) X
  have hxbar_eval :
      charpoly_quotient_aeval (A := A ⧸ I) n pbar xbar = pbar := by
    -- Proof comment: in the characteristic-polynomial quotient, the universal root still acts by
    -- the original projector.
    simpa [xbar] using charpoly_quotient_aeval_mk_X (A := A ⧸ I) n pbar
  have hxbar_idempotent :
      IsIdempotentElem ((charpoly_quotient_aeval (A := A ⧸ I) n pbar).toRingHom xbar) := by
    -- Proof comment: the image of the universal root is exactly `pbar`, which is idempotent.
    simpa [hxbar_eval] using hpbar
  obtain ⟨ebar, hebar, hmap⟩ :=
    idempotent_of_nilpotent_projector_defect xbar hxnil
      (charpoly_quotient_aeval (A := A ⧸ I) n pbar).toRingHom hxbar_idempotent
  refine ⟨ebar, hebar, ?_⟩
  -- Proof comment: the correction term is invisible under `charpoly_quotient_aeval`, so the new
  -- idempotent has the same image as the universal root.
  calc
    charpoly_quotient_aeval (A := A ⧸ I) n pbar ebar =
        charpoly_quotient_aeval (A := A ⧸ I) n pbar xbar := hmap
    _ = pbar := hxbar_eval

-- Proof sketch: choose an idempotent projector on a finite free `(A ⧸ I)`-module whose image is
-- `Pbar`, lift the corresponding characteristic-polynomial factorization to an étale extension as
-- in Lemma `15.9.10`, and take the image of the lifted idempotent on the free `A'`-module.
/-- Lemma 15.9.11: after an étale base change `A → A'` inducing `A ⧸ I ≃ A' ⧸ IA'`, a finite
projective `A ⧸ I`-module lifts to a finite projective `A'`-module whose reduction modulo `IA'` is
linearly equivalent to the original module after transporting scalars across the quotient-ring
isomorphism. -/
@[stacks 07M5]
theorem exists_etale_finite_projective_lift_of_finite_projective_quotient
    (hPbar : Module.FiniteProjective (A ⧸ I) Pbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (P' : Type v) (_ : AddCommGroup P') (_ : Module A' P'),
      let J : Ideal A' := Ideal.map (algebraMap A A') I
      let Q : Type u := A' ⧸ J
      let _ : CommRing Q := inferInstance
      let _ : Module Q Pbar := Module.compHom Pbar eIso.symm.toRingHom
      ∃ eP : (P' ⧸ (J • (⊤ : Submodule A' P'))) ≃ₗ[Q] Pbar,
        Module.FiniteProjective A' P' := by
  classical
  letI : Module.Finite (A ⧸ I) Pbar := hPbar.1
  letI : Module.Projective (A ⧸ I) Pbar := hPbar.2
  obtain ⟨n, pi, iota, hpisurj, _, hpiiota⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (A ⧸ I) Pbar
  let pbar : (Fin n → A ⧸ I) →ₗ[A ⧸ I] Fin n → A ⧸ I := iota.comp pi
  have hpbar : IsIdempotentElem pbar :=
    split_projector_isIdempotentElem pi iota hpiiota
  let ePbar : Pbar ≃ₗ[A ⧸ I] LinearMap.range pbar :=
    split_projector_range_equiv pi iota hpiiota hpisurj
  obtain ⟨φ, hφ⟩ := free_endomorphism_lift_mod_ideal (A := A) (I := I) n pbar
  let f : A[X] := LinearMap.charpoly φ
  have hcharpoly :
      Polynomial.map (Ideal.Quotient.mk I) f = LinearMap.charpoly pbar := by
    -- Proof comment: reduce the lifted characteristic polynomial to the closed-fiber projector
    -- before invoking the étale idempotent-lift package from the source argument.
    simpa [f] using
      charpoly_lift_maps_to_projector_charpoly (A := A) (I := I) n pbar hφ
  let B : Type u := A[X] ⧸ Ideal.span ({f} : Set A[X])
  let β : B →ₐ[A] Module.End A (Fin n → A) := charpoly_quotient_aeval (A := A) n φ
  have hβX :
      β (Ideal.Quotient.mk (Ideal.span ({f} : Set A[X])) X) = φ := by
    -- Proof comment: the universal root in the characteristic-polynomial quotient recovers the
    -- chosen lift `φ` under the descended evaluation map.
    simpa [B, β, f] using charpoly_quotient_aeval_mk_X (A := A) n φ
  -- Proof comment: the source proof has now been reduced to the canonical projector package on a
  -- finite free `(A ⧸ I)`-module, and the first adapter step from Agent C's plan is complete: `φ`
  -- is a genuine lift of the quotient projector after conjugating through
  -- `free_pi_quotient_equiv`.
  -- Proof comment: in addition, the characteristic-polynomial quotient now carries the canonical
  -- source-style algebra map `β : B → End_A(A^n)` sending the class of `X` to `φ`, exactly as in
  -- the textbook Cayley-Hamilton package.
  have hresidue_from_nilpotent :
      IsNilpotent
        ((Ideal.Quotient.mk
            (Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])) X) *
          (1 - Ideal.Quotient.mk
            (Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])) X)) →
      ∃ ebar : ((A ⧸ I)[X] ⧸ Ideal.span ({LinearMap.charpoly pbar} : Set (A ⧸ I)[X])),
        IsIdempotentElem ebar ∧
          charpoly_quotient_aeval (A := A ⧸ I) n pbar ebar = pbar := by
    intro hxnil
    -- Proof comment: once the closed-fiber nilpotence is available, the residue idempotent is now
    -- produced entirely inside this file.
    exact residue_idempotent_of_universal_root_nilpotent_defect
      (A := A) (I := I) n pbar hpbar hxnil
  -- Route correction: the charpoly bridge is now established inside this file, so the remaining
  -- blocker is no longer the free-module reduction or the Cayley-Hamilton factor. The unresolved
  -- step is the residue-idempotent package over `B / I B` and the final range comparison after
  -- invoking the canonical owner theorem from `Lemma_15_9_10`.
  -- TODO: first prove that the class of `X` in the closed-fiber charpoly quotient has nilpotent
  -- projector defect; then `idempotent_of_nilpotent_projector_defect` supplies the residue
  -- idempotent to feed into
  -- `exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map`, after which the
  -- remaining task is to compare the quotient of the lifted projector range with
  -- `LinearMap.range pbar`.
  sorry

end

end Algebra
