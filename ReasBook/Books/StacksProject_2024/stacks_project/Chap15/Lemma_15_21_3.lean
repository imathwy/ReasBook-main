import Mathlib
import StacksProject_2024.Chap10.Lemma_10_36_3
import StacksProject_2024.Chap15.Lemma_15_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open MvPolynomial
open Polynomial

universe u v w

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Helper for Lemma 15.21.3: a monic polynomial different from `1` gives an injective algebra
map into its adjoined-root algebra. -/
lemma adjoinRoot_algebraMap_injective_of_monic_ne_one [Nontrivial R] {P : R[X]}
    (hP : P.Monic) (hP1 : P ≠ 1) :
    Function.Injective (algebraMap R (AdjoinRoot P)) := by
  -- Compare two coefficients after transporting equality into the quotient presentation.
  intro r s hrs
  change AdjoinRoot.mk P (Polynomial.C r) = AdjoinRoot.mk P (Polynomial.C s) at hrs
  rw [AdjoinRoot.mk_eq_mk] at hrs
  have hmod :
      (Polynomial.C (r - s)) %ₘ P = 0 := by
    rw [Polynomial.modByMonic_eq_zero_iff_dvd hP]
    simpa using hrs
  -- The difference polynomial has degree strictly below the positive degree of `P`.
  have hPdeg :
      (0 : WithBot ℕ) < P.degree := by
    have hPnat : 0 < P.natDegree := hP.natDegree_pos.mpr hP1
    simpa [Polynomial.degree_eq_natDegree hP.ne_zero] using hPnat
  have hself :
      (Polynomial.C (r - s)) %ₘ P = Polynomial.C (r - s) := by
    rw [Polynomial.modByMonic_eq_self_iff hP]
    exact lt_of_le_of_lt Polynomial.degree_C_le hPdeg
  have hzero : Polynomial.C (r - s) = 0 := by
    rw [← hself, hmod]
  simpa [Polynomial.C_eq_zero, sub_eq_zero] using hzero

/-- Helper for Lemma 15.21.3: adjoining a root of a monic polynomial different from `1` yields a
finite free injective extension with a monic linear factor. -/
lemma exists_injective_finiteFree_extension_with_monic_linear_factor [Nontrivial R] {P : R[X]}
    (hP : P.Monic) (hP1 : P ≠ 1) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (α : R') (Q : R'[X]),
      Q.Monic ∧
        P.map (algebraMap R R') = (Polynomial.X - Polynomial.C α) * Q := by
  letI : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  letI : Module.Free R (AdjoinRoot P) := hP.free_adjoinRoot
  have hinj : Function.Injective (algebraMap R (AdjoinRoot P)) :=
    adjoinRoot_algebraMap_injective_of_monic_ne_one hP hP1
  -- The canonical root in `AdjoinRoot P` gives the desired linear factorization.
  have hroot : (P.map (algebraMap R (AdjoinRoot P))).IsRoot (AdjoinRoot.root P) := by
    simpa [-AdjoinRoot.algebraMap_eq] using AdjoinRoot.isRoot_root P
  obtain ⟨Q, hQ, hfactor⟩ :=
    exists_monic_factor_of_isRoot (P.map (algebraMap R (AdjoinRoot P))) (hP.map _) hroot
  exact ⟨AdjoinRoot P, inferInstance, inferInstance, hinj, inferInstance, inferInstance,
    AdjoinRoot.root P, Q, hQ, hfactor⟩

/-- Helper for Lemma 15.21.3: in the nontrivial base-ring case, an integral element admits a
monic annihilator that is not `1`. -/
lemma exists_monic_ne_one_annihilator [Nontrivial R] {x : S} (hx : IsIntegral R x) :
    ∃ P : R[X], P.Monic ∧ P ≠ 1 ∧ Polynomial.aeval x P = 0 := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · -- In the trivial target ring, the linear polynomial `X` already annihilates every element.
    refine ⟨Polynomial.X, Polynomial.monic_X, ?_, ?_⟩
    · simpa using (Polynomial.X_ne_C (1 : R))
    · have hx0 : x = 0 := Subsingleton.elim _ _
      simp [hx0]
  · obtain ⟨Q, hQ, hQeval⟩ := hx
    refine ⟨Polynomial.X * Q, Polynomial.monic_X.mul hQ, ?_, ?_⟩
    · -- Multiplying by `X` forces positive degree, so the polynomial cannot be `1`.
      intro hXQ
      have hdeg : 0 < (Polynomial.X * Q).natDegree := by
        rw [Polynomial.natDegree_X_mul hQ.ne_zero]
        exact Nat.succ_pos _
      have hdeg0 : (Polynomial.X * Q).natDegree = 0 := by simpa [hXQ]
      exact (Nat.ne_of_gt hdeg) hdeg0
    · -- Evaluate the product at `x`; the original annihilator kills the second factor.
      have hQeval' : (Polynomial.aeval x) Q = 0 := by
        simpa using hQeval
      rw [map_mul, hQeval', mul_zero]

/-- Helper for Lemma 15.21.3: mapping a split product of linear factors transports each chosen
root through the coefficient map. -/
lemma map_prod_X_sub_C {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {d : ℕ} (α : Fin d → A) :
    Polynomial.map f (∏ j : Fin d, (Polynomial.X - Polynomial.C (α j))) =
      ∏ j : Fin d, (Polynomial.X - Polynomial.C (f (α j))) := by
  -- Rewrite the product factorwise, then simplify the image of each linear factor.
  simp [Polynomial.map_prod]

/-- Helper for Lemma 15.21.3: in a finite free injective tower, the composite algebra map is still
injective. The finite/free transitivity instances are installed locally for future recursive use. -/
lemma finiteFree_injective_tower {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : Function.Injective (algebraMap A B))
    (hBC : Function.Injective (algebraMap B C))
    [Module.Finite A B] [Module.Free A B] [Module.Finite B C] [Module.Free B C] :
    Function.Injective (algebraMap A C) := by
  letI : Module.Finite A C := Module.Finite.trans B C
  letI : Module.Free A C := Module.Free.trans (R := A) (S := B) (M := C)
  -- Compare through the factorization `A → B → C` coming from the scalar tower.
  intro a a' haa
  apply hAB
  apply hBC
  simpa [IsScalarTower.algebraMap_eq A B C] using haa

/-- Helper for Lemma 15.21.3: a split factorization over `B` transports through a scalar tower to
the corresponding split factorization over `C`. -/
lemma split_factorization_map_to_tower
    {A : Type*} {B : Type*} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {P : A[X]} {d : ℕ} {β : Fin d → B}
    (h :
      P.map (algebraMap A B) =
        ∏ j : Fin d, (Polynomial.X - Polynomial.C (β j))) :
    P.map (algebraMap A C) =
      ∏ j : Fin d, (Polynomial.X - Polynomial.C (algebraMap B C (β j))) := by
  -- First rewrite the base change through the tower, then map each linear factor coefficientwise.
  calc
    P.map (algebraMap A C) = (P.map (algebraMap A B)).map (algebraMap B C) := by
      rw [Polynomial.map_map]
      congr 1
      ext a
      simp [RingHom.comp_apply, IsScalarTower.algebraMap_eq A B C]
    _ = (∏ j : Fin d, (Polynomial.X - Polynomial.C (β j))).map (algebraMap B C) := by rw [h]
    _ = ∏ j : Fin d, (Polynomial.X - Polynomial.C (algebraMap B C (β j))) := by
      simpa using map_prod_X_sub_C (algebraMap B C) β

/-- Helper for Lemma 15.21.3: a monic polynomial of nat-degree zero is the constant polynomial
`1`. -/
lemma monic_eq_one_of_natDegree_zero
    {A : Type*} [Semiring A] {P : A[X]} (hP : P.Monic) (hdeg : P.natDegree = 0) :
    P = 1 := by
  -- This is the canonical degree-zero normalization used in the recursion base case.
  exact Polynomial.eq_one_of_monic_natDegree_zero hP hdeg

/-- Helper for Lemma 15.21.3: reindexing a finite product of split linear factors along
`finCongr` leaves the product unchanged. -/
lemma prod_X_sub_C_finCongr
    {A : Type*} [CommRing A] {m n : ℕ} (h : m = n) (β : Fin n → A) :
    ∏ j : Fin m, (Polynomial.X - Polynomial.C (β ((finCongr h) j))) =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (β j)) := by
  -- Reindex the product along the canonical equivalence between the two `Fin` types.
  exact Fintype.prod_equiv (finCongr h) _ _ (fun j ↦ by simp)

/-- Helper for Lemma 15.21.3: one monic polynomial splits completely after a finite free injective
base extension. -/
lemma exists_injective_finiteFree_extension_splitting_monic_over
    {A : Type w} [CommRing A] [Nontrivial A] {P : A[X]} (hP : P.Monic) :
    ∃ (B : Type w) (_ : CommRing B) (_ : Algebra A B)
      (_ : Function.Injective (algebraMap A B)) (_ : Module.Finite A B)
      (_ : Module.Free A B) (d : ℕ) (β : Fin d → B),
      P.map (algebraMap A B) = ∏ j : Fin d, (Polynomial.X - Polynomial.C (β j)) := by
  -- Follow the source proof: peel off one linear factor, then recurse on the monic quotient.
  let aux :
      ∀ n : ℕ, ∀ {A : Type w} [CommRing A] [Nontrivial A] {P : A[X]},
        P.Monic → P.natDegree ≤ n →
          ∃ (B : Type w) (_ : CommRing B) (_ : Algebra A B)
            (_ : Function.Injective (algebraMap A B)) (_ : Module.Finite A B)
            (_ : Module.Free A B) (d : ℕ) (β : Fin d → B),
            P.map (algebraMap A B) = ∏ j : Fin d, (Polynomial.X - Polynomial.C (β j)) := by
    intro n
    induction n with
    | zero =>
        intro A _ _ P hP hdeg
        have hPdeg : P.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
        have hPone : P = 1 := monic_eq_one_of_natDegree_zero hP hPdeg
        refine ⟨A, inferInstance, Algebra.id A, ?_, inferInstance, inferInstance, 0, Fin.elim0, ?_⟩
        · -- The identity extension keeps the base ring map injective.
          intro a b hab
          simpa using hab
        · -- In the degree-zero case the empty product already gives the full factorization.
          simpa [hPone]
    | succ n ihn =>
        intro A _ _ P hP hdeg
        by_cases hPdeg0 : P.natDegree = 0
        · have hPone : P = 1 := monic_eq_one_of_natDegree_zero hP hPdeg0
          refine ⟨A, inferInstance, Algebra.id A, ?_, inferInstance, inferInstance, 0, Fin.elim0, ?_⟩
          · -- Again the base case is realized by the identity extension.
            intro a b hab
            simpa using hab
          · simpa [hPone]
        · have hP1 : P ≠ 1 := by
            intro hPone
            exact hPdeg0 (by simpa [hPone] using (show (1 : A[X]).natDegree = 0 by simp))
          obtain ⟨B, hBComm, hBAlg, hinjAB, hBfinite, hBfree, α, Q, hQmonic, hfactor⟩ :=
            exists_injective_finiteFree_extension_with_monic_linear_factor (R := A) hP hP1
          letI : CommRing B := hBComm
          letI : Algebra A B := hBAlg
          letI : Nontrivial B := Function.Injective.nontrivial hinjAB
          letI : Module.Finite A B := hBfinite
          letI : Module.Free A B := hBfree
          have hQlt : Q.natDegree < P.natDegree := by
            -- Compare nat-degrees after the peeled factorization over `B`.
            have hdeg_eq : P.natDegree = 1 + Q.natDegree := by
              calc
                P.natDegree = (P.map (algebraMap A B)).natDegree := by
                  symm
                  simpa using (hP.natDegree_map (algebraMap A B))
                _ = ((Polynomial.X - Polynomial.C α) * Q).natDegree := by rw [hfactor]
                _ = (Polynomial.X - Polynomial.C α).natDegree + Q.natDegree := by
                  rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C α) hQmonic]
                _ = 1 + Q.natDegree := by
                  simpa using congrArg (fun m ↦ m + Q.natDegree) (Polynomial.natDegree_X_sub_C α)
            rw [hdeg_eq]
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.lt_succ_self Q.natDegree
          have hQle : Q.natDegree ≤ n := by
            exact Nat.lt_succ_iff.mp (lt_of_lt_of_le hQlt hdeg)
          obtain ⟨C, hCComm, hCAlg, hinjBC, hCfinite, hCfree, d, β, hsplitQ⟩ :=
            ihn (A := B) (P := Q) hQmonic hQle
          letI : CommRing C := hCComm
          letI : Algebra B C := hCAlg
          letI : Algebra A C := RingHom.toAlgebra ((algebraMap B C).comp (algebraMap A B))
          letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
          letI : Module.Finite B C := hCfinite
          letI : Module.Free B C := hCfree
          letI : Module.Finite A C := Module.Finite.trans B C
          letI : Module.Free A C := Module.Free.trans (R := A) (S := B) (M := C)
          have hinjAC : Function.Injective (algebraMap A C) :=
            finiteFree_injective_tower (A := A) (B := B) (C := C) hinjAB hinjBC
          let βtop : Fin (d + 1) → C := Fin.cons (algebraMap B C α) β
          refine ⟨C, inferInstance, inferInstance, hinjAC, inferInstance, inferInstance,
            d + 1, βtop, ?_⟩
          -- Transport the peeled factorization to the top ring and prepend the new root.
          calc
            P.map (algebraMap A C) = ((Polynomial.X - Polynomial.C α) * Q).map (algebraMap B C) := by
              simpa [Polynomial.map_map, RingHom.comp_apply, IsScalarTower.algebraMap_eq A B C] using
                congrArg (Polynomial.map (algebraMap B C)) hfactor
            _ = (Polynomial.X - Polynomial.C (algebraMap B C α)) * Q.map (algebraMap B C) := by
              simp
            _ = (Polynomial.X - Polynomial.C (algebraMap B C α)) *
                  ∏ j : Fin d, (Polynomial.X - Polynomial.C (β j)) := by
              rw [hsplitQ]
            _ = ∏ j : Fin (d + 1), (Polynomial.X - Polynomial.C (βtop j)) := by
              symm
              simpa [βtop] using
                (Fin.prod_univ_succ
                  (f := fun j : Fin (d + 1) ↦ (Polynomial.X - Polynomial.C (βtop j))))
  exact aux P.natDegree (A := A) (P := P) hP le_rfl

/-- Helper for Lemma 15.21.3: a finite family of monic polynomials acquires a common injective
finite free splitting extension. -/
lemma exists_injective_finiteFree_extension_splitting_family [Nontrivial R] {n : ℕ}
    (P : Fin n → R[X]) (hmonic : ∀ i, (P i).Monic) :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R'),
      ∀ i, (P i).map (algebraMap R R') =
        ∏ j : Fin (d i), (Polynomial.X - Polynomial.C (α i j)) := by
  -- Route correction: split the family one index at a time, transporting older factorizations
  -- through the tower instead of redoing the coefficient rewrites inline.
  induction n with
  | zero =>
      let R' := ULift.{v} R
      let d : Fin 0 → ℕ := fun i ↦ nomatch i
      let α : ∀ i, Fin (d i) → R' := fun i ↦ nomatch i
      refine ⟨R', inferInstance, inferInstance, ?_, inferInstance, inferInstance, d, α, ?_⟩
      · -- The empty family is realized over the base ring itself.
        intro a b hab
        exact congrArg ULift.down hab
      · intro i
        nomatch i
  | succ n ih =>
      let Pinit : Fin n → R[X] := fun i ↦ P i.castSucc
      have hmonic_init : ∀ i, (Pinit i).Monic := by
        -- The previously indexed polynomials stay monic.
        intro i
        exact hmonic i.castSucc
      obtain ⟨B, hBComm, hBAlg, hinjRB, hBfinite, hBfree, dB, βB, hsplitB⟩ :=
        ih Pinit hmonic_init
      letI : CommRing B := hBComm
      letI : Algebra R B := hBAlg
      letI : Nontrivial B := Function.Injective.nontrivial hinjRB
      letI : Module.Finite R B := hBfinite
      letI : Module.Free R B := hBfree
      have hlast_monic : ((P (Fin.last n)).map (algebraMap R B)).Monic := by
        exact (hmonic (Fin.last n)).map (algebraMap R B)
      obtain ⟨C, hCComm, hCAlg, hinjBC, hCfinite, hCfree, dLast, βLast, hsplitLast⟩ :=
        exists_injective_finiteFree_extension_splitting_monic_over
          (A := B) (P := (P (Fin.last n)).map (algebraMap R B)) hlast_monic
      letI : CommRing C := hCComm
      letI : Algebra B C := hCAlg
      letI : Algebra R C := RingHom.toAlgebra ((algebraMap B C).comp (algebraMap R B))
      letI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun x ↦ rfl
      letI : Module.Finite B C := hCfinite
      letI : Module.Free B C := hCfree
      letI : Module.Finite R C := Module.Finite.trans B C
      letI : Module.Free R C := Module.Free.trans (R := R) (S := B) (M := C)
      have hinjRC : Function.Injective (algebraMap R C) :=
        finiteFree_injective_tower (A := R) (B := B) (C := C) hinjRB hinjBC
      let dTotal : Fin (n + 1) → ℕ := Fin.lastCases dLast dB
      let αTotal : ∀ i : Fin (n + 1), Fin (dTotal i) → C := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · let e : Fin (dTotal (Fin.last n)) ≃ Fin dLast := finCongr (by simp [dTotal])
          exact fun j ↦ βLast (e j)
        · intro i
          let e : Fin (dTotal i.castSucc) ≃ Fin (dB i) := finCongr (by simp [dTotal])
          exact fun j ↦ algebraMap B C (βB i (e j))
      refine ⟨C, inferInstance, inferInstance, hinjRC, inferInstance, inferInstance,
        dTotal, αTotal, ?_⟩
      intro i
      refine Fin.lastCases ?_ ?_ i
      · -- The last polynomial is split directly over the current base ring `B`.
        calc
          Polynomial.map (algebraMap R C) (P (Fin.last n)) =
              ∏ j : Fin dLast, (Polynomial.X - Polynomial.C (βLast j)) := by
                simpa [Polynomial.map_map, IsScalarTower.algebraMap_eq R B C] using hsplitLast
          _ = ∏ j : Fin (dTotal (Fin.last n)),
                (Polynomial.X - Polynomial.C (αTotal (Fin.last n) j)) := by
                symm
                simpa [dTotal, αTotal] using
                  prod_X_sub_C_finCongr (A := C) (h := by simp [dTotal]) (β := βLast)
      · intro i
        -- Earlier splittings are transported once through the tower `R → B → C`.
        calc
          Polynomial.map (algebraMap R C) (P i.castSucc) =
              ∏ j : Fin (dB i), (Polynomial.X - Polynomial.C (algebraMap B C (βB i j))) := by
                simpa [Pinit] using
                  split_factorization_map_to_tower
                    (A := R) (B := B) (C := C) (P := P i.castSucc) (β := βB i) (h := hsplitB i)
          _ = ∏ j : Fin (dTotal i.castSucc),
                (Polynomial.X - Polynomial.C (αTotal i.castSucc j)) := by
                symm
                simpa [dTotal, αTotal] using
                  prod_X_sub_C_finCongr (A := C) (h := by simp [dTotal]) (β := fun j ↦
                    algebraMap B C (βB i j))

/-- Helper for Lemma 15.21.3: if the base ring is subsingleton, the theorem is realized by the
zero-variable quotient over the universe-lifted base ring. -/
lemma subsingleton_base_zero_variable_split_quotient [Subsingleton R] :
    ∃ (n : ℕ) (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R'),
      ∃ φ :
        (MvPolynomial (Fin n) R' ⧸
          Ideal.span
            (Set.range fun i ↦
              ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))) →ₐ[R']
          (R' ⊗[R] S),
        Function.Surjective φ := by
  let R' := ULift.{v} R
  let d : Fin 0 → ℕ := fun i ↦ nomatch i
  let α : ∀ i, Fin (d i) → R' := fun i ↦ nomatch i
  have hinj : Function.Injective (algebraMap R R') := by
    -- The universe lift does not identify distinct base-ring elements.
    intro r s hrs
    exact congrArg ULift.down hrs
  have hzero_one : (0 : S) = 1 := by
    simpa using congrArg (algebraMap R S) (Subsingleton.elim (0 : R) 1)
  haveI : Subsingleton S := subsingleton_of_zero_eq_one hzero_one
  haveI : Subsingleton (R' ⊗[R] S) := by infer_instance
  have hspan :
      Ideal.span
        (Set.range fun i : Fin 0 ↦
          ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j))) = ⊥ := by
    -- There are no variables, hence no defining split relations.
    simp [d, α]
  let θ : MvPolynomial (Fin 0) R' →ₐ[R'] (R' ⊗[R] S) :=
    MvPolynomial.aeval (fun i ↦ nomatch i)
  have hθ :
      ∀ p : MvPolynomial (Fin 0) R',
        p ∈
            Ideal.span
              (Set.range fun i : Fin 0 ↦
                ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j))) →
          θ p = 0 := by
    -- After identifying the relation ideal with `⊥`, every element in it is zero.
    intro p hp
    rw [hspan] at hp
    have hp0 : p = 0 := by
      simpa using hp
    simpa [hp0]
  let φ :
      (MvPolynomial (Fin 0) R' ⧸
          Ideal.span
            (Set.range fun i ↦
              ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))) →ₐ[R']
        (R' ⊗[R] S) :=
    Ideal.Quotient.liftₐ _ θ hθ
  have hsurj : Function.Surjective φ := by
    -- The tensor target is subsingleton, so any element is the image of `0`.
    intro z
    refine ⟨0, Subsingleton.elim _ _⟩
  exact ⟨0, R', inferInstance, inferInstance, hinj, inferInstance, inferInstance, d, α, φ,
    hsurj⟩

/-- Helper for Lemma 15.21.3: after base change, evaluating a polynomial cover at the tensors
`1 ⊗ ψ(X i)` sends coefficient-wise base change to `1 ⊗ ψ(p)`. -/
lemma aeval_map_eq_tmul_of_cover
    {n : ℕ} {R' : Type*} [CommRing R'] [Algebra R R']
    (ψ : MvPolynomial (Fin n) R →ₐ[R] S) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))
        (p.map (algebraMap R R')) =
      (1 : R') ⊗ₜ[R] ψ p := by
  have hcomp :
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).comp ψ) =
        MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i)) := by
    -- Both algebra maps are characterized by the same images of the polynomial variables.
    simpa using
      (MvPolynomial.aeval_unique
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).comp ψ))
  calc
    MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))
        (p.map (algebraMap R R')) =
      MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i)) p := by
        -- `MvPolynomial.aeval_map_algebraMap` removes the coefficient base change.
        simpa using
          (MvPolynomial.aeval_map_algebraMap (R := R) (A := R') (B := R' ⊗[R] S)
            (x := fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i)) p)
    _ = ((Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).comp ψ) p := by
      rw [hcomp]
    _ = (1 : R') ⊗ₜ[R] ψ p := by
      simp [Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.21.3: evaluating a product of split linear factors at `x` gives the
corresponding split product in the target algebra. -/
lemma aeval_prod_X_sub_C
    {R' : Type*} {A : Type*} [CommRing R'] [CommRing A] [Algebra R' A]
    {d : ℕ} (x : A) (β : Fin d → R') :
    Polynomial.aeval x (∏ j : Fin d, (Polynomial.X - Polynomial.C (β j))) =
      ∏ j : Fin d, (x - algebraMap R' A (β j)) := by
  -- Evaluate factorwise, then simplify the image of each linear factor.
  simp [Polynomial.aeval_def]

/-- Helper for Lemma 15.21.3: the multivariate split relation is the univariate evaluation of the
already-split polynomial at the chosen variable `X i`. -/
lemma split_relation_eq_polynomial_aeval
    {n : ℕ} {R' : Type (max u v)} [CommRing R'] [Algebra R R']
    (P : Fin n → R[X]) (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R')
    (hsplit : ∀ i, (P i).map (algebraMap R R') =
      ∏ j : Fin (d i), (Polynomial.X - Polynomial.C (α i j)))
    (i : Fin n) :
    ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) =
      Polynomial.aeval (MvPolynomial.X i) ((P i).map (algebraMap R R')) := by
  calc
    ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) =
        Polynomial.aeval (MvPolynomial.X i)
          (∏ j : Fin (d i), (Polynomial.X - Polynomial.C (α i j))) := by
      -- Normalize the split relation as univariate polynomial evaluation at `X i`.
      symm
      simpa using
        (aeval_prod_X_sub_C (R' := R') (A := MvPolynomial (Fin n) R')
          (x := MvPolynomial.X i) (β := α i))
    _ = Polynomial.aeval (MvPolynomial.X i) ((P i).map (algebraMap R R')) := by
      -- Replace the explicit product by the chosen splitting factorization.
      rw [← hsplit i]

/-- Helper for Lemma 15.21.3: an `R'`-algebra hom commutes with univariate polynomial evaluation
over `R'`. -/
lemma algHom_apply_polynomial_aeval
    {R' : Type*} {A : Type*} {B : Type*}
    [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R' A] [Algebra R' B]
    (φ : A →ₐ[R'] B) (x : A) (q : R'[X]) :
    φ (Polynomial.aeval x q) = Polynomial.aeval (φ x) q := by
  -- Push evaluation through the algebra hom and simplify the scalar-map composite.
  simpa [Polynomial.aeval_def] using
    (Polynomial.hom_eval₂ q (algebraMap R' A) φ x)

/-- Helper for Lemma 15.21.3: after base change, evaluating `p.map (algebraMap R R')` at
`1 ⊗ s` is the same as tensoring the original evaluation of `p` at `s`. -/
lemma polynomial_aeval_map_eq_tmul
    {R' : Type*} [CommRing R'] [Algebra R R']
    (s : S) (p : R[X]) :
    Polynomial.aeval ((1 : R') ⊗ₜ[R] s) (p.map (algebraMap R R')) =
      (1 : R') ⊗ₜ[R] Polynomial.aeval s p := by
  let F : R[X] →+* (R' ⊗[R] S) :=
    (Polynomial.aeval ((1 : R') ⊗ₜ[R] s)).toRingHom.comp
      (Polynomial.mapRingHom (algebraMap R R'))
  let G : R[X] →+* (R' ⊗[R] S) :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom.comp
      (Polynomial.aeval s).toRingHom
  have hFG : F = G := by
    -- Both polynomial ring homs agree on coefficients and on `X`.
    ext a <;> simp [F, G, Polynomial.aeval_def, Algebra.TensorProduct.includeRight_apply,
      IsScalarTower.algebraMap_eq R R' (R' ⊗[R] S)]
  -- Evaluate the equality of ring homs on the chosen polynomial.
  simpa [F, G, Algebra.TensorProduct.includeRight_apply] using
    congrArg (fun φ : R[X] →+* (R' ⊗[R] S) ↦ φ p) hFG

/-- Helper for Lemma 15.21.3: each split relation maps to zero under the base-changed evaluation
map once the corresponding annihilator polynomial vanishes on the chosen generator. -/
-- TODO: rewrite the relation as the image of `(P i).map (algebraMap R R')` under evaluation at
-- `X i ↦ 1 ⊗ ψ (X i)`, then invoke `aeval_map_eq_tmul_of_cover` and the annihilator equation
-- `hPaeval i`.
lemma split_relation_mem_ker_baseChange_aeval
    {n : ℕ} {R' : Type (max u v)} [CommRing R'] [Algebra R R']
    (ψ : MvPolynomial (Fin n) R →ₐ[R] S) (P : Fin n → R[X]) (d : Fin n → ℕ)
    (α : ∀ i, Fin (d i) → R')
    (hsplit : ∀ i, (P i).map (algebraMap R R') =
      ∏ j : Fin (d i), (Polynomial.X - Polynomial.C (α i j)))
    (hPaeval : ∀ i, Polynomial.aeval (ψ (MvPolynomial.X i)) (P i) = 0) :
    ∀ i,
      ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈
        RingHom.ker
          (MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))).toRingHom := by
  intro i
  change
    MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))
        (∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j))) = 0
  -- Route correction: first rewrite the split relation as univariate polynomial evaluation at
  -- `X i`; this isolates the remaining blocker to commuting `Polynomial.aeval` with `θ`.
  rw [split_relation_eq_polynomial_aeval (R := R) (P := P) (d := d) (α := α) hsplit i]
  -- Commute the polynomial evaluation through `θ`, then rewrite the coefficient base change.
  calc
    MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))
        (Polynomial.aeval (MvPolynomial.X i) ((P i).map (algebraMap R R'))) =
      Polynomial.aeval ((1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))
        ((P i).map (algebraMap R R')) := by
          simpa using
            (algHom_apply_polynomial_aeval
              (φ := MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i)))
              (x := MvPolynomial.X i) (q := (P i).map (algebraMap R R')))
    _ = (1 : R') ⊗ₜ[R] Polynomial.aeval (ψ (MvPolynomial.X i)) (P i) := by
      rw [polynomial_aeval_map_eq_tmul (R := R) (S := S) (R' := R') (s := ψ (MvPolynomial.X i))
        (p := P i)]
    _ = 0 := by
      simp [hPaeval i]

/- Domain sampling for this item:
* primary domain: finite polynomial quotient models for finite algebras after finite free base
  change;
* sampled declarations: `exists_finiteFree_extension_with_monic_linear_factor`,
  `Algebra.FiniteType.iff_quotient_mvPolynomial''`, `MvPolynomial.aeval`, and
  `Algebra.TensorProduct.commRight`;
* layer triage:
  - `source-facing`: the existence of a finite free injective base change after which `S` is a
    quotient of a split polynomial algebra;
  - `core/canonical`: `Algebra.FiniteType.iff_quotient_mvPolynomial''` for quotient presentations
    by polynomial algebras, together with the canonical base-change owner `R' ⊗[R] S`;
  - `source-facing owner`: the quotient ring
    `MvPolynomial (Fin n) R' ⧸ Ideal.span (Set.range fun i ↦ ∏ j, (X i - C (α i j)))`
    together with its canonical `R'`-algebra map to `R' ⊗[R] S`;
  - `bridge/view`: the textbook right-tensor presentation `S ⊗[R] R'`, identified with the chosen
    owner by `Algebra.TensorProduct.commRight`.
* owner decision: keep the source-facing split quotient presentation, but phrase it directly as an
  `R'`-algebra quotient of the canonical base-change owner `R' ⊗[R] S`; the unsplit polynomial
  quotient owner already lives upstream in `Algebra.FiniteType.iff_quotient_mvPolynomial''`, so
  this file should add only the extra split-relations content.
* primitive data: the finite free injective extension `R → R'`, the arities `d`, and the chosen
  roots `α`;
* derived API: the quotient type and its surjective map to `R' ⊗[R] S`, obtained from
  `MvPolynomial.aeval` followed by the canonical ideal quotient lift; the right-tensor textbook
  form is only a bridge via tensor commutativity.
  -/

-- Proof sketch: choose finitely many generators `x₁, …, xₙ` of the finite `R`-algebra `S`. For
-- each generator, pick a monic annihilating polynomial over `R`, then apply Lemma `15.21.2`
-- repeatedly to obtain a finite free `R`-algebra `R'` over which all these polynomials split
-- completely. After base change, send `X i` to `1 ⊗ₜ[R] xᵢ` in the canonical base-change owner
-- `R' ⊗[R] S`; the split relations vanish, so `MvPolynomial.aeval` factors through the quotient
-- and remains surjective.
/-- Lemma 15.21.3: after a finite free injective base change `R → R'`, the canonical base-changed
algebra `R' ⊗[R] S` (equivalently the textbook `S ⊗[R] R'`) is a quotient of a split polynomial
algebra `R'[T₁, …, Tₙ] / (P₁(T₁), …, Pₙ(Tₙ))`, where each `Pᵢ` is a product of linear factors over
`R'`; the equivalence with `S ⊗[R] R'` is the tensor-symmetry bridge
`Algebra.TensorProduct.commRight`. -/
theorem exists_finiteFree_baseChange_surjective_splitPolynomialQuotient
    :
    ∃ (n : ℕ) (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R'),
      ∃ φ :
        (MvPolynomial (Fin n) R' ⧸
          Ideal.span
            (Set.range fun i ↦
              ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))) →ₐ[R']
          (R' ⊗[R] S),
        Function.Surjective φ := by
  -- Start from a finite polynomial presentation of the finite `R`-algebra `S`.
  obtain ⟨n, ψ, hψ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType R S)
  -- A finite ring map is integral, so each chosen generator satisfies a monic equation.
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  rcases subsingleton_or_nontrivial R with hR | hR
  · -- TODO: reduce the subsingleton base-ring case to a zero-variable quotient and the
    -- subsingleton tensor product. This is now packaged in the dedicated zero-variable helper.
    letI : Subsingleton R := hR
    exact subsingleton_base_zero_variable_split_quotient (R := R) (S := S)
  · letI : Nontrivial R := hR
    have hxIntegral : ∀ i : Fin n, IsIntegral R (ψ (X i)) := by
      intro i
      exact Algebra.IsIntegral.isIntegral (ψ (MvPolynomial.X i))
    choose P hPmonic hPne_one hPaeval using
      fun i : Fin n ↦ exists_monic_ne_one_annihilator (x := ψ (MvPolynomial.X i)) (hxIntegral i)
    -- Route correction: isolate polynomial-transport and tower injectivity first, then reduce the
    -- source proof to the two structural steps `common splitting extension` and `kernel descent`.
    obtain ⟨R', hR'Comm, hR'Alg, hinj, hR'finite, hR'free, d, α, hsplit⟩ :=
      exists_injective_finiteFree_extension_splitting_family (R := R) P hPmonic
    letI : CommRing R' := hR'Comm
    letI : Algebra R R' := hR'Alg
    letI : Module.Finite R R' := hR'finite
    letI : Module.Free R R' := hR'free
    let θ : MvPolynomial (Fin n) R' →ₐ[R'] (R' ⊗[R] S) :=
      MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))
    have hθsurj : Function.Surjective θ := by
      -- Surjectivity is preserved after base change because `ψ` already surjects onto `S`.
      intro z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · exact ⟨0, by simp [θ]⟩
      · intro r' s
        obtain ⟨p, rfl⟩ := hψ s
        refine ⟨MvPolynomial.C r' * p.map (algebraMap R R'), ?_⟩
        -- Evaluate the coefficient part and the polynomial part separately.
        simp [θ, aeval_map_eq_tmul_of_cover, Algebra.TensorProduct.tmul_mul_tmul]
      · intro z₁ z₂ hz₁ hz₂
        rcases hz₁ with ⟨p₁, rfl⟩
        rcases hz₂ with ⟨p₂, rfl⟩
        exact ⟨p₁ + p₂, by simp [θ]⟩
    let I : Ideal (MvPolynomial (Fin n) R') :=
      Ideal.span
        (Set.range fun i ↦
          ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))
    have hIle : I ≤ RingHom.ker θ.toRingHom := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      change
        ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)) ∈
          RingHom.ker
            (MvPolynomial.aeval (fun i ↦ (1 : R') ⊗ₜ[R] ψ (MvPolynomial.X i))).toRingHom
      exact
        split_relation_mem_ker_baseChange_aeval
          (R := R) (S := S) (R' := R') ψ P d α hsplit hPaeval i
    let φ : (MvPolynomial (Fin n) R' ⧸ I) →ₐ[R'] (R' ⊗[R] S) :=
      Ideal.Quotient.liftₐ I θ fun p hp ↦ hIle hp
    have hφsurj : Function.Surjective φ := by
      -- Every tensor has a preimage through `θ`, hence also through the quotient lift `φ`.
      intro z
      rcases hθsurj z with ⟨p, hp⟩
      refine ⟨Ideal.Quotient.mk I p, ?_⟩
      simpa [φ] using hp
    refine ⟨n, R', inferInstance, inferInstance, hinj, inferInstance, inferInstance, d, α, ?_⟩
    -- The quotient presentation now follows from the descended surjective evaluation map.
    simpa [I] using
      (show ∃ φ : (MvPolynomial (Fin n) R' ⧸ I) →ₐ[R'] (R' ⊗[R] S),
          Function.Surjective φ from ⟨φ, hφsurj⟩)

end
