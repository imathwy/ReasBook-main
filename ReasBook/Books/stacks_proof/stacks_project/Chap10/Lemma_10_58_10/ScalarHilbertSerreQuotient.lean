import stacks_proof.stacks_project.Chap10.Lemma_10_58_10.ScalarHilbertSerre

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

noncomputable section

universe u v

section

/-- Helper for Chap10 Lemma 10 58 10: the standard grading shifts integer scalar degrees by
addition in scalar quotient arguments. -/
local instance scalarQuotientNatVAddInt : AddAction ℕ ℤ where
  vadd n z := (n : ℤ) + z
  zero_vadd := by
    intro z
    change ((0 : ℕ) : ℤ) + z = z
    simp
  add_vadd := by
    intro m n z
    change (((m + n : ℕ) : ℤ) + z) = ((m : ℤ) + ((n : ℤ) + z))
    simp [Nat.cast_add, add_assoc]

variable {k : Type u} [Field k] {d : ℕ}
variable {M : Type v} [AddCommGroup M] [Module k M]
variable [Module (MvPolynomial (Fin d) k) M] [IsScalarTower k (MvPolynomial (Fin d) k) M]

local notation "S" => MvPolynomial (Fin d) k

/-- Helper for Chap10 Lemma 10 58 10: scalar quotient pieces are images of scalar graded pieces
under the quotient map by an `S`-submodule. -/
def scalarQuotientGrading (ℳ : ℤ → Submodule k M) (K : Submodule S M) (n : ℤ) :
    Submodule k (M ⧸ K) :=
  (ℳ n).map (K.mkQ.restrictScalars k)

/-- Helper for Chap10 Lemma 10 58 10: the scalar quotient piece is the range of the quotient map
restricted to the corresponding scalar degree piece. -/
lemma scalarQuotientGrading_eq_range_domRestrict
    (ℳ : ℤ → Submodule k M) (K : Submodule S M) (n : ℤ) :
    scalarQuotientGrading ℳ K n =
      LinearMap.range ((K.mkQ.restrictScalars k).domRestrict (ℳ n)) := by
  -- Normalize the quotient piece to the range form used by rank-nullity.
  rw [scalarQuotientGrading]
  symm
  exact LinearMap.range_domRestrict (ℳ n) (K.mkQ.restrictScalars k)

/-- Helper for Chap10 Lemma 10 58 10: the degree-`n` part of `K` and the kernel of the restricted
quotient map have the same image inside the ambient module. -/
lemma scalarSubmoduleDegreePiece_map_eq_kernel_map
    (ℳ : ℤ → Submodule k M) (K : Submodule S M) (n : ℤ) :
    ((ℳ n).comap ((K.restrictScalars k).subtype)).map ((K.restrictScalars k).subtype) =
      (LinearMap.ker ((K.mkQ.restrictScalars k).domRestrict (ℳ n))).map (ℳ n).subtype := by
  -- Both sides are the same intersection `K ∩ ℳ n`, written from opposite subtype owners.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨(y : M), hy⟩, ?_, rfl⟩
    change K.mkQ (y : M) = 0
    exact (Submodule.Quotient.mk_eq_zero K).2 y.2
  · rintro ⟨y, hy, rfl⟩
    have hyK : (y : M) ∈ K := by
      change K.mkQ (y : M) = 0 at hy
      exact (Submodule.Quotient.mk_eq_zero K).1 hy
    exact ⟨⟨(y : M), hyK⟩, y.2, rfl⟩

/-- Helper for Chap10 Lemma 10 58 10: scalar quotient degree pieces are finite-dimensional when
the source scalar degree pieces are finite-dimensional. -/
lemma scalarQuotientGrading_moduleFinite
    (ℳ : ℤ → Submodule k M) (K : Submodule S M)
    (hfinite : ∀ n, Module.Finite k (ℳ n)) (n : ℤ) :
    Module.Finite k (scalarQuotientGrading ℳ K n) := by
  let q : ℳ n →ₗ[k] M ⧸ K := (K.mkQ.restrictScalars k).domRestrict (ℳ n)
  let _ : Module.Finite k (ℳ n) := hfinite n
  -- The quotient piece is a range of a map out of a finite-dimensional source.
  rw [scalarQuotientGrading_eq_range_domRestrict (ℳ := ℳ) K n]
  infer_instance

/-- Helper for Chap10 Lemma 10 58 10: scalar quotient pieces inherit the graded action from the
ambient scalar pieces. -/
lemma scalarQuotientGrading_setLikeGradedSMul
    (ℳ : ℤ → Submodule k M) [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) ℳ]
    (K : Submodule S M) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k)
      (scalarQuotientGrading ℳ K) where
  smul_mem := by
    intro i j a x ha hx
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨a • y, SetLike.GradedSMul.smul_mem ha hy, ?_⟩
    -- The quotient action is represented by multiplying before taking the quotient class.
    change K.mkQ (a • y) = a • K.mkQ y
    exact (Submodule.Quotient.mk_smul K a y).symm

/-- Helper for Chap10 Lemma 10 58 10: scalar submodule degree pieces are finite-dimensional
whenever the ambient scalar degree pieces are finite-dimensional. -/
lemma scalarSubmoduleGrading_moduleFinite
    (ℳ : ℤ → Submodule k M) (K : Submodule S M)
    (hfinite : ∀ n, Module.Finite k (ℳ n)) (n : ℤ) :
    Module.Finite k ((ℳ n).comap ((K.restrictScalars k).subtype)) := by
  let f : ((ℳ n).comap ((K.restrictScalars k).subtype)) →ₗ[k] ℳ n :=
    { toFun := fun x ↦ ⟨(x : M), x.2⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  let _ : Module.Finite k (ℳ n) := hfinite n
  -- Embed the submodule piece into the finite ambient scalar piece.
  refine Module.Finite.of_injective f ?_
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ℳ n ↦ (z : M)) hxy

/-- Helper for Chap10 Lemma 10 58 10: scalar submodule degree pieces inherit the graded action
from the ambient scalar pieces. -/
lemma scalarSubmoduleGrading_setLikeGradedSMul
    (ℳ : ℤ → Submodule k M) [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k) ℳ]
    (K : Submodule S M) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin d) k)
      (fun n ↦ (ℳ n).comap ((K.restrictScalars k).subtype)) where
  smul_mem := by
    intro i j a x ha hx
    change (a • (x : M)) ∈ ℳ ((i : ℕ) +ᵥ j)
    -- Forgetting the subtype reduces the claim to the ambient graded action.
    exact SetLike.GradedSMul.smul_mem ha hx

omit [Module k M] [IsScalarTower k S M] in
/-- Helper for Chap10 Lemma 10 58 10: the quotient by `(a)M` is killed by multiplication by
`a`. -/
lemma quotient_smul_eq_zero_of_span_singleton_smul_top
    (a : S) (q : M ⧸ ((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M))) :
    a • q = 0 := by
  obtain ⟨m, rfl⟩ :=
    Submodule.mkQ_surjective (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M))) q
  change (((Ideal.span ({a} : Set S)) • (⊤ : Submodule S M))).mkQ (a • m) = 0
  -- The representative `a • m` lies in `(a)M`, so its quotient class vanishes.
  exact (Submodule.Quotient.mk_eq_zero _).2 (by
    rw [Submodule.ideal_span_singleton_smul]
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨m, by simp, rfl⟩)

/-- Helper for Chap10 Lemma 10 58 10: the scalar degree piece splits in dimension as the part
inside a submodule plus the corresponding scalar quotient piece. -/
lemma scalarHomogeneousSubmodule_finrank_add
    (ℳ : ℤ → Submodule k M) (K : Submodule S M)
    (hfinite : ∀ n, Module.Finite k (ℳ n)) (n : ℤ) :
    (Module.finrank k (ℳ n) : ℤ) =
      (Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) : ℤ) +
        (Module.finrank k (scalarQuotientGrading ℳ K n) : ℤ) := by
  let q : ℳ n →ₗ[k] M ⧸ K := (K.mkQ.restrictScalars k).domRestrict (ℳ n)
  let _ : Module.Finite k (ℳ n) := hfinite n
  have hker_finrank :
      Module.finrank k (LinearMap.ker q) =
        Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) := by
    let eD := (K.restrictScalars k).equivSubtypeMap
      ((ℳ n).comap ((K.restrictScalars k).subtype))
    let eK := (ℳ n).equivSubtypeMap (LinearMap.ker q)
    have hmaps :
        ((ℳ n).comap ((K.restrictScalars k).subtype)).map
            ((K.restrictScalars k).subtype) =
          (LinearMap.ker q).map (ℳ n).subtype := by
      exact scalarSubmoduleDegreePiece_map_eq_kernel_map (ℳ := ℳ) K n
    -- Transport both subtype presentations of `K ∩ ℳ n` to the same ambient submodule.
    calc
      Module.finrank k (LinearMap.ker q) =
          Module.finrank k ((LinearMap.ker q).map (ℳ n).subtype) := by
            exact LinearEquiv.finrank_eq eK
      _ = Module.finrank k
            (((ℳ n).comap ((K.restrictScalars k).subtype)).map
              ((K.restrictScalars k).subtype)) := by
            rw [hmaps]
      _ = Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) := by
            exact (LinearEquiv.finrank_eq eD).symm
  have hrange_finrank :
      Module.finrank k (LinearMap.range q) =
        Module.finrank k (scalarQuotientGrading ℳ K n) := by
    rw [scalarQuotientGrading_eq_range_domRestrict (ℳ := ℳ) K n]
  have hnat :
      Module.finrank k (ℳ n) =
        Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) +
          Module.finrank k (scalarQuotientGrading ℳ K n) := by
    -- Rank-nullity for the restricted quotient map gives the additive dimension formula.
    calc
      Module.finrank k (ℳ n) =
          Module.finrank k (LinearMap.range q) + Module.finrank k (LinearMap.ker q) := by
            rw [LinearMap.finrank_range_add_finrank_ker q]
      _ = Module.finrank k (scalarQuotientGrading ℳ K n) +
          Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) := by
            rw [hrange_finrank, hker_finrank]
      _ = Module.finrank k ((ℳ n).comap ((K.restrictScalars k).subtype)) +
          Module.finrank k (scalarQuotientGrading ℳ K n) := by
            rw [add_comm]
  exact_mod_cast hnat

end
