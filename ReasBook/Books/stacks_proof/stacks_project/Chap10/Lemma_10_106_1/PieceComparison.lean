import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_59_9
import stacks_proof.stacks_project.Chap10.Lemma_10_106_1.StageClassAPI

open IsLocalRing

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local notation "κ" => ResidueField R
local notation "grR" => idealAssociatedGradedRing (maximalIdeal R)

local instance pieceComparisonCommRingGrR : CommRing grR :=
  inferInstanceAs (CommRing (idealAssociatedGradedRing (maximalIdeal R)))

local instance pieceComparisonAlgebraGrR : Algebra κ grR :=
  inferInstance

local instance pieceComparisonSMulGrR : SMul κ grR where
  smul c z := algebraMap κ grR c * z

local instance pieceComparisonModuleGrR : Module κ grR := by
  let _ : Module grR grR := Semiring.toModule
  exact Module.compHom grR (algebraMap κ grR)

local instance pieceComparisonPieceModule (n : ℕ) :
    Module κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  exact inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n))

local instance pieceComparisonStageQuotientModule (n : ℕ) :
    Module κ
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
  exact inferInstanceAs
    (Module (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))))

local instance pieceComparisonStageQuotientScalarTower (n : ℕ) :
    IsScalarTower R κ
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
  exact inferInstanceAs
    (IsScalarTower R (R ⧸ maximalIdeal R)
      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))))

/-- Helper for Lemma 10.106.1: each owner grade of `grR` inherits the ambient residue-field
scalar action. -/
local instance pieceComparisonGradeSMul (n : ℕ) :
    SMul κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) :=
  -- Transport the residue-field scalar action from the textbook quotient piece through the
  -- canonical owner-grade/piece equivalence.
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  show SMul κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) from
    (e.toAddEquiv.module κ).toSMul

/-- Helper for Lemma 10.106.1: each owner grade of `grR` is a `κ`-module via the ambient scalar
action on `grR`. -/
local instance pieceComparisonGradeModule (n : ℕ) :
    Module κ (idealAssociatedGradedRingGrade (maximalIdeal R) n) :=
  -- Route correction: transport the module structure from the textbook quotient piece instead of
  -- rebuilding the stage-class action inside `grR`.
  let e := idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n
  e.toAddEquiv.module κ

/-- Helper for Lemma 10.106.1: the textbook quotient
`maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)` agrees with the intrinsic quotient
`maximalIdeal R ^ n / maximalIdeal R · maximalIdeal R ^ n`. -/
noncomputable def idealAssociatedGradedPiece_internal_quotient_equiv
    (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) ≃ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  -- Replace the intrinsic denominator by the next stage before passing to the quotient.
  Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [Submodule.mem_smul_top_iff]
    change ((x : R) ∈ maximalIdeal R •
        RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) ↔
      ((x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R (n + 1))
    rw [← mul_smul]
    rw [show maximalIdeal R * maximalIdeal R ^ n = maximalIdeal R ^ (n + 1) by
      rw [Ideal.mul_comm, ← pow_succ]])

/-- Helper for Lemma 10.106.1: the degree-`n` owner piece of `grR` identifies with the textbook
quotient `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`. -/
noncomputable abbrev idealAssociatedGradedRingGrade_equiv_piece_local (n : ℕ) :
    idealAssociatedGradedRingGrade (maximalIdeal R) n ≃ₗ[R]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  idealAssociatedGradedRingGrade_equiv_piece (R := R) (I := maximalIdeal R) n

/-- Helper for Lemma 10.106.1: on a stage representative, the local owner-grade equivalence is the
obvious quotient class modulo the next maximal-ideal power. -/
theorem idealAssociatedGradedRingGrade_equiv_piece_local_apply_stage (n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedRingGrade_equiv_piece_local (R := R) n
      ⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
        idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ =
        Submodule.Quotient.mk a := by
  -- This is the stage-level normal form needed later to compare polynomial evaluation with the
  -- textbook quotient `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`.
  simpa [idealAssociatedGradedRingGrade_equiv_piece_local] using
    idealAssociatedGradedRingGrade_equiv_piece_apply_stage (R := R) (I := maximalIdeal R) n a

/-- Helper for Lemma 10.106.1: the owner-grade/piece comparison is already linear over the
residue field. -/
noncomputable def idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (n : ℕ) :
    idealAssociatedGradedRingGrade (maximalIdeal R) n ≃ₗ[κ]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
  -- The owner grade now carries the transported `κ`-module structure, so the same additive
  -- equivalence becomes `κ`-linear without further transport data.
  (idealAssociatedGradedRingGrade_equiv_piece_local (R := R) n).toAddEquiv.linearEquiv κ

/-- Helper for Lemma 10.106.1: the residue-field-linear owner-grade/piece equivalence still sends
each stage class to its textbook quotient class. -/
theorem idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear_apply_stage (n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear (R := R) n
      ⟨idealAssociatedGradedStageClass (maximalIdeal R) n a,
        idealAssociatedGradedStageClass_mem_grade (maximalIdeal R) n a⟩ =
        Submodule.Quotient.mk a := by
  -- The `κ`-linear packaging has the same underlying function as the original owner-grade
  -- equivalence, so the stage representative formula is unchanged.
  simpa [idealAssociatedGradedRingGrade_equiv_piece_local_residueFieldLinear] using
    idealAssociatedGradedRingGrade_equiv_piece_local_apply_stage (R := R) n a

/-- Helper for Lemma 10.106.1: the internal quotient model for
`maximalIdeal R ^ n / maximalIdeal R · maximalIdeal R ^ n` is already `κ`-linearly equivalent to
the textbook associated graded piece `maximalIdeal R ^ n / maximalIdeal R ^ (n + 1)`. -/
noncomputable def idealAssociatedGradedPiece_internal_quotient_equiv_quotient
    (n : ℕ) :
    (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
        ((maximalIdeal R) •
          (⊤ : Submodule R
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) ≃ₗ[κ]
      RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n := by
  -- The quotient `κ = R ⧸ maximalIdeal R` acts on both sides through the same additive model, so
  -- the existing additive equivalence upgrades directly to a `κ`-linear equivalence.
  simpa using
    (AddEquiv.linearEquiv
      (A := κ)
      ((idealAssociatedGradedPiece_internal_quotient_equiv (R := R) n).symm.toAddEquiv)).symm

/-- Helper for Lemma 10.106.1: after identifying the intrinsic quotient with the textbook quotient,
a stage class is still represented by the same quotient element. -/
theorem idealAssociatedGradedPiece_internal_quotient_equiv_quotient_apply_stage
    (n : ℕ)
    (a : RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n) :
    idealAssociatedGradedPiece_internal_quotient_equiv_quotient (R := R) n
      (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk a :
          RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  -- The quotient equivalence only replaces the denominator by the equal next-stage submodule.
  rfl

/-- Helper for Lemma 10.106.1: the textbook associated graded piece has `κ`-length equal to the
Hilbert-Samuel `φ`-value of the maximal ideal. -/
private theorem idealAssociatedGradedPiece_length_over_quotient_eq_phi_local
    (n : ℕ) :
    Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
      Ideal.hilbertSamuelPhi (maximalIdeal R) R n := by
  let Q :=
    RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
      ((maximalIdeal R) •
        (⊤ : Submodule R
          (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))
  have hlengthQ :
      Module.length R Q = Module.length κ Q :=
    Module.length_eq_of_surjective
      (R := κ) (S := R) (M := Q) Ideal.Quotient.mk_surjective
  -- Compare first with the internal quotient model used in the definition of `φ`, then forget the
  -- base ring from `R` to `κ`.
  calc
    Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        Module.length κ Q := by
          exact
            (idealAssociatedGradedPiece_internal_quotient_equiv_quotient n).symm.length_eq
    _ = Module.length R Q := by
          symm
          exact hlengthQ
    _ = Ideal.hilbertSamuelPhi (maximalIdeal R) R n := by
          rfl

/-- Helper for Lemma 10.106.1: the degree-`n` associated graded piece of the maximal-ideal
filtration is finite-dimensional over the residue field. -/
private theorem idealAssociatedGradedPiece_moduleFinite_local
    (n : ℕ) :
    Module.Finite κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
  let I : Ideal R := maximalIdeal R
  let N : Submodule R R := RingTheory.Sequence.idealAssociatedGradedStage I R n
  let J : Submodule R R := RingTheory.Sequence.idealAssociatedGradedStage I R (n + 1)
  have hJN : J ≤ N := by
    -- The adic filtration is decreasing, so the `(n + 1)`st stage sits inside the `n`th stage.
    simpa [I, N, J, RingTheory.Sequence.idealAssociatedGradedStage] using
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_succ n)) :
        ((maximalIdeal R) ^ (n + 1) • (⊤ : Submodule R R)) ≤
          (maximalIdeal R ^ n • (⊤ : Submodule R R)))
  have hIdef : I.IsIdealOfDefinition := Ideal.maximalIdeal_isIdealOfDefinition
  have hlen_top :
      Module.length R (R ⧸ J) ≠ ⊤ := by
    exact
      (Module.length_ne_top_iff).2 <|
        by
          simpa [I, J, RingTheory.Sequence.idealAssociatedGradedStage] using
            Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
              (R := R) (M := R) I hIdef n
  have hlen_bottom :
      Module.length R (R ⧸ N) ≠ ⊤ := by
    cases n with
    | zero =>
        -- In degree zero the source quotient is `R ⧸ ⊤`, hence already the zero module.
        simpa [I, N, RingTheory.Sequence.idealAssociatedGradedStage]
    | succ n =>
        exact
          (Module.length_ne_top_iff).2 <|
            by
              simpa [I, N, RingTheory.Sequence.idealAssociatedGradedStage] using
                Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
                  (R := R) (M := R) I hIdef n
  have hdecomp :
      Module.length R (R ⧸ J) =
        Module.length R (R ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
    -- The short exact sequence
    -- `0 → N / J → R / J → R / N → 0`
    -- isolates the degree-`n` piece as the length difference of two Hilbert-Samuel quotients.
    simpa [N, J] using
      Ideal.length_quotient_eq_add_length_submodule_quotient_of_le
        (R := R) (M := R) hJN
  have hpiece_ne_top_R :
      Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) ≠ ⊤ := by
    intro htop
    have : Module.length R (R ⧸ J) = ⊤ := by
      rw [hdecomp, htop]
      simp
    exact hlen_top this
  have hpiece_ne_top_κ :
      Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) ≠ ⊤ := by
    -- The `κ`-length and the `R`-length agree on this quotient, so finiteness transfers across the
    -- residue-field scalar restriction.
    intro htop
    have : Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) = ⊤ := by
      have hcompare :
          Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
            Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
        have e :
            (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
              ((maximalIdeal R) •
                (⊤ : Submodule R
                  (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) ≃ₗ[κ]
              RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n :=
          idealAssociatedGradedPiece_internal_quotient_equiv_quotient n
        calc
          Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
              Module.length κ
                (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                  ((maximalIdeal R) •
                    (⊤ : Submodule R
                      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
                exact e.symm.length_eq
          _ = Module.length R
                (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                  ((maximalIdeal R) •
                    (⊤ : Submodule R
                      (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n)))) := by
                symm
                exact Module.length_eq_of_surjective
                  (R := κ) (S := R)
                  (M := RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n ⧸
                    ((maximalIdeal R) •
                      (⊤ : Submodule R
                        (RingTheory.Sequence.idealAssociatedGradedStage (maximalIdeal R) R n))))
                  Ideal.Quotient.mk_surjective
          _ = Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
                exact (idealAssociatedGradedPiece_internal_quotient_equiv (R := R) n).length_eq
      simpa [hcompare] using htop
    exact hpiece_ne_top_R this
  have hfiniteLength :
      IsFiniteLength κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
    rw [← Module.length_ne_top_iff]
    exact hpiece_ne_top_κ
  have hNoeth :
      IsNoetherian κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  let _ : IsNoetherian κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    hNoeth
  infer_instance

/-- Helper for Lemma 10.106.1: each degree piece of the maximal-ideal associated graded ring has
dimension equal to the Hilbert-Samuel `φ`-value. -/
theorem idealAssociatedGradedPiece_finrank_eq_phi_local (n : ℕ) :
    Module.finrank κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
      (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
  let _ :
      Module.Finite κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) :=
    idealAssociatedGradedPiece_moduleFinite_local n
  have hlength :
      Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        Ideal.hilbertSamuelPhi (maximalIdeal R) R n :=
    idealAssociatedGradedPiece_length_over_quotient_eq_phi_local n
  have hlength_toNat :
      (Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n)).toNat =
        Module.finrank κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) := by
    simpa using congrArg ENat.toNat
      (Module.length_eq_finrank κ
        (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n))
  -- Once the degree piece is known to be finite-dimensional over `κ`, taking `ENat.toNat`
  -- converts the length identity into the desired finrank identity.
  calc
    Module.finrank κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n) =
        (Module.length κ (RingTheory.Sequence.idealAssociatedGradedPiece (maximalIdeal R) R n)).toNat := by
          symm
          exact hlength_toNat
    _ = (Ideal.hilbertSamuelPhi (maximalIdeal R) R n).toNat := by
          exact congrArg ENat.toNat hlength

end
