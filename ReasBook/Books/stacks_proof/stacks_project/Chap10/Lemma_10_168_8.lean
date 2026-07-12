import StacksProject_2024.Chap10.Lemma_10_127_7.BackendComparison
import StacksProject_2024.Chap10.Lemma_10_138_5
import StacksProject_2024.Chap10.Lemma_10_138_15
import StacksProject_2024.Chap10.Lemma_10_168_5.DirectedRingLimit
import StacksProject_2024.Chap10.Lemma_10_168_5.TensorColimitDirectLimit
import StacksProject_2024.Chap10.Lemma_10_168_6
import StacksProject_2024.Chap10.Lemma_10_168_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TensorProduct

universe u v w

section

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ : Type w} [CommRing B₀] [Algebra (A i₀) B₀]
variable {C₀ : Type w} [CommRing C₀] [Algebra (A i₀) C₀]

local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

omit [IsDirected I (· ≤ ·)] in
/-- Helper for Chap10 Lemma 10 168 8: a witness over the cofinal tail above `i₀` unpacks to the
corresponding ambient stage witness with its lower-bound proof. -/
lemma existsStageOfTailProperty
    {P : ∀ i : I, i₀ ≤ i → Prop}
    (htail : ∃ j : Set.Ici i₀, P j.1 j.2) :
    ∃ (j : I) (hij : i₀ ≤ j), P j hij := by
  -- Proof comment: a tail index already stores both the ambient stage and the proof that the
  -- stage lies above `i₀`.
  obtain ⟨j, hj⟩ := htail
  exact ⟨j.1, j.2, hj⟩

/-- Helper for Chap10 Lemma 10 168 8: the cofinal tail above `i₀` is nonempty, with distinguished
point the base stage itself. -/
local instance tail_nonempty_168_8 : Nonempty (Set.Ici i₀) :=
  ⟨⟨i₀, le_rfl⟩⟩

/-- Helper for Chap10 Lemma 10 168 8: the cofinal tail above `i₀` remains a directed order. -/
local instance tail_isDirectedOrder_168_8 : IsDirectedOrder (Set.Ici i₀) :=
  tail_index_isDirected (i₀ := i₀)

/-- Helper for Chap10 Lemma 10 168 8: the preorder category on the tail above `i₀` is filtered,
which is the categorical input needed by the filtered-colimit smooth-model theorem. -/
local instance tail_isFiltered_168_8 : IsFiltered (Set.Ici i₀) :=
  CategoryTheory.isFiltered_of_directed_le_nonempty (Set.Ici i₀)

/-- Helper for Chap10 Lemma 10 168 8: every canonical stage tensor base-change map is finitely
presented once the original stage map `φ₀` is finitely presented. -/
lemma stageTensorMapFinitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).FinitePresentation := by
  -- Proof comment: this is exactly the tail-indexed finite-presentation descent wrapper already
  -- proved in `Lemma_10_168_6`.
  simpa using
    literal_stage_tensor_finitePresentation A f φ₀ hfp j

/-- Helper for Chap10 Lemma 10 168 8: the target ring `C₀ ⊗[A i₀] A j.1` is finitely presented
over the source tensor stage `B₀ ⊗[A i₀] A j.1`. -/
lemma stageTensorTargetAlgebraFinitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let S := B₀ ⊗[A i₀] A j.1
    let T := C₀ ⊗[A i₀] A j.1
    letI : Algebra S T :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
    Algebra.FinitePresentation S T := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let S := B₀ ⊗[A i₀] A j.1
  let T := C₀ ⊗[A i₀] A j.1
  letI : Algebra S T :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
  have hmap :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).FinitePresentation := by
    -- Proof comment: first reuse the map-level finite-presentation descent helper at the chosen
    -- tail stage.
    exact stageTensorMapFinitePresentation A f φ₀ hfp j
  -- Proof comment: unfold the owner predicate once so the stage tensor target acquires its
  -- algebra-level finite-presentation instance over the stage tensor source.
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation, S, T] using hmap

/-- Helper for Chap10 Lemma 10 168 8: the map-level finite-presentation hypothesis on `φ₀`
matches the algebra-level finite-presentation instance on `C₀` over `B₀`. -/
lemma algebraFinitePresentationOfHomFinitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    Algebra.FinitePresentation B₀ C₀ := by
  -- Proof comment: unfold the owner predicates once so the map-level and algebra-level
  -- formulations coincide.
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using hfp

/-- Helper for Chap10 Lemma 10 168 8: a finitely presented `B₀`-algebra can be replaced by one
explicit finite polynomial quotient model. -/
lemma finitePresentationQuotientModel
    {D : Type*} [CommRing D] [Algebra B₀ D]
    (hD : Algebra.FinitePresentation B₀ D) :
    ∃ (n c : ℕ) (fs : Fin c → MvPolynomial (Fin n) B₀),
      Nonempty ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)) ≃ₐ[B₀] D) := by
  letI : Algebra.FinitePresentation B₀ D := hD
  -- Proof comment: unwrap the standard finite-presentation witness and choose one finite family
  -- of generators for the presentation kernel.
  obtain ⟨n, π, hπsurj, hπkerfg⟩ :=
    (Algebra.FinitePresentation.out :
      ∃ (n : ℕ) (π : MvPolynomial (Fin n) B₀ →ₐ[B₀] D),
        Function.Surjective π ∧ (RingHom.ker π.toRingHom).FG)
  obtain ⟨c, fs, hfs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hπkerfg
  -- Proof comment: first rewrite the quotient by `ker π` as the quotient by the chosen explicit
  -- relations, then finish with the canonical quotient-by-kernel equivalence.
  exact ⟨n, c, fs, ⟨(Ideal.quotientEquivAlgOfEq B₀ hfs).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπsurj)⟩⟩

/-- Helper for Chap10 Lemma 10 168 8: base-changing an explicit polynomial quotient model from
`B₀` to the tensor source `B₀ ⊗[A i₀] R'` gives the corresponding explicit quotient over the
base-changed coefficient ring. -/
lemma presentationBaseChangeAlgEquiv
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (R' : Type*) [CommRing R'] [Algebra (A i₀) R'] :
    let S := B₀ ⊗[A i₀] R'
    letI : Algebra S ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)) ⊗[B₀] S) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      (((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)) ⊗[B₀] S) ≃ₐ[S]
        (MvPolynomial (Fin n) S ⧸
          Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ S) (fs i)))) := by
  let S := B₀ ⊗[A i₀] R'
  letI : Algebra S ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)) ⊗[B₀] S) :=
    Algebra.TensorProduct.rightAlgebra
  let ePoly : S ⊗[B₀] MvPolynomial (Fin n) B₀ ≃ₐ[S] MvPolynomial (Fin n) S :=
    MvPolynomial.algebraTensorAlgEquiv B₀ S
  have hgen :
      ∀ i,
        ePoly (Algebra.TensorProduct.includeRight (fs i)) =
          MvPolynomial.map (algebraMap B₀ S) (fs i) := by
    intro i
    -- Proof comment: the tensor/polynomial equivalence sends each chosen relation to its
    -- coefficientwise image in the polynomial ring over the tensor source.
    rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  -- Proof comment: first commute quotient with the tensor product, then identify the tensor
  -- polynomial ring with the polynomial ring over the base-changed coefficients.
  exact ⟨((Algebra.TensorProduct.commRight B₀ S
      (MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs))).symm.trans
    (Algebra.TensorProduct.tensorQuotientEquiv S
      (MvPolynomial (Fin n) B₀) S (Ideal.span (Set.range fs)))).trans
    (Ideal.quotientEquivAlg _ _ ePoly <| by
      rw [Ideal.map_span, Ideal.map_span, Set.image_image]
      apply congrArg Ideal.span
      ext q
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨fs i, ⟨i, rfl⟩, hgen i⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hgen i).symm⟩)⟩

/-- Helper for Chap10 Lemma 10 168 8: base-changing the square-zero quotient
`MvPolynomial (Fin n) B₀ ⧸ (Ideal.span (Set.range fs)) ^ 2` from `B₀` to the tensor source
`B₀ ⊗[A i₀] R'` gives the corresponding square-zero quotient over the base-changed coefficient
ring. -/
lemma presentationSquareBaseChangeAlgEquiv
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (R' : Type*) [CommRing R'] [Algebra (A i₀) R'] :
    let P₀ := MvPolynomial (Fin n) B₀
    let S := B₀ ⊗[A i₀] R'
    let I₀ : Ideal P₀ := Ideal.span (Set.range fs)
    let I : Ideal (MvPolynomial (Fin n) S) :=
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ S) (fs i))
    letI : Algebra S ((P₀ ⧸ I₀ ^ 2) ⊗[B₀] S) :=
      Algebra.TensorProduct.rightAlgebra
    Nonempty
      (((P₀ ⧸ I₀ ^ 2) ⊗[B₀] S) ≃ₐ[S]
        (MvPolynomial (Fin n) S ⧸ I ^ 2)) := by
  let P₀ := MvPolynomial (Fin n) B₀
  let S := B₀ ⊗[A i₀] R'
  let I₀ : Ideal P₀ := Ideal.span (Set.range fs)
  let I : Ideal (MvPolynomial (Fin n) S) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ S) (fs i))
  letI : Algebra S ((P₀ ⧸ I₀ ^ 2) ⊗[B₀] S) :=
    Algebra.TensorProduct.rightAlgebra
  let ePoly : S ⊗[B₀] P₀ ≃ₐ[S] MvPolynomial (Fin n) S :=
    MvPolynomial.algebraTensorAlgEquiv B₀ S
  let ιP : P₀ →ₐ[B₀] S ⊗[B₀] P₀ := Algebra.TensorProduct.includeRight
  have hgen :
      ∀ i,
        ePoly (ιP (fs i)) =
          MvPolynomial.map (algebraMap B₀ S) (fs i) := by
    intro i
    -- Proof comment: the tensor/polynomial equivalence still sends each chosen relation to its
    -- coefficientwise image after we replace the ordinary quotient by the square-zero quotient.
    rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul,
      one_smul]
  have hmap :
      I = Ideal.map ePoly.toRingHom (Ideal.map ιP.toRingHom I₀) := by
    -- Proof comment: the ordinary relation ideal after base change is unchanged from the
    -- non-square quotient case; only the later `Ideal.map_pow` step is new.
    change
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ S) (fs i)) =
        Ideal.map ePoly.toRingHom
          (Ideal.map ιP.toRingHom (Ideal.span (Set.range fs)))
    rw [Ideal.map_span, Ideal.map_span, Set.image_image]
    apply congrArg Ideal.span
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨fs i, ⟨i, rfl⟩, hgen i⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hgen i).symm⟩
  -- Proof comment: first commute quotient with tensor product as before; then identify the
  -- square relation ideal by pushing `Ideal.map_pow` through the ordinary base-change bridge.
  exact ⟨((Algebra.TensorProduct.commRight B₀ S (P₀ ⧸ I₀ ^ 2)).symm.trans
    (Algebra.TensorProduct.tensorQuotientEquiv S P₀ S (I₀ ^ 2))).trans
    (Ideal.quotientEquivAlg _ _ ePoly <| by
      rw [Ideal.map_pow, Ideal.map_pow]
      change I ^ 2 = Ideal.map ePoly.toRingHom (Ideal.map ιP.toRingHom I₀) ^ 2
      rw [hmap])⟩

/-- Helper for Chap10 Lemma 10 168 8: the standard `comm` plus `cancelBaseChange`
normalization identifies the literal tensor target `(B₀ ⊗[A i₀] R') ⊗[B₀] C₀` with the canonical
tensor target `C₀ ⊗[A i₀] R'`. -/
noncomputable abbrev tensorTargetRingEquiv
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (R' : Type*) [CommRing R'] [Algebra (A i₀) R'] :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S := B₀ ⊗[A i₀] R'
    (S ⊗[B₀] C₀) ≃+* (C₀ ⊗[A i₀] R') :=
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A i₀] R'
  (Algebra.TensorProduct.comm B₀ S C₀).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange (A i₀) B₀ C₀ C₀ R').toRingEquiv

/-- Helper for Chap10 Lemma 10 168 8: the standard `comm` plus `cancelBaseChange`
normalization on one tensor stage is compatible with the canonical source algebra map from
`B₀ ⊗[A i₀] A j.1`. -/
lemma stageTensorTargetRingEquiv_commutes
    (φ₀ : B₀ →ₐ[A i₀] C₀) (j : Set.Ici i₀) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let S := B₀ ⊗[A i₀] A j.1
    letI : Algebra S (C₀ ⊗[A i₀] A j.1) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
    ∀ x : S,
      tensorTargetRingEquiv A φ₀ (A j.1)
          (algebraMap S (S ⊗[B₀] C₀) x) =
        algebraMap S (C₀ ⊗[A i₀] A j.1) x := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let S := B₀ ⊗[A i₀] A j.1
  letI : Algebra S (C₀ ⊗[A i₀] A j.1) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
  intro x
  -- Proof comment: it is enough to check the compatibility on the tensor generators of the
  -- canonical source stage `S = B₀ ⊗[A i₀] A j.1`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b r
    change
      (Algebra.TensorProduct.cancelBaseChange (A i₀) B₀ C₀ C₀ (A j.1))
        ((1 : C₀) ⊗ₜ[B₀] ((b ⊗ₜ[A i₀] r : S))) =
      φ₀ b ⊗ₜ[A i₀] r
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simp [Algebra.smul_def]
    simpa using
      (show (algebraMap B₀ C₀) b ⊗ₜ[A i₀] r = φ₀ b ⊗ₜ[A i₀] r from rfl)
  · intro x y hx hy
    rw [TensorProduct.tmul_add, map_add, hx, hy]
    exact ((algebraMap S (C₀ ⊗[A i₀] A j.1)).map_add x y).symm

/-- Helper for Chap10 Lemma 10 168 8: the one-stage `comm` plus `cancelBaseChange`
normalization upgrades to an algebra equivalence over the canonical tensor source
`B₀ ⊗[A i₀] A j.1`. -/
noncomputable abbrev stageTensorTargetAlgEquiv
    (φ₀ : B₀ →ₐ[A i₀] C₀) (j : Set.Ici i₀) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let S := B₀ ⊗[A i₀] A j.1
    letI : Algebra S (C₀ ⊗[A i₀] A j.1) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
    (S ⊗[B₀] C₀) ≃ₐ[S] (C₀ ⊗[A i₀] A j.1) :=
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let S := B₀ ⊗[A i₀] A j.1
  letI : Algebra S (C₀ ⊗[A i₀] A j.1) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
  { __ := tensorTargetRingEquiv A φ₀ (A j.1)
    commutes' := stageTensorTargetRingEquiv_commutes A f φ₀ j }

/-- Helper for Chap10 Lemma 10 168 8: after base change to one tail stage, the fixed polynomial
presentation of `C₀` identifies with the canonical tensor target at that stage. -/
noncomputable abbrev stagePresentationTargetAlgEquiv
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (e₀ :
      letI : Algebra B₀ C₀ := φ₀.toAlgebra
      Nonempty ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)) ≃ₐ[B₀] C₀))
    (j : Set.Ici i₀) :
    letI : Algebra B₀ C₀ := φ₀.toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Sj := B₀ ⊗[A i₀] A j.1
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    letI : Algebra Sj (Q₀ ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra Sj (C₀ ⊗[A i₀] A j.1) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
    (Q₀ ⊗[B₀] Sj) ≃ₐ[Sj] (C₀ ⊗[A i₀] A j.1) :=
  letI : Algebra B₀ C₀ := φ₀.toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let Sj := B₀ ⊗[A i₀] A j.1
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  letI : Algebra Sj (Q₀ ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra Sj (C₀ ⊗[A i₀] A j.1) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
  let eQ₀ : Q₀ ≃ₐ[B₀] C₀ := e₀.some
  -- Proof comment: commute the fixed presentation to the left tensor factor, tensor the chosen
  -- presentation equivalence with the stage source, and finally normalize to the canonical
  -- tensor target at stage `j`.
  (((Algebra.TensorProduct.commRight B₀ Sj Q₀).symm).trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : Sj ≃ₐ[Sj] Sj) eQ₀)).trans
    (stageTensorTargetAlgEquiv A f φ₀ j)

/-- Helper for Chap10 Lemma 10 168 8: the square-zero quotient obtained by base-changing the
fixed presentation to one tail stage is the literal square-zero quotient over that stage. -/
noncomputable abbrev stageSquareZeroTargetAlgEquiv
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let P₀ := MvPolynomial (Fin n) B₀
    let Sj := B₀ ⊗[A i₀] A j.1
    let I₀ : Ideal P₀ := Ideal.span (Set.range fs)
    let Ij : Ideal (MvPolynomial (Fin n) Sj) :=
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ Sj) (fs i))
    letI : Algebra Sj ((P₀ ⧸ I₀ ^ 2) ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
    ((P₀ ⧸ I₀ ^ 2) ⊗[B₀] Sj) ≃ₐ[Sj] (MvPolynomial (Fin n) Sj ⧸ Ij ^ 2) :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: this is exactly the stage specialization of the already-proved square-zero
  -- base-change equivalence.
  (presentationSquareBaseChangeAlgEquiv
    (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) (A j.1)).some

/-- Helper for Chap10 Lemma 10 168 8: the normalized polynomial presentation map at one tail
stage has kernel equal to the explicit relation ideal obtained by base change. -/
lemma stagePresentationMap_ker
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Sj := B₀ ⊗[A i₀] A j.1
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Ij : Ideal (MvPolynomial (Fin n) Sj) :=
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ Sj) (fs i))
    letI : Algebra Sj (Q₀ ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
    let ePresj :
        (Q₀ ⊗[B₀] Sj) ≃ₐ[Sj] (MvPolynomial (Fin n) Sj ⧸ Ij) :=
      (presentationBaseChangeAlgEquiv
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) (A j.1)).some
    let qj : MvPolynomial (Fin n) Sj →ₐ[Sj] (Q₀ ⊗[B₀] Sj) :=
      ePresj.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Sj Ij)
    RingHom.ker qj.toRingHom = Ij := by
  dsimp
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let Sj := B₀ ⊗[A i₀] A j.1
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  let Ij : Ideal (MvPolynomial (Fin n) Sj) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ Sj) (fs i))
  letI : Algebra Sj (Q₀ ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
  let ePresj :
      (Q₀ ⊗[B₀] Sj) ≃ₐ[Sj] (MvPolynomial (Fin n) Sj ⧸ Ij) :=
    (presentationBaseChangeAlgEquiv
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) (A j.1)).some
  let qj : MvPolynomial (Fin n) Sj →ₐ[Sj] (Q₀ ⊗[B₀] Sj) :=
    ePresj.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Sj Ij)
  -- Proof comment: as at the limit stage, the normalized map is the quotient map by `Ij`
  -- followed by an algebra equivalence, so the kernel is unchanged.
  rw [show qj.toRingHom =
      ePresj.symm.toRingHom.comp (Ideal.Quotient.mkₐ Sj Ij).toRingHom by rfl]
  rw [RingHom.ker_equiv_comp, Ideal.Quotient.mkₐ_ker]

/-- Helper for Chap10 Lemma 10 168 8: the square-zero quotient attached to the normalized stage
presentation is canonically the base change of the fixed square-zero quotient over `B₀`. -/
noncomputable abbrev stagePresentationKerSquareAlgEquiv
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀ := MvPolynomial (Fin n) B₀
    let Q₀ := P₀ ⧸ Ideal.span (Set.range fs)
    let Ij : Ideal (MvPolynomial (Fin n) Sj) :=
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ Sj) (fs i))
    letI : Algebra Sj (Q₀ ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
    let ePresj :
        (Q₀ ⊗[B₀] Sj) ≃ₐ[Sj] (MvPolynomial (Fin n) Sj ⧸ Ij) :=
      (presentationBaseChangeAlgEquiv
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) (A j.1)).some
    let qj : MvPolynomial (Fin n) Sj →ₐ[Sj] (Q₀ ⊗[B₀] Sj) :=
      ePresj.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Sj Ij)
    (MvPolynomial (Fin n) Sj ⧸ RingHom.ker qj.toRingHom ^ 2) ≃ₐ[Sj]
      ((P₀ ⧸ Ideal.span (Set.range fs) ^ 2) ⊗[B₀] Sj) :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let Sj := B₀ ⊗[A i₀] A j.1
  let P₀ := MvPolynomial (Fin n) B₀
  let Q₀ := P₀ ⧸ Ideal.span (Set.range fs)
  let Ij : Ideal (MvPolynomial (Fin n) Sj) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ Sj) (fs i))
  letI : Algebra Sj (Q₀ ⊗[B₀] Sj) := Algebra.TensorProduct.rightAlgebra
  let ePresj :
      (Q₀ ⊗[B₀] Sj) ≃ₐ[Sj] (MvPolynomial (Fin n) Sj ⧸ Ij) :=
    (presentationBaseChangeAlgEquiv
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) (A j.1)).some
  let qj : MvPolynomial (Fin n) Sj →ₐ[Sj] (Q₀ ⊗[B₀] Sj) :=
    ePresj.symm.toAlgHom.comp (Ideal.Quotient.mkₐ Sj Ij)
  let eKerSq :
      (MvPolynomial (Fin n) Sj ⧸ RingHom.ker qj.toRingHom ^ 2) ≃ₐ[Sj]
        (MvPolynomial (Fin n) Sj ⧸ Ij ^ 2) :=
    Ideal.quotientEquivAlgOfEq Sj <| by
      rw [stagePresentationMap_ker (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j]
  -- Proof comment: first replace the kernel of the normalized presentation map by the explicit
  -- base-changed ideal `Ij`, then apply the stage square-zero base-change equivalence.
  eKerSq.trans
    (stageSquareZeroTargetAlgEquiv (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j).symm

/-- Helper for Chap10 Lemma 10 168 8: the canonical source-stage transition
`B₀ ⊗[A i₀] A j₀.1 → B₀ ⊗[A i₀] A j.1` is compatible with the original `B₀`-algebra structures.
-/
lemma tailTensorSourceTransition_isScalarTower
    {j₀ j : Set.Ici i₀} (hjj : j₀ ≤ j) :
    letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let S₀ := B₀ ⊗[A i₀] A j₀.1
    let S := B₀ ⊗[A i₀] A j.1
    letI : Algebra S₀ S :=
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f hjj)).toRingHom.toAlgebra
    IsScalarTower B₀ S₀ S := by
  dsimp
  letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let S₀ := B₀ ⊗[A i₀] A j₀.1
  let S := B₀ ⊗[A i₀] A j.1
  letI : Algebra S₀ S :=
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
      (tail_transition_algHom A f hjj)).toRingHom.toAlgebra
  -- Proof comment: both maps from `B₀` to the later tensor source send `b` to `b ⊗ 1`; the
  -- transition map carries the earlier `b ⊗ 1` to the same later-stage tensor.
  refine IsScalarTower.of_algebraMap_eq' (R := B₀) (S := S₀) (A := S) ?_
  ext b
  change (b ⊗ₜ[A i₀] (1 : A j.1) : S) =
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
      (tail_transition_algHom A f hjj))
      (b ⊗ₜ[A i₀] (1 : A j₀.1))
  simp

/-- Helper for Chap10 Lemma 10 168 8: tensoring the tail transition maps with `B₀` preserves the
directed-system composition law on the source-stage family. -/
lemma tailTensorSourceTransition_comp_transition
    {j₀ j k : Set.Ici i₀} (h₀j : j₀ ≤ j) (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    ((Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f hjk)).comp
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f h₀j))) =
      Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f (h₀j.trans hjk)) := by
  letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  -- Proof comment: on a pure tensor `b ⊗ a`, both composites send it to
  -- `b ⊗ f_{j₀k}(a)`, so tensor induction proves equality of the two tensor-source transition
  -- maps.
  apply AlgHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b a
    change b ⊗ₜ[A i₀] (f (↑j) (↑k) hjk ((f (↑j₀) (↑j) h₀j) a)) =
      b ⊗ₜ[A i₀] (f ↑j₀ ↑k (h₀j.trans hjk) a)
    congr 1
    let ds : DirectedSystem A (fun i j hij ↦ f i j hij) := inferInstance
    simpa using ds.map_map h₀j hjk a
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 168 8: the tail tensor-source stages
`B₀ ⊗[A i₀] A j.1` form a directed system under the tensor-transition maps. -/
lemma tailTensorSourceDirectedSystem :
    DirectedSystem
      (fun j : Set.Ici i₀ ↦
        letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
        B₀ ⊗[A i₀] A j.1)
      (fun j k hjk ↦
        letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
        letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
          (tail_transition_algHom A f hjk)).toRingHom) := by
  refine
    { map_self := ?_
      map_map := ?_ }
  · intro j x
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    -- Proof comment: on a pure tensor `b ⊗ a`, the transition along `j ≤ j` is the identity on
    -- the second factor, so tensor induction proves the whole source-stage map is the identity.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro b a
      change b ⊗ₜ[A i₀] (tail_transition_algHom A f (show j ≤ j by rfl) a) = b ⊗ₜ[A i₀] a
      congr 1
      let ds : DirectedSystem A (fun i j hij ↦ f i j hij) := inferInstance
      exact ds.map_self a
    · intro x y hx hy
      simpa [map_add] using congrArg (fun z ↦ z) (show
        (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
            (tail_transition_algHom A f (show j ≤ j by rfl))).toRingHom (x + y) =
          x + y by rw [RingHom.map_add, hx, hy])
  · intro k j j₀ h₀j hjk x
    letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    -- Proof comment: the tensor-transition composition law is already available as an algebra-hom
    -- equality, so specialize it to the element `x`.
    exact congrArg (fun g ↦ g x)
      (tailTensorSourceTransition_comp_transition A f h₀j hjk)

/-- Helper for Chap10 Lemma 10 168 8: the tail transition maps act as the identity on each
tail stage when viewed in `CommAlgCat (A i₀)`. -/
lemma tailCommAlgDiagram_map_id
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    CommAlgCat.ofHom (tail_transition_algHom A f (show j ≤ j by rfl)) =
      𝟙 (CommAlgCat.of (A j.1)) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: the tail transition along the identity relation is the identity ring map, so
  -- the corresponding algebra morphism is literally the identity in `CommAlgCat`.
  ext x
  let ds : DirectedSystem A (fun i j hij ↦ f i j hij) := inferInstance
  simpa using ds.map_self x

/-- Helper for Chap10 Lemma 10 168 8: the tail transition maps compose correctly in
`CommAlgCat (A i₀)`. -/
lemma tailCommAlgDiagram_map_comp
    {j₀ j k : Set.Ici i₀} (h₀j : j₀ ≤ j) (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    CommAlgCat.ofHom (tail_transition_algHom A f (h₀j.trans hjk)) =
      CommAlgCat.ofHom (tail_transition_algHom A f h₀j) ≫
        CommAlgCat.ofHom (tail_transition_algHom A f hjk) := by
  letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  -- Proof comment: both composites are the same stage map `A j₀.1 → A k.1`, so directed-system
  -- functoriality gives the categorical composition law on the nose.
  ext x
  let ds : DirectedSystem A (fun i j hij ↦ f i j hij) := inferInstance
  simpa using (ds.map_map h₀j hjk x).symm

/-- Helper for Chap10 Lemma 10 168 8: the cofinal tail above `i₀` as a diagram of
`A i₀`-algebras. -/
abbrev tailCommAlgDiagram : Set.Ici i₀ ⥤ CommAlgCat.{u} (A i₀) where
  obj j :=
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    CommAlgCat.of (A j.1)
  map {j k} h :=
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    CommAlgCat.ofHom (tail_transition_algHom A f (show j ≤ k from leOfHom h))
  map_id := by
    intro j
    simpa using tailCommAlgDiagram_map_id A f (i₀ := i₀) j
  map_comp := by
    intro j k l h₀j hjk
    simpa [homOfLE_leOfHom] using
      tailCommAlgDiagram_map_comp A f (i₀ := i₀)
        (h₀j := leOfHom h₀j) (hjk := leOfHom hjk)

/-- Helper for Chap10 Lemma 10 168 8: the pushout normalization from one canonical tensor target
to a later one is the same tensor-stage transition equivalence from Lemma `10.168.7`, specialized
to the tail diagram above `i₀`. -/
noncomputable abbrev tailTensorTargetBaseChangeRingEquiv
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {j₀ j : Set.Ici i₀} (h₀j : j₀ ≤ j) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    let S₀ := B₀ ⊗[A i₀] A j₀.1
    let S := B₀ ⊗[A i₀] A j.1
    let C₀j := C₀ ⊗[A i₀] A j₀.1
    let Cj := C₀ ⊗[A i₀] A j.1
    letI : Algebra S₀ C₀j :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j₀.1))).toRingHom.toAlgebra
    letI : Algebra S₀ S :=
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f h₀j)).toRingHom.toAlgebra
    letI : Algebra S Cj :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.toAlgebra
    (C₀j ⊗[S₀] S) ≃+* Cj :=
  tensorStageTransitionPushoutRingEquiv
    (F := tailCommAlgDiagram A f (i₀ := i₀)) φ₀ (homOfLE h₀j)

/-- Helper for Chap10 Lemma 10 168 8: once one canonical tensor stage is smooth, every later
tail stage remains smooth by the tensor-stage pushout square. -/
lemma tailTensorSmooth_of_transition
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {j₀ j : Set.Ici i₀} (h₀j : j₀ ≤ j)
    (hSmooth :
      letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j₀.1))).Smooth) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).Smooth := by
  letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: specialize the already-proved transition stability theorem for canonical
  -- tensor maps to the tail functor above `i₀`.
  simpa using
    tensorBaseChangeSmooth_of_transition
      (F := tailCommAlgDiagram A f (i₀ := i₀)) φ₀ (homOfLE h₀j) hSmooth

/-- Helper for Chap10 Lemma 10 168 8: the finite-presentation and formally-smooth parts already
force smoothness once they are known on a canonical tensor stage. -/
lemma stageTensorSmooth_of_formallySmooth
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    (j : Set.Ici i₀)
    (hform :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).FormallySmooth) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).Smooth := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let φj := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom
  have hfpj : φj.FinitePresentation := by
    -- Proof comment: this is exactly the stagewise finite-presentation transport already proved
    -- for the canonical tensor map.
    simpa [φj, AlgHom.FinitePresentation, RingHom.FinitePresentation] using
      stageTensorMapFinitePresentation A f φ₀ hfp j
  -- Proof comment: reconstruct smoothness from the owner definition once the formally-smooth and
  -- finite-presentation halves are both available at the same stage.
  exact (RingHom.smooth_def).2 ⟨by simpa [φj] using hform, hfpj⟩

/-- Helper for Chap10 Lemma 10 168 8: finite presentation lets a formally smooth tensor stage be
upgraded to smoothness, and then every later tail stage is formally smooth again by transition
stability. -/
lemma tailTensorFormallySmooth_of_transition
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    {j₀ j : Set.Ici i₀} (h₀j : j₀ ≤ j)
    (hForm :
      letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j₀.1))).FormallySmooth) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).FormallySmooth := by
  letI : Algebra (A i₀) (A j₀.1) := (f i₀ j₀.1 j₀.2).toAlgebra
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  have hSmooth₀ :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j₀.1))).Smooth := by
    -- Proof comment: the base tail stage becomes smooth by combining the fixed finite-presentation
    -- hypothesis with the given formally-smooth input.
    exact stageTensorSmooth_of_formallySmooth A f φ₀ hfp j₀ hForm
  -- Proof comment: after transporting smoothness to the later stage, formal smoothness is again
  -- just the first projection of the owner predicate `Smooth`.
  exact (tailTensorSmooth_of_transition A f φ₀ h₀j hSmooth₀).formallySmooth

/-- Helper for Chap10 Lemma 10 168 8: the canonical map on a tail stage is literally the
transition ring hom of the directed system. -/
lemma tailStageAlgebraMap_eq
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    algebraMap (A i₀) (A j.1) = f i₀ j.1 j.2 := rfl

/-- Helper for Chap10 Lemma 10 168 8: once the canonical limit tensor map is formally smooth, its
finite-presentation hypothesis upgrades it to smoothness at the limit stage. -/
lemma limitTensorSmooth_of_formallySmooth
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hform :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).FormallySmooth)
    (hfp :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).FinitePresentation) :
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth := by
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let phiInf := Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)
  have hfpInf : phiInf.toRingHom.FinitePresentation := by
    -- Proof comment: reinterpret the algebra-map finite-presentation owner as the ring-hom
    -- finite-presentation component used by `RingHom.smooth_def`.
    simpa [phiInf, AlgHom.FinitePresentation, RingHom.FinitePresentation] using hfp
  -- Proof comment: smoothness is exactly formal smoothness plus finite presentation for the
  -- underlying ring hom, so the limit-stage owner theorem closes immediately.
  exact (RingHom.smooth_def).2 ⟨by simpa [phiInf] using hform, hfpInf⟩

/-- Helper for Chap10 Lemma 10 168 8: finite presentation of `φ₀` survives after tensoring with
the direct limit ring `A∞`. This is the limit-stage finite-presentation input used both in the
formal-smooth and smooth descent routes. -/
lemma limitTensorMapFinitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation) :
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).FinitePresentation := by
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A i₀] A∞
  let T := S ⊗[B₀] C₀
  letI : CommRing S := inferInstance
  letI : CommRing T := inferInstance
  letI : Algebra B₀ S := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S T := Algebra.TensorProduct.leftAlgebra
  let α : S →ₐ[S] T := Algebra.ofId S T
  let e : T ≃+* (C₀ ⊗[A i₀] A∞) := tensorTargetRingEquiv A φ₀ A∞
  let ψ : S →ₐ[A i₀] (C₀ ⊗[A i₀] A∞) :=
    Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)
  letI : Algebra.FinitePresentation B₀ C₀ :=
    algebraFinitePresentationOfHomFinitePresentation A φ₀ hfp
  have hα : α.toRingHom.FinitePresentation := by
    -- Proof comment: the literal tensor target is finitely presented over the literal tensor
    -- source by the standard owner-level base-change instance.
    letI : Algebra.FinitePresentation S T := by
      simpa [S, T] using (inferInstance : Algebra.FinitePresentation S (S ⊗[B₀] C₀))
    simpa [α, RingHom.finitePresentation_algebraMap]
  have he : e.toRingHom.comp α.toRingHom = ψ.toRingHom := by
    -- Proof comment: after commuting the two tensor factors and cancelling the intermediate base
    -- change along `B₀`, the literal algebra map `S → S ⊗[B₀] C₀` becomes the displayed
    -- limit-stage tensor map.
    apply RingHom.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [α, ψ]
    · intro b a
      -- Proof comment: first rewrite the source algebra map to the explicit tensor generator in
      -- the literal target `T`, then the same `comm + cancelBaseChange` normalization as in the
      -- stage proof identifies the result with the canonical tensor generator.
      have hα_apply :
          α (b ⊗ₜ[A i₀] a) =
            ((((b ⊗ₜ[A i₀] a) : S) ⊗ₜ[B₀] (1 : C₀)) : T) := rfl
      change e.toRingHom (α (b ⊗ₜ[A i₀] a)) = ψ.toRingHom (b ⊗ₜ[A i₀] a)
      rw [hα_apply]
      change
        (Algebra.TensorProduct.cancelBaseChange (A i₀) B₀ C₀ C₀ A∞)
          ((Algebra.TensorProduct.comm B₀ S C₀)
            ((((b ⊗ₜ[A i₀] a) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[A i₀] a
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[A i₀] a = φ₀ b ⊗ₜ[A i₀] a from rfl)
    · intro z₁ z₂ hz₁ hz₂
      rw [RingHom.map_add, RingHom.map_add, hz₁, hz₂]
  have hψ : ψ.toRingHom.FinitePresentation := by
    -- Proof comment: finite presentation is preserved under postcomposition with the tensor
    -- target equivalence, and `he` identifies that postcomposition with the canonical limit map.
    have hpost :
        (e.toRingHom.comp α.toRingHom).FinitePresentation :=
      RingHom.finitePresentation_respectsIso.1 _ e hα
    rw [he] at hpost
    simpa [ψ] using hpost
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation, ψ] using hψ

/-- Helper for Chap10 Lemma 10 168 8: the limit tensor target `C₀ ⊗[A i₀] A∞` is finitely
presented over the limit tensor source `B₀ ⊗[A i₀] A∞`. -/
lemma limitTensorTargetAlgebraFinitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation) :
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let S := B₀ ⊗[A i₀] A∞
    let T := C₀ ⊗[A i₀] A∞
    letI : Algebra S T :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
    Algebra.FinitePresentation S T := by
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let S := B₀ ⊗[A i₀] A∞
  let T := C₀ ⊗[A i₀] A∞
  letI : Algebra S T :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
  have hmap :
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).FinitePresentation := by
    -- Proof comment: reuse the already normalized limit-stage finite-presentation bridge for the
    -- canonical tensor map.
    exact limitTensorMapFinitePresentation A f φ₀ hfp
  -- Proof comment: reinterpret the map-level finite-presentation statement as the algebra-level
  -- instance on the literal limit tensor target.
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation, S, T] using hmap

/-- Helper for Chap10 Lemma 10 168 8: the canonical map from a tail stage to the ambient direct
limit is compatible with the tail transition maps. -/
lemma tailStageToDirectLimitAlgHom_comp_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (tail_stage_to_direct_limit_algHom A f k).comp (tail_transition_algHom A f hjk) =
      tail_stage_to_direct_limit_algHom A f j := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  apply AlgHom.ext
  intro x
  -- Proof comment: both algebra maps send `x` to the same class in the ambient direct limit,
  -- represented either at `j` or after pushing `x` forward to the later tail stage `k`.
  simpa only [tail_stage_to_direct_limit_algHom, tail_transition_algHom] using
    (@Ring.DirectLimit.of_f I _ A _ (fun i j hij ↦ f i j hij) j.1 k.1 hjk x)

/-- Helper for Chap10 Lemma 10 168 8: the canonical map from a tail stage to the tail direct
limit is compatible with the tail transition maps. -/
lemma tailStageToTailDirectLimitAlgHom_comp_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j' : Set.Ici i₀ ↦ A j'.1)
        (fun j' k' hjk ↦
          (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
    (tail_stage_to_tail_direct_limit_algHom A f k).comp (tail_transition_algHom A f hjk) =
      tail_stage_to_tail_direct_limit_algHom A f j := by
  let tailLimit :=
    Ring.DirectLimit
      (fun j' : Set.Ici i₀ ↦ A j'.1)
      (fun j' k' hjk ↦
        (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let e : tailLimit ≃ₐ[A i₀] A∞ := tail_directLimitAlgEquivToFull A f
  have heinj : Function.Injective e.toAlgHom := e.injective
  apply DFunLike.ext
  intro x
  apply heinj
  -- Proof comment: compare after transporting both sides to the ambient direct limit `A∞`, where
  -- the corresponding stage maps are already known to commute with the tail transition maps.
  change
    (e.toAlgHom.comp
        ((tail_stage_to_tail_direct_limit_algHom A f k).comp (tail_transition_algHom A f hjk))) x =
      (e.toAlgHom.comp
        (tail_stage_to_tail_direct_limit_algHom A f j)) x
  have hcomp :
      ((e.toAlgHom.comp
          (tail_stage_to_tail_direct_limit_algHom A f k)).comp
          (tail_transition_algHom A f hjk)) =
        e.toAlgHom.comp
          (tail_stage_to_tail_direct_limit_algHom A f j) := by
    -- Proof comment: first compare the composites as algebra morphisms, where the tail/full
    -- direct-limit compatibility lemma rewrites cleanly.
    rw [tail_directLimitAlgEquivToFull_comp_tail_stage_to_tail_direct_limit_algHom A f]
    exact tailStageToDirectLimitAlgHom_comp_transition A f hjk
  simpa [AlgHom.comp_assoc] using congrArg (fun g : A j.1 →ₐ[A i₀] A∞ ↦ g x) hcomp

/-- Helper for Chap10 Lemma 10 168 8: the ambient direct-limit stage map compatibility from
`tailStageToDirectLimitAlgHom_comp_transition`, evaluated on one element. -/
lemma tailStageToDirectLimitAlgHom_apply_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) (x : A j.1) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    tail_stage_to_direct_limit_algHom A f k (tail_transition_algHom A f hjk x) =
      tail_stage_to_direct_limit_algHom A f j x := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  -- Proof comment: specialize the algebra-hom compatibility lemma to the element `x`.
  exact congrArg (fun g : A j.1 →ₐ[A i₀] A∞ ↦ g x)
    (tailStageToDirectLimitAlgHom_comp_transition A f hjk)

/-- Helper for Chap10 Lemma 10 168 8: after tensoring with `B₀`, the canonical map from a tail
stage to the ambient limit source is compatible with the stage-transition maps. -/
lemma tailTensorSourceToLimitAlgHom_comp_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    ((Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f k)).comp
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f hjk))) =
      Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f j) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  -- Proof comment: after tensoring with `B₀`, the source-stage transition followed by the limit
  -- map still sends `b ⊗ a` to `b ⊗ of_j(a)`, so the compatibility reduces to the ambient
  -- direct-limit stage-map identity already proved above.
  apply AlgHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b a
    change b ⊗ₜ[A i₀]
        (tail_stage_to_direct_limit_algHom A f k (tail_transition_algHom A f hjk a)) =
      b ⊗ₜ[A i₀]
        (tail_stage_to_direct_limit_algHom A f j a)
    congr 1
    exact tailStageToDirectLimitAlgHom_apply_transition A f hjk a
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 168 8: the explicit tail direct-limit stage map compatibility from
`tailStageToTailDirectLimitAlgHom_comp_transition`, evaluated on one element. -/
lemma tailStageToTailDirectLimitAlgHom_apply_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) (x : A j.1) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j' : Set.Ici i₀ ↦ A j'.1)
        (fun j' k' hjk ↦
          (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
    tail_stage_to_tail_direct_limit_algHom A f k (tail_transition_algHom A f hjk x) =
      tail_stage_to_tail_direct_limit_algHom A f j x := by
  let tailLimit :=
    Ring.DirectLimit
      (fun j' : Set.Ici i₀ ↦ A j'.1)
      (fun j' k' hjk ↦
        (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
  -- Proof comment: specialize the explicit tail direct-limit compatibility lemma to the element
  -- `x`.
  exact congrArg (fun g : A j.1 →ₐ[A i₀] tailLimit ↦ g x)
    (tailStageToTailDirectLimitAlgHom_comp_transition A f hjk)

/-- Helper for Chap10 Lemma 10 168 8: the literal tensor-stage map to the ambient limit source
sends a pure tensor `b ⊗ a` to `b ⊗ of_j(a)`. -/
lemma tailTensorSourceToLimitAlgHom_tmul
    (j : Set.Ici i₀) (b : B₀) (a : A j.1) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
      (tail_stage_to_direct_limit_algHom A f j))
      (b ⊗ₜ[A i₀] a) =
        b ⊗ₜ[A i₀]
          (tail_stage_to_direct_limit_algHom A f j a) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  -- Proof comment: `Algebra.TensorProduct.map` acts componentwise on pure tensors.
  simp

/-- Helper for Chap10 Lemma 10 168 8: after passing from a tail stage `j` to a later tail stage
`k`, the two evident maps from `B₀ ⊗[A i₀] A j.1` to the literal limit source
`B₀ ⊗[A i₀] A∞` agree on every element. -/
lemma tailTensorSourceToLimitAlgHom_apply_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k)
    (x :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      B₀ ⊗[A i₀] A j.1) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f k))
      ((Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
          (tail_transition_algHom A f hjk)) x) =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f j)) x := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  -- Proof comment: specialize the already proved algebra-hom compatibility of the literal
  -- tensor-source stage maps to the chosen tensor element `x`.
  exact congrArg (fun g : B₀ ⊗[A i₀] A j.1 →ₐ[A i₀] B₀ ⊗[A i₀] A∞ ↦ g x)
    (tailTensorSourceToLimitAlgHom_comp_transition A f hjk)

/-- Helper for Chap10 Lemma 10 168 8: on pure tensors, the stage-transition route to the literal
limit source agrees with the direct stage-to-limit route. -/
lemma tailTensorSourceToLimitAlgHom_tmul_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) (b : B₀) (a : A j.1) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f k))
      (b ⊗ₜ[A i₀]
        (tail_transition_algHom A f hjk a)) =
      b ⊗ₜ[A i₀]
        (tail_stage_to_direct_limit_algHom A f j a) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  -- Proof comment: first rewrite the transition route as an equality of maps on the pure tensor
  -- `b ⊗ a`, then use the already normalized pure-tensor formula for the literal limit map.
  simpa using
    tailTensorSourceToLimitAlgHom_apply_transition A f hjk (b ⊗ₜ[A i₀] a)

/-- Helper for Chap10 Lemma 10 168 8: after tensoring with `B₀`, the canonical map from a tail
stage to the raw tail direct limit is compatible with the stage-transition maps. -/
lemma tailTensorSourceToTailDirectLimitAlgHom_comp_transition
    {j k : Set.Ici i₀} (hjk : j ≤ k) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j' : Set.Ici i₀ ↦ A j'.1)
        (fun j' k' hjk ↦
          (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
    letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
    ((Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_tail_direct_limit_algHom A f k)).comp
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_transition_algHom A f hjk))) =
      Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_tail_direct_limit_algHom A f j) := by
  let tailLimit :=
    Ring.DirectLimit
      (fun j' : Set.Ici i₀ ↦ A j'.1)
      (fun j' k' hjk ↦
        (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) (A k.1) := (f i₀ k.1 k.2).toAlgebra
  letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
  -- Proof comment: after tensoring with `B₀`, the source-stage transition followed by the raw
  -- tail-limit map still sends `b ⊗ a` to `b ⊗ of_j(a)`, so the compatibility reduces to the raw
  -- tail direct-limit stage-map identity already proved above.
  apply AlgHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b a
    change
      b ⊗ₜ[A i₀]
          (tail_stage_to_tail_direct_limit_algHom A f k
            (tail_transition_algHom A f hjk a)) =
        b ⊗ₜ[A i₀]
          (tail_stage_to_tail_direct_limit_algHom A f j a)
    congr 1
    exact tailStageToTailDirectLimitAlgHom_apply_transition A f hjk a
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Chap10 Lemma 10 168 8: the literal source-stage map
`B₀ ⊗[A i₀] A j.1 → B₀ ⊗[A i₀] A∞` is compatible with the original `B₀`-algebra structures, so
it forms a scalar tower `B₀ → S₀ → S∞`. -/
lemma tailTensorSourceLimit_isScalarTower
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let S₀ := B₀ ⊗[A i₀] A j.1
    let SInf := B₀ ⊗[A i₀] A∞
    letI : Algebra S₀ SInf :=
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f j)).toRingHom.toAlgebra
    IsScalarTower B₀ S₀ SInf := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let S₀ := B₀ ⊗[A i₀] A j.1
  let SInf := B₀ ⊗[A i₀] A∞
  letI : Algebra S₀ SInf :=
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
      (tail_stage_to_direct_limit_algHom A f j)).toRingHom.toAlgebra
  -- Proof comment: both composites from `B₀` to the literal limit source send `b` to the pure
  -- tensor `b ⊗ 1`, so the scalar tower identity is literal on generators.
  refine IsScalarTower.of_algebraMap_eq' (R := B₀) (S := S₀) (A := SInf) ?_
  ext b
  change (b ⊗ₜ[A i₀] (1 : A∞) : SInf) =
    (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
      (tail_stage_to_direct_limit_algHom A f j))
      (b ⊗ₜ[A i₀] (1 : A j.1))
  simp

/-- Helper for Chap10 Lemma 10 168 8: the base tail index `j0 = i₀` lies below every later tail
stage, so all later source-stage comparisons may be anchored over `j0`. -/
lemma baseTailIndex_le
    (j : Set.Ici i₀) :
    (⟨i₀, le_rfl⟩ : Set.Ici i₀) ≤ j := by
  -- Proof comment: in the tail preorder, the distinguished base point is minimal by definition.
  exact j.2

/-- Helper for Chap10 Lemma 10 168 8: the limit-stage `comm` plus `cancelBaseChange`
normalization is compatible with the canonical algebra map from the literal limit tensor source. -/
lemma limitTensorTargetRingEquiv_commutes
    (φ₀ : B₀ →ₐ[A i₀] C₀) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let S := B₀ ⊗[A i₀] A∞
    letI : Algebra S (C₀ ⊗[A i₀] A∞) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
    ∀ x : S,
      tensorTargetRingEquiv A φ₀ A∞
          (algebraMap S (S ⊗[B₀] C₀) x) =
        algebraMap S (C₀ ⊗[A i₀] A∞) x := by
  dsimp
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let S := B₀ ⊗[A i₀] A∞
  letI : Algebra S (C₀ ⊗[A i₀] A∞) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
  intro x
  -- Proof comment: as in the finite-stage normalization, it suffices to check the comparison on
  -- tensor generators of the source ring `S = B₀ ⊗[A i₀] A∞`.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b r
    change
      (Algebra.TensorProduct.cancelBaseChange (A i₀) B₀ C₀ C₀ A∞)
        ((1 : C₀) ⊗ₜ[B₀] ((b ⊗ₜ[A i₀] r : S))) =
      φ₀ b ⊗ₜ[A i₀] r
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simp [Algebra.smul_def]
    simpa using
      (show (algebraMap B₀ C₀) b ⊗ₜ[A i₀] r = φ₀ b ⊗ₜ[A i₀] r from rfl)
  · intro x y hx hy
    rw [TensorProduct.tmul_add, map_add, hx, hy]
    exact ((algebraMap S (C₀ ⊗[A i₀] A∞)).map_add x y).symm

/-- Helper for Chap10 Lemma 10 168 8: the limit-stage `comm` plus `cancelBaseChange`
normalization upgrades to an algebra equivalence over the literal limit tensor source. -/
noncomputable abbrev limitTensorTargetAlgEquiv
    (φ₀ : B₀ →ₐ[A i₀] C₀) :
    letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let S := B₀ ⊗[A i₀] A∞
    letI : Algebra S (C₀ ⊗[A i₀] A∞) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
    (S ⊗[B₀] C₀) ≃ₐ[S] (C₀ ⊗[A i₀] A∞) :=
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let S := B₀ ⊗[A i₀] A∞
  letI : Algebra S (C₀ ⊗[A i₀] A∞) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
  { __ := tensorTargetRingEquiv A φ₀ A∞
    commutes' := limitTensorTargetRingEquiv_commutes A f φ₀ }

/-- Helper for Chap10 Lemma 10 168 8: after base change to the literal limit tensor source,
the fixed polynomial presentation of `C₀` identifies with the canonical limit tensor target. -/
noncomputable abbrev limitPresentationTargetAlgEquiv
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (e₀ :
      letI : Algebra B₀ C₀ := φ₀.toAlgebra
      Nonempty ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)) ≃ₐ[B₀] C₀)) :
    letI : Algebra B₀ C₀ := φ₀.toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let SInf := B₀ ⊗[A i₀] A∞
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra SInf (C₀ ⊗[A i₀] A∞) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
    (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf] (C₀ ⊗[A i₀] A∞) :=
  letI : Algebra B₀ C₀ := φ₀.toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let SInf := B₀ ⊗[A i₀] A∞
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra SInf (C₀ ⊗[A i₀] A∞) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.toAlgebra
  let eQ₀ : Q₀ ≃ₐ[B₀] C₀ := e₀.some
  -- Proof comment: first commute the fixed presentation to the left tensor-factor spelling,
  -- then tensor the chosen presentation equivalence with `SInf`, and finally normalize to the
  -- canonical limit tensor target via `comm + cancelBaseChange`.
  (((Algebra.TensorProduct.commRight B₀ SInf Q₀).symm).trans
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : SInf ≃ₐ[SInf] SInf) eQ₀)).trans
    (limitTensorTargetAlgEquiv A f φ₀)

/-- Helper for Chap10 Lemma 10 168 8: the normalized limit-presentation quotient map has kernel
equal to the explicit relation ideal `IInf`. -/
lemma limitPresentationMap_ker
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀) :
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let SInf := B₀ ⊗[A i₀] A∞
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let IInf : Ideal (MvPolynomial (Fin n) SInf) :=
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ SInf) (fs i))
    letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
    let ePresInf :
        (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf] (MvPolynomial (Fin n) SInf ⧸ IInf) :=
      (presentationBaseChangeAlgEquiv
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) A∞).some
    let qInf : MvPolynomial (Fin n) SInf →ₐ[SInf] (Q₀ ⊗[B₀] SInf) :=
      ePresInf.symm.toAlgHom.comp (Ideal.Quotient.mkₐ SInf IInf)
    RingHom.ker qInf.toRingHom = IInf := by
  dsimp
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let SInf := B₀ ⊗[A i₀] A∞
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  let IInf : Ideal (MvPolynomial (Fin n) SInf) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ SInf) (fs i))
  letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
  let ePresInf :
      (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf] (MvPolynomial (Fin n) SInf ⧸ IInf) :=
    (presentationBaseChangeAlgEquiv
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) A∞).some
  let qInf : MvPolynomial (Fin n) SInf →ₐ[SInf] (Q₀ ⊗[B₀] SInf) :=
    ePresInf.symm.toAlgHom.comp (Ideal.Quotient.mkₐ SInf IInf)
  -- Proof comment: `qInf` is just the quotient map by `IInf` followed by an algebra
  -- equivalence, so its kernel is unchanged.
  rw [show qInf.toRingHom =
      ePresInf.symm.toRingHom.comp (Ideal.Quotient.mkₐ SInf IInf).toRingHom by rfl]
  rw [RingHom.ker_equiv_comp, Ideal.Quotient.mkₐ_ker]

/-- Helper for Chap10 Lemma 10 168 8: the square-zero quotient used by the normalized limit
presentation is canonically identified with the explicit square-zero base-change model. -/
noncomputable abbrev limitPresentationKerSquareAlgEquiv
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀) :
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    let SInf := B₀ ⊗[A i₀] A∞
    let P₀ := MvPolynomial (Fin n) B₀
    let Q₀ := P₀ ⧸ Ideal.span (Set.range fs)
    let IInf : Ideal (MvPolynomial (Fin n) SInf) :=
      Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ SInf) (fs i))
    letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
    let ePresInf :
        (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf] (MvPolynomial (Fin n) SInf ⧸ IInf) :=
      (presentationBaseChangeAlgEquiv
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) A∞).some
    let qInf : MvPolynomial (Fin n) SInf →ₐ[SInf] (Q₀ ⊗[B₀] SInf) :=
      ePresInf.symm.toAlgHom.comp (Ideal.Quotient.mkₐ SInf IInf)
    (MvPolynomial (Fin n) SInf ⧸ RingHom.ker qInf.toRingHom ^ 2) ≃ₐ[SInf]
      ((P₀ ⧸ Ideal.span (Set.range fs) ^ 2) ⊗[B₀] SInf) :=
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  let SInf := B₀ ⊗[A i₀] A∞
  let P₀ := MvPolynomial (Fin n) B₀
  let Q₀ := P₀ ⧸ Ideal.span (Set.range fs)
  let IInf : Ideal (MvPolynomial (Fin n) SInf) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ SInf) (fs i))
  letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
  let ePresInf :
      (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf] (MvPolynomial (Fin n) SInf ⧸ IInf) :=
    (presentationBaseChangeAlgEquiv
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) A∞).some
  let qInf : MvPolynomial (Fin n) SInf →ₐ[SInf] (Q₀ ⊗[B₀] SInf) :=
    ePresInf.symm.toAlgHom.comp (Ideal.Quotient.mkₐ SInf IInf)
  let eKerSq :
      (MvPolynomial (Fin n) SInf ⧸ RingHom.ker qInf.toRingHom ^ 2) ≃ₐ[SInf]
        (MvPolynomial (Fin n) SInf ⧸ IInf ^ 2) :=
    Ideal.quotientEquivAlgOfEq SInf <| by
      rw [limitPresentationMap_ker (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs]
  -- Proof comment: first replace `ker qInf` by the explicit ideal `IInf`, then use the already
  -- proved square-zero base-change normalization.
  eKerSq.trans
    ((presentationSquareBaseChangeAlgEquiv
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) A∞).some.symm)

/-- Helper for Chap10 Lemma 10 168 8: the explicit tensor-source direct limit carries the
canonical `B₀`-algebra map to the literal limit source `B₀ ⊗[A i₀] A∞`. -/
noncomputable theorem tailTensorSourceToLimitDirectLimitAlgHom :
    let G :=
      tensor_base_change_commAlgDiagram
        (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
    directed_commAlg_ringDirectLimit (A₀ := B₀) G →ₐ[B₀] (B₀ ⊗[A i₀] A∞) := by
  let G :=
    tensor_base_change_commAlgDiagram
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
  let tSource : Cocone G where
    pt := CommAlgCat.of (B₀ ⊗[A i₀] A∞)
    ι :=
      { app := fun j ↦
          CommAlgCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
              (tail_stage_to_direct_limit_algHom A f j))
        naturality := by
          intro j k hjk
          ext x
          -- Proof comment: the cocone naturality is exactly the already-proved compatibility of
          -- the literal tensor-source stage maps with the tail transition maps.
          exact congrArg
            (fun g :
              B₀ ⊗[A i₀] A j.1 →ₐ[A i₀] B₀ ⊗[A i₀] A∞ ↦ g x)
            (tailTensorSourceToLimitAlgHom_comp_transition A f (i₀ := i₀) (B₀ := B₀)
              (hjk := leOfHom hjk)) }
  -- Proof comment: apply the explicit direct-limit desc map to the literal cocone with point
  -- `B₀ ⊗[A i₀] A∞`.
  exact directed_commAlg_ringDirectLimitDescAlgHom (A₀ := B₀) G tSource

/-- Helper for Chap10 Lemma 10 168 8: the canonical tensor-source direct-limit desc map sends a
stage class to the corresponding literal stage-to-limit tensor map. -/
theorem tailTensorSourceToLimitDirectLimitAlgHom_comp_of
    (j : Set.Ici i₀)
    (x :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      B₀ ⊗[A i₀] A j.1) :
    let G :=
      tensor_base_change_commAlgDiagram
        (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
    tailTensorSourceToLimitDirectLimitAlgHom (A := A) (f := f) (i₀ := i₀) (B₀ := B₀)
        (Ring.DirectLimit.of
          (fun j ↦ ↑(G.obj j))
          (fun j k h ↦ (G.map (homOfLE h)).hom)
          j x) =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f j)) x := by
  let G :=
    tensor_base_change_commAlgDiagram
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
  let tSource : Cocone G where
    pt := CommAlgCat.of (B₀ ⊗[A i₀] A∞)
    ι :=
      { app := fun j ↦
          CommAlgCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
              (tail_stage_to_direct_limit_algHom A f j))
        naturality := by
          intro j k hjk
          ext y
          exact congrArg
            (fun g :
              B₀ ⊗[A i₀] A j.1 →ₐ[A i₀] B₀ ⊗[A i₀] A∞ ↦ g y)
            (tailTensorSourceToLimitAlgHom_comp_transition A f (i₀ := i₀) (B₀ := B₀)
              (hjk := leOfHom hjk)) }
  -- Proof comment: specialize the general explicit direct-limit desc computation formula to the
  -- tensor-source tail diagram and its literal `SInf` cocone.
  simpa [tailTensorSourceToLimitDirectLimitAlgHom, G, tSource] using
    (directed_commAlg_ringDirectLimitDescAlgHom_comp_of (A₀ := B₀) G tSource j x)

/-- Helper for Chap10 Lemma 10 168 8: swapping the tensor factors is compatible with the
canonical tail-stage map to the literal limit source. -/
lemma tailTensorSourceComm_naturality
    (j : Set.Ici i₀)
    (z :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      A j.1 ⊗[A i₀] B₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
    (Algebra.TensorProduct.comm (R := A i₀) (A := A∞) (B := B₀))
        ((Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom A f j)
          (AlgHom.id (A i₀) B₀)) z) =
      (Algebra.TensorProduct.map
        (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f j))
        ((Algebra.TensorProduct.comm (R := A i₀) (A := A j.1) (B := B₀)) z) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  -- Proof comment: both composites send a pure tensor `a ⊗ b` to `b ⊗ of_j(a)`, so tensor
  -- induction proves the naturality identity.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a b
    simp
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

/-- Helper for Chap10 Lemma 10 168 8: the canonical map from the explicit tensor-source direct
limit onto the literal limit source `B₀ ⊗[A i₀] A∞` is surjective. -/
lemma tailTensorSourceToLimitDirectLimitAlgHom_surjective :
    let G :=
      tensor_base_change_commAlgDiagram
        (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
    Function.Surjective
      (tailTensorSourceToLimitDirectLimitAlgHom
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀)) := by
  let G :=
    tensor_base_change_commAlgDiagram
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
  intro z
  let zComm : A∞ ⊗[A i₀] B₀ :=
    (Algebra.TensorProduct.comm (R := A i₀) (A := A∞) (B := B₀)).symm z
  obtain ⟨j, zj, hzj⟩ :=
    directLimit_tensor_exists_tail_repr
      (G := A) (f := f) (i0 := i₀) (X := B₀) zComm
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let zjComm : B₀ ⊗[A i₀] A j.1 :=
    (Algebra.TensorProduct.comm (R := A i₀) (A := A j.1) (B := B₀)) zj
  refine ⟨Ring.DirectLimit.of
      (fun j ↦ ↑(G.obj j))
      (fun j k h ↦ (G.map (homOfLE h)).hom)
      j zjComm, ?_⟩
  -- Proof comment: first lift `z` to one tail stage after commuting the factors, then apply the
  -- direct-limit stage computation formula and commute back.
  calc
    tailTensorSourceToLimitDirectLimitAlgHom
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀)
        (Ring.DirectLimit.of
          (fun j ↦ ↑(G.obj j))
          (fun j k h ↦ (G.map (homOfLE h)).hom)
          j zjComm) =
      (Algebra.TensorProduct.map
        (AlgHom.id (A i₀) B₀)
        (tail_stage_to_direct_limit_algHom A f j)) zjComm := by
          simpa [zjComm] using
            (tailTensorSourceToLimitDirectLimitAlgHom_comp_of
              (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) j zjComm)
    _ =
      (Algebra.TensorProduct.comm (R := A i₀) (A := A∞) (B := B₀))
        ((Algebra.TensorProduct.map
          (tail_stage_to_direct_limit_algHom A f j)
          (AlgHom.id (A i₀) B₀)) zj) := by
            simpa [zjComm] using
              (tailTensorSourceComm_naturality
                (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) j zj)
    _ =
      (Algebra.TensorProduct.comm (R := A i₀) (A := A∞) (B := B₀)) zComm := by
            exact congrArg
              (Algebra.TensorProduct.comm (R := A i₀) (A := A∞) (B := B₀))
              hzj
    _ = z := by
          simp [zComm]

/-- Helper for Chap10 Lemma 10 168 8: the explicit tensor-source direct limit also maps to the
raw tail tensor source `B₀ ⊗[A i₀] tailA` by sending each stage class to the corresponding pure
tail-limit tensor class. -/
noncomputable theorem tailTensorSourceToTailLimitDirectLimitAlgHom :
    let tailLimit :=
      Ring.DirectLimit
        (fun j : Set.Ici i₀ ↦ A j.1)
        (fun j k hjk ↦
          (tail_transition_algHom A f hjk : A j.1 →+* A k.1))
    letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
    let G :=
      tensor_base_change_commAlgDiagram
        (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
    directed_commAlg_ringDirectLimit (A₀ := B₀) G →ₐ[B₀] (B₀ ⊗[A i₀] tailLimit) := by
  let tailLimit :=
    Ring.DirectLimit
      (fun j : Set.Ici i₀ ↦ A j.1)
      (fun j k hjk ↦
        (tail_transition_algHom A f hjk : A j.1 →+* A k.1))
  letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
  let G :=
    tensor_base_change_commAlgDiagram
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
  let tSource : Cocone G where
    pt := CommAlgCat.of (B₀ ⊗[A i₀] tailLimit)
    ι :=
      { app := fun j ↦
          CommAlgCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
              (tail_stage_to_tail_direct_limit_algHom A f j))
        naturality := by
          intro j k hjk
          ext x
          -- Proof comment: the cocone naturality is the already-proved compatibility of the raw
          -- tail direct-limit tensor-source stage maps with the tail transition maps.
          exact congrArg
            (fun g :
              B₀ ⊗[A i₀] A j.1 →ₐ[A i₀] B₀ ⊗[A i₀] tailLimit ↦ g x)
            (tailTensorSourceToTailDirectLimitAlgHom_comp_transition A f
              (i₀ := i₀) (B₀ := B₀) (hjk := leOfHom hjk)) }
  -- Proof comment: apply the explicit direct-limit desc map to the raw tail cocone with point
  -- `B₀ ⊗[A i₀] tailLimit`.
  exact directed_commAlg_ringDirectLimitDescAlgHom (A₀ := B₀) G tSource

/-- Helper for Chap10 Lemma 10 168 8: the raw-tail tensor-source direct-limit desc map sends a
stage class to the corresponding raw stage-to-tail-limit tensor map. -/
theorem tailTensorSourceToTailLimitDirectLimitAlgHom_comp_of
    (j : Set.Ici i₀)
    (x :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      B₀ ⊗[A i₀] A j.1) :
    let tailLimit :=
      Ring.DirectLimit
        (fun j' : Set.Ici i₀ ↦ A j'.1)
        (fun j' k' hjk ↦
          (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
    letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
    let G :=
      tensor_base_change_commAlgDiagram
        (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
    tailTensorSourceToTailLimitDirectLimitAlgHom
        (A := A) (f := f) (i₀ := i₀) (B₀ := B₀)
        (Ring.DirectLimit.of
          (fun j ↦ ↑(G.obj j))
          (fun j k h ↦ (G.map (homOfLE h)).hom)
          j x) =
      (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
        (tail_stage_to_tail_direct_limit_algHom A f j)) x := by
  let tailLimit :=
    Ring.DirectLimit
      (fun j' : Set.Ici i₀ ↦ A j'.1)
      (fun j' k' hjk ↦
        (tail_transition_algHom A f hjk : A j'.1 →+* A k'.1))
  letI : Algebra (A i₀) tailLimit := tail_directLimit_algebra A f
  let G :=
    tensor_base_change_commAlgDiagram
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
  let tSource : Cocone G where
    pt := CommAlgCat.of (B₀ ⊗[A i₀] tailLimit)
    ι :=
      { app := fun j ↦
          CommAlgCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id (A i₀) B₀)
              (tail_stage_to_tail_direct_limit_algHom A f j))
        naturality := by
          intro j k hjk
          ext y
          exact congrArg
            (fun g :
              B₀ ⊗[A i₀] A j.1 →ₐ[A i₀] B₀ ⊗[A i₀] tailLimit ↦ g y)
            (tailTensorSourceToTailDirectLimitAlgHom_comp_transition A f
              (i₀ := i₀) (B₀ := B₀) (hjk := leOfHom hjk)) }
  -- Proof comment: specialize the general explicit direct-limit desc computation formula to the
  -- tensor-source tail diagram and its raw-tail tensor cocone.
  simpa [tailTensorSourceToTailLimitDirectLimitAlgHom, G, tSource] using
    (directed_commAlg_ringDirectLimitDescAlgHom_comp_of (A₀ := B₀) G tSource j x)

/-- Helper for Chap10 Lemma 10 168 8: applying the tail/full colimit equivalence inversely to the
literal stage map `A j.1 → A∞` recovers the canonical stage map into the explicit tail direct
limit. -/
lemma tail_directLimitAlgEquivToFull_symm_comp_tail_stage_to_direct_limit_algHom
    (j : Set.Ici i₀) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    ((tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)).symm.toAlgHom).comp
        (tail_stage_to_direct_limit_algHom A f j) =
      tail_stage_to_tail_direct_limit_algHom A f j := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  -- Proof comment: compose both sides with the forward tail/full equivalence; both resulting
  -- maps are the literal stage map into `A∞`.
  apply AlgHom.ext
  intro x
  apply (tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)).injective
  change
    tail_stage_to_direct_limit_algHom A f j x =
      (tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀))
        (tail_stage_to_tail_direct_limit_algHom A f j x)
  simpa using
    congrArg
      (fun g : A j.1 →ₐ[A i₀] A∞ ↦ g x)
      (tail_directLimitAlgEquivToFull_comp_tail_stage_to_tail_direct_limit_algHom
        (A := A) (f := f) (i₀ := i₀) j)

/-- Helper for Chap10 Lemma 10 168 8: the canonical stage maps into the explicit
`directed_commAlg_ringDirectLimit` cocone are natural in `CommAlgCat`. -/
lemma directedCommAlg_directLimitCocone_naturality
    {A₀ : Type u} [CommRing A₀]
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (G : J ⥤ CommAlgCat.{u} A₀) {i j : J} (g : i ⟶ j) :
    G.map g ≫
        CommAlgCat.ofHom
          (directed_commAlg_stageToRingDirectLimitAlgHom (A₀ := A₀) G j) =
      CommAlgCat.ofHom
        (directed_commAlg_stageToRingDirectLimitAlgHom (A₀ := A₀) G i) := by
  -- Proof comment: this is exactly the directed-system relation for the explicit stage maps into
  -- the `Ring.DirectLimit`, rewritten in `CommAlgCat`.
  ext x
  simpa only [homOfLE_leOfHom] using
    congrArg
      (fun h :
        ↑(G.obj i) →ₐ[A₀] directed_commAlg_ringDirectLimit (A₀ := A₀) G ↦ h x)
      (directed_commAlg_stageToRingDirectLimitAlgHom_naturality
        (A₀ := A₀) G (leOfHom g))

/-- Helper for Chap10 Lemma 10 168 8: the explicit `Ring.DirectLimit` of a directed
`CommAlgCat A₀` diagram carries the canonical cocone of stage maps. -/
noncomputable abbrev directedCommAlg_directLimitCocone
    {A₀ : Type u} [CommRing A₀]
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (G : J ⥤ CommAlgCat.{u} A₀) :
    Cocone G where
  pt := CommAlgCat.of (directed_commAlg_ringDirectLimit (A₀ := A₀) G)
  ι :=
    { app := fun i ↦
        CommAlgCat.ofHom
          (directed_commAlg_stageToRingDirectLimitAlgHom (A₀ := A₀) G i)
      naturality := fun {_ _} g ↦
        directedCommAlg_directLimitCocone_naturality (A₀ := A₀) G g }

/-- Helper for Chap10 Lemma 10 168 8: the explicit `Ring.DirectLimit` cocone is already
colimiting in `CommAlgCat`. -/
theorem directedCommAlg_directLimitCoconeIsColimit
    {A₀ : Type u} [CommRing A₀]
    {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (G : J ⥤ CommAlgCat.{u} A₀) :
    IsColimit (directedCommAlg_directLimitCocone (A₀ := A₀) G) := by
  refine
    { desc := fun s ↦
        CommAlgCat.ofHom
          (directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A₀) G s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    -- Proof comment: the explicit desc map from the `Ring.DirectLimit` is characterized on each
    -- stage representative by the corresponding cocone leg.
    ext x
    simpa [directedCommAlg_directLimitCocone] using
      (directed_commAlg_ringDirectLimitDescAlgHom_comp_of (A₀ := A₀) G s i x)
  · intro s m hm
    -- Proof comment: every class in the explicit direct limit is represented at some stage, and
    -- the cocone equations force any candidate desc map to agree with the canonical one on that
    -- representative.
    ext z
    induction z using Ring.DirectLimit.induction_on with
    | ih i x =>
        have hmStage :
            m.hom
                (directed_commAlg_stageToRingDirectLimitAlgHom
                  (A₀ := A₀) G i x) =
              (s.ι.app i).hom x := by
          simpa [directedCommAlg_directLimitCocone] using
            congrArg (fun f : G.obj i ⟶ s.pt ↦ f.hom x) (hm i)
        calc
          m.hom
              (directed_commAlg_stageToRingDirectLimitAlgHom
                (A₀ := A₀) G i x) =
            (s.ι.app i).hom x := hmStage
          _ =
            directed_commAlg_ringDirectLimitDescAlgHom
              (A₀ := A₀) G s
              (directed_commAlg_stageToRingDirectLimitAlgHom
                (A₀ := A₀) G i x) := by
                  symm
                  simpa [directedCommAlg_directLimitCocone] using
                    (directed_commAlg_ringDirectLimitDescAlgHom_comp_of
                      (A₀ := A₀) G s i x)

/-- Helper for Chap10 Lemma 10 168 8: the cofinal tail above `i₀` has the literal cocone point
`A∞` with legs given by the canonical stage maps to the ambient direct limit. -/
noncomputable def tailCommAlgCoconeToLimit :
    Cocone (tailCommAlgDiagram A f (i₀ := i₀)) where
  pt := CommAlgCat.of A∞
  ι :=
    { app := fun j ↦
        letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
        CommAlgCat.ofHom (tail_stage_to_direct_limit_algHom A f j)
      naturality := by
        intro j k hjk
        ext x
        -- Proof comment: both cocone routes send `x` to the same class in the ambient direct
        -- limit, represented either at stage `j` or after moving to stage `k`.
        exact congrArg
          (fun g : A j.1 →ₐ[A i₀] A∞ ↦ g x)
          (tailStageToDirectLimitAlgHom_comp_transition
            (A := A) (f := f) (i₀ := i₀) (hjk := leOfHom hjk)) }

/-- Helper for Chap10 Lemma 10 168 8: the literal tail cocone with point `A∞` is colimiting in
`CommAlgCat (A i₀)`. -/
theorem tailCommAlgCoconeToLimit_isColimit :
    IsColimit (tailCommAlgCoconeToLimit (A := A) (f := f) (i₀ := i₀)) :=
by
  let G := tailCommAlgDiagram A f (i₀ := i₀)
  let e :
      directed_commAlg_ringDirectLimit (A₀ := A i₀) G ≃ₐ[A i₀] A∞ :=
    tail_directLimitAlgEquivToFull (A := A) (f := f) (i₀ := i₀)
  refine
    { desc := fun s ↦
        CommAlgCat.ofHom
          ((directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A i₀) G s).comp
            e.symm.toAlgHom)
      fac := ?_
      uniq := ?_ }
  · intro s j
    -- Proof comment: transport the literal stage map into the explicit tail direct limit and
    -- then apply the canonical direct-limit desc computation formula.
    ext x
    have htransport :
        e.symm.toAlgHom (tail_stage_to_direct_limit_algHom A f j x) =
          directed_commAlg_stageToRingDirectLimitAlgHom
            (A₀ := A i₀) G j x := by
      simpa [G] using
        congrArg
          (fun h :
            A j.1 →ₐ[A i₀]
              directed_commAlg_ringDirectLimit (A₀ := A i₀) G ↦ h x)
          (tail_directLimitAlgEquivToFull_symm_comp_tail_stage_to_direct_limit_algHom
            (A := A) (f := f) (i₀ := i₀) j)
    calc
      (directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A i₀) G s)
          (e.symm.toAlgHom (tail_stage_to_direct_limit_algHom A f j x)) =
        (directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A i₀) G s)
          (directed_commAlg_stageToRingDirectLimitAlgHom
            (A₀ := A i₀) G j x) := by
              rw [htransport]
      _ = (s.ι.app j).hom x := by
            simpa [G, directedCommAlg_directLimitCocone] using
              (directed_commAlg_ringDirectLimitDescAlgHom_comp_of
                (A₀ := A i₀) G s j x)
  · intro s m hm
    -- Proof comment: precompose a candidate desc map with the tail/full equivalence to get a map
    -- out of the explicit tail direct limit; uniqueness there reduces to stage representatives.
    have hmRaw :
        m.hom.comp e.toAlgHom =
          directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A i₀) G s := by
      apply AlgHom.ext
      intro z
      induction z using Ring.DirectLimit.induction_on with
      | ih j x =>
          have hmStage :
              m.hom (tail_stage_to_direct_limit_algHom A f j x) =
                (s.ι.app j).hom x := by
            simpa [tailCommAlgCoconeToLimit] using
              congrArg (fun f : G.obj j ⟶ s.pt ↦ f.hom x) (hm j)
          have htransport :
              e.toAlgHom
                  (directed_commAlg_stageToRingDirectLimitAlgHom
                    (A₀ := A i₀) G j x) =
                tail_stage_to_direct_limit_algHom A f j x := by
            simpa [G] using
              congrArg
                (fun h :
                  A j.1 →ₐ[A i₀] A∞ ↦ h x)
                (tail_directLimitAlgEquivToFull_comp_tail_stage_to_tail_direct_limit_algHom
                  (A := A) (f := f) (i₀ := i₀) j)
          calc
            m.hom
                (e.toAlgHom
                  (directed_commAlg_stageToRingDirectLimitAlgHom
                    (A₀ := A i₀) G j x)) =
              m.hom (tail_stage_to_direct_limit_algHom A f j x) := by
                rw [htransport]
            _ = (s.ι.app j).hom x := hmStage
            _ =
              directed_commAlg_ringDirectLimitDescAlgHom
                (A₀ := A i₀) G s
                (directed_commAlg_stageToRingDirectLimitAlgHom
                  (A₀ := A i₀) G j x) := by
                    symm
                    simpa [G, directedCommAlg_directLimitCocone] using
                      (directed_commAlg_ringDirectLimitDescAlgHom_comp_of
                        (A₀ := A i₀) G s j x)
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    change m.hom (e.toAlgHom y) =
      (directed_commAlg_ringDirectLimitDescAlgHom (A₀ := A i₀) G s)
        (e.symm.toAlgHom (e.toAlgHom y))
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg
      (fun h :
        directed_commAlg_ringDirectLimit (A₀ := A i₀) G →ₐ[A i₀] ↑s.pt ↦ h y)
      hmRaw

/-- Helper for Chap10 Lemma 10 168 8: the explicit tensor-source direct limit canonically
identifies with the literal source ring `B₀ ⊗[A i₀] A∞`. -/
noncomputable theorem tailTensorSourceDirectLimitAlgEquiv :
    let G :=
      tensor_base_change_commAlgDiagram
        (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
    directed_commAlg_ringDirectLimit (A₀ := B₀) G ≃ₐ[B₀] (B₀ ⊗[A i₀] A∞) :=
by
  let cTail : ColimitCocone (tailCommAlgDiagram A f (i₀ := i₀)) :=
    { cocone := tailCommAlgCoconeToLimit (A := A) (f := f) (i₀ := i₀)
      isColimit := tailCommAlgCoconeToLimit_isColimit (A := A) (f := f) (i₀ := i₀) }
  let G :=
    tensor_base_change_commAlgDiagram
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) B₀
  let hExp :=
    directedCommAlg_directLimitCoconeIsColimit (A₀ := B₀) G
  let hLit :
      IsColimit
        (tensor_base_change_commAlgCocone
          (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) cTail B₀) :=
    tensor_base_change_commAlgCocone_isColimit
      (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) cTail B₀
  let eIso := hExp.coconePointUniqueUpToIso hLit
  have hleft :
      eIso.hom.hom.comp eIso.inv.hom =
        AlgHom.id B₀
          ↑((tensor_base_change_commAlgCocone
              (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) cTail B₀).pt) := by
    -- Proof comment: the categorical inverse laws on the cocone-point iso become the algebra-hom
    -- inverse laws after evaluating on the underlying carriers.
    ext x
    exact congrArg
      (fun f :
        (tensor_base_change_commAlgCocone
          (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) cTail B₀).pt ⟶
            (tensor_base_change_commAlgCocone
              (A₀ := A i₀) (tailCommAlgDiagram A f (i₀ := i₀)) cTail B₀).pt ↦
        f.hom x)
      eIso.hom_inv_id
  have hright :
      eIso.inv.hom.comp eIso.hom.hom =
        AlgHom.id B₀ ↑((directedCommAlg_directLimitCocone (A₀ := B₀) G).pt) := by
    -- Proof comment: the same inverse-law computation on the explicit direct-limit point gives
    -- the reverse algebra-hom identity.
    ext x
    exact congrArg
      (fun f :
        (directedCommAlg_directLimitCocone (A₀ := B₀) G).pt ⟶
            (directedCommAlg_directLimitCocone (A₀ := B₀) G).pt ↦
        f.hom x)
      eIso.inv_hom_id
  -- Proof comment: both the explicit tensor-source direct limit and the literal tensor source
  -- are colimit points of the same tensor-base-changed tail diagram, so uniqueness of colimits
  -- supplies the required algebra equivalence.
  simpa [G, cTail, tensor_base_change_commAlgCocone, tailCommAlgCoconeToLimit] using
    (AlgEquiv.ofAlgHom eIso.hom.hom eIso.inv.hom hleft hright)

/-- Helper for Chap10 Lemma 10 168 8: a raw `B₀`-algebra map into the stage square-zero tensor
target induces the corresponding tensor adjoint over `B₀`. This packages the universal property
that is actually available before the later `Sj`-linear normalization step. -/
noncomputable abbrev stageTensorBaseAdjoint
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀)
    (σj₀ :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
      let Sj := B₀ ⊗[A i₀] A j.1
      let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
      Q₀ →ₐ[B₀] P₀Sq ⊗[B₀] Sj) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
    (Q₀ ⊗[B₀] Sj) →ₐ[B₀] (P₀Sq ⊗[B₀] Sj) :=
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  let Sj := B₀ ⊗[A i₀] A j.1
  let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
  Algebra.TensorProduct.lift σj₀ (algebraMap Sj (P₀Sq ⊗[B₀] Sj))
    (fun _ _ ↦ Commute.all _ _)

/-- Helper for Chap10 Lemma 10 168 8: the raw tensor adjoint agrees with the original descended
section on the `Q₀` factor. -/
lemma stageTensorBaseAdjoint_comp_includeLeft
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀)
    (σj₀ :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
      let Sj := B₀ ⊗[A i₀] A j.1
      let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
      Q₀ →ₐ[B₀] P₀Sq ⊗[B₀] Sj) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
    (stageTensorBaseAdjoint (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀).comp
      (Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] Sj) = σj₀ := by
  dsimp [stageTensorBaseAdjoint]
  -- Proof comment: this is exactly the left computation rule for the tensor-product universal
  -- property, specialized to the descended stage section.
  simpa using
    (Algebra.TensorProduct.lift_comp_includeLeft σj₀
      (algebraMap (B₀ ⊗[A i₀] A j.1)
        ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2) ⊗[B₀]
          (B₀ ⊗[A i₀] A j.1)))
      (fun _ _ ↦ Commute.all _ _))

/-- Helper for Chap10 Lemma 10 168 8: the raw tensor adjoint acts on the stage tensor-source
factor by the canonical algebra map. This isolates the exact compatibility still needed to
promote the raw adjoint to the later `Sj`-linear comparison. -/
lemma stageTensorBaseAdjoint_comp_includeRight
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀)
    (σj₀ :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
      let Sj := B₀ ⊗[A i₀] A j.1
      let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
      Q₀ →ₐ[B₀] P₀Sq ⊗[B₀] Sj) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
    ((stageTensorBaseAdjoint (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀)
        .restrictScalars B₀).comp
      (Algebra.TensorProduct.includeRight : Sj →ₐ[B₀] Q₀ ⊗[B₀] Sj) =
        algebraMap Sj (P₀Sq ⊗[B₀] Sj) := by
  dsimp [stageTensorBaseAdjoint]
  -- Proof comment: the right computation rule records that the raw adjoint is already compatible
  -- with the stage tensor-source factor, so the remaining gap is only the owner API that packages
  -- this compatibility as an `Sj`-algebra map.
  simpa using
    (Algebra.TensorProduct.lift_comp_includeRight σj₀
      (algebraMap (B₀ ⊗[A i₀] A j.1)
        ((MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2) ⊗[B₀]
          (B₀ ⊗[A i₀] A j.1)))
      (fun _ _ ↦ Commute.all _ _))

/-- Helper for Chap10 Lemma 10 168 8: a raw descended `B₀`-algebra map into the stage
square-zero tensor target can be repackaged as the corresponding `Sj`-algebra map on the
base-changed source. -/
noncomputable abbrev stageTensorLinearizationAlgHom
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀)
    (σj₀ :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
      let Sj := B₀ ⊗[A i₀] A j.1
      let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
      Q₀ →ₐ[B₀] P₀Sq ⊗[B₀] Sj) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
    (Q₀ ⊗[B₀] Sj) →ₐ[Sj] (P₀Sq ⊗[B₀] Sj) := by
  letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  let Sj := B₀ ⊗[A i₀] A j.1
  let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
  refine
    { toRingHom :=
        (stageTensorBaseAdjoint (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀).toRingHom
      commutes' := ?_ }
  intro s
  -- Proof comment: the raw tensor adjoint already acts on the right tensor factor by the stage
  -- scalar map, so the only work is to repackage that computation as the `Sj`-algebra
  -- compatibility field.
  change
    ((stageTensorBaseAdjoint (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀)
      ((Algebra.TensorProduct.includeRight : Sj →ₐ[B₀] Q₀ ⊗[B₀] Sj) s)) =
      (algebraMap Sj (P₀Sq ⊗[B₀] Sj)) s
  exact congrArg (fun g : Sj →ₐ[B₀] P₀Sq ⊗[B₀] Sj ↦ g s)
    (stageTensorBaseAdjoint_comp_includeRight
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀)

/-- Helper for Chap10 Lemma 10 168 8: the `Sj`-linearized tensor adjoint still agrees with the
original descended section on the left tensor generator. -/
lemma stageTensorLinearizationAlgHom_comp_includeLeft
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀)
    (σj₀ :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
      let Sj := B₀ ⊗[A i₀] A j.1
      let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
      Q₀ →ₐ[B₀] P₀Sq ⊗[B₀] Sj) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
    ((stageTensorLinearizationAlgHom (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀)
      .restrictScalars B₀).comp
      (Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] Sj) = σj₀ := by
  -- Proof comment: the `Sj`-linearized map uses the same underlying ring hom as the raw tensor
  -- adjoint, so the left-generator formula is unchanged.
  dsimp [stageTensorLinearizationAlgHom]
  exact stageTensorBaseAdjoint_comp_includeLeft
    (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀

/-- Helper for Chap10 Lemma 10 168 8: the `Sj`-linearized tensor adjoint acts on the right tensor
generator by the scalar map of the stage target. -/
lemma stageTensorLinearizationAlgHom_comp_includeRight
    {n c : ℕ} (fs : Fin c → MvPolynomial (Fin n) B₀)
    (j : Set.Ici i₀)
    (σj₀ :
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
      let Sj := B₀ ⊗[A i₀] A j.1
      let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
      Q₀ →ₐ[B₀] P₀Sq ⊗[B₀] Sj) :
    letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
    let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
    let Sj := B₀ ⊗[A i₀] A j.1
    let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
    ((stageTensorLinearizationAlgHom (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀)
      .restrictScalars B₀).comp
      (Algebra.TensorProduct.includeRight : Sj →ₐ[B₀] Q₀ ⊗[B₀] Sj) =
        algebraMap Sj (P₀Sq ⊗[B₀] Sj) := by
  -- Proof comment: the `Sj`-algebra structure was defined precisely so that the right-generator
  -- computation rule of the raw tensor adjoint becomes the scalar-compatibility formula.
  dsimp [stageTensorLinearizationAlgHom]
  exact stageTensorBaseAdjoint_comp_includeRight
    (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs j σj₀

/-- Helper for Chap10 Lemma 10 168 8: once the canonical limit tensor map is smooth, the
remaining source-faithful task is to descend that smoothness to one canonical tail tensor stage.
This packages the single structural blocker behind the later formal-smooth wrapper. -/
lemma smoothCanonicalTailStage_of_limitSmooth
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hSmoothInf :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth) :
    ∃ j : Set.Ici i₀,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).Smooth := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
  have hC₀fp : Algebra.FinitePresentation B₀ C₀ := by
    -- Proof comment: first reinterpret the map-level finite-presentation hypothesis as the
    -- algebra-level finite-presentation input needed to choose one explicit quotient model.
    exact algebraFinitePresentationOfHomFinitePresentation A φ₀ hfp
  obtain ⟨n, c, fs, e₀⟩ :=
    finitePresentationQuotientModel (B₀ := B₀) (D := C₀) hC₀fp
  let SInf := B₀ ⊗[A i₀] A∞
  let Q₀ := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs)
  let IInf : Ideal (MvPolynomial (Fin n) SInf) :=
    Ideal.span (Set.range fun i ↦ MvPolynomial.map (algebraMap B₀ SInf) (fs i))
  letI : Algebra SInf (Q₀ ⊗[B₀] SInf) := Algebra.TensorProduct.rightAlgebra
  let φInf := Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)
  letI : Algebra SInf (C₀ ⊗[A i₀] A∞) := φInf.toRingHom.toAlgebra
  let eInf : (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf] (C₀ ⊗[A i₀] A∞) :=
    limitPresentationTargetAlgEquiv A f φ₀ fs e₀
  have hAlgSmoothInf : Algebra.Smooth SInf (C₀ ⊗[A i₀] A∞) := by
    -- Proof comment: reinterpret the limit-stage `AlgHom.Smooth` hypothesis as the owner-level
    -- algebra smoothness instance on the literal tensor target.
    rw [← RingHom.smooth_algebraMap]
    simpa [φInf] using hSmoothInf
  letI : Algebra.FormallySmooth SInf (C₀ ⊗[A i₀] A∞) := hAlgSmoothInf.formallySmooth
  have hFormQInf : Algebra.FormallySmooth SInf (Q₀ ⊗[B₀] SInf) := by
    -- Proof comment: transport formal smoothness back across the fixed-presentation
    -- normalization, so the section criterion can be applied in the source-faithful spelling.
    exact Algebra.FormallySmooth.of_equiv eInf.symm
  let ePresInf :
      (Q₀ ⊗[B₀] SInf) ≃ₐ[SInf]
        (MvPolynomial (Fin n) SInf ⧸ IInf) :=
    (presentationBaseChangeAlgEquiv
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (fs := fs) A∞).some
  let qInf : MvPolynomial (Fin n) SInf →ₐ[SInf] (Q₀ ⊗[B₀] SInf) :=
    ePresInf.symm.toAlgHom.comp (Ideal.Quotient.mkₐ SInf IInf)
  have hqInfSurj : Function.Surjective qInf := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (ePresInf x)
    exact ⟨y, by simp [qInf]⟩
  obtain ⟨σInfQ, hσInfQ⟩ :=
    (formallySmooth_iff_exists_polynomial_presentation_section_mod_ker_sq
      (R := SInf) (ι := Fin n) (S := Q₀ ⊗[B₀] SInf) qInf hqInfSurj).mp hFormQInf
  have hqInfKer : RingHom.ker qInf.toRingHom = IInf := by
    -- Proof comment: isolate the fixed-presentation kernel computation now, so the remaining
    -- blocker is the actual finite-presentation descent rather than quotient bookkeeping.
    simpa [qInf, ePresInf, Q₀, IInf, SInf] using
      limitPresentationMap_ker (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs
  let P₀Sq := MvPolynomial (Fin n) B₀ ⧸ Ideal.span (Set.range fs) ^ 2
  let eKerSq :
      (MvPolynomial (Fin n) SInf ⧸ RingHom.ker qInf.toRingHom ^ 2) ≃ₐ[SInf]
        (P₀Sq ⊗[B₀] SInf) :=
    limitPresentationKerSquareAlgEquiv (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) fs
  let πInf :
      (P₀Sq ⊗[B₀] SInf) →ₐ[SInf] (Q₀ ⊗[B₀] SInf) :=
    qInf.kerSquareLift.comp eKerSq.symm.toAlgHom
  let σInf :
      (Q₀ ⊗[B₀] SInf) →ₐ[SInf] (P₀Sq ⊗[B₀] SInf) :=
    eKerSq.toAlgHom.comp σInfQ
  have hσInf :
      πInf.comp σInf = AlgHom.id SInf (Q₀ ⊗[B₀] SInf) := by
    -- Proof comment: after naming the normalized limit quotient map `πInf`, the section
    -- identity is exactly the original `hσInfQ` transported across the square-zero
    -- normalization equivalence `eKerSq`.
    simpa [πInf, σInf, AlgHom.comp_assoc] using hσInfQ
  let σInfAdj : Q₀ →ₐ[B₀] (P₀Sq ⊗[B₀] SInf) :=
    σInf.restrictScalars B₀ ∘ₐ (Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] SInf)
  have hσInfAdj :
      πInf.restrictScalars B₀ ∘ₐ σInfAdj =
        (Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] SInf) := by
    -- Proof comment: after restricting scalars from `SInf` to `B₀`, the adjoint limit section
    -- still splits the normalized limit quotient map `πInf`, so the only remaining work is to
    -- descend this split identity to one finite stage.
    ext x
    change
      πInf (σInf ((Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] SInf) x)) =
        (Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] SInf) x
    exact congrArg
      (fun g : (Q₀ ⊗[B₀] SInf) →ₐ[SInf] Q₀ ⊗[B₀] SInf ↦
        g ((Algebra.TensorProduct.includeLeft : Q₀ →ₐ[B₀] Q₀ ⊗[B₀] SInf) x))
      hσInf
  -- Route correction: the proof is now reduced to the fixed-presentation limit section
  -- `σInfAdj`. The remaining owner-level gap is no longer kernel or square-zero transport, but
  -- descending this adjoint section through the tensor-source tail and converting the descended
  -- comparison into a canonical stage section without reintroducing chosen-colimit transport.
  -- The stage-side presentation normalizations are now explicit via
  -- `stagePresentationTargetAlgEquiv`, `stagePresentationMap_ker`, and
  -- `stagePresentationKerSquareAlgEquiv`, so the only missing transport is the filtered-colimit
  -- descent of `σInfAdj` through the tensor-source tail and the stabilization of the resulting
  -- split identity.
  -- TODO for Chap10 Lemma 10 168 8: the new `stageTensorLinearizationAlgHom` bridge resolves the
  -- raw-`B₀` versus `Sj`-algebra mismatch, so the first remaining blocker is now earlier:
  -- `finitePresentation_hom_to_limit_baseChange_descends` needs a directed system whose base stage
  -- is literally `B₀`, whereas the current tensor-source tail starts at `B₀ ⊗[A i₀] A i₀`.
  -- The next proof step therefore needs a dedicated owner-level normalization/descent wrapper that
  -- packages the literal `B₀` stage into the tensor-source tail before the filtered-colimit
  -- descent and stabilization theorems can be applied.
  let _ := hqInfKer
  let _ := πInf
  let _ := hσInf
  let _ := σInfAdj
  let _ := hσInfAdj
  sorry

/-- Helper for Chap10 Lemma 10 168 8: formal smoothness of the canonical limit tensor map should
already descend to one tail stage. The remaining blocker is descending the fixed-presentation
section through the tail system and normalizing its codomain once. -/
lemma formalSmoothLimitTensor_descends_to_tail
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hform :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).FormallySmooth) :
    ∃ j : Set.Ici i₀,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).FormallySmooth := by
  have hSmoothInf :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth := by
    -- Proof comment: the limit tensor map is already smooth because the fixed finite-presentation
    -- hypothesis upgrades the given formal smoothness at the limit stage.
    exact limitTensorSmooth_of_formallySmooth A f φ₀ hform
      (limitTensorMapFinitePresentation A f φ₀ hfp)
  suffices
      ∃ j : Set.Ici i₀,
        letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).Smooth by
    rcases this with ⟨j, hj⟩
    exact ⟨j, hj.formallySmooth⟩
  -- Proof comment: the formal-smooth wrapper now delegates the single remaining structural step
  -- to the owner-level smooth-stage descent helper and then projects back to formal smoothness.
  exact smoothCanonicalTailStage_of_limitSmooth A f φ₀ hfp hSmoothInf

/-- Helper for Chap10 Lemma 10 168 8: once the formal-smooth stage has been produced by the
presentation descent argument, smoothness follows immediately from stagewise finite presentation.
-/
lemma smoothLimitTensor_descends_to_tail_of_limitSmooth
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsmooth :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth) :
    ∃ j : Set.Ici i₀,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).Smooth := by
  -- Proof comment: the owner-level smooth-stage descent helper is already stated at the precise
  -- smooth level needed here, so this wrapper is now just a direct specialization.
  exact smoothCanonicalTailStage_of_limitSmooth A f φ₀ hfp hsmooth

/-- Helper for Chap10 Lemma 10 168 8: smoothness of the canonical limit tensor map should descend
to one tail stage. This is the remaining structural comparison-descent step. -/
lemma smoothLimitTensor_descends_to_tail
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsmooth :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth) :
    ∃ j : Set.Ici i₀,
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).Smooth := by
  -- Proof comment: the remaining work has already been isolated to the single smooth-model
  -- comparison helper above, so this theorem is now just the public wrapper around that blocker.
  exact smoothLimitTensor_descends_to_tail_of_limitSmooth A f φ₀ hfp hsmooth

/-- Chap10 Lemma 10 168 8: if a finitely presented map of stage algebras becomes smooth after base
change to the direct limit ring, then its base change to some later stage is already smooth. -/
@[stacks 0C0B]
theorem exists_smooth_stageBaseChange_of_smooth_limitBaseChange
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsmooth :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).Smooth) :
    ∃ (j : I) (hij : i₀ ≤ j),
      letI : Algebra (A i₀) (A j) := (f i₀ j hij).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j))).Smooth := by
  -- Proof comment: first normalize the target to a witness over the cofinal tail above `i₀`,
  -- where the remaining structural descent will be carried out.
  refine existsStageOfTailProperty ?_
  exact smoothLimitTensor_descends_to_tail A f φ₀ hfp hsmooth

end
