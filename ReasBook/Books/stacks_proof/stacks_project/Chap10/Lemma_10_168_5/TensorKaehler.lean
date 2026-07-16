import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_127_5
import stacks_proof.stacks_project.Chap10.Lemma_10_131_9
import stacks_proof.stacks_project.Chap10.Lemma_10_131_14
import stacks_proof.stacks_project.Chap10.Lemma_10_151_2

-- Stable helper declarations split out for Lemma 10.168.5.

open CategoryTheory Limits
open scoped TensorProduct

universe u v

section

variable {A₀ : Type u} [CommRing A₀]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A₀) [HasColimit F]
variable {B₀ C₀ : Type u} [CommRing B₀] [CommRing C₀]
variable [Algebra A₀ B₀] [Algebra A₀ C₀]


/-- Helper for Lemma 10.168.5: the stage tensor-product base-change hom of a finite-type map is
again of finite type. -/
theorem tensor_base_change_hom_finiteType
    (φ₀ : B₀ →ₐ[A₀] C₀) (hφ₀ : φ₀.FiniteType) (j : J) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).FiniteType := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] ↑(F.obj j)
  let e :=
    (Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange
        (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j))).toRingEquiv
  let fbase : S →+* (S ⊗[B₀] C₀) :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[B₀] (S ⊗[B₀] C₀)).toRingHom
  -- Finite type is stable under the literal base change along `B₀ → S`.
  have hbaseAlg : Algebra.FiniteType S (S ⊗[B₀] C₀) := by
    letI : Algebra.FiniteType B₀ C₀ := by
      simpa [AlgHom.FiniteType, RingHom.FiniteType] using hφ₀
    exact Algebra.FiniteType.baseChange (R := B₀) (A := C₀) (B := S)
  have hfbase : @RingHom.FiniteType S (S ⊗[B₀] C₀) inferInstance inferInstance fbase := by
    -- Package the base-changed algebra structure as the corresponding finite-type ring map.
    unfold fbase
    exact RingHom.finiteType_algebraMap.mpr hbaseAlg
  have he :
      e.toRingHom.comp fbase =
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).toRingHom := by
    -- The standard `comm` plus `cancelBaseChange` transport rewrites the literal base change
    -- into the tensor-product map appearing in the statement.
    ext b
    · -- On the `B₀`-generator, the composite sends `b ⊗ 1` to `φ₀ b ⊗ 1`.
      change
        (Algebra.TensorProduct.cancelBaseChange
          (R := A₀) (S := B₀) (T := C₀) (A := C₀) (B := ↑(F.obj j)))
          ((Algebra.TensorProduct.comm (R := B₀) (A := S) (B := C₀))
            ((((b ⊗ₜ[A₀] (1 : ↑(F.obj j))) : S) ⊗ₜ[B₀] (1 : C₀)))) =
          φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j))
      simp [S, Algebra.smul_def]
      simpa using
        (show (algebraMap B₀ C₀) b ⊗ₜ[A₀] (1 : ↑(F.obj j)) = φ₀ b ⊗ₜ[A₀] (1 : ↑(F.obj j)) from
          rfl)
    · -- On the stage-ring generator, the composite fixes `1 ⊗ a`.
      simpa [e, fbase, S] using
        (show
          ((e.toRingHom.comp fbase).comp Algebra.TensorProduct.includeRight.toRingHom) b =
            ((Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ ↑(F.obj j))).comp
              Algebra.TensorProduct.includeRight.toRingHom) b from
          rfl)
  have hcomp : (e.toRingHom.comp fbase).FiniteType :=
    RingHom.finiteType_respectsIso.1 _ e hfbase
  -- After rewriting the transported base-change map, this is exactly the desired finite-type
  -- statement for the tensor-product hom.
  rw [AlgHom.FiniteType]
  rw [← he]
  exact hcomp

/-- Helper for Lemma 10.168.5: if a finite family generates an algebra, then the differentials of
that family span the Kähler differentials. -/
theorem kaehler_generators_span_top_of_adjoin_eq_top
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (x : Fin n → S) (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    Submodule.span S (Set.range fun i : Fin n ↦ KaehlerDifferential.D R S (x i)) = ⊤ := by
  let f : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval x
  have hsurj : Function.Surjective f := by
    -- Proof comment: the chosen family generates exactly when the corresponding polynomial
    -- evaluation map is surjective.
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    simpa [f] using hx
  let P : Algebra.Generators R S (Fin n) := Algebra.Generators.ofAlgHom f hsurj
  have hval : P.val = x := by
    -- Proof comment: the generator family attached to `aeval x` is exactly the original family.
    ext i
    change f (MvPolynomial.X i) = x i
    simp [f]
  have himage :
      P.toExtension.toKaehler '' Set.range P.cotangentSpaceBasis =
        Set.range fun i : Fin n ↦ KaehlerDifferential.D R S (x i) := by
    -- Proof comment: the canonical cotangent basis maps to the universal differentials of the
    -- chosen generators.
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      rw [← hval]
      simp
    · rintro ⟨i, rfl⟩
      refine ⟨P.cotangentSpaceBasis i, ⟨i, rfl⟩, ?_⟩
      rw [← hval]
      simp
  have hbasis :
      Submodule.span S (Set.range P.cotangentSpaceBasis) =
        (⊤ : Submodule S P.toExtension.CotangentSpace) := by
    simpa using (Module.Basis.span_eq P.cotangentSpaceBasis)
  calc
    Submodule.span S (Set.range fun i : Fin n ↦ KaehlerDifferential.D R S (x i)) =
      Submodule.map P.toExtension.toKaehler
        (Submodule.span S (Set.range P.cotangentSpaceBasis)) := by
          rw [Submodule.map_span, himage]
    _ = Submodule.map P.toExtension.toKaehler (⊤ : Submodule S P.toExtension.CotangentSpace) := by
          rw [hbasis]
    _ = ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top.2 P.toExtension.toKaehler_surjective]

/-- Helper for Lemma 10.168.5: if `c` lies in the `B₀`-subalgebra generated by `x`, then the pure
tensor `c ⊗ 1` lies in the `(B₀ ⊗[A₀] R)`-subalgebra generated by the pure tensors `x i ⊗ 1`. -/
theorem tensor_base_change_pure_tensor_mem_adjoin
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (R : Type u) [CommRing R] [Algebra A₀ R] {c : C₀}
    (hc :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      c ∈ Algebra.adjoin B₀ (Set.range x)) :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    c ⊗ₜ[A₀] (1 : R) ∈
      Algebra.adjoin (B₀ ⊗[A₀] R)
        (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] R
  letI : Algebra S (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  -- Proof comment: build `c ⊗ 1` inside the tensor-base-change adjoin by induction on the
  -- original proof that `c` lies in the `B₀`-adjoin of the family `x`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hc
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  · intro b
    -- Proof comment: coefficients from `B₀` become scalars coming from the base algebra
    -- `B₀ ⊗[A₀] R`.
    change algebraMap S (C₀ ⊗[A₀] R) ((b : B₀) ⊗ₜ[A₀] (1 : R)) ∈
      Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))
    exact Subalgebra.algebraMap_mem _ _
  · intro y z _ _ hy hz
    simpa [TensorProduct.add_tmul] using Subalgebra.add_mem
      (Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))) hy hz
  · intro y z _ _ hy hz
    simpa [Algebra.TensorProduct.tmul_mul_tmul] using
      Subalgebra.mul_mem
        (Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))) hy hz

/-- Helper for Lemma 10.168.5: the pure tensors `x i ⊗ 1` still generate the base-changed target
algebra over `B₀ ⊗[A₀] R`. -/
theorem tensor_base_change_comm_cancel_adjoin_eq_top
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hx :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (Set.range x) = ⊤)
    (R : Type u) [CommRing R] [Algebra A₀ R] :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    Algebra.adjoin (B₀ ⊗[A₀] R)
      (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) = ⊤ := by
  letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
  let S := B₀ ⊗[A₀] R
  letI : Algebra S (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  apply top_unique
  intro z hz
  -- Proof comment: every element of the tensor product is built from pure tensors, and each pure
  -- tensor `c ⊗ r` is a scalar multiple of the already-controlled tensor `c ⊗ 1`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact Subalgebra.zero_mem _ 
  · intro c r
    have hc : c ∈ Algebra.adjoin B₀ (Set.range x) := by
      simpa [hx] using (show c ∈ (⊤ : Subalgebra B₀ C₀) from trivial)
    have hc' :
        c ⊗ₜ[A₀] (1 : R) ∈
          Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) :=
      tensor_base_change_pure_tensor_mem_adjoin (φ₀ := φ₀) x R hc
    have hs :
        algebraMap S (C₀ ⊗[A₀] R) ((1 : B₀) ⊗ₜ[A₀] r) ∈
          Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) :=
      Subalgebra.algebraMap_mem _ _
    have hmul :
        algebraMap S (C₀ ⊗[A₀] R) ((1 : B₀) ⊗ₜ[A₀] r) * (c ⊗ₜ[A₀] (1 : R)) ∈
          Algebra.adjoin S (Set.range fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R)) :=
      Subalgebra.mul_mem _ hs hc'
    have hEq :
        algebraMap S (C₀ ⊗[A₀] R) ((1 : B₀) ⊗ₜ[A₀] r) * (c ⊗ₜ[A₀] (1 : R)) =
          c ⊗ₜ[A₀] r := by
      change
        (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)) ((1 : B₀) ⊗ₜ[A₀] r) *
            (c ⊗ₜ[A₀] (1 : R)) =
          c ⊗ₜ[A₀] r
      rw [Algebra.TensorProduct.map_tmul]
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hEq] at hmul
    exact hmul
  · intro z₁ z₂ hz₁ hz₂
    exact Subalgebra.add_mem _ hz₁ hz₂

/-- Helper for Lemma 10.168.5: the same finite generating family still spans the Kähler
differentials after tensoring with any `A₀`-algebra. -/
theorem tensor_base_change_kaehler_generators_span_top
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hx :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (Set.range x) = ⊤)
    (R : Type u) [CommRing R] [Algebra A₀ R] :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    Submodule.span (C₀ ⊗[A₀] R)
      (Set.range fun i : Fin n ↦
        KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x i ⊗ₜ[A₀] (1 : R))) = ⊤ := by
  letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  -- Proof comment: once the pure tensors still generate the base-changed algebra, the standard
  -- finite-generation statement for Kähler differentials applies verbatim.
  simpa using
    kaehler_generators_span_top_of_adjoin_eq_top
      (R := B₀ ⊗[A₀] R) (S := C₀ ⊗[A₀] R)
      (x := fun i : Fin n ↦ x i ⊗ₜ[A₀] (1 : R))
      (tensor_base_change_comm_cancel_adjoin_eq_top (φ₀ := φ₀) x hx R)

/-- Helper for Lemma 10.168.5: formal unramifiedness of the tensor-base-changed map makes the
target Kähler differential module a subsingleton. -/
theorem tensor_base_change_subsingleton_kaehlerDifferential
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (R : Type u) [CommRing R] [Algebra A₀ R]
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).FormallyUnramified) :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    Subsingleton (KaehlerDifferential (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R)) := by
  letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  letI : Algebra.FormallyUnramified (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) := hfu
  -- Proof comment: this is exactly the canonical `FormallyUnramified` owner instance on
  -- Kähler differentials.
  infer_instance

/-- Helper for Lemma 10.168.5: under formal unramifiedness after tensor base change, every
distinguished differential `d(x ⊗ 1)` vanishes in the target Kähler differential module. -/
theorem tensor_base_change_D_tmul_one_eq_zero
    (φ₀ : B₀ →ₐ[A₀] C₀)
    (R : Type u) [CommRing R] [Algebra A₀ R]
    (hfu : (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).FormallyUnramified)
    (x : C₀) :
    letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
      (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
    KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x ⊗ₜ[A₀] (1 : R)) = 0 := by
  -- Proof comment: once the target differential module is subsingleton, every generator equals
  -- `0`.
  let hsub :=
    tensor_base_change_subsingleton_kaehlerDifferential (φ₀ := φ₀) R hfu
  exact @Subsingleton.elim _ hsub _ _

/-- Helper for Lemma 10.168.5: if the distinguished differentials of a finite generating family
span the stage Kähler differential module and all vanish, then the stage map is formally
unramified. -/
theorem tensor_base_change_formallyUnramified_of_generator_zero
    (φ₀ : B₀ →ₐ[A₀] C₀) {n : ℕ} (x : Fin n → C₀)
    (hx :
      letI : Algebra B₀ C₀ := φ₀.toRingHom.toAlgebra
      Algebra.adjoin B₀ (Set.range x) = ⊤)
    (R : Type u) [CommRing R] [Algebra A₀ R]
    (hz :
      ∀ k : Fin n,
        letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
          (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
        KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x k ⊗ₜ[A₀] (1 : R)) = 0) :
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).FormallyUnramified := by
  letI : Algebra (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) :=
    (Algebra.TensorProduct.map φ₀ (AlgHom.id A₀ R)).toRingHom.toAlgebra
  let Ω := KaehlerDifferential (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R)
  have hspan :
      Submodule.span (C₀ ⊗[A₀] R)
        (Set.range fun i : Fin n ↦
          KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x i ⊗ₜ[A₀] (1 : R))) = ⊤ :=
    tensor_base_change_kaehler_generators_span_top (φ₀ := φ₀) x hx R
  have hzero_all : ∀ z : Ω, z = 0 := by
    intro z
    have hzmem :
        z ∈ Submodule.span (C₀ ⊗[A₀] R)
          (Set.range fun i : Fin n ↦
            KaehlerDifferential.D (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R) (x i ⊗ₜ[A₀] (1 : R))) := by
      simpa [hspan] using (show z ∈ (⊤ : Submodule (C₀ ⊗[A₀] R) Ω) from trivial)
    -- Proof comment: span induction reduces every differential to the chosen vanishing family.
    refine Submodule.span_induction (p := fun y _ ↦ y = 0) ?_ ?_ ?_ ?_ hzmem
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hz i
    · simp
    · intro y z _ _ hy hz'
      rw [hy, hz', add_zero]
    · intro a y _ hy
      rw [hy, smul_zero]
  -- Proof comment: `Ω = 0` is exactly the Kähler criterion for formal unramifiedness.
  refine (Algebra.formallyUnramified_iff (B₀ ⊗[A₀] R) (C₀ ⊗[A₀] R)).2 ?_
  exact ⟨fun y z ↦ (hzero_all y).trans (hzero_all z).symm⟩

end
