import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_78_6
import StacksProject_2024.stacks_project.Chap15.Lemma_15_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]

local notation "C" => SymmetricAlgebra A M

/- Domain triage:
- primary domain: smooth commutative algebra maps and symmetric algebras;
- sampled owner declarations:
  `Algebra.Smooth`,
  `SymmetricAlgebra`,
  `SymmetricAlgebra.algebraMapInv`,
  `Module.FiniteProjective`;
- best owner abstraction: the source-facing statement should use the canonical smoothness owner
  `Algebra.Smooth A (SymmetricAlgebra A M)` and the project-level finite-projective owner
  `Module.FiniteProjective A M`;
- primitive data: the base ring `A` and the `A`-module `M`;
- derived API: the smoothness criterion for the symmetric algebra.

Source/core/bridge triage:
- `source-facing`: the smoothness criterion for `Sym_A^*(M)`;
- `core/canonical`: `Algebra.Smooth`, `SymmetricAlgebra`, and `Module.FiniteProjective`;
- `bridge/view`: the proof sketch passes through the augmentation
  `SymmetricAlgebra.algebraMapInv` and the conormal computation of Lemma `15.9.12`. -/

-- Proof sketch: for the forward implication, use the augmentation
-- `SymmetricAlgebra.algebraMapInv : SymmetricAlgebra A M →ₐ[A] A` and Lemma `10.139.4` to identify
-- the conormal module of its kernel with `M`, since the positive-degree ideal modulo its square is
-- the degree-one piece. For the reverse implication, choose a finite free presentation of the
-- finite projective module `M`, apply the conormal-sequence computation of Lemma `15.9.12`, and
-- conclude from the characterization of smoothness in Definition `10.137.1`.

/-- Helper for Lemma 15.9.13: the augmentation of the symmetric algebra is a left inverse to the
structure map `A → Sym_A(M)`. -/
noncomputable def symmetricAlgebra_augmentation : C →ₐ[A] A :=
  SymmetricAlgebra.lift (0 : M →ₗ[A] A)

/-- Helper for Lemma 15.9.13: the augmentation of the symmetric algebra is a left inverse to the
structure map `A → Sym_A(M)`. -/
lemma symmetricAlgebra_augmentation_leftInverse :
    Function.LeftInverse (symmetricAlgebra_augmentation (A := A) (M := M)) (algebraMap A C) := by
  -- The augmentation kills positive-degree terms and fixes the scalars from `A`.
  intro a
  simpa [symmetricAlgebra_augmentation] using
    (symmetricAlgebra_augmentation (A := A) (M := M)).commutes a

/-- Helper for Lemma 15.9.13: the augmentation endows `A` with the compatible
`A → Sym_A(M) → A` scalar tower needed for tensor cancellation. -/
lemma symmetricAlgebra_augmentation_isScalarTower :
    let σ : C →ₐ[A] A := symmetricAlgebra_augmentation (A := A) (M := M)
    letI : Algebra C A := σ.toRingHom.toAlgebra
    IsScalarTower A C A := by
  let σ : C →ₐ[A] A := symmetricAlgebra_augmentation (A := A) (M := M)
  letI : Algebra C A := σ.toRingHom.toAlgebra
  -- The augmentation is an `A`-algebra retraction, so the two scalar routes agree.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro a
  change algebraMap A A a = σ (algebraMap A C a)
  simpa using (σ.commutes a).symm

/-- Helper for Lemma 15.9.13: after base change along the augmentation
`Sym_A(M) → A`, the Kähler differentials of the symmetric algebra identify with the original
module `M`. -/
noncomputable def symmetricAlgebra_augmentation_kaehler_equiv :
    let σ : C →ₐ[A] A := symmetricAlgebra_augmentation (A := A) (M := M)
    letI : Algebra C A := σ.toRingHom.toAlgebra
    letI : IsScalarTower A C A := symmetricAlgebra_augmentation_isScalarTower (A := A) (M := M)
    A ⊗[C] Ω[C⁄A] ≃ₗ[A] M :=
  let σ : C →ₐ[A] A := symmetricAlgebra_augmentation (A := A) (M := M)
  letI : Algebra C A := σ.toRingHom.toAlgebra
  letI : IsScalarTower A C A := symmetricAlgebra_augmentation_isScalarTower (A := A) (M := M)
  let eKaehler : C ⊗[A] M ≃ₗ[C] Ω[C⁄A] :=
    LinearEquiv.ofBijective
      ((((KaehlerDifferential.D A C).tensorProductTo).comp
        ((SymmetricAlgebra.ι A M).baseChange C)))
      (symmetricAlgebra_tensorToKaehler_bijective (A := A) (M := M))
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) eKaehler.symm).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A C A A M).trans
      (TensorProduct.lid A M))

/-- Helper for Lemma 15.9.13: smoothness of `Sym_A(M)` forces `M` to be finite projective by
pulling back the finite projective Kähler differential module along the augmentation. -/
lemma finiteProjective_of_smooth_symmetricAlgebra
    (hSmooth : Algebra.Smooth A C) :
    Module.FiniteProjective A M := by
  let σ : C →ₐ[A] A := symmetricAlgebra_augmentation (A := A) (M := M)
  letI : Algebra C A := σ.toRingHom.toAlgebra
  letI : IsScalarTower A C A := symmetricAlgebra_augmentation_isScalarTower (A := A) (M := M)
  letI : Algebra.Smooth A C := hSmooth
  have hfiniteOmega : Module.Finite C Ω[C⁄A] := by
    infer_instance
  have hprojectiveOmega : Module.Projective C Ω[C⁄A] := by
    -- Smooth algebras have projective Kähler differentials.
    infer_instance
  letI : Module.Finite C Ω[C⁄A] := hfiniteOmega
  letI : Module.Projective C Ω[C⁄A] := hprojectiveOmega
  have hfiniteBase : Module.Finite A (A ⊗[C] Ω[C⁄A]) := by
    -- Finiteness survives the augmentation base change.
    infer_instance
  have hprojectiveBase : Module.Projective A (A ⊗[C] Ω[C⁄A]) := by
    -- Projectivity also survives after tensoring with the augmentation algebra.
    infer_instance
  let e := symmetricAlgebra_augmentation_kaehler_equiv (A := A) (M := M)
  -- Transport the finite/projective structure across the augmentation comparison.
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- Helper for Lemma 15.9.13: a split linear map `M ↪ F ↠ M` induces a split algebra map on the
corresponding symmetric algebras. -/
lemma symmetricAlgebra_retraction_of_split_linear_map
    {F : Type*} [AddCommMonoid F] [Module A F]
    (i : M →ₗ[A] F) (s : F →ₗ[A] M)
    (hsi : s.comp i = LinearMap.id) :
    let τ : SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A F :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A F).comp i)
    let σ : SymmetricAlgebra A F →ₐ[A] SymmetricAlgebra A M :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp s)
    σ.comp τ = AlgHom.id A (SymmetricAlgebra A M) := by
  -- Both algebra maps agree on the generators coming from `M`, so generator-ext closes the proof.
  apply SymmetricAlgebra.algHom_ext
  ext m
  have hsimp : s (i m) = m := by
    simpa using congrArg (fun l : M →ₗ[A] M ↦ l m) hsi
  simpa [hsimp]

/-- Helper for Lemma 15.9.13: for a split surjection from the finite free module `A^n`, the
kernel of the induced symmetric-algebra map is generated by the finitely many basis relations. -/
lemma symmetricAlgebra_ker_eq_span_basis_relations
    {n : ℕ} (i : M →ₗ[A] (Fin n → A)) (s : (Fin n → A) →ₗ[A] M)
    (hsi : s.comp i = LinearMap.id) :
    let τ : C →ₐ[A] SymmetricAlgebra A (Fin n → A) :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (Fin n → A)).comp i)
    let σ : SymmetricAlgebra A (Fin n → A) →ₐ[A] C :=
      SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp s)
    RingHom.ker σ.toRingHom =
      Ideal.span
        (Set.range fun j : Fin n ↦
          SymmetricAlgebra.ι A (Fin n → A) (Pi.basisFun A (Fin n) j) -
            τ (σ (SymmetricAlgebra.ι A (Fin n → A) (Pi.basisFun A (Fin n) j))) ) := by
  let τ : C →ₐ[A] SymmetricAlgebra A (Fin n → A) :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (Fin n → A)).comp i)
  let σ : SymmetricAlgebra A (Fin n → A) →ₐ[A] C :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp s)
  let J : Ideal (SymmetricAlgebra A (Fin n → A)) :=
    Ideal.span
      (Set.range fun j : Fin n ↦
        SymmetricAlgebra.ι A (Fin n → A) (Pi.basisFun A (Fin n) j) -
          τ (σ (SymmetricAlgebra.ι A (Fin n → A) (Pi.basisFun A (Fin n) j))) )
  have hτ_σ_ι (x : M) :
      τ (SymmetricAlgebra.ι A M x) =
        SymmetricAlgebra.ι A (Fin n → A) (i x) := by
    simp [τ]
  have hσ_ι (x : Fin n → A) :
      σ (SymmetricAlgebra.ι A (Fin n → A) x) = SymmetricAlgebra.ι A M (s x) := by
    simp [σ]
  have hdiff_ι (x : Fin n → A) :
      SymmetricAlgebra.ι A (Fin n → A) x -
          τ (σ (SymmetricAlgebra.ι A (Fin n → A) x)) =
        SymmetricAlgebra.ι A (Fin n → A) (x - i (s x)) := by
    rw [hσ_ι, hτ_σ_ι, LinearMap.map_sub]
  have hgen_basis (j : Fin n) :
      SymmetricAlgebra.ι A (Fin n → A)
          (Pi.basisFun A (Fin n) j - i (s (Pi.basisFun A (Fin n) j))) ∈ J := by
    -- Each basis relation is one of the chosen ideal generators.
    rw [← hdiff_ι]
    exact Ideal.subset_span (Set.mem_range_self j)
  have hgen (x : Fin n → A) :
      SymmetricAlgebra.ι A (Fin n → A) x -
          τ (σ (SymmetricAlgebra.ι A (Fin n → A) x)) ∈ J := by
    have hxsum : x = ∑ j : Fin n, x j • (Pi.basisFun A (Fin n)) j := by
      simpa [Pi.basisFun_repr] using ((Pi.basisFun A (Fin n)).sum_repr x).symm
    let d : (Fin n → A) →ₗ[A] (Fin n → A) := LinearMap.id - i.comp s
    have hxsum' :
        ∑ j : Fin n, x j • (Pi.basisFun A (Fin n)) j =
          ∑ j : Fin n, (∑ k : Fin n, x k • (Pi.basisFun A (Fin n)) k) j •
            (Pi.basisFun A (Fin n)) j := by
      symm
      simpa [Pi.basisFun_repr] using
        ((Pi.basisFun A (Fin n)).sum_repr (∑ j : Fin n, x j • (Pi.basisFun A (Fin n)) j))
    have hmap :
        d (∑ j : Fin n, (∑ k : Fin n, x k • (Pi.basisFun A (Fin n)) k) j •
          (Pi.basisFun A (Fin n)) j) =
          ∑ j : Fin n, x j • d ((Pi.basisFun A (Fin n)) j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hcoeff : (∑ k : Fin n, x k • (Pi.basisFun A (Fin n)) k) j = x j := by
        simpa [Pi.basisFun] using (congrArg (fun f : Fin n → A ↦ f j) hxsum).symm
      rw [hcoeff]
      rw [map_smul]
    have hx :
        x - i (s x) =
          ∑ j : Fin n, x j • (Pi.basisFun A (Fin n) j - i (s (Pi.basisFun A (Fin n) j))) := by
      calc
        x - i (s x) = d x := by
          rfl
        _ = d (∑ j : Fin n, x j • (Pi.basisFun A (Fin n)) j) := by
          exact congrArg d hxsum
        _ = d (∑ j : Fin n, (∑ k : Fin n, x k • (Pi.basisFun A (Fin n)) k) j •
              (Pi.basisFun A (Fin n)) j) := by
          exact congrArg d hxsum'
        _ = ∑ j : Fin n, x j • d ((Pi.basisFun A (Fin n)) j) := by
          exact hmap
        _ = ∑ j : Fin n, x j • (Pi.basisFun A (Fin n) j - i (s (Pi.basisFun A (Fin n) j))) := by
          rfl
    rw [hdiff_ι, hx, map_sum]
    -- Linearity rewrites the general relation into an `A`-linear combination of the basis ones.
    refine Ideal.sum_mem J fun j _ ↦ ?_
    rw [LinearMap.map_smul]
    simpa [Algebra.smul_def] using
      Ideal.mul_mem_left J (algebraMap A (SymmetricAlgebra A (Fin n → A)) (x j)) (hgen_basis j)
  have hspan_le_ker : J ≤ RingHom.ker σ.toRingHom := by
    -- Every chosen basis relation maps to zero under the quotient map `σ`.
    rw [Ideal.span_le]
    intro y hy
    rcases hy with ⟨j, rfl⟩
    change σ
        ((SymmetricAlgebra.ι A (Fin n → A)) ((Pi.basisFun A (Fin n)) j) -
          τ (σ ((SymmetricAlgebra.ι A (Fin n → A)) ((Pi.basisFun A (Fin n)) j)))) = 0
    rw [map_sub, hσ_ι, hτ_σ_ι, hσ_ι]
    have hsis :
        s (i (s ((Pi.basisFun A (Fin n)) j))) = s ((Pi.basisFun A (Fin n)) j) := by
      simpa using congrArg (fun l : M →ₗ[A] M ↦ l (s ((Pi.basisFun A (Fin n)) j))) hsi
    rw [hsis]
    simp
  have hdiff_all (y : SymmetricAlgebra A (Fin n → A)) :
      y - τ (σ y) ∈ J := by
    induction y using SymmetricAlgebra.induction with
    | algebraMap a =>
        rw [σ.commutes, τ.commutes]
        simpa using J.zero_mem
    | ι x =>
        exact hgen x
    | add a b ha hb =>
        have hadd :
            a + b - τ (σ (a + b)) = (a - τ (σ a)) + (b - τ (σ b)) := by
          rw [map_add, map_add]
          ring
        rw [hadd]
        exact J.add_mem ha hb
    | mul a b ha hb =>
        have hmul :
            a * b - τ (σ (a * b)) =
              a * (b - τ (σ b)) + (a - τ (σ a)) * τ (σ b) := by
          rw [map_mul, map_mul]
          ring
        rw [hmul]
        exact J.add_mem
          (Ideal.mul_mem_left J a hb)
          (by simpa [mul_comm] using Ideal.mul_mem_left J (τ (σ b)) ha)
  have hker_le_span : RingHom.ker σ.toRingHom ≤ J := by
    intro y hy
    have hy0 : σ y = 0 := by
      simpa [RingHom.mem_ker] using hy
    have hτσy : τ (σ y) = 0 := by
      rw [hy0]
      exact map_zero τ
    simpa [hτσy] using hdiff_all y
  simpa [τ, σ, J] using le_antisymm hker_le_span hspan_le_ker

/-- Helper for Lemma 15.9.13: a finite projective module should give a smooth symmetric algebra
once the split finite free presentation is turned into the conormal splitting of
Lemma `15.9.12`. -/
lemma smooth_symmetricAlgebra_of_finite_projective
    (hM : Module.FiniteProjective A M) :
    Algebra.Smooth A C := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  letI : Module.Finite A M := hM.1
  letI : Module.Projective A M := hM.2
  obtain ⟨n, s, i, hsurj, _, hsi⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let τ : C →ₐ[A] SymmetricAlgebra A (Fin n → A) :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A (Fin n → A)).comp i)
  let σ : SymmetricAlgebra A (Fin n → A) →ₐ[A] C :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp s)
  have hστ : σ.comp τ = AlgHom.id A C :=
    symmetricAlgebra_retraction_of_split_linear_map (A := A) (M := M) i s hsi
  have hσsurj : Function.Surjective σ := by
    -- The section `τ` gives a right inverse to `σ`, hence `σ` is surjective.
    exact Function.RightInverse.surjective (DFunLike.congr_fun hστ)
  have hfreeFormallySmooth : Algebra.FormallySmooth A (SymmetricAlgebra A (Fin n → A)) := by
    -- The finite free symmetric algebra is a polynomial ring in `n` variables.
    exact Algebra.FormallySmooth.of_equiv
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun A (Fin n))).symm
  have hformallySmooth : Algebra.FormallySmooth A C := by
    letI : Algebra.FormallySmooth A (SymmetricAlgebra A (Fin n → A)) := hfreeFormallySmooth
    -- Route correction: descend formal smoothness through the split surjection `σ`.
    refine Algebra.FormallySmooth.of_split σ
      ((Ideal.Quotient.mkₐ A (RingHom.ker σ.toRingHom ^ 2)).comp τ) ?_
    apply SymmetricAlgebra.algHom_ext
    ext m
    change
      σ.kerSquareLift
          ((Ideal.Quotient.mkₐ A (RingHom.ker σ.toRingHom ^ 2))
            (τ ((SymmetricAlgebra.ι A M) m))) =
        (SymmetricAlgebra.ι A M) m
    change σ (τ ((SymmetricAlgebra.ι A M) m)) = (SymmetricAlgebra.ι A M) m
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : C →ₐ[A] C ↦ f ((SymmetricAlgebra.ι A M) m)) hστ
  have hfreeFinitePresentation : Algebra.FinitePresentation A (SymmetricAlgebra A (Fin n → A)) := by
    -- The finite free symmetric algebra is equivalent to a finitely presented polynomial algebra.
    exact Algebra.FinitePresentation.equiv
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun A (Fin n))).symm
  have hkerσ : (RingHom.ker σ.toRingHom).FG := by
    -- The kernel is generated by the finitely many basis relations coming from the section.
    rw [symmetricAlgebra_ker_eq_span_basis_relations (A := A) (M := M) i s hsi]
    exact Submodule.fg_span (Set.finite_range _)
  have hfinitePresentation : Algebra.FinitePresentation A C := by
    letI : Algebra.FinitePresentation A (SymmetricAlgebra A (Fin n → A)) := hfreeFinitePresentation
    -- A surjection from a finitely presented algebra with finitely generated kernel stays finitely
    -- presented.
    exact Algebra.FinitePresentation.of_surjective (f := σ) hσsurj hkerσ
  exact
    { formallySmooth := hformallySmooth
      finitePresentation := hfinitePresentation }

/-- Lemma 15.9.13: the symmetric algebra `Sym_A^*(M)` is smooth over `A` if and only if `M` is a
finite `A`-module and a projective `A`-module. -/
theorem smooth_symmetricAlgebra_iff_finite_and_projective :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔
      Module.FiniteProjective A M := by
  constructor
  · intro hSmooth
    -- The forward implication is exactly the augmentation pullback of `Ω[Sym_A(M)⁄A]`.
    exact finiteProjective_of_smooth_symmetricAlgebra (A := A) (M := M) hSmooth
  · intro hM
    -- The reverse implication is delegated to the split-presentation helper above.
    exact smooth_symmetricAlgebra_of_finite_projective (A := A) (M := M) hM

end
