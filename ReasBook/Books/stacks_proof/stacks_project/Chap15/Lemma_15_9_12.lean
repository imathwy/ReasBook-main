import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]
variable {m : ℕ}

local notation "C" => SymmetricAlgebra A M

variable (q : (Fin m →₀ A) →ₗ[A] M)

/-- Helper for Lemma 15.9.12: a module over a commutative ring carries an additive-group structure,
so `LinearMap.exact_subtype_ker_map` applies to the presentation map despite the source-facing
`AddCommMonoid` binder. -/
lemma exact_subtype_ker_map_of_surjective
    (_hq : Function.Surjective q) :
    Function.Exact q.ker.subtype q := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  -- Route correction: the previous route searched for a new exactness theorem, but the real
  -- blocker is only the local additive-group instance needed by the owner theorem.
  simpa using LinearMap.exact_subtype_ker_map q

/-- Helper for Lemma 15.9.12: tensoring an exact-surjective pair on the left preserves both
exactness and surjectivity. -/
lemma lTensor_exact_surjective_of_exact_surjective
    {R : Type*} [CommRing R]
    {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.lTensor Q f) (LinearMap.lTensor Q g) ∧
      Function.Surjective (LinearMap.lTensor Q g) := by
  constructor
  · -- Right exactness of tensor product is the canonical owner for the exactness claim.
    exact lTensor_exact Q hfg hg
  · -- Surjectivity also survives after tensoring on the left.
    exact LinearMap.lTensor_surjective Q hg

/- Domain-style sampling:
- primary domain: symmetric-algebra presentations, tensor base change, and the conormal/Kähler
  exact sequence;
- sampled owner declarations:
  `LinearMap.lTensor`,
  `LinearMap.lTensor_surjective`,
  `lTensor_exact`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`;
- best owner abstraction: the canonical tensorized presentation maps attached to the kernel
  inclusion `i : q.ker →ₗ[A] Fin m →₀ A`, namely `i.lTensor C` and `q.lTensor C`, with the
  right-exactness of tensor product as the owner for the tensor sequence; the Kähler map is the
  source-facing specialization obtained by composing `q.lTensor C`,
  `(SymmetricAlgebra.ι A M).lTensor C`, and `Derivation.tensorProductTo` for the universal
  derivation on `C`;
- primitive data: the surjective module map `q` and the kernel inclusion
  `i : q.ker →ₗ[A] Fin m →₀ A`;
- derived API: the source-facing description of that canonical Kähler map on the standard basis of
  `Fin m →₀ A`.

Layer triage:
- `source-facing`: the conormal/Kähler exact sequence attached to the presentation `q`;
- `core/canonical`: the tensorized presentation maps `i.baseChange C` and `q.baseChange C`,
  together with the generic right-exactness owners `lTensor_exact` and
  `LinearMap.lTensor_surjective`;
- `bridge/view`: the identification of `C ⊗[A] A^{⊕ m}` with `⨁_{j=1}^m C \, dy_j`. -/

/-- Helper for Lemma 15.9.12: tensoring the presentation
`0 → ker(q) → A^{⊕ m} → M → 0` with `C = Sym_A(M)` preserves exactness on the left and
surjectivity on the right. -/
lemma baseChange_exact_surjective_of_kernel_presentation
    (hq : Function.Surjective q) :
    Function.Exact (LinearMap.lTensor C q.ker.subtype) (LinearMap.lTensor C q) ∧
      Function.Surjective (LinearMap.lTensor C q) :=
  by
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
    -- After transporting the additive-group structure across `q`, right exactness of tensor
    -- product is the canonical owner for the tensorized presentation sequence.
    simpa using
      (lTensor_exact_surjective_of_exact_surjective
        (R := A) (Q := C) (M := q.ker) (N := Fin m →₀ A) (P := M)
        (f := q.ker.subtype) (g := q)
        (exact_subtype_ker_map_of_surjective (q := q) hq) hq)

section SymmetricAlgebraDerivations

variable {N : Type*} [AddCommGroup N] [Module (SymmetricAlgebra A M) N] [Module A N]
  [IsScalarTower A (SymmetricAlgebra A M) N]

/-- Helper for Lemma 15.9.12: over the commutative algebra `Sym_A(M)`, the opposite-module action
needed by `TrivSqZeroExt` is induced from the ordinary scalar action. -/
private instance symmetricAlgebraDerivationsModuleOpposite :
    Module Cᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id C).fromOpposite mul_comm)

/-- Helper for Lemma 15.9.12: the scalar action of `Sym_A(M)` on `N` is central. -/
private instance symmetricAlgebraDerivationsIsCentralScalar :
    IsCentralScalar C N :=
  ⟨fun _ _ => rfl⟩

/-- Helper for Lemma 15.9.12: the square-zero lift attached to a linear map on generators sends
`m` to `(ι(m), f(m))`. -/
private noncomputable def symmetricAlgebra_toTrivSqZero (f : M →ₗ[A] N) :
    C →ₐ[A] TrivSqZeroExt C N :=
  -- The symmetric algebra lift packages the source-faithful square-zero extension step.
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).prod f)

/-- Helper for Lemma 15.9.12: the first projection of the square-zero lift is the identity on the
symmetric algebra. -/
private theorem symmetricAlgebra_toTrivSqZero_fst (f : M →ₗ[A] N) :
    (TrivSqZeroExt.fstHom A C N).comp (symmetricAlgebra_toTrivSqZero (A := A) (M := M) f) =
      AlgHom.id A C := by
  -- Both algebra maps agree on the generators, so the symmetric-algebra universal property closes
  -- the comparison.
  apply SymmetricAlgebra.algHom_ext
  ext m
  simp [symmetricAlgebra_toTrivSqZero]
  rfl

/-- Helper for Lemma 15.9.12: the second projection of the square-zero lift satisfies Leibniz. -/
private theorem symmetricAlgebraDerivationOfLinearMap_leibniz (f : M →ₗ[A] N) :
    ∀ x y : C,
      (((TrivSqZeroExt.sndHom C N).restrictScalars A).comp
        (symmetricAlgebra_toTrivSqZero (A := A) (M := M) f).toLinearMap) (x * y) =
          x • (((TrivSqZeroExt.sndHom C N).restrictScalars A).comp
            (symmetricAlgebra_toTrivSqZero (A := A) (M := M) f).toLinearMap) y +
          y • (((TrivSqZeroExt.sndHom C N).restrictScalars A).comp
            (symmetricAlgebra_toTrivSqZero (A := A) (M := M) f).toLinearMap) x := by
  let F : C →ₐ[A] TrivSqZeroExt C N := symmetricAlgebra_toTrivSqZero (A := A) (M := M) f
  intro x y
  -- Multiplication in the square-zero extension rewrites the second component into Leibniz form.
  change TrivSqZeroExt.snd (F (x * y)) = x • TrivSqZeroExt.snd (F y) + y • TrivSqZeroExt.snd (F x)
  rw [map_mul, TrivSqZeroExt.snd_mul]
  rw [show TrivSqZeroExt.fst (F x) = x by
        simpa using congrArg (fun g : C →ₐ[A] C => g x)
          (symmetricAlgebra_toTrivSqZero_fst (A := A) (M := M) (N := N) f)]
  rw [show TrivSqZeroExt.fst (F y) = y by
        simpa using congrArg (fun g : C →ₐ[A] C => g y)
          (symmetricAlgebra_toTrivSqZero_fst (A := A) (M := M) (N := N) f)]
  simp

/-- Helper for Lemma 15.9.12: composing the square-zero lift with the second projection gives the
derivation corresponding to the chosen generator map. -/
private noncomputable def symmetricAlgebraDerivationOfLinearMap (f : M →ₗ[A] N) :
    Derivation A C N :=
  Derivation.mk'
    (((TrivSqZeroExt.sndHom C N).restrictScalars A).comp
      (symmetricAlgebra_toTrivSqZero (A := A) (M := M) f).toLinearMap)
    (symmetricAlgebraDerivationOfLinearMap_leibniz (A := A) (M := M) (N := N) f)

omit [IsScalarTower A C N] in
/-- Helper for Lemma 15.9.12: two derivations out of the symmetric algebra agree once they agree
on the generators. -/
private theorem derivation_eq_of_eq_on_ι {D E : Derivation A C N}
    (h : ∀ m, D (SymmetricAlgebra.ι A M m) = E (SymmetricAlgebra.ι A M m)) :
    D = E := by
  -- The symmetric algebra is generated by scalars and `ι(M)`, and both derivations satisfy the
  -- same additivity and Leibniz rules.
  ext x
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
      simp [Derivation.map_algebraMap]
  | ι m =>
      exact h m
  | mul x y hx hy =>
      simp [Derivation.leibniz, hx, hy]
  | add x y hx hy =>
      simp [Derivation.map_add, hx, hy]

/-- Helper for Lemma 15.9.12: linear maps on the generators of the symmetric algebra should be
identified with derivations out of `Sym_A(M)`. -/
private noncomputable def symmetricAlgebra_linearMapEquivDerivation :
    (M →ₗ[A] N) ≃ₗ[C] Derivation A C N :=
  { toFun := symmetricAlgebraDerivationOfLinearMap (A := A) (M := M) (N := N)
    invFun := fun D => D.toLinearMap.comp (SymmetricAlgebra.ι A M)
    left_inv := by
      intro f
      ext m
      -- On generators the constructed derivation was built to recover `f`.
      simp [symmetricAlgebraDerivationOfLinearMap, symmetricAlgebra_toTrivSqZero]
      rfl
    right_inv := by
      intro D
      -- Once the constructed derivation and `D` agree on `ι(M)`, generator-ext closes the proof.
      apply derivation_eq_of_eq_on_ι (A := A) (M := M) (N := N)
      intro m
      simp [symmetricAlgebraDerivationOfLinearMap, symmetricAlgebra_toTrivSqZero]
      rfl
    map_add' := by
      intro f g
      apply derivation_eq_of_eq_on_ι (A := A) (M := M) (N := N)
      intro m
      simp [symmetricAlgebraDerivationOfLinearMap, symmetricAlgebra_toTrivSqZero]
      rfl
    map_smul' := by
      intro c f
      apply derivation_eq_of_eq_on_ι (A := A) (M := M) (N := N)
      intro m
      simp [symmetricAlgebraDerivationOfLinearMap, symmetricAlgebra_toTrivSqZero]
      rfl }

/-- Helper for Lemma 15.9.12: the derivation corresponding to a generator map evaluates back to
that generator map on `ι`. -/
  lemma symmetricAlgebra_linearMapEquivDerivation_apply_ι
    (f : M →ₗ[A] N) (m : M) :
    symmetricAlgebra_linearMapEquivDerivation (A := A) (M := M) (N := N) f
      (SymmetricAlgebra.ι A M m) = f m := by
  -- This is the direct computation on generators coming from the square-zero lift.
  simp [symmetricAlgebra_linearMapEquivDerivation, symmetricAlgebraDerivationOfLinearMap,
    symmetricAlgebra_toTrivSqZero]
  rfl

end SymmetricAlgebraDerivations

/-- Helper for Lemma 15.9.12: the universal derivation on the symmetric algebra identifies
`C ⊗[A] M` with `Ω[C⁄A]`. -/
lemma symmetricAlgebra_tensorToKaehler_bijective :
    Function.Bijective
      ((((KaehlerDifferential.D A C).tensorProductTo).comp
        ((SymmetricAlgebra.ι A M).baseChange C)) : C ⊗[A] M →ₗ[C] Ω[C⁄A]) :=
  by
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
    let κ : C ⊗[A] M →ₗ[C] Ω[C⁄A] :=
      (((KaehlerDifferential.D A C).tensorProductTo).comp ((SymmetricAlgebra.ι A M).baseChange C))
    let oneTensor : M →ₗ[A] C ⊗[A] M := TensorProduct.mk A C M (1 : C)
    let δ : Derivation A C (C ⊗[A] M) :=
      symmetricAlgebra_linearMapEquivDerivation (A := A) (M := M) (N := C ⊗[A] M) oneTensor
    let ψ : Ω[C⁄A] →ₗ[C] C ⊗[A] M := Derivation.liftKaehlerDifferential δ
    have hψκ : ψ.comp κ = (LinearMap.id : C ⊗[A] M →ₗ[C] C ⊗[A] M) := by
      -- On pure tensors, `κ` applies the universal derivation to the generator and `ψ` sends that
      -- differential back to the original tensor.
      apply LinearMap.ext
      intro x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp [κ, ψ]
      · intro c m
        simp [κ, ψ, δ, oneTensor, LinearMap.baseChange_eq_ltensor,
          Derivation.liftKaehlerDifferential_comp_D, Derivation.tensorProductTo_tmul,
          symmetricAlgebra_linearMapEquivDerivation_apply_ι]
        rw [← TensorProduct.tmul_eq_smul_one_tmul]
      · intro x y hx hy
        simpa using congrArg₂ (· + ·) hx hy
    have hcompDer :
        (κ.comp ψ).compDer (KaehlerDifferential.D A C) =
          (LinearMap.id : Ω[C⁄A] →ₗ[C] Ω[C⁄A]).compDer (KaehlerDifferential.D A C) := by
      -- The two endomorphisms of `Ω[C⁄A]` induce the same derivation because they agree on the
      -- generating differentials `D(ι(m))`.
      apply derivation_eq_of_eq_on_ι (A := A) (M := M) (N := Ω[C⁄A])
      intro m
      simp [κ, ψ, δ, oneTensor, LinearMap.baseChange_eq_ltensor,
        Derivation.liftKaehlerDifferential_comp_D, Derivation.tensorProductTo_tmul,
        symmetricAlgebra_linearMapEquivDerivation_apply_ι]
    have hκψ : κ.comp ψ = (LinearMap.id : Ω[C⁄A] →ₗ[C] Ω[C⁄A]) := by
      -- The universal property of Kähler differentials upgrades equality after composing with `D`
      -- to equality of the linear maps themselves.
      exact Derivation.liftKaehlerDifferential_unique _ _ hcompDer
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hx :
          (ψ.comp κ) x = x := by
        simpa using congrArg (fun f : C ⊗[A] M →ₗ[C] C ⊗[A] M => f x) hψκ
      have hy :
          (ψ.comp κ) y = y := by
        simpa using congrArg (fun f : C ⊗[A] M →ₗ[C] C ⊗[A] M => f y) hψκ
      calc
        x = (ψ.comp κ) x := hx.symm
        _ = (ψ.comp κ) y := by simpa using congrArg ψ hxy
        _ = y := hy
    · intro y
      refine ⟨ψ y, ?_⟩
      have hy := congrArg (fun f : Ω[C⁄A] →ₗ[C] Ω[C⁄A] => f y) hκψ
      simpa using hy

/-- Lemma 15.9.12: if `q : A^{⊕ m} → M` is surjective and `C = Sym_A(M)`, then the polynomial
presentation of `C` induced by `q` has naive cotangent differential
`C ⊗_A ker(q) → C ⊗_A A^{⊕ m}`, and after the canonical identification
`C ⊗_A A^{⊕ m} ≃ \bigoplus_j C \, dy_j` the resulting sequence
`C ⊗_A ker(q) → \bigoplus_j C \, dy_j → Ω_{C/A} → 0`
is exact. This is the textbook complex `NL(α) = (K ⊗_A C → \bigoplus_j C \, dy_j)` written in the
equivalent library-facing tensor order `C ⊗_A K`. -/
@[stacks 07EV]
theorem symmetricAlgebra_presentation_conormal_sequence
    (hq : Function.Surjective q) :
    let i : q.ker →ₗ[A] (Fin m →₀ A) := q.ker.subtype
    let toKaehler :
        C ⊗[A] (Fin m →₀ A) →ₗ[C] Ω[C⁄A] :=
      (KaehlerDifferential.D A C).tensorProductTo ∘ₗ
        (SymmetricAlgebra.ι A M).baseChange C ∘ₗ
        q.baseChange C
    Function.Exact (i.baseChange C) toKaehler ∧
      Function.Surjective toKaehler :=
  by
    dsimp
    let kappa : C ⊗[A] M →ₗ[C] Ω[C⁄A] :=
      ((KaehlerDifferential.D A C).tensorProductTo).comp ((SymmetricAlgebra.ι A M).baseChange C)
    have hbase :
        Function.Exact ((q.ker.subtype).baseChange C) (q.baseChange C) ∧
          Function.Surjective (q.baseChange C) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using
        baseChange_exact_surjective_of_kernel_presentation (q := q) hq
    have hkappa : Function.Bijective kappa := by
      simpa [kappa] using symmetricAlgebra_tensorToKaehler_bijective (A := A) (M := M)
    -- The source-facing map is exactly the canonical `kappa` after the tensorized presentation map.
    change Function.Exact ((q.ker.subtype).baseChange C) (kappa.comp (q.baseChange C)) ∧
      Function.Surjective (kappa.comp (q.baseChange C))
    constructor
    · -- Exactness transfers across postcomposition by the injective comparison map `kappa`.
      exact (hkappa.injective.comp_exact_iff_exact).2 hbase.1
    · -- Surjectivity of the tensorized presentation map and of `kappa` compose.
      intro y
      obtain ⟨x, rfl⟩ := hkappa.surjective y
      obtain ⟨z, rfl⟩ := hbase.2 x
      exact ⟨z, rfl⟩

end
