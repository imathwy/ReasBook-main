import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

open HomogeneousLocalization
open Polynomial
open scoped AffineBlowupChart DirectSum TensorProduct

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling pass for Lemma 10.70.3.

Primary domain: commutative algebra of affine blowup charts under flat base change.

Sampled owner declarations:
* `affineBlowupChart` from `Definition_10_70_1.lean`;
* `affineBlowupChartScaledMap_surjective_and_ker_eq_f_power_torsion` from
  `Lemma_10_70_8.lean`;
* `Ideal.primaryComponent_mem` and `Submodule.mem_torsionBySet_iff` from mathlib's torsion API.

Owner abstraction: the affine blowup chart `R[I/a]`, with the canonical base-change map
`tensorToAffineBlowupAlgebra : S ⊗[R] R[I/a] → S[IS/b]`.
Primitive data here are the induced ideal `Ideal.map (algebraMap R S) I`, the distinguished image
`mappedIdealElement I a`, and the comparison map on blowup charts. The primary-component equality
is derived API; the source-facing statement is the torsion description of the kernel.

Source/core/bridge triage:
* source-facing: the surjective base-change map with kernel given by powers of the distinguished
  tensor image of `a`;
* core/canonical: the same kernel as a primary component;
* bridge/view: `tensorToAffineBlowupAlgebra`.
-/

/-- The image of `a ∈ I` in the extended ideal `Ideal.map (algebraMap R S) I`. -/
def mappedIdealElement {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) : Ideal.map (algebraMap R S) I :=
  ⟨algebraMap R S a.1, Ideal.mem_map_of_mem (algebraMap R S) a.2⟩

private noncomputable instance affineBlowupAlgebraBaseChangeAlgebra {S : Type v} [CommRing S]
    [Algebra R S] (J : Ideal S) (b : J) :
    Algebra R S[J / b] :=
  RingHom.toAlgebra <| (algebraMap S S[J / b]).comp (algebraMap R S)

private theorem map_ideal_le_comap {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R) :
    I ≤ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) := by
  intro x hx
  exact Ideal.mem_map_of_mem (algebraMap R S) hx

private theorem reesAlgebraMap_mem_grade {S : Type v} [CommRing S] [Algebra R S] (I : Ideal R)
    {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ reesAlgebraGrade I n) :
    reesAlgebraMap (algebraMap R S) (map_ideal_le_comap I) x ∈
      reesAlgebraGrade (Ideal.map (algebraMap R S) I) n := sorry

private noncomputable def reesAlgebraBaseChangeGradedHom {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) :
    reesAlgebraGrade I →+*ᵍ reesAlgebraGrade (Ideal.map (algebraMap R S) I) where
  toRingHom := reesAlgebraMap (algebraMap R S) (map_ideal_le_comap I)
  map_mem := reesAlgebraMap_mem_grade I

private theorem reesAlgebraBaseChange_degreeOne {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    reesAlgebraBaseChangeGradedHom I (reesAlgebraDegreeOne I a) =
      reesAlgebraDegreeOne (Ideal.map (algebraMap R S) I) (mappedIdealElement I a) := sorry

/- The direct chart map is the canonical bridge from the source-facing blowup chart `R[I/a]` to
the base-changed chart `S[IS/b]`; the tensor-product comparison map below is derived from it. -/
/-- The canonical affine-blowup-chart map induced by a base change `R → S`. -/
noncomputable def affineBlowupChartBaseChangeMap {S : Type v} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    R[I / a] →ₐ[R] S[J / b] := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  letI : Algebra R S[J / b] :=
    affineBlowupAlgebraBaseChangeAlgebra J b
  letI :
      CommRing (Away (reesAlgebraGrade J) ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a))) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  let φring : R[I / a] →+* S[J / b] := by
    have hdeg :
        (reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a) =
          reesAlgebraDegreeOne J b := by
      simpa [J, b] using reesAlgebraBaseChange_degreeOne I a
    let ψ :
        R[I / a] →+*
          Away (reesAlgebraGrade J) ((reesAlgebraBaseChangeGradedHom I) (reesAlgebraDegreeOne I a)) :=
      HomogeneousLocalization.map (reesAlgebraBaseChangeGradedHom I) <| by
        intro x hx
        rcases hx with ⟨n, rfl⟩
        exact ⟨n, by simp [hdeg]⟩
    exact Eq.mp
      (by
        simpa [affineBlowupChart] using
          congrArg
            (fun x ↦ R[I / a] →+* Away (reesAlgebraGrade J) x)
            hdeg)
      ψ
  exact
    { toRingHom := φring
      commutes' := by
        intro r
        sorry }

noncomputable instance instAlgebraAffineBlowupChartBaseChange {S : Type v} [CommRing S]
    [Algebra R S]
    (I : Ideal R) (a : I) :
    Algebra R[I / a] (affineBlowupChart (Ideal.map (algebraMap R S) I) (mappedIdealElement I a)) :=
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  RingHom.toAlgebra (show R[I / a] →+* S[J / b] from (affineBlowupChartBaseChangeMap I a).toRingHom)

/-- The canonical base-change map
`S ⊗[R] R[I/a] → S[J/b]`, where `J = Ideal.map (algebraMap R S) I` and `b ∈ J` is the image of
`a`. -/
noncomputable def tensorToAffineBlowupAlgebra
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a
    S ⊗[R] R[I / a] →ₐ[S] S[J / b] :=
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a
  letI : Algebra S S := Algebra.id S
  letI : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S S[J / b] := inferInstance
  letI : SMul S S[J / b] := (inferInstance : Algebra S S[J / b]).toSMul
  letI : Algebra R S[J / b] := affineBlowupAlgebraBaseChangeAlgebra J b
  letI : IsScalarTower R S S[J / b] :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change ((algebraMap S S[J / b]).comp (algebraMap R S)) x =
        (algebraMap S S[J / b]) ((algebraMap R S) x)
      rfl
  let f : S →ₐ[S] S[J / b] := Algebra.ofId S S[J / b]
  let g : R[I / a] →ₐ[R] S[J / b] := affineBlowupChartBaseChangeMap I a
  (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) :
    S ⊗[R] R[I / a] →ₐ[S] S[J / b])

-- Proof sketch: the canonical map `S ⊗[R] R[I/a] → S[IS/b]` sends `s ⊗ x / a^n` to the
-- corresponding fraction in `S[IS/b]`, which gives surjectivity by writing elements of `J^n` as
-- sums of tensors from `I^n`. Its kernel is exactly the `b`-power torsion, because localizing away
-- from `b` kills precisely the elements annihilated by some power of `b`.
/-- Membership in the kernel of the base-change map is exactly torsion by a power of the
distinguished tensor image of `a`. -/
theorem mem_ker_tensorToAffineBlowupAlgebra_iff_exists_pow_mul_eq_zero
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I)
    (x : S ⊗[R] R[I / a]) :
    x ∈ RingHom.ker (tensorToAffineBlowupAlgebra S I a).toRingHom ↔
      ∃ n : ℕ, (algebraMap R (S ⊗[R] R[I / a]) a.1) ^ n * x = 0 := sorry

/-- Lemma 10.70.3 (Stacks tag `0BIP`): the canonical base-change map
`S ⊗[R] R[I/a] → S[IS/b]` is surjective, and its kernel consists exactly of the elements
annihilated by some power of the image of `a` in the tensor product. -/
theorem affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let A := S ⊗[R] R[I / a]
    let φ := tensorToAffineBlowupAlgebra S I a
    let aS : A := algebraMap R A a.1
    Function.Surjective φ ∧
      ∀ x : A, x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, aS ^ n * x = 0 := by
  let A := S ⊗[R] R[I / a]
  let φ := tensorToAffineBlowupAlgebra S I a
  let aS : A := algebraMap R A a.1
  change Function.Surjective φ ∧
    ∀ x : A, x ∈ RingHom.ker φ.toRingHom ↔ ∃ n : ℕ, aS ^ n * x = 0
  refine ⟨?_, ?_⟩
  · sorry
  · intro x
    exact mem_ker_tensorToAffineBlowupAlgebra_iff_exists_pow_mul_eq_zero S I a x

/-- Canonical reformulation of Lemma 10.70.3: the kernel of the base-change map is the primary
component of the principal ideal generated by the distinguished tensor image of `a`. -/
theorem affineBlowupChart_baseChange_surjective_and_ker_eq_primaryComponent
    (S : Type v) [CommRing S] [Algebra R S] (I : Ideal R) (a : I) :
    let A := S ⊗[R] R[I / a]
    let φ := tensorToAffineBlowupAlgebra S I a
    let aS : A := algebraMap R A a.1
    Function.Surjective φ ∧
      RingHom.ker φ.toRingHom = (Ideal.span ({aS} : Set A)).primaryComponent A := by
  let A := S ⊗[R] R[I / a]
  let φ := tensorToAffineBlowupAlgebra S I a
  let aT : A := (algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a])
  have hbase := affineBlowupChart_baseChange_surjective_and_ker_eq_a_power_torsion S I a
  have h :
      Function.Surjective φ ∧
        RingHom.ker φ.toRingHom = (Ideal.span ({aT} : Set A)).primaryComponent A := by
    have haTpow (n : ℕ) : aT ^ n = ((algebraMap R S a.1) ^ n) ⊗ₜ[R] (1 : R[I / a]) := by
      induction n with
      | zero =>
          rw [pow_zero, Algebra.TensorProduct.one_def]
          simp
      | succ n ih =>
          rw [pow_succ, ih, show aT = (algebraMap R S a.1) ⊗ₜ[R] (1 : R[I / a]) by rfl,
            Algebra.TensorProduct.tmul_mul_tmul]
          simp [pow_succ]
    refine ⟨hbase.1, ?_⟩
    ext x
    rw [Ideal.primaryComponent_mem]
    constructor
    · intro hx
      rcases (hbase.2 x).mp hx with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hx' : x ∈ Submodule.torsionBy A A (aT ^ n) := by
        simpa [Submodule.mem_torsionBy_iff, smul_eq_mul, haTpow n] using hn
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx'
    · rintro ⟨n, hx⟩
      have hx' : x ∈ Submodule.torsionBy A A (aT ^ n) := by
        simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx
      refine (hbase.2 x).mpr ⟨n, ?_⟩
      simpa [Submodule.mem_torsionBy_iff, smul_eq_mul, haTpow n] using hx'
  simpa [aT, Algebra.TensorProduct.algebraMap_apply] using h

end
