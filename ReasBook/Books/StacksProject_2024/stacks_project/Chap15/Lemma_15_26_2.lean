import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_6_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_7_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_70_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_70_12
import StacksProject_2024.stacks_project.Chap15.Definition_15_26_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w x

open scoped AffineBlowupChart

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
variable {S : Type w} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type x} [AddCommGroup M] [Module S M] [Module.Finite S M]

noncomputable local instance instModuleAffineBlowupApproximationStage
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    Module R[I / a.1]
      (affineBlowupStrictTransform
        (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M) :=
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a.1
  Module.compHom _ <| algebraMap (R[I / a.1]) (S[J / b])

/-
Domain-style sampling pass for Lemma 15.26.2.

Primary domain: affine blowup strict transforms in commutative algebra over a local domain.

Sampled owner declarations:
* `R[I / a]` from `Chap10/Definition_10_70_1.lean`;
* `IsAffineBlowupApproximation` from `Chap10/Lemma_10_70_12.lean`;
* `mappedIdealElement` from `Chap10/Lemma_10_70_3.lean`;
* `affineBlowupStrictTransform` from `Chap15/Definition_15_26_1.lean`.

Owner abstraction: the source-facing strict transform algebra of `S` on `R[I/a]` is the affine
blowup chart `S[Ideal.map (algebraMap R S) I / mappedIdealElement I a.1]`, and the source-facing
strict transform of `M` is the Chapter 15 owner
`affineBlowupStrictTransform (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M`.
Primitive data are the ideal `I`, the chosen nonzero `a ∈ I`, and the induced ideal map
`Ideal.map (algebraMap R S) I`; flatness and finite-presentation conditions are derived API.

Source/core/bridge triage:
* `source-facing`: the existence theorem returning a blowup chart approximation together with the
  flatness and finite-presentation properties of its strict transform algebra and module;
* `core/canonical`: `IsAffineBlowupApproximation`, the strict transform algebra owner
  `S[Ideal.map (algebraMap R S) I / mappedIdealElement I a.1]`, and the strict transform module
  owner
  `affineBlowupStrictTransform (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M`;
* `bridge/view`: `mappedIdealElement` and `tensorToAffineBlowupAlgebra` from
  `Lemma_10_70_3.lean`.
-/

-- Proof sketch: approximate the dominating valuation ring `A` by affine blowup charts as in
-- Lemma `10.70.12`, reduce to the polynomial-algebra case by presenting `S` as a quotient of a
-- polynomial ring, and then use the valuation-ring flatness and finite-presentation results from
-- Lemmas `15.22.10`, `15.25.6`, and the limit-flatness descent statement `10.168.1 (3)` to find a
-- stage where both strict transforms have the required properties.
/-- Helper for Lemma 15.26.2: finite presentation of the strict transform over the base chart
upgrades to finite presentation over the strict-transform algebra. -/
lemma affineBlowupStrictTransform_finitePresentation_of_base
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 })
    (hBft :
      let J : Ideal S := Ideal.map (algebraMap R S) I
      let b : J := mappedIdealElement I a.1
      Algebra.FiniteType R[I / a.1] S[J / b])
    [Module.FinitePresentation R[I / a.1]
      (affineBlowupStrictTransform
        (Ideal.map (algebraMap R S) I) (mappedIdealElement I a.1) M)] :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a.1
    Module.FinitePresentation S[J / b] (affineBlowupStrictTransform J b M) := by
  let R' := R[I / a.1]
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a.1
  let B := S[J / b]
  letI : Algebra.FiniteType R' B := by
    simpa [R', J, b, B] using hBft
  letI : Module R' (affineBlowupStrictTransform J b M) :=
    instModuleAffineBlowupApproximationStage (R := R) (S := S) (M := M) I a
  letI : IsScalarTower R' B (affineBlowupStrictTransform J b M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  -- Once the base-chart module is finitely presented, the finite-type chart map upgrades it to
  -- finite presentation over the strict-transform algebra.
  simpa [R', J, b, B] using
    (Module.FinitePresentation.of_restrictScalars_finiteType R' :
      Module.FinitePresentation B
        (affineBlowupStrictTransform J b M))

/-- Helper for Lemma 15.26.2: the Chapter 10 tensor-to-chart comparison map is surjective. -/
lemma tensorToAffineBlowupAlgebra_surjective
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    let J : Ideal S := Ideal.map (algebraMap R S) I
    let b : J := mappedIdealElement I a.1
    Function.Surjective (tensorToAffineBlowupAlgebra S I a.1) := by
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a.1
  -- The surjectivity statement is exactly the first half of the Chapter 10 chart comparison.
  simpa [J, b] using
    (affineBlowupChart_baseChange_surjective_and_ker_eq_primaryComponent
      (S := S) I a.1).1

/-- Helper for Lemma 15.26.2: quotienting the tensor-product chart model by the distinguished
primary component recovers the affine blowup chart algebra. -/
theorem tensor_quotient_primaryComponent_algEquiv_affineBlowupChart
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    let A := S ⊗[R] R[I / a.1];
    let J : Ideal S := Ideal.map (algebraMap R S) I;
    let b : J := mappedIdealElement I a.1;
    let aS : A := algebraMap R A a.1;
    (A ⧸ (Ideal.span ({aS} : Set A)).primaryComponent A) ≃ₐ[S] S[J / b] := by
  let A := S ⊗[R] R[I / a.1]
  let J : Ideal S := Ideal.map (algebraMap R S) I
  let b : J := mappedIdealElement I a.1
  let φ : A →ₐ[S] S[J / b] := tensorToAffineBlowupAlgebra S I a.1
  let aS : A := algebraMap R A a.1
  have hφ :
      Function.Surjective φ ∧
        RingHom.ker φ.toRingHom = (Ideal.span ({aS} : Set A)).primaryComponent A := by
    -- This is exactly the Chapter 10 kernel description, now packaged as the quotient algebra
    -- equivalence used by the source proof's strict-transform comparison.
    simpa [A, J, b, φ, aS] using
      (affineBlowupChart_baseChange_surjective_and_ker_eq_primaryComponent
        (S := S) I a.1)
  -- Rewrite the quotient by the primary component as the quotient by `ker φ`, then apply the
  -- canonical quotient-to-target algebra equivalence attached to a surjective map.
  exact
    (Ideal.quotientEquivAlgOfEq S hφ.2.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hφ.1)

/-- Helper for Lemma 15.26.2: once the polynomial-chart algebra factor is finitely presented as a
module over the polynomial chart, it is finitely presented as an algebra over the base chart. -/
lemma algebraFinitePresentation_of_mvPolynomial_moduleFinitePresentation
    {R' : Type*} [CommRing R'] {n : ℕ}
    {B : Type*} [CommRing B] [Algebra R' B]
    [Algebra (MvPolynomial (Fin n) R') B]
    [IsScalarTower R' (MvPolynomial (Fin n) R') B]
    [Module.FinitePresentation (MvPolynomial (Fin n) R') B] :
    Algebra.FinitePresentation R' B := by
  let P := MvPolynomial (Fin n) R'
  letI : Algebra.FinitePresentation P B := by
    -- Algebra Lemma 10.7.4 upgrades module finite presentation over the polynomial chart to an
    -- algebra finite-presentation statement over that same chart.
    exact Algebra.FinitePresentation.of_finitePresentation P B
  letI : Algebra.FinitePresentation R' P := by
    -- The polynomial chart itself is finitely presented over the base chart.
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
        (R := R') (A := R') (Fin n))
  -- Compose the polynomial-chart presentation with the chart-to-factor presentation.
  exact Algebra.FinitePresentation.trans R' P B

/-- Helper for Lemma 15.26.2: choose a surjective polynomial presentation of the finite type
algebra `S`. -/
lemma exists_surjective_mvPolynomial_presentation :
    ∃ (n : ℕ) (π : MvPolynomial (Fin n) R →ₐ[R] S),
      Function.Surjective π := by
  obtain ⟨n, π, hπ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1
      (inferInstance : Algebra.FiniteType R S)
  -- The first source-proof reduction is exactly a surjective polynomial presentation of `S`.
  exact ⟨n, π, hπ⟩

/-- Helper for Lemma 15.26.2: for a principal ideal, the primary component is exactly the
submodule of elements annihilated by a power of the generator. -/
lemma primaryComponent_principalIdeal_eq_torsion'
    {A : Type*} [CommRing A]
    {M' : Type*} [AddCommGroup M'] [Module A M']
    (f : A) :
    (principalIdeal f).primaryComponent M' =
      Submodule.torsion' (M := M') (Submonoid.powers f) := by
  -- Proof comment: unfold the primary component through `Ideal.primaryComponent_mem`, then rewrite
  -- finite powers of the principal ideal as powers of the single generator `f`.
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x]
    have hx₀ :
        ∃ n, x ∈ Submodule.torsionBySet A M' ↑(principalIdeal f ^ n) := by
      simpa using (Ideal.primaryComponent_mem M' (principalIdeal f) x).1 hx
    rcases hx₀ with ⟨n, hx'⟩
    have hx'' : x ∈ Submodule.torsionBy A M' (f ^ n) := by
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx'
    rw [Submodule.mem_torsionBy_iff] at hx''
    exact ⟨⟨f ^ n, ⟨n, rfl⟩⟩, hx''⟩
  · rintro ⟨⟨a, ha⟩, hx⟩
    rcases (Submonoid.mem_powers_iff a f).mp ha with ⟨n, hn⟩
    have hx' : x ∈ Submodule.torsionBy A M' (f ^ n) := by
      rw [Submodule.mem_torsionBy_iff]
      exact hn.symm ▸ hx
    refine (Ideal.primaryComponent_mem M' (principalIdeal f) x).2 ?_
    refine ⟨n, ?_⟩
    simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx'

/-- Helper for Lemma 15.26.2: `f`-power torsion in a product is exactly the product of the
factorwise `f`-power torsion submodules. -/
lemma torsion'_powers_prod_eq
    {A : Type*} [CommRing A]
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module A M₂]
    (f : A) :
    Submodule.torsion' (M := M₁ × M₂) (Submonoid.powers f) =
      Submodule.prod
        (Submodule.torsion' (M := M₁) (Submonoid.powers f))
        (Submodule.torsion' (M := M₂) (Submonoid.powers f)) := by
  -- Proof comment: a single power killing a pair kills both coordinates, and conversely the
  -- product of two annihilating powers kills the whole pair.
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x] at hx
    rcases hx with ⟨a, ha⟩
    rcases a.2 with ⟨n, rfl⟩
    constructor
    · rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x.1]
      refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
      exact congrArg Prod.fst ha
    · rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x.2]
      refine ⟨⟨f ^ n, ⟨n, rfl⟩⟩, ?_⟩
      exact congrArg Prod.snd ha
  · rintro ⟨hx, hy⟩
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x.1] at hx
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x.2] at hy
    rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x]
    rcases hx with ⟨ax, hax⟩
    rcases hy with ⟨ay, hay⟩
    rcases ax.2 with ⟨m, rfl⟩
    rcases ay.2 with ⟨n, rfl⟩
    refine ⟨⟨f ^ (m + n), ⟨m + n, rfl⟩⟩, ?_⟩
    apply Prod.ext
    · -- Multiply the `M₁`-relation by the extra power coming from the second coordinate.
      calc
        (f ^ (m + n) : A) • x.1 = (f ^ n : A) • ((f ^ m : A) • x.1) := by
          rw [pow_add, mul_smul]
        _ = 0 := by simp [hax]
    · -- Multiply the `M₂`-relation by the extra power coming from the first coordinate.
      calc
        (f ^ (m + n) : A) • x.2 = (f ^ m : A) • ((f ^ n : A) • x.2) := by
          rw [pow_add, mul_smul, mul_comm]
        _ = 0 := by simp [hay]

/-- Helper for Lemma 15.26.2: `TensorProduct.prodRight` preserves `a`-power torsion and turns it
into the product of the factorwise torsion submodules. -/
lemma tensorProduct_prodRight_mem_torsion'_iff
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    let R' := R[I / a.1];
    let aR' : R' := algebraMap R R' a.1;
    let e := TensorProduct.prodRight R R' R' S M;
    ∀ x : R' ⊗[R] (S × M),
      x ∈ Submodule.torsion' (M := R' ⊗[R] (S × M)) (Submonoid.powers aR') ↔
        e x ∈
          Submodule.prod
            (Submodule.torsion' (M := R' ⊗[R] S) (Submonoid.powers aR'))
            (Submodule.torsion' (M := R' ⊗[R] M) (Submonoid.powers aR')) := by
  let R' := R[I / a.1]
  let aR' : R' := algebraMap R R' a.1
  let e := TensorProduct.prodRight R R' R' S M
  intro x
  constructor
  · intro hx
    have hx' :
        e x ∈
          Submodule.torsion'
            (M := (R' ⊗[R] S) × (R' ⊗[R] M))
            (Submonoid.powers aR') := by
      -- Transport the annihilating power through the tensor/product linear equivalence.
      rw [Submodule.mem_torsion'_iff (Submonoid.powers aR') x] at hx
      rw [Submodule.mem_torsion'_iff (Submonoid.powers aR') (e x)]
      rcases hx with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simpa using congrArg e hc
    -- Rewrite torsion in the product as the product of the factorwise torsion submodules.
    simpa [torsion'_powers_prod_eq (A := R') (M₁ := R' ⊗[R] S) (M₂ := R' ⊗[R] M) aR'] using hx'
  · intro hx
    have hx' :
        e x ∈
          Submodule.torsion'
            (M := (R' ⊗[R] S) × (R' ⊗[R] M))
            (Submonoid.powers aR') := by
      -- Read the product membership back as a single torsion statement in the product module.
      simpa [torsion'_powers_prod_eq (A := R') (M₁ := R' ⊗[R] S) (M₂ := R' ⊗[R] M) aR'] using hx
    rw [Submodule.mem_torsion'_iff (Submonoid.powers aR') (e x)] at hx'
    rw [Submodule.mem_torsion'_iff (Submonoid.powers aR') x]
    rcases hx' with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    -- Injectivity of `TensorProduct.prodRight` pulls the annihilating equation back to `x`.
    apply e.injective
    simpa using hc

/-- Helper for Lemma 15.26.2: under `TensorProduct.prodRight`, the distinguished primary
component for the tensor product with `S × M` becomes the product of the two factor primary
components. -/
lemma strictTransform_primaryComponent_prod_eq
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    let R' := R[I / a.1];
    let aR' : R' := algebraMap R R' a.1;
    let e := TensorProduct.prodRight R R' R' S M;
    ((principalIdeal aR').primaryComponent (R' ⊗[R] (S × M))).map e.toLinearMap =
      Submodule.prod
        ((principalIdeal aR').primaryComponent (R' ⊗[R] S))
        ((principalIdeal aR').primaryComponent (R' ⊗[R] M)) :=
by
  let R' := R[I / a.1]
  let aR' : R' := algebraMap R R' a.1
  let e := TensorProduct.prodRight R R' R' S M
  -- Rewrite both primary components as powers-torsion submodules before comparing them.
  rw [primaryComponent_principalIdeal_eq_torsion' (M' := R' ⊗[R] (S × M)) aR']
  rw [primaryComponent_principalIdeal_eq_torsion' (M' := R' ⊗[R] S) aR']
  rw [primaryComponent_principalIdeal_eq_torsion' (M' := R' ⊗[R] M) aR']
  ext y
  constructor
  · intro hy
    rcases Submodule.mem_map.1 hy with ⟨x, hx, rfl⟩
    -- The new elementwise transport lemma is exactly the missing bridge from the source module
    -- to the product decomposition.
    simpa [R', aR', e] using
      (tensorProduct_prodRight_mem_torsion'_iff (R := R) (S := S) (M := M) I a x).1 hx
  · intro hy
    refine Submodule.mem_map.2 ?_
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    -- Apply the same transport lemma in the reverse direction to lift product torsion back.
    have hy' :
        e (e.symm y) ∈
          Submodule.prod
            (Submodule.torsion' (M := R' ⊗[R] S) (Submonoid.powers aR'))
            (Submodule.torsion' (M := R' ⊗[R] M) (Submonoid.powers aR')) := by
      simpa using hy
    simpa [R', aR', e] using
      (tensorProduct_prodRight_mem_torsion'_iff (R := R) (S := S) (M := M) I a (e.symm y)).2 hy'

/-- Helper for Lemma 15.26.2: quotienting a product by the product of two submodules is the same
as taking the product of the two quotient modules. -/
lemma quotient_prod_submodule_equiv
    {A : Type*} [CommRing A]
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module A M₂]
    (P : Submodule A M₁) (Q : Submodule A M₂) :
    ((M₁ × M₂) ⧸ Submodule.prod P Q) ≃ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := by
  let φ : M₁ × M₂ →ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := LinearMap.prod P.mkQ Q.mkQ
  have hker : LinearMap.ker φ = Submodule.prod P Q := by
    -- Proof comment: the product quotient map vanishes exactly when both coordinates lie in the
    -- chosen submodules.
    simpa [φ] using (LinearMap.ker_prodMap (f := P.mkQ) (g := Q.mkQ))
  have hsurj : Function.Surjective φ := by
    intro y
    rcases Submodule.mkQ_surjective P y.1 with ⟨x₁, rfl⟩
    rcases Submodule.mkQ_surjective Q y.2 with ⟨x₂, rfl⟩
    exact ⟨(x₁, x₂), rfl⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hsurj
  -- Rewrite to the actual kernel of the product quotient map and then collapse the full range.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivRange.trans
        ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.26.2: after transporting through `TensorProduct.prodRight`, the quotient
of the tensor-product model by the distinguished primary component splits as the product of the
two factorwise quotients. -/
lemma tensor_quotient_primaryComponent_prod_split
    (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }) :
    let R' := R[I / a.1];
    let aR' : R' := algebraMap R R' a.1;
    let T := R' ⊗[R] (S × M);
    let T₁ := R' ⊗[R] S;
    let T₂ := R' ⊗[R] M;
    (T ⧸ (principalIdeal aR').primaryComponent T) ≃ₗ[R']
      ((T₁ ⧸ (principalIdeal aR').primaryComponent T₁) ×
        (T₂ ⧸ (principalIdeal aR').primaryComponent T₂)) := by
  let R' := R[I / a.1]
  let aR' : R' := algebraMap R R' a.1
  let T := R' ⊗[R] (S × M)
  let T₁ := R' ⊗[R] S
  let T₂ := R' ⊗[R] M
  let e : T ≃ₗ[R'] (T₁ × T₂) := TensorProduct.prodRight R R' R' S M
  let P : Submodule R' T := (principalIdeal aR').primaryComponent T
  let Q : Submodule R' (T₁ × T₂) :=
    Submodule.prod
      ((principalIdeal aR').primaryComponent T₁)
      ((principalIdeal aR').primaryComponent T₂)
  have hPQ : P.map e.toLinearMap = Q := by
    -- Proof comment: this is the primary-component transport established just above.
    simpa [R', aR', e, P, Q] using
      strictTransform_primaryComponent_prod_eq (R := R) (S := S) (M := M) I a
  -- First identify the source quotient with the quotient of the transported product submodule,
  -- then split that quotient factorwise.
  exact
    (Submodule.Quotient.equiv P Q e hPQ).trans
      (quotient_prod_submodule_equiv
        ((principalIdeal aR').primaryComponent T₁)
        ((principalIdeal aR').primaryComponent T₂))

/-- Lemma 15.26.2: for every valuation ring `A ⊆ K` dominating the local domain `R`, there exists
an affine blowup chart `R' = R[I/a]` with nonzero `a ∈ I ⊆ maximalIdeal R` and nonzero special
fibre such that, writing `J = Ideal.map (algebraMap R S) I`, `b` for the image of `a` in `J`, and
`B = S[J/b]`, the strict transform algebra `B` is flat and finitely presented over `R'`, while
the strict transform module `affineBlowupStrictTransform J b M` is flat over `R'` and finitely
presented over `B`. -/
theorem exists_affineBlowup_with_flat_finitelyPresented_strictTransforms
    (A : ValuationSubring K)
    (hA : LocalSubring.range (algebraMap R K) ≤ A.toLocalSubring) :
    ∃ (I : Ideal R) (a : { a : I // (a : R) ≠ 0 }),
      let R' := R[I / a.1]
      let J : Ideal S := Ideal.map (algebraMap R S) I
      let b : J := mappedIdealElement I a.1
      let B := S[J / b]
      let T := affineBlowupStrictTransform J b M
      IsAffineBlowupApproximation A I a ∧
        Module.Flat R' B ∧
        Algebra.FinitePresentation R' B ∧
        Module.Flat R' T ∧
        Module.FinitePresentation B T := by
  -- Route correction: the source proof first reduces to a polynomial presentation, then descends
  -- flat finitely presented data from the dominating valuation ring to one affine blowup stage.
  -- The helper lemmas above isolate the two terminal assembly steps from the source route: first
  -- upgrade the strict-transform module from base-chart finite presentation to algebra-side finite
  -- presentation, then compose the polynomial-chart module presentation into an algebra finite-
  -- presentation statement for the algebra factor itself.
  obtain ⟨n, π, hπ⟩ :=
    exists_surjective_mvPolynomial_presentation (R := R) (S := S)
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := π.toAlgebra
  letI : Module P M := Module.compHom (M := M) π.toRingHom
  letI : IsScalarTower P S M := IsScalarTower.of_algebraMap_smul fun p m ↦ by
    change π p • m = π p • m
    rfl
  letI : Module.Finite P S :=
    Module.Finite.of_surjective (Algebra.linearMap P S) hπ
  letI : Module.Finite P M := Module.Finite.trans S M
  letI : Module.Finite P (S × M) := by infer_instance
  -- The quotient-presentation step of the source proof is now explicit: everything is reduced to
  -- the polynomial algebra `P` and the finite `P`-module `S × M`.
  -- TODO: prove the polynomial-case existence theorem for the strict transform of the finite
  -- `P`-module `S × M`. The quotient-to-chart algebra bridge is now isolated in
  -- `tensor_quotient_primaryComponent_algEquiv_affineBlowupChart`, and the submodule-level product
  -- transport is now further upgraded to the quotient-level split
  -- `tensor_quotient_primaryComponent_prod_split`; the remaining blocker is the source-faithful
  -- valuation-descent stage together with the final comparison that identifies the second factor
  -- of that tensor-model split with the actual strict transform module over `S[Ideal.map ... I / b]`.
  sorry

end
