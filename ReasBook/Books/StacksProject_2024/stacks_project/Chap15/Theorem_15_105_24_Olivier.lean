import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_153_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_107_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_156_5
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_18_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_23

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open PrimeSpectrum
open scoped TensorProduct
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [StrictHenselianLocalRing A] [Algebra.IsWeaklyEtale A B]

/- Domain-style sampling for Theorem 15.105.24 (Olivier):
- primary domain: local commutative algebra of weakly étale maps over strictly henselian local
  rings;
- sampled owner declarations:
  `StrictHenselianLocalRing`,
  `Algebra.IsWeaklyEtale`,
  `Algebra.IsEpi`,
  `faithfullyFlat_epi_bijective`;
- best owner abstraction: this item is `source-facing`, but the canonical owner controlling the
  final bijectivity step is `Algebra.IsEpi A B`; faithful flatness is derived from the flatness
  field of `Algebra.IsWeaklyEtale` together with `IsLocalHom (algebraMap A B)`;
- primitive data: `StrictHenselianLocalRing A`, `IsLocalHom (algebraMap A B)`, and
  `Algebra.IsWeaklyEtale A B`;
- derived API: the public bridge to `Algebra.IsEpi A B`, then bijectivity of `algebraMap A B`
  via `faithfullyFlat_epi_bijective`.

Source/core/bridge triage:
- `source-facing`: `bijective_algebraMap_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale`;
- `core/canonical`: `Algebra.IsWeaklyEtale`, `Algebra.IsEpi`, and `RingHom.FaithfullyFlat`;
- `bridge/view`: the epimorphism bridge below.
-/

-- Proof sketch: weakly étale maps induce separable residue-field extensions on fibers, while the
-- strict henselian local hypotheses force the closed-fiber residue-field extension to be purely
-- inseparable. Thus the diagonal/base-change fiber is trivial, so the canonical owner
-- `Algebra.IsEpi A B` holds.
/-- Helper for Theorem 15.105.24 (Olivier): the tensor-square multiplication map
`B ⊗[A] B → B` is always surjective. -/
lemma tensorSquareMul_surjective :
    Function.Surjective (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B) := by
  -- Every `b : B` is the image of the pure tensor `1 ⊗ b`.
  intro b
  exact ⟨1 ⊗ₜ[A] b, by simp⟩

/-- Helper for Theorem 15.105.24 (Olivier): flatness of the tensor-square multiplication makes
its kernel a pure ideal. -/
lemma tensorSquareMul_kernel_pure_of_flat :
    let I : Ideal (B ⊗[A] B) :=
      RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom
    I.Pure := by
  let f : B ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.lmul' A
  let I : Ideal (B ⊗[A] B) := RingHom.ker f.toRingHom
  letI : Algebra (B ⊗[A] B) B := f.toRingHom.toAlgebra
  letI : Module.Flat (B ⊗[A] B) B :=
    ‹Algebra.IsWeaklyEtale A B›.flat_tensorSquareMultiplication
  let f' : B ⊗[A] B →ₐ[B ⊗[A] B] B :=
    { f with
      commutes' := by
        intro x
        rfl }
  have hsurj : Function.Surjective f' := by
    -- The same explicit preimage `1 ⊗ b` witnesses surjectivity over the larger scalar ring.
    intro b
    obtain ⟨x, hx⟩ := tensorSquareMul_surjective (A := A) (B := B) b
    exact ⟨x, hx⟩
  have e : (B ⊗[A] B ⧸ I) ≃ₐ[B ⊗[A] B] B := by
    -- The quotient by the kernel is canonically the target algebra because `f'` is surjective.
    simpa [I] using Ideal.quotientKerAlgEquivOfSurjective hsurj
  -- Transport flatness across the quotient equivalence to obtain purity of the kernel ideal.
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Theorem 15.105.24 (Olivier): once the diagonal map
`Spec(B) → Spec(B ⊗[A] B)` is bijective, flatness forces the kernel of `B ⊗[A] B → B` to
vanish, so the multiplication map is injective. -/
lemma tensorSquareMul_injective_of_flat_and_specComap_bijective
    (hbij :
      Function.Bijective
        (PrimeSpectrum.comap
          ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom))) :
    Function.Injective (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B) := by
  let f : B ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.lmul' A
  let I : Ideal (B ⊗[A] B) := RingHom.ker f.toRingHom
  have hI_pure : I.Pure := tensorSquareMul_kernel_pure_of_flat (A := A) (B := B)
  have hrange :
      Set.range (PrimeSpectrum.comap f.toRingHom) =
        PrimeSpectrum.zeroLocus (I : Set (B ⊗[A] B)) := by
    -- For a surjective ring map, the image on spectra is exactly the zero locus of the kernel.
    simpa [f, I, Ideal.mk_ker] using
      (range_comap_of_surjective
        (R := B ⊗[A] B) (S := B) f.toRingHom
        (tensorSquareMul_surjective (A := A) (B := B)))
  have hzero :
      PrimeSpectrum.zeroLocus (I : Set (B ⊗[A] B)) = Set.univ := by
    -- Bijectivity of `comap` upgrades the standard range description to `V(I) = Spec`.
    rw [← hrange, Set.range_eq_univ]
    exact hbij.2
  have hI_eq_bot :
      I = ⊥ := by
    letI : I.Pure := hI_pure
    have hbot_pure : (⊥ : Ideal (B ⊗[A] B)).Pure := by
      let e :
          (B ⊗[A] B) ≃ₐ[B ⊗[A] B] (B ⊗[A] B) ⧸ (⊥ : Ideal (B ⊗[A] B)) :=
        (AlgEquiv.quotientBot (B ⊗[A] B) (B ⊗[A] B)).symm
      -- Purity of `⊥` is just flatness of the identity quotient `R ⧸ ⊥ ≃ R`.
      exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    letI : (⊥ : Ideal (B ⊗[A] B)).Pure := hbot_pure
    have hzero_bot :
        PrimeSpectrum.zeroLocus ((⊥ : Ideal (B ⊗[A] B)) : Set (B ⊗[A] B)) = Set.univ := by
      ext q
      simp
    -- Lemma `10.108.3` makes the zero locus injective on pure ideals.
    exact
      (Ideal.zeroLocus_inj_of_pure (R := B ⊗[A] B) (I := I) (J := (⊥ : Ideal (B ⊗[A] B)))).mp <|
        hzero.trans hzero_bot.symm
  -- Trivial kernel is exactly injectivity of the diagonal multiplication map.
  exact (RingHom.injective_iff_ker_eq_bot f.toRingHom).2 hI_eq_bot

/-- Helper for Theorem 15.105.24 (Olivier): contraction along `includeRight` is a left inverse to
contraction along the tensor-square multiplication map. -/
lemma tensorSquareMul_specComap_includeRight_leftInverse :
    Function.LeftInverse
      (PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom))
      (PrimeSpectrum.comap
        ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom)) := by
  intro q
  -- Proof comment: `lmul' A` retracts the `includeRight` branch, so the induced spectrum map
  -- retracts as well.
  rw [← PrimeSpectrum.comap_comp_apply]
  change
    PrimeSpectrum.comap
      (((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)) q = q
  have hcomp :
      (((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)) =
        RingHom.id B := by
    ext b
    simp [Algebra.TensorProduct.includeRight_apply]
  rw [hcomp]
  rfl

/-- Helper for Theorem 15.105.24 (Olivier): the contraction of `q` to `A` is the ideal-theoretic
compatibility needed to compare residue fields along `A → B`. -/
lemma tensorSquare_closedFiber_compat
    (q : PrimeSpectrum B) :
    Ideal.comap (Algebra.ofId A B).toRingHom q.asIdeal =
      (PrimeSpectrum.comap (algebraMap A B) q).asIdeal := rfl

/-- Helper for Theorem 15.105.24 (Olivier): the residue field `κ(q)` carries its canonical
`κ(q ∩ A)`-algebra structure. -/
noncomputable instance tensorSquare_closedFiber_residueFieldAlgebra
    (q : PrimeSpectrum B) :
    Algebra (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField q.asIdeal.ResidueField :=
  (Ideal.ResidueField.mapₐ
    (PrimeSpectrum.comap (algebraMap A B) q).asIdeal q.asIdeal (Algebra.ofId A B)
    (tensorSquare_closedFiber_compat (A := A) (B := B) q)).toAlgebra

/-- Helper for Theorem 15.105.24 (Olivier): in a local ring integrally closed in an overring,
every idempotent of the overring already descends to the trivial idempotents `0` or `1`. -/
lemma idempotent_eq_zero_or_one_of_integrallyClosedIn_local
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [IsIntegrallyClosedIn R S] (e : S) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hRS : Function.Injective (algebraMap R S) :=
    (isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn R S›).1
  have he_integral : IsIntegral R e := by
    -- The idempotent equation makes `e` a root of the monic polynomial `X^2 - X`.
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · have hdeg : Polynomial.degree (Polynomial.X : Polynomial R) < 2 := by
        simpa using
          (show Polynomial.degree (Polynomial.X : Polynomial R) < (2 : WithBot ℕ) by simp)
      simpa using
        (Polynomial.monic_X_pow_sub (p := (Polynomial.X : Polynomial R)) (n := 2) hdeg)
    · simpa [IsIdempotentElem, pow_two] using (sub_eq_zero.mpr he)
  obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral he_integral
  have hr_idem : r * r = r := by
    -- Injectivity of the integrally closed map lets us descend the idempotent relation to `R`.
    apply hRS
    simpa [hr, IsIdempotentElem, pow_two] using he
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hr_unit | h1r_unit
  · -- A unit idempotent must be `1`.
    right
    have hr_one : r = 1 := by
      rcases hr_unit with ⟨u, hu⟩
      calc
        r = r * 1 := by simp
        _ = r * ((↑u : R) * ↑u⁻¹) := by simp
        _ = (r * ↑u) * ↑u⁻¹ := by ring
        _ = (r * r) * ↑u⁻¹ := by rw [hu]
        _ = r * ↑u⁻¹ := by rw [hr_idem]
        _ = 1 := by rw [← hu]; simp
    simpa [hr] using congrArg (algebraMap R S) hr_one
  · -- If `1 - r` is a unit, the zero-product `r * (1 - r) = 0` forces `r = 0`.
    left
    rcases h1r_unit with ⟨u, hu⟩
    have hr_mul : r * (1 - r) = 0 := by
      calc
        r * (1 - r) = r - r * r := by ring
        _ = r - r := by rw [hr_idem]
        _ = 0 := by simp
    have hr_zero : r = 0 := by
      calc
        r = r * 1 := by simp
        _ = r * ((↑u : R) * ↑u⁻¹) := by simp
        _ = (r * ↑u) * ↑u⁻¹ := by ring
        _ = 0 := by
          have hru : r * (↑u : R) = 0 := by simpa [hu] using hr_mul
          simp [hru]
    simpa [hr] using congrArg (algebraMap R S) hr_zero

/-- Helper for Theorem 15.105.24 (Olivier): an absolutely flat ring with only trivial
idempotents is a field. -/
lemma isField_of_idempotents_trivial_of_isAbsolutelyFlatRing
    {R : Type*} [CommRing R] [Nontrivial R] [IsAbsolutelyFlatRing R]
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField R := by
  let hlocal : IsLocalRing R := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    obtain ⟨b, hx⟩ := IsAbsolutelyFlatRing.exists_factor (A := R) x
    have he : IsIdempotentElem (x * b) := by
      -- The source-proof idempotent is the regular factor `x * b`.
      have hx' : x * (x * b) = x := by
        calc
          x * (x * b) = x ^ 2 * b := by ring
          _ = x := hx.symm
      calc
        (x * b) * (x * b) = (x * (x * b)) * b := by ring
        _ = x * b := by rw [hx']
    rcases hidem (x * b) he with hxb0 | hxb1
    · -- If `x * b = 0`, then the factorization collapses to `x = 0`, so `1 - x` is a unit.
      right
      have hx0 : x = 0 := by
        calc
          x = x ^ 2 * b := hx
          _ = x * (x * b) := by ring
          _ = 0 := by simp [hxb0]
      simpa [hx0]
    · -- If `x * b = 1`, then `x` is already invertible.
      left
      exact ⟨⟨x, b, hxb1, by simpa [mul_comm] using hxb1⟩, rfl⟩
  let _ : IsLocalRing R := hlocal
  -- The local absolutely-flat criterion from Definition `15.105.1` upgrades the factorization.
  exact isField_of_localRing_exists_factor (R := R) fun r ↦
    IsAbsolutelyFlatRing.exists_factor (A := R) r

/-- Helper for Theorem 15.105.24 (Olivier): scalar extension of the closed fiber along a residue
field extension is the same tensor product as base-changing `B` directly from `A` to the larger
field. -/
noncomputable def scalarExtension_closedFiber_algEquiv_ambientTensor
    (p : PrimeSpectrum A) (L : Type*) [Field L] [Algebra A L]
    [Algebra p.asIdeal.ResidueField L] [IsScalarTower A p.asIdeal.ResidueField L] :
    L ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B ≃ₐ[L] L ⊗[A] B :=
  Algebra.TensorProduct.cancelBaseChange A p.asIdeal.ResidueField L L B

/-- Helper for Theorem 15.105.24 (Olivier): the residue field `κ(q)` is algebraic over the
residue field `κ(q ∩ A)` for a weakly étale local map. -/
lemma closedFiber_residueField_isAlgebraic_of_localHom_of_isWeaklyEtale
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      tensorSquare_closedFiber_residueFieldAlgebra (A := A) (B := B) q
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.asIdeal.ResidueField := by
  -- TODO for Theorem 15.105.24 (Olivier): once `Lemma_15_105_17` compiles from source again,
  -- package `q` as an element of `p.asIdeal.primesOver B` and invoke the canonical residue-field
  -- algebraicity theorem there.
  sorry

/-- Helper for Theorem 15.105.24 (Olivier): the normalization of the prime quotient `A ⧸ p` in an
algebraic field extension is again a local ring. -/
lemma integralClosure_quotient_isLocal
    (p : PrimeSpectrum A) {L : Type*} [Field L] [Algebra (A ⧸ p.asIdeal) L] :
    IsLocalRing (integralClosure (A ⧸ p.asIdeal) L) := by
  let A0 := A ⧸ p.asIdeal
  let _ : IsDomain A0 := Ideal.Quotient.isDomain p.asIdeal
  let _ : StrictHenselianLocalRing A0 :=
    strictHenselianLocalRing_of_strictHenselianLocalRing_of_integral_domain (B := A0) A
  -- Proof comment: Lemma `15.105.23` upgrades the prime quotient to a strictly henselian local
  -- domain, and the integral closure of such a ring in a field is strictly henselian local again.
  infer_instance

/-- Helper for Theorem 15.105.24 (Olivier): after any algebraic scalar extension of the closed
fiber, every idempotent remains trivial. -/
lemma scalarExtension_closedFiber_idempotents_trivial_of_algebraic_extension
    (p : PrimeSpectrum A) {L : Type*} [Field L]
    [Algebra p.asIdeal.ResidueField L] [Algebra.IsAlgebraic p.asIdeal.ResidueField L]
    (e : L ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  -- TODO for Theorem 15.105.24 (Olivier): transport `e` to `L ⊗[A] B`, use the normalization
  -- `integralClosure (A ⧸ p) L` as the local model (the previous helper isolates its locality),
  -- then combine Lemma `10.156.5` with the still-missing integrally-closed tensor step and
  -- descend the ambient `0/1` conclusion back across
  -- `scalarExtension_closedFiber_algEquiv_ambientTensor`.
  sorry

/-- Helper for Theorem 15.105.24 (Olivier): the scalar extension of the closed fiber to `κ(q)` is
absolutely flat. -/
lemma scalarExtension_closedFiber_isAbsolutelyFlat_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      tensorSquare_closedFiber_residueFieldAlgebra (A := A) (B := B) q
    IsAbsolutelyFlatRing
      (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) := by
  -- TODO for Theorem 15.105.24 (Olivier): once `Lemma_15_105_8` compiles from source again,
  -- base change weak étaleness from `A → B` to the closed fiber `p.asIdeal.Fiber B`, then along
  -- `κ(p) → κ(q)`, and apply the canonical absolute-flatness theorem over the field `κ(q)`.
  sorry

/-- Helper for Theorem 15.105.24 (Olivier): Olivier's source argument shows that the scalar
extension of the closed fiber over each `q` is a field. -/
lemma scalarExtension_closedFiber_isField_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      tensorSquare_closedFiber_residueFieldAlgebra (A := A) (B := B) q
    IsField (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) := by
  -- TODO for Theorem 15.105.24 (Olivier): combine the finished algebraicity and absolute-flatness
  -- adapters with the pending trivial-idempotent lemma to invoke
  -- `isField_of_idempotents_trivial_of_isAbsolutelyFlatRing`.
  sorry

/-- Helper for Theorem 15.105.24 (Olivier): if the scalar-extended closed fiber over `q` is a
field, then there is at most one prime of `B ⊗[A] B` above `q` along `includeLeft`. -/
lemma tensorSquareMul_unique_primes_over_includeLeft_of_scalarExtension_field
    (q : PrimeSpectrum B)
    (hfield :
      let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
      let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
        tensorSquare_closedFiber_residueFieldAlgebra (A := A) (B := B) q
      IsField (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B)) :
    Subsingleton
      (PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
          ({q} : Set (PrimeSpectrum B))) := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    tensorSquare_closedFiber_residueFieldAlgebra (A := A) (B := B) q
  have hfield' :
      IsField (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) := by
    simpa [p] using hfield
  let _ : Field (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) :=
    IsField.toField hfield'
  let _ : Algebra q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) :=
    Algebra.TensorProduct.leftAlgebra
  let efiberLeftRing :
      q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B ≃ₐ[q.asIdeal.ResidueField]
        q.asIdeal.Fiber (B ⊗[A] B) := by
    -- Proof comment: Lemma `15.18.2` identifies the scalar-extended closed fiber with the tensor
    -- square fiber over `q` for the default left `B`-algebra structure on `B ⊗[A] B`.
    simpa [p] using
      (baseChanged_sourceFiber_algEquiv_rightOrderedFiber
        (R := A) (S := B) (R' := B) q q rfl)
  have hsubFiberSource :
      Subsingleton
        (PrimeSpectrum
          (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B)) :=
    inferInstance
  have hsubFiberLeft : Subsingleton (PrimeSpectrum (q.asIdeal.Fiber (B ⊗[A] B))) := by
    -- Proof comment: the left tensor-square fiber has singleton prime spectrum because it is
    -- algebra-equivalent to a field.
    exact
      (Equiv.subsingleton_congr
        (PrimeSpectrum.homeomorphOfRingEquiv efiberLeftRing.toRingEquiv).toEquiv).1
        hsubFiberSource
  let efiberLeftPrime :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
            ({q} : Set (PrimeSpectrum B)) ≃
        PrimeSpectrum (q.asIdeal.Fiber (B ⊗[A] B)) := by
    -- Proof comment: `PrimeSpectrum.preimageEquivFiber` rewrites primes above `q` along the left
    -- tensor inclusion as primes of the left fiber ring.
    simpa using (PrimeSpectrum.preimageEquivFiber B (B ⊗[A] B) q)
  exact (Equiv.subsingleton_congr efiberLeftPrime).2 hsubFiberLeft

/-- Helper for Theorem 15.105.24 (Olivier): tensor commutativity swaps the two structural
`B`-algebra maps into `B ⊗[A] B`. -/
lemma tensorSquare_comm_comp_includeRight :
    ((Algebra.TensorProduct.comm A B B).toRingHom.comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)) =
      ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom) := by
  -- Proof comment: the tensor symmetry sends `1 ⊗ b` to `b ⊗ 1`.
  ext b
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeft_apply]

/-- Helper for Theorem 15.105.24 (Olivier): the inverse tensor symmetry swaps the left structural
`B`-algebra map with the right one. -/
lemma tensorSquare_comm_comp_includeLeft :
    (((Algebra.TensorProduct.comm A B B).symm.toRingHom).comp
      ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)) =
      ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) := by
  -- Proof comment: the inverse tensor symmetry sends `b ⊗ 1` back to `1 ⊗ b`.
  ext b
  change
    (Algebra.TensorProduct.comm A B B).symm ((algebraMap B (B ⊗[A] B)) b) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b
  change
    (Algebra.TensorProduct.comm A B B).symm (b ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] b
  simpa using (Algebra.TensorProduct.comm_symm_tmul (R := A) (a := b) (b := (1 : B)))

/-- Helper for Theorem 15.105.24 (Olivier): if the scalar-extended closed fiber over `q` is a
field, then there is at most one prime of `B ⊗[A] B` above `q` along `includeRight`. -/
lemma tensorSquareMul_unique_primes_over_includeRight_of_scalarExtension_field
    (q : PrimeSpectrum B)
    (hfield :
      let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
      let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
        tensorSquare_closedFiber_residueFieldAlgebra (A := A) (B := B) q
      IsField (q.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B)) :
    Subsingleton
      (PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
          ({q} : Set (PrimeSpectrum B))) := by
  let hleft :=
    tensorSquareMul_unique_primes_over_includeLeft_of_scalarExtension_field
      (A := A) (B := B) q hfield
  let e :
      PrimeSpectrum (B ⊗[A] B) ≃ PrimeSpectrum (B ⊗[A] B) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm A B B).toRingEquiv).toEquiv
  have hforward :
      ∀ {Q : PrimeSpectrum (B ⊗[A] B)},
        Q ∈
            PrimeSpectrum.comap
              ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
              ({q} : Set (PrimeSpectrum B)) →
          e Q ∈
            PrimeSpectrum.comap
              ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
              ({q} : Set (PrimeSpectrum B)) := by
    intro Q hQ
    -- Proof comment: transporting a prime across tensor commutativity turns right contraction
    -- into left contraction via the inverse composition identity above.
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hQ ⊢
    change
      PrimeSpectrum.comap
        (((Algebra.TensorProduct.comm A B B).symm.toRingHom).comp
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)) Q = q
    rw [tensorSquare_comm_comp_includeLeft]
    exact hQ
  have hback :
      ∀ {Q : PrimeSpectrum (B ⊗[A] B)},
        Q ∈
            PrimeSpectrum.comap
              ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
              ({q} : Set (PrimeSpectrum B)) →
          e.symm Q ∈
            PrimeSpectrum.comap
              ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
              ({q} : Set (PrimeSpectrum B)) := by
    intro Q hQ
    -- Proof comment: the inverse transport uses the already-proved compatibility for
    -- `tensorSquare_comm_comp_includeRight`.
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hQ ⊢
    change
      PrimeSpectrum.comap
        (((Algebra.TensorProduct.comm A B B).toRingHom).comp
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)) Q = q
    rw [tensorSquare_comm_comp_includeRight]
    exact hQ
  let efiber :
      PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
            ({q} : Set (PrimeSpectrum B)) ≃
        PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
            ({q} : Set (PrimeSpectrum B)) :=
    { toFun := fun Q ↦ ⟨e Q, hforward Q.2⟩
      invFun := fun Q ↦ ⟨e.symm Q, hback Q.2⟩
      left_inv := by
        intro Q
        exact Subtype.ext (e.left_inv Q.1)
      right_inv := by
        intro Q
        exact Subtype.ext (e.right_inv Q.1) }
  -- Proof comment: the left fiber is already known to be a singleton, and tensor commutativity
  -- identifies it with the right fiber.
  exact (Equiv.subsingleton_congr efiber).2 hleft

/-- Helper for Theorem 15.105.24 (Olivier): Olivier's fiber argument shows that for each
`q : Spec(B)`, there is at most one prime of `B ⊗[A] B` above `q` along `includeRight`. -/
lemma tensorSquareMul_unique_primes_over_includeRight_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
    (q : PrimeSpectrum B) :
    Subsingleton
      (PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
          ({q} : Set (PrimeSpectrum B))) := by
  -- Proof comment: all transport around the tensor-square fiber is now explicit, so the only
  -- remaining input is the fieldness of Olivier's scalar-extended closed fiber.
  exact
      tensorSquareMul_unique_primes_over_includeRight_of_scalarExtension_field
      q
      (scalarExtension_closedFiber_isField_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
        q)

/-- Helper for Theorem 15.105.24 (Olivier): uniqueness of primes above every `q : Spec(B)` along
`includeRight` makes `Spec(B) → Spec(B ⊗[A] B)` for `lmul' A` bijective. -/
lemma tensorSquareMul_specComap_bijective_of_unique_primes_over_includeRight
    (hunique :
      ∀ q : PrimeSpectrum B,
        Subsingleton
          (PrimeSpectrum.comap
            ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
              ({q} : Set (PrimeSpectrum B)))) :
    Function.Bijective
      (PrimeSpectrum.comap
        ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom)) := by
  have hleft :=
    tensorSquareMul_specComap_includeRight_leftInverse (A := A) (B := B)
  constructor
  · -- Proof comment: the retraction through `includeRight` makes the diagonal spectrum map
    -- formally injective.
    exact hleft.injective
  · intro Q
    let q : PrimeSpectrum B :=
      PrimeSpectrum.comap
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) Q
    have hQ :
        PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) Q = q := rfl
    have hdiag :
        PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)
          (PrimeSpectrum.comap
            ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom) q) = q :=
      hleft q
    have hQmem :
        PrimeSpectrum.comap
            ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) Q ∈
          ({q} : Set (PrimeSpectrum B)) := by
      simpa [Set.mem_singleton_iff, q] using hQ
    have hdiagMem :
        PrimeSpectrum.comap
            ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)
            (PrimeSpectrum.comap
              ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom) q) ∈
          ({q} : Set (PrimeSpectrum B)) := by
      simpa [Set.mem_singleton_iff, q] using hdiag
    let Qfiber :
        PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
            ({q} : Set (PrimeSpectrum B)) := ⟨Q, hQmem⟩
    let Qdiag :
        PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
            ({q} : Set (PrimeSpectrum B)) :=
      ⟨PrimeSpectrum.comap
          ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom) q, hdiagMem⟩
    have hfiberEq : Qfiber = Qdiag := (hunique q).elim Qfiber Qdiag
    -- Proof comment: both `Q` and the diagonal prime lie over the same `q`, and the fiber over
    -- `q` is a singleton, so they coincide.
    refine ⟨q, ?_⟩
    exact (congrArg Subtype.val hfiberEq).symm

/-- A weakly étale local homomorphism out of a strictly henselian local ring is an epimorphism. -/
theorem algebra_isEpi_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale :
    Algebra.IsEpi A B := by
  -- Route correction: isolate Olivier's source proof at the diagonal map `B ⊗[A] B → B`.
  -- The flat/pure-ideal endgame is closed above; the remaining source-faithful work is to prove
  -- that each right fiber of `includeRight` is a field, which then forces bijectivity on spectra
  -- for `lmul' A`.
  rw [algebra_isEpi_iff_bijective_lmul]
  refine ⟨tensorSquareMul_injective_of_flat_and_specComap_bijective (A := A) (B := B) ?_,
    tensorSquareMul_surjective (A := A) (B := B)⟩
  have hunique :
      ∀ q : PrimeSpectrum B,
        Subsingleton
          (PrimeSpectrum.comap
            ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) ⁻¹'
              ({q} : Set (PrimeSpectrum B))) := by
    intro q
    -- Proof comment: the only remaining source-faithful ingredient is Olivier's uniqueness of the
    -- prime above each `q` in the `includeRight` fiber.
    exact
      tensorSquareMul_unique_primes_over_includeRight_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
        (A := A) (B := B) q
  exact
    tensorSquareMul_specComap_bijective_of_unique_primes_over_includeRight
      (A := A) (B := B) hunique

-- Proof sketch: once the public epimorphism bridge supplies the canonical owner, the local weakly
-- étale hypotheses give faithful flatness by `Module.FaithfullyFlat.of_flat_of_isLocalHom`, and
-- Lemma `10.107.7` finishes.
/-- Theorem 15.105.24 (Olivier): if `A → B` is a weakly étale local homomorphism of local rings
with `A` strictly henselian, then the structure map `A → B` is bijective, hence an isomorphism. -/
theorem bijective_algebraMap_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale :
    Function.Bijective (algebraMap A B) := by
  let _ : Algebra.IsEpi A B :=
    algebra_isEpi_of_localHom_of_strictHenselianLocalRing_of_isWeaklyEtale
  exact faithfullyFlat_epi_bijective <|
    RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom

end
