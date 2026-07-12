import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.ExteriorDeterminants
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_2
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.CommonKernelQuotient
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.MatrixCornerActions
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.ProductIdempotentDecomposition
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.SplitDensityOwner
import Mathlib.LinearAlgebra.Basis.VectorSpace

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v w

open scoped Matrix.Module
open scoped TensorProduct

namespace Representation

section

variable {k : Type} [Field k]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- Domain-style sampling for this item:
-- * `Representation.Equiv` is the canonical owner for isomorphism of unbundled
--   `k`-representations.
-- * `Representation.nthExteriorPower` and the Chapter `9` determinant bridge
--   `exteriorPowerCharacterSeries_eval_eq_det` are the canonical owner-level link from
--   `(-ρ s).charpoly.reverse` to exterior-power character data.
-- * `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple` in Remark `14-14.1-2`
--   is the chapter's semisimple isomorphism owner on bundled finite-dimensional
--   representations.
-- * `Representation.Equiv.toFDRepIso` is the exact bridge from the source-facing unbundled
--   `ρ.Equiv ρ'` language to the bundled `FDRep.of ρ ≅ FDRep.of ρ'` owner used by Chapter `14`.
--
-- Primitive data vs derived API:
-- * primitive data: the semisimple representations `ρ`, `ρ'` and the equality of the basis-free
--   determinant polynomials `(-ρ s).charpoly.reverse`.
-- * derived API: equality of the exterior-power character data, hence equality of the semisimple
--   Grothendieck classes and the resulting isomorphism criterion.
--
-- Layer triage:
-- * source-facing: Serre's determinant-polynomial criterion and its unipotent triviality
--   corollary.
-- * core/canonical: the bundled semisimple owner theorem
--   `finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple` on `FDRep.of ρ` and
--   `FDRep.of ρ'`.
-- * bridge/view: Chapter `9`'s determinant/exterior-power comparison, the rebundling `FDRep.of`,
--   and the source-facing isomorphism bridge `Representation.Equiv.toFDRepIso`.

section EquivalenceCriterion

variable {V W : Type w}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper for Exercise 18-18.2-6: for each exterior degree, equality of the determinant
polynomials `det (1 + ρ(s) T)` forces equality of the corresponding exterior-power characters. -/
lemma nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse)
    (n : ℕ) :
    (ρ.nthExteriorPower n).character = (ρ'.nthExteriorPower n).character := by
  ext s
  -- Read the `n`th coefficient of `det (1 + ρ(s) T)` through the exterior-power trace bridge.
  calc
    (ρ.nthExteriorPower n).character s =
        LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n (ρ s)) := by
          simp [Representation.character, Representation.nthExteriorPower]
    _ = (((-ρ s).charpoly.reverse : Polynomial k).coeff n) := by
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ s) n
    _ = (((-ρ' s).charpoly.reverse : Polynomial k).coeff n) := by
          rw [hdet s]
    _ = LinearMap.trace k (⋀[k]^n W) (exteriorPower.map n (ρ' s)) := by
          symm
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ' s) n
    _ = (ρ'.nthExteriorPower n).character s := by
          simp [Representation.character, Representation.nthExteriorPower]

/-- Helper for Exercise 18-18.2-6: the determinant-polynomial hypothesis supplies trace equality
on the faithful common-kernel quotient algebra. -/
lemma trace_eq_on_common_kernel_quotient_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let A := MonoidAlgebra k G ⧸ I
    let φV : A →ₐ[k] Module.End k V :=
      Ideal.Quotient.liftₐ I ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
    let φW : A →ₐ[k] Module.End k W :=
      Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
    ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
  -- Route correction: Serre's proof only needs trace equality on the common image algebra, so
  -- we first extract ordinary character equality from the determinant polynomials and then
  -- descend that linear invariant across the quotient.
  have hchar :
      ρ.character = ρ'.character :=
    character_eq_of_det_one_add_polynomial_eq (ρ := ρ) (ρ' := ρ') hdet
  simpa using
    trace_eq_on_common_kernel_quotient_of_character_eq (ρ := ρ) (ρ' := ρ') hchar

/-- Helper for Exercise 18-18.2-6: for every exterior degree, the determinant-polynomial
hypothesis gives trace equality on the whole monoid algebra for the induced exterior-power
representations. -/
lemma trace_eq_asAlgebraHom_of_nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse)
    (n : ℕ) (a : MonoidAlgebra k G) :
    LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
      LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a) := by
  -- The source proof first upgrades the determinant identity to equality of all exterior-power
  -- characters, and only then extends that additive invariant from `G` to `k[G]`.
  have hchar :
      (ρ.nthExteriorPower n).character = (ρ'.nthExteriorPower n).character :=
    nthExteriorPower_character_eq_of_det_one_add_polynomial_eq (ρ := ρ) (ρ' := ρ') hdet n
  exact
    trace_eq_asAlgebraHom_of_character_eq
      (ρ := ρ.nthExteriorPower n) (ρ' := ρ'.nthExteriorPower n) hchar a

/-- Helper for Exercise 18-18.2-6: the determinant-polynomial hypothesis already yields ordinary
trace equality on every element of `k[G]`. This is the `n = 1` shadow of the exterior-power
comparison that later feeds the source-faithful separator argument. -/
lemma trace_eq_asAlgebraHom_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse)
    (a : MonoidAlgebra k G) :
    LinearMap.trace k V (ρ.asAlgebraHom a) =
      LinearMap.trace k W (ρ'.asAlgebraHom a) := by
  -- First collapse the determinant hypothesis to ordinary character equality on `G`, then extend
  -- that additive invariant linearly across the whole monoid algebra.
  have hchar :
      ρ.character = ρ'.character :=
    character_eq_of_det_one_add_polynomial_eq (ρ := ρ) (ρ' := ρ') hdet
  exact trace_eq_asAlgebraHom_of_character_eq (ρ := ρ) (ρ' := ρ') hchar a

/-- Helper for Exercise 18-18.2-6: an algebra homomorphism acts by the ambient scalar
multiplication on scalar elements. -/
lemma algHom_scalar_action_apply
    {A : Type*} [Ring A] [Algebra k A]
    {X : Type*} [AddCommGroup X] [Module k X]
    (φ : A →ₐ[k] Module.End k X) (r : k) (x : X) :
    (φ (algebraMap k A r)) x = r • x := by
  -- Evaluate the algebra-hom commutation relation at the chosen vector.
  exact congrArg (fun f : Module.End k X ↦ f x) (φ.commutes r)

/-- Helper for Exercise 18-18.2-6: for a `k[G]`-module viewed through
`Representation.ofModule'`, the induced monoid-algebra action is the original scalar
multiplication. -/
lemma ofModulePrime_asAlgebraHom_apply_local
    (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M]
    (r : MonoidAlgebra k G) (m : M) :
    ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r) m = r • m := by
  -- Expand the monoid-algebra element linearly and check the claim on generators.
  refine MonoidAlgebra.induction_on
    (p := fun s : MonoidAlgebra k G ↦
      ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom s) m = s • m)
    r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    simp [ha, hb, add_smul]
  · intro a b hb
    simp [hb]

/-- Helper for Exercise 18-18.2-6: the owner module of `Representation.ofModule'` is canonically
the original `k[G]`-module. -/
lemma nonempty_ofModulePrime_asModuleLinearEquiv_local
    (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M] :
    Nonempty ((Representation.ofModule' (k := k) (G := G) M).asModule ≃ₗ[MonoidAlgebra k G] M) := by
  let toFun : (Representation.ofModule' (k := k) (G := G) M).asModule → M :=
    fun x ↦ (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x
  let invFun : M → (Representation.ofModule' (k := k) (G := G) M).asModule :=
    fun x ↦ (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv.symm x
  have hsmul : ∀ (r : MonoidAlgebra k G) x, toFun (r • x) = r • toFun x := by
    intro r x
    calc
      (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv (r • x) =
          ((Representation.ofModule' (k := k) (G := G) M).asAlgebraHom r)
            ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x) := by
              exact
                (Representation.asModuleEquiv_map_smul
                  (ρ := Representation.ofModule' (k := k) (G := G) M) r x)
      _ = r • (Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x := by
            simpa [toFun] using
              (ofModulePrime_asAlgebraHom_apply_local (k := k) (G := G) M r
                ((Representation.ofModule' (k := k) (G := G) M).asModuleEquiv x))
  exact
    ⟨{ toFun := toFun
       invFun := invFun
       left_inv := fun x ↦ by simp [toFun, invFun]
       right_inv := fun x ↦ by simp [toFun, invFun]
       map_add' := fun x y ↦ rfl
       map_smul' := hsmul }⟩

/-- Helper for Exercise 18-18.2-6: the left quotient action on the common-kernel quotient
recovers the original representation after precomposition with the quotient map. -/
lemma common_kernel_quotient_left_lift_comp_eq_asAlgebraHom
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let φV : (MonoidAlgebra k G ⧸ I) →ₐ[k] Module.End k V :=
      Ideal.Quotient.liftₐ I ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
    φV.comp (Ideal.Quotient.mkₐ k I) = ρ.asAlgebraHom := by
  -- The quotient lift is defined exactly to factor the original action through `k[G] ⧸ I`.
  simpa using
    Ideal.Quotient.liftₐ_comp
      (RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom)) ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: the right quotient action on the common-kernel quotient
recovers the original representation after precomposition with the quotient map. -/
lemma common_kernel_quotient_right_lift_comp_eq_asAlgebraHom
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let φW : (MonoidAlgebra k G ⧸ I) →ₐ[k] Module.End k W :=
      Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
    φW.comp (Ideal.Quotient.mkₐ k I) = ρ'.asAlgebraHom := by
  -- The same quotient-factorization identity holds for the second representation.
  simpa using
    Ideal.Quotient.liftₐ_comp
      (RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom)) ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: an `A`-linear equivalence for the descended quotient actions
already intertwines the original `k[G]`-representations after restricting scalars back along the
quotient map. -/
lemma nonempty_equiv_of_common_kernel_quotient_linearEquiv
    {A : Type*} [Ring A] [Algebra k A]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    [Module A V] [Module A W]
    [IsScalarTower k A V] [IsScalarTower k A W]
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hsmulV : ∀ a : A, ∀ x : V, a • x = (φV a) x)
    (hsmulW : ∀ a : A, ∀ x : W, a • x = (φW a) x)
    (e : V ≃ₗ[A] W) :
    Nonempty (ρ.Equiv ρ') := by
  -- Restrict the `A`-linear equivalence to `k`, then rewrite the `k[G]`-action through the lift.
  refine ⟨Representation.Equiv.mk (e.restrictScalars k) ?_⟩
  intro g
  ext x
  have hρg : ρ g = φV (liftι (MonoidAlgebra.of k G g)) := by
    -- Evaluate the compatibility of `φV` with the quotient lift on the monoid generator `g`.
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f (MonoidAlgebra.of k G g))
        hφV.symm
  have hρ'g : ρ' g = φW (liftι (MonoidAlgebra.of k G g)) := by
    -- The same lift identity identifies the second representation action at `g`.
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f (MonoidAlgebra.of k G g))
        hφW.symm
  -- `A`-linearity with respect to the lifted monoid generator is exactly the intertwining relation.
  calc
    e (ρ g x) = e (liftι (MonoidAlgebra.of k G g) • x) := by rw [hρg, ← hsmulV]
    _ = liftι (MonoidAlgebra.of k G g) • e x := by
          exact e.map_smul (liftι (MonoidAlgebra.of k G g)) x
    _ = (φW (liftι (MonoidAlgebra.of k G g))) (e x) := by rw [hsmulW]
    _ = ρ' g (e x) := by rw [← hρ'g]

/-- Helper for Exercise 18-18.2-6: specializing the exterior-trace hypothesis to the monoid
generators recovers the determinant-polynomial equality on `G`. -/
lemma detOneAddPolynomialEq_of_exteriorTraceOnGeneratorsLocal
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse := by
  intro g
  ext n
  -- On generators, the exterior-power action is the honest exterior power of `ρ g`.
  calc
    (((-ρ g).charpoly.reverse : Polynomial k).coeff n) =
        LinearMap.trace k (⋀[k]^n V)
          ((ρ.nthExteriorPower n).asAlgebraHom (MonoidAlgebra.of k G g)) := by
            simpa [Representation.nthExteriorPower, Representation.asAlgebraHom_of] using
              (trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ g) n).symm
    _ =
        LinearMap.trace k (⋀[k]^n W)
          ((ρ'.nthExteriorPower n).asAlgebraHom (MonoidAlgebra.of k G g)) :=
        hexteriorTrace n (MonoidAlgebra.of k G g)
    _ = (((-ρ' g).charpoly.reverse : Polynomial k).coeff n) := by
          simpa [Representation.nthExteriorPower, Representation.asAlgebraHom_of] using
            trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ' g) n

/-- Helper for Exercise 18-18.2-6: the scalar-extension route through `AlgebraicClosure k`
reduces determinant-polynomial equality to the ordinary-character separator argument and then
descends the resulting equivalence back to `k`. -/
theorem nonemptyEquivOfDetOneAddPolynomialEqViaAlgClosureLocal
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
  let A := MonoidAlgebra k G ⧸ I
  let liftι : MonoidAlgebra k G →ₐ[k] A := Ideal.Quotient.mkₐ k I
  let φV : A →ₐ[k] Module.End k V :=
    Ideal.Quotient.liftₐ I ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
  let φW : A →ₐ[k] Module.End k W :=
    Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
  have hφV : φV.comp liftι = ρ.asAlgebraHom := by
    -- The left quotient action is the original action factored through the common image algebra.
    simpa [ψ, I, A, liftι, φV] using
      common_kernel_quotient_left_lift_comp_eq_asAlgebraHom (ρ := ρ) (ρ' := ρ')
  have hφW : φW.comp liftι = ρ'.asAlgebraHom := by
    -- The same factorization identity holds for the right action.
    simpa [ψ, I, A, liftι, φW] using
      common_kernel_quotient_right_lift_comp_eq_asAlgebraHom (ρ := ρ) (ρ' := ρ')
  have hlift : Function.Surjective liftι := by
    -- Every element of the quotient algebra comes from a monoid-algebra lift.
    simpa [I, A, liftι] using (Ideal.Quotient.mkₐ_surjective k I)
  let _ : Module.Finite k A := by
    -- The common image algebra is finite-dimensional because it identifies with a finite range.
    simpa [ψ, I, A] using common_kernel_quotient_finite (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing A := by
    -- Semisimplicity of both representations forces semisimplicity of their common finite image.
    simpa [ψ, I, A] using
      common_kernel_quotient_isSemisimpleRing (ρ := ρ) (ρ' := ρ') hρ hρ'
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      exact congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
      change (φW (algebraMap k A r)) x = r • x
      exact congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
  have hV : IsSemisimpleModule A V := by
    -- Over a semisimple ring every module is semisimple, so the descended action is ready to use.
    infer_instance
  have hW : IsSemisimpleModule A W := by
    -- The same semisimplicity transfer applies to the second descended module.
    infer_instance
  have hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a) := by
    intro n a
    -- The determinant-polynomial hypothesis already controls every exterior-power trace upstairs.
    exact
      trace_eq_asAlgebraHom_of_nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
        (ρ := ρ) (ρ' := ρ') hdet n a
  obtain ⟨e⟩ :=
    nonempty_linearEquiv_of_exterior_trace_eq_on_finite_semisimple_image
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hV hW hexteriorTrace
  -- Once the descended modules are `A`-linearly equivalent, restriction along the quotient map
  -- recovers an intertwining equivalence of the original `k[G]`-representations.
  exact
    nonempty_equiv_of_common_kernel_quotient_linearEquiv
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW
      (fun a x ↦ rfl) (fun a x ↦ rfl) e

/-- Helper for Exercise 18-18.2-6: the determinant-polynomial hypothesis identifies the two
semisimple representations by the complete-simple-family separator argument from Theorem `42(a)`. -/
lemma nonempty_equiv_of_det_one_add_polynomial_eq_via_separator
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  -- Route correction: the primitive-projector finite-image detour has been replaced by the
  -- global scalar-extension engine, so the separator theorem is now just that owner-level call.
  exact
    nonemptyEquivOfDetOneAddPolynomialEqViaAlgClosureLocal
      (ρ := ρ) (ρ' := ρ') hρ hρ' hdet

/-- Exercise 18-18.2-6: two semisimple finite-dimensional `k[G]`-modules for an arbitrary monoid
are isomorphic as `k[G]`-modules if, for every `s : G`, the polynomial `det (1 + s T)` agrees on
the two modules; in Lean this is expressed by equality of `(-ρ s).charpoly.reverse`, the
basis-free polynomial corresponding to `det (1 + ρ(s) T)`. -/
-- Proof sketch: the coefficients of `(-ρ s).charpoly.reverse` are the values at `s` of the
-- characters of the exterior powers of `ρ`, via Chapter `9`'s determinant/exterior-power bridge.
-- Equality of these polynomials for all `s` therefore identifies the exterior-power character data
-- of `ρ` and `ρ'`. In the semisimple Grothendieck group this forces the same multiset of simple
-- constituents, and Remark `14-14.1-2` then upgrades equality of classes to an isomorphism.
theorem nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  -- Route correction: the old common-image quotient proof has been removed because it only
  -- extracted the `n = 1` trace relation. The remaining source-faithful frontier is the separator
  -- argument on a complete simple family, isolated in the helper below.
  exact
    nonempty_equiv_of_det_one_add_polynomial_eq_via_separator
      (ρ := ρ) (ρ' := ρ') hρ hρ' hdet

end EquivalenceCriterion

section TrivialityCriterion

/-- Helper for Exercise 18-18.2-6: a unipotent action endomorphism has the same determinant
polynomial `det (1 + s T)` as the trivial action. -/
lemma charpoly_reverse_neg_eq_trivial_of_isNilpotent_sub_one
    {ρ : Representation k G V} (s : G) (hs : IsNilpotent (ρ s - 1)) :
    (-ρ s).charpoly.reverse = (-(Representation.trivial k G V s)).charpoly.reverse := by
  -- Rewrite unipotence as nilpotence of `1 - ρ(s)` so that `charpoly_sub_smul` applies directly.
  have hneg : IsNilpotent ((1 : V →ₗ[k] V) - ρ s) := by
    simpa [sub_eq_add_neg, add_comm] using hs.neg
  have hnil : (((1 : V →ₗ[k] V) - ρ s)).charpoly = Polynomial.X ^ Module.finrank k V :=
    IsNilpotent.charpoly_eq_X_pow_finrank hneg
  have hchar : (-ρ s).charpoly = (Polynomial.X + 1) ^ Module.finrank k V := by
    -- Translating the characteristic polynomial by `-1` identifies the `-ρ(s)` characteristic
    -- polynomial with the nilpotent polynomial `X^n`.
    have hsub : (((1 : V →ₗ[k] V) - ρ s)).charpoly =
        (-ρ s).charpoly.comp (Polynomial.X + Polynomial.C (-1 : k)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        LinearMap.charpoly_sub_smul (-ρ s) (-1 : k)
    rw [hnil] at hsub
    have hcomp :=
      congrArg (fun q : Polynomial k ↦ q.comp (Polynomial.X + 1)) hsub.symm
    simpa [Polynomial.comp_assoc, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, pow_mul] using
      hcomp
  -- Both sides are now the reverse of the same binomial characteristic polynomial.
  have htriv : (-(Representation.trivial k G V s)).charpoly =
      (Polynomial.X + 1) ^ Module.finrank k V := by
    simpa [Representation.trivial] using
      LinearMap.charpoly_sub_smul (0 : V →ₗ[k] V) (1 : k)
  rw [hchar, htriv]

/-- Helper for Exercise 18-18.2-6: an equivariant equivalence with the trivial representation
forces the original representation itself to be trivial. -/
lemma isTrivial_of_nonempty_equiv_trivial
    {ρ : Representation k G V}
    (h : Nonempty (ρ.Equiv (Representation.trivial k G V))) :
    ρ.IsTrivial := by
  rcases h with ⟨e⟩
  -- Conjugating `ρ(g)` by the chosen equivalence identifies it with the identity map.
  refine ⟨fun g ↦ ?_⟩
  ext x
  have hx : e ((ρ g) x) = e x := by
    simpa [Representation.trivial] using
      congrArg (fun f : V →ₗ[k] V ↦ f x) (e.isIntertwining' g)
  exact e.injective hx

/-- Helper for Exercise 18-18.2-6: the trivial representation is semisimple because every
subspace is stable under the identity action. -/
lemma trivial_isSemisimpleRepresentation :
    IsSemisimpleRepresentation (Representation.trivial k G V) := by
  let e : Submodule k V ≃o Subrepresentation (Representation.trivial k G V) :=
    { toFun := fun W ↦
        { toSubmodule := W
          apply_mem_toSubmodule := by
            intro g x hx
            simpa [Representation.trivial] using hx }
      invFun := Subrepresentation.toSubmodule
      left_inv := by
        intro W
        rfl
      right_inv := by
        intro W
        rfl
      map_rel_iff' := by
        intro W W'
        rfl }
  letI : ComplementedLattice (Subrepresentation (Representation.trivial k G V)) :=
    OrderIso.complementedLattice e
  infer_instance

/-- A semisimple finite-dimensional representation is trivial when every action endomorphism is
unipotent, i.e. when `ρ s - 1` is nilpotent for every `s : G`. -/
-- Proof sketch: compare `ρ` with the trivial representation on the same vector space. If every
-- `ρ s` is unipotent, then
-- `(-ρ s).charpoly.reverse = (-(Representation.trivial k G V s)).charpoly.reverse`
-- for all `s`, because both equal `(X + 1) ^ finrank k V`. Apply
-- `nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq`, and transport the trivial action
-- across the resulting equivariant linear equivalence.
theorem isTrivial_of_isSemisimple_of_isNilpotent_sub_one
    {ρ : Representation k G V} (hρ : IsSemisimpleRepresentation ρ)
    (hunipotent : ∀ s : G, IsNilpotent (ρ s - 1)) :
    ρ.IsTrivial := by
  -- Compare `ρ` with the trivial representation via the determinant-polynomial criterion above.
  have htriv : IsSemisimpleRepresentation (Representation.trivial k G V) :=
    trivial_isSemisimpleRepresentation
  have hequiv : Nonempty (ρ.Equiv (Representation.trivial k G V)) := by
    apply nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq hρ htriv
    intro s
    exact charpoly_reverse_neg_eq_trivial_of_isNilpotent_sub_one s (hunipotent s)
  -- Once the two representations are equivariantly equivalent, the action must be trivial.
  exact isTrivial_of_nonempty_equiv_trivial hequiv

end TrivialityCriterion

end

end Representation
