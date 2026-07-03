import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_2
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_1_2
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.Index
import Mathlib.RingTheory.Morita.Matrix

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v w

open scoped Matrix.Module

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
-- * source-facing: LinearRepresentations_Serre_1977's determinant-polynomial criterion and its unipotent triviality
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
  -- Route correction: LinearRepresentations_Serre_1977's proof only needs trace equality on the common image algebra, so
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

/-- Helper for Exercise 18-18.2-6: an algebra homomorphism acts by the ambient scalar
multiplication on scalar elements. -/
lemma algHom_scalar_action_apply
    {A : Type*} [Ring A] [Algebra k A]
    {X : Type*} [AddCommGroup X] [Module k X]
    (φ : A →ₐ[k] Module.End k X) (r : k) (x : X) :
    (φ (algebraMap k A r)) x = r • x := by
  -- Evaluate the algebra-hom commutation relation at the chosen vector.
  simpa using congrArg (fun f : Module.End k X ↦ f x) (φ.commutes r)

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
  let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra k G ⧸ I
  let φV : A →ₐ[k] Module.End k V :=
    Ideal.Quotient.liftₐ I ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
  let φW : A →ₐ[k] Module.End k W :=
    Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
  have htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
    -- Route correction: this is the last valid quotient-level invariant presently available. The
    -- stronger exterior-power descent on the same quotient algebra is blocked by the
    -- nonadditivity of `A ↦ exteriorPower.map n A`.
    simpa [ψ, I, A, φV, φW] using
      trace_eq_on_common_kernel_quotient_of_det_one_add_polynomial_eq
        (ρ := ρ) (ρ' := ρ') hdet
  let _ : Module.Finite k A := by
    -- The common image algebra is finite-dimensional because it is a quotient of the image in
    -- `End_k(V) × End_k(W)`.
    simpa [ψ, I, A] using common_kernel_quotient_finite (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing A := by
    -- The quotient is semisimple because it acts faithfully on the descended semisimple modules.
    simpa [ψ, I, A] using
      common_kernel_quotient_isSemisimpleRing
        (ρ := ρ) (ρ' := ρ') hρ hρ'
  letI : Module A V := Module.compHom V φV.toRingHom
  letI : Module A W := Module.compHom W φW.toRingHom
  have hsemV : IsSemisimpleModule A V := by
    have hsemV_from_monoidAlgebra :
        let _ : Module (MonoidAlgebra k G) V :=
          Module.compHom V (φV.toRingHom.comp (Ideal.Quotient.mkₐ k I).toRingHom)
        IsSemisimpleModule (MonoidAlgebra k G) V := by
      -- Restricting scalars along the quotient map recovers the original `k[G]`-module.
      simpa [A, I, φV, ψ] using
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
    exact
      isSemisimpleModule_of_ringHom_surjective
        (q := (Ideal.Quotient.mkₐ k I).toRingHom)
        (hq := Ideal.Quotient.mk_surjective)
        hsemV_from_monoidAlgebra
  have hsemW : IsSemisimpleModule A W := by
    have hsemW_from_monoidAlgebra :
        let _ : Module (MonoidAlgebra k G) W :=
          Module.compHom W (φW.toRingHom.comp (Ideal.Quotient.mkₐ k I).toRingHom)
        IsSemisimpleModule (MonoidAlgebra k G) W := by
      -- The same quotient-action comparison holds for the second representation.
      simpa [A, I, φW, ψ] using
        (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ').mp hρ'
    exact
      isSemisimpleModule_of_ringHom_surjective
        (q := (Ideal.Quotient.mkₐ k I).toRingHom)
        (hq := Ideal.Quotient.mk_surjective)
        hsemW_from_monoidAlgebra
  have hexteriorTrace :
      ∀ n (a : MonoidAlgebra k G),
        LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
          LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a) := by
    intro n a
    -- Route correction: this is the exact additive invariant delivered by LinearRepresentations_Serre_1977's proof route on
    -- `k[G]`; the missing owner still has to convert these exterior-power traces into
    -- multiplicity equality on the common semisimple image algebra.
    exact
      trace_eq_asAlgebraHom_of_nthExteriorPower_character_eq_of_det_one_add_polynomial_eq
        (ρ := ρ) (ρ' := ρ') hdet n a
  have hcompV : φV.comp (Ideal.Quotient.mkₐ k I) = ρ.asAlgebraHom := by
    -- The quotient action was defined precisely so that composing with the quotient map recovers
    -- the original representation algebra homomorphism.
    simpa [ψ, I, φV] using
      common_kernel_quotient_left_lift_comp_eq_asAlgebraHom (ρ := ρ) (ρ' := ρ')
  have hcompW : φW.comp (Ideal.Quotient.mkₐ k I) = ρ'.asAlgebraHom := by
    -- The same compatibility holds for the second representation.
    simpa [ψ, I, φW] using
      common_kernel_quotient_right_lift_comp_eq_asAlgebraHom (ρ := ρ) (ρ' := ρ')
  have hAlinear : Nonempty (V ≃ₗ[A] W) := by
    -- Route correction: pass the quotient map and its algebra-hom compatibility directly to the
    -- projector-lift owner, matching the source proof's density step.
    simpa [A, φV, φW] using
      nonempty_linearEquiv_of_exterior_trace_eq_on_finite_semisimple_image
        (A := A) (V := V) (W := W) (ρ := ρ) (ρ' := ρ')
        (φV := φV) (φW := φW) (liftι := Ideal.Quotient.mkₐ k I) hcompV hcompW
        Ideal.Quotient.mk_surjective
        (by simpa [A, φV] using hsemV)
        (by simpa [A, φW] using hsemW)
        hexteriorTrace
  rcases hAlinear with ⟨e⟩
  -- Convert the descended `A`-linear equivalence back into a `G`-equivariant equivalence.
  let eₖ : V ≃ₗ[k] W :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        have hVscalar : (φV (algebraMap k A r) : V →ₗ[k] V) x = r • x :=
          algHom_scalar_action_apply (k := k) (φ := φV) r x
        have hWscalar : (φW (algebraMap k A r) : W →ₗ[k] W) (e x) = r • e x :=
          algHom_scalar_action_apply (k := k) (φ := φW) r (e x)
        calc
          e (r • x) = e ((φV (algebraMap k A r)) x) := by rw [hVscalar]
          _ = (φW (algebraMap k A r)) (e x) := by
                exact e.map_smul (algebraMap k A r) x
          _ = r • e x := hWscalar }
  refine ⟨Representation.Equiv.mk eₖ ?_⟩
  intro g
  ext x
  let a : A := Ideal.Quotient.mkₐ k I ((MonoidAlgebra.of k G) g)
  have hVg : (φV a : V →ₗ[k] V) x = (ρ g) x := by
    simpa [a, A, I, φV, Representation.asAlgebraHom_of]
  have hWg : (φW a : W →ₗ[k] W) (e x) = (ρ' g) (e x) := by
    simpa [a, A, I, φW, Representation.asAlgebraHom_of]
  calc
    e ((ρ g) x) = e ((φV a) x) := by rw [hVg]
    _ = (φW a) (e x) := by exact e.map_smul a x
    _ = (ρ' g) (e x) := hWg

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
