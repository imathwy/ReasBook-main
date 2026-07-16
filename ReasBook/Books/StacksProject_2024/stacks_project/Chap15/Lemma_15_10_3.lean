import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import StacksProject_2024.stacks_project.Chap10.Lemma_10_16_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_36_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_36_23
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)
variable [Module.Flat A B] [Algebra.IsIntegral A B] [Algebra.FinitePresentation A B]

open LinearMap

local notation "IB" => I.map (algebraMap A B)
local notation "AQM" => A ⧸ ((I • (⊤ : Submodule A A)) : Submodule A A)
local notation "BQM" => B ⧸ ((I • (⊤ : Submodule A B)) : Submodule A B)

/-- Helper for Lemma 15.10.3: a quotient linear map from a projective source lifts through the
canonical quotient projection. -/
private theorem exists_lift_with_prescribed_quotientMapByIdeal
    {Q : Type*} [AddCommGroup Q] [Module A Q] [Module.Projective A Q]
    {M : Type*} [AddCommGroup M] [Module A M]
    (gbar : Q ⧸ (I • (⊤ : Submodule A Q)) →ₗ[A] M ⧸ (I • (⊤ : Submodule A M))) :
    ∃ g : Q →ₗ[A] M, g.quotientMapByIdeal I = gbar := by
  let gbarLift : Q →ₗ[A] M ⧸ (I • (⊤ : Submodule A M)) :=
    gbar.comp (I • (⊤ : Submodule A Q)).mkQ
  -- Lift the quotient map through the canonical quotient projection.
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property (I • (⊤ : Submodule A M)).mkQ gbarLift
      (Submodule.mkQ_surjective _)
  have hgsmul : I • (⊤ : Submodule A Q) ≤ Submodule.comap g (I • (⊤ : Submodule A M)) := by
    exact Submodule.smul_top_le_comap_smul_top I g
  have hcomp :
      ((I • (⊤ : Submodule A Q)).mapQ (I • (⊤ : Submodule A M)) g hgsmul).comp
          (I • (⊤ : Submodule A Q)).mkQ =
        (I • (⊤ : Submodule A M)).mkQ.comp g :=
    Submodule.mapQ_mkQ (I • (⊤ : Submodule A Q)) (I • (⊤ : Submodule A M)) g
  refine ⟨g, ?_⟩
  -- Evaluate on quotient representatives to identify the induced quotient map.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A Q)) x
  simpa [LinearMap.quotientMapByIdeal, gbarLift] using
    (DFunLike.congr_fun hcomp x).trans (DFunLike.congr_fun hg x)

/-- Helper for Lemma 15.10.3: evaluating an induced quotient map on a quotient class matches
first applying the linear map and then quotienting. -/
private theorem quotientMapByIdeal_apply_mkQ
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (x : M) :
    f.quotientMapByIdeal I ((I • (⊤ : Submodule A M)).mkQ x) =
      (I • (⊤ : Submodule A N)).mkQ (f x) := by
  -- Expand the induced quotient map through the defining `mapQ_mkQ` square.
  simpa [LinearMap.quotientMapByIdeal] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ (I • (⊤ : Submodule A M)) (I • (⊤ : Submodule A N)) f) x

/-- Helper for Lemma 15.10.3: quotient inverses force the lifted composites to become the identity
after reduction modulo `I`. -/
private theorem quotientMapByIdeal_comp_eq_id_of_inverse
    {P : Type*} [AddCommGroup P] [Module A P]
    {P' : Type*} [AddCommGroup P'] [Module A P']
    (e : (P ⧸ (I • (⊤ : Submodule A P))) ≃ₗ[A] (P' ⧸ (I • (⊤ : Submodule A P'))))
    (f : P →ₗ[A] P') (g : P' →ₗ[A] P)
    (hf : f.quotientMapByIdeal I = e.toLinearMap)
    (hg : g.quotientMapByIdeal I = e.symm.toLinearMap) :
    (g.comp f).quotientMapByIdeal I = LinearMap.id ∧
      (f.comp g).quotientMapByIdeal I = LinearMap.id := by
  constructor
  · -- Evaluate on quotient representatives and rewrite by the inverse identities.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A P)) x
    calc
      (g.comp f).quotientMapByIdeal I ((I • (⊤ : Submodule A P)).mkQ x)
          = (I • (⊤ : Submodule A P)).mkQ (g (f x)) := by
              simp
      _ = g.quotientMapByIdeal I (f.quotientMapByIdeal I ((I • (⊤ : Submodule A P)).mkQ x)) := by
            simp
      _ = e.symm.toLinearMap (e.toLinearMap ((I • (⊤ : Submodule A P)).mkQ x)) := by
            rw [hf, hg]
      _ = (I • (⊤ : Submodule A P)).mkQ x := by simp
  · -- The same computation gives the identity on the target quotient.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A P')) x
    calc
      (f.comp g).quotientMapByIdeal I ((I • (⊤ : Submodule A P')).mkQ x)
          = (I • (⊤ : Submodule A P')).mkQ (f (g x)) := by
              simp
      _ = f.quotientMapByIdeal I (g.quotientMapByIdeal I ((I • (⊤ : Submodule A P')).mkQ x)) := by
            simp
      _ = e.toLinearMap (e.symm.toLinearMap ((I • (⊤ : Submodule A P')).mkQ x)) := by
            rw [hf, hg]
      _ = (I • (⊤ : Submodule A P')).mkQ x := by simp

/-- Helper for Lemma 15.10.3: an integral finitely presented flat `A`-algebra is finite
projective as an `A`-module. -/
private theorem finite_projective_of_flat_integral_finitePresentation :
    Module.Finite A B ∧ Module.Projective A B := by
  have hfinite : Module.Finite A B :=
    (Algebra.finite_iff_isIntegral_and_finiteType).2 ⟨inferInstance, inferInstance⟩
  letI : Module.Finite A B := hfinite
  have hfinitePresentation : Module.FinitePresentation A B :=
    (Module.FinitePresentation.iff_of_finite_finitePresentation
      (R := A) (S := B) (M := B)).2 inferInstance
  letI : Module.FinitePresentation A B := hfinitePresentation
  -- Flat plus finite presentation gives projectivity.
  exact ⟨hfinite, Module.Flat.projective_of_finitePresentation (R := A) (M := B)⟩

/-- Helper for Lemma 15.10.3: the ideal quotient `B ⧸ I.map (algebraMap A B)` is canonically the
same `A`-module quotient as `B ⧸ (I • ⊤)`. -/
private noncomputable abbrev ideal_quotient_equiv_module_quotient :
    (B ⧸ IB) ≃ₗ[A] BQM :=
  (Submodule.Quotient.restrictScalarsEquiv A (IB : Ideal B)).symm.trans
    (Submodule.quotEquivOfEq
      (Submodule.restrictScalars A (IB : Submodule B B))
      ((I • (⊤ : Submodule A B)) : Submodule A B)
      (Ideal.smul_top_eq_map I).symm)

/-- Helper for Lemma 15.10.3: the canonical ideal-quotient/module-quotient bridge sends an ideal
quotient class to the corresponding module quotient class. -/
private theorem ideal_quotient_equiv_module_quotient_mk (x : B) :
    ideal_quotient_equiv_module_quotient (A := A) (B := B) (I := I)
        ((Ideal.Quotient.mk IB) x) =
      ((I • (⊤ : Submodule A B)) : Submodule A B).mkQ x := by
  have hrestrict :
      (Submodule.Quotient.restrictScalarsEquiv A (IB : Ideal B)).symm
          ((Ideal.Quotient.mk IB) x) =
        Submodule.Quotient.mk x := by
    -- The restriction-of-scalars quotient equivalence fixes quotient generators.
    apply (Submodule.Quotient.restrictScalarsEquiv A (IB : Ideal B)).injective
    simpa [Ideal.Quotient.mk_eq_mk] using
      (Submodule.Quotient.restrictScalarsEquiv_mk A (IB : Ideal B) x)
  -- Compute through the two quotient-model identifications one step at a time.
  calc
    ideal_quotient_equiv_module_quotient (A := A) (B := B) (I := I)
        ((Ideal.Quotient.mk IB) x)
      = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars A (IB : Submodule B B))
          ((I • (⊤ : Submodule A B)) : Submodule A B)
          (Ideal.smul_top_eq_map I).symm)
          ((Submodule.Quotient.restrictScalarsEquiv A (IB : Ideal B)).symm
            ((Ideal.Quotient.mk IB) x)) := by
            rfl
    _ = (Submodule.quotEquivOfEq
          (Submodule.restrictScalars A (IB : Submodule B B))
          ((I • (⊤ : Submodule A B)) : Submodule A B)
          (Ideal.smul_top_eq_map I).symm)
          (Submodule.Quotient.mk x) := by
            rw [hrestrict]
    _ = ((I • (⊤ : Submodule A B)) : Submodule A B).mkQ x := by
            simpa using
              (Submodule.quotEquivOfEq_mk
                (Submodule.restrictScalars A (IB : Submodule B B))
                ((I • (⊤ : Submodule A B)) : Submodule A B)
                (Ideal.smul_top_eq_map I).symm x)

/-- Helper for Lemma 15.10.3: the inverse quotient-model bridge sends a module quotient class back
to the corresponding ideal quotient class. -/
private theorem ideal_quotient_equiv_module_quotient_symm_mkQ (x : B) :
    (ideal_quotient_equiv_module_quotient (A := A) (B := B) (I := I)).symm
        (((I • (⊤ : Submodule A B)) : Submodule A B).mkQ x) =
      (Ideal.Quotient.mk IB) x := by
  -- Apply the forward bridge to reduce to the already-normalized generator formula.
  apply (ideal_quotient_equiv_module_quotient (A := A) (B := B) (I := I)).injective
  simpa using
    ideal_quotient_equiv_module_quotient_mk (A := A) (B := B) (I := I) x

/-- Helper for Lemma 15.10.3: after transporting the quotient algebra equivalence to module
quotients, it is exactly the induced quotient map of `algebraMap A B`. -/
private theorem quotient_algebraMap_eq_conjugate_of_quotient_equiv
    (hquot : (A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ IB)) :
    ∃ e : AQM ≃ₗ[A] BQM, (Algebra.linearMap A B).quotientMapByIdeal I = e.toLinearMap := by
  let eA : (A ⧸ I) ≃ₗ[A] AQM := by
    -- On `A` itself, the module quotient is just the quotient by the ideal-submodule `I`.
    refine Submodule.quotEquivOfEq (I : Submodule A A) ((I • (⊤ : Submodule A A)) : Submodule A A) ?_
    simp
  let eB : (B ⧸ IB) ≃ₗ[A] BQM :=
    ideal_quotient_equiv_module_quotient (A := A) (B := B) (I := I)
  let e : AQM ≃ₗ[A] BQM :=
    (eA.symm.trans (LinearEquiv.restrictScalars A hquot.toLinearEquiv)).trans eB
  -- Route correction: compare the two quotient maps only after transporting both sides to the
  -- same module-quotient model.
  refine ⟨e, ?_⟩
  apply DFunLike.ext
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective ((I • (⊤ : Submodule A A)) : Submodule A A) q
  have hsource : eA.symm (((I • (⊤ : Submodule A A)) : Submodule A A).mkQ x) = (Ideal.Quotient.mk I) x := by
    -- Reduce the source quotient class back to the textbook ring-quotient representative.
    apply eA.injective
    simpa [eA, Ideal.Quotient.mk_eq_mk] using
      (Submodule.quotEquivOfEq_mk
        (I : Submodule A A)
        ((I • (⊤ : Submodule A A)) : Submodule A A)
        (by simp) x)
  have htarget :
      eB
          ((Ideal.Quotient.mk IB) (algebraMap A B x)) =
        ((I • (⊤ : Submodule A B)) : Submodule A B).mkQ (algebraMap A B x) := by
    simpa using
      ideal_quotient_equiv_module_quotient_mk (A := A) (B := B) (I := I) (algebraMap A B x)
  -- Evaluate both maps on the quotient generator represented by `x : A`.
  calc
    (Algebra.linearMap A B).quotientMapByIdeal I
        (((I • (⊤ : Submodule A A)) : Submodule A A).mkQ x)
      = ((I • (⊤ : Submodule A B)) : Submodule A B).mkQ (algebraMap A B x) := by
          simpa using
            quotientMapByIdeal_apply_mkQ (A := A) (I := I) (Algebra.linearMap A B) x
    _ = eB
          ((Ideal.Quotient.mk IB) (algebraMap A B x)) := by
          simpa using htarget.symm
    _ = eB
          (hquot ((Ideal.Quotient.mk I) x)) := by
          congr 1
          simpa using (hquot.commutes ((Ideal.Quotient.mk I) x)).symm
    _ = eB ((LinearEquiv.restrictScalars A hquot.toLinearEquiv) ((Ideal.Quotient.mk I) x)) := by
          rfl
    _ = eB ((LinearEquiv.restrictScalars A hquot.toLinearEquiv)
          (eA.symm (((I • (⊤ : Submodule A A)) : Submodule A A).mkQ x))) := by
          rw [hsource]
    _ = e.toLinearMap (((I • (⊤ : Submodule A A)) : Submodule A A).mkQ x) := by
          rfl

/-- Helper for Lemma 15.10.3: the quotient algebra equivalence makes the induced quotient linear
map of `A → B` bijective. -/
private theorem bijective_quotient_algebraMap_of_quotient_equiv
    (hquot : (A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ IB)) :
    Function.Bijective ((Algebra.linearMap A B).quotientMapByIdeal I) := by
  obtain ⟨e, hmap⟩ :=
    quotient_algebraMap_eq_conjugate_of_quotient_equiv
      (A := A) (B := B) (I := I) hquot
  -- Once the quotient map is identified with a linear equivalence, bijectivity is immediate.
  simpa [hmap] using e.bijective

/-- Helper for Lemma 15.10.3: if the quotient of `A → B` is bijective modulo a Jacobson-radical
ideal and `B` is finite projective over `A`, then `A → B` is bijective. -/
private theorem bijective_algebraLinearMap_of_bijective_mod_jacobson
    [Module.Finite A B] [Module.Projective A B]
    (hI : I ≤ Ring.jacobson A)
    (hquot :
      Function.Bijective ((Algebra.linearMap A B).quotientMapByIdeal I)) :
    Function.Bijective (Algebra.linearMap A B) := by
  let e0 : AQM ≃ₗ[A] BQM :=
    LinearEquiv.ofBijective ((Algebra.linearMap A B).quotientMapByIdeal I) hquot
  -- Lift the inverse quotient map back to an `A`-linear map `B → A`.
  obtain ⟨ψ, hψ⟩ := exists_lift_with_prescribed_quotientMapByIdeal
    (A := A) (I := I) (Q := B) (M := A) e0.symm.toLinearMap
  have hφquot : (Algebra.linearMap A B).quotientMapByIdeal I = e0.toLinearMap := rfl
  have hcomp :
      (ψ.comp (Algebra.linearMap A B)).quotientMapByIdeal I = LinearMap.id ∧
        ((Algebra.linearMap A B).comp ψ).quotientMapByIdeal I = LinearMap.id :=
    quotientMapByIdeal_comp_eq_id_of_inverse
      (A := A) (I := I) e0 (Algebra.linearMap A B) ψ hφquot hψ
  have hsurj_comp_left : Function.Surjective (ψ.comp (Algebra.linearMap A B)) := by
    -- The left composite is the identity modulo `I`, so Nakayama upgrades it to surjectivity.
    apply surjective_of_quotientMap_surjective_of_le_ring_jacobson (I := I)
    · simpa [hcomp.1] using
        (show Function.Surjective (LinearMap.id : AQM →ₗ[A] AQM) from fun y ↦ ⟨y, rfl⟩)
    · exact hI
  have hsurj_comp_right : Function.Surjective ((Algebra.linearMap A B).comp ψ) := by
    -- The same argument applies to the right composite on `B`.
    apply surjective_of_quotientMap_surjective_of_le_ring_jacobson (I := I)
    · simpa [hcomp.2] using
        (show Function.Surjective (LinearMap.id : BQM →ₗ[A] BQM) from fun y ↦ ⟨y, rfl⟩)
    · exact hI
  have hinj_comp_left : Function.Injective (ψ.comp (Algebra.linearMap A B)) :=
    (OrzechProperty.bijective_of_surjective_endomorphism
      (ψ.comp (Algebra.linearMap A B)) hsurj_comp_left).1
  have hinjφ : Function.Injective (Algebra.linearMap A B) := by
    -- Injectivity of the left composite descends to injectivity of `A → B`.
    intro x y hxy
    apply hinj_comp_left
    simpa [LinearMap.comp_apply, hxy]
  have hsurjφ : Function.Surjective (Algebra.linearMap A B) := by
    -- Surjectivity of the right composite gives a preimage for every `y : B`.
    intro y
    obtain ⟨x, hx⟩ := hsurj_comp_right y
    refine ⟨ψ x, ?_⟩
    simpa [LinearMap.comp_apply] using hx
  exact ⟨hinjφ, hsurjφ⟩

/- Domain-style sampling:
- primary domain: flat integral finitely presented algebras over a Jacobson pair, quotient algebra
  equivalences, and finite projective comparison modulo the Jacobson radical;
- sampled owner declarations of the same kind:
  `Algebra.finite_iff_isIntegral_and_finiteType`,
  `Module.FinitePresentation.iff_of_finite_finitePresentation`,
  `Module.Flat.projective_of_finitePresentation`,
  `bijective_of_bijective_mod_jacobson_of_finite_projective`,
  `LinearMap.quotientMapByIdeal`;
- best owner abstraction: the source-facing quotient hypothesis should live on the canonical owner
  `(A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ I B)`, while the module-theoretic core owner remains
  `Module.Projective`;
- primitive data: the flat integral finitely presented `A`-algebra `B`, the ideal `I`, and the
  quotient algebra equivalence modulo `I`;
- derived API: finiteness of `B` over `A`, finite presentation of `B` as an `A`-module,
  projectivity of `B`, and finally bijectivity of `algebraMap A B`; the raw quotient-map
  bijectivity is only an internal bridge extracted from the quotient algebra equivalence.

Layer classification:
- `source-facing`: the present Jacobson-pair lemma for algebras;
- `core/canonical`: `Module.Projective`;
- `bridge/view`: the quotient linear equivalence induced by `hquot`, together with the chapter
  comparison lemma `bijective_of_bijective_mod_jacobson_of_finite_projective`.
-/

-- Proof sketch: the quotient algebra equivalence identifies `B ⧸ I B` with `A ⧸ I`, so
-- `B ⧸ I B` is projective over `A ⧸ I`. Since `B` is integral and finitely presented over `A`, it
-- is finite over `A`, hence finitely presented as an `A`-module via the canonical finite/finitely
-- presented change-of-scalars bridge. Flatness then upgrades `B` to a projective `A`-module, and
-- Lemma `15.3.5` applies to the linear map underlying `A → B` after identifying its quotient
-- `LinearMap.quotientMapByIdeal` with the given quotient algebra equivalence.
/-- Lemma 15.10.3: for a Zariski pair `(A, I)`, a flat integral finitely presented
`A`-algebra `B` whose reduction modulo the extended ideal `I.map (algebraMap A B)` is identified
with `A ⧸ I` by an `(A ⧸ I)`-algebra equivalence already satisfies that the canonical map
`A → B` is bijective. -/
theorem bijective_algebraMap_of_zariskiPair_of_flat_integral_finitePresentation
    (hI : I ≤ Ring.jacobson A)
    (hquot : (A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ IB)) :
    Function.Bijective (algebraMap A B) := by
  letI : Module.Finite A B :=
    (finite_projective_of_flat_integral_finitePresentation
      (A := A) (B := B)).1
  letI : Module.Projective A B :=
    (finite_projective_of_flat_integral_finitePresentation
      (A := A) (B := B)).2
  have hquotBij :
      Function.Bijective ((Algebra.linearMap A B).quotientMapByIdeal I) :=
    bijective_quotient_algebraMap_of_quotient_equiv
      (A := A) (B := B) (I := I) hquot
  -- Apply the finite-projective Jacobson-radical lifting argument to the underlying linear map.
  simpa using
    bijective_algebraLinearMap_of_bijective_mod_jacobson
      (A := A) (B := B) (I := I) hI hquotBij

end

end Algebra
