import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Jacobson.Ring
import StacksProject_2024.stacks_project.Chap10.Lemma_10_16_4
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {P' : Type w} [AddCommGroup P'] [Module R P']
variable [Module.Finite R P]
variable [Module.Finite R P'] [Module.Projective R P']
variable (I : Ideal R)

local notation "IP" => I • (⊤ : Submodule R P)
local notation "IP'" => I • (⊤ : Submodule R P')

/-- Helper for Lemma 15.3.5: a quotient map between reductions modulo `I` lifts along `mkQ`
from a projective source module. -/
private theorem exists_lift_with_prescribed_quotientMapByIdeal
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Projective R Q]
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R)
    (gbar : Q ⧸ (I • (⊤ : Submodule R Q)) →ₗ[R] M ⧸ (I • (⊤ : Submodule R M))) :
    ∃ g : Q →ₗ[R] M, g.quotientMapByIdeal I = gbar := by
  let gbarLift : Q →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
    gbar.comp (I • (⊤ : Submodule R Q)).mkQ
  -- Lift the quotient map through the canonical quotient projection.
  obtain ⟨g, hg⟩ :=
    Module.projective_lifting_property (I • (⊤ : Submodule R M)).mkQ gbarLift
      (Submodule.mkQ_surjective _)
  have hgsmul : I • (⊤ : Submodule R Q) ≤ Submodule.comap g (I • (⊤ : Submodule R M)) := by
    exact Submodule.smul_top_le_comap_smul_top I g
  have hcomp :
      ((I • (⊤ : Submodule R Q)).mapQ (I • (⊤ : Submodule R M)) g hgsmul).comp
          (I • (⊤ : Submodule R Q)).mkQ =
        (I • (⊤ : Submodule R M)).mkQ.comp g :=
    Submodule.mapQ_mkQ (I • (⊤ : Submodule R Q)) (I • (⊤ : Submodule R M)) g
  refine ⟨g, ?_⟩
  -- Evaluate on quotient representatives to identify the induced quotient map.
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R Q)) x
  simpa [LinearMap.quotientMapByIdeal, gbarLift] using
    (DFunLike.congr_fun hcomp x).trans (DFunLike.congr_fun hg x)

/-- Helper for Lemma 15.3.5: evaluating a quotient map on a quotient class matches quotienting
after applying the underlying linear map. -/
private theorem quotientMapByIdeal_apply_mkQ
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) (x : M) :
    f.quotientMapByIdeal I ((I • (⊤ : Submodule R M)).mkQ x) =
      (I • (⊤ : Submodule R N)).mkQ (f x) := by
  -- Expand the induced quotient map through the defining `mapQ_mkQ` square.
  simpa [LinearMap.quotientMapByIdeal] using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) f) x

/-- Helper for Lemma 15.3.5: quotient inverses force the lifted composites to be the identity
after reduction modulo `I`. -/
private theorem quotientMapByIdeal_comp_eq_id_of_inverse
    (e : (P ⧸ IP) ≃ₗ[R] (P' ⧸ IP'))
    (f : P →ₗ[R] P') (g : P' →ₗ[R] P)
    (hf : f.quotientMapByIdeal I = e.toLinearMap)
    (hg : g.quotientMapByIdeal I = e.symm.toLinearMap) :
    (g.comp f).quotientMapByIdeal I = LinearMap.id ∧
      (f.comp g).quotientMapByIdeal I = LinearMap.id := by
  constructor
  · -- Evaluate on quotient representatives and rewrite by the inverse identities.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective IP x
    calc
      (g.comp f).quotientMapByIdeal I ((I • (⊤ : Submodule R P)).mkQ x)
          = (I • (⊤ : Submodule R P)).mkQ (g (f x)) := by
              simp
      _ = g.quotientMapByIdeal I
            (f.quotientMapByIdeal I ((I • (⊤ : Submodule R P)).mkQ x)) := by
            simp
      _ = e.symm.toLinearMap (e.toLinearMap ((I • (⊤ : Submodule R P)).mkQ x)) := by
            rw [hf, hg]
      _ = (I • (⊤ : Submodule R P)).mkQ x := by simp
  · -- The same computation gives the identity on the target quotient.
    apply DFunLike.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective IP' x
    calc
      (f.comp g).quotientMapByIdeal I ((I • (⊤ : Submodule R P')).mkQ x)
          = (I • (⊤ : Submodule R P')).mkQ (f (g x)) := by
              simp
      _ = f.quotientMapByIdeal I
            (g.quotientMapByIdeal I ((I • (⊤ : Submodule R P')).mkQ x)) := by
            simp
      _ = e.toLinearMap (e.symm.toLinearMap ((I • (⊤ : Submodule R P')).mkQ x)) := by
            rw [hf, hg]
      _ = (I • (⊤ : Submodule R P')).mkQ x := by simp

/- Domain-style sampling:
- primary domain: finite projective modules over a commutative ring and comparison modulo an
  ideal in the Jacobson radical;
- sampled owner declarations of the same kind:
  `LinearMap.quotientMapByIdeal`,
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `Module.projective_lifting_property`,
  `OrzechProperty.bijective_of_surjective_endomorphism`,
  `LinearEquiv.ofBijective`;
- best owner abstraction: the reduced comparison map `φ.quotientMapByIdeal I`, together with the
  chapter-level Nakayama owner
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`; `LinearEquiv` is the canonical owner
  for a lifted bijection;
- primitive data: for the first theorem, the ideal `I`, the Jacobson-radical containment `hI`,
  the map `φ`, finiteness of `P`, and finiteness plus projectivity of `P'`; for the second
  theorem, add projectivity of `P` and the quotient `(R ⧸ I)`-linear equivalence `e`;
- derived API: bijectivity of `φ` and the lifted `LinearEquiv`.

Layer classification:
- `source-facing`: the Jacobson-radical lifting statements below;
- `core/canonical`: `LinearMap.quotientMapByIdeal`,
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `Module.projective_lifting_property`, `OrzechProperty.bijective_of_surjective_endomorphism`, and
  `LinearEquiv.ofBijective`;
- `bridge/view`: the quotient comparison equation for the lifted equivalence.
-/

-- Proof sketch: use projectivity of `P'` to lift an inverse to the induced quotient map, obtaining
-- `ψ : P' →ₗ[R] P`. The composites `ψ ∘ₗ φ` and `φ ∘ₗ ψ` are the identity modulo `I`, so the
-- chapter owner `surjective_of_quotientMap_surjective_of_le_ring_jacobson` makes them surjective;
-- the canonical finite-module endomorphism criterion
-- `OrzechProperty.bijective_of_surjective_endomorphism` then upgrades these surjective
-- endomorphisms to automorphisms, which forces `φ` to be bijective.
/-- Lemma 15.3.5: if `I` is contained in the Jacobson radical of `R`, `P` is finite, `P'` is
finite projective, and the induced map `P / IP → P' / IP'` is bijective, then `φ` is bijective. -/
theorem bijective_of_bijective_mod_jacobson_of_finite_projective
    (hI : I ≤ Ring.jacobson R) (φ : P →ₗ[R] P')
    (hφ : Function.Bijective (φ.quotientMapByIdeal I)) :
    Function.Bijective φ := by
  let e0 : (P ⧸ IP) ≃ₗ[R] (P' ⧸ IP') :=
    LinearEquiv.ofBijective (φ.quotientMapByIdeal I) hφ
  -- Lift the inverse quotient map back to an `R`-linear map `P' → P`.
  obtain ⟨ψ, hψ⟩ := exists_lift_with_prescribed_quotientMapByIdeal
    (R := R) (I := I) (Q := P') (M := P) e0.symm.toLinearMap
  have hφquot : φ.quotientMapByIdeal I = e0.toLinearMap := rfl
  have hcomp :
      (ψ.comp φ).quotientMapByIdeal I = LinearMap.id ∧
        (φ.comp ψ).quotientMapByIdeal I = LinearMap.id :=
    quotientMapByIdeal_comp_eq_id_of_inverse
      (R := R) (P := P) (P' := P') (I := I) e0 φ ψ hφquot hψ
  have hsurj_comp_left : Function.Surjective (ψ.comp φ) := by
    -- The left composite is the identity modulo `I`, so Nakayama upgrades it to surjectivity.
    apply surjective_of_quotientMap_surjective_of_le_ring_jacobson (I := I)
    · simpa [hcomp.1] using
        (show Function.Surjective (LinearMap.id : (P ⧸ IP) →ₗ[R] (P ⧸ IP)) from
          fun y ↦ ⟨y, rfl⟩)
    · exact hI
  have hsurj_comp_right : Function.Surjective (φ.comp ψ) := by
    -- The same argument applies to the right composite on `P'`.
    apply surjective_of_quotientMap_surjective_of_le_ring_jacobson (I := I)
    · simpa [hcomp.2] using
        (show Function.Surjective (LinearMap.id : (P' ⧸ IP') →ₗ[R] (P' ⧸ IP')) from
          fun y ↦ ⟨y, rfl⟩)
    · exact hI
  have hinj_comp_left : Function.Injective (ψ.comp φ) :=
    (OrzechProperty.bijective_of_surjective_endomorphism
      (ψ.comp φ) hsurj_comp_left).1
  have hinjφ : Function.Injective φ := by
    -- Injectivity of the left composite descends to injectivity of `φ`.
    intro x y hxy
    apply hinj_comp_left
    simpa [LinearMap.comp_apply, hxy]
  have hsurjφ : Function.Surjective φ := by
    -- Surjectivity of the right composite gives a preimage for every `y : P'`.
    intro y
    obtain ⟨x, hx⟩ := hsurj_comp_right y
    refine ⟨ψ x, ?_⟩
    simpa [LinearMap.comp_apply] using hx
  exact ⟨hinjφ, hsurjφ⟩

variable [Module.Projective R P]

-- Proof sketch: choose a linear lift `φ : P →ₗ[R] P'` of the underlying `R`-linear quotient
-- equivalence `e.restrictScalars R` using the projectivity owner
-- `Module.projective_lifting_property`, apply
-- `bijective_of_bijective_mod_jacobson_of_finite_projective` to obtain a bijective lift, and then
-- package that lift by the canonical owner `LinearEquiv.ofBijective`.
/-- An `(R ⧸ I)`-linear quotient equivalence between finite projective `R`-modules over a
Jacobson-radical ideal lifts to an `R`-linear equivalence. -/
theorem exists_lift_of_quotient_equiv_of_finite_projective
    (hI : I ≤ Ring.jacobson R) (e : (P ⧸ IP) ≃ₗ[R ⧸ I] (P' ⧸ IP')) :
    ∃ φ : P ≃ₗ[R] P',
      (φ : P →ₗ[R] P').quotientMapByIdeal I = e.restrictScalars R := by
  -- Lift the quotient equivalence viewed as an `R`-linear map.
  obtain ⟨φ, hφquot⟩ :=
    exists_lift_with_prescribed_quotientMapByIdeal (R := R) (I := I)
      (Q := P) (M := P') (e.restrictScalars R).toLinearMap
  have hbijφ : Function.Bijective φ := by
    -- The lifted map is bijective because its reduction is the given quotient equivalence.
    apply bijective_of_bijective_mod_jacobson_of_finite_projective (I := I) hI φ
    simpa [hφquot] using (e.restrictScalars R).bijective
  refine ⟨LinearEquiv.ofBijective φ hbijφ, ?_⟩
  -- Packaging the bijective lift as a linear equivalence does not change its underlying map.
  simpa using hφquot

end
