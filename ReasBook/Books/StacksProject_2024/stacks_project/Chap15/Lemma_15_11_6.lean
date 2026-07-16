import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Ring
import StacksProject_2024.stacks_project.Chap10.Lemma_10_19_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_11_1
import StacksProject_2024.stacks_project.Chap15.IdempotentLifting
import StacksProject_2024.stacks_project.Chap15.Lemma_15_9_10
import StacksProject_2024.stacks_project.Chap15.Lemma_15_10_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_10_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_11_5
import StacksProject_2024.stacks_project.Chap15.«15_11_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial TensorProduct
open Polynomial

universe u v

section

variable {A : Type u} [CommRing A]

namespace Ideal

/-
Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, expressed through the canonical owner
  `HenselianRing A I`, étale quotient sections, and quotient-induced maps on idempotents;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasFiniteAlgebraIdempotentLifting`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `RingHom.idempotentMap`,
  `Algebra.FormallyEtale.iff_comp_bijective`;
- best owner abstraction: the main owner remains `HenselianRing A I`; among the auxiliary clauses,
  the idempotent conditions are already canonically owned upstream in Chapter 15, while the
  étale-section and Gabber polynomial conditions are genuinely source-facing here and should be
  phrased through canonical comparison maps rather than parallel wrapper data;
- primitive data: the ideal `I`, the owner predicate `HenselianRing A I`, the canonical quotient
  composition map `τ ↦ (Ideal.Quotient.mkₐ A I).comp τ`, and the quotient polynomial identity
  defining Gabber's test polynomials;
- derived API: the TFAE packaging and the uniqueness of a root in `1 + I`.

Source/core/bridge triage:
- `source-facing`: `HasEtaleLiftProperty`, `IsGabberHenselPolynomial`,
  `SatisfiesGabberRootCriterion`, and the chapter TFAE theorem;
- `core/canonical`: `HenselianRing A I`, the Chapter 15 idempotent-lifting owners, and the
  canonical map `RingHom.idempotentMap`;
- `bridge/view`: the unique-root consequence extracted from Gabber's criterion.
-/

/-- The étale lifting formulation of the henselian pair condition modulo `I`. -/
def HasEtaleLiftProperty (I : Ideal A) : Prop :=
  ∀ ⦃A' : Type u⦄ [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
    Function.Surjective fun τ : A' →ₐ[A] A ↦ (Ideal.Quotient.mkₐ A I).comp τ

/-- A Gabber test polynomial for the henselian criterion modulo `I`. -/
def IsGabberHenselPolynomial (I : Ideal A) (f : A[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ f.Monic ∧
    f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)

/-- Gabber's Jacobson-plus-root criterion for the pair `(A, I)`. -/
def SatisfiesGabberRootCriterion (I : Ideal A) : Prop :=
  I ≤ Ring.jacobson A ∧
    ∀ ⦃f : A[X]⦄, I.IsGabberHenselPolynomial f → ∃ i : I, f.IsRoot (1 + ↑i)

end Ideal

namespace Ideal

/-- Helper for Lemma 15.11.6: the étale lifting property forces `I` into the Jacobson radical. -/
theorem le_ring_jacobson_of_hasEtaleLiftProperty (I : Ideal A)
    (hI : I.HasEtaleLiftProperty) :
    I ≤ Ring.jacobson A := by
  -- Proof comment: localizing away from an element congruent to `1` modulo `I` produces an
  -- étale algebra with a quotient section. Lifting that section back to `A` makes the inverted
  -- element a unit of `A`.
  rw [ideal_le_ring_jacobson_iff_isUnit_one_add]
  intro x hx
  let s : A := 1 + x
  have hs : Ideal.Quotient.mk I s = 1 := by
    -- Elements of `I` vanish in `A / I`, so `1 + x` reduces to `1`.
    dsimp [s]
    rw [map_add]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  let e :
      (A ⧸ I) ≃ₐ[A ⧸ I]
        ((Localization.Away s) ⧸ Ideal.map (algebraMap A (Localization.Away s)) I) :=
    Algebra.quotientAlgEquiv_localizationAway_of_eq_one_mod_ideal (A := A) I hs
  let σ : Localization.Away s →ₐ[A] A ⧸ I :=
    (e.symm.toAlgHom.restrictScalars A).comp
      ((Ideal.Quotient.mkₐ (Localization.Away s)
        (Ideal.map (algebraMap A (Localization.Away s)) I)).restrictScalars A)
  obtain ⟨τ, hτ⟩ := hI (A' := Localization.Away s) σ
  have hunitLoc : IsUnit (algebraMap A (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit s
  have hunit : IsUnit (τ (algebraMap A (Localization.Away s) s)) :=
    IsUnit.map τ.toRingHom hunitLoc
  simpa [s] using hunit

/-- Helper for Lemma 15.11.6: any `A`-algebra map carries the extension of `I` in its source into
the extension of `I` in its target. -/
private theorem ideal_map_le_comap_map
    {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (I : Ideal A) (f : B →ₐ[A] C) :
    Ideal.map (algebraMap A B) I ≤
      Ideal.comap f.toRingHom (Ideal.map (algebraMap A C) I) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  -- Proof comment: `f` is compatible with the `A`-algebra structures, so the image of a base
  -- element from `I` remains a base element from `I` after applying `f`.
  exact Ideal.mem_comap.mpr <| by
    simpa using (Ideal.mem_map_of_mem (algebraMap A C) hx : algebraMap A C x ∈ Ideal.map (algebraMap A C) I)

/-- Helper for Lemma 15.11.6: if `I` lies in the Jacobson radical of `A`, then `I B` lies in the
Jacobson radical of every integral `A`-algebra `B`. -/
private theorem ideal_map_le_ring_jacobson_of_isIntegral
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (I : Ideal A) (hI : I ≤ Ring.jacobson A) :
    Ideal.map (algebraMap A B) I ≤ Ring.jacobson B := by
  rw [ideal_le_ring_jacobson_iff_isUnit_one_add]
  intro y hy
  by_contra hUnit
  let J : Ideal B := Ideal.span ({1 + y} : Set B)
  have hJ_ne_top : J ≠ ⊤ := by
    intro hJ_top
    exact hUnit <| Ideal.span_singleton_eq_top.mp <| by simpa [J] using hJ_top
  obtain ⟨m, hmMax, hJm⟩ := Ideal.exists_le_maximal J hJ_ne_top
  let n : Ideal A := Ideal.comap (algebraMap A B) m
  let _ : n.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  have hI_to_m : Ideal.map (algebraMap A B) I ≤ m := by
    exact Ideal.map_le_iff_le_comap.mpr <| le_trans hI <|
      Ring.jacobson_le_of_isMaximal n
  have hy_mem : y ∈ m := hI_to_m hy
  have hone_add_mem : 1 + y ∈ m := hJm <| Ideal.subset_span (by simp)
  have hone : (1 : B) ∈ m := by
    -- Proof comment: if both `y` and `1 + y` lie in the maximal ideal, then their difference
    -- forces `1` into that maximal ideal.
    simpa using m.sub_mem hone_add_mem hy_mem
  exact hmMax.ne_top <| m.eq_top_of_isUnit_mem hone isUnit_one

/-- Helper for Lemma 15.11.6: étale section lifting implies idempotent lifting for integral
`A`-algebras. -/
theorem integral_idempotent_lifting_of_hasEtaleLiftProperty (I : Ideal A)
    (hI : I.HasEtaleLiftProperty) :
    Ideal.HasIntegralAlgebraIdempotentLifting (A := A) I := by
  intro B _ _ hIntB
  have hJacA : I ≤ Ring.jacobson A :=
    le_ring_jacobson_of_hasEtaleLiftProperty (A := A) I hI
  have hJacB :
      Ideal.map (algebraMap A B) I ≤ Ring.jacobson B :=
    ideal_map_le_ring_jacobson_of_isIntegral (A := A) I hJacA
  refine ⟨?_, ?_⟩
  · -- Proof comment: after transporting the Jacobson-radical containment to `B`, injectivity is
    -- exactly Lemma `15.10.2` for the quotient `B → B / I B`.
    exact quotientMk_injective_on_idempotents_of_le_jacobson
      (A := B) (I := Ideal.map (algebraMap A B) I) hJacB
  · intro ebar
    -- Proof comment: first lift the residue idempotent after an étale base change as in
    -- Lemma `15.9.10`.
    obtain ⟨A', _, _, _, eIso, e', he', hquot⟩ :=
      Algebra.exists_etale_baseChange_idempotent_lift_of_isIdempotentElem_mod_map
        (A := A) (B := B) I ebar.1 ebar.2
    let I' : Ideal A' := Ideal.map (algebraMap A A') I
    let σ : A' →ₐ[A] A ⧸ I :=
      (eIso.symm.toAlgHom.restrictScalars A).comp ((Ideal.Quotient.mkₐ A' I').restrictScalars A)
    -- Proof comment: the étale lifting hypothesis gives a section `A' → A` of the quotient map.
    obtain ⟨τ, _hτ⟩ := hI (A' := A') σ
    let μA' : A' →ₐ[A] B := (Algebra.ofId A B).comp τ
    let μ : B ⊗[A] A' →ₐ[A] B := Algebra.TensorProduct.productMap (AlgHom.id A B) μA'
    let qB' :
        B ⧸ Ideal.map (algebraMap A B) I →ₐ[A]
          (B ⊗[A] A') ⧸ Ideal.map (algebraMap A (B ⊗[A] A')) I :=
      Ideal.quotientMapₐ _ (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A')
        (ideal_map_le_comap_map (A := A) I (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A'))
    let qμ :
        (B ⊗[A] A') ⧸ Ideal.map (algebraMap A (B ⊗[A] A')) I →ₐ[A]
          B ⧸ Ideal.map (algebraMap A B) I :=
      Ideal.quotientMapₐ _ μ (ideal_map_le_comap_map (A := A) I μ)
    have hquot' : qB' ebar.1 = Ideal.Quotient.mk _ e' := by
      -- Proof comment: this is exactly the residue compatibility supplied by Lemma `15.9.10`,
      -- rewritten with the local name `qB'`.
      simpa [qB'] using hquot
    refine ⟨⟨μ e', he'.map μ⟩, ?_⟩
    apply Subtype.ext
    -- Proof comment: compose the lifted quotient identity with the tensor contraction `qμ`; on
    -- classes from `B`, this contraction is the identity because `μ ∘ includeLeft = id_B`.
    calc
      Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) (μ e')
          = qμ (Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I) e') := by
              rfl
      _ = qμ (qB' ebar.1) := by rw [hquot']
      _ = ebar.1 := by
            obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ebar.1
            rw [← hb]
            simp [qμ, qB', μ, μA', Algebra.TensorProduct.productMap_apply_tmul,
              Algebra.TensorProduct.includeLeft_apply]

/-- Helper for Lemma 15.11.6: a henselian pair satisfies Gabber's Jacobson-plus-root criterion. -/
theorem satisfiesGabberRootCriterion_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    I.SatisfiesGabberRootCriterion := by
  refine ⟨Ideal.le_ring_jacobson_of_henselianRing (A := A) (I := I), ?_⟩
  intro f hf
  rcases hf with ⟨n, hn, hmonic, hmap⟩
  have hEval : f.eval (1 : A) ∈ I := by
    -- Proof comment: the model Gabber polynomial `X^n * (X - 1)` vanishes at `1` modulo `I`.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [Polynomial.eval_mul, hn.ne'] using
      congrArg (fun p : (A ⧸ I)[X] ↦ p.eval (1 : A ⧸ I)) hmap
  let i0 : I := ⟨0, Ideal.zero_mem I⟩
  have hderiv :
      IsUnit ((Ideal.Quotient.mk I) (f.derivative.eval (1 : A))) := by
    -- Proof comment: the derivative of a Gabber polynomial is `1` modulo `I` at `1`.
    have hderivEq :
        (Ideal.Quotient.mk I) (f.derivative.eval (1 : A)) = 1 :=
      calc
        (Ideal.Quotient.mk I) (f.derivative.eval (1 : A))
            = (Polynomial.map (Ideal.Quotient.mk I) f.derivative).eval (1 : A ⧸ I) := by
                rw [← Polynomial.eval₂_eq_eval_map]
                exact (Polynomial.eval₂_at_apply (p := f.derivative) (f := Ideal.Quotient.mk I)
                  (1 : A)).symm
        _ = ((Polynomial.map (Ideal.Quotient.mk I) f).derivative).eval (1 : A ⧸ I) := by
              rw [Polynomial.derivative_map]
        _ = (((X ^ n) * (X - 1 : (A ⧸ I)[X])).derivative).eval (1 : A ⧸ I) := by
              rw [hmap]
        _ = 1 := by
              simp
    rw [hderivEq]
    exact isUnit_one
  obtain ⟨a, ha_root, ha_mem⟩ := HenselianRing.is_henselian (I := I) f hmonic 1 hEval hderiv
  refine ⟨⟨a - 1, ha_mem⟩, ?_⟩
  simpa [Polynomial.IsRoot, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ha_root

/-- Helper for Lemma 15.11.6: reduction modulo the unit ideal collapses the two basic
idempotents in any nontrivial ring, so the induced idempotent map cannot be injective. -/
private theorem not_injective_idempotentMap_quotient_top
    {R : Type*} [CommRing R] [Nontrivial R] :
    ¬ Function.Injective (Ideal.Quotient.mk (⊤ : Ideal R)).idempotentMap := by
  intro hInjective
  let e₀ : {x : R // IsIdempotentElem x} := ⟨0, by simp [IsIdempotentElem]⟩
  let e₁ : {x : R // IsIdempotentElem x} := ⟨1, by simp [IsIdempotentElem]⟩
  have hsame :
      (Ideal.Quotient.mk (⊤ : Ideal R)).idempotentMap e₀ =
        (Ideal.Quotient.mk (⊤ : Ideal R)).idempotentMap e₁ := by
    -- Proof comment: the quotient by `⊤` is a subsingleton, so every two idempotents agree.
    apply Subsingleton.elim
  have hEq : e₀ = e₁ := hInjective hsame
  have h01 : (0 : R) = 1 := congrArg Subtype.val hEq
  exact zero_ne_one h01

/-- Helper for Lemma 15.11.6: if an ideal is the unit ideal, then its quotient idempotent map is
noninjective. -/
private theorem not_injective_idempotentMap_of_eq_top
    {R : Type*} [CommRing R] [Nontrivial R] (J : Ideal R) (hJ : J = ⊤) :
    ¬ Function.Injective (Ideal.Quotient.mk J).idempotentMap := by
  -- Proof comment: once `J = ⊤`, the quotient ring is a subsingleton, so the two basic
  -- idempotents have the same image.
  intro hInjective
  let e₀ : {x : R // IsIdempotentElem x} := ⟨0, by simp [IsIdempotentElem]⟩
  let e₁ : {x : R // IsIdempotentElem x} := ⟨1, by simp [IsIdempotentElem]⟩
  have hSub : Subsingleton (R ⧸ J) := by
    rw [hJ]
    infer_instance
  have hsame :
      (Ideal.Quotient.mk J).idempotentMap e₀ =
        (Ideal.Quotient.mk J).idempotentMap e₁ := by
    apply Subtype.ext
    exact hSub.elim _ _
  have hEq : e₀ = e₁ := hInjective hsame
  have h01 : (0 : R) = 1 := congrArg Subtype.val hEq
  exact zero_ne_one h01

/-- Helper for Lemma 15.11.6: finite idempotent lifting forces `I` into the Jacobson radical. -/
theorem finite_idempotent_lifting_le_ring_jacobson (I : Ideal A)
    (hI : Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I) :
    I ≤ Ring.jacobson A := by
  rw [ideal_le_ring_jacobson_iff_isUnit_one_add]
  intro x hx
  by_contra hunit
  let J : Ideal A := Ideal.span ({1 + x} : Set A)
  have hJ_ne_top : J ≠ ⊤ := by
    intro hJ_top
    exact hunit <| (Ideal.span_singleton_eq_top.mp <| by simpa [J] using hJ_top)
  obtain ⟨m, hmMax, hJm⟩ := Ideal.exists_le_maximal J hJ_ne_top
  have h_one_add_mem : 1 + x ∈ m := hJm (Ideal.subset_span (by simp))
  have hx_not_mem : x ∉ m := by
    intro hxm
    have hone : (1 : A) ∈ m := by
      -- Proof comment: if both `x` and `1 + x` lie in `m`, then their difference forces `1 ∈ m`.
      simpa using m.sub_mem h_one_add_mem hxm
    exact hmMax.ne_top (m.eq_top_of_isUnit_mem hone isUnit_one)
  let B := A ⧸ m
  letI : m.IsMaximal := hmMax
  letI : Field B := Ideal.Quotient.field m
  have hJB_top : Ideal.map (algebraMap A B) I = ⊤ := by
    have hx_mem : algebraMap A B x ∈ Ideal.map (algebraMap A B) I :=
      Ideal.mem_map_of_mem (algebraMap A B) hx
    have hx_unit : IsUnit ((algebraMap A B x : B)) := by
      -- Proof comment: modulo the maximal ideal `m`, the class of `x` is nonzero, hence a unit.
      refine (isUnit_iff_ne_zero).mpr ?_
      intro hx_zero
      exact hx_not_mem (Ideal.Quotient.eq_zero_iff_mem.mp hx_zero)
    exact (Ideal.map (algebraMap A B) I).eq_top_of_isUnit_mem hx_mem hx_unit
  have hBij :
      Function.Bijective
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)).idempotentMap := hI (B := B)
  have hNotInj :
      ¬ Function.Injective
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)).idempotentMap := by
    -- Proof comment: once `I` maps to `⊤` in the residue field, the quotient idempotent map
    -- becomes the noninjective collapse modulo the unit ideal.
    exact not_injective_idempotentMap_of_eq_top
      (R := B) (Ideal.map (algebraMap A B) I) hJB_top
  exact hNotInj hBij.1

/-- Helper for Lemma 15.11.6: if `p(a)` is a unit, then the residue linear factor `X - C a`
is coprime to `p`. -/
private theorem isCoprime_X_sub_C_of_isUnit_eval
    {R : Type u} [CommRing R] (a : R) (p : R[X]) (hp : IsUnit (p.eval a)) :
    IsCoprime (X - C a) p := by
  have hroot : (p - C (p.eval a)).IsRoot a := by
    -- Proof comment: subtracting the constant value `p(a)` forces the adjusted polynomial to
    -- vanish at `a`.
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub]
    simp
  obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
  rcases hp with ⟨u, hu⟩
  refine ⟨-q * C (((u⁻¹ : Units R) : R)), C (((u⁻¹ : Units R) : R)), ?_⟩
  -- Proof comment: the Euclidean remainder identity writes a unit-valued linear combination of
  -- `X - C a` and `p`, which normalizes to `1`.
  calc
    (-q * C (((u⁻¹ : Units R) : R))) * (X - C a) + C (((u⁻¹ : Units R) : R)) * p =
        C (((u⁻¹ : Units R) : R)) * (p - q * (X - C a)) := by
      ring
    _ = C (((u⁻¹ : Units R) : R)) * C (p.eval a) := by
      rw [show p - q * (X - C a) = C (p.eval a) by
        calc
          p - q * (X - C a) = p - ((X - C a) * q) := by rw [mul_comm]
          _ = p - (p - C (p.eval a)) := by rw [hq]
          _ = C (p.eval a) := by ring]
    _ = 1 := by
      rw [← hu]
      rw [← Polynomial.C_mul]
      simp

/-- Helper for Lemma 15.11.6: once `a` is a root, the cofactor obtained by dividing by
`X - C a` evaluates to the derivative at `a`. -/
private theorem divByMonic_X_sub_C_eval_eq_derivative_eval
    {R : Type u} [CommRing R] (p : R[X]) {a : R} (ha : p.IsRoot a) :
    (p /ₘ (X - C a)).eval a = p.derivative.eval a := by
  let q : R[X] := p /ₘ (X - C a)
  have hfactor : (X - C a) * q = p := by
    -- Proof comment: a root exactly says that `X - C a` divides `p`.
    simpa [q] using (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha)
  have hderiv :=
    congrArg (fun r : R[X] => r.derivative.eval a) hfactor
  -- Proof comment: differentiating the linear factorization kills the `X - C a` term at `a`,
  -- leaving only the cofactor value.
  simpa [q, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul] using hderiv

/-- Helper for Lemma 15.11.6: modulo `I`, a simple residue root at `a₀` produces the canonical
coprime factorization by `X - C ā₀`. -/
private theorem exists_coprime_residue_factorization_of_simple_root_mod_ideal
    (I : Ideal A) {f : A[X]} (hf : f.Monic) (a₀ : A) (ha₀ : f.eval a₀ ∈ I)
    (hderiv : IsUnit ((Ideal.Quotient.mk I) (f.derivative.eval a₀))) :
    ∃ hbar : (A ⧸ I)[X],
      f.map (Ideal.Quotient.mk I) = (X - C ((Ideal.Quotient.mk I) a₀)) * hbar ∧
      hbar.Monic ∧
      IsCoprime (X - C ((Ideal.Quotient.mk I) a₀)) hbar := by
  let abar : A ⧸ I := Ideal.Quotient.mk I a₀
  let fbar : (A ⧸ I)[X] := f.map (Ideal.Quotient.mk I)
  let hbar : (A ⧸ I)[X] := fbar /ₘ (X - C abar)
  have hrootbar : fbar.IsRoot abar := by
    -- Proof comment: reducing the evaluation condition `f(a₀) ∈ I` gives the residue root
    -- `ā₀` of `f̄`.
    exact (Polynomial.IsRoot.def).2 <| by
      simpa [fbar, abar, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_at_apply] using
        (Ideal.Quotient.eq_zero_iff_mem.mpr ha₀ :
          Ideal.Quotient.mk I (Polynomial.eval a₀ f) = 0)
  have hfactorbar : fbar = (X - C abar) * hbar := by
    -- Proof comment: the residue root forces the standard linear factorization by `X - C ā₀`.
    simpa [fbar, abar, hbar] using
      (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hrootbar).symm
  have hhbar : hbar.Monic := by
    -- Proof comment: both `f̄` and the residue linear factor are monic, so the quotient
    -- cofactor remains monic.
    have hfbar : fbar.Monic := by
      simpa [fbar] using hf.map (Ideal.Quotient.mk I)
    rw [hfactorbar] at hfbar
    exact (monic_X_sub_C abar).of_mul_monic_left hfbar
  have hderivbar : IsUnit (hbar.eval abar) := by
    -- Proof comment: evaluating the cofactor at the root recovers the derivative value modulo
    -- `I`, so the simple-root hypothesis turns into a unit evaluation.
    rw [show hbar.eval abar = fbar.derivative.eval abar by
          simpa [fbar, abar, hbar] using
            divByMonic_X_sub_C_eval_eq_derivative_eval fbar hrootbar]
    have hmap_deriv :
        fbar.derivative.eval abar =
          (Ideal.Quotient.mk I) (f.derivative.eval a₀) := by
      simpa [fbar, abar, Polynomial.derivative_map, Polynomial.eval₂_eq_eval_map,
        Polynomial.eval₂_at_apply]
    rw [hmap_deriv]
    exact hderiv
  have hcoprime : IsCoprime (X - C abar) hbar := by
    -- Proof comment: the cofactor value is a unit at `ā₀`, so the residue linear factor is
    -- coprime to the cofactor.
    simpa [abar] using isCoprime_X_sub_C_of_isUnit_eval abar hbar hderivbar
  exact ⟨hbar, hfactorbar, hhbar, hcoprime⟩

/-- Helper for Lemma 15.11.6: the kernel of evaluation at `a` on `R[X]` is the principal ideal
generated by `X - C a`. -/
private theorem ker_evalRingHom_eq_span_X_sub_C
    {R : Type u} [CommRing R] (a : R) :
    RingHom.ker (Polynomial.evalRingHom a) =
      Ideal.span ({X - C a} : Set R[X]) := by
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).2 <| (Polynomial.IsRoot.def).2 hp
    refine ⟨q, ?_⟩
    simpa [mul_comm] using hq
  · rintro ⟨q, rfl⟩
    simp

/-- Helper for Lemma 15.11.6: quotienting `R[X]` by the linear factor `X - C a` identifies the
resulting `R`-algebra with `R` via evaluation at `a`. -/
private noncomputable def quotient_span_X_sub_C_algEquiv
    {R : Type u} [CommRing R] (a : R) :
    (R[X] ⧸ Ideal.span ({X - C a} : Set R[X])) ≃ₐ[R] R := by
  let τ : R[X] →ₐ[R] R := Polynomial.aeval a
  have hker :
      RingHom.ker τ.toRingHom =
        Ideal.span ({X - C a} : Set R[X]) :=
    ker_evalRingHom_eq_span_X_sub_C a
  have hsurj : Function.Surjective τ := by
    intro r
    refine ⟨C r, ?_⟩
    simp [τ]
  -- Proof comment: rewrite the quotient by the explicit kernel equality, then apply the standard
  -- quotient-by-kernel equivalence for the surjective evaluation map.
  exact
    (Ideal.quotientEquivAlgOfEq R hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)

/-- Helper for Lemma 15.11.6: under the quotient-by-`X - C a` equivalence, the class of `X`
evaluates to `a`. -/
private theorem quotient_span_X_sub_C_algEquiv_apply_mk_X
    {R : Type u} [CommRing R] (a : R) :
    quotient_span_X_sub_C_algEquiv a
      (Ideal.Quotient.mk (Ideal.span ({X - C a} : Set R[X])) X) = a := by
  let τ : R[X] →ₐ[R] R := Polynomial.aeval a
  have hker :
      RingHom.ker τ.toRingHom =
        Ideal.span ({X - C a} : Set R[X]) :=
    ker_evalRingHom_eq_span_X_sub_C a
  have hsurj : Function.Surjective τ := by
    intro r
    refine ⟨C r, ?_⟩
    simp [τ]
  -- Proof comment: both quotient equivalences are evaluated on the class of `X`, so the result is
  -- the ordinary polynomial evaluation `X ↦ a`.
  calc
    quotient_span_X_sub_C_algEquiv a
        (Ideal.Quotient.mk (Ideal.span ({X - C a} : Set R[X])) X)
      = (Ideal.quotientKerAlgEquivOfSurjective hsurj)
          ((Ideal.quotientEquivAlgOfEq R hker.symm)
            (Ideal.Quotient.mk (Ideal.span ({X - C a} : Set R[X])) X)) := by
              rfl
    _ = (Ideal.quotientKerAlgEquivOfSurjective hsurj)
          (Ideal.Quotient.mk (RingHom.ker τ.toRingHom) X) := by
            rw [Ideal.quotientEquivAlgOfEq_mk]
    _ = τ X := Ideal.quotientKerAlgEquivOfSurjective_mk hsurj X
    _ = a := by
          simp [τ]

/-- Helper for Lemma 15.11.6: an algebra product equivalence sending an idempotent `e` to the
distinguished first-factor idempotent identifies the quotient by `1 - e` with the first factor,
and records the first coordinate of a chosen element `x`. -/
private theorem factorwise_split_of_product_equiv_and_first_coordinate
    {R : Type*} {Q : Type*} {C₁ : Type*} {C₂ : Type*}
    [CommRing R] [CommRing Q] [CommRing C₁] [CommRing C₂]
    [Algebra R Q] [Algebra R C₁] [Algebra R C₂]
    {e x : Q} (he : IsIdempotentElem e)
    (φ : Q ≃ₐ[R] (C₁ × C₂))
    (heφ : φ e = ((1 : C₁), (0 : C₂)))
    {c : C₁} (hxφ : φ x = (c, (0 : C₂)))
    (hsurj : Function.Surjective (algebraMap R C₁)) :
    ∃ firstFactor : (Q ⧸ Ideal.span ({1 - e} : Set Q)) ≃ₐ[R] C₁,
      firstFactor (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set Q)) x) = c ∧
        Function.Surjective (algebraMap R (Q ⧸ Ideal.span ({1 - e} : Set Q))) := by
  let π₁ : Q →ₐ[R] C₁ := (AlgHom.fst R C₁ C₂).comp φ.toAlgHom
  have h_one_sub_e : φ (1 - e) = ((0 : C₁), (1 : C₂)) := by
    -- Proof comment: the complementary idempotent cuts out the complementary product factor.
    calc
      φ (1 - e) = 1 - φ e := by simp
      _ = ((0 : C₁), (1 : C₂)) := by
            rw [heφ]
            ext <;> simp
  have hπ₁surj : Function.Surjective π₁ := by
    -- Proof comment: any first coordinate is represented by taking second coordinate `0`.
    intro y
    rcases φ.surjective (y, 0) with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    change (φ q).1 = y
    simpa using congrArg Prod.fst hq
  have hπ₁ker : RingHom.ker π₁.toRingHom = Ideal.span ({1 - e} : Set Q) := by
    -- Proof comment: transport the obvious kernel of the first projection back across `φ`.
    ext q
    constructor
    · intro hq
      have hqfst : (φ q).1 = 0 := by
        simpa [π₁] using hq
      rw [Ideal.mem_span_singleton]
      refine ⟨φ.symm ((1 : C₁), (φ q).2), ?_⟩
      symm
      apply φ.injective
      calc
        φ ((1 - e) * φ.symm ((1 : C₁), (φ q).2))
            = ((1 : C₁), (φ q).2) * ((0 : C₁), (1 : C₂)) := by
                simp [h_one_sub_e]
        _ = (0, (φ q).2) := by
              ext <;> simp
        _ = φ q := by
              ext <;> simp [hqfst]
    · intro hq
      rw [Ideal.mem_span_singleton] at hq
      rcases hq with ⟨y, rfl⟩
      rw [RingHom.mem_ker]
      change (φ ((1 - e) * y)).1 = 0
      rw [map_mul]
      simp [h_one_sub_e]
  let firstFactor : (Q ⧸ Ideal.span ({1 - e} : Set Q)) ≃ₐ[R] C₁ :=
    (Ideal.quotientEquivAlgOfEq R hπ₁ker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hπ₁surj)
  refine ⟨firstFactor, ?_, ?_⟩
  · -- Proof comment: the quotient by `1 - e` remembers exactly the first coordinate of `x`.
    change π₁ x = c
    change (φ x).1 = c
    simpa [hxφ]
  · -- Proof comment: surjectivity of `R → C₁` transports back across the first-factor quotient.
    intro q
    let c₀ : C₁ := firstFactor q
    rcases hsurj c₀ with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    apply firstFactor.injective
    simpa [c₀] using hr

/-- Helper for Lemma 15.11.6: after lifting an idempotent from `A / I`, the corresponding branch
double quotient is canonically the same as the double quotient cut out by the residue idempotent. -/
private theorem component_residue_ringEquiv_after_idempotent_split
    (I : Ideal A) {e : A} {ebar : A ⧸ I}
    (hquot_e : (Ideal.Quotient.mk I) e = ebar) :
    ∃ φ₀ :
        ((A ⧸ Ideal.span ({e} : Set A)) ⧸
            Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I) ≃+*
          ((A ⧸ I) ⧸ Ideal.span ({ebar} : Set (A ⧸ I))),
      ∃ φ₁ :
          ((A ⧸ Ideal.span ({1 - e} : Set A)) ⧸
              Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I) ≃+*
            ((A ⧸ I) ⧸ Ideal.span ({1 - ebar} : Set (A ⧸ I))),
        (∀ a : A,
            φ₀
                ((Ideal.Quotient.mk
                    (Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I))
                  ((Ideal.Quotient.mk (Ideal.span ({e} : Set A))) a)) =
              (Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) ∧
          (∀ a : A,
            φ₁
                ((Ideal.Quotient.mk
                    (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I))
                  ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) a)) =
              (Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) := by
  have hmap_e :
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({e} : Set A)) =
        Ideal.span ({ebar} : Set (A ⧸ I)) := by
    -- Proof comment: the quotient image of the principal idempotent ideal is the principal ideal
    -- of the residue idempotent.
    calc
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({e} : Set A))
          = Ideal.span ((Ideal.Quotient.mk I) '' ({e} : Set A)) := by
              rw [Ideal.map_span]
      _ = Ideal.span ({ebar} : Set (A ⧸ I)) := by
            congr
            ext x
            simp [hquot_e]
  have hmap_one_sub :
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({1 - e} : Set A)) =
        Ideal.span ({1 - ebar} : Set (A ⧸ I)) := by
    -- Proof comment: the complementary idempotent ideal behaves identically under quotient.
    calc
      Ideal.map (Ideal.Quotient.mk I) (Ideal.span ({1 - e} : Set A))
          = Ideal.span ((Ideal.Quotient.mk I) '' ({1 - e} : Set A)) := by
              rw [Ideal.map_span]
      _ = Ideal.span ({1 - ebar} : Set (A ⧸ I)) := by
            congr
            ext x
            simp [hquot_e]
  let leftEquiv₀ :
      ((A ⧸ Ideal.span ({e} : Set A)) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I) ≃+*
        (A ⧸ (Ideal.span ({e} : Set A) ⊔ I)) := by
    simpa [Ideal.add_eq_sup] using
      DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({e} : Set A)) I
  let rightEquiv₀ :
      ((A ⧸ I) ⧸ Ideal.span ({ebar} : Set (A ⧸ I))) ≃+*
        (A ⧸ (Ideal.span ({e} : Set A) ⊔ I)) :=
    (((Ideal.quotEquivOfEq hmap_e).symm.trans <|
        by
          simpa [Ideal.add_eq_sup] using
            DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({e} : Set A))).trans
      (Ideal.quotEquivOfEq (sup_comm I (Ideal.span ({e} : Set A)) :
        I ⊔ Ideal.span ({e} : Set A) =
        Ideal.span ({e} : Set A) ⊔ I)))
  let φ₀ := leftEquiv₀.trans rightEquiv₀.symm
  let leftEquiv₁ :
      ((A ⧸ Ideal.span ({1 - e} : Set A)) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I) ≃+*
        (A ⧸ (Ideal.span ({1 - e} : Set A) ⊔ I)) := by
    simpa [Ideal.add_eq_sup] using
      DoubleQuot.quotQuotEquivQuotSup (Ideal.span ({1 - e} : Set A)) I
  let rightEquiv₁ :
      ((A ⧸ I) ⧸ Ideal.span ({1 - ebar} : Set (A ⧸ I))) ≃+*
        (A ⧸ (Ideal.span ({1 - e} : Set A) ⊔ I)) :=
    (((Ideal.quotEquivOfEq hmap_one_sub).symm.trans <|
        by
          simpa [Ideal.add_eq_sup] using
            DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({1 - e} : Set A))).trans
      (Ideal.quotEquivOfEq (sup_comm I (Ideal.span ({1 - e} : Set A)) :
        I ⊔ Ideal.span ({1 - e} : Set A) =
        Ideal.span ({1 - e} : Set A) ⊔ I)))
  let φ₁ := leftEquiv₁.trans rightEquiv₁.symm
  refine ⟨φ₀, φ₁, ?_⟩
  constructor
  · intro a
    have hleft :
        leftEquiv₀
            ((Ideal.Quotient.mk
                (Ideal.map (Ideal.Quotient.mk (Ideal.span ({e} : Set A))) I))
              ((Ideal.Quotient.mk (Ideal.span ({e} : Set A))) a)) =
          (Ideal.Quotient.mk (Ideal.span ({e} : Set A) ⊔ I)) a := by
      -- Proof comment: the left iterated quotient is the quotient by the supremum ideal.
      simpa [leftEquiv₀, DoubleQuot.quotQuotMk] using
        (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk
          (I := Ideal.span ({e} : Set A)) (J := I) a)
    have hright :
        rightEquiv₀
            ((Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
              ((Ideal.Quotient.mk I) a)) =
          (Ideal.Quotient.mk (Ideal.span ({e} : Set A) ⊔ I)) a := by
      -- Proof comment: the right branch first rewrites the ideal, then collapses to the same
      -- supremum quotient.
      have hrewrite :
          (Ideal.quotEquivOfEq hmap_e).symm
              ((Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) =
            DoubleQuot.quotQuotMk I (Ideal.span ({e} : Set A)) a := by
        simp [Ideal.quotEquivOfEq_symm, DoubleQuot.quotQuotMk]
      calc
        rightEquiv₀
            ((Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
              ((Ideal.Quotient.mk I) a))
            = (Ideal.quotEquivOfEq
                (sup_comm I (Ideal.span ({e} : Set A)) :
                  I ⊔ Ideal.span ({e} : Set A) =
                    Ideal.span ({e} : Set A) ⊔ I))
                ((DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({e} : Set A)))
                  ((Ideal.quotEquivOfEq hmap_e).symm
                    ((Ideal.Quotient.mk (Ideal.span ({ebar} : Set (A ⧸ I))))
                      ((Ideal.Quotient.mk I) a)))) := by
                  rfl
        _ = (Ideal.quotEquivOfEq
              (sup_comm I (Ideal.span ({e} : Set A)) :
                I ⊔ Ideal.span ({e} : Set A) =
                  Ideal.span ({e} : Set A) ⊔ I))
              ((DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({e} : Set A)))
                (DoubleQuot.quotQuotMk I (Ideal.span ({e} : Set A)) a)) := by
                  rw [hrewrite]
        _ = (Ideal.Quotient.mk (Ideal.span ({e} : Set A) ⊔ I)) a := by
              simp
    apply rightEquiv₀.injective
    simpa [φ₀, RingEquiv.trans_apply] using hleft.trans hright.symm
  · intro a
    have hleft :
        leftEquiv₁
            ((Ideal.Quotient.mk
                (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) I))
              ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A))) a)) =
          (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A) ⊔ I)) a := by
      -- Proof comment: the complementary branch has the same double-quotient description.
      simpa [leftEquiv₁, DoubleQuot.quotQuotMk] using
        (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk
          (I := Ideal.span ({1 - e} : Set A)) (J := I) a)
    have hright :
        rightEquiv₁
            ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
              ((Ideal.Quotient.mk I) a)) =
          (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A) ⊔ I)) a := by
      -- Proof comment: again rewrite the quotient-side ideal and pass to the common quotient.
      have hrewrite :
          (Ideal.quotEquivOfEq hmap_one_sub).symm
              ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
                ((Ideal.Quotient.mk I) a)) =
            DoubleQuot.quotQuotMk I (Ideal.span ({1 - e} : Set A)) a := by
        simp [Ideal.quotEquivOfEq_symm, DoubleQuot.quotQuotMk]
      calc
        rightEquiv₁
            ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
              ((Ideal.Quotient.mk I) a))
            = (Ideal.quotEquivOfEq
                (sup_comm I (Ideal.span ({1 - e} : Set A)) :
                  I ⊔ Ideal.span ({1 - e} : Set A) =
                    Ideal.span ({1 - e} : Set A) ⊔ I))
                ((DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({1 - e} : Set A)))
                  ((Ideal.quotEquivOfEq hmap_one_sub).symm
                    ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (A ⧸ I))))
                      ((Ideal.Quotient.mk I) a)))) := by
                  rfl
        _ = (Ideal.quotEquivOfEq
              (sup_comm I (Ideal.span ({1 - e} : Set A)) :
                I ⊔ Ideal.span ({1 - e} : Set A) =
                  Ideal.span ({1 - e} : Set A) ⊔ I))
              ((DoubleQuot.quotQuotEquivQuotSup I (Ideal.span ({1 - e} : Set A)))
                (DoubleQuot.quotQuotMk I (Ideal.span ({1 - e} : Set A)) a)) := by
                  rw [hrewrite]
        _ = (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set A) ⊔ I)) a := by
              simp
    apply rightEquiv₁.injective
    simpa [φ₁, RingEquiv.trans_apply] using hleft.trans hright.symm

/-- Helper for Lemma 15.11.6: once the closed fiber of a finite `A`-algebra `B` is split as
`(A / I) × C`, lifting the distinguished quotient idempotent identifies the corresponding first
branch double quotient of `B` with `A / I`, and the class of `x` lands on `a₀ mod I`. -/
theorem exists_first_factor_quotient_ringEquiv_of_lifted_simple_root_idempotent
    (I : Ideal A)
    (hI : Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I)
    {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B]
    {C : Type u} [CommRing C] [Algebra (A ⧸ I) C]
    (x : B) (a₀ : A)
    (productDecomposition :
      (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] ((A ⧸ I) × C))
    (hx :
      productDecomposition (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) x) =
        ((Ideal.Quotient.mk I) a₀, 0)) :
    ∃ e : B, IsIdempotentElem e ∧
      ∃ firstFactor :
          ((B ⧸ Ideal.span ({1 - e} : Set B)) ⧸
              Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B)))
                (Ideal.map (algebraMap A B) I)) ≃+*
            (A ⧸ I),
        firstFactor
            ((Ideal.Quotient.mk
                (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B)))
                  (Ideal.map (algebraMap A B) I)))
              ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B))) x)) =
          (Ideal.Quotient.mk I) a₀ := by
  let IB : Ideal B := Ideal.map (algebraMap A B) I
  let ebar : B ⧸ IB := productDecomposition.symm (1, 0)
  have hebar : IsIdempotentElem ebar := by
    -- Proof comment: the distinguished first-factor idempotent pulls back along the product
    -- decomposition of `B / I B`.
    change ebar * ebar = ebar
    apply productDecomposition.injective
    simp [ebar]
  obtain ⟨⟨e, he⟩, heLift⟩ := (hI (B := B)).2 ⟨ebar, hebar⟩
  have hquot_e : (Ideal.Quotient.mk IB) e = ebar := by
    -- Proof comment: unwrap the idempotent-lifting witness on the closed fiber.
    simpa [RingHom.idempotentMap, ebar] using congrArg Subtype.val heLift
  obtain ⟨firstFactorBar, hfirstFactorBar, _⟩ :=
    factorwise_split_of_product_equiv_and_first_coordinate
      (R := A ⧸ I) (Q := B ⧸ IB) (C₁ := A ⧸ I) (C₂ := C) hebar productDecomposition
      (by simp [ebar]) hx
      (by
        intro y
        refine ⟨y, ?_⟩
        simp)
  obtain ⟨_, φ₁, _, hφ₁⟩ :=
    component_residue_ringEquiv_after_idempotent_split (A := B) (I := IB) hquot_e
  let firstFactor :
      ((B ⧸ Ideal.span ({1 - e} : Set B)) ⧸
          Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B))) IB) ≃+*
        (A ⧸ I) :=
    φ₁.trans firstFactorBar.toRingEquiv
  refine ⟨e, he, firstFactor, ?_⟩
  -- Proof comment: the double-quotient transport sends the branch class of `x` to the quotient
  -- branch of `x mod I`, and the factorwise split then reads off the first coordinate `a₀ mod I`.
  calc
    firstFactor
        ((Ideal.Quotient.mk
            (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B))) IB))
          ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B))) x))
        = firstFactorBar
            ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (B ⧸ IB))))
              ((Ideal.Quotient.mk IB) x)) := by
                change firstFactorBar
                    (φ₁
                      ((Ideal.Quotient.mk
                          (Ideal.map (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B))) IB))
                        ((Ideal.Quotient.mk (Ideal.span ({1 - e} : Set B))) x))) =
                  firstFactorBar
                    ((Ideal.Quotient.mk (Ideal.span ({1 - ebar} : Set (B ⧸ IB))))
                      ((Ideal.Quotient.mk IB) x))
                rw [hφ₁ x]
    _ = (Ideal.Quotient.mk I) a₀ := hfirstFactorBar

/-- Helper for Lemma 15.11.6: the finite-idempotent lifting controller on `A[X] / (f)` produces
the simple root needed for the henselian lifting field. -/
theorem exists_root_of_finite_idempotent_lifting_controller_split (I : Ideal A)
    (hI : Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I)
    {f : A[X]} (hf : f.Monic) (a₀ : A) (ha₀ : f.eval a₀ ∈ I)
    (hderiv : IsUnit ((Ideal.Quotient.mk I) (f.derivative.eval a₀))) :
    ∃ a : A, f.IsRoot a ∧ a - a₀ ∈ I := by
  -- Route correction: the missing controller argument must stay source-faithful. One has to form
  -- `B := A[X] / (f)`, lift the distinguished idempotent of `B / I B`, identify the first factor
  -- with `A` by Lemma `15.10.3`, and then read back the class of `X` as the lifted root.
  obtain ⟨hbar, hfactorbar, hhbar, hcoprime⟩ :=
    exists_coprime_residue_factorization_of_simple_root_mod_ideal
      (A := A) I hf a₀ ha₀ hderiv
  let Abar : Type u := A ⧸ I
  let abar : Abar := Ideal.Quotient.mk I a₀
  let B := AdjoinRoot f
  let x : B := AdjoinRoot.root f
  let IB : Ideal B := Ideal.map (algebraMap A B) I
  let fbar : Abar[X] := f.map (Ideal.Quotient.mk I)
  let linearFactorQuotient :
      (Abar[X] ⧸ Ideal.span ({X - C abar} : Set Abar[X])) ≃ₐ[Abar] Abar :=
    quotient_span_X_sub_C_algEquiv abar
  have hx_linear :
      linearFactorQuotient
        (Ideal.Quotient.mk (Ideal.span ({X - C abar} : Set Abar[X])) X) = abar := by
    -- Proof comment: the first branch of the residue factorization is exactly evaluation at `ā₀`.
    simpa [linearFactorQuotient, abar] using
      quotient_span_X_sub_C_algEquiv_apply_mk_X abar
  let closedFiberQuotientEquiv :
      (B ⧸ IB) ≃ₐ[A] (Abar[X] ⧸ Ideal.span ({fbar} : Set Abar[X])) :=
    AdjoinRoot.quotEquivQuotMap f I
  let _ := hI
  let _ := hhbar
  let _ := hcoprime
  let _ := x
  let _ := hfactorbar
  let _ := hx_linear
  let _ := closedFiberQuotientEquiv
  -- TODO: the verified frontier is now the exact closed-fiber normalization of the source proof.
  -- The remaining `(3 -> 1)` blocker is to package `f̄ = (X - C ā₀) * h̄` with `IsCoprime` into a
  -- binary Chinese-remainder product decomposition of `Ā[X] / (f̄)`, transport that split back
  -- along `closedFiberQuotientEquiv`, and then invoke
  -- `exists_first_factor_quotient_ringEquiv_of_lifted_simple_root_idempotent` followed by
  -- Lemma `15.10.3` to read the image of `AdjoinRoot.root f` as the desired root in `A`.
  sorry

/-- Helper for Lemma 15.11.6: the finite-idempotent criterion should recover the henselian owner
through the quotient algebra controller `A[X] / (f)`. -/
theorem henselianRing_of_hasFiniteAlgebraIdempotentLifting (I : Ideal A)
    (hI : Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I) :
    HenselianRing A I := by
  -- Route correction: the remaining source-faithful step has to lift the distinguished idempotent
  -- in `A[X] / (f)`, split off the factor corresponding to the simple root modulo `I`, identify
  -- that factor with `A` via Lemma `15.10.3`, and read back the lifted root.
  refine
    { jac := ?_
      is_henselian := ?_ }
  · -- Proof comment: the Jacobson field is already forced by the finite idempotent criterion.
    simpa [Ideal.jacobson_bot] using
      finite_idempotent_lifting_le_ring_jacobson (A := A) I hI
  · intro f hf a₀ ha₀ hderiv
    -- Proof comment: the remaining work is isolated in the exact-output controller package, so
    -- the owner field now reduces to one direct invocation.
    exact
      exists_root_of_finite_idempotent_lifting_controller_split
        (A := A) I hI hf a₀ ha₀ hderiv

section IntegralClosureQuotientFactor

variable (I : Ideal A)
variable {A' : Type v} [CommRing A'] [Algebra A A']

local notation "Abar" => A ⧸ I
local notation "Qe" => A' ⧸ Ideal.map (algebraMap A A') I
local notation "B'" => integralClosure A A'
local notation "IB'" => Ideal.map (algebraMap A B') I

/-- Helper for Lemma 15.11.6: the quotient comparison from `B' / I B'` to `A' / I A'` is
defined because the ideal `I B'` maps into `I A'` under the inclusion `B' → A'`. -/
private theorem integralClosure_ideal_map_le_comap :
    Ideal.map (algebraMap A B') I ≤
      Ideal.comap (integralClosure A A').val.toRingHom (Ideal.map (algebraMap A A') I) := by
  -- Proof comment: rewrite the target ideal through the inclusion `B' → A'` and use the
  -- canonical `map ≤ comap map` comparison.
  simpa only [Ideal.map_map] using
    (Ideal.le_comap_map :
      Ideal.map (algebraMap A B') I ≤
        Ideal.comap (integralClosure A A').val.toRingHom
          (Ideal.map (integralClosure A A').val.toRingHom
            (Ideal.map (algebraMap A B') I)))

/-- Helper for Lemma 15.11.6: the reduction of the integral closure maps canonically to the
reduction of `A'` through the inclusion `B' → A'`. -/
private abbrev quotient_to_etale_quotient : B' ⧸ IB' →ₐ[Abar] Qe :=
  AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A I) <|
    Ideal.quotientMapₐ (Ideal.map (algebraMap A A') I) (integralClosure A A').val
      (integralClosure_ideal_map_le_comap (A := A) (I := I) (A' := A'))

/-- Helper for Lemma 15.11.6: the kernel of the first projection `R × S → R` is generated by the
distinguished idempotent `(0, 1)`. -/
private theorem prod_fst_ker_eq_span_zero_one
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    RingHom.ker (AlgHom.fst R R S).toRingHom = Ideal.span ({(0, (1 : S))} : Set (R × S)) := by
  -- Proof comment: pairs with zero first coordinate are exactly multiples of `(0, 1)`.
  apply le_antisymm
  · intro x hx
    rcases x with ⟨r, s⟩
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(1, s), ?_⟩
    ext
    · simpa using hx
    · simp
  · intro x hx
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hx with ⟨y, rfl⟩
    simp

/-- Helper for Lemma 15.11.6: under an algebra equivalence with a product, the induced first
projection has kernel generated by the preimage of `(0, 1)`. -/
private theorem ker_first_projection_eq_span_symm_zero_one
    {R : Type u} {S : Type v} {T : Type _}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (φ : S ≃ₐ[R] (R × T)) :
    RingHom.ker (((AlgHom.fst R R T).comp φ.toAlgHom).toRingHom) =
      Ideal.span ({φ.symm (0, (1 : T))} : Set S) := by
  -- Proof comment: transport the explicit kernel generator of the product projection through `φ`.
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨φ.symm (1, (φ x).2), ?_⟩
    have hx0 : (φ x).1 = 0 := by
      simpa [AlgHom.comp_apply] using hx
    exact φ.injective <| by
      calc
        φ x = (0, (φ x).2) := by
          ext <;> simp [hx0]
        _ = (0, (1 : T)) * (1, (φ x).2) := by
          simp
        _ = φ (φ.symm (0, (1 : T)) * φ.symm (1, (φ x).2)) := by
          simp
  · intro x hx
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hx with ⟨y, rfl⟩
    simp [AlgHom.comp_apply]

/-- Helper for Lemma 15.11.6: a compatible product decomposition of `B' / I B'` retracts the
base algebra on its first projection. -/
private theorem first_projection_retract_of_integralClosure_split
    {C : Type _} {D : Type _}
    [CommRing C] [CommRing D]
    [Algebra Abar C] [Algebra Abar D]
    (hprod : Qe ≃ₐ[Abar] (Abar × C))
    (hprod_base : ∀ x : Abar, (hprod (algebraMap Abar Qe x)).1 = x)
    (productDecomposition : (B' ⧸ IB') ≃ₐ[Abar] (Abar × D))
    (toSecondFactor : D →ₐ[Abar] C)
    (hcompat :
      hprod.toAlgHom.comp (quotient_to_etale_quotient (A := A) (I := I) (A' := A')) =
        (AlgHom.prodMap (AlgHom.id Abar Abar) toSecondFactor).comp
          productDecomposition.toAlgHom) :
    ∀ x : Abar,
      ((AlgHom.fst Abar Abar D).comp productDecomposition.toAlgHom)
        (algebraMap Abar (B' ⧸ IB') x) = x := by
  -- Proof comment: compare the first coordinates in the compatibility square and simplify the
  -- quotient comparison on base elements.
  intro x
  have hfirst :
      (hprod
          (quotient_to_etale_quotient (A := A) (I := I) (A' := A')
            (algebraMap Abar (B' ⧸ IB') x))).1 =
        (productDecomposition (algebraMap Abar (B' ⧸ IB') x)).1 := by
    simpa [AlgHom.comp_apply] using
      congrArg Prod.fst (AlgHom.congr_fun hcompat (algebraMap Abar (B' ⧸ IB') x))
  have hbase :
      (hprod
          (quotient_to_etale_quotient (A := A) (I := I) (A' := A')
            (algebraMap Abar (B' ⧸ IB') x))).1 = x := by
    -- Proof comment: on elements coming from `A / I`, the comparison map is just the canonical
    -- algebra map.
    simpa [quotient_to_etale_quotient] using hprod_base x
  exact hfirst.symm.trans hbase

/-- Helper for Lemma 15.11.6: an étale quotient section induces a distinguished quotient factor
of `integralClosure A A' / I` identified with `A / I`. -/
theorem exists_integralClosure_quotient_product_of_etale_section
    [Algebra.Etale A A']
    (σ : A' →ₐ[A] Abar) :
    ∃ e : B' ⧸ IB',
      IsIdempotentElem e ∧
        ∃ firstFactor :
            ((B' ⧸ IB') ⧸ Ideal.span ({e} : Set (B' ⧸ IB'))) ≃ₐ[Abar] Abar,
          ∀ x : Abar,
            firstFactor
                (Ideal.Quotient.mk (Ideal.span ({e} : Set (B' ⧸ IB')))
                  (algebraMap Abar (B' ⧸ IB') x)) = x := by
  -- Route correction: extract the product decomposition of `B' / I B'` from Lemma `15.11.5`,
  -- then recover the first quotient factor as the quotient by the kernel of the induced first
  -- projection to `A / I`.
  obtain ⟨e₀, he₀, hprod, hprod_base⟩ :=
    exists_quotient_product_decomposition_of_etale_section (A := A) (A' := A') (I := I) σ
  obtain ⟨e₁, he₁, productDecomposition, toSecondFactor, g, hdata⟩ :=
    exists_integralClosure_product_decomposition_mod_ideal_with_localization
      (A := A) (B := A') (C₁ := Abar) (I := I) hprod
  dsimp [quotient_to_etale_quotient] at hdata
  rcases hdata with ⟨hcompat, hg, hbij⟩
  let D := (B' ⧸ IB') ⧸ Ideal.span ({1 - e₁} : Set (B' ⧸ IB'))
  let τ : B' ⧸ IB' →ₐ[Abar] Abar :=
    (AlgHom.fst Abar Abar D).comp productDecomposition.toAlgHom
  have hτ : ∀ x : Abar, τ (algebraMap Abar (B' ⧸ IB') x) = x := by
    -- Proof comment: the compatibility square identifies the first projection with the original
    -- quotient split.
    simpa [τ, D] using
      first_projection_retract_of_integralClosure_split
        (A := A) (I := I) (A' := A') hprod hprod_base productDecomposition toSecondFactor hcompat
  have hsurj : Function.Surjective τ := by
    -- Proof comment: the retraction property makes the first projection onto.
    intro x
    exact ⟨algebraMap Abar (B' ⧸ IB') x, hτ x⟩
  let e : B' ⧸ IB' := productDecomposition.symm (0, (1 : D))
  have he : IsIdempotentElem e := by
    -- Proof comment: pull back the canonical idempotent `(0, 1)` from the product decomposition.
    change e * e = e
    apply productDecomposition.injective
    simp [e]
  have hker : RingHom.ker τ.toRingHom = Ideal.span ({e} : Set (B' ⧸ IB')) := by
    -- Proof comment: the kernel is exactly the pullback of the model kernel of the first
    -- projection.
    simpa [τ, e, D] using
      ker_first_projection_eq_span_symm_zero_one
        (R := Abar) (S := B' ⧸ IB') (T := D) productDecomposition
  let firstFactor :
      ((B' ⧸ IB') ⧸ Ideal.span ({e} : Set (B' ⧸ IB'))) ≃ₐ[Abar] Abar :=
    (Ideal.quotientEquivAlgOfEq Abar hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  refine ⟨e, he, firstFactor, ?_⟩
  intro x
  -- Proof comment: evaluating the quotient-by-kernel equivalence on base elements recovers the
  -- retraction `τ`.
  simpa [firstFactor, τ, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk] using hτ x

end IntegralClosureQuotientFactor

/-- Helper for Lemma 15.11.6: Gabber's criterion yields an actual lift of any prescribed section
of an étale `A`-algebra modulo `I`. -/
theorem exists_lift_of_etale_section_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion)
    {A' : Type u} [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (σ : A' →ₐ[A] A ⧸ I) :
    ∃ τ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
  -- Route correction: the source proof does not stop at a decomposition of the integral closure.
  -- It must descend the controller split all the way back to an explicit section `A' →ₐ[A] A`.
  rcases hI with ⟨hJac, hGabber⟩
  let B' := integralClosure A A'
  let IB' : Ideal B' := Ideal.map (algebraMap A B') I
  -- Proof comment: the given quotient section first splits `A' / I A'` with a distinguished
  -- first factor `A / I`.
  obtain ⟨ebar, hebar, hquot, hquot_base⟩ :=
    exists_quotient_product_decomposition_of_etale_section (A := A) (A' := A') (I := I) σ
  -- Proof comment: Lemma `15.11.5` upgrades that quotient split to the integral closure together
  -- with the localization witness singled out in the source proof.
  obtain ⟨e, he, productDecomposition, toSecondFactor, g, hcontroller⟩ :=
    exists_integralClosure_product_decomposition_mod_ideal_with_localization
      (A := A) (B := A') (C₁ := A ⧸ I) (I := I) hquot
  obtain ⟨eIntegral, heIntegral, firstFactor, hfirstFactor⟩ :=
    exists_integralClosure_quotient_product_of_etale_section
      (A := A) (A' := A') (I := I) σ
  have hg_char :
      productDecomposition (Ideal.Quotient.mk IB' g) = (1, 0) := by
    simpa [B', IB'] using hcontroller.2.1
  have hAway :
      Function.Bijective (Localization.awayMapₐ (integralClosure A A').val g) := by
    simpa [B'] using hcontroller.2.2
  -- TODO: choose the finite controller subalgebra `B'' ⊆ B'` containing `g` and the localization
  -- numerators for `B'[1/g]`, apply Lemma `15.10.4` to obtain the monic controller polynomial,
  -- use `hGabber` to get a root in `1 + I`, split the controller algebra at that root, then
  -- descend the induced product decomposition from `B'` to `A'` through `hAway` and finish the
  -- first-factor identification with Lemma `15.10.3`.
  let _ := hJac
  let _ := hGabber
  let _ := hebar
  let _ := hquot_base
  let _ := e
  let _ := he
  let _ := eIntegral
  let _ := heIntegral
  let _ := firstFactor
  let _ := hfirstFactor
  let _ := toSecondFactor
  let _ := hg_char
  let _ := hAway
  sorry

/-- Helper for Lemma 15.11.6: Gabber's criterion should lift sections of étale algebras by the
integral-closure splitting route from the source proof. -/
theorem hasEtaleLiftProperty_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) :
    I.HasEtaleLiftProperty := by
  intro A' _ _ _ σ
  -- Proof comment: after isolating the source-faithful descent package, the section-lifting owner
  -- is again a direct invocation of the exact-output helper.
  exact
    exists_lift_of_etale_section_of_satisfiesGabberRootCriterion
      (A := A) I hI σ

end Ideal

-- Proof sketch: use the Stacks chain of implications `(2) → (4) → (3) → (1) → (5) → (2)`.
-- The Jacobson-radical condition enters via the henselian definition and the idempotent
-- injectivity lemma, finite and integral cases are related by integrality of finite algebras, and
-- Gabber's polynomial criterion supplies the final lifting step for étale sections.
/-- Lemma 15.11.6: for a commutative ring `A` and an ideal `I`, the following are equivalent: the
pair `(A, I)` is henselian; every section modulo `I` of an étale `A`-algebra lifts to `A`; for
all finite `A`-algebras the reduction map induces a bijection on idempotents; for all integral
`A`-algebras the reduction map induces a bijection on idempotents; and Gabber's Jacobson-plus-root
criterion holds for `I`. -/
theorem henselianRing_tfae_etaleLift_idempotents_gabberCriterion (I : Ideal A) :
    List.TFAE
      [ HenselianRing A I
      , I.HasEtaleLiftProperty
      , Ideal.HasFiniteAlgebraIdempotentLifting.{u, u} (A := A) I
      , Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) I
      , I.SatisfiesGabberRootCriterion
      ] := by
  -- Proof comment: package the source cycle through named implication lemmas. The two remaining
  -- controller arguments stay isolated behind dedicated helper statements.
  tfae_have 2 → 4 := by
    intro hEtale
    exact Ideal.integral_idempotent_lifting_of_hasEtaleLiftProperty (A := A) I hEtale
  tfae_have 4 → 3 := by
    intro hIntegral B _ _ _
    let _ : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite (R := A) (B := B)
    exact hIntegral (B := B)
  tfae_have 3 → 1 := by
    intro hFinite
    exact Ideal.henselianRing_of_hasFiniteAlgebraIdempotentLifting (A := A) I hFinite
  tfae_have 1 → 5 := by
    intro hHenselian
    let _ : HenselianRing A I := hHenselian
    exact Ideal.satisfiesGabberRootCriterion_of_henselianRing (A := A) I
  tfae_have 5 → 2 := by
    intro hGabber
    exact Ideal.hasEtaleLiftProperty_of_satisfiesGabberRootCriterion (A := A) I hGabber
  tfae_finish

namespace Ideal

-- Proof sketch: this is the `(5) → (1)` implication in Lemma `15.11.6`.
/-- Gabber's Jacobson-plus-root criterion implies that `(A, I)` is henselian. -/
theorem henselianRing_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) :
    HenselianRing A I := by
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (K : Ideal A) : List Prop :=
    [ HenselianRing A K
    , K.HasEtaleLiftProperty
    , Q K
    , P K
    , K.SatisfiesGabberRootCriterion
    ]
  have hTfae : List.TFAE (T I) := by
    -- Proof comment: reuse the chapter TFAE and extract the `(5) -> (1)` leg.
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hiff : I.SatisfiesGabberRootCriterion ↔ HenselianRing A I := by
    -- Proof comment: `List.TFAE.out` packages the required implication directly.
    simpa [T] using hTfae.out 4 0
  exact hiff.mp hI

-- Proof sketch: this is the `(1) → (3)` implication in Lemma `15.11.6`, specialized to the
-- identity `A`-algebra.
/-- If `(A, I)` is henselian, then reduction modulo `I` induces a bijection on idempotents of
`A`. -/
theorem quotientMk_bijective_idempotentMap_of_henselianRing (I : Ideal A) [HenselianRing A I] :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := by
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (K : Ideal A) : List Prop :=
    [ HenselianRing A K
    , K.HasEtaleLiftProperty
    , Q K
    , P K
    , K.SatisfiesGabberRootCriterion
    ]
  have hTfae : List.TFAE (T I) := by
    -- Proof comment: again extract the relevant TFAE leg instead of reproving idempotent lifting.
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hiff : HenselianRing A I ↔ Q I := by
    -- Proof comment: clause `(1) <-> (3)` specializes the finite-algebra idempotent criterion.
    simpa [T] using hTfae.out 0 2
  have hLift : Q I := by
    exact hiff.mp inferInstance
  exact hLift.bijective_idempotentMap

end Ideal

namespace Ideal

/-- Helper for Lemma 15.11.6: a Gabber test polynomial has derivative equal to `1` modulo `I` at
any point of the form `1 + i`. -/
theorem gabber_derivative_eval_eq_one_mod_ideal
    (I : Ideal A) {f : A[X]} (hf : I.IsGabberHenselPolynomial f) (i : I) :
    (Ideal.Quotient.mk I) (f.derivative.eval (1 + (i : A))) = 1 := by
  rcases hf with ⟨n, hn, -, hmap⟩
  have hq :
      (Ideal.Quotient.mk I) (1 + (i : A)) = (1 : A ⧸ I) := by
    -- Proof comment: points in `1 + I` reduce to `1` in the quotient ring.
    rw [map_add]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr i.property]
  -- Proof comment: transport the derivative evaluation to the quotient and simplify the model
  -- polynomial `X^n * (X - 1)` at `1`.
  calc
    (Ideal.Quotient.mk I) (f.derivative.eval (1 + (i : A)))
        = (Polynomial.map (Ideal.Quotient.mk I) f.derivative).eval
            ((Ideal.Quotient.mk I) (1 + (i : A))) := by
            rw [← Polynomial.eval₂_eq_eval_map]
            exact (Polynomial.eval₂_at_apply (p := f.derivative) (f := Ideal.Quotient.mk I)
              (1 + (i : A))).symm
    _ = ((Polynomial.map (Ideal.Quotient.mk I) f).derivative).eval (1 : A ⧸ I) := by
          rw [Polynomial.derivative_map, hq]
    _ = (((X ^ n) * (X - 1 : (A ⧸ I)[X])).derivative).eval (1 : A ⧸ I) := by
          rw [hmap]
    _ = 1 := by
          simp

/-- Helper for Lemma 15.11.6: over a Jacobson ideal, two congruent roots coincide once the
derivative at one root is congruent to `1` modulo the ideal. -/
theorem eq_of_roots_of_sub_mem_ideal_and_derivative_eq_one_mod_ideal
    (I : Ideal A) (hJac : I ≤ Ring.jacobson A) {f : A[X]} {a b : A}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (hd : b - a ∈ I)
    (hder : f.derivative.eval a - 1 ∈ I) :
    a = b := by
  let d := b - a
  obtain ⟨c, hc⟩ := binomExpansion f a d
  have hfactor :
      f.derivative.eval a * d + c * d ^ 2 = (f.derivative.eval a + c * d) * d := by
    -- Proof comment: factor the linear and quadratic correction terms by the common difference.
    dsimp [d]
    ring
  have hsum : 0 = f.derivative.eval a * d + c * d ^ 2 := by
    -- Proof comment: the binomial expansion collapses because both evaluation endpoints are roots.
    simpa [d, ha.eq_zero, hb.eq_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc
  have hrootEq : (f.derivative.eval a + c * d) * d = 0 := by
    rw [hfactor] at hsum
    exact hsum.symm
  have hd' : d ∈ I := by
    simpa [d] using hd
  have hcd : c * d ∈ I := by
    simpa [mul_comm] using I.mul_mem_left c hd'
  have hcorr :
      f.derivative.eval a + c * d - 1 ∈ I := by
    -- Proof comment: both the derivative correction and the quadratic correction lie in `I`.
    have hsum_mem : (f.derivative.eval a - 1) + c * d ∈ I := I.add_mem hder hcd
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum_mem
  have hunit : IsUnit (f.derivative.eval a + c * d) := by
    -- Proof comment: elements congruent to `1` modulo a Jacobson ideal are units.
    have hone :
        IsUnit (1 + (f.derivative.eval a + c * d - 1)) :=
      (ideal_le_ring_jacobson_iff_isUnit_one_add (R := A) (I := I)).mp hJac
        (f.derivative.eval a + c * d - 1) hcorr
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hone
  have hd_zero : d = 0 := hunit.mul_right_eq_zero.mp hrootEq
  have hba : b - a = 0 := by
    simpa [d] using hd_zero
  exact (sub_eq_zero.mp hba).symm

end Ideal

-- Proof sketch: for a Gabber test polynomial, the derivative at any root in `1 + I` is a unit
-- modulo `I`; comparing two such roots modulo the square of their difference shows that the
-- difference is annihilated by a unit, hence the roots coincide.
/-- Under Gabber's criterion, a henselian test polynomial has a unique root in `1 + I`. -/
theorem existsUnique_gabber_root_of_satisfiesGabberRootCriterion (I : Ideal A)
    (hI : I.SatisfiesGabberRootCriterion) {f : A[X]} (hf : I.IsGabberHenselPolynomial f) :
    ∃! i : I, f.IsRoot (1 + ↑i) := by
  rcases hI with ⟨hJac, hExists⟩
  obtain ⟨i, hi⟩ := hExists hf
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hder_eq :
      f.derivative.eval (1 + (i : A)) - 1 ∈ I := by
    -- Proof comment: the Gabber shape forces the derivative to reduce to `1` at every point of
    -- the form `1 + i`.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [map_sub] using sub_eq_zero.mpr
      (Ideal.gabber_derivative_eval_eq_one_mod_ideal (A := A) I hf i)
  have hdiff : (1 + (j : A)) - (1 + (i : A)) ∈ I := by
    -- Proof comment: two elements of `1 + I` differ by an element of `I`.
    simpa using I.sub_mem j.property i.property
  have hEq :
      (1 + (j : A)) = 1 + (i : A) := by
    -- Proof comment: apply the Jacobson-ideal uniqueness lemma to the two roots.
    exact
      (Ideal.eq_of_roots_of_sub_mem_ideal_and_derivative_eq_one_mod_ideal
        (A := A) I hJac hi hj hdiff hder_eq).symm
  apply Subtype.ext
  exact add_left_cancel hEq

end
