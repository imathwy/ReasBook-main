import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap15.Lemma_15_11_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "FiniteProjectiveClassModI" => finiteProjectiveModuleProperty (R ⧸ I)
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "ReduceCpx" =>
  (Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I))
    (ComplexShape.up ℤ))

/- Domain-style sampling for Lemma 15.79.4:
- primary domain: perfect complexes in derived categories of commutative rings and their
  nilpotent-thickening base change;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `K ⊗[R]^L[(R ⧸ I)]`,
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction:
  the source-facing statement already lives on the chapter's canonical base-change owner
  `derivedTensorWithAlgebra`, with public surface notation `K ⊗[R]^L[(R ⧸ I)]`;
- primitive vs. derived:
  primitive data are the commutative ring `R`, the nilpotent ideal `I`, and the object
  `K : D(R)`;
  the quotient perfectness hypothesis and the conclusion are derived API over the existing owners
  `derivedTensorWithAlgebra` and `DerivedCategory.IsPerfect`, so no extra public reduction package
  should be introduced;
- source/core/bridge triage:
  `source-facing`: perfectness descends from the derived quotient modulo a nilpotent ideal;
  `core/canonical`: `derivedTensorWithAlgebra` and `DerivedCategory.IsPerfect`;
  `bridge/view`: the notation `K ⊗[R]^L[(R ⧸ I)]` for the owner applied to `K`.
-/

/-- Helper for Lemma 15.79.4: a finite `R`-module vanishes if its reduction modulo a nilpotent
ideal vanishes. -/
private theorem isZero_of_reduceModI_obj_of_finite_of_isNilpotent
    {M : ModR} [Module.Finite R M]
    (hI : IsNilpotent I)
    (hMbar : IsZero (ReduceModI.obj M)) :
    IsZero M := by
  have hquot :
      IsZero (ModuleCat.of (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) := by
    -- Proof comment: rewrite scalar extension modulo `I` as the concrete quotient module once.
    exact hMbar.of_iso (reduceModI_obj_iso_quotient (I := I) M).symm
  have hquotSub : Subsingleton (M ⧸ (I • (⊤ : Submodule R M))) := by
    -- Proof comment: a zero quotient object is exactly a subsingleton quotient type.
    rw [ModuleCat.isZero_iff_subsingleton] at hquot
    exact hquot
  have hIM : I • (⊤ : Submodule R M) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    have hxzero :
        ((I • (⊤ : Submodule R M)).mkQ x : M ⧸ (I • (⊤ : Submodule R M))) = 0 := by
      exact Subsingleton.elim _ _
    exact (Submodule.Quotient.eq_zero_iff_mem).1 hxzero
  have hsub : Subsingleton M := by
    -- Proof comment: nilpotent Nakayama kills the whole module once the quotient is trivial.
    exact
      subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent
        (R := R) (I := I) (M := M) hIM hI
  rw [ModuleCat.isZero_iff_subsingleton]
  exact hsub

/-- Helper for Lemma 15.79.4: pseudo-coherence is preserved by isomorphisms in `D(R)`. -/
private theorem isPseudoCoherent_of_iso_local
    {K L : DModR} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  have hIso : IsIso (α ≫ e.hom) := by
    infer_instance
  -- Proof comment: keep the same bounded-above finite-free model and postcompose its comparison
  -- map with the chosen isomorphism.
  exact ⟨E, hEbounded, hEfree, α ≫ e.hom, hIso⟩

/-- Helper for Lemma 15.79.4: every perfect derived `R`-complex is pseudo-coherent. -/
private theorem isPseudoCoherent_of_isPerfect_local
    {K : DModR} (hK : K.IsPerfect) :
    K.IsPseudoCoherent := by
  rcases hK with ⟨L, eL, hL⟩
  let L' : CochainComplex (ModuleCat.{u} R) ℤ := L
  have eL' : K ≅ DerivedCategory.Q.obj L' := by
    simpa [L'] using eL
  have hL' : CochainComplex.IsBoundedFiniteProjective L' := by
    simpa [L'] using hL
  rcases hL'.bounded with ⟨_, b, _, hLLE⟩
  have hLminus : CochainComplex.minus (ModuleCat.{u} R) L' := by
    exact (CochainComplex.minus_iff (ModuleCat.{u} R) L').2 ⟨b, hLLE⟩
  have hTerms :
      ∀ i : ℤ, Module.Finite R (L'.X i) ∧ Module.Projective R (L'.X i) := by
    intro i
    exact ⟨hL'.finite i, hL'.projective i⟩
  let P : CochainComplex.MinusWithTermsIn
      (fun M : ModuleCat.{u} R ↦ Module.Finite R M ∧ Module.Projective R M) :=
    ⟨⟨L', hLminus⟩, hTerms⟩
  have hTFAE := cochainComplex_pseudoCoherent_tfae (R := R) L'
  have hIdQuasi : QuasiIso (𝟙 L') := by
    infer_instance
  have hLpc : L'.IsPseudoCoherent := by
    -- Proof comment: a bounded finite-projective complex is one of the explicit bounded-above
    -- finite-projective models appearing in the cochain-level pseudo-coherence criterion.
    exact (hTFAE.out 2 0).mp ⟨P, 𝟙 L', hIdQuasi⟩
  exact isPseudoCoherent_of_iso_local eL'.symm hLpc

/-- Helper for Lemma 15.79.4: a commutative ring is henselian at a locally nilpotent ideal. -/
private theorem henselianRing_of_isLocallyNilpotent_local
    (hI : I.IsLocallyNilpotent) : HenselianRing R I := by
  -- Proof comment: reuse the earlier chapter proof packaged in the stable inverse-system file.
  exact
    _private.stacks_project.Chap15.Lemma_15_11_3.0.henselianRing_of_locally_nilpotent_ideal
      I hI

-- Route correction: `Lemma_15_67_20` is currently broken upstream, so we follow the textbook
-- route directly. First descend pseudo-coherence from the perfect quotient, then use
-- `Lemma 15.76.9` to lift the bounded-above finite-projective quotient model, and finally apply
-- nilpotent Nakayama degreewise to recover the missing lower bound.
--
-- Proof sketch: pick a bounded finite-projective quotient representative `E` of
-- `K ⊗[R]^L[(R ⧸ I)]`. The pseudo-coherent part of perfectness descends across the nilpotent
-- quotient by Lemma `15.76.4`, so Lemma `15.76.9` lifts `E` to a bounded-above finite-projective
-- representative `P` of `K`. Since `E` vanishes below some degree `a`, each reduced term
-- `Pⁱ / I Pⁱ` is zero for `i < a`; nilpotent Nakayama then forces `Pⁱ = 0`, so `P` is actually
-- bounded on both sides.
/-- Lemma 15.79.4: let `R` be a commutative ring, let `I ⊆ R` be a nilpotent ideal, and let
`K ∈ D(R)`. If the derived reduction
`K \otimes_R^{\mathbf L} (R / I)` is perfect in `D(R / I)`, then `K` is perfect in `D(R)`. -/
theorem isPerfect_of_derivedTensorWithAlgebra_quotient_isPerfect_of_isNilpotent
    (K : DModR)
    (hbase : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect) (hI : IsNilpotent I) :
    K.IsPerfect := by
  have hIloc : I.IsLocallyNilpotent := by
    rw [Ideal.isLocallyNilpotent_iff]
    intro x hx
    rcases hI with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hxpow : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
    simpa [hn] using hxpow
  letI : HenselianRing R I :=
    henselianRing_of_isLocallyNilpotent_local (R := R) (I := I) hIloc
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  have hker : IsNilpotent (RingHom.ker (algebraMap R (R ⧸ I))) := by
    have hker_eq : RingHom.ker (algebraMap R (R ⧸ I)) = I := by
      ext x
      change Ideal.Quotient.mk I x = 0 ↔ x ∈ I
      rw [Ideal.Quotient.eq_zero_iff_mem]
    simpa [hker_eq] using hI
  have hKpc : K.IsPseudoCoherent := by
    -- Proof comment: the pseudo-coherent half of perfectness descends across nilpotent thickenings.
    exact
      (isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
        (R' := R) (R := R ⧸ I) hsurj hker K).1
        (isPseudoCoherent_of_isPerfect_local (I := I) hbase)
  rcases hbase with ⟨E, eBase, hE⟩
  rcases hE.bounded with ⟨a, b, hEGE, hELE⟩
  rw [CochainComplex.isStrictlyGE_iff] at hEGE
  let Eminus : CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat (R ⧸ I)) E).2 ⟨b, hELE⟩⟩,
      fun i ↦ ⟨hE.finite i, hE.projective i⟩⟩
  have hErep :
      Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (Eminus : CpxRI)) := by
    refine ⟨?_⟩
    simpa [Eminus] using eBase
  obtain ⟨P, eK, eE, _⟩ :=
    exists_boundedAbove_finiteProjective_representative_lifting_derivedReduction
      (R := R) (I := I) K Eminus hErep hKpc
  have hPGE : (P : CpxR).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hEzero : IsZero (E.X i) := hEGE i hi
    have hPbarZero : IsZero ((ReduceCpx.obj (P : CpxR)).X i) := by
      let eXi : ((ReduceCpx.obj (P : CpxR)).X i) ≅ E.X i := asIso (eE.hom.f i)
      -- Proof comment: the lifted reduction agrees degreewise with the zero quotient term.
      exact hEzero.of_iso eXi.symm
    -- Proof comment: once the reduced term is zero, nilpotent Nakayama forces the source term to
    -- vanish as well.
    simpa [ReduceCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      isZero_of_reduceModI_obj_of_finite_of_isNilpotent
        (I := I) (M := (P : CpxR).X i) hI hPbarZero
  obtain ⟨bP, hPLE⟩ := (CochainComplex.minus_iff (ModuleCat R) (P : CpxR)).1 P.minus
  have hPperfect : CochainComplex.IsBoundedFiniteProjective (P : CpxR) := by
    refine ⟨⟨a, bP, hPGE, hPLE⟩, ?_, ?_⟩
    · intro i
      exact (P.term_mem i).1
    · intro i
      exact (P.term_mem i).2
  -- Proof comment: the lifted complex is now bounded on both sides with finite projective terms,
  -- so it is exactly a perfect representative of `K`.
  exact ⟨(P : CpxR), eK, hPperfect⟩

end

end CategoryTheory
