import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_13_6
import stacks_proof.stacks_project.Chap10.Lemma_10_134_15
import stacks_proof.stacks_project.Chap10.Lemma_10_134_16
import stacks_proof.stacks_project.Chap10.Lemma_10_137_9
import stacks_proof.stacks_project.Chap10.Lemma_10_139_1
import stacks_proof.stacks_project.Chap10.Definition_10_125_1
import stacks_proof.stacks_project.Chap10.Definition_10_135_5
import stacks_proof.stacks_project.Chap15.Lemma_15_3_2
import stacks_proof.stacks_project.Chap15.Definition_15_33_2
import stacks_proof.stacks_project.Chap15.Lemma_15_3_3
import stacks_proof.stacks_project.Chap15.Lemma_15_9_13
import stacks_proof.stacks_project.Chap15.Lemma_15_86_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open CategoryTheory

universe u v w

namespace Algebra

noncomputable section

section

/- Domain-style sampling:
- primary domain: finitely presented algebras, away localizations, cotangent modules, and smooth
  localized comparison maps;
- sampled owner declarations:
  `Localization.awayMapₐ`,
  `Algebra.Generators`,
  `Algebra.Generators.exists_presentation_of_free_cotangent`,
  `RingHom.IsLocalCompleteIntersection`;
- best owner abstraction:
  the localized comparison map is the canonical away map `Localization.awayMapₐ`, while the
  free-cotangent presentation datum should be recorded through the canonical generators/cotangent
  owners rather than via a parallel local wrapper;
- primitive vs. derived:
  primitive data are a finite generator family and freeness of its cotangent module; finite type
  is derived from that witness and should not remain separate primitive local data.

Source/core/bridge triage:
- `source-facing`: the localized existence of a finite generator family with free cotangent module;
- `core/canonical`: `Localization.awayMapₐ` for the localized algebra map and
  `Algebra.Generators.exists_presentation_of_free_cotangent` for derived presentation upgrades;
- `bridge/view`: the theorem below, which applies those owners to the localized `A`-algebras
  `C_a`.
-/

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [FinitePresentation R A]
variable {C : Type w} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

local notation:max "A[" a "]" => Localization.Away a
local notation:max "C[" a "]" => Localization.Away (algebraMap A C a)

/-- Helper for Lemma 16.3.1: the symmetric algebra over an `A`-module inherits the ambient
`R`-algebra structure by restricting scalars along `R → A`. -/
local instance symmetricAlgebraBaseAlgebra
    (M : Type*) [AddCommMonoid M] [Module A M] :
    Algebra R (SymmetricAlgebra A M) :=
  ((algebraMap A (SymmetricAlgebra A M)).comp (algebraMap R A)).toAlgebra

/-- Helper for Lemma 16.3.1: the restricted `R`-scalar action on `Sym_A(M)` is compatible with
the canonical `A`-algebra structure. -/
local instance symmetricAlgebraScalarTower
    (M : Type*) [AddCommMonoid M] [Module A M] :
    IsScalarTower R A (SymmetricAlgebra A M) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ rfl

/-- Helper for Lemma 16.3.1: the model symmetric algebra over `A[a]` inherits the ambient
`R`-algebra structure by restricting scalars along `R → A[a]`. -/
local instance localizedSymmetricAlgebraBaseAlgebra
    (M : Type*) [AddCommMonoid M] [Module A[a] M] (a : A) :
    Algebra R (SymmetricAlgebra A[a] M) :=
  ((algebraMap A[a] (SymmetricAlgebra A[a] M)).comp (algebraMap R A[a])).toAlgebra

/-- Helper for Lemma 16.3.1: the restricted `R`-scalar action on the model symmetric algebra over
`A[a]` is compatible with the canonical `A[a]`-algebra structure. -/
local instance localizedSymmetricAlgebraScalarTower
    (M : Type*) [AddCommMonoid M] [Module A[a] M] (a : A) :
    IsScalarTower R A[a] (SymmetricAlgebra A[a] M) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ rfl

/-- Helper for Lemma 16.3.1: the section-local notation `C[a]` carries the canonical
`A[a]`-algebra structure coming from the localized map `A[a] → C[a]`. -/
local instance awayLocalizationAlgebra (a : A) : Algebra A[a] C[a] :=
  (Localization.awayMapₐ (algebraMap A C) a).toRingHom.toAlgebra

/-- Helper for Lemma 16.3.1: the away localization of a symmetric algebra over `A` carries the
canonical `A[a]`-algebra structure coming from localizing the structure map `A → Sym_A(M)`. -/
local instance symmetricAlgebraAwayAlgebra
    (M : Type*) [AddCommMonoid M] [Module A M] (a : A) :
    Algebra A[a] (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) :=
  (Localization.awayMapₐ (algebraMap A (SymmetricAlgebra A M)) a).toRingHom.toAlgebra

/-- Helper for Lemma 16.3.1: the degree-zero projection of a symmetric algebra over `A`. -/
noncomputable def symmetricAlgebra_augmentation
    (M : Type*) [AddCommMonoid M] [Module A M] :
    SymmetricAlgebra A M →ₐ[A] A :=
  SymmetricAlgebra.lift (0 : M →ₗ[A] A)

/-- Helper for Lemma 16.3.1: the source submonoid for localizing `Sym_A(M)` away from `a`
coincides with the powers of the image of `a` in the symmetric algebra. -/
theorem away_localized_symmetricAlgebra_sourceSubmonoid_eq
    (M : Type*) [AddCommMonoid M] [Module A M] (a : A) :
    Algebra.algebraMapSubmonoid (SymmetricAlgebra A M) (Submonoid.powers a) =
      Submonoid.powers (algebraMap A (SymmetricAlgebra A M) a) :=
  by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨n, rfl⟩
      exact ⟨n, by simp⟩
    · intro hx
      rcases hx with ⟨n, rfl⟩
      exact ⟨n, rfl⟩

/-- Helper for Lemma 16.3.1: localizing `Sym_A(M)` away from `a` agrees with taking the symmetric
algebra of the away-localized module. -/
noncomputable def away_localized_symmetricAlgebra_algEquiv
    (M : Type*) [AddCommMonoid M] [Module A M] (a : A) :
    Localization.Away (algebraMap A (SymmetricAlgebra A M) a) ≃ₐ[A[a]]
      SymmetricAlgebra A[a] (LocalizedModule.Away a M) := by
  -- Route correction: identify the actual away localization with the tensor-product base change,
  -- then apply the canonical symmetric-algebra localization equivalence once.
  let eAway :
      A[a] ⊗[A] SymmetricAlgebra A M ≃ₐ[A[a]]
        Localization.Away (algebraMap A (SymmetricAlgebra A M) a) :=
    IsLocalization.Away.tensorRightEquiv (SymmetricAlgebra A M) a A[a]
  let eModel :
      SymmetricAlgebra A[a] (LocalizedModule.Away a M) ≃ₐ[A[a]]
        A[a] ⊗[A] SymmetricAlgebra A M :=
    localizedSymmetricAlgebraEquiv (Submonoid.powers a)
  -- The source submonoid is exactly the powers of `algebraMap A (Sym_A M) a`, so the base-change
  -- localization owner matches the actual away localization in the target statement.
  exact
    (AlgEquiv.ofEq
      (R := A[a])
      (S := Localization.Away (algebraMap A (SymmetricAlgebra A M) a))
      (T := Localization
        (Algebra.algebraMapSubmonoid (SymmetricAlgebra A M) (Submonoid.powers a)))
      rfl
      (by
        rw [away_localized_symmetricAlgebra_sourceSubmonoid_eq (A := A) (M := M) a]))
      |>.trans eAway.symm |>.trans eModel.symm

/-- Helper for Lemma 16.3.1: smoothness of the away-localized symmetric-algebra model transports
back to the actual away localization of `Sym_A(M)`. -/
lemma away_localized_symmetricAlgebra_smooth_of_model
    (M : Type*) [AddCommMonoid M] [Module A M] (a : A)
    (hsmooth : Smooth A[a] (SymmetricAlgebra A[a] (LocalizedModule.Away a M))) :
    Smooth A[a] (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) := by
  letI : Algebra A[a] (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) :=
    (Localization.awayMapₐ (algebraMap A (SymmetricAlgebra A M)) a).toRingHom.toAlgebra
  letI : Smooth A[a] (SymmetricAlgebra A[a] (LocalizedModule.Away a M)) := hsmooth
  -- Transport the smooth symmetric-algebra model back across the canonical localization
  -- equivalence.
  exact Smooth.of_equiv ((away_localized_symmetricAlgebra_algEquiv (A := A) (M := M) a).symm)

/-- Helper for Lemma 16.3.1: once the away-localized cotangent module is finite projective over
`A[a]`, the away localization of `Sym_A(M)` is smooth over `A[a]`. -/
lemma away_localized_symmetricAlgebra_smooth_of_finite_projective
    (M : Type*) [AddCommMonoid M] [Module A M] (a : A)
    (hM : Module.FiniteProjective A[a] (LocalizedModule.Away a M)) :
    Smooth A[a] (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) := by
  letI : Algebra A[a] (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) :=
    (Localization.awayMapₐ (algebraMap A (SymmetricAlgebra A M)) a).toRingHom.toAlgebra
  -- First smooth the canonical localized symmetric-algebra model using the standard
  -- finite-projective criterion for symmetric algebras.
  have hsmoothModel :
      Smooth A[a] (SymmetricAlgebra A[a] (LocalizedModule.Away a M)) := by
    exact
      (smooth_symmetricAlgebra_iff_finite_and_projective
        (A := A[a]) (M := LocalizedModule.Away a M)).2 hM
  -- Then transport that model smoothness back to the actual away localization.
  exact away_localized_symmetricAlgebra_smooth_of_model (A := A) (M := M) a hsmoothModel

/-- Helper for Lemma 16.3.1: a free-cotangent generator family on the canonical localized
symmetric-algebra model transports across `away_localized_symmetricAlgebra_algEquiv` to the actual
away localization of `Sym_A(M)`. -/
lemma away_localized_symmetricAlgebra_generators_freeCotangent_of_model
    (M : Type*) [AddCommMonoid M] [Module A M] (a : A)
    {m : ℕ}
    (Q : Generators R (SymmetricAlgebra A[a] (LocalizedModule.Away a M)) (Fin m))
    (hfree : Module.Free (SymmetricAlgebra A[a] (LocalizedModule.Away a M))
      Q.toExtension.Cotangent) :
    ∃ Q' :
      Generators R (Localization.Away (algebraMap A (SymmetricAlgebra A M) a)) (Fin m),
        Module.Free
          (Localization.Away (algebraMap A (SymmetricAlgebra A M) a))
          Q'.toExtension.Cotangent := by
  -- TODO for Lemma 16.3.1: once the canonical `A[a]`-algebra equivalence between the actual away
  -- localization and the model symmetric algebra is stabilized, transport the generator family and
  -- its free cotangent module across that equivalence.
  sorry

/-- Helper for Lemma 16.3.1: a finite module over `A` admits a surjective coordinate map from a
finite free module `A^n`. -/
lemma finiteModule_exists_coordinate_surjection
    {M : Type*} [AddCommMonoid M] [Module A M]
    (hM : Module.Finite A M) :
    ∃ n : ℕ, ∃ π : (Fin n → A) →ₗ[A] M, Function.Surjective π := by
  classical
  letI : Module.Finite A M := hM
  -- Choose a finite generating family and turn it into the canonical coordinate map.
  rcases (Submodule.fg_def.mp (Module.Finite.fg_top (R := A) (M := M))) with ⟨S, hSfin, hSspan⟩
  let s : Finset M := hSfin.toFinset
  let v0 : s → M := fun x ↦ x.1
  have hv0 : Submodule.span A (Set.range v0) = ⊤ := by
    -- The `Finset` version spans the same submodule as the original finite generating set.
    rw [← hSspan]
    congr 1
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, rfl⟩
      exact (Set.Finite.mem_toFinset hSfin).1 y.2
    · intro hx
      refine ⟨⟨x, (Set.Finite.mem_toFinset hSfin).2 hx⟩, rfl⟩
  have hsurj0 : Function.Surjective (Fintype.linearCombination A v0) := by
    -- A spanning family gives a surjective linear-combination map.
    exact (span_range_eq_top_iff_surjective_fintypeLinearCombination A v0).1 hv0
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let π0 : (s → A) →ₗ[A] M := Fintype.linearCombination A v0
  refine ⟨Fintype.card s, π0.comp (LinearEquiv.funCongrLeft (R := A) (M := A) e).toLinearMap, ?_⟩
  -- Transport surjectivity across the reindexing equivalence `s ≃ Fin n`.
  intro x
  rcases hsurj0 x with ⟨y, rfl⟩
  refine ⟨fun i ↦ y (e.symm i), ?_⟩
  change π0 ((LinearMap.funLeft A A e) (fun i ↦ y (e.symm i))) = π0 y
  congr 1
  ext j
  simp [LinearMap.funLeft_apply]

/-- Helper for Lemma 16.3.1: the symmetric algebra on a finite `A`-module is finite type
over `A`. -/
lemma symmetricAlgebra_finiteType_of_finite
    {M : Type*} [AddCommMonoid M] [Module A M]
    (hM : Module.Finite A M) :
    Algebra.FiniteType A (SymmetricAlgebra A M) := by
  classical
  obtain ⟨n, π, hπ⟩ := finiteModule_exists_coordinate_surjection (A := A) hM
  have hfreeFiniteType : Algebra.FiniteType A (SymmetricAlgebra A (Fin n → A)) := by
    -- The symmetric algebra of the finite free module `A^n` is a polynomial algebra in `n`
    -- variables.
    exact Algebra.FiniteType.equiv inferInstance
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun A (Fin n))).symm
  let σ : SymmetricAlgebra A (Fin n → A) →ₐ[A] SymmetricAlgebra A M :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι A M).comp π)
  have hσsurj : Function.Surjective σ := by
    -- Surjectivity is checked on the symmetric-algebra generators and then propagated by
    -- the induction principle.
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap a =>
        refine ⟨algebraMap A (SymmetricAlgebra A (Fin n → A)) a, ?_⟩
        simp [σ]
    | ι m =>
        rcases hπ m with ⟨m', rfl⟩
        refine ⟨SymmetricAlgebra.ι A (Fin n → A) m', ?_⟩
        simp [σ]
    | mul x y hx hy =>
        rcases hx with ⟨x', rfl⟩
        rcases hy with ⟨y', rfl⟩
        refine ⟨x' * y', ?_⟩
        simp [σ]
    | add x y hx hy =>
        rcases hx with ⟨x', rfl⟩
        rcases hy with ⟨y', rfl⟩
        refine ⟨x' + y', ?_⟩
        simp [σ]
  letI : Algebra.FiniteType A (SymmetricAlgebra A (Fin n → A)) := hfreeFiniteType
  -- Descend finite type along the surjective symmetric-algebra map induced by the free cover.
  exact Algebra.FiniteType.of_surjective σ hσsurj

/-- Helper for Lemma 16.3.1: a finite projective module over `A` is a direct summand of a finite
free module, exhibited by a surjective coordinate map whose kernel supplies the complementary
factor. -/
lemma finiteProjective_exists_coordinate_split_surjection
    {M : Type*} [AddCommMonoid M] [Module A M]
    (hM : Module.FiniteProjective A M) :
    ∃ n : ℕ, ∃ q : (Fin n → A) →ₗ[A] M, Function.Surjective q ∧
      Nonempty ((M × LinearMap.ker q) ≃ₗ[A] (Fin n → A)) := by
  classical
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  letI : Module.Finite A M := hM.1
  letI : Module.Projective A M := hM.2
  obtain ⟨n, q, i, hq, _hi, hqi⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  refine ⟨n, q, hq, ?_⟩
  -- Proof comment: the chosen right inverse splits the surjection `q`, so the source free module
  -- identifies with `M` times the kernel complement.
  refine ⟨(LinearEquiv.prodComm A M (LinearMap.ker q)).trans ?_⟩
  exact kernel_prod_equiv_of_rightInverse (R := A) q i hqi

/-- Helper for Lemma 16.3.1: if `R → A[a]` is a local complete intersection, then the
away-localized cotangent module of any fixed finite presentation of `A` is finite projective over
`A[a]`. -/
lemma localizedCotangentFiniteProjectiveOfLci
    {n : ℕ} (P : Generators R A (Fin n)) (a : A)
    (ha : (algebraMap R A[a]).IsLocalCompleteIntersection) :
    Module.FiniteProjective A[a] (LocalizedModule.Away a P.toExtension.Cotangent) := by
  classical
  -- TODO for Lemma 16.3.1: combine the lci witness presentation of `A[a]` with the localized
  -- presentation-stability theorem to transport finite projectivity of the witness cotangent
  -- module back to the localized cotangent of the fixed presentation `P`.
  let _ := ha
  sorry

/-- Helper for Lemma 16.3.1: on an lci chart `A[a]`, the away localization of the symmetric
algebra on the cotangent module of a fixed presentation admits an `R`-generator family with free
cotangent module. -/
lemma awayLocalizedSymmetricAlgebra_generators_freeCotangent_of_lci
    {n : ℕ} (P : Generators R A (Fin n)) (a : A)
    (ha : (algebraMap R A[a]).IsLocalCompleteIntersection) :
    ∃ m : ℕ,
      ∃ Q :
        Generators R
          (Localization.Away (algebraMap A (SymmetricAlgebra A P.toExtension.Cotangent) a))
          (Fin m),
        Module.Free
          (Localization.Away (algebraMap A (SymmetricAlgebra A P.toExtension.Cotangent) a))
          Q.toExtension.Cotangent := by
  let N := LocalizedModule.Away a P.toExtension.Cotangent
  have hlocalizedCotangent : Module.FiniteProjective A[a] N := by
    -- Reuse the localized cotangent finite-projective bridge before choosing the free cover.
    exact localizedCotangentFiniteProjectiveOfLci (R := R) (A := A) P a ha
  obtain ⟨m, q, hq, hsplit⟩ :=
    finiteProjective_exists_coordinate_split_surjection
      (A := A[a]) (M := N) hlocalizedCotangent
  let _ := q
  let _ := hq
  let _ := hsplit
  -- Route correction: the old proof route tried to identify the induced symmetric-algebra
  -- presentation cotangent directly with `S ⊗ ker(q)` on the away-localized target. The stabilized
  -- route should instead work on the model `S := SymmetricAlgebra A[a] N`, use the presentation
  -- exact sequence from `q`, splice it with the localized `R -> A[a]` presentation, and then use
  -- `away_localized_symmetricAlgebra_generators_freeCotangent_of_model` for the final transport
  -- step only once.
  --
  -- TODO for Lemma 16.3.1: construct a model-level `R`-generator family on
  -- `SymmetricAlgebra A[a] N`, prove its cotangent module is free using the split cover
  -- `N ⊕ ker(q) ≃ A[a]^m` together with the localized `R -> A[a]` conormal sequence, and then
  -- invoke `away_localized_symmetricAlgebra_generators_freeCotangent_of_model`.
  sorry

/-- Helper for Lemma 16.3.1: on the model symmetric algebra over `A[a]`, freeness of
`LocalizedModule.Away a P.toExtension.Cotangent × Ω[A[a]⁄R]` upgrades to freeness of the absolute
Kähler differentials over `R`. -/
lemma modelSymmetricAlgebra_kaehler_free_of_freeCotangentAndKaehler
    {n : ℕ} (P : Generators R A (Fin n)) (a : A)
    (hlocalizedCotangent :
      Module.FiniteProjective A[a] (LocalizedModule.Away a P.toExtension.Cotangent))
    (hfree :
      Module.Free A[a]
        (LocalizedModule.Away a P.toExtension.Cotangent × Ω[A[a]⁄R])) :
    Module.Free
      (SymmetricAlgebra A[a] (LocalizedModule.Away a P.toExtension.Cotangent))
      Ω[SymmetricAlgebra A[a] (LocalizedModule.Away a P.toExtension.Cotangent)⁄R] := by
  -- TODO for Lemma 16.3.1: split the transitivity short exact sequence
  -- `S ⊗[A[a]] Ω[A[a]⁄R] → Ω[S⁄R] → Ω[S⁄A[a]]` for the model ring
  -- `S = SymmetricAlgebra A[a] (LocalizedModule.Away a P.toExtension.Cotangent)`, identify
  -- `Ω[S⁄A[a]]` with `S ⊗[A[a]] LocalizedModule.Away a P.toExtension.Cotangent`, and then
  -- transport freeness from `hfree`.
  let _ := hlocalizedCotangent
  let _ := hfree
  sorry

/-- Helper for Lemma 16.3.1: on a smooth chart `A[a]`, the away localization of the symmetric
algebra on the cotangent module of a fixed presentation has free absolute Kähler differentials
over `R`. -/
lemma awayLocalizedSymmetricAlgebra_kaehler_free_of_smooth
    {n : ℕ} (P : Generators R A (Fin n)) (a : A)
    (hsmooth : Smooth R A[a]) :
    Module.Free
      (Localization.Away (algebraMap A (SymmetricAlgebra A P.toExtension.Cotangent) a))
      Ω[Localization.Away (algebraMap A (SymmetricAlgebra A P.toExtension.Cotangent) a)⁄R] := by
  let N := LocalizedModule.Away a P.toExtension.Cotangent
  have hlocalizedCotangent :
      Module.FiniteProjective A[a] N := by
    have hSyntomic : (algebraMap R A[a]).Syntomic := by
      simpa [RingHom.algebraMap_toAlgebra] using (Algebra.smooth_syntomic (R := R) (S := A[a]))
    have hlci : (algebraMap R A[a]).IsLocalCompleteIntersection :=
      (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection
        (algebraMap R A[a])).mp hSyntomic |>.2
    exact localizedCotangentFiniteProjectiveOfLci (R := R) (A := A) P a hlci
  obtain ⟨m, q, hq, hsplit⟩ :=
    finiteProjective_exists_coordinate_split_surjection
      (A := A[a]) (M := N) hlocalizedCotangent
  let _ := q
  let _ := hq
  let _ := hsplit
  -- Route correction: avoid the unavailable tensor-kernel transport on the actual away-localized
  -- algebra. The intended route is to prove first on `S := SymmetricAlgebra A[a] N` that
  -- `N × Ω[A[a]⁄R]` is free using the smooth localized presentation of `A[a]`, then use the
  -- transitivity short exact sequence for `R -> A[a] -> S` together with
  -- `symmetricAlgebra_tensorToKaehler_bijective`, and only at the end transport the result across
  -- `away_localized_symmetricAlgebra_algEquiv`.
  --
  -- TODO for Lemma 16.3.1: build the free decomposition of
  -- `LocalizedModule.Away a P.toExtension.Cotangent × Ω[A[a]⁄R]` from the localized presentation
  -- of `A[a]`, propagate it to `Ω[SymmetricAlgebra A[a] N⁄R]` via the transitivity sequence, and
  -- transport the resulting freeness statement back to the away localization.
  sorry

-- Proof sketch: choose the symmetric algebra `C = Sym_A^*(I/I²)` for a finite presentation of
-- `A` over `R`. Its degree-zero projection gives the retraction. The localized Jacobi-Zariski
-- sequence and the local complete intersection hypothesis make the localized conormal module free,
-- yielding smoothness over `A_a`; when `A_a` is already smooth over `R`, the localized Kähler
-- differentials of `C_a` become free as well.
/-- Lemma 16.3.1: if `A` is a finitely presented `R`-algebra, there exists a finite type
`A`-algebra `C` together with an `A`-algebra retraction `C → A` such that for every `a : A` with
`R → A[a]` a local complete intersection, the localization `C[a]` is smooth over `A[a]` and
admits a finite generator family over `R` whose cotangent module is free; this can be upgraded to
a finite presentation with free conormal module by
`Algebra.Generators.exists_presentation_of_free_cotangent`. For every `a : A` with `A[a]` smooth
over `R`, the module `Ω[C[a]⁄R]` is free over `C[a]`. -/
@[stacks 07CE]
theorem exists_finiteType_retraction_with_smoothing_localizations :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Algebra.FiniteType A C) (r : C →ₐ[A] A),
      (∀ a : A,
        (algebraMap R A[a]).IsLocalCompleteIntersection →
          Smooth A[a] C[a] ∧
            ∃ n : ℕ, ∃ P : Generators R C[a] (Fin n),
              Module.Free C[a] P.toExtension.Cotangent) ∧
      ∀ a : A,
        Smooth R A[a] →
          Module.Free C[a] Ω[C[a]⁄R] := by
  classical
  obtain ⟨n, α, hα, hkerα⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  let val : Fin n → A := fun i ↦ α (MvPolynomial.X i)
  have hval : (MvPolynomial.aeval val : MvPolynomial (Fin n) R →ₐ[R] A) = α := by
    -- Both algebra maps agree on the polynomial variables, so generator extensionality applies.
    ext i
    simp [val]
  have hsurjVal : Function.Surjective (MvPolynomial.aeval val : MvPolynomial (Fin n) R → A) := by
    -- The generator family is induced by the chosen finite polynomial presentation of `A`.
    intro a
    rcases hα a with ⟨φ, rfl⟩
    refine ⟨φ, ?_⟩
    rw [hval]
  let P : Generators R A (Fin n) := Algebra.Generators.ofSurjective val hsurjVal
  have hkerP : P.toExtension.ker.FG := by
    -- The extension attached to `P` is the original polynomial presentation `α`.
    change (RingHom.ker (MvPolynomial.aeval val).toRingHom).FG
    simpa [hval] using hkerα
  let M := P.toExtension.Cotangent
  let C' := SymmetricAlgebra A M
  let r : C' →ₐ[A] A := symmetricAlgebra_augmentation (A := A) M
  have hfiniteM : Module.Finite A M := by
    -- The conormal module `I / I²` is finite because the defining ideal of `A` is finitely generated.
    simpa [M] using Extension.Cotangent.finite hkerP
  have hfiniteTypeC : Algebra.FiniteType A C' := by
    -- The new helper packages exactly the free-cover argument from the source construction.
    simpa [C', M] using symmetricAlgebra_finiteType_of_finite (A := A) hfiniteM
  refine ⟨C', inferInstance, inferInstance, inferInstance, inferInstance, hfiniteTypeC, r, ?_, ?_⟩
  · intro a ha
    refine ⟨?_, ?_⟩
    · -- Route correction: the smoothness half is now reduced to the single source-faithful bridge
      -- from the localized cotangent finite-projective input to the actual away localization.
      have hlocalizedCotangent :
          Module.FiniteProjective A[a]
            (LocalizedModule.Away a P.toExtension.Cotangent) := by
        -- The new helper packages the lci witness presentation together with the stable
        -- localized-presentation comparison.
        exact localizedCotangentFiniteProjectiveOfLci (R := R) (A := A) P a ha
      -- The remaining work is now exactly the finite-projective localized cotangent bridge from
      -- the source proof.
      exact
        away_localized_symmetricAlgebra_smooth_of_finite_projective
          (A := A) (M := P.toExtension.Cotangent) a hlocalizedCotangent
    · -- The presentation half still follows the source q/K localized conormal computation after
      -- the same finite-projective cotangent bridge is established.
      -- Delegate the source-faithful localized generator construction to the dedicated helper so
      -- the main theorem only records the final witness shape.
      simpa [C', M] using
        awayLocalizedSymmetricAlgebra_generators_freeCotangent_of_lci
          (R := R) (A := A) P a ha
  · intro a hsmooth
    -- Route correction: avoid the unavailable syntomic owner. The source proof computes
    -- `Ω[C'_a⁄R]` directly from the same localized q/K presentation used in the first clause and
    -- the cotangent-to-Kähler exact sequence for the canonical localized presentation of `A[a]`.
    -- Delegate the smooth Kähler-freeness computation to the dedicated helper so the remaining
    -- blocker is isolated at the model level rather than spread through the main theorem.
    simpa [C', M] using
      awayLocalizedSymmetricAlgebra_kaehler_free_of_smooth
        (R := R) (A := A) P a hsmooth

end

end

end Algebra
