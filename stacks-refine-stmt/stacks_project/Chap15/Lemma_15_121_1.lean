import Mathlib
import stacks_project.Chap10.Lemma_10_52_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ModuleCat Polynomial
open IsLocalRing
open scoped BigOperators TensorProduct

universe u v w

/- Domain triage:
- primary domain: finite-length `R`-modules equipped with an endomorphism, viewed canonically as
  `R[X]`-modules;
- sampled owner API:
  `Module.compHom`,
  `IsFiniteLength`,
  `CompositionSeries.factor`,
  `Module.length_compositionSeries`,
  `LinearMap.det_eq_det_mul_det`;
- `source-facing`: the filtration-defined determinant, trace, and characteristic polynomial of an
  endomorphism `φ : Module.End R M` of a finite-length `R`-module `M`;
- `core/canonical`: `CompositionSeries (Submodule R[X] M)` after endowing `M` with the
  `R[X]`-module structure coming from `aeval φ`;
- `bridge/view`: the residue-field base change of the `X`-action on each simple `R[X]`-module
  factor, together with the short-exact-sequence comparison lemmas for determinant, trace, and
  characteristic polynomial.
-/

variable {R : Type u} [CommRing R]

namespace Module.End

variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem isNoetherian_of_isFiniteLength (hM : IsFiniteLength R M) :
    IsNoetherian R M :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1

private theorem isArtinian_of_isFiniteLength (hM : IsFiniteLength R M) :
    IsArtinian R M :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2

/-- View `(M, φ)` as an `R[X]`-module via the algebra map sending `X` to `φ`. -/
abbrev toPolynomialModule (φ : Module.End R M) : Module R[X] M :=
  Module.compHom M (aeval φ).toRingHom

/-- A `φ`-stable composition series of submodules of `M` from `⊥` to `⊤`, implemented canonically
as a composition series of `R[X]`-submodules of `M`. -/
abbrev StableCompositionSeries (φ : Module.End R M) :=
  let _ : Module R[X] M := φ.toPolynomialModule
  { s : CompositionSeries (Submodule R[X] M) // s.head = ⊥ ∧ s.last = ⊤ }

namespace StableCompositionSeries

variable {φ : Module.End R M}

@[simp] theorem head_eq_bot (s : StableCompositionSeries φ) : s.1.head = ⊥ :=
  s.2.1

@[simp] theorem last_eq_top (s : StableCompositionSeries φ) : s.1.last = ⊤ :=
  s.2.2

/-- The endomorphism induced on the `i`-th simple factor by the `X`-action on the canonical
`R[X]`-module attached to `(M, φ)`. -/
private noncomputable def factorMap (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
    s.1.factor i →ₗ[R] s.1.factor i :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  { toFun := fun x ↦ X • x
    map_add' := by
      intro x y
      exact smul_add (X : R[X]) x y
    map_smul' := by
      intro a x
      change
        (X : R[X]) • (((C : R →+* R[X]) a) • x) =
          ((C : R →+* R[X]) a) • ((X : R[X]) • x)
      rw [smul_smul, smul_smul, mul_comm] }

section LocalRing

variable [IsLocalRing R]

local notation "κ" => ResidueField R

/-- Each simple `R[X]`-factor contributes a finite-dimensional residue-field vector space after
base change along `R → κ`. -/
private noncomputable instance factorFiniteDimensional
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
    FiniteDimensional κ (κ ⊗[R] s.1.factor i) := by
  sorry

/- Bridge/view: the endomorphism induced on the residue-field tensor module of the `i`-th simple
`R[X]`-factor. -/
private noncomputable abbrev factorResidueFieldMap
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
    κ ⊗[R] s.1.factor i →ₗ[κ] κ ⊗[R] s.1.factor i :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  (factorMap s i).baseChange κ

/-- The determinant contributed by the `i`-th simple `R[X]`-factor in a composition series. -/
private noncomputable def factorDet (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    κ :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  (factorResidueFieldMap s i).det

/-- The trace contributed by the `i`-th simple `R[X]`-factor in a composition series. -/
private noncomputable def factorTrace (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    κ :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  let _ : FiniteDimensional κ (κ ⊗[R] s.1.factor i) :=
    factorFiniteDimensional s i
  (LinearMap.trace κ (κ ⊗[R] s.1.factor i)) (factorResidueFieldMap s i)

/-- The characteristic polynomial contributed by the `i`-th simple `R[X]`-factor in a composition
series. -/
private noncomputable def factorCharpoly
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    Polynomial κ :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  let _ : FiniteDimensional κ (κ ⊗[R] s.1.factor i) :=
    factorFiniteDimensional s i
  (factorResidueFieldMap s i).charpoly

/-- The determinant attached to a chosen composition series is the product of the simple-factor
determinants. -/
noncomputable def det (s : StableCompositionSeries φ) :
    κ :=
  ∏ i : Fin s.1.length, factorDet s i

/-- The trace attached to a chosen composition series is the sum of the simple-factor traces. -/
noncomputable def trace (s : StableCompositionSeries φ) :
    κ :=
  ∑ i : Fin s.1.length, factorTrace s i

/-- The characteristic polynomial attached to a chosen composition series is the product of the
simple-factor characteristic polynomials. -/
noncomputable def charpoly (s : StableCompositionSeries φ) :
    Polynomial κ :=
  ∏ i : Fin s.1.length, factorCharpoly s i

end LocalRing

end StableCompositionSeries

section LocalRing

variable [IsLocalRing R]

local notation "κ" => ResidueField R

section FiniteLength

variable [IsNoetherian R M] [IsArtinian R M]

-- Proof sketch: any two composition series in the `R[X]`-submodule lattice of the polynomial
-- module attached to `(M, φ)` are Jordan-Hölder equivalent, and isomorphic simple factors
-- contribute equal residue-field determinants. Hence the product over the factors is independent of
-- the chosen series.
/-- The filtration-defined determinant of `(M, φ)` is independent of the chosen `φ`-stable
composition series. -/
private theorem existsUnique_det
    (φ : Module.End R M) :
    ∃! a : κ,
      ∀ s : StableCompositionSeries φ, a = s.det := sorry

-- Proof sketch: the same Jordan-Hölder argument applies, now using additivity of trace on the
-- simple `R[X]`-factor residue-field vector spaces and invariance under isomorphism of factors.
/-- The filtration-defined trace of `(M, φ)` is independent of the chosen `φ`-stable composition
series. -/
private theorem existsUnique_trace
    (φ : Module.End R M) :
    ∃! a : κ,
      ∀ s : StableCompositionSeries φ, a = s.trace := sorry

-- Proof sketch: again Jordan-Hölder gives the same multiset of simple `R[X]`-factors, and the
-- characteristic polynomial of each factor is invariant under isomorphism, so the product is
-- independent of the chosen series.
/-- The filtration-defined characteristic polynomial of `(M, φ)` is independent of the chosen
`φ`-stable composition series. -/
private theorem existsUnique_charpoly
    (φ : Module.End R M) :
    ∃! p : Polynomial κ,
      ∀ s : StableCompositionSeries φ, p = s.charpoly := sorry

end FiniteLength

/-- The determinant of `(M, φ)` defined as the common value computed from any finite filtration by
simple `(M, φ)`-factors. -/
noncomputable def finiteLengthDeterminant
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    κ :=
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  (existsUnique_det φ).choose

/-- The trace of `(M, φ)` defined as the common value computed from any finite filtration by simple
`(M, φ)`-factors. -/
noncomputable def finiteLengthTrace
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    κ :=
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  (existsUnique_trace φ).choose

/-- The characteristic polynomial of `(M, φ)` defined as the common value computed from any finite
filtration by simple `(M, φ)`-factors. -/
noncomputable def finiteLengthCharpoly
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    Polynomial κ :=
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  (existsUnique_charpoly φ).choose

/-- The canonical finite-length determinant is computed by any `φ`-stable composition series of
submodules of `M`. -/
theorem finiteLengthDeterminant_eq_det
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthDeterminant hM = s.det := by
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  exact (existsUnique_det φ).choose_spec.1 s

/-- The canonical finite-length trace is computed by any `φ`-stable composition series of
submodules of `M`. -/
theorem finiteLengthTrace_eq_trace
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthTrace hM = s.trace := by
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  exact (existsUnique_trace φ).choose_spec.1 s

/-- The canonical finite-length characteristic polynomial is computed by any `φ`-stable
composition series of submodules of `M`. -/
theorem finiteLengthCharpoly_eq_charpoly
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthCharpoly hM = s.charpoly := by
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  exact (existsUnique_charpoly φ).choose_spec.1 s

end LocalRing

end Module.End

variable [IsLocalRing R]

section ShortExact

variable {S : ShortComplex (ModuleCat R)}
variable (φ₁ : Module.End R S.X₁) (φ₂ : Module.End R S.X₂) (φ₃ : Module.End R S.X₃)
variable (hX₁ : IsFiniteLength R S.X₁) (hX₂ : IsFiniteLength R S.X₂) (hX₃ : IsFiniteLength R S.X₃)

local notation "fS" => S.f.hom
local notation "gS" => S.g.hom

-- Proof sketch: pass the commuting short exact sequence of `R`-modules with endomorphism to the
-- associated `R[X]`-modules, refine compatible composition series, identify the factors for the
-- middle term with the factors for the outer terms, and reassemble the filtration-defined
-- invariants using multiplicativity of determinant and characteristic polynomial and additivity of
-- trace on simple factors.

namespace Module.End

/-- Lemma 15.121.1: for a short exact sequence
`0 → (M, φ) → (M', φ') → (M'', φ'') → 0` of finite-length `R`-modules with endomorphism, the
determinant over `κ` is multiplicative. -/
theorem finiteLengthDeterminant_eq_mul_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    : φ₂.finiteLengthDeterminant hX₂ =
        φ₁.finiteLengthDeterminant hX₁ * φ₃.finiteLengthDeterminant hX₃ := sorry

/-- Lemma 15.121.1: for a short exact sequence
`0 → (M, φ) → (M', φ') → (M'', φ'') → 0` of finite-length `R`-modules with endomorphism, the
trace over `κ` is additive. -/
theorem finiteLengthTrace_eq_add_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    : φ₂.finiteLengthTrace hX₂ = φ₁.finiteLengthTrace hX₁ + φ₃.finiteLengthTrace hX₃ := sorry

/-- Lemma 15.121.1: for a short exact sequence
`0 → (M, φ) → (M', φ') → (M'', φ'') → 0` of finite-length `R`-modules with endomorphism, the
characteristic polynomial over `κ` of `φ'` is the product of those of `φ` and `φ''`. -/
theorem finiteLengthCharpoly_eq_mul_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    : φ₂.finiteLengthCharpoly hX₂ =
        φ₁.finiteLengthCharpoly hX₁ * φ₃.finiteLengthCharpoly hX₃ := sorry

end Module.End

end ShortExact

section LinearAlgebraBridge

variable {κ : Type u} {V : Type v}
variable [Field κ] [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
variable (W : Submodule κ V) (φ : Module.End κ V) (hW : W ≤ W.comap φ)

namespace LinearMap

-- Proof sketch: choose a basis of `W` and a basis of `V ⧸ W`, combine them into a basis of `V`,
-- and identify the matrix of `φ` with an upper block-triangular matrix; the characteristic
-- polynomial is then the product of the diagonal block characteristic polynomials.
/-- Bridge/view: for an invariant subspace decomposition, the characteristic polynomial is the
product of the characteristic polynomials of the restriction and quotient endomorphisms. -/
theorem charpoly_eq_mul_restrict_mapQ :
    φ.charpoly = (φ.restrict hW).charpoly * (W.mapQ W φ hW).charpoly := sorry

/- Bridge/view: the determinant statement in the same situation is already the canonical mathlib
owner theorem. -/
recall LinearMap.det_eq_det_mul_det

-- Proof sketch: after choosing a basis adapted to `W`, the matrix of `φ` becomes block upper
-- triangular, so its trace is the sum of the traces of the diagonal blocks.
/-- Bridge/view: for an invariant subspace decomposition, the trace is the sum of the traces of
the restriction and quotient endomorphisms. -/
theorem trace_eq_add_restrict_mapQ :
    trace κ V φ = trace κ W (φ.restrict hW) + trace κ (V ⧸ W) (W.mapQ W φ hW) := sorry

end LinearMap

end LinearAlgebraBridge
