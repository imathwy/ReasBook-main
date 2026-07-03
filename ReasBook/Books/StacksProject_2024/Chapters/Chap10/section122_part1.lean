import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_122_1 (from Chap10) -/
universe u v w

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Domain-style sampling for Lemma 10.122.1:
- primary domain: isolated points of `Spec(S)` for a finite type `k`-algebra over a field, together
  with the resulting localization and product-splitting structure;
- sampled owner declarations:
  `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`,
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`,
  `PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen`,
  `exists_idempotent_algEquiv_localization_prod_quotient_of_isClosed_range_comap`;
- best owner abstraction: the canonical prime-spectrum owner `PrimeSpectrum`, with the chapter's
  source-facing basic-open notation `D(-)` and canonical localization/product decomposition
  owners supplying the derived structure;
- primitive data: a prime `q : PrimeSpectrum S`;
- derived API: the TFAE clauses, the localized factor `Localization.AtPrime q.asIdeal`, and the
  complementary finite type factor.

Source/core/bridge triage:
- `source-facing`: `isolatedPoint_tfae` and the complementary-factor decomposition theorem;
- `core/canonical`: `PrimeSpectrum`, `D(-)`, `Localization.AtPrime`, and
  `PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`;
- `bridge/view`: the product decomposition theorem, which presents the source-facing splitting
  while deriving it from canonical idempotent/localization owners.
-/

-- Proof sketch: combine the Jacobson-space criterion for isolated points in a Noetherian Jacobson
-- spectrum with the characterization of finite type zero-dimensional algebras over a field as
-- finite algebras. Clause `(3)` is the basic-open reformulation of an isolated point; clauses
-- `(4)`, `(5)`, and `(6)` come from the local Krull-dimension formulas at a point of a finite type
-- `k`-algebra and the finite residue-field criterion for closed points.
/-- Lemma 10.122.1: for a prime `q` of a finite type `k`-algebra `S`, the following are
equivalent: `q` is an isolated point of `Spec(S)`; the local ring `S_q` is finite over `k`; there
exists `g ∉ q` with `D(g) = {q}`; the local topological dimension of `Spec(S)` at `q` is zero;
`q` is a closed point and `S_q` has Krull dimension zero; and the residue field extension
`κ(q) / k` is finite while `S_q` has Krull dimension zero. -/
theorem isolatedPoint_tfae (q : PrimeSpectrum S) :
    List.TFAE
      [ IsOpen ({q} : Set (PrimeSpectrum S))
      , Module.Finite k (Localization.AtPrime q.asIdeal)
      , ∃ g : S, g ∉ q.asIdeal ∧ (D(g) : Set (PrimeSpectrum S)) = {q}
      , topologicalKrullDimAt q = 0
      , IsClosed ({q} : Set (PrimeSpectrum S)) ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0
      , Module.Finite k q.asIdeal.ResidueField ∧
          ringKrullDim (Localization.AtPrime q.asIdeal) = 0
      ] := sorry

-- Proof sketch: an isolated point gives a clopen singleton in `Spec(S)`, hence a decomposition of
-- `S` by the standard correspondence between clopen subsets of the spectrum and product
-- decompositions of the ring. The factor corresponding to `{q}` is canonically `S_q`, and finite
-- type over `k` passes to the complementary factor.
/-- If `q` is an isolated point of `Spec(S)`, then `S` splits as the product of `S_q` and another
finite type `k`-algebra, with first projection equal to the localization map `S → S_q`. -/
theorem exists_finiteType_complementary_factor_of_isolatedPoint
    (q : PrimeSpectrum S) (hq : IsOpen ({q} : Set (PrimeSpectrum S))) :
    ∃ (S' : Type w) (_ : CommRing S') (_ : Algebra k S') (_ : Algebra.FiniteType k S')
      (e : S ≃ₐ[k] Localization.AtPrime q.asIdeal × S'),
      (RingHom.fst (Localization.AtPrime q.asIdeal) S').comp e.toRingHom =
        algebraMap S (Localization.AtPrime q.asIdeal) := sorry

/- Canonical owner reuse: the `D(g) = {q}` localization comparison is exactly
`PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton`. -/
recall PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton

end

/-! ### Lemma_10_122_2 (from Chap10) -/
universe u v

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Domain-style sampling for Lemma 10.122.2:
- primary domain: the fiber of `Spec S → Spec R` over a prime `p`, viewed through the canonical
  fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S`;
- sampled owner declarations:
  `PrimeSpectrum.preimageEquivFiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `isolatedPoint_tfae`,
  `topologicalKrullDimAt`;
- best owner abstraction: the canonical fiber-prime owner
  `PrimeSpectrum.preimageEquivFiber R S p`, with Lemma `10.122.1` supplying the derived
  isolated-point `List.TFAE` on the fiber ring;
- primitive data: `p : PrimeSpectrum R`, `q : PrimeSpectrum S`, and the lies-over witness
  `hq : PrimeSpectrum.comap (algebraMap R S) q = p`;
- derived API: the six equivalent fiberwise conditions.

Source/core/bridge triage:
- `source-facing`: `prime_over_isolated_point_in_fiber_tfae`;
- `core/canonical`: `PrimeSpectrum.preimageEquivFiber`, `PrimeSpectrum.preimageHomeomorphFiber`,
  and `isolatedPoint_tfae`;
- `bridge/view`: clause `(3)`, which keeps the textbook basic-open singleton condition on primes
  of `S` lying over `p` while the other clauses live directly on the fiber prime. -/

-- Proof sketch: identify the fiber of `Spec S → Spec R` over `p` with `Spec (κ(p) ⊗[R] S)` via
-- `PrimeSpectrum.preimageHomeomorphFiber`. Under this correspondence, the point `q` becomes
-- `PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩`, and the six clauses are exactly the six
-- clauses of Lemma `10.122.1` for the finite type `κ(p)`-algebra `p.asIdeal.Fiber S`, with
-- clause `(3)` restated in the source-facing primes-over-`p` basic-open language.
/-- Lemma 10.122.2: for a finite type ring map `R → S`, a prime `q` of `S` lying over `p`, and the
corresponding point `\bar q` of the fiber `Spec (κ(p) ⊗[R] S)`, the following are equivalent:
`\bar q` is an isolated point of the fiber; the local fiber ring at `\bar q` is finite over
`κ(p)`; there exists `g ∉ q` such that the primes of `S` lying over `p` inside `D(g)` are exactly
`{q}`; the local topological dimension of the fiber at `\bar q` is zero; `\bar q` is closed and
the local fiber ring has Krull dimension zero; and the residue field extension at `\bar q` is
finite over `κ(p)` while the local fiber ring has Krull dimension zero. -/
theorem prime_over_isolated_point_in_fiber_tfae (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    let qbar : PrimeSpectrum (p.asIdeal.Fiber S) := PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩
    List.TFAE
      [ IsOpen ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))
      , Module.Finite p.asIdeal.ResidueField (Localization.AtPrime qbar.asIdeal)
      , ∃ g : S, g ∉ q.asIdeal ∧
          ({q' : PrimeSpectrum S | PrimeSpectrum.comap (algebraMap R S) q' = p} ∩
            (D(g) : Set (PrimeSpectrum S)) = ({q} : Set (PrimeSpectrum S)))
      , topologicalKrullDimAt qbar = 0
      , IsClosed ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∧
          ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
      , Module.Finite p.asIdeal.ResidueField qbar.asIdeal.ResidueField ∧
          ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0
      ] := sorry

end

/-! ### Definition_10_122_3 (from Chap10) -/
universe u v

/- Domain triage:
* primary domain: quasi-finite finite-type ring maps in commutative algebra;
* sampled owner declarations:
  `Algebra.QuasiFiniteAt`, `Algebra.QuasiFinite`,
  `RingHom.QuasiFiniteAt`, `RingHom.QuasiFinite`;
* source-facing layer: Definition `10.122.3` packages finite type together with the canonical
  primewise and global quasi-finite owners;
* core/canonical owners: `Algebra.QuasiFiniteAt` and `Algebra.QuasiFinite`;
* bridge/view: the thin projection/equivalence lemmas exposing the owner predicates under the
  source-facing finite-type packaging.
* primitive data: the finite-type hypothesis and the canonical owner predicates;
* derived API: the projection lemmas and the ambient-finite-type equivalences below.
-/

namespace Algebra.FiniteType

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.122.3 (1): `R → S` is quasi-finite at the prime `q` when it is of finite type
and the canonical owner predicate `Algebra.QuasiFiniteAt R q` holds. -/
def QuasiFiniteAt (q : Ideal S) [q.IsPrime] : Prop :=
  Algebra.FiniteType R S ∧ Algebra.QuasiFiniteAt R q

namespace QuasiFiniteAt

variable {R S}
variable {q : Ideal S} [q.IsPrime]

/-- The finite-type hypothesis carried by the source-facing primewise quasi-finite predicate. -/
theorem finiteType (h : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.FiniteType R S :=
  h.1

/-- The canonical local quasi-finite owner carried by the source-facing finite-type predicate. -/
theorem toQuasiFiniteAt (h : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.QuasiFiniteAt R q :=
  h.2

/-- Under an ambient finite-type hypothesis, the source-facing primewise notion is obtained
directly from the canonical owner. -/
theorem of_quasiFiniteAt [Algebra.FiniteType R S] (h : Algebra.QuasiFiniteAt R q) :
    Algebra.FiniteType.QuasiFiniteAt R S q :=
  ⟨inferInstance, h⟩

/-- Under an ambient finite-type hypothesis, the source-facing primewise notion is equivalent to
the canonical owner `Algebra.QuasiFiniteAt R q`. -/
theorem iff_quasiFiniteAt [Algebra.FiniteType R S] :
    Algebra.FiniteType.QuasiFiniteAt R S q ↔ Algebra.QuasiFiniteAt R q :=
  ⟨toQuasiFiniteAt, of_quasiFiniteAt⟩

end QuasiFiniteAt

/-- Definition 10.122.3 (2): `R → S` is quasi-finite when it is of finite type and quasi-finite in
the canonical sense. -/
def QuasiFinite : Prop :=
  Algebra.FiniteType R S ∧ Algebra.QuasiFinite R S

namespace QuasiFinite

variable {R S}

/-- The finite-type hypothesis carried by the source-facing global quasi-finite predicate. -/
theorem finiteType (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.FiniteType R S :=
  h.1

/-- The canonical global quasi-finite owner carried by the source-facing finite-type predicate. -/
theorem toQuasiFinite (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.QuasiFinite R S :=
  h.2

/-- Under an ambient finite-type hypothesis, the source-facing global notion is obtained directly
from the canonical owner. -/
theorem of_quasiFinite [Algebra.FiniteType R S] (h : Algebra.QuasiFinite R S) :
    Algebra.FiniteType.QuasiFinite R S :=
  ⟨inferInstance, h⟩

/-- Under an ambient finite-type hypothesis, the source-facing global notion is equivalent to the
canonical owner `Algebra.QuasiFinite R S`. -/
theorem iff_quasiFinite [Algebra.FiniteType R S] :
    Algebra.FiniteType.QuasiFinite R S ↔ Algebra.QuasiFinite R S :=
  ⟨toQuasiFinite, of_quasiFinite⟩

end QuasiFinite

end

end Algebra.FiniteType

/-! ### Lemma_10_122_4 (from Chap10) -/
universe u v

section

open PrimeSpectrum
open Algebra.TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

private noncomputable abbrev fiberPrime (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    PrimeSpectrum (p.asIdeal.Fiber S) :=
  PrimeSpectrum.preimageEquivFiber R S p ⟨q, hq⟩

omit [Algebra.FiniteType R S] in
private theorem fiberPrime_asIdeal_comap (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Ideal.comap includeRight.toRingHom (fiberPrime p q hq).asIdeal = q.asIdeal := by
  change
    ((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrime p q hq)).1.asIdeal =
      q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, hq⟩)

private theorem isOpen_singleton_of_quasiFiniteAt (K : Type*) {A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (Q : PrimeSpectrum A)
    [Algebra.QuasiFiniteAt K Q.asIdeal] :
    IsOpen ({Q} : Set (PrimeSpectrum A)) := by
  exact
    (@Algebra.QuasiFiniteAt.isClopen_singleton K A _ _ _ Q inferInstance inferInstance
      inferInstance).isOpen

private theorem quasiFiniteAt_iff_quasiFiniteAt_fiberPrime (p : PrimeSpectrum R)
    (q : PrimeSpectrum S) (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField (fiberPrime p q hq).asIdeal := by
  constructor
  · intro h
    letI : Algebra.QuasiFiniteAt R q.asIdeal := h
    have hfiber : Ideal.comap includeRight.toRingHom (fiberPrime p q hq).asIdeal = q.asIdeal :=
      fiberPrime_asIdeal_comap p q hq
    exact
      Algebra.QuasiFiniteAt.baseChange q.asIdeal (fiberPrime p q hq).asIdeal (by
          simpa using hfiber.symm)
  · intro h
    letI : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField (fiberPrime p q hq).asIdeal := h
    have hfiber : Ideal.comap includeRight.toRingHom (fiberPrime p q hq).asIdeal = q.asIdeal :=
      fiberPrime_asIdeal_comap p q hq
    exact
      Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
        p.asIdeal q.asIdeal (fiberPrime p q hq).asIdeal (by
          simpa using hfiber)

-- Proof sketch: identify the primes of the fiber `p.asIdeal.Fiber S` with the primes of `S`
-- lying over `p` via `PrimeSpectrum.preimageHomeomorphFiber`. Under this identification, clause
-- (1) says every point of `Spec (p.asIdeal.Fiber S)` is open, so the spectrum is discrete.
-- Since `p.asIdeal.Fiber S` is a finite type algebra over the field `p.asIdeal.ResidueField`,
-- apply Lemma `10.61.3` to obtain the equivalence with module-finiteness over the residue field
-- and with finiteness of the prime spectrum.
/-- Lemma 10.122.4: for a finite type ring map `R → S` and a prime `p` of `R`, the following are
equivalent: `R → S` is quasi-finite at every prime of `S` lying over `p`; the fiber algebra
`p.asIdeal.Fiber S = S ⊗[R] κ(p)` is finite over `κ(p)`; and `Spec (p.asIdeal.Fiber S)` is a
finite set. -/
theorem quasiFiniteAt_primesOver_tfae_fiberFinite (p : PrimeSpectrum R) :
    List.TFAE
      [ (∀ q : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap R S) q = p → Algebra.QuasiFiniteAt R q.asIdeal)
      , Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S)
      , Finite (PrimeSpectrum (p.asIdeal.Fiber S))
      ] := by
  let K := p.asIdeal.ResidueField
  let A := p.asIdeal.Fiber S
  have hA :
      List.TFAE
        [ Ring.KrullDimLE 0 A
        , Finite (PrimeSpectrum A)
        , Finite (MaximalSpectrum A)
        , T2Space (PrimeSpectrum A)
        , FiniteDimensional K A
        , IsArtinianRing A
        , DiscreteTopology (PrimeSpectrum A)
        ] :=
      (finiteTypeAlgebra_over_field_zeroDimensional_tfae :
        List.TFAE
          [ Ring.KrullDimLE 0 A
          , Finite (PrimeSpectrum A)
          , Finite (MaximalSpectrum A)
          , T2Space (PrimeSpectrum A)
          , FiniteDimensional K A
          , IsArtinianRing A
          , DiscreteTopology (PrimeSpectrum A)
          ])
  tfae_have 1 → 3 := by
    intro hqf
    have hFiber : ∀ Q : PrimeSpectrum A, Algebra.QuasiFiniteAt K Q.asIdeal := by
      intro Q
      let q := (PrimeSpectrum.preimageEquivFiber R S p).symm Q
      have hQ : fiberPrime p q.1 q.2 = Q := by
        change
          (PrimeSpectrum.preimageEquivFiber R S p)
              ((PrimeSpectrum.preimageEquivFiber R S p).symm Q) = Q
        exact (PrimeSpectrum.preimageEquivFiber R S p).apply_symm_apply Q
      simpa [hQ] using
        (quasiFiniteAt_iff_quasiFiniteAt_fiberPrime p q.1 q.2).mp
          (hqf q.1 q.2)
    letI : DiscreteTopology (PrimeSpectrum A) :=
      discreteTopology_iff_isOpen_singleton.mpr fun Q ↦ by
        letI : Algebra.QuasiFiniteAt K Q.asIdeal := hFiber Q
        simpa using isOpen_singleton_of_quasiFiniteAt K Q
    simpa [A] using (finite_of_compact_of_discrete : Finite (PrimeSpectrum A))
  tfae_have 3 → 2 := by
    intro hfinite
    have hfd : FiniteDimensional K A := (hA.out 1 4 rfl rfl).mp hfinite
    letI : FiniteDimensional K A := hfd
    simpa [A, K] using (inferInstance : Module.Finite K A)
  tfae_have 2 → 1 := by
    intro hfinite
    letI : Module.Finite K A := hfinite
    have hFiber : ∀ Q : PrimeSpectrum A, Algebra.QuasiFiniteAt K Q.asIdeal := by
      intro Q
      dsimp [Algebra.QuasiFiniteAt]
      infer_instance
    intro q hq
    exact
      (quasiFiniteAt_iff_quasiFiniteAt_fiberPrime p q hq).mpr <|
        hFiber (fiberPrime p q hq)
  tfae_finish

end

/-! ### Lemma_10_122_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Lemma 10.122.5: for a finite type ring map `R → S`, quasi-finiteness is exactly the canonical
condition that every fiber algebra `κ(𝔭) ⊗[R] S` is finite over `κ(𝔭)`. This is the canonical
theorem `Algebra.quasiFinite_iff`. -/
recall Algebra.quasiFinite_iff

end

/-! ### Lemma_10_122_6 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain triage:
* primary domain: quasi-finiteness at a prime under localization away from elements;
* sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Algebra.QuasiFiniteAt.baseChange`,
  `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`,
  `IsLocalization.isPrime_of_isPrime_disjoint`;
* source-facing layer: `quasiFiniteAt_iff_quasiFiniteAt_away_mul`;
* core/canonical owner: `Algebra.QuasiFiniteAt`;
* bridge/view: the localized prime
  `q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))` and the induced algebra
  `Localization.Away f → Localization.Away ((algebraMap R S f) * g)`.

Primitive data are only `f : R`, `g : S`, and the prime `q : Ideal S`. The localized prime and the
comparison algebra are derived from the owner abstraction, so they should not survive as separate
public wrapper declarations. The finite-type hypothesis from the source is redundant here: the
equivalence is a formal property of `Algebra.QuasiFiniteAt` under the canonical localization maps.
-/

-- Proof sketch: `q` is disjoint from the powers of `(algebraMap R S f) * g` because neither
-- `algebraMap R S f` nor `g` lies in `q`; then `IsLocalization.isPrime_of_isPrime_disjoint`
-- gives the corresponding prime in the localization.
private theorem isPrime_map_away_mul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    (q.map (algebraMap S (Localization.Away ((algebraMap R S f) * g)))).IsPrime := by
  refine IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers ((algebraMap R S f) * g))
    (Localization.Away ((algebraMap R S f) * g)) q inferInstance ?_
  rw [Set.disjoint_left]
  intro x hxM hxq
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hxM
  have hqPrime : q.IsPrime := inferInstance
  rcases hqPrime.mem_or_mem (by simpa [mul_pow] using hxq) with hfq | hgq
  · exact hf <| hqPrime.mem_of_pow_mem n hfq
  · exact hg <| hqPrime.mem_of_pow_mem n hgq

-- Proof sketch: localize `R → S` away from `f` on the source and away from `g` on the target.
-- The canonical owner API proves this by base change and the inverse localization-on-stalks map.
-- The finite-type hypothesis appearing in the source is redundant for `Algebra.QuasiFiniteAt`.
/-- Lemma 10.122.6: if `q` is a prime of `S`, `f` avoids `q ∩ R`, and `g` avoids `q`, then
`R → S` is quasi-finite at `q` iff the localized map `R_f → S_{fg}` is quasi-finite at the
extended prime `qS_{fg}`. -/
theorem quasiFiniteAt_iff_quasiFiniteAt_away_mul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.under R) (hg : g ∉ q) :
    let fg : S := (algebraMap R S f) * g
    let qfg : Ideal (Localization.Away fg) := q.map (algebraMap S (Localization.Away fg))
    letI : qfg.IsPrime := isPrime_map_away_mul f g q hf hg
    letI : Algebra (Localization.Away f) (Localization.Away fg) :=
      ((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
        (Localization.awayMap (algebraMap R S) f)).toAlgebra
    Algebra.QuasiFiniteAt R q ↔
      Algebra.QuasiFiniteAt (Localization.Away f) qfg := sorry

end

/-! ### Lemma_10_122_7 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
variable [IsScalarTower R S S'] [IsScalarTower R R' S']

-- Proof sketch: first base change quasi-finiteness at the pulled-back prime of `S` to the
-- corresponding prime of `R' ⊗[R] S` using `Algebra.QuasiFiniteAt.baseChange`. Then descend along
-- the surjective canonical tensor-product map
-- `productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S')`
-- via `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`, using
-- `RingHom.surjectiveOnStalks_of_surjective`.
/-- Lemma 10.122.7: if the canonical map `R' ⊗[R] S → S'` is surjective and the pullback of `q'`
to `S` is a point where `R → S` is quasi-finite, then `R' → S'` is quasi-finite at `q'`.

The source states this in the finite-type setting, but the canonical owner proof only uses
`Algebra.QuasiFiniteAt.baseChange` and `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`, so no finite
type hypothesis is needed in the public API. -/
theorem quasiFiniteAt_baseChange_of_surjective
    (hSurj : Function.Surjective
      (productLeftAlgHom (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S') :
        R' ⊗[R] S →ₐ[R'] S'))
    (q' : Ideal S') [q'.IsPrime]
    [Algebra.QuasiFiniteAt R (q'.comap (algebraMap S S'))] :
    Algebra.QuasiFiniteAt R' q' := sorry

end

/-! ### Lemma_10_122_8 (from Chap10) -/
/- Lemma 10.122.8: a composition of quasi-finite ring maps is quasi-finite. This is exactly the
canonical mathlib theorem `RingHom.QuasiFinite.comp`. -/
recall RingHom.QuasiFinite.comp

/-! ### Lemma_10_122_9 (from Chap10) -/
/- Domain triage:
* primary domain: quasi-finite ring maps and their base-change stability;
* source-facing layer: a base change of a quasi-finite ring map is quasi-finite;
* core/canonical owner: `RingHom.QuasiFinite.isStableUnderBaseChange`;
* derived API: the `Algebra.QuasiFinite` and `Algebra.QuasiFiniteAt` instances used internally by
  mathlib to prove the owner theorem.

Primitive data vs. derived API:
* primitive input: a quasi-finite ring hom together with a base-change square;
* derived layer: primewise/tensor-product reformulations belong to the internal proof of the owner
  theorem, not to this file's public API.
-/

/- Lemma 10.122.9: any base change of a quasi-finite ring map is quasi-finite. This is exactly the
canonical mathlib theorem `RingHom.QuasiFinite.isStableUnderBaseChange`. -/
recall RingHom.QuasiFinite.isStableUnderBaseChange

/-! ### Lemma_10_122_10 (from Chap10) -/
universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/- Domain-style sampling for Lemma 10.122.10:
- primary domain: quasi-finite finite-type algebras at a prime in a tower;
- sampled owner declarations:
  `Algebra.FiniteType.QuasiFiniteAt`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.QuasiFinite.of_restrictScalars`,
  `Algebra.FiniteType.of_restrictScalars_finiteType`;
- best owner abstraction for the numbered lemma: the source-facing predicate
  `Algebra.FiniteType.QuasiFiniteAt A C r.asIdeal`;
- primitive data: the tower `A → B → C`, the prime `r : PrimeSpectrum C`, and the source-facing
  hypothesis that `A → C` is quasi-finite at `r`;
- derived API: the core local quasi-finite consequence for `B → C` and the finite-type component
  needed to reassemble the source-facing conclusion.

Source/core/bridge triage:
- `source-facing`: the textbook permanence lemma for quasi-finiteness at `r`, where Definition
  `10.122.3` includes both finite type and the local quasi-finite owner;
- `core/canonical`: `Algebra.QuasiFiniteAt` and `Algebra.FiniteType`;
- `bridge/view`: the restriction-of-scalars theorem for `Algebra.QuasiFiniteAt`.

Primitive data vs. derived API:
- primitive source-facing data: `hAC : Algebra.FiniteType.QuasiFiniteAt A C r.asIdeal`;
- derived core owner consequence: `Algebra.QuasiFiniteAt B r.asIdeal`;
- derived finite-type component: `Algebra.FiniteType B C`. -/

-- Proof sketch: first restrict scalars on `Localization.AtPrime r.asIdeal` to transport the core
-- owner `Algebra.QuasiFiniteAt` from `A → C` to `B → C`. Then recover the finite-type component
-- of `B → C` by restricting scalars on the finite-type algebra `C` over `A`.
/-- Core owner bridge for Lemma 10.122.10: quasi-finiteness at `r` is preserved under restriction
of scalars along a tower `A → B → C`. -/
theorem toQuasiFiniteAt_of_restrictScalars (r : PrimeSpectrum C)
    (hAC : Algebra.QuasiFiniteAt A r.asIdeal) : Algebra.QuasiFiniteAt B r.asIdeal := by
  letI : Algebra.QuasiFiniteAt A r.asIdeal := hAC
  change Algebra.QuasiFinite B (Localization.AtPrime r.asIdeal)
  exact Algebra.QuasiFinite.of_restrictScalars A B (Localization.AtPrime r.asIdeal)

/-- Lemma 10.122.10: in a tower `A → B → C`, if `A → C` is quasi-finite at the prime `r` in the
source-facing sense of Definition `10.122.3`, then `B → C` is also quasi-finite at `r`. -/
theorem quasiFiniteAt_of_restrictScalars (r : PrimeSpectrum C)
    (hAC : Algebra.FiniteType.QuasiFiniteAt A C r.asIdeal) :
    Algebra.FiniteType.QuasiFiniteAt B C r.asIdeal := by
  refine ⟨?_, ?_⟩
  · letI : Algebra.FiniteType A C := hAC.finiteType
    exact Algebra.FiniteType.of_restrictScalars_finiteType A B C
  · letI : Algebra.QuasiFiniteAt A r.asIdeal := hAC.toQuasiFiniteAt
    exact toQuasiFiniteAt_of_restrictScalars r hAC.toQuasiFiniteAt

end
