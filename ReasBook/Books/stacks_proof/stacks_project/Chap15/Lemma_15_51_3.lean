import StacksProject_2024.Chap10.Lemma_10_124_3
import StacksProject_2024.Chap10.Lemma_10_97_6
import StacksProject_2024.Chap15.Lemma_15_18_2
import StacksProject_2024.Chap15.Lemma_15_51_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra IsLocalRing
open scoped TensorProduct

universe u

namespace FieldAlgebraProperty

/- Domain sampling pass:
- primary domain: permanence of formal-fiber conditions for properties of Noetherian algebras over
  fields;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `FieldAlgebraProperty`,
  `IsPRing`,
  `SatisfiesPPrimePairCondition`;
- best owner abstraction: `FieldAlgebraProperty`, with the transfer/locality axioms packaged by
  `HasPropertyA` and `HasPropertyB`, and the source-facing ring owner `IsPRing`; clause `(2)`
  should therefore be phrased on the theorem surface using the local `P`-ring owner
  `IsPRing P (Localization.AtPrime p.asIdeal)` rather than duplicating its prime-pair expansion;
- primitive data: the underlying predicate `P k A` together with the base-change and
  prime-localization laws;
- derived API: source-facing specializations and larger chapter packages built from those owner
  axioms.

Sampling note: the nearby local-fiber criterion `Lemma_15_51_2` is also phrased over the chapter
owner `FieldAlgebraProperty.HasPropertyB`. That owner is the right layer here as well, because
`FieldAlgebraProperty` depends on a chosen `k`-algebra structure, not just the underlying
commutative ring.

Source/core/bridge triage:
- `source-facing`: the quasi-finite transfer theorems for formal fibers and the resulting
  `isPRing_of_quasiFinite`;
- `core/canonical`: the owner classes `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`, and the ring owner `IsPRing`;
- `bridge/view`: the geometric-regularity specialization in `Lemma_15_50_3`.
-/

/-- A field-algebra property satisfies `(A)` if it is preserved by base change along finitely
generated extensions of the ground field. -/
class HasPropertyA (P : FieldAlgebraProperty) : Prop where
  /-- Base change of a Noetherian `k`-algebra along a finitely generated field extension preserves
  the property `P`. -/
  baseChange (k A K : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
      [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (K ⊗[k] A)

/-- A field-algebra property satisfies `(B)` if for every ground field `k`, the induced ring
property on Noetherian `k`-algebras can be checked on prime localizations. -/
class HasPropertyB (P : FieldAlgebraProperty) : Prop where
  /-- The prime-local criterion for `P` over the fixed base field `k`. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

end FieldAlgebraProperty

section

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyA] [P.HasPropertyB]

section QuasiFiniteAtPrime

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R']

omit [IsNoetherianRing R] in
/-- Helper for Lemma 15.51.3: the residue-field map induced by a finite type morphism is
essentially finite type. -/
private theorem residueField_extension_essFiniteType
    (q' : PrimeSpectrum R') :
    let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') q'
    Algebra.EssFiniteType q.asIdeal.ResidueField q'.asIdeal.ResidueField := by
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') q'
  -- First pass to the target residue field as an essentially finite type `R'`-algebra.
  let _ : Algebra.EssFiniteType R' q'.asIdeal.ResidueField := inferInstance
  -- Then compose with `R → R'`, and descend along the contracted residue-field map.
  let _ : Algebra.EssFiniteType R q'.asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp R R' q'.asIdeal.ResidueField
  exact
    Algebra.EssFiniteType.of_comp R q.asIdeal.ResidueField q'.asIdeal.ResidueField

/-- Helper for Lemma 15.51.3: if the target ring is Noetherian, then every fiber algebra over a
prime of the source is Noetherian as well. -/
private theorem fiber_isNoetherianRing
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing B]
    (p : PrimeSpectrum A) :
    IsNoetherianRing (p.asIdeal.Fiber B) := by
  -- Commute the tensor factors so the fiber is viewed as an essentially finite type `B`-algebra.
  let _ : Algebra.EssFiniteType B (B ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (B ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing B (B ⊗[A] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (B ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField B).toRingEquiv.symm

/-- Helper for Lemma 15.51.3: the completed localization `R̂_[p]` is Noetherian. -/
private theorem completedLocalizationAtPrime_isNoetherianRing
    (p : PrimeSpectrum R) :
    IsNoetherianRing (R̂_[p]) := by
  let _ : IsNoetherianRing (Localization.AtPrime p.asIdeal) := inferInstance
  -- Rewrite the completed localization into the canonical adic-completion owner.
  simpa [CompletedLocalizationAtPrime] using
    (adicCompletion_isNoetherianRing
      (R := Localization.AtPrime p.asIdeal)
      (I := maximalIdeal (Localization.AtPrime p.asIdeal)))

omit [P.HasPropertyB] in
/-- Helper for Lemma 15.51.3: axiom `(A)` base-changes the source formal fiber along the induced
residue-field extension `κ(q) → κ(q')`. -/
private theorem baseChanged_source_formalFiber_hasProperty
    (p : PrimeSpectrum R) (q' : PrimeSpectrum R')
    (hP :
      P (PrimeSpectrum.comap (algebraMap R R') q').asIdeal.ResidueField
        ((PrimeSpectrum.comap (algebraMap R R') q').asIdeal.Fiber (R̂_[p]))) :
    P q'.asIdeal.ResidueField
      (q'.asIdeal.ResidueField ⊗[
        (PrimeSpectrum.comap (algebraMap R R') q').asIdeal.ResidueField]
        (PrimeSpectrum.comap (algebraMap R R') q').asIdeal.Fiber (R̂_[p])) := by
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') q'
  let _ : Algebra q.asIdeal.ResidueField q'.asIdeal.ResidueField := inferInstance
  let _ : IsNoetherianRing (R̂_[p]) :=
    completedLocalizationAtPrime_isNoetherianRing (R := R) p
  let _ : IsNoetherianRing (q.asIdeal.Fiber (R̂_[p])) :=
    fiber_isNoetherianRing (A := R) (B := R̂_[p]) q
  let _ : Algebra.EssFiniteType q.asIdeal.ResidueField q'.asIdeal.ResidueField := by
    -- Rewrite the contracted prime to the given source prime so the residue-field bridge matches
    -- the source formal fiber in the theorem statement.
    simpa [q] using residueField_extension_essFiniteType (R := R) (R' := R') q'
  -- Apply axiom `(A)` to the exact source formal fiber before any quasi-finite tensor transport.
  exact
    FieldAlgebraProperty.HasPropertyA.baseChange (P := P)
      q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) q'.asIdeal.ResidueField hP

/-- Helper for Lemma 15.51.3: after base changing the source formal fiber from `κ(q)` to `κ(q')`,
the canonical tensor-cancellation comparison rewrites it as the `q'`-fiber of the right-ordered
tensor product `R' ⊗[R] R̂_[p]`. -/
private noncomputable theorem source_formalFiber_baseChange_rightOrder_algEquiv
    (p : PrimeSpectrum R) (q : PrimeSpectrum R) (q' : PrimeSpectrum R')
    (hq : PrimeSpectrum.comap (algebraMap R R') q' = q) :
    q'.asIdeal.ResidueField ⊗[q.asIdeal.ResidueField] q.asIdeal.Fiber (R̂_[p]) ≃ₐ[
      q'.asIdeal.ResidueField] q'.asIdeal.Fiber (R' ⊗[R] R̂_[p]) := by
  let _ : Algebra q.asIdeal.ResidueField q'.asIdeal.ResidueField :=
    (Ideal.ResidueField.mapₐ q.asIdeal q'.asIdeal (Algebra.ofId R R')
      (by
        simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hq).symm)).toAlgebra
  -- First cancel the intermediate source residue field, then rewrite the result as the canonical
  -- `q'`-fiber of the right-ordered base change.
  exact
    (Algebra.TensorProduct.cancelBaseChange R q.asIdeal.ResidueField
      q'.asIdeal.ResidueField q'.asIdeal.ResidueField (R̂_[p])).trans
      (fiber_tensor_base_change_rightOrderAlgEquiv (R := R) (S := R̂_[p]) (R' := R') q').symm

/-- Helper for Lemma 15.51.3: quasi-finiteness at `p'` yields the same completed-local-ring
product decomposition after commuting the tensor factors to the right-ordered tensor product
`R' ⊗[R] R̂_[p]`. -/
private theorem exists_rightOrdered_completionTensorProduct_ringEquiv_completedLocalRing_prod
    (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal] :
    ∃ (B : Type u) (_ : CommRing B),
      Nonempty (R' ⊗[R] R̂_[p] ≃+* (R̂_[p'] × B)) := by
  -- Reuse Lemma `10.124.3` on the left-ordered tensor product and commute the tensor factors.
  rcases
      exists_completionTensorProduct_algEquiv_completedLocalRing_prod
        (R := R) (S := R') (q := p'.asIdeal) with
    ⟨B, _, _, e, -, -⟩
  refine ⟨B, inferInstance, ?_⟩
  refine ⟨?_⟩
  -- The first factor of the quasi-finite split is exactly the completed localization `R̂_[p']`.
  simpa [CompletedLocalizationAtPrime, hp] using
    (Algebra.TensorProduct.comm R R' (R̂_[p])).toRingEquiv.trans e.toRingEquiv

-- Proof sketch: use quasi-finiteness at `p'` to identify `R̂_[p] ⊗[R] R'` with a product whose
-- first factor is `R̂_[p']`. After tensoring with `κ(q')`, the target formal fiber is therefore a
-- direct factor of the base change of the source formal fiber along `κ(q) → κ(q')`. Apply
-- property `(A)` to obtain `P` after base change and property `(B)` to descend `P` from the
-- product ring to the direct factor.
/-- Lemma 15.51.3 (1): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
`q' ⊆ p'` lies over `q`, the map is quasi-finite at `p'`, and the formal fibre
`(R_p)^∧ ⊗[R] κ(q)` has property `P`, then the formal fibre `(R'_(p'))^∧ ⊗[R'] κ(q')` also has
property `P`. -/
@[stacks 0BIT]
theorem completed_localization_formalFiber_hasProperty_of_quasiFiniteAt
    (p q : PrimeSpectrum R) (p' q' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    (hq : PrimeSpectrum.comap (algebraMap R R') q' = q)
    (hqp' : q'.asIdeal ≤ p'.asIdeal)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) :
    P q'.asIdeal.ResidueField (q'.asIdeal.Fiber (R̂_[p'])) := by
  -- Route correction: the source proof first sets up the Noetherian fiber algebras needed for
  -- axioms `(A)` and `(B)`, and only then transports across the quasi-finite completion
  -- decomposition. The remaining blocker is that this file still lacks the source-faithful
  -- transport lemmas across the canonical algebra equivalences.
  let _ : IsNoetherianRing (R̂_[p]) :=
    completedLocalizationAtPrime_isNoetherianRing (R := R) p
  let _ : IsNoetherianRing (q.asIdeal.Fiber (R̂_[p])) :=
    fiber_isNoetherianRing (A := R) (B := R̂_[p]) q
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  let _ : IsNoetherianRing (R̂_[p']) :=
    completedLocalizationAtPrime_isNoetherianRing (R := R') p'
  let _ : IsNoetherianRing (q'.asIdeal.Fiber (R̂_[p'])) :=
    fiber_isNoetherianRing (A := R') (B := R̂_[p']) q'
  have hbase :
      P q'.asIdeal.ResidueField
        (q'.asIdeal.ResidueField ⊗[q.asIdeal.ResidueField] q.asIdeal.Fiber (R̂_[p])) :=
    baseChanged_source_formalFiber_hasProperty (P := P) (R := R) (R' := R') p q' <| by
      simpa [hq] using hP
  have hsource_right :
      q'.asIdeal.ResidueField ⊗[q.asIdeal.ResidueField] q.asIdeal.Fiber (R̂_[p]) ≃ₐ[
        q'.asIdeal.ResidueField] q'.asIdeal.Fiber (R' ⊗[R] R̂_[p]) :=
    source_formalFiber_baseChange_rightOrder_algEquiv
      (R := R) (R' := R') p q q' hq
  rcases
      exists_rightOrdered_completionTensorProduct_ringEquiv_completedLocalRing_prod
        (R := R) (R' := R') p p' hp with
    ⟨B, _, hsplit⟩
  -- TODO: follow the source route through the quasi-finite completion splitting
  -- `R' ⊗[R] R̂_[p] ≃ R̂_[p'] × B`, identify its `q'`-fiber with the base change of the source
  -- formal fiber via `hsource_right`, and then descend to the first product factor using
  -- property `(B)`. The remaining structural blocker is still the same: both the right-ordered
  -- fiber comparison `hsource_right` and the quasi-finite split `hsplit` are equivalences, but the
  -- current owner API for a generic `FieldAlgebraProperty` has no theorem transporting `P` across
  -- ring/algebra equivalences, so the source-faithful endgame cannot yet be formalized.
  sorry

-- Proof sketch: view the hypothesis as saying that the local ring `R_p` is a `P`-ring. For a
-- prime `q'` of `R'_(p')`, let `q` be its image in `R_p`, equivalently in `R`. The `P`-ring
-- hypothesis on `R_p` gives `P` on the source formal fiber over `q`, and clause (1) transfers
-- that property to the formal fiber over `q'`.
/-- Lemma 15.51.3 (2): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
the map is quasi-finite at `p'`, and every formal fibre of `R_p` has `P`, then every formal fibre
of `R'_(p')` has `P`. -/
@[stacks 0BIT]
theorem completed_localization_formalFibers_haveProperty_of_quasiFiniteAt
    (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : IsPRing P (Localization.AtPrime p.asIdeal)) :
    IsPRing P (Localization.AtPrime p'.asIdeal) := by
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  -- Repackage the local `P`-ring hypothesis as the prime-pair criterion on `R_p`.
  refine (isPRing_localizationAtPrime_iff (P := P) p').2 ?_
  intro q' hq'
  let q : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') q'
  have hq : PrimeSpectrum.comap (algebraMap R R') q' = q := rfl
  -- The inclusion `q' ≤ p'` descends to the corresponding inclusion `q ≤ p`.
  have hqp : q ≤ p := by
    rw [← hp, ← hq]
    exact Ideal.comap_mono (f := algebraMap R R') hq'
  -- Clause (1) transfers the source formal-fiber property at `q ≤ p` to the target one.
  have hsource : P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) :=
    (isPRing_localizationAtPrime_iff (P := P) p).1 hP q hqp
  exact
    completed_localization_formalFiber_hasProperty_of_quasiFiniteAt
      (P := P) p q p' q' hp hq hq' hsource

end QuasiFiniteAtPrime

section QuasiFinite

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R'] [Algebra.QuasiFinite R R']

-- Proof sketch: finite type over the Noetherian ring `R` makes `R'` Noetherian. For each prime
-- `p'` of `R'`, let `p` be its image in `R`. The hypothesis that `R` is a `P`-ring gives that
-- the local ring `R_p` is a `P`-ring, and clause (2) transfers that owner statement to the local
-- ring `R'_(p')`.
/-- Lemma 15.51.3 (3): if `R → R'` is quasi-finite and `R` satisfies the `P`-ring formal-fibre
condition, then `R'` also satisfies the `P`-ring formal-fibre condition. -/
@[stacks 0BIT]
theorem isPRing_of_quasiFinite
    (hP : IsPRing P R) :
    IsPRing P R' := by
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  -- Expand the target `P`-ring statement to the prime-pair formulation on `R'`.
  refine (isPRing_iff_satisfiesPPrimePairCondition (P := P) (R := R')).2 ?_
  intro p' q' hq'
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  have hp : PrimeSpectrum.comap (algebraMap R R') p' = p := rfl
  -- First localize the source `P`-ring hypothesis at `p`.
  have hlocal : IsPRing P (Localization.AtPrime p.asIdeal) := by
    refine (isPRing_localizationAtPrime_iff (P := P) p).2 ?_
    intro q hqp
    exact
      (isPRing_iff_satisfiesPPrimePairCondition (P := P) (R := R)).1 hP p q hqp
  -- Then apply clause (2) to transfer the entire local formal-fiber condition to `R'_(p')`.
  have hlocal' : IsPRing P (Localization.AtPrime p'.asIdeal) :=
    completed_localization_formalFibers_haveProperty_of_quasiFiniteAt
      (P := P) p p' hp hlocal
  -- Finally read off the specific target prime `q' ≤ p'`.
  exact (isPRing_localizationAtPrime_iff (P := P) p').1 hlocal' q' hq'

end QuasiFinite

end
