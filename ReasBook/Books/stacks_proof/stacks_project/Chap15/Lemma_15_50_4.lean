import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_18_6
import stacks_proof.stacks_project.Chap10.Lemma_10_159_3
import stacks_proof.stacks_project.Chap10.Lemma_10_166_1
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_8
import stacks_proof.stacks_project.Chap15.Lemma_15_18_2
import stacks_proof.stacks_project.Chap15.Lemma_15_50_2
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Lemma_15_51_1
import stacks_proof.stacks_project.Chap15.Lemma_15_51_3

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.50.4: geometric regularity packaged as a Chapter 15 field-algebra
property, without importing the heavier `G`-ring bridge module. -/
abbrev Algebra.IsGeometricallyRegularPropertyForGRing : FieldAlgebraProperty :=
  Algebra.IsGeometricallyRegularProperty

/-- Helper for Lemma 15.50.4: geometric regularity satisfies the Chapter 15 base-change axiom
`(A)` for the local property package used in this file. -/
instance isGeometricallyRegularPropertyForGRing_hasPropertyA :
    Algebra.IsGeometricallyRegularPropertyForGRing.HasPropertyA :=
  inferInstance

/-- Helper for Lemma 15.50.4: geometric regularity satisfies the Chapter 15 localization axiom
`(B)` for the local property package used in this file. -/
instance isGeometricallyRegularPropertyForGRing_hasPropertyB :
    Algebra.IsGeometricallyRegularPropertyForGRing.HasPropertyB :=
  inferInstance

/-- Helper for Lemma 15.50.4: the `G`-ring owner is equivalent to the `P`-ring owner specialized
to geometric regularity of formal fibers. -/
theorem isGRing_iff_isPRing_isGeometricallyRegularPropertyForGRing :
    IsGRing R ↔ IsPRing Algebra.IsGeometricallyRegularPropertyForGRing R := by
  -- Reuse the canonical bridge from Lemma `15.50.2`; this file only needs a thin local alias.
  simpa [Algebra.IsGeometricallyRegularPropertyForGRing] using
    (isGRing_iff_isPRing_isGeometricallyRegularProperty (R := R))

/-- Helper for Lemma 15.50.4: the `G`-ring condition can be tested on prime-pair formal fibers
via geometric regularity. -/
theorem isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular_local
    [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ p q : PrimeSpectrum R, ∀ _hqp : q.asIdeal ≤ p.asIdeal,
        IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := by
  -- Reuse the canonical prime-pair criterion from Lemma `15.50.2`.
  simpa using
    (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular (R := R))

/-- Helper for Lemma 15.50.4: if every finite free `R`-algebra has regular formal fibers, then
`R` is a `G`-ring. -/
private theorem isGRing_of_forall_finiteFree_formalFibers_regular
    [IsNoetherianRing R]
    (hfiniteFree :
      ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
        (p q : PrimeSpectrum S) (_hqp : q.asIdeal ≤ p.asIdeal),
          IsRegularRing (q.asIdeal.Fiber (R̂_[p]))) :
    IsGRing R := by
  -- Follow the source proof through the prime-pair criterion for `G`-rings.
  refine (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular_local (R := R)).2 ?_
  intro p q hqp
  -- Then unpack geometric regularity into the finite purely inseparable tensor test.
  rw [Algebra.isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
  intro L _ _ _ _
  -- Realize the residue-field extension by a finite free `R`-algebra as in the source proof.
  obtain ⟨S, _, _, _, _, hS⟩ :=
    exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv
      (p := q.asIdeal) L
  classical
  dsimp at hS
  rcases hS with ⟨hqprime, hqover, hL⟩
  let q' : PrimeSpectrum S := ⟨q.asIdeal.map (algebraMap R S), hqprime⟩
  have hq'q : q'.asIdeal = q.asIdeal.map (algebraMap R S) := rfl
  -- Route correction: keep the source-faithful decomposition route. The next step is to identify
  -- `L ⊗[κ(q)] q.Fiber (R̂_[p])` with the `q'`-fiber of `R̂_[p] ⊗[R] S`, then transport through
  -- `completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion S p` and analyze the
  -- resulting branch factors over `p.asIdeal.primesOver S`.
  -- TODO: use `baseChanged_sourceFiber_algEquiv_rightOrderedFiber` from Lemma `15.18.2` together
  -- with the residue-field equivalence `hL`, then prove that the `q'`-fiber of the product
  -- decomposition is regular because the `q' ≤ p'` branches are covered by `hfiniteFree` and the
  -- remaining branches vanish after tensoring with `κ(q')`.
  let _ := hfiniteFree
  let _ := hqover
  let _ := hL
  let _ := hq'q
  sorry

/- Domain triage:
- primary domain: `G`-rings and regularity of formal fibres under finite free base change;
- sampled owner declarations:
  `Ideal.Fiber`,
  `IsGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`,
  `isGRing_of_finiteType`,
  `exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv`;
- best owner abstraction: the chapter owner `IsGRing`, with the source-facing finite-free
  regular-formal-fibre criterion as the theorem surface and the canonical fiber owner
  `Ideal.Fiber`; Lemma `15.50.2` is only the bridge to geometric regularity;
- primitive data: the Noetherian ring `R` and a finite free `R`-algebra `S`;
- derived API: the owner-level companion criterion `IsGRing S`.

Layering:
- the numbered lemma is `source-facing`;
- `IsGRing` is the `core/canonical` owner;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/
-- Proof sketch: for the forward implication, finite free algebras are finite type, so the
-- source-facing finite-type transfer theorem `isGRing_of_finiteType` makes every such algebra a
-- `G`-ring; Lemma
-- `15.50.2` then upgrades each formal fibre to geometric regularity, hence to ordinary
-- regularity. Conversely, to prove that `R` is a `G`-ring it is enough by Lemma `15.50.2` to show
-- geometric regularity of each formal fibre of `R`. By Definition `10.166.2`, that geometric
-- regularity is tested after finite purely inseparable residue-field extensions, and
-- `exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv` realizes those extensions by
-- finite free algebras. The resulting formal fibres of the finite free algebra localize the
-- corresponding tensor base changes of the original formal fibre, so the assumed regularity of all
-- finite-free formal fibres forces the needed geometric regularity.
/-- Lemma 15.50.4: for a Noetherian commutative ring `R`, `R` is a `G`-ring if and only if every
finite free `R`-algebra has regular formal fibre rings. -/
@[stacks 07PQ]
  theorem isGRing_iff_forall_finiteFree
    [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
        (p q : PrimeSpectrum S) (_hqp : q.asIdeal ≤ p.asIdeal),
          IsRegularRing (q.asIdeal.Fiber (R̂_[p])) := by
  constructor
  · intro hR S _ _ _ _ p q hqp
    let hPR : IsPRing Algebra.IsGeometricallyRegularPropertyForGRing R :=
      (isGRing_iff_isPRing_isGeometricallyRegularPropertyForGRing (R := R)).1 hR
    let hPS : IsPRing Algebra.IsGeometricallyRegularPropertyForGRing S :=
      isPRing_of_quasiFinite (P := Algebra.IsGeometricallyRegularPropertyForGRing) hPR
    have hgeom : IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := by
      exact
        (isPRing_iff_satisfiesPPrimePairCondition
          (P := Algebra.IsGeometricallyRegularPropertyForGRing) (R := S)).1 hPS p q hqp
    letI : IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := hgeom
    exact
      Algebra.isRegularRing_of_isGeometricallyRegular
        q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))
  · intro hfiniteFree
    exact isGRing_of_forall_finiteFree_formalFibers_regular (R := R) hfiniteFree

end
