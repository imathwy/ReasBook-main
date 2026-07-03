import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap15.Definition_15_41_1
import StacksProject_2024.Chap15.Lemma_15_51_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

namespace FieldAlgebraProperty

/- Domain sampling pass:
- primary domain: Chapter 15 formal-fiber permanence axioms for `FieldAlgebraProperty`;
- sampled owner declarations:
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `IsPRing`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: `FieldAlgebraProperty`, with the reusable axioms `(C)` and `(D)` owned
  as inferable classes, matching the existing owner form for `(A)` and `(B)`;
- primitive data: the field-algebra predicate `P` together with the regular-ascent and faithfully
  flat local-descent laws on fibers, plus the local formal-fiber predicate itself;
- derived API: the maximal-ideal criterion for `IsPRing`.

Source/core/bridge triage:
- `source-facing`: `LocalFormalFibersHaveProperty` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- `core/canonical`: `P.HasPropertyC` and `P.HasPropertyD`;
- `bridge/view`: none needed.
-/

section

/-- A field-algebra property has property `(C)` if it ascends along regular morphisms on fibers of
flat maps of Noetherian rings. -/
class HasPropertyC (P : FieldAlgebraProperty) : Prop where
  /-- Property `(C)` ascends from the fibers of `A → B` to the fibers of `A → C` when `A → B` is
  flat and `B → C` is regular. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).IsRegularRingMap]
      (hB : ∀ q : PrimeSpectrum A, P q.asIdeal.ResidueField (q.asIdeal.Fiber B))
      (q : PrimeSpectrum A) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- A field-algebra property has property `(D)` if it descends along faithfully flat local
extensions on closed fibers of Noetherian local rings. -/
class HasPropertyD (P : FieldAlgebraProperty) : Prop where
  /-- Property `(D)` descends from the closed fiber over `A → C` to the closed fiber over `A → B`
  along a faithfully flat local extension `B → C`. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

end

end FieldAlgebraProperty

section

/-- A local ring has formal fibers with property `P` if every fiber of its completion map to the
maximal-ideal adic completion has property `P`. -/
abbrev LocalFormalFibersHaveProperty
    (P : FieldAlgebraProperty) (A : Type u) [CommRing A] [IsLocalRing A] :
    Prop :=
  ∀ q : PrimeSpectrum A,
    P q.asIdeal.ResidueField (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

-- Proof sketch: the forward implication is the specialization of the `P`-ring condition to the
-- maximal prime `m`. For the converse, fix `p : Spec(R)` and choose a maximal ideal `m ⊇ p`.
-- The hypothesis gives `P` on the fibers of `R_m → (R_m)^∧`. After choosing a prime of
-- `(R_m)^∧` over `pR_m` using faithful flatness of completion, apply Proposition `15.50.6` and
-- Lemma `15.41.4` to obtain a regular map from `(R_m)^∧` to the relevant completed localization,
-- then use `(C)` to transfer `P` to those fibers and `(D)` to descend from that faithfully flat
-- local extension to the fibers of `R_p → (R_p)^∧`.
/-- Lemma 15.51.4: let `R` be a Noetherian ring, and assume the field-algebra property `P`
satisfies `(C)` and `(D)`. Then `R` is a `P`-ring if and only if, for every maximal ideal `m` of
`R`, the local ring `R_m` has formal fibers with property `P`. -/
theorem isPRing_iff_localFormalFibersHaveProperty_atMaximal
    (P : FieldAlgebraProperty)
    [P.HasPropertyC] [P.HasPropertyD] :
    IsPRing P R ↔
      ∀ m : MaximalSpectrum R,
        LocalFormalFibersHaveProperty P (Localization.AtPrime m.asIdeal) := sorry

end
