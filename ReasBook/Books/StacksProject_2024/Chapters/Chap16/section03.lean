import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_16_3_1 (from Chap16) -/
open scoped TensorProduct

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

local notation:max "C[" a "]" => Localization.Away ((IsScalarTower.toAlgHom R A C) a)

noncomputable local instance localizedAwayAlgebra (a : A) :
    Algebra (Localization.Away a) C[a] :=
  (Localization.awayMapₐ (IsScalarTower.toAlgHom R A C) a).toAlgebra

-- Proof sketch: choose the symmetric algebra `C = Sym_A^*(I/I²)` for a finite presentation of
-- `A` over `R`. Its degree-zero projection gives the retraction. The localized Jacobi-Zariski
-- sequence and the local complete intersection hypothesis make the localized conormal module free,
-- yielding smoothness over `A_a`; when `A_a` is already smooth over `R`, the localized Kähler
-- differentials of `C_a` become free as well.
/-- Lemma 16.3.1: if `A` is a finitely presented `R`-algebra, there exists a finite type
`A`-algebra `C` together with an `A`-algebra retraction `C → A` such that for every `a : A` with
`R → A_a` a local complete intersection, the localization `C_a` is smooth over `A_a` and admits a
finite generator family over `R` whose cotangent module is free; this can be upgraded to a finite
presentation with free conormal module by
`Algebra.Generators.exists_presentation_of_free_cotangent`. For every `a : A` with `A_a` smooth
over `R`, the module `Ω[C_a⁄R]` is free over `C_a`. -/
theorem exists_finiteType_retraction_with_smoothing_localizations :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Algebra.FiniteType A C) (r : C →ₐ[A] A),
      (∀ a : A,
        (algebraMap R (Localization.Away a)).IsLocalCompleteIntersection →
          Smooth (Localization.Away a) C[a] ∧
            ∃ n : ℕ, ∃ P : Generators R C[a] (Fin n),
              Module.Free C[a] P.toExtension.Cotangent) ∧
      ∀ a : A,
        Smooth R (Localization.Away a) →
          Module.Free C[a] Ω[C[a]⁄R] := sorry

end

end

end Algebra

/-! ### Proposition_16_3_2 (from Chap16) -/
universe u v

namespace Algebra

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A₀ : Type v} [CommRing A₀] [Algebra (R ⧸ I) A₀]

/- Domain-style sampling for lifting smooth and syntomic quotient algebras:
* primary domain: commutative algebra of smooth and syntomic ring maps over quotient rings;
* core/canonical owners: `RingHom.Syntomic` for clause `(1)` and `Smooth (R ⧸ I) A₀` for
  clause `(2)`;
* relevant upstream declarations inspected for this owner choice:
  `RingHom.Syntomic` in `Definition_10_136_1`,
  `Algebra.Smooth` in mathlib `RingTheory/Smooth/Basic`,
  the local quotient lifting criterion `smooth_exists_lift_of_quotient_by_locally_nilpotent`
  in `Lemma_10_138_17`,
  and the quotient lift cover statements
  `exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic` and
  `exists_standardSmooth_lift_cover_of_quotient_smooth` in Chapter 10.

Source/core/bridge triage:
* `source-facing`: the two existence theorems below, matching Proposition `16.3.2`;
* `core/canonical`: the owner predicates `RingHom.Syntomic` and `Smooth`;
* `bridge/view`: the reduction comparison
  `(A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀`.

Primitive data are only the quotient ideal `I` and the quotient algebra `A₀` with its canonical
owner hypothesis. The reduction isomorphism is derived bridge data, so no additional wrapper
structure is introduced here.
-/

-- Proof sketch: use the local complete intersection description of syntomic algebras over the
-- quotient `R ⧸ I`, lift a suitable complete-intersection presentation to a syntomic `R`-algebra,
-- and then shrink near `V (IA)` so that the reduction modulo `I` remains isomorphic to `A₀`.
/-- Proposition 16.3.2 (1): every syntomic algebra over the quotient ring `R ⧸ I` lifts to a
syntomic `R`-algebra whose reduction modulo `I` is isomorphic to the given algebra. -/
theorem exists_syntomic_lift_of_quotient_syntomic
    (hA₀ : (algebraMap (R ⧸ I) A₀).Syntomic) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A)
      (_ : (algebraMap R A).Syntomic),
      Nonempty ((A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀) := sorry

-- Proof sketch: first apply clause `(1)` to obtain a syntomic lift over `R`; then use the
-- canonical owner theorem `smooth_syntomic` to view the quotient algebra as syntomic, and then
-- use the openness of the smooth locus to localize the resulting lift so that it becomes smooth
-- while preserving the reduction modulo `I`.
/-- Proposition 16.3.2 (2): every smooth algebra over the quotient ring `R ⧸ I` lifts to a smooth
`R`-algebra whose reduction modulo `I` is isomorphic to the given algebra. -/
theorem exists_smooth_lift_of_quotient_smooth [Smooth (R ⧸ I) A₀] :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Smooth R A),
      Nonempty ((A ⧸ Ideal.map (algebraMap R A) I) ≃ₐ[R ⧸ I] A₀) := sorry

end

end Algebra

/-! ### Lemma_16_3_3 (from Chap16) -/
universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/- Domain-style sampling:
- primary domain: syntomic ring maps, smooth retractions, and relative global complete
  intersections;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `exists_finiteType_retraction_with_smoothing_localizations`,
  `Algebra.Generators.exists_presentation_of_free_cotangent`;
- best owner abstraction:
  the ambient canonical owners are `RingHom.Syntomic` for `R → A` and
  `Algebra.IsRelativeGlobalCompleteIntersection R C` for the output algebra `C`; the localized
  free-cotangent presentations from Lemma `16.3.1` are bridge data used to construct the global
  complete-intersection owner and should not survive here as a parallel public wrapper;
- primitive vs. derived:
  this lemma exports only the smooth `A`-algebra retract and the canonical relative-global-complete
  intersection owner; finite presentation and local presentation data are derived API coming from
  those owners.

Source/core/bridge triage:
- `source-facing`: the existence of a smooth `A`-algebra retract `C` that is a relative global
  complete intersection over `R`;
- `core/canonical`: `RingHom.Syntomic` and `Algebra.IsRelativeGlobalCompleteIntersection`;
- `bridge/view`: `exists_finiteType_retraction_with_smoothing_localizations`, whose localized free
  cotangent presentations are converted into the source-facing owner below.
-/
-- Proof sketch: apply
-- `exists_finiteType_retraction_with_smoothing_localizations` to the syntomic map `R → A` to
-- obtain an `A`-algebra `C` with an `A`-algebra retraction such that `A → C` is smooth and the
-- localizations `C_a` admit free cotangent presentations over `R`. Then use
-- `Algebra.Generators.exists_presentation_of_free_cotangent` to replace those local presentations
-- by finite presentations whose defining equations map to bases of the corresponding conormal
-- modules, and apply Lemma `10.135.4` fiberwise to identify the fiber dimensions with the
-- presentation dimension.
/-- Lemma 16.3.3: if `R → A` is syntomic, then there exists an `A`-algebra `C` with an
`A`-algebra retraction `C → A` such that `A → C` is smooth and `C` is a relative global complete
intersection over `R`. The presentation-theoretic form of the last condition is packaged by the
owner `IsRelativeGlobalCompleteIntersection R C`, rather than by a separate local wrapper in this
file. -/
theorem exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic
    (hA : (algebraMap R A).Syntomic) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Smooth A C) (r : C →ₐ[A] A),
      IsRelativeGlobalCompleteIntersection R C := by
  letI : FinitePresentation R A :=
    RingHom.finitePresentation_algebraMap.mp hA.finitePresentation
  sorry

end

end Algebra

/-! ### Lemma_16_3_4 (from Chap16) -/
universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/- Domain-style sampling for smooth retractions with standard smooth targets:
* primary domain: smooth commutative algebra, syntomic factorization, and standard smooth
  presentations;
* sampled owner declarations:
  `Smooth R A`,
  `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic`,
  `Algebra.IsStandardSmooth`;
* best owner abstraction:
  the ambient owners are `Smooth R A` for the input algebra, the Chapter 16 retraction theorem
  `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic` for the retract data,
  and `Algebra.IsStandardSmooth R B` for the strengthened target conclusion;
* primitive vs. derived:
  the primitive public output is only the smooth `A`-algebra retract together with the standard
  smooth owner on the target. The syntomic upgrade and the relative-global-complete-intersection
  witness are bridge data from upstream owners and should not be repackaged here as a parallel
  local wrapper.

Source/core/bridge triage:
* `source-facing`: the existence of a smooth `A`-algebra retract `B` that is standard smooth over
  `R`;
* `core/canonical`: `Smooth`, `RingHom.Syntomic`, `Algebra.IsStandardSmooth`, and the Chapter 16
  retraction owner theorem;
* `bridge/view`: the intermediate relative-global-complete-intersection presentation obtained from
  syntomicity, together with the bridge theorem `smooth_syntomic` converting the input smoothness
  hypothesis into the syntomic hypothesis needed for that retraction theorem.
-/

-- Proof sketch: first apply the bridge theorem `smooth_syntomic` to view the smooth map `R → A`
-- as syntomic. Then invoke the Chapter 16 retraction theorem
-- `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic` to obtain a smooth
-- `A`-algebra retraction `A → B → A` with `B` a relative global complete intersection over `R`.
-- Finally apply the Stacks Jacobian argument to that retract presentation to promote the target to
-- the canonical owner `IsStandardSmooth R B`, while preserving the same retract shape over `A`.
/-- Lemma 16.3.4: if `R → A` is smooth, then there exists a smooth `R`-algebra map `A → B` with
an `A`-algebra retraction such that `B` is standard smooth over `R`. The presentation-theoretic
Jacobian data are carried canonically by the owner `IsStandardSmooth R B`, so they are not
repackaged here as separate public output. -/
theorem exists_smooth_retraction_standardSmooth_of_smooth [Smooth R A] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : IsScalarTower R A B) (_ : Smooth A B) (r : B →ₐ[A] A),
      IsStandardSmooth R B := sorry

end

end Algebra

/-! ### Lemma_16_3_5 (from Chap16) -/
open CategoryTheory MorphismProperty Limits
open CommRingCat

universe u

namespace RingHom

section

variable {R A : Type u} [CommRing R] [CommRing A]

/- Domain-style sampling for Lemma 16.3.5:
* primary domain: filtered colimits of smooth and standard smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the Chapter 10 source-facing owner for PT
    presentations;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `RingHom.toMorphismProperty`, the canonical bridge from a ring-hom property to a
    `CommRingCat` morphism property;
  - `RingHom.IsStandardSmooth`, the canonical owner for standard smoothness of a ring map.
* best owner abstraction: `(toMorphismProperty IsStandardSmooth).ind (ofHom f)`;
* primitive data: standard smoothness of each stage map;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism witnessing the
  filtered-colimit presentation.

Source/core/bridge triage:
* `source-facing`: the map `R → A` is a filtered colimit of standard smooth `R`-algebras;
* `core/canonical`: `(toMorphismProperty IsStandardSmooth).ind (ofHom f)`;
* `bridge/view`: a particular filtered diagram in `Under (CommRingCat.of R)` presenting `f`.

The previous local `CommRingCat.standardSmooth` abbreviation duplicated mathlib's canonical bridge
`RingHom.toMorphismProperty`, so the file now states the lemma directly at that owner level.
-/

-- Proof sketch: use Lemma `10.127.4` in the standard-smooth variant. Given a finitely presented
-- `R`-algebra mapping to `A`, factor the map through one of the smooth stages of the given
-- filtered colimit presentation, then apply Lemma `16.3.4` to replace that smooth stage by a
-- standard smooth `R`-algebra through which the map still factors.
/-- Lemma 16.3.5: if a ring map `R → A` is a filtered colimit of smooth `R`-algebras, then it is
a filtered colimit of standard smooth `R`-algebras. -/
theorem isFilteredColimitOfStandardSmooth_of_isFilteredColimitOfSmooth
    {f : R →+* A} (h : f.IsFilteredColimitOfSmooth) :
    (toMorphismProperty IsStandardSmooth).ind (ofHom f) := sorry

end

end RingHom

/-! ### Lemma_16_3_6 (from Chap16) -/
universe u v

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

section

variable {n : ℕ}

/- Domain-style sampling for standard smooth presentations with prescribed generators:
* primary domain: standard smooth commutative algebra and submersive presentations;
* sampled owner declarations:
  `Algebra.IsStandardSmooth.out`,
  `Algebra.SubmersivePresentation.reindex`,
  `Algebra.SubmersivePresentation.comp`,
  `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`;
* best owner abstraction:
  `Algebra.IsStandardSmooth` is the ambient owner providing a chosen `SubmersivePresentation`, and
  `SubmersivePresentation.reindex` is the canonical bridge for normalizing the distinguished
  Jacobian variables to a `Fin c`-summand;
* primitive vs. derived:
  the primitive source-facing data are the standard smooth owner, the chosen finite family
  `e : Fin n ↪ A`, and the distinguished variable-selection map `P.map`. The inequality
  `n ≤ c` is auxiliary bookkeeping used only to identify the first `n` distinguished variables
  inside the chosen owner `P`.

Source/core/bridge triage:
* source-facing: a standard smooth presentation of `A` in which a prescribed finite family of
  elements of `A` appears among the distinguished Jacobian generators;
* core/canonical owner: `Algebra.IsStandardSmooth` and `SubmersivePresentation`;
* bridge/view: the coordinate presentation indexed by `Fin c ⊕ Fin m` with
  `P.map = Sum.inl` is the canonical reindexing of an arbitrary `SubmersivePresentation` along the
  distinguished range of `P.map`.

Primitive data are the standard smooth owner, the chosen finite family `e : Fin n ↪ A`, and the
distinguished variables selected by the primitive field `P.map`. The index inequality `n ≤ c` is
derived only after choosing the canonical `P.map = Sum.inl` presentation and is used solely to
place the prescribed family inside the first `c` distinguished variables.
-/
-- Proof sketch: choose a submersive presentation of `A` over `R`, enumerate the prescribed finite
-- subset by `e : Fin n ↪ A`, lift those elements to polynomials in the chosen generators, and
-- adjoin new variables `x₁, …, xₙ` together with relations `xᵢ - hᵢ`. Reindex the resulting
-- submersive presentation so that the Jacobian variables are exactly the `Fin c`-summand. Then
-- the first `n` of those distinguished variables map to the chosen elements.
/-- Lemma 16.3.6: if `R → A` is standard smooth and `e : Fin n ↪ A` enumerates a finite subset
of cardinality `n`, then `A` admits a submersive presentation
`R[x₁, ..., x_{c + m}] / (f₁, ..., f_c)` whose distinguished Jacobian variables are the first
`c`, with `n ≤ c`, and whose first `n` distinguished generators map to the prescribed
elements `e i`. This is a bridge theorem on the canonical owner `Algebra.IsStandardSmooth`,
not a second owner abstraction. -/
theorem IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators
    [IsStandardSmooth R A] (e : Fin n ↪ A) :
    ∃ c m, ∃ P : SubmersivePresentation R A (Fin c ⊕ Fin m) (Fin c),
      P.map = Sum.inl ∧
        ∃ h : n ≤ c, ∀ i : Fin n, P.val (.inl (Fin.castLE h i)) = e i := sorry

end

end Algebra

/-! ### Lemma_16_3_7 (from Chap16) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

local notation:max "A[" a "]" => Localization.Away a

/- Domain-style sampling for local smoothness criteria in finitely presented commutative algebra:
* primary domain: standard smooth localizations, Kähler differentials, and the Chapter 16
  predicates `IsElementaryStandard` and `IsStrictlyStandard`;
* sampled owner declarations:
  `Algebra.IsStandardSmooth`,
  `IsStandardSmooth.smooth`,
  `IsStandardSmooth.free_kaehlerDifferential`,
  `Module.StablyFree`;
* best owner abstraction:
  `Algebra.IsStandardSmooth` and `Smooth` are the canonical owners for the localized algebra
  `A[a]`, while `Module.StablyFree` is the chapter owner for the stable-freeness clause on
  `Ω[A[a]⁄R]`; the predicates `IsElementaryStandard` and `IsStrictlyStandard` remain the
  source-facing conditions on `a`;
* primitive vs. derived:
  the primitive source-facing data are only the two Chapter 16 predicates on `a`. Standard
  smoothness and smoothness of `A[a]`, together with freeness or stable freeness of `Ω[A[a]⁄R]`,
  are derived owner-level consequences and should be stated directly through those owners rather
  than repackaged in a local wrapper.

Source/core/bridge triage:
* `source-facing`: the six conditions in Stacks Lemma 16.3.7 on a single element `a : A`;
* `core/canonical`: `Algebra.IsStandardSmooth`, `Smooth`, `Module.Free`, and `Module.StablyFree`
  for the localized algebra and its Kähler differentials;
* `bridge/view`: the Chapter 16 predicates `IsElementaryStandard` and `IsStrictlyStandard`
  translate presentation-level Jacobian conditions into those canonical owner conclusions.
-/

-- Proof sketch for Lemma 16.3.7 (a), implication `(4) ⇒ (3)`: this is the direct source-facing
-- conjunction of the canonical owner consequences
-- `IsStandardSmooth.free_kaehlerDifferential` and `[IsStandardSmooth R A_a] : Smooth R A_a`.
/-- Lemma 16.3.7 (a), implication `(4) ⇒ (3)`: if `A_a` is standard smooth over `R`, then `A_a`
is smooth over `R` and its module of Kähler differentials is free. -/
theorem standardSmoothAway_implies_freeKaehler
    (a : A) (h : IsStandardSmooth R A[a]) :
    Smooth R A[a] ∧ Module.Free A[a] Ω[A[a]⁄R] := by
  let _ : IsStandardSmooth R A[a] := h
  exact ⟨inferInstance, inferInstance⟩

-- Proof sketch for Lemma 16.3.7 (a), implication `(3) ⇒ (2)`: this is the direct owner-level
-- upgrade from `Module.Free` to `Module.StablyFree`, via the canonical instance
-- `Module.stablyFree_of_free`, together with the unchanged smoothness hypothesis.
/-- Lemma 16.3.7 (a), implication `(3) ⇒ (2)`: if `A_a` is smooth over `R` and `Ω[(A_a)/R]` is
free, then `A_a` is smooth over `R` and `Ω[(A_a)/R]` is stably free. -/
theorem freeKaehlerAway_implies_stablyFreeKaehler
    (a : A) (hsmooth : Smooth R A[a]) (hfree : Module.Free A[a] Ω[A[a]⁄R]) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := by
  let _ : Module.Free A[a] Ω[A[a]⁄R] := hfree
  exact ⟨hsmooth, inferInstance⟩

-- Proof sketch for Lemma 16.3.7 (a), implication `(2) ⇒ (1)`: this is the tautological
-- projection from condition `(2)` to its smoothness component.
/-- Lemma 16.3.7 (a), implication `(2) ⇒ (1)`: condition `(2)` implies that `A_a` is smooth over
`R`. -/
theorem stablyFreeKaehlerAway_implies_smooth
    (a : A) (h : Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R]) :
    Smooth R A[a] := h.1

-- Proof sketch for Lemma 16.3.7 (b), implication `(6) ⇒ (5)`: an elementary standard element is,
-- by definition, a special case of a strictly standard element using a single leading Jacobian
-- determinant.
/-- Lemma 16.3.7 (b), implication `(6) ⇒ (5)`: every elementary standard element of `A` over `R`
is strictly standard. -/
theorem isElementaryStandard_implies_isStrictlyStandard
    (a : A) (h : IsElementaryStandard R a) :
    IsStrictlyStandard R a := sorry

-- Proof sketch for Lemma 16.3.7 (c), implication `(6) ⇒ (4)`: starting from an elementary
-- standard presentation, adjoin an inverse to the chosen Jacobian determinant and rewrite the
-- localization as a standard smooth presentation.
/-- Lemma 16.3.7 (c), implication `(6) ⇒ (4)`: if `a` is elementary standard in `A` over `R`,
then the localization `A_a` is standard smooth over `R`. -/
theorem isElementaryStandard_implies_standardSmoothAway
    (a : A) (h : IsElementaryStandard R a) :
    IsStandardSmooth R A[a] := sorry

-- Proof sketch for Lemma 16.3.7 (d), implication `(5) ⇒ (2)`: a strictly standard presentation
-- gives a smooth localization, and the conormal sequence shows that `Ω[(A_a)/R]` is a direct
-- summand of a finite free module, hence stably free.
/-- Lemma 16.3.7 (d), implication `(5) ⇒ (2)`: if `a` is strictly standard in `A` over `R`, then
`A_a` is smooth over `R` and `Ω[(A_a)/R]` is stably free. -/
theorem isStrictlyStandard_implies_stablyFreeKaehlerAway
    (a : A) (h : IsStrictlyStandard R a) :
    Smooth R A[a] ∧ Module.StablyFree A[a] Ω[A[a]⁄R] := sorry

section

variable [FinitePresentation R A]

-- Proof sketch for Lemma 16.3.7 (e): choose a finite presentation of `A` over `R`, stabilize the
-- conormal module so it becomes free after adjoining dummy variables, and then use the Jacobian
-- criterion to obtain that all sufficiently large powers of `a` are strictly standard.
/-- Lemma 16.3.7 (e): if condition `(2)` holds, then there exists `e0` such that every power
`a^e` with `e ≥ e0` is strictly standard in `A` over `R`. -/
theorem stablyFreeKaehlerAway_eventually_strictlyStandard_pow
    (a : A) (hsmooth : Smooth R A[a]) (hstablyFree : Module.StablyFree A[a] Ω[A[a]⁄R]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → IsStrictlyStandard R (a ^ e) := sorry

-- Proof sketch for Lemma 16.3.7 (f): from a standard smooth presentation of `A_a`, clear
-- denominators in the chosen generators and defining equations to descend to a presentation of
-- `A`; for all sufficiently large powers of `a`, the Jacobian determinant and tail
-- ideal-membership conditions then witness elementary standardness.
/-- Lemma 16.3.7 (f): if condition `(4)` holds, then there exists `e0` such that every power
`a^e` with `e ≥ e0` is elementary standard in `A` over `R`. -/
theorem standardSmoothAway_eventually_elementaryStandard_pow
    (a : A) (h : IsStandardSmooth R A[a]) :
    ∃ e0 : ℕ, ∀ e : ℕ, e0 ≤ e → IsElementaryStandard R (a ^ e) := sorry

end

end

end Algebra
