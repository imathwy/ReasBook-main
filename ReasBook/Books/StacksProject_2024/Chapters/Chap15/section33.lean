import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_33_1 (from Chap15) -/
universe u v

open Algebra

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace Algebra.Generators

/- Domain triage:
- primary domain: finite polynomial presentations of commutative algebras and presentation
  independence of local complete intersection kernels;
- sampled owner declarations: `Algebra.Generators.defaultHom`,
  `Algebra.Generators.presentation_cotangent_stable_equiv`,
  `Ideal.IsKoszulRegularIdeal`, and
  `RingTheory.Sequence.isKoszulRegularSequence_of_span_eq`;
- best owner abstraction: the primitive data are the two finite presentation owners
  `P : Generators A B ι` and `Q : Generators A B κ`; the kernel ideals are derived fields of
  those owners, so the independence statement belongs on `Algebra.Generators` rather than as a
  parallel global wrapper;
- primitive vs. derived: `P` and `Q` are primitive public data, while `P.ker`, `Q.ker`, and the
  resulting ring-hom notion of Definition `15.33.2` are derived from that owner data;
- layer triage:
  - `source-facing`: the theorem below asserting that Koszul-regularity of the kernel does not
    depend on the chosen finite presentation;
  - `core/canonical`: `Algebra.Generators`;
  - `bridge/view`: the stable cotangent comparison of Lemma `10.134.15` and the sequence-transfer
    lemmas `15.30.13` through `15.30.15`. -/

-- Proof sketch: compare the two presentations by adjoining both sets of variables and mapping the
-- extra variables to chosen polynomial lifts. The kernel of the combined presentation is generated
-- both by the first kernel together with the new variable differences and by the second kernel
-- together with the opposite variable differences. Lemma `10.134.15` gives the equality of the
-- local conormal ranks, Lemma `15.30.15` transfers Koszul-regularity between generating sequences
-- of the same length for the same ideal, and Lemmas `15.30.13` and `15.30.14` add and then remove
-- the obvious regular variable-difference sequences. Any auxiliary reindexing to `Fin` belongs
-- only inside that proof bridge via `Fintype.ofFinite` and `Fintype.equivFin`, not in the public
-- theorem statement.
/-- Lemma 15.33.1: for two finite polynomial presentations of the same `A`-algebra `B`, the
kernel ideal of one presentation is Koszul-regular if and only if the kernel ideal of the other
presentation is Koszul-regular. Equivalently, Koszul-regularity of the kernel is independent of
the chosen finite presentation. -/
theorem ker_isKoszulRegularIdeal_iff {ι κ : Type*} [Finite ι] [Finite κ]
    (P : Generators A B ι) (Q : Generators A B κ) :
    P.ker.IsKoszulRegularIdeal ↔ Q.ker.IsKoszulRegularIdeal := sorry

end Algebra.Generators

end

/-! ### Definition_15_33_2 (from Chap15) -/
universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/- Domain triage:
- primary domain: commutative algebra of local complete intersection ring maps via finite
  polynomial presentations;
- sampled owner declarations: `Ideal.IsKoszulRegularIdeal`, `Algebra.Generators`,
  `RingHom.Syntomic`, and Chapter 10's field-fiber owner `IsLocalCompleteIntersection`;
- layer: `source-facing`; this file owns the general ring-hom notion, while `RingHom.Syntomic`
  is the flatter/fiberwise core notion used later and the Chapter 10 field-algebra definition
  controls fibers only;
- primitive vs derived split: the primitive data are a finite generator presentation together with
  Koszul-regularity of its kernel ideal, while finite type is derived API and should not be stored
  as primitive owner data. -/

/-- Definition 15.33.2: a ring map `f : A →+* B` is a local complete intersection if for some
finite family of generators of `B` over `A`, the kernel ideal of the induced polynomial
presentation `A[x₁, …, xₙ] → B` is Koszul-regular. This is the Stacks-project presentation
criterion, whose finite generation of variables already encodes the finite-type hypothesis. -/
class IsLocalCompleteIntersection (f : A →+* B) : Prop where
  exists_generators_ker_isKoszulRegular :
    let _ : Algebra A B := f.toAlgebra
    ∃ n : ℕ, ∃ P : Algebra.Generators A B (Fin n),
      P.ker.IsKoszulRegularIdeal

namespace IsLocalCompleteIntersection

/-- A local complete intersection ring map is of finite type. -/
theorem finiteType {f : A →+* B} (h : f.IsLocalCompleteIntersection) : f.FiniteType := by
  let _ : Algebra A B := f.toAlgebra
  rcases h.exists_generators_ker_isKoszulRegular with ⟨n, P, _⟩
  simpa [RingHom.FiniteType] using (P.finiteType : Algebra.FiniteType A B)

instance {f : A →+* B} [h : f.IsLocalCompleteIntersection] : f.FiniteType :=
  h.finiteType

/-- The identity ring map is a local complete intersection. -/
@[instance] theorem id :
    (RingHom.id A).IsLocalCompleteIntersection := sorry

end IsLocalCompleteIntersection

end

end RingHom

/-! ### Lemma_15_33_3 (from Chap15) -/
universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: target-local properties of commutative ring homomorphisms, specialized here to
  local complete intersections;
- sampled owner declarations:
  `RingHom.IsLocalCompleteIntersection`,
  `RingHom.OfLocalizationSpanTarget`,
  `RingHom.OfLocalizationFiniteSpanTarget`,
  `RingHom.ofLocalizationSpanTarget_iff_finite`;
- best owner abstraction: the locality statement belongs at the meta-property owner
  `RingHom.OfLocalizationSpanTarget` for the ring-hom predicate
  `RingHom.IsLocalCompleteIntersection`; the finite principal-open version is only the bridge
  supplied by `RingHom.ofLocalizationSpanTarget_iff_finite`;
- primitive vs. derived: the primitive owner inputs are the ring map `f`, a spanning set
  `s : Set S`, and the localized `IsLocalCompleteIntersection` hypotheses on the maps
  `R → S[1 / g]`; any theorem specialized to one chosen finite family is derived API obtained by
  applying `RingHom.ofLocalizationSpanTarget_iff_finite`.

Source/core/bridge triage:
- `source-facing`: target-local descent of `RingHom.IsLocalCompleteIntersection` from a finite
  principal-open cover;
- `core/canonical`: `RingHom.OfLocalizationSpanTarget RingHom.IsLocalCompleteIntersection`;
- `bridge/view`: the finite-family specialization
  `RingHom.OfLocalizationFiniteSpanTarget RingHom.IsLocalCompleteIntersection`, recovered via
  `RingHom.ofLocalizationSpanTarget_iff_finite`. -/

namespace IsLocalCompleteIntersection

-- Proof sketch: first reduce to the finite-spanning formulation via
-- `RingHom.ofLocalizationSpanTarget_iff_finite`. Then choose a finite polynomial presentation of
-- `S` over `R`. For each `g ∈ s`, the localization `S[1 / g]` inherits a presentation whose
-- kernel ideal is obtained by adjoining one equation `x * h_j - 1`. The local complete
-- intersection hypothesis on each principal chart makes these localized kernel ideals
-- Koszul-regular. Since the elements of `s` generate the unit ideal, every prime of the global
-- presentation misses some `g ∈ s`, so Lemmas `15.30.15` and `15.30.14` descend the local
-- Koszul-regular generators back to a Zariski neighborhood of that prime in the original
-- presentation. Hence the original kernel ideal is locally Koszul-regular.
/-- Lemma 15.33.3: local complete intersection is local on the target for principal-open covers. -/
theorem ofLocalizationSpanTarget :
    OfLocalizationSpanTarget IsLocalCompleteIntersection := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  sorry

/-- Source-facing finite-cover specialization of
`IsLocalCompleteIntersection.ofLocalizationSpanTarget`. -/
theorem ofLocalizationFiniteSpanTarget :
    OfLocalizationFiniteSpanTarget IsLocalCompleteIntersection := by
  rw [← RingHom.ofLocalizationSpanTarget_iff_finite]
  exact ofLocalizationSpanTarget

end IsLocalCompleteIntersection

end

end RingHom

/-! ### Lemma_15_33_4 (from Chap15) -/
noncomputable section

universe u

open RingTheory Sequence

namespace Algebra

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

/- Domain-style sampling:
- primary domain: explicit polynomial presentations of relative global complete intersections and
  their Koszul complexes in commutative algebra;
- sampled owner declarations:
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.naive`,
  `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.IsRegular.isKoszulRegularOn`;
- best owner abstraction: for the explicit quotient by the displayed relations `f`, the source-
  facing hypothesis should be the naive presentation-level predicate
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`; the conclusion already uses the
  chapter owner `IsKoszulRegularSequence`;
- primitive vs. derived: the primitive data are the relations `f`; the intrinsic existential class
  `Algebra.IsRelativeGlobalCompleteIntersection R _` is derived bridge data that forgets which
  presentation witnesses the complete-intersection condition, so it is too coarse for this item.

Source/core/bridge triage:
- `source-facing`: the theorem about the specific relations `f₁, …, f_c` in the displayed
  polynomial quotient;
- `core/canonical`: the naive presentation of that quotient together with its presentation-level
  relative-global-complete-intersection predicate, and the owner predicate
  `RingTheory.Sequence.IsKoszulRegularSequence`;
- `bridge/view`: Lemma `10.136.12` for localized regularity of the displayed relations and Lemma
  `15.30.2` upgrading regular sequences to Koszul-regularity.
-/
variable (f : Fin c → MvPolynomial (Fin n) R)

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal
local notation "PresentedPresentation" =>
  (Algebra.Presentation.naive : Algebra.Presentation R PresentedAlgebra (Fin n) (Fin c))

-- Proof sketch: by Lemma `10.136.12`, every localization of the displayed presentation at a prime
-- of `PresentedAlgebra` makes the localized relations regular. Lemma `15.30.2` upgrades each such
-- localized regular sequence to localized Koszul-regularity, and the local vanishing of positive
-- Koszul homology descends back to the global Koszul complex on `f`.
/-- Lemma 15.33.4: if the quotient `R[x₁, …, xₙ] / (f₁, …, f_c)` is a relative global complete
intersection over `R`, then the defining equations `f₁, …, f_c` form a Koszul-regular sequence in
`R[x₁, …, xₙ]`. -/
theorem relativeGCI_relations_isKoszulRegularSequence
    (hP : Algebra.Presentation.IsRelativeGlobalCompleteIntersection PresentedPresentation) :
    IsKoszulRegularSequence f := by
  sorry

end Algebra

/-! ### Lemma_15_33_5 (from Chap15) -/
universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: syntomic and local-complete-intersection properties of commutative ring
  homomorphisms;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Syntomic.flat`,
  `RingHom.Syntomic.hasLocalCompleteIntersectionFibers`,
  `RingHom.IsLocalCompleteIntersection`;
- best owner abstraction: this lemma belongs on the ring-hom owner
  `RingHom.Syntomic`, not on the algebra-map specialization `algebraMap R S`;
- primitive vs. derived: the primitive owner data are already in `RingHom.Syntomic`, while the
  flatness projection is derived API and the local-complete-intersection criterion is the new
  companion characterization supplied here.

Source/core/bridge triage:
- `source-facing`: the equivalence between syntomicity and flat local complete intersection for a
  ring map;
- `core/canonical`: the owner predicates `RingHom.Syntomic` and
  `RingHom.IsLocalCompleteIntersection`;
- `bridge/view`: the algebra-map specialization obtained by instantiating the theorem below with
  `f := algebraMap R S`. -/

namespace Syntomic

-- Proof sketch: for the forward implication, unpack `Syntomic R S`; flatness is built into the
-- definition, and the fiberwise local complete intersection condition can be upgraded to the ring-
-- map local complete intersection criterion via the relative-global-complete-intersection
-- neighborhood theorem together with Lemmas `15.33.3` and `15.33.4`. For the reverse implication,
-- a flat local complete intersection map is of finite presentation, and after base change to each
-- residue field its fibers are local complete intersections, which is exactly the remaining
-- syntomic condition.
/-- Lemma 15.33.5: a ring map is syntomic if and only if it is flat and a local complete
intersection. -/
theorem iff_flat_and_isLocalCompleteIntersection (f : R →+* S) :
    f.Syntomic ↔ f.Flat ∧ f.IsLocalCompleteIntersection := sorry

end Syntomic

end

end RingHom

/-! ### Lemma_15_33_6 (from Chap15) -/
open CategoryTheory
open scoped TensorProduct
open Algebra

universe u v w

noncomputable section

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {ι : Type v} {κ : Type w}

/-- The conormal map from the tensorized naive cotangent complex of `P` to the composite
presentation `Q.comp P` sends cycles to cycles. -/
-- Proof sketch: apply functoriality of `Extension.Cotangent.map` with respect to `Q.toComp P`,
-- then use compatibility of cotangent complexes under presentation morphisms. Since the source
-- element lies in the kernel of the tensorized differential of `P`, its image lies in
-- `H₁` of the composite presentation.
theorem tensor_presentation_conormal_map_mem_comp_generators_h1
    (P : Generators A B ι) (Q : Generators B C κ)
    (x : C ⊗[B] P.toExtension.Cotangent)
    (hx : x ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex)) :
    LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x ∈
      LinearMap.ker (Q.comp P).toExtension.cotangentComplex := sorry

/-- The canonical map from the first homology of the tensorized naive cotangent complex of `P`
to the first homology of the composite presentation `Q.comp P` for an arbitrary presentation
`Q` of `C` over `B`. -/
noncomputable def tensor_presentation_cotangent_h1_to_comp_generators_h1
    (P : Generators A B ι) (Q : Generators B C κ) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      (Q.comp P).toExtension.H1Cotangent :=
  (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)).restrict
    (tensor_presentation_conormal_map_mem_comp_generators_h1 P Q)

/-- The canonical map from the first homology of the tensorized naive cotangent complex of `P`
to `H¹(L_{C/A})`, computed from the canonical self-presentation of `C` over `B`. -/
noncomputable def tensor_presentation_cotangent_h1_to_h1_cotangent
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      H1Cotangent A C :=
  ((Generators.self B C).comp P).equivH1Cotangent.toLinearMap ∘ₗ
    tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C)

/-- Any presentation `Q` of `C` over `B` computes the same left Jacobi-Zariski map as the
canonical self-presentation of `C` over `B`. -/
theorem tensor_presentation_cotangent_h1_to_h1_cotangent_eq_of_generators
    (P : Generators A B ι) (Q : Generators B C κ) :
    tensor_presentation_cotangent_h1_to_h1_cotangent C P =
      (Q.comp P).equivH1Cotangent.toLinearMap ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := sorry

/-- The two conormal maps for the composite presentation `Q.comp P` compose to zero. -/
theorem compPresentationConormalSequence_comp_eq_zero
    (P : Generators A B ι) (Q : Generators B C κ) :
    (Extension.Cotangent.map (Q.ofComp P).toExtensionHom).comp
      (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)) =
        0 := sorry

/-- The source-facing conormal short complex
`C ⊗[B] I/I² ⟶ K/K² ⟶ J/J²`
attached to the composite presentation `Q.comp P`, where `I`, `J`, and `K` are the kernel ideals
of `P`, `Q`, and `Q.comp P`. -/
noncomputable def compPresentationConormalSequence
    (P : Generators A B ι) (Q : Generators B C κ) :
    ShortComplex (ModuleCat.{max u (max v w)} C) :=
  let α :
      ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) →ₗ[C]
        ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent :=
    (ULift.moduleEquiv :
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
        (Q.comp P).toExtension.Cotangent).symm.toLinearMap ∘ₗ
      LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) ∘ₗ
      (ULift.moduleEquiv :
        ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) ≃ₗ[C]
          (C ⊗[B] P.toExtension.Cotangent)).toLinearMap
  let β :
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent →ₗ[C]
        ULift.{max u (max v w), max u w} Q.toExtension.Cotangent :=
    (ULift.moduleEquiv :
      ULift.{max u (max v w), max u w} Q.toExtension.Cotangent ≃ₗ[C]
        Q.toExtension.Cotangent).symm.toLinearMap ∘ₗ
      Extension.Cotangent.map (Q.ofComp P).toExtensionHom ∘ₗ
      (ULift.moduleEquiv :
        ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
          (Q.comp P).toExtension.Cotangent).toLinearMap
  let h : β.comp α = 0 := by
    ext x
    simpa [α, β, LinearMap.comp_assoc] using
      congrArg (fun y : Q.toExtension.Cotangent ↦ y.val) <|
        LinearMap.congr_fun (compPresentationConormalSequence_comp_eq_zero P Q) x.down
  ModuleCat.shortComplexOfCompEqZero α β h

/-- The leftmost two maps in the presentation-level Jacobi-Zariski sequence compose to zero. -/
theorem presentationJacobiZariskiLeftSequence_comp_eq_zero
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    (H1Cotangent.map A B C C).comp
      (tensor_presentation_cotangent_h1_to_h1_cotangent C P) =
        0 := sorry

/-- The source-facing left three-term Jacobi-Zariski short complex
`H₁(NL_{B/A} ⊗[B] C) ⟶ H¹(L_{C/A}) ⟶ H¹(L_{C/B})`,
where the left term is represented by the kernel of the tensorized differential attached to the
chosen presentation `P`, and the first map is the canonical one induced by the self-presentation
of `C` over `B`. -/
noncomputable def presentationJacobiZariskiLeftSequence
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    ShortComplex (ModuleCat.{max u v} C) :=
  let α :
      LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
        ULift.{max u v, u} (H1Cotangent A C) :=
    (ULift.moduleEquiv :
      ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C] H1Cotangent A C).symm.toLinearMap ∘ₗ
      tensor_presentation_cotangent_h1_to_h1_cotangent C P
  let β :
      ULift.{max u v, u} (H1Cotangent A C) →ₗ[C]
        ULift.{max u v, u} (H1Cotangent B C) :=
    (ULift.moduleEquiv :
      ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C] H1Cotangent B C).symm.toLinearMap ∘ₗ
      H1Cotangent.map A B C C ∘ₗ
      (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C] H1Cotangent A C).toLinearMap
  let h : β.comp α = 0 := by
    ext x
    change (((H1Cotangent.map A B C C)
        ((tensor_presentation_cotangent_h1_to_h1_cotangent C P) x) :
          LinearMap.ker ((Generators.self B C).toExtension.cotangentComplex))).val = 0
    simpa using congrArg Subtype.val
      (LinearMap.congr_fun (presentationJacobiZariskiLeftSequence_comp_eq_zero C P) x)
  ModuleCat.shortComplexOfCompEqZero α β h

-- Proof sketch: `Generators.Cotangent.exact Q P` already gives exactness of the lower conormal
-- row for the composite presentation. The local complete intersection hypothesis on `Q` makes the
-- kernel ideal `J` Koszul-regular, hence `H₁`-regular; applying Lemma `15.32.5` to the induced
-- ideals identifies the kernel of `K/K² → J/J²` with `(I / I²) ⊗[B] C`, which yields injectivity
-- of the left map.
section

variable [Finite κ]

/-- Lemma 15.33.6: for a chosen presentation `P : A[x_s] → B` and a chosen finite presentation
`Q : B[y_t] → C` indexed by a finite type `κ`, whose kernel ideal is Koszul-regular, the conormal
sequence of the induced composite presentation is exact on the left:
`0 → C ⊗[B] I/I² → K/K² → J/J² → 0`. Here `I`, `J`, and `K` are the kernel ideals of `P`, `Q`,
and `Q.comp P`. -/
theorem comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    (compPresentationConormalSequence P Q).ShortExact := sorry

-- Proof sketch: use the injective conormal sequence above to identify the kernel of
-- `H1Cotangent.map A B C C` with the first homology of the tensorized naive cotangent complex of
-- `P`, then combine this with the Jacobi-Zariski exact sequence
-- `jacobi_zariski_exact_sequence` for the remaining four terms.
/-- For a finite local complete intersection presentation `Q : B[y_t] → C` indexed by a finite
type `κ`, the
Jacobi-Zariski sequence extends on the left by the first homology of the tensorized naive
cotangent complex of `P`, namely
`0 → H₁(NL_{B/A} ⊗[B] C) → H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`,
where `H₁(NL_{B/A} ⊗[B] C)` is written as the kernel of the tensorized differential attached to
the chosen presentation `P`. -/
theorem jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) ∧
      (presentationJacobiZariskiLeftSequence C P).Exact := sorry

/-- The presentation-level left Jacobi-Zariski short complex is exact under the Koszul-regular
kernel hypothesis. -/
theorem presentationJacobiZariskiLeftSequence_exact_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    (presentationJacobiZariskiLeftSequence C P).Exact :=
  (jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel P Q hQ).2

/-- The left map in the presentation-level Jacobi-Zariski short complex is injective under the
Koszul-regular kernel hypothesis. -/
theorem presentationJacobiZariskiLeftSequence_injective_f_of_koszul_regular_kernel
    (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal (Q.toExtension.ker)) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) :=
  (jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel P Q hQ).1

end

end

/-! ### Lemma_15_33_7 (from Chap15) -/
open Algebra
open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u v

noncomputable section

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.33.7:
* primary domain: filtered-colimit presentations of local complete intersection ring maps in
  commutative algebra;
* sampled owner declarations:
  - `RingHom.IsLocalCompleteIntersection` from `Definition_15_33_2`;
  - `RingHom.toMorphismProperty`, the canonical bridge from ring-hom properties to
    `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical owner for filtered-colimit morphism
    properties;
  - `RingHom.IsFilteredColimitOfSmooth` from `Lemma_10_147_5`, which already uses this owner
    pattern for the analogous smooth case.
* best owner abstraction: the source-facing owner here is
  `RingHom.IsFilteredColimitOfLocalCompleteIntersection`, whose core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
  RingHom.IsLocalCompleteIntersection)`;
* primitive data: only the ring map `f : R →+* S`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism exhibiting `f` as
  a filtered colimit of local complete intersection `R`-algebras.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfLocalCompleteIntersection`;
* `core/canonical`: `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
  RingHom.IsLocalCompleteIntersection)`;
* `bridge/view`: the hidden same-universe `ULift` presentation used to speak to
  `CategoryTheory.MorphismProperty.ind`.
-/
/-- An `R`-algebra map `f : R →+* S` is a filtered colimit of local complete intersection
`R`-algebras. This thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed
to express the canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
RingHom.IsLocalCompleteIntersection)`. -/
abbrev IsFilteredColimitOfLocalCompleteIntersection (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty IsLocalCompleteIntersection)
    (ofHom (algebraMap (ULift.{v} R) (ULift S)))

end

end RingHom

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {ι : Type v}

-- Proof sketch: write `B → C` as a filtered colimit of local complete intersection maps. Apply
-- Lemma `15.33.6` to each stage to obtain the left-extended Jacobi-Zariski sequence there, then
-- use Lemma `10.134.9` to identify the direct limit of the stagewise naive cotangent complexes
-- with the naive cotangent complex of `A → B → C`. Exactness of filtered colimits transports the
-- stagewise exactness to the limit sequence.
/-- Lemma 15.33.7: let `A → B → C` be ring maps. If `B → C` is a filtered colimit of local
complete intersection homomorphisms, then for any presentation `P : A[x_s] → B`, the
left-extended Jacobi-Zariski sequence
`0 → H₁(NL_{B/A} ⊗[B] C) → H¹(L_{C/A}) → H¹(L_{C/B}) → C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
is exact, where `H₁(NL_{B/A} ⊗[B] C)` is represented by the kernel of the tensorized differential
attached to `P`. -/
theorem presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection
    (P : Generators A B ι)
    (hQ : (algebraMap B C).IsFilteredColimitOfLocalCompleteIntersection) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) ∧
      (presentationJacobiZariskiLeftSequence C P).Exact := sorry

end

/-! ### Lemma_15_33_8 (from Chap15) -/
open Algebra
open scoped TensorProduct

universe u v

noncomputable section

section

variable {A : Type u} {B : Type u} {Ah : Type u} {Bh : Type u}
variable [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
variable [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
variable [IsScalarTower A B Bh] [IsScalarTower A Ah Bh]

/-
Domain-style sampling for Lemma 15.33.8:
* primary domain: cotangent-homology and Kähler-differential comparison maps for a compatible
  square of commutative rings under ind-étale hypotheses;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter owner for ind-étale ring maps;
  - `tensor_presentation_cotangent_h1_to_h1_cotangent`, the source-facing `H^{-1}` map from a
    tensorized naive cotangent complex to cotangent homology;
  - `H1Cotangent.map`, the owner change-of-base map on `H^{-1}`;
  - `KaehlerDifferential.mapBaseChange` and `KaehlerDifferential.map`, the owner maps on degree
    `0`.
* best owner abstraction: the primitive data here are the two cohomology comparison maps induced
  by the source-facing comparison
  `NL_{B/A} ⊗[B] Bh ⟶ NL_{Bh/Ah}`. The current chapter already has canonical owners for these
  induced maps on `H^{-1}` and `H^0`, but not for a general non-flat tensorized morphism in
  `D(Bh)`, so this file should expose those cohomology-level maps directly instead of inventing a
  parallel derived-category owner.

Source/core/bridge triage:
* `source-facing`: the comparison
  `NL_{B/A} ⊗[B] Bh ⟶ NL_{Bh/Ah}` through its induced maps on `H^{-1}` and `H^0`;
* `core/canonical`: `RingHom.IsFilteredColimitOfEtale`,
  `tensor_presentation_cotangent_h1_to_h1_cotangent`, `H1Cotangent.map`,
  `KaehlerDifferential.mapBaseChange`, and `KaehlerDifferential.map`;
* `bridge/view`: the named cohomology comparison composites below.
-/

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.H1Cotangent

/-- The degree `-1` comparison
`H₁(NL(P/A) ⊗[B] Bh) → H₁(L_{Bh/Ah})`
attached to a compatible square `A → Ah`, `A → B`, `B → Bh`, `Ah → Bh`, written through the
chapter owners for the presentation-level Jacobi-Zariski map and the change-of-base map. -/
noncomputable abbrev presentationBaseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] {ι : Type v}
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange Bh P.toExtension.cotangentComplex) →ₗ[Bh]
      H1Cotangent Ah Bh :=
  (map A Ah Bh Bh).comp (tensor_presentation_cotangent_h1_to_h1_cotangent Bh P)

end Algebra.H1Cotangent

namespace KaehlerDifferential

/-- The degree `0` comparison
`Bh ⊗[B] Ω[B⁄A] → Ω[Bh⁄Ah]`
attached to a compatible square `A → Ah`, `A → B`, `B → Bh`, `Ah → Bh`. -/
noncomputable abbrev baseChangeComparison
    (A Ah B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [Algebra A B] [Algebra A Ah] [Algebra B Bh] [Algebra A Bh] [Algebra Ah Bh]
    [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    Bh ⊗[B] Ω[B⁄A] →ₗ[Bh] Ω[Bh⁄Ah] :=
  (map A Ah Bh Bh).comp (mapBaseChange A B Bh)

end KaehlerDifferential

-- Proof sketch: `A → Ah` and `B → Bh` being filtered colimits of étale algebras makes
-- `NL_{Ah/A}` and `NL_{Bh/B}` acyclic. Apply the Jacobi-Zariski sequence to `A → Ah → Bh` to
-- identify `NL_{Bh/A}` and `NL_{Bh/Ah}` on cohomology, then apply Lemma `15.33.7` to
-- `A → B → Bh`, using that étale maps are local complete intersections, to identify
-- `NL_{B/A} ⊗[B] Bh` and `NL_{Bh/A}` on cohomology. Composing these identifications gives the
-- stated bijectivity in degrees `1` and `0`. 
/-- Lemma 15.33.8, degree `-1`: if `A → Ah` and `B → Bh` are filtered colimits of étale
algebras compatible with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces a bijection on `H^{-1}`. -/
theorem naiveCotangentFilteredColimitOfEtaleComparison_h1_bijective
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective
      (H1Cotangent.presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) := sorry

/-- Lemma 15.33.8, degree `0`: if `A → Ah` and `B → Bh` are filtered colimits of étale
algebras compatible with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces a bijection on `H^0 = Ω`. -/
theorem naiveCotangentFilteredColimitOfEtaleComparison_kaehler_bijective
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := sorry

/-- Lemma 15.33.8: if `A → Ah` and `B → Bh` are filtered colimits of étale algebras compatible
with `A → B`, then the canonical comparison
`NL_{B/A} ⊗[B] Bh → NL_{Bh/Ah}` induces bijections on the two cohomology groups of the naive
cotangent complex. In particular, this applies to henselizations and strict henselizations. -/
theorem naiveCotangent_cohomology_comparison_bijective_of_filteredColimitOfEtale
    (hAh : (algebraMap A Ah).IsFilteredColimitOfEtale)
    (hBh : (algebraMap B Bh).IsFilteredColimitOfEtale) :
    Function.Bijective
      (H1Cotangent.presentationBaseChangeComparison A Ah B Bh (Generators.self A B)) ∧
      Function.Bijective (KaehlerDifferential.baseChangeComparison A Ah B Bh) := by
  exact ⟨
    naiveCotangentFilteredColimitOfEtaleComparison_h1_bijective hAh hBh,
    naiveCotangentFilteredColimitOfEtaleComparison_kaehler_bijective hAh hBh
  ⟩

end
