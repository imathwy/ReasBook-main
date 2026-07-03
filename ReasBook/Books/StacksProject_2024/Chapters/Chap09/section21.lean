import Mathlib
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_21_1 (from Chap09) -/
/- Domain-style sampling for Definition 9.21.1:
- primary domain: Galois field extensions in field theory;
- sampled owner declarations:
  `Algebra.IsSeparable`,
  `Normal`,
  `IsGalois`;
- sampled derived/specification API:
  `isGalois_iff`;
- best owner abstraction: the extension-level owner is the canonical mathlib typeclass
  `IsGalois F E`;
- primitive data: none locally, since the source notion is already owned upstream;
- derived API: the source-style characterization by separability and normality is already packaged
  by `isGalois_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that a field extension is Galois;
- `core/canonical`: `IsGalois`;
- `bridge/view`: `isGalois_iff`.

This file should therefore remain a pure recall surface. Any local alias or restated wrapper would
only duplicate the owner declaration already provided by mathlib. -/

/- Definition 9.21.1: for a field extension `E/F`, the canonical mathlib notion of a Galois
extension is `IsGalois F E`. -/
recall IsGalois

/- Companion recall: the textbook characterization of a Galois extension as algebraic,
separable, and normal is canonically packaged by `isGalois_iff`; the algebraicity clause is
already absorbed by the canonical owner predicates `Algebra.IsSeparable` and `Normal`. -/
recall isGalois_iff

/-! ### Lemma_9_21_2 (from Chap09) -/
universe u v

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/- Domain-style sampling:
* primary domain: finite-dimensional Galois extensions and their automorphism groups;
* sampled owner declarations:
  `IsGalois`,
  `isGalois_iff`,
  `IsGalois.card_aut_eq_finrank`,
  `IsGalois.of_card_aut_eq_finrank`;
* best owner abstraction: the field-extension owner predicate `IsGalois F E`, already introduced
  in Definition 9.21.1;
* primitive data: fields `F`, `E`, an `F`-algebra structure on `E`, and finite dimensionality;
* derived API: the numerical criterion comparing `Nat.card Gal(E / F)` with `Module.finrank F E`
  is already split upstream into the two owner-direction theorems recalled below.

Layer triage:
* `source-facing`: Lemma 9.21.2 is the textbook finite-dimensional criterion for Galoisness;
* `core/canonical`: `IsGalois F E`;
* `bridge/view`: the cardinality equality `Nat.card Gal(E / F) = Module.finrank F E`.

So this file should reuse the two canonical owner theorems directly rather than keep a local `↔`
wrapper duplicating upstream API. -/
/- Lemma 9.21.2: for a finite field extension `E/F`, the forward implication
`IsGalois F E → Nat.card Gal(E / F) = Module.finrank F E` is the canonical owner theorem
`IsGalois.card_aut_eq_finrank`. -/
recall IsGalois.card_aut_eq_finrank

/- Companion recall: the converse implication
`Nat.card Gal(E / F) = Module.finrank F E → IsGalois F E` is the canonical owner theorem
`IsGalois.of_card_aut_eq_finrank`. -/
recall IsGalois.of_card_aut_eq_finrank

end

/-! ### Definition_9_21_3 (from Chap09) -/
universe u v

section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.21.3:
- primary domain: Galois extensions and their automorphism groups in field theory;
- sampled chapter/project owner declarations:
  `Gal(E / F)`,
  `(inferInstance : Group Gal(E / F))`,
  `IsGalois`,
  `IsGalois.card_aut_eq_finrank`;
- best owner abstraction: the canonical automorphism-group owner `Gal(E / F)` already recalled in
  Definition 9.15.8, with `IsGalois F E` from Definition 9.21.1 as the extension property naming
  the case in which this automorphism group is called the Galois group.

Layer triage:
- `source-facing`: the terminology that for a Galois extension `E/F`, the automorphism group of
  `E` over `F` is called the Galois group;
- `core/canonical`: `Gal(E / F)`;
- `bridge/view`: later owner theorems for Galois extensions, such as
  `IsGalois.card_aut_eq_finrank`.

Primitive data are only the field extension `E/F` and its `F`-algebra structure. The source's
extra `IsGalois` hypothesis does not create a new object; it only specifies the terminology for
the already canonical owner `Gal(E / F)`. So this file should remain a direct recall/check surface
rather than introduce any parallel local alias or wrapper.
-/

/- Definition 9.21.3 (Tag 09DV): when `E/F` is a Galois extension, its Galois group is the
already existing canonical automorphism group `Gal(E / F)`. -/
#check Gal(E / F)

/- Companion check: the Galois group uses the canonical group structure on `Gal(E / F)` induced by
composition. -/
#check (inferInstance : Group Gal(E / F))

end

/-! ### Lemma_9_21_4 (from Chap09) -/
/- Domain-style sampling for Lemma 9.21.4:
- primary domain: Galois theory for towers of field extensions;
- sampled owner declarations:
  `IsGalois`,
  `isGalois_iff`,
  `IsGalois.tower_top_of_isGalois`,
  `IsGalois.tower_top_intermediateField`;
- best owner abstraction: the extension-level owner remains `IsGalois`;
- primitive data: a tower of fields together with the canonical compatibility data
  `[IsScalarTower F E K]`;
- derived API: upward inheritance of Galoisness along the tower is already owned by
  `IsGalois.tower_top_of_isGalois`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that in a tower `K/E/F`, Galoisness over `F` implies
  Galoisness over `E`;
- `core/canonical`: `IsGalois`;
- `bridge/view`: the tower inheritance theorem `IsGalois.tower_top_of_isGalois`.

So this file should remain a direct recall of the canonical tower theorem rather than a local
wrapper. The source's separate algebraicity hypothesis is redundant here, since the canonical
owner `IsGalois` already packages separability and normality. -/
/- Lemma 9.21.4: in a tower of field extensions `K/E/F`, if `K` is Galois over `F`, then `K` is
Galois over `E`. -/
recall IsGalois.tower_top_of_isGalois

/-! ### Lemma_9_21_5 (from Chap09) -/
noncomputable section

universe u v

open IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [Algebra.IsSeparable K L]

/-
Domain-style sampling for Lemma 9.21.5:
- primary domain: Galois and normal closure theory for separable field extensions;
- sampled owner declarations:
  `IntermediateField.normalClosure`,
  `IntermediateField.normalClosure_le_iff`,
  `IntermediateField.le_separableClosure_iff`,
  `Algebra.IsAlgebraic.isNormalClosure_normalClosure`;
- best owner abstraction: the canonical intermediate field `normalClosure K L (AlgebraicClosure L)`.

Source/core/bridge triage:
- `source-facing`: the normal closure of the separable extension `L/K` inside
  `AlgebraicClosure L`;
- `core/canonical`: the owner-level construction `normalClosure K L (AlgebraicClosure L)`;
- `bridge/view`: the proof that this owner is Galois over `K`, assembled from the canonical
  normality and separability APIs.

Primitive data are only the tower `K → L → AlgebraicClosure L` together with the separability of
`L/K`. The Galois property is entirely derived API, so this file should use the canonical owner
directly rather than introducing any parallel local closure object or comparison wrapper.
-/

/-- Helper for Lemma 9.21.5: the field range of a `K`-embedding of `L` into `AlgebraicClosure L`
lies in the separable closure over `K`. -/
lemma field_range_le_separable_closure_of_embedding
    (f : L →ₐ[K] AlgebraicClosure L) :
    f.fieldRange ≤ separableClosure K (AlgebraicClosure L) := by
  -- Transport separability of `L/K` across the canonical equivalence onto the embedding range.
  refine (le_separableClosure_iff K (AlgebraicClosure L) f.fieldRange).2 ?_
  exact AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)

/-- Helper for Lemma 9.21.5: the canonical normal closure inside `AlgebraicClosure L` is
contained in the separable closure over `K`. -/
lemma normal_closure_le_separable_closure :
    normalClosure K L (AlgebraicClosure L) ≤ separableClosure K (AlgebraicClosure L) := by
  -- Control the normal closure through the defining condition on the ranges of embeddings.
  exact normalClosure_le_iff.2 field_range_le_separable_closure_of_embedding

/-- Lemma 9.21.5: for a separable extension `L/K` (in particular for a finite separable one),
the normal closure of `L/K`, taken inside `AlgebraicClosure L`, is Galois over `K`. -/
theorem isGalois_normalClosure_of_separable :
    IsGalois K (normalClosure K L (AlgebraicClosure L)) := by
  -- Decompose the Galois condition into separability and normality of the canonical owner.
  rw [isGalois_iff]
  constructor
  · rw [← le_separableClosure_iff]
    -- The normal closure is separable because every embedding range lands in the separable closure.
    exact normal_closure_le_separable_closure (K := K) (L := L)
  · -- Route correction: close normality through the owner-level `normalClosure.normal` instance.
    infer_instance

/-! ### Lemma_9_21_6 (from Chap09) -/
universe u v

variable {G : Type u} {K : Type v}
variable [Group G] [Field K] [MulSemiringAction G K]

/- Domain-style sampling for Lemma 9.21.6:
- primary domain: finite group actions on fields, fixed fields, and Galois-group realizations;
- sampled owner declarations:
  `FixedPoints.subfield`,
  `IsGaloisGroup`,
  `IsGaloisGroup.fixedPoints`,
  `IsGaloisGroup.mulEquivAlgEquiv`;
- best owner abstraction: the canonical owner predicate `IsGaloisGroup G F K` for a group action on
  a field `K` with fixed field `F`;
- primitive data: the group `G`, the field `K`, the action `MulSemiringAction G K`, and the
  upstream finiteness and faithfulness assumptions needed by the owner instance;
- derived API: the Galoisness of `K / FixedPoints.subfield G K`, the degree formula
  `Module.finrank (FixedPoints.subfield G K) K = Nat.card G`, and the comparison
  `G ≃* Gal(K / FixedPoints.subfield G K)` come from the owner theorems built on that instance.

Layer triage:
- `source-facing`: the textbook statement that a finite faithful action on a field realizes the
  acting group as the Galois group over the fixed field;
- `core/canonical`: the instance `IsGaloisGroup.fixedPoints`;
- `bridge/view`: downstream consequences such as `IsGaloisGroup.isGalois`,
  `IsGaloisGroup.card_eq_finrank`, and `IsGaloisGroup.mulEquivAlgEquiv`.

This item is therefore a pure canonical-recall surface. There is no additional source-facing data
to define locally, so the refined file should reuse the owner instance directly instead of
introducing a parallel theorem or wrapper. -/
/- Lemma 9.21.6: if a finite group `G` acts faithfully on a field `K`, then the extension
`K / FixedPoints.subfield G K` has `G` as its Galois group. This is the canonical mathlib
instance `IsGaloisGroup.fixedPoints`, from which the textbook consequences follow: the extension is
Galois, its degree is `|G|`, and `G ≃* Gal(K / FixedPoints.subfield G K)`. -/
recall IsGaloisGroup.fixedPoints

/-! ### Theorem_9_21_7_Fundamental_theorem_of_Galois_theory (from Chap09) -/
universe u v

section

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/- Domain-style sampling for Theorem 9.21.7:
- primary domain: finite Galois correspondence between intermediate fields and subgroups of
  `Gal(L / K)`;
- sampled owner declarations:
  `IsGalois.intermediateFieldEquivSubgroup`,
  `IsGalois.fixedField_top`,
  `IsGalois.of_fixedField_normal_subgroup`,
  `IsGalois.fixingSubgroup_normal_of_isGalois`;
- best owner abstraction: the finite Galois correspondence is owned by the order isomorphism
  `IsGalois.intermediateFieldEquivSubgroup`;
- primitive data: a finite-dimensional Galois extension `L / K`;
- derived API: the fixed field of the whole Galois group and the two normal/Galois directions of
  the correspondence are already exposed upstream as owner theorems and instances.

Layer triage:
- `source-facing`: the finite fundamental theorem identifying intermediate fields with subgroups of
  `Gal(L / K)`;
- `core/canonical`: `IsGalois.intermediateFieldEquivSubgroup`;
- `bridge/view`: `IsGalois.fixedField_top`,
  `IsGalois.of_fixedField_normal_subgroup`,
  `IsGalois.fixingSubgroup_normal_of_isGalois`.

This file should therefore stay a pure recall surface. A local restatement of the correspondence,
or a local bundled theorem for the normal-subgroup criterion, would only duplicate the canonical
owner API already used in the chapter. -/

/- Theorem 9.21.7 (Fundamental theorem of Galois theory): for a finite Galois extension `L/K`,
the canonical Galois correspondence is the order isomorphism
`IsGalois.intermediateFieldEquivSubgroup`, which identifies intermediate fields `M` with
subgroups `M.fixingSubgroup` of `Gal(L / K)` and sends a subgroup `H` to its fixed field
`fixedField H`. -/
recall IsGalois.intermediateFieldEquivSubgroup

/- Companion recall: the textbook equality `K = L^G` for `G = Gal(L/K)` is the canonical theorem
`IsGalois.fixedField_top`, which identifies the fixed field of the whole Galois group with the
bottom intermediate field. -/
recall IsGalois.fixedField_top

/- Companion recalls: under the finite Galois correspondence, a normal subgroup
`H ≤ Gal(L / K)` cuts out a Galois intermediate field `fixedField H` by
`IsGalois.of_fixedField_normal_subgroup`, and conversely an intermediate field `M` that is Galois
over `K` has normal fixing subgroup by `IsGalois.fixingSubgroup_normal_of_isGalois`. -/
recall IsGalois.of_fixedField_normal_subgroup

recall IsGalois.fixingSubgroup_normal_of_isGalois

end

/-! ### Lemma_9_21_8 (from Chap09) -/
universe u v

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/- Domain-style sampling:
* primary domain: finite-dimensional Galois extensions and their automorphism groups;
* sampled owner declarations:
  `IsGalois`,
  `isGalois_iff`,
  `IsGalois.card_aut_eq_finrank`,
  `IsGalois.of_card_aut_eq_finrank`;
* best owner abstraction: the field-extension owner predicate `IsGalois F E`, already introduced
  in Definition 9.21.1;
* primitive data: fields `F`, `E`, an `F`-algebra structure on `E`, and finite dimensionality;
* derived API: the numerical criterion comparing `Nat.card Gal(E / F)` with `Module.finrank F E`
  is already split upstream into the two owner-direction theorems recalled below.

Layer triage:
* `source-facing`: Lemma 9.21.2 is the textbook finite-dimensional criterion for Galoisness;
* `core/canonical`: `IsGalois F E`;
* `bridge/view`: the cardinality equality `Nat.card Gal(E / F) = Module.finrank F E`.

So this file should reuse the two canonical owner theorems directly rather than keep a local `↔`
wrapper duplicating upstream API. -/
/-- Lemma 9.21.2: for a finite field extension `E/F`, `E` is Galois over `F` if and only if the
number of `F`-automorphisms of `E` is `[E : F]`. -/
theorem isGalois_iff_card_aut_eq_finrank :
    IsGalois F E ↔ Nat.card Gal(E / F) = Module.finrank F E := by
  constructor
  · intro hGalois
    -- The forward direction is the canonical cardinality theorem for finite Galois extensions.
    letI : IsGalois F E := hGalois
    simpa using (IsGalois.card_aut_eq_finrank F E)
  · intro hcard
    -- The converse is the companion canonical reconstruction theorem.
    exact IsGalois.of_card_aut_eq_finrank F E hcard

/- Companion recall: the forward implication
`IsGalois F E → Nat.card Gal(E / F) = Module.finrank F E` is the canonical owner theorem
`IsGalois.card_aut_eq_finrank`. -/
-- Route correction: the original target file contained stale Lemma 9.21.8 content, so the proof
-- work here is a file-alignment repair followed by direct reuse of the canonical owner theorem.
recall IsGalois.card_aut_eq_finrank

/- Companion recall: the converse implication
`Nat.card Gal(E / F) = Module.finrank F E → IsGalois F E` is the canonical owner theorem
`IsGalois.of_card_aut_eq_finrank`. -/
-- This closes the textbook criterion by reusing the existing upstream converse directly.
recall IsGalois.of_card_aut_eq_finrank

end
