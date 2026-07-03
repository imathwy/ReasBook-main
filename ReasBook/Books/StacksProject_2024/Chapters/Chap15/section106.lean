import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_106_1 (from Chap15) -/
open scoped TensorProduct

universe u v

section

variable {K : Type u} [Field K]
variable {B : Type v} [CommRing B] [Algebra K B]

section WeaklyEtale

variable [Algebra.IsWeaklyEtale K B]

/- Domain-style sampling for Lemma 15.106.1:
- primary domain: weakly étale commutative `K`-algebras over a field and their finite-type
  subalgebras, quotients, and tensor products;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `isReduced_of_isWeaklyEtale`,
  `etale_of_fg_subalgebra_of_isWeaklyEtale`,
  `Algebra.Etale.iff_exists_algEquiv_prod`,
  `Algebra.IsSeparable`,
  `isSeparable_of_flat_tensorSquareMultiplication`,
  `Algebra.IsWeaklyEtale.comp`;
- best owner abstraction: the canonical owner is `Algebra.IsWeaklyEtale K B`; finite generation of
  a `K`-subalgebra belongs primitively to `A.FG`, while the `FiniteType` phrasing in part `(3)` is
  a downstream bridge from the existing owner theorem in `Lemma 15.105.16` to
  `Algebra.Etale.iff_exists_algEquiv_prod`;
- primitive data: the weakly étale owner class on `K → B`, the subalgebra `A : Subalgebra K B`,
  and field structure when part `(5)` specializes to a field extension;
- derived API: reducedness, the finite-product classification bridge for finitely generated
  subalgebras, the canonical separability owner in the field case, and the tensor-product closure
  obtained by reusing the base-change and composition API from `15.105.*`.

This file therefore keeps the Stacks source-facing consequences, but it should not introduce a
parallel owner-level API where the chapter already proved the canonical theorem upstream.
-/

/- Lemma 15.106.1 (1): if `B` is weakly étale over a field `K`, then `B` is reduced. This is the
canonical theorem `isReduced_of_isWeaklyEtale`, specialized to the reduced base ring `K`. -/
recall isReduced_of_isWeaklyEtale

-- Proof sketch: by Lemma `15.105.16`, every finitely generated `K`-subalgebra of `B` is étale
-- over `K`, hence finite over `K`; finite algebras over a field are integral, and every element
-- of `B` lies in some finitely generated `K`-subalgebra.
/-- Lemma 15.106.1 (2): if `B` is weakly étale over a field `K`, then `B` is integral over `K`. -/
theorem isIntegral_of_isWeaklyEtale_over_field
    : Algebra.IsIntegral K B := sorry

/- Lemma 15.106.1 (3): any finitely generated `K`-subalgebra of a weakly étale `K`-algebra is
étale over `K`, equivalently a finite product of finite separable extensions of `K`. This is
exactly the canonical theorem `etale_of_fg_subalgebra_of_isWeaklyEtale` from `Lemma 15.105.16`,
with the finite-product classification supplied by `Algebra.Etale.iff_exists_algEquiv_prod`. -/
recall etale_of_fg_subalgebra_of_isWeaklyEtale

/-- Lemma 15.106.1 (3), source-facing finite-product form: any finitely generated `K`-subalgebra
of a weakly étale `K`-algebra is isomorphic to a finite product of finite separable extensions
of `K`. -/
theorem exists_algEquiv_prod_of_fg_subalgebra_of_isWeaklyEtale_over_field
    (A : Subalgebra K B) (hA : A.FG) :
    ∃ (I : Type v) (_ : Finite I) (Ai : I → Type v) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  exact (Algebra.Etale.iff_exists_algEquiv_prod K A).mp
    (etale_of_fg_subalgebra_of_isWeaklyEtale A hA)

-- Proof sketch: by `etale_of_fg_subalgebra_of_isWeaklyEtale`, every weakly étale `K`-algebra over
-- a field is a filtered colimit of finite products of finite separable field extensions. Such a
-- nontrivial product is a field exactly when it has only the trivial idempotents `0` and `1`,
-- and this criterion passes to `B`.
/-- Lemma 15.106.1 (4): a weakly étale `K`-algebra `B` is a field if and only if it has no
nontrivial idempotents. -/
theorem isField_iff_idempotents_eq_zero_or_one_of_isWeaklyEtale_over_field
    [Nontrivial B] :
    IsField B ↔ ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := sorry

-- Proof sketch: if `B` is a field, then part `(4)` together with
-- `etale_of_fg_subalgebra_of_isWeaklyEtale` reduces to the case of a single finite separable
-- field extension at each finitely generated stage. Taking the filtered colimit shows that every
-- element of `B` is separable over `K`; algebraicity is absorbed canonically by
-- `Algebra.IsSeparable`.
/-- Lemma 15.106.1 (5): if a weakly étale `K`-algebra `B` is a field, then `B` is a separable
algebraic extension of `K`. -/
theorem isSeparable_of_isField_of_isWeaklyEtale_over_field
    (hB : IsField B) :
    Algebra.IsSeparable K B := sorry

-- Proof sketch: a `K`-subalgebra is the filtered colimit of its finitely generated
-- `K`-subalgebras. Each finitely generated stage is étale over `K` by
-- `etale_of_fg_subalgebra_of_isWeaklyEtale`, hence weakly étale; then Lemma `15.105.14 (3)` gives
-- weak étaleness of the filtered colimit.
/-- Lemma 15.106.1 (6): any `K`-subalgebra of a weakly étale `K`-algebra is weakly étale over
`K`. -/
theorem isWeaklyEtale_subalgebra_of_isWeaklyEtale_over_field
    (A : Subalgebra K B) :
    Algebra.IsWeaklyEtale K A := sorry

-- Proof sketch: every quotient of a finite product of finite separable field extensions is again
-- a product of some of those factors, hence weakly étale over `K`. Express the quotient of `B` as
-- a filtered colimit of quotients of finitely generated weakly étale subalgebras and apply Lemma
-- `15.105.14 (3)`.
/-- Lemma 15.106.1 (7): any quotient `K`-algebra of a weakly étale `K`-algebra is weakly étale
over `K`. -/
theorem isWeaklyEtale_quotient_of_isWeaklyEtale_over_field
    (I : Ideal B) :
    Algebra.IsWeaklyEtale K (B ⧸ I) := sorry

end WeaklyEtale

-- Proof sketch: write both weakly étale `K`-algebras as filtered colimits of finite étale
-- `K`-algebras by `etale_of_fg_subalgebra_of_isWeaklyEtale`. Tensor products of finite étale
-- algebras over a field are again finite étale, so the tensor product is a filtered colimit of
-- weakly étale `K`-algebras; conclude with Lemma `15.105.14 (3)`.
/-- Lemma 15.106.1 (8): the tensor product of two weakly étale `K`-algebras is weakly étale over
`K`. -/
theorem isWeaklyEtale_tensorProduct_of_isWeaklyEtale_over_field
    {B' : Type v} [CommRing B'] [Algebra K B']
    [Algebra.IsWeaklyEtale K B] [Algebra.IsWeaklyEtale K B'] :
    Algebra.IsWeaklyEtale K (B ⊗[K] B') := by
  let hKB : Algebra.IsWeaklyEtale K B := inferInstance
  let hBT : Algebra.IsWeaklyEtale B (B ⊗[K] B') :=
    (inferInstance : Algebra.IsWeaklyEtale K B').baseChange
  exact (Algebra.IsWeaklyEtale.comp hKB hBT : Algebra.IsWeaklyEtale K (B ⊗[K] B'))

end

/-! ### Lemma_15_106_2 (from Chap15) -/
universe u v

section

variable (K : Type u) [Field K]
variable (A : Type v) [CommRing A] [Algebra K A]

/- Domain-style sampling for Lemma 15.106.2:
- primary domain: commutative algebra of weakly étale `K`-subalgebras of `A`, ordered by
  inclusion in `Subalgebra K A`;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Subalgebra`'s complete lattice structure,
  `le_sSup`,
  `IsGreatest`;
- target layer: `source-facing`, since the Stacks lemma asserts that the supremum of all weakly
  étale `K`-subalgebras is itself the greatest such subalgebra;
- core/canonical owner abstraction: the complete lattice `Subalgebra K A` together with the owner
  predicate `Algebra.IsWeaklyEtale K B`;
- primitive data: the supremum subalgebra `maximalWeaklyEtaleSubalgebra K A`;
- derived API: its weak étaleness and the universal upper-bound property, both obtained from the
  single source-facing `IsGreatest` statement below.

This file should therefore keep the `sSup` construction as the owner object and avoid presenting
projection lemmas as independent primitive data.
-/

/-- The supremum of all weakly étale `K`-subalgebras of `A`. -/
def maximalWeaklyEtaleSubalgebra : Subalgebra K A :=
  sSup {B : Subalgebra K A | Algebra.IsWeaklyEtale K B}

namespace MaximalWeaklyEtaleSubalgebraNotation

/- The textbook surface is `B_max(A/K)`. As elsewhere in the project, the scoped Lean notation
uses `⁄` for the parameterized owner form. -/
@[inherit_doc maximalWeaklyEtaleSubalgebra]
scoped notation:max "B_max(" A "⁄" K ")" => maximalWeaklyEtaleSubalgebra K A

end MaximalWeaklyEtaleSubalgebraNotation

open scoped MaximalWeaklyEtaleSubalgebraNotation

-- Proof sketch: the collection of weakly étale `K`-subalgebras of `A` is directed because the
-- image in `A` of the tensor product of two such subalgebras is again weakly étale. Lemma
-- `15.105.14` then shows that the filtered colimit, identified with the supremum subalgebra, is
-- weakly étale over `K`, and `le_sSup` gives the universal upper-bound property in the lattice of
-- `K`-subalgebras.
/-- Lemma 15.106.2: the supremum of all weakly étale `K`-subalgebras of `A` is a greatest weakly
étale `K`-subalgebra of `A`. -/
theorem isGreatest_maximalWeaklyEtaleSubalgebra :
    IsGreatest {B : Subalgebra K A | Algebra.IsWeaklyEtale K B}
      B_max(A⁄K) := sorry

/-- The supremum of weakly étale `K`-subalgebras of `A` is weakly étale over `K`. -/
theorem isWeaklyEtale_maximalWeaklyEtaleSubalgebra :
    Algebra.IsWeaklyEtale K B_max(A⁄K) :=
  (isGreatest_maximalWeaklyEtaleSubalgebra K A).1

/-- Every weakly étale `K`-subalgebra of `A` is contained in the maximal weakly étale
`K`-subalgebra. -/
theorem le_maximalWeaklyEtaleSubalgebra
    (B : Subalgebra K A) (hB : Algebra.IsWeaklyEtale K B) :
    B ≤ B_max(A⁄K) :=
  (isGreatest_maximalWeaklyEtaleSubalgebra K A).2 <|
    show B ∈ {B : Subalgebra K A | Algebra.IsWeaklyEtale K B} from hB

end

/-! ### Lemma_15_106_3 (from Chap15) -/
universe u v w x

open CategoryTheory
open CategoryTheory.Limits

section

open scoped MaximalWeaklyEtaleSubalgebraNotation

variable {K : Type u} [Field K]
variable {A' : Type v} [CommRing A'] [Algebra K A']
variable {A : Type w} [CommRing A] [Algebra K A]

local notation "A_red" => A ⧸ nilradical A
local notation "B_red" => B_max(A_red⁄K)

/- Domain-style sampling for Lemma 15.106.3:
- primary domain: functoriality and permanence of the owner subalgebra `B_max(A⁄K)` under
  `K`-algebra maps, filtered colimits, reduction, and finite products;
- sampled owner declarations:
  `maximalWeaklyEtaleSubalgebra`,
  `le_maximalWeaklyEtaleSubalgebra`,
  `CommAlgCat`,
  `PreservesFilteredColimits`,
  `Subalgebra.map`,
  `Subalgebra.comap`,
  `Algebra.IsSeparable`,
  `Algebra.IsSeparable.isAlgebraic`;
- best owner abstraction: `B_max(A⁄K)` from `Lemma_15_106_2` is the primitive source-facing
  object, and the filtered-colimit clause `(3)` is best expressed by the induced endofunctor on
  `CommAlgCat K`; the directed-union equality inside a fixed ambient algebra is a bridge/view
  specialization of that owner-level statement;
- layer triage:
  part `(1)` is `bridge/view`,
  part `(3)` is `source-facing` at the functorial filtered-colimit level and only secondarily a
  directed-subalgebra specialization,
  parts `(2)` and `(4)` through `(7)` remain source-facing consequences about the same owner;
- primitive vs. derived:
  the primitive data here is still only the owner subalgebra `B_max`; containment of its image,
  the induced `CommAlgCat` endofunctor, its filtered-colimit preservation, reduction maps, and
  field/separability consequences are derived API.

This file should therefore keep the image statement as the owner-level subalgebra inequality,
package it into the canonical endofunctor on `CommAlgCat K`, and state filtered-colimit
compatibility through `PreservesFilteredColimits` before specializing to directed unions inside a
fixed ambient algebra.
-/

namespace AlgHom

-- Proof sketch: the image of `B_max(A')` inside `A` is weakly étale over `K` by
-- Lemma `15.106.1 (6)`, so maximality of `B_max(A)` forces that image to lie in
-- `B_max(A)`.
/-- The image of the maximal weakly étale `K`-subalgebra under a `K`-algebra map is contained in
the maximal weakly étale `K`-subalgebra of the target. -/
theorem map_maximalWeaklyEtaleSubalgebra_le
    (f : A' →ₐ[K] A) :
    (B_max(A'⁄K)).map f ≤ B_max(A⁄K) := sorry

/-- An element of `B_max(A'/K)` maps into `B_max(A/K)` under any `K`-algebra map `A' → A`. -/
theorem map_maximalWeaklyEtaleSubalgebra_mem
    (f : A' →ₐ[K] A) (x : B_max(A'⁄K)) :
    f x ∈ B_max(A⁄K) :=
  map_maximalWeaklyEtaleSubalgebra_le f <|
    show f x ∈ (B_max(A'⁄K)).map f from ⟨x, x.2, rfl⟩

/-- Lemma 15.106.3 (1): any `K`-algebra map `A' → A` induces a `K`-algebra map
`B_max(A') → B_max(A)`. -/
def maximalWeaklyEtaleSubalgebraMap
    (f : A' →ₐ[K] A) :
    B_max(A'⁄K) →ₐ[K] B_max(A⁄K) :=
  (f.comp B_max(A'⁄K).val).codRestrict B_max(A⁄K)
    (map_maximalWeaklyEtaleSubalgebra_mem f)

/-- The induced map on maximal weakly étale subalgebras agrees with the ambient algebra map. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraMap_apply
    (f : A' →ₐ[K] A) (x : B_max(A'⁄K)) :
    ↑(maximalWeaklyEtaleSubalgebraMap f x) = f x := rfl

end AlgHom

/-- The maximal weakly étale subalgebra construction as an endofunctor on `K`-algebras. -/
def maximalWeaklyEtaleSubalgebraFunctor (K : Type u) [Field K] :
    CommAlgCat K ⥤ CommAlgCat K where
  obj A := CommAlgCat.of K B_max(A⁄K)
  map f := CommAlgCat.ofHom <| AlgHom.maximalWeaklyEtaleSubalgebraMap f.hom
  map_id A := by
    apply CommAlgCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    ext x
    rfl

-- Proof sketch: the inclusion `A' ↪ A` gives the forward containment by part `(1)`. For the
-- reverse containment, the preimage `(B_max(A)).comap i` is weakly étale over `K`, so maximality
-- of `B_max(A')` forces equality.
/-- Lemma 15.106.3 (2): if `A'` is identified with a `K`-subalgebra of `A`, then `B_max(A')`
is the intersection `B_max(A) ∩ A'`, written as a comap. -/
theorem maximalWeaklyEtaleSubalgebra_comap_of_injective
    (i : A' →ₐ[K] A) (hi : Function.Injective i) :
    B_max(A'⁄K) = (B_max(A⁄K)).comap i := sorry

-- Proof sketch: view `B_max` as the functor `maximalWeaklyEtaleSubalgebraFunctor K` on
-- `CommAlgCat K`. For a filtered diagram `F`, each finitely presented weakly étale `K`-subalgebra
-- of the colimit algebra factors through some stage by Lemma `10.127.3`, while part `(1)` gives
-- the forward maps from the stagewise `B_max`; this identifies the mapped cocone as colimiting.
/-- Lemma 15.106.3 (3): the maximal weakly étale subalgebra construction commutes with filtered
colimits, expressed canonically as preservation of filtered colimits by the endofunctor
`maximalWeaklyEtaleSubalgebraFunctor K` on `CommAlgCat K`. -/
theorem maximalWeaklyEtaleSubalgebra_preservesFilteredColimits
    (K : Type u) [Field K] :
    PreservesFilteredColimits (maximalWeaklyEtaleSubalgebraFunctor K) := sorry

-- Proof sketch: this is the directed-union specialization of the filtered-colimit owner theorem
-- above, after identifying a directed family of `K`-subalgebras of `A` with a filtered diagram in
-- `CommAlgCat K` whose colimit is `A`.
/-- Directed-union specialization of Lemma 15.106.3 (3): for a directed union presentation
`A = colim Aᵢ` by `K`-subalgebras, `B_max(A)` is the directed supremum of the images of the
stagewise maximal weakly étale subalgebras `B_max(Aᵢ)`. -/
theorem maximalWeaklyEtaleSubalgebra_eq_sSup_of_directed
    {ι : Type x} (Aᵢ : ι → Subalgebra K A)
    (hdir : Directed (· ≤ ·) Aᵢ) (hA : sSup (Set.range Aᵢ) = ⊤) :
    B_max(A⁄K) =
      sSup (Set.range fun i ↦
        (B_max(Aᵢ i⁄K)).map (Aᵢ i).val) := sorry

/-- The canonical map from `B_max(A)` to the maximal weakly étale subalgebra of the reduction of
`A`. -/
def maximalWeaklyEtaleSubalgebraReductionMap
    (K : Type u) [Field K] (A : Type w) [CommRing A] [Algebra K A] :
    B_max(A⁄K) →ₐ[K] B_max(A ⧸ nilradical A⁄K) :=
  (Ideal.Quotient.mkₐ K (nilradical A)).maximalWeaklyEtaleSubalgebraMap

-- Proof sketch: write `B_max(A_red)` as a filtered colimit of étale `K`-algebras and lift each
-- étale stage across `A → A_red`; maximality makes the induced map surjective. Its kernel is made
-- of nilpotents, but `B_max(A_red)` is reduced by Lemma `15.106.1 (1)`, so the kernel vanishes.
/-- Lemma 15.106.3 (4): the canonical map `B_max(A) → B_max(A_red)` is an isomorphism, expressed
as bijectivity of the induced algebra map to the quotient by the nilradical. -/
theorem bijective_maximalWeaklyEtaleSubalgebraReductionMap :
    Function.Bijective (maximalWeaklyEtaleSubalgebraReductionMap K A) := sorry

-- Proof sketch: each projection from a finite product to one factor and each diagonal inclusion of
-- a factor into the product gives maps between the corresponding `B_max`. Using part `(1)`, these
-- maps identify the maximal weakly étale subalgebra of the product with the product of the
-- stagewise maximal weakly étale subalgebras.
/-- Lemma 15.106.3 (5): for a finite family of `K`-algebras, the maximal weakly étale subalgebra
of the product is the product of the maximal weakly étale subalgebras of the factors. -/
theorem maximalWeaklyEtaleSubalgebra_pi
    {ι : Type x} [Finite ι] (Aᵢ : ι → Type v)
    [∀ i, CommRing (Aᵢ i)] [∀ i, Algebra K (Aᵢ i)] :
    B_max(((i : ι) → Aᵢ i)⁄K) = Subalgebra.pi Set.univ (fun i ↦ B_max(Aᵢ i⁄K)) := sorry

-- Proof sketch: `B_max(A)` is weakly étale over `K` by Lemma `15.106.2`, so Lemma `15.106.1 (4)`
-- applies directly. The hypothesis on idempotents of `A` forces the same condition on the
-- subalgebra `B_max(A)`.
/-- Lemma 15.106.3 (6): if `A` has no nontrivial idempotents, then `B_max(A)` is a field. -/
theorem isField_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
    [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField B_max(A⁄K) := sorry

-- Proof sketch: part `(6)` makes `B_max(A)` a field, and Lemma `15.106.1 (5)` then gives the
-- canonical owner `Algebra.IsSeparable K B_max(A⁄K)`. Algebraicity is a derived consequence via
-- `Algebra.IsSeparable.isAlgebraic`.
/-- Lemma 15.106.3 (7): if `A` has no nontrivial idempotents, then `B_max(A)` is a separable
algebraic extension of `K`, expressed through the canonical owner `Algebra.IsSeparable`. -/
theorem isSeparable_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
    [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Algebra.IsSeparable K B_max(A⁄K) := sorry

/-- Under the hypotheses of part `(7)`, `B_max(A)` is algebraic over `K`. -/
theorem isAlgebraic_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one
    [Nontrivial A]
    (hA : ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Algebra.IsAlgebraic K B_max(A⁄K) := by
  let _ : Algebra.IsSeparable K B_max(A⁄K) :=
    isSeparable_maximalWeaklyEtaleSubalgebra_of_idempotents_eq_zero_or_one hA
  infer_instance

end

/-! ### Lemma_15_106_4 (from Chap15) -/
open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped MaximalWeaklyEtaleSubalgebraNotation

variable {K : Type u} [Field K]
variable {L : Type v} [Field L] [Algebra K L]
variable {A : Type w} [CommRing A] [Algebra K A]
variable (K) (L) (A)

/- Domain-style sampling for Lemma 15.106.4:
- primary domain: commutative algebra of maximal weakly étale subalgebras under base change along
  a field extension;
- sampled owner declarations:
  `maximalWeaklyEtaleSubalgebra`,
  `isWeaklyEtale_maximalWeaklyEtaleSubalgebra`,
  `le_maximalWeaklyEtaleSubalgebra`,
  `Algebra.IsWeaklyEtale.baseChange`;
- target layer: `source-facing`, since the Stacks lemma identifies the base change of `B_max(A⁄K)`
  with `B_max((A ⊗[K] L)⁄L)`;
- core/canonical owner abstraction: the source-facing owner remains `B_max` from
  `Lemma_15_106_2`; the only primitive bridge data here is the tensor-base-change hom obtained
  from the inclusion `B_max(A⁄K) ↪ A`;
- primitive vs. derived: the primitive data is the ambient tensor-base-change hom
  `B_max(A⁄K) ⊗[K] L →ₐ[L] A ⊗[K] L`; landing in `B_max((A ⊗[K] L)⁄L)` and bijectivity are
  derived API.

This file should therefore state the canonical map directly as an `L`-algebra hom into
`B_max((A ⊗[K] L)⁄L)`, rather than routing the public surface through a `K`-algebra map into a
`restrictScalars` codomain.
-/

/-- The ambient tensor-base-change map `B_max(A/K) ⊗[K] L → A ⊗[K] L` obtained by tensoring the
inclusion `B_max(A/K) ↪ A` with `L`, viewed in its natural `L`-algebra form. -/
def maximalWeaklyEtaleSubalgebraTensorBaseChangeMap :
    B_max(A⁄K) ⊗[K] L →ₐ[L] A ⊗[K] L :=
  { __ := (Algebra.TensorProduct.map B_max(A⁄K).val (AlgHom.id K L)).toRingHom
    commutes' := by
      intro l
      change (Algebra.TensorProduct.map B_max(A⁄K).val (AlgHom.id K L))
          ((includeRight : L →ₐ[K] B_max(A⁄K) ⊗[K] L) l) =
        (includeRight : L →ₐ[K] A ⊗[K] L) l
      simp }

-- Proof sketch: `B_max(A/K)` is weakly étale over `K` by Lemma `15.106.2`, so after base change
-- along `K → L` it remains weakly étale over `L`. Since the tensor-base-change map lands inside
-- `A ⊗[K] L`, maximality of `B_max((A ⊗[K] L)/L)` forces its image to lie in that subalgebra.
/-- The tensor-base-change map from `B_max(A/K) ⊗[K] L` lands in the maximal weakly étale
`L`-subalgebra of `A ⊗[K] L`. -/
theorem maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_mem
    (x : B_max(A⁄K) ⊗[K] L) :
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
      B_max(A⁄K) ⊗[K] L → A ⊗[K] L) x ∈ B_max((A ⊗[K] L)⁄L) := sorry

/-- The canonical map from `B_max(A/K) ⊗[K] L` to the maximal weakly étale `L`-subalgebra of
`A ⊗[K] L`. -/
def maximalWeaklyEtaleSubalgebraTensorBaseChange :
    B_max(A⁄K) ⊗[K] L →ₐ[L] B_max((A ⊗[K] L)⁄L) :=
  (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A).codRestrict
    B_max((A ⊗[K] L)⁄L)
    (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap_mem K L A)

/-- The codomain-restricted tensor-base-change map agrees with the ambient tensor-base-change map
after forgetting the target subalgebra. -/
@[simp]
theorem maximalWeaklyEtaleSubalgebraTensorBaseChange_apply
    (x : B_max(A⁄K) ⊗[K] L) :
    ↑((maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
      B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) x) =
      (maximalWeaklyEtaleSubalgebraTensorBaseChangeMap K L A :
        B_max(A⁄K) ⊗[K] L → A ⊗[K] L) x := rfl

-- Proof sketch: first reduce to the case where `L` is algebraically closed, then to finite type
-- and reduced `K`-algebras, then to total quotient rings, and finally to finitely generated field
-- extensions. In the field case, decompose after base change using the separable field
-- `B_max(A/K)` and show each factor has maximal weakly étale subalgebra equal to `L`.
/-- Lemma 15.106.4: the canonical map
`B_max(A/K) ⊗[K] L → B_max((A ⊗[K] L)/L)` is bijective, i.e. base change carries the maximal
weakly étale `K`-subalgebra of `A` to the maximal weakly étale `L`-subalgebra of `A ⊗[K] L`. -/
theorem bijective_maximalWeaklyEtaleSubalgebraTensorBaseChange :
    Function.Bijective
      (maximalWeaklyEtaleSubalgebraTensorBaseChange K L A :
        B_max(A⁄K) ⊗[K] L → B_max((A ⊗[K] L)⁄L)) := sorry

end
