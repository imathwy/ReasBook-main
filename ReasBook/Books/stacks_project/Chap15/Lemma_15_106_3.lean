import Mathlib
import stacks_project.Chap15.Lemma_15_106_2

-- Declarations for this item will be appended below by the statement pipeline.

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
