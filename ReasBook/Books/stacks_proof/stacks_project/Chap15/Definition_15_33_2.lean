import Mathlib
import StacksProject_2024.Chap15.Definition_15_32_1
import StacksProject_2024.Chap15.Lemma_15_30_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

noncomputable section

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
@[stacks 07D0]
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

/-- Helper for Definition 15.33.2: the empty polynomial algebra over `A` is canonically `A`. -/
noncomputable def empty_polynomial_algEquiv (A : Type u) [CommRing A] :
    MvPolynomial (Fin 0) A ≃ₐ[A] A :=
  (MvPolynomial.renameEquiv A (_root_.finZeroEquiv' : Fin 0 ≃ PEmpty.{u + 1})).trans
    (MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1})

/-- Helper for Definition 15.33.2: the identity map admits the empty `Fin 0` polynomial
presentation. -/
noncomputable def empty_identity_presentation (A : Type u) [CommRing A] :
    Algebra.Generators A A (Fin 0) :=
  Algebra.Generators.ofAlgHom
    (empty_polynomial_algEquiv A).toAlgHom
    (empty_polynomial_algEquiv A).surjective

/-- Helper for Definition 15.33.2: the kernel of the empty identity presentation is the zero
ideal. -/
lemma empty_identity_presentation_ker_eq_bot (A : Type u) [CommRing A] :
    (empty_identity_presentation A).ker = ⊥ := by
  -- Unfold the chosen presentation and identify its kernel with the kernel of an algebra
  -- equivalence.
  rw [empty_identity_presentation, Algebra.Generators.ker_ofAlgHom]
  -- The defining algebra equivalence is injective, so its ring-hom kernel is trivial.
  exact (RingHom.injective_iff_ker_eq_bot _).1 (empty_polynomial_algEquiv A).injective

/-- Helper for Definition 15.33.2: the zero ideal of a commutative ring is Koszul-regular,
witnessed by the empty localized sequence. -/
lemma bot_isKoszulRegularIdeal (R : Type u) [CommRing R] :
    ((⊥ : Ideal R)).IsKoszulRegularIdeal := by
  -- Unwind the local criterion and use the empty sequence after localizing away from `1`.
  rw [Ideal.isKoszulRegularIdeal_iff]
  intro p hp hbot
  refine ⟨1, ?_, 0, ([] : List (Localization.Away (1 : R))).get, ?_, ?_⟩
  · -- A prime ideal is proper, so `1` does not lie in it.
    simpa [Ideal.eq_top_iff_one] using hp.ne_top
  · -- The empty sequence is weakly regular, hence Koszul-regular.
    have hweak :
        RingTheory.Sequence.IsWeaklyRegular
          (Localization.Away (1 : R)) ([] : List (Localization.Away (1 : R))) :=
      RingTheory.Sequence.IsWeaklyRegular.nil
        (R := Localization.Away (1 : R)) (M := Localization.Away (1 : R))
    have hkoszul :
        RingTheory.Sequence.IsKoszulRegularOn
          (Localization.Away (1 : R)) ([] : List (Localization.Away (1 : R))).get :=
      hweak.isKoszulRegularOn
    simpa [RingTheory.Sequence.IsKoszulRegularSequence] using hkoszul
  · -- Both the localized zero ideal and the span of an empty family are the zero ideal.
    simp

/-- The identity ring map is a local complete intersection. -/
@[instance] theorem id :
    (RingHom.id A).IsLocalCompleteIntersection := by
  let _ : Algebra A A := (RingHom.id A).toAlgebra
  refine RingHom.IsLocalCompleteIntersection.mk ?_
  -- Witness the identity map by the empty polynomial presentation.
  refine ⟨0, empty_identity_presentation A, ?_⟩
  -- The kernel is zero, and the zero ideal is Koszul-regular by the empty-sequence criterion.
  exact
    (empty_identity_presentation_ker_eq_bot A) ▸
      bot_isKoszulRegularIdeal (MvPolynomial (Fin 0) A)

end IsLocalCompleteIntersection

end

end

end RingHom
