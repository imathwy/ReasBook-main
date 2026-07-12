import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/- Domain triage:
* primary domain: commutative algebra of ideals in quotient rings;
* source-facing layer: the textbook quotient statement for Jacobson rings and maximal ideals;
* core/canonical owner: mathlib's quotient ideal correspondence
  `Ideal.relIsoOfSurjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`;
* bridge/view layer: the maximal-ideal statement is the restriction of that owner order isomorphism
  along `Ideal.isMaximal_def`, with `OrderIso.isCoatom_iff` transporting maximality.
* sampled owner/style declarations in this domain:
  - `Ideal.relIsoOfSurjective`;
  - `Ideal.mk_ker`;
  - `Ideal.isMaximal_def`;
  - `isJacobsonRing_quotient`.
* primitive data vs. derived API: the only primitive datum is the ideal `I`; both the quotient
  ideal correspondence and the maximal-ideal restriction are derived from the owner abstraction.
-/

/- Lemma 10.35.17 (1): if `R` is a Jacobson ring and `I` is an ideal, then the quotient ring
`R ⧸ I` is again Jacobson. This is the canonical mathlib instance
`isJacobsonRing_quotient`. -/
recall isJacobsonRing_quotient

namespace Ideal.Quotient

/- Lemma 10.35.17 (2): maximal ideals of `R ⧸ I` correspond order-isomorphically to maximal
ideals of `R` containing `I`. This is the maximal-ideal restriction of the canonical quotient
ideal correspondence `Ideal.relIsoOfSurjective` for `Ideal.Quotient.mk I`. -/
@[stacks 00G9]
def orderIsoOfMaximal (I : Ideal R) :
    { J : Ideal (R ⧸ I) // J.IsMaximal } ≃o { K : Ideal R // I ≤ K ∧ K.IsMaximal } :=
  let e : Ideal (R ⧸ I) ≃o Set.Ici I :=
    (Ideal.relIsoOfSurjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).trans <|
      OrderIso.setCongr _ _ <| by
        ext K
        change (RingHom.ker (Ideal.Quotient.mk I) ≤ K) ↔ I ≤ K
        rw [Ideal.mk_ker]
  { toFun := fun J ↦
      ⟨(e J.1).1, (e J.1).2,
        Ideal.isMaximal_def.2 <|
          IsCoatom.of_isCoatom_coe_Ici <| (OrderIso.isCoatom_iff e J.1).2 <|
            Ideal.isMaximal_def.1 J.2⟩
    invFun := fun K ↦
      ⟨e.symm ⟨K.1, K.2.1⟩,
        Ideal.isMaximal_def.2 <|
          (OrderIso.isCoatom_iff e.symm ⟨K.1, K.2.1⟩).2 <|
            IsCoatom.Ici (Ideal.isMaximal_def.1 K.2.2) K.2.1⟩
    left_inv := fun J ↦ by
      apply Subtype.ext
      simp [e]
    right_inv := fun K ↦ by
      apply Subtype.ext
      simpa [e] using congrArg Subtype.val (e.right_inv ⟨K.1, K.2.1⟩)
    map_rel_iff' := fun {J J'} ↦ e.map_rel_iff }

end Ideal.Quotient

end
