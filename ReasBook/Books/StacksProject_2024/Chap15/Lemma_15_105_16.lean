import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_154_3
import StacksProject_2024.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section TFAE

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]

/- Domain-style sampling for Lemma 15.105.16:
- primary domain: weakly étale algebras over a field and their filtered-colimit presentations by
  étale algebras;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `Algebra.Etale`,
  `RingHom.IsFilteredColimitOfEtale`,
  `Subalgebra.fg_iff_finiteType`;
- best owner abstraction: `Algebra.IsWeaklyEtale K B` is the core/canonical owner on the map
  `K → B`, while `(algebraMap K B).IsFilteredColimitOfEtale` is the source-facing
  filtered-colimit bridge already owned upstream in Chapter 10;
- primitive data: the owner class `Algebra.IsWeaklyEtale K B` and finite generation of a
  `K`-subalgebra expressed by `A.FG`;
- derived API: the TFAE below and the later `FiniteType` specialization obtained from
  `Subalgebra.fg_iff_finiteType`.

This file keeps the source-facing `FG` theorem as the owner statement for finitely generated
subalgebras and leaves `FiniteType` as a downstream bridge, rather than maintaining parallel public
copies of the same result.
-/

-- Proof sketch: over a field, every `K`-algebra is flat over `K`, so flatness of the tensor-square
-- multiplication map is equivalent to weakly étaleness. The implication from a filtered colimit of
-- étale `K`-algebras to weakly étale is Lemma `15.105.14`, while the converse is proved by showing
-- that every finitely generated `K`-subalgebra is étale and then expressing `B` as the filtered
-- colimit of its finitely generated `K`-subalgebras.
/-- Lemma 15.105.16: for a `K`-algebra `B`, the following are equivalent: the multiplication map
`B ⊗[K] B → B` is flat, the structure map `K → B` is weakly étale, and `B` is a filtered colimit
of étale `K`-algebras. -/
theorem weaklyEtale_over_field_tfae :
    List.TFAE
      [ (Algebra.TensorProduct.lmul' K : B ⊗[K] B →ₐ[K] B).Flat,
        Algebra.IsWeaklyEtale K B,
        (algebraMap K B).IsFilteredColimitOfEtale ] := sorry

end TFAE

section

variable {K : Type u} {B : Type v} [Field K] [CommRing B] [Algebra K B]

-- Proof sketch: assume `K → B` is weakly étale. For a finitely generated `K`-subalgebra `A ⊆ B`,
-- every localization `B_𝔮` at a prime is weakly étale over `K`, hence a separable algebraic field
-- extension of `K`. The residue fields of the minimal primes of `A` are therefore finite
-- separable over `K`, so `A` is reduced and zero-dimensional. A reduced finite type `K`-algebra of
-- dimension zero is a finite product of finite separable field extensions, hence étale over `K`.
/-- Every finitely generated `K`-subalgebra of a weakly étale `K`-algebra is étale over `K`. -/
theorem etale_of_fg_subalgebra_of_isWeaklyEtale
    [Algebra.IsWeaklyEtale K B] (A : Subalgebra K B) (hA : A.FG) :
    Algebra.Etale K A := sorry

end
