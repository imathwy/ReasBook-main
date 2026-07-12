import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S]
variable {N : Type w} [AddCommGroup N] [Module R N]

/- Lemma 10.82.15: if `R → S` is faithfully flat, then for every `R`-module `N` the canonical
map `N →ₗ[R] S ⊗[R] N` is injective, which is the Lean form of saying that `R → S` is
universally injective as a map of `R`-modules. This is exactly the canonical theorem
`Module.FaithfullyFlat.tensorProduct_mk_injective`. -/
recall Module.FaithfullyFlat.tensorProduct_mk_injective

/- Companion check: the textbook corollary `R ∩ IS = I` is the canonical contraction statement
`(I.map (algebraMap R S)).comap (algebraMap R S) = I`. This is exactly
`Ideal.comap_map_eq_self_of_faithfullyFlat`. -/
recall Ideal.comap_map_eq_self_of_faithfullyFlat

end
