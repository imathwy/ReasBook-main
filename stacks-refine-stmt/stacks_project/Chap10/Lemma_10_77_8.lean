import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [Ring R]
variable {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
variable {P : Type v} [AddCommGroup P] [Module R P]

/- 
Domain triage:
- primary domain: projective modules over a ring, glued from projective reductions modulo ideals;
- sampled owner-style declarations of the same kind:
  `Module.Projective.of_split`,
  `Module.Projective.iff_split_of_projective`,
  `Module.projective_of_localization_maximal`,
  `Ideal.pi_tensorProductMk_quotient_surjective`;
- owner abstraction: `Module.Projective R P`;
- primitive data: the ring `R`, module `P`, ideals `I`, `J` with `I ⊓ J = ⊥`, and projectivity of
  the two reductions modulo `I` and `J`;
- derived API: the resulting projectivity of `P`.

This item stays at the `source-facing` layer: it is a patching criterion whose natural public
conclusion is the owner predicate `Module.Projective`, not a renamed wrapper around an existing
owner theorem.
-/

-- Proof sketch: choose a surjection from a free `R`-module onto `P`, split it modulo `I` and
-- modulo `J` using the projectivity assumptions on the two quotients, and glue the two splittings
-- through the fiber-product description coming from `I ⊓ J = ⊥`. The resulting endomorphism of
-- `P` is the identity modulo `I` and modulo `J`, hence is an automorphism, so `P` is a direct
-- summand of a free module.
/-- Lemma 10.77.8: if ideals `I` and `J` of a ring `R` satisfy `I ∩ J = 0`, and the quotient
modules `P / IP` and `P / JP` are projective over `R / I` and `R / J` respectively, then `P` is a
projective `R`-module. -/
theorem projective_of_projective_quotients_of_inf_eq_bot (hIJ : I ⊓ J = ⊥)
    (hPI : Module.Projective (R ⧸ I) (P ⧸ (I • ⊤ : Submodule R P)))
    (hPJ : Module.Projective (R ⧸ J) (P ⧸ (J • ⊤ : Submodule R P))) :
    Module.Projective R P := sorry

end
