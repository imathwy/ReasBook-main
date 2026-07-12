import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.RepresentationTheory.Induced

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Rep

noncomputable section

universe u v

section ExistenceAndAdjunction

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

variable (H : Subgroup G) (W : Rep k H)

-- Source/core/bridge triage for Remark 7-7.1-2:
-- * source-facing: existence of the induced representation, Frobenius reciprocity, and
--   transitivity of induction.
-- * core/canonical owners sampled in the induction domain:
--   `Rep.ind`, `Rep.indResHomEquiv`, `Rep.indResAdjunction`, and
--   `CategoryTheory.Adjunction.leftAdjointCompIso`.
-- * primitive data: a subgroup inclusion or group homomorphisms together with the source
--   representation.
-- * derived API: the transitivity isomorphism, obtained by specializing adjunction composition to
--   `indResAdjunction`.
/- Remark 7-7.1-2 (1): the induced representation of `W` along the subgroup inclusion `H ≤ G`
is the canonical mathlib object `ind H.subtype W`, so existence is built into the owner
declaration and uniqueness is up to the usual isomorphism notion in `Rep k G`. -/
#check (Rep.ind H.subtype W : Rep k G)

variable (E : Rep k G)

/- Frobenius reciprocity identifies the `H`-equivariant maps
`W ⟶ res H.subtype E` with the `G`-equivariant maps `ind H.subtype W ⟶ E`; this is the
canonical linear equivalence `indResHomEquiv H.subtype W E`. -/
#check
  (Rep.indResHomEquiv H.subtype W E :
    (Rep.ind H.subtype W ⟶ E) ≃ₗ[k] (W ⟶ Rep.res H.subtype E))

end ExistenceAndAdjunction

section Transitivity

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {H : Type v} [Group H]
variable {K : Type v} [Group K]
variable (φ : G →* H) (ψ : H →* K)

/- Remark 7-7.1-2 (2): induction is transitive. For homomorphisms `φ : G →* H` and
`ψ : H →* K`, the canonical transitivity isomorphism
`indFunctor k φ ⋙ indFunctor k ψ ≅ indFunctor k (ψ.comp φ)` is exactly the
specialization of the adjunction composition isomorphism to `Rep.indResAdjunction`. -/
#check
  ((indResAdjunction k φ).leftAdjointCompIso
    (indResAdjunction k ψ)
    (indResAdjunction k (ψ.comp φ))
    (eqToIso rfl) :
      indFunctor k φ ⋙ indFunctor k ψ ≅ indFunctor k (ψ.comp φ))

end Transitivity
