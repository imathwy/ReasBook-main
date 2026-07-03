import stacks_project.Chap10.Lemma_10_133_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped PrincipalParts

/- Domain triage:
* primary domain: base change for modules of principal parts over a commutative square of rings;
* sampled owner API:
  `principal_parts_module`,
  `principal_parts_relation_submodule`,
  `principal_parts_linear_map_equiv_differential_operators`,
  `principalPartsBaseChangeMap`;
* source-facing owner: `principalPartsBaseChangeMap`;
* core/canonical owner: `principal_parts_module`;
* bridge/view: the free-presentation map
  `principalPartsBaseChangeMapOnFree` and its compatibility with
  `principal_parts_relation_submodule`.

Primitive-vs-derived split:
* primitive data: the commutative square `A → B`, `A' → B'` and the `B`-linear map `M → M'`;
* derived API: the induced quotient map on principal parts and its composition theorem.

This file is itself the chapter owner for principal-parts base change, so the refinement keeps the
source-facing owner `principalPartsBaseChangeMap` and removes only duplicate local surface syntax.
-/

section BaseChange

variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']

variable {M M' : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']

/-- The map on the free presentations induced by a morphism of modules over a commutative square
of rings. -/
private abbrev principalPartsBaseChangeMapOnFree (f : M →ₗ[B] M') :
    (M →₀ B) →ₗ[B] (M' →₀ B') :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap B B')).comp (Finsupp.lmapDomain B B f)

-- Proof sketch: check the image of each generator of
-- `principal_parts_relation_submodule` for the source data `A → B`, `M`, and `k`. Additivity
-- relations are preserved
-- by `Finsupp.lmapDomain`; the `A`-linearity relations are transported across the commutative
-- square by `f`; and iterated commutator relations are sent to the corresponding relations over
-- `B'`.
/-- The map on free presentations sends the order-`k` principal-parts relations over `A → B`
into the corresponding relation submodule over `A' → B'`. -/
private theorem principalPartsRelationSubmodule_le_comap_baseChangeMapOnFree
    (k : ℕ) (f : M →ₗ[B] M') :
    principal_parts_relation_submodule A B M k ≤
      Submodule.comap (principalPartsBaseChangeMapOnFree f)
        ((principal_parts_relation_submodule A' B' M' k).restrictScalars B) := sorry

/-- Remark 10.133.7: a commutative square of rings together with a `B`-linear map `M → M'`
induces a canonical map `P^k_{B/A}(M) → P^k_{B'/A'}(M')` on modules of principal parts. -/
abbrev principalPartsBaseChangeMap (k : ℕ) (f : M →ₗ[B] M') :
    P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M') :=
  Submodule.mapQ
    (principal_parts_relation_submodule A B M k)
    ((principal_parts_relation_submodule A' B' M' k).restrictScalars B)
    (principalPartsBaseChangeMapOnFree f)
    (principalPartsRelationSubmodule_le_comap_baseChangeMapOnFree k f)

end BaseChange

section Composition

variable {A B A' B' A'' B'' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [Algebra A' A''] [Algebra B' B''] [Algebra A' B''] [Algebra A'' B'']
variable [Algebra A A''] [Algebra A B''] [Algebra B B'']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable [IsScalarTower A' B' B''] [IsScalarTower A' A'' B'']
variable [IsScalarTower A A' A''] [IsScalarTower B B' B'']
variable [IsScalarTower A B B''] [IsScalarTower A A'' B'']

variable {M M' M'' : Type u}
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']
variable [AddCommGroup M''] [Module B'' M''] [Module A M''] [Module A' M''] [Module A'' M'']
variable [Module B' M''] [Module B M'']
variable [IsScalarTower B B' M'']
variable [IsScalarTower A'' B'' M''] [IsScalarTower B' B'' M''] [IsScalarTower B B'' M'']
variable [IsScalarTower A A'' M''] [IsScalarTower A' A'' M'']

-- Proof sketch: on the free presentations this is the compatibility of `Finsupp.lmapDomain` and
-- `Finsupp.mapRange.linearMap` with composition. Passing to quotients via `Submodule.mapQ_comp`
-- gives the result for principal parts.
/-- The principal-parts base-change maps are compatible with further composition of ring squares
and module maps. -/
theorem principalPartsBaseChangeMap_comp (k : ℕ) (f : M →ₗ[B] M') (g : M' →ₗ[B'] M'') :
    ((principalPartsBaseChangeMap k g :
          P^{k}_{B'⁄A'}(M') →ₗ[B'] P^{k}_{B''⁄A''}(M'')).restrictScalars B) ∘ₗ
        (principalPartsBaseChangeMap k f :
          P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B'⁄A'}(M')) =
      (principalPartsBaseChangeMap k (((g.restrictScalars B).comp f) : M →ₗ[B] M'') :
        P^{k}_{B⁄A}(M) →ₗ[B] P^{k}_{B''⁄A''}(M'')) := sorry

end Composition

end
