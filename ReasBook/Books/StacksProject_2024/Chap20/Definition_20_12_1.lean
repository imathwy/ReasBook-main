import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Opposite TopologicalSpace TopCat

variable {X : TopCat.{u}}

/- Domain-style sampling for Definition 20.12.1:
- primary domain: set-valued presheaves on a topological space, with flasqueness expressed through
  restriction morphisms;
- sampled owner API:
  `TopCat.Presheaf.IsFlasque`,
  `TopCat.Sheaf.IsFlasque`,
  `CategoryTheory.epi_iff_surjective`,
- source/core/bridge triage:
  `source-facing`: the Stacks-project condition that every restriction map `F(V) → F(U)` is
  surjective for `U ≤ V`;
  `core/canonical`: `TopCat.Presheaf.IsFlasque F`;
  `bridge/view`: the `Type`-valued reformulation of the epi field as surjectivity of restriction
  maps.

Primitive data are only the presheaf `F` and the owner predicate `Presheaf.IsFlasque F`, whose
single field asks that every restriction morphism be epi. The elementwise surjectivity condition
is derived API from that owner, so this file should recall `Presheaf.IsFlasque` directly and keep
the restriction-surjectivity formulation only as a thin companion theorem.
-/

/- Definition 20.12.1: a presheaf of sets on a topological space `X` is flasque (or flabby) in
the canonical mathlib sense `TopCat.Presheaf.IsFlasque`. -/
recall Presheaf.IsFlasque

-- Proof sketch: unwind `TopCat.Presheaf.IsFlasque`, which asks that every restriction morphism be
-- an epimorphism; for `Type`-valued presheaves, epimorphisms are exactly surjective maps by
-- `CategoryTheory.epi_iff_surjective`.
/-- A set-valued presheaf is flasque exactly when each restriction map along an inclusion of open
sets is surjective. -/
theorem presheaf_isFlasque_iff_restriction_surjective
    (F : X.Presheaf (Type v)) :
    Presheaf.IsFlasque F ↔
      ∀ ⦃U V : Opens X⦄ (hUV : U ≤ V), Function.Surjective (F.map (homOfLE hUV).op) := by
  constructor
  · intro h U V hUV
    let _ : Epi (F.map (homOfLE hUV).op) := h.epi (homOfLE hUV).op
    exact (CategoryTheory.epi_iff_surjective _).1 inferInstance
  · intro h
    exact ⟨fun i ↦ (CategoryTheory.epi_iff_surjective _).2 (by
      simpa using h (leOfHom i.unop))⟩
