import Mathlib
import StacksProject_2024.Chap17.Definition_17_10_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Domain-style sampling for Lemma 17.10.8:
- primary domain: quasi-coherent `\mathcal O_X`-modules and associated module sheaves on open
  subspaces;
- inspected owner declarations:
  `associatedModuleSheaf`,
  `RingedSpace.restrict`,
  `RingedSpace.Hom.pullback`,
  `SheafedSpace.Γ`;
- best owner abstraction: the source-facing existence statement should be expressed directly on the
  restricted ringed space `X.restrict U.isOpenEmbedding`, with owner `associatedModuleSheaf` in its
  identity-map form `𝓕_ M`, rather than through a separate ring-map bridge from `Γ(U, \mathcal O_X)`;
- primitive data: `U`, `x ∈ U`, the open-inclusion morphism `X.ofRestrict U.isOpenEmbedding`, the
  restricted ringed space `X.restrict U.isOpenEmbedding`, and a module `M` over its top-sections
  ring `(X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)`;
- derived API: the neighborhood existence conclusion together with the direct isomorphism witness
  `((X.ofRestrict U.isOpenEmbedding)^*).obj ℱ ≅ 𝓕_ M`.

Source/core/bridge triage:
- `source-facing`: existence of an open neighbourhood on which `ℱ` is associated to a module over
  the ring of sections of that neighbourhood;
- `core/canonical`: `associatedModuleSheaf` on the restricted ringed space and the pullback owner
  `j^*` for `j := X.ofRestrict U.isOpenEmbedding`;
- `bridge/view`: the upstream identification between sections on `U` and global sections of the
  restricted ringed space stays internal and does not belong in the public theorem surface.
-/

-- Proof sketch: choose a quasi-compact neighbourhood basis element around `x`, shrink to an open
-- neighbourhood on which the local cokernel presentation of the quasi-coherent sheaf `ℱ` is given
-- by a genuine matrix of sections over that open, and then invoke the associated-module-sheaf
-- construction on the restricted ringed space.
/-- Lemma 17.10.8: if `x` has a neighbourhood basis consisting of quasi-compact neighbourhoods,
then every quasi-coherent `\mathcal O_X`-module becomes on some open neighbourhood of `x`
via an isomorphism to a module sheaf associated to a module over the ring of sections on that
neighbourhood. -/
theorem exists_open_neighborhood_associatedGlobalSectionsModuleSheaf_of_isQuasicoherent
    {X : RingedSpace.{u}} (x : X)
    (hx : (𝓝 x).HasBasis (fun K : Set X ↦ K ∈ 𝓝 x ∧ IsCompact K) id)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ (U : Opens X) (_ : x ∈ U)
      (M : ModuleCat ((X.restrict U.isOpenEmbedding).presheaf.obj (op ⊤))),
        Nonempty
          (((X.ofRestrict U.isOpenEmbedding)^*).obj ℱ ≅
            𝓕_ M) := sorry

end AlgebraicGeometry
