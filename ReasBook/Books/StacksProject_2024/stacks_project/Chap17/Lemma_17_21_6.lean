import Mathlib
import StacksProject_2024.stacks_project.Chap17.Lemma_17_14_2
import StacksProject_2024.stacks_project.Chap17.AlgebraSheafConstructions

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/- Domain-style sampling for Lemma 17.21.6:
- primary domain: tensor, exterior, and symmetric algebra sheaves of `\mathcal O_X`-modules, and
  stability of quasi-coherence and local freeness under those algebra constructions;
- inspected owner declarations:
  `T(ℱ)`, `Λ(ℱ)`, `Symm(ℱ)` from `AlgebraSheafConstructions`,
  `tensorPowerSheaf_isQuasicoherent`,
  `exteriorPowerSheaf_isQuasicoherent`,
  `symmetricPowerSheaf_isQuasicoherent`,
  `tensorPowerSheaf_isLocallyFree`,
  `exteriorPowerSheaf_isLocallyFree`,
  `symmetricPowerSheaf_isLocallyFree` from `Lemma_17_21_5`,
  `ringedSpaceModule_isQuasicoherent_of_isLocallyFree`;
- best owner abstraction: the public owners are the already-defined algebra sheaves `T(ℱ)`, `Λ(ℱ)`,
  and `Symm(ℱ)` in `X.Modules`, while `IsQuasicoherent` and `IsLocallyFree` are the derived owner
  predicates that should be attached directly to those objects;
- primitive data: a module sheaf `ℱ : ModX`;
- derived API: the six closure instances below.

Source/core/bridge triage:
- `source-facing`: the six Stacks assertions that tensor, exterior, and symmetric algebra sheaves
  of a quasi-coherent or locally free module sheaf retain the same property;
- `core/canonical`: the owner objects `T(ℱ)`, `Λ(ℱ)`, `Symm(ℱ)` together with the predicates
  `( _ ).IsQuasicoherent` and `( _ ).IsLocallyFree` on `X.Modules`;
- `bridge/view`: proofs may use the power-sheaf closure results from `Lemma_17_21_5`, but the
  public surface should be owner-level instances on the algebra sheaves themselves, not parallel
  non-instance wrapper theorems.
-/ 

section Quasicoherent

variable (ℱ : ModX) [ℱ.IsQuasicoherent]

-- Proof sketch: quasi-coherence is checked locally on affine opens. On such a neighborhood,
-- `ℱ` comes from a module of sections, and the tensor algebra sheaf is the associated sheaf of
-- the ordinary tensor algebra of that module, so it remains quasi-coherent.
/-- Lemma 17.21.6 (1): if `\mathcal F` is quasi-coherent, then its tensor algebra
`\mathrm{T}(\mathcal F)` is quasi-coherent. -/
instance moduleTensorAlgebra_isQuasicoherent :
    (T(ℱ)).IsQuasicoherent := by
  -- The owner-level tensor algebra sheaf already carries the required canonical instance.
  infer_instance

-- Proof sketch: after restricting to an affine open where `ℱ` is represented by a module `M`,
-- the sheaf `Λ(ℱ)` is the associated sheaf of the exterior algebra `Λ(M)`, hence is
-- quasi-coherent on that neighborhood.
/-- Lemma 17.21.6 (2): if `\mathcal F` is quasi-coherent, then its exterior algebra
`\bigwedge(\mathcal F)` is quasi-coherent. -/
instance moduleExteriorAlgebra_isQuasicoherent :
    (Λ(ℱ)).IsQuasicoherent := by
  -- The exterior algebra inherits quasi-coherence through the existing owner API.
  infer_instance

-- Proof sketch: on an affine neighborhood where `ℱ` comes from a module of sections, `Symm(ℱ)`
-- is the sheaf associated to the ordinary symmetric algebra of that module, which is again a
-- quasi-coherent module sheaf.
/-- Lemma 17.21.6 (3): if `\mathcal F` is quasi-coherent, then its symmetric algebra
`\operatorname{Sym}(\mathcal F)` is quasi-coherent. -/
instance moduleSymmetricAlgebra_isQuasicoherent :
    (Symm(ℱ)).IsQuasicoherent := by
  -- The symmetric algebra case is also packaged as a canonical instance.
  infer_instance

end Quasicoherent

section LocallyFree

variable (ℱ : ModX) [ℱ.IsLocallyFree]

-- Proof sketch: once `ℱ` is free on an open neighbourhood, the proof of Lemma `17.21.5` shows
-- that the same neighbourhood makes every tensor power `T^n(ℱ)` free, so their direct sum
-- realizes the tensor algebra as locally free.
/-- Lemma 17.21.6 (4): if `\mathcal F` is locally free, then its tensor algebra
`\mathrm{T}(\mathcal F)` is locally free. -/
instance moduleTensorAlgebra_isLocallyFree :
    (T(ℱ)).IsLocallyFree := by
  -- Local freeness of the tensor algebra is available directly from instance search.
  infer_instance

-- Proof sketch: on any neighbourhood where `ℱ` is free, all exterior powers `\bigwedge^n(ℱ)` are
-- free by the argument of Lemma `17.21.5`; summing these compatible local trivializations gives a
-- local trivialization of the exterior algebra itself.
/-- Lemma 17.21.6 (5): if `\mathcal F` is locally free, then its exterior algebra
`\bigwedge(\mathcal F)` is locally free. -/
instance moduleExteriorAlgebra_isLocallyFree :
    (Λ(ℱ)).IsLocallyFree := by
  -- The owner-level exterior algebra sheaf already knows it is locally free.
  infer_instance

-- Proof sketch: on a neighbourhood where `ℱ` is free, all symmetric powers
-- `\operatorname{Sym}^n(ℱ)` are free by Lemma `17.21.5`, and their direct sum therefore gives a
-- free local model for the symmetric algebra.
/-- Lemma 17.21.6 (6): if `\mathcal F` is locally free, then its symmetric algebra
`\operatorname{Sym}(\mathcal F)` is locally free. -/
instance moduleSymmetricAlgebra_isLocallyFree :
    (Symm(ℱ)).IsLocallyFree := by
  -- The symmetric algebra local-freeness goal is likewise solved by the canonical instance.
  infer_instance

end LocallyFree

end AlgebraicGeometry.RingedSpace
