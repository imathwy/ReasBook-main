import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_104_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_31_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
variable {S : Type w} [CommRing S] [Algebra k S] [IsNoetherianRing S]

local notation "S_K" => K ⊗[k] S

/- Domain-style sampling:
- primary domain: Cohen-Macaulay local rings under tensor base change along a finitely generated
  field extension;
- sampled owner declarations of the same kind:
  `Algebra.EssFiniteType` from Definition `9.6.6`,
  `isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.31.8`,
  `cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.167.1`,
  `cohenMacaulayRing_iff_source_and_closedFiber` from Lemma `10.163.3`;
- best owner abstraction: the field-extension hypothesis belongs on the canonical owner
  `Algebra.EssFiniteType k K`, while the Cohen-Macaulay condition itself belongs directly on the
  local self-module owner `Module.CohenMacaulay`;
- primitive data: only the upstairs prime `qK` of `K ⊗[k] S`;
- derived API: Noetherianity of `S_K`, the local flatness of the induced map on localizations, and
  the Cohen-Macaulayness of the closed fiber over the canonical contraction `qK.under S`.

Source/core/bridge triage:
* `source-facing`: the Stacks lemma comparing the local rings at an upstairs prime and its
  downstairs contraction;
* `core/canonical`: `Algebra.EssFiniteType k K` and `Module.CohenMacaulay` on the localized
  self-modules;
* `bridge/view`: the induced localization map
  `Localization.AtPrime (qK.under S) → Localization.AtPrime qK` and the closed-fiber comparison
  with `K ⊗[k] (qK.under S).ResidueField`.

This file therefore should not keep a parallel finite-type field-extension hypothesis or a local
duplicate of the tensor-product Noetherianity theorem. Once `qK` is fixed, the downstairs prime is
canonically `qK.under S`, so separate public data `q` and `qK.LiesOver q` would be redundant.
-/

-- The tensor product ring is Noetherian by the chapter owner theorem for finitely generated field
-- extensions, already formulated on `Algebra.EssFiniteType`.
local instance tensorProduct_isNoetherianRing : IsNoetherianRing S_K :=
  isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension

-- Proof sketch: the local map `S_(q_K ∩ S) → (K ⊗[k] S)_{q_K}` is flat because it is obtained from the
-- flat base-change map `S → K ⊗[k] S` by localization. Its closed fiber is a localization of
-- `κ(q_K ∩ S) ⊗[k] K`, which is Cohen-Macaulay by Lemma `10.167.1`. Apply Lemma `10.163.3` to
-- this flat local map and the Cohen-Macaulay closed fiber.
/-- Lemma 10.167.2: for a field `k`, a Noetherian `k`-algebra `S`, a finitely generated field
extension `K / k`, recorded canonically by `Algebra.EssFiniteType k K`, and a prime `q_K` of
`K ⊗[k] S`, the local ring `S_(q_K ∩ S)` is Cohen-Macaulay if and only if
`(K ⊗[k] S)_{q_K}` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_localizationAtPrime_under_iff_tensorProduct_localizationAtPrime
    (qK : Ideal S_K) [qK.IsPrime] :
    Module.CohenMacaulay (Localization.AtPrime (qK.under S)) (Localization.AtPrime (qK.under S)) ↔
      Module.CohenMacaulay (Localization.AtPrime qK) (Localization.AtPrime qK) := sorry

end
