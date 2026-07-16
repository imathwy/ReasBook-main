import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_104_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {L : Type w} [Field L] [Algebra k L]

/- Domain triage:
* primary domain: tensor products of finitely generated field extensions and Cohen-Macaulayness;
* sampled owner API:
  `Algebra.EssFiniteType` from Definition `9.6.6`,
  `isNoetherianRing_tensorProduct_of_finitelyGeneratedFieldExtension` from Lemma `10.31.8`,
  `cohenMacaulayRing_mvPolynomial` from Lemma `10.104.7`,
  `cohenMacaulayRing_of_finiteFlat_localHom` from Lemma `10.112.9`;
* source-facing: the symmetric textbook statement for `K ⊗[k] L` when one extension is finitely
  generated;
* core/canonical: `Algebra.EssFiniteType` for finitely generated field extensions and
  `CohenMacaulayRing` for the target ring property;
* bridge/view: the one-sided base-change form with `[Algebra.EssFiniteType k K]`, together with
  `TensorProduct.comm` for the symmetric reformulation.

The only primitive extra input is that one field extension is finitely generated over `k`. By the
chapter owner choice in Definition `9.6.6`, the reusable bridge theorem should expose that input
directly as `[Algebra.EssFiniteType k K]`; the symmetric "one side or the other" statement is then
derived API obtained by factor swapping.
-/
-- Proof sketch for the one-sided base-change form: `K ⊗[k] L` is Noetherian by Lemma `10.31.8`.
-- Choose a purely transcendental subextension `k(t₁, …, t_r) ⊆ K` over which `K` is finite; the
-- induced map from `k(t₁, …, t_r) ⊗[k] L` to `K ⊗[k] L` is finite free, so Cohen-Macaulayness
-- ascends from the source by Lemma `10.112.9`. Finally, `k(t₁, …, t_r) ⊗[k] L` is a localization
-- of a polynomial ring over `L`, hence Cohen-Macaulay by Lemma `10.104.7`.
/-- Lemma 10.167.1, canonical base-change form: if `k` is a field, `L / k` is a field extension,
and `K / k` is a finitely generated field extension recorded by `Algebra.EssFiniteType`, then
`K ⊗[k] L` is a Noetherian Cohen-Macaulay ring. This is the owner-aligned form used when the
finitely generated side is fixed in advance. -/
theorem cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension
    [Algebra.EssFiniteType k K] :
    CohenMacaulayRing (K ⊗[k] L) := sorry

-- Proof sketch for the symmetric source statement: apply the one-sided theorem when the finitely
-- generated side is `K`; if the finitely generated side is `L`, swap the tensor factors by
-- `TensorProduct.comm`.
/-- Lemma 10.167.1, source-facing symmetric form: if `k` is a field and `K / k`, `L / k` are
field extensions such that one of them is finitely generated over `k`, recorded canonically by
`Algebra.EssFiniteType`, then `K ⊗[k] L` is a Noetherian Cohen-Macaulay ring. -/
theorem cohenMacaulayRing_tensorProduct_of_fieldExtensions_of_finitelyGeneratedFieldExtension
    (hfin : Algebra.EssFiniteType k K ∨ Algebra.EssFiniteType k L) :
    CohenMacaulayRing (K ⊗[k] L) := by
  rcases hfin with hK | hL
  · letI : Algebra.EssFiniteType k K := hK
    simpa using
      (cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension :
        CohenMacaulayRing (K ⊗[k] L))
  · letI : Algebra.EssFiniteType k L := hL
    sorry

end
