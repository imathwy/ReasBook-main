import Mathlib
import stacks_proof.stacks_project.Chap10.Proposition_10_158_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime] [CharP k p]

/- Domain triage:
- primary domain: characteristic-`p` field extensions and the Jacobi-Zariski transitivity map on
  Kähler differentials;
- sampled owner declarations:
  - `Algebra.IsSeparableOver`,
  - `KaehlerDifferential.mapBaseChange`,
  - `Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth`;
- best owner abstraction: the chapter owner theorem
  `Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth`,
  whose fourth clause is exactly the injectivity of
  `KaehlerDifferential.mapBaseChange (ZMod p) k K`;
- primitive data: the field extension `K / k` in characteristic `p`;
- derived API: the individual pairwise equivalences extracted from the TFAE owner theorem.

Layer triage:
- `source-facing`: this lemma isolates the textbook equivalence between Stacks-project
  separability and injectivity of the canonical differential map;
- `core/canonical`: the owner TFAE theorem above;
- `bridge/view`: the present lemma is the `0 ↔ 3` projection of that owner theorem.

So this file should stay a thin projection theorem rather than reintroducing a parallel proof
package around the same six-way equivalence.
-/
/-- Lemma 10.158.4: for a field extension `K / k` of characteristic `p > 0`, the Stacks Project
notion that `K / k` is separable is equivalent to injectivity of the canonical map
`K ⊗[k] Ω[k⁄ZMod p] → Ω[K⁄ZMod p]`. -/
@[stacks 031X]
theorem isSeparableOver_iff_kaehlerDifferential_mapBaseChange_injective :
    by
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
      letI : Algebra (ZMod p) K := ZMod.algebra K p
      letI : IsScalarTower (ZMod p) k K := by infer_instance
      exact
        Algebra.IsSeparableOver k K ↔
          Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K) := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : CharP K p := CharP.of_ringHom_of_ne_zero (algebraMap k K) p (Fact.out : p.Prime).ne_zero
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : IsScalarTower (ZMod p) k K := by infer_instance
  let l : List Prop := [
    Algebra.IsSeparableOver k K,
    IsReduced (K ⊗[k] onePthRootExtension k p),
    Algebra.IsGeometricallyReduced k K,
    Function.Injective (KaehlerDifferential.mapBaseChange (ZMod p) k K),
    Subsingleton (Algebra.H1Cotangent k K),
    Algebra.FormallySmooth k K
  ]
  have htfae : List.TFAE l := by
    simpa [l] using
      Algebra.char_p_field_extension_tfae_separable_reduced_one_pth_root_geometrically_reduced_kaehler_injective_h1_cotangent_formally_smooth
  simpa [l] using htfae.out 0 3 (by simp [l]) (by simp [l])

end
