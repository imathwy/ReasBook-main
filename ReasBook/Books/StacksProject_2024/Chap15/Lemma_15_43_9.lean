import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_43_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]

/- The comparison map on maximal-ideal completions is the owner theorem
`maximalIdealCompletionMap_comp` from Lemma `10.97.7`, specialized to `algebraMap A B`. -/
recall maximalIdealCompletionMap_comp

-- Proof sketch: apply Lemma `10.97.7` to identify `B^∧` with the completion of `B` along
-- `maximalIdeal A`, use Lemma `15.27.5` to deduce flatness of `B^∧` over `A^∧`, then invoke
-- `Module.free_of_flat_of_isLocalRing` from Lemma `10.78.5`. The residue-field bijectivity
-- hypothesis shows that the closed fiber has dimension one over the residue field, so the free
-- module has rank `1`, forcing the canonical completion map to be bijective.
/-- Lemma 15.43.9: if `A → B` is a flat local homomorphism of Noetherian local rings, the
maximal ideal of `B` is the extension of the maximal ideal of `A`, and the induced map on residue
fields is bijective, then the induced map `A^∧ → B^∧` on maximal-ideal completions is
bijective. -/
theorem maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Bijective (maximalIdealCompletionMap (algebraMap A B)) := sorry

end
