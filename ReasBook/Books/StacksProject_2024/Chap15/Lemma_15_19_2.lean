import Mathlib
import StacksProject_2024.Chap15.«15_18_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped TensorProduct

universe u v w x y

section

variable {R : Type u} {S : Type v} {M : Type w} {R' : Type x} {R'' : Type y}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing R'']
variable [Algebra R S] [Algebra R R'] [Algebra R R''] [Algebra R' R'']
variable [IsScalarTower R R' R'']
variable [AddCommGroup M] [Module S M]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "S1" => S ⊗[R] R'
local notation "S2" => S ⊗[R] R''
local notation "M1" => S1 ⊗[S] M
local notation "M2" => S2 ⊗[S] M

/-
Domain triage:
- primary domain: flatness loci under tensor-product base change in commutative algebra;
- sampled owner declarations: `Module.flatOverBaseLocus`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_iff`,
  `Ideal.zeroLocus_subset_flatOverBaseLocus_of_baseChange_of_map_le`,
  `Algebra.TensorProduct.map`;
- best owner abstraction: the flatness-locus owner `Module.flatOverBaseLocus`;
- bridge/view layer needed here: the explicit tensor-base-change map
  `Algebra.TensorProduct.map (AlgHom.id S S) (algebraMap R' R'')`, because the chapter keeps the
  target ring as `S ⊗[R] R''` rather than the associatively equivalent iterated tensor product from
  `15.18.1`;
- layer choice here: `source-facing`; the lemma keeps the Stacks sum ideal `I'S + J` visible, but
  states it directly as inclusion of the closed subset into the flatness locus rather than
  repeating its primewise expansion.
-/

/-- Tensor-base-change stability of a flatness-locus inclusion for the chapter’s preferred target
ring `S ⊗[R] R''`, expressed using the canonical map induced by `R' → R''` on the right tensor
factor. -/
theorem zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_of_map_le
    {K1 : Ideal S1} {K2 : Ideal S2}
    (hflat : zeroLocus (K1 : Set S1) ⊆ Module.flatOverBaseLocus R' S1 M1)
    (hK2 :
      Ideal.map
          (Algebra.TensorProduct.map (AlgHom.id S S)
            (IsScalarTower.toAlgHom R R' R'')).toRingHom K1 ≤
        K2) :
    zeroLocus (K2 : Set S2) ⊆ Module.flatOverBaseLocus R'' S2 M2 := sorry

-- Proof sketch: apply the tensor-base-change bridge theorem to the source-facing sum ideal
-- `I'S1 + JS1`. The ideal-containment input is checked entrywise on the two summands, using `hI''`
-- on the `I'`-part and functoriality of `Ideal.map` on the `J`-part.
/-- Lemma 15.19.2: for the base change of Situation `15.19.1`, if condition `(15.19.1.1)` holds
over `R'` for an ideal `I'`, then it also holds after any further `R`-algebra base change
`R' → R''` for every ideal `I''` containing `I'R''`. -/
theorem localizedModule_flat_over_base_at_primes_of_zeroLocus_add_of_baseChange
    (J : Ideal S) (I' : Ideal R') (I'' : Ideal R'')
    (hI'' : Ideal.map (algebraMap R' R'') I' ≤ I'')
    (hflat : zeroLocus
      ((Ideal.map (algebraMap R' S1) I' + Ideal.map (algebraMap S S1) J : Ideal S1) : Set S1) ⊆
        Module.flatOverBaseLocus R' S1 M1) :
    zeroLocus
        ((Ideal.map (algebraMap R'' S2) I'' + Ideal.map (algebraMap S S2) J : Ideal S2) :
          Set S2) ⊆
      Module.flatOverBaseLocus R'' S2 M2 := by
  let K1 : Ideal S1 := Ideal.map (algebraMap R' S1) I' + Ideal.map (algebraMap S S1) J
  let K2 : Ideal S2 := Ideal.map (algebraMap R'' S2) I'' + Ideal.map (algebraMap S S2) J
  have hflat' : zeroLocus (K1 : Set S1) ⊆ Module.flatOverBaseLocus R' S1 M1 := by
    simpa [K1] using hflat
  have hmap :
      Ideal.map
          (Algebra.TensorProduct.map (AlgHom.id S S)
            (IsScalarTower.toAlgHom R R' R'')).toRingHom K1 ≤
        K2 := by
    let φ : S1 →ₐ[S] S2 := Algebra.TensorProduct.map (AlgHom.id S S)
      (IsScalarTower.toAlgHom R R' R'')
    change Ideal.map φ.toRingHom K1 ≤ K2
    dsimp [K1, K2, φ]
    rw [Ideal.map_sup]
    refine sup_le ?_ ?_
    · have hmap_eq :
          Ideal.map
              ((Algebra.TensorProduct.map (AlgHom.id S S)
                (IsScalarTower.toAlgHom R R' R'')) : S1 →+* S2)
              (Ideal.map (algebraMap R' S1) I') =
            Ideal.map (algebraMap R'' S2) (Ideal.map (algebraMap R' R'') I') := by
        rw [Ideal.map_map, Ideal.map_map]
        rfl
      rw [hmap_eq]
      exact le_trans (Ideal.map_mono hI'') le_sup_left
    · have hmap_eq :
          Ideal.map
              ((Algebra.TensorProduct.map (AlgHom.id S S)
                (IsScalarTower.toAlgHom R R' R'')) : S1 →+* S2)
              (Ideal.map (algebraMap S S1) J) =
            Ideal.map (algebraMap S S2) J := by
        rw [Ideal.map_map]
        congr 1
        ext x
        simp
      rw [hmap_eq]
      exact le_sup_right
  have hresult : zeroLocus (K2 : Set S2) ⊆ Module.flatOverBaseLocus R'' S2 M2 :=
    zeroLocus_subset_flatOverBaseLocus_of_tensorBaseChange_of_map_le hflat' hmap
  simpa [K2] using hresult

end
