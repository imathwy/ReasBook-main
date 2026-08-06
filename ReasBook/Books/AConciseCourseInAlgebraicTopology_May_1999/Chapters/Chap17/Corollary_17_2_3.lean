import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_2_2
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

-- Semantic recall via `lean_leansearch`: `CategoryTheory.isZero_Tor_succ_of_projective` is the
-- canonical Tor-vanishing input, while local Chapter 17 precedent packages the comparison map as
-- `(S Y).tensorToHomology` for `S : KunnethHomologyNaturality K X n`.

/-- Over a field, the `Tor(H_i(X), H_j(Y))` term in the nat-indexed Kunneth short exact sequence
vanishes. -/
theorem kunnethTorTerm_isZero_of_field
    (K : Type u) [Field K] (X Y : ChainComplex (ModuleCat K) ℕ) (n : ℕ) :
    IsZero (kunnethTorTerm K X Y n) := by
  change IsZero
    (ModuleCat.of K
      (∀ pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        (ModuleCat.tor K (X.homology pq.1.1) (Y.homology pq.1.2) : ModuleCat K)))
  rw [ModuleCat.isZero_of_iff_subsingleton]
  letI (pq : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) :
      Subsingleton (ModuleCat.tor K (X.homology pq.1.1) (Y.homology pq.1.2)) := by
    letI : Module.Projective K (Y.homology pq.1.2) := inferInstance
    letI : Projective (Y.homology pq.1.2) := inferInstance
    exact ModuleCat.isZero_iff_subsingleton.mp
      (ModuleCat.isZero_tor_of_projective_right K (X.homology pq.1.1) (Y.homology pq.1.2))
  infer_instance

/-- Corollary 17.2.3. In the nat-indexed convention of Theorem 17.2.2, over a field `K` any
chosen degree-`n + 1` Kunneth comparison map
`(S Y).tensorToHomology : kunnethTensorTerm K X Y n ⟶ kunnethHomologyTerm K X Y n`
is an isomorphism. -/
theorem kunnethTensorToHomology_isIso_of_field
    (K : Type u) [Field K] (X : ChainComplex (ModuleCat K) ℕ) (n : ℕ)
    (S : KunnethHomologyNaturality K X n) (Y : ChainComplex (ModuleCat K) ℕ) :
    IsIso ((S Y).tensorToHomology) := by
  let T : ShortComplex (ModuleCat K) := (S Y).toShortComplex
  have hT : T.ShortExact := (S Y).shortExact
  have hzero : IsZero T.X₃ := by
    change IsZero (kunnethTorTerm K X Y n)
    exact kunnethTorTerm_isZero_of_field K X Y n
  change IsIso T.f
  exact (ShortComplex.ShortExact.isIso_f_iff hT).2 hzero

/-- Corollary 17.2.3. For any chosen natural Kunneth sequence over a field, the degree-`n + 1`
Kunneth comparison map yields an isomorphism
`kunnethTensorTerm K X Y n ≅ kunnethHomologyTerm K X Y n`. -/
noncomputable def kunnethIso_of_field
    (K : Type u) [Field K] (X : ChainComplex (ModuleCat K) ℕ) (n : ℕ)
    (S : KunnethHomologyNaturality K X n) (Y : ChainComplex (ModuleCat K) ℕ) :
    kunnethTensorTerm K X Y n ≅ kunnethHomologyTerm K X Y n :=
  let _ := kunnethTensorToHomology_isIso_of_field K X n S Y
  asIso ((S Y).tensorToHomology)
