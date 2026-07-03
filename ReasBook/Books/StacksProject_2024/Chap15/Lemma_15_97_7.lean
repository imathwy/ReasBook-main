import StacksProject_2024.Chap15.LinearMapIdentifiesWithProdSubmodules

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
universe u v y

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
variable {N₁ : Type v} [AddCommGroup N₁] [Module A N₁]
variable {N₂ : Type v} [AddCommGroup N₂] [Module A N₂]

-- Proof sketch: choose a retraction `π` of `s`, form the induced endomorphisms of `M`
-- corresponding to the two projections `N₁ × N₂ → Nᵢ`, and let `J` be the finitely generated
-- ideal cutting out the locus where these endomorphisms become complementary idempotents. After
-- base change to `B`, the condition `J ≤ ker(algebraMap A B)` is equivalent to the base-changed
-- map identifying `B ⊗[A] M` with a product of submodules of the two ambient summands.
/-- Lemma 15.97.7: for a split injection of a finite projective `A`-module into `N₁ × N₂`, there
exists a finitely generated ideal `J` whose quotient detects exactly when every base change of the
map identifies `M` with a direct sum of submodules of the two base-changed summands. -/
theorem exists_fgIdeal_iff_baseChangeIdentifiesWithProdSubmodules_of_splitInjection
    [Module.Finite A M] [Module.Projective A M]
    (s : M →ₗ[A] N₁ × N₂)
    (hs : IsSplitMono (ModuleCat.ofHom s)) :
    ∃ J : Ideal A, J.FG ∧
      ∀ (B : Type y) [CommRing B] [Algebra A B],
        J ≤ RingHom.ker (algebraMap A B) ↔
          s.baseChangeIdentifiesWithProdSubmodules B := sorry

end
