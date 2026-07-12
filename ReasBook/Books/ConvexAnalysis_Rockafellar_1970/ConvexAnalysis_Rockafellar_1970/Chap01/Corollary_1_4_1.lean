import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_1_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AffineSubspace

/-
Corollary 1.4.1 is organized around the affine-subspace owner abstraction
`AffineSubspace.is_hyperplane`. The coordinate-free chapter owner theorem
`AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot` identifies a proper affine subspace with
the fiber of a surjective linear map into finite coordinate space. The scalar projections of that
map are then converted to the chapter-owned hyperplane constructor `linearHyperplane`, and the
hyperplane witness is discharged via the canonical owner theorem
`linearHyperplane_is_hyperplane` from Theorem 1.3 rather than a local duplicate proof.
The public corollary is formulated at the intrinsic quotient finite/free layer
`Module.Free k (V ⧸ s.direction)` + `Module.Finite k (V ⧸ s.direction)` over a division ring.
-/
recall exists_surjective_eq_pi_fiber_of_ne_bot

/-
Source/core/bridge triage:
- `source-facing`: Corollary 1.4.1 says every affine subspace is a finite intersection of
  hyperplanes.
- `core/canonical`: the owner abstraction is `AffineSubspace k V` with the predicate
  `AffineSubspace.is_hyperplane`.
- `bridge/view`: the `Finset`/`sInf` formulation is an operational finite-set bridge derived from
  the owner-level finite `iInf` statement. The finite family of scalar equations is obtained from
  the owner-side coordinate bridge `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot`.
- Primitive data vs derived API: the primitive data are just the affine subspace `s`; the quotient
  presentation from `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot` and the coordinate
  projections `LinearMap.proj` are internal proof data, while the family of `linearHyperplane`s
  and the finite-intersection statements are the public derived API.
- Domain-style sampling: the owner-side declarations used here are
  `AffineSubspace.exists_surjective_eq_pi_fiber_of_ne_bot`, `LinearMap.proj`,
  `linearHyperplane`, `linearHyperplane_is_hyperplane`, and
  `Projective.exists_dual_ne_zero`.
- Layer target: `source-facing`, with the public statements kept directly in the intrinsic
  `AffineSubspace`/hyperplane language.
-/

section HyperplaneIntersections

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

private theorem exists_setFinite_eq_sInf_of_eq_iInf {ι : Type*} [Finite ι]
    {s : AffineSubspace k V}
    (H : ι → AffineSubspace k V)
    (hH : ∀ i, (H i).is_hyperplane)
    (hs : s = ⨅ i, H i) :
    ∃ T : Set (AffineSubspace k V), T.Finite ∧
      (∀ K ∈ T, K.is_hyperplane) ∧ s = sInf T := by
  refine ⟨Set.range H, Set.finite_range H, ?_, ?_⟩
  · intro K hK
    rcases hK with ⟨i, rfl⟩
    exact hH i
  · simpa [sInf_range] using hs

namespace AffineSubspace

/-- Corollary 1.4.1, primitive owner form: every proper affine subspace whose direction quotient
is finite and free over a division ring is the intersection of finitely many affine hyperplanes,
expressed as an `iInf` of a finite indexed family at the owner layer. -/
theorem exists_eq_iInf_hyperplanes_of_ne_bot (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)]
    (hs : s ≠ ⊥) :
    ∃ ι : Type, ∃ _ : Finite ι, ∃ H : ι → AffineSubspace k V,
      (∀ i, (H i).is_hyperplane) ∧ s = ⨅ i, H i := by
  classical
  rcases s.exists_surjective_eq_pi_fiber_of_ne_bot hs with ⟨ι, hι, A, b, hA_surj, hsA⟩
  let _ : Fintype ι := hι
  let H : ι → AffineSubspace k V := fun i ↦ linearHyperplane ((LinearMap.proj i).comp A) (b i)
  have hH : ∀ i, (H i).is_hyperplane := by
    intro i
    have hproj : (LinearMap.proj i).comp A ≠ 0 := by
      intro hzero
      obtain ⟨x, hx⟩ := hA_surj (Pi.single i 1)
      have hx1 : ((LinearMap.proj i).comp A) x = 1 := by
        simp [hx]
      have hx0 : ((LinearMap.proj i).comp A) x = 0 := by
        simp [hzero]
      exact one_ne_zero (hx1.symm.trans hx0)
    simpa [H] using linearHyperplane_is_hyperplane ((LinearMap.proj i).comp A) (b i) hproj
  have hs' : (affineSpan k ({b} : Set (ι → k))).comap A.toAffineMap = ⨅ i, H i := by
    refine le_antisymm ?_ ?_
    · refine le_iInf ?_
      intro i x hx
      have hxA : A x = b := by
        rw [mem_comap, mem_affineSpan_singleton] at hx
        simpa [LinearMap.coe_toAffineMap] using hx
      have hEq : ((LinearMap.proj i).comp A) x = b i := by
        simpa [LinearMap.proj_apply] using congrArg (fun y : ι → k ↦ y i) hxA
      simpa [H] using hEq
    · intro x hx
      have hxA : A x = b := by
        ext i
        have hmem : x ∈ H i := (mem_iInf_iff H x).1 hx i
        have hEq : ((LinearMap.proj i).comp A) x = b i := by
          simpa [H] using hmem
        simpa [LinearMap.proj_apply] using hEq
      rw [mem_comap, mem_affineSpan_singleton]
      simpa [LinearMap.coe_toAffineMap] using hxA
  exact ⟨ι, Finite.of_fintype ι, H, hH, hsA.trans hs'⟩

/-- Corollary 1.4.1, owner-level finite-family form: every affine subspace of a nontrivial module
whose direction quotient is finite and free over a division ring is the intersection of finitely
many affine hyperplanes, expressed canonically as an `iInf` of a finite indexed family. -/
theorem exists_eq_iInf_hyperplanes [Nontrivial V] (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)] :
    ∃ ι : Type, ∃ _ : Finite ι, ∃ H : ι → AffineSubspace k V,
      (∀ i, (H i).is_hyperplane) ∧ s = ⨅ i, H i := by
  rcases s.eq_bot_or_nonempty with rfl | ⟨p, hp⟩
  · obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
      simpa using exists_ne (0 : V)
    obtain ⟨f, hfv⟩ : ∃ f : Module.Dual k V, f v ≠ 0 :=
      Module.Projective.exists_dual_ne_zero k hv
    have hf : (f : V →ₗ[k] k) ≠ 0 := by
      intro hf0
      have : f v = 0 := by simp [hf0]
      exact hfv this
    let γ : k := f v
    let H : Bool → AffineSubspace k V
      | false => linearHyperplane f 0
      | true => linearHyperplane f γ
    have hH : ∀ i, (H i).is_hyperplane := by
      intro i
      cases i with
      | false => simpa [H] using linearHyperplane_is_hyperplane f (0 : k) hf
      | true => simpa [H, γ] using linearHyperplane_is_hyperplane f γ hf
    have hs : (⊥ : AffineSubspace k V) = ⨅ i, H i := by
      refine le_antisymm bot_le ?_
      intro x hx
      exfalso
      have h0 : f x = 0 := by
        simpa [H] using (mem_iInf_iff H x).1 hx false
      have hγ : f x = γ := by
        simpa [H, γ] using (mem_iInf_iff H x).1 hx true
      have hfv0 : f v = 0 := by
        have hγ' : f x = f v := by simpa [γ] using hγ
        exact hγ'.symm.trans h0
      exact hfv hfv0
    exact ⟨Bool, inferInstance, H, hH, hs⟩
  · have hsbot : s ≠ (⊥ : AffineSubspace k V) := by
      intro hbot
      simp [hbot] at hp
    exact exists_eq_iInf_hyperplanes_of_ne_bot s hsbot

/-- Corollary 1.4.1, intrinsic finite-set owner form from primitive data: every proper affine
subspace whose direction quotient is finite and free is an `sInf` of a finite set of affine
hyperplanes. -/
theorem exists_eq_sInf_hyperplanes_of_ne_bot (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)]
    (hs : s ≠ ⊥) :
    ∃ T : Set (AffineSubspace k V), T.Finite ∧
      (∀ H ∈ T, H.is_hyperplane) ∧ s = sInf T := by
  rcases exists_eq_iInf_hyperplanes_of_ne_bot s hs with ⟨ι, hι, H, hH, hs⟩
  let _ : Finite ι := hι
  exact exists_setFinite_eq_sInf_of_eq_iInf H hH hs

/-- Corollary 1.4.1, intrinsic finite-set owner form: every affine subspace of a nontrivial module
whose direction quotient is finite and free is an `sInf` of a finite set of affine hyperplanes.
-/
theorem exists_eq_sInf_hyperplanes [Nontrivial V] (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)] :
    ∃ T : Set (AffineSubspace k V), T.Finite ∧
      (∀ H ∈ T, H.is_hyperplane) ∧ s = sInf T := by
  rcases exists_eq_iInf_hyperplanes s with ⟨ι, hι, H, hH, hs⟩
  let _ : Finite ι := hι
  exact exists_setFinite_eq_sInf_of_eq_iInf H hH hs

/-- Corollary 1.4.1, finite-operational bridge form from primitive data: every proper affine
subspace whose direction quotient is finite and free is a finite `sInf` of affine hyperplanes,
indexed by a `Finset`. -/
theorem exists_eq_sInf_finset_hyperplanes_of_ne_bot (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)]
    (hs : s ≠ ⊥) :
    ∃ t : Finset (AffineSubspace k V),
      (∀ H ∈ t, H.is_hyperplane) ∧
        s = sInf (t : Set (AffineSubspace k V)) := by
  rcases exists_eq_sInf_hyperplanes_of_ne_bot s hs with ⟨T, hTfin, hT, hsT⟩
  refine ⟨hTfin.toFinset, ?_, ?_⟩
  · intro H hHmem
    exact hT H (hTfin.mem_toFinset.mp hHmem)
  · simpa [hTfin.coe_toFinset] using hsT

/-- Corollary 1.4.1: every affine subspace of a nontrivial module over a division ring whose
direction quotient is finite and free is the intersection of finitely many affine hyperplanes. -/
theorem exists_eq_sInf_finset_hyperplanes [Nontrivial V] (s : AffineSubspace k V)
    [Module.Free k (V ⧸ s.direction)] [Module.Finite k (V ⧸ s.direction)] :
    ∃ t : Finset (AffineSubspace k V),
      (∀ H ∈ t, H.is_hyperplane) ∧
        s = sInf (t : Set (AffineSubspace k V)) := by
  rcases exists_eq_sInf_hyperplanes s with ⟨T, hTfin, hT, hsT⟩
  refine ⟨hTfin.toFinset, ?_, ?_⟩
  · intro H hHmem
    exact hT H (hTfin.mem_toFinset.mp hHmem)
  · simpa [hTfin.coe_toFinset] using hsT

end AffineSubspace

end HyperplaneIntersections
