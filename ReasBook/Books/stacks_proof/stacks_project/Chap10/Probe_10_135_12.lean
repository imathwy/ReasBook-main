import Mathlib

open IsLocalRing

section

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable (K : Ideal S)

example (a : S) (y : K) :
    let NK : Submodule S K := maximalIdeal S • (⊤ : Submodule S K)
    Submodule.mkQ NK (a • y) =
      (Ideal.Quotient.mk (maximalIdeal S) a) • (Submodule.mkQ NK y) := by
  intro NK
  change Submodule.Quotient.mk (p := (maximalIdeal S • (⊤ : Submodule S K))) (a • y) =
    (Ideal.Quotient.mk (maximalIdeal S) a) •
      Submodule.Quotient.mk (p := (maximalIdeal S • (⊤ : Submodule S K))) y
  rw [Module.Quotient.mk_smul_mk]

example {n : ℕ} (fK : Fin n → K)
    (hspanK_S : Submodule.span S (Set.range fK) = ⊤) :
    let NK : Submodule S K := maximalIdeal S • (⊤ : Submodule S K)
    let qK : K →ₗ[S] K ⧸ NK := Submodule.mkQ NK
    let fVK : Fin n → K ⧸ NK := fun i ↦ qK (fK i)
    Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK) = ⊤ := by
  intro NK qK fVK
  apply top_unique
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective NK z
  change qK x ∈ Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK)
  have hxspan : x ∈ Submodule.span S (Set.range fK) := by
    rw [hspanK_S]
    exact trivial
  refine Submodule.span_induction (s := Set.range fK)
    (p := fun y _ ↦ qK y ∈ Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK))
    ?mem ?zero ?add ?smul hxspan
  · rintro y ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · simpa [qK] using (Submodule.zero_mem
      (Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK)))
  · intro y z hyspan hzspan hy hz
    simpa [qK, map_add] using Submodule.add_mem
      (Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK)) hy hz
  · intro a y hyspan hy
    have hsmul :
        (Ideal.Quotient.mk (maximalIdeal S) a) • qK y ∈
          Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK) :=
      Submodule.smul_mem _ _ hy
    change qK (a • y) ∈ Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK)
    change Submodule.Quotient.mk (p := (maximalIdeal S • (⊤ : Submodule S K))) (a • y) ∈
      Submodule.span (S ⧸ maximalIdeal S) (Set.range fVK)
    rwa [← Module.Quotient.mk_smul_mk]

end
