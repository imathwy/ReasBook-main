import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open QuotientGroup Subgroup

variable {G : Type u} [Group G]

/-- A finite increasing series of subgroups from `⊥` to `⊤` whose terms are normal in `G` and
whose successive quotients are cyclic. -/
def IsSupersolvableSeries (f : ℕ → Subgroup G) (n : ℕ) : Prop :=
  Monotone f ∧
    ∃ hnormal : ∀ i < n, (f i).Normal,
      (∀ i, ∀ hi : i < n,
        letI : ((f i).subgroupOf (f (i + 1))).Normal := (hnormal i hi).subgroupOf (f (i + 1))
        IsCyclic (f (i + 1) ⧸ (f i).subgroupOf (f (i + 1)))) ∧
      f 0 = ⊥ ∧
      f n = ⊤

/-- Definition 8-8.3-2: a group is supersolvable if it admits a finite increasing series of
subgroups from `⊥` to `⊤`, each normal in `G` and with cyclic successive quotients. -/
@[mk_iff isSupersolvable_def]
class IsSupersolvable (G : Type u) [Group G] : Prop where
  /-- A witnessing finite normal series with cyclic successive quotients. -/
  supersolvable : ∃ n : ℕ, ∃ f : ℕ → Subgroup G, IsSupersolvableSeries f n

/-- A cyclic group is supersolvable. -/
instance isSupersolvable_of_isCyclic [IsCyclic G] : IsSupersolvable G := by
  refine ⟨?_⟩
  refine ⟨1, (fun n ↦ match n with | 0 => ⊥ | _ + 1 => ⊤), ?_⟩
  refine ⟨?_, ⟨?_, ⟨?_, by simp, by simp⟩⟩⟩
  · refine monotone_nat_of_le_succ ?_
    intro i
    cases i <;> simp
  · intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    infer_instance
  · intro i hi
    have : i = 0 := Nat.lt_one_iff.mp hi
    subst this
    simpa using
      isCyclic_of_surjective
        (mk' ((⊥ : Subgroup G).subgroupOf ⊤))
        (mk'_surjective _)

attribute [instance 100] isSupersolvable_of_isCyclic

/-- A supersolvable group is solvable. -/
instance IsSupersolvable.to_isSolvable [IsSupersolvable G] : IsSolvable G := by
  let hsup : IsSupersolvable G := inferInstance
  rcases hsup.supersolvable with ⟨n, f, hmono, hnormal, hcyclic, h0, hn⟩
  have hs : ∀ i ≤ n, IsSolvable (f i) := by
    intro i hi
    induction i with
    | zero =>
        rw [h0]
        infer_instance
    | succ i ih =>
        have hi_lt : i < n := Nat.lt_of_succ_le hi
        let hle : f i ≤ f (i + 1) := hmono (Nat.le_succ i)
        letI : IsSolvable (f i) := ih (Nat.le_of_lt hi_lt)
        letI : (f i).Normal := hnormal i hi_lt
        letI : ((f i).subgroupOf (f (i + 1))).Normal := (hnormal i hi_lt).subgroupOf (f (i + 1))
        letI : IsCyclic (f (i + 1) ⧸ (f i).subgroupOf (f (i + 1))) := hcyclic i hi_lt
        let _ : CommGroup (f (i + 1) ⧸ (f i).subgroupOf (f (i + 1))) := IsCyclic.commGroup
        exact
          solvable_of_ker_le_range
            (inclusion hle)
            (mk' ((f i).subgroupOf (f (i + 1))))
            (by simp [Subgroup.inclusion_range])
  letI : IsSolvable (f n) := hs n le_rfl
  let e : f n ≃* G := (MulEquiv.subgroupCongr hn).trans topEquiv
  let φ : f n →* G := e.toMonoidHom
  let hφ : Function.Surjective φ := e.surjective
  exact solvable_of_surjective hφ

attribute [instance 100] IsSupersolvable.to_isSolvable

end
