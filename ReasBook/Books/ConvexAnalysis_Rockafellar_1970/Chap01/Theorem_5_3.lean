import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u}
variable {𝕜 : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.3 starts from a convex set `F ⊆ E × 𝕜` and defines
  `f(x) = inf {μ | (x, μ) ∈ F}`.
  `Convex 𝕜 (epi f)`, i.e. convexity of the scalar epigraph.
- `bridge/view`: the epigraph of the resulting function is the vertical upward closure of `F`, so
  the theorem is the passage from convexity of `F` to convexity of that epigraph.
- Primitive data vs derived API: the set `F` and the infimum formula are primitive; convexity of
  the resulting function is the derived statement.
- Ambient minimization: neither the infimum construction nor its convexity proof needs a concrete
  finite-dimensional model, so the owner construction is stated over an arbitrary base type `E`
  and an abstract ordered scalar type `𝕜`.

Domain-style sampling used here:
- `Convex`;
- `epi`;
- `ConvexOn.convex_epigraph`;
- `convexOn_iff_convex_epigraph`;
-/

namespace Function

section Fiber

/-- The scalar vertical fiber of `F` above `x`. -/
def verticalSection (F : Set (E × 𝕜)) (x : E) : Set 𝕜 :=
  {μ : 𝕜 | (x, μ) ∈ F}

/-- The `WithTopBot`-valued heights of the vertical fiber of `F` above `x`. -/
def verticalHeights (F : Set (E × 𝕜)) (x : E) : Set (WithTopBot 𝕜) :=
  ((↑) : 𝕜 → WithTopBot 𝕜) '' verticalSection F x

end Fiber

section WithTopBotLemmas

variable [Preorder 𝕜]

private theorem withTopBot_coe_lt_coe_iff {a b : 𝕜} :
    ((a : WithTopBot 𝕜) < (b : WithTopBot 𝕜)) ↔ a < b := by
  constructor
  · intro h
    exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp h)
  · intro h
    exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr h)

private theorem withTopBot_coe_le_coe_iff {a b : 𝕜} :
    ((a : WithTopBot 𝕜) ≤ (b : WithTopBot 𝕜)) ↔ a ≤ b := by
  constructor
  · intro h
    exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp h)
  · intro h
    exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr h)

private theorem withTopBot_bot_lt_coe (a : 𝕜) :
    (⊥ : WithTopBot 𝕜) < (a : WithTopBot 𝕜) :=
  WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

private theorem withTopBot_coe_lt_top (a : 𝕜) :
    (a : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) :=
  WithTop.coe_lt_top (a : WithBot 𝕜)

end WithTopBotLemmas

section Infimum

variable [ConditionallyCompleteLattice 𝕜]

/-- The function attached to a subset `F ⊆ E × 𝕜` by taking, at each base point `x`, the infimum
of the scalar heights `μ` with `(x, μ) ∈ F`. Empty fibers contribute the value `⊤`. -/
noncomputable def verticalInfimum (F : Set (E × 𝕜)) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (verticalHeights F x)

/-- Coercion-clean bridge: `verticalInfimum F x` is the infimum of the intrinsic owner
`Function.verticalHeights F x`. -/
theorem verticalInfimum_eq_sInf_verticalHeights (F : Set (E × 𝕜)) (x : E) :
    verticalInfimum F x = sInf (verticalHeights F x) := rfl

/-- Bridge to the raw set-comprehension formula for the vertical infimum. -/
theorem verticalInfimum_eq_sInf (F : Set (E × 𝕜)) (x : E) :
    verticalInfimum F x =
      sInf (((↑) : 𝕜 → WithTopBot 𝕜) '' {μ : 𝕜 | (x, μ) ∈ F}) := by
  simp [verticalHeights, verticalSection, verticalInfimum_eq_sInf_verticalHeights]

/-- Every point of `F` lies in the epigraph of its attached vertical-infimum function. -/
theorem verticalInfimum_le_of_mem
    {F : Set (E × 𝕜)} {x : E} {μ : 𝕜} (h : (x, μ) ∈ F) :
    verticalInfimum F x ≤ μ := by
  rw [verticalInfimum_eq_sInf]
  exact sInf_le ⟨μ, h, rfl⟩

/-- If every point of `F` lies in the global epigraph `epi h`, then `h` is pointwise bounded
above by the vertical infimum attached to `F`. -/
theorem le_verticalInfimum_of_subset_epi
    {F : Set (E × 𝕜)} {h : E → WithTopBot 𝕜} (hF : F ⊆ epi h) :
    h ≤ verticalInfimum F := by
  intro x
  rw [verticalInfimum_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨μ, hμF, rfl⟩
  simpa [mem_epi_restrict_iff] using hF hμF

end Infimum

section EffectiveDomain

variable [ConditionallyCompleteLattice 𝕜]

/-- A point lies in the effective domain of `verticalInfimum F` exactly when the scalar vertical
fiber above that point is nonempty. -/
theorem mem_effectiveDomain_verticalInfimum_iff_verticalSection_nonempty
    (F : Set (E × 𝕜)) {x : E} :
    x ∈ dom(verticalInfimum F) ↔ (verticalSection F x).Nonempty := by
  rw [mem_effectiveDomain, verticalInfimum_eq_sInf_verticalHeights]
  constructor
  · intro hx
    by_contra h_empty
    have : ¬ sInf (verticalHeights F x) < (⊤ : WithTopBot 𝕜) := by
      simp [verticalHeights, Set.not_nonempty_iff_eq_empty.mp h_empty]
    exact this hx
  · rintro ⟨μ, hμ⟩
    exact lt_of_le_of_lt (sInf_le ⟨μ, hμ, rfl⟩) (withTopBot_coe_lt_top μ)

/-- Bridge form of `mem_effectiveDomain_verticalInfimum_iff_verticalSection_nonempty` using the
raw predicate `(x, μ) ∈ F`. -/
theorem mem_effectiveDomain_verticalInfimum_iff
    (F : Set (E × 𝕜)) {x : E} :
    x ∈ dom(verticalInfimum F) ↔ ∃ μ : 𝕜, (x, μ) ∈ F := by
  constructor
  · intro hx
    rcases (mem_effectiveDomain_verticalInfimum_iff_verticalSection_nonempty (F := F)).1 hx with
      ⟨μ, hμ⟩
    exact ⟨μ, by simpa [verticalSection] using hμ⟩
  · rintro ⟨μ, hμ⟩
    exact
      (mem_effectiveDomain_verticalInfimum_iff_verticalSection_nonempty (F := F)).2
        ⟨μ, by simpa [verticalSection] using hμ⟩

/-- The effective domain of `verticalInfimum F` is the first-coordinate projection of `F`. -/
theorem effectiveDomain_verticalInfimum_eq_image_fst
    (F : Set (E × 𝕜)) :
    dom(verticalInfimum F) = Prod.fst '' F := by
  ext x
  constructor
  · intro hx
    rcases (mem_effectiveDomain_verticalInfimum_iff F).1 hx with ⟨μ, hμ⟩
    exact ⟨(x, μ), hμ, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (mem_effectiveDomain_verticalInfimum_iff F).2 ⟨p.2, hp⟩

end EffectiveDomain

section LinearOrder

variable [ConditionallyCompleteLinearOrder 𝕜]

private theorem exists_mem_lt_of_lt_verticalInfimum
    {F : Set (E × 𝕜)} {x : E} {α : 𝕜} (h : verticalInfimum F x < α) :
    ∃ μ : 𝕜, (x, μ) ∈ F ∧ μ < α := by
  rw [verticalInfimum_eq_sInf] at h
  rcases sInf_lt_iff.mp h with ⟨r, hr, hrα⟩
  rcases hr with ⟨μ, hμ, rfl⟩
  exact ⟨μ, hμ, withTopBot_coe_lt_coe_iff.mp hrα⟩

section Topology

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

/-- If the vertical section of `F` above `x` is upward closed, then its closure is exactly the set
of heights lying above the vertical infimum. -/
theorem closure_verticalSection_eq_preimage_Ici_of_upward_closed
    (F : Set (E × 𝕜)) (x : E)
    (hup : ∀ {μ ν : 𝕜}, μ ∈ verticalSection F x → μ ≤ ν → ν ∈ verticalSection F x) :
    closure (verticalSection F x) =
      verticalSection (epi (verticalInfimum F)) x := by
  let S : Set 𝕜 := verticalSection F x
  let T : Set 𝕜 := verticalSection (epi (verticalInfimum F)) x
  change closure S = T
  by_cases hbot : verticalInfimum F x = ⊥
  · have hSuniv : S = Set.univ := by
      ext μ
      constructor
      · intro _
        simp
      · intro _
        have hlt : verticalInfimum F x < μ := by
          rw [hbot]
          exact withTopBot_bot_lt_coe μ
        rcases exists_mem_lt_of_lt_verticalInfimum hlt with ⟨ν, hνF, hνμ⟩
        have hνS : ν ∈ S := by
          simpa [S, verticalSection] using hνF
        exact hup hνS hνμ.le
    rw [hSuniv]
    ext μ
    simp [T, verticalSection, mem_epi_restrict_iff, hbot]
  · by_cases htop : verticalInfimum F x = ⊤
    · have hSempty : S = ∅ := by
        ext μ
        constructor
        · intro hμ
          have hμF : (x, μ) ∈ F := by
            simpa [S, verticalSection] using hμ
          have hle : verticalInfimum F x ≤ μ := by
            simpa using (verticalInfimum_le_of_mem hμF : verticalInfimum F x ≤ μ)
          rw [htop] at hle
          simp at hle
        · simp
      rw [hSempty]
      ext μ
      simp [T, verticalSection, mem_epi_restrict_iff, htop]
    · cases hvi : verticalInfimum F x with
      | none =>
          have htop' : verticalInfimum F x = (⊤ : WithTopBot 𝕜) := by
            simpa [WithTopBot] using hvi
          exact (htop htop').elim
      | some z =>
          cases hz : z with
          | bot =>
              have hbot' : verticalInfimum F x = (⊥ : WithTopBot 𝕜) := by
                simpa [WithTopBot, hz] using hvi
              exact (hbot hbot').elim
          | coe a =>
              have ha : verticalInfimum F x = (a : WithTopBot 𝕜) := by
                simpa [WithTopBot, hz] using hvi
              have hIoi_subset : Set.Ioi a ⊆ S := by
                intro μ hμ
                have hlt : verticalInfimum F x < μ := by
                  rw [ha]
                  exact withTopBot_coe_lt_coe_iff.mpr hμ
                rcases exists_mem_lt_of_lt_verticalInfimum hlt with ⟨ν, hνF, hνμ⟩
                have hνS : ν ∈ S := by
                  simpa [S, verticalSection] using hνF
                exact hup hνS hνμ.le
              have hsubset : S ⊆ Set.Ici a := by
                intro μ hμ
                have hμF : (x, μ) ∈ F := by
                  simpa [S, verticalSection] using hμ
                have hle : (a : WithTopBot 𝕜) ≤ μ := by
                  rw [← ha]
                  simpa using (verticalInfimum_le_of_mem hμF : verticalInfimum F x ≤ μ)
                exact withTopBot_coe_le_coe_iff.mp hle
              have hclosure : closure S = Set.Ici a := by
                apply le_antisymm
                · exact closure_minimal hsubset isClosed_Ici
                · intro μ hμ
                  have hμ' : μ ∈ closure (Set.Ioi a) := by
                    rw [closure_Ioi a]
                    exact hμ
                  exact closure_mono hIoi_subset hμ'
              rw [hclosure]
              ext μ
              constructor
              · intro hμ
                have : (a : WithTopBot 𝕜) ≤ μ :=
                  withTopBot_coe_le_coe_iff.mpr hμ
                simpa [T, verticalSection, mem_epi_restrict_iff, ha] using this
              · intro hμ
                have : (a : WithTopBot 𝕜) ≤ μ := by
                  simpa [T, verticalSection, mem_epi_restrict_iff, ha] using hμ
                exact withTopBot_coe_le_coe_iff.mp this

end Topology

end LinearOrder

section NoBotOrder

variable [ConditionallyCompleteLattice 𝕜] [NoBotOrder 𝕜] [Nonempty 𝕜]

/-- The vertical infimum of the global epigraph `epi h` recovers `h` itself. -/
@[simp] theorem verticalInfimum_epi (h : E → WithTopBot 𝕜) :
    verticalInfimum (epi h) = h := by
  apply le_antisymm
  · intro x
    by_cases htop : h x = ⊤
    · simpa [htop]
    by_cases hbot : h x = ⊥
    · have hle_all : ∀ μ : 𝕜, verticalInfimum (epi h) x ≤ μ := by
        intro μ
        exact verticalInfimum_le_of_mem ((mem_epi_restrict_iff).2 ⟨by simp, by simpa [hbot]⟩)
      have hbot' : verticalInfimum (epi h) x = ⊥ := by
        by_contra hne
        cases hvi : verticalInfimum (epi h) x with
        | none =>
            have htop' : verticalInfimum (epi h) x = (⊤ : WithTopBot 𝕜) := by
              simpa [WithTopBot] using hvi
            have μ0 : 𝕜 := Classical.choice (inferInstance : Nonempty 𝕜)
            have : (⊤ : WithTopBot 𝕜) ≤ μ0 := by
              simpa [htop'] using hle_all μ0
            have hnot : ¬ ((⊤ : WithTopBot 𝕜) ≤ μ0) := by simp
            exact (hnot this).elim
        | some z =>
            cases hz : z with
            | bot =>
                have hbot'' : verticalInfimum (epi h) x = (⊥ : WithTopBot 𝕜) := by
                  simpa [WithTopBot, hz] using hvi
                exact hne hbot''
            | coe a =>
                have hcoe : verticalInfimum (epi h) x = (a : WithTopBot 𝕜) := by
                  simpa [WithTopBot, hz] using hvi
                rcases exists_not_ge a with ⟨μ, hnaμ⟩
                have haμ : (a : WithTopBot 𝕜) ≤ μ := by
                  simpa [hcoe] using hle_all μ
                exact hnaμ (withTopBot_coe_le_coe_iff.mp haμ)
      simpa [hbot, hbot']
    · cases hhx : h x with
      | none => exact (htop hhx).elim
      | some z =>
          cases hz : z with
          | bot => exact (hbot (by simpa [WithTopBot, hz] using hhx)).elim
          | coe a =>
              have ha : h x = (a : WithTopBot 𝕜) := by
                simpa [WithTopBot, hz] using hhx
              have hxepi : (x, a) ∈ epi h := (mem_epi_restrict_iff).2 ⟨by simp, by simpa [ha]⟩
              have hle : verticalInfimum (epi h) x ≤ a := verticalInfimum_le_of_mem hxepi
              simpa [ha] using hle
  · exact le_verticalInfimum_of_subset_epi (subset_rfl : epi h ⊆ epi h)

/-- If the global epigraph `epi h` is contained in `F`, then the vertical infimum attached to `F`
is pointwise bounded above by `h`. -/
theorem verticalInfimum_le_of_epi_subset
    {F : Set (E × 𝕜)} {h : E → WithTopBot 𝕜} (hF : epi h ⊆ F) :
    verticalInfimum F ≤ h := by
  have hsubset : epi h ⊆ epi (verticalInfimum F) := by
    intro p hp
    exact (mem_epi_iff).2 (verticalInfimum_le_of_mem (hF hp))
  have hle : verticalInfimum F ≤ verticalInfimum (epi h) :=
    le_verticalInfimum_of_subset_epi (F := epi h) (h := verticalInfimum F) hsubset
  simpa [verticalInfimum_epi] using hle

end NoBotOrder

section Convex

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

section Owner

variable [DenselyOrdered 𝕜]

local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

/-- Theorem 5.3 on the canonical owner surface: if `F ⊆ E × 𝕜` is convex, then
`x ↦ inf {μ | (x, μ) ∈ F}` is convex on `Set.univ`. -/
theorem isConvex_verticalInfimum
    {F : Set (E × 𝕜)} (hF : Convex 𝕜 F) :
    (verticalInfimum F).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_lt_affine_upper_bound]
  intro x y α β t hx hy ht0 ht1
  rcases exists_mem_lt_of_lt_verticalInfimum (F := F) (x := x) (α := α) hx with
    ⟨μ, hμF, hμα⟩
  rcases exists_mem_lt_of_lt_verticalInfimum (F := F) (x := y) (α := β) hy with
    ⟨ν, hνF, hνβ⟩
  have hcombF : (1 - t) • (x, μ) + t • (y, ν) ∈ F :=
    hF hμF hνF (sub_nonneg.mpr ht1.le) ht0.le (sub_add_cancel 1 t)
  have hle :
      verticalInfimum F ((1 - t) • x + t • y) ≤ ((1 - t) * μ + t * ν : 𝕜) := by
    have hmem : ((1 - t) • x + t • y, (1 - t) * μ + t * ν) ∈ F := by
      simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
        add_assoc, mul_comm, mul_left_comm, mul_assoc] using hcombF
    exact verticalInfimum_le_of_mem hmem
  have hlt : ((1 - t) * μ + t * ν : 𝕜) < ((1 - t) * α + t * β : 𝕜) := by
    have h1t : 0 < 1 - t := sub_pos.mpr ht1
    exact add_lt_add
      (mul_lt_mul_of_pos_left hμα h1t)
      (mul_lt_mul_of_pos_left hνβ ht0)
  exact lt_of_le_of_lt hle (withTopBot_coe_lt_coe_iff.mpr hlt)

end Owner

end Convex

end Function

end
