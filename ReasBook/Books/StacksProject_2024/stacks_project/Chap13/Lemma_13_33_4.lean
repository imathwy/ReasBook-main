import Mathlib
import StacksProject_2024.stacks_project.Chap13.Remark_13_33_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D]

/- Domain-style sampling for Lemma 13.33.4:
- primary domain: sequential diagrams in a triangulated category, together with homotopy colimits
  and the source-facing structure maps from Remark 13.33.2;
- sampled owner declarations:
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsHomotopyColimitOf.exists_presentation`,
  `CategoryTheory.exists_iso_between_derived_colimit_presentations`,
  `CategoryTheory.sequentialTelescopeMap`,
  `Preorder.Monotone.functor`;
- best owner abstraction: the original sequential system is the canonical diagram `K : ℕ ⥤ D`;
  `IsHomotopyColimitOf K X` is the core owner, and a subsequence should be only a thin
  reindexing view of `K`, not a new ambient system owner;
- primitive-vs-derived split:
  the primitive data are the sequential diagram `K` and the strictly increasing index function
  `s : ℕ → ℕ`;
  the reindexed subsystem is derived API obtained by precomposing `K` with the monotone functor
  induced by `s`, while the explicit telescope-presentation maps and distinguished-triangle
  witnesses remain bridge-level source-facing data.

Source/core/bridge triage:
- `source-facing`: the sequential system `(K_n, f_n)` and the chosen subsequence of indices;
- `core/canonical`: the predicate `IsHomotopyColimitOf K X`;
- `bridge/view`: the reindexed diagram `hs.monotone.functor ⋙ K`, obtained by precomposing `K`
  along the monotone functor attached to the strictly increasing map `s`, together with the
  explicit telescope-presentation data used to compare chosen structure maps. -/

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Helper for Lemma 13.33.4: homotopy-colimit presentations transport across an isomorphism of
the target object. -/
theorem isHomotopyColimitOf_iff_of_iso {S : ℕ ⥤ D} [HasCoproduct S.obj]
    {X Y : D} (e : X ≅ Y) :
    IsHomotopyColimitOf S X ↔ IsHomotopyColimitOf S Y := by
  constructor
  · intro hX
    rcases hX with ⟨g, h, hT⟩
    let h' : Y ⟶ (∐ S.obj)⟦(1 : ℤ)⟧ := e.inv ≫ h
    have hIso :
        Triangle.mk (sequentialTelescopeMap S) (g ≫ e.hom) h' ≅
          Triangle.mk (sequentialTelescopeMap S) g h := by
      -- Only the third vertex changes, so the telescope triangle is transported by an identity
      -- isomorphism on the two coproduct terms and by `e` on the hocolim object.
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_
      · simp
      · simp
      · simp [h']
    have hT' :
        Triangle.mk (sequentialTelescopeMap S) (g ≫ e.hom) h' ∈ distTriang D := by
      -- The transported triangle stays distinguished because it is isomorphic to the original
      -- telescope triangle.
      exact isomorphic_distinguished _ hT _ hIso
    exact ⟨g ≫ e.hom, h', hT'⟩
  · intro hY
    rcases hY with ⟨g, h, hT⟩
    let h' : X ⟶ (∐ S.obj)⟦(1 : ℤ)⟧ := e.hom ≫ h
    have hIso :
        Triangle.mk (sequentialTelescopeMap S) (g ≫ e.inv) h' ≅
          Triangle.mk (sequentialTelescopeMap S) g h := by
      -- This is the inverse transport of the previous direction.
      refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
      · simp
      · simp
      · simp [h']
    have hT' :
        Triangle.mk (sequentialTelescopeMap S) (g ≫ e.inv) h' ∈ distTriang D := by
      exact isomorphic_distinguished _ hT _ hIso
    exact ⟨g ≫ e.inv, h', hT'⟩

/-- Helper for Lemma 13.33.4: compatibility with the successor maps propagates along every later
stage of a sequential diagram. -/
theorem compatible_maps_of_le (K : ℕ ⥤ D) {X : D} (ι : ∀ n, K.obj n ⟶ X)
    (hι : ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
    {m n : ℕ} (hmn : m ≤ n) :
    K.map (homOfLE hmn) ≫ ι n = ι m := by
  let τ : K ⟶ (Functor.const ℕ).obj X :=
    NatTrans.ofSequence ι (by
      intro n
      simpa using hι n)
  simpa using τ.naturality (homOfLE hmn)

/-- Helper for Lemma 13.33.4: a strictly increasing sequence on `ℕ` dominates the identity. -/
theorem le_strictMono_self {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    n ≤ s n := by
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      exact le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (hs (Nat.lt_succ_self n)))

/-- Helper for Lemma 13.33.4: every stage lies below some selected subsequence stage. -/
theorem exists_selected_ge {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    ∃ i, n ≤ s i :=
  ⟨n, le_strictMono_self hs n⟩

/-- Helper for Lemma 13.33.4: the least selected subsequence index whose stage is at least `n`. -/
def nextSelectedIndex (s : ℕ → ℕ) (hs : StrictMono s) (n : ℕ) : ℕ :=
  Nat.find (exists_selected_ge hs n)

/-- Helper for Lemma 13.33.4: the chosen selected stage really lies above the original stage. -/
theorem le_nextSelectedStage {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    n ≤ s (nextSelectedIndex s hs n) :=
  Nat.find_spec (exists_selected_ge hs n)

/-- Helper for Lemma 13.33.4: the chosen selected index is minimal among indices whose stage lies
above `n`. -/
theorem nextSelectedIndex_minimal {s : ℕ → ℕ} (hs : StrictMono s) (n i : ℕ)
    (hi : n ≤ s i) :
    nextSelectedIndex s hs n ≤ i :=
  Nat.find_min' (exists_selected_ge hs n) hi

/-- Helper for Lemma 13.33.4: at a selected stage `s i`, the least selected index above it is
exactly `i`. -/
theorem nextSelectedIndex_of_stage {s : ℕ → ℕ} (hs : StrictMono s) (i : ℕ) :
    nextSelectedIndex s hs (s i) = i := by
  apply le_antisymm
  · exact nextSelectedIndex_minimal hs (s i) i (le_rfl)
  · have hle : s i ≤ s (nextSelectedIndex s hs (s i)) := le_nextSelectedStage hs (s i)
    exact le_of_not_gt (fun hgt ↦ not_lt_of_ge hle (hs hgt))

/-- Helper for Lemma 13.33.4: consecutive selected stages are ordered by the subsequence. -/
theorem selected_stage_le_succ_stage {s : ℕ → ℕ} (hs : StrictMono s) (i : ℕ) :
    s i ≤ s (i + 1) := by
  exact hs.monotone (Nat.le_succ i)

/-- Helper for Lemma 13.33.4: if the next selected stage for `n` is still at least `n + 1`, then
the same selected index also works for `n + 1`. -/
theorem nextSelectedIndex_succ_eq_of_succ_le {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ)
    (h : n + 1 ≤ s (nextSelectedIndex s hs n)) :
    nextSelectedIndex s hs (n + 1) = nextSelectedIndex s hs n := by
  apply le_antisymm
  · exact nextSelectedIndex_minimal hs (n + 1) (nextSelectedIndex s hs n) h
  · have hle :
        n ≤ s (nextSelectedIndex s hs (n + 1)) := by
      exact le_trans (Nat.le_succ n) (le_nextSelectedStage hs (n + 1))
    exact nextSelectedIndex_minimal hs n (nextSelectedIndex s hs (n + 1)) hle

/-- Helper for Lemma 13.33.4: if the next selected stage for `n` is not at least `n + 1`, then it
is exactly `n`. -/
theorem nextSelectedStage_eq_of_not_succ_le {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ)
    (h : ¬ n + 1 ≤ s (nextSelectedIndex s hs n)) :
    s (nextSelectedIndex s hs n) = n := by
  apply le_antisymm
  · have hlt : s (nextSelectedIndex s hs n) < n + 1 := Nat.lt_of_not_ge h
    exact Nat.lt_succ_iff.mp hlt
  · exact le_nextSelectedStage hs n

/-- Helper for Lemma 13.33.4: once the selected stage for `n` is exactly `n`, the next selected
index for `n + 1` is the following subsequence index. -/
theorem nextSelectedIndex_succ_eq_succ {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ)
    (hstage : s (nextSelectedIndex s hs n) = n) :
    nextSelectedIndex s hs (n + 1) = nextSelectedIndex s hs n + 1 := by
  apply le_antisymm
  · have hbound :
        n + 1 ≤ s (nextSelectedIndex s hs n + 1) := by
      simpa [hstage] using Nat.succ_le_of_lt (hs (Nat.lt_succ_self (nextSelectedIndex s hs n)))
    exact nextSelectedIndex_minimal hs (n + 1) (nextSelectedIndex s hs n + 1) hbound
  · have hnot :
        ¬ nextSelectedIndex s hs (n + 1) ≤ nextSelectedIndex s hs n := by
      intro hle
      have hbound :
          n + 1 ≤ s (nextSelectedIndex s hs n) := by
        exact le_trans (le_nextSelectedStage hs (n + 1)) (hs.monotone hle)
      simpa [hstage] using hbound
    exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)

/-- Helper for Lemma 13.33.4: maps induced by two proofs of the same inequality in `ℕ` agree,
since the indexing category is thin. -/
theorem map_homOfLE_congr (K : ℕ ⥤ D) {m n : ℕ} (h₁ h₂ : m ≤ n) :
    K.map (homOfLE h₁) = K.map (homOfLE h₂) := by
  -- There is only one morphism `m ⟶ n` in the preorder category on `ℕ`.
  have hhom : (homOfLE h₁ : m ⟶ n) = homOfLE h₂ := Subsingleton.elim _ _
  simpa using congrArg K.map hhom

/-- Helper for Lemma 13.33.4: transporting the target stage of a `homOfLE` map across an index
equality commutes with postcomposition. -/
theorem comp_homOfLE_transport (K : ℕ ⥤ D) {m a b : ℕ} {X : D}
    (e : a = b) (ha : m ≤ a) (hb : m ≤ b) (t : K.obj b ⟶ X) :
    K.map (homOfLE ha) ≫ eqToHom (congrArg K.obj e) ≫ t =
      K.map (homOfLE hb) ≫ t := by
  -- Reduce the transport to the reflexive case, then use thinness of the preorder category.
  cases e
  simpa [Category.assoc] using
    congrArg (fun f ↦ f ≫ t) (map_homOfLE_congr K ha hb)

/-- Helper for Lemma 13.33.4: transporting a subsequence component across an equality of
subsequence indices just changes the object identity transport in front of that component. -/
theorem subsequence_component_transport (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    {X : D} (ι : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ X) {i j : ℕ} (e : i = j) :
    eqToHom (congrArg K.obj (congrArg s e)) ≫ ι j = ι i := by
  -- Reduce to the reflexive equality; then the transport is the identity.
  cases e
  simp

/-- Helper for Lemma 13.33.4: extend structure maps on the subsequence to maps from every stage by
going forward to the next selected stage. -/
def extendAlongSubsequence (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s) {X : D}
    (ι : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ X) :
    ∀ n, K.obj n ⟶ X :=
  fun n ↦
    K.map (homOfLE (le_nextSelectedStage hs n)) ≫ ι (nextSelectedIndex s hs n)

/-- Helper for Lemma 13.33.4: at a selected stage, the extension recovers the original
subsequence map. -/
theorem extendAlongSubsequence_at_selected_stage (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    {X : D} (ι : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ X) (i : ℕ) :
    extendAlongSubsequence K s hs ι (s i) = ι i := by
  -- At a selected stage, the target index is exactly `i`; use the transport lemmas to rewrite
  -- both the `homOfLE` codomain and the dependent component `ι`.
  let j := nextSelectedIndex s hs (s i)
  have hj : j = i := nextSelectedIndex_of_stage hs i
  have hcomp :
      K.map (homOfLE (show s i ≤ s j by
        simpa [j] using le_nextSelectedStage hs (s i))) ≫ ι j =
        K.map (homOfLE (show s i ≤ s i by exact le_rfl)) ≫ ι i := by
    have htransport :=
      comp_homOfLE_transport (K := K) (m := s i) (a := s j) (b := s i) (X := X)
        (congrArg s hj)
        (show s i ≤ s j by simpa [j] using le_nextSelectedStage hs (s i))
        (show s i ≤ s i by exact le_rfl)
        (ι i)
    simpa [j, Category.assoc, subsequence_component_transport (K := K) (s := s) (hs := hs)
      (ι := ι) hj] using htransport
  simpa [extendAlongSubsequence, j] using hcomp

/-- Helper for Lemma 13.33.4: if `n` and `n + 1` lie in the same subsequence block, extending
along the subsequence is compatible with the successor map. -/
theorem extendAlongSubsequence_same_block_compat (K : ℕ ⥤ D) (s : ℕ → ℕ)
    (hs : StrictMono s) {X : D}
    (ι : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ X) (n : ℕ)
    (h : n + 1 ≤ s (nextSelectedIndex s hs n)) :
    K.map (homOfLE (Nat.le_succ n)) ≫ extendAlongSubsequence K s hs ι (n + 1) =
      extendAlongSubsequence K s hs ι n := by
  -- TODO: normalize the composed `homOfLE` on the left to the common selected endpoint
  -- `s (nextSelectedIndex s hs n)`, then use `subsequence_component_transport` together with
  -- `comp_homOfLE_transport` to rewrite the dependent component `ι`.
  sorry

/-- Helper for Lemma 13.33.4: if `n` is itself the selected boundary of its block, the extension
compatibility across `n ⟶ n + 1` reduces to the subsequence compatibility. -/
theorem extendAlongSubsequence_boundary_block_compat (K : ℕ ⥤ D) (s : ℕ → ℕ)
    (hs : StrictMono s) {X : D}
    (ι : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ X)
    (hι :
      ∀ n,
        (hs.monotone.functor ⋙ K).map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
    (n : ℕ) (h : ¬ n + 1 ≤ s (nextSelectedIndex s hs n)) :
    K.map (homOfLE (Nat.le_succ n)) ≫ extendAlongSubsequence K s hs ι (n + 1) =
      extendAlongSubsequence K s hs ι n := by
  -- TODO: rewrite the boundary case to the selected stage `s (nextSelectedIndex s hs n) = n`,
  -- identify `nextSelectedIndex s hs (n + 1)` with the successor selected index, and then map
  -- the subsequence compatibility `hι` through the resulting `homOfLE` transport.
  sorry

/-- Helper for Lemma 13.33.4: the extended maps satisfy the full successor compatibility
relations. -/
theorem extendAlongSubsequence_compat (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s) {X : D}
    (ι : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ X)
    (hι :
      ∀ n,
        (hs.monotone.functor ⋙ K).map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) :
    ∀ n,
      K.map (homOfLE (Nat.le_succ n)) ≫ extendAlongSubsequence K s hs ι (n + 1) =
        extendAlongSubsequence K s hs ι n := by
  intro n
  by_cases h : n + 1 ≤ s (nextSelectedIndex s hs n)
  · -- If no subsequence boundary is crossed, both stages map into the same block.
    exact extendAlongSubsequence_same_block_compat K s hs ι n h
  · -- If a boundary is crossed, the compatibility is exactly the subsequence relation.
    exact extendAlongSubsequence_boundary_block_compat K s hs ι hι n h

/-- Helper for Lemma 13.33.4: the coproduct map `a` inserting the selected subsequence summands
into the full coproduct. -/
def subsequenceCoproductInclusion (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ (hs.monotone.functor ⋙ K).obj ⟶ ∐ K.obj :=
  Limits.Sigma.desc (fun i ↦ Sigma.ι K.obj (s i))

/-- Helper for Lemma 13.33.4: the coproduct map `c` induced by extending the subsequence
inclusions to every stage of the original diagram. -/
def extendAlongSubsequenceCoproductDesc (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ K.obj ⟶ ∐ (hs.monotone.functor ⋙ K).obj :=
  Limits.Sigma.desc
    (extendAlongSubsequence K s hs (fun i ↦ Sigma.ι (hs.monotone.functor ⋙ K).obj i))

/-- Helper for Lemma 13.33.4: precomposing `a` with a selected coproduct summand gives the
corresponding full coproduct summand. -/
theorem Sigma.ι_comp_subsequenceCoproductInclusion (K : ℕ ⥤ D) (s : ℕ → ℕ)
    (hs : StrictMono s) [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    (i : ℕ) :
    Sigma.ι (hs.monotone.functor ⋙ K).obj i ≫ subsequenceCoproductInclusion K s hs =
      Sigma.ι K.obj (s i) := by
  -- Unfold the coproduct desc map and read off its `i`th summand formula.
  letI : HasCoproduct (fun j ↦ K.obj (s j)) := by
    simpa using (inferInstance : HasCoproduct (hs.monotone.functor ⋙ K).obj)
  simpa [subsequenceCoproductInclusion] using
    (Limits.Sigma.ι_desc (fun j ↦ Sigma.ι K.obj (s j)) i)

/-- Helper for Lemma 13.33.4: precomposing `c` with the `n`th full coproduct summand gives the
extended selected-stage inclusion at stage `n`. -/
theorem Sigma.ι_comp_extendAlongSubsequenceCoproductDesc (K : ℕ ⥤ D) (s : ℕ → ℕ)
    (hs : StrictMono s) [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    (n : ℕ) :
    Sigma.ι K.obj n ≫ extendAlongSubsequenceCoproductDesc K s hs =
      extendAlongSubsequence K s hs (fun i ↦ Sigma.ι (hs.monotone.functor ⋙ K).obj i) n := by
  -- This is the defining component formula for the coproduct desc map.
  simpa [extendAlongSubsequenceCoproductDesc] using
    (Limits.Sigma.ι_desc
      (extendAlongSubsequence K s hs
        (fun i ↦ Sigma.ι (hs.monotone.functor ⋙ K).obj i)) n)

/-- Helper for Lemma 13.33.4: the extension map `c` retracts the subsequence inclusion `a`,
matching the easy identity `a ≫ c = 𝟙` from the source proof. -/
theorem subsequenceCoproductInclusion_comp_extendAlongSubsequenceCoproductDesc
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    subsequenceCoproductInclusion K s hs ≫ extendAlongSubsequenceCoproductDesc K s hs =
      𝟙 (∐ (hs.monotone.functor ⋙ K).obj) := by
  -- Check the identity on each selected summand of the subsequence coproduct.
  -- TODO: precompose with `Sigma.ι`, rewrite by the two coproduct component formulas, and reduce
  -- the selected summand to `extendAlongSubsequence_at_selected_stage`.
  sorry

/-- Helper for Lemma 13.33.4: the vanishing of the telescope composite forces the induced stage
maps to satisfy the successor compatibility relation. -/
theorem stage_maps_compatible_of_telescope_zero (S : ℕ ⥤ D) [HasCoproduct S.obj] {X : D}
    (g : ∐ S.obj ⟶ X) (hzero : sequentialTelescopeMap S ≫ g = 0) :
    ∀ n, S.map (homOfLE (Nat.le_succ n)) ≫ (Sigma.ι S.obj (n + 1) ≫ g) = Sigma.ι S.obj n ≫ g := by
  intro n
  -- Evaluate the telescope relation on the `n`th coproduct summand and rearrange the difference.
  have hzero' := congrArg (fun f ↦ Sigma.ι S.obj n ≫ f) hzero
  have hcompat :
      Sigma.ι S.obj n ≫ g - S.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι S.obj (n + 1) ≫ g = 0 := by
    simpa [Sigma.ι_comp_sequentialTelescopeMap_assoc, Preadditive.sub_comp, Category.assoc,
      comp_zero] using hzero'
  have hcompat' :
      Sigma.ι S.obj n ≫ g = S.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι S.obj (n + 1) ≫ g := by
    simpa [sub_eq_zero] using hcompat
  simpa [Category.assoc] using hcompat'.symm

/-- Helper for Lemma 13.33.4: the half-open interval block from stage `m` through stage
`m + l - 1`, viewed as a map into the full coproduct. -/
def intervalLengthToCoproduct (K : ℕ ⥤ D) [HasCoproduct K.obj] (m : ℕ) :
    ℕ → (K.obj m ⟶ ∐ K.obj)
  | 0 => 0
  | l + 1 =>
      intervalLengthToCoproduct K m l +
        K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l)

/-- Helper for Lemma 13.33.4: adjoining one more summand to an interval block changes the
telescope boundary only by the new terminal endpoint. -/
theorem intervalLengthToCoproduct_boundary_succ (K : ℕ ⥤ D) [HasCoproduct K.obj] (m l : ℕ) :
    (K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l)) ≫ sequentialTelescopeMap K =
      K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l) -
        K.map (homOfLE (Nat.le_add_right m (l + 1))) ≫ Sigma.ι K.obj (m + l + 1) := by
  have hcomp :
      homOfLE (Nat.le_add_right m (l + 1)) =
        homOfLE (Nat.le_add_right m l) ≫ homOfLE (Nat.le_succ (m + l)) := by
    simpa [homOfLE_comp, Nat.add_assoc] using
      (Subsingleton.elim
        (homOfLE (Nat.le_add_right m (l + 1)))
        (homOfLE (Nat.le_add_right m l) ≫ homOfLE (Nat.le_succ (m + l))))
  -- Evaluate the telescope map on the new endpoint summand.
  calc
    (K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l)) ≫ sequentialTelescopeMap K =
        K.map (homOfLE (Nat.le_add_right m l)) ≫
          (Sigma.ι K.obj (m + l) ≫ sequentialTelescopeMap K) := by
            simp [Category.assoc]
    _ =
        K.map (homOfLE (Nat.le_add_right m l)) ≫
          (Sigma.ι K.obj (m + l) -
            K.map (homOfLE (Nat.le_succ (m + l))) ≫ Sigma.ι K.obj (m + l + 1)) := by
              rw [Sigma.ι_comp_sequentialTelescopeMap]
    _ =
        K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l) -
          (K.map (homOfLE (Nat.le_add_right m l)) ≫
            K.map (homOfLE (Nat.le_succ (m + l)))) ≫ Sigma.ι K.obj (m + l + 1) := by
              rw [Preadditive.comp_sub, Category.assoc]
    _ =
        K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l) -
          K.map (homOfLE (Nat.le_add_right m (l + 1))) ≫ Sigma.ι K.obj (m + l + 1) := by
              rw [← Functor.map_comp, hcomp]

/-- Helper for Lemma 13.33.4: composing the half-open interval block with the telescope map
leaves only the boundary terms. -/
theorem intervalLengthToCoproduct_boundary (K : ℕ ⥤ D) [HasCoproduct K.obj] (m : ℕ) :
    ∀ l,
      intervalLengthToCoproduct K m l ≫ sequentialTelescopeMap K =
        Sigma.ι K.obj m - K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l)
  | 0 => by
      -- The empty interval contributes no summands, so its two boundary terms cancel.
      have hhom : (homOfLE (Nat.le_add_right m 0) : m ⟶ m + 0) = 𝟙 m := by
        exact Subsingleton.elim _ _
      simpa [intervalLengthToCoproduct, hhom]
  | l + 1 => by
      -- Split off the new endpoint summand and cancel the old interior boundary term.
      calc
        intervalLengthToCoproduct K m (l + 1) ≫ sequentialTelescopeMap K =
            intervalLengthToCoproduct K m l ≫ sequentialTelescopeMap K +
              ((K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l)) ≫
                sequentialTelescopeMap K) := by
                rw [intervalLengthToCoproduct, Preadditive.add_comp]
        _ = (Sigma.ι K.obj m - K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l)) +
              (K.map (homOfLE (Nat.le_add_right m l)) ≫ Sigma.ι K.obj (m + l) -
                K.map (homOfLE (Nat.le_add_right m (l + 1))) ≫ Sigma.ι K.obj (m + l + 1)) := by
                rw [intervalLengthToCoproduct_boundary, intervalLengthToCoproduct_boundary_succ]
        _ = Sigma.ι K.obj m - K.map (homOfLE (Nat.le_add_right m (l + 1))) ≫
              Sigma.ι K.obj (m + l + 1) := by
                abel

/-- Helper for Lemma 13.33.4: the half-open interval block from `m` up to but excluding `n`. -/
def interval_before_to_coproduct (K : ℕ ⥤ D) [HasCoproduct K.obj] (m n : ℕ) :
    K.obj m ⟶ ∐ K.obj :=
  intervalLengthToCoproduct K m (n - m)

/-- Helper for Lemma 13.33.4: for `m ≤ n`, the arithmetic endpoint of the interval block from
`m` to `n` is exactly `n`. -/
theorem interval_endpoint_eq (m n : ℕ) (hmn : m ≤ n) :
    m + (n - m) = n := by
  exact Nat.add_sub_of_le hmn

/-- Helper for Lemma 13.33.4: rewriting the endpoint `m + (n - m)` as `n` identifies the
terminal map of the interval block with the canonical map attached to `hmn`. -/
theorem interval_before_boundary_transport (K : ℕ ⥤ D) [HasCoproduct K.obj]
    (m n : ℕ) (hmn : m ≤ n) :
    K.map (homOfLE (Nat.le_add_right m (n - m))) ≫ Sigma.ι K.obj (m + (n - m)) =
      K.map (homOfLE hmn) ≫ Sigma.ι K.obj n := by
  -- Route correction: use the generic transport lemma instead of rewriting under a dependent
  -- codomain by hand.
  have htransport :
      K.map (homOfLE (Nat.le_add_right m (n - m))) ≫
          eqToHom (congrArg K.obj (interval_endpoint_eq m n hmn)) ≫ Sigma.ι K.obj n =
        K.map (homOfLE hmn) ≫ Sigma.ι K.obj n :=
    comp_homOfLE_transport (K := K) (m := m) (a := m + (n - m)) (b := n)
      (X := ∐ K.obj) (interval_endpoint_eq m n hmn)
      (Nat.le_add_right m (n - m)) hmn (Sigma.ι K.obj n)
  -- Once the arithmetic endpoint is identified with `n`, the two coproduct inclusions coincide.
  simpa [Category.assoc, interval_endpoint_eq m n hmn] using htransport

/-- Helper for Lemma 13.33.4: the interval block has the expected two-term telescope boundary. -/
theorem interval_before_to_coproduct_boundary (K : ℕ ⥤ D) [HasCoproduct K.obj]
    (m n : ℕ) (hmn : m ≤ n) :
    interval_before_to_coproduct K m n ≫ sequentialTelescopeMap K =
      Sigma.ι K.obj m - K.map (homOfLE hmn) ≫ Sigma.ι K.obj n := by
  -- Rewrite the interval length boundary, then normalize the endpoint transport to the chosen
  -- proof `hmn`.
  calc
    interval_before_to_coproduct K m n ≫ sequentialTelescopeMap K =
      Sigma.ι K.obj m -
        K.map (homOfLE (Nat.le_add_right m (n - m))) ≫ Sigma.ι K.obj (m + (n - m)) := by
          simpa [interval_before_to_coproduct] using intervalLengthToCoproduct_boundary K m (n - m)
    _ = Sigma.ι K.obj m - K.map (homOfLE hmn) ≫ Sigma.ι K.obj n := by
      rw [interval_before_boundary_transport K m n hmn]

/-- Helper for Lemma 13.33.4: the source block map `b` from the selected coproduct to the full
coproduct, built from the half-open intervals between consecutive selected indices. -/
def subsequenceIntervalBlockMap (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    ∐ (hs.monotone.functor ⋙ K).obj ⟶ ∐ K.obj :=
  Limits.Sigma.desc
    (fun i ↦ interval_before_to_coproduct K (s i) (s (i + 1)))

/-- Helper for Lemma 13.33.4: the first telescope square from the source proof, expressing that
the block map `b` intertwines the subsequence telescope map with the full one after inclusion. -/
theorem subsequence_interval_block_forward_square
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj] :
    sequentialTelescopeMap (hs.monotone.functor ⋙ K) ≫ subsequenceCoproductInclusion K s hs =
      subsequenceIntervalBlockMap K s hs ≫ sequentialTelescopeMap K := by
  -- This is the interval-boundary identity on each selected summand of the subsequence coproduct.
  -- TODO: evaluate both sides on each selected summand, then identify the resulting telescope
  -- boundary with `interval_before_to_coproduct_boundary`.
  sorry

-- Proof sketch: use Remark 13.33.2 to choose source-style telescope presentations from each
-- `IsHomotopyColimitOf` hypothesis, compare them using the subsequence reindexing bridge from
-- Remarks 13.33.2 and 13.33.3, and transport the resulting isomorphism back to the canonical
-- owner predicate. The converse direction is symmetric.
/-- Lemma 13.33.4: an object is a homotopy colimit of a strictly increasing
subsequence if and only if it is a homotopy colimit of the original sequential system. -/
theorem isHomotopyColimitOf_subsequence_iff
    (K : ℕ ⥤ D) (s : ℕ → ℕ) (hs : StrictMono s)
    [HasCoproduct K.obj] [HasCoproduct (hs.monotone.functor ⋙ K).obj]
    {Khocolim : D} :
    IsHomotopyColimitOf (hs.monotone.functor ⋙ K) Khocolim ↔ IsHomotopyColimitOf K Khocolim := by
  -- Route correction: `Remark_13_33_3` only handles honest natural transformations, so the
  -- remaining proof must compare the two telescope triangles via the textbook coproduct maps
  -- `a`, `b`, `c`, `d`, and the correction homotopy `h`.
  constructor
  · intro hsub
    let S := hs.monotone.functor ⋙ K
    rcases hsub with ⟨gsub, hsub', hTsub⟩
    let ιsub : ∀ n, S.obj n ⟶ Khocolim := fun n ↦ Sigma.ι S.obj n ≫ gsub
    have hιsub :
        ∀ n, S.map (homOfLE (Nat.le_succ n)) ≫ ιsub (n + 1) = ιsub n := by
      -- The successor compatibility is read off from the vanishing of the composite
      -- `sequentialTelescopeMap ≫ gsub`.
      have hzero :
          sequentialTelescopeMap S ≫ gsub = 0 := by
        simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hTsub
      simpa [ιsub] using stage_maps_compatible_of_telescope_zero S gsub hzero
    let ιfull : ∀ n, K.obj n ⟶ Khocolim := extendAlongSubsequence K s hs ιsub
    have hιfull :
        ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ιfull (n + 1) = ιfull n :=
      extendAlongSubsequence_compat K s hs ιsub hιsub
    -- TODO: complete the source-faithful bridge from the subsequence telescope triangle to the
    -- full telescope triangle by constructing the coproduct maps `a,b,c,d,h` and then apply TR3
    -- to obtain a distinguished telescope presentation of `Khocolim` for `K`.
    sorry
  · intro hfull
    rcases hfull with ⟨gfull, hfull', hTfull⟩
    let ιfull : ∀ n, K.obj n ⟶ Khocolim := fun n ↦ Sigma.ι K.obj n ≫ gfull
    have hιfull :
        ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ιfull (n + 1) = ιfull n := by
      -- The same telescope-vanishing computation gives the compatibility for the full system.
      have hzero : sequentialTelescopeMap K ≫ gfull = 0 := by
        simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ _ hTfull
      simpa [ιfull] using stage_maps_compatible_of_telescope_zero K gfull hzero
    let ιsub : ∀ n, (hs.monotone.functor ⋙ K).obj n ⟶ Khocolim := fun n ↦ ιfull (s n)
    have hιsub :
        ∀ n,
          (hs.monotone.functor ⋙ K).map (homOfLE (Nat.le_succ n)) ≫ ιsub (n + 1) = ιsub n := by
      intro n
      -- Restricting a full compatible family to the selected stages keeps compatibility because
      -- the full relations propagate along every later stage map.
      simpa [ιsub, Category.assoc] using
        compatible_maps_of_le K ιfull hιfull (hs.monotone (Nat.le_succ n))
    -- TODO: compare the chosen full telescope presentation with the subsequence telescope by the
    -- same interleaving maps as in the forward direction, then transport the resulting
    -- distinguished presentation back to `Khocolim`.
    sorry

end

end CategoryTheory
