import Mathlib

noncomputable section
namespace ConvexSpaceWithTop

variable {R : Type u} {M : Type v}
variable [LinearOrder R] [Semiring R] [IsStrictOrderedRing R] [ConvexSpace R M]

def restrict (f : StdSimplex R (WithTop M)) (h : f.weights ⊤ = 0) : StdSimplex R M where
  weights := f.weights.some
  nonneg x := f.nonneg x
  total := by
    rw [← f.total, ← zero_add (f.some.sum fun x r ↦ r), ← h, Eq.comm]
    simpa using Finsupp.sum_option_index_smul f.weights (fun _ : WithTop M => (1 : R))

omit [ConvexSpace R M] in
lemma restrict_single (x : M) :
    ConvexSpaceWithTop.restrict (R := R) (.single x) (by simp) = .single x := by
  ext a
  change (Finsupp.single (some x) 1).some a = Finsupp.single x 1 a
  simp

def combination (f : StdSimplex R (WithTop M)) : WithTop M :=
  if h : f.weights ⊤ = 0 then (convexCombination (restrict f h) : M) else ⊤

lemma combination_eq_top_iff (f : StdSimplex R (WithTop M)) :
    combination (M := M) f = ⊤ ↔ f.weights ⊤ ≠ 0 := by
  by_cases h : f.weights ⊤ = 0 <;> simp [combination, h]

omit [ConvexSpace R M] in
lemma join_weight_eq_zero_iff (F : StdSimplex R (StdSimplex R (WithTop M))) (m : WithTop M) :
    F.join.weights m = 0 ↔ (∀ d ∈ F.support, d.weights m = 0) := by
  simp only [StdSimplex.join, Finsupp.sum, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ mul_nonneg (F.nonneg x) (x.nonneg m)]
  refine forall₂_congr fun d hd => ⟨not_imp_not.mp fun h' =>
    (mul_pos ((F.nonneg d).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.mp hd)))
      ((d.nonneg m).lt_of_ne (Ne.symm h'))).ne', (mul_eq_zero_of_right _ ·)⟩

lemma map_combination_weight_top_eq_zero_iff (F : StdSimplex R (StdSimplex R (WithTop M))) :
    (F.map combination).weights ⊤ = 0 ↔ (∀ d ∈ F.support, d.weights ⊤ = 0) := by
  simp only [StdSimplex.map, Finsupp.mapDomain, Finsupp.sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ Finsupp.single_nonneg.mpr (F.nonneg x) ⊤]
  refine forall₂_congr fun d hd => ?_
  rw [Finsupp.single_apply_eq_zero, eq_comm, combination_eq_top_iff]
  have := Finsupp.mem_support_iff.mp hd; tauto

def outer (F : StdSimplex R (StdSimplex R (WithTop M))) (hF : F.join.weights ⊤ = 0) :
    StdSimplex R (StdSimplex R M) where
  weights := F.weights.mapDomain fun d =>
    if h : d.weights ⊤ = 0 then restrict d h else restrict F.join hF
  nonneg := F.weights.mapDomain_nonneg F.nonneg
  total := by simp [Finsupp.sum_mapDomain_index]

lemma join_zero_iff_map_zero (F : StdSimplex R (StdSimplex R (WithTop M))) :
    F.join.weights ⊤ = 0 ↔ (F.map combination).weights ⊤ = 0 :=
  (join_weight_eq_zero_iff F ⊤).trans (map_combination_weight_top_eq_zero_iff F).symm

lemma restrict_map_eq (F : StdSimplex R (StdSimplex R (WithTop M))) (hF : F.join.weights ⊤ = 0)
    (hmap : (F.map combination).weights ⊤ = 0 := (join_zero_iff_map_zero F).1 hF) :
    restrict (F.map combination) hmap =
      (outer F hF).map (ConvexSpace.convexCombination) := by
  ext m; simp only [restrict, StdSimplex.map, outer, Finsupp.some_apply]
  let g : StdSimplex R (WithTop M) → StdSimplex R M := fun d =>
    if h : d.weights ⊤ = 0 then restrict d h else restrict F.join hF
  let c := ConvexSpace.convexCombination (R := R) (M := M)
  rw [Finsupp.mapDomain_congr (g := fun d => (c (g d) : WithTop M))
    (by intro d hd; simp only [combination, (map_combination_weight_top_eq_zero_iff F).1 hmap d hd,
      ↓reduceDIte, c, g])]
  change (Finsupp.mapDomain (↑Function.Embedding.some ∘ (c ∘ g)) F.weights).some m =
    (Finsupp.mapDomain c (Finsupp.mapDomain g F.weights)) m
  rw [Finsupp.mapDomain_comp, ← Finsupp.embDomain_eq_mapDomain Function.Embedding.some]
  simp [Finsupp.mapDomain_comp]

omit [ConvexSpace R M] in
lemma restrict_join_eq (F : StdSimplex R (StdSimplex R (WithTop M))) (hF : F.join.weights ⊤ = 0) :
    restrict F.join hF = (outer F hF).join := by
  ext m; simp only [outer, StdSimplex.join]
  rw [Finsupp.sum_mapDomain_index (by intro; ext; simp) (by intros; ext; simp [add_mul])]
  change (F.weights.sum fun d r => r • d.weights) (some m) = _
  simpa only [Finsupp.sum_apply, Finsupp.smul_apply] using
    Finsupp.sum_congr fun d hd => by
      rw [dif_pos ((join_weight_eq_zero_iff F ⊤).1 hF d hd), restrict, Finsupp.some_apply]; rfl

lemma assoc (F : StdSimplex R (StdSimplex R (WithTop M))) :
    combination (F.map combination) = combination F.join := by
  by_cases hF : F.join.weights ⊤ = 0
  · rw [combination, dif_pos ((join_zero_iff_map_zero F).1 hF),
    combination, dif_pos hF, WithTop.coe_inj,
    restrict_map_eq F hF, ConvexSpace.assoc, ← restrict_join_eq F hF]
  · have : (F.map combination).weights ⊤ ≠ 0 :=
      fun h => hF ((join_zero_iff_map_zero F).2 h)
    simp [combination, hF, this]

/-- Adding a top element to a convex space gives a convex space, with `⊤` absorbing
any nonzero weight. -/
instance : ConvexSpace R (WithTop M) where
  convexCombination := combination
  assoc := assoc
  single x := by
    cases x with
    | top => simp [combination]
    | coe x => simp [combination, restrict_single x]

end ConvexSpaceWithTop
