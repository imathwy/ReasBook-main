import stacks_proof.stacks_project.Chap10.Lemma_10_102_2.BiproductBlock

open CategoryTheory CategoryTheory.Limits ChainComplex Matrix

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

namespace FiniteFreeComplex

variable {e : ℕ}
/-- Helper for Lemma 10.102.2: the reduced complex keeps the original terms away from the two
distinguished degrees and replaces degrees `i + 1` and `i` by the split tail modules. -/
def reduced_complex_of_normalized_middle_object
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) (j : ℕ) : ModuleCat R :=
  if hSucc : j = i.1 + 1 then
    ModuleCat.of R (Fin ns → R)
  else if hCast : j = i.1 then
    ModuleCat.of R (Fin nt → R)
  else
    D.toChainComplex.X j

/-- Helper for Lemma 10.102.2: at degree `i + 1`, the reduced object is the source tail module. -/
theorem reduced_complex_of_normalized_middle_object_eq_succ
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) (i := i) (i.1 + 1) =
      ModuleCat.of R (Fin ns → R) := by
  -- The first branch of the definition is selected exactly in degree `i + 1`.
  simp [reduced_complex_of_normalized_middle_object]

/-- Helper for Lemma 10.102.2: at degree `i`, the reduced object is the target tail module. -/
theorem reduced_complex_of_normalized_middle_object_eq_castSucc
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) (i := i) i.1 =
      ModuleCat.of R (Fin nt → R) := by
  -- The second branch of the definition is selected exactly in degree `i`.
  simp [reduced_complex_of_normalized_middle_object]

/-- Helper for Lemma 10.102.2: away from the two distinguished degrees, the reduced object agrees
with the original chain complex. -/
theorem reduced_complex_of_normalized_middle_object_eq_of_ne_support
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hjSucc : j ≠ i.1 + 1) (hjCast : j ≠ i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j = D.toChainComplex.X j := by
  -- Outside the support, both conditional branches collapse to the inherited term.
  simp [reduced_complex_of_normalized_middle_object, hjSucc, hjCast]

/-- Helper for Lemma 10.102.2: in the upper adjacent branch, the target term is the split source
tail module. -/
theorem reduced_complex_of_normalized_middle_object_eq_target_of_upper
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hUpper : j = i.1 + 1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      ModuleCat.of R (Fin ns → R) := by
  -- After substituting the branch index, this is the defining `i + 1` case.
  subst hUpper
  exact reduced_complex_of_normalized_middle_object_eq_succ (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: in the middle branch, the source term is the split source tail
module. -/
theorem reduced_complex_of_normalized_middle_object_eq_source_of_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hMid : j = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      ModuleCat.of R (Fin ns → R) := by
  -- The source of the middle differential is the degree-`i + 1` tail term.
  subst hMid
  exact reduced_complex_of_normalized_middle_object_eq_succ (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: in the middle branch, the target term is the split target tail
module. -/
theorem reduced_complex_of_normalized_middle_object_eq_target_of_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hMid : j = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      ModuleCat.of R (Fin nt → R) := by
  -- After substituting the branch index, this is the defining degree-`i` case.
  subst hMid
  exact reduced_complex_of_normalized_middle_object_eq_castSucc (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: in the lower adjacent branch, the source term is the split target
tail module. -/
theorem reduced_complex_of_normalized_middle_object_eq_source_of_lower
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      ModuleCat.of R (Fin nt → R) := by
  -- The source of the lower adjacent differential is again the degree-`i` tail term.
  rw [hLower]
  exact reduced_complex_of_normalized_middle_object_eq_castSucc (R := R) (ns := ns) (nt := nt) D i

/-- Helper for Lemma 10.102.2: the source term in the upper adjacent differential is inherited
unchanged from `D`. -/
theorem reduced_complex_of_normalized_middle_object_eq_source_of_upper
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hUpper : j = i.1 + 1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      D.toChainComplex.X (j + 1) := by
  -- Once `j = i + 1`, the source degree `j + 1 = i + 2` is outside the two-point support.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support (R := R) (ns := ns) (nt := nt)
  · omega
  · omega

/-- Helper for Lemma 10.102.2: the target term in the lower adjacent differential is inherited
unchanged from `D`. -/
theorem reduced_complex_of_normalized_middle_object_eq_target_of_lower
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      D.toChainComplex.X j := by
  -- The lower target degree satisfies `j = i - 1`, hence lies outside the supported degrees.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support (R := R) (ns := ns) (nt := nt)
  · omega
  · omega

/-- Helper for Lemma 10.102.2: in the generic branch, the source term remains the original source
term of `D`. -/
theorem reduced_complex_of_normalized_middle_object_eq_source_of_generic
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hMid : j ≠ i.1) (hLower : j + 1 ≠ i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i (j + 1) =
      D.toChainComplex.X (j + 1) := by
  -- If `j + 1 = i + 1`, then `j = i`, contradicting `hMid`; the other support point is excluded
  -- directly by `hLower`.
  apply reduced_complex_of_normalized_middle_object_eq_of_ne_support (R := R) (ns := ns) (nt := nt)
  · intro h
    exact hMid (by simpa using Nat.succ.inj h)
  · exact hLower

/-- Helper for Lemma 10.102.2: in the generic branch, the target term remains the original target
term of `D`. -/
theorem reduced_complex_of_normalized_middle_object_eq_target_of_generic
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hUpper : j ≠ i.1 + 1) (hMid : j ≠ i.1) :
    reduced_complex_of_normalized_middle_object
        (R := R) (ns := ns) (nt := nt) (D := D) i j =
      D.toChainComplex.X j := by
  -- The generic target index is outside both distinguished degrees by assumption.
  exact reduced_complex_of_normalized_middle_object_eq_of_ne_support
    (R := R) (ns := ns) (nt := nt) D i hUpper hMid

/-- Helper for Lemma 10.102.2: rewriting `diffAt` back into chain-complex coordinates on the
source side exposes the original middle differential. -/
theorem termIso_hom_comp_diffAt
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    (D.termIso i.succ).hom ≫ ModuleCat.ofHom (D.diffAt i) =
      D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom := by
  -- Expanding `diffAt` cancels the source coordinate isomorphism.
  change
    (D.termIso i.succ).hom ≫
        (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
          (D.termIso i.castSucc).hom =
      D.toChainComplex.d (i.1 + 1) i.1 ≫ (D.termIso i.castSucc).hom
  simp [Category.assoc]

/-- Helper for Lemma 10.102.2: rewriting `diffAt` back into chain-complex coordinates on the
target side exposes the original middle differential. -/
theorem diffAt_comp_termIso_inv
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    ModuleCat.ofHom (D.diffAt i) ≫ (D.termIso i.castSucc).inv =
      (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 := by
  -- Expanding `diffAt` cancels the target coordinate isomorphism.
  change
    (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1 ≫
        (D.termIso i.castSucc).hom ≫ (D.termIso i.castSucc).inv =
      (D.termIso i.succ).inv ≫ D.toChainComplex.d (i.1 + 1) i.1
  simp [Category.assoc]

/-- Helper for Lemma 10.102.2: the reduced differential keeps the original adjacent maps away
from the split head summands and replaces the middle map by its tail component. -/
noncomputable def reduced_complex_of_normalized_middle_d
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (j : ℕ) :
    reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i (j + 1) ⟶
      reduced_complex_of_normalized_middle_object (R := R) (ns := ns) (nt := nt) D i j :=
  if hUpper : j = i.1 + 1 then
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_upper
          (R := R) (ns := ns) (nt := nt) D i hUpper) ≫
      D.toChainComplex.d (j + 1) (i.1 + 1) ≫
      (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_upper
          (R := R) (ns := ns) (nt := nt) D i hUpper).symm
  else if hMid : j = i.1 then
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_middle
          (R := R) (ns := ns) (nt := nt) D i hMid) ≫
      tailDiff ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_middle
          (R := R) (ns := ns) (nt := nt) D i hMid).symm
  else if hLower : j + 1 = i.1 then
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower) ≫
      biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
        D.toChainComplex.d i.1 j ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_lower
          (R := R) (ns := ns) (nt := nt) D i hLower).symm
  else
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_generic
          (R := R) (ns := ns) (nt := nt) D i hMid hLower) ≫
      D.toChainComplex.d (j + 1) j ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_generic
          (R := R) (ns := ns) (nt := nt) D i hUpper hMid).symm

/-- Helper for Lemma 10.102.2: projecting the normalized middle differential to the target tail
summand records exactly `tailDiff`. -/
theorem normalized_middle_tail_projection
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _)) :
    ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.fst =
      eSource.hom ≫ biprod.fst ≫ tailDiff := by
  -- Precompose the normalized middle block with `eSource.hom` and then project to the tail
  -- factor.
  calc
    ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom ≫ biprod.fst =
        eSource.hom ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom) ≫
          biprod.fst := by
            simp [Category.assoc]
    _ = eSource.hom ≫ biprod.map tailDiff (𝟙 _) ≫ biprod.fst := by
          rw [hmid]
    _ = eSource.hom ≫ biprod.fst ≫ tailDiff := by
          simp [Category.assoc]

/-- Helper for Lemma 10.102.2: including the source tail into the normalized middle block and
undoing the target splitting recovers the original middle differential on tail inputs. -/
theorem normalized_middle_tail_inclusion
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    (hmid :
      eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom =
        biprod.map tailDiff (𝟙 _)) :
    tailDiff ≫ biprod.inl ≫ eTarget.inv =
      biprod.inl ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) := by
  -- Precompose the normalized middle block with the tail inclusion and then cancel `eTarget`.
  calc
    tailDiff ≫ biprod.inl ≫ eTarget.inv =
        biprod.inl ≫ biprod.map tailDiff (𝟙 _) ≫ eTarget.inv := by
          simp [Category.assoc]
    _ = biprod.inl ≫ (eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) ≫ eTarget.hom) ≫
          eTarget.inv := by
            rw [← hmid]
    _ = biprod.inl ≫ eSource.inv ≫ ModuleCat.ofHom (D.diffAt i) := by
          simp [Category.assoc]

/-- Helper for Lemma 10.102.2: in the upper adjacent degree, the reduced differential is the
original upper differential followed by the source-tail projection. -/
theorem reduced_complex_of_normalized_middle_d_eq_upper
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R)) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff (i.1 + 1) =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) ≫
        D.toChainComplex.d (i.1 + 2) (i.1 + 1) ≫
        (D.termIso i.succ).hom ≫ eSource.hom ≫ biprod.fst ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_upper
            (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm := by
  -- This is exactly the `j = i + 1` branch of the reduced differential definition.
  simp [reduced_complex_of_normalized_middle_d]

/-- Helper for Lemma 10.102.2: in the middle degree, the reduced differential is the normalized
tail map. -/
theorem reduced_complex_of_normalized_middle_d_eq_middle
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R)) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff i.1 =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_middle
            (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) ≫
        tailDiff ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_middle
            (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm := by
  -- This is exactly the `j = i` branch of the reduced differential definition.
  simp [reduced_complex_of_normalized_middle_d]

/-- Helper for Lemma 10.102.2: in the lower adjacent degree, the reduced differential is the
original lower differential preceded by the target-tail inclusion. -/
theorem reduced_complex_of_normalized_middle_d_eq_lower
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    {j : ℕ}
    (hLower : j + 1 = i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLower) ≫
        biprod.inl ≫ eTarget.inv ≫ (D.termIso i.castSucc).inv ≫
          D.toChainComplex.d i.1 j ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_lower
            (R := R) (ns := ns) (nt := nt) D i hLower).symm := by
  -- This is exactly the `j + 1 = i` branch of the reduced differential definition.
  have hUpper : j ≠ i.1 + 1 := by
    omega
  have hMid : j ≠ i.1 := by
    omega
  simp [reduced_complex_of_normalized_middle_d, hUpper, hMid, hLower]

/-- Helper for Lemma 10.102.2: away from the three supported branches, the reduced differential is
the inherited differential of `D`. -/
theorem reduced_complex_of_normalized_middle_d_eq_generic
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e)
    (eSource :
      ModuleCat.of R (Fin (D.rank i.succ) → R) ≅
        biprod (ModuleCat.of R (Fin ns → R)) (ModuleCat.of R (Fin 1 → R)))
    (eTarget :
      ModuleCat.of R (Fin (D.rank i.castSucc) → R) ≅
        biprod (ModuleCat.of R (Fin nt → R)) (ModuleCat.of R (Fin 1 → R)))
    (tailDiff : ModuleCat.of R (Fin ns → R) ⟶ ModuleCat.of R (Fin nt → R))
    {j : ℕ}
    (hUpper : j ≠ i.1 + 1) (hMid : j ≠ i.1) (hLower : j + 1 ≠ i.1) :
    reduced_complex_of_normalized_middle_d (R := R) (D := D) (i := i)
        (eSource := eSource) (eTarget := eTarget) tailDiff j =
      eqToHom
          (reduced_complex_of_normalized_middle_object_eq_source_of_generic
            (R := R) (ns := ns) (nt := nt) D i hMid hLower) ≫
        D.toChainComplex.d (j + 1) j ≫
        eqToHom
          (reduced_complex_of_normalized_middle_object_eq_target_of_generic
            (R := R) (ns := ns) (nt := nt) D i hUpper hMid).symm := by
  -- Once the supported branches are excluded, the definition reduces to the generic case.
  simp [reduced_complex_of_normalized_middle_d, hUpper, hMid, hLower]

/-- Helper for Lemma 10.102.2: the transport between the upper and middle supported branches is
trivial, so the two consecutive branch formulas compose without an extra cast. -/
theorem reduced_complex_of_normalized_middle_upper_middle_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_upper
          (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl).symm ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_middle
          (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `ModuleCat.of R (Fin ns → R)`.
  simp

/-- Helper for Lemma 10.102.2: the transport between the middle and lower supported branches is
trivial, so the two consecutive branch formulas compose without an extra cast. -/
theorem reduced_complex_of_normalized_middle_middle_lower_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 1 = i.1) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_middle
          (R := R) (ns := ns) (nt := nt) D i (j := i.1) rfl).symm ≫
      eqToHom
        (by
          simpa [hLower] using
            reduced_complex_of_normalized_middle_object_eq_source_of_lower
              (R := R) (ns := ns) (nt := nt) D i hLower) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `ModuleCat.of R (Fin nt → R)`.
  simp

/-- Helper for Lemma 10.102.2: the transport between the generic branch above the support and the
upper supported branch is trivial, so the two consecutive branch formulas compose without an
extra cast. -/
theorem reduced_complex_of_normalized_middle_generic_upper_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) :
    eqToHom
        (reduced_complex_of_normalized_middle_object_eq_target_of_generic
          (R := R) (ns := ns) (nt := nt) D i
          (j := i.1 + 2) (by omega) (by omega)).symm ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_upper
          (R := R) (ns := ns) (nt := nt) D i (j := i.1 + 1) rfl) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `D.X (i + 2)`.
  simp

/-- Helper for Lemma 10.102.2: the transport between the lower supported branch and the generic
branch below the support is trivial, so the two consecutive branch formulas compose without an
extra cast. -/
theorem reduced_complex_of_normalized_middle_lower_generic_transport
    {ns nt : ℕ}
    (D : _root_.FiniteFreeComplex R e)
    (i : Fin e) {j : ℕ}
    (hLower : j + 2 = i.1) :
    eqToHom
        ((reduced_complex_of_normalized_middle_object_eq_target_of_lower
          (R := R) (ns := ns) (nt := nt) D i (j := j + 1)
          (by simpa [Nat.add_assoc] using hLower)).symm) ≫
      eqToHom
        (reduced_complex_of_normalized_middle_object_eq_source_of_generic
          (R := R) (ns := ns) (nt := nt) D i (j := j) (by omega) (by omega)) =
      𝟙 _ := by
  -- Both branch descriptions identify the same intermediate object `D.X (j + 1)`.
  simp


end FiniteFreeComplex

end
