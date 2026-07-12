import DifferentialForms_Cartan_1970.III.section12.«0012_Remark_III_6_extra_7».PositiveAxisKeyholeCornerFibers

open Filter MeasureTheory Bornology

open scoped unitInterval

noncomputable section


/-- Helper for Remark III.6-extra-7: equality on the keyhole contour can only occur at the same parameter
or at the identified endpoint pair `(0, 1)` / `(1, 0)`. -/
lemma positiveAxisKeyhole_simple_eq_or_endpoints
    {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) {s t : I}
    (hst : positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t) :
    s = t ∨ (s = (0 : I) ∧ t = (1 : I)) ∨ (s = (1 : I) ∧ t = (0 : I)) := by
  have hr : 0 < R := lt_trans hε hεR
  have hbreak := positive_axis_keyhole_breakpoint_values R ε
  rcases positive_axis_keyhole_parameter_cases s with
    hs0 | hsupper | hs18 | hsinner | hs14 | hslower | hs12 | hsouter | hs1
  · have hsEq : s = (0 : I) := Subtype.ext hs0
    -- If `s` is the initial endpoint, `t` must be one of the two parameters for the same corner.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [hsEq] using hbreak.1
    rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 htCorner with ht0 | ht1
    · left
      simpa [hsEq, ht0]
    · right
      left
      simpa [hsEq, ht1]
  · -- Route correction: use the branch geometry already proved for the four open pieces instead of
    -- trying to recurse on the concatenated path itself.
    rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR hsupper with
      ⟨ρs, hρs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR (Or.inl ⟨hsupper, htupper⟩) hst
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR htlower with
        ⟨ρt, hρt, htPath⟩
      have hsIm : 0 < (positiveAxisKeyhole R ε s).im := by
        rw [hsPath]
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ρs)
        have hre :=
          positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htIm : (positiveAxisKeyhole R ε t).im < 0 := by
        rw [htPath]
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := ρt)
        have hre :=
          positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have him : (positiveAxisKeyhole R ε s).im = (positiveAxisKeyhole R ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsupper.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsupper.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsupper.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext hs18
    -- The first interior corner has a singleton fiber.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by simpa [hsEq] using hbreak.2.1
    have htEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR hsinner with
      ⟨αs, hαs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.1]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR
        (Or.inr <| Or.inl ⟨hsinner, htinner⟩) hst
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          ε = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (-positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsinner.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ε = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ε αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hε, abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsinner.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsinner.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext hs14
    -- The lower inner corner also has a singleton fiber.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
            simpa [hsEq] using hbreak.2.2.1
    have htEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR hslower with
      ⟨ρs, hρs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR htupper with
        ⟨ρt, hρt, htPath⟩
      have hsIm : (positiveAxisKeyhole R ε s).im < 0 := by
        rw [hsPath]
        have hline := positiveAxisKeyhole_lower_lip_line (R := R) (ε := ε) (ρ := ρs)
        have hre :=
          positiveAxisKeyhole_lower_lip_re_pos (R := R) (ε := ε) (ρ := ρs) (lt_trans hε hρs.1)
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have htIm : 0 < (positiveAxisKeyhole R ε t).im := by
        rw [htPath]
        have hline := positiveAxisKeyhole_upper_lip_line (R := R) (ε := ε) (ρ := ρt)
        have hre :=
          positiveAxisKeyhole_upper_lip_re_pos (R := R) (ε := ε) (ρ := ρt) (lt_trans hε hρt.1)
        have hratio : 0 < ε / R := div_pos hε hr
        rw [hline]
        nlinarith
      have him : (positiveAxisKeyhole R ε s).im = (positiveAxisKeyhole R ε t).im := congrArg Complex.im hst
      have : False := by
        linarith [hsIm, htIm, him]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hρs.1, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.1]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR
        (Or.inr <| Or.inr <| Or.inl ⟨hslower, htlower⟩) hst
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hslower.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR htouter with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          ρs = R := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 ρs (-positiveAxisKeyholeAngle R ε) = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos (lt_trans hε hρs.1), abs_of_pos hr] using hnorm'
      have : False := by
        linarith [hρs.2, hnorm]
      exact this.elim
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hslower.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hslower.2]
      exact this.elim
  · have hsEq : s = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext hs12
    -- The lower outer corner has a singleton fiber as well.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
            simpa [hsEq] using hbreak.2.2.2.1
    have htEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 htCorner
    left
    simpa [hsEq, htEq]
  · rcases positive_axis_keyhole_eq_outer_arc_circleMap_of_mem_Ioo R ε hε hεR hsouter with
      ⟨αs, hαs, hsPath⟩
    rcases positive_axis_keyhole_parameter_cases t with
      ht0 | htupper | ht18 | htinner | ht14 | htlower | ht12 | htouter | ht1
    · have htEq : t = (0 : I) := Subtype.ext ht0
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by simpa [htEq] using hbreak.1
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
    · rcases positive_axis_keyhole_eq_upper_lip_circleMap_of_mem_Ioo R ε hε hεR htupper with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          R = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 8 : ℝ), by norm_num⟩ : I) := Subtype.ext ht18
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_upper_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 8 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases positive_axis_keyhole_eq_inner_arc_circleMap_of_mem_Ioo R ε hε hεR htinner with
        ⟨αt, hαt, htPath⟩
      have hnorm :
          R = ε := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε αt := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos hε] using hnorm'
      have : False := by
        linarith [hεR, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 4 : ℝ), by norm_num⟩ : I) := Subtype.ext ht14
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ε (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_inner_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 4 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · rcases positive_axis_keyhole_eq_lower_lip_circleMap_of_mem_Ioo R ε hε hεR htlower with
        ⟨ρt, hρt, htPath⟩
      have hnorm :
          R = ρt := by
        have hnorm' := congrArg norm <| calc
          circleMap 0 R αs = positiveAxisKeyhole R ε s := hsPath.symm
          _ = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 ρt (-positiveAxisKeyholeAngle R ε) := htPath
        simpa [norm_circleMap_zero, abs_of_pos hr, abs_of_pos (lt_trans hε hρt.1)] using hnorm'
      have : False := by
        linarith [hρt.2, hnorm]
      exact this.elim
    · have htEq : t = (⟨(1 / 2 : ℝ), by norm_num⟩ : I) := Subtype.ext ht12
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (-positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.1
      have : False := by
        have hsEq := (positiveAxisKeyhole_eq_lower_outer_corner_iff R ε hε hεR).1 hsCorner
        have hsval : (s : ℝ) = 1 / 2 := by simpa using congrArg Subtype.val hsEq
        linarith [hsouter.1]
      exact this.elim
    · left
      exact positiveAxisKeyhole_same_branch_injective R ε hε hεR
        (Or.inr <| Or.inr <| Or.inr ⟨hsouter, htouter⟩) hst
    · have htEq : t = (1 : I) := Subtype.ext ht1
      have hsCorner :
          positiveAxisKeyhole R ε s = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
        calc
          positiveAxisKeyhole R ε s = positiveAxisKeyhole R ε t := hst
          _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
              simpa [htEq] using hbreak.2.2.2.2
      have : False := by
        rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 hsCorner with hs0' | hs1'
        · have hs0val : (s : ℝ) = 0 := by simpa using congrArg Subtype.val hs0'
          linarith [hsouter.1]
        · have hs1val : (s : ℝ) = 1 := by simpa using congrArg Subtype.val hs1'
          linarith [hsouter.2]
      exact this.elim
  · have hsEq : s = (1 : I) := Subtype.ext hs1
    -- The terminal endpoint is the second parameter for the same upper outer corner.
    have htCorner :
        positiveAxisKeyhole R ε t = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
      calc
        positiveAxisKeyhole R ε t = positiveAxisKeyhole R ε s := hst.symm
        _ = circleMap 0 R (positiveAxisKeyholeAngle R ε) := by
            simpa [hsEq] using hbreak.2.2.2.2
    rcases (positiveAxisKeyhole_eq_upper_outer_corner_iff R ε hε hεR).1 htCorner with ht0 | ht1
    · right
      right
      simpa [hsEq, ht0]
    · left
      simpa [hsEq, ht1]
