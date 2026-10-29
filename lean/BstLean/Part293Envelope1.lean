import BstLean.Part293Envelope0

namespace BstLean.Part293.Envelope
open Real

noncomputable def v45 (x : ℝ) : ℝ := (v44 x) ^ 24

theorem v45_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v45 x ∧ v45 x ≤ (767369 / 500000000000000000 : ℝ) := by
  have h44 := v44_bounds x hx0 hx1
  unfold v45
  constructor <;> interval_num

noncomputable def v46 (x : ℝ) : ℝ := (v40 x) + (v45 x)

theorem v46_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v46 x ∧ v46 x ≤ (845231 / 500000000000000000 : ℝ) := by
  have h40 := v40_bounds x hx0 hx1
  have h45 := v45_bounds x hx0 hx1
  unfold v46
  constructor <;> interval_num

noncomputable def v47 (x : ℝ) : ℝ := (v46 x) + ((33554432 / 191581231380566414401 : ℝ))

theorem v47_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (175143 / 1000000000000000000 : ℝ) ≤ v47 x ∧ v47 x ≤ (233201 / 125000000000000000 : ℝ) := by
  have h46 := v46_bounds x hx0 hx1
  unfold v47
  constructor <;> interval_num

noncomputable def v48 (x : ℝ) : ℝ := (v47 x) * ((4018 / 9 : ℝ))

theorem v48_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (39095809 / 500000000000000000 : ℝ) ≤ v48 x ∧ v48 x ≤ (832890329 / 1000000000000000000 : ℝ) := by
  have h47 := v47_bounds x hx0 hx1
  unfold v48
  constructor <;> interval_num

noncomputable def v49 (x : ℝ) : ℝ := √(v48 x)

theorem v49_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (8842602444981 / 1000000000000000000 : ℝ) ≤ v49 x ∧ v49 x ≤ (14429919689659 / 500000000000000000 : ℝ) := by
  have h48 := v48_bounds x hx0 hx1
  unfold v49
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v50 (x : ℝ) : ℝ := (v7 x) * ((2 : ℝ))

theorem v50_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v50 x ∧ v50 x ≤ (5252121750000003 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v50
  constructor <;> interval_num

noncomputable def v51 (x : ℝ) : ℝ := (v11 x) * ((2 : ℝ))

theorem v51_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1682578972886562607 / 1000000000000000000 : ℝ) ≤ v51 x ∧ v51 x ≤ (1687768096126571857 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v51
  constructor <;> interval_num

noncomputable def v52 (x : ℝ) : ℝ := (v51 x) * (v2 x)

theorem v52_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v52 x ∧ v52 x ≤ (697819351441249639 / 200000000000000000 : ℝ) := by
  have h51 := v51_bounds x hx0 hx1
  have h2 := v2_bounds x hx0 hx1
  unfold v52
  constructor <;> interval_num

noncomputable def v53 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v53_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v53 x ∧ v53 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v53
  constructor <;> interval_num

noncomputable def v54 (x : ℝ) : ℝ := √(v53 x)

theorem v54_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v54 x ∧ v54 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h53 := v53_bounds x hx0 hx1
  unfold v54
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v55 (x : ℝ) : ℝ := (v52 x) * (v54 x)

theorem v55_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v55 x ∧ v55 x ≤ (12896213263154193 / 1000000000000000000 : ℝ) := by
  have h52 := v52_bounds x hx0 hx1
  have h54 := v54_bounds x hx0 hx1
  unfold v55
  constructor <;> interval_num

noncomputable def v56 (x : ℝ) : ℝ := (v50 x) + (v55 x)

theorem v56_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v56 x ∧ v56 x ≤ (18148335013154197 / 1000000000000000000 : ℝ) := by
  have h50 := v50_bounds x hx0 hx1
  have h55 := v55_bounds x hx0 hx1
  unfold v56
  constructor <;> interval_num

noncomputable def v57 (x : ℝ) : ℝ := (v3 x) ^ 2

theorem v57_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v57 x ∧ v57 x ≤ (7898364572744526401 / 1000000000000000000 : ℝ) := by
  have h3 := v3_bounds x hx0 hx1
  unfold v57
  constructor <;> interval_num

noncomputable def v58 (x : ℝ) : ℝ := (v57 x) * ((27323 / 250000 : ℝ))

theorem v58_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v58 x ∧ v58 x ≤ (863228060884394781 / 1000000000000000000 : ℝ) := by
  have h57 := v57_bounds x hx0 hx1
  unfold v58
  constructor <;> interval_num

noncomputable def v59 (x : ℝ) : ℝ := (v58 x) * (v0 x)

theorem v59_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v59 x ∧ v59 x ≤ (107903507610551 / 1000000000000000000 : ℝ) := by
  have h58 := v58_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v59
  constructor <;> interval_num

noncomputable def v60 (x : ℝ) : ℝ := (v56 x) + (v59 x)

theorem v60_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v60 x ∧ v60 x ≤ (18256238520764749 / 1000000000000000000 : ℝ) := by
  have h56 := v56_bounds x hx0 hx1
  have h59 := v59_bounds x hx0 hx1
  unfold v60
  constructor <;> interval_num

noncomputable def v61 (x : ℝ) : ℝ := √((9 / 1991 : ℝ))

theorem v61_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (67233485235529197 / 1000000000000000000 : ℝ) ≤ v61 x ∧ v61 x ≤ (33616742617764599 / 500000000000000000 : ℝ) := by
  unfold v61
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v62 (x : ℝ) : ℝ := (v61 x) * ((2 : ℝ))

theorem v62_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134466970471058393 / 1000000000000000000 : ℝ) ≤ v62 x ∧ v62 x ≤ (134466970471058397 / 1000000000000000000 : ℝ) := by
  have h61 := v61_bounds x hx0 hx1
  unfold v62
  constructor <;> interval_num

noncomputable def v63 (x : ℝ) : ℝ := (v7 x) + ((1 : ℝ))

theorem v63_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v63 x ∧ v63 x ≤ (501313030437500001 / 500000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v63
  constructor <;> interval_num

noncomputable def v64 (x : ℝ) : ℝ := (v62 x) * (v63 x)

theorem v64_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134466970471058391 / 1000000000000000000 : ℝ) ≤ v64 x ∧ v64 x ≤ (67410044460596113 / 500000000000000000 : ℝ) := by
  have h62 := v62_bounds x hx0 hx1
  have h63 := v63_bounds x hx0 hx1
  unfold v64
  constructor <;> interval_num

noncomputable def v65 (x : ℝ) : ℝ := √((1521 / 500 : ℝ))

theorem v65_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1744133022449835963 / 1000000000000000000 : ℝ) ≤ v65 x ∧ v65 x ≤ (436033255612458991 / 250000000000000000 : ℝ) := by
  unfold v65
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v66 (x : ℝ) : ℝ := (v3 x) * (v65 x)

theorem v66_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v66 x ∧ v66 x ≤ (1225429134790361137 / 250000000000000000 : ℝ) := by
  have h3 := v3_bounds x hx0 hx1
  have h65 := v65_bounds x hx0 hx1
  unfold v66
  constructor <;> interval_num

noncomputable def v67 (x : ℝ) : ℝ := (v66 x) * (v0 x)

theorem v67_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v67 x ∧ v67 x ≤ (306357283697591 / 500000000000000000 : ℝ) := by
  have h66 := v66_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v67
  constructor <;> interval_num

noncomputable def v68 (x : ℝ) : ℝ := (v0 x) * ((9 : ℝ))

theorem v68_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v68 x ∧ v68 x ≤ (1125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v68
  constructor <;> interval_num

noncomputable def v69 (x : ℝ) : ℝ := ((1 : ℝ)) - (v68 x)

theorem v69_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499437499999999999 / 500000000000000000 : ℝ) ≤ v69 x ∧ v69 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h68 := v68_bounds x hx0 hx1
  unfold v69
  constructor <;> interval_num

noncomputable def v70 (x : ℝ) : ℝ := √(v69 x)

theorem v70_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999437341707823121 / 1000000000000000000 : ℝ) ≤ v70 x ∧ v70 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h69 := v69_bounds x hx0 hx1
  unfold v70
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v71 (x : ℝ) : ℝ := (v67 x) / (v70 x)

theorem v71_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v71 x ∧ v71 x ≤ (122611902082463 / 200000000000000000 : ℝ) := by
  have h67 := v67_bounds x hx0 hx1
  have h70 := v70_bounds x hx0 hx1
  unfold v71
  constructor <;> interval_num

noncomputable def v72 (x : ℝ) : ℝ := (v64 x) * (v71 x)

theorem v72_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v72 x ∧ v72 x ≤ (20663184426943 / 250000000000000000 : ℝ) := by
  have h64 := v64_bounds x hx0 hx1
  have h71 := v71_bounds x hx0 hx1
  unfold v72
  constructor <;> interval_num

noncomputable def v73 (x : ℝ) : ℝ := (v18 x) / ((1991 / 2000 : ℝ))

theorem v73_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v73 x ∧ v73 x ≤ (11941004749 / 250000000000000000 : ℝ) := by
  have h18 := v18_bounds x hx0 hx1
  unfold v73
  constructor <;> interval_num

noncomputable def v74 (x : ℝ) : ℝ := (v72 x) + (v73 x)

theorem v74_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v74 x ∧ v74 x ≤ (82700501726769 / 1000000000000000000 : ℝ) := by
  have h72 := v72_bounds x hx0 hx1
  have h73 := v73_bounds x hx0 hx1
  unfold v74
  constructor <;> interval_num

noncomputable def v75 (x : ℝ) : ℝ := (v60 x) + (v74 x)

theorem v75_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v75 x ∧ v75 x ≤ (18338939022491519 / 1000000000000000000 : ℝ) := by
  have h60 := v60_bounds x hx0 hx1
  have h74 := v74_bounds x hx0 hx1
  unfold v75
  constructor <;> interval_num

noncomputable def v76 (x : ℝ) : ℝ := (v7 x) * ((2 : ℝ))

theorem v76_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v76 x ∧ v76 x ≤ (5252121750000003 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v76
  constructor <;> interval_num

noncomputable def v77 (x : ℝ) : ℝ := (v11 x) * ((2 : ℝ))

theorem v77_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1682578972886562607 / 1000000000000000000 : ℝ) ≤ v77 x ∧ v77 x ≤ (1687768096126571857 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v77
  constructor <;> interval_num

noncomputable def v78 (x : ℝ) : ℝ := (v77 x) * (v3 x)

theorem v78_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v78 x ∧ v78 x ≤ (2371654192818479119 / 500000000000000000 : ℝ) := by
  have h77 := v77_bounds x hx0 hx1
  have h3 := v3_bounds x hx0 hx1
  unfold v78
  constructor <;> interval_num

noncomputable def v79 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v79_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v79 x ∧ v79 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v79
  constructor <;> interval_num

noncomputable def v80 (x : ℝ) : ℝ := √(v79 x)

theorem v80_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v80 x ∧ v80 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h79 := v79_bounds x hx0 hx1
  unfold v80
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v81 (x : ℝ) : ℝ := (v78 x) * (v80 x)

theorem v81_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v81 x ∧ v81 x ≤ (8765981681038533 / 500000000000000000 : ℝ) := by
  have h78 := v78_bounds x hx0 hx1
  have h80 := v80_bounds x hx0 hx1
  unfold v81
  constructor <;> interval_num

noncomputable def v82 (x : ℝ) : ℝ := (v76 x) + (v81 x)

theorem v82_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v82 x ∧ v82 x ≤ (2278408511207707 / 100000000000000000 : ℝ) := by
  have h76 := v76_bounds x hx0 hx1
  have h81 := v81_bounds x hx0 hx1
  unfold v82
  constructor <;> interval_num

noncomputable def v83 (x : ℝ) : ℝ := (v5 x) ^ 2

theorem v83_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v83 x ∧ v83 x ≤ (15156441186218404901 / 1000000000000000000 : ℝ) := by
  have h5 := v5_bounds x hx0 hx1
  unfold v83
  constructor <;> interval_num

noncomputable def v84 (x : ℝ) : ℝ := (v83 x) * ((27323 / 250000 : ℝ))

theorem v84_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v84 x ∧ v84 x ≤ (165647777012418191 / 100000000000000000 : ℝ) := by
  have h83 := v83_bounds x hx0 hx1
  unfold v84
  constructor <;> interval_num

noncomputable def v85 (x : ℝ) : ℝ := (v84 x) * (v0 x)

theorem v85_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v85 x ∧ v85 x ≤ (51764930316381 / 250000000000000000 : ℝ) := by
  have h84 := v84_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v85
  constructor <;> interval_num

noncomputable def v86 (x : ℝ) : ℝ := (v82 x) + (v85 x)

theorem v86_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v86 x ∧ v86 x ≤ (4598228966668519 / 200000000000000000 : ℝ) := by
  have h82 := v82_bounds x hx0 hx1
  have h85 := v85_bounds x hx0 hx1
  unfold v86
  constructor <;> interval_num

noncomputable def v87 (x : ℝ) : ℝ := √((9 / 1991 : ℝ))

theorem v87_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (67233485235529197 / 1000000000000000000 : ℝ) ≤ v87 x ∧ v87 x ≤ (33616742617764599 / 500000000000000000 : ℝ) := by
  unfold v87
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v88 (x : ℝ) : ℝ := (v87 x) * ((2 : ℝ))

theorem v88_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134466970471058393 / 1000000000000000000 : ℝ) ≤ v88 x ∧ v88 x ≤ (134466970471058397 / 1000000000000000000 : ℝ) := by
  have h87 := v87_bounds x hx0 hx1
  unfold v88
  constructor <;> interval_num

noncomputable def v89 (x : ℝ) : ℝ := (v7 x) + ((1 : ℝ))

theorem v89_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v89 x ∧ v89 x ≤ (501313030437500001 / 500000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v89
  constructor <;> interval_num

end BstLean.Part293.Envelope
