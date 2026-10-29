import BstLean.Part293Envelope1

namespace BstLean.Part293.Envelope
open Real

noncomputable def v90 (x : ℝ) : ℝ := (v88 x) * (v89 x)

theorem v90_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134466970471058391 / 1000000000000000000 : ℝ) ≤ v90 x ∧ v90 x ≤ (67410044460596113 / 500000000000000000 : ℝ) := by
  have h88 := v88_bounds x hx0 hx1
  have h89 := v89_bounds x hx0 hx1
  unfold v90
  constructor <;> interval_num

noncomputable def v91 (x : ℝ) : ℝ := √((1521 / 500 : ℝ))

theorem v91_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1744133022449835963 / 1000000000000000000 : ℝ) ≤ v91 x ∧ v91 x ≤ (436033255612458991 / 250000000000000000 : ℝ) := by
  unfold v91
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v92 (x : ℝ) : ℝ := (v5 x) * (v91 x)

theorem v92_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v92 x ∧ v92 x ≤ (424383256954266387 / 62500000000000000 : ℝ) := by
  have h5 := v5_bounds x hx0 hx1
  have h91 := v91_bounds x hx0 hx1
  unfold v92
  constructor <;> interval_num

noncomputable def v93 (x : ℝ) : ℝ := (v92 x) * (v0 x)

theorem v93_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v93 x ∧ v93 x ≤ (424383256954267 / 500000000000000000 : ℝ) := by
  have h92 := v92_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v93
  constructor <;> interval_num

noncomputable def v94 (x : ℝ) : ℝ := (v0 x) * ((17 : ℝ))

theorem v94_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v94 x ∧ v94 x ≤ (2125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v94
  constructor <;> interval_num

noncomputable def v95 (x : ℝ) : ℝ := ((1 : ℝ)) - (v94 x)

theorem v95_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (498937499999999999 / 500000000000000000 : ℝ) ≤ v95 x ∧ v95 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h94 := v94_bounds x hx0 hx1
  unfold v95
  constructor <;> interval_num

noncomputable def v96 (x : ℝ) : ℝ := √(v95 x)

theorem v96_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (124867116868293231 / 125000000000000000 : ℝ) ≤ v96 x ∧ v96 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h95 := v95_bounds x hx0 hx1
  unfold v96
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v97 (x : ℝ) : ℝ := (v93 x) / (v96 x)

theorem v97_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v97 x ∧ v97 x ≤ (424834884073099 / 500000000000000000 : ℝ) := by
  have h93 := v93_bounds x hx0 hx1
  have h96 := v96_bounds x hx0 hx1
  unfold v97
  constructor <;> interval_num

noncomputable def v98 (x : ℝ) : ℝ := (v90 x) * (v97 x)

theorem v98_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v98 x ∧ v98 x ≤ (114552553695121 / 1000000000000000000 : ℝ) := by
  have h90 := v90_bounds x hx0 hx1
  have h97 := v97_bounds x hx0 hx1
  unfold v98
  constructor <;> interval_num

noncomputable def v99 (x : ℝ) : ℝ := (v18 x) / ((1991 / 2000 : ℝ))

theorem v99_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v99 x ∧ v99 x ≤ (11941004749 / 250000000000000000 : ℝ) := by
  have h18 := v18_bounds x hx0 hx1
  unfold v99
  constructor <;> interval_num

noncomputable def v100 (x : ℝ) : ℝ := (v98 x) + (v99 x)

theorem v100_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v100 x ∧ v100 x ≤ (57300158857059 / 500000000000000000 : ℝ) := by
  have h98 := v98_bounds x hx0 hx1
  have h99 := v99_bounds x hx0 hx1
  unfold v100
  constructor <;> interval_num

noncomputable def v101 (x : ℝ) : ℝ := (v86 x) + (v100 x)

theorem v101_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v101 x ∧ v101 x ≤ (11552872575528357 / 500000000000000000 : ℝ) := by
  have h86 := v86_bounds x hx0 hx1
  have h100 := v100_bounds x hx0 hx1
  unfold v101
  constructor <;> interval_num

noncomputable def v102 (x : ℝ) : ℝ := (v7 x) * ((2 : ℝ))

theorem v102_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v102 x ∧ v102 x ≤ (5252121750000003 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v102
  constructor <;> interval_num

noncomputable def v103 (x : ℝ) : ℝ := (v11 x) * ((2 : ℝ))

theorem v103_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1682578972886562607 / 1000000000000000000 : ℝ) ≤ v103 x ∧ v103 x ≤ (1687768096126571857 / 1000000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v103
  constructor <;> interval_num

noncomputable def v104 (x : ℝ) : ℝ := (v103 x) * (v4 x)

theorem v104_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v104 x ∧ v104 x ≤ (2865088740065247727 / 500000000000000000 : ℝ) := by
  have h103 := v103_bounds x hx0 hx1
  have h4 := v4_bounds x hx0 hx1
  unfold v104
  constructor <;> interval_num

noncomputable def v105 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v105_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v105 x ∧ v105 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v105
  constructor <;> interval_num

noncomputable def v106 (x : ℝ) : ℝ := √(v105 x)

theorem v106_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v106 x ∧ v106 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h105 := v105_bounds x hx0 hx1
  unfold v106
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v107 (x : ℝ) : ℝ := (v104 x) * (v106 x)

theorem v107_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v107 x ∧ v107 x ≤ (5294894062973539 / 250000000000000000 : ℝ) := by
  have h104 := v104_bounds x hx0 hx1
  have h106 := v106_bounds x hx0 hx1
  unfold v107
  constructor <;> interval_num

noncomputable def v108 (x : ℝ) : ℝ := (v102 x) + (v107 x)

theorem v108_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v108 x ∧ v108 x ≤ (330396225023677 / 12500000000000000 : ℝ) := by
  have h102 := v102_bounds x hx0 hx1
  have h107 := v107_bounds x hx0 hx1
  unfold v108
  constructor <;> interval_num

noncomputable def v109 (x : ℝ) : ℝ := (v6 x) ^ 2

theorem v109_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v109 x ∧ v109 x ≤ (22416815361443203601 / 1000000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  unfold v109
  constructor <;> interval_num

noncomputable def v110 (x : ℝ) : ℝ := (v109 x) * ((27323 / 250000 : ℝ))

theorem v110_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v110 x ∧ v110 x ≤ (2449978584482850609 / 1000000000000000000 : ℝ) := by
  have h109 := v109_bounds x hx0 hx1
  unfold v110
  constructor <;> interval_num

noncomputable def v111 (x : ℝ) : ℝ := (v110 x) * (v0 x)

theorem v111_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v111 x ∧ v111 x ≤ (153123661530179 / 500000000000000000 : ℝ) := by
  have h110 := v110_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v111
  constructor <;> interval_num

noncomputable def v112 (x : ℝ) : ℝ := (v108 x) + (v111 x)

theorem v112_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v112 x ∧ v112 x ≤ (26737945324954519 / 1000000000000000000 : ℝ) := by
  have h108 := v108_bounds x hx0 hx1
  have h111 := v111_bounds x hx0 hx1
  unfold v112
  constructor <;> interval_num

noncomputable def v113 (x : ℝ) : ℝ := √((9 / 1991 : ℝ))

theorem v113_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (67233485235529197 / 1000000000000000000 : ℝ) ≤ v113 x ∧ v113 x ≤ (33616742617764599 / 500000000000000000 : ℝ) := by
  unfold v113
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v114 (x : ℝ) : ℝ := (v113 x) * ((2 : ℝ))

theorem v114_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134466970471058393 / 1000000000000000000 : ℝ) ≤ v114 x ∧ v114 x ≤ (134466970471058397 / 1000000000000000000 : ℝ) := by
  have h113 := v113_bounds x hx0 hx1
  unfold v114
  constructor <;> interval_num

noncomputable def v115 (x : ℝ) : ℝ := (v7 x) + ((1 : ℝ))

theorem v115_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v115 x ∧ v115 x ≤ (501313030437500001 / 500000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v115
  constructor <;> interval_num

noncomputable def v116 (x : ℝ) : ℝ := (v114 x) * (v115 x)

theorem v116_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (134466970471058391 / 1000000000000000000 : ℝ) ≤ v116 x ∧ v116 x ≤ (67410044460596113 / 500000000000000000 : ℝ) := by
  have h114 := v114_bounds x hx0 hx1
  have h115 := v115_bounds x hx0 hx1
  unfold v116
  constructor <;> interval_num

noncomputable def v117 (x : ℝ) : ℝ := √((1521 / 500 : ℝ))

theorem v117_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1744133022449835963 / 1000000000000000000 : ℝ) ≤ v117 x ∧ v117 x ≤ (436033255612458991 / 250000000000000000 : ℝ) := by
  unfold v117
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v118 (x : ℝ) : ℝ := (v6 x) * (v117 x)

theorem v118_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v118 x ∧ v118 x ≤ (8257841868763910003 / 1000000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  have h117 := v117_bounds x hx0 hx1
  unfold v118
  constructor <;> interval_num

noncomputable def v119 (x : ℝ) : ℝ := (v118 x) * (v0 x)

theorem v119_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v119 x ∧ v119 x ≤ (103223023359549 / 100000000000000000 : ℝ) := by
  have h118 := v118_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v119
  constructor <;> interval_num

noncomputable def v120 (x : ℝ) : ℝ := (v0 x) * ((25 : ℝ))

theorem v120_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v120 x ∧ v120 x ≤ (3125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v120
  constructor <;> interval_num

noncomputable def v121 (x : ℝ) : ℝ := ((1 : ℝ)) - (v120 x)

theorem v121_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (498437499999999999 / 500000000000000000 : ℝ) ≤ v121 x ∧ v121 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h120 := v120_bounds x hx0 hx1
  unfold v121
  constructor <;> interval_num

noncomputable def v122 (x : ℝ) : ℝ := √(v121 x)

theorem v122_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (998436277385792907 / 1000000000000000000 : ℝ) ≤ v122 x ∧ v122 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h121 := v121_bounds x hx0 hx1
  unfold v122
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v123 (x : ℝ) : ℝ := (v119 x) / (v122 x)

theorem v123_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v123 x ∧ v123 x ≤ (64615430209163 / 62500000000000000 : ℝ) := by
  have h119 := v119_bounds x hx0 hx1
  have h122 := v122_bounds x hx0 hx1
  unfold v123
  constructor <;> interval_num

noncomputable def v124 (x : ℝ) : ℝ := (v116 x) * (v123 x)

theorem v124_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v124 x ∧ v124 x ≤ (139383328743689 / 1000000000000000000 : ℝ) := by
  have h116 := v116_bounds x hx0 hx1
  have h123 := v123_bounds x hx0 hx1
  unfold v124
  constructor <;> interval_num

noncomputable def v125 (x : ℝ) : ℝ := (v18 x) / ((1991 / 2000 : ℝ))

theorem v125_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v125 x ∧ v125 x ≤ (11941004749 / 250000000000000000 : ℝ) := by
  have h18 := v18_bounds x hx0 hx1
  unfold v125
  constructor <;> interval_num

noncomputable def v126 (x : ℝ) : ℝ := (v124 x) + (v125 x)

theorem v126_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v126 x ∧ v126 x ≤ (69715546381343 / 500000000000000000 : ℝ) := by
  have h124 := v124_bounds x hx0 hx1
  have h125 := v125_bounds x hx0 hx1
  unfold v126
  constructor <;> interval_num

noncomputable def v127 (x : ℝ) : ℝ := (v112 x) + (v126 x)

theorem v127_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v127 x ∧ v127 x ≤ (13438688208858603 / 500000000000000000 : ℝ) := by
  have h112 := v112_bounds x hx0 hx1
  have h126 := v126_bounds x hx0 hx1
  unfold v127
  constructor <;> interval_num

noncomputable def v128 (x : ℝ) : ℝ := ((1 : ℝ)) / (v13 x)

theorem v128_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1710969366804456697 / 500000000000000000 : ℝ) ≤ v128 x ∧ v128 x ≤ (1736957193669443181 / 500000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v128
  constructor <;> interval_num

noncomputable def v129 (x : ℝ) : ℝ := (v13 x) ^ 2

theorem v129_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (41431607306366313 / 500000000000000000 : ℝ) ≤ v129 x ∧ v129 x ≤ (17079908364800001 / 200000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v129
  constructor <;> interval_num

noncomputable def v130 (x : ℝ) : ℝ := (v75 x) / (v129 x)

theorem v130_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v130 x ∧ v130 x ≤ (11065790235268997 / 50000000000000000 : ℝ) := by
  have h75 := v75_bounds x hx0 hx1
  have h129 := v129_bounds x hx0 hx1
  unfold v130
  constructor <;> interval_num

noncomputable def v131 (x : ℝ) : ℝ := (v128 x) + (v130 x)

theorem v131_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (3421938733608913393 / 1000000000000000000 : ℝ) ≤ v131 x ∧ v131 x ≤ (3695230192044266303 / 1000000000000000000 : ℝ) := by
  have h128 := v128_bounds x hx0 hx1
  have h130 := v130_bounds x hx0 hx1
  unfold v131
  constructor <;> interval_num

noncomputable def v132 (x : ℝ) : ℝ := (v101 x) ^ 2

theorem v132_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v132 x ∧ v132 x ≤ (266937729492791 / 500000000000000000 : ℝ) := by
  have h101 := v101_bounds x hx0 hx1
  unfold v132
  constructor <;> interval_num

noncomputable def v133 (x : ℝ) : ℝ := (v13 x) ^ 3

theorem v133_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (23852981211839281 / 1000000000000000000 : ℝ) ≤ v133 x ∧ v133 x ≤ (24956478906311171 / 1000000000000000000 : ℝ) := by
  have h13 := v13_bounds x hx0 hx1
  unfold v133
  constructor <;> interval_num

noncomputable def v134 (x : ℝ) : ℝ := (v132 x) / (v133 x)

theorem v134_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v134 x ∧ v134 x ≤ (22381917557567027 / 1000000000000000000 : ℝ) := by
  have h132 := v132_bounds x hx0 hx1
  have h133 := v133_bounds x hx0 hx1
  unfold v134
  constructor <;> interval_num

end BstLean.Part293.Envelope
