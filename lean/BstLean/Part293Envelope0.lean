import BstLean.Part293ScalarTools
import BstLean.Part252MomentNum

namespace BstLean.Part293.Envelope
open Real

noncomputable def v0 (x : ℝ) : ℝ := x

theorem v0_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v0 x ∧ v0 x ≤ (1 / 8000 : ℝ) := by
  unfold v0
  exact ⟨hx0, hx1⟩

noncomputable def v1 (x : ℝ) : ℝ := π

theorem v1_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (392699 / 125000 : ℝ) ≤ v1 x ∧ v1 x ≤ (3141593 / 1000000 : ℝ) := by
  unfold v1
  constructor <;> linarith [pi_gt_d6, pi_lt_d6]

noncomputable def v2 (x : ℝ) : ℝ := BstLean.Part195.rotationConstant 2

theorem v2_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v2 x ∧ v2 x ≤ (103364223 / 50000000 : ℝ) := by
  unfold v2
  constructor
  · exact BstLean.Part195.rotationConstant_nonneg 2
  · apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

noncomputable def v3 (x : ℝ) : ℝ := BstLean.Part195.rotationConstant 4

theorem v3_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v3 x ∧ v3 x ≤ (70260073 / 25000000 : ℝ) := by
  unfold v3
  constructor
  · exact BstLean.Part195.rotationConstant_nonneg 4
  · apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

noncomputable def v4 (x : ℝ) : ℝ := BstLean.Part195.rotationConstant 6

theorem v4_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v4 x ∧ v4 x ≤ (169756067 / 50000000 : ℝ) := by
  unfold v4
  constructor
  · exact BstLean.Part195.rotationConstant_nonneg 6
  · apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

noncomputable def v5 (x : ℝ) : ℝ := BstLean.Part195.rotationConstant 8

theorem v5_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v5 x ∧ v5 x ≤ (389312743 / 100000000 : ℝ) := by
  unfold v5
  constructor
  · exact BstLean.Part195.rotationConstant_nonneg 8
  · apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

noncomputable def v6 (x : ℝ) : ℝ := BstLean.Part195.rotationConstant 12

theorem v6_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v6 x ∧ v6 x ≤ (236731997 / 50000000 : ℝ) := by
  unfold v6
  constructor
  · exact BstLean.Part195.rotationConstant_nonneg 12
  · apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

noncomputable def v7 (x : ℝ) : ℝ := (v0 x) * ((21008487 / 1000000 : ℝ))

theorem v7_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v7 x ∧ v7 x ≤ (2626060875000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v7
  constructor <;> interval_num

noncomputable def v8 (x : ℝ) : ℝ := √((88471 / 125000 : ℝ))

theorem v8_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (168257897288656261 / 200000000000000000 : ℝ) ≤ v8 x ∧ v8 x ≤ (420644743221640653 / 500000000000000000 : ℝ) := by
  unfold v8
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v9 (x : ℝ) : ℝ := (v0 x) * ((26927 / 500000 : ℝ))

theorem v9_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v9 x ∧ v9 x ≤ (6731750000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v9
  constructor <;> interval_num

noncomputable def v10 (x : ℝ) : ℝ := √(v9 x)

theorem v10_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v10 x ∧ v10 x ≤ (2594561620004621 / 1000000000000000000 : ℝ) := by
  have h9 := v9_bounds x hx0 hx1
  unfold v10
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v11 (x : ℝ) : ℝ := (v8 x) + (v10 x)

theorem v11_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (105161185805410163 / 125000000000000000 : ℝ) ≤ v11 x ∧ v11 x ≤ (105485506007910741 / 125000000000000000 : ℝ) := by
  have h8 := v8_bounds x hx0 hx1
  have h10 := v10_bounds x hx0 hx1
  unfold v11
  constructor <;> interval_num

noncomputable def v12 (x : ℝ) : ℝ := (v11 x) ^ 2

theorem v12_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (141553599999999999 / 200000000000000000 : ℝ) ≤ v12 x ∧ v12 x ≤ (178035071643919569 / 250000000000000000 : ℝ) := by
  have h11 := v11_bounds x hx0 hx1
  unfold v12
  constructor <;> interval_num

noncomputable def v13 (x : ℝ) : ℝ := ((1 : ℝ)) - (v12 x)

theorem v13_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (287859713424321723 / 1000000000000000000 : ℝ) ≤ v13 x ∧ v13 x ≤ (146116000000000003 / 500000000000000000 : ℝ) := by
  have h12 := v12_bounds x hx0 hx1
  unfold v13
  constructor <;> interval_num

noncomputable def v14 (x : ℝ) : ℝ := (v0 x) * ((1521 / 500 : ℝ))

theorem v14_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v14 x ∧ v14 x ≤ (380250000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v14
  constructor <;> interval_num

noncomputable def v15 (x : ℝ) : ℝ := (v14 x) * (v0 x)

theorem v15_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v15 x ∧ v15 x ≤ (23765625001 / 500000000000000000 : ℝ) := by
  have h14 := v14_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v15
  constructor <;> interval_num

noncomputable def v16 (x : ℝ) : ℝ := (v0 x) * ((3 : ℝ))

theorem v16_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v16 x ∧ v16 x ≤ (375000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v16
  constructor <;> interval_num

noncomputable def v17 (x : ℝ) : ℝ := ((1 : ℝ)) - (v16 x)

theorem v17_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499812499999999999 / 500000000000000000 : ℝ) ≤ v17 x ∧ v17 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h16 := v16_bounds x hx0 hx1
  unfold v17
  constructor <;> interval_num

noncomputable def v18 (x : ℝ) : ℝ := (v15 x) / (v17 x)

theorem v18_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v18 x ∧ v18 x ≤ (47549080909 / 1000000000000000000 : ℝ) := by
  have h15 := v15_bounds x hx0 hx1
  have h17 := v17_bounds x hx0 hx1
  unfold v18
  constructor <;> interval_num

noncomputable def v19 (x : ℝ) : ℝ := √((1521 / 500 : ℝ))

theorem v19_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (1744133022449835963 / 1000000000000000000 : ℝ) ≤ v19 x ∧ v19 x ≤ (436033255612458991 / 250000000000000000 : ℝ) := by
  unfold v19
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v20 (x : ℝ) : ℝ := (v6 x) * (v19 x)

theorem v20_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v20 x ∧ v20 x ≤ (8257841868763910003 / 1000000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  have h19 := v19_bounds x hx0 hx1
  unfold v20
  constructor <;> interval_num

noncomputable def v21 (x : ℝ) : ℝ := (v20 x) * (v0 x)

theorem v21_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v21 x ∧ v21 x ≤ (103223023359549 / 100000000000000000 : ℝ) := by
  have h20 := v20_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v21
  constructor <;> interval_num

noncomputable def v22 (x : ℝ) : ℝ := (v0 x) * ((25 : ℝ))

theorem v22_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v22 x ∧ v22 x ≤ (3125000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v22
  constructor <;> interval_num

noncomputable def v23 (x : ℝ) : ℝ := ((1 : ℝ)) - (v22 x)

theorem v23_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (498437499999999999 / 500000000000000000 : ℝ) ≤ v23 x ∧ v23 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h22 := v22_bounds x hx0 hx1
  unfold v23
  constructor <;> interval_num

noncomputable def v24 (x : ℝ) : ℝ := √(v23 x)

theorem v24_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (998436277385792907 / 1000000000000000000 : ℝ) ≤ v24 x ∧ v24 x ≤ (1000000000000000001 / 1000000000000000000 : ℝ) := by
  have h23 := v23_bounds x hx0 hx1
  unfold v24
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v25 (x : ℝ) : ℝ := (v21 x) / (v24 x)

theorem v25_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v25 x ∧ v25 x ≤ (64615430209163 / 62500000000000000 : ℝ) := by
  have h21 := v21_bounds x hx0 hx1
  have h24 := v24_bounds x hx0 hx1
  unfold v25
  constructor <;> interval_num

noncomputable def v26 (x : ℝ) : ℝ := (v25 x) * ((7 / 2 : ℝ))

theorem v26_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v26 x ∧ v26 x ≤ (3618464091713129 / 1000000000000000000 : ℝ) := by
  have h25 := v25_bounds x hx0 hx1
  unfold v26
  constructor <;> interval_num

noncomputable def v27 (x : ℝ) : ℝ := (v0 x) * ((12 : ℝ))

theorem v27_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v27 x ∧ v27 x ≤ (1500000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v27
  constructor <;> interval_num

noncomputable def v28 (x : ℝ) : ℝ := √(v27 x)

theorem v28_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v28 x ∧ v28 x ≤ (19364916731037091 / 500000000000000000 : ℝ) := by
  have h27 := v27_bounds x hx0 hx1
  unfold v28
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v29 (x : ℝ) : ℝ := (v28 x) * ((2 : ℝ))

theorem v29_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v29 x ∧ v29 x ≤ (15491933384829673 / 200000000000000000 : ℝ) := by
  have h28 := v28_bounds x hx0 hx1
  unfold v29
  constructor <;> interval_num

noncomputable def v30 (x : ℝ) : ℝ := (v29 x) + ((1 : ℝ))

theorem v30_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (999999999999999999 / 1000000000000000000 : ℝ) ≤ v30 x ∧ v30 x ≤ (538729833462074183 / 500000000000000000 : ℝ) := by
  have h29 := v29_bounds x hx0 hx1
  unfold v30
  constructor <;> interval_num

noncomputable def v31 (x : ℝ) : ℝ := (v0 x) * ((24 : ℝ))

theorem v31_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v31 x ∧ v31 x ≤ (3000000000000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v31
  constructor <;> interval_num

noncomputable def v32 (x : ℝ) : ℝ := (v30 x) + (v31 x)

theorem v32_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (499999999999999999 / 500000000000000000 : ℝ) ≤ v32 x ∧ v32 x ≤ (67528729182759273 / 62500000000000000 : ℝ) := by
  have h30 := v30_bounds x hx0 hx1
  have h31 := v31_bounds x hx0 hx1
  unfold v32
  constructor <;> interval_num

noncomputable def v33 (x : ℝ) : ℝ := √((20171089 / 25000000 : ℝ))

theorem v33_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (28070147204147327 / 31250000000000000 : ℝ) ≤ v33 x ∧ v33 x ≤ (179648942106542893 / 200000000000000000 : ℝ) := by
  unfold v33
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v34 (x : ℝ) : ℝ := √((88471 / 125000 : ℝ))

theorem v34_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (168257897288656261 / 200000000000000000 : ℝ) ≤ v34 x ∧ v34 x ≤ (420644743221640653 / 500000000000000000 : ℝ) := by
  unfold v34
  constructor
  · apply le_sqrt_of_sq_le
    interval_num
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v35 (x : ℝ) : ℝ := (v33 x) - (v34 x)

theorem v35_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (56955224089433157 / 1000000000000000000 : ℝ) ≤ v35 x ∧ v35 x ≤ (56955224089433161 / 1000000000000000000 : ℝ) := by
  have h33 := v33_bounds x hx0 hx1
  have h34 := v34_bounds x hx0 hx1
  unfold v35
  constructor <;> interval_num

noncomputable def v36 (x : ℝ) : ℝ := (v0 x) * ((26927 / 500000 : ℝ))

theorem v36_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v36 x ∧ v36 x ≤ (6731750000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v36
  constructor <;> interval_num

noncomputable def v37 (x : ℝ) : ℝ := √(v36 x)

theorem v37_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v37 x ∧ v37 x ≤ (2594561620004621 / 1000000000000000000 : ℝ) := by
  have h36 := v36_bounds x hx0 hx1
  unfold v37
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v38 (x : ℝ) : ℝ := (v35 x) - (v37 x)

theorem v38_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (10872132493885707 / 200000000000000000 : ℝ) ≤ v38 x ∧ v38 x ≤ (28477612044716581 / 500000000000000000 : ℝ) := by
  have h35 := v35_bounds x hx0 hx1
  have h37 := v37_bounds x hx0 hx1
  unfold v38
  constructor <;> interval_num

noncomputable def v39 (x : ℝ) : ℝ := (v7 x) / ((33 / 5000 : ℝ))

theorem v39_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v39 x ∧ v39 x ≤ (397888011363636517 / 1000000000000000000 : ℝ) := by
  have h7 := v7_bounds x hx0 hx1
  unfold v39
  constructor <;> interval_num

noncomputable def v40 (x : ℝ) : ℝ := (v39 x) ^ 32

theorem v40_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v40 x ∧ v40 x ≤ (155723 / 1000000000000000000 : ℝ) := by
  have h39 := v39_bounds x hx0 hx1
  unfold v40
  constructor <;> interval_num

noncomputable def v41 (x : ℝ) : ℝ := (v0 x) * ((27323 / 250000 : ℝ))

theorem v41_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v41 x ∧ v41 x ≤ (13661500000001 / 1000000000000000000 : ℝ) := by
  have h0 := v0_bounds x hx0 hx1
  unfold v41
  constructor <;> interval_num

noncomputable def v42 (x : ℝ) : ℝ := √(v41 x)

theorem v42_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v42 x ∧ v42 x ≤ (1848073321056351 / 500000000000000000 : ℝ) := by
  have h41 := v41_bounds x hx0 hx1
  unfold v42
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v43 (x : ℝ) : ℝ := (v6 x) * (v42 x)

theorem v43_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v43 x ∧ v43 x ≤ (8749961757921843 / 500000000000000000 : ℝ) := by
  have h6 := v6_bounds x hx0 hx1
  have h42 := v42_bounds x hx0 hx1
  unfold v43
  constructor <;> interval_num

noncomputable def v44 (x : ℝ) : ℝ := (v43 x) / (v38 x)

theorem v44_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v44 x ∧ v44 x ≤ (160961278991819961 / 500000000000000000 : ℝ) := by
  have h43 := v43_bounds x hx0 hx1
  have h38 := v38_bounds x hx0 hx1
  unfold v44
  constructor <;> interval_num

end BstLean.Part293.Envelope
