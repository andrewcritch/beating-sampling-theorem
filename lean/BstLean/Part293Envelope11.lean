import BstLean.Part293Envelope10

namespace BstLean.Part293.Envelope
open Real

noncomputable def v495 (x : ℝ) : ℝ := (v494 x) * (v454 x)

theorem v495_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (39764190826683023 / 500000000000000000 : ℝ) ≤ v495 x ∧ v495 x ≤ (88260589802208223 / 1000000000000000000 : ℝ) := by
  have h494 := v494_bounds x hx0 hx1
  have h454 := v454_bounds x hx0 hx1
  unfold v495
  constructor <;> interval_num

noncomputable def v496 (x : ℝ) : ℝ := (v456 x) + (v495 x)

theorem v496_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (252148012053366043 / 1000000000000000000 : ℝ) ≤ v496 x ∧ v496 x ≤ (268420525042871243 / 1000000000000000000 : ℝ) := by
  have h456 := v456_bounds x hx0 hx1
  have h495 := v495_bounds x hx0 hx1
  unfold v496
  constructor <;> interval_num

noncomputable def v497 (x : ℝ) : ℝ := (v496 x) * (v0 x)

theorem v497_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v497 x ∧ v497 x ≤ (838814140759 / 25000000000000000 : ℝ) := by
  have h496 := v496_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v497
  constructor <;> interval_num

noncomputable def v498 (x : ℝ) : ℝ := (v493 x) * ((1773981 / 10000000 : ℝ))

theorem v498_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (227009558260171 / 250000000000000000 : ℝ) ≤ v498 x ∧ v498 x ≤ (2483573400000001 / 500000000000000000 : ℝ) := by
  have h493 := v493_bounds x hx0 hx1
  unfold v498
  constructor <;> interval_num

noncomputable def v499 (x : ℝ) : ℝ := (v497 x) / (v498 x)

theorem v499_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v499 x ∧ v499 x ≤ (18475304458274227 / 500000000000000000 : ℝ) := by
  have h497 := v497_bounds x hx0 hx1
  have h498 := v498_bounds x hx0 hx1
  unfold v499
  constructor <;> interval_num

noncomputable def v500 (x : ℝ) : ℝ := (v499 x) ^ 6

theorem v500_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v500 x ∧ v500 x ≤ (2545245029 / 1000000000000000000 : ℝ) := by
  have h499 := v499_bounds x hx0 hx1
  unfold v500
  constructor <;> interval_num

noncomputable def v501 (x : ℝ) : ℝ := (v454 x) ^ 2

theorem v501_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (2234052503222611 / 1000000000000000000 : ℝ) ≤ v501 x ∧ v501 x ≤ (2624702511134001 / 1000000000000000000 : ℝ) := by
  have h454 := v454_bounds x hx0 hx1
  unfold v501
  constructor <;> interval_num

noncomputable def v502 (x : ℝ) : ℝ := (v501 x) * (v0 x)

theorem v502_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v502 x ∧ v502 x ≤ (328087813893 / 1000000000000000000 : ℝ) := by
  have h501 := v501_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v502
  constructor <;> interval_num

noncomputable def v503 (x : ℝ) : ℝ := (v502 x) * (v0 x)

theorem v503_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v503 x ∧ v503 x ≤ (20505489 / 500000000000000000 : ℝ) := by
  have h502 := v502_bounds x hx0 hx1
  have h0 := v0_bounds x hx0 hx1
  unfold v503
  constructor <;> interval_num

noncomputable def v504 (x : ℝ) : ℝ := (v493 x) * ((17919 / 10000000 : ℝ))

theorem v504_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (4586051682023 / 500000000000000000 : ℝ) ≤ v504 x ∧ v504 x ≤ (25086600000001 / 500000000000000000 : ℝ) := by
  have h493 := v493_bounds x hx0 hx1
  unfold v504
  constructor <;> interval_num

noncomputable def v505 (x : ℝ) : ℝ := (v503 x) / (v504 x)

theorem v505_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v505 x ∧ v505 x ≤ (1117818246597 / 250000000000000000 : ℝ) := by
  have h503 := v503_bounds x hx0 hx1
  have h504 := v504_bounds x hx0 hx1
  unfold v505
  constructor <;> interval_num

noncomputable def v506 (x : ℝ) : ℝ := (v505 x) ^ 4

theorem v506_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v506 x ∧ v506 x ≤ (1 / 500000000000000000 : ℝ) := by
  have h505 := v505_bounds x hx0 hx1
  unfold v506
  constructor <;> interval_num

noncomputable def v507 (x : ℝ) : ℝ := (v500 x) + (v506 x)

theorem v507_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v507 x ∧ v507 x ≤ (318155629 / 125000000000000000 : ℝ) := by
  have h500 := v500_bounds x hx0 hx1
  have h506 := v506_bounds x hx0 hx1
  unfold v507
  constructor <;> interval_num

noncomputable def v508 (x : ℝ) : ℝ := (v507 x) * ((2 : ℝ))

theorem v508_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v508 x ∧ v508 x ≤ (1018098013 / 200000000000000000 : ℝ) := by
  have h507 := v507_bounds x hx0 hx1
  unfold v508
  constructor <;> interval_num

noncomputable def v509 (x : ℝ) : ℝ := (v485 x) + (v508 x)

theorem v509_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v509 x ∧ v509 x ≤ (4088952580349 / 250000000000000000 : ℝ) := by
  have h485 := v485_bounds x hx0 hx1
  have h508 := v508_bounds x hx0 hx1
  unfold v509
  constructor <;> interval_num

noncomputable def v510 (x : ℝ) : ℝ := √(v509 x)

theorem v510_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (0 : ℝ) ≤ v510 x ∧ v510 x ≤ (4044231734383677 / 1000000000000000000 : ℝ) := by
  have h509 := v509_bounds x hx0 hx1
  unfold v510
  constructor
  · exact sqrt_nonneg _
  · apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · interval_num

noncomputable def v511 (x : ℝ) : ℝ := (v49 x) + (v368 x)

theorem v511_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (442130122249 / 50000000000000000 : ℝ) ≤ v511 x ∧ v511 x ≤ (979997782176937 / 500000000000000000 : ℝ) := by
  have h49 := v49_bounds x hx0 hx1
  have h368 := v368_bounds x hx0 hx1
  unfold v511
  constructor <;> interval_num

noncomputable def v512 (x : ℝ) : ℝ := (v511 x) + (v384 x)

theorem v512_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (8842602444979 / 1000000000000000000 : ℝ) ≤ v512 x ∧ v512 x ≤ (289903934698299 / 125000000000000000 : ℝ) := by
  have h511 := v511_bounds x hx0 hx1
  have h384 := v384_bounds x hx0 hx1
  unfold v512
  constructor <;> interval_num

noncomputable def v513 (x : ℝ) : ℝ := (v512 x) + (v510 x)

theorem v513_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (4421301222489 / 500000000000000000 : ℝ) ≤ v513 x ∧ v513 x ≤ (636346321197007 / 100000000000000000 : ℝ) := by
  have h512 := v512_bounds x hx0 hx1
  have h510 := v510_bounds x hx0 hx1
  unfold v513
  constructor <;> interval_num

noncomputable def v514 (x : ℝ) : ℝ := (v513 x) + ((1 / 50000000 : ℝ))

theorem v514_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (8862602444977 / 1000000000000000000 : ℝ) ≤ v514 x ∧ v514 x ≤ (6363483211970071 / 1000000000000000000 : ℝ) := by
  have h513 := v513_bounds x hx0 hx1
  unfold v514
  constructor <;> interval_num

noncomputable def v515 (x : ℝ) : ℝ := (v514 x) + ((1 / 100000000000000000000 : ℝ))

theorem v515_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8000) :
    (553912652811 / 62500000000000000 : ℝ) ≤ v515 x ∧ v515 x ≤ (6363483211970073 / 1000000000000000000 : ℝ) := by
  have h514 := v514_bounds x hx0 hx1
  unfold v515
  constructor <;> interval_num

end BstLean.Part293.Envelope
