import BstLean.Part293EndpointInterface

namespace BstLean.Part293.Coarse
open Real BstLean.Part232 BstLean.Part236

noncomputable def radiusBoundary : ℕ → ℝ
  | 0 => (0 / 1 : ℝ)
  | 1 => (2187 / 12800000 : ℝ)
  | 2 => (6561 / 25600000 : ℝ)
  | 3 => (19683 / 51200000 : ℝ)
  | 4 => (59049 / 102400000 : ℝ)
  | 5 => (177147 / 204800000 : ℝ)
  | 6 => (1594323 / 819200000 : ℝ)
  | 7 => (14348907 / 3276800000 : ℝ)
  | 8 => (43046721 / 6553600000 : ℝ)
  | 9 => (105401599641 / 10000000000000 : ℝ)
  | _ => 0

noncomputable def frameBoundary : ℕ → ℝ
  | 0 => (0 / 1 : ℝ)
  | 1 => (12977 / 409600 : ℝ)
  | 2 => (1051137 / 10240000 : ℝ)
  | 3 => (2193113 / 10240000 : ℝ)
  | 4 => (12977 / 40000 : ℝ)
  | _ => 0

noncomputable def radiusCover : RadiusCover where
  K := 9
  positive := by norm_num
  h := radiusBoundary
  zero := by norm_num [radiusBoundary]
  increasing := by
    intro i hi
    interval_cases i <;> norm_num [radiusBoundary]

noncomputable def frameCover : FrameCover where
  K := 4
  positive := by norm_num
  h := frameBoundary
  zero := by norm_num [frameBoundary]
  increasing := by
    intro i hi
    interval_cases i <;> norm_num [frameBoundary]
  maximum := frameMaximum
  last := by norm_num [frameBoundary, frameMaximum]

theorem terminal_payment :
    1 ≤ endpointIntercept + radiusPrice * radiusCover.h radiusCover.K ^ 2 := by
  norm_num [endpointIntercept, radiusPrice, radiusCover, radiusBoundary]

end BstLean.Part293.Coarse
