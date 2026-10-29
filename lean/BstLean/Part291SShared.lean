import BstLean.Part291SBridge
import BstLean.Part291CoarseSBatch0
import BstLean.Part291CoarseSBatch1
import BstLean.Part291CoarseSBatch2
import BstLean.Part291CoarseSBatch3
import BstLean.Part291CoarseSBatch4
import BstLean.Part291CoarseSBatch5

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255 BstLean.Part264b

theorem lowNormalizedSCore {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0.38 0.63 c) :
    LowSBounds x c 0.2 := by
  obtain ⟨j, hj⟩ := unit_interval_cover 24
    (x := (c - 0.38) * 100) (by constructor <;> norm_num <;> linarith [hc.1,hc.2])
  match j with
  | ⟨0, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS8 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨1, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS9 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨2, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS10 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨3, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS11 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨4, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS12 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨5, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS13 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨6, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS14 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨7, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS15 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨8, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS16 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨9, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS17 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨10, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS18 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨11, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS19 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨12, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS20 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨13, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS21 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨14, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS22 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨15, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS23 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨16, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS24 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨17, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS25 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨18, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS26 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨19, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS27 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨20, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS28 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨21, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS29 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨22, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS30 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨23, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS31 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨24, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS32 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨j + 25, h⟩ => omega

theorem lowNormalizedSWide {x c : ℝ} (hx : B 0 (1/8000) x) (hc : B 0.3 0.74 c) :
    LowSBounds x c 0.36 := by
  obtain ⟨j, hj⟩ := unit_interval_cover 43
    (x := (c - 0.3) * 100) (by constructor <;> norm_num <;> linarith [hc.1,hc.2])
  match j with
  | ⟨0, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS0 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨1, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS1 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨2, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS2 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨3, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS3 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨4, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS4 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨5, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS5 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨6, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS6 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨7, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS7 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨8, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS8 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨9, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS9 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨10, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS10 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨11, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS11 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨12, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS12 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨13, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS13 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨14, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS14 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨15, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS15 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨16, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS16 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨17, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS17 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨18, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS18 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨19, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS19 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨20, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS20 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨21, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS21 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨22, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS22 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨23, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS23 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨24, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS24 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨25, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS25 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨26, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS26 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨27, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS27 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨28, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS28 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨29, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS29 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨30, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS30 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨31, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS31 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨32, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.2 : ℝ))
      · convert lowCoarseS32 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨33, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS33 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨34, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS34 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨35, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS35 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨36, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS36 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨37, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS37 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨38, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS38 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨39, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS39 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨40, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS40 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨41, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS41 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨42, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS42 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨43, h⟩ =>
      apply LowSBounds.mono (x := x) (c := c) (a := (0.36 : ℝ))
      · convert lowCoarseS43 (c := c) hx (by constructor <;> norm_num at hj ⊢ <;> linarith [hj.1,hj.2]) using 1 <;> norm_num [LowSBounds]
      · norm_num
  | ⟨j + 44, h⟩ => omega

end BstLean.BlueprintLow
