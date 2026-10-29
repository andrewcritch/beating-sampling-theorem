import BstLean.Part271R3Rows13225
import BstLean.Part271R3Rows14885
import BstLean.Part271R3Rows15280
import BstLean.Part271R3Rows16130
import BstLean.Part271R3Rows13226
import BstLean.Part271R3Rows13301
import BstLean.Part271R3Rows13376
import BstLean.Part271R3Rows13451
import BstLean.Part271R3Rows13456
import BstLean.Part271R3Rows13457
import BstLean.Part271R3Rows13532
import BstLean.Part271R3Rows13607
import BstLean.Part271R3Rows13682
import BstLean.Part271R3Rows13689
import BstLean.Part271R3Rows13690
import BstLean.Part271R3Rows13765
import BstLean.Part271R3Rows13840
import BstLean.Part271R3Rows13915
import BstLean.Part271R3Rows13924
import BstLean.Part271R3Rows13925
import BstLean.Part271R3Rows14000
import BstLean.Part271R3Rows14075
import BstLean.Part271R3Rows14150
import BstLean.Part271R3Rows14161
import BstLean.Part271R3Rows14162
import BstLean.Part271R3Rows14237
import BstLean.Part271R3Rows14312
import BstLean.Part271R3Rows14387
import BstLean.Part271R3Rows14400
import BstLean.Part271R3Rows14401
import BstLean.Part271R3Rows14476
import BstLean.Part271R3Rows14551
import BstLean.Part271R3Rows14626
import BstLean.Part271R3Rows14641
import BstLean.Part271R3Rows14642
import BstLean.Part271R3Rows14717
import BstLean.Part271R3Rows14792
import BstLean.Part271R3Rows14867
import BstLean.Part271R3Rows14884
import BstLean.Part271R3Rows14960
import BstLean.Part271R3Rows15035
import BstLean.Part271R3Rows15110
import BstLean.Part271R3Rows15129
import BstLean.Part271R3Rows15130
import BstLean.Part271R3Rows15205
import BstLean.Part271R3Rows15355
import BstLean.Part271R3Rows15376
import BstLean.Part271R3Rows15377
import BstLean.Part271R3Rows15452
import BstLean.Part271R3Rows15527
import BstLean.Part271R3Rows15602
import BstLean.Part271R3Rows15625
import BstLean.Part271R3Rows15626
import BstLean.Part271R3Rows15701
import BstLean.Part271R3Rows15776
import BstLean.Part271R3Rows15851
import BstLean.Part271R3Rows15876
import BstLean.Part271R3Rows15877
import BstLean.Part271R3Rows15952
import BstLean.Part271R3Rows16027
import BstLean.Part271R3Rows16102
import BstLean.Part271R3Rows16129

namespace BstLean.Part271.R3.Family
noncomputable def band13226_13375 (n : ℕ) : Allowances :=
  if n ≤ 13300 then Rows13226.record n else Rows13301.record n

noncomputable def band13226_13375_arithmetic (n : ℕ) (ha : 13226 ≤ n) (hb : n ≤ 13375) :
    RowArithmetic n (band13226_13375 n).hidden (band13226_13375 n).frame (band13226_13375 n).moment := by
  unfold band13226_13375
  split_ifs with h
  · exact Rows13226.arithmetic n ha h
  · exact Rows13301.arithmetic n (by omega) hb

noncomputable def band13225_13375 (n : ℕ) : Allowances :=
  if n ≤ 13225 then Rows13225.record n else band13226_13375 n

noncomputable def band13225_13375_arithmetic (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 13375) :
    RowArithmetic n (band13225_13375 n).hidden (band13225_13375 n).frame (band13225_13375 n).moment := by
  unfold band13225_13375
  split_ifs with h
  · exact Rows13225.arithmetic n ha h
  · exact band13226_13375_arithmetic n (by omega) hb

noncomputable def band13376_13455 (n : ℕ) : Allowances :=
  if n ≤ 13450 then Rows13376.record n else Rows13451.record n

noncomputable def band13376_13455_arithmetic (n : ℕ) (ha : 13376 ≤ n) (hb : n ≤ 13455) :
    RowArithmetic n (band13376_13455 n).hidden (band13376_13455 n).frame (band13376_13455 n).moment := by
  unfold band13376_13455
  split_ifs with h
  · exact Rows13376.arithmetic n ha h
  · exact Rows13451.arithmetic n (by omega) hb

noncomputable def band13456_13531 (n : ℕ) : Allowances :=
  if n ≤ 13456 then Rows13456.record n else Rows13457.record n

noncomputable def band13456_13531_arithmetic (n : ℕ) (ha : 13456 ≤ n) (hb : n ≤ 13531) :
    RowArithmetic n (band13456_13531 n).hidden (band13456_13531 n).frame (band13456_13531 n).moment := by
  unfold band13456_13531
  split_ifs with h
  · exact Rows13456.arithmetic n ha h
  · exact Rows13457.arithmetic n (by omega) hb

noncomputable def band13376_13531 (n : ℕ) : Allowances :=
  if n ≤ 13455 then band13376_13455 n else band13456_13531 n

noncomputable def band13376_13531_arithmetic (n : ℕ) (ha : 13376 ≤ n) (hb : n ≤ 13531) :
    RowArithmetic n (band13376_13531 n).hidden (band13376_13531 n).frame (band13376_13531 n).moment := by
  unfold band13376_13531
  split_ifs with h
  · exact band13376_13455_arithmetic n ha h
  · exact band13456_13531_arithmetic n (by omega) hb

noncomputable def band13225_13531 (n : ℕ) : Allowances :=
  if n ≤ 13375 then band13225_13375 n else band13376_13531 n

noncomputable def band13225_13531_arithmetic (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 13531) :
    RowArithmetic n (band13225_13531 n).hidden (band13225_13531 n).frame (band13225_13531 n).moment := by
  unfold band13225_13531
  split_ifs with h
  · exact band13225_13375_arithmetic n ha h
  · exact band13376_13531_arithmetic n (by omega) hb

noncomputable def band13532_13681 (n : ℕ) : Allowances :=
  if n ≤ 13606 then Rows13532.record n else Rows13607.record n

noncomputable def band13532_13681_arithmetic (n : ℕ) (ha : 13532 ≤ n) (hb : n ≤ 13681) :
    RowArithmetic n (band13532_13681 n).hidden (band13532_13681 n).frame (band13532_13681 n).moment := by
  unfold band13532_13681
  split_ifs with h
  · exact Rows13532.arithmetic n ha h
  · exact Rows13607.arithmetic n (by omega) hb

noncomputable def band13682_13689 (n : ℕ) : Allowances :=
  if n ≤ 13688 then Rows13682.record n else Rows13689.record n

noncomputable def band13682_13689_arithmetic (n : ℕ) (ha : 13682 ≤ n) (hb : n ≤ 13689) :
    RowArithmetic n (band13682_13689 n).hidden (band13682_13689 n).frame (band13682_13689 n).moment := by
  unfold band13682_13689
  split_ifs with h
  · exact Rows13682.arithmetic n ha h
  · exact Rows13689.arithmetic n (by omega) hb

noncomputable def band13532_13689 (n : ℕ) : Allowances :=
  if n ≤ 13681 then band13532_13681 n else band13682_13689 n

noncomputable def band13532_13689_arithmetic (n : ℕ) (ha : 13532 ≤ n) (hb : n ≤ 13689) :
    RowArithmetic n (band13532_13689 n).hidden (band13532_13689 n).frame (band13532_13689 n).moment := by
  unfold band13532_13689
  split_ifs with h
  · exact band13532_13681_arithmetic n ha h
  · exact band13682_13689_arithmetic n (by omega) hb

noncomputable def band13690_13839 (n : ℕ) : Allowances :=
  if n ≤ 13764 then Rows13690.record n else Rows13765.record n

noncomputable def band13690_13839_arithmetic (n : ℕ) (ha : 13690 ≤ n) (hb : n ≤ 13839) :
    RowArithmetic n (band13690_13839 n).hidden (band13690_13839 n).frame (band13690_13839 n).moment := by
  unfold band13690_13839
  split_ifs with h
  · exact Rows13690.arithmetic n ha h
  · exact Rows13765.arithmetic n (by omega) hb

noncomputable def band13840_13923 (n : ℕ) : Allowances :=
  if n ≤ 13914 then Rows13840.record n else Rows13915.record n

noncomputable def band13840_13923_arithmetic (n : ℕ) (ha : 13840 ≤ n) (hb : n ≤ 13923) :
    RowArithmetic n (band13840_13923 n).hidden (band13840_13923 n).frame (band13840_13923 n).moment := by
  unfold band13840_13923
  split_ifs with h
  · exact Rows13840.arithmetic n ha h
  · exact Rows13915.arithmetic n (by omega) hb

noncomputable def band13690_13923 (n : ℕ) : Allowances :=
  if n ≤ 13839 then band13690_13839 n else band13840_13923 n

noncomputable def band13690_13923_arithmetic (n : ℕ) (ha : 13690 ≤ n) (hb : n ≤ 13923) :
    RowArithmetic n (band13690_13923 n).hidden (band13690_13923 n).frame (band13690_13923 n).moment := by
  unfold band13690_13923
  split_ifs with h
  · exact band13690_13839_arithmetic n ha h
  · exact band13840_13923_arithmetic n (by omega) hb

noncomputable def band13532_13923 (n : ℕ) : Allowances :=
  if n ≤ 13689 then band13532_13689 n else band13690_13923 n

noncomputable def band13532_13923_arithmetic (n : ℕ) (ha : 13532 ≤ n) (hb : n ≤ 13923) :
    RowArithmetic n (band13532_13923 n).hidden (band13532_13923 n).frame (band13532_13923 n).moment := by
  unfold band13532_13923
  split_ifs with h
  · exact band13532_13689_arithmetic n ha h
  · exact band13690_13923_arithmetic n (by omega) hb

noncomputable def band13225_13923 (n : ℕ) : Allowances :=
  if n ≤ 13531 then band13225_13531 n else band13532_13923 n

noncomputable def band13225_13923_arithmetic (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 13923) :
    RowArithmetic n (band13225_13923 n).hidden (band13225_13923 n).frame (band13225_13923 n).moment := by
  unfold band13225_13923
  split_ifs with h
  · exact band13225_13531_arithmetic n ha h
  · exact band13532_13923_arithmetic n (by omega) hb

noncomputable def band13924_13999 (n : ℕ) : Allowances :=
  if n ≤ 13924 then Rows13924.record n else Rows13925.record n

noncomputable def band13924_13999_arithmetic (n : ℕ) (ha : 13924 ≤ n) (hb : n ≤ 13999) :
    RowArithmetic n (band13924_13999 n).hidden (band13924_13999 n).frame (band13924_13999 n).moment := by
  unfold band13924_13999
  split_ifs with h
  · exact Rows13924.arithmetic n ha h
  · exact Rows13925.arithmetic n (by omega) hb

noncomputable def band14000_14149 (n : ℕ) : Allowances :=
  if n ≤ 14074 then Rows14000.record n else Rows14075.record n

noncomputable def band14000_14149_arithmetic (n : ℕ) (ha : 14000 ≤ n) (hb : n ≤ 14149) :
    RowArithmetic n (band14000_14149 n).hidden (band14000_14149 n).frame (band14000_14149 n).moment := by
  unfold band14000_14149
  split_ifs with h
  · exact Rows14000.arithmetic n ha h
  · exact Rows14075.arithmetic n (by omega) hb

noncomputable def band13924_14149 (n : ℕ) : Allowances :=
  if n ≤ 13999 then band13924_13999 n else band14000_14149 n

noncomputable def band13924_14149_arithmetic (n : ℕ) (ha : 13924 ≤ n) (hb : n ≤ 14149) :
    RowArithmetic n (band13924_14149 n).hidden (band13924_14149 n).frame (band13924_14149 n).moment := by
  unfold band13924_14149
  split_ifs with h
  · exact band13924_13999_arithmetic n ha h
  · exact band14000_14149_arithmetic n (by omega) hb

noncomputable def band14150_14161 (n : ℕ) : Allowances :=
  if n ≤ 14160 then Rows14150.record n else Rows14161.record n

noncomputable def band14150_14161_arithmetic (n : ℕ) (ha : 14150 ≤ n) (hb : n ≤ 14161) :
    RowArithmetic n (band14150_14161 n).hidden (band14150_14161 n).frame (band14150_14161 n).moment := by
  unfold band14150_14161
  split_ifs with h
  · exact Rows14150.arithmetic n ha h
  · exact Rows14161.arithmetic n (by omega) hb

noncomputable def band14162_14311 (n : ℕ) : Allowances :=
  if n ≤ 14236 then Rows14162.record n else Rows14237.record n

noncomputable def band14162_14311_arithmetic (n : ℕ) (ha : 14162 ≤ n) (hb : n ≤ 14311) :
    RowArithmetic n (band14162_14311 n).hidden (band14162_14311 n).frame (band14162_14311 n).moment := by
  unfold band14162_14311
  split_ifs with h
  · exact Rows14162.arithmetic n ha h
  · exact Rows14237.arithmetic n (by omega) hb

noncomputable def band14150_14311 (n : ℕ) : Allowances :=
  if n ≤ 14161 then band14150_14161 n else band14162_14311 n

noncomputable def band14150_14311_arithmetic (n : ℕ) (ha : 14150 ≤ n) (hb : n ≤ 14311) :
    RowArithmetic n (band14150_14311 n).hidden (band14150_14311 n).frame (band14150_14311 n).moment := by
  unfold band14150_14311
  split_ifs with h
  · exact band14150_14161_arithmetic n ha h
  · exact band14162_14311_arithmetic n (by omega) hb

noncomputable def band13924_14311 (n : ℕ) : Allowances :=
  if n ≤ 14149 then band13924_14149 n else band14150_14311 n

noncomputable def band13924_14311_arithmetic (n : ℕ) (ha : 13924 ≤ n) (hb : n ≤ 14311) :
    RowArithmetic n (band13924_14311 n).hidden (band13924_14311 n).frame (band13924_14311 n).moment := by
  unfold band13924_14311
  split_ifs with h
  · exact band13924_14149_arithmetic n ha h
  · exact band14150_14311_arithmetic n (by omega) hb

noncomputable def band14312_14399 (n : ℕ) : Allowances :=
  if n ≤ 14386 then Rows14312.record n else Rows14387.record n

noncomputable def band14312_14399_arithmetic (n : ℕ) (ha : 14312 ≤ n) (hb : n ≤ 14399) :
    RowArithmetic n (band14312_14399 n).hidden (band14312_14399 n).frame (band14312_14399 n).moment := by
  unfold band14312_14399
  split_ifs with h
  · exact Rows14312.arithmetic n ha h
  · exact Rows14387.arithmetic n (by omega) hb

noncomputable def band14400_14475 (n : ℕ) : Allowances :=
  if n ≤ 14400 then Rows14400.record n else Rows14401.record n

noncomputable def band14400_14475_arithmetic (n : ℕ) (ha : 14400 ≤ n) (hb : n ≤ 14475) :
    RowArithmetic n (band14400_14475 n).hidden (band14400_14475 n).frame (band14400_14475 n).moment := by
  unfold band14400_14475
  split_ifs with h
  · exact Rows14400.arithmetic n ha h
  · exact Rows14401.arithmetic n (by omega) hb

noncomputable def band14312_14475 (n : ℕ) : Allowances :=
  if n ≤ 14399 then band14312_14399 n else band14400_14475 n

noncomputable def band14312_14475_arithmetic (n : ℕ) (ha : 14312 ≤ n) (hb : n ≤ 14475) :
    RowArithmetic n (band14312_14475 n).hidden (band14312_14475 n).frame (band14312_14475 n).moment := by
  unfold band14312_14475
  split_ifs with h
  · exact band14312_14399_arithmetic n ha h
  · exact band14400_14475_arithmetic n (by omega) hb

noncomputable def band14476_14625 (n : ℕ) : Allowances :=
  if n ≤ 14550 then Rows14476.record n else Rows14551.record n

noncomputable def band14476_14625_arithmetic (n : ℕ) (ha : 14476 ≤ n) (hb : n ≤ 14625) :
    RowArithmetic n (band14476_14625 n).hidden (band14476_14625 n).frame (band14476_14625 n).moment := by
  unfold band14476_14625
  split_ifs with h
  · exact Rows14476.arithmetic n ha h
  · exact Rows14551.arithmetic n (by omega) hb

noncomputable def band14626_14641 (n : ℕ) : Allowances :=
  if n ≤ 14640 then Rows14626.record n else Rows14641.record n

noncomputable def band14626_14641_arithmetic (n : ℕ) (ha : 14626 ≤ n) (hb : n ≤ 14641) :
    RowArithmetic n (band14626_14641 n).hidden (band14626_14641 n).frame (band14626_14641 n).moment := by
  unfold band14626_14641
  split_ifs with h
  · exact Rows14626.arithmetic n ha h
  · exact Rows14641.arithmetic n (by omega) hb

noncomputable def band14476_14641 (n : ℕ) : Allowances :=
  if n ≤ 14625 then band14476_14625 n else band14626_14641 n

noncomputable def band14476_14641_arithmetic (n : ℕ) (ha : 14476 ≤ n) (hb : n ≤ 14641) :
    RowArithmetic n (band14476_14641 n).hidden (band14476_14641 n).frame (band14476_14641 n).moment := by
  unfold band14476_14641
  split_ifs with h
  · exact band14476_14625_arithmetic n ha h
  · exact band14626_14641_arithmetic n (by omega) hb

noncomputable def band14312_14641 (n : ℕ) : Allowances :=
  if n ≤ 14475 then band14312_14475 n else band14476_14641 n

noncomputable def band14312_14641_arithmetic (n : ℕ) (ha : 14312 ≤ n) (hb : n ≤ 14641) :
    RowArithmetic n (band14312_14641 n).hidden (band14312_14641 n).frame (band14312_14641 n).moment := by
  unfold band14312_14641
  split_ifs with h
  · exact band14312_14475_arithmetic n ha h
  · exact band14476_14641_arithmetic n (by omega) hb

noncomputable def band13924_14641 (n : ℕ) : Allowances :=
  if n ≤ 14311 then band13924_14311 n else band14312_14641 n

noncomputable def band13924_14641_arithmetic (n : ℕ) (ha : 13924 ≤ n) (hb : n ≤ 14641) :
    RowArithmetic n (band13924_14641 n).hidden (band13924_14641 n).frame (band13924_14641 n).moment := by
  unfold band13924_14641
  split_ifs with h
  · exact band13924_14311_arithmetic n ha h
  · exact band14312_14641_arithmetic n (by omega) hb

noncomputable def band13225_14641 (n : ℕ) : Allowances :=
  if n ≤ 13923 then band13225_13923 n else band13924_14641 n

noncomputable def band13225_14641_arithmetic (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 14641) :
    RowArithmetic n (band13225_14641 n).hidden (band13225_14641 n).frame (band13225_14641 n).moment := by
  unfold band13225_14641
  split_ifs with h
  · exact band13225_13923_arithmetic n ha h
  · exact band13924_14641_arithmetic n (by omega) hb

noncomputable def band14717_14866 (n : ℕ) : Allowances :=
  if n ≤ 14791 then Rows14717.record n else Rows14792.record n

noncomputable def band14717_14866_arithmetic (n : ℕ) (ha : 14717 ≤ n) (hb : n ≤ 14866) :
    RowArithmetic n (band14717_14866 n).hidden (band14717_14866 n).frame (band14717_14866 n).moment := by
  unfold band14717_14866
  split_ifs with h
  · exact Rows14717.arithmetic n ha h
  · exact Rows14792.arithmetic n (by omega) hb

noncomputable def band14642_14866 (n : ℕ) : Allowances :=
  if n ≤ 14716 then Rows14642.record n else band14717_14866 n

noncomputable def band14642_14866_arithmetic (n : ℕ) (ha : 14642 ≤ n) (hb : n ≤ 14866) :
    RowArithmetic n (band14642_14866 n).hidden (band14642_14866 n).frame (band14642_14866 n).moment := by
  unfold band14642_14866
  split_ifs with h
  · exact Rows14642.arithmetic n ha h
  · exact band14717_14866_arithmetic n (by omega) hb

noncomputable def band14867_14884 (n : ℕ) : Allowances :=
  if n ≤ 14883 then Rows14867.record n else Rows14884.record n

noncomputable def band14867_14884_arithmetic (n : ℕ) (ha : 14867 ≤ n) (hb : n ≤ 14884) :
    RowArithmetic n (band14867_14884 n).hidden (band14867_14884 n).frame (band14867_14884 n).moment := by
  unfold band14867_14884
  split_ifs with h
  · exact Rows14867.arithmetic n ha h
  · exact Rows14884.arithmetic n (by omega) hb

noncomputable def band14885_15034 (n : ℕ) : Allowances :=
  if n ≤ 14959 then Rows14885.record n else Rows14960.record n

noncomputable def band14885_15034_arithmetic (n : ℕ) (ha : 14885 ≤ n) (hb : n ≤ 15034) :
    RowArithmetic n (band14885_15034 n).hidden (band14885_15034 n).frame (band14885_15034 n).moment := by
  unfold band14885_15034
  split_ifs with h
  · exact Rows14885.arithmetic n ha h
  · exact Rows14960.arithmetic n (by omega) hb

noncomputable def band14867_15034 (n : ℕ) : Allowances :=
  if n ≤ 14884 then band14867_14884 n else band14885_15034 n

noncomputable def band14867_15034_arithmetic (n : ℕ) (ha : 14867 ≤ n) (hb : n ≤ 15034) :
    RowArithmetic n (band14867_15034 n).hidden (band14867_15034 n).frame (band14867_15034 n).moment := by
  unfold band14867_15034
  split_ifs with h
  · exact band14867_14884_arithmetic n ha h
  · exact band14885_15034_arithmetic n (by omega) hb

noncomputable def band14642_15034 (n : ℕ) : Allowances :=
  if n ≤ 14866 then band14642_14866 n else band14867_15034 n

noncomputable def band14642_15034_arithmetic (n : ℕ) (ha : 14642 ≤ n) (hb : n ≤ 15034) :
    RowArithmetic n (band14642_15034 n).hidden (band14642_15034 n).frame (band14642_15034 n).moment := by
  unfold band14642_15034
  split_ifs with h
  · exact band14642_14866_arithmetic n ha h
  · exact band14867_15034_arithmetic n (by omega) hb

noncomputable def band15035_15128 (n : ℕ) : Allowances :=
  if n ≤ 15109 then Rows15035.record n else Rows15110.record n

noncomputable def band15035_15128_arithmetic (n : ℕ) (ha : 15035 ≤ n) (hb : n ≤ 15128) :
    RowArithmetic n (band15035_15128 n).hidden (band15035_15128 n).frame (band15035_15128 n).moment := by
  unfold band15035_15128
  split_ifs with h
  · exact Rows15035.arithmetic n ha h
  · exact Rows15110.arithmetic n (by omega) hb

noncomputable def band15129_15204 (n : ℕ) : Allowances :=
  if n ≤ 15129 then Rows15129.record n else Rows15130.record n

noncomputable def band15129_15204_arithmetic (n : ℕ) (ha : 15129 ≤ n) (hb : n ≤ 15204) :
    RowArithmetic n (band15129_15204 n).hidden (band15129_15204 n).frame (band15129_15204 n).moment := by
  unfold band15129_15204
  split_ifs with h
  · exact Rows15129.arithmetic n ha h
  · exact Rows15130.arithmetic n (by omega) hb

noncomputable def band15035_15204 (n : ℕ) : Allowances :=
  if n ≤ 15128 then band15035_15128 n else band15129_15204 n

noncomputable def band15035_15204_arithmetic (n : ℕ) (ha : 15035 ≤ n) (hb : n ≤ 15204) :
    RowArithmetic n (band15035_15204 n).hidden (band15035_15204 n).frame (band15035_15204 n).moment := by
  unfold band15035_15204
  split_ifs with h
  · exact band15035_15128_arithmetic n ha h
  · exact band15129_15204_arithmetic n (by omega) hb

noncomputable def band15205_15354 (n : ℕ) : Allowances :=
  if n ≤ 15279 then Rows15205.record n else Rows15280.record n

noncomputable def band15205_15354_arithmetic (n : ℕ) (ha : 15205 ≤ n) (hb : n ≤ 15354) :
    RowArithmetic n (band15205_15354 n).hidden (band15205_15354 n).frame (band15205_15354 n).moment := by
  unfold band15205_15354
  split_ifs with h
  · exact Rows15205.arithmetic n ha h
  · exact Rows15280.arithmetic n (by omega) hb

noncomputable def band15355_15376 (n : ℕ) : Allowances :=
  if n ≤ 15375 then Rows15355.record n else Rows15376.record n

noncomputable def band15355_15376_arithmetic (n : ℕ) (ha : 15355 ≤ n) (hb : n ≤ 15376) :
    RowArithmetic n (band15355_15376 n).hidden (band15355_15376 n).frame (band15355_15376 n).moment := by
  unfold band15355_15376
  split_ifs with h
  · exact Rows15355.arithmetic n ha h
  · exact Rows15376.arithmetic n (by omega) hb

noncomputable def band15205_15376 (n : ℕ) : Allowances :=
  if n ≤ 15354 then band15205_15354 n else band15355_15376 n

noncomputable def band15205_15376_arithmetic (n : ℕ) (ha : 15205 ≤ n) (hb : n ≤ 15376) :
    RowArithmetic n (band15205_15376 n).hidden (band15205_15376 n).frame (band15205_15376 n).moment := by
  unfold band15205_15376
  split_ifs with h
  · exact band15205_15354_arithmetic n ha h
  · exact band15355_15376_arithmetic n (by omega) hb

noncomputable def band15035_15376 (n : ℕ) : Allowances :=
  if n ≤ 15204 then band15035_15204 n else band15205_15376 n

noncomputable def band15035_15376_arithmetic (n : ℕ) (ha : 15035 ≤ n) (hb : n ≤ 15376) :
    RowArithmetic n (band15035_15376 n).hidden (band15035_15376 n).frame (band15035_15376 n).moment := by
  unfold band15035_15376
  split_ifs with h
  · exact band15035_15204_arithmetic n ha h
  · exact band15205_15376_arithmetic n (by omega) hb

noncomputable def band14642_15376 (n : ℕ) : Allowances :=
  if n ≤ 15034 then band14642_15034 n else band15035_15376 n

noncomputable def band14642_15376_arithmetic (n : ℕ) (ha : 14642 ≤ n) (hb : n ≤ 15376) :
    RowArithmetic n (band14642_15376 n).hidden (band14642_15376 n).frame (band14642_15376 n).moment := by
  unfold band14642_15376
  split_ifs with h
  · exact band14642_15034_arithmetic n ha h
  · exact band15035_15376_arithmetic n (by omega) hb

noncomputable def band15377_15526 (n : ℕ) : Allowances :=
  if n ≤ 15451 then Rows15377.record n else Rows15452.record n

noncomputable def band15377_15526_arithmetic (n : ℕ) (ha : 15377 ≤ n) (hb : n ≤ 15526) :
    RowArithmetic n (band15377_15526 n).hidden (band15377_15526 n).frame (band15377_15526 n).moment := by
  unfold band15377_15526
  split_ifs with h
  · exact Rows15377.arithmetic n ha h
  · exact Rows15452.arithmetic n (by omega) hb

noncomputable def band15527_15624 (n : ℕ) : Allowances :=
  if n ≤ 15601 then Rows15527.record n else Rows15602.record n

noncomputable def band15527_15624_arithmetic (n : ℕ) (ha : 15527 ≤ n) (hb : n ≤ 15624) :
    RowArithmetic n (band15527_15624 n).hidden (band15527_15624 n).frame (band15527_15624 n).moment := by
  unfold band15527_15624
  split_ifs with h
  · exact Rows15527.arithmetic n ha h
  · exact Rows15602.arithmetic n (by omega) hb

noncomputable def band15377_15624 (n : ℕ) : Allowances :=
  if n ≤ 15526 then band15377_15526 n else band15527_15624 n

noncomputable def band15377_15624_arithmetic (n : ℕ) (ha : 15377 ≤ n) (hb : n ≤ 15624) :
    RowArithmetic n (band15377_15624 n).hidden (band15377_15624 n).frame (band15377_15624 n).moment := by
  unfold band15377_15624
  split_ifs with h
  · exact band15377_15526_arithmetic n ha h
  · exact band15527_15624_arithmetic n (by omega) hb

noncomputable def band15625_15700 (n : ℕ) : Allowances :=
  if n ≤ 15625 then Rows15625.record n else Rows15626.record n

noncomputable def band15625_15700_arithmetic (n : ℕ) (ha : 15625 ≤ n) (hb : n ≤ 15700) :
    RowArithmetic n (band15625_15700 n).hidden (band15625_15700 n).frame (band15625_15700 n).moment := by
  unfold band15625_15700
  split_ifs with h
  · exact Rows15625.arithmetic n ha h
  · exact Rows15626.arithmetic n (by omega) hb

noncomputable def band15701_15850 (n : ℕ) : Allowances :=
  if n ≤ 15775 then Rows15701.record n else Rows15776.record n

noncomputable def band15701_15850_arithmetic (n : ℕ) (ha : 15701 ≤ n) (hb : n ≤ 15850) :
    RowArithmetic n (band15701_15850 n).hidden (band15701_15850 n).frame (band15701_15850 n).moment := by
  unfold band15701_15850
  split_ifs with h
  · exact Rows15701.arithmetic n ha h
  · exact Rows15776.arithmetic n (by omega) hb

noncomputable def band15625_15850 (n : ℕ) : Allowances :=
  if n ≤ 15700 then band15625_15700 n else band15701_15850 n

noncomputable def band15625_15850_arithmetic (n : ℕ) (ha : 15625 ≤ n) (hb : n ≤ 15850) :
    RowArithmetic n (band15625_15850 n).hidden (band15625_15850 n).frame (band15625_15850 n).moment := by
  unfold band15625_15850
  split_ifs with h
  · exact band15625_15700_arithmetic n ha h
  · exact band15701_15850_arithmetic n (by omega) hb

noncomputable def band15377_15850 (n : ℕ) : Allowances :=
  if n ≤ 15624 then band15377_15624 n else band15625_15850 n

noncomputable def band15377_15850_arithmetic (n : ℕ) (ha : 15377 ≤ n) (hb : n ≤ 15850) :
    RowArithmetic n (band15377_15850 n).hidden (band15377_15850 n).frame (band15377_15850 n).moment := by
  unfold band15377_15850
  split_ifs with h
  · exact band15377_15624_arithmetic n ha h
  · exact band15625_15850_arithmetic n (by omega) hb

noncomputable def band15851_15876 (n : ℕ) : Allowances :=
  if n ≤ 15875 then Rows15851.record n else Rows15876.record n

noncomputable def band15851_15876_arithmetic (n : ℕ) (ha : 15851 ≤ n) (hb : n ≤ 15876) :
    RowArithmetic n (band15851_15876 n).hidden (band15851_15876 n).frame (band15851_15876 n).moment := by
  unfold band15851_15876
  split_ifs with h
  · exact Rows15851.arithmetic n ha h
  · exact Rows15876.arithmetic n (by omega) hb

noncomputable def band15877_16026 (n : ℕ) : Allowances :=
  if n ≤ 15951 then Rows15877.record n else Rows15952.record n

noncomputable def band15877_16026_arithmetic (n : ℕ) (ha : 15877 ≤ n) (hb : n ≤ 16026) :
    RowArithmetic n (band15877_16026 n).hidden (band15877_16026 n).frame (band15877_16026 n).moment := by
  unfold band15877_16026
  split_ifs with h
  · exact Rows15877.arithmetic n ha h
  · exact Rows15952.arithmetic n (by omega) hb

noncomputable def band15851_16026 (n : ℕ) : Allowances :=
  if n ≤ 15876 then band15851_15876 n else band15877_16026 n

noncomputable def band15851_16026_arithmetic (n : ℕ) (ha : 15851 ≤ n) (hb : n ≤ 16026) :
    RowArithmetic n (band15851_16026 n).hidden (band15851_16026 n).frame (band15851_16026 n).moment := by
  unfold band15851_16026
  split_ifs with h
  · exact band15851_15876_arithmetic n ha h
  · exact band15877_16026_arithmetic n (by omega) hb

noncomputable def band16027_16128 (n : ℕ) : Allowances :=
  if n ≤ 16101 then Rows16027.record n else Rows16102.record n

noncomputable def band16027_16128_arithmetic (n : ℕ) (ha : 16027 ≤ n) (hb : n ≤ 16128) :
    RowArithmetic n (band16027_16128 n).hidden (band16027_16128 n).frame (band16027_16128 n).moment := by
  unfold band16027_16128
  split_ifs with h
  · exact Rows16027.arithmetic n ha h
  · exact Rows16102.arithmetic n (by omega) hb

noncomputable def band16129_16199 (n : ℕ) : Allowances :=
  if n ≤ 16129 then Rows16129.record n else Rows16130.record n

noncomputable def band16129_16199_arithmetic (n : ℕ) (ha : 16129 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (band16129_16199 n).hidden (band16129_16199 n).frame (band16129_16199 n).moment := by
  unfold band16129_16199
  split_ifs with h
  · exact Rows16129.arithmetic n ha h
  · exact Rows16130.arithmetic n (by omega) hb

noncomputable def band16027_16199 (n : ℕ) : Allowances :=
  if n ≤ 16128 then band16027_16128 n else band16129_16199 n

noncomputable def band16027_16199_arithmetic (n : ℕ) (ha : 16027 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (band16027_16199 n).hidden (band16027_16199 n).frame (band16027_16199 n).moment := by
  unfold band16027_16199
  split_ifs with h
  · exact band16027_16128_arithmetic n ha h
  · exact band16129_16199_arithmetic n (by omega) hb

noncomputable def band15851_16199 (n : ℕ) : Allowances :=
  if n ≤ 16026 then band15851_16026 n else band16027_16199 n

noncomputable def band15851_16199_arithmetic (n : ℕ) (ha : 15851 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (band15851_16199 n).hidden (band15851_16199 n).frame (band15851_16199 n).moment := by
  unfold band15851_16199
  split_ifs with h
  · exact band15851_16026_arithmetic n ha h
  · exact band16027_16199_arithmetic n (by omega) hb

noncomputable def band15377_16199 (n : ℕ) : Allowances :=
  if n ≤ 15850 then band15377_15850 n else band15851_16199 n

noncomputable def band15377_16199_arithmetic (n : ℕ) (ha : 15377 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (band15377_16199 n).hidden (band15377_16199 n).frame (band15377_16199 n).moment := by
  unfold band15377_16199
  split_ifs with h
  · exact band15377_15850_arithmetic n ha h
  · exact band15851_16199_arithmetic n (by omega) hb

noncomputable def band14642_16199 (n : ℕ) : Allowances :=
  if n ≤ 15376 then band14642_15376 n else band15377_16199 n

noncomputable def band14642_16199_arithmetic (n : ℕ) (ha : 14642 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (band14642_16199 n).hidden (band14642_16199 n).frame (band14642_16199 n).moment := by
  unfold band14642_16199
  split_ifs with h
  · exact band14642_15376_arithmetic n ha h
  · exact band15377_16199_arithmetic n (by omega) hb

noncomputable def band13225_16199 (n : ℕ) : Allowances :=
  if n ≤ 14641 then band13225_14641 n else band14642_16199 n

noncomputable def band13225_16199_arithmetic (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    RowArithmetic n (band13225_16199 n).hidden (band13225_16199 n).frame (band13225_16199 n).moment := by
  unfold band13225_16199
  split_ifs with h
  · exact band13225_14641_arithmetic n ha h
  · exact band14642_16199_arithmetic n (by omega) hb

noncomputable def record (n : ℕ) : Allowances := band13225_16199 n

/-- A variant-E World package at each integer in the requested interval. -/
noncomputable def worldPackage (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    BstLean.Part192.WorldPackage (BstLean.Part192.paperProgram n) (record n).parameters :=
  (band13225_16199_arithmetic n ha hb).worldPackage ha hb

theorem angle_events (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (worldPackage n ha hb).lowerEvent =
      BstLean.Part159.Ethm (BstLean.Part192.paperProgram n).design.toCentres ∧
    (worldPackage n ha hb).upperEvent =
      BstLean.Part159.Ethp (BstLean.Part192.paperProgram n).design.toCentres := ⟨rfl,rfl⟩

end BstLean.Part271.R3.Family
