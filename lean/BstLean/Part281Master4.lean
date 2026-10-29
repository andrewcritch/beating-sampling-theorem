import BstLean.Part261Checker
import BstLean.Part281Scalar4
namespace BstLean.Part281
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp11959 : ℝ := (605103349 / 2500000000)
noncomputable def tm11959 : ℝ := (-((6257303881 / 10000000000)))
noncomputable def ep11959 : ℝ := (28056614104877029 / 50000000000000000000)
noncomputable def em11959 : ℝ := (54033517854067939 / 100000000000000000000)
noncomputable def bp11959 : ℝ := (43221911001960810717 / 100000000000000000000)
noncomputable def bm11959 : ℝ := (44586745821393268757 / 100000000000000000000)

theorem positive11959 :
    Eplus aL (agent11959.root+dsL) scalar11959.worldRadius world11959.frame
      agent11959.frame tp11959 ≤ -ep11959 := by
  apply positive_check (eT := (116657013592775953293 / 100000000000000000000)) (y := (39765334803515575013 / 100000000000000000000)) (u := (148832800864402344939 / 100000000000000000000))
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11959, agent11959, tp11959, tm11959, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11959, agent11959, tp11959, tm11959, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]

theorem negative11959 :
    Eminus aL (agent11959.root+dsL) scalar11959.worldRadius world11959.frame
      agent11959.frame tm11959 ≤ -em11959 := by
  apply negative_check (lo := (13429215419933122373 / 20000000000000000000)) (hi := (33573038549832805933 / 50000000000000000000))
    (y := (-((9107913646280998021 / 12500000000000000000)))) (u := (48256816590121330801 / 100000000000000000000))
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11959, agent11959, tp11959, tm11959, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11959, agent11959, tp11959, tm11959, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11959, agent11959, tp11959, tm11959, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]

theorem tails11959 :
    exp (-((11959:ℝ)*ep11959)) ≤ scalar11959.upperTail ∧
    exp (-((11959:ℝ)*em11959)) ≤ scalar11959.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11959:ℝ)) (by norm_num [ep11959]) ?_)
      (show bp11959^8 ≤ scalar11959.upperTail by norm_num [bp11959, scalar11959])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11959, bp11959, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11959:ℝ)) (by norm_num [em11959]) ?_)
      (show bm11959^8 ≤ scalar11959.lowerTail by norm_num [bm11959, scalar11959])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11959, bm11959, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11959 :
    agent11959.root+dsL+scalar11959.worldRadius < √(1/100/aL) ∧
    2*(agent11959.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11959, agent11959, scalar11959, tp11959, tm11959, ep11959, em11959, dsL]

noncomputable def master11959 : MasterCertificate 11959 world11959 agent11959 :=
  master scalar11959 dsL tp11959 tm11959 ep11959 em11959
    (by norm_num [dsL]) (by norm_num [tp11959]) (by norm_num [tm11959])
    (by norm_num [ep11959]) (by norm_num [em11959])
    positive11959 negative11959 tails11959.1 tails11959.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11959.1 tailGuards11959.2

theorem preserves11959 : master11959.toScalarCertificate = scalar11959 := rfl

noncomputable def tp11960 : ℝ := (484101761 / 2000000000)
noncomputable def tm11960 : ℝ := (-((6257515409 / 10000000000)))
noncomputable def ep11960 : ℝ := (5611603371433893 / 10000000000000000000)
noncomputable def em11960 : ℝ := (54035936523295027 / 100000000000000000000)
noncomputable def bp11960 : ℝ := (84408333586271553 / 195312500000000000)
noncomputable def bm11960 : ℝ := (44582122370896333253 / 100000000000000000000)

theorem positive11960 :
    Eplus aL (agent11960.root+dsL) scalar11960.worldRadius world11960.frame
      agent11960.frame tp11960 ≤ -ep11960 := by
  apply positive_check (eT := (4666291196522178273 / 4000000000000000000)) (y := (19882981396319621521 / 50000000000000000000)) (u := (29766747104227798427 / 20000000000000000000))
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11960, agent11960, tp11960, tm11960, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11960, agent11960, tp11960, tm11960, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]

theorem negative11960 :
    Eminus aL (agent11960.root+dsL) scalar11960.worldRadius world11960.frame
      agent11960.frame tm11960 ≤ -em11960 := by
  apply negative_check (lo := (33572915468502188249 / 50000000000000000000)) (hi := (67145830937004376499 / 100000000000000000000))
    (y := (-((14572585728685327649 / 20000000000000000000)))) (u := (24128500110300482657 / 50000000000000000000))
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11960, agent11960, tp11960, tm11960, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11960, agent11960, tp11960, tm11960, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11960, agent11960, tp11960, tm11960, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]

theorem tails11960 :
    exp (-((11960:ℝ)*ep11960)) ≤ scalar11960.upperTail ∧
    exp (-((11960:ℝ)*em11960)) ≤ scalar11960.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11960:ℝ)) (by norm_num [ep11960]) ?_)
      (show bp11960^8 ≤ scalar11960.upperTail by norm_num [bp11960, scalar11960])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11960, bp11960, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11960:ℝ)) (by norm_num [em11960]) ?_)
      (show bm11960^8 ≤ scalar11960.lowerTail by norm_num [bm11960, scalar11960])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11960, bm11960, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11960 :
    agent11960.root+dsL+scalar11960.worldRadius < √(1/100/aL) ∧
    2*(agent11960.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11960, agent11960, scalar11960, tp11960, tm11960, ep11960, em11960, dsL]

noncomputable def master11960 : MasterCertificate 11960 world11960 agent11960 :=
  master scalar11960 dsL tp11960 tm11960 ep11960 em11960
    (by norm_num [dsL]) (by norm_num [tp11960]) (by norm_num [tm11960])
    (by norm_num [ep11960]) (by norm_num [em11960])
    positive11960 negative11960 tails11960.1 tails11960.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11960.1 tailGuards11960.2

theorem preserves11960 : master11960.toScalarCertificate = scalar11960 := rfl

noncomputable def tp11961 : ℝ := (2420604109 / 10000000000)
noncomputable def tm11961 : ℝ := (-((3128863549 / 5000000000)))
noncomputable def ep11961 : ℝ := (56118837226801751 / 100000000000000000000)
noncomputable def em11961 : ℝ := (54038353369920373 / 100000000000000000000)
noncomputable def bp11961 : ℝ := (2160611205864574661 / 5000000000000000000)
noncomputable def bm11961 : ℝ := (11144375086257515563 / 25000000000000000000)

theorem positive11961 :
    Eplus aL (agent11961.root+dsL) scalar11961.worldRadius world11961.frame
      agent11961.frame tp11961 ≤ -ep11961 := by
  apply positive_check (eT := (116657545495783422131 / 100000000000000000000)) (y := (39766589377045000133 / 100000000000000000000)) (u := (148834668093037945339 / 100000000000000000000))
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11961, agent11961, tp11961, tm11961, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11961, agent11961, tp11961, tm11961, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]

theorem negative11961 :
    Eminus aL (agent11961.root+dsL) scalar11961.worldRadius world11961.frame
      agent11961.frame tm11961 ≤ -em11961 := by
  apply negative_check (lo := (4196599001126291573 / 6250000000000000000)) (hi := (67145584018020665169 / 100000000000000000000))
    (y := (-((72862550219041100683 / 100000000000000000000)))) (u := (24128591418601530821 / 50000000000000000000))
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11961, agent11961, tp11961, tm11961, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11961, agent11961, tp11961, tm11961, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11961, agent11961, tp11961, tm11961, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]

theorem tails11961 :
    exp (-((11961:ℝ)*ep11961)) ≤ scalar11961.upperTail ∧
    exp (-((11961:ℝ)*em11961)) ≤ scalar11961.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11961:ℝ)) (by norm_num [ep11961]) ?_)
      (show bp11961^8 ≤ scalar11961.upperTail by norm_num [bp11961, scalar11961])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11961, bp11961, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11961:ℝ)) (by norm_num [em11961]) ?_)
      (show bm11961^8 ≤ scalar11961.lowerTail by norm_num [bm11961, scalar11961])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11961, bm11961, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11961 :
    agent11961.root+dsL+scalar11961.worldRadius < √(1/100/aL) ∧
    2*(agent11961.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11961, agent11961, scalar11961, tp11961, tm11961, ep11961, em11961, dsL]

noncomputable def master11961 : MasterCertificate 11961 world11961 agent11961 :=
  master scalar11961 dsL tp11961 tm11961 ep11961 em11961
    (by norm_num [dsL]) (by norm_num [tp11961]) (by norm_num [tm11961])
    (by norm_num [ep11961]) (by norm_num [em11961])
    positive11961 negative11961 tails11961.1 tails11961.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11961.1 tailGuards11961.2

theorem preserves11961 : master11961.toScalarCertificate = scalar11961 := rfl

noncomputable def tp11962 : ℝ := (1210349723 / 5000000000)
noncomputable def tm11962 : ℝ := (-((1564484639 / 2500000000)))
noncomputable def ep11962 : ℝ := (1403040974302627 / 2500000000000000000)
noncomputable def em11962 : ℝ := (6755096069269557 / 12500000000000000000)
noncomputable def bp11962 : ℝ := (21603691409957192273 / 50000000000000000000)
noncomputable def bm11962 : ℝ := (22286439818488818573 / 50000000000000000000)

theorem positive11962 :
    Eplus aL (agent11962.root+dsL) scalar11962.worldRadius world11962.frame
      agent11962.frame tp11962 ≤ -ep11962 := by
  apply positive_check (eT := (58328905682804298199 / 50000000000000000000)) (y := (39767217164867620001 / 100000000000000000000)) (u := (29767120492378598801 / 20000000000000000000))
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11962, agent11962, tp11962, tm11962, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11962, agent11962, tp11962, tm11962, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]

theorem negative11962 :
    Eminus aL (agent11962.root+dsL) scalar11962.worldRadius world11962.frame
      agent11962.frame tm11962 ≤ -em11962 := by
  apply negative_check (lo := (67145338018188157223 / 100000000000000000000)) (hi := (8393167252273519653 / 12500000000000000000))
    (y := (-((1821554261992584459 / 2500000000000000000)))) (u := (48257366089057510557 / 100000000000000000000))
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11962, agent11962, tp11962, tm11962, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11962, agent11962, tp11962, tm11962, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11962, agent11962, tp11962, tm11962, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]

theorem tails11962 :
    exp (-((11962:ℝ)*ep11962)) ≤ scalar11962.upperTail ∧
    exp (-((11962:ℝ)*em11962)) ≤ scalar11962.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11962:ℝ)) (by norm_num [ep11962]) ?_)
      (show bp11962^8 ≤ scalar11962.upperTail by norm_num [bp11962, scalar11962])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11962, bp11962, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11962:ℝ)) (by norm_num [em11962]) ?_)
      (show bm11962^8 ≤ scalar11962.lowerTail by norm_num [bm11962, scalar11962])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11962, bm11962, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11962 :
    agent11962.root+dsL+scalar11962.worldRadius < √(1/100/aL) ∧
    2*(agent11962.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11962, agent11962, scalar11962, tp11962, tm11962, ep11962, em11962, dsL]

noncomputable def master11962 : MasterCertificate 11962 world11962 agent11962 :=
  master scalar11962 dsL tp11962 tm11962 ep11962 em11962
    (by norm_num [dsL]) (by norm_num [tp11962]) (by norm_num [tm11962])
    (by norm_num [ep11962]) (by norm_num [em11962])
    positive11962 negative11962 tails11962.1 tails11962.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11962.1 tailGuards11962.2

theorem preserves11962 : master11962.toScalarCertificate = scalar11962 := rfl

noncomputable def tp11963 : ℝ := (2420794687 / 10000000000)
noncomputable def tm11963 : ℝ := (-((6258149947 / 10000000000)))
noncomputable def ep11963 : ℝ := (2244977586460751 / 4000000000000000000)
noncomputable def em11963 : ℝ := (27021591394870091 / 50000000000000000000)
noncomputable def bp11963 : ℝ := (43202542444474459731 / 100000000000000000000)
noncomputable def bm11963 : ℝ := (5571032471378432857 / 12500000000000000000)

theorem positive11963 :
    Eplus aL (agent11963.root+dsL) scalar11963.worldRadius world11963.frame
      agent11963.frame tp11963 ≤ -ep11963 := by
  apply positive_check (eT := (7291129785297375153 / 6250000000000000000)) (y := (39767843710157674241 / 100000000000000000000)) (u := (37209133746817871679 / 25000000000000000000))
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11963, agent11963, tp11963, tm11963, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11963, agent11963, tp11963, tm11963, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]

theorem negative11963 :
    Eminus aL (agent11963.root+dsL) scalar11963.worldRadius world11963.frame
      agent11963.frame tm11963 ≤ -em11963 := by
  apply negative_check (lo := (13429018447291466691 / 20000000000000000000)) (hi := (4196568264778583341 / 6250000000000000000))
    (y := (-((72861791354896148441 / 100000000000000000000)))) (u := (48257549045050485491 / 100000000000000000000))
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11963, agent11963, tp11963, tm11963, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11963, agent11963, tp11963, tm11963, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11963, agent11963, tp11963, tm11963, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]

theorem tails11963 :
    exp (-((11963:ℝ)*ep11963)) ≤ scalar11963.upperTail ∧
    exp (-((11963:ℝ)*em11963)) ≤ scalar11963.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11963:ℝ)) (by norm_num [ep11963]) ?_)
      (show bp11963^8 ≤ scalar11963.upperTail by norm_num [bp11963, scalar11963])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11963, bp11963, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11963:ℝ)) (by norm_num [em11963]) ?_)
      (show bm11963^8 ≤ scalar11963.lowerTail by norm_num [bm11963, scalar11963])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11963, bm11963, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11963 :
    agent11963.root+dsL+scalar11963.worldRadius < √(1/100/aL) ∧
    2*(agent11963.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11963, agent11963, scalar11963, tp11963, tm11963, ep11963, em11963, dsL]

noncomputable def master11963 : MasterCertificate 11963 world11963 agent11963 :=
  master scalar11963 dsL tp11963 tm11963 ep11963 em11963
    (by norm_num [dsL]) (by norm_num [tp11963]) (by norm_num [tm11963])
    (by norm_num [ep11963]) (by norm_num [em11963])
    positive11963 negative11963 tails11963.1 tails11963.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11963.1 tailGuards11963.2

theorem preserves11963 : master11963.toScalarCertificate = scalar11963 := rfl

noncomputable def tp11964 : ℝ := (302611227 / 1250000000)
noncomputable def tm11964 : ℝ := (-((97786891 / 156250000)))
noncomputable def ep11964 : ℝ := (11225447640760571 / 20000000000000000000)
noncomputable def em11964 : ℝ := (27022797521187549 / 50000000000000000000)
noncomputable def bp11964 : ℝ := (4319770369591909717 / 10000000000000000000)
noncomputable def bm11964 : ℝ := (22281820718240803703 / 50000000000000000000)

theorem positive11964 :
    Eplus aL (agent11964.root+dsL) scalar11964.worldRadius world11964.frame
      agent11964.frame tp11964 ≤ -ep11964 := by
  apply positive_check (eT := (11665834097440703451 / 10000000000000000000)) (y := (39768468886893471363 / 100000000000000000000)) (u := (37209366370392801899 / 25000000000000000000))
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11964, agent11964, tp11964, tm11964, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11964, agent11964, tp11964, tm11964, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]

theorem negative11964 :
    Eminus aL (agent11964.root+dsL) scalar11964.worldRadius world11964.frame
      agent11964.frame tm11964 ≤ -em11964 := by
  apply negative_check (lo := (67144847728469594137 / 100000000000000000000)) (hi := (33572423864234797069 / 50000000000000000000))
    (y := (-((72861410123838917049 / 100000000000000000000)))) (u := (24128866509082792499 / 50000000000000000000))
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11964, agent11964, tp11964, tm11964, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11964, agent11964, tp11964, tm11964, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11964, agent11964, tp11964, tm11964, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]

theorem tails11964 :
    exp (-((11964:ℝ)*ep11964)) ≤ scalar11964.upperTail ∧
    exp (-((11964:ℝ)*em11964)) ≤ scalar11964.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11964:ℝ)) (by norm_num [ep11964]) ?_)
      (show bp11964^8 ≤ scalar11964.upperTail by norm_num [bp11964, scalar11964])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11964, bp11964, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11964:ℝ)) (by norm_num [em11964]) ?_)
      (show bm11964^8 ≤ scalar11964.lowerTail by norm_num [bm11964, scalar11964])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11964, bm11964, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11964 :
    agent11964.root+dsL+scalar11964.worldRadius < √(1/100/aL) ∧
    2*(agent11964.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11964, agent11964, scalar11964, tp11964, tm11964, ep11964, em11964, dsL]

noncomputable def master11964 : MasterCertificate 11964 world11964 agent11964 :=
  master scalar11964 dsL tp11964 tm11964 ep11964 em11964
    (by norm_num [dsL]) (by norm_num [tp11964]) (by norm_num [tm11964])
    (by norm_num [ep11964]) (by norm_num [em11964])
    positive11964 negative11964 tails11964.1 tails11964.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11964.1 tailGuards11964.2

theorem preserves11964 : master11964.toScalarCertificate = scalar11964 := rfl

noncomputable def tp11965 : ℝ := (1210492509 / 5000000000)
noncomputable def tm11965 : ℝ := (-((782321517 / 1250000000)))
noncomputable def ep11965 : ℝ := (28065017624060871 / 50000000000000000000)
noncomputable def em11965 : ℝ := (54048005927478033 / 100000000000000000000)
noncomputable def bp11965 : ℝ := (10798216538702130597 / 25000000000000000000)
noncomputable def bm11965 : ℝ := (44559024223158696991 / 100000000000000000000)

theorem positive11965 :
    Eplus aL (agent11965.root+dsL) scalar11965.worldRadius world11965.frame
      agent11965.frame tp11965 ≤ -ep11965 := by
  apply positive_check (eT := (23331721193635819703 / 20000000000000000000)) (y := (39769095760999580307 / 100000000000000000000)) (u := (5953535940321077919 / 4000000000000000000))
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11965, agent11965, tp11965, tm11965, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11965, agent11965, tp11965, tm11965, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]

theorem negative11965 :
    Eminus aL (agent11965.root+dsL) scalar11965.worldRadius world11965.frame
      agent11965.frame tm11965 ≤ -em11965 := by
  apply negative_check (lo := (67144603002697003459 / 100000000000000000000)) (hi := (3357230150134850173 / 5000000000000000000))
    (y := (-((36430514963396637719 / 50000000000000000000)))) (u := (48257916492989596389 / 100000000000000000000))
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11965, agent11965, tp11965, tm11965, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11965, agent11965, tp11965, tm11965, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11965, agent11965, tp11965, tm11965, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]

theorem tails11965 :
    exp (-((11965:ℝ)*ep11965)) ≤ scalar11965.upperTail ∧
    exp (-((11965:ℝ)*em11965)) ≤ scalar11965.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11965:ℝ)) (by norm_num [ep11965]) ?_)
      (show bp11965^8 ≤ scalar11965.upperTail by norm_num [bp11965, scalar11965])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11965, bp11965, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11965:ℝ)) (by norm_num [em11965]) ?_)
      (show bm11965^8 ≤ scalar11965.lowerTail by norm_num [bm11965, scalar11965])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11965, bm11965, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11965 :
    agent11965.root+dsL+scalar11965.worldRadius < √(1/100/aL) ∧
    2*(agent11965.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11965, agent11965, scalar11965, tp11965, tm11965, ep11965, em11965, dsL]

noncomputable def master11965 : MasterCertificate 11965 world11965 agent11965 :=
  master scalar11965 dsL tp11965 tm11965 ep11965 em11965
    (by norm_num [dsL]) (by norm_num [tp11965]) (by norm_num [tm11965])
    (by norm_num [ep11965]) (by norm_num [em11965])
    positive11965 negative11965 tails11965.1 tails11965.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11965.1 tailGuards11965.2

theorem preserves11965 : master11965.toScalarCertificate = scalar11965 := rfl

noncomputable def tp11966 : ℝ := (60527003 / 250000000)
noncomputable def tm11966 : ℝ := (-((125175661 / 200000000)))
noncomputable def ep11966 : ℝ := (28066415488851189 / 50000000000000000000)
noncomputable def em11966 : ℝ := (54050415578161443 / 100000000000000000000)
noncomputable def bp11966 : ℝ := (21594014851369606139 / 50000000000000000000)
noncomputable def bm11966 : ℝ := (44554408042328727913 / 100000000000000000000)

theorem positive11966 :
    Eplus aL (agent11966.root+dsL) scalar11966.worldRadius world11966.frame
      agent11966.frame tp11966 ≤ -ep11966 := by
  apply positive_check (eT := (113924677989856517 / 97656250000000000)) (y := (39769721535376684991 / 100000000000000000000)) (u := (74419664951751159123 / 50000000000000000000))
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11966, agent11966, tp11966, tm11966, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11966, agent11966, tp11966, tm11966, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]

theorem negative11966 :
    Eminus aL (agent11966.root+dsL) scalar11966.worldRadius world11966.frame
      agent11966.frame tm11966 ≤ -em11966 := by
  apply negative_check (lo := (33572179527403446741 / 50000000000000000000)) (hi := (67144359054806893483 / 100000000000000000000))
    (y := (-((18215162318118500259 / 25000000000000000000)))) (u := (6032262523647842789 / 12500000000000000000))
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11966, agent11966, tp11966, tm11966, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11966, agent11966, tp11966, tm11966, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11966, agent11966, tp11966, tm11966, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]

theorem tails11966 :
    exp (-((11966:ℝ)*ep11966)) ≤ scalar11966.upperTail ∧
    exp (-((11966:ℝ)*em11966)) ≤ scalar11966.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11966:ℝ)) (by norm_num [ep11966]) ?_)
      (show bp11966^8 ≤ scalar11966.upperTail by norm_num [bp11966, scalar11966])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11966, bp11966, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11966:ℝ)) (by norm_num [em11966]) ?_)
      (show bm11966^8 ≤ scalar11966.lowerTail by norm_num [bm11966, scalar11966])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11966, bm11966, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11966 :
    agent11966.root+dsL+scalar11966.worldRadius < √(1/100/aL) ∧
    2*(agent11966.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11966, agent11966, scalar11966, tp11966, tm11966, ep11966, em11966, dsL]

noncomputable def master11966 : MasterCertificate 11966 world11966 agent11966 :=
  master scalar11966 dsL tp11966 tm11966 ep11966 em11966
    (by norm_num [dsL]) (by norm_num [tp11966]) (by norm_num [tm11966])
    (by norm_num [ep11966]) (by norm_num [em11966])
    positive11966 negative11966 tails11966.1 tails11966.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11966.1 tailGuards11966.2

theorem preserves11966 : master11966.toScalarCertificate = scalar11966 := rfl

noncomputable def tp11967 : ℝ := (2421175389 / 10000000000)
noncomputable def tm11967 : ℝ := (-((6258994731 / 10000000000)))
noncomputable def ep11967 : ℝ := (28067814540671341 / 50000000000000000000)
noncomputable def em11967 : ℝ := (27026414104466511 / 50000000000000000000)
noncomputable def bp11967 : ℝ := (10795797989209834817 / 25000000000000000000)
noncomputable def bm11967 : ℝ := (11137447521347368683 / 25000000000000000000)

theorem positive11967 :
    Eplus aL (agent11967.root+dsL) scalar11967.worldRadius world11967.frame
      agent11967.frame tp11967 ≤ -ep11967 := by
  apply positive_check (eT := (1166591358370019547 / 1000000000000000000)) (y := (310705811777611773 / 781250000000000000)) (u := (14884025624093385887 / 10000000000000000000))
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11967, agent11967, tp11967, tm11967, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11967, agent11967, tp11967, tm11967, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]

theorem negative11967 :
    Eminus aL (agent11967.root+dsL) scalar11967.worldRadius world11967.frame
      agent11967.frame tm11967 ≤ -em11967 := by
  apply negative_check (lo := (8393013970154847501 / 12500000000000000000)) (hi := (67144111761238780009 / 100000000000000000000))
    (y := (-((72860262853445608801 / 100000000000000000000)))) (u := (48258286668024908537 / 100000000000000000000))
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11967, agent11967, tp11967, tm11967, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11967, agent11967, tp11967, tm11967, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11967, agent11967, tp11967, tm11967, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]

theorem tails11967 :
    exp (-((11967:ℝ)*ep11967)) ≤ scalar11967.upperTail ∧
    exp (-((11967:ℝ)*em11967)) ≤ scalar11967.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11967:ℝ)) (by norm_num [ep11967]) ?_)
      (show bp11967^8 ≤ scalar11967.upperTail by norm_num [bp11967, scalar11967])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11967, bp11967, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11967:ℝ)) (by norm_num [em11967]) ?_)
      (show bm11967^8 ≤ scalar11967.lowerTail by norm_num [bm11967, scalar11967])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11967, bm11967, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11967 :
    agent11967.root+dsL+scalar11967.worldRadius < √(1/100/aL) ∧
    2*(agent11967.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11967, agent11967, scalar11967, tp11967, tm11967, ep11967, em11967, dsL]

noncomputable def master11967 : MasterCertificate 11967 world11967 agent11967 :=
  master scalar11967 dsL tp11967 tm11967 ep11967 em11967
    (by norm_num [dsL]) (by norm_num [tp11967]) (by norm_num [tm11967])
    (by norm_num [ep11967]) (by norm_num [em11967])
    positive11967 negative11967 tails11967.1 tails11967.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11967.1 tailGuards11967.2

theorem preserves11967 : master11967.toScalarCertificate = scalar11967 := rfl

noncomputable def tp11968 : ℝ := (2421270737 / 10000000000)
noncomputable def tm11968 : ℝ := (-((6259206407 / 10000000000)))
noncomputable def ep11968 : ℝ := (2245537114689553 / 4000000000000000000)
noncomputable def em11968 : ℝ := (13513810432021887 / 25000000000000000000)
noncomputable def bp11968 : ℝ := (43178354010098219159 / 100000000000000000000)
noncomputable def bm11968 : ℝ := (22272585873199022491 / 50000000000000000000)

theorem positive11968 :
    Eplus aL (agent11968.root+dsL) scalar11968.worldRadius world11968.frame
      agent11968.frame tp11968 ≤ -ep11968 := by
  apply positive_check (eT := (116659402040947440063 / 100000000000000000000)) (y := (19885482915151230311 / 50000000000000000000)) (u := (2325643467425845097 / 1562500000000000000))
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11968, agent11968, tp11968, tm11968, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11968, agent11968, tp11968, tm11968, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]

theorem negative11968 :
    Eminus aL (agent11968.root+dsL) scalar11968.worldRadius world11968.frame
      agent11968.frame tm11968 ≤ -em11968 := by
  apply negative_check (lo := (33571932210508068751 / 50000000000000000000)) (hi := (67143864421016137503 / 100000000000000000000))
    (y := (-((18214968240506648003 / 25000000000000000000)))) (u := (48258474823310392107 / 100000000000000000000))
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11968, agent11968, tp11968, tm11968, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11968, agent11968, tp11968, tm11968, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11968, agent11968, tp11968, tm11968, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]

theorem tails11968 :
    exp (-((11968:ℝ)*ep11968)) ≤ scalar11968.upperTail ∧
    exp (-((11968:ℝ)*em11968)) ≤ scalar11968.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11968:ℝ)) (by norm_num [ep11968]) ?_)
      (show bp11968^8 ≤ scalar11968.upperTail by norm_num [bp11968, scalar11968])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11968, bp11968, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11968:ℝ)) (by norm_num [em11968]) ?_)
      (show bm11968^8 ≤ scalar11968.lowerTail by norm_num [bm11968, scalar11968])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11968, bm11968, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11968 :
    agent11968.root+dsL+scalar11968.worldRadius < √(1/100/aL) ∧
    2*(agent11968.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11968, agent11968, scalar11968, tp11968, tm11968, ep11968, em11968, dsL]

noncomputable def master11968 : MasterCertificate 11968 world11968 agent11968 :=
  master scalar11968 dsL tp11968 tm11968 ep11968 em11968
    (by norm_num [dsL]) (by norm_num [tp11968]) (by norm_num [tm11968])
    (by norm_num [ep11968]) (by norm_num [em11968])
    positive11968 negative11968 tails11968.1 tails11968.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11968.1 tailGuards11968.2

theorem preserves11968 : master11968.toScalarCertificate = scalar11968 := rfl

noncomputable def tp11969 : ℝ := (2421366031 / 10000000000)
noncomputable def tm11969 : ℝ := (-((6259417981 / 10000000000)))
noncomputable def ep11969 : ℝ := (56141224845265387 / 100000000000000000000)
noncomputable def em11969 : ℝ := (13514413389755331 / 25000000000000000000)
noncomputable def bp11969 : ℝ := (43173517471040483981 / 100000000000000000000)
noncomputable def bm11969 : ℝ := (44540554742427377709 / 100000000000000000000)

theorem positive11969 :
    Eplus aL (agent11969.root+dsL) scalar11969.worldRadius world11969.frame
      agent11969.frame tp11969 ≤ -ep11969 := by
  apply positive_check (eT := (58329833943015249451 / 50000000000000000000)) (y := (9942896879970717337 / 25000000000000000000)) (u := (18605263406031219621 / 12500000000000000000))
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11969, agent11969, tp11969, tm11969, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11969, agent11969, tp11969, tm11969, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]

theorem negative11969 :
    Eminus aL (agent11969.root+dsL) scalar11969.worldRadius world11969.frame
      agent11969.frame tm11969 ≤ -em11969 := by
  apply negative_check (lo := (67143617448595758447 / 100000000000000000000)) (hi := (4196476090537234903 / 6250000000000000000))
    (y := (-((36429741696904170739 / 50000000000000000000)))) (u := (24129331411678555069 / 50000000000000000000))
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11969, agent11969, tp11969, tm11969, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11969, agent11969, tp11969, tm11969, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11969, agent11969, tp11969, tm11969, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]

theorem tails11969 :
    exp (-((11969:ℝ)*ep11969)) ≤ scalar11969.upperTail ∧
    exp (-((11969:ℝ)*em11969)) ≤ scalar11969.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11969:ℝ)) (by norm_num [ep11969]) ?_)
      (show bp11969^8 ≤ scalar11969.upperTail by norm_num [bp11969, scalar11969])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11969, bp11969, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11969:ℝ)) (by norm_num [em11969]) ?_)
      (show bm11969^8 ≤ scalar11969.lowerTail by norm_num [bm11969, scalar11969])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11969, bm11969, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11969 :
    agent11969.root+dsL+scalar11969.worldRadius < √(1/100/aL) ∧
    2*(agent11969.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11969, agent11969, scalar11969, tp11969, tm11969, ep11969, em11969, dsL]

noncomputable def master11969 : MasterCertificate 11969 world11969 agent11969 :=
  master scalar11969 dsL tp11969 tm11969 ep11969 em11969
    (by norm_num [dsL]) (by norm_num [tp11969]) (by norm_num [tm11969])
    (by norm_num [ep11969]) (by norm_num [em11969])
    positive11969 negative11969 tails11969.1 tails11969.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11969.1 tailGuards11969.2

theorem preserves11969 : master11969.toScalarCertificate = scalar11969 := rfl

noncomputable def tp11970 : ℝ := (1210730617 / 5000000000)
noncomputable def tm11970 : ℝ := (-((782453683 / 1250000000)))
noncomputable def ep11970 : ℝ := (28072009916165339 / 50000000000000000000)
noncomputable def em11970 : ℝ := (10812012713766757 / 20000000000000000000)
noncomputable def bp11970 : ℝ := (21584341228934092419 / 50000000000000000000)
noncomputable def bm11970 : ℝ := (44535939162004359357 / 100000000000000000000)

theorem positive11970 :
    Eplus aL (agent11970.root+dsL) scalar11970.worldRadius world11970.frame
      agent11970.frame tp11970 ≤ -ep11970 := by
  apply positive_check (eT := (58329966548774826659 / 50000000000000000000)) (y := (310720375396393983 / 781250000000000000)) (u := (74421515431158475473 / 50000000000000000000))
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11970, agent11970, tp11970, tm11970, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11970, agent11970, tp11970, tm11970, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]

theorem negative11970 :
    Eminus aL (agent11970.root+dsL) scalar11970.worldRadius world11970.frame
      agent11970.frame tm11970 ≤ -em11970 := by
  apply negative_check (lo := (16785842699253419357 / 25000000000000000000)) (hi := (67143370797013677429 / 100000000000000000000))
    (y := (-((7285909353535476783 / 10000000000000000000)))) (u := (12064712741050112463 / 25000000000000000000))
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11970, agent11970, tp11970, tm11970, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11970, agent11970, tp11970, tm11970, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11970, agent11970, tp11970, tm11970, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]

theorem tails11970 :
    exp (-((11970:ℝ)*ep11970)) ≤ scalar11970.upperTail ∧
    exp (-((11970:ℝ)*em11970)) ≤ scalar11970.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11970:ℝ)) (by norm_num [ep11970]) ?_)
      (show bp11970^8 ≤ scalar11970.upperTail by norm_num [bp11970, scalar11970])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11970, bp11970, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11970:ℝ)) (by norm_num [em11970]) ?_)
      (show bm11970^8 ≤ scalar11970.lowerTail by norm_num [bm11970, scalar11970])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11970, bm11970, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11970 :
    agent11970.root+dsL+scalar11970.worldRadius < √(1/100/aL) ∧
    2*(agent11970.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11970, agent11970, scalar11970, tp11970, tm11970, ep11970, em11970, dsL]

noncomputable def master11970 : MasterCertificate 11970 world11970 agent11970 :=
  master scalar11970 dsL tp11970 tm11970 ep11970 em11970
    (by norm_num [dsL]) (by norm_num [tp11970]) (by norm_num [tm11970])
    (by norm_num [ep11970]) (by norm_num [em11970])
    positive11970 negative11970 tails11970.1 tails11970.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11970.1 tailGuards11970.2

theorem preserves11970 : master11970.toScalarCertificate = scalar11970 := rfl

noncomputable def tp11971 : ℝ := (2421556401 / 10000000000)
noncomputable def tm11971 : ℝ := (-((1564960209 / 2500000000)))
noncomputable def ep11971 : ℝ := (56146814009275189 / 100000000000000000000)
noncomputable def em11971 : ℝ := (27031236404118573 / 50000000000000000000)
noncomputable def bp11971 : ℝ := (21581924103907805643 / 50000000000000000000)
noncomputable def bm11971 : ℝ := (22265662152470871313 / 50000000000000000000)

theorem positive11971 :
    Eplus aL (agent11971.root+dsL) scalar11971.worldRadius world11971.frame
      agent11971.frame tp11971 ≤ -ep11971 := by
  apply positive_check (eT := (23332039616766338571 / 20000000000000000000)) (y := (621450446292978861 / 1562500000000000000)) (u := (148843954454068295813 / 100000000000000000000))
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11971, agent11971, tp11971, tm11971, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11971, agent11971, tp11971, tm11971, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]

theorem negative11971 :
    Eminus aL (agent11971.root+dsL) scalar11971.worldRadius world11971.frame
      agent11971.frame tm11971 ≤ -em11971 := by
  apply negative_check (lo := (13428624910344206189 / 20000000000000000000)) (hi := (33571562275860515473 / 50000000000000000000))
    (y := (-((14571740833957348097 / 20000000000000000000)))) (u := (48259038867915446027 / 100000000000000000000))
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11971, agent11971, tp11971, tm11971, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11971, agent11971, tp11971, tm11971, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11971, agent11971, tp11971, tm11971, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]

theorem tails11971 :
    exp (-((11971:ℝ)*ep11971)) ≤ scalar11971.upperTail ∧
    exp (-((11971:ℝ)*em11971)) ≤ scalar11971.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11971:ℝ)) (by norm_num [ep11971]) ?_)
      (show bp11971^8 ≤ scalar11971.upperTail by norm_num [bp11971, scalar11971])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11971, bp11971, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11971:ℝ)) (by norm_num [em11971]) ?_)
      (show bm11971^8 ≤ scalar11971.lowerTail by norm_num [bm11971, scalar11971])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11971, bm11971, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11971 :
    agent11971.root+dsL+scalar11971.worldRadius < √(1/100/aL) ∧
    2*(agent11971.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11971, agent11971, scalar11971, tp11971, tm11971, ep11971, em11971, dsL]

noncomputable def master11971 : MasterCertificate 11971 world11971 agent11971 :=
  master scalar11971 dsL tp11971 tm11971 ep11971 em11971
    (by norm_num [dsL]) (by norm_num [tp11971]) (by norm_num [tm11971])
    (by norm_num [ep11971]) (by norm_num [em11971])
    positive11971 negative11971 tails11971.1 tails11971.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11971.1 tailGuards11971.2

theorem preserves11971 : master11971.toScalarCertificate = scalar11971 := rfl

noncomputable def tp11972 : ℝ := (2421651553 / 10000000000)
noncomputable def tm11972 : ℝ := (-((1252010397 / 2000000000)))
noncomputable def ep11972 : ℝ := (11229921140299163 / 20000000000000000000)
noncomputable def em11972 : ℝ := (54064879772095179 / 100000000000000000000)
noncomputable def bp11972 : ℝ := (43159015802462492333 / 100000000000000000000)
noncomputable def bm11972 : ℝ := (11131677793544561157 / 25000000000000000000)

theorem positive11972 :
    Eplus aL (agent11972.root+dsL) scalar11972.worldRadius world11972.frame
      agent11972.frame tp11972 ≤ -ep11972 := by
  apply positive_check (eT := (11666046300082511589 / 10000000000000000000)) (y := (39773449314655321819 / 100000000000000000000)) (u := (74422439204309146187 / 50000000000000000000))
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11972, agent11972, tp11972, tm11972, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11972, agent11972, tp11972, tm11972, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]

theorem negative11972 :
    Eminus aL (agent11972.root+dsL) scalar11972.worldRadius world11972.frame
      agent11972.frame tm11972 ≤ -em11972 := by
  apply negative_check (lo := (67142879191146931267 / 100000000000000000000)) (hi := (16785719797786732817 / 25000000000000000000))
    (y := (-((72858313134576788411 / 100000000000000000000)))) (u := (24129613789059182731 / 50000000000000000000))
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11972, agent11972, tp11972, tm11972, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11972, agent11972, tp11972, tm11972, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11972, agent11972, tp11972, tm11972, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]

theorem tails11972 :
    exp (-((11972:ℝ)*ep11972)) ≤ scalar11972.upperTail ∧
    exp (-((11972:ℝ)*em11972)) ≤ scalar11972.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11972:ℝ)) (by norm_num [ep11972]) ?_)
      (show bp11972^8 ≤ scalar11972.upperTail by norm_num [bp11972, scalar11972])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11972, bp11972, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11972:ℝ)) (by norm_num [em11972]) ?_)
      (show bm11972^8 ≤ scalar11972.lowerTail by norm_num [bm11972, scalar11972])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11972, bm11972, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11972 :
    agent11972.root+dsL+scalar11972.worldRadius < √(1/100/aL) ∧
    2*(agent11972.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11972, agent11972, scalar11972, tp11972, tm11972, ep11972, em11972, dsL]

noncomputable def master11972 : MasterCertificate 11972 world11972 agent11972 :=
  master scalar11972 dsL tp11972 tm11972 ep11972 em11972
    (by norm_num [dsL]) (by norm_num [tp11972]) (by norm_num [tm11972])
    (by norm_num [ep11972]) (by norm_num [em11972])
    positive11972 negative11972 tails11972.1 tails11972.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11972.1 tailGuards11972.2

theorem preserves11972 : master11972.toScalarCertificate = scalar11972 := rfl

noncomputable def tp11973 : ℝ := (2421746623 / 10000000000)
noncomputable def tm11973 : ℝ := (-((6260263147 / 10000000000)))
noncomputable def ep11973 : ℝ := (56152395976174209 / 100000000000000000000)
noncomputable def em11973 : ℝ := (3379205336083369 / 6250000000000000000)
noncomputable def bp11973 : ℝ := (43154184552466542323 / 100000000000000000000)
noncomputable def bm11973 : ℝ := (22261049579341035313 / 50000000000000000000)

theorem positive11973 :
    Eplus aL (agent11973.root+dsL) scalar11973.worldRadius world11973.frame
      agent11973.frame tp11973 ≤ -ep11973 := by
  apply positive_check (eT := (116660727351099676789 / 100000000000000000000)) (y := (19887034668836175831 / 50000000000000000000)) (u := (148845801283985112781 / 100000000000000000000))
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11973, agent11973, tp11973, tm11973, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11973, agent11973, tp11973, tm11973, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]

theorem negative11973 :
    Eminus aL (agent11973.root+dsL) scalar11973.worldRadius world11973.frame
      agent11973.frame tm11973 ≤ -em11973 := by
  apply negative_check (lo := (13428526741408058149 / 20000000000000000000)) (hi := (33571316853520145373 / 50000000000000000000))
    (y := (-((72857923514564013977 / 100000000000000000000)))) (u := (24129707803046658621 / 50000000000000000000))
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11973, agent11973, tp11973, tm11973, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11973, agent11973, tp11973, tm11973, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11973, agent11973, tp11973, tm11973, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]

theorem tails11973 :
    exp (-((11973:ℝ)*ep11973)) ≤ scalar11973.upperTail ∧
    exp (-((11973:ℝ)*em11973)) ≤ scalar11973.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11973:ℝ)) (by norm_num [ep11973]) ?_)
      (show bp11973^8 ≤ scalar11973.upperTail by norm_num [bp11973, scalar11973])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11973, bp11973, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11973:ℝ)) (by norm_num [em11973]) ?_)
      (show bm11973^8 ≤ scalar11973.lowerTail by norm_num [bm11973, scalar11973])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11973, bm11973, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11973 :
    agent11973.root+dsL+scalar11973.worldRadius < √(1/100/aL) ∧
    2*(agent11973.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11973, agent11973, scalar11973, tp11973, tm11973, ep11973, em11973, dsL]

noncomputable def master11973 : MasterCertificate 11973 world11973 agent11973 :=
  master scalar11973 dsL tp11973 tm11973 ep11973 em11973
    (by norm_num [dsL]) (by norm_num [tp11973]) (by norm_num [tm11973])
    (by norm_num [ep11973]) (by norm_num [em11973])
    positive11973 negative11973 tails11973.1 tails11973.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11973.1 tailGuards11973.2

theorem preserves11973 : master11973.toScalarCertificate = scalar11973 := rfl

noncomputable def tp11974 : ℝ := (1210920853 / 5000000000)
noncomputable def tm11974 : ℝ := (-((6260474099 / 10000000000)))
noncomputable def ep11974 : ℝ := (56155184872734917 / 100000000000000000000)
noncomputable def em11974 : ℝ := (13517422438643937 / 25000000000000000000)
noncomputable def bp11974 : ℝ := (4314935443232838569 / 10000000000000000000)
noncomputable def bm11974 : ℝ := (8903497634279343687 / 20000000000000000000)

theorem positive11974 :
    Eplus aL (agent11974.root+dsL) scalar11974.worldRadius world11974.frame
      agent11974.frame tp11974 ≤ -ep11974 := by
  apply positive_check (eT := (2333219836798658157 / 2000000000000000000)) (y := (19887344969280181237 / 50000000000000000000)) (u := (148846725025216018177 / 100000000000000000000))
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11974, agent11974, tp11974, tm11974, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11974, agent11974, tp11974, tm11974, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]

theorem negative11974 :
    Eminus aL (agent11974.root+dsL) scalar11974.worldRadius world11974.frame
      agent11974.frame tm11974 ≤ -em11974 := by
  apply negative_check (lo := (16785597263017716811 / 25000000000000000000)) (hi := (13428477810414173449 / 20000000000000000000))
    (y := (-((36428766363440925897 / 50000000000000000000)))) (u := (12064901049578371663 / 25000000000000000000))
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11974, agent11974, tp11974, tm11974, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11974, agent11974, tp11974, tm11974, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11974, agent11974, tp11974, tm11974, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]

theorem tails11974 :
    exp (-((11974:ℝ)*ep11974)) ≤ scalar11974.upperTail ∧
    exp (-((11974:ℝ)*em11974)) ≤ scalar11974.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11974:ℝ)) (by norm_num [ep11974]) ?_)
      (show bp11974^8 ≤ scalar11974.upperTail by norm_num [bp11974, scalar11974])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11974, bp11974, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11974:ℝ)) (by norm_num [em11974]) ?_)
      (show bm11974^8 ≤ scalar11974.lowerTail by norm_num [bm11974, scalar11974])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11974, bm11974, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11974 :
    agent11974.root+dsL+scalar11974.worldRadius < √(1/100/aL) ∧
    2*(agent11974.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11974, agent11974, scalar11974, tp11974, tm11974, ep11974, em11974, dsL]

noncomputable def master11974 : MasterCertificate 11974 world11974 agent11974 :=
  master scalar11974 dsL tp11974 tm11974 ep11974 em11974
    (by norm_num [dsL]) (by norm_num [tp11974]) (by norm_num [tm11974])
    (by norm_num [ep11974]) (by norm_num [em11974])
    positive11974 negative11974 tails11974.1 tails11974.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11974.1 tailGuards11974.2

theorem preserves11974 : master11974.toScalarCertificate = scalar11974 := rfl

noncomputable def tp11975 : ℝ := (605484167 / 2500000000)
noncomputable def tm11975 : ℝ := (-((1565171223 / 2500000000)))
noncomputable def ep11975 : ℝ := (28078986061091961 / 50000000000000000000)
noncomputable def em11975 : ℝ := (5407209260929969 / 10000000000000000000)
noncomputable def bp11975 : ℝ := (21572262807867137357 / 50000000000000000000)
noncomputable def bm11975 : ℝ := (1391027450267082399 / 3125000000000000000)

theorem positive11975 :
    Eplus aL (agent11975.root+dsL) scalar11975.worldRadius world11975.frame
      agent11975.frame tp11975 ≤ -ep11975 := by
  apply positive_check (eT := (58330627736309645247 / 50000000000000000000)) (y := (39775308956795654213 / 100000000000000000000)) (u := (148847646416438345717 / 100000000000000000000))
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11975, agent11975, tp11975, tm11975, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11975, agent11975, tp11975, tm11975, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]

theorem negative11975 :
    Eminus aL (agent11975.root+dsL) scalar11975.worldRadius world11975.frame
      agent11975.frame tm11975 ≤ -em11975 := by
  apply negative_check (lo := (839276812603926529 / 1250000000000000000)) (hi := (67142145008314122321 / 100000000000000000000))
    (y := (-((3642857071262393731 / 5000000000000000000)))) (u := (48259793039302734267 / 100000000000000000000))
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11975, agent11975, tp11975, tm11975, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11975, agent11975, tp11975, tm11975, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11975, agent11975, tp11975, tm11975, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]

theorem tails11975 :
    exp (-((11975:ℝ)*ep11975)) ≤ scalar11975.upperTail ∧
    exp (-((11975:ℝ)*em11975)) ≤ scalar11975.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11975:ℝ)) (by norm_num [ep11975]) ?_)
      (show bp11975^8 ≤ scalar11975.upperTail by norm_num [bp11975, scalar11975])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11975, bp11975, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11975:ℝ)) (by norm_num [em11975]) ?_)
      (show bm11975^8 ≤ scalar11975.lowerTail by norm_num [bm11975, scalar11975])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11975, bm11975, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11975 :
    agent11975.root+dsL+scalar11975.worldRadius < √(1/100/aL) ∧
    2*(agent11975.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11975, agent11975, scalar11975, tp11975, tm11975, ep11975, em11975, dsL]

noncomputable def master11975 : MasterCertificate 11975 world11975 agent11975 :=
  master scalar11975 dsL tp11975 tm11975 ep11975 em11975
    (by norm_num [dsL]) (by norm_num [tp11975]) (by norm_num [tm11975])
    (by norm_num [ep11975]) (by norm_num [em11975])
    positive11975 negative11975 tails11975.1 tails11975.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11975.1 tailGuards11975.2

theorem preserves11975 : master11975.toScalarCertificate = scalar11975 := rfl

noncomputable def tp11976 : ℝ := (1211015799 / 5000000000)
noncomputable def tm11976 : ℝ := (-((6260895831 / 10000000000)))
noncomputable def ep11976 : ℝ := (28080379111770237 / 50000000000000000000)
noncomputable def em11976 : ℝ := (10814898880112633 / 20000000000000000000)
noncomputable def bp11976 : ℝ := (8627939556073350951 / 20000000000000000000)
noncomputable def bm11976 : ℝ := (44508269564239638263 / 100000000000000000000)

theorem positive11976 :
    Eplus aL (agent11976.root+dsL) scalar11976.worldRadius world11976.frame
      agent11976.frame tp11976 ≤ -ep11976 := by
  apply positive_check (eT := (14582689863728854823 / 12500000000000000000)) (y := (39775927917194970319 / 100000000000000000000)) (u := (18606070965909531151 / 12500000000000000000))
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11976, agent11976, tp11976, tm11976, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11976, agent11976, tp11976, tm11976, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]

theorem negative11976 :
    Eminus aL (agent11976.root+dsL) scalar11976.worldRadius world11976.frame
      agent11976.frame tm11976 ≤ -em11976 := by
  apply negative_check (lo := (1678547506819322231 / 2500000000000000000)) (hi := (67141900272772889241 / 100000000000000000000))
    (y := (-((14571350525246185929 / 20000000000000000000)))) (u := (24129990336634205013 / 50000000000000000000))
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11976, agent11976, tp11976, tm11976, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11976, agent11976, tp11976, tm11976, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11976, agent11976, tp11976, tm11976, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]

theorem tails11976 :
    exp (-((11976:ℝ)*ep11976)) ≤ scalar11976.upperTail ∧
    exp (-((11976:ℝ)*em11976)) ≤ scalar11976.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11976:ℝ)) (by norm_num [ep11976]) ?_)
      (show bp11976^8 ≤ scalar11976.upperTail by norm_num [bp11976, scalar11976])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11976, bp11976, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11976:ℝ)) (by norm_num [em11976]) ?_)
      (show bm11976^8 ≤ scalar11976.lowerTail by norm_num [bm11976, scalar11976])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11976, bm11976, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11976 :
    agent11976.root+dsL+scalar11976.worldRadius < √(1/100/aL) ∧
    2*(agent11976.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11976, agent11976, scalar11976, tp11976, tm11976, ep11976, em11976, dsL]

noncomputable def master11976 : MasterCertificate 11976 world11976 agent11976 :=
  master scalar11976 dsL tp11976 tm11976 ep11976 em11976
    (by norm_num [dsL]) (by norm_num [tp11976]) (by norm_num [tm11976])
    (by norm_num [ep11976]) (by norm_num [em11976])
    positive11976 negative11976 tails11976.1 tails11976.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11976.1 tailGuards11976.2

theorem preserves11976 : master11976.toScalarCertificate = scalar11976 := rfl

noncomputable def tp11977 : ℝ := (484425297 / 2000000000)
noncomputable def tm11977 : ℝ := (-((3130553199 / 5000000000)))
noncomputable def ep11977 : ℝ := (56163541534553471 / 100000000000000000000)
noncomputable def em11977 : ℝ := (1081537871983861 / 2000000000000000000)
noncomputable def bp11977 : ℝ := (8626974397348165169 / 20000000000000000000)
noncomputable def bm11977 : ℝ := (8900732531463448311 / 20000000000000000000)

theorem positive11977 :
    Eplus aL (agent11977.root+dsL) scalar11977.worldRadius world11977.frame
      agent11977.frame tp11977 ≤ -ep11977 := by
  apply positive_check (eT := (5833089103495759957 / 5000000000000000000)) (y := (9944136735483997951 / 25000000000000000000)) (u := (148849489139589019319 / 100000000000000000000))
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11977, agent11977, tp11977, tm11977, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11977, agent11977, tp11977, tm11977, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]

theorem negative11977 :
    Eminus aL (agent11977.root+dsL) scalar11977.worldRadius world11977.frame
      agent11977.frame tm11977 ≤ -em11977 := by
  apply negative_check (lo := (67141657058383724031 / 100000000000000000000)) (hi := (131136048942155711 / 195312500000000000))
    (y := (-((36428180666834868383 / 50000000000000000000)))) (u := (48260169511352272093 / 100000000000000000000))
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11977, agent11977, tp11977, tm11977, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11977, agent11977, tp11977, tm11977, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11977, agent11977, tp11977, tm11977, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]

theorem tails11977 :
    exp (-((11977:ℝ)*ep11977)) ≤ scalar11977.upperTail ∧
    exp (-((11977:ℝ)*em11977)) ≤ scalar11977.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11977:ℝ)) (by norm_num [ep11977]) ?_)
      (show bp11977^8 ≤ scalar11977.upperTail by norm_num [bp11977, scalar11977])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11977, bp11977, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11977:ℝ)) (by norm_num [em11977]) ?_)
      (show bm11977^8 ≤ scalar11977.lowerTail by norm_num [bm11977, scalar11977])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11977, bm11977, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11977 :
    agent11977.root+dsL+scalar11977.worldRadius < √(1/100/aL) ∧
    2*(agent11977.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11977, agent11977, scalar11977, tp11977, tm11977, ep11977, em11977, dsL]

noncomputable def master11977 : MasterCertificate 11977 world11977 agent11977 :=
  master scalar11977 dsL tp11977 tm11977 ep11977 em11977
    (by norm_num [dsL]) (by norm_num [tp11977]) (by norm_num [tm11977])
    (by norm_num [ep11977]) (by norm_num [em11977])
    positive11977 negative11977 tails11977.1 tails11977.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11977.1 tailGuards11977.2

theorem preserves11977 : master11977.toScalarCertificate = scalar11977 := rfl

noncomputable def tp11978 : ℝ := (2422221289 / 10000000000)
noncomputable def tm11978 : ℝ := (-((1565329249 / 2500000000)))
noncomputable def ep11978 : ℝ := (56166323853027447 / 100000000000000000000)
noncomputable def em11978 : ℝ := (2703964594772743 / 5000000000000000000)
noncomputable def bp11978 : ℝ := (43130047073784848761 / 100000000000000000000)
noncomputable def bm11978 : ℝ := (44499056561549349701 / 100000000000000000000)

theorem positive11978 :
    Eplus aL (agent11978.root+dsL) scalar11978.worldRadius world11978.frame
      agent11978.frame tp11978 ≤ -ep11978 := by
  apply positive_check (eT := (116662044656003355039 / 100000000000000000000)) (y := (19888582421900984357 / 50000000000000000000)) (u := (148850408886201472751 / 100000000000000000000))
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11978, agent11978, tp11978, tm11978, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11978, agent11978, tp11978, tm11978, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]

theorem negative11978 :
    Eminus aL (agent11978.root+dsL) scalar11978.worldRadius world11978.frame
      agent11978.frame tm11978 ≤ -em11978 := by
  apply negative_check (lo := (13428282728693600659 / 20000000000000000000)) (hi := (2098169176358375103 / 3125000000000000000))
    (y := (-((9106996394843403187 / 12500000000000000000)))) (u := (4826035781079861519 / 10000000000000000000))
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11978, agent11978, tp11978, tm11978, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11978, agent11978, tp11978, tm11978, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11978, agent11978, tp11978, tm11978, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]

theorem tails11978 :
    exp (-((11978:ℝ)*ep11978)) ≤ scalar11978.upperTail ∧
    exp (-((11978:ℝ)*em11978)) ≤ scalar11978.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11978:ℝ)) (by norm_num [ep11978]) ?_)
      (show bp11978^8 ≤ scalar11978.upperTail by norm_num [bp11978, scalar11978])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11978, bp11978, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11978:ℝ)) (by norm_num [em11978]) ?_)
      (show bm11978^8 ≤ scalar11978.lowerTail by norm_num [bm11978, scalar11978])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11978, bm11978, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11978 :
    agent11978.root+dsL+scalar11978.worldRadius < √(1/100/aL) ∧
    2*(agent11978.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11978, agent11978, scalar11978, tp11978, tm11978, ep11978, em11978, dsL]

noncomputable def master11978 : MasterCertificate 11978 world11978 agent11978 :=
  master scalar11978 dsL tp11978 tm11978 ep11978 em11978
    (by norm_num [dsL]) (by norm_num [tp11978]) (by norm_num [tm11978])
    (by norm_num [ep11978]) (by norm_num [em11978])
    positive11978 negative11978 tails11978.1 tails11978.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11978.1 tailGuards11978.2

theorem preserves11978 : master11978.toScalarCertificate = scalar11978 := rfl

noncomputable def tp11979 : ℝ := (605579019 / 2500000000)
noncomputable def tm11979 : ℝ := (-((6261527321 / 10000000000)))
noncomputable def ep11979 : ℝ := (87764225835179 / 156250000000000000)
noncomputable def em11979 : ℝ := (13520422169491069 / 25000000000000000000)
noncomputable def bp11979 : ℝ := (8625044691526878261 / 20000000000000000000)
noncomputable def bm11979 : ℝ := (22247225842133716141 / 50000000000000000000)

theorem positive11979 :
    Eplus aL (agent11979.root+dsL) scalar11979.worldRadius world11979.frame
      agent11979.frame tp11979 ≤ -ep11979 := by
  apply positive_check (eT := (2916557678949064017 / 2500000000000000000)) (y := (3977778300516132887 / 10000000000000000000)) (u := (29770265804951284883 / 20000000000000000000))
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11979, agent11979, tp11979, tm11979, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11979, agent11979, tp11979, tm11979, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]

theorem negative11979 :
    Eminus aL (agent11979.root+dsL) scalar11979.worldRadius world11979.frame
      agent11979.frame tm11979 ≤ -em11979 := by
  apply negative_check (lo := (33570585663349836333 / 50000000000000000000)) (hi := (67141171326699672667 / 100000000000000000000))
    (y := (-((72855579388559014517 / 100000000000000000000)))) (u := (603256836010795021 / 1250000000000000000))
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11979, agent11979, tp11979, tm11979, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11979, agent11979, tp11979, tm11979, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11979, agent11979, tp11979, tm11979, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]

theorem tails11979 :
    exp (-((11979:ℝ)*ep11979)) ≤ scalar11979.upperTail ∧
    exp (-((11979:ℝ)*em11979)) ≤ scalar11979.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11979:ℝ)) (by norm_num [ep11979]) ?_)
      (show bp11979^8 ≤ scalar11979.upperTail by norm_num [bp11979, scalar11979])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11979, bp11979, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11979:ℝ)) (by norm_num [em11979]) ?_)
      (show bm11979^8 ≤ scalar11979.lowerTail by norm_num [bm11979, scalar11979])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11979, bm11979, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11979 :
    agent11979.root+dsL+scalar11979.worldRadius < √(1/100/aL) ∧
    2*(agent11979.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11979, agent11979, scalar11979, tp11979, tm11979, ep11979, em11979, dsL]

noncomputable def master11979 : MasterCertificate 11979 world11979 agent11979 :=
  master scalar11979 dsL tp11979 tm11979 ep11979 em11979
    (by norm_num [dsL]) (by norm_num [tp11979]) (by norm_num [tm11979])
    (by norm_num [ep11979]) (by norm_num [em11979])
    positive11979 negative11979 tails11979.1 tails11979.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11979.1 tailGuards11979.2

theorem preserves11979 : master11979.toScalarCertificate = scalar11979 := rfl

noncomputable def tp11980 : ℝ := (2422410841 / 10000000000)
noncomputable def tm11980 : ℝ := (-((3130868771 / 5000000000)))
noncomputable def ep11980 : ℝ := (56171883460492607 / 100000000000000000000)
noncomputable def em11980 : ℝ := (54084083808860393 / 100000000000000000000)
noncomputable def bp11980 : ℝ := (5390050151846608969 / 12500000000000000000)
noncomputable def bm11980 : ℝ := (8897969623458449283 / 20000000000000000000)

theorem positive11980 :
    Eplus aL (agent11980.root+dsL) scalar11980.worldRadius world11980.frame
      agent11980.frame tp11980 ≤ -ep11980 := by
  apply positive_check (eT := (5833128476934982969 / 5000000000000000000)) (y := (19889200695305185311 / 50000000000000000000)) (u := (74426124751280933121 / 50000000000000000000))
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11980, agent11980, tp11980, tm11980, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11980, agent11980, tp11980, tm11980, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]

theorem negative11980 :
    Eminus aL (agent11980.root+dsL) scalar11980.worldRadius world11980.frame
      agent11980.frame tm11980 ≤ -em11980 := by
  apply negative_check (lo := (524538510828724809 / 781250000000000000)) (hi := (67140929386076775553 / 100000000000000000000))
    (y := (-((18213796874884727607 / 25000000000000000000)))) (u := (9652147201803691193 / 20000000000000000000))
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11980, agent11980, tp11980, tm11980, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11980, agent11980, tp11980, tm11980, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11980, agent11980, tp11980, tm11980, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]

theorem tails11980 :
    exp (-((11980:ℝ)*ep11980)) ≤ scalar11980.upperTail ∧
    exp (-((11980:ℝ)*em11980)) ≤ scalar11980.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11980:ℝ)) (by norm_num [ep11980]) ?_)
      (show bp11980^8 ≤ scalar11980.upperTail by norm_num [bp11980, scalar11980])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11980, bp11980, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11980:ℝ)) (by norm_num [em11980]) ?_)
      (show bm11980^8 ≤ scalar11980.lowerTail by norm_num [bm11980, scalar11980])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11980, bm11980, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11980 :
    agent11980.root+dsL+scalar11980.worldRadius < √(1/100/aL) ∧
    2*(agent11980.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11980, agent11980, scalar11980, tp11980, tm11980, ep11980, em11980, dsL]

noncomputable def master11980 : MasterCertificate 11980 world11980 agent11980 :=
  master scalar11980 dsL tp11980 tm11980 ep11980 em11980
    (by norm_num [dsL]) (by norm_num [tp11980]) (by norm_num [tm11980])
    (by norm_num [ep11980]) (by norm_num [em11980])
    positive11980 negative11980 tails11980.1 tails11980.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11980.1 tailGuards11980.2

theorem preserves11980 : master11980.toScalarCertificate = scalar11980 := rfl

noncomputable def tp11981 : ℝ := (302813187 / 1250000000)
noncomputable def tm11981 : ℝ := (-((250477907 / 400000000)))
noncomputable def ep11981 : ℝ := (56174661013923991 / 100000000000000000000)
noncomputable def em11981 : ℝ := (54086477716891699 / 100000000000000000000)
noncomputable def bp11981 : ℝ := (21557790048930769663 / 50000000000000000000)
noncomputable def bm11981 : ℝ := (44485245574949458501 / 100000000000000000000)

theorem positive11981 :
    Eplus aL (agent11981.root+dsL) scalar11981.worldRadius world11981.frame
      agent11981.frame tp11981 ≤ -ep11981 := by
  apply positive_check (eT := (116662831145099362553 / 100000000000000000000)) (y := (39779018172830884553 / 100000000000000000000)) (u := (37213291899900739957 / 25000000000000000000))
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11981, agent11981, tp11981, tm11981, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11981, agent11981, tp11981, tm11981, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]

theorem negative11981 :
    Eminus aL (agent11981.root+dsL) scalar11981.worldRadius world11981.frame
      agent11981.frame tm11981 ≤ -em11981 := by
  apply negative_check (lo := (13428137550641642719 / 20000000000000000000)) (hi := (16785171938302053399 / 25000000000000000000))
    (y := (-((72854795595695455917 / 100000000000000000000)))) (u := (24130462572534185113 / 50000000000000000000))
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11981, agent11981, tp11981, tm11981, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11981, agent11981, tp11981, tm11981, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11981, agent11981, tp11981, tm11981, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]

theorem tails11981 :
    exp (-((11981:ℝ)*ep11981)) ≤ scalar11981.upperTail ∧
    exp (-((11981:ℝ)*em11981)) ≤ scalar11981.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11981:ℝ)) (by norm_num [ep11981]) ?_)
      (show bp11981^8 ≤ scalar11981.upperTail by norm_num [bp11981, scalar11981])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11981, bp11981, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11981:ℝ)) (by norm_num [em11981]) ?_)
      (show bm11981^8 ≤ scalar11981.lowerTail by norm_num [bm11981, scalar11981])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11981, bm11981, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11981 :
    agent11981.root+dsL+scalar11981.worldRadius < √(1/100/aL) ∧
    2*(agent11981.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11981, agent11981, scalar11981, tp11981, tm11981, ep11981, em11981, dsL]

noncomputable def master11981 : MasterCertificate 11981 world11981 agent11981 :=
  master scalar11981 dsL tp11981 tm11981 ep11981 em11981
    (by norm_num [dsL]) (by norm_num [tp11981]) (by norm_num [tm11981])
    (by norm_num [ep11981]) (by norm_num [em11981])
    positive11981 negative11981 tails11981.1 tails11981.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11981.1 tailGuards11981.2

theorem preserves11981 : master11981.toScalarCertificate = scalar11981 := rfl

noncomputable def tp11982 : ℝ := (1211300069 / 5000000000)
noncomputable def tm11982 : ℝ := (-((782769709 / 1250000000)))
noncomputable def ep11982 : ℝ := (56177436770376651 / 100000000000000000000)
noncomputable def em11982 : ℝ := (10817773989323667 / 20000000000000000000)
noncomputable def bp11982 : ℝ := (43110760380917328973 / 100000000000000000000)
noncomputable def bm11982 : ℝ := (5560080545080206589 / 12500000000000000000)

theorem positive11982 :
    Eplus aL (agent11982.root+dsL) scalar11982.worldRadius world11982.frame
      agent11982.frame tp11982 ≤ -ep11982 := by
  apply positive_check (eT := (11666309269708620469 / 10000000000000000000)) (y := (39779635445542847759 / 100000000000000000000)) (u := (595416345729693177 / 400000000000000000))
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11982, agent11982, tp11982, tm11982, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11982, agent11982, tp11982, tm11982, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]

theorem negative11982 :
    Eminus aL (agent11982.root+dsL) scalar11982.worldRadius world11982.frame
      agent11982.frame tm11982 ≤ -em11982 := by
  apply negative_check (lo := (8392555829144856271 / 12500000000000000000)) (hi := (67140446633158850169 / 100000000000000000000))
    (y := (-((14570880737499973917 / 20000000000000000000)))) (u := (482611142839599047 / 1000000000000000000))
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11982, agent11982, tp11982, tm11982, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11982, agent11982, tp11982, tm11982, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11982, agent11982, tp11982, tm11982, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]

theorem tails11982 :
    exp (-((11982:ℝ)*ep11982)) ≤ scalar11982.upperTail ∧
    exp (-((11982:ℝ)*em11982)) ≤ scalar11982.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11982:ℝ)) (by norm_num [ep11982]) ?_)
      (show bp11982^8 ≤ scalar11982.upperTail by norm_num [bp11982, scalar11982])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11982, bp11982, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11982:ℝ)) (by norm_num [em11982]) ?_)
      (show bm11982^8 ≤ scalar11982.lowerTail by norm_num [bm11982, scalar11982])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11982, bm11982, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11982 :
    agent11982.root+dsL+scalar11982.worldRadius < √(1/100/aL) ∧
    2*(agent11982.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11982, agent11982, scalar11982, tp11982, tm11982, ep11982, em11982, dsL]

noncomputable def master11982 : MasterCertificate 11982 world11982 agent11982 :=
  master scalar11982 dsL tp11982 tm11982 ep11982 em11982
    (by norm_num [dsL]) (by norm_num [tp11982]) (by norm_num [tm11982])
    (by norm_num [ep11982]) (by norm_num [em11982])
    positive11982 negative11982 tails11982.1 tails11982.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11982.1 tailGuards11982.2

theorem preserves11982 : master11982.toScalarCertificate = scalar11982 := rfl

noncomputable def tp11983 : ℝ := (2422694743 / 10000000000)
noncomputable def tm11983 : ℝ := (-((6262367713 / 10000000000)))
noncomputable def ep11983 : ℝ := (14045052722541467 / 25000000000000000000)
noncomputable def em11983 : ℝ := (2163650426523567 / 4000000000000000000)
noncomputable def bp11983 : ℝ := (43105941960370459383 / 100000000000000000000)
noncomputable def bm11983 : ℝ := (4447604436438032197 / 10000000000000000000)

theorem positive11983 :
    Eplus aL (agent11983.root+dsL) scalar11983.worldRadius world11983.frame
      agent11983.frame tp11983 ≤ -ep11983 := by
  apply positive_check (eT := (116663354016555914851 / 100000000000000000000)) (y := (19890126311226696677 / 50000000000000000000)) (u := (116292972756492301 / 78125000000000000))
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11983, agent11983, tp11983, tm11983, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11983, agent11983, tp11983, tm11983, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]

theorem negative11983 :
    Eminus aL (agent11983.root+dsL) scalar11983.worldRadius world11983.frame
      agent11983.frame tm11983 ≤ -em11983 := by
  apply negative_check (lo := (67140205257053950531 / 100000000000000000000)) (hi := (16785051314263487633 / 25000000000000000000))
    (y := (-((36427006592288225997 / 50000000000000000000)))) (u := (24130651372695015463 / 50000000000000000000))
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world11983, agent11983, tp11983, tm11983, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11983, agent11983, tp11983, tm11983, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world11983, agent11983, tp11983, tm11983, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]

theorem tails11983 :
    exp (-((11983:ℝ)*ep11983)) ≤ scalar11983.upperTail ∧
    exp (-((11983:ℝ)*em11983)) ≤ scalar11983.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (11983:ℝ)) (by norm_num [ep11983]) ?_)
      (show bp11983^8 ≤ scalar11983.upperTail by norm_num [bp11983, scalar11983])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep11983, bp11983, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (11983:ℝ)) (by norm_num [em11983]) ?_)
      (show bm11983^8 ≤ scalar11983.lowerTail by norm_num [bm11983, scalar11983])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em11983, bm11983, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards11983 :
    agent11983.root+dsL+scalar11983.worldRadius < √(1/100/aL) ∧
    2*(agent11983.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]
  · apply le_trans _ x0_lo
    norm_num [world11983, agent11983, scalar11983, tp11983, tm11983, ep11983, em11983, dsL]

noncomputable def master11983 : MasterCertificate 11983 world11983 agent11983 :=
  master scalar11983 dsL tp11983 tm11983 ep11983 em11983
    (by norm_num [dsL]) (by norm_num [tp11983]) (by norm_num [tm11983])
    (by norm_num [ep11983]) (by norm_num [em11983])
    positive11983 negative11983 tails11983.1 tails11983.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards11983.1 tailGuards11983.2

theorem preserves11983 : master11983.toScalarCertificate = scalar11983 := rfl

end BstLean.Part281
