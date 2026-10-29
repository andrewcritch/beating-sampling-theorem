import BstLean.Part261Checker
import BstLean.Part268Scalar3
namespace BstLean.Part268
open Real BstLean.Part156 BstLean.Part160 BstLean.Part192 BstLean.Part196
open BstLean.Part261
noncomputable def tp12425 : ℝ := (228964339 / 1000000000)
noncomputable def tm12425 : ℝ := (-((6003199231 / 10000000000)))
noncomputable def ep12425 : ℝ := (10123861184428199 / 20000000000000000000)
noncomputable def em12425 : ℝ := (12351675157505437 / 25000000000000000000)
noncomputable def bp12425 : ℝ := (22779064952718335941 / 50000000000000000000)
noncomputable def bm12425 : ℝ := (11606067314296051483 / 25000000000000000000)

theorem positive12425 :
    Eplus aL (agent12425.root+dsL) scalar12425.worldRadius world12425.frame
      agent12425.frame tp12425 ≤ -ep12425 := by
  apply positive_check (eT := (11550429665430839547 / 10000000000000000000)) (y := (9412486429129873363 / 25000000000000000000)) (u := (145717474841882456173 / 100000000000000000000))
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12425, agent12425, tp12425, tm12425, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12425, agent12425, tp12425, tm12425, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]

theorem negative12425 :
    Eminus aL (agent12425.root+dsL) scalar12425.worldRadius world12425.frame
      agent12425.frame tm12425 ≤ -em12425 := by
  apply negative_check (lo := (685290001775729199 / 1000000000000000000)) (hi := (68529000177572919901 / 100000000000000000000))
    (y := (-((1792653100747543023 / 2500000000000000000)))) (u := (122046201951492517 / 250000000000000000))
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12425, agent12425, tp12425, tm12425, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12425, agent12425, tp12425, tm12425, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12425, agent12425, tp12425, tm12425, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]

theorem tails12425 :
    exp (-((12425:ℝ)*ep12425)) ≤ scalar12425.upperTail ∧
    exp (-((12425:ℝ)*em12425)) ≤ scalar12425.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12425:ℝ)) (by norm_num [ep12425]) ?_)
      (show bp12425^8 ≤ scalar12425.upperTail by norm_num [bp12425, scalar12425])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12425, bp12425, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12425:ℝ)) (by norm_num [em12425]) ?_)
      (show bm12425^8 ≤ scalar12425.lowerTail by norm_num [bm12425, scalar12425])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12425, bm12425, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12425 :
    agent12425.root+dsL+scalar12425.worldRadius < √(1/100/aL) ∧
    2*(agent12425.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12425, agent12425, scalar12425, tp12425, tm12425, ep12425, em12425, dsL]

noncomputable def master12425 : MasterCertificate 12425 world12425 agent12425 :=
  master scalar12425 dsL tp12425 tm12425 ep12425 em12425
    (by norm_num [dsL]) (by norm_num [tp12425]) (by norm_num [tm12425])
    (by norm_num [ep12425]) (by norm_num [em12425])
    positive12425 negative12425 tails12425.1 tails12425.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12425.1 tailGuards12425.2

theorem preserves12425 : master12425.toScalarCertificate = scalar12425 := rfl

noncomputable def tp12426 : ℝ := (457947673 / 2000000000)
noncomputable def tm12426 : ℝ := (-((1500851297 / 2500000000)))
noncomputable def ep12426 : ℝ := (25311129016084941 / 50000000000000000000)
noncomputable def em12426 : ℝ := (49409253698713937 / 100000000000000000000)
noncomputable def bp12426 : ℝ := (45553158519057274243 / 100000000000000000000)
noncomputable def bm12426 : ℝ := (9283912285799988489 / 20000000000000000000)

theorem positive12426 :
    Eplus aL (agent12426.root+dsL) scalar12426.worldRadius world12426.frame
      agent12426.frame tp12426 ≤ -ep12426 := by
  apply positive_check (eT := (28876151102127009891 / 25000000000000000000)) (y := (37650838354675594797 / 100000000000000000000)) (u := (18214846947183553079 / 12500000000000000000))
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12426, agent12426, tp12426, tm12426, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12426, agent12426, tp12426, tm12426, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]

theorem negative12426 :
    Eminus aL (agent12426.root+dsL) scalar12426.worldRadius world12426.frame
      agent12426.frame tm12426 ≤ -em12426 := by
  apply negative_check (lo := (34264353595053780367 / 50000000000000000000)) (hi := (13705741438021512147 / 20000000000000000000))
    (y := (-((71706308068197573801 / 100000000000000000000)))) (u := (61022988669974489 / 125000000000000000))
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12426, agent12426, tp12426, tm12426, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12426, agent12426, tp12426, tm12426, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12426, agent12426, tp12426, tm12426, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]

theorem tails12426 :
    exp (-((12426:ℝ)*ep12426)) ≤ scalar12426.upperTail ∧
    exp (-((12426:ℝ)*em12426)) ≤ scalar12426.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12426:ℝ)) (by norm_num [ep12426]) ?_)
      (show bp12426^8 ≤ scalar12426.upperTail by norm_num [bp12426, scalar12426])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12426, bp12426, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12426:ℝ)) (by norm_num [em12426]) ?_)
      (show bm12426^8 ≤ scalar12426.lowerTail by norm_num [bm12426, scalar12426])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12426, bm12426, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12426 :
    agent12426.root+dsL+scalar12426.worldRadius < √(1/100/aL) ∧
    2*(agent12426.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12426, agent12426, scalar12426, tp12426, tm12426, ep12426, em12426, dsL]

noncomputable def master12426 : MasterCertificate 12426 world12426 agent12426 :=
  master scalar12426 dsL tp12426 tm12426 ep12426 em12426
    (by norm_num [dsL]) (by norm_num [tp12426]) (by norm_num [tm12426])
    (by norm_num [ep12426]) (by norm_num [em12426])
    positive12426 negative12426 tails12426.1 tails12426.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12426.1 tailGuards12426.2

theorem preserves12426 : master12426.toScalarCertificate = scalar12426 := rfl

noncomputable def tp12427 : ℝ := (457966661 / 2000000000)
noncomputable def tm12427 : ℝ := (-((240144433 / 400000000)))
noncomputable def ep12427 : ℝ := (50625208140821333 / 100000000000000000000)
noncomputable def em12427 : ℝ := (24705902451694549 / 50000000000000000000)
noncomputable def bp12427 : ℝ := (22774094377524702207 / 50000000000000000000)
noncomputable def bm12427 : ℝ := (5801856890741274153 / 12500000000000000000)

theorem positive12427 :
    Eplus aL (agent12427.root+dsL) scalar12427.worldRadius world12427.frame
      agent12427.frame tp12427 ≤ -ep12427 := by
  apply positive_check (eT := (115504911940366728009 / 100000000000000000000)) (y := (18825865475477813229 / 50000000000000000000)) (u := (145720076263643466371 / 100000000000000000000))
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12427, agent12427, tp12427, tm12427, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12427, agent12427, tp12427, tm12427, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]

theorem negative12427 :
    Eminus aL (agent12427.root+dsL) scalar12427.worldRadius world12427.frame
      agent12427.frame tm12427 ≤ -em12427 := by
  apply negative_check (lo := (34264207763523860877 / 50000000000000000000)) (hi := (13705683105409544351 / 20000000000000000000))
    (y := (-((35853244898401581529 / 50000000000000000000)))) (u := (976366044381581683 / 2000000000000000000))
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12427, agent12427, tp12427, tm12427, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12427, agent12427, tp12427, tm12427, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12427, agent12427, tp12427, tm12427, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]

theorem tails12427 :
    exp (-((12427:ℝ)*ep12427)) ≤ scalar12427.upperTail ∧
    exp (-((12427:ℝ)*em12427)) ≤ scalar12427.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12427:ℝ)) (by norm_num [ep12427]) ?_)
      (show bp12427^8 ≤ scalar12427.upperTail by norm_num [bp12427, scalar12427])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12427, bp12427, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12427:ℝ)) (by norm_num [em12427]) ?_)
      (show bm12427^8 ≤ scalar12427.lowerTail by norm_num [bm12427, scalar12427])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12427, bm12427, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12427 :
    agent12427.root+dsL+scalar12427.worldRadius < √(1/100/aL) ∧
    2*(agent12427.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12427, agent12427, scalar12427, tp12427, tm12427, ep12427, em12427, dsL]

noncomputable def master12427 : MasterCertificate 12427 world12427 agent12427 :=
  master scalar12427 dsL tp12427 tm12427 ep12427 em12427
    (by norm_num [dsL]) (by norm_num [tp12427]) (by norm_num [tm12427])
    (by norm_num [ep12427]) (by norm_num [em12427])
    positive12427 negative12427 tails12427.1 tails12427.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12427.1 tailGuards12427.2

theorem preserves12427 : master12427.toScalarCertificate = scalar12427 := rfl

noncomputable def tp12428 : ℝ := (2236258 / 9765625)
noncomputable def tm12428 : ℝ := (-((300190823 / 500000000)))
noncomputable def ep12428 : ℝ := (1582129922254981 / 3125000000000000000)
noncomputable def em12428 : ℝ := (49414355389392901 / 100000000000000000000)
noncomputable def bp12428 : ℝ := (45543219718999320877 / 100000000000000000000)
noncomputable def bm12428 : ℝ := (46410149522159042837 / 100000000000000000000)

theorem positive12428 :
    Eplus aL (agent12428.root+dsL) scalar12428.worldRadius world12428.frame
      agent12428.frame tp12428 ≤ -ep12428 := by
  apply positive_check (eT := (115505219119007613413 / 100000000000000000000)) (y := (9413155772746432373 / 25000000000000000000)) (u := (145721376296574759473 / 100000000000000000000))
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12428, agent12428, tp12428, tm12428, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12428, agent12428, tp12428, tm12428, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]

theorem negative12428 :
    Eminus aL (agent12428.root+dsL) scalar12428.worldRadius world12428.frame
      agent12428.frame tm12428 ≤ -em12428 := by
  apply negative_check (lo := (68528123816561362917 / 100000000000000000000)) (hi := (34264061908280681459 / 50000000000000000000))
    (y := (-((71706672600994698837 / 100000000000000000000)))) (u := (48818212977257959989 / 100000000000000000000))
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12428, agent12428, tp12428, tm12428, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12428, agent12428, tp12428, tm12428, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12428, agent12428, tp12428, tm12428, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]

theorem tails12428 :
    exp (-((12428:ℝ)*ep12428)) ≤ scalar12428.upperTail ∧
    exp (-((12428:ℝ)*em12428)) ≤ scalar12428.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12428:ℝ)) (by norm_num [ep12428]) ?_)
      (show bp12428^8 ≤ scalar12428.upperTail by norm_num [bp12428, scalar12428])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12428, bp12428, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12428:ℝ)) (by norm_num [em12428]) ?_)
      (show bm12428^8 ≤ scalar12428.lowerTail by norm_num [bm12428, scalar12428])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12428, bm12428, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12428 :
    agent12428.root+dsL+scalar12428.worldRadius < √(1/100/aL) ∧
    2*(agent12428.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12428, agent12428, scalar12428, tp12428, tm12428, ep12428, em12428, dsL]

noncomputable def master12428 : MasterCertificate 12428 world12428 agent12428 :=
  master scalar12428 dsL tp12428 tm12428 ep12428 em12428
    (by norm_num [dsL]) (by norm_num [tp12428]) (by norm_num [tm12428])
    (by norm_num [ep12428]) (by norm_num [em12428])
    positive12428 negative12428 tails12428.1 tails12428.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12428.1 tailGuards12428.2

theorem preserves12428 : master12428.toScalarCertificate = scalar12428 := rfl

noncomputable def tp12429 : ℝ := (91600921 / 400000000)
noncomputable def tm12429 : ℝ := (-((6004022011 / 10000000000)))
noncomputable def ep12429 : ℝ := (25315552515251519 / 50000000000000000000)
noncomputable def em12429 : ℝ := (24708452085614113 / 50000000000000000000)
noncomputable def bp12429 : ℝ := (4553825220025023761 / 10000000000000000000)
noncomputable def bm12429 : ℝ := (11601361332051529109 / 25000000000000000000)

theorem positive12429 :
    Eplus aL (agent12429.root+dsL) scalar12429.worldRadius world12429.frame
      agent12429.frame tp12429 ≤ -ep12429 := by
  apply positive_check (eT := (115505525937191656417 / 100000000000000000000)) (y := (37653514803658205339 / 100000000000000000000)) (u := (72861337859173623971 / 50000000000000000000))
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12429, agent12429, tp12429, tm12429, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12429, agent12429, tp12429, tm12429, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]

theorem negative12429 :
    Eminus aL (agent12429.root+dsL) scalar12429.worldRadius world12429.frame
      agent12429.frame tm12429 ≤ -em12429 := by
  apply negative_check (lo := (8565979051543842699 / 12500000000000000000)) (hi := (68527832412350741593 / 100000000000000000000))
    (y := (-((35853427769723946847 / 50000000000000000000)))) (u := (24409061835027975327 / 50000000000000000000))
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12429, agent12429, tp12429, tm12429, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12429, agent12429, tp12429, tm12429, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12429, agent12429, tp12429, tm12429, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]

theorem tails12429 :
    exp (-((12429:ℝ)*ep12429)) ≤ scalar12429.upperTail ∧
    exp (-((12429:ℝ)*em12429)) ≤ scalar12429.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12429:ℝ)) (by norm_num [ep12429]) ?_)
      (show bp12429^8 ≤ scalar12429.upperTail by norm_num [bp12429, scalar12429])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12429, bp12429, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12429:ℝ)) (by norm_num [em12429]) ?_)
      (show bm12429^8 ≤ scalar12429.lowerTail by norm_num [bm12429, scalar12429])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12429, bm12429, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12429 :
    agent12429.root+dsL+scalar12429.worldRadius < √(1/100/aL) ∧
    2*(agent12429.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12429, agent12429, scalar12429, tp12429, tm12429, ep12429, em12429, dsL]

noncomputable def master12429 : MasterCertificate 12429 world12429 agent12429 :=
  master scalar12429 dsL tp12429 tm12429 ep12429 em12429
    (by norm_num [dsL]) (by norm_num [tp12429]) (by norm_num [tm12429])
    (by norm_num [ep12429]) (by norm_num [em12429])
    positive12429 negative12429 tails12429.1 tails12429.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12429.1 tailGuards12429.2

theorem preserves12429 : master12429.toScalarCertificate = scalar12429 := rfl

noncomputable def tp12430 : ℝ := (2290194661 / 10000000000)
noncomputable def tm12430 : ℝ := (-((6004459119 / 10000000000)))
noncomputable def ep12430 : ℝ := (50635530331405099 / 100000000000000000000)
noncomputable def em12430 : ℝ := (9884212051152853 / 20000000000000000000)
noncomputable def bp12430 : ℝ := (22766119703963519481 / 50000000000000000000)
noncomputable def bm12430 : ℝ := (46399582542560154159 / 100000000000000000000)

theorem positive12430 :
    Eplus aL (agent12430.root+dsL) scalar12430.worldRadius world12430.frame
      agent12430.frame tp12430 ≤ -ep12430 := by
  apply positive_check (eT := (115506391183766895357 / 100000000000000000000)) (y := (37653673594984543223 / 100000000000000000000)) (u := (145722907113500513827 / 100000000000000000000))
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12430, agent12430, tp12430, tm12430, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12430, agent12430, tp12430, tm12430, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]

theorem negative12430 :
    Eminus aL (agent12430.root+dsL) scalar12430.worldRadius world12430.frame
      agent12430.frame tm12430 ≤ -em12430 := by
  apply negative_check (lo := (8565817768810156349 / 12500000000000000000)) (hi := (68526542150481250793 / 100000000000000000000))
    (y := (-((8963137034836918183 / 12500000000000000000)))) (u := (48818982515700453429 / 100000000000000000000))
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12430, agent12430, tp12430, tm12430, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12430, agent12430, tp12430, tm12430, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12430, agent12430, tp12430, tm12430, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]

theorem tails12430 :
    exp (-((12430:ℝ)*ep12430)) ≤ scalar12430.upperTail ∧
    exp (-((12430:ℝ)*em12430)) ≤ scalar12430.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12430:ℝ)) (by norm_num [ep12430]) ?_)
      (show bp12430^8 ≤ scalar12430.upperTail by norm_num [bp12430, scalar12430])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12430, bp12430, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12430:ℝ)) (by norm_num [em12430]) ?_)
      (show bm12430^8 ≤ scalar12430.lowerTail by norm_num [bm12430, scalar12430])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12430, bm12430, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12430 :
    agent12430.root+dsL+scalar12430.worldRadius < √(1/100/aL) ∧
    2*(agent12430.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12430, agent12430, scalar12430, tp12430, tm12430, ep12430, em12430, dsL]

noncomputable def master12430 : MasterCertificate 12430 world12430 agent12430 :=
  master scalar12430 dsL tp12430 tm12430 ep12430 em12430
    (by norm_num [dsL]) (by norm_num [tp12430]) (by norm_num [tm12430])
    (by norm_num [ep12430]) (by norm_num [em12430])
    positive12430 negative12430 tails12430.1 tails12430.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12430.1 tailGuards12430.2

theorem preserves12430 : master12430.toScalarCertificate = scalar12430 := rfl

noncomputable def tp12431 : ℝ := (572572337 / 2500000000)
noncomputable def tm12431 : ℝ := (-((3002332211 / 5000000000)))
noncomputable def ep12431 : ℝ := (25319237058928677 / 50000000000000000000)
noncomputable def em12431 : ℝ := (24711802791223041 / 50000000000000000000)
noncomputable def bp12431 : ℝ := (9105454994369101337 / 20000000000000000000)
noncomputable def bm12431 : ℝ := (23197440613054350949 / 50000000000000000000)

theorem positive12431 :
    Eplus aL (agent12431.root+dsL) scalar12431.worldRadius world12431.frame
      agent12431.frame tp12431 ≤ -ep12431 := by
  apply positive_check (eT := (115506696993421005447 / 100000000000000000000)) (y := (294176278382358367 / 781250000000000000)) (u := (72862102054229105299 / 50000000000000000000))
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12431, agent12431, tp12431, tm12431, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12431, agent12431, tp12431, tm12431, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]

theorem negative12431 :
    Eminus aL (agent12431.root+dsL) scalar12431.worldRadius world12431.frame
      agent12431.frame tm12431 ≤ -em12431 := by
  apply negative_check (lo := (8565781466386013557 / 12500000000000000000)) (hi := (68526251731088108457 / 100000000000000000000))
    (y := (-((71705278025285960851 / 100000000000000000000)))) (u := (48818893788944786973 / 100000000000000000000))
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12431, agent12431, tp12431, tm12431, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12431, agent12431, tp12431, tm12431, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12431, agent12431, tp12431, tm12431, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]

theorem tails12431 :
    exp (-((12431:ℝ)*ep12431)) ≤ scalar12431.upperTail ∧
    exp (-((12431:ℝ)*em12431)) ≤ scalar12431.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12431:ℝ)) (by norm_num [ep12431]) ?_)
      (show bp12431^8 ≤ scalar12431.upperTail by norm_num [bp12431, scalar12431])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12431, bp12431, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12431:ℝ)) (by norm_num [em12431]) ?_)
      (show bm12431^8 ≤ scalar12431.lowerTail by norm_num [bm12431, scalar12431])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12431, bm12431, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12431 :
    agent12431.root+dsL+scalar12431.worldRadius < √(1/100/aL) ∧
    2*(agent12431.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12431, agent12431, scalar12431, tp12431, tm12431, ep12431, em12431, dsL]

noncomputable def master12431 : MasterCertificate 12431 world12431 agent12431 :=
  master scalar12431 dsL tp12431 tm12431 ep12431 em12431
    (by norm_num [dsL]) (by norm_num [tp12431]) (by norm_num [tm12431])
    (by norm_num [ep12431]) (by norm_num [em12431])
    positive12431 negative12431 tails12431.1 tails12431.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12431.1 tailGuards12431.2

theorem preserves12431 : master12431.toScalarCertificate = scalar12431 := rfl

noncomputable def tp12432 : ℝ := (2290384091 / 10000000000)
noncomputable def tm12432 : ℝ := (-((6004869449 / 10000000000)))
noncomputable def ep12432 : ℝ := (25320708891564401 / 50000000000000000000)
noncomputable def em12432 : ℝ := (2471307538837587 / 5000000000000000000)
noncomputable def bp12432 : ℝ := (45522310827747970613 / 100000000000000000000)
noncomputable def bm12432 : ℝ := (2899386261640054247 / 6250000000000000000)

theorem positive12432 :
    Eplus aL (agent12432.root+dsL) scalar12432.worldRadius world12432.frame
      agent12432.frame tp12432 ≤ -ep12432 := by
  apply positive_check (eT := (57753501621198729007 / 50000000000000000000)) (y := (470693186726308041 / 1250000000000000000)) (u := (72862751480800601049 / 50000000000000000000))
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12432, agent12432, tp12432, tm12432, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12432, agent12432, tp12432, tm12432, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]

theorem negative12432 :
    Eminus aL (agent12432.root+dsL) scalar12432.worldRadius world12432.frame
      agent12432.frame tm12432 ≤ -em12432 := by
  apply negative_check (lo := (13705192489206742657 / 20000000000000000000)) (hi := (34262981223016856643 / 50000000000000000000))
    (y := (-((71705457993115233079 / 100000000000000000000)))) (u := (12204701482680104647 / 25000000000000000000))
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12432, agent12432, tp12432, tm12432, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12432, agent12432, tp12432, tm12432, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12432, agent12432, tp12432, tm12432, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]

theorem tails12432 :
    exp (-((12432:ℝ)*ep12432)) ≤ scalar12432.upperTail ∧
    exp (-((12432:ℝ)*em12432)) ≤ scalar12432.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12432:ℝ)) (by norm_num [ep12432]) ?_)
      (show bp12432^8 ≤ scalar12432.upperTail by norm_num [bp12432, scalar12432])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12432, bp12432, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12432:ℝ)) (by norm_num [em12432]) ?_)
      (show bm12432^8 ≤ scalar12432.lowerTail by norm_num [bm12432, scalar12432])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12432, bm12432, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12432 :
    agent12432.root+dsL+scalar12432.worldRadius < √(1/100/aL) ∧
    2*(agent12432.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12432, agent12432, scalar12432, tp12432, tm12432, ep12432, em12432, dsL]

noncomputable def master12432 : MasterCertificate 12432 world12432 agent12432 :=
  master scalar12432 dsL tp12432 tm12432 ep12432 em12432
    (by norm_num [dsL]) (by norm_num [tp12432]) (by norm_num [tm12432])
    (by norm_num [ep12432]) (by norm_num [em12432])
    positive12432 negative12432 tails12432.1 tails12432.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12432.1 tailGuards12432.2

theorem preserves12432 : master12432.toScalarCertificate = scalar12432 := rfl

noncomputable def tp12433 : ℝ := (57261969 / 250000000)
noncomputable def tm12433 : ℝ := (-((6005074427 / 10000000000)))
noncomputable def ep12433 : ℝ := (3165272436525711 / 6250000000000000000)
noncomputable def em12433 : ℝ := (6178586710681049 / 12500000000000000000)
noncomputable def bp12433 : ℝ := (45517348632971829189 / 100000000000000000000)
noncomputable def bm12433 : ℝ := (9277096195046519999 / 20000000000000000000)

theorem positive12433 :
    Eplus aL (agent12433.root+dsL) scalar12433.worldRadius world12433.frame
      agent12433.frame tp12433 ≤ -ep12433 := by
  apply positive_check (eT := (115507308985516845773 / 100000000000000000000)) (y := (37656345661978025611 / 100000000000000000000)) (u := (9107925061201659713 / 6250000000000000000))
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12433, agent12433, tp12433, tm12433, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12433, agent12433, tp12433, tm12433, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]

theorem negative12433 :
    Eminus aL (agent12433.root+dsL) scalar12433.worldRadius world12433.frame
      agent12433.frame tm12433 ≤ -em12433 := by
  apply negative_check (lo := (17131418329058883587 / 25000000000000000000)) (hi := (68525673316235534349 / 100000000000000000000))
    (y := (-((2868225543893539327 / 4000000000000000000)))) (u := (48818717761974785701 / 100000000000000000000))
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12433, agent12433, tp12433, tm12433, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12433, agent12433, tp12433, tm12433, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12433, agent12433, tp12433, tm12433, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]

theorem tails12433 :
    exp (-((12433:ℝ)*ep12433)) ≤ scalar12433.upperTail ∧
    exp (-((12433:ℝ)*em12433)) ≤ scalar12433.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12433:ℝ)) (by norm_num [ep12433]) ?_)
      (show bp12433^8 ≤ scalar12433.upperTail by norm_num [bp12433, scalar12433])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12433, bp12433, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12433:ℝ)) (by norm_num [em12433]) ?_)
      (show bm12433^8 ≤ scalar12433.lowerTail by norm_num [bm12433, scalar12433])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12433, bm12433, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12433 :
    agent12433.root+dsL+scalar12433.worldRadius < √(1/100/aL) ∧
    2*(agent12433.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12433, agent12433, scalar12433, tp12433, tm12433, ep12433, em12433, dsL]

noncomputable def master12433 : MasterCertificate 12433 world12433 agent12433 :=
  master scalar12433 dsL tp12433 tm12433 ep12433 em12433
    (by norm_num [dsL]) (by norm_num [tp12433]) (by norm_num [tm12433])
    (by norm_num [ep12433]) (by norm_num [em12433])
    positive12433 negative12433 tails12433.1 tails12433.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12433.1 tailGuards12433.2

theorem preserves12433 : master12433.toScalarCertificate = scalar12433 := rfl

noncomputable def tp12434 : ℝ := (572643347 / 2500000000)
noncomputable def tm12434 : ℝ := (-((3002639703 / 5000000000)))
noncomputable def ep12434 : ℝ := (12661824817819497 / 25000000000000000000)
noncomputable def em12434 : ℝ := (49431235751614317 / 100000000000000000000)
noncomputable def bp12434 : ℝ := (45512387291287005873 / 100000000000000000000)
noncomputable def bm12434 : ℝ := (1159519563818637787 / 2500000000000000000)

theorem positive12434 :
    Eplus aL (agent12434.root+dsL) scalar12434.worldRadius world12434.frame
      agent12434.frame tp12434 ≤ -ep12434 := by
  apply positive_check (eT := (115507614462754084373 / 100000000000000000000)) (y := (37657235987810673829 / 100000000000000000000)) (u := (145728098428356519133 / 100000000000000000000))
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12434, agent12434, tp12434, tm12434, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12434, agent12434, tp12434, tm12434, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]

theorem negative12434 :
    Eminus aL (agent12434.root+dsL) scalar12434.worldRadius world12434.frame
      agent12434.frame tm12434 ≤ -em12434 := by
  apply negative_check (lo := (68525384125980109427 / 100000000000000000000)) (hi := (17131346031495027357 / 25000000000000000000))
    (y := (-((7170582001219093823 / 10000000000000000000)))) (u := (48818629197650321809 / 100000000000000000000))
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12434, agent12434, tp12434, tm12434, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12434, agent12434, tp12434, tm12434, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12434, agent12434, tp12434, tm12434, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]

theorem tails12434 :
    exp (-((12434:ℝ)*ep12434)) ≤ scalar12434.upperTail ∧
    exp (-((12434:ℝ)*em12434)) ≤ scalar12434.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12434:ℝ)) (by norm_num [ep12434]) ?_)
      (show bp12434^8 ≤ scalar12434.upperTail by norm_num [bp12434, scalar12434])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12434, bp12434, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12434:ℝ)) (by norm_num [em12434]) ?_)
      (show bm12434^8 ≤ scalar12434.lowerTail by norm_num [bm12434, scalar12434])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12434, bm12434, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12434 :
    agent12434.root+dsL+scalar12434.worldRadius < √(1/100/aL) ∧
    2*(agent12434.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12434, agent12434, scalar12434, tp12434, tm12434, ep12434, em12434, dsL]

noncomputable def master12434 : MasterCertificate 12434 world12434 agent12434 :=
  master scalar12434 dsL tp12434 tm12434 ep12434 em12434
    (by norm_num [dsL]) (by norm_num [tp12434]) (by norm_num [tm12434])
    (by norm_num [ep12434]) (by norm_num [em12434])
    positive12434 negative12434 tails12434.1 tails12434.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12434.1 tailGuards12434.2

theorem preserves12434 : master12434.toScalarCertificate = scalar12434 := rfl

noncomputable def tp12435 : ℝ := (2290667921 / 10000000000)
noncomputable def tm12435 : ℝ := (-((93835691 / 156250000)))
noncomputable def ep12435 : ℝ := (10130047541331557 / 20000000000000000000)
noncomputable def em12435 : ℝ := (49433776109157449 / 100000000000000000000)
noncomputable def bp12435 : ℝ := (45507427465531259679 / 100000000000000000000)
noncomputable def bm12435 : ℝ := (23188042771556289637 / 50000000000000000000)

theorem positive12435 :
    Eplus aL (agent12435.root+dsL) scalar12435.worldRadius world12435.frame
      agent12435.frame tp12435 ≤ -ep12435 := by
  apply positive_check (eT := (115507919281540858927 / 100000000000000000000)) (y := (7531625011869296051 / 20000000000000000000)) (u := (29145878812231772063 / 20000000000000000000))
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12435, agent12435, tp12435, tm12435, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12435, agent12435, tp12435, tm12435, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]

theorem negative12435 :
    Eminus aL (agent12435.root+dsL) scalar12435.worldRadius world12435.frame
      agent12435.frame tm12435 ≤ -em12435 := by
  apply negative_check (lo := (34262547786986454867 / 50000000000000000000)) (hi := (13705019114794581947 / 20000000000000000000))
    (y := (-((71706000388562368813 / 100000000000000000000)))) (u := (1525579410639306567 / 3125000000000000000))
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12435, agent12435, tp12435, tm12435, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12435, agent12435, tp12435, tm12435, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12435, agent12435, tp12435, tm12435, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]

theorem tails12435 :
    exp (-((12435:ℝ)*ep12435)) ≤ scalar12435.upperTail ∧
    exp (-((12435:ℝ)*em12435)) ≤ scalar12435.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12435:ℝ)) (by norm_num [ep12435]) ?_)
      (show bp12435^8 ≤ scalar12435.upperTail by norm_num [bp12435, scalar12435])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12435, bp12435, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12435:ℝ)) (by norm_num [em12435]) ?_)
      (show bm12435^8 ≤ scalar12435.lowerTail by norm_num [bm12435, scalar12435])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12435, bm12435, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12435 :
    agent12435.root+dsL+scalar12435.worldRadius < √(1/100/aL) ∧
    2*(agent12435.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12435, agent12435, scalar12435, tp12435, tm12435, ep12435, em12435, dsL]

noncomputable def master12435 : MasterCertificate 12435 world12435 agent12435 :=
  master scalar12435 dsL tp12435 tm12435 ep12435 em12435
    (by norm_num [dsL]) (by norm_num [tp12435]) (by norm_num [tm12435])
    (by norm_num [ep12435]) (by norm_num [em12435])
    positive12435 negative12435 tails12435.1 tails12435.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12435.1 tailGuards12435.2

theorem preserves12435 : master12435.toScalarCertificate = scalar12435 := rfl

noncomputable def tp12436 : ℝ := (2290762481 / 10000000000)
noncomputable def tm12436 : ℝ := (-((300284441 / 500000000)))
noncomputable def ep12436 : ℝ := (10130634961614207 / 20000000000000000000)
noncomputable def em12436 : ℝ := (4943631517906479 / 10000000000000000000)
noncomputable def bp12436 : ℝ := (11375617197395527817 / 25000000000000000000)
noncomputable def bm12436 : ℝ := (46371389642832419261 / 100000000000000000000)

theorem positive12436 :
    Eplus aL (agent12436.root+dsL) scalar12436.worldRadius world12436.frame
      agent12436.frame tp12436 ≤ -ep12436 := by
  apply positive_check (eT := (115508224328769469953 / 100000000000000000000)) (y := (7531803057045843057 / 20000000000000000000)) (u := (36432672846929526379 / 25000000000000000000))
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12436, agent12436, tp12436, tm12436, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12436, agent12436, tp12436, tm12436, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]

theorem negative12436 :
    Eminus aL (agent12436.root+dsL) scalar12436.worldRadius world12436.frame
      agent12436.frame tm12436 ≤ -em12436 := by
  apply negative_check (lo := (68524807923303866271 / 100000000000000000000)) (hi := (2141400247603245821 / 3125000000000000000))
    (y := (-((17926544958776529403 / 25000000000000000000)))) (u := (12204613384337906351 / 25000000000000000000))
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12436, agent12436, tp12436, tm12436, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12436, agent12436, tp12436, tm12436, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12436, agent12436, tp12436, tm12436, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]

theorem tails12436 :
    exp (-((12436:ℝ)*ep12436)) ≤ scalar12436.upperTail ∧
    exp (-((12436:ℝ)*em12436)) ≤ scalar12436.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12436:ℝ)) (by norm_num [ep12436]) ?_)
      (show bp12436^8 ≤ scalar12436.upperTail by norm_num [bp12436, scalar12436])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12436, bp12436, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12436:ℝ)) (by norm_num [em12436]) ?_)
      (show bm12436^8 ≤ scalar12436.lowerTail by norm_num [bm12436, scalar12436])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12436, bm12436, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12436 :
    agent12436.root+dsL+scalar12436.worldRadius < √(1/100/aL) ∧
    2*(agent12436.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12436, agent12436, scalar12436, tp12436, tm12436, ep12436, em12436, dsL]

noncomputable def master12436 : MasterCertificate 12436 world12436 agent12436 :=
  master scalar12436 dsL tp12436 tm12436 ep12436 em12436
    (by norm_num [dsL]) (by norm_num [tp12436]) (by norm_num [tm12436])
    (by norm_num [ep12436]) (by norm_num [em12436])
    positive12436 negative12436 tails12436.1 tails12436.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12436.1 tailGuards12436.2

theorem preserves12436 : master12436.toScalarCertificate = scalar12436 := rfl

noncomputable def tp12437 : ℝ := (572714239 / 2500000000)
noncomputable def tm12437 : ℝ := (-((3002946713 / 5000000000)))
noncomputable def ep12437 : ℝ := (50656110663518031 / 100000000000000000000)
noncomputable def em12437 : ℝ := (49438853123581619 / 100000000000000000000)
noncomputable def bp12437 : ℝ := (45497511201165090867 / 100000000000000000000)
noncomputable def bm12437 : ℝ := (46366694734937276217 / 100000000000000000000)

theorem positive12437 :
    Eplus aL (agent12437.root+dsL) scalar12437.worldRadius world12437.frame
      agent12437.frame tp12437 ≤ -ep12437 := by
  apply positive_check (eT := (23101705758061342709 / 20000000000000000000)) (y := (37659904334670138189 / 100000000000000000000)) (u := (145731987011374500009 / 100000000000000000000))
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12437, agent12437, tp12437, tm12437, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12437, agent12437, tp12437, tm12437, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]

theorem negative12437 :
    Eminus aL (agent12437.root+dsL) scalar12437.worldRadius world12437.frame
      agent12437.frame tm12437 ≤ -em12437 := by
  apply negative_check (lo := (68524520173288568479 / 100000000000000000000)) (hi := (428278251083053553 / 625000000000000000))
    (y := (-((14341272035185883987 / 20000000000000000000)))) (u := (9763673099565995661 / 20000000000000000000))
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12437, agent12437, tp12437, tm12437, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12437, agent12437, tp12437, tm12437, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12437, agent12437, tp12437, tm12437, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]

theorem tails12437 :
    exp (-((12437:ℝ)*ep12437)) ≤ scalar12437.upperTail ∧
    exp (-((12437:ℝ)*em12437)) ≤ scalar12437.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12437:ℝ)) (by norm_num [ep12437]) ?_)
      (show bp12437^8 ≤ scalar12437.upperTail by norm_num [bp12437, scalar12437])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12437, bp12437, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12437:ℝ)) (by norm_num [em12437]) ?_)
      (show bm12437^8 ≤ scalar12437.lowerTail by norm_num [bm12437, scalar12437])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12437, bm12437, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12437 :
    agent12437.root+dsL+scalar12437.worldRadius < √(1/100/aL) ∧
    2*(agent12437.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12437, agent12437, scalar12437, tp12437, tm12437, ep12437, em12437, dsL]

noncomputable def master12437 : MasterCertificate 12437 world12437 agent12437 :=
  master scalar12437 dsL tp12437 tm12437 ep12437 em12437
    (by norm_num [dsL]) (by norm_num [tp12437]) (by norm_num [tm12437])
    (by norm_num [ep12437]) (by norm_num [em12437])
    positive12437 negative12437 tails12437.1 tails12437.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12437.1 tailGuards12437.2

theorem preserves12437 : master12437.toScalarCertificate = scalar12437 := rfl

noncomputable def tp12438 : ℝ := (57273783 / 250000000)
noncomputable def tm12438 : ℝ := (-((600609791 / 1000000000)))
noncomputable def ep12438 : ℝ := (25329522035070617 / 50000000000000000000)
noncomputable def em12438 : ℝ := (49441388789613337 / 100000000000000000000)
noncomputable def bp12438 : ℝ := (5686569443878843307 / 12500000000000000000)
noncomputable def bm12438 : ℝ := (2318100082529174271 / 5000000000000000000)

theorem positive12438 :
    Eplus aL (agent12438.root+dsL) scalar12438.worldRadius world12438.frame
      agent12438.frame tp12438 ≤ -ep12438 := by
  apply positive_check (eT := (115508832477116176477 / 100000000000000000000)) (y := (37660792046855820843 / 100000000000000000000)) (u := (145733280697723734631 / 100000000000000000000))
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12438, agent12438, tp12438, tm12438, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12438, agent12438, tp12438, tm12438, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]

theorem negative12438 :
    Eminus aL (agent12438.root+dsL) scalar12438.worldRadius world12438.frame
      agent12438.frame tm12438 ≤ -em12438 := by
  apply negative_check (lo := (68524232893287670599 / 100000000000000000000)) (hi := (342621164466438353 / 500000000000000000))
    (y := (-((224082937563219809 / 312500000000000000)))) (u := (48818277700860777623 / 100000000000000000000))
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12438, agent12438, tp12438, tm12438, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12438, agent12438, tp12438, tm12438, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12438, agent12438, tp12438, tm12438, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]

theorem tails12438 :
    exp (-((12438:ℝ)*ep12438)) ≤ scalar12438.upperTail ∧
    exp (-((12438:ℝ)*em12438)) ≤ scalar12438.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12438:ℝ)) (by norm_num [ep12438]) ?_)
      (show bp12438^8 ≤ scalar12438.upperTail by norm_num [bp12438, scalar12438])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12438, bp12438, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12438:ℝ)) (by norm_num [em12438]) ?_)
      (show bm12438^8 ≤ scalar12438.lowerTail by norm_num [bm12438, scalar12438])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12438, bm12438, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12438 :
    agent12438.root+dsL+scalar12438.worldRadius < √(1/100/aL) ∧
    2*(agent12438.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12438, agent12438, scalar12438, tp12438, tm12438, ep12438, em12438, dsL]

noncomputable def master12438 : MasterCertificate 12438 world12438 agent12438 :=
  master scalar12438 dsL tp12438 tm12438 ep12438 em12438
    (by norm_num [dsL]) (by norm_num [tp12438]) (by norm_num [tm12438])
    (by norm_num [ep12438]) (by norm_num [em12438])
    positive12438 negative12438 tails12438.1 tails12438.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12438.1 tailGuards12438.2

theorem preserves12438 : master12438.toScalarCertificate = scalar12438 := rfl

noncomputable def tp12439 : ℝ := (2291045767 / 10000000000)
noncomputable def tm12439 : ℝ := (-((6006302169 / 10000000000)))
noncomputable def ep12439 : ℝ := (50661976558221559 / 100000000000000000000)
noncomputable def em12439 : ℝ := (24721961804950873 / 50000000000000000000)
noncomputable def bp12439 : ℝ := (4548760075675112703 / 10000000000000000000)
noncomputable def bm12439 : ℝ := (23178654678495943723 / 50000000000000000000)

theorem positive12439 :
    Eplus aL (agent12439.root+dsL) scalar12439.worldRadius world12439.frame
      agent12439.frame tp12439 ≤ -ep12439 := by
  apply positive_check (eT := (23101827359895528397 / 20000000000000000000)) (y := (18830840774358782859 / 50000000000000000000)) (u := (145734577003734047269 / 100000000000000000000))
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12439, agent12439, tp12439, tm12439, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12439, agent12439, tp12439, tm12439, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]

theorem negative12439 :
    Eminus aL (agent12439.root+dsL) scalar12439.worldRadius world12439.frame
      agent12439.frame tm12439 ≤ -em12439 := by
  apply negative_check (lo := (68523946527419006923 / 100000000000000000000)) (hi := (17130986631854751731 / 25000000000000000000))
    (y := (-((14341343690476720431 / 20000000000000000000)))) (u := (48818190593434403783 / 100000000000000000000))
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12439, agent12439, tp12439, tm12439, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12439, agent12439, tp12439, tm12439, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12439, agent12439, tp12439, tm12439, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]

theorem tails12439 :
    exp (-((12439:ℝ)*ep12439)) ≤ scalar12439.upperTail ∧
    exp (-((12439:ℝ)*em12439)) ≤ scalar12439.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12439:ℝ)) (by norm_num [ep12439]) ?_)
      (show bp12439^8 ≤ scalar12439.upperTail by norm_num [bp12439, scalar12439])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12439, bp12439, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12439:ℝ)) (by norm_num [em12439]) ?_)
      (show bm12439^8 ≤ scalar12439.lowerTail by norm_num [bm12439, scalar12439])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12439, bm12439, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12439 :
    agent12439.root+dsL+scalar12439.worldRadius < √(1/100/aL) ∧
    2*(agent12439.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12439, agent12439, scalar12439, tp12439, tm12439, ep12439, em12439, dsL]

noncomputable def master12439 : MasterCertificate 12439 world12439 agent12439 :=
  master scalar12439 dsL tp12439 tm12439 ep12439 em12439
    (by norm_num [dsL]) (by norm_num [tp12439]) (by norm_num [tm12439])
    (by norm_num [ep12439]) (by norm_num [em12439])
    positive12439 negative12439 tails12439.1 tails12439.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12439.1 tailGuards12439.2

theorem preserves12439 : master12439.toScalarCertificate = scalar12439 := rfl

noncomputable def tp12440 : ℝ := (2291216793 / 10000000000)
noncomputable def tm12440 : ℝ := (-((1501684501 / 2500000000)))
noncomputable def ep12440 : ℝ := (12666596286337649 / 25000000000000000000)
noncomputable def em12440 : ℝ := (49448063887025433 / 100000000000000000000)
noncomputable def bp12440 : ℝ := (45481602202006907031 / 100000000000000000000)
noncomputable def bm12440 : ℝ := (11587865018175029083 / 25000000000000000000)

theorem positive12440 :
    Eplus aL (agent12440.root+dsL) scalar12440.worldRadius world12440.frame
      agent12440.frame tp12440 ≤ -ep12440 := by
  apply positive_check (eT := (115509997811250315721 / 100000000000000000000)) (y := (941545904349368773 / 2500000000000000000)) (u := (36433700586593191333 / 25000000000000000000))
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12440, agent12440, tp12440, tm12440, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12440, agent12440, tp12440, tm12440, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]

theorem negative12440 :
    Eminus aL (agent12440.root+dsL) scalar12440.worldRadius world12440.frame
      agent12440.frame tm12440 ≤ -em12440 := by
  apply negative_check (lo := (4282666344227987547 / 6250000000000000000)) (hi := (68522661507647800753 / 100000000000000000000))
    (y := (-((71704958949552082091 / 100000000000000000000)))) (u := (24409524779218463367 / 50000000000000000000))
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12440, agent12440, tp12440, tm12440, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12440, agent12440, tp12440, tm12440, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12440, agent12440, tp12440, tm12440, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]

theorem tails12440 :
    exp (-((12440:ℝ)*ep12440)) ≤ scalar12440.upperTail ∧
    exp (-((12440:ℝ)*em12440)) ≤ scalar12440.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12440:ℝ)) (by norm_num [ep12440]) ?_)
      (show bp12440^8 ≤ scalar12440.upperTail by norm_num [bp12440, scalar12440])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12440, bp12440, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12440:ℝ)) (by norm_num [em12440]) ?_)
      (show bm12440^8 ≤ scalar12440.lowerTail by norm_num [bm12440, scalar12440])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12440, bm12440, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12440 :
    agent12440.root+dsL+scalar12440.worldRadius < √(1/100/aL) ∧
    2*(agent12440.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12440, agent12440, scalar12440, tp12440, tm12440, ep12440, em12440, dsL]

noncomputable def master12440 : MasterCertificate 12440 world12440 agent12440 :=
  master scalar12440 dsL tp12440 tm12440 ep12440 em12440
    (by norm_num [dsL]) (by norm_num [tp12440]) (by norm_num [tm12440])
    (by norm_num [ep12440]) (by norm_num [em12440])
    positive12440 negative12440 tails12440.1 tails12440.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12440.1 tailGuards12440.2

theorem preserves12440 : master12440.toScalarCertificate = scalar12440 := rfl

noncomputable def tp12441 : ℝ := (572827761 / 2500000000)
noncomputable def tm12441 : ℝ := (-((6006942157 / 10000000000)))
noncomputable def ep12441 : ℝ := (3166832178312061 / 6250000000000000000)
noncomputable def em12441 : ℝ := (24725298065816127 / 50000000000000000000)
noncomputable def bp12441 : ℝ := (22738324908186906659 / 50000000000000000000)
noncomputable def bm12441 : ℝ := (23173385011015128223 / 50000000000000000000)

theorem positive12441 :
    Eplus aL (agent12441.root+dsL) scalar12441.worldRadius world12441.frame
      agent12441.frame tp12441 ≤ -ep12441 := by
  apply positive_check (eT := (3609696898812183727 / 3125000000000000000)) (y := (188313615087831061 / 500000000000000000)) (u := (72868047395929439707 / 50000000000000000000))
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12441, agent12441, tp12441, tm12441, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12441, agent12441, tp12441, tm12441, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]

theorem negative12441 :
    Eminus aL (agent12441.root+dsL) scalar12441.worldRadius world12441.frame
      agent12441.frame tm12441 ≤ -em12441 := by
  apply negative_check (lo := (68522375513525144391 / 100000000000000000000)) (hi := (8565296939190643049 / 12500000000000000000))
    (y := (-((17926284458541566749 / 25000000000000000000)))) (u := (48818962228746585099 / 100000000000000000000))
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12441, agent12441, tp12441, tm12441, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12441, agent12441, tp12441, tm12441, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12441, agent12441, tp12441, tm12441, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]

theorem tails12441 :
    exp (-((12441:ℝ)*ep12441)) ≤ scalar12441.upperTail ∧
    exp (-((12441:ℝ)*em12441)) ≤ scalar12441.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12441:ℝ)) (by norm_num [ep12441]) ?_)
      (show bp12441^8 ≤ scalar12441.upperTail by norm_num [bp12441, scalar12441])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12441, bp12441, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12441:ℝ)) (by norm_num [em12441]) ?_)
      (show bm12441^8 ≤ scalar12441.lowerTail by norm_num [bm12441, scalar12441])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12441, bm12441, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12441 :
    agent12441.root+dsL+scalar12441.worldRadius < √(1/100/aL) ∧
    2*(agent12441.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12441, agent12441, scalar12441, tp12441, tm12441, ep12441, em12441, dsL]

noncomputable def master12441 : MasterCertificate 12441 world12441 agent12441 :=
  master scalar12441 dsL tp12441 tm12441 ep12441 em12441
    (by norm_num [dsL]) (by norm_num [tp12441]) (by norm_num [tm12441])
    (by norm_num [ep12441]) (by norm_num [em12441])
    positive12441 negative12441 tails12441.1 tails12441.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12441.1 tailGuards12441.2

theorem preserves12441 : master12441.toScalarCertificate = scalar12441 := rfl

noncomputable def tp12442 : ℝ := (4475401 / 19531250)
noncomputable def tm12442 : ℝ := (-((600714617 / 1000000000)))
noncomputable def ep12442 : ℝ := (25336121449875631 / 50000000000000000000)
noncomputable def em12442 : ℝ := (49453126809848991 / 100000000000000000000)
noncomputable def bp12442 : ℝ := (45471698811522378179 / 100000000000000000000)
noncomputable def bm12442 : ℝ := (9268416256299949081 / 20000000000000000000)

theorem positive12442 :
    Eplus aL (agent12442.root+dsL) scalar12442.worldRadius world12442.frame
      agent12442.frame tp12442 ≤ -ep12442 := by
  apply positive_check (eT := (14438825483561037877 / 12500000000000000000)) (y := (37663610836576208611 / 100000000000000000000)) (u := (72868694335178254531 / 50000000000000000000))
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12442, agent12442, tp12442, tm12442, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12442, agent12442, tp12442, tm12442, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]

theorem negative12442 :
    Eminus aL (agent12442.root+dsL) scalar12442.worldRadius world12442.frame
      agent12442.frame tm12442 ≤ -em12442 := by
  apply negative_check (lo := (68522090066943875079 / 100000000000000000000)) (hi := (1713052251673596877 / 2500000000000000000))
    (y := (-((71705316588825742641 / 100000000000000000000)))) (u := (9763774992530977937 / 20000000000000000000))
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12442, agent12442, tp12442, tm12442, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12442, agent12442, tp12442, tm12442, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12442, agent12442, tp12442, tm12442, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]

theorem tails12442 :
    exp (-((12442:ℝ)*ep12442)) ≤ scalar12442.upperTail ∧
    exp (-((12442:ℝ)*em12442)) ≤ scalar12442.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12442:ℝ)) (by norm_num [ep12442]) ?_)
      (show bp12442^8 ≤ scalar12442.upperTail by norm_num [bp12442, scalar12442])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12442, bp12442, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12442:ℝ)) (by norm_num [em12442]) ?_)
      (show bm12442^8 ≤ scalar12442.lowerTail by norm_num [bm12442, scalar12442])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12442, bm12442, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12442 :
    agent12442.root+dsL+scalar12442.worldRadius < √(1/100/aL) ∧
    2*(agent12442.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12442, agent12442, scalar12442, tp12442, tm12442, ep12442, em12442, dsL]

noncomputable def master12442 : MasterCertificate 12442 world12442 agent12442 :=
  master scalar12442 dsL tp12442 tm12442 ep12442 em12442
    (by norm_num [dsL]) (by norm_num [tp12442]) (by norm_num [tm12442])
    (by norm_num [ep12442]) (by norm_num [em12442])
    positive12442 negative12442 tails12442.1 tails12442.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12442.1 tailGuards12442.2

theorem preserves12442 : master12442.toScalarCertificate = scalar12442 := rfl

noncomputable def tp12443 : ℝ := (286437441 / 1250000000)
noncomputable def tm12443 : ℝ := (-((6007350043 / 10000000000)))
noncomputable def ep12443 : ℝ := (50675169431915557 / 100000000000000000000)
noncomputable def em12443 : ℝ := (12363914016871603 / 25000000000000000000)
noncomputable def bp12443 : ℝ := (45466749083949007259 / 100000000000000000000)
noncomputable def bm12443 : ℝ := (23168696872995189937 / 50000000000000000000)

theorem positive12443 :
    Eplus aL (agent12443.root+dsL) scalar12443.worldRadius world12443.frame
      agent12443.frame tp12443 ≤ -ep12443 := by
  apply positive_check (eT := (57755453314618433721 / 50000000000000000000)) (y := (7532899631920757443 / 20000000000000000000)) (u := (145738681837503249321 / 100000000000000000000))
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12443, agent12443, tp12443, tm12443, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12443, agent12443, tp12443, tm12443, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]

theorem negative12443 :
    Eminus aL (agent12443.root+dsL) scalar12443.worldRadius world12443.frame
      agent12443.frame tm12443 ≤ -em12443 := by
  apply negative_check (lo := (68521805167804491849 / 100000000000000000000)) (hi := (1370436103356089837 / 2000000000000000000))
    (y := (-((7170549451135096889 / 10000000000000000000)))) (u := (3051174256434815037 / 6250000000000000000))
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12443, agent12443, tp12443, tm12443, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12443, agent12443, tp12443, tm12443, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12443, agent12443, tp12443, tm12443, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]

theorem tails12443 :
    exp (-((12443:ℝ)*ep12443)) ≤ scalar12443.upperTail ∧
    exp (-((12443:ℝ)*em12443)) ≤ scalar12443.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12443:ℝ)) (by norm_num [ep12443]) ?_)
      (show bp12443^8 ≤ scalar12443.upperTail by norm_num [bp12443, scalar12443])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12443, bp12443, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12443:ℝ)) (by norm_num [em12443]) ?_)
      (show bm12443^8 ≤ scalar12443.lowerTail by norm_num [bm12443, scalar12443])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12443, bm12443, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12443 :
    agent12443.root+dsL+scalar12443.worldRadius < √(1/100/aL) ∧
    2*(agent12443.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12443, agent12443, scalar12443, tp12443, tm12443, ep12443, em12443, dsL]

noncomputable def master12443 : MasterCertificate 12443 world12443 agent12443 :=
  master scalar12443 dsL tp12443 tm12443 ep12443 em12443
    (by norm_num [dsL]) (by norm_num [tp12443]) (by norm_num [tm12443])
    (by norm_num [ep12443]) (by norm_num [em12443])
    positive12443 negative12443 tails12443.1 tails12443.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12443.1 tailGuards12443.2

theorem preserves12443 : master12443.toScalarCertificate = scalar12443 := rfl

noncomputable def tp12444 : ℝ := (2291593649 / 10000000000)
noncomputable def tm12444 : ℝ := (-((1201510773 / 2000000000)))
noncomputable def ep12444 : ℝ := (25339047363914473 / 50000000000000000000)
noncomputable def em12444 : ℝ := (12364546052114773 / 25000000000000000000)
noncomputable def bp12444 : ℝ := (9092360087355903449 / 20000000000000000000)
noncomputable def bm12444 : ℝ := (46332707196446435313 / 100000000000000000000)

theorem positive12444 :
    Eplus aL (agent12444.root+dsL) scalar12444.worldRadius world12444.frame
      agent12444.frame tp12444 ≤ -ep12444 := by
  apply positive_check (eT := (14438901091465219627 / 12500000000000000000)) (y := (7533076825659697721 / 20000000000000000000)) (u := (72869986521160113423 / 50000000000000000000))
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12444, agent12444, tp12444, tm12444, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12444, agent12444, tp12444, tm12444, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]

theorem negative12444 :
    Eminus aL (agent12444.root+dsL) scalar12444.worldRadius world12444.frame
      agent12444.frame tm12444 ≤ -em12444 := by
  apply negative_check (lo := (8565190054038618173 / 12500000000000000000)) (hi := (13704304086461789077 / 20000000000000000000))
    (y := (-((71705672725720294293 / 100000000000000000000)))) (u := (24409350550469617837 / 50000000000000000000))
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12444, agent12444, tp12444, tm12444, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12444, agent12444, tp12444, tm12444, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12444, agent12444, tp12444, tm12444, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]

theorem tails12444 :
    exp (-((12444:ℝ)*ep12444)) ≤ scalar12444.upperTail ∧
    exp (-((12444:ℝ)*em12444)) ≤ scalar12444.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12444:ℝ)) (by norm_num [ep12444]) ?_)
      (show bp12444^8 ≤ scalar12444.upperTail by norm_num [bp12444, scalar12444])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12444, bp12444, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12444:ℝ)) (by norm_num [em12444]) ?_)
      (show bm12444^8 ≤ scalar12444.lowerTail by norm_num [bm12444, scalar12444])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12444, bm12444, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12444 :
    agent12444.root+dsL+scalar12444.worldRadius < √(1/100/aL) ∧
    2*(agent12444.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12444, agent12444, scalar12444, tp12444, tm12444, ep12444, em12444, dsL]

noncomputable def master12444 : MasterCertificate 12444 world12444 agent12444 :=
  master scalar12444 dsL tp12444 tm12444 ep12444 em12444
    (by norm_num [dsL]) (by norm_num [tp12444]) (by norm_num [tm12444])
    (by norm_num [ep12444]) (by norm_num [em12444])
    positive12444 negative12444 tails12444.1 tails12444.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12444.1 tailGuards12444.2

theorem preserves12444 : master12444.toScalarCertificate = scalar12444 := rfl

noncomputable def tp12445 : ℝ := (229168779 / 1000000000)
noncomputable def tm12445 : ℝ := (-((1501939391 / 2500000000)))
noncomputable def ep12445 : ℝ := (50681018041529979 / 100000000000000000000)
noncomputable def em12445 : ℝ := (49460710502773169 / 100000000000000000000)
noncomputable def bp12445 : ℝ := (45456853397486961453 / 100000000000000000000)
noncomputable def bm12445 : ℝ := (23164011079479071441 / 50000000000000000000)

theorem positive12445 :
    Eplus aL (agent12445.root+dsL) scalar12445.worldRadius world12445.frame
      agent12445.frame tp12445 ≤ -ep12445 := by
  apply positive_check (eT := (115511511011798915221 / 100000000000000000000)) (y := (7533254204372370151 / 20000000000000000000)) (u := (72870632803246105333 / 50000000000000000000))
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12445, agent12445, tp12445, tm12445, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12445, agent12445, tp12445, tm12445, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]

theorem negative12445 :
    Eminus aL (agent12445.root+dsL) scalar12445.worldRadius world12445.frame
      agent12445.frame tm12445 ≤ -em12445 := by
  apply negative_check (lo := (68521236170945182037 / 100000000000000000000)) (hi := (34260618085472591019 / 50000000000000000000))
    (y := (-((71705850559118151783 / 100000000000000000000)))) (u := (48818614285061471817 / 100000000000000000000))
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12445, agent12445, tp12445, tm12445, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12445, agent12445, tp12445, tm12445, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12445, agent12445, tp12445, tm12445, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]

theorem tails12445 :
    exp (-((12445:ℝ)*ep12445)) ≤ scalar12445.upperTail ∧
    exp (-((12445:ℝ)*em12445)) ≤ scalar12445.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12445:ℝ)) (by norm_num [ep12445]) ?_)
      (show bp12445^8 ≤ scalar12445.upperTail by norm_num [bp12445, scalar12445])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12445, bp12445, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12445:ℝ)) (by norm_num [em12445]) ?_)
      (show bm12445^8 ≤ scalar12445.lowerTail by norm_num [bm12445, scalar12445])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12445, bm12445, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12445 :
    agent12445.root+dsL+scalar12445.worldRadius < √(1/100/aL) ∧
    2*(agent12445.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12445, agent12445, scalar12445, tp12445, tm12445, ep12445, em12445, dsL]

noncomputable def master12445 : MasterCertificate 12445 world12445 agent12445 :=
  master scalar12445 dsL tp12445 tm12445 ep12445 em12445
    (by norm_num [dsL]) (by norm_num [tp12445]) (by norm_num [tm12445])
    (by norm_num [ep12445]) (by norm_num [em12445])
    positive12445 negative12445 tails12445.1 tails12445.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12445.1 tailGuards12445.2

theorem preserves12445 : master12445.toScalarCertificate = scalar12445 := rfl

noncomputable def tp12446 : ℝ := (286472729 / 1250000000)
noncomputable def tm12446 : ℝ := (-((6007960981 / 10000000000)))
noncomputable def ep12446 : ℝ := (50683940633488047 / 100000000000000000000)
noncomputable def em12446 : ℝ := (24731618046389741 / 50000000000000000000)
noncomputable def bp12446 : ℝ := (45451907074700851511 / 100000000000000000000)
noncomputable def bm12446 : ℝ := (23161668905109690163 / 50000000000000000000)

theorem positive12446 :
    Eplus aL (agent12446.root+dsL) scalar12446.worldRadius world12446.frame
      agent12446.frame tp12446 ≤ -ep12446 := by
  apply positive_check (eT := (115511812604552893459 / 100000000000000000000)) (y := (37667156643369321753 / 100000000000000000000)) (u := (29148511265640225657 / 20000000000000000000))
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12446, agent12446, tp12446, tm12446, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12446, agent12446, tp12446, tm12446, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]

theorem negative12446 :
    Eminus aL (agent12446.root+dsL) scalar12446.worldRadius world12446.frame
      agent12446.frame tm12446 ≤ -em12446 := by
  apply negative_check (lo := (13704190613836254663 / 20000000000000000000)) (hi := (17130238267295318329 / 25000000000000000000))
    (y := (-((71706026709537391507 / 100000000000000000000)))) (u := (48818528290943481179 / 100000000000000000000))
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12446, agent12446, tp12446, tm12446, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12446, agent12446, tp12446, tm12446, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12446, agent12446, tp12446, tm12446, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]

theorem tails12446 :
    exp (-((12446:ℝ)*ep12446)) ≤ scalar12446.upperTail ∧
    exp (-((12446:ℝ)*em12446)) ≤ scalar12446.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12446:ℝ)) (by norm_num [ep12446]) ?_)
      (show bp12446^8 ≤ scalar12446.upperTail by norm_num [bp12446, scalar12446])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12446, bp12446, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12446:ℝ)) (by norm_num [em12446]) ?_)
      (show bm12446^8 ≤ scalar12446.lowerTail by norm_num [bm12446, scalar12446])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12446, bm12446, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12446 :
    agent12446.root+dsL+scalar12446.worldRadius < √(1/100/aL) ∧
    2*(agent12446.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12446, agent12446, scalar12446, tp12446, tm12446, ep12446, em12446, dsL]

noncomputable def master12446 : MasterCertificate 12446 world12446 agent12446 :=
  master scalar12446 dsL tp12446 tm12446 ep12446 em12446
    (by norm_num [dsL]) (by norm_num [tp12446]) (by norm_num [tm12446])
    (by norm_num [ep12446]) (by norm_num [em12446])
    positive12446 negative12446 tails12446.1 tails12446.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12446.1 tailGuards12446.2

theorem preserves12446 : master12446.toScalarCertificate = scalar12446 := rfl

noncomputable def tp12447 : ℝ := (1145937927 / 5000000000)
noncomputable def tm12447 : ℝ := (-((6008164443 / 10000000000)))
noncomputable def ep12447 : ℝ := (50686861382531741 / 100000000000000000000)
noncomputable def em12447 : ℝ := (24732879994146739 / 50000000000000000000)
noncomputable def bp12447 : ℝ := (22723481130602707603 / 50000000000000000000)
noncomputable def bm12447 : ℝ := (2894915928989132521 / 6250000000000000000)

theorem positive12447 :
    Eplus aL (agent12447.root+dsL) scalar12447.worldRadius world12447.frame
      agent12447.frame tp12447 ≤ -ep12447 := by
  apply positive_check (eT := (115512114084184381053 / 100000000000000000000)) (y := (18834021216836648373 / 50000000000000000000)) (u := (36435961826837881103 / 25000000000000000000))
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12447, agent12447, tp12447, tm12447, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12447, agent12447, tp12447, tm12447, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]

theorem negative12447 :
    Eminus aL (agent12447.root+dsL) scalar12447.worldRadius world12447.frame
      agent12447.frame tm12447 ≤ -em12447 := by
  apply negative_check (lo := (34260334858572394409 / 50000000000000000000)) (hi := (68520669717144788819 / 100000000000000000000))
    (y := (-((14341240850635564721 / 20000000000000000000)))) (u := (48818441616828090277 / 100000000000000000000))
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12447, agent12447, tp12447, tm12447, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12447, agent12447, tp12447, tm12447, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12447, agent12447, tp12447, tm12447, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]

theorem tails12447 :
    exp (-((12447:ℝ)*ep12447)) ≤ scalar12447.upperTail ∧
    exp (-((12447:ℝ)*em12447)) ≤ scalar12447.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12447:ℝ)) (by norm_num [ep12447]) ?_)
      (show bp12447^8 ≤ scalar12447.upperTail by norm_num [bp12447, scalar12447])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12447, bp12447, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12447:ℝ)) (by norm_num [em12447]) ?_)
      (show bm12447^8 ≤ scalar12447.lowerTail by norm_num [bm12447, scalar12447])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12447, bm12447, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12447 :
    agent12447.root+dsL+scalar12447.worldRadius < √(1/100/aL) ∧
    2*(agent12447.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12447, agent12447, scalar12447, tp12447, tm12447, ep12447, em12447, dsL]

noncomputable def master12447 : MasterCertificate 12447 world12447 agent12447 :=
  master scalar12447 dsL tp12447 tm12447 ep12447 em12447
    (by norm_num [dsL]) (by norm_num [tp12447]) (by norm_num [tm12447])
    (by norm_num [ep12447]) (by norm_num [em12447])
    positive12447 negative12447 tails12447.1 tails12447.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12447.1 tailGuards12447.2

theorem preserves12447 : master12447.toScalarCertificate = scalar12447 := rfl

noncomputable def tp12448 : ℝ := (2291969831 / 10000000000)
noncomputable def tm12448 : ℝ := (-((6008367843 / 10000000000)))
noncomputable def ep12448 : ℝ := (25344890147265811 / 50000000000000000000)
noncomputable def em12448 : ℝ := (24734141094121657 / 50000000000000000000)
noncomputable def bp12448 : ℝ := (22721009476394128387 / 50000000000000000000)
noncomputable def bm12448 : ℝ := (46313973320515531339 / 100000000000000000000)

theorem positive12448 :
    Eplus aL (agent12448.root+dsL) scalar12448.worldRadius world12448.frame
      agent12448.frame tp12448 ≤ -ep12448 := by
  apply positive_check (eT := (28878103817253213529 / 25000000000000000000)) (y := (4708615981187193733 / 12500000000000000000)) (u := (36436284438037837951 / 25000000000000000000))
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12448, agent12448, tp12448, tm12448, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12448, agent12448, tp12448, tm12448, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]

theorem negative12448 :
    Eminus aL (agent12448.root+dsL) scalar12448.worldRadius world12448.frame
      agent12448.frame tm12448 ≤ -em12448 := by
  apply negative_check (lo := (34260193288071170331 / 50000000000000000000)) (hi := (68520386576142340663 / 100000000000000000000))
    (y := (-((71706381725296348799 / 100000000000000000000)))) (u := (9763670995556480401 / 20000000000000000000))
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12448, agent12448, tp12448, tm12448, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12448, agent12448, tp12448, tm12448, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12448, agent12448, tp12448, tm12448, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]

theorem tails12448 :
    exp (-((12448:ℝ)*ep12448)) ≤ scalar12448.upperTail ∧
    exp (-((12448:ℝ)*em12448)) ≤ scalar12448.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12448:ℝ)) (by norm_num [ep12448]) ?_)
      (show bp12448^8 ≤ scalar12448.upperTail by norm_num [bp12448, scalar12448])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12448, bp12448, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12448:ℝ)) (by norm_num [em12448]) ?_)
      (show bm12448^8 ≤ scalar12448.lowerTail by norm_num [bm12448, scalar12448])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12448, bm12448, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12448 :
    agent12448.root+dsL+scalar12448.worldRadius < √(1/100/aL) ∧
    2*(agent12448.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12448, agent12448, scalar12448, tp12448, tm12448, ep12448, em12448, dsL]

noncomputable def master12448 : MasterCertificate 12448 world12448 agent12448 :=
  master scalar12448 dsL tp12448 tm12448 ep12448 em12448
    (by norm_num [dsL]) (by norm_num [tp12448]) (by norm_num [tm12448])
    (by norm_num [ep12448]) (by norm_num [em12448])
    positive12448 negative12448 tails12448.1 tails12448.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12448.1 tailGuards12448.2

theorem preserves12448 : master12448.toScalarCertificate = scalar12448 := rfl

noncomputable def tp12449 : ℝ := (57301593 / 250000000)
noncomputable def tm12449 : ℝ := (-((3004285503 / 5000000000)))
noncomputable def ep12449 : ℝ := (50692698158885277 / 100000000000000000000)
noncomputable def em12449 : ℝ := (49470803399696153 / 100000000000000000000)
noncomputable def bp12449 : ℝ := (45437076591238626731 / 100000000000000000000)
noncomputable def bm12449 : ℝ := (4630929267071816139 / 10000000000000000000)

theorem positive12449 :
    Eplus aL (agent12449.root+dsL) scalar12449.worldRadius world12449.frame
      agent12449.frame tp12449 ≤ -ep12449 := by
  apply positive_check (eT := (115512715846526632021 / 100000000000000000000)) (y := (2354363255253319879 / 6250000000000000000)) (u := (145746426486720126597 / 100000000000000000000))
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12449, agent12449, tp12449, tm12449, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12449, agent12449, tp12449, tm12449, Finset.sum_range_succ, Nat.factorial]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]

theorem negative12449 :
    Eminus aL (agent12449.root+dsL) scalar12449.worldRadius world12449.frame
      agent12449.frame tm12449 ≤ -em12449 := by
  apply negative_check (lo := (68520104400626532791 / 100000000000000000000)) (hi := (8565013050078316599 / 12500000000000000000))
    (y := (-((17926639384647927363 / 25000000000000000000)))) (u := (12204567287174806049 / 25000000000000000000))
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · exact by
      apply le_exp_taylor (b := 1) 24 <;>
        norm_num [world12449, agent12449, tp12449, tm12449, Finset.sum_range_succ, Nat.factorial]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12449, agent12449, tp12449, tm12449, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · exact by
      apply exp_le_taylor (b := 1) 24 <;>
        norm_num [world12449, agent12449, tp12449, tm12449, Finset.sum_range_succ, Nat.factorial]
  · norm_num
  · norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]

theorem tails12449 :
    exp (-((12449:ℝ)*ep12449)) ≤ scalar12449.upperTail ∧
    exp (-((12449:ℝ)*em12449)) ≤ scalar12449.lowerTail := by
  constructor
  · apply le_trans (tail8 (le_refl (12449:ℝ)) (by norm_num [ep12449]) ?_)
      (show bp12449^8 ≤ scalar12449.upperTail by norm_num [bp12449, scalar12449])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [ep12449, bp12449, Finset.sum_range_succ, Nat.factorial]
  · apply le_trans (tail8 (le_refl (12449:ℝ)) (by norm_num [em12449]) ?_)
      (show bm12449^8 ≤ scalar12449.lowerTail by norm_num [bm12449, scalar12449])
    apply exp_le_taylor (b := 1) 24 <;>
      norm_num [em12449, bm12449, Finset.sum_range_succ, Nat.factorial]

theorem tailGuards12449 :
    agent12449.root+dsL+scalar12449.worldRadius < √(1/100/aL) ∧
    2*(agent12449.root+dsL) ≤ √(1/100/aL) := by
  constructor
  · apply lt_of_lt_of_le _ x0_lo
    norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]
  · apply le_trans _ x0_lo
    norm_num [world12449, agent12449, scalar12449, tp12449, tm12449, ep12449, em12449, dsL]

noncomputable def master12449 : MasterCertificate 12449 world12449 agent12449 :=
  master scalar12449 dsL tp12449 tm12449 ep12449 em12449
    (by norm_num [dsL]) (by norm_num [tp12449]) (by norm_num [tm12449])
    (by norm_num [ep12449]) (by norm_num [em12449])
    positive12449 negative12449 tails12449.1 tails12449.2
    (by exact BstLean.Part243.row_sampling)
    (by
      have he : -((10^12:ℕ):ℝ)*dsL^2 = -100 := by norm_num [dsL]
      rw [he]
      exact BstLean.Part243.row_sampling)
    tailGuards12449.1 tailGuards12449.2

theorem preserves12449 : master12449.toScalarCertificate = scalar12449 := rfl

end BstLean.Part268
