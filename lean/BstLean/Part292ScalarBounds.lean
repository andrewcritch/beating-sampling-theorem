import BstLean.Part292ScalarDefs

/-! Each interval rule is checked over 0 <= x <= 1/8000. -/
namespace BstLean.Part292
open BstLean.Part228

theorem lowScalar0_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar0 x) (0 / 1 : ℝ) (1 / 8000 : ℝ) := by
  unfold lowScalar0
  simpa only [zero_div] using hx

theorem lowScalar1_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar1 x) (0 / 1 : ℝ) (111803398874989484820458683436563811773 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar1
  exact Bounds.sqrt (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar2_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar2 x) (517 / 200 : ℝ) (517 / 200 : ℝ) := by
  unfold lowScalar2
  exact Bounds.point _

theorem lowScalar3_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar3 x) (27 / 50 : ℝ) (27 / 50 : ℝ) := by
  unfold lowScalar3
  exact Bounds.point _

theorem lowScalar4_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar4 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (3674234614174767147295926112058837087949 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar4
  exact Bounds.sqrt (lowScalar3_bounds hx) (by norm_num)

theorem lowScalar5_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar5 x) (23 / 50 : ℝ) (23 / 50 : ℝ) := by
  unfold lowScalar5
  exact Bounds.point _

theorem lowScalar6_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar6 x) (0 / 1 : ℝ) (23 / 400000 : ℝ) := by
  unfold lowScalar6
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar5_bounds hx) (by norm_num)

theorem lowScalar7_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar7 x) (0 / 1 : ℝ) (37914377220257752771284127181410357773 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar7
  exact Bounds.sqrt (lowScalar6_bounds hx) (by norm_num)

theorem lowScalar8_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar8 x) (6 / 1 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar8
  exact Bounds.point _

theorem lowScalar9_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar9 x) (0 / 1 : ℝ) (113743131660773258313852381544231073319 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar9
  exact Bounds.mul (lowScalar7_bounds hx) (lowScalar8_bounds hx) (by norm_num)

theorem lowScalar10_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar10 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (3901720877496313663923630875147299234587 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar10
  exact Bounds.add (lowScalar4_bounds hx) (lowScalar9_bounds hx) (by norm_num)

theorem lowScalar11_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar11 x) (2699999999999999999999999999999999999999 / 5000000000000000000000000000000000000000 : ℝ) (6089370322356241558955484756562117825269 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar11
  exact Bounds.pow (lowScalar10_bounds hx) 2 (by norm_num)

theorem lowScalar12_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar12 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar12
  exact Bounds.point _

theorem lowScalar13_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar13 x) (-6089370322356241558955484756562117825269 / 10000000000000000000000000000000000000000 : ℝ) (-2699999999999999999999999999999999999999 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar13
  convert Bounds.neg (lowScalar11_bounds hx) using 1 <;> norm_num

theorem lowScalar14_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar14 x) (3910629677643758441044515243437882174731 / 10000000000000000000000000000000000000000 : ℝ) (2300000000000000000000000000000000000001 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar14
  exact Bounds.add (lowScalar12_bounds hx) (lowScalar13_bounds hx) (by norm_num)

theorem lowScalar15_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar15 x) (23 / 50 : ℝ) (23 / 50 : ℝ) := by
  unfold lowScalar15
  exact Bounds.point _

theorem lowScalar16_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar16 x) (1356465996625053627812911265325193821039 / 2000000000000000000000000000000000000000 : ℝ) (1695582495781317034766139081656492276299 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar16
  exact Bounds.sqrt (lowScalar15_bounds hx) (by norm_num)

theorem lowScalar17_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar17 x) (27 / 50 : ℝ) (27 / 50 : ℝ) := by
  unfold lowScalar17
  exact Bounds.point _

theorem lowScalar18_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar18 x) (0 / 1 : ℝ) (27 / 400000 : ℝ) := by
  unfold lowScalar18
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar17_bounds hx) (by norm_num)

theorem lowScalar19_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar19 x) (0 / 1 : ℝ) (82158383625774917018545467420120320093 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar19
  exact Bounds.sqrt (lowScalar18_bounds hx) (by norm_num)

theorem lowScalar20_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar20 x) (6 / 1 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar20
  exact Bounds.point _

theorem lowScalar21_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar21 x) (0 / 1 : ℝ) (246475150877324751055636402260360960279 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar21
  exact Bounds.mul (lowScalar19_bounds hx) (lowScalar20_bounds hx) (by norm_num)

theorem lowScalar22_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar22 x) (-246475150877324751055636402260360960279 / 5000000000000000000000000000000000000000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar22
  convert Bounds.neg (lowScalar21_bounds hx) using 1 <;> norm_num

theorem lowScalar23_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar23 x) (6289379681370618636953283522105247184637 / 10000000000000000000000000000000000000000 : ℝ) (1695582495781317034766139081656492276299 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar23
  exact Bounds.add (lowScalar16_bounds hx) (lowScalar22_bounds hx) (by norm_num)

theorem lowScalar24_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar24 x) (791125935528751688208903048687576434947 / 2000000000000000000000000000000000000000 : ℝ) (4600000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar24
  exact Bounds.pow (lowScalar23_bounds hx) 2 (by norm_num)

theorem lowScalar25_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar25 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar25
  exact Bounds.point _

theorem lowScalar26_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar26 x) (-4600000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) (-791125935528751688208903048687576434947 / 2000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar26
  convert Bounds.neg (lowScalar24_bounds hx) using 1 <;> norm_num

theorem lowScalar27_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar27 x) (5399999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℝ) (1208874064471248311791096951312423565053 / 2000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar27
  exact Bounds.add (lowScalar25_bounds hx) (lowScalar26_bounds hx) (by norm_num)

theorem lowScalar28_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar28 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar28
  exact Bounds.point _

theorem lowScalar29_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar29 x) (1 / 1 : ℝ) (10111803398874989484820458683436563811773 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar29
  exact Bounds.add (lowScalar1_bounds hx) (lowScalar28_bounds hx) (by norm_num)

theorem lowScalar30_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar30 x) (6 / 1 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar30
  exact Bounds.point _

theorem lowScalar31_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar31 x) (0 / 1 : ℝ) (3 / 4000 : ℝ) := by
  unfold lowScalar31
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar30_bounds hx) (by norm_num)

theorem lowScalar32_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar32 x) (1 / 1 : ℝ) (10119303398874989484820458683436563811773 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar32
  exact Bounds.add (lowScalar29_bounds hx) (lowScalar31_bounds hx) (by norm_num)

theorem lowScalar33_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar33 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar33
  exact Bounds.point _

theorem lowScalar34_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar34 x) (2 / 1 : ℝ) (10119303398874989484820458683436563811773 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar34
  exact Bounds.mul (lowScalar32_bounds hx) (lowScalar33_bounds hx) (by norm_num)

theorem lowScalar35_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar35 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar35
  exact Bounds.point _

theorem lowScalar36_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar36 x) (0 / 1 : ℝ) (1 / 4000 : ℝ) := by
  unfold lowScalar36
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar35_bounds hx) (by norm_num)

theorem lowScalar37_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar37 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar37
  exact Bounds.point _

theorem lowScalar38_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar38 x) (-1 / 4000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar38
  convert Bounds.neg (lowScalar36_bounds hx) using 1 <;> norm_num

theorem lowScalar39_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar39 x) (3999 / 4000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar39
  exact Bounds.add (lowScalar37_bounds hx) (lowScalar38_bounds hx) (by norm_num)

theorem lowScalar40_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar40 x) (9998749921865232848854014863667874180739 / 10000000000000000000000000000000000000000 : ℝ) (10000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar40
  exact Bounds.sqrt (lowScalar39_bounds hx) (by norm_num)

theorem lowScalar41_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar41 x) (9999999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℝ) (10001250234423838808556153902143410033249 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar41
  exact Bounds.inv (lowScalar40_bounds hx) (by norm_num)

theorem lowScalar42_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar42 x) (9999999999999999999999999999999999999999 / 5000000000000000000000000000000000000000 : ℝ) (20241137098040887483561113202444700099627 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar42
  exact Bounds.mul (lowScalar34_bounds hx) (lowScalar41_bounds hx) (by norm_num)

theorem lowScalar43_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar43 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar43
  exact Bounds.point _

theorem lowScalar44_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar44 x) (-1 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar44
  convert Bounds.neg (lowScalar0_bounds hx) using 1 <;> norm_num

theorem lowScalar45_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar45 x) (7999 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar45
  exact Bounds.add (lowScalar43_bounds hx) (lowScalar44_bounds hx) (by norm_num)

theorem lowScalar46_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar46 x) (4999687490233764600749611463359320359407 / 5000000000000000000000000000000000000000 : ℝ) (10000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar46
  exact Bounds.sqrt (lowScalar45_bounds hx) (by norm_num)

theorem lowScalar47_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar47 x) (6 / 1 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar47
  exact Bounds.point _

theorem lowScalar48_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar48 x) (0 / 1 : ℝ) (3 / 4000 : ℝ) := by
  unfold lowScalar48
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar47_bounds hx) (by norm_num)

theorem lowScalar49_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar49 x) (0 / 1 : ℝ) (83852549156242113615344012577422859 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar49
  exact Bounds.mul (lowScalar48_bounds hx) (lowScalar1_bounds hx) (by norm_num)

theorem lowScalar50_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar50 x) (4999687490233764600749611463359320359407 / 5000000000000000000000000000000000000000 : ℝ) (500004192627457812105680767200628871143 / 500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar50
  exact Bounds.add (lowScalar46_bounds hx) (lowScalar49_bounds hx) (by norm_num)

theorem lowScalar51_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar51 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar51
  exact Bounds.point _

theorem lowScalar52_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar52 x) (4999687490233764600749611463359320359407 / 2500000000000000000000000000000000000000 : ℝ) (500004192627457812105680767200628871143 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar52
  exact Bounds.mul (lowScalar50_bounds hx) (lowScalar51_bounds hx) (by norm_num)

theorem lowScalar53_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar53 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar53
  exact Bounds.point _

theorem lowScalar54_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar54 x) (0 / 1 : ℝ) (1 / 4000 : ℝ) := by
  unfold lowScalar54
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar53_bounds hx) (by norm_num)

theorem lowScalar55_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar55 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar55
  exact Bounds.point _

theorem lowScalar56_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar56 x) (-1 / 4000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar56
  convert Bounds.neg (lowScalar54_bounds hx) using 1 <;> norm_num

theorem lowScalar57_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar57 x) (3999 / 4000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar57
  exact Bounds.add (lowScalar55_bounds hx) (lowScalar56_bounds hx) (by norm_num)

theorem lowScalar58_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar58 x) (9998749921865232848854014863667874180739 / 10000000000000000000000000000000000000000 : ℝ) (10000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar58
  exact Bounds.sqrt (lowScalar57_bounds hx) (by norm_num)

theorem lowScalar59_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar59 x) (9999999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℝ) (10001250234423838808556153902143410033249 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar59
  exact Bounds.inv (lowScalar58_bounds hx) (by norm_num)

theorem lowScalar60_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar60 x) (9999374980467529201499222926718640718813 / 5000000000000000000000000000000000000000 : ℝ) (20002668194913058797693484782662298565189 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar60
  exact Bounds.mul (lowScalar52_bounds hx) (lowScalar59_bounds hx) (by norm_num)

theorem lowScalar61_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar61 x) (6 / 1 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar61
  exact Bounds.point _

theorem lowScalar62_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar62 x) (24494897427831780981972840747058913919659 / 10000000000000000000000000000000000000000 : ℝ) (1224744871391589049098642037352945695983 / 500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar62
  exact Bounds.sqrt (lowScalar61_bounds hx) (by norm_num)

theorem lowScalar63_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar63 x) (0 / 1 : ℝ) (38273277230987157784332563667279553 / 125000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar63
  exact Bounds.mul (lowScalar62_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar64_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar64 x) (1 / 2 : ℝ) (1 / 2 : ℝ) := by
  unfold lowScalar64
  exact Bounds.point _

theorem lowScalar65_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar65 x) (-38273277230987157784332563667279553 / 125000000000000000000000000000000000000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar65
  convert Bounds.neg (lowScalar63_bounds hx) using 1 <;> norm_num

theorem lowScalar66_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar66 x) (62461726722769012842215667436332720447 / 125000000000000000000000000000000000000 : ℝ) (1 / 2 : ℝ) := by
  unfold lowScalar66
  exact Bounds.add (lowScalar64_bounds hx) (lowScalar65_bounds hx) (by norm_num)

theorem lowScalar67_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar67 x) (12 / 1 : ℝ) (12 / 1 : ℝ) := by
  unfold lowScalar67
  exact Bounds.point _

theorem lowScalar68_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar68 x) (187385180168307038526647002308998161341 / 31250000000000000000000000000000000000 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar68
  exact Bounds.mul (lowScalar66_bounds hx) (lowScalar67_bounds hx) (by norm_num)

theorem lowScalar69_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar69 x) (24487396279281766940163116204132248060961 / 10000000000000000000000000000000000000000 : ℝ) (1224744871391589049098642037352945695983 / 500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar69
  exact Bounds.sqrt (lowScalar68_bounds hx) (by norm_num)

theorem lowScalar70_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar70 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar70
  exact Bounds.point _

theorem lowScalar71_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar71 x) (24487396279281766940163116204132248060961 / 5000000000000000000000000000000000000000 : ℝ) (1224744871391589049098642037352945695983 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar71
  exact Bounds.mul (lowScalar69_bounds hx) (lowScalar70_bounds hx) (by norm_num)

theorem lowScalar72_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar72 x) (0 / 1 : ℝ) (38273277230987157784332563667279553 / 62500000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar72
  exact Bounds.mul (lowScalar71_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar73_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar73 x) (0 / 1 : ℝ) (68465319688145764182121222850100267 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar73
  exact Bounds.mul (lowScalar72_bounds hx) (lowScalar1_bounds hx) (by norm_num)

theorem lowScalar74_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar74 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar74
  exact Bounds.point _

theorem lowScalar75_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar75 x) (-1 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar75
  convert Bounds.neg (lowScalar0_bounds hx) using 1 <;> norm_num

theorem lowScalar76_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar76 x) (7999 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar76
  exact Bounds.add (lowScalar74_bounds hx) (lowScalar75_bounds hx) (by norm_num)

theorem lowScalar77_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar77 x) (4999687490233764600749611463359320359407 / 5000000000000000000000000000000000000000 : ℝ) (10000000000000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar77
  exact Bounds.sqrt (lowScalar76_bounds hx) (by norm_num)

theorem lowScalar78_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar78 x) (9999999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℝ) (5000312529299927091636065971605771080793 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar78
  exact Bounds.inv (lowScalar77_bounds hx) (by norm_num)

theorem lowScalar79_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar79 x) (0 / 1 : ℝ) (34234799585916024163013923473801323 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar79
  exact Bounds.mul (lowScalar73_bounds hx) (lowScalar78_bounds hx) (by norm_num)

theorem lowScalar80_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar80 x) (-34234799585916024163013923473801323 / 5000000000000000000000000000000000000000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar80
  convert Bounds.neg (lowScalar79_bounds hx) using 1 <;> norm_num

theorem lowScalar81_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar81 x) (2498434834111174597664463683529835016557 / 5000000000000000000000000000000000000000 : ℝ) (1 / 2 : ℝ) := by
  unfold lowScalar81
  exact Bounds.add (lowScalar66_bounds hx) (lowScalar80_bounds hx) (by norm_num)

theorem lowScalar82_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar82 x) (7068853986483487406204256091040906457327 / 10000000000000000000000000000000000000000 : ℝ) (7071067811865475244008443621048490392849 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar82
  exact Bounds.sqrt (lowScalar81_bounds hx) (by norm_num)

theorem lowScalar83_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar83 x) (4 / 1 : ℝ) (4 / 1 : ℝ) := by
  unfold lowScalar83
  exact Bounds.point _

theorem lowScalar84_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar84 x) (517 / 50 : ℝ) (517 / 50 : ℝ) := by
  unfold lowScalar84
  exact Bounds.mul (lowScalar2_bounds hx) (lowScalar83_bounds hx) (by norm_num)

theorem lowScalar85_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar85 x) (3 / 1 : ℝ) (3 / 1 : ℝ) := by
  unfold lowScalar85
  exact Bounds.point _

theorem lowScalar86_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar86 x) (0 / 1 : ℝ) (3 / 8000 : ℝ) := by
  unfold lowScalar86
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar85_bounds hx) (by norm_num)

theorem lowScalar87_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar87 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar87
  exact Bounds.point _

theorem lowScalar88_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar88 x) (-3 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar88
  convert Bounds.neg (lowScalar86_bounds hx) using 1 <;> norm_num

theorem lowScalar89_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar89 x) (7997 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar89
  exact Bounds.add (lowScalar87_bounds hx) (lowScalar88_bounds hx) (by norm_num)

theorem lowScalar90_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar90 x) (1 / 1 : ℝ) (10003751406777541578091784419157183943979 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar90
  exact Bounds.inv (lowScalar89_bounds hx) (by norm_num)

theorem lowScalar91_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar91 x) (517 / 50 : ℝ) (103438789546079779917469050894085281980743 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar91
  exact Bounds.mul (lowScalar84_bounds hx) (lowScalar90_bounds hx) (by norm_num)

theorem lowScalar92_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar92 x) (16 / 1 : ℝ) (16 / 1 : ℝ) := by
  unfold lowScalar92
  exact Bounds.point _

theorem lowScalar93_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar93 x) (1034 / 25 : ℝ) (1034 / 25 : ℝ) := by
  unfold lowScalar93
  exact Bounds.mul (lowScalar2_bounds hx) (lowScalar92_bounds hx) (by norm_num)

theorem lowScalar94_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar94 x) (3 / 1 : ℝ) (3 / 1 : ℝ) := by
  unfold lowScalar94
  exact Bounds.point _

theorem lowScalar95_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar95 x) (0 / 1 : ℝ) (3 / 8000 : ℝ) := by
  unfold lowScalar95
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar94_bounds hx) (by norm_num)

theorem lowScalar96_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar96 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar96
  exact Bounds.point _

theorem lowScalar97_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar97 x) (-3 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar97
  convert Bounds.neg (lowScalar95_bounds hx) using 1 <;> norm_num

theorem lowScalar98_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar98 x) (7997 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar98
  exact Bounds.add (lowScalar96_bounds hx) (lowScalar97_bounds hx) (by norm_num)

theorem lowScalar99_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar99 x) (1 / 1 : ℝ) (10003751406777541578091784419157183943979 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar99
  exact Bounds.inv (lowScalar98_bounds hx) (by norm_num)

theorem lowScalar100_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar100 x) (1034 / 25 : ℝ) (103438789546079779917469050894085281980743 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar100
  exact Bounds.mul (lowScalar93_bounds hx) (lowScalar99_bounds hx) (by norm_num)

theorem lowScalar101_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar101 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar101
  exact Bounds.point _

theorem lowScalar102_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar102 x) (1 / 1 : ℝ) (10111803398874989484820458683436563811773 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar102
  exact Bounds.add (lowScalar1_bounds hx) (lowScalar101_bounds hx) (by norm_num)

theorem lowScalar103_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar103 x) (6 / 1 : ℝ) (6 / 1 : ℝ) := by
  unfold lowScalar103
  exact Bounds.point _

theorem lowScalar104_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar104 x) (0 / 1 : ℝ) (3 / 4000 : ℝ) := by
  unfold lowScalar104
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar103_bounds hx) (by norm_num)

theorem lowScalar105_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar105 x) (1 / 1 : ℝ) (10119303398874989484820458683436563811773 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar105
  exact Bounds.add (lowScalar102_bounds hx) (lowScalar104_bounds hx) (by norm_num)

theorem lowScalar106_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar106 x) (1 / 1 : ℝ) (640001882990518215866759253431142654329 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar106
  exact Bounds.pow (lowScalar105_bounds hx) 2 (by norm_num)

theorem lowScalar107_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar107 x) (4 / 1 : ℝ) (4 / 1 : ℝ) := by
  unfold lowScalar107
  exact Bounds.point _

theorem lowScalar108_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar108 x) (4 / 1 : ℝ) (640001882990518215866759253431142654329 / 156250000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar108
  exact Bounds.mul (lowScalar106_bounds hx) (lowScalar107_bounds hx) (by norm_num)

theorem lowScalar109_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar109 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar109
  exact Bounds.point _

theorem lowScalar110_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar110 x) (1 / 2 : ℝ) (1 / 2 : ℝ) := by
  unfold lowScalar110
  exact Bounds.inv (lowScalar109_bounds hx) (by norm_num)

theorem lowScalar111_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar111 x) (2498434834111174597664463683529835016557 / 10000000000000000000000000000000000000000 : ℝ) (1 / 4 : ℝ) := by
  unfold lowScalar111
  exact Bounds.mul (lowScalar81_bounds hx) (lowScalar110_bounds hx) (by norm_num)

theorem lowScalar112_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar112 x) (4999999999999999999999999999999999999999 / 1250000000000000000000000000000000000000 : ℝ) (20485181551084353996235354948533698363123 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar112
  exact Bounds.pow (lowScalar42_bounds hx) 2 (by norm_num)

theorem lowScalar113_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar113 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar113
  exact Bounds.point _

theorem lowScalar114_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar114 x) (4999999999999999999999999999999999999999 / 625000000000000000000000000000000000000 : ℝ) (20485181551084353996235354948533698363123 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar114
  exact Bounds.mul (lowScalar112_bounds hx) (lowScalar113_bounds hx) (by norm_num)

theorem lowScalar115_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar115 x) (0 / 1 : ℝ) (5121295387771088499058838737133424591 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar115
  exact Bounds.mul (lowScalar114_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar116_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar116 x) (-5121295387771088499058838737133424591 / 5000000000000000000000000000000000000000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar116
  convert Bounds.neg (lowScalar115_bounds hx) using 1 <;> norm_num

theorem lowScalar117_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar117 x) (19905537946685059365330768048444545339 / 80000000000000000000000000000000000000 : ℝ) (1 / 4 : ℝ) := by
  unfold lowScalar117
  exact Bounds.add (lowScalar111_bounds hx) (lowScalar116_bounds hx) (by norm_num)

theorem lowScalar118_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar118 x) (5623 / 2000 : ℝ) (5623 / 2000 : ℝ) := by
  unfold lowScalar118
  exact Bounds.point _

theorem lowScalar119_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar119 x) (999412249309389778928032130881 / 256000000000000000000000000 : ℝ) (999412249309389778928032130881 / 256000000000000000000000000 : ℝ) := by
  unfold lowScalar119
  exact Bounds.pow (lowScalar118_bounds hx) 8 (by norm_num)

theorem lowScalar120_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar120 x) (16 / 1 : ℝ) (16 / 1 : ℝ) := by
  unfold lowScalar120
  exact Bounds.point _

theorem lowScalar121_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar121 x) (1034 / 25 : ℝ) (1034 / 25 : ℝ) := by
  unfold lowScalar121
  exact Bounds.mul (lowScalar2_bounds hx) (lowScalar120_bounds hx) (by norm_num)

theorem lowScalar122_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar122 x) (1143094552336 / 390625 : ℝ) (1143094552336 / 390625 : ℝ) := by
  unfold lowScalar122
  exact Bounds.pow (lowScalar121_bounds hx) 4 (by norm_num)

theorem lowScalar123_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar123 x) (71401418607714483406567055913177553518001 / 6250000000000000000000000000000 : ℝ) (71401418607714483406567055913177553518001 / 6250000000000000000000000000000 : ℝ) := by
  unfold lowScalar123
  exact Bounds.mul (lowScalar119_bounds hx) (lowScalar122_bounds hx) (by norm_num)

theorem lowScalar124_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar124 x) (3 / 1 : ℝ) (3 / 1 : ℝ) := by
  unfold lowScalar124
  exact Bounds.point _

theorem lowScalar125_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar125 x) (0 / 1 : ℝ) (3 / 8000 : ℝ) := by
  unfold lowScalar125
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar124_bounds hx) (by norm_num)

theorem lowScalar126_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar126 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar126
  exact Bounds.point _

theorem lowScalar127_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar127 x) (-3 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar127
  convert Bounds.neg (lowScalar125_bounds hx) using 1 <;> norm_num

theorem lowScalar128_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar128 x) (7997 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar128
  exact Bounds.add (lowScalar126_bounds hx) (lowScalar127_bounds hx) (by norm_num)

theorem lowScalar129_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar129 x) (5 / 1 : ℝ) (5 / 1 : ℝ) := by
  unfold lowScalar129
  exact Bounds.point _

theorem lowScalar130_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar130 x) (0 / 1 : ℝ) (1 / 1600 : ℝ) := by
  unfold lowScalar130
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar129_bounds hx) (by norm_num)

theorem lowScalar131_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar131 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar131
  exact Bounds.point _

theorem lowScalar132_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar132 x) (-1 / 1600 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar132
  convert Bounds.neg (lowScalar130_bounds hx) using 1 <;> norm_num

theorem lowScalar133_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar133 x) (1599 / 1600 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar133
  exact Bounds.add (lowScalar131_bounds hx) (lowScalar132_bounds hx) (by norm_num)

theorem lowScalar134_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar134 x) (12787203 / 12800000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar134
  exact Bounds.mul (lowScalar128_bounds hx) (lowScalar133_bounds hx) (by norm_num)

theorem lowScalar135_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar135 x) (7 / 1 : ℝ) (7 / 1 : ℝ) := by
  unfold lowScalar135
  exact Bounds.point _

theorem lowScalar136_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar136 x) (0 / 1 : ℝ) (7 / 8000 : ℝ) := by
  unfold lowScalar136
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar135_bounds hx) (by norm_num)

theorem lowScalar137_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar137 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar137
  exact Bounds.point _

theorem lowScalar138_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar138 x) (-7 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar138
  convert Bounds.neg (lowScalar136_bounds hx) using 1 <;> norm_num

theorem lowScalar139_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar139 x) (7993 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar139
  exact Bounds.add (lowScalar137_bounds hx) (lowScalar138_bounds hx) (by norm_num)

theorem lowScalar140_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar140 x) (102208113579 / 102400000000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar140
  exact Bounds.mul (lowScalar134_bounds hx) (lowScalar139_bounds hx) (by norm_num)

theorem lowScalar141_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar141 x) (9 / 1 : ℝ) (9 / 1 : ℝ) := by
  unfold lowScalar141
  exact Bounds.point _

theorem lowScalar142_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar142 x) (0 / 1 : ℝ) (9 / 8000 : ℝ) := by
  unfold lowScalar142
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar141_bounds hx) (by norm_num)

theorem lowScalar143_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar143 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar143
  exact Bounds.point _

theorem lowScalar144_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar144 x) (-9 / 8000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar144
  convert Bounds.neg (lowScalar142_bounds hx) using 1 <;> norm_num

theorem lowScalar145_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar145 x) (7991 / 8000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar145
  exact Bounds.add (lowScalar143_bounds hx) (lowScalar144_bounds hx) (by norm_num)

theorem lowScalar146_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar146 x) (816745035609789 / 819200000000000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar146
  exact Bounds.mul (lowScalar140_bounds hx) (lowScalar145_bounds hx) (by norm_num)

theorem lowScalar147_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar147 x) (36729199550488094270074164765963331 / 2500000000000000000000000000000000000000 : ℝ) (1 / 65536 : ℝ) := by
  unfold lowScalar147
  exact Bounds.pow (lowScalar117_bounds hx) 8 (by norm_num)

theorem lowScalar148_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar148 x) (36619130120584038923812997645540457 / 2500000000000000000000000000000000000000 : ℝ) (1 / 65536 : ℝ) := by
  unfold lowScalar148
  exact Bounds.mul (lowScalar146_bounds hx) (lowScalar147_bounds hx) (by norm_num)

theorem lowScalar149_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar149 x) (65536 / 1 : ℝ) (136540654666983524265965627150297551974801971 / 2000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar149
  exact Bounds.inv (lowScalar148_bounds hx) (by norm_num)

theorem lowScalar150_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar150 x) (71401418607714483406567055913177553518001 / 95367431640625000000000000 : ℝ) (7799357152678939864134173213610526488976258474811640041 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar150
  exact Bounds.mul (lowScalar123_bounds hx) (lowScalar149_bounds hx) (by norm_num)

theorem lowScalar151_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar151 x) (132 / 5 : ℝ) (132 / 5 : ℝ) := by
  unfold lowScalar151
  exact Bounds.point _

theorem lowScalar152_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar152 x) (0 / 1 : ℝ) (33 / 10000 : ℝ) := by
  unfold lowScalar152
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar151_bounds hx) (by norm_num)

theorem lowScalar153_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar153 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar153
  exact Bounds.point _

theorem lowScalar154_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar154 x) (-33 / 10000 : ℝ) (0 / 1 : ℝ) := by
  unfold lowScalar154
  convert Bounds.neg (lowScalar152_bounds hx) using 1 <;> norm_num

theorem lowScalar155_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar155 x) (9967 / 10000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar155
  exact Bounds.add (lowScalar153_bounds hx) (lowScalar154_bounds hx) (by norm_num)

theorem lowScalar156_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar156 x) (66 / 125 : ℝ) (66 / 125 : ℝ) := by
  unfold lowScalar156
  exact Bounds.point _

theorem lowScalar157_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar157 x) (1 / 1 : ℝ) (250827731513996187418480987257951239089 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar157
  exact Bounds.inv (lowScalar155_bounds hx) (by norm_num)

theorem lowScalar158_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar158 x) (66 / 125 : ℝ) (132437042239389986956957961272198254239 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar158
  exact Bounds.mul (lowScalar156_bounds hx) (lowScalar157_bounds hx) (by norm_num)

theorem lowScalar159_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar159 x) (45 / 1 : ℝ) (45 / 1 : ℝ) := by
  unfold lowScalar159
  exact Bounds.point _

theorem lowScalar160_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar160 x) (0 / 1 : ℝ) (9 / 1600 : ℝ) := by
  unfold lowScalar160
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar159_bounds hx) (by norm_num)

theorem lowScalar161_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar161 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar161
  exact Bounds.point _

theorem lowScalar162_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar162 x) (1 / 1 : ℝ) (1609 / 1600 : ℝ) := by
  unfold lowScalar162
  exact Bounds.add (lowScalar160_bounds hx) (lowScalar161_bounds hx) (by norm_num)

theorem lowScalar163_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar163 x) (66 / 125 : ℝ) (1331820006019865556335908498043543694191 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar163
  exact Bounds.mul (lowScalar158_bounds hx) (lowScalar162_bounds hx) (by norm_num)

theorem lowScalar164_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar164 x) (27 / 50 : ℝ) (27 / 50 : ℝ) := by
  unfold lowScalar164
  exact Bounds.point _

theorem lowScalar165_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar165 x) (0 / 1 : ℝ) (27 / 400000 : ℝ) := by
  unfold lowScalar165
  exact Bounds.mul (lowScalar0_bounds hx) (lowScalar164_bounds hx) (by norm_num)

theorem lowScalar166_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar166 x) (0 / 1 : ℝ) (82158383625774917018545467420120320093 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar166
  exact Bounds.sqrt (lowScalar165_bounds hx) (by norm_num)

theorem lowScalar167_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar167 x) (12 / 1 : ℝ) (12 / 1 : ℝ) := by
  unfold lowScalar167
  exact Bounds.point _

theorem lowScalar168_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar168 x) (0 / 1 : ℝ) (246475150877324751055636402260360960279 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar168
  exact Bounds.mul (lowScalar166_bounds hx) (lowScalar167_bounds hx) (by norm_num)

theorem lowScalar169_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar169 x) (0 / 1 : ℝ) (123237575438662375527818201130180481 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar169
  exact Bounds.mul (lowScalar168_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar170_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar170 x) (512 / 1 : ℝ) (512 / 1 : ℝ) := by
  unfold lowScalar170
  exact Bounds.point _

theorem lowScalar171_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar171 x) (1 / 512 : ℝ) (1 / 512 : ℝ) := by
  unfold lowScalar171
  exact Bounds.inv (lowScalar170_bounds hx) (by norm_num)

theorem lowScalar172_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar172 x) (0 / 1 : ℝ) (15043649345539840762673120255149 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar172
  exact Bounds.mul (lowScalar169_bounds hx) (lowScalar171_bounds hx) (by norm_num)

theorem lowScalar173_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar173 x) (1086956521739130434782608695652173913043 / 500000000000000000000000000000000000000 : ℝ) (25571329489897450290368667448212634457471 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar173
  exact Bounds.inv (lowScalar14_bounds hx) (by norm_num)

theorem lowScalar174_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar174 x) (0 / 1 : ℝ) (615497782632447053107626487301081 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar174
  exact Bounds.mul (lowScalar172_bounds hx) (lowScalar173_bounds hx) (by norm_num)

theorem lowScalar175_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar175 x) (1 / 1 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar175
  exact Bounds.point _

theorem lowScalar176_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar176 x) (1 / 1 : ℝ) (10000000615497782632447053107626487301081 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar176
  exact Bounds.add (lowScalar174_bounds hx) (lowScalar175_bounds hx) (by norm_num)

theorem lowScalar177_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar177 x) (66 / 125 : ℝ) (1065456070394473290729489673634280317499 / 2000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar177
  exact Bounds.mul (lowScalar163_bounds hx) (lowScalar176_bounds hx) (by norm_num)

theorem lowScalar178_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar178 x) (7979 / 20000 : ℝ) (7979 / 20000 : ℝ) := by
  unfold lowScalar178
  exact Bounds.point _

theorem lowScalar179_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar179 x) (12099 / 50000 : ℝ) (12099 / 50000 : ℝ) := by
  unfold lowScalar179
  exact Bounds.point _

theorem lowScalar180_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar180 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar180
  exact Bounds.point _

theorem lowScalar181_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar181 x) (441941738241592202750527726315530649553 / 312500000000000000000000000000000000000 : ℝ) (14142135623730950488016887242096980785697 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar181
  exact Bounds.sqrt (lowScalar180_bounds hx) (by norm_num)

theorem lowScalar182_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar182 x) (4125143 / 1000000 : ℝ) (20633452544704264099037138927097661623109 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar182
  exact Bounds.mul (lowScalar178_bounds hx) (lowScalar91_bounds hx) (by norm_num)

theorem lowScalar183_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar183 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (7774554856939554426154536161775240711421 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar183
  exact Bounds.sqrt (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar184_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar184 x) (15156743199020741474297758529676727401491 / 5000000000000000000000000000000000000000 : ℝ) (32083181739372469040060424425153434331909 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar184
  exact Bounds.mul (lowScalar182_bounds hx) (lowScalar183_bounds hx) (by norm_num)

theorem lowScalar185_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar185 x) (0 / 1 : ℝ) (1002599429355389657501888263286044823 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar185
  exact Bounds.mul (lowScalar184_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar186_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar186 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar186
  exact Bounds.point _

theorem lowScalar187_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar187 x) (7068853986483487406204256091040906457327 / 5000000000000000000000000000000000000000 : ℝ) (7071067811865475244008443621048490392849 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar187
  exact Bounds.mul (lowScalar82_bounds hx) (lowScalar186_bounds hx) (by norm_num)

theorem lowScalar188_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar188 x) (7071067811865475244008443621048490392847 / 10000000000000000000000000000000000000000 : ℝ) (7073282330573825644252098652429648824501 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar188
  exact Bounds.inv (lowScalar187_bounds hx) (by norm_num)

theorem lowScalar189_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar189 x) (0 / 1 : ℝ) (283666753132115128725980045379590307 / 1000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar189
  exact Bounds.mul (lowScalar185_bounds hx) (lowScalar188_bounds hx) (by norm_num)

theorem lowScalar190_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar190 x) (0 / 1 : ℝ) (7979 / 160000000 : ℝ) := by
  unfold lowScalar190
  exact Bounds.mul (lowScalar178_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar191_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar191 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar191
  exact Bounds.point _

theorem lowScalar192_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar192 x) (441941738241592202750527726315530649553 / 156250000000000000000000000000000000000 : ℝ) (14142135623730950488016887242096980785697 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar192
  exact Bounds.mul (lowScalar181_bounds hx) (lowScalar191_bounds hx) (by norm_num)

theorem lowScalar193_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar193 x) (176610710370759870993571630546459861121 / 500000000000000000000000000000000000000 : ℝ) (1767766952966368811002110905262122598213 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar193
  exact Bounds.pow (lowScalar82_bounds hx) 3 (by norm_num)

theorem lowScalar194_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar194 x) (9990610474667009576366359267239215855317 / 10000000000000000000000000000000000000000 : ℝ) (5000000000000000000000000000000000000003 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar194
  exact Bounds.mul (lowScalar192_bounds hx) (lowScalar193_bounds hx) (by norm_num)

theorem lowScalar195_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar195 x) (4999999999999999999999999999999999999997 / 5000000000000000000000000000000000000000 : ℝ) (10009398349937473044845494657092329823051 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar195
  exact Bounds.inv (lowScalar194_bounds hx) (by norm_num)

theorem lowScalar196_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar196 x) (0 / 1 : ℝ) (499156183963444358905138761680873123 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar196
  exact Bounds.mul (lowScalar190_bounds hx) (lowScalar195_bounds hx) (by norm_num)

theorem lowScalar197_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar197 x) (312675138028423937283598417849335239061 / 500000000000000000000000000000000000000 : ℝ) (3391164991562634069532278163312984552599 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar197
  exact Bounds.sqrt (lowScalar14_bounds hx) (by norm_num)

theorem lowScalar198_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar198 x) (1843024451936214168224064219191839430759 / 1250000000000000000000000000000000000000 : ℝ) (124929984028499886579191234599984838793 / 78125000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar198
  exact Bounds.inv (lowScalar197_bounds hx) (by norm_num)

theorem lowScalar199_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar199 x) (609819930656654543981978368846195830849537 / 10000000000000000000000000000000000000000 : ℝ) (661637443887058326413569819953570324228833 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar199
  exact Bounds.mul (lowScalar100_bounds hx) (lowScalar198_bounds hx) (by norm_num)

theorem lowScalar200_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar200 x) (267289 / 2500 : ℝ) (1069958318275818356230216317363853260653631 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar200
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar91_bounds hx) (by norm_num)

theorem lowScalar201_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar201 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (7774554856939554426154536161775240711421 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar201
  exact Bounds.sqrt (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar202_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar202 x) (785665996630527468826864635652875605120533 / 10000000000000000000000000000000000000000 : ℝ) (415922482003707061127023760061278162907943 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar202
  exact Bounds.mul (lowScalar200_bounds hx) (lowScalar201_bounds hx) (by norm_num)

theorem lowScalar203_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar203 x) (0 / 1 : ℝ) (103980620500926765281755940015319540727 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar203
  exact Bounds.mul (lowScalar202_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar204_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar204 x) (609819930656654543981978368846195830849537 / 10000000000000000000000000000000000000000 : ℝ) (16543535612688981329471289397339641094239 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar204
  exact Bounds.add (lowScalar199_bounds hx) (lowScalar203_bounds hx) (by norm_num)

theorem lowScalar205_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar205 x) (0 / 1 : ℝ) (33031232422772697395874487330414430773 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar205
  exact Bounds.mul (lowScalar196_bounds hx) (lowScalar204_bounds hx) (by norm_num)

theorem lowScalar206_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar206 x) (0 / 1 : ℝ) (35867899954093848683134287784210333843 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar206
  exact Bounds.add (lowScalar189_bounds hx) (lowScalar205_bounds hx) (by norm_num)

theorem lowScalar207_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar207 x) (0 / 1 : ℝ) (12099 / 400000000 : ℝ) := by
  unfold lowScalar207
  exact Bounds.mul (lowScalar179_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar208_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar208 x) (2 / 1 : ℝ) (20012529171203156192123098718918491710447 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar208
  exact Bounds.inv (lowScalar81_bounds hx) (by norm_num)

theorem lowScalar209_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar209 x) (0 / 1 : ℝ) (605328976105967466921243428500487079 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar209
  exact Bounds.mul (lowScalar207_bounds hx) (lowScalar208_bounds hx) (by norm_num)

theorem lowScalar210_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar210 x) (267289 / 625 : ℝ) (4279833273103273424920865269455413042614521 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar210
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar100_bounds hx) (by norm_num)

theorem lowScalar211_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar211 x) (517 / 25 : ℝ) (206877579092159559834938101788170563961487 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar211
  exact Bounds.sqrt (lowScalar210_bounds hx) (by norm_num)

theorem lowScalar212_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar212 x) (1004870949425845428047425655755077868537 / 312500000000000000000000000000000000000 : ℝ) (32161901303573422277151275913063196447951 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar212
  exact Bounds.sqrt (lowScalar91_bounds hx) (by norm_num)

theorem lowScalar213_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar213 x) (166245849873011867616166100488120082570761 / 5000000000000000000000000000000000000000 : ℝ) (166339407017106007925844288078566187956391 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar213
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar212_bounds hx) (by norm_num)

theorem lowScalar214_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar214 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (7774554856939554426154536161775240711421 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar214
  exact Bounds.sqrt (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar215_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar215 x) (48866100485305761708815698942888772882721 / 2000000000000000000000000000000000000000 : ℝ) (129321484472528691509349005875139085077299 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar215
  exact Bounds.mul (lowScalar213_bounds hx) (lowScalar214_bounds hx) (by norm_num)

theorem lowScalar216_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar216 x) (0 / 1 : ℝ) (3233037111813217287733725146878477127 / 1000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar216
  exact Bounds.mul (lowScalar215_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar217_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar217 x) (517 / 25 : ℝ) (206909909463277692007815439039639348732757 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar217
  exact Bounds.add (lowScalar211_bounds hx) (lowScalar216_bounds hx) (by norm_num)

theorem lowScalar218_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar218 x) (0 / 1 : ℝ) (3131214091039607847336541379298182049 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar218
  exact Bounds.mul (lowScalar209_bounds hx) (lowScalar217_bounds hx) (by norm_num)

theorem lowScalar219_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar219 x) (4125143 / 1000000 : ℝ) (20633452544704264099037138927097661623109 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar219
  exact Bounds.mul (lowScalar178_bounds hx) (lowScalar91_bounds hx) (by norm_num)

theorem lowScalar220_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar220 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (7774554856939554426154536161775240711421 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar220
  exact Bounds.sqrt (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar221_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar221 x) (15156743199020741474297758529676727401491 / 5000000000000000000000000000000000000000 : ℝ) (32083181739372469040060424425153434331909 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar221
  exact Bounds.mul (lowScalar219_bounds hx) (lowScalar220_bounds hx) (by norm_num)

theorem lowScalar222_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar222 x) (0 / 1 : ℝ) (1002599429355389657501888263286044823 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar222
  exact Bounds.mul (lowScalar221_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar223_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar223 x) (9996869178120067001969330525144914397221 / 10000000000000000000000000000000000000000 : ℝ) (5000000000000000000000000000000000000001 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar223
  exact Bounds.mul (lowScalar181_bounds hx) (lowScalar82_bounds hx) (by norm_num)

theorem lowScalar224_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar224 x) (4999999999999999999999999999999999999999 / 5000000000000000000000000000000000000000 : ℝ) (10003131802391478084638269295086531471777 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar224
  exact Bounds.inv (lowScalar223_bounds hx) (by norm_num)

theorem lowScalar225_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar225 x) (0 / 1 : ℝ) (4011653694737778538928998436299305081 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar225
  exact Bounds.mul (lowScalar222_bounds hx) (lowScalar224_bounds hx) (by norm_num)

theorem lowScalar226_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar226 x) (55835999999999999999999999999999999999989 / 10000000000000000000000000000000000000000 : ℝ) (3907639685704860430136283130102056915921 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar226
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar227_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar227 x) (0 / 1 : ℝ) (976909921426215107534070782525514229 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar227
  exact Bounds.mul (lowScalar226_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar228_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar228 x) (0 / 1 : ℝ) (12099 / 400000000 : ℝ) := by
  unfold lowScalar228
  exact Bounds.mul (lowScalar179_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar229_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar229 x) (2 / 1 : ℝ) (2 / 1 : ℝ) := by
  unfold lowScalar229
  exact Bounds.point _

theorem lowScalar230_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar230 x) (2498434834111174597664463683529835016557 / 2500000000000000000000000000000000000000 : ℝ) (1 / 1 : ℝ) := by
  unfold lowScalar230
  exact Bounds.mul (lowScalar81_bounds hx) (lowScalar229_bounds hx) (by norm_num)

theorem lowScalar231_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar231 x) (1 / 1 : ℝ) (1250783073200197262007693669932405731903 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar231
  exact Bounds.inv (lowScalar230_bounds hx) (by norm_num)

theorem lowScalar232_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar232 x) (0 / 1 : ℝ) (15133224402649186673031085712512177 / 500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar232
  exact Bounds.mul (lowScalar228_bounds hx) (lowScalar231_bounds hx) (by norm_num)

theorem lowScalar233_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar233 x) (267289 / 2500 : ℝ) (1069958318275818356230216317363853260653631 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar233
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar91_bounds hx) (by norm_num)

theorem lowScalar234_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar234 x) (577344239999999999999999999999999999999893 / 10000000000000000000000000000000000000000 : ℝ) (646722430514455030198070957653204247762881 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar234
  exact Bounds.mul (lowScalar233_bounds hx) (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar235_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar235 x) (0 / 1 : ℝ) (80840303814306878774758869706650530971 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar235
  exact Bounds.mul (lowScalar234_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar236_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar236 x) (1034 / 25 : ℝ) (413835998488133426548650962446047778453943 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar236
  exact Bounds.add (lowScalar100_bounds hx) (lowScalar235_bounds hx) (by norm_num)

theorem lowScalar237_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar237 x) (0 / 1 : ℝ) (391417064438457043319808008819169767 / 312500000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar237
  exact Bounds.mul (lowScalar232_bounds hx) (lowScalar236_bounds hx) (by norm_num)

theorem lowScalar238_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar238 x) (0 / 1 : ℝ) (2542578179180043280813302817802193297 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar238
  exact Bounds.add (lowScalar227_bounds hx) (lowScalar237_bounds hx) (by norm_num)

theorem lowScalar239_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar239 x) (5642005007087462697194337165234590484453 / 10000000000000000000000000000000000000000 : ℝ) (2821002503543731348597168582617295242227 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar239
  exact Bounds.mul (lowScalar181_bounds hx) (lowScalar178_bounds hx) (by norm_num)

theorem lowScalar240_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar240 x) (0 / 1 : ℝ) (705250625885932837149292145654323811 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar240
  exact Bounds.mul (lowScalar239_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar241_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar241 x) (2828427124746190097603377448419396157139 / 2000000000000000000000000000000000000000 : ℝ) (7073282330573825644252098652429648824501 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar241
  exact Bounds.inv (lowScalar82_bounds hx) (by norm_num)

theorem lowScalar242_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar242 x) (0 / 1 : ℝ) (498843679070510022733304691909346467 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar242
  exact Bounds.mul (lowScalar240_bounds hx) (lowScalar241_bounds hx) (by norm_num)

theorem lowScalar243_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar243 x) (267289 / 625 : ℝ) (4279833273103273424920865269455413042614521 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar243
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar100_bounds hx) (by norm_num)

theorem lowScalar244_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar244 x) (517 / 25 : ℝ) (206877579092159559834938101788170563961487 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar244
  exact Bounds.sqrt (lowScalar243_bounds hx) (by norm_num)

theorem lowScalar245_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar245 x) (7348469228349534294591852224117674175897 / 10000000000000000000000000000000000000000 : ℝ) (7774554856939554426154536161775240711421 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar245
  exact Bounds.sqrt (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar246_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar246 x) (151966343642268369212159503994753501957549 / 10000000000000000000000000000000000000000 : ℝ) (20104763591535574031871427763600347369287 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar246
  exact Bounds.mul (lowScalar244_bounds hx) (lowScalar245_bounds hx) (by norm_num)

theorem lowScalar247_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar247 x) (1004870949425845428047425655755077868537 / 312500000000000000000000000000000000000 : ℝ) (32161901303573422277151275913063196447951 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar247
  exact Bounds.sqrt (lowScalar91_bounds hx) (by norm_num)

theorem lowScalar248_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar248 x) (166245849873011867616166100488120082570761 / 5000000000000000000000000000000000000000 : ℝ) (166339407017106007925844288078566187956391 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar248
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar247_bounds hx) (by norm_num)

theorem lowScalar249_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar249 x) (44886379465713204256364847131792422294097 / 2500000000000000000000000000000000000000 : ℝ) (25135424380313277757659368409759838899607 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar249
  exact Bounds.mul (lowScalar248_bounds hx) (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar250_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar250 x) (0 / 1 : ℝ) (251354243803132777576593684097598389 / 100000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar250
  exact Bounds.mul (lowScalar249_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar251_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar251 x) (151966343642268369212159503994753501957549 / 10000000000000000000000000000000000000000 : ℝ) (40215811039166226383182270369303134698299 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar251
  exact Bounds.add (lowScalar246_bounds hx) (lowScalar250_bounds hx) (by norm_num)

theorem lowScalar252_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar252 x) (0 / 1 : ℝ) (4012280627116422242428680777298262183 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar252
  exact Bounds.mul (lowScalar242_bounds hx) (lowScalar251_bounds hx) (by norm_num)

theorem lowScalar253_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar253 x) (55835999999999999999999999999999999999989 / 10000000000000000000000000000000000000000 : ℝ) (3907639685704860430136283130102056915921 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar253
  exact Bounds.mul (lowScalar91_bounds hx) (lowScalar27_bounds hx) (by norm_num)

theorem lowScalar254_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar254 x) (0 / 1 : ℝ) (976909921426215107534070782525514229 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar254
  exact Bounds.mul (lowScalar253_bounds hx) (lowScalar0_bounds hx) (by norm_num)

theorem lowScalar255_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar255 x) (0 / 1 : ℝ) (298023223877 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar255
  exact Bounds.pow (lowScalar0_bounds hx) 7 (by norm_num)

theorem lowScalar256_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar256 x) (0 / 1 : ℝ) (3719023300495227144691005867 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar256
  exact Bounds.mul (lowScalar150_bounds hx) (lowScalar255_bounds hx) (by norm_num)

theorem lowScalar257_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar257 x) (11693829880669218097240096618297437427 / 500000000000000000000000000000000000000 : ℝ) (447745600000000000000000000000000000001 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar257
  exact Bounds.pow (lowScalar14_bounds hx) 4 (by norm_num)

theorem lowScalar258_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar258 x) (13958819472486161784727756118653092291663 / 625000000000000000000000000000000000000 : ℝ) (106893978513091265792644256490720665631953 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar258
  exact Bounds.inv (lowScalar257_bounds hx) (by norm_num)

theorem lowScalar259_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar259 x) (0 / 1 : ℝ) (39754119677282257227303687897 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar259
  exact Bounds.mul (lowScalar256_bounds hx) (lowScalar258_bounds hx) (by norm_num)

theorem lowScalar260_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar260 x) (3 / 2 : ℝ) (3 / 2 : ℝ) := by
  unfold lowScalar260
  exact Bounds.point _

theorem lowScalar261_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar261 x) (23937 / 40000 : ℝ) (23937 / 40000 : ℝ) := by
  unfold lowScalar261
  exact Bounds.mul (lowScalar178_bounds hx) (lowScalar260_bounds hx) (by norm_num)

theorem lowScalar262_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar262 x) (7 / 1 : ℝ) (7 / 1 : ℝ) := by
  unfold lowScalar262
  exact Bounds.point _

theorem lowScalar263_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar263 x) (167559 / 40000 : ℝ) (167559 / 40000 : ℝ) := by
  unfold lowScalar263
  exact Bounds.mul (lowScalar261_bounds hx) (lowScalar262_bounds hx) (by norm_num)

theorem lowScalar264_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar264 x) (0 / 1 : ℝ) (333058026950286886937488932017 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar264
  exact Bounds.mul (lowScalar263_bounds hx) (lowScalar259_bounds hx) (by norm_num)

theorem lowScalar265_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar265 x) (312675138028423937283598417849335239061 / 500000000000000000000000000000000000000 : ℝ) (3391164991562634069532278163312984552599 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar265
  exact Bounds.sqrt (lowScalar14_bounds hx) (by norm_num)

theorem lowScalar266_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar266 x) (4420509791852998443669798267204964779979 / 10000000000000000000000000000000000000000 : ℝ) (4795831523312719541597438064162693919999 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar266
  exact Bounds.mul (lowScalar82_bounds hx) (lowScalar265_bounds hx) (by norm_num)

theorem lowScalar267_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar267 x) (20851441405707476267814948105055190956497 / 10000000000000000000000000000000000000000 : ℝ) (22621825243844057413610389703138076607167 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar267
  exact Bounds.inv (lowScalar266_bounds hx) (by norm_num)

theorem lowScalar268_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar268 x) (0 / 1 : ℝ) (753438048172889430182421270493 / 5000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar268
  exact Bounds.mul (lowScalar264_bounds hx) (lowScalar267_bounds hx) (by norm_num)

theorem lowScalar269_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar269 x) (12 / 1 : ℝ) (12 / 1 : ℝ) := by
  unfold lowScalar269
  exact Bounds.point _

theorem lowScalar270_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar270 x) (1325825214724776608251583178946591948659 / 78125000000000000000000000000000000000 : ℝ) (42426406871192851464050661726290942357091 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar270
  exact Bounds.mul (lowScalar181_bounds hx) (lowScalar269_bounds hx) (by norm_num)

theorem lowScalar271_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar271 x) (0 / 1 : ℝ) (67464978249378836032667027847 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar271
  exact Bounds.mul (lowScalar270_bounds hx) (lowScalar259_bounds hx) (by norm_num)

theorem lowScalar272_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar272 x) (28 / 1 : ℝ) (28 / 1 : ℝ) := by
  unfold lowScalar272
  exact Bounds.point _

theorem lowScalar273_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar273 x) (0 / 1 : ℝ) (278278837740975800591125815279 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar273
  exact Bounds.mul (lowScalar259_bounds hx) (lowScalar272_bounds hx) (by norm_num)

theorem lowScalar274_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar274 x) (24 / 1 : ℝ) (24 / 1 : ℝ) := by
  unfold lowScalar274
  exact Bounds.point _

theorem lowScalar275_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar275 x) (1325825214724776608251583178946591948659 / 39062500000000000000000000000000000000 : ℝ) (42426406871192851464050661726290942357091 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar275
  exact Bounds.mul (lowScalar181_bounds hx) (lowScalar274_bounds hx) (by norm_num)

theorem lowScalar276_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar276 x) (0 / 1 : ℝ) (5397198259950306882613362227759 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar276
  exact Bounds.mul (lowScalar275_bounds hx) (lowScalar259_bounds hx) (by norm_num)

theorem lowScalar277_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar277 x) (252 / 1 : ℝ) (252 / 1 : ℝ) := by
  unfold lowScalar277
  exact Bounds.point _

theorem lowScalar278_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar278 x) (0 / 1 : ℝ) (2504509539668782205320132337511 / 625000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar278
  exact Bounds.mul (lowScalar259_bounds hx) (lowScalar277_bounds hx) (by norm_num)

theorem lowScalar279_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar279 x) (0 / 1 : ℝ) (35867901460969945028913148149052874829 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar279
  exact Bounds.add (lowScalar206_bounds hx) (lowScalar268_bounds hx) (by norm_num)

theorem lowScalar280_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar280 x) (0 / 1 : ℝ) (3131214765689390341124901705968460519 / 2500000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar280
  exact Bounds.add (lowScalar218_bounds hx) (lowScalar271_bounds hx) (by norm_num)

theorem lowScalar281_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar281 x) (0 / 1 : ℝ) (508515747147543752552980800010764771 / 250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar281
  exact Bounds.add (lowScalar238_bounds hx) (lowScalar273_bounds hx) (by norm_num)

theorem lowScalar282_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar282 x) (0 / 1 : ℝ) (16049127905663948920021605722555276491 / 10000000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar282
  exact Bounds.add (lowScalar252_bounds hx) (lowScalar276_bounds hx) (by norm_num)

theorem lowScalar283_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lowScalar283 x) (0 / 1 : ℝ) (976914930445294445098481422790189251 / 1250000000000000000000000000000000000000 : ℝ) := by
  unfold lowScalar283
  exact Bounds.add (lowScalar254_bounds hx) (lowScalar278_bounds hx) (by norm_num)

theorem qLower_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (qLower x) (3910629677643758441044515243437882174731 / 10000000000000000000000000000000000000000 : ℝ) (2300000000000000000000000000000000000001 / 5000000000000000000000000000000000000000 : ℝ) := lowScalar14_bounds hx

theorem qUpper_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (qUpper x) (5399999999999999999999999999999999999999 / 10000000000000000000000000000000000000000 : ℝ) (1208874064471248311791096951312423565053 / 2000000000000000000000000000000000000000 : ℝ) := lowScalar27_bounds hx

theorem lambdaScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (lambdaScaled x) (9999999999999999999999999999999999999999 / 5000000000000000000000000000000000000000 : ℝ) (20241137098040887483561113202444700099627 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar42_bounds hx

theorem sigmaScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (sigmaScaled x) (9999374980467529201499222926718640718813 / 5000000000000000000000000000000000000000 : ℝ) (20002668194913058797693484782662298565189 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar60_bounds hx

theorem sigmaFloorScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (sigmaFloorScaled x) (7068853986483487406204256091040906457327 / 10000000000000000000000000000000000000000 : ℝ) (7071067811865475244008443621048490392849 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar82_bounds hx

theorem hScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (hScaled x) (517 / 50 : ℝ) (103438789546079779917469050894085281980743 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar91_bounds hx

theorem vScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (vScaled x) (1034 / 25 : ℝ) (103438789546079779917469050894085281980743 / 2500000000000000000000000000000000000000 : ℝ) := lowScalar100_bounds hx

theorem gScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (gScaled x) (4 / 1 : ℝ) (640001882990518215866759253431142654329 / 156250000000000000000000000000000000000 : ℝ) := lowScalar108_bounds hx

theorem gapScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (gapScaled x) (19905537946685059365330768048444545339 / 80000000000000000000000000000000000000 : ℝ) (1 / 4 : ℝ) := lowScalar117_bounds hx

theorem exceptionalScaled_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (exceptionalScaled x) (71401418607714483406567055913177553518001 / 95367431640625000000000000 : ℝ) (7799357152678939864134173213610526488976258474811640041 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar150_bounds hx

theorem nodeMoment12_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (nodeMoment12 x) (66 / 125 : ℝ) (1065456070394473290729489673634280317499 / 2000000000000000000000000000000000000000 : ℝ) := lowScalar177_bounds hx

theorem locationA_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (locationA x) (0 / 1 : ℝ) (35867901460969945028913148149052874829 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar279_bounds hx

theorem locationB_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (locationB x) (0 / 1 : ℝ) (3131214765689390341124901705968460519 / 2500000000000000000000000000000000000000 : ℝ) := lowScalar280_bounds hx

theorem locationC_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (locationC x) (0 / 1 : ℝ) (4011653694737778538928998436299305081 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar225_bounds hx

theorem energyA_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (energyA x) (0 / 1 : ℝ) (508515747147543752552980800010764771 / 250000000000000000000000000000000000000 : ℝ) := lowScalar281_bounds hx

theorem energyB_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (energyB x) (0 / 1 : ℝ) (16049127905663948920021605722555276491 / 10000000000000000000000000000000000000000 : ℝ) := lowScalar282_bounds hx

theorem energyC_bounds {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    Bounds (energyC x) (0 / 1 : ℝ) (976914930445294445098481422790189251 / 1250000000000000000000000000000000000000 : ℝ) := lowScalar283_bounds hx


end BstLean.Part292
