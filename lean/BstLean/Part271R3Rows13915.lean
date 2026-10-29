import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 13915–13923. -/
namespace BstLean.Part271.R3.Rows13915
open Real BstLean.Part130 BstLean.Part227

theorem width_13915 : mW 13915 = 317827328424748 := by
  have hu : mW 13915 ≤ 317827328424748 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13915 ≤ 317827328424747 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13915 : RowArithmetic 13915 (1126514791351723188409/1000000000000000000000000) (305146464325908229424763/500000000000000000000000) (743183692274181/100000000000000000000000) where
  r0 := (121844289451/200000000000000000)
  k0 := (3689999911402337/1000000000000000000)
  k6 := (11608043601255663/1000000000000000000)
  q := (83411629884567056097/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13915]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13915]

theorem width_13916 : mW 13916 = 317907277801738 := by
  have hu : mW 13916 ≤ 317907277801738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13916 ≤ 317907277801737 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13916 : RowArithmetic 13916 (281620676297547220531/250000000000000000000000) (610281417637798608619517/1000000000000000000000000) (7430446005081377/1000000000000000000000000) where
  r0 := (304577890351/500000000000000000)
  k0 := (3689801037818937/1000000000000000000)
  k6 := (725476657395267/62500000000000000)
  q := (166829254029381789357/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13916]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13916]

theorem width_13917 : mW 13917 = 317987241542870 := by
  have hu : mW 13917 ≤ 317987241542870 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13917 ≤ 317987241542869 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13917 : RowArithmetic 13917 (1126450626754066892999/1000000000000000000000000) (61026990827801028764093/100000000000000000000000) (928631931406151/125000000000000000000000) where
  r0 := (121818025189/200000000000000000)
  k0 := (461200273655443/125000000000000000)
  k6 := (11607209480347659/1000000000000000000)
  q := (83417624037130187253/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13917]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13917]

theorem width_13918 : mW 13918 = 318067219649693 := by
  have hu : mW 13918 ≤ 318067219649693 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13918 ≤ 318067219649692 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13918 : RowArithmetic 13918 (563209278020461098077/500000000000000000000000) (610258400572071764771163/1000000000000000000000000) (3713832630561559/500000000000000000000000) where
  r0 := (30451224149/50000000000000000)
  k0 := (1844701682834043/500000000000000000)
  k6 := (2901698121829437/250000000000000000)
  q := (166841241903793080103/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13918]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13918]

theorem width_13919 : mW 13919 = 318147212123753 := by
  have hu : mW 13919 ≤ 318147212123753 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13919 ≤ 318147212123752 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13919 : RowArithmetic 13919 (1126386493048322565377/1000000000000000000000000) (305123447259801683261759/500000000000000000000000) (928284429322631/125000000000000000000000) where
  r0 := (304479425903/500000000000000000)
  k0 := (3689204567093577/1000000000000000000)
  k6 := (5803187769613233/500000000000000000)
  q := (166847235518003114441/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13919]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13919]

theorem width_13920 : mW 13920 = 318227218966601 := by
  have hu : mW 13920 ≤ 318227218966601 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13920 ≤ 318227218966600 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13920 : RowArithmetic 13920 (112635443777383372669/100000000000000000000000) (305117695060112787625407/500000000000000000000000) (742488597150087/100000000000000000000000) where
  r0 := (608893232419/1000000000000000000)
  k0 := (3689005793511939/1000000000000000000)
  k6 := (5802979318032871/500000000000000000)
  q := (41713307229228420411/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13920]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13920]

theorem width_13921 : mW 13921 = 318307240179784 := by
  have hu : mW 13921 ≤ 318307240179784 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13921 ≤ 318307240179783 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13921 : RowArithmetic 13921 (563161195107512404639/500000000000000000000000) (19069496480423718705657/31250000000000000000000) (1855874217940151/250000000000000000000000) where
  r0 := (121765524963/200000000000000000)
  k0 := (3688807044915097/1000000000000000000)
  k6 := (11605541777827507/1000000000000000000)
  q := (166859222100547981669/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13921]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13921]

theorem width_13922 : mW 13922 = 318387275764852 := by
  have hu : mW 13922 ≤ 318387275764852 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13922 ≤ 318387275764851 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13922 : RowArithmetic 13922 (225258070073892821321/200000000000000000000000) (305106193139612156417521/500000000000000000000000) (927763516904781/125000000000000000000000) where
  r0 := (608762028993/1000000000000000000)
  k0 := (184430416065203/50000000000000000)
  k6 := (2321024992900739/200000000000000000)
  q := (166865215068929210307/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13922]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13922]

theorem width_13923 : mW 13923 = 318467325723351 := by
  have hu : mW 13923 ≤ 318467325723351 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 13923 ≤ 318467325723350 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_13923 : RowArithmetic 13923 (225251663646944662247/200000000000000000000000) (152550221709210605007959/250000000000000000000000) (7420719761811947/1000000000000000000000000) where
  r0 := (608696444949/1000000000000000000)
  k0 := (1844204811335373/500000000000000000)
  k6 := (72529426225539/6250000000000000)
  q := (166871207822080559183/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_13923]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_13923]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 13915 then ⟨(1126514791351723188409/1000000000000000000000000), (305146464325908229424763/500000000000000000000000), (743183692274181/100000000000000000000000)⟩ else
  if n = 13916 then ⟨(281620676297547220531/250000000000000000000000), (610281417637798608619517/1000000000000000000000000), (7430446005081377/1000000000000000000000000)⟩ else
  if n = 13917 then ⟨(1126450626754066892999/1000000000000000000000000), (61026990827801028764093/100000000000000000000000), (928631931406151/125000000000000000000000)⟩ else
  if n = 13918 then ⟨(563209278020461098077/500000000000000000000000), (610258400572071764771163/1000000000000000000000000), (3713832630561559/500000000000000000000000)⟩ else
  if n = 13919 then ⟨(1126386493048322565377/1000000000000000000000000), (305123447259801683261759/500000000000000000000000), (928284429322631/125000000000000000000000)⟩ else
  if n = 13920 then ⟨(112635443777383372669/100000000000000000000000), (305117695060112787625407/500000000000000000000000), (742488597150087/100000000000000000000000)⟩ else
  if n = 13921 then ⟨(563161195107512404639/500000000000000000000000), (19069496480423718705657/31250000000000000000000), (1855874217940151/250000000000000000000000)⟩ else
  if n = 13922 then ⟨(225258070073892821321/200000000000000000000000), (305106193139612156417521/500000000000000000000000), (927763516904781/125000000000000000000000)⟩ else
  ⟨(225251663646944662247/200000000000000000000000), (152550221709210605007959/250000000000000000000000), (7420719761811947/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 13915 ≤ n) (hb : n ≤ 13923) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_13915
  · exact row_13916
  · exact row_13917
  · exact row_13918
  · exact row_13919
  · exact row_13920
  · exact row_13921
  · exact row_13922
  · exact row_13923

end BstLean.Part271.R3.Rows13915
