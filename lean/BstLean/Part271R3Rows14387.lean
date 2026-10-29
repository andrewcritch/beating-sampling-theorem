import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14387–14399. -/
namespace BstLean.Part271.R3.Rows14387
open Real BstLean.Part130 BstLean.Part227

theorem width_14387 : mW 14387 = 357187171463353 := by
  have hu : mW 14387 ≤ 357187171463353 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14387 ≤ 357187171463352 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14387 : RowArithmetic 14387 (139023538261830282567/125000000000000000000000) (605037229453213741776351/1000000000000000000000000) (6813735802267437/1000000000000000000000000) where
  r0 := (289744125121/500000000000000000)
  k0 := (899706979831097/250000000000000000)
  k6 := (2854010213058051/250000000000000000)
  q := (169629006953409946561/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14387]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14387]

theorem width_14388 : mW 14388 = 357274073786448 := by
  have hu : mW 14388 ≤ 357274073786448 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14388 ≤ 357274073786447 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14388 : RowArithmetic 14388 (556079805677982743347/500000000000000000000000) (605026459010755418050927/1000000000000000000000000) (17031259642061/2500000000000000000000) where
  r0 := (144856959397/250000000000000000)
  k0 := (1799320161206157/500000000000000000)
  k6 := (5707822062215289/500000000000000000)
  q := (10602181379320012369/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14388]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14388]

theorem width_14389 : mW 14389 = 357360991210646 := by
  have hu : mW 14389 ≤ 357360991210646 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14389 ≤ 357360991210645 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14389 : RowArithmetic 14389 (27803273082292918049/25000000000000000000000) (605015690055778288187707/1000000000000000000000000) (3405636111358079/500000000000000000000000) where
  r0 := (579367435429/1000000000000000000)
  k0 := (3598452748312551/1000000000000000000)
  k6 := (2853811859496769/250000000000000000)
  q := (33928159395994354471/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14389]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14389]

theorem width_14390 : mW 14390 = 357447923737523 := by
  have hu : mW 14390 ≤ 357447923737523 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14390 ≤ 357447923737522 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14390 : RowArithmetic 14390 (1112102241899862888537/1000000000000000000000000) (75625615323494265963227/125000000000000000000000) (6810040899841671/1000000000000000000000000) where
  r0 := (115861408753/200000000000000000)
  k0 := (3598265197028667/1000000000000000000)
  k6 := (11414850792894513/1000000000000000000)
  q := (84823345842993012651/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14390]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14390]

theorem width_14391 : mW 14391 = 357534871368653 := by
  have hu : mW 14391 ≤ 357534871368653 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14391 ≤ 357534871368652 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14391 : RowArithmetic 14391 (1112073567178372698777/1000000000000000000000000) (75624269575869341749/125000000000000000000) (6808809888099977/1000000000000000000000000) where
  r0 := (579246662591/1000000000000000000)
  k0 := (3598077668548701/1000000000000000000)
  k6 := (1426806773643213/125000000000000000)
  q := (169652586187184308423/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14391]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14391]

theorem width_14392 : mW 14392 = 357621834105610 := by
  have hu : mW 14392 ≤ 357621834105610 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14392 ≤ 357621834105609 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14392 : RowArithmetic 14392 (1112044899125215655991/1000000000000000000000000) (604983392112452031703329/1000000000000000000000000) (1701894796847539/250000000000000000000000) where
  r0 := (289593145953/500000000000000000)
  k0 := (3597890162873111/1000000000000000000)
  k6 := (2853514406683367/250000000000000000)
  q := (84829240241793984843/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14392]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14392]

theorem width_14393 : mW 14393 = 357708811949968 := by
  have hu : mW 14393 ≤ 357708811949968 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14393 ≤ 357708811949967 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14393 : RowArithmetic 14393 (222403247547672410809/200000000000000000000000) (15124315727602951335237/25000000000000000000000) (6806348797611329/1000000000000000000000000) where
  r0 := (579125931707/1000000000000000000)
  k0 := (1798851339998073/500000000000000000)
  k6 := (18261857769041/1600000000000000)
  q := (169664374575218353351/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14393]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14393]

theorem width_14394 : mW 14394 = 357795804903303 := by
  have hu : mW 14394 ≤ 357795804903303 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14394 ≤ 357795804903302 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14394 : RowArithmetic 14394 (1111987583015781981/1000000000000000000000) (24198474703264998645671/40000000000000000000000) (6805118718662619/1000000000000000000000000) where
  r0 := (579065581991/1000000000000000000)
  k0 := (3597515219912051/1000000000000000000)
  k6 := (11413264625889997/1000000000000000000)
  q := (169670268462096799973/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14394]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14394]

theorem width_14395 : mW 14395 = 357882812967189 := by
  have hu : mW 14395 ≤ 357882812967189 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14395 ≤ 357882812967188 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14395 : RowArithmetic 14395 (1111958934955447311859/1000000000000000000000000) (151237776886161236419613/250000000000000000000000) (6803888950443229/1000000000000000000000000) where
  r0 := (144751310689/250000000000000000)
  k0 := (56208246603409/15625000000000000)
  k6 := (5706434093722203/500000000000000000)
  q := (169676162144244646397/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14395]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14395]

theorem width_14396 : mW 14396 = 357969836143201 := by
  have hu : mW 14396 ≤ 357969836143201 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14396 ≤ 357969836143200 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14396 : RowArithmetic 14396 (555965146777665106703/500000000000000000000000) (75617543624106294444953/125000000000000000000000) (212583109151637/31250000000000000000000) where
  r0 := (578944913999/1000000000000000000)
  k0 := (899285092027191/250000000000000000)
  k6 := (5706235895153339/500000000000000000)
  q := (33936411124336645153/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14396]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14396]

theorem width_14397 : mW 14397 = 358056874432913 := by
  have hu : mW 14397 ≤ 358056874432913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14397 ≤ 358056874432912 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14397 : RowArithmetic 14397 (555950829406702069791/500000000000000000000000) (12098591838518271743643/20000000000000000000000) (6801430345789369/1000000000000000000000000) where
  r0 := (289442297859/500000000000000000)
  k0 := (1798476488190581/500000000000000000)
  k6 := (285301885861741/25000000000000000)
  q := (84843974447216933757/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14397]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14397]

theorem width_14398 : mW 14398 = 358143927837901 := by
  have hu : mW 14398 ≤ 358143927837901 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14398 ≤ 358143927837900 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14398 : RowArithmetic 14398 (555936515363821169271/500000000000000000000000) (604918836343507172384533/1000000000000000000000000) (680020150915347/100000000000000000000000) where
  r0 := (57882428791/100000000000000000)
  k0 := (899191401857403/250000000000000000)
  k6 := (11411679119926121/1000000000000000000)
  q := (1357550735700143179/8000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14398]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14398]

theorem width_14399 : mW 14399 = 358230996359738 := by
  have hu : mW 14399 ≤ 358230996359738 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14399 ≤ 358230996359737 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14399 : RowArithmetic 14399 (555922204648010169579/500000000000000000000000) (120981616449060753439261/200000000000000000000000) (6798972982844073/1000000000000000000000000) where
  r0 := (578763990573/1000000000000000000)
  k0 := (3596578261251457/1000000000000000000)
  k6 := (11411282846668951/1000000000000000000)
  q := (8484986741297831869/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14399]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14399]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14387 then ⟨(139023538261830282567/125000000000000000000000), (605037229453213741776351/1000000000000000000000000), (6813735802267437/1000000000000000000000000)⟩ else
  if n = 14388 then ⟨(556079805677982743347/500000000000000000000000), (605026459010755418050927/1000000000000000000000000), (17031259642061/2500000000000000000000)⟩ else
  if n = 14389 then ⟨(27803273082292918049/25000000000000000000000), (605015690055778288187707/1000000000000000000000000), (3405636111358079/500000000000000000000000)⟩ else
  if n = 14390 then ⟨(1112102241899862888537/1000000000000000000000000), (75625615323494265963227/125000000000000000000000), (6810040899841671/1000000000000000000000000)⟩ else
  if n = 14391 then ⟨(1112073567178372698777/1000000000000000000000000), (75624269575869341749/125000000000000000000), (6808809888099977/1000000000000000000000000)⟩ else
  if n = 14392 then ⟨(1112044899125215655991/1000000000000000000000000), (604983392112452031703329/1000000000000000000000000), (1701894796847539/250000000000000000000000)⟩ else
  if n = 14393 then ⟨(222403247547672410809/200000000000000000000000), (15124315727602951335237/25000000000000000000000), (6806348797611329/1000000000000000000000000)⟩ else
  if n = 14394 then ⟨(1111987583015781981/1000000000000000000000), (24198474703264998645671/40000000000000000000000), (6805118718662619/1000000000000000000000000)⟩ else
  if n = 14395 then ⟨(1111958934955447311859/1000000000000000000000000), (151237776886161236419613/250000000000000000000000), (6803888950443229/1000000000000000000000000)⟩ else
  if n = 14396 then ⟨(555965146777665106703/500000000000000000000000), (75617543624106294444953/125000000000000000000000), (212583109151637/31250000000000000000000)⟩ else
  if n = 14397 then ⟨(555950829406702069791/500000000000000000000000), (12098591838518271743643/20000000000000000000000), (6801430345789369/1000000000000000000000000)⟩ else
  if n = 14398 then ⟨(555936515363821169271/500000000000000000000000), (604918836343507172384533/1000000000000000000000000), (680020150915347/100000000000000000000000)⟩ else
  ⟨(555922204648010169579/500000000000000000000000), (120981616449060753439261/200000000000000000000000), (6798972982844073/1000000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14387 ≤ n) (hb : n ≤ 14399) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14387
  · exact row_14388
  · exact row_14389
  · exact row_14390
  · exact row_14391
  · exact row_14392
  · exact row_14393
  · exact row_14394
  · exact row_14395
  · exact row_14396
  · exact row_14397
  · exact row_14398
  · exact row_14399

end BstLean.Part271.R3.Rows14387
