import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 15355–15375. -/
namespace BstLean.Part271.R3.Rows15355
open Real BstLean.Part130 BstLean.Part227

theorem width_15355 : mW 15355 = 448615601254823 := by
  have hu : mW 15355 ≤ 448615601254823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15355 ≤ 448615601254822 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15355 : RowArithmetic 15355 (543627461266226991471/500000000000000000000000) (148815379213789001732323/250000000000000000000000) (46024296356171/8000000000000000000000) where
  r0 := (262781793969/500000000000000000)
  k0 := (685458859171411/200000000000000000)
  k6 := (11050342160725071/1000000000000000000)
  q := (21905336107898458813/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15355]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15355]

theorem width_15356 : mW 15356 = 448717866473297 := by
  have hu : mW 15356 ≤ 448717866473297 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15356 ≤ 448717866473296 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15356 : RowArithmetic 15356 (1087231841373763607769/1000000000000000000000000) (59525204636108995318893/100000000000000000000000) (2876032304243957/500000000000000000000000) where
  r0 := (105102450167/200000000000000000)
  k0 := (27417015220377/8000000000000000)
  k6 := (5524991174754479/500000000000000000)
  q := (10953024696402359523/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15356]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15356]

theorem width_15357 : mW 15357 = 448820148342192 := by
  have hu : mW 15357 ≤ 448820148342192 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15357 ≤ 448820148342191 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15357 : RowArithmetic 15357 (135901095654280163369/125000000000000000000000) (595242577078092084989891/1000000000000000000000000) (1437773100560637/250000000000000000000000) where
  r0 := (525460922089/1000000000000000000)
  k0 := (3426959528312109/1000000000000000000)
  k6 := (2209924514687619/200000000000000000)
  q := (87627050617945597953/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15357]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15357]

theorem width_15358 : mW 15358 = 448922446863134 := by
  have hu : mW 15358 ≤ 448922446863134 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15358 ≤ 448922446863133 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15358 : RowArithmetic 15358 (543592847056229063823/500000000000000000000000) (59523310900591482728717/100000000000000000000000) (1437530106428891/250000000000000000000000) where
  r0 := (525409601699/1000000000000000000)
  k0 := (171339608657577/50000000000000000)
  k6 := (5524631416253381/500000000000000000)
  q := (21907475892945768571/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15358]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15358]

theorem width_15359 : mW 15359 = 449024762037749 := by
  have hu : mW 15359 ≤ 449024762037749 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15359 ≤ 449024762037748 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15359 : RowArithmetic 15359 (1087162628006985637517/1000000000000000000000000) (297611821072155338047501/500000000000000000000000) (2874574339418637/500000000000000000000000) where
  r0 := (262679144831/500000000000000000)
  k0 := (3426624837058429/1000000000000000000)
  k6 := (5524451563354619/500000000000000000)
  q := (87632756432740377427/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15359]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15359]

theorem width_15360 : mW 15360 = 449127093867665 := by
  have hu : mW 15360 ≤ 449127093867665 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15360 ≤ 449127093867664 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15360 : RowArithmetic 15360 (217427913383279048421/200000000000000000000000) (119042835298606457085737/200000000000000000000000) (5748177161537991/1000000000000000000000000) where
  r0 := (525306985977/1000000000000000000)
  k0 := (856614380008077/250000000000000000)
  k6 := (5524271728019903/500000000000000000)
  q := (175271218401653156307/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15360]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15360]

theorem width_15361 : mW 15361 = 449229442354507 := by
  have hu : mW 15361 ≤ 449229442354507 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15361 ≤ 449229442354506 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15361 : RowArithmetic 15361 (84930977409317179/78125000000000000000) (148801178012958056763277/250000000000000000000000) (2873602936874047/500000000000000000000000) where
  r0 := (525255690641/1000000000000000000)
  k0 := (1713145111033093/500000000000000000)
  k6 := (11048183820492747/1000000000000000000)
  q := (547740386725317161/3125000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15361]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15361]

theorem width_15362 : mW 15362 = 449331807499903 := by
  have hu : mW 15362 ≤ 449331807499903 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15362 ≤ 449331807499902 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15362 : RowArithmetic 15362 (543546729887076015521/500000000000000000000000) (595195248820463300018883/1000000000000000000000000) (1436558703849487/250000000000000000000000) where
  r0 := (525204403653/1000000000000000000)
  k0 := (3426122943159593/1000000000000000000)
  k6 := (5523912110031173/500000000000000000)
  q := (43820657229210974033/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15362]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15362]

theorem width_15363 : mW 15363 = 449434189305479 := by
  have hu : mW 15363 ≤ 449434189305479 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15363 ≤ 449434189305478 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15363 : RowArithmetic 15363 (217414082743929062009/200000000000000000000000) (4761486294389426039449/8000000000000000000000) (5745263986417973/1000000000000000000000000) where
  r0 := (52515312501/100000000000000000)
  k0 := (53530557551649/15625000000000000)
  k6 := (11047464654742889/1000000000000000000)
  q := (175288333895898502833/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15363]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15363]

theorem width_15364 : mW 15364 = 449536587772862 := by
  have hu : mW 15364 ≤ 449536587772862 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15364 ≤ 449536587772861 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15364 : RowArithmetic 15364 (33970230396072298601/31250000000000000000000) (595176325986229953338043/1000000000000000000000000) (5744293386738601/1000000000000000000000000) where
  r0 := (65637731839/125000000000000000)
  k0 := (685157688501361/200000000000000000)
  k6 := (11047105124528661/1000000000000000000)
  q := (2191175483616043017/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15364]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15364]

theorem width_15365 : mW 15365 = 449639002903679 := by
  have hu : mW 15365 ≤ 449639002903679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15365 ≤ 449639002903678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15365 : RowArithmetic 15365 (1087024336636731113181/1000000000000000000000000) (595166866382871355669299/1000000000000000000000000) (574332301629029/100000000000000000000000) where
  r0 := (105010118551/200000000000000000)
  k0 := (3425621220753143/1000000000000000000)
  k6 := (172605400459593/15625000000000000)
  q := (175299743297016838501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15365]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15365]

theorem width_15366 : mW 15366 = 449741434699557 := by
  have hu : mW 15366 ≤ 449741434699557 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15366 ≤ 449741434699556 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15366 : RowArithmetic 15366 (1087001305605472849783/1000000000000000000000000) (595157407988355453579837/1000000000000000000000000) (1435588218750881/250000000000000000000000) where
  r0 := (262499669569/500000000000000000)
  k0 := (856363504511019/250000000000000000)
  k6 := (11046386169393051/1000000000000000000)
  q := (10956590482444801131/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15366]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15366]

theorem width_15367 : mW 15367 = 449843883162122 := by
  have hu : mW 15367 ≤ 449843883162122 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15367 ≤ 449843883162121 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15367 : RowArithmetic 15367 (67936142473694655643/62500000000000000000000) (119029590160487058410577/200000000000000000000000) (5741382962808829/1000000000000000000000000) where
  r0 := (524948093859/1000000000000000000)
  k0 := (856321708593967/250000000000000000)
  k6 := (11046026744460247/1000000000000000000)
  q := (175311151955601501033/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15367]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15367]

theorem width_15368 : mW 15368 = 449946348293002 := by
  have hu : mW 15368 ≤ 449946348293002 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15368 ≤ 449946348293001 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15368 : RowArithmetic 15368 (543477629278115798963/500000000000000000000000) (29756924741243202594287/50000000000000000000000) (5740413279636729/1000000000000000000000000) where
  r0 := (524896856917/1000000000000000000)
  k0 := (685023933949609/200000000000000000)
  k6 := (5522833677304917/500000000000000000)
  q := (21914607000811125657/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15368]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15368]

theorem width_15369 : mW 15369 = 450048830093823 := by
  have hu : mW 15369 ≤ 450048830093823 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15369 ≤ 450048830093822 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15369 : RowArithmetic 15369 (1086932242535400935091/1000000000000000000000000) (595129040055394894915029/1000000000000000000000000) (28697219127089/5000000000000000000000) where
  r0 := (524845628309/1000000000000000000)
  k0 := (684990504830721/200000000000000000)
  k6 := (11045307999836103/1000000000000000000)
  q := (175322559871797445759/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15369]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15369]

theorem width_15370 : mW 15370 = 450151328566213 := by
  have hu : mW 15370 ≤ 450151328566213 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15370 ≤ 450151328566212 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15370 : RowArithmetic 15370 (543454615757599551093/500000000000000000000000) (297559793246890570441901/500000000000000000000000) (2869237300041311/500000000000000000000000) where
  r0 := (524794408033/1000000000000000000)
  k0 := (3424785397588811/1000000000000000000)
  k6 := (11044948680133351/1000000000000000000)
  q := (175328263551544934589/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15370]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15370]

theorem width_15371 : mW 15371 = 450253843711800 := by
  have hu : mW 15371 ≤ 450253843711800 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15371 ≤ 450253843711799 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15371 : RowArithmetic 15371 (1086886225494203218217/1000000000000000000000000) (595110134139776139229219/1000000000000000000000000) (5737505603561797/1000000000000000000000000) where
  r0 := (65592899511/125000000000000000)
  k0 := (684923658010637/200000000000000000)
  k6 := (172571709304623/15625000000000000)
  q := (3506679340914991617/20000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15371]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15371]

theorem width_15372 : mW 15372 = 450356375532209 := by
  have hu : mW 15372 ≤ 450356375532209 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15372 ≤ 450356375532208 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15372 : RowArithmetic 15372 (1086863224470991939499/1000000000000000000000000) (595100682993133310323131/1000000000000000000000000) (2868268417892997/500000000000000000000000) where
  r0 := (524691992471/1000000000000000000)
  k0 := (3424451201539723/1000000000000000000)
  k6 := (2761057536479491/250000000000000000)
  q := (87669835177214745349/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15372]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15372]

theorem width_15373 : mW 15373 = 450458924029069 := by
  have hu : mW 15373 ≤ 450458924029069 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15373 ≤ 450458924029068 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15373 : RowArithmetic 15373 (1086840228444143080841/1000000000000000000000000) (2324575129115648671851/3906250000000000000000) (2867784148342929/500000000000000000000000) where
  r0 := (262320398591/500000000000000000)
  k0 := (3424284132051209/1000000000000000000)
  k6 := (441754837255757/40000000000000000)
  q := (87672686738801383673/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15373]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15373]

theorem width_15374 : mW 15374 = 450561489204007 := by
  have hu : mW 15374 ≤ 450561489204007 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15374 ≤ 450561489204006 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15374 : RowArithmetic 15374 (543408618706117827111/500000000000000000000000) (595081784320948053577293/1000000000000000000000000) (1433649996548021/250000000000000000000000) where
  r0 := (524589610217/1000000000000000000)
  k0 := (1712058540788687/500000000000000000)
  k6 := (2208702350383611/200000000000000000)
  q := (175351076415287511061/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15374]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15374]

theorem width_15375 : mW 15375 = 450664071058649 := by
  have hu : mW 15375 ≤ 450664071058649 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 15375 ≤ 450664071058648 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_15375 : RowArithmetic 15375 (1086794251373849528001/1000000000000000000000000) (595072336794912862318659/1000000000000000000000000) (358351994014713/62500000000000000000000) where
  r0 := (20981537263/40000000000000000)
  k0 := (3423950050117737/1000000000000000000)
  k6 := (2208630521496931/200000000000000000)
  q := (175356779167501819169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_15375]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_15375]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 15355 then ⟨(543627461266226991471/500000000000000000000000), (148815379213789001732323/250000000000000000000000), (46024296356171/8000000000000000000000)⟩ else
  if n = 15356 then ⟨(1087231841373763607769/1000000000000000000000000), (59525204636108995318893/100000000000000000000000), (2876032304243957/500000000000000000000000)⟩ else
  if n = 15357 then ⟨(135901095654280163369/125000000000000000000000), (595242577078092084989891/1000000000000000000000000), (1437773100560637/250000000000000000000000)⟩ else
  if n = 15358 then ⟨(543592847056229063823/500000000000000000000000), (59523310900591482728717/100000000000000000000000), (1437530106428891/250000000000000000000000)⟩ else
  if n = 15359 then ⟨(1087162628006985637517/1000000000000000000000000), (297611821072155338047501/500000000000000000000000), (2874574339418637/500000000000000000000000)⟩ else
  if n = 15360 then ⟨(217427913383279048421/200000000000000000000000), (119042835298606457085737/200000000000000000000000), (5748177161537991/1000000000000000000000000)⟩ else
  if n = 15361 then ⟨(84930977409317179/78125000000000000000), (148801178012958056763277/250000000000000000000000), (2873602936874047/500000000000000000000000)⟩ else
  if n = 15362 then ⟨(543546729887076015521/500000000000000000000000), (595195248820463300018883/1000000000000000000000000), (1436558703849487/250000000000000000000000)⟩ else
  if n = 15363 then ⟨(217414082743929062009/200000000000000000000000), (4761486294389426039449/8000000000000000000000), (5745263986417973/1000000000000000000000000)⟩ else
  if n = 15364 then ⟨(33970230396072298601/31250000000000000000000), (595176325986229953338043/1000000000000000000000000), (5744293386738601/1000000000000000000000000)⟩ else
  if n = 15365 then ⟨(1087024336636731113181/1000000000000000000000000), (595166866382871355669299/1000000000000000000000000), (574332301629029/100000000000000000000000)⟩ else
  if n = 15366 then ⟨(1087001305605472849783/1000000000000000000000000), (595157407988355453579837/1000000000000000000000000), (1435588218750881/250000000000000000000000)⟩ else
  if n = 15367 then ⟨(67936142473694655643/62500000000000000000000), (119029590160487058410577/200000000000000000000000), (5741382962808829/1000000000000000000000000)⟩ else
  if n = 15368 then ⟨(543477629278115798963/500000000000000000000000), (29756924741243202594287/50000000000000000000000), (5740413279636729/1000000000000000000000000)⟩ else
  if n = 15369 then ⟨(1086932242535400935091/1000000000000000000000000), (595129040055394894915029/1000000000000000000000000), (28697219127089/5000000000000000000000)⟩ else
  if n = 15370 then ⟨(543454615757599551093/500000000000000000000000), (297559793246890570441901/500000000000000000000000), (2869237300041311/500000000000000000000000)⟩ else
  if n = 15371 then ⟨(1086886225494203218217/1000000000000000000000000), (595110134139776139229219/1000000000000000000000000), (5737505603561797/1000000000000000000000000)⟩ else
  if n = 15372 then ⟨(1086863224470991939499/1000000000000000000000000), (595100682993133310323131/1000000000000000000000000), (2868268417892997/500000000000000000000000)⟩ else
  if n = 15373 then ⟨(1086840228444143080841/1000000000000000000000000), (2324575129115648671851/3906250000000000000000), (2867784148342929/500000000000000000000000)⟩ else
  if n = 15374 then ⟨(543408618706117827111/500000000000000000000000), (595081784320948053577293/1000000000000000000000000), (1433649996548021/250000000000000000000000)⟩ else
  ⟨(1086794251373849528001/1000000000000000000000000), (595072336794912862318659/1000000000000000000000000), (358351994014713/62500000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 15355 ≤ n) (hb : n ≤ 15375) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_15355
  · exact row_15356
  · exact row_15357
  · exact row_15358
  · exact row_15359
  · exact row_15360
  · exact row_15361
  · exact row_15362
  · exact row_15363
  · exact row_15364
  · exact row_15365
  · exact row_15366
  · exact row_15367
  · exact row_15368
  · exact row_15369
  · exact row_15370
  · exact row_15371
  · exact row_15372
  · exact row_15373
  · exact row_15374
  · exact row_15375

end BstLean.Part271.R3.Rows15355
