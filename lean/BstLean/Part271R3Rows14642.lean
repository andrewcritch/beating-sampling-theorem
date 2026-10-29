import BstLean.Part271R3Records

/-! Exact R0 row arithmetic for 14642–14716. -/
namespace BstLean.Part271.R3.Rows14642
open Real BstLean.Part130 BstLean.Part227

theorem width_14642 : mW 14642 = 379840622320189 := by
  have hu : mW 14642 ≤ 379840622320189 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14642 ≤ 379840622320188 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14642 : RowArithmetic 14642 (552540938652726649763/500000000000000000000000) (150584514733542911435299/250000000000000000000000) (3254701572541099/500000000000000000000000) where
  r0 := (282208051749/500000000000000000)
  k0 := (443964735247567/125000000000000000)
  k6 := (2829048829387757/250000000000000000)
  q := (171125684805057829169/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14642]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14642]

theorem width_14643 : mW 14643 = 379931426559884 := by
  have hu : mW 14643 ≤ 379931426559884 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14643 ≤ 379931426559883 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14643 : RowArithmetic 14643 (552527410380570652627/500000000000000000000000) (120465531486687269643361/200000000000000000000000) (6508247424928217/1000000000000000000000000) where
  r0 := (282179143407/500000000000000000)
  k0 := (3551535964944309/1000000000000000000)
  k6 := (11315808908054149/1000000000000000000)
  q := (42782882090854982511/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14643]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14643]

theorem width_14644 : mW 14644 = 380022246303913 := by
  have hu : mW 14644 ≤ 380022246303913 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14644 ≤ 380022246303912 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14644 : RowArithmetic 14644 (1105027770396879282647/1000000000000000000000000) (301158628669795492896527/500000000000000000000000) (3253545995798809/500000000000000000000000) where
  r0 := (564300480001/1000000000000000000)
  k0 := (710270813930077/200000000000000000)
  k6 := (11315422538138269/1000000000000000000)
  q := (10696085732640702801/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14644]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14644]

theorem width_14645 : mW 14645 = 380113081553866 := by
  have hu : mW 14645 ≤ 380113081553866 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14645 ≤ 380113081553865 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14645 : RowArithmetic 14645 (221000145242163696939/200000000000000000000000) (602306858652331395370073/1000000000000000000000000) (6505936844998981/1000000000000000000000000) where
  r0 := (112848536611/200000000000000000)
  k0 := (1775586098044759/500000000000000000)
  k6 := (1131503620779663/100000000000000000)
  q := (2139290186019652641/12500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14645]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14645]

theorem width_14646 : mW 14646 = 380203932311331 := by
  have hu : mW 14646 ≤ 380203932311331 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14646 ≤ 380203932311330 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14646 : RowArithmetic 14646 (1104973688201111772857/1000000000000000000000000) (37643528835709599594657/62500000000000000000000) (20327443703253/3125000000000000000000) where
  r0 := (22567395839/40000000000000000)
  k0 := (3550990344261901/1000000000000000000)
  k6 := (11314649917022477/1000000000000000000)
  q := (85574528920701631871/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14646]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14646]

theorem width_14647 : mW 14647 = 380294798577895 := by
  have hu : mW 14647 ≤ 380294798577895 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14647 ≤ 380294798577894 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14647 : RowArithmetic 14647 (110494665636591316499/100000000000000000000000) (602286065496353631540953/1000000000000000000000000) (6503627411632259/1000000000000000000000000) where
  r0 := (564127118757/1000000000000000000)
  k0 := (3550808514158283/1000000000000000000)
  k6 := (11314263665809057/1000000000000000000)
  q := (8557745030088241651/50000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14647]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14647]

theorem width_14648 : mW 14648 = 380385680355149 := by
  have hu : mW 14648 ≤ 380385680355149 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14648 ≤ 380385680355148 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14648 : RowArithmetic 14648 (1104919630703375585343/1000000000000000000000000) (120455134205405528566989/200000000000000000000000) (3251236562340777/500000000000000000000000) where
  r0 := (564069351401/1000000000000000000)
  k0 := (1775313352891001/500000000000000000)
  k6 := (5656938727074809/500000000000000000)
  q := (34232148632535469289/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14648]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14648]

theorem width_14649 : mW 14649 = 380476577644679 := by
  have hu : mW 14649 ≤ 380476577644679 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14649 ≤ 380476577644678 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14649 : RowArithmetic 14649 (276223152802913728487/250000000000000000000000) (150566319490767974656873/250000000000000000000000) (3250659562048819/500000000000000000000000) where
  r0 := (564011593903/1000000000000000000)
  k0 := (3550444919123807/1000000000000000000)
  k6 := (353546602563669/31250000000000000)
  q := (171166585524161227863/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14649]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14649]

theorem width_14650 : mW 14650 = 380567490448074 := by
  have hu : mW 14650 ≤ 380567490448074 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14650 ≤ 380567490448073 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14650 : RowArithmetic 14650 (1104865597888906386639/1000000000000000000000000) (37640930394011421483839/62500000000000000000000) (3250082704894647/500000000000000000000000) where
  r0 := (563953846261/1000000000000000000)
  k0 := (3550263154180737/1000000000000000000)
  k6 := (11313105149465681/1000000000000000000)
  q := (5349138365194903051/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14650]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14650]

theorem width_14651 : mW 14651 = 380658418766924 := by
  have hu : mW 14651 ≤ 380658418766924 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14651 ≤ 380658418766923 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14651 : RowArithmetic 14651 (1104838590733285495819/1000000000000000000000000) (602244496050056615040787/1000000000000000000000000) (6499011981665321/1000000000000000000000000) where
  r0 := (563896108473/1000000000000000000)
  k0 := (3550081410949833/1000000000000000000)
  k6 := (1414089882053461/125000000000000000)
  q := (171178269648924772627/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14651]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14651]

theorem width_14652 : mW 14652 = 380749362602817 := by
  have hu : mW 14652 ≤ 380749362602817 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14652 ≤ 380749362602816 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14652 : RowArithmetic 14652 (1104811589742949338121/1000000000000000000000000) (602234107200389948763439/1000000000000000000000000) (6497858839634591/1000000000000000000000000) where
  r0 := (70479797567/125000000000000000)
  k0 := (709979937884997/200000000000000000)
  k6 := (11312333002916683/1000000000000000000)
  q := (171184111412245266239/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14652]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14652]

theorem width_14653 : mW 14653 = 380840321957340 := by
  have hu : mW 14653 ≤ 380840321957340 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14653 ≤ 380840321957339 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14653 : RowArithmetic 14653 (69049037182253510213/62500000000000000000000) (120444743950975890421393/200000000000000000000000) (6496705983606027/1000000000000000000000000) where
  r0 := (35236291403/62500000000000000)
  k0 := (3549717989603231/1000000000000000000)
  k6 := (11311946988925923/1000000000000000000)
  q := (21398744122027348547/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14653]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14653]

theorem width_14654 : mW 14654 = 380931296832084 := by
  have hu : mW 14654 ≤ 380931296832084 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14654 ≤ 380931296832083 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14654 : RowArithmetic 14654 (276189401562690782533/250000000000000000000000) (301106666856610876713273/500000000000000000000000) (6495553413488521/1000000000000000000000000) where
  r0 := (563722954207/1000000000000000000)
  k0 := (3549536311481607/1000000000000000000)
  k6 := (5655780507224333/500000000000000000)
  q := (171195794340865745463/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14654]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14654]

theorem width_14655 : mW 14655 = 381022287228637 := by
  have hu : mW 14655 ≤ 381022287228637 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14655 ≤ 381022287228636 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14655 : RowArithmetic 14655 (138091327968153681009/125000000000000000000000) (301101474537556836719143/500000000000000000000000) (6494401129191053/1000000000000000000000000) where
  r0 := (56366525581/100000000000000000)
  k0 := (3549354655054001/1000000000000000000)
  k6 := (1131117507947817/100000000000000000)
  q := (34240327101241308089/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14655]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14655]

theorem width_14656 : mW 14656 = 381113293148588 := by
  have hu : mW 14656 ≤ 381113293148588 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14656 ≤ 381113293148587 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14656 : RowArithmetic 14656 (276175911849403645503/250000000000000000000000) (301096282920126042798979/500000000000000000000000) (6493249130622623/1000000000000000000000000) where
  r0 := (112721513451/200000000000000000)
  k0 := (709834604063489/200000000000000000)
  k6 := (11310789184007697/1000000000000000000)
  q := (171207476472261572787/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14656]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14656]

theorem width_14657 : mW 14657 = 381204314593526 := by
  have hu : mW 14657 ≤ 381204314593526 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14657 ≤ 381204314593525 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14657 : RowArithmetic 14657 (1104676677206078700433/1000000000000000000000000) (120436436801666796095331/200000000000000000000000) (811512177211533/125000000000000000000000) where
  r0 := (28177494427/50000000000000000)
  k0 := (3548991407268973/1000000000000000000)
  k6 := (11310403328030509/1000000000000000000)
  q := (171213317239051238471/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14657]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14657]

theorem width_14658 : mW 14658 = 381295351565039 := by
  have hu : mW 14658 ≤ 381295351565039 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14658 ≤ 381295351565038 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14658 : RowArithmetic 14658 (1104649713168783123131/1000000000000000000000000) (301085901789528173263871/500000000000000000000000) (6490945990309067/1000000000000000000000000) where
  r0 := (281746109831/500000000000000000)
  k0 := (3548809815902467/1000000000000000000)
  k6 := (11310017511539871/1000000000000000000)
  q := (171219157806595930003/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14658]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14658]

theorem width_14659 : mW 14659 = 381386404064717 := by
  have hu : mW 14659 ≤ 381386404064717 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14659 ≤ 381386404064716 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14659 : RowArithmetic 14659 (110462275528388897661/100000000000000000000000) (120432284910423271776289/200000000000000000000000) (6489794848382121/1000000000000000000000000) where
  r0 := (563434560619/1000000000000000000)
  k0 := (3548628246214959/1000000000000000000)
  k6 := (11309631734529047/1000000000000000000)
  q := (42806249543729009103/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14659]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14659]

theorem width_14660 : mW 14660 = 381477472094148 := by
  have hu : mW 14660 ≤ 381477472094148 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14660 ≤ 381477472094147 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14660 : RowArithmetic 14660 (552297901774779492983/500000000000000000000000) (602151046927211299658173/1000000000000000000000000) (6488643991820587/1000000000000000000000000) where
  r0 := (35211056963/62500000000000000)
  k0 := (3548446698200327/1000000000000000000)
  k6 := (2261849199398261/200000000000000000)
  q := (171230838344031943247/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14660]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14660]

theorem width_14661 : mW 14661 = 381568555654923 := by
  have hu : mW 14661 ≤ 381568555654923 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14661 ≤ 381568555654922 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14661 : RowArithmetic 14661 (1104568857963955235583/1000000000000000000000000) (602140670704038417585699/1000000000000000000000000) (1621873355133403/250000000000000000000000) where
  r0 := (140829818007/250000000000000000)
  k0 := (2838612137487/800000000000000)
  k6 := (5654430149459957/500000000000000000)
  q := (85618339156982016291/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14661]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14661]

theorem width_14662 : mW 14662 = 381659654748630 := by
  have hu : mW 14662 ≤ 381659654748630 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14662 ≤ 381659654748629 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14662 : RowArithmetic 14662 (552270959262620927501/500000000000000000000000) (602130295882295176221577/1000000000000000000000000) (6486343134430429/1000000000000000000000000) where
  r0 := (22530465699/40000000000000000)
  k0 := (709616733436191/200000000000000000)
  k6 := (2261694928061629/200000000000000000)
  q := (21405314760591585377/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14662]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14662]

theorem width_14663 : mW 14663 = 381750769376858 := by
  have hu : mW 14663 ≤ 381750769376858 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14663 ≤ 381750769376857 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14663 : RowArithmetic 14663 (552257492615791613791/500000000000000000000000) (602119922461679057563553/1000000000000000000000000) (6485193133420291/1000000000000000000000000) where
  r0 := (140801005687/250000000000000000)
  k0 := (1773951092083559/500000000000000000)
  k6 := (1130808902114927/100000000000000000)
  q := (21406044707044783709/125000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14663]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14663]

theorem width_14664 : mW 14664 = 381841899541196 := by
  have hu : mW 14664 ≤ 381841899541196 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14664 ≤ 381841899541195 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14664 : RowArithmetic 14664 (220897611616228887591/200000000000000000000000) (602109550441887704852689/1000000000000000000000000) (3242021708706243/500000000000000000000000) where
  r0 := (140786603211/250000000000000000)
  k0 := (3547720722811113/1000000000000000000)
  k6 := (11307703441436563/1000000000000000000)
  q := (171254197028861164201/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14664]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14664]

theorem width_14665 : mW 14665 = 381933045243235 := by
  have hu : mW 14665 ≤ 381933045243235 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14665 ≤ 381933045243234 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14665 : RowArithmetic 14665 (1104461137072090378217/1000000000000000000000000) (7526239747782733975173/12500000000000000000000) (3241446993158153/500000000000000000000000) where
  r0 := (563088812761/1000000000000000000)
  k0 := (3547539283109963/1000000000000000000)
  k6 := (5653658950581649/500000000000000000)
  q := (171260036202261734779/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14665]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14665]

theorem width_14666 : mW 14666 = 382024206484563 := by
  have hu : mW 14666 ≤ 382024206484563 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14666 ≤ 382024206484562 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14666 : RowArithmetic 14666 (552217111101293991053/500000000000000000000000) (602088810603569946770179/1000000000000000000000000) (810218105005141/125000000000000000000000) where
  r0 := (17594725703/31250000000000000)
  k0 := (1773678932528771/500000000000000000)
  k6 := (11306932400322753/1000000000000000000)
  q := (171265875176580346111/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14666]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14666]

theorem width_14667 : mW 14667 = 382115383266770 := by
  have hu : mW 14667 ≤ 382115383266770 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14667 ≤ 382115383266769 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14667 : RowArithmetic 14667 (138050914183850498767/125000000000000000000000) (120415688556887843596751/200000000000000000000000) (6480595978496333/1000000000000000000000000) where
  r0 := (8796463157/15625000000000000)
  k0 := (177358823432701/50000000000000000)
  k6 := (5653273469454103/500000000000000000)
  q := (171271713951837359431/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14667]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14667]

theorem width_14668 : mW 14668 = 382206575591445 := by
  have hu : mW 14668 ≤ 382206575591445 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14668 ≤ 382206575591444 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14668 : RowArithmetic 14668 (552190205437453144803/500000000000000000000000) (301034038182462250355343/500000000000000000000000) (6479447401591353/1000000000000000000000000) where
  r0 := (562916071413/1000000000000000000)
  k0 := (886748773472529/250000000000000000)
  k6 := (11306161516912937/1000000000000000000)
  q := (171277552528053132501/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14668]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14668]

theorem width_14669 : mW 14669 = 382297783460178 := by
  have hu : mW 14669 ≤ 382297783460178 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14669 ≤ 382297783460177 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14669 : RowArithmetic 14669 (552176757206531510669/500000000000000000000000) (120411542268944761829287/200000000000000000000000) (3239149554617821/500000000000000000000000) where
  r0 := (56285851059/100000000000000000)
  k0 := (1773406870383/500000000000000)
  k6 := (11305776134330229/1000000000000000000)
  q := (85641695452624009807/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14669]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14669]

theorem width_14670 : mW 14670 = 382389006874559 := by
  have hu : mW 14670 ≤ 382389006874559 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14670 ≤ 382389006874558 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14670 : RowArithmetic 14670 (1104326624083443026053/1000000000000000000000000) (7525591846544191387673/12500000000000000000000) (6477151101338687/1000000000000000000000000) where
  r0 := (70350119947/125000000000000000)
  k0 := (3546632409275537/1000000000000000000)
  k6 := (2261078158230673/200000000000000000)
  q := (42822307270860592899/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14670]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14670]

theorem width_14671 : mW 14671 = 382480245836177 := by
  have hu : mW 14671 ≤ 382480245836177 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14671 ≤ 382480245836176 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14671 : RowArithmetic 14671 (1104299739884216289691/1000000000000000000000000) (150509246375264295252851/250000000000000000000000) (647600337781003/100000000000000000000000) where
  r0 := (1099108239/1953125000000000)
  k0 := (709290219882519/200000000000000000)
  k6 := (11305005487375629/1000000000000000000)
  q := (85647533531328267901/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14671]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14671]

theorem width_14672 : mW 14672 = 382571500346621 := by
  have hu : mW 14672 ≤ 382571500346621 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14672 ≤ 382571500346620 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14672 : RowArithmetic 14672 (552136430906776748347/500000000000000000000000) (602026624676987774116159/1000000000000000000000000) (6474855938559249/1000000000000000000000000) where
  r0 := (112537177393/200000000000000000)
  k0 := (1773134905588669/500000000000000000)
  k6 := (2826155055747577/250000000000000000)
  q := (4282522621072771403/25000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14672]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14672]

theorem width_14673 : mW 14673 = 382662770407483 := by
  have hu : mW 14673 ≤ 382662770407483 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14673 ≤ 382662770407482 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14673 : RowArithmetic 14673 (220849197973924938747/200000000000000000000000) (60201626525102545055609/100000000000000000000000) (6473708783495907/1000000000000000000000000) where
  r0 := (140657091341/250000000000000000)
  k0 := (354608854456363/100000000000000000)
  k6 := (11304234997990691/1000000000000000000)
  q := (6852269696969026919/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14673]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14673]

theorem width_14674 : mW 14674 = 382754056020350 := by
  have hu : mW 14674 ≤ 382754056020350 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14674 ≤ 382754056020349 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14674 : RowArithmetic 14674 (276054781012650713271/250000000000000000000000) (301002953611434364351189/500000000000000000000000) (3236280956264843/500000000000000000000000) where
  r0 := (562570853563/1000000000000000000)
  k0 := (3545907299568483/1000000000000000000)
  k6 := (11303849812370067/1000000000000000000)
  q := (85656289903310661661/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14674]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14674]

theorem width_14675 : mW 14675 = 382845357186815 := by
  have hu : mW 14675 ≤ 382845357186815 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14675 ≤ 382845357186814 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14675 : RowArithmetic 14675 (1104192264354658973329/1000000000000000000000000) (300997775296108093299897/500000000000000000000000) (1617853831392551/250000000000000000000000) where
  r0 := (14062833789/25000000000000000)
  k0 := (354572607618891/100000000000000000)
  k6 := (11303464666121727/1000000000000000000)
  q := (34263683398023628131/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14675]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14675]

theorem width_14676 : mW 14676 = 382936673908465 := by
  have hu : mW 14676 ≤ 382936673908465 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14676 ≤ 382936673908464 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14676 : RowArithmetic 14676 (1104165410779967421687/1000000000000000000000000) (150496298839691621351783/250000000000000000000000) (6470269022527217/1000000000000000000000000) where
  r0 := (562455859351/1000000000000000000)
  k0 := (3545544874415617/1000000000000000000)
  k6 := (2825769889809741/250000000000000000)
  q := (85662126987368227501/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14676]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14676]

theorem width_14677 : mW 14677 = 383028006186892 := by
  have hu : mW 14677 ≤ 383028006186892 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14677 ≤ 383028006186891 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14677 : RowArithmetic 14677 (110413856332470103773/100000000000000000000000) (300987420761109175192463/500000000000000000000000) (202160093853451/31250000000000000000000) where
  r0 := (112479675387/200000000000000000)
  k0 := (709072738849753/200000000000000000)
  k6 := (5651347245857537/500000000000000000)
  q := (171330090760496592927/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14677]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14677]

theorem width_14678 : mW 14678 = 383119354023685 := by
  have hu : mW 14678 ≤ 383119354023685 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14678 ≤ 383119354023684 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14678 : RowArithmetic 14678 (1104111721987034692861/1000000000000000000000000) (601964489082270663400101/1000000000000000000000000) (3233988633914821/500000000000000000000000) where
  r0 := (56234090431/100000000000000000)
  k0 := (3545182535685363/1000000000000000000)
  k6 := (1412788682942919/125000000000000000)
  q := (34267185469483775507/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14678]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14678]

theorem width_14679 : mW 14679 = 383210717420435 := by
  have hu : mW 14679 ≤ 383210717420435 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14679 ≤ 383210717420434 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14679 : RowArithmetic 14679 (6900530542282144163/6250000000000000000000) (601954138038622332185549/1000000000000000000000000) (3233415907997321/500000000000000000000000) where
  r0 := (8785678773/15625000000000000)
  k0 := (1772500699358057/500000000000000000)
  k6 := (2260384894943419/200000000000000000)
  q := (85670881867761814233/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14679]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14679]

theorem width_14680 : mW 14680 = 383302096378732 := by
  have hu : mW 14680 ≤ 383302096378732 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14680 ≤ 383302096378731 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14680 : RowArithmetic 14680 (552029028828600988809/500000000000000000000000) (601943788390972425509373/1000000000000000000000000) (80821083096441/12500000000000000000000) where
  r0 := (562225988421/1000000000000000000)
  k0 := (3544820283344327/1000000000000000000)
  k6 := (2825384881307401/250000000000000000)
  q := (171347599924831161903/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14680]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14680]

theorem width_14681 : mW 14681 = 383393490900165 := by
  have hu : mW 14681 ≤ 383393490900165 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14681 ≤ 383393490900164 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14681 : RowArithmetic 14681 (552015617330694193859/500000000000000000000000) (601933440139019986125757/1000000000000000000000000) (3232270881450729/500000000000000000000000) where
  r0 := (4391941759/7812500000000000)
  k0 := (70892783791151/20000000000000000)
  k6 := (11301154615074179/1000000000000000000)
  q := (34270687183072358113/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14681]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14681]

theorem width_14682 : mW 14682 = 383484900986325 := by
  have hu : mW 14682 ≤ 383484900986325 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14682 ≤ 383484900986324 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14682 : RowArithmetic 14682 (220800883555175812849/200000000000000000000000) (601923093282464311109751/1000000000000000000000000) (6463397161463079/1000000000000000000000000) where
  r0 := (112422222333/200000000000000000)
  k0 := (3544458117359091/1000000000000000000)
  k6 := (11300769744244123/1000000000000000000)
  q := (171359271707135823717/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14682]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14682]

theorem width_14683 : mW 14683 = 383576326638803 := by
  have hu : mW 14683 ≤ 383576326638803 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14683 ≤ 383576326638802 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14683 : RowArithmetic 14683 (110397760699885147119/100000000000000000000000) (60191274782100458264003/100000000000000000000000) (3231126421655041/500000000000000000000000) where
  r0 := (562053687957/1000000000000000000)
  k0 := (3544277066742801/1000000000000000000)
  k6 := (565019245636637/50000000000000000)
  q := (171365107300173567161/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14683]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14683]

theorem width_14684 : mW 14684 = 383667767859189 := by
  have hu : mW 14684 ≤ 383667767859189 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14684 ≤ 383667767859188 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14684 : RowArithmetic 14684 (137993850291060526463/125000000000000000000000) (24076096150173610555729/40000000000000000000000) (3230554404176229/500000000000000000000000) where
  r0 := (22479850961/40000000000000000)
  k0 := (3544096037702527/1000000000000000000)
  k6 := (1412500015066667/125000000000000000)
  q := (42842735673623830811/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14684]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14684]

theorem width_14685 : mW 14685 = 383759224649073 := by
  have hu : mW 14685 ≤ 383759224649073 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14685 ≤ 383759224649072 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14685 : RowArithmetic 14685 (551962001881478291839/500000000000000000000000) (601892061082170760820817/1000000000000000000000000) (1291993011300047/200000000000000000000000) where
  r0 := (561938869867/1000000000000000000)
  k0 := (354391503023527/100000000000000000)
  k6 := (11299615367639217/1000000000000000000)
  q := (85688388945060695429/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14685]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14685]

theorem width_14686 : mW 14686 = 383850697010046 := by
  have hu : mW 14686 ≤ 383850697010046 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14686 ≤ 383850697010045 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14686 : RowArithmetic 14686 (1103897211300448136379/1000000000000000000000000) (601881719804195695084807/1000000000000000000000000) (322941079383173/50000000000000000000000) where
  r0 := (14047036887/25000000000000000)
  k0 := (1771867022167437/500000000000000000)
  k6 := (5649615327021847/500000000000000000)
  q := (42845653221768016359/250000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14686]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14686]

theorem width_14687 : mW 14687 = 383942184943698 := by
  have hu : mW 14687 ≤ 383942184943698 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14687 ≤ 383942184943697 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14687 : RowArithmetic 14687 (1103870424939139556679/1000000000000000000000000) (300935689960057328123023/500000000000000000000000) (807209800219029/125000000000000000000000) where
  r0 := (35114005679/62500000000000000)
  k0 := (708710616000929/200000000000000000)
  k6 := (2824711494935019/250000000000000000)
  q := (171388447685367638959/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14687]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14687]

theorem width_14688 : mW 14688 = 384033688451619 := by
  have hu : mW 14688 ≤ 384033688451619 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14688 ≤ 384033688451618 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14688 : RowArithmetic 14688 (1103843644677212225161/1000000000000000000000000) (601861041429627407091671/1000000000000000000000000) (1291307099735337/200000000000000000000000) where
  r0 := (280883358007/500000000000000000)
  k0 := (3543372137232117/1000000000000000000)
  k6 := (2824615336180419/250000000000000000)
  q := (10712142642814274997/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14688]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14688]

theorem width_14689 : mW 14689 = 384125207535402 := by
  have hu : mW 14689 ≤ 384125207535402 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14689 ≤ 384125207535401 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14689 : RowArithmetic 14689 (1103816870512846888303/1000000000000000000000000) (601850704332433742918269/1000000000000000000000000) (6455392878346939/1000000000000000000000000) where
  r0 := (561709350929/1000000000000000000)
  k0 := (3543191216017441/1000000000000000000)
  k6 := (11298076748981807/1000000000000000000)
  q := (171400116686074633489/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14689]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14689]

theorem width_14690 : mW 14690 = 384216742196635 := by
  have hu : mW 14690 ≤ 384216742196635 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14690 ≤ 384216742196634 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14690 : RowArithmetic 14690 (137973762805528399913/125000000000000000000000) (601840368628233627766957/1000000000000000000000000) (1613562635168309/250000000000000000000000) where
  r0 := (561651995607/1000000000000000000)
  k0 := (354301031635761/100000000000000000)
  k6 := (2259538438502757/200000000000000000)
  q := (17140595088852662119/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14690]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14690]

theorem width_14691 : mW 14691 = 384308292436911 := by
  have hu : mW 14691 ≤ 384308292436911 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14691 ≤ 384308292436910 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14691 : RowArithmetic 14691 (34492604389672977873/31250000000000000000000) (300915017158363509976329/500000000000000000000000) (3226554242782883/500000000000000000000000) where
  r0 := (140398662511/250000000000000000)
  k0 := (3542829438243309/1000000000000000000)
  k6 := (11297307675310927/1000000000000000000)
  q := (171411784892404641223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14691]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14691]

theorem width_14692 : mW 14692 = 384399858257819 := by
  have hu : mW 14692 ≤ 384399858257819 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14692 ≤ 384399858257818 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14692 : RowArithmetic 14692 (275934146146738940573/250000000000000000000000) (30090985069880700107573/50000000000000000000000) (258078668517393/40000000000000000000000) where
  r0 := (1754804107/3125000000000000)
  k0 := (3542648581677839/1000000000000000000)
  k6 := (11296923197366551/1000000000000000000)
  q := (85708809348864484153/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14692]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14692]

theorem width_14693 : mW 14693 = 384491439660951 := by
  have hu : mW 14693 ≤ 384491439660951 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14693 ≤ 384491439660950 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14693 : RowArithmetic 14693 (137963729349334071549/125000000000000000000000) (601809369870594800320927/1000000000000000000000000) (6450825222690691/1000000000000000000000000) where
  r0 := (561479988191/1000000000000000000)
  k0 := (3542467746651881/1000000000000000000)
  k6 := (1412067344834247/125000000000000000)
  q := (171423452304519873709/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14693]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14693]

theorem width_14694 : mW 14694 = 384583036647897 := by
  have hu : mW 14694 ≤ 384583036647897 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14694 ≤ 384583036647896 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14694 : RowArithmetic 14694 (275920772772717815139/250000000000000000000000) (150449759933842409491659/250000000000000000000000) (1289936802948743/200000000000000000000000) where
  r0 := (112284534379/200000000000000000)
  k0 := (442785866645303/125000000000000000)
  k6 := (5648077179613263/500000000000000000)
  q := (5357165178524925789/31250000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14694]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14694]

theorem width_14695 : mW 14695 = 384674649220249 := by
  have hu : mW 14695 ≤ 384674649220249 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14695 ≤ 384674649220248 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14695 : RowArithmetic 14695 (220731270694747434709/200000000000000000000000) (120357742198327776045643/200000000000000000000000) (6448543089004247/1000000000000000000000000) where
  r0 := (561365365349/1000000000000000000)
  k0 := (3542106141203303/1000000000000000000)
  k6 := (11295769999017523/1000000000000000000)
  q := (171435118922582487297/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14695]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14695]

theorem width_14696 : mW 14696 = 384766277379597 := by
  have hu : mW 14696 ≤ 384766277379597 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14696 ≤ 384766277379596 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14696 : RowArithmetic 14696 (551814810970728616517/500000000000000000000000) (601778383639103016553309/1000000000000000000000000) (1611850611345677/250000000000000000000000) where
  r0 := (561308068553/1000000000000000000)
  k0 := (1770962685388907/500000000000000000)
  k6 := (2823846419510073/250000000000000000)
  q := (85720475966947360389/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14696]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14696]

theorem width_14697 : mW 14697 = 384857921127533 := by
  have hu : mW 14697 ≤ 384857921127533 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14697 ≤ 384857921127532 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14697 : RowArithmetic 14697 (1103602896492218169159/1000000000000000000000000) (37610503604841404395943/62500000000000000000000) (6446262083789521/1000000000000000000000000) where
  r0 := (280625390751/500000000000000000)
  k0 := (1770872310936739/500000000000000000)
  k6 := (11295001396288159/1000000000000000000)
  q := (171446784746754583167/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14697]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14697]

theorem width_14698 : mW 14698 = 384949580465648 := by
  have hu : mW 14698 ≤ 384949580465648 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14698 ≤ 384949580465647 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14698 : RowArithmetic 14698 (551788088562103922337/500000000000000000000000) (150439433276604494105597/250000000000000000000000) (6445122004135161/1000000000000000000000000) where
  r0 := (140298376049/250000000000000000)
  k0 := (354156389449359/100000000000000000)
  k6 := (11294617153754453/1000000000000000000)
  q := (10715788585073895531/62500000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14698]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14698]

theorem width_14699 : mW 14699 = 385041255395533 := by
  have hu : mW 14699 ≤ 385041255395533 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14699 ≤ 385041255395532 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14699 : RowArithmetic 14699 (220709892767122962599/200000000000000000000000) (300873704962835090635233/500000000000000000000000) (6443982206330137/1000000000000000000000000) where
  r0 := (561136236631/1000000000000000000)
  k0 := (442672898578603/125000000000000000)
  k6 := (11294232950432503/1000000000000000000)
  q := (171458449777198207351/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14699]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14699]

theorem width_14700 : mW 14700 = 385132945918778 := by
  have hu : mW 14700 ≤ 385132945918778 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14700 ≤ 385132945918777 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14700 : RowArithmetic 14700 (44140910264985150337/40000000000000000000000) (300868544067459970630633/500000000000000000000000) (3221421345142507/500000000000000000000000) where
  r0 := (112215795761/200000000000000000)
  k0 := (3541202504276161/1000000000000000000)
  k6 := (11293848786315641/1000000000000000000)
  q := (85732140997411233437/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14700]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14700]

theorem width_14701 : mW 14701 = 385224652036977 := by
  have hu : mW 14701 ≤ 385224652036977 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14701 ≤ 385224652036976 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14701 : RowArithmetic 14701 (1103496055489438292979/1000000000000000000000000) (300863383866934009141493/500000000000000000000000) (6441703455910321/1000000000000000000000000) where
  r0 := (140255432679/250000000000000000)
  k0 := (3541021841432583/1000000000000000000)
  k6 := (11293464661397199/1000000000000000000)
  q := (171470114014075350763/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14701]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14701]

theorem width_14702 : mW 14702 = 385316373751719 := by
  have hu : mW 14702 ≤ 385316373751719 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14702 ≤ 385316373751718 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14702 : RowArithmetic 14702 (1103469360428234921499/1000000000000000000000000) (120343289744443107197727/200000000000000000000000) (6440564503116711/1000000000000000000000000) where
  r0 := (560964492361/1000000000000000000)
  k0 := (708168240018383/200000000000000000)
  k6 := (11293080575670511/1000000000000000000)
  q := (6859037833399083971/40000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14702]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14702]

theorem width_14703 : mW 14703 = 385408111064596 := by
  have hu : mW 14703 ≤ 385408111064596 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14703 ≤ 385408111064595 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14703 : RowArithmetic 14703 (275860667859802379151/250000000000000000000000) (37606633193728965358673/62500000000000000000000) (6439425831814819/1000000000000000000000000) where
  r0 := (560907263739/1000000000000000000)
  k0 := (3540660580254291/1000000000000000000)
  k6 := (5646348264564457/500000000000000000)
  q := (171481777457547949223/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14703]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14703]

theorem width_14704 : mW 14704 = 385499863977200 := by
  have hu : mW 14704 ≤ 385499863977200 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14704 ≤ 385499863977199 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14704 : RowArithmetic 14704 (1103415988520553640569/1000000000000000000000000) (300847907432956479920691/500000000000000000000000) (6438287441915317/1000000000000000000000000) where
  r0 := (560850044847/1000000000000000000)
  k0 := (3540479981913533/1000000000000000000)
  k6 := (2258462504353149/200000000000000000)
  q := (171487608881808133981/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14704]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14704]

theorem width_14705 : mW 14705 = 385591632491122 := by
  have hu : mW 14705 ≤ 385591632491122 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14705 ≤ 385591632491121 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14705 : RowArithmetic 14705 (1103389311670459984687/1000000000000000000000000) (601685500020665319161981/1000000000000000000000000) (6437149333328927/1000000000000000000000000) where
  r0 := (560792835683/1000000000000000000)
  k0 := (3540299405066619/1000000000000000000)
  k6 := (11291928553574343/1000000000000000000)
  q := (85746720053888941741/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14705]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14705]

theorem width_14706 : mW 14706 = 385683416607954 := by
  have hu : mW 14706 ≤ 385683416607954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14706 ≤ 385683416607953 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14706 : RowArithmetic 14706 (551681320443560744507/500000000000000000000000) (601675186563621818972461/1000000000000000000000000) (3218005752983197/500000000000000000000000) where
  r0 := (560735636243/1000000000000000000)
  k0 := (3540118849704209/1000000000000000000)
  k6 := (11291544624548049/1000000000000000000)
  q := (171499271135477424221/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14706]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14706]

theorem width_14707 : mW 14707 = 385775216329288 := by
  have hu : mW 14707 ≤ 385775216329288 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14707 ≤ 385775216329287 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14707 : RowArithmetic 14707 (1103335976168731782247/1000000000000000000000000) (120332974898896778975453/200000000000000000000000) (1286974791947699/200000000000000000000000) where
  r0 := (560678446527/1000000000000000000)
  k0 := (3539938315829593/1000000000000000000)
  k6 := (5645580367340103/500000000000000000)
  q := (85752550982463489627/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14707]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14707]

theorem width_14708 : mW 14708 = 385867031656714 := by
  have hu : mW 14708 ≤ 385867031656714 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14708 ≤ 385867031656713 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14708 : RowArithmetic 14708 (551654658756743029867/500000000000000000000000) (120330912762590605406839/200000000000000000000000) (6433736694556077/1000000000000000000000000) where
  r0 := (140155316633/250000000000000000)
  k0 := (1769878901718293/500000000000000000)
  k6 := (11290776883964157/1000000000000000000)
  q := (85755466298073384099/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14708]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14708]

theorem width_14709 : mW 14709 = 385958862591825 := by
  have hu : mW 14709 ≤ 385958862591825 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14709 ≤ 385958862591824 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14709 : RowArithmetic 14709 (220656532983915777279/200000000000000000000000) (601644254518730838608943/1000000000000000000000000) (6432599710329971/1000000000000000000000000) where
  r0 := (280282048127/500000000000000000)
  k0 := (3539577312515847/1000000000000000000)
  k6 := (11290393072393247/1000000000000000000)
  q := (34303352605831401447/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14709]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14709]

theorem width_14710 : mW 14710 = 386050709136213 := by
  have hu : mW 14710 ≤ 386050709136213 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14710 ≤ 386050709136212 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14710 : RowArithmetic 14710 (137907002298150744287/125000000000000000000000) (601633946611518986766627/1000000000000000000000000) (6431463006971063/1000000000000000000000000) where
  r0 := (560506935693/1000000000000000000)
  k0 := (176969842153533/50000000000000000)
  k6 := (451600371998433/40000000000000000)
  q := (17152259326397790911/100000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14710]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14710]

theorem width_14711 : mW 14711 = 386142571291469 := by
  have hu : mW 14711 ≤ 386142571291469 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14711 ≤ 386142571291468 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14711 : RowArithmetic 14711 (220645875581712816289/200000000000000000000000) (300811820045509616078669/500000000000000000000000) (401895411524393/62500000000000000000000) where
  r0 := (280224892423/500000000000000000)
  k0 := (1769608197547419/500000000000000000)
  k6 := (5644812783330119/500000000000000000)
  q := (85764211650314841567/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14711]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14711]

theorem width_14712 : mW 14712 = 386234449059185 := by
  have hu : mW 14712 ≤ 386234449059185 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14712 ≤ 386234449059184 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14712 : RowArithmetic 14712 (8825621947902802669/8000000000000000000000) (601613334956933459261189/1000000000000000000000000) (3214595221249301/500000000000000000000000) where
  r0 := (56039264371/100000000000000000)
  k0 := (3539035968582193/1000000000000000000)
  k6 := (11289241872484837/1000000000000000000)
  q := (85767126569566267591/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14712]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14712]

theorem width_14713 : mW 14713 = 386326342440954 := by
  have hu : mW 14713 ≤ 386326342440954 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14713 ≤ 386326342440953 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14713 : RowArithmetic 14713 (1103176115121262024921/1000000000000000000000000) (601603031208963613216211/1000000000000000000000000) (3214027290603489/500000000000000000000000) where
  r0 := (560335512283/1000000000000000000)
  k0 := (884713890882423/250000000000000000)
  k6 := (11288858217427973/1000000000000000000)
  q := (171540082779506667697/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14713]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14713]

theorem width_14714 : mW 14714 = 386418251438366 := by
  have hu : mW 14714 ≤ 386418251438366 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14714 ≤ 386418251438365 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14714 : RowArithmetic 14714 (220629898561399694157/200000000000000000000000) (601592728846811695085237/1000000000000000000000000) (1606729750106619/250000000000000000000000) where
  r0 := (560278390563/1000000000000000000)
  k0 := (35386751799343/10000000000000000)
  k6 := (11288474601483/1000000000000000)
  q := (171545912221772279689/1000000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14714]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14714]

theorem width_14715 : mW 14715 = 386510176053015 := by
  have hu : mW 14715 ≤ 386510176053015 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14715 ≤ 386510176053014 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14715 : RowArithmetic 14715 (1103122876543257919381/1000000000000000000000000) (601582427870179830054423/1000000000000000000000000) (1606445925017031/250000000000000000000000) where
  r0 := (140055319637/250000000000000000)
  k0 := (442311852224123/125000000000000000)
  k6 := (11288091024643273/1000000000000000000)
  q := (34310348293189913347/200000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14715]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14715]

theorem width_14716 : mW 14716 = 386602116286493 := by
  have hu : mW 14716 ≤ 386602116286493 := (mW_le_iff _ _).mpr (by norm_num)
  have hl : ¬mW 14716 ≤ 386602116286492 := by rw [mW_le_iff]; norm_num
  omega

noncomputable def row_14716 : RowArithmetic 14716 (1103096266328240181427/1000000000000000000000000) (300786064139385131284031/500000000000000000000000) (3212324340021509/500000000000000000000000) where
  r0 := (112032835247/200000000000000000)
  k0 := (3538314477099549/1000000000000000000)
  k6 := (11287707486902149/1000000000000000000)
  q := (85778785256029360491/500000000000000000)
  r0_nonneg := by norm_num
  radius := by norm_num
  k0_nonneg := by norm_num
  kernel := by norm_num
  k6_nonneg := by norm_num
  sixth := by norm_num
  q_nonneg := by norm_num
  q_square := by norm_num
  hidden_payment := by norm_num [hiddenChargeWithDistance, paymentBound, width_14716]
  frame_payment := by norm_num [frameEnvelope]
  moment_payment := by norm_num [momentEnvelope, width_14716]

noncomputable def record (n : ℕ) : Allowances :=
  if n = 14642 then ⟨(552540938652726649763/500000000000000000000000), (150584514733542911435299/250000000000000000000000), (3254701572541099/500000000000000000000000)⟩ else
  if n = 14643 then ⟨(552527410380570652627/500000000000000000000000), (120465531486687269643361/200000000000000000000000), (6508247424928217/1000000000000000000000000)⟩ else
  if n = 14644 then ⟨(1105027770396879282647/1000000000000000000000000), (301158628669795492896527/500000000000000000000000), (3253545995798809/500000000000000000000000)⟩ else
  if n = 14645 then ⟨(221000145242163696939/200000000000000000000000), (602306858652331395370073/1000000000000000000000000), (6505936844998981/1000000000000000000000000)⟩ else
  if n = 14646 then ⟨(1104973688201111772857/1000000000000000000000000), (37643528835709599594657/62500000000000000000000), (20327443703253/3125000000000000000000)⟩ else
  if n = 14647 then ⟨(110494665636591316499/100000000000000000000000), (602286065496353631540953/1000000000000000000000000), (6503627411632259/1000000000000000000000000)⟩ else
  if n = 14648 then ⟨(1104919630703375585343/1000000000000000000000000), (120455134205405528566989/200000000000000000000000), (3251236562340777/500000000000000000000000)⟩ else
  if n = 14649 then ⟨(276223152802913728487/250000000000000000000000), (150566319490767974656873/250000000000000000000000), (3250659562048819/500000000000000000000000)⟩ else
  if n = 14650 then ⟨(1104865597888906386639/1000000000000000000000000), (37640930394011421483839/62500000000000000000000), (3250082704894647/500000000000000000000000)⟩ else
  if n = 14651 then ⟨(1104838590733285495819/1000000000000000000000000), (602244496050056615040787/1000000000000000000000000), (6499011981665321/1000000000000000000000000)⟩ else
  if n = 14652 then ⟨(1104811589742949338121/1000000000000000000000000), (602234107200389948763439/1000000000000000000000000), (6497858839634591/1000000000000000000000000)⟩ else
  if n = 14653 then ⟨(69049037182253510213/62500000000000000000000), (120444743950975890421393/200000000000000000000000), (6496705983606027/1000000000000000000000000)⟩ else
  if n = 14654 then ⟨(276189401562690782533/250000000000000000000000), (301106666856610876713273/500000000000000000000000), (6495553413488521/1000000000000000000000000)⟩ else
  if n = 14655 then ⟨(138091327968153681009/125000000000000000000000), (301101474537556836719143/500000000000000000000000), (6494401129191053/1000000000000000000000000)⟩ else
  if n = 14656 then ⟨(276175911849403645503/250000000000000000000000), (301096282920126042798979/500000000000000000000000), (6493249130622623/1000000000000000000000000)⟩ else
  if n = 14657 then ⟨(1104676677206078700433/1000000000000000000000000), (120436436801666796095331/200000000000000000000000), (811512177211533/125000000000000000000000)⟩ else
  if n = 14658 then ⟨(1104649713168783123131/1000000000000000000000000), (301085901789528173263871/500000000000000000000000), (6490945990309067/1000000000000000000000000)⟩ else
  if n = 14659 then ⟨(110462275528388897661/100000000000000000000000), (120432284910423271776289/200000000000000000000000), (6489794848382121/1000000000000000000000000)⟩ else
  if n = 14660 then ⟨(552297901774779492983/500000000000000000000000), (602151046927211299658173/1000000000000000000000000), (6488643991820587/1000000000000000000000000)⟩ else
  if n = 14661 then ⟨(1104568857963955235583/1000000000000000000000000), (602140670704038417585699/1000000000000000000000000), (1621873355133403/250000000000000000000000)⟩ else
  if n = 14662 then ⟨(552270959262620927501/500000000000000000000000), (602130295882295176221577/1000000000000000000000000), (6486343134430429/1000000000000000000000000)⟩ else
  if n = 14663 then ⟨(552257492615791613791/500000000000000000000000), (602119922461679057563553/1000000000000000000000000), (6485193133420291/1000000000000000000000000)⟩ else
  if n = 14664 then ⟨(220897611616228887591/200000000000000000000000), (602109550441887704852689/1000000000000000000000000), (3242021708706243/500000000000000000000000)⟩ else
  if n = 14665 then ⟨(1104461137072090378217/1000000000000000000000000), (7526239747782733975173/12500000000000000000000), (3241446993158153/500000000000000000000000)⟩ else
  if n = 14666 then ⟨(552217111101293991053/500000000000000000000000), (602088810603569946770179/1000000000000000000000000), (810218105005141/125000000000000000000000)⟩ else
  if n = 14667 then ⟨(138050914183850498767/125000000000000000000000), (120415688556887843596751/200000000000000000000000), (6480595978496333/1000000000000000000000000)⟩ else
  if n = 14668 then ⟨(552190205437453144803/500000000000000000000000), (301034038182462250355343/500000000000000000000000), (6479447401591353/1000000000000000000000000)⟩ else
  if n = 14669 then ⟨(552176757206531510669/500000000000000000000000), (120411542268944761829287/200000000000000000000000), (3239149554617821/500000000000000000000000)⟩ else
  if n = 14670 then ⟨(1104326624083443026053/1000000000000000000000000), (7525591846544191387673/12500000000000000000000), (6477151101338687/1000000000000000000000000)⟩ else
  if n = 14671 then ⟨(1104299739884216289691/1000000000000000000000000), (150509246375264295252851/250000000000000000000000), (647600337781003/100000000000000000000000)⟩ else
  if n = 14672 then ⟨(552136430906776748347/500000000000000000000000), (602026624676987774116159/1000000000000000000000000), (6474855938559249/1000000000000000000000000)⟩ else
  if n = 14673 then ⟨(220849197973924938747/200000000000000000000000), (60201626525102545055609/100000000000000000000000), (6473708783495907/1000000000000000000000000)⟩ else
  if n = 14674 then ⟨(276054781012650713271/250000000000000000000000), (301002953611434364351189/500000000000000000000000), (3236280956264843/500000000000000000000000)⟩ else
  if n = 14675 then ⟨(1104192264354658973329/1000000000000000000000000), (300997775296108093299897/500000000000000000000000), (1617853831392551/250000000000000000000000)⟩ else
  if n = 14676 then ⟨(1104165410779967421687/1000000000000000000000000), (150496298839691621351783/250000000000000000000000), (6470269022527217/1000000000000000000000000)⟩ else
  if n = 14677 then ⟨(110413856332470103773/100000000000000000000000), (300987420761109175192463/500000000000000000000000), (202160093853451/31250000000000000000000)⟩ else
  if n = 14678 then ⟨(1104111721987034692861/1000000000000000000000000), (601964489082270663400101/1000000000000000000000000), (3233988633914821/500000000000000000000000)⟩ else
  if n = 14679 then ⟨(6900530542282144163/6250000000000000000000), (601954138038622332185549/1000000000000000000000000), (3233415907997321/500000000000000000000000)⟩ else
  if n = 14680 then ⟨(552029028828600988809/500000000000000000000000), (601943788390972425509373/1000000000000000000000000), (80821083096441/12500000000000000000000)⟩ else
  if n = 14681 then ⟨(552015617330694193859/500000000000000000000000), (601933440139019986125757/1000000000000000000000000), (3232270881450729/500000000000000000000000)⟩ else
  if n = 14682 then ⟨(220800883555175812849/200000000000000000000000), (601923093282464311109751/1000000000000000000000000), (6463397161463079/1000000000000000000000000)⟩ else
  if n = 14683 then ⟨(110397760699885147119/100000000000000000000000), (60191274782100458264003/100000000000000000000000), (3231126421655041/500000000000000000000000)⟩ else
  if n = 14684 then ⟨(137993850291060526463/125000000000000000000000), (24076096150173610555729/40000000000000000000000), (3230554404176229/500000000000000000000000)⟩ else
  if n = 14685 then ⟨(551962001881478291839/500000000000000000000000), (601892061082170760820817/1000000000000000000000000), (1291993011300047/200000000000000000000000)⟩ else
  if n = 14686 then ⟨(1103897211300448136379/1000000000000000000000000), (601881719804195695084807/1000000000000000000000000), (322941079383173/50000000000000000000000)⟩ else
  if n = 14687 then ⟨(1103870424939139556679/1000000000000000000000000), (300935689960057328123023/500000000000000000000000), (807209800219029/125000000000000000000000)⟩ else
  if n = 14688 then ⟨(1103843644677212225161/1000000000000000000000000), (601861041429627407091671/1000000000000000000000000), (1291307099735337/200000000000000000000000)⟩ else
  if n = 14689 then ⟨(1103816870512846888303/1000000000000000000000000), (601850704332433742918269/1000000000000000000000000), (6455392878346939/1000000000000000000000000)⟩ else
  if n = 14690 then ⟨(137973762805528399913/125000000000000000000000), (601840368628233627766957/1000000000000000000000000), (1613562635168309/250000000000000000000000)⟩ else
  if n = 14691 then ⟨(34492604389672977873/31250000000000000000000), (300915017158363509976329/500000000000000000000000), (3226554242782883/500000000000000000000000)⟩ else
  if n = 14692 then ⟨(275934146146738940573/250000000000000000000000), (30090985069880700107573/50000000000000000000000), (258078668517393/40000000000000000000000)⟩ else
  if n = 14693 then ⟨(137963729349334071549/125000000000000000000000), (601809369870594800320927/1000000000000000000000000), (6450825222690691/1000000000000000000000000)⟩ else
  if n = 14694 then ⟨(275920772772717815139/250000000000000000000000), (150449759933842409491659/250000000000000000000000), (1289936802948743/200000000000000000000000)⟩ else
  if n = 14695 then ⟨(220731270694747434709/200000000000000000000000), (120357742198327776045643/200000000000000000000000), (6448543089004247/1000000000000000000000000)⟩ else
  if n = 14696 then ⟨(551814810970728616517/500000000000000000000000), (601778383639103016553309/1000000000000000000000000), (1611850611345677/250000000000000000000000)⟩ else
  if n = 14697 then ⟨(1103602896492218169159/1000000000000000000000000), (37610503604841404395943/62500000000000000000000), (6446262083789521/1000000000000000000000000)⟩ else
  if n = 14698 then ⟨(551788088562103922337/500000000000000000000000), (150439433276604494105597/250000000000000000000000), (6445122004135161/1000000000000000000000000)⟩ else
  if n = 14699 then ⟨(220709892767122962599/200000000000000000000000), (300873704962835090635233/500000000000000000000000), (6443982206330137/1000000000000000000000000)⟩ else
  if n = 14700 then ⟨(44140910264985150337/40000000000000000000000), (300868544067459970630633/500000000000000000000000), (3221421345142507/500000000000000000000000)⟩ else
  if n = 14701 then ⟨(1103496055489438292979/1000000000000000000000000), (300863383866934009141493/500000000000000000000000), (6441703455910321/1000000000000000000000000)⟩ else
  if n = 14702 then ⟨(1103469360428234921499/1000000000000000000000000), (120343289744443107197727/200000000000000000000000), (6440564503116711/1000000000000000000000000)⟩ else
  if n = 14703 then ⟨(275860667859802379151/250000000000000000000000), (37606633193728965358673/62500000000000000000000), (6439425831814819/1000000000000000000000000)⟩ else
  if n = 14704 then ⟨(1103415988520553640569/1000000000000000000000000), (300847907432956479920691/500000000000000000000000), (6438287441915317/1000000000000000000000000)⟩ else
  if n = 14705 then ⟨(1103389311670459984687/1000000000000000000000000), (601685500020665319161981/1000000000000000000000000), (6437149333328927/1000000000000000000000000)⟩ else
  if n = 14706 then ⟨(551681320443560744507/500000000000000000000000), (601675186563621818972461/1000000000000000000000000), (3218005752983197/500000000000000000000000)⟩ else
  if n = 14707 then ⟨(1103335976168731782247/1000000000000000000000000), (120332974898896778975453/200000000000000000000000), (1286974791947699/200000000000000000000000)⟩ else
  if n = 14708 then ⟨(551654658756743029867/500000000000000000000000), (120330912762590605406839/200000000000000000000000), (6433736694556077/1000000000000000000000000)⟩ else
  if n = 14709 then ⟨(220656532983915777279/200000000000000000000000), (601644254518730838608943/1000000000000000000000000), (6432599710329971/1000000000000000000000000)⟩ else
  if n = 14710 then ⟨(137907002298150744287/125000000000000000000000), (601633946611518986766627/1000000000000000000000000), (6431463006971063/1000000000000000000000000)⟩ else
  if n = 14711 then ⟨(220645875581712816289/200000000000000000000000), (300811820045509616078669/500000000000000000000000), (401895411524393/62500000000000000000000)⟩ else
  if n = 14712 then ⟨(8825621947902802669/8000000000000000000000), (601613334956933459261189/1000000000000000000000000), (3214595221249301/500000000000000000000000)⟩ else
  if n = 14713 then ⟨(1103176115121262024921/1000000000000000000000000), (601603031208963613216211/1000000000000000000000000), (3214027290603489/500000000000000000000000)⟩ else
  if n = 14714 then ⟨(220629898561399694157/200000000000000000000000), (601592728846811695085237/1000000000000000000000000), (1606729750106619/250000000000000000000000)⟩ else
  if n = 14715 then ⟨(1103122876543257919381/1000000000000000000000000), (601582427870179830054423/1000000000000000000000000), (1606445925017031/250000000000000000000000)⟩ else
  ⟨(1103096266328240181427/1000000000000000000000000), (300786064139385131284031/500000000000000000000000), (3212324340021509/500000000000000000000000)⟩

noncomputable def arithmetic (n : ℕ) (ha : 14642 ≤ n) (hb : n ≤ 14716) :
    RowArithmetic n (record n).hidden (record n).frame (record n).moment := by
  interval_cases n
  · exact row_14642
  · exact row_14643
  · exact row_14644
  · exact row_14645
  · exact row_14646
  · exact row_14647
  · exact row_14648
  · exact row_14649
  · exact row_14650
  · exact row_14651
  · exact row_14652
  · exact row_14653
  · exact row_14654
  · exact row_14655
  · exact row_14656
  · exact row_14657
  · exact row_14658
  · exact row_14659
  · exact row_14660
  · exact row_14661
  · exact row_14662
  · exact row_14663
  · exact row_14664
  · exact row_14665
  · exact row_14666
  · exact row_14667
  · exact row_14668
  · exact row_14669
  · exact row_14670
  · exact row_14671
  · exact row_14672
  · exact row_14673
  · exact row_14674
  · exact row_14675
  · exact row_14676
  · exact row_14677
  · exact row_14678
  · exact row_14679
  · exact row_14680
  · exact row_14681
  · exact row_14682
  · exact row_14683
  · exact row_14684
  · exact row_14685
  · exact row_14686
  · exact row_14687
  · exact row_14688
  · exact row_14689
  · exact row_14690
  · exact row_14691
  · exact row_14692
  · exact row_14693
  · exact row_14694
  · exact row_14695
  · exact row_14696
  · exact row_14697
  · exact row_14698
  · exact row_14699
  · exact row_14700
  · exact row_14701
  · exact row_14702
  · exact row_14703
  · exact row_14704
  · exact row_14705
  · exact row_14706
  · exact row_14707
  · exact row_14708
  · exact row_14709
  · exact row_14710
  · exact row_14711
  · exact row_14712
  · exact row_14713
  · exact row_14714
  · exact row_14715
  · exact row_14716

end BstLean.Part271.R3.Rows14642
