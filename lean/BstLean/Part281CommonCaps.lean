import BstLean.Part281Repair
import BstLean.Part277Frame
namespace BstLean.Part281
open Real Set BstLean.Part263
open BstLean.Part281.TI (parameters parameters_valid)
noncomputable def commonCap : Fin 43 → ℝ
  | ⟨0,_⟩ => (276717619/1000000000)
  | ⟨1,_⟩ => (277122997/1000000000)
  | ⟨2,_⟩ => (69381879/250000000)
  | ⟨3,_⟩ => (69482753/250000000)
  | ⟨4,_⟩ => (139169771/500000000)
  | ⟨5,_⟩ => (278740887/1000000000)
  | ⟨6,_⟩ => (279141383/1000000000)
  | ⟨7,_⟩ => (69885219/250000000)
  | ⟨8,_⟩ => (69986383/250000000)
  | ⟨9,_⟩ => (11213697/40000000)
  | ⟨10,_⟩ => (140369479/500000000)
  | ⟨11,_⟩ => (140567251/500000000)
  | ⟨12,_⟩ => (56307427/200000000)
  | ⟨13,_⟩ => (56386151/200000000)
  | ⟨14,_⟩ => (282322757/1000000000)
  | ⟨15,_⟩ => (56542787/200000000)
  | ⟨16,_⟩ => (283113601/1000000000)
  | ⟨17,_⟩ => (17718961/62500000)
  | ⟨18,_⟩ => (141945773/500000000)
  | ⟨19,_⟩ => (142139449/500000000)
  | ⟨20,_⟩ => (284674467/1000000000)
  | ⟨21,_⟩ => (285059961/1000000000)
  | ⟨22,_⟩ => (71361089/250000000)
  | ⟨23,_⟩ => (71456863/250000000)
  | ⟨24,_⟩ => (143109989/500000000)
  | ⟨25,_⟩ => (71650309/250000000)
  | ⟨26,_⟩ => (286981559/1000000000)
  | ⟨27,_⟩ => (143680651/500000000)
  | ⟨28,_⟩ => (143869647/500000000)
  | ⟨29,_⟩ => (72031741/250000000)
  | ⟨30,_⟩ => (288503617/1000000000)
  | ⟨31,_⟩ => (72219839/250000000)
  | ⟨32,_⟩ => (57850733/200000000)
  | ⟨33,_⟩ => (289637489/1000000000)
  | ⟨34,_⟩ => (290010537/1000000000)
  | ⟨35,_⟩ => (36297771/125000000)
  | ⟨36,_⟩ => (290752899/1000000000)
  | ⟨37,_⟩ => (145566431/500000000)
  | ⟨38,_⟩ => (291501847/1000000000)
  | ⟨39,_⟩ => (145934711/500000000)
  | ⟨40,_⟩ => (292236619/1000000000)
  | ⟨41,_⟩ => (73153323/250000000)
  | ⟨42,_⟩ => (146489131/500000000)
  | ⟨j+43,h⟩ => False.elim (by omega)

noncomputable def commonUpper : Fin 43 → ℝ
  | ⟨0,_⟩ => (236618719868117662125663/500000000000000000000000)
  | ⟨1,_⟩ => (5930510541857754421609/12500000000000000000000)
  | ⟨2,_⟩ => (475644246961005383206113/1000000000000000000000000)
  | ⟨3,_⟩ => (238423825286695206341753/500000000000000000000000)
  | ⟨4,_⟩ => (478051054185775442160899/1000000000000000000000000)
  | ⟨5,_⟩ => (479254457798160471638293/1000000000000000000000000)
  | ⟨6,_⟩ => (240228930705272750557843/500000000000000000000000)
  | ⟨7,_⟩ => (481661265022930530593079/1000000000000000000000000)
  | ⟨8,_⟩ => (60358083579414445008809/125000000000000000000000)
  | ⟨9,_⟩ => (242034036123850294773933/500000000000000000000000)
  | ⟨10,_⟩ => (485271475860085619025259/1000000000000000000000000)
  | ⟨11,_⟩ => (121618719868117662125663/250000000000000000000000)
  | ⟨12,_⟩ => (97535656616971135596009/200000000000000000000000)
  | ⟨13,_⟩ => (488881686697240707457439/1000000000000000000000000)
  | ⟨14,_⟩ => (30630318144351608558427/62500000000000000000000)
  | ⟨15,_⟩ => (19651539756880430656489/40000000000000000000000)
  | ⟨16,_⟩ => (246245948767197897944809/500000000000000000000000)
  | ⟨17,_⟩ => (123423825286695206341753/250000000000000000000000)
  | ⟨18,_⟩ => (98979740951833170968881/200000000000000000000000)
  | ⟨19,_⟩ => (248051054185775442160899/500000000000000000000000)
  | ⟨20,_⟩ => (497305511983935913799191/1000000000000000000000000)
  | ⟨21,_⟩ => (99701783119264188655317/200000000000000000000000)
  | ⟨22,_⟩ => (249856159604352986376989/500000000000000000000000)
  | ⟨23,_⟩ => (500915722821091002231371/1000000000000000000000000)
  | ⟨24,_⟩ => (125529781608369007927191/250000000000000000000000)
  | ⟨25,_⟩ => (251661265022930530593079/500000000000000000000000)
  | ⟨26,_⟩ => (504525933658246090663551/1000000000000000000000000)
  | ⟨27,_⟩ => (31608083579414445008809/62500000000000000000000)
  | ⟨28,_⟩ => (506932740883016149618337/1000000000000000000000000)
  | ⟨29,_⟩ => (508136144495401179095731/1000000000000000000000000)
  | ⟨30,_⟩ => (127334887026946552143281/250000000000000000000000)
  | ⟨31,_⟩ => (510542951720171238050517/1000000000000000000000000)
  | ⟨32,_⟩ => (51174635533255626752791/100000000000000000000000)
  | ⟨33,_⟩ => (64118719868117662125663/125000000000000000000000)
  | ⟨34,_⟩ => (514153162557326326482697/1000000000000000000000000)
  | ⟨35,_⟩ => (51535656616971135596009/100000000000000000000000)
  | ⟨36,_⟩ => (516559969782096385437483/1000000000000000000000000)
  | ⟨37,_⟩ => (517763373394481414914877/1000000000000000000000000)
  | ⟨38,_⟩ => (51896677700686644439227/100000000000000000000000)
  | ⟨39,_⟩ => (520170180619251473869663/1000000000000000000000000)
  | ⟨40,_⟩ => (32585849014477281459191/62500000000000000000000)
  | ⟨41,_⟩ => (10451539756880430656489/20000000000000000000000)
  | ⟨42,_⟩ => (523780391456406562301843/1000000000000000000000000)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem commonCell0 :
    0 ≤ commonCap ⟨0,by decide⟩ ∧ commonUpper ⟨0,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨0,by decide⟩) (commonUpper ⟨0,by decide⟩) ≤ commonCap ⟨0,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell1 :
    0 ≤ commonCap ⟨1,by decide⟩ ∧ commonUpper ⟨1,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨1,by decide⟩) (commonUpper ⟨1,by decide⟩) ≤ commonCap ⟨1,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell2 :
    0 ≤ commonCap ⟨2,by decide⟩ ∧ commonUpper ⟨2,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨2,by decide⟩) (commonUpper ⟨2,by decide⟩) ≤ commonCap ⟨2,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell3 :
    0 ≤ commonCap ⟨3,by decide⟩ ∧ commonUpper ⟨3,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨3,by decide⟩) (commonUpper ⟨3,by decide⟩) ≤ commonCap ⟨3,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell4 :
    0 ≤ commonCap ⟨4,by decide⟩ ∧ commonUpper ⟨4,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨4,by decide⟩) (commonUpper ⟨4,by decide⟩) ≤ commonCap ⟨4,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell5 :
    0 ≤ commonCap ⟨5,by decide⟩ ∧ commonUpper ⟨5,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨5,by decide⟩) (commonUpper ⟨5,by decide⟩) ≤ commonCap ⟨5,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell6 :
    0 ≤ commonCap ⟨6,by decide⟩ ∧ commonUpper ⟨6,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨6,by decide⟩) (commonUpper ⟨6,by decide⟩) ≤ commonCap ⟨6,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell7 :
    0 ≤ commonCap ⟨7,by decide⟩ ∧ commonUpper ⟨7,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨7,by decide⟩) (commonUpper ⟨7,by decide⟩) ≤ commonCap ⟨7,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell8 :
    0 ≤ commonCap ⟨8,by decide⟩ ∧ commonUpper ⟨8,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨8,by decide⟩) (commonUpper ⟨8,by decide⟩) ≤ commonCap ⟨8,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell9 :
    0 ≤ commonCap ⟨9,by decide⟩ ∧ commonUpper ⟨9,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨9,by decide⟩) (commonUpper ⟨9,by decide⟩) ≤ commonCap ⟨9,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell10 :
    0 ≤ commonCap ⟨10,by decide⟩ ∧ commonUpper ⟨10,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨10,by decide⟩) (commonUpper ⟨10,by decide⟩) ≤ commonCap ⟨10,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell11 :
    0 ≤ commonCap ⟨11,by decide⟩ ∧ commonUpper ⟨11,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨11,by decide⟩) (commonUpper ⟨11,by decide⟩) ≤ commonCap ⟨11,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell12 :
    0 ≤ commonCap ⟨12,by decide⟩ ∧ commonUpper ⟨12,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨12,by decide⟩) (commonUpper ⟨12,by decide⟩) ≤ commonCap ⟨12,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell13 :
    0 ≤ commonCap ⟨13,by decide⟩ ∧ commonUpper ⟨13,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨13,by decide⟩) (commonUpper ⟨13,by decide⟩) ≤ commonCap ⟨13,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell14 :
    0 ≤ commonCap ⟨14,by decide⟩ ∧ commonUpper ⟨14,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨14,by decide⟩) (commonUpper ⟨14,by decide⟩) ≤ commonCap ⟨14,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell15 :
    0 ≤ commonCap ⟨15,by decide⟩ ∧ commonUpper ⟨15,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨15,by decide⟩) (commonUpper ⟨15,by decide⟩) ≤ commonCap ⟨15,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell16 :
    0 ≤ commonCap ⟨16,by decide⟩ ∧ commonUpper ⟨16,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨16,by decide⟩) (commonUpper ⟨16,by decide⟩) ≤ commonCap ⟨16,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell17 :
    0 ≤ commonCap ⟨17,by decide⟩ ∧ commonUpper ⟨17,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨17,by decide⟩) (commonUpper ⟨17,by decide⟩) ≤ commonCap ⟨17,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell18 :
    0 ≤ commonCap ⟨18,by decide⟩ ∧ commonUpper ⟨18,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨18,by decide⟩) (commonUpper ⟨18,by decide⟩) ≤ commonCap ⟨18,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell19 :
    0 ≤ commonCap ⟨19,by decide⟩ ∧ commonUpper ⟨19,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨19,by decide⟩) (commonUpper ⟨19,by decide⟩) ≤ commonCap ⟨19,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell20 :
    0 ≤ commonCap ⟨20,by decide⟩ ∧ commonUpper ⟨20,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨20,by decide⟩) (commonUpper ⟨20,by decide⟩) ≤ commonCap ⟨20,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell21 :
    0 ≤ commonCap ⟨21,by decide⟩ ∧ commonUpper ⟨21,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨21,by decide⟩) (commonUpper ⟨21,by decide⟩) ≤ commonCap ⟨21,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell22 :
    0 ≤ commonCap ⟨22,by decide⟩ ∧ commonUpper ⟨22,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨22,by decide⟩) (commonUpper ⟨22,by decide⟩) ≤ commonCap ⟨22,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell23 :
    0 ≤ commonCap ⟨23,by decide⟩ ∧ commonUpper ⟨23,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨23,by decide⟩) (commonUpper ⟨23,by decide⟩) ≤ commonCap ⟨23,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell24 :
    0 ≤ commonCap ⟨24,by decide⟩ ∧ commonUpper ⟨24,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨24,by decide⟩) (commonUpper ⟨24,by decide⟩) ≤ commonCap ⟨24,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell25 :
    0 ≤ commonCap ⟨25,by decide⟩ ∧ commonUpper ⟨25,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨25,by decide⟩) (commonUpper ⟨25,by decide⟩) ≤ commonCap ⟨25,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell26 :
    0 ≤ commonCap ⟨26,by decide⟩ ∧ commonUpper ⟨26,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨26,by decide⟩) (commonUpper ⟨26,by decide⟩) ≤ commonCap ⟨26,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell27 :
    0 ≤ commonCap ⟨27,by decide⟩ ∧ commonUpper ⟨27,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨27,by decide⟩) (commonUpper ⟨27,by decide⟩) ≤ commonCap ⟨27,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell28 :
    0 ≤ commonCap ⟨28,by decide⟩ ∧ commonUpper ⟨28,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨28,by decide⟩) (commonUpper ⟨28,by decide⟩) ≤ commonCap ⟨28,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell29 :
    0 ≤ commonCap ⟨29,by decide⟩ ∧ commonUpper ⟨29,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨29,by decide⟩) (commonUpper ⟨29,by decide⟩) ≤ commonCap ⟨29,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell30 :
    0 ≤ commonCap ⟨30,by decide⟩ ∧ commonUpper ⟨30,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨30,by decide⟩) (commonUpper ⟨30,by decide⟩) ≤ commonCap ⟨30,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell31 :
    0 ≤ commonCap ⟨31,by decide⟩ ∧ commonUpper ⟨31,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨31,by decide⟩) (commonUpper ⟨31,by decide⟩) ≤ commonCap ⟨31,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell32 :
    0 ≤ commonCap ⟨32,by decide⟩ ∧ commonUpper ⟨32,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨32,by decide⟩) (commonUpper ⟨32,by decide⟩) ≤ commonCap ⟨32,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell33 :
    0 ≤ commonCap ⟨33,by decide⟩ ∧ commonUpper ⟨33,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨33,by decide⟩) (commonUpper ⟨33,by decide⟩) ≤ commonCap ⟨33,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell34 :
    0 ≤ commonCap ⟨34,by decide⟩ ∧ commonUpper ⟨34,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨34,by decide⟩) (commonUpper ⟨34,by decide⟩) ≤ commonCap ⟨34,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell35 :
    0 ≤ commonCap ⟨35,by decide⟩ ∧ commonUpper ⟨35,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨35,by decide⟩) (commonUpper ⟨35,by decide⟩) ≤ commonCap ⟨35,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell36 :
    0 ≤ commonCap ⟨36,by decide⟩ ∧ commonUpper ⟨36,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨36,by decide⟩) (commonUpper ⟨36,by decide⟩) ≤ commonCap ⟨36,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell37 :
    0 ≤ commonCap ⟨37,by decide⟩ ∧ commonUpper ⟨37,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨37,by decide⟩) (commonUpper ⟨37,by decide⟩) ≤ commonCap ⟨37,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell38 :
    0 ≤ commonCap ⟨38,by decide⟩ ∧ commonUpper ⟨38,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨38,by decide⟩) (commonUpper ⟨38,by decide⟩) ≤ commonCap ⟨38,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell39 :
    0 ≤ commonCap ⟨39,by decide⟩ ∧ commonUpper ⟨39,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨39,by decide⟩) (commonUpper ⟨39,by decide⟩) ≤ commonCap ⟨39,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell40 :
    0 ≤ commonCap ⟨40,by decide⟩ ∧ commonUpper ⟨40,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨40,by decide⟩) (commonUpper ⟨40,by decide⟩) ≤ commonCap ⟨40,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell41 :
    0 ≤ commonCap ⟨41,by decide⟩ ∧ commonUpper ⟨41,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨41,by decide⟩) (commonUpper ⟨41,by decide⟩) ≤ commonCap ⟨41,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCell42 :
    0 ≤ commonCap ⟨42,by decide⟩ ∧ commonUpper ⟨42,by decide⟩ ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters ⟨42,by decide⟩) (commonUpper ⟨42,by decide⟩) ≤ commonCap ⟨42,by decide⟩ := by
  norm_num [commonCap,commonUpper,parameters,envelope]

theorem commonCells (j : Fin 43) :
    0 ≤ commonCap j ∧ commonUpper j ≤ (528/1000 : ℝ) ∧
    envelope 11883 (parameters j) (commonUpper j) ≤ commonCap j := by
  match j with
  | ⟨0,_⟩ => exact commonCell0
  | ⟨1,_⟩ => exact commonCell1
  | ⟨2,_⟩ => exact commonCell2
  | ⟨3,_⟩ => exact commonCell3
  | ⟨4,_⟩ => exact commonCell4
  | ⟨5,_⟩ => exact commonCell5
  | ⟨6,_⟩ => exact commonCell6
  | ⟨7,_⟩ => exact commonCell7
  | ⟨8,_⟩ => exact commonCell8
  | ⟨9,_⟩ => exact commonCell9
  | ⟨10,_⟩ => exact commonCell10
  | ⟨11,_⟩ => exact commonCell11
  | ⟨12,_⟩ => exact commonCell12
  | ⟨13,_⟩ => exact commonCell13
  | ⟨14,_⟩ => exact commonCell14
  | ⟨15,_⟩ => exact commonCell15
  | ⟨16,_⟩ => exact commonCell16
  | ⟨17,_⟩ => exact commonCell17
  | ⟨18,_⟩ => exact commonCell18
  | ⟨19,_⟩ => exact commonCell19
  | ⟨20,_⟩ => exact commonCell20
  | ⟨21,_⟩ => exact commonCell21
  | ⟨22,_⟩ => exact commonCell22
  | ⟨23,_⟩ => exact commonCell23
  | ⟨24,_⟩ => exact commonCell24
  | ⟨25,_⟩ => exact commonCell25
  | ⟨26,_⟩ => exact commonCell26
  | ⟨27,_⟩ => exact commonCell27
  | ⟨28,_⟩ => exact commonCell28
  | ⟨29,_⟩ => exact commonCell29
  | ⟨30,_⟩ => exact commonCell30
  | ⟨31,_⟩ => exact commonCell31
  | ⟨32,_⟩ => exact commonCell32
  | ⟨33,_⟩ => exact commonCell33
  | ⟨34,_⟩ => exact commonCell34
  | ⟨35,_⟩ => exact commonCell35
  | ⟨36,_⟩ => exact commonCell36
  | ⟨37,_⟩ => exact commonCell37
  | ⟨38,_⟩ => exact commonCell38
  | ⟨39,_⟩ => exact commonCell39
  | ⟨40,_⟩ => exact commonCell40
  | ⟨41,_⟩ => exact commonCell41
  | ⟨42,_⟩ => exact commonCell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem commonCap_mono : Monotone commonCap := Fin.monotone_iff_le_succ.mpr (by
  intro j
  fin_cases j <;> norm_num [commonCap])

theorem common_cap_bound {n : ℕ} (hn : 11883 ≤ n) (j : Fin 43) {θ : ℝ}
    (hθ : 0 ≤ θ) (hupper : θ ≤ commonUpper j) :
    envelope n (parameters j) θ ≤ commonCap j := by
  have hp := parameters_valid j
  have hhi := (commonCells j).2.1
  have hm := envelope_mono hn (parameters j) hp hθ hupper hhi hp.wRadius_lt hp.cRadius_lt
  exact hm.trans ((BstLean.Part277.envelope_dimension_leP (by norm_num : 8000 ≤ 11883) hn
    (parameters j) hp (hθ.trans hupper) hhi).trans (commonCells j).2.2)
end BstLean.Part281
