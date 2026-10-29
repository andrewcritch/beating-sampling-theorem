import BstLean.Part287UniformAssembly

/-! Band assembly generated from the Part285 records. No individual row enumeration. -/
namespace BstLean.Part287
open Set

noncomputable def interval13484_13524 : IntervalInputs 13484 13524 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval13525_13824 : IntervalInputs 13525 13824 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval13825_14124 : IntervalInputs 13825 14124 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval14125_14424 : IntervalInputs 14125 14424 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval14425_14724 : IntervalInputs 14425 14724 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval14725_15024 : IntervalInputs 14725 15024 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval15025_15324 : IntervalInputs 15025 15324 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval15325_15624 : IntervalInputs 15325 15624 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval15625_15924 : IntervalInputs 15625 15924 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval15925_16199 : IntervalInputs 15925 16199 :=
  uniformIntervalInputs.restrict (by norm_num) (by norm_num)

noncomputable def interval13484_16199 : IntervalInputs 13484 16199 :=
  (((((((((interval13484_13524.append interval13525_13824).append interval13825_14124).append interval14125_14424).append interval14425_14724).append interval14725_15024).append interval15025_15324).append interval15325_15624).append interval15625_15924).append interval15925_16199)

end BstLean.Part287
