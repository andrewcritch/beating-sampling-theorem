import BstLean.Part253Retune

/-! Rational frame certificates for the larger centre allowances. -/
namespace BstLean.Part253

theorem retunedCell52 : RetunedDataCertificate 52 := by
  constructor <;> norm_num [retunedEnergy, retunedCentre, retunedCutoff, energyTable, centreTable, centreGroup, cutoffTable, capTable, massTable, BstLean.Part249.optionBAgentFrame]

end BstLean.Part253
