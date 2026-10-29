import BstLean.Part254Contract
import BstLean.Part253Local

/-! The checked Part253 contract with the larger Part254 caps. -/
namespace BstLean.Part254

theorem localCov_part253 : BstLean.Part253.LocalCovariance cell capTable :=
  localCov_contract

end BstLean.Part254
