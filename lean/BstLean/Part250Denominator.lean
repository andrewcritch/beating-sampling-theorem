import BstLean.Part250Bounds

/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
theorem denominator : Bounds (1 - (161/10000 : ℝ) - (4938/10000 + 1118/100000)^2 / centreLower 12225 (1232/10^7)) (46727425734650091187273241/100000000000000000000000000) (11683949405241464991479341/25000000000000000000000000) := by
  let v1 : ℝ := 202009148155087
  have h1 : Bounds v1 202009148155087 202009148155087 := Bounds.point _
  let v2 : ℝ := (129/2000)
  have h2 : Bounds v2 (129/2000) (129/2000) := Bounds.point _
  let v3 : ℝ := 1/v1
  have h3 : Bounds v3 (24751354310753227442987949/5000000000000000000000000000000000000000) (49502708621506454885975899/10000000000000000000000000000000000000000) := Bounds.inv h1 (by norm_num)
  let v4 : ℝ := v2/v1
  have h4 : Bounds v4 (159646235304358317007272271/500000000000000000000000000000000000000000) (319292470608716634014544549/1000000000000000000000000000000000000000000) := bounds_div h2 h3 (by norm_num)
  let v19 : ℝ := (77/625000)
  have h19 : Bounds v19 (77/625000) (77/625000) := Bounds.point _
  let v20 : ℝ := -v19
  have h20 : Bounds v20 (-77/625000) (-77/625000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h19
  let v21 : ℝ := kap1 (2*12225)+v20
  have h21 : Bounds v21 (154249/312500) (77137/156250) := Bounds.add kap_bounds h20 (by norm_num)
  let v22 : ℝ := Real.sqrt v21
  have h22 : Bounds v22 (17564111136063788867157733/25000000000000000000000000) (175655344353651819084224363/250000000000000000000000000) := Bounds.sqrt h21 (by norm_num)
  let v23 : ℝ := Real.sqrt v4
  have h23 : Bounds v23 (7147502731541601967317513/400000000000000000000000000000000) (44671892072135012295734457/2500000000000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v24 : ℝ := -v23
  have h24 : Bounds v24 (-44671892072135012295734457/2500000000000000000000000000000000) (-7147502731541601967317513/400000000000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h23
  let v25 : ℝ := v22+v24
  have h25 : Bounds v25 (1756411068934486814580761/2500000000000000000000000) (35131067977292522374144627/50000000000000000000000000) := Bounds.add h22 h24 (by norm_num)
  let v26 : ℝ := v25^2
  have h26 : Bounds v26 (24679838744604692743461523/50000000000000000000000000) (49367677489005924774032889/100000000000000000000000000) := Bounds.pow h25 2 (by norm_num)
  let v27 : ℝ := (161/10000)
  have h27 : Bounds v27 (161/10000) (161/10000) := Bounds.point _
  let v28 : ℝ := 1
  have h28 : Bounds v28 1 1 := Bounds.point _
  let v29 : ℝ := -v27
  have h29 : Bounds v29 (-161/10000) (-161/10000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h27
  let v30 : ℝ := v28+v29
  have h30 : Bounds v30 (9839/10000) (9839/10000) := Bounds.add h28 h29 (by norm_num)
  let v31 : ℝ := (2469/5000)
  have h31 : Bounds v31 (2469/5000) (2469/5000) := Bounds.point _
  let v32 : ℝ := (559/50000)
  have h32 : Bounds v32 (559/50000) (559/50000) := Bounds.point _
  let v33 : ℝ := v31+v32
  have h33 : Bounds v33 (25249/50000) (25249/50000) := Bounds.add h31 h32 (by norm_num)
  let v34 : ℝ := v33^2
  have h34 : Bounds v34 (637512001/2500000000) (637512001/2500000000) := Bounds.pow h33 2 (by norm_num)
  let v35 : ℝ := 1/v26
  have h35 : Bounds v35 (5064042157050520766792851/2500000000000000000000000) (202594516590715555850088061/100000000000000000000000000) := Bounds.inv h26 (by norm_num)
  let v36 : ℝ := v34/v26
  have h36 : Bounds v36 (12913550594758535008520659/25000000000000000000000000) (51662574265349908812726759/100000000000000000000000000) := bounds_div h34 h35 (by norm_num)
  let v37 : ℝ := -v36
  have h37 : Bounds v37 (-51662574265349908812726759/100000000000000000000000000) (-12913550594758535008520659/25000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h36
  let v38 : ℝ := v30+v37
  have h38 : Bounds v38 (46727425734650091187273241/100000000000000000000000000) (11683949405241464991479341/25000000000000000000000000) := Bounds.add h30 h37 (by norm_num)
  convert h38 using 1 <;>
    simp only [v1, v2, v4, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v36, v37, v38, centreLower, perturbation, width] <;> norm_num <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.denominator
