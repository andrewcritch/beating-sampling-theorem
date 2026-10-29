import BstLean.Part250Bounds

/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
theorem noisehi : Bounds (noiseUpper 12225 (202831/100000)) (261570075380831286567568599/500000000000000000000000000) (26157007538083128656756861/50000000000000000000000000) := by
  let v0 : ℝ := 12225
  have h0 : Bounds v0 12225 12225 := Bounds.point _
  let v8 : ℝ := 2
  have h8 : Bounds v8 2 2 := Bounds.point _
  let v38 : ℝ := 1
  have h38 : Bounds v38 1 1 := Bounds.point _
  let v52 : ℝ := (202831/100000)
  have h52 : Bounds v52 (202831/100000) (202831/100000) := Bounds.point _
  let v53 : ℝ := -v38
  have h53 : Bounds v53 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h38
  let v54 : ℝ := v52+v53
  have h54 : Bounds v54 (102831/100000) (102831/100000) := Bounds.add h52 h53 (by norm_num)
  let v55 : ℝ := 12
  have h55 : Bounds v55 12 12 := Bounds.point _
  let v56 : ℝ := 1/v0
  have h56 : Bounds v56 (20449897750511247443762781/250000000000000000000000000000) (654396728016359918200409/8000000000000000000000000000) := Bounds.inv h0 (by norm_num)
  let v57 : ℝ := v55/v0
  have h57 : Bounds v57 (24539877300613496932515337/25000000000000000000000000000) (1963190184049079754601227/2000000000000000000000000000) := bounds_div h55 h56 (by norm_num)
  let v58 : ℝ := Real.sqrt v57
  have h58 : Bounds v58 (313304179995182936483704341/10000000000000000000000000000) (62660835999036587296740869/2000000000000000000000000000) := Bounds.sqrt h57 (by norm_num)
  let v59 : ℝ := v58*v8
  have h59 : Bounds v59 (15665208999759146824185217/250000000000000000000000000) (62660835999036587296740869/1000000000000000000000000000) := Bounds.mul h58 h8 (by norm_num)
  let v60 : ℝ := -v59
  have h60 : Bounds v60 (-62660835999036587296740869/1000000000000000000000000000) (-15665208999759146824185217/250000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h59
  let v61 : ℝ := v38+v60
  have h61 : Bounds v61 (937339164000963412703259131/1000000000000000000000000000) (46866958200048170635162957/50000000000000000000000000) := Bounds.add h38 h60 (by norm_num)
  let v62 : ℝ := -v38
  have h62 : Bounds v62 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h38
  let v63 : ℝ := v52+v62
  have h63 : Bounds v63 (102831/100000) (102831/100000) := Bounds.add h52 h62 (by norm_num)
  let v64 : ℝ := v61+v63
  have h64 : Bounds v64 (196564916400096341270325913/100000000000000000000000000) (98282458200048170635162957/50000000000000000000000000) := Bounds.add h61 h63 (by norm_num)
  let v65 : ℝ := 1/v64
  have h65 : Bounds v65 (50873778409396249490439381/100000000000000000000000000) (50873778409396249490439383/100000000000000000000000000) := Bounds.inv h64 (by norm_num)
  let v66 : ℝ := v54/v64
  have h66 : Bounds v66 (261570075380831286567568599/500000000000000000000000000) (26157007538083128656756861/50000000000000000000000000) := bounds_div h54 h65 (by norm_num)
  convert h66 using 1 <;>
    simp only [v0, v8, v38, v52, v53, v54, v55, v57, v58, v59, v60, v61, v62, v63, v64, v66, noiseUpper, width] <;> norm_num <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.noisehi
