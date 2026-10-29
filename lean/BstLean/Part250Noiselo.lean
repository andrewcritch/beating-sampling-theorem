import BstLean.Part250Bounds

/-! Generated rational certificate; every interval step is kernel checked. -/
namespace BstLean.Part250
open Real BstLean.Part130 BstLean.Part140 BstLean.Part137 BstLean.Part159
open BstLean.Part227 BstLean.Part228
theorem noiselo : Bounds (noiseLower (202225/100000)) (47208061039176155206478087/100000000000000000000000000) (236040305195880776032390443/500000000000000000000000000) := by
  let v8 : ℝ := 2
  have h8 : Bounds v8 2 2 := Bounds.point _
  let v37 : ℝ := (8089/4000)
  have h37 : Bounds v37 (8089/4000) (8089/4000) := Bounds.point _
  let v38 : ℝ := 1
  have h38 : Bounds v38 1 1 := Bounds.point _
  let v39 : ℝ := -v38
  have h39 : Bounds v39 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h38
  let v40 : ℝ := v37+v39
  have h40 : Bounds v40 (4089/4000) (4089/4000) := Bounds.add h37 h39 (by norm_num)
  let v41 : ℝ := (9/2000)
  have h41 : Bounds v41 (9/2000) (9/2000) := Bounds.point _
  let v42 : ℝ := Real.sqrt v41
  have h42 : Bounds v42 (6708203932499369089227521/100000000000000000000000000) (670820393249936908922752101/10000000000000000000000000000) := Bounds.sqrt h41 (by norm_num)
  let v43 : ℝ := v42*v8
  have h43 : Bounds v43 (6708203932499369089227521/50000000000000000000000000) (134164078649987381784550421/1000000000000000000000000000) := Bounds.mul h42 h8 (by norm_num)
  let v44 : ℝ := v43+v38
  have h44 : Bounds v44 (56708203932499369089227521/50000000000000000000000000) (113416407864998738178455043/100000000000000000000000000) := Bounds.add h43 h38 (by norm_num)
  let v45 : ℝ := (9/1000)
  have h45 : Bounds v45 (9/1000) (9/1000) := Bounds.point _
  let v46 : ℝ := v44+v45
  have h46 : Bounds v46 (57158203932499369089227521/50000000000000000000000000) (114316407864998738178455043/100000000000000000000000000) := Bounds.add h44 h45 (by norm_num)
  let v47 : ℝ := -v38
  have h47 : Bounds v47 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h38
  let v48 : ℝ := v37+v47
  have h48 : Bounds v48 (4089/4000) (4089/4000) := Bounds.add h37 h47 (by norm_num)
  let v49 : ℝ := v46+v48
  have h49 : Bounds v49 (84586487447265132100959/39062500000000000000000) (216541407864998738178455043/100000000000000000000000000) := Bounds.add h46 h48 (by norm_num)
  let v50 : ℝ := 1/v49
  have h50 : Bounds v50 (9236108787317418480113101/20000000000000000000000000) (23090271968293546200282753/50000000000000000000000000) := Bounds.inv h49 (by norm_num)
  let v51 : ℝ := v40/v49
  have h51 : Bounds v51 (47208061039176155206478087/100000000000000000000000000) (236040305195880776032390443/500000000000000000000000000) := bounds_div h40 h50 (by norm_num)
  convert h51 using 1 <;>
    simp only [v8, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v51, noiseLower, cUp, width] <;> norm_num <;> ring
end BstLean.Part250
#print axioms BstLean.Part250.noiselo
