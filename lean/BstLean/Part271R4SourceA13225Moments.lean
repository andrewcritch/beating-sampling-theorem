import BstLean.Part271R4SourceCommon

/-! Source moment intervals on dimensions 13225 through 16199. -/
namespace BstLean.Part271.R4.A13225
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211
open BstLean.Part228 BstLean.Part250 BstLean.Part271.R4

theorem source_wn {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (wn n) (103167486688856030173411903/100000000000000000000000000) (25877126654064272211720227/25000000000000000000000000) := by
  let v0 : ℝ := Real.sqrt (n : ℝ)
  have h0 : Bounds v0 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v2 : ℝ := 1/v0
  have h2 : Bounds v2 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h0 (by norm_num)
  let v3 : ℝ := v1/v0
  have h3 : Bounds v3 (15713969032896732137508313/1000000000000000000000000000) (869565217391304347826087/50000000000000000000000000) := bounds_div h1 h2 (by norm_num)
  let v4 : ℝ := 1
  have h4 : Bounds v4 1 1 := Bounds.point _
  let v5 : ℝ := v3+v4
  have h5 : Bounds v5 (101571396903289673213750831/100000000000000000000000000) (50869565217391304347826087/50000000000000000000000000) := Bounds.add h3 h4 (by norm_num)
  let v6 : ℝ := v5^2
  have h6 : Bounds v6 (103167486688856030173411903/100000000000000000000000000) (25877126654064272211720227/25000000000000000000000000) := Bounds.pow h5 2 (by norm_num)
  convert h6 using 1 <;>
    simp only [v0, v1, v3, v4, v5, v6, wn] <;> ring

theorem source_rho {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (rhoBar n csC) (196686148953936447568286161/1000000000000000000000000000000) (6042827170051984846295059/25000000000000000000000000000) := by
  let v7 : ℝ := 4
  have h7 : Bounds v7 4 4 := Bounds.point _
  let v8 : ℝ := (wn n)*v7
  have h8 : Bounds v8 (41266994675542412069364761/10000000000000000000000000) (10350850661625708884688091/2500000000000000000000000) := Bounds.mul (source_wn ha hb) h7 (by norm_num)
  let v9 : ℝ := csC*(n : ℝ)
  have h9 : Bounds v9 (68516609/4000) (5245284797/250000) := Bounds.mul source_cs (source_dimension ha hb) (by norm_num)
  let v10 : ℝ := 1/v9
  have h10 : Bounds v10 (47661854346399944391808779/1000000000000000000000000000000) (14595001337558897580585169/250000000000000000000000000000) := Bounds.inv h9 (by norm_num)
  let v11 : ℝ := v8/v9
  have h11 : Bounds v11 (196686148953936447568286161/1000000000000000000000000000000) (6042827170051984846295059/25000000000000000000000000000) := bounds_div h8 h10 (by norm_num)
  convert h11 using 1 <;>
    simp only [v7, v8, v9, v11, rhoBar] <;> ring

theorem source_nu {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (nuR (rhoBar n csC)) (157356656251387224069734531/200000000000000000000000000000) (96691077242464896497486263/100000000000000000000000000000) := by
  let v7 : ℝ := 4
  have h7 : Bounds v7 4 4 := Bounds.point _
  let v12 : ℝ := (rhoBar n csC)*v7
  have h12 : Bounds v12 (2458576861924205594603577/3125000000000000000000000000) (6042827170051984846295059/6250000000000000000000000000) := Bounds.mul (source_rho ha hb) h7 (by norm_num)
  let v13 : ℝ := (rhoBar n csC)^2
  have h13 : Bounds v13 (386854411903300755280150899/10000000000000000000000000000000000) (11685043266277913530637701/200000000000000000000000000000000) := Bounds.pow (source_rho ha hb) 2 (by norm_num)
  let v14 : ℝ := v12+v13
  have h14 : Bounds v14 (157356656251387224069734531/200000000000000000000000000000) (96691077242464896497486263/100000000000000000000000000000) := Bounds.add h12 h13 (by norm_num)
  convert h14 using 1 <;>
    simp only [v7, v12, v13, v14, nuR] <;> ring

theorem source_cc0 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (cc0 (rhoBar n csC) (piBar (rhoBar n csC))) 0 (36924347806356264884976121/200000000000000000000000000000) := by
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v15 : ℝ := (phiG 0)*(rhoBar n csC)
  have h15 : Bounds v15 0 (48221760817014839073434571/500000000000000000000000000000) := Bounds.mul source_phi0 (source_rho ha hb) (by norm_num)
  let v16 : ℝ := 1/v1
  have h16 : Bounds v16 (1/2) (1/2) := Bounds.inv h1 (by norm_num)
  let v17 : ℝ := v15/v1
  have h17 : Bounds v17 0 (48221760817014839073434571/1000000000000000000000000000000) := bounds_div h15 h16 (by norm_num)
  let v18 : ℝ := (phiG 0)*(nuR (rhoBar n csC))
  have h18 : Bounds v18 0 (38579739819743493702497019/100000000000000000000000000000) := Bounds.mul source_phi0 (source_nu ha hb) (by norm_num)
  let v19 : ℝ := Real.sqrt v1
  have h19 : Bounds v19 (17677669529663688110021109/12500000000000000000000000) (141421356237309504880168873/100000000000000000000000000) := Bounds.sqrt h1 (by norm_num)
  let v20 : ℝ := v19*v1
  have h20 : Bounds v20 (14142135623730950488016887/5000000000000000000000000) (1131370849898476039041351/400000000000000000000000) := Bounds.mul h19 h1 (by norm_num)
  let v21 : ℝ := 1/v20
  have h21 : Bounds v21 (176776695296636881100211087/500000000000000000000000000) (88388347648318440550105547/250000000000000000000000000) := Bounds.inv h20 (by norm_num)
  let v22 : ℝ := v18/v20
  have h22 : Bounds v22 0 (8524998638422905322833833/62500000000000000000000000000) := bounds_div h18 h21 (by norm_num)
  let v23 : ℝ := v17+v22
  have h23 : Bounds v23 0 (184621739031781324238775899/1000000000000000000000000000000) := Bounds.add h17 h22 (by norm_num)
  let v24 : ℝ := (3/2)
  have h24 : Bounds v24 (3/2) (3/2) := Bounds.point _
  let v25 : ℝ := (phiG 0)*v24
  have h25 : Bounds v25 0 (1197/2000) := Bounds.mul source_phi0 h24 (by norm_num)
  let v26 : ℝ := (piBar (rhoBar n csC))*(nuR (rhoBar n csC))
  have h26 : Bounds v26 0 (96691077242464896497486263/1000000000000000000000000000000000000000000000000000000000000000000000) := Bounds.mul (source_pi (lt_of_lt_of_le (by norm_num) (source_rho ha hb).1) ((source_rho ha hb).2.trans (by norm_num))) (source_nu ha hb) (by norm_num)
  let v27 : ℝ := Real.sqrt v26
  have h27 : Bounds v27 0 (310951888951433926640541489/1000000000000000000000000000000000000000000000000) := Bounds.sqrt h26 (by norm_num)
  let v28 : ℝ := v25*v27
  have h28 : Bounds v28 0 (93052352768716602547182041/500000000000000000000000000000000000000000000000) := Bounds.mul h25 h27 (by norm_num)
  let v29 : ℝ := v23+v28
  have h29 : Bounds v29 0 (36924347806356264884976121/200000000000000000000000000000) := Bounds.add h23 h28 (by norm_num)
  convert h29 using 1 <;>
    simp only [v1, v15, v17, v18, v19, v20, v22, v23, v24, v25, v26, v27, v28, v29, cc0] <;> ring

theorem source_cc1 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (cc1 (rhoBar n csC) (piBar (rhoBar n csC))) 0 (11747610946408433967660569/100000000000000000000000000000) := by
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v30 : ℝ := (rhoBar n csC)*(nuR (rhoBar n csC))
  have h30 : Bounds v30 (38687343412942153030451557/250000000000000000000000000000000) (233714987464944810045920417/1000000000000000000000000000000000) := Bounds.mul (source_rho ha hb) (source_nu ha hb) (by norm_num)
  let v31 : ℝ := Real.sqrt v30
  have h31 : Bounds v31 (49172746143660560910762087/125000000000000000000000000000) (483440779687589873932770349/1000000000000000000000000000000) := Bounds.sqrt h30 (by norm_num)
  let v32 : ℝ := (phiG 1)*v31
  have h32 : Bounds v32 0 (23495221892816867873132639/200000000000000000000000000000) := Bounds.mul source_phi1 h31 (by norm_num)
  let v33 : ℝ := (piBar (rhoBar n csC))*(rhoBar n csC)
  have h33 : Bounds v33 0 (6042827170051984846295059/250000000000000000000000000000000000000000000000000000000000000000000) := Bounds.mul (source_pi (lt_of_lt_of_le (by norm_num) (source_rho ha hb).1) ((source_rho ha hb).2.trans (by norm_num))) (source_rho ha hb) (by norm_num)
  let v34 : ℝ := Real.sqrt v33
  have h34 : Bounds v34 0 (19433905889662249079495957/125000000000000000000000000000000000000000000000) := Bounds.sqrt h33 (by norm_num)
  let v35 : ℝ := v34*v1
  have h35 : Bounds v35 0 (7773562355864899631798383/25000000000000000000000000000000000000000000000) := Bounds.mul h34 h1 (by norm_num)
  let v36 : ℝ := v32+v35
  have h36 : Bounds v36 0 (11747610946408433967660569/100000000000000000000000000000) := Bounds.add h32 h35 (by norm_num)
  convert h36 using 1 <;>
    simp only [v1, v30, v31, v32, v33, v34, v35, v36, cc1] <;> ring

theorem source_cc2 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (cc2 (rhoBar n csC)) 0 (34097934074466942989113099/500000000000000000000000000000) := by
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v37 : ℝ := (phiG 0)*(rhoBar n csC)
  have h37 : Bounds v37 0 (48221760817014839073434571/500000000000000000000000000000) := Bounds.mul source_phi0 (source_rho ha hb) (by norm_num)
  let v38 : ℝ := Real.sqrt v1
  have h38 : Bounds v38 (17677669529663688110021109/12500000000000000000000000) (141421356237309504880168873/100000000000000000000000000) := Bounds.sqrt h1 (by norm_num)
  let v39 : ℝ := 1/v38
  have h39 : Bounds v39 (14142135623730950488016887/20000000000000000000000000) (70710678118654752440084437/100000000000000000000000000) := Bounds.inv h38 (by norm_num)
  let v40 : ℝ := v37/v38
  have h40 : Bounds v40 0 (34097934074466942989113099/500000000000000000000000000000) := bounds_div h37 h39 (by norm_num)
  convert h40 using 1 <;>
    simp only [v1, v37, v38, v40, cc2] <;> ring

theorem source_qb {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (QB (rhoBar n csC) (piBar (rhoBar n csC))) 0 (147197441920791039860045413/1000000000000000000000000000000000) := by
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v7 : ℝ := 4
  have h7 : Bounds v7 4 4 := Bounds.point _
  let v41 : ℝ := (cc0 (rhoBar n csC) (piBar (rhoBar n csC)))^2
  have h41 : Bounds v41 0 (34085186523119167767099317/1000000000000000000000000000000000) := Bounds.pow (source_cc0 ha hb) 2 (by norm_num)
  let v42 : ℝ := (cc1 (rhoBar n csC) (piBar (rhoBar n csC)))^2
  have h42 : Bounds v42 0 (1725079536852190770182273/125000000000000000000000000000000) := Bounds.pow (source_cc1 ha hb) 2 (by norm_num)
  let v43 : ℝ := v41+v42
  have h43 : Bounds v43 0 (47885822817936693928557501/1000000000000000000000000000000000) := Bounds.add h41 h42 (by norm_num)
  let v44 : ℝ := (cc2 (rhoBar n csC))^2
  have h44 : Bounds v44 0 (23253382162933876399888159/5000000000000000000000000000000000) := Bounds.pow (source_cc2 ha hb) 2 (by norm_num)
  let v45 : ℝ := 3
  have h45 : Bounds v45 3 3 := Bounds.point _
  let v46 : ℝ := v44*v45
  have h46 : Bounds v46 0 (69760146488801629199664477/5000000000000000000000000000000000) := Bounds.mul h44 h45 (by norm_num)
  let v47 : ℝ := v43+v46
  have h47 : Bounds v47 0 (61837852115697019768490397/1000000000000000000000000000000000) := Bounds.add h43 h46 (by norm_num)
  let v48 : ℝ := 1/π
  have h48 : Bounds v48 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v49 : ℝ := v1/π
  have h49 : Bounds v49 (15915494309189533576851107/25000000000000000000000000) (1989436788648691697112721/3125000000000000000000000) := bounds_div h1 h48 (by norm_num)
  let v50 : ℝ := Real.sqrt v49
  have h50 : Bounds v50 (79788456080286535587895791/100000000000000000000000000) (3989422804014326779401139/5000000000000000000000000) := Bounds.sqrt h49 (by norm_num)
  let v51 : ℝ := v50*v1
  have h51 : Bounds v51 (79788456080286535587895791/50000000000000000000000000) (3989422804014326779401139/2500000000000000000000000) := Bounds.mul h50 h1 (by norm_num)
  let v52 : ℝ := v51*(cc0 (rhoBar n csC) (piBar (rhoBar n csC)))
  have h52 : Bounds v52 0 (5892273406481362650637631/20000000000000000000000000000) := Bounds.mul h51 (source_cc0 ha hb) (by norm_num)
  let v53 : ℝ := v52*(cc1 (rhoBar n csC) (piBar (rhoBar n csC)))
  have h53 : Bounds v53 0 (173050338923029419563940619/5000000000000000000000000000000000) := Bounds.mul h52 (source_cc1 ha hb) (by norm_num)
  let v54 : ℝ := v47+v53
  have h54 : Bounds v54 0 (96447919900302903681278521/1000000000000000000000000000000000) := Bounds.add h47 h53 (by norm_num)
  let v55 : ℝ := (cc0 (rhoBar n csC) (piBar (rhoBar n csC)))*v1
  have h55 : Bounds v55 0 (36924347806356264884976121/100000000000000000000000000000) := Bounds.mul (source_cc0 ha hb) h1 (by norm_num)
  let v56 : ℝ := v55*(cc2 (rhoBar n csC))
  have h56 : Bounds v56 0 (12590439772438240035405487/500000000000000000000000000000000) := Bounds.mul h55 (source_cc2 ha hb) (by norm_num)
  let v57 : ℝ := v54+v56
  have h57 : Bounds v57 0 (24325759889035876750417899/200000000000000000000000000000000) := Bounds.add h54 h56 (by norm_num)
  let v58 : ℝ := 1/π
  have h58 : Bounds v58 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v59 : ℝ := v1/π
  have h59 : Bounds v59 (15915494309189533576851107/25000000000000000000000000) (1989436788648691697112721/3125000000000000000000000) := bounds_div h1 h58 (by norm_num)
  let v60 : ℝ := Real.sqrt v59
  have h60 : Bounds v60 (79788456080286535587895791/100000000000000000000000000) (3989422804014326779401139/5000000000000000000000000) := Bounds.sqrt h59 (by norm_num)
  let v61 : ℝ := v60*v7
  have h61 : Bounds v61 (79788456080286535587895791/25000000000000000000000000) (3989422804014326779401139/1250000000000000000000000) := Bounds.mul h60 h7 (by norm_num)
  let v62 : ℝ := v61*(cc1 (rhoBar n csC) (piBar (rhoBar n csC)))
  have h62 : Bounds v62 0 (5858273375286266724879109/15625000000000000000000000000) := Bounds.mul h61 (source_cc1 ha hb) (by norm_num)
  let v63 : ℝ := v62*(cc2 (rhoBar n csC))
  have h63 : Bounds v63 0 (12784321237805828053977959/500000000000000000000000000000000) := Bounds.mul h62 (source_cc2 ha hb) (by norm_num)
  let v64 : ℝ := v57+v63
  have h64 : Bounds v64 0 (147197441920791039860045413/1000000000000000000000000000000000) := Bounds.add h57 h63 (by norm_num)
  convert h64 using 1 <;>
    simp only [v1, v7, v41, v42, v43, v44, v45, v46, v47, v49, v50, v51, v52, v53, v54, v55, v56, v57, v59, v60, v61, v62, v63, v64, QB] <;> ring

theorem source_bncoef {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (4 * wn n * QB (rhoBar n csC) (piBar (rhoBar n csC)) / rhoBar n csC) 0 (309857861816646913636134703/100000000000000000000000000000) := by
  let v7 : ℝ := 4
  have h7 : Bounds v7 4 4 := Bounds.point _
  let v65 : ℝ := (wn n)*v7
  have h65 : Bounds v65 (41266994675542412069364761/10000000000000000000000000) (10350850661625708884688091/2500000000000000000000000) := Bounds.mul (source_wn ha hb) h7 (by norm_num)
  let v66 : ℝ := v65*(QB (rhoBar n csC) (piBar (rhoBar n csC)))
  have h66 : Bounds v66 0 (12188949912763454334331413/20000000000000000000000000000000) := Bounds.mul h65 (source_qb ha hb) (by norm_num)
  let v67 : ℝ := 1/(rhoBar n csC)
  have h67 : Bounds v67 (41371363595998612024253047/10000000000000000000000) (25421210525459986833730533/5000000000000000000000) := Bounds.inv (source_rho ha hb) (by norm_num)
  let v68 : ℝ := v66/(rhoBar n csC)
  have h68 : Bounds v68 0 (309857861816646913636134703/100000000000000000000000000000) := bounds_div h66 h67 (by norm_num)
  convert h68 using 1 <;>
    simp only [v7, v65, v66, v68] <;> ring

theorem source_linear0 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (4 * wn n * (6863/10000) * rhoBar n csC * n * nuR (rhoBar n csC) / π) (92248975800089997477916759/50000000000000000000000000000) (3424324625830753252502757/1000000000000000000000000000) := by
  let v7 : ℝ := 4
  have h7 : Bounds v7 4 4 := Bounds.point _
  let v69 : ℝ := (wn n)*v7
  have h69 : Bounds v69 (41266994675542412069364761/10000000000000000000000000) (10350850661625708884688091/2500000000000000000000000) := Bounds.mul (source_wn ha hb) h7 (by norm_num)
  let v70 : ℝ := (6863/10000)
  have h70 : Bounds v70 (6863/10000) (6863/10000) := Bounds.point _
  let v71 : ℝ := v69*v70
  have h71 : Bounds v71 (141607692229123787016025177/50000000000000000000000000) (11366062094517958412098299/4000000000000000000000000) := Bounds.mul h69 h70 (by norm_num)
  let v72 : ℝ := v71*(rhoBar n csC)
  have h72 : Bounds v72 (27852271646800629956747953/50000000000000000000000000000) (21463484012890965667662897/31250000000000000000000000000) := Bounds.mul h71 (source_rho ha hb) (by norm_num)
  let v73 : ℝ := v72*(n : ℝ)
  have h73 : Bounds v73 (14733851701157533247119667/2000000000000000000000000) (55629916403971320456075403/5000000000000000000000000) := Bounds.mul h72 (source_dimension ha hb) (by norm_num)
  let v74 : ℝ := v73*(nuR (rhoBar n csC))
  have h74 : Bounds v74 (57961740934949070999617513/10000000000000000000000000000) (107578330880165119501255627/10000000000000000000000000000) := Bounds.mul h73 (source_nu ha hb) (by norm_num)
  let v75 : ℝ := 1/π
  have h75 : Bounds v75 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v76 : ℝ := v74/π
  have h76 : Bounds v76 (92248975800089997477916759/50000000000000000000000000000) (3424324625830753252502757/1000000000000000000000000000) := bounds_div h74 h75 (by norm_num)
  convert h76 using 1 <;>
    simp only [v7, v69, v70, v71, v72, v73, v74, v76] <;> ring

theorem source_linear1 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (4 * wn n * (2 * rhoBar n csC / π + piBar (rhoBar n csC))) (6459021869337846784247177/12500000000000000000000000000) (31855639356553968596258463/50000000000000000000000000000) := by
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v7 : ℝ := 4
  have h7 : Bounds v7 4 4 := Bounds.point _
  let v77 : ℝ := (wn n)*v7
  have h77 : Bounds v77 (41266994675542412069364761/10000000000000000000000000) (10350850661625708884688091/2500000000000000000000000) := Bounds.mul (source_wn ha hb) h7 (by norm_num)
  let v78 : ℝ := (rhoBar n csC)*v1
  have h78 : Bounds v78 (2458576861924205594603577/6250000000000000000000000000) (6042827170051984846295059/12500000000000000000000000000) := Bounds.mul (source_rho ha hb) h1 (by norm_num)
  let v79 : ℝ := 1/π
  have h79 : Bounds v79 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v80 : ℝ := v78/π
  have h80 : Bounds v80 (62607145687455609274980889/500000000000000000000000000000) (153879330298205213925603827/1000000000000000000000000000000) := bounds_div h78 h79 (by norm_num)
  let v81 : ℝ := v80+(piBar (rhoBar n csC))
  have h81 : Bounds v81 (62607145687455609274980889/500000000000000000000000000000) (38469832574551303481400957/250000000000000000000000000000) := Bounds.add h80 (source_pi (lt_of_lt_of_le (by norm_num) (source_rho ha hb).1) ((source_rho ha hb).2.trans (by norm_num))) (by norm_num)
  let v82 : ℝ := v77*v81
  have h82 : Bounds v82 (6459021869337846784247177/12500000000000000000000000000) (31855639356553968596258463/50000000000000000000000000000) := Bounds.mul h77 h81 (by norm_num)
  convert h82 using 1 <;>
    simp only [v1, v7, v77, v78, v80, v81, v82] <;> ring

theorem source_gamma {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) (Θ : ℝ) (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    Bounds (gammaRatio n 0.011 Θ) (1481106164877476361208227/25000000000000000000000000000) (41547354337053502818040011/500000000000000000000000000000) := by
  let v1 : ℝ := 2
  have h1 : Bounds v1 2 2 := Bounds.point _
  let v83 : ℝ := (wn n)*v1
  have h83 : Bounds v83 (1031674866888560301734119/500000000000000000000000) (25877126654064272211720227/12500000000000000000000000) := Bounds.mul (source_wn ha hb) h1 (by norm_num)
  let v84 : ℝ := v83*Θ
  have h84 : Bounds v84 (23728521938436886939884737/25000000000000000000000000) (54341965973534971644612477/50000000000000000000000000) := Bounds.mul h83 hw (by norm_num)
  let v85 : ℝ := (989/1000)
  have h85 : Bounds v85 (989/1000) (989/1000) := Bounds.point _
  let v86 : ℝ := (n : ℝ)*v85
  have h86 : Bounds v86 (523181/40) (16020811/1000) := Bounds.mul (source_dimension ha hb) h85 (by norm_num)
  let v87 : ℝ := 1/v86
  have h87 : Bounds v87 (62418812630646476011732489/1000000000000000000000000000000) (4778460991511541894678897/62500000000000000000000000000) := Bounds.inv h86 (by norm_num)
  let v88 : ℝ := v84/v86
  have h88 : Bounds v88 (1481106164877476361208227/25000000000000000000000000000) (41547354337053502818040011/500000000000000000000000000000) := bounds_div h84 h87 (by norm_num)
  convert h88 using 1 <;>
    simp only [v1, v83, v84, v85, v86, v88, gammaRatio] <;> ring

theorem source_exp0 : exp (-(92/5) : ℝ) ≤ (10208961357/1000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((789548224361/250000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem source_exp1 : exp (-(91/5) : ℝ) ≤ (12469253473/1000000000000000000) := by
  apply BstLean.Part269.Tails.exp_negative_sixteen_bound (E := ((3118961196557/1000000000000) : ℝ))
  all_goals norm_num [Finset.sum_range_succ, Nat.factorial]

theorem source_bad {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    badAllowance n csC 0.011 1.22 1.12 Θ ≤ (88133751/250000000000) := by
  have hnR : (n : ℝ) ≤ 16199 := by exact_mod_cast hb
  have hr := source_rho ha hb
  have hg := source_gamma ha hb Θ hw
  have hr0 : 0 < rhoBar n csC := lt_of_lt_of_le (by norm_num) hr.1
  have hg0 : 0 < gammaRatio n 0.011 Θ := lt_of_lt_of_le (by norm_num) hg.1
  have hrU : rhoBar n csC ≤ (12085654340109/50000000000000000) := hr.2.trans (by norm_num)
  have hgU : gammaRatio n 0.011 Θ ≤ (41547354337071/500000000000000000) := hg.2.trans (by norm_num)
  have ht1 : tail 2 (rhoBar n csC) 1.22 ≤ (10208961357/1000000000000000000) :=
    source_tail (r := (12085654340109/50000000000000000)) (g := 0.09438)
      (E := (92/5)) hr0 hrU
      (by norm_num) (source_gap2 (hrU.trans (by norm_num)))
      (by norm_num) (by norm_num) source_exp0
  have ht2 : tail 1 (gammaRatio n 0.011 Θ) 1.12 ≤ (12469253473/1000000000000000000) :=
    source_tail (r := (41547354337071/500000000000000000)) (g := 0.055043)
      (E := (91/5)) hg0 hgU
      (by norm_num) (source_gap1 (hgU.trans (by norm_num)))
      (by norm_num) (by norm_num) source_exp1
  have ht10 : 0 ≤ tail 2 (rhoBar n csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio n 0.011 Θ) 1.12 := (exp_pos _).le
  have hw0 : 0 ≤ wn n := by unfold wn; positivity
  have hwu : wn n ≤ (1035085066163/1000000000000) := (source_wn ha hb).2.trans (by norm_num)
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  calc
    _ ≤ (1035085066163/1000000000000) * 16199 *
        ((10208961357/1000000000000000000) / (1.1045361 : ℝ) + (12469253473/1000000000000000000) / 1.05830052) := by gcongr
    _ ≤ _ := by norm_num

theorem source_bn_upper {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN n csC Θ ≤ (3098579317/1000000000000) * Θ := by
  have h : 4 * wn n * QB (rhoBar n csC) (piBar (rhoBar n csC)) / rhoBar n csC ≤
      (3098579317/1000000000000) := (source_bncoef ha hb).2.trans (by norm_num)
  have hm := mul_le_mul_of_nonneg_right h hΘ
  convert hm using 1 <;> unfold bN <;> ring

theorem source_moment_upper {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance n csC 0.011 1.22 1.12 Θ S ≤
      0.2654 * S + (3776860343/1000000000000) + (3735692237/1000000000000) * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have h0 : 4 * wn n * (6863/10000) * rhoBar n csC * n * nuR (rhoBar n csC) / π ≤
      (3424325339/1000000000000) := (source_linear0 ha hb).2.trans (by norm_num)
  have h1 : 4 * wn n * (2 * rhoBar n csC / π + piBar (rhoBar n csC)) ≤
      (15927823/25000000000) := (source_linear1 ha hb).2.trans (by norm_num)
  have h1' := mul_le_mul_of_nonneg_right h1 hΘ
  have he : linearAllowance n csC Θ =
      4 * wn n * (6863/10000) * rhoBar n csC * n * nuR (rhoBar n csC) / π +
      (4 * wn n * (2 * rhoBar n csC / π + piBar (rhoBar n csC))) * Θ := by
    unfold linearAllowance
    ring
  have hl : linearAllowance n csC Θ ≤ (3424325339/1000000000000) + (15927823/25000000000) * Θ := by
    rw [he]
    exact add_le_add h0 h1'
  have hr := BstLean.Part264.pilot_rest_upper hS
  have ht := source_bad ha hb hw
  have hbn := source_bn_upper ha hb hΘ
  unfold momentAllowance
  linarith

end BstLean.Part271.R4.A13225
