import BstLean.Part290FrameBounds

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part140 BstLean.Part159 BstLean.Part233
open BstLean.Part228 BstLean.Part250
open BstLean.Part271.R3 (angularMomentCore angularMomentCore_formula j2Core j4Core
  jbCore aCore bCore offsetCore ba1Core ba2Core traceCore diagonalCore covariancePaymentCore normCore)
theorem ar_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (BstLean.Part271.R3.arCore n) (158113883008418966599944677/50000000000000000000000000) (316227766016846565136879261/100000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v131 : ℝ := 25
  have h131 : Bounds v131 25 25 := Bounds.point _
  let v132 : ℝ := (1/(mW n : ℝ))*v131
  have h132 : Bounds v132 0 (27296581507155635062611807/50000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h131 (by norm_num)
  let v133 : ℝ := 10
  have h133 : Bounds v133 10 10 := Bounds.point _
  let v134 : ℝ := v132+v133
  have h134 : Bounds v134 10 (12500000000000682414537679/1250000000000000000000000) := Bounds.add h132 h133 (by norm_num)
  let v135 : ℝ := Real.sqrt v134
  have h135 : Bounds v135 (158113883008418966599944677/50000000000000000000000000) (316227766016846565136879261/100000000000000000000000000) := Bounds.sqrt h134 (by norm_num)
  convert h135 using 1 <;>
    simp only [v131, v132, v133, v134, v135, BstLean.Part271.R3.arCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem ch_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (BstLean.Part271.R3.chCore n) (283075787737161115860442117/100000000000000000000000000) (283256553850738297947994189/100000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v136 : ℝ := 5
  have h136 : Bounds v136 5 5 := Bounds.point _
  let v137 : ℝ := (1/(mW n : ℝ))*v136
  have h137 : Bounds v137 0 (10918632602862254025044723/100000000000000000000000000000000000000) := Bounds.mul (inverse_width ha) h136 (by norm_num)
  let v138 : ℝ := v137+v15
  have h138 : Bounds v138 1 (100000000000010918632602863/100000000000000000000000000) := Bounds.add h137 h15 (by norm_num)
  let v139 : ℝ := 6
  have h139 : Bounds v139 6 6 := Bounds.point _
  let v140 : ℝ := v138*v139
  have h140 : Bounds v140 6 (30000000000003275589780859/5000000000000000000000000) := Bounds.mul h138 h139 (by norm_num)
  let v141 : ℝ := 1/π
  have h141 : Bounds v141 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v142 : ℝ := v15/π
  have h142 : Bounds v142 (15915494309189533576851107/50000000000000000000000000) (1989436788648691697112721/6250000000000000000000000) := bounds_div h15 h141 (by norm_num)
  let v143 : ℝ := Real.sqrt v136
  have h143 : Bounds v143 (111803398874989484820458683/50000000000000000000000000) (223606797749978969640917367/100000000000000000000000000) := Bounds.sqrt h136 (by norm_num)
  let v144 : ℝ := Real.sqrt (1/(n : ℝ))
  have h144 : Bounds v144 0 (27950849718747371205114671/2500000000000000000000000000) := Bounds.sqrt (inverse_n ha) (by norm_num)
  let v145 : ℝ := v143+v144
  have h145 : Bounds v145 (2795084971874737120511467/1250000000000000000000000) (112362415869364432244560977/50000000000000000000000000) := Bounds.add h143 h144 (by norm_num)
  let v146 : ℝ := v142*v145
  have h146 : Bounds v146 (71176254341717705847509591/100000000000000000000000000) (35766067806713147188487419/50000000000000000000000000) := Bounds.mul h142 h145 (by norm_num)
  let v147 : ℝ := (1/(n : ℝ))+v15
  have h147 : Bounds v147 1 (8001/8000) := Bounds.add (inverse_n ha) h15 (by norm_num)
  let v148 : ℝ := 1/v3
  have h148 : Bounds v148 (1/2) (1/2) := Bounds.inv h3 (by norm_num)
  let v149 : ℝ := v147/v3
  have h149 : Bounds v149 (1/2) (8001/16000) := bounds_div h147 h148 (by norm_num)
  let v150 : ℝ := Real.sqrt v149
  have h150 : Bounds v150 (17677669529663688110021109/25000000000000000000000000) (176787743494847515404747083/250000000000000000000000000) := Bounds.sqrt h149 (by norm_num)
  let v151 : ℝ := v146+v150
  have h151 : Bounds v151 (141886932460372458287594027/100000000000000000000000000) (17780904126420662567359209/12500000000000000000000000) := Bounds.add h146 h150 (by norm_num)
  let v152 : ℝ := v151^2
  have h152 : Bounds v152 (100659508015071477896960903/50000000000000000000000000) (202342752993896541078655477/100000000000000000000000000) := Bounds.pow h151 2 (by norm_num)
  let v153 : ℝ := v140+v152
  have h153 : Bounds v153 (4006595080150714778969609/500000000000000000000000) (802342752993962052874272657/100000000000000000000000000) := Bounds.add h140 h152 (by norm_num)
  let v154 : ℝ := Real.sqrt v153
  have h154 : Bounds v154 (283075787737161115860442117/100000000000000000000000000) (283256553850738297947994189/100000000000000000000000000) := Bounds.sqrt h153 (by norm_num)
  convert h154 using 1 <;>
    simp only [v3, v15, v136, v137, v138, v139, v140, v142, v143, v144, v145, v146, v147, v149, v150, v151, v152, v153, v154, chCore_inverse (n_positive ha), Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem arw_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (arW n) 0 (46730359730827773947099633/100000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v155 : ℝ := Real.sqrt (1/(mW n : ℝ))
  have h155 : Bounds v155 0 (36943593157106168970195211/250000000000000000000000000000000) := Bounds.sqrt (inverse_width ha) (by norm_num)
  let v156 : ℝ := (BstLean.Part271.R3.arCore n)*v155
  have h156 : Bounds v156 0 (46730359730827773947099633/100000000000000000000000000000000) := Bounds.mul (ar_bounds ha) h155 (by norm_num)
  convert h156 using 1 <;>
    simp only [v155, v156, arW_scaled_inverse, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem lx_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (BstLean.Part271.R3.lxCore n) (62539339726757915789324347/10000000000000000000000000) (78336523260099481614581703/12500000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := (129/2000)
  have h0 : Bounds v0 (129/2000) (129/2000) := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v29 : ℝ := (1001/1000)
  have h29 : Bounds v29 (1001/1000) (1001/1000) := Bounds.point _
  let v157 : ℝ := v29*(BstLean.Part271.R3.chCore n)
  have h157 : Bounds v157 (283358863524898276976302559/100000000000000000000000000) (35442476300573629530742773/12500000000000000000000000) := Bounds.mul h29 (ch_bounds ha) (by norm_num)
  let v158 : ℝ := 1/kap1 (2*n)
  have h158 : Bounds v158 (20253615776756545462278653/10000000000000000000000000) (5063503421814342393696303/2500000000000000000000000) := Bounds.inv (kernel_window ha) (by norm_num)
  let v159 : ℝ := v157/kap1 (2*n)
  have h159 : Bounds v159 (573904154877168457375865699/100000000000000000000000000) (57428192008169058681739609/10000000000000000000000000) := bounds_div h157 h158 (by norm_num)
  let v160 : ℝ := v159+BstLean.Part210.Rnew n
  have h160 : Bounds v160 (573904154877168457375865699/100000000000000000000000000) (57520192008169058681739609/10000000000000000000000000) := Bounds.add h159 (calibration_bound ha) (by norm_num)
  let v161 : ℝ := Real.sqrt v0
  have h161 : Bounds v161 (126984250992002941372375567/500000000000000000000000000) (50793700396801176548950227/200000000000000000000000000) := Bounds.sqrt h0 (by norm_num)
  let v162 : ℝ := v29*v161
  have h162 : Bounds v162 (6355561762149747215687397/25000000000000000000000000) (254222470485989888627495887/1000000000000000000000000000) := Bounds.mul h29 h161 (by norm_num)
  let v163 : ℝ := 1/kap1 (2*n)
  have h163 : Bounds v163 (20253615776756545462278653/10000000000000000000000000) (5063503421814342393696303/2500000000000000000000000) := Bounds.inv (kernel_window ha) (by norm_num)
  let v164 : ℝ := v162/kap1 (2*n)
  have h164 : Bounds v164 (51489242390410700517377779/100000000000000000000000000) (51490253968316218751347327/100000000000000000000000000) := bounds_div h162 h163 (by norm_num)
  let v165 : ℝ := (arW n)+v15
  have h165 : Bounds v165 1 (25000011682589932706943487/25000000000000000000000000) := Bounds.add (arw_bounds ha) h15 (by norm_num)
  let v166 : ℝ := Real.sqrt v165
  have h166 : Bounds v166 1 (3125000730161785492386689/3125000000000000000000000) := Bounds.sqrt h165 (by norm_num)
  let v167 : ℝ := v164*v166
  have h167 : Bounds v167 (51489242390410700517377779/100000000000000000000000000) (25745132999552633049628767/50000000000000000000000000) := Bounds.mul h164 h166 (by norm_num)
  let v168 : ℝ := v160+v167
  have h168 : Bounds v168 (62539339726757915789324347/10000000000000000000000000) (78336523260099481614581703/12500000000000000000000000) := Bounds.add h160 h167 (by norm_num)
  convert h168 using 1 <;>
    simp only [v0, v15, v29, v157, v159, v160, v161, v162, v164, v165, v166, v167, v168, BstLean.Part271.R3.lxCore, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_main_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldMomentMain n) (15504955557859495431865813/100000000000000000000000) (9722822099995806543661509/62500000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v102 : ℝ := (101139/50000)
  have h102 : Bounds v102 (101139/50000) (101139/50000) := Bounds.point _
  let v103 : ℝ := (101399/50000)
  have h103 : Bounds v103 (101399/50000) (101399/50000) := Bounds.point _
  let v104 : ℝ := (11/500)
  have h104 : Bounds v104 (11/500) (11/500) := Bounds.point _
  let v169 : ℝ := v103*v104
  have h169 : Bounds v169 (1115389/25000000) (1115389/25000000) := Bounds.mul h103 h104 (by norm_num)
  let v170 : ℝ := 3
  have h170 : Bounds v170 3 3 := Bounds.point _
  let v171 : ℝ := v104+v170
  have h171 : Bounds v171 (1511/500) (1511/500) := Bounds.add h104 h170 (by norm_num)
  let v172 : ℝ := v169*v171
  have h172 : Bounds v172 (1685352779/12500000000) (1685352779/12500000000) := Bounds.mul h169 h171 (by norm_num)
  let v173 : ℝ := -v104
  have h173 : Bounds v173 (-11/500) (-11/500) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h104
  let v174 : ℝ := v15+v173
  have h174 : Bounds v174 (489/500) (489/500) := Bounds.add h15 h173 (by norm_num)
  let v175 : ℝ := v174^2
  have h175 : Bounds v175 (239121/250000) (239121/250000) := Bounds.pow h174 2 (by norm_num)
  let v176 : ℝ := 1/v175
  have h176 : Bounds v176 (52274789750795622300007109/50000000000000000000000000) (104549579501591244600014219/100000000000000000000000000) := Bounds.inv h175 (by norm_num)
  let v177 : ℝ := v172/v175
  have h177 : Bounds v177 (35240584871257647801740541/250000000000000000000000000) (70481169742515295603481083/500000000000000000000000000) := bounds_div h172 h176 (by norm_num)
  let v178 : ℝ := -v15
  have h178 : Bounds v178 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h15
  let v179 : ℝ := v102+v178
  have h179 : Bounds v179 (51139/50000) (51139/50000) := Bounds.add h102 h178 (by norm_num)
  let v180 : ℝ := 1/v179
  have h180 : Bounds v180 (195545474100001955454741/200000000000000000000000) (97772737050000977727370501/100000000000000000000000000) := Bounds.inv h179 (by norm_num)
  let v181 : ℝ := v177/v179
  have h181 : Bounds v181 (6891136876211433114010939/50000000000000000000000000) (4306960547632145696256837/31250000000000000000000000) := bounds_div h177 h180 (by norm_num)
  let v182 : ℝ := -v181
  have h182 : Bounds v182 (-4306960547632145696256837/31250000000000000000000000) (-6891136876211433114010939/50000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h181
  let v183 : ℝ := v15+v182
  have h183 : Bounds v183 (86217726247577133771978121/100000000000000000000000000) (43108863123788566885989061/50000000000000000000000000) := Bounds.add h15 h182 (by norm_num)
  let v184 : ℝ := Real.sqrt v183
  have h184 : Bounds v184 (928535008750758593453130603/1000000000000000000000000000) (92853500875075859345313061/100000000000000000000000000) := Bounds.sqrt h183 (by norm_num)
  let v185 : ℝ := v184+v15
  have h185 : Bounds v185 (9642675043753792967265653/5000000000000000000000000) (192853500875075859345313061/100000000000000000000000000) := Bounds.add h184 h15 (by norm_num)
  let v186 : ℝ := v185^2
  have h186 : Bounds v186 (4649059099971610655782553/1250000000000000000000000) (74384945599545770492520849/20000000000000000000000000) := Bounds.pow h185 2 (by norm_num)
  let v187 : ℝ := v183+v15
  have h187 : Bounds v187 (186217726247577133771978121/100000000000000000000000000) (93108863123788566885989061/50000000000000000000000000) := Bounds.add h183 h15 (by norm_num)
  let v188 : ℝ := v186*v187
  have h188 : Bounds v188 (34629488591492829103387977/5000000000000000000000000) (346294885914928291033879777/50000000000000000000000000) := Bounds.mul h186 h187 (by norm_num)
  let v189 : ℝ := -v104
  have h189 : Bounds v189 (-11/500) (-11/500) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h104
  let v190 : ℝ := v15+v189
  have h190 : Bounds v190 (489/500) (489/500) := Bounds.add h15 h189 (by norm_num)
  let v191 : ℝ := v190^2
  have h191 : Bounds v191 (239121/250000) (239121/250000) := Bounds.pow h190 2 (by norm_num)
  let v192 : ℝ := 1/v191
  have h192 : Bounds v192 (52274789750795622300007109/50000000000000000000000000) (104549579501591244600014219/100000000000000000000000000) := Bounds.inv h191 (by norm_num)
  let v193 : ℝ := v103/v191
  have h193 : Bounds v193 (212024456237637012223936833/100000000000000000000000000) (5300611405940925305598421/2500000000000000000000000) := bounds_div h103 h192 (by norm_num)
  let v194 : ℝ := v104+v3
  have h194 : Bounds v194 (1011/500) (1011/500) := Bounds.add h104 h3 (by norm_num)
  let v195 : ℝ := v194*(BstLean.Part271.R3.lxCore n)
  have h195 : Bounds v195 (126454544927504505726013829/10000000000000000000000000) (126717160025536921459747363/10000000000000000000000000) := Bounds.mul h194 (lx_bounds ha) (by norm_num)
  let v196 : ℝ := (BstLean.Part271.R3.arCore n)+v195
  have h196 : Bounds v196 (39519330382297074761500691/2500000000000000000000000) (15833993662722157797343529/1000000000000000000000000) := Bounds.add (ar_bounds ha) h195 (by norm_num)
  let v197 : ℝ := v193*v196
  have h197 : Bounds v197 (335162581407282596153529679/10000000000000000000000000) (167859694820442796585498193/5000000000000000000000000) := Bounds.mul h193 h196 (by norm_num)
  let v198 : ℝ := v197^2
  have h198 : Bounds v198 (14041744496949166676534309/12500000000000000000000) (56353754290424380463636651/50000000000000000000000) := Bounds.pow h197 2 (by norm_num)
  let v199 : ℝ := -v15
  have h199 : Bounds v199 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h15
  let v200 : ℝ := v102+v199
  have h200 : Bounds v200 (51139/50000) (51139/50000) := Bounds.add h102 h199 (by norm_num)
  let v201 : ℝ := v200^2
  have h201 : Bounds v201 (2615197321/2500000000) (2615197321/2500000000) := Bounds.pow h200 2 (by norm_num)
  let v202 : ℝ := v201*v188
  have h202 : Bounds v202 (144900713267315376099025711/20000000000000000000000000) (724503566336576880495128571/100000000000000000000000000) := Bounds.mul h201 h188 (by norm_num)
  let v203 : ℝ := 1/v202
  have h203 : Bounds v203 (3450638638869853141914319/25000000000000000000000000) (138025545554794125676572771/1000000000000000000000000000) := Bounds.inv h202 (by norm_num)
  let v204 : ℝ := v198/v202
  have h204 : Bounds v204 (15504955557859495431865813/100000000000000000000000) (9722822099995806543661509/62500000000000000000000) := bounds_div h198 h203 (by norm_num)
  convert h204 using 1 <;>
    simp only [v3, v15, v102, v103, v104, v169, v170, v171, v172, v173, v174, v175, v177, v178, v179, v181, v182, v183, v184, v185, v186, v187, v188, v189, v190, v191, v193, v194, v195, v196, v197, v198, v199, v200, v201, v202, v204, worldMomentMain, cRhoG, rLowG, zetaG, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_residual_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldMomentResidual n) (4058817366494909802595937/20000000000000000000) (25451606203240305510897401/125000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v104 : ℝ := (11/500)
  have h104 : Bounds v104 (11/500) (11/500) := Bounds.point _
  let v205 : ℝ := (BstLean.Part271.R3.arCore n)^2
  have h205 : Bounds v205 (99999999999999999999999999/10000000000000000000000000) (100000000000005459316301433/10000000000000000000000000) := Bounds.pow (ar_bounds ha) 2 (by norm_num)
  let v206 : ℝ := (BstLean.Part271.R3.lxCore n)^2
  have h206 : Bounds v206 (391116901345884086114108399/10000000000000000000000000) (392743096094726855374672241/10000000000000000000000000) := Bounds.pow (lx_bounds ha) 2 (by norm_num)
  let v207 : ℝ := v205+v206
  have h207 : Bounds v207 (49111690134588408611410839/1000000000000000000000000) (6159288701184153933637171/125000000000000000000000) := Bounds.add h205 h206 (by norm_num)
  let v208 : ℝ := v207*v3
  have h208 : Bounds v208 (49111690134588408611410839/500000000000000000000000) (6159288701184153933637171/62500000000000000000000) := Bounds.mul h207 h3 (by norm_num)
  let v209 : ℝ := v104^2
  have h209 : Bounds v209 (121/250000) (121/250000) := Bounds.pow h104 2 (by norm_num)
  let v210 : ℝ := 1/v209
  have h210 : Bounds v210 (206611570247933884297520661/100000000000000000000000) (103305785123966942148760331/50000000000000000000000) := Bounds.inv h209 (by norm_num)
  let v211 : ℝ := v208/v209
  have h211 : Bounds v211 (4058817366494909802595937/20000000000000000000) (25451606203240305510897401/125000000000000000000) := bounds_div h208 h210 (by norm_num)
  convert h211 using 1 <;>
    simp only [v3, v104, v205, v206, v207, v208, v209, v211, worldMomentResidual, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (momentValue n (202278/100000) (202798/100000) (22/1000)) 0 (316232879240226007325933511/10000000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v212 : ℝ := 1/v3
  have h212 : Bounds v212 (1/2) (1/2) := Bounds.inv h3 (by norm_num)
  let v213 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))/v3
  have h213 : Bounds v213 0 (17469812164579606440071557/100000000000000000000000000000000000) := bounds_div (dimension_width ha) h212 (by norm_num)
  let v214 : ℝ := v213*(worldMomentMain n)
  have h214 : Bounds v214 0 (13588470063724014064822101/500000000000000000000000000000000) := Bounds.mul h213 (moment_main_bounds ha) (by norm_num)
  let v215 : ℝ := (1/(mW n : ℝ))*(worldMomentResidual n)
  have h215 : Bounds v215 0 (44463477965745726029491491/10000000000000000000000000000000000) := Bounds.mul (inverse_width ha) (moment_residual_bounds ha) (by norm_num)
  let v216 : ℝ := v214+v215
  have h216 : Bounds v216 0 (316232879240226007325933511/10000000000000000000000000000000000) := Bounds.add h214 h215 (by norm_num)
  convert h216 using 1 <;>
    simp only [v3, v213, v214, v215, v216, world_moment_scale (width_positive ha), Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem hidden_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (groupedCharge n (4/100) (4/10000) (25/10^7) (1232/10^7) (805/10^9)) (155041/200000000) (27286309653098018053375197/25000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v6 : ℝ := (77/625000)
  have h6 : Bounds v6 (77/625000) (77/625000) := Bounds.point _
  let v72 : ℝ := (1/400000)
  have h72 : Bounds v72 (1/400000) (1/400000) := Bounds.point _
  let v217 : ℝ := (93/250)
  have h217 : Bounds v217 (93/250) (93/250) := Bounds.point _
  let v218 : ℝ := (1/25)
  have h218 : Bounds v218 (1/25) (1/25) := Bounds.point _
  let v219 : ℝ := v218^2
  have h219 : Bounds v219 (1/625) (1/625) := Bounds.pow h218 2 (by norm_num)
  let v220 : ℝ := v217*v219
  have h220 : Bounds v220 (93/156250) (93/156250) := Bounds.mul h217 h219 (by norm_num)
  let v221 : ℝ := (56/125)
  have h221 : Bounds v221 (56/125) (56/125) := Bounds.point _
  let v222 : ℝ := (1/2500)
  have h222 : Bounds v222 (1/2500) (1/2500) := Bounds.point _
  let v223 : ℝ := v221*v222
  have h223 : Bounds v223 (14/78125) (14/78125) := Bounds.mul h221 h222 (by norm_num)
  let v224 : ℝ := v220+v223
  have h224 : Bounds v224 (121/156250) (121/156250) := Bounds.add h220 h223 (by norm_num)
  let v225 : ℝ := (161/200000000)
  have h225 : Bounds v225 (161/200000000) (161/200000000) := Bounds.point _
  let v226 : ℝ := v224+v225
  have h226 : Bounds v226 (155041/200000000) (155041/200000000) := Bounds.add h224 h225 (by norm_num)
  let v227 : ℝ := (893/200)
  have h227 : Bounds v227 (893/200) (893/200) := Bounds.point _
  let v228 : ℝ := 1/v3
  have h228 : Bounds v228 (1/2) (1/2) := Bounds.inv h3 (by norm_num)
  let v229 : ℝ := (((2*n : ℕ) : ℝ)/(mW n : ℝ))/v3
  have h229 : Bounds v229 0 (17469812164579606440071557/100000000000000000000000000000000000) := bounds_div (dimension_width ha) h228 (by norm_num)
  let v230 : ℝ := v227*v229
  have h230 : Bounds v230 0 (78002711314847942754919503/100000000000000000000000000000000000) := Bounds.mul h227 h229 (by norm_num)
  let v231 : ℝ := 1/v72
  have h231 : Bounds v231 400000 400000 := Bounds.inv h72 (by norm_num)
  let v232 : ℝ := v230/v72
  have h232 : Bounds v232 0 (78002711314847942754919503/250000000000000000000000000000) := bounds_div h230 h231 (by norm_num)
  let v233 : ℝ := v226+v232
  have h233 : Bounds v233 (155041/200000000) (54360792262969588550983901/50000000000000000000000000000) := Bounds.add h226 h232 (by norm_num)
  let v234 : ℝ := (429/250)
  have h234 : Bounds v234 (429/250) (429/250) := Bounds.point _
  let v235 : ℝ := v234^2
  have h235 : Bounds v235 (184041/62500) (184041/62500) := Bounds.pow h234 2 (by norm_num)
  let v236 : ℝ := v235*(1/(mW n : ℝ))
  have h236 : Bounds v236 0 (64303234011627906976744187/1000000000000000000000000000000000000000) := Bounds.mul h235 (inverse_width ha) (by norm_num)
  let v237 : ℝ := v6^2
  have h237 : Bounds v237 (5929/390625000000) (5929/390625000000) := Bounds.pow h6 2 (by norm_num)
  let v238 : ℝ := 1/v237
  have h238 : Bounds v238 (65883791533142182492831843/1000000000000000000) (16470947883285545623207961/250000000000000000) := Bounds.inv h237 (by norm_num)
  let v239 : ℝ := v236/v237
  have h239 : Bounds v239 0 (4236540864528951115329853/1000000000000000000000000000000) := bounds_div h236 h238 (by norm_num)
  let v240 : ℝ := v233+v239
  have h240 : Bounds v240 (155041/200000000) (27286309653098018053375197/25000000000000000000000000000) := Bounds.add h233 h239 (by norm_num)
  convert h240 using 1 <;>
    simp only [v3, v6, v72, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v229, v230, v232, v233, v234, v235, v236, v237, v239, v240, grouped_charge_scaled (n_positive ha), Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

end BstLean.Part290
