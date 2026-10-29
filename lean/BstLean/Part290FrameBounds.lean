import BstLean.Part290WorldBounds

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part140 BstLean.Part159 BstLean.Part233
open BstLean.Part228 BstLean.Part250
open BstLean.Part271.R3 (angularMomentCore angularMomentCore_formula j2Core j4Core
  jbCore aCore bCore offsetCore ba1Core ba2Core traceCore diagonalCore covariancePaymentCore normCore)
theorem k0_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldK0 n) 0 (279445988297686679793203003/50000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v47 : ℝ := (447/20)
  have h47 : Bounds v47 (447/20) (447/20) := Bounds.point _
  let v48 : ℝ := v47*worldR0 n
  have h48 : Bounds v48 0 (78090060375670840787119857/2500000000000000000000000000000) := Bounds.mul h47 (worldR0_bounds ha) (by norm_num)
  let v49 : ℝ := Real.sqrt v48
  have h49 : Bounds v49 0 (279445988297686679793203003/50000000000000000000000000000) := Bounds.sqrt h48 (by norm_num)
  convert h49 using 1 <;>
    simp only [v47, v48, v49, worldK0, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem k6_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldK6 n) 0 (30618621784789726227466051/2000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v50 : ℝ := (15/8)
  have h50 : Bounds v50 (15/8) (15/8) := Bounds.point _
  let v51 : ℝ := v50*(1/(n : ℝ))
  have h51 : Bounds v51 0 (3/12800) := Bounds.mul h50 (inverse_n ha) (by norm_num)
  let v52 : ℝ := Real.sqrt v51
  have h52 : Bounds v52 0 (30618621784789726227466051/2000000000000000000000000000) := Bounds.sqrt h51 (by norm_num)
  convert h52 using 1 <;>
    simp only [v50, v51, v52, worldK6, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem coeffK_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldAK n) 0 (7616008924880125181885161/625000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v53 : ℝ := (1/1000000000)
  have h53 : Bounds v53 (1/1000000000) (1/1000000000) := Bounds.point _
  let v54 : ℝ := v53+v15
  have h54 : Bounds v54 (1000000001/1000000000) (1000000001/1000000000) := Bounds.add h53 h15 (by norm_num)
  let v55 : ℝ := v54*(worldK0 n)
  have h55 : Bounds v55 0 (55889197715426533618177937/10000000000000000000000000000) := Bounds.mul h54 (k0_bounds ha) (by norm_num)
  let v56 : ℝ := 1/(worldS n)
  have h56 : Bounds v56 (10901338997405846627225299/5000000000000000000000000) (10901582754733950702132923/5000000000000000000000000) := Bounds.inv (denominator_bounds ha) (by norm_num)
  let v57 : ℝ := v55/(worldS n)
  have h57 : Bounds v57 0 (7616008924880125181885161/625000000000000000000000000) := bounds_div h55 h56 (by norm_num)
  convert h57 using 1 <;>
    simp only [v15, v53, v54, v55, v57, worldAK, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem coeffD_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldAD n) 0 (786072380681073532841738383/100000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v14 : ℝ := (22287/1000000)
  have h14 : Bounds v14 (22287/1000000) (22287/1000000) := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v47 : ℝ := (447/20)
  have h47 : Bounds v47 (447/20) (447/20) := Bounds.point _
  let v53 : ℝ := (1/1000000000)
  have h53 : Bounds v53 (1/1000000000) (1/1000000000) := Bounds.point _
  let v58 : ℝ := v53+v15
  have h58 : Bounds v58 (1000000001/1000000000) (1000000001/1000000000) := Bounds.add h53 h15 (by norm_num)
  let v59 : ℝ := v58*v47
  have h59 : Bounds v59 (447000000447/20000000000) (447000000447/20000000000) := Bounds.mul h58 h47 (by norm_num)
  let v60 : ℝ := v59*worldR0 n
  have h60 : Bounds v60 0 (312360241815043604651162791/10000000000000000000000000000000) := Bounds.mul h59 (worldR0_bounds ha) (by norm_num)
  let v61 : ℝ := v60*(1/(n : ℝ))
  have h61 : Bounds v61 0 (39045030226880450581395349/10000000000000000000000000000000000) := Bounds.mul h60 (inverse_n ha) (by norm_num)
  let v62 : ℝ := v14^2
  have h62 : Bounds v62 (496710369/1000000000000) (496710369/1000000000000) := Bounds.pow h14 2 (by norm_num)
  let v63 : ℝ := 1/v62
  have h63 : Bounds v63 (78642409013209063892121/39062500000000000000) (20132456707381520356382977/10000000000000000000000) := Bounds.inv h62 (by norm_num)
  let v64 : ℝ := v61/v62
  have h64 : Bounds v64 0 (786072380681073532841738383/100000000000000000000000000000000) := bounds_div h61 h63 (by norm_num)
  convert h64 using 1 <;>
    simp only [v14, v15, v47, v53, v58, v59, v60, v61, v62, v64, worldAD, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem distance_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (centreDistance n (525/10000)) (26249999999999999999999999/1000000000000000000000000000) (262510877350513700737562207/10000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v65 : ℝ := (21/400)
  have h65 : Bounds v65 (21/400) (21/400) := Bounds.point _
  let v66 : ℝ := 1/v3
  have h66 : Bounds v66 (1/2) (1/2) := Bounds.inv h3 (by norm_num)
  let v67 : ℝ := v65/v3
  have h67 : Bounds v67 (21/800) (21/800) := bounds_div h65 h66 (by norm_num)
  let v68 : ℝ := Real.sqrt v67
  have h68 : Bounds v68 (32403703492039301154829837/200000000000000000000000000) (81009258730098252887074593/500000000000000000000000000) := Bounds.sqrt h67 (by norm_num)
  let v69 : ℝ := Real.sqrt ((n : ℝ)*perturbation n)
  have h69 : Bounds v69 0 (335678847205984162737594341/100000000000000000000000000000000) := Bounds.sqrt (nperturbation_bounds ha) (by norm_num)
  let v70 : ℝ := v68+v69
  have h70 : Bounds v70 (32403703492039301154829837/200000000000000000000000000) (81010937124334282807888281/500000000000000000000000000) := Bounds.add h68 h69 (by norm_num)
  let v71 : ℝ := v70^2
  have h71 : Bounds v71 (26249999999999999999999999/1000000000000000000000000000) (262510877350513700737562207/10000000000000000000000000000) := Bounds.pow h70 2 (by norm_num)
  convert h71 using 1 <;>
    simp only [v3, v65, v67, v68, v69, v70, v71, centreDistance, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem fluctuation_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (centreFluctuation n (25/10^7)) (249999999999999999999999999/100000000000000000000000000000000) (125751727523845961322818139/50000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v72 : ℝ := (1/400000)
  have h72 : Bounds v72 (1/400000) (1/400000) := Bounds.point _
  let v73 : ℝ := Real.sqrt v72
  have h73 : Bounds v73 (158113883008418966599944677/100000000000000000000000000000) (79056941504209483299972339/50000000000000000000000000000) := Bounds.sqrt h72 (by norm_num)
  let v74 : ℝ := ((n : ℝ)*perturbation n)*v3
  have h74 : Bounds v74 0 (5634014423076923076923077/250000000000000000000000000000000000) := Bounds.mul (nperturbation_bounds ha) h3 (by norm_num)
  let v75 : ℝ := Real.sqrt v74
  have h75 : Bounds v75 0 (5934019729005859079759153/1250000000000000000000000000000) := Bounds.sqrt h74 (by norm_num)
  let v76 : ℝ := v73+v75
  have h76 : Bounds v76 (158113883008418966599944677/100000000000000000000000000000) (158588604586739435326325411/100000000000000000000000000000) := Bounds.add h73 h75 (by norm_num)
  let v77 : ℝ := v76^2
  have h77 : Bounds v77 (249999999999999999999999999/100000000000000000000000000000000) (125751727523845961322818139/50000000000000000000000000000000) := Bounds.pow h76 2 (by norm_num)
  convert h77 using 1 <;>
    simp only [v3, v72, v73, v74, v75, v76, v77, centreFluctuation, mul_assoc, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem frame_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldC1 n) (40433851302556904879240119/100000000000000000000000000) (417818210524454651175660077/1000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v19 : ℝ := (99/8000)
  have h19 : Bounds v19 (99/8000) (99/8000) := Bounds.point _
  let v78 : ℝ := (3017/20000)
  have h78 : Bounds v78 (3017/20000) (3017/20000) := Bounds.point _
  let v79 : ℝ := (69/500)
  have h79 : Bounds v79 (69/500) (69/500) := Bounds.point _
  let v80 : ℝ := v79*(1/(n : ℝ))
  have h80 : Bounds v80 0 (69/4000000) := Bounds.mul h79 (inverse_n ha) (by norm_num)
  let v81 : ℝ := 1/v3
  have h81 : Bounds v81 (1/2) (1/2) := Bounds.inv h3 (by norm_num)
  let v82 : ℝ := v80/v3
  have h82 : Bounds v82 0 (69/8000000) := bounds_div h80 h81 (by norm_num)
  let v83 : ℝ := v78+v82
  have h83 : Bounds v83 (3017/20000) (1206869/8000000) := Bounds.add h78 h82 (by norm_num)
  let v84 : ℝ := (17321/20000000)
  have h84 : Bounds v84 (17321/20000000) (17321/20000000) := Bounds.point _
  let v85 : ℝ := v83+v84
  have h85 : Bounds v85 (3034321/20000000) (6068987/40000000) := Bounds.add h83 h84 (by norm_num)
  let v86 : ℝ := (2/5)
  have h86 : Bounds v86 (2/5) (2/5) := Bounds.point _
  let v87 : ℝ := v86*(worldK6 n)
  have h87 : Bounds v87 0 (30618621784789726227466051/5000000000000000000000000000) := Bounds.mul h86 (k6_bounds ha) (by norm_num)
  let v88 : ℝ := v85+v87
  have h88 : Bounds v88 (3034321/20000000) (157848399356957945245493211/1000000000000000000000000000) := Bounds.add h85 h87 (by norm_num)
  let v89 : ℝ := v88+(centreDistance n (525/10000))
  have h89 : Bounds v89 (177966049999999999999999999/1000000000000000000000000000) (23012435886501164414906179/125000000000000000000000000) := Bounds.add h88 (distance_bounds ha) (by norm_num)
  let v90 : ℝ := 1/(worldS n)
  have h90 : Bounds v90 (10901338997405846627225299/5000000000000000000000000) (10901582754733950702132923/5000000000000000000000000) := Bounds.inv (denominator_bounds ha) (by norm_num)
  let v91 : ℝ := v89/(worldS n)
  have h91 : Bounds v91 (19400682410792787711531089/50000000000000000000000000) (40139515872752286218103377/100000000000000000000000000) := bounds_div h89 h90 (by norm_num)
  let v92 : ℝ := v19^2
  have h92 : Bounds v92 (9801/64000000) (9801/64000000) := Bounds.pow h19 2 (by norm_num)
  let v93 : ℝ := 1/v92
  have h93 : Bounds v93 (65299459238853178247117641/10000000000000000000000) (32649729619426589123558821/5000000000000000000000) := Bounds.inv h92 (by norm_num)
  let v94 : ℝ := (centreFluctuation n (25/10^7))/v92
  have h94 : Bounds v94 (163248648097132945617794101/10000000000000000000000000000) (82115198056587506628510979/5000000000000000000000000000) := bounds_div (fluctuation_bounds ha) h93 (by norm_num)
  let v95 : ℝ := v91+v94
  have h95 : Bounds v95 (40433851302556904879240119/100000000000000000000000000) (41781819833884036350673597/100000000000000000000000000) := Bounds.add h91 h94 (by norm_num)
  let v96 : ℝ := (1/1000000)
  have h96 : Bounds v96 (1/1000000) (1/1000000) := Bounds.point _
  let v97 : ℝ := (worldAK n)*v96
  have h97 : Bounds v97 0 (7616008924880125181885161/625000000000000000000000000000000) := Bounds.mul (coeffK_bounds ha) h96 (by norm_num)
  let v98 : ℝ := v95+v97
  have h98 : Bounds v98 (40433851302556904879240119/100000000000000000000000000) (41781821052445464331493627/100000000000000000000000000) := Bounds.add h95 h97 (by norm_num)
  let v99 : ℝ := (1/1000000000000)
  have h99 : Bounds v99 (1/1000000000000) (1/1000000000000) := Bounds.point _
  let v100 : ℝ := (worldAD n)*v99
  have h100 : Bounds v100 0 (786072380681073532841738383/100000000000000000000000000000000000000000000) := Bounds.mul (coeffD_bounds ha) h99 (by norm_num)
  let v101 : ℝ := v98+v100
  have h101 : Bounds v101 (40433851302556904879240119/100000000000000000000000000) (417818210524454651175660077/1000000000000000000000000000) := Bounds.add h98 h100 (by norm_num)
  convert h101 using 1 <;>
    simp only [v3, v19, v78, v79, v80, v82, v83, v84, v85, v86, v87, v88, v89, v91, v92, v94, v95, v96, v97, v98, v99, v100, v101, worldC1, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem noise_lower_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (noiseLower (202278/100000)) (472209790678201246940986509/1000000000000000000000000000) (47220979067820124694098653/100000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v102 : ℝ := (101139/50000)
  have h102 : Bounds v102 (101139/50000) (101139/50000) := Bounds.point _
  let v105 : ℝ := -v15
  have h105 : Bounds v105 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h15
  let v106 : ℝ := v102+v105
  have h106 : Bounds v106 (51139/50000) (51139/50000) := Bounds.add h102 h105 (by norm_num)
  let v107 : ℝ := (9/2000)
  have h107 : Bounds v107 (9/2000) (9/2000) := Bounds.point _
  let v108 : ℝ := Real.sqrt v107
  have h108 : Bounds v108 (6708203932499369089227521/100000000000000000000000000) (670820393249936908922752101/10000000000000000000000000000) := Bounds.sqrt h107 (by norm_num)
  let v109 : ℝ := v108*v3
  have h109 : Bounds v109 (6708203932499369089227521/50000000000000000000000000) (134164078649987381784550421/1000000000000000000000000000) := Bounds.mul h108 h3 (by norm_num)
  let v110 : ℝ := v109+v15
  have h110 : Bounds v110 (56708203932499369089227521/50000000000000000000000000) (113416407864998738178455043/100000000000000000000000000) := Bounds.add h109 h15 (by norm_num)
  let v111 : ℝ := (9/1000)
  have h111 : Bounds v111 (9/1000) (9/1000) := Bounds.point _
  let v112 : ℝ := v110+v111
  have h112 : Bounds v112 (57158203932499369089227521/50000000000000000000000000) (114316407864998738178455043/100000000000000000000000000) := Bounds.add h110 h111 (by norm_num)
  let v113 : ℝ := -v15
  have h113 : Bounds v113 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h15
  let v114 : ℝ := v102+v113
  have h114 : Bounds v114 (51139/50000) (51139/50000) := Bounds.add h102 h113 (by norm_num)
  let v115 : ℝ := v112+v114
  have h115 : Bounds v115 (84607190572265132100959/39062500000000000000000) (216594407864998738178455043/100000000000000000000000000) := Bounds.add h112 h114 (by norm_num)
  let v116 : ℝ := 1/v115
  have h116 : Bounds v116 (9233848739283154675316031/20000000000000000000000000) (46169243696415773376580157/100000000000000000000000000) := Bounds.inv h115 (by norm_num)
  let v117 : ℝ := v106/v115
  have h117 : Bounds v117 (472209790678201246940986509/1000000000000000000000000000) (47220979067820124694098653/100000000000000000000000000) := bounds_div h106 h116 (by norm_num)
  convert h117 using 1 <;>
    simp only [v3, v15, v102, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v117, noiseLower, BstLean.Part159.cUp, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem noise_upper_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (noiseUpper n (202798/100000)) (12672462253079418929180761/25000000000000000000000000) (527028599788518074693809941/1000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v103 : ℝ := (101399/50000)
  have h103 : Bounds v103 (101399/50000) (101399/50000) := Bounds.point _
  let v118 : ℝ := -v15
  have h118 : Bounds v118 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h15
  let v119 : ℝ := v103+v118
  have h119 : Bounds v119 (51399/50000) (51399/50000) := Bounds.add h103 h118 (by norm_num)
  let v120 : ℝ := 12
  have h120 : Bounds v120 12 12 := Bounds.point _
  let v121 : ℝ := (1/(n : ℝ))*v120
  have h121 : Bounds v121 0 (3/2000) := Bounds.mul (inverse_n ha) h120 (by norm_num)
  let v122 : ℝ := Real.sqrt v121
  have h122 : Bounds v122 0 (19364916731037084425896327/500000000000000000000000000) := Bounds.sqrt h121 (by norm_num)
  let v123 : ℝ := v122*v3
  have h123 : Bounds v123 0 (19364916731037084425896327/250000000000000000000000000) := Bounds.mul h122 h3 (by norm_num)
  let v124 : ℝ := -v123
  have h124 : Bounds v124 (-19364916731037084425896327/250000000000000000000000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h123
  let v125 : ℝ := v15+v124
  have h125 : Bounds v125 (92254033307585166229641469/100000000000000000000000000) 1 := Bounds.add h15 h124 (by norm_num)
  let v126 : ℝ := -v15
  have h126 : Bounds v126 (-1) (-1) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h15
  let v127 : ℝ := v103+v126
  have h127 : Bounds v127 (51399/50000) (51399/50000) := Bounds.add h103 h126 (by norm_num)
  let v128 : ℝ := v125+v127
  have h128 : Bounds v128 (195052033307585166229641469/100000000000000000000000000) (101399/50000) := Bounds.add h125 h127 (by norm_num)
  let v129 : ℝ := 1/v128
  have h129 : Bounds v129 (493101509876823242832769553/1000000000000000000000000000) (10253674191881516657791201/20000000000000000000000000) := Bounds.inv h128 (by norm_num)
  let v130 : ℝ := v119/v128
  have h130 : Bounds v130 (12672462253079418929180761/25000000000000000000000000) (527028599788518074693809941/1000000000000000000000000000) := bounds_div h119 h129 (by norm_num)
  convert h130 using 1 <;>
    simp only [v3, v15, v103, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v130, noiseUpper, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

end BstLean.Part290
