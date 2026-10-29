import BstLean.Part271R4SourceA13225Moments
import BstLean.Part253GroupBounds
import BstLean.Part264HS

/-! Full-centre and parallel formulas shared by dimensions 13225 through 16199. -/
namespace BstLean.Part271.R4.A13225
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211
open BstLean.Part228 BstLean.Part250 BstLean.Part271.R4
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

theorem source_finite {n : ℕ} (ha : 13225 ≤ n) :
    finiteEnergy n n (11/1000) ≤ (8307107689/1000000000000) := by
  have h := BstLean.Part277.finite_centre_upperP (n0 := 13225) (by norm_num) ha
    (r := 115) (w := (1035085066163/1000000000000)) (d := (524008979/1000000000000))
    (s1 := (1421979478597/1000000000000)) (s2 := (325298400031/200000000000)) (s3 := (878678309029/1000000000000))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.trans (by norm_num)

theorem source_finite_decimal {n : ℕ} (ha : 13225 ≤ n) :
    finiteEnergy n n 0.011 ≤ (8307107689/1000000000000) := by
  convert source_finite ha using 1 <;> norm_num

theorem source_deviation {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) (Θ : ℝ) (hw : Bounds Θ 0 0.525) :
    Bounds (sharpDeviation n csC 0.011 0.46 Θ) (367741039013598417875329/8000000000000000000000000) (401722284946192717488989/7812500000000000000000000) := by
  let v0 : ℝ := 24
  have h0 : Bounds v0 24 24 := Bounds.point _
  let v1 : ℝ := Real.sqrt v0
  have h1 : Bounds v1 (244948974278317809819728407/50000000000000000000000000) (97979589711327123927891363/20000000000000000000000000) := Bounds.sqrt h0 (by norm_num)
  let v2 : ℝ := (23/50)
  have h2 : Bounds v2 (23/50) (23/50) := Bounds.point _
  let v3 : ℝ := csC*v2
  have h3 : Bounds v3 (2978983/5000000) (7447469/12500000) := Bounds.mul source_cs h2 (by norm_num)
  let v4 : ℝ := 2
  have h4 : Bounds v4 2 2 := Bounds.point _
  let v5 : ℝ := 1/v4
  have h5 : Bounds v5 (1/2) (1/2) := Bounds.inv h4 (by norm_num)
  let v6 : ℝ := v3/v4
  have h6 : Bounds v6 (2978983/10000000) (7447469/25000000) := bounds_div h3 h5 (by norm_num)
  let v7 : ℝ := (1011/1000)
  have h7 : Bounds v7 (1011/1000) (1011/1000) := Bounds.point _
  let v8 : ℝ := -v6
  have h8 : Bounds v8 (-7447469/25000000) (-2978983/10000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h6
  let v9 : ℝ := v7+v8
  have h9 : Bounds v9 (17827531/25000000) (7131017/10000000) := Bounds.add h7 h8 (by norm_num)
  let v10 : ℝ := v9*v4
  have h10 : Bounds v10 (17827531/12500000) (7131017/5000000) := Bounds.mul h9 h4 (by norm_num)
  let v11 : ℝ := 1/(n : ℝ)
  have h11 : Bounds v11 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.inv (source_dimension ha hb) (by norm_num)
  let v12 : ℝ := v10/(n : ℝ)
  have h12 : Bounds v12 (44021312426693005741095129/500000000000000000000000000000) (13480183364839319470699433/125000000000000000000000000000) := bounds_div h10 h11 (by norm_num)
  let v13 : ℝ := Real.sqrt v12
  have h13 : Bounds v13 (46915515784595721388375577/5000000000000000000000000000) (51923373089273234292484969/5000000000000000000000000000) := Bounds.sqrt h12 (by norm_num)
  let v14 : ℝ := (wn n)*Θ
  have h14 : Bounds v14 0 (21736786389423/40000000000000) := Bounds.mul (show Bounds (wn n) (128959358361/125000000000) (1035085066163/1000000000000) from ⟨le_trans (by norm_num) (source_wn ha hb).1, (source_wn ha hb).2.trans (by norm_num)⟩) hw (by norm_num)
  let v15 : ℝ := Real.sqrt v14
  have h15 : Bounds v15 0 (73717003448022424346767783/100000000000000000000000000) := Bounds.sqrt h14 (by norm_num)
  let v16 : ℝ := v15*v4
  have h16 : Bounds v16 0 (73717003448022424346767783/50000000000000000000000000) := Bounds.mul h15 h4 (by norm_num)
  let v17 : ℝ := 1/(n : ℝ)
  have h17 : Bounds v17 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.inv (source_dimension ha hb) (by norm_num)
  let v18 : ℝ := v16/(n : ℝ)
  have h18 : Bounds v18 0 (111481290658635046271104399/1000000000000000000000000000000) := bounds_div h16 h17 (by norm_num)
  let v19 : ℝ := v13+v18
  have h19 : Bounds v19 (46915515784595721388375577/5000000000000000000000000000) (52480779542566409523840491/5000000000000000000000000000) := Bounds.add h13 h18 (by norm_num)
  let v20 : ℝ := v1*v19
  have h20 : Bounds v20 (367741039013598417875329/8000000000000000000000000) (401722284946192717488989/7812500000000000000000000) := Bounds.mul h1 h19 (by norm_num)
  convert h20 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v6, v7, v8, v9, v10, v12, v13, v14, v15, v16, v18, v19, v20, sharpDeviation] <;> ring

theorem source_n22 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (N22bar n 12) (113178140162286606988245993/100000000000000000000000000000) (69319065415697146439673359/50000000000000000000000000000) := by
  let v0 : ℝ := 5
  have h0 : Bounds v0 5 5 := Bounds.point _
  let v1 : ℝ := Real.sqrt v0
  have h1 : Bounds v1 (111803398874989484820458683/50000000000000000000000000) (223606797749978969640917367/100000000000000000000000000) := Bounds.sqrt h0 (by norm_num)
  let v2 : ℝ := 12
  have h2 : Bounds v2 12 12 := Bounds.point _
  let v3 : ℝ := Real.sqrt v2
  have h3 : Bounds v3 (86602540378443864676372317/25000000000000000000000000) (346410161513775458705489269/100000000000000000000000000) := Bounds.sqrt h2 (by norm_num)
  let v4 : ℝ := 2
  have h4 : Bounds v4 2 2 := Bounds.point _
  let v5 : ℝ := v3*v4
  have h5 : Bounds v5 (86602540378443864676372317/12500000000000000000000000) (34641016151377545870548927/5000000000000000000000000) := Bounds.mul h3 h4 (by norm_num)
  let v6 : ℝ := v1+v5
  have h6 : Bounds v6 (9164271207775298870518959/1000000000000000000000000) (916427120777529887051895907/100000000000000000000000000) := Bounds.add h1 h5 (by norm_num)
  let v7 : ℝ := 1/(n : ℝ)
  have h7 : Bounds v7 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.inv (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := v6/(n : ℝ)
  have h8 : Bounds v8 (56573067521299455957274887/100000000000000000000000000000) (866188204893695545417671/1250000000000000000000000000) := bounds_div h6 h7 (by norm_num)
  let v9 : ℝ := v8+v4
  have h9 : Bounds v9 (100028286533760649727978637/50000000000000000000000000) (100034647528195747821816707/50000000000000000000000000) := Bounds.add h8 h4 (by norm_num)
  let v10 : ℝ := v8*v9
  have h10 : Bounds v10 (113178140162286606988245993/100000000000000000000000000000) (69319065415697146439673359/50000000000000000000000000000) := Bounds.mul h8 h9 (by norm_num)
  convert h10 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v8, v9, v10, N22bar, N12bar] <;> ring

theorem source_plow {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (plow n 0.011) (896842284802691008936223/1600000000000000000000000) (5606276846714626362412483/10000000000000000000000000) := by
  let v0 : ℝ := (989/1000)
  have h0 : Bounds v0 (989/1000) (989/1000) := Bounds.point _
  let v1 : ℝ := 1/π
  have h1 : Bounds v1 (15915494309189533576851107/50000000000000000000000000) (159154943091895335769017679/500000000000000000000000000) := Bounds.inv pi_bounds (by norm_num)
  let v2 : ℝ := v0/π
  have h2 : Bounds v2 (31480847743576897415011489/100000000000000000000000000) (31480847743576897415111697/100000000000000000000000000) := bounds_div h0 h1 (by norm_num)
  let v3 : ℝ := Real.sqrt v2
  have h3 : Bounds v3 (561077960212098309925709073/1000000000000000000000000000) (561077960212098309926602069/1000000000000000000000000000) := Bounds.sqrt h2 (by norm_num)
  let v4 : ℝ := 13
  have h4 : Bounds v4 13 13 := Bounds.point _
  let v5 : ℝ := 1/(n : ℝ)
  have h5 : Bounds v5 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.inv (source_dimension ha hb) (by norm_num)
  let v6 : ℝ := v4/(n : ℝ)
  have h6 : Bounds v6 (80251867399222174208284461/100000000000000000000000000000) (49149338374291115311909263/50000000000000000000000000000) := bounds_div h4 h5 (by norm_num)
  let v7 : ℝ := 1
  have h7 : Bounds v7 1 1 := Bounds.point _
  let v8 : ℝ := -v6
  have h8 : Bounds v8 (-49149338374291115311909263/50000000000000000000000000000) (-80251867399222174208284461/100000000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h6
  let v9 : ℝ := v7+v8
  have h9 : Bounds v9 (99901701323251417769376181/100000000000000000000000000) (249799370331501944564479289/250000000000000000000000000) := Bounds.add h7 h8 (by norm_num)
  let v10 : ℝ := v3*v9
  have h10 : Bounds v10 (896842284802691008936223/1600000000000000000000000) (5606276846714626362412483/10000000000000000000000000) := Bounds.mul h3 h9 (by norm_num)
  convert h10 using 1 <;>
    simp only [v0, v2, v3, v4, v6, v7, v8, v9, v10, plow] <;> ring

theorem source_emp {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) {ξ bn cd Θ : ℝ} (hξ : Bounds ξ 0 (3327793673/62500000000)) (hbn : Bounds bn 0 (813377071/500000000000)) (hcd : Bounds cd 0 (70542146573/250000000000)) (hΘ : Bounds Θ 0 0.525) :
    Bounds (eMP n 0.011 ξ bn) 0 (63148066549517415237480503/50000000000000000000000000000) := by
  let v0 : ℝ := π*bn
  have h0 : Bounds v0 0 (51105988617039673196046663/10000000000000000000000000000) := Bounds.mul pi_bounds hbn (by norm_num)
  let v1 : ℝ := (989/1000)
  have h1 : Bounds v1 (989/1000) (989/1000) := Bounds.point _
  let v2 : ℝ := (n : ℝ)*v1
  have h2 : Bounds v2 (523181/40) (16020811/1000) := Bounds.mul (source_dimension ha hb) h1 (by norm_num)
  let v3 : ℝ := 1/v2
  have h3 : Bounds v3 (62418812630646476011732489/1000000000000000000000000000000) (4778460991511541894678897/62500000000000000000000000000) := Bounds.inv h2 (by norm_num)
  let v4 : ℝ := v0/v2
  have h4 : Bounds v4 0 (39073275686265115282127343/100000000000000000000000000000000) := bounds_div h0 h3 (by norm_num)
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 0 (625086199545831561003110019/1000000000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := 2
  have h6 : Bounds v6 2 2 := Bounds.point _
  let v7 : ℝ := v5*v6
  have h7 : Bounds v7 0 (31254309977291578050155501/25000000000000000000000000000) := Bounds.mul h5 h6 (by norm_num)
  let v8 : ℝ := π*ξ
  have h8 : Bounds v8 0 (8363657724607515741086917/50000000000000000000000000) := Bounds.mul pi_bounds hξ (by norm_num)
  let v9 : ℝ := (n : ℝ)*v1
  have h9 : Bounds v9 (523181/40) (16020811/1000) := Bounds.mul (source_dimension ha hb) h1 (by norm_num)
  let v10 : ℝ := 1/v9
  have h10 : Bounds v10 (62418812630646476011732489/1000000000000000000000000000000) (4778460991511541894678897/62500000000000000000000000000) := Bounds.inv h9 (by norm_num)
  let v11 : ℝ := v8/v9
  have h11 : Bounds v11 0 (3996541218339119607309381/312500000000000000000000000000) := bounds_div h8 h10 (by norm_num)
  let v12 : ℝ := v7+v11
  have h12 : Bounds v12 0 (63148066549517415237480503/50000000000000000000000000000) := Bounds.add h7 h11 (by norm_num)
  convert h12 using 1 <;>
    simp only [v0, v1, v2, v4, v5, v6, v7, v8, v9, v11, v12, eMP] <;> ring

theorem source_parallel {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) {ξ bn cd Θ : ℝ} (hξ : Bounds ξ 0 (3327793673/62500000000)) (hbn : Bounds bn 0 (813377071/500000000000)) (hcd : Bounds cd 0 (70542146573/250000000000)) (hΘ : Bounds Θ 0 0.525) :
    Bounds (parallelFormula n n 0.011 ξ bn cd Θ 1.22) (119838114387664601078115327/10000000000000000000000000000) (835760641766936438474901/25000000000000000000000000) := by
  let v0 : ℝ := π*bn
  have h0 : Bounds v0 0 (51105988617039673196046663/10000000000000000000000000000) := Bounds.mul pi_bounds hbn (by norm_num)
  let v1 : ℝ := (989/1000)
  have h1 : Bounds v1 (989/1000) (989/1000) := Bounds.point _
  let v2 : ℝ := (n : ℝ)*v1
  have h2 : Bounds v2 (523181/40) (16020811/1000) := Bounds.mul (source_dimension ha hb) h1 (by norm_num)
  let v3 : ℝ := 1/v2
  have h3 : Bounds v3 (62418812630646476011732489/1000000000000000000000000000000) (4778460991511541894678897/62500000000000000000000000000) := Bounds.inv h2 (by norm_num)
  let v4 : ℝ := v0/v2
  have h4 : Bounds v4 0 (39073275686265115282127343/100000000000000000000000000000000) := bounds_div h0 h3 (by norm_num)
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 0 (625086199545831561003110019/1000000000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := 2
  have h6 : Bounds v6 2 2 := Bounds.point _
  let v7 : ℝ := v5*v6
  have h7 : Bounds v7 0 (31254309977291578050155501/25000000000000000000000000000) := Bounds.mul h5 h6 (by norm_num)
  let v8 : ℝ := π*ξ
  have h8 : Bounds v8 0 (8363657724607515741086917/50000000000000000000000000) := Bounds.mul pi_bounds hξ (by norm_num)
  let v9 : ℝ := (n : ℝ)*v1
  have h9 : Bounds v9 (523181/40) (16020811/1000) := Bounds.mul (source_dimension ha hb) h1 (by norm_num)
  let v10 : ℝ := 1/v9
  have h10 : Bounds v10 (62418812630646476011732489/1000000000000000000000000000000) (4778460991511541894678897/62500000000000000000000000000) := Bounds.inv h9 (by norm_num)
  let v11 : ℝ := v8/v9
  have h11 : Bounds v11 0 (3996541218339119607309381/312500000000000000000000000000) := bounds_div h8 h10 (by norm_num)
  let v12 : ℝ := v7+v11
  have h12 : Bounds v12 0 (63148066549517415237480503/50000000000000000000000000000) := Bounds.add h7 h11 (by norm_num)
  let v13 : ℝ := Real.sqrt bn
  have h13 : Bounds v13 0 (16133216130703759960708613/400000000000000000000000000) := Bounds.sqrt hbn (by norm_num)
  let v14 : ℝ := Real.sqrt π
  have h14 : Bounds v14 (177245385090551602729742179/100000000000000000000000000) (7089815403622064109200971/4000000000000000000000000) := Bounds.sqrt pi_bounds (by norm_num)
  let v15 : ℝ := ξ*v14
  have h15 : Bounds v15 0 (9437377137164578490319749/100000000000000000000000000) := Bounds.mul hξ h14 (by norm_num)
  let v16 : ℝ := (n : ℝ)*v1
  have h16 : Bounds v16 (523181/40) (16020811/1000) := Bounds.mul (source_dimension ha hb) h1 (by norm_num)
  let v17 : ℝ := Real.sqrt v16
  have h17 : Bounds v17 (7147859437009796151717463/62500000000000000000000) (5062933695003322873360283/40000000000000000000000) := Bounds.sqrt h16 (by norm_num)
  let v18 : ℝ := v17*v6
  have h18 : Bounds v18 (7147859437009796151717463/31250000000000000000000) (5062933695003322873360283/20000000000000000000000) := Bounds.mul h17 h6 (by norm_num)
  let v19 : ℝ := 1/v18
  have h19 : Bounds v19 (19751394354362440177655031/5000000000000000000000000000) (10929845597618867889648077/2500000000000000000000000000) := Bounds.inv h18 (by norm_num)
  let v20 : ℝ := v15/v18
  have h20 : Bounds v20 0 (10314907495570722294947227/25000000000000000000000000000) := bounds_div h15 h19 (by norm_num)
  let v21 : ℝ := v13+v20
  have h21 : Bounds v21 0 (20372818313291114396784711/500000000000000000000000000) := Bounds.add h13 h20 (by norm_num)
  let v22 : ℝ := 1
  have h22 : Bounds v22 1 1 := Bounds.point _
  let v23 : ℝ := v12+v22
  have h23 : Bounds v23 1 (50063148066549517415237481/50000000000000000000000000) := Bounds.add h12 h22 (by norm_num)
  let v24 : ℝ := v21*v23
  have h24 : Bounds v24 0 (40797096790048186170759993/1000000000000000000000000000) := Bounds.mul h21 h23 (by norm_num)
  let v25 : ℝ := Real.sqrt (n : ℝ)
  have h25 : Bounds v25 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v26 : ℝ := (n : ℝ)*v25
  have h26 : Bounds v26 1520875 (51543311451384019511789483/25000000000000000000) := Bounds.mul (source_dimension ha hb) h25 (by norm_num)
  let v27 : ℝ := 8
  have h27 : Bounds v27 8 8 := Bounds.point _
  let v28 : ℝ := 1/v26
  have h28 : Bounds v28 (48502898428596617499562667/100000000000000000000000000000000) (65751623243198816470781623/100000000000000000000000000000000) := Bounds.inv h26 (by norm_num)
  let v29 : ℝ := v27/v26
  have h29 : Bounds v29 (48502898428596617499562667/12500000000000000000000000000000) (65751623243198816470781623/12500000000000000000000000000000) := bounds_div h27 h28 (by norm_num)
  let v30 : ℝ := v24+v29
  have h30 : Bounds v30 (48502898428596617499562667/12500000000000000000000000000000) (102005892299769105190194139/2500000000000000000000000000) := Bounds.add h24 h29 (by norm_num)
  let v31 : ℝ := (24264/125)
  have h31 : Bounds v31 (24264/125) (24264/125) := Bounds.point _
  let v32 : ℝ := 1/(n : ℝ)
  have h32 : Bounds v32 (7716525711463670596950429/125000000000000000000000000000) (37807183364839319470699433/500000000000000000000000000000) := Bounds.inv (source_dimension ha hb) (by norm_num)
  let v33 : ℝ := v31/(n : ℝ)
  have h33 : Bounds v33 (119829619112290882153219333/10000000000000000000000000000) (14677655954631379962192817/1000000000000000000000000000) := bounds_div h31 h32 (by norm_num)
  let v34 : ℝ := Real.sqrt v33
  have h34 : Bounds v34 (109466715997279685522467547/1000000000000000000000000000) (60575688098921707507166077/500000000000000000000000000) := Bounds.sqrt h33 (by norm_num)
  let v35 : ℝ := v30+v34
  have h35 : Bounds v35 (13683824528644246656483439/125000000000000000000000000) (16195373311775105709040981/100000000000000000000000000) := Bounds.add h30 h34 (by norm_num)
  let v36 : ℝ := (plow n 0.011)*v6
  have h36 : Bounds v36 (70065795981/62500000000) 2 := Bounds.mul (show Bounds (plow n 0.011) (70065795981/125000000000) 1 from ⟨le_trans (by norm_num) (source_plow ha hb).1, (source_plow ha hb).2.trans (by norm_num)⟩) h6 (by norm_num)
  let v37 : ℝ := Real.sqrt (n : ℝ)
  have h37 : Bounds v37 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v38 : ℝ := v36*v37
  have h38 : Bounds v38 (1611513307563/12500000000) (25455058436389416389549717/100000000000000000000000) := Bounds.mul h36 h37 (by norm_num)
  let v39 : ℝ := 1/v38
  have h39 : Bounds v39 (19642461291120915171885391/5000000000000000000000000000) (77566843173656689695104879/10000000000000000000000000000) := Bounds.inv h38 (by norm_num)
  let v40 : ℝ := cd/v38
  have h40 : Bounds v40 0 (218869264814439787874162683/100000000000000000000000000000) := bounds_div hcd h39 (by norm_num)
  let v41 : ℝ := v40+v22
  have h41 : Bounds v41 1 (100218869264814439787874163/100000000000000000000000000) := Bounds.add h40 h22 (by norm_num)
  let v42 : ℝ := v41*v35
  have h42 : Bounds v42 (13683824528644246656483439/125000000000000000000000000) (16230820006276541872287431/100000000000000000000000000) := Bounds.mul h41 h35 (by norm_num)
  let v43 : ℝ := cd^2
  have h43 : Bounds v43 0 (4976194443126615644329/62500000000000000000000) := Bounds.pow hcd 2 (by norm_num)
  let v44 : ℝ := (plow n 0.011)*v6
  have h44 : Bounds v44 (70065795981/62500000000) 2 := Bounds.mul (show Bounds (plow n 0.011) (70065795981/125000000000) 1 from ⟨le_trans (by norm_num) (source_plow ha hb).1, (source_plow ha hb).2.trans (by norm_num)⟩) h6 (by norm_num)
  let v45 : ℝ := Real.sqrt (n : ℝ)
  have h45 : Bounds v45 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v46 : ℝ := v44*v45
  have h46 : Bounds v46 (1611513307563/12500000000) (25455058436389416389549717/100000000000000000000000) := Bounds.mul h44 h45 (by norm_num)
  let v47 : ℝ := 1/v46
  have h47 : Bounds v47 (19642461291120915171885391/5000000000000000000000000000) (77566843173656689695104879/10000000000000000000000000000) := Bounds.inv h46 (by norm_num)
  let v48 : ℝ := v43/v46
  have h48 : Bounds v48 0 (61758031035459852652408849/100000000000000000000000000000) := bounds_div h43 h47 (by norm_num)
  let v49 : ℝ := v42+v48
  have h49 : Bounds v49 (13683824528644246656483439/125000000000000000000000000) (162925780373120017249398399/1000000000000000000000000000) := Bounds.add h42 h48 (by norm_num)
  let v50 : ℝ := (N22bar n 12)+v22
  have h50 : Bounds v50 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h22 (by norm_num)
  let v51 : ℝ := Θ*v50
  have h51 : Bounds v51 0 (42063/80000) := Bounds.mul hΘ h50 (by norm_num)
  let v52 : ℝ := (61/50)
  have h52 : Bounds v52 (61/50) (61/50) := Bounds.point _
  let v53 : ℝ := Θ*v52
  have h53 : Bounds v53 0 (1281/2000) := Bounds.mul hΘ h52 (by norm_num)
  let v54 : ℝ := Real.sqrt v53
  have h54 : Bounds v54 0 (80031243898867397274070841/100000000000000000000000000) := Bounds.sqrt h53 (by norm_num)
  let v55 : ℝ := v51+v54
  have h55 : Bounds v55 0 (132609993898867397274070841/100000000000000000000000000) := Bounds.add h51 h54 (by norm_num)
  let v56 : ℝ := Real.sqrt (n : ℝ)
  have h56 : Bounds v56 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v57 : ℝ := 1/v56
  have h57 : Bounds v57 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h56 (by norm_num)
  let v58 : ℝ := v55/v56
  have h58 : Bounds v58 0 (115313038172928171542670297/10000000000000000000000000000) := bounds_div h55 h57 (by norm_num)
  let v59 : ℝ := v49+v58
  have h59 : Bounds v59 (13683824528644246656483439/125000000000000000000000000) (174457084190412834403665429/1000000000000000000000000000) := Bounds.add h49 h58 (by norm_num)
  let v60 : ℝ := cd+v58
  have h60 : Bounds v60 0 (29369989010929281715426703/100000000000000000000000000) := Bounds.add hcd h58 (by norm_num)
  let v61 : ℝ := v60*v6
  have h61 : Bounds v61 0 (29369989010929281715426703/50000000000000000000000000) := Bounds.mul h60 h6 (by norm_num)
  let v62 : ℝ := Real.sqrt (n : ℝ)
  have h62 : Bounds v62 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v63 : ℝ := (plow n 0.011)*v62
  have h63 : Bounds v63 (1611513307563/25000000000) (15909411522743385243468573/125000000000000000000000) := Bounds.mul (show Bounds (plow n 0.011) (70065795981/125000000000) 1 from ⟨le_trans (by norm_num) (source_plow ha hb).1, (source_plow ha hb).2.trans (by norm_num)⟩) h62 (by norm_num)
  let v64 : ℝ := 1/v63
  have h64 : Bounds v64 (15713969032896732137508313/2000000000000000000000000000) (155133686347313379390209757/10000000000000000000000000000) := Bounds.inv h63 (by norm_num)
  let v65 : ℝ := v61/v63
  have h65 : Bounds v65 0 (91125493264910877877714411/10000000000000000000000000000) := bounds_div h61 h64 (by norm_num)
  let v66 : ℝ := v65+v22
  have h66 : Bounds v66 1 (20182250986529821755755429/20000000000000000000000000) := Bounds.add h65 h22 (by norm_num)
  let v67 : ℝ := (finiteEnergy n n 0.011)*v66
  have h67 : Bounds v67 0 (83828066175764858867517703/10000000000000000000000000000) := Bounds.mul (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) h66 (by norm_num)
  let v68 : ℝ := v59+v67
  have h68 : Bounds v68 (13683824528644246656483439/125000000000000000000000000) (457099727019973300726043/2500000000000000000000000) := Bounds.add h59 h67 (by norm_num)
  let v69 : ℝ := v68^2
  have h69 : Bounds v69 (119838114387664601078115327/10000000000000000000000000000) (835760641766936438474901/25000000000000000000000000) := Bounds.pow h68 2 (by norm_num)
  dsimp only [v69, v68, v67, v66, v65, v63, v62, v61] at h69
  dsimp only [v60, v59, v58, v56, v55, v54, v53, v52] at h69
  dsimp only [v51, v50, v49, v48, v46, v45, v44, v43] at h69
  dsimp only [v42, v41, v40, v38, v37, v36, v35, v34] at h69
  dsimp only [v33, v31, v30, v29, v27, v26, v25, v24] at h69
  dsimp only [v23, v22, v21, v20, v18, v17, v16, v15] at h69
  dsimp only [v14, v13, v12, v11, v9, v8, v7, v6] at h69
  dsimp only [v5, v4, v2, v1, v0] at h69
  convert h69 using 1 <;>
    simp only [parallelFormula, BstLean.Part206.parallelAllowance, parallelOracle, PiBarMP, eMP, xiNr] <;> congr 1 <;> ring

noncomputable def source_centres : Fin 10 → ℝ
  | ⟨0,_⟩ => (8772214303/100000000000)
  | ⟨1,_⟩ => (422312977/5000000000)
  | ⟨2,_⟩ => (85443658731/1000000000000)
  | ⟨3,_⟩ => (43209086243/500000000000)
  | ⟨4,_⟩ => (87386055887/1000000000000)
  | ⟨5,_⟩ => (44173615181/500000000000)
  | ⟨6,_⟩ => (11162702301/125000000000)
  | ⟨7,_⟩ => (2820285769/31250000000)
  | ⟨8,_⟩ => (2279743363/25000000000)
  | ⟨9,_⟩ => (8772214303/100000000000)
  | ⟨j+10,h⟩ => False.elim (by omega)

theorem source_moment_group1 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨1,by decide⟩) (groupProfile ⟨1,by decide⟩)) 0 (2423306690243186131/50000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨1,by decide⟩)) (S := (groupProfile ⟨1,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full1 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨1,by decide⟩) (groupProfile ⟨1,by decide⟩) 1.22) (94179274606284753422230899/1000000000000000000000000000000) (422312976991965542623517401/5000000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (23719663/50000000)
  have h2 : Bounds v2 (23719663/50000000) (23719663/50000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (23719663/50000000) (47510484989/100000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (1446899443/2500000000)
  have h4 : Bounds v4 (1446899443/2500000000) (1446899443/2500000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (15215252573651217571824659/20000000000000000000000000) (2377383214633002745597603/3125000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (24703117773651217571824659/20000000000000000000000000) (3862085870539252745597603/3125000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (19409201385557804904851639/2000000000000000000000000000) (53733368633589603417010129/5000000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨1,by decide⟩) (groupProfile ⟨1,by decide⟩))
  have h10 : Bounds v10 0 (220150252793095203886025981/1000000000000000000000000000) := Bounds.sqrt (source_moment_group1 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨1,by decide⟩))
  have h11 : Bounds v11 0 (271570710667095203886025981/1000000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨1,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨1,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (19409201385557804904851639/2000000000000000000000000000) (282317384393813124569428007/1000000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (19409201385557804904851639/2000000000000000000000000000) (290624492082813124569428007/1000000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (94179274606284753422230899/1000000000000000000000000000000) (422312976991965542623517401/5000000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group2 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨2,by decide⟩) (groupProfile ⟨2,by decide⟩)) 0 (49160011791770991693/1000000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨2,by decide⟩)) (S := (groupProfile ⟨2,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full2 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨2,by decide⟩) (groupProfile ⟨2,by decide⟩) 1.22) (961637586923108640078299773/10000000000000000000000000000000) (854436587302016384073975701/10000000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (481589889/1000000000)
  have h2 : Bounds v2 (481589889/1000000000) (481589889/1000000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (481589889/1000000000) (964624547667/2000000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (29376983229/50000000000)
  have h4 : Bounds v4 (29376983229/50000000000) (29376983229/50000000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (4790695998250802179572687/6250000000000000000000000) (76651135972012834873162993/100000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (7800632804500802179572687/6250000000000000000000000) (124882363355362834873162993/100000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (98063121861539195038128621/10000000000000000000000000000) (108593359439445943367967821/10000000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨2,by decide⟩) (groupProfile ⟨2,by decide⟩))
  have h10 : Bounds v10 0 (110860285711082072437448119/500000000000000000000000000) := Bounds.sqrt (source_moment_group2 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨2,by decide⟩))
  have h11 : Bounds v11 0 (3414262866202051810936203/12500000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨2,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨2,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (98063121861539195038128621/10000000000000000000000000000) (284000365240108739211693023/1000000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (98063121861539195038128621/10000000000000000000000000000) (292307472929108739211693023/1000000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (961637586923108640078299773/10000000000000000000000000000000) (854436587302016384073975701/10000000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group3 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨3,by decide⟩) (groupProfile ⟨3,by decide⟩)) 0 (49849710777824553003/1000000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨3,by decide⟩)) (S := (groupProfile ⟨3,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full3 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨3,by decide⟩) (groupProfile ⟨3,by decide⟩) 1.22) (981622706943025858388038991/10000000000000000000000000000000) (864181724852308359646406951/10000000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (488786519/1000000000)
  have h2 : Bounds v2 (488786519/1000000000) (488786519/1000000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (488786519/1000000000) (979039397557/2000000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (29815977659/50000000000)
  have h4 : Bounds v4 (29815977659/50000000000) (29815977659/50000000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (38610864830381616304498797/50000000000000000000000000) (15444345932152646521799519/20000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (63050190780381616304498797/50000000000000000000000000) (25234739907722646521799519/20000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (495384372720573882049899457/50000000000000000000000000000) (109716260468359332703476171/10000000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨3,by decide⟩) (groupProfile ⟨3,by decide⟩))
  have h10 : Bounds v10 0 (223270487924007889921450791/1000000000000000000000000000) := Bounds.sqrt (source_moment_group3 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨3,by decide⟩))
  have h11 : Bounds v11 0 (274690945798007889921450791/1000000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨3,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨3,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (99076874544114776409979891/10000000000000000000000000000) (285662571844843823191798409/1000000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (99076874544114776409979891/10000000000000000000000000000) (293969679533843823191798409/1000000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (981622706943025858388038991/10000000000000000000000000000000) (864181724852308359646406951/10000000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group4 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨4,by decide⟩) (groupProfile ⟨4,by decide⟩)) 0 (12633783373670105519/250000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨4,by decide⟩)) (S := (groupProfile ⟨4,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full4 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨4,by decide⟩) (groupProfile ⟨4,by decide⟩) 1.22) (50087376825785516998082557/500000000000000000000000000000) (43693027943086170003076611/500000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (123995787/250000000)
  have h2 : Bounds v2 (123995787/250000000) (123995787/250000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (123995787/250000000) (248363561361/500000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (7563743007/12500000000)
  have h4 : Bounds v4 (7563743007/12500000000) (7563743007/12500000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (194470344872939431932039849/250000000000000000000000000) (777881379491757727728159397/1000000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (127386452749175772772815939/100000000000000000000000000) (6373042511068788638640797/5000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (100087338685555544147003427/10000000000000000000000000000) (6927220120726944172435649/625000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨4,by decide⟩) (groupProfile ⟨4,by decide⟩))
  have h10 : Bounds v10 0 (224800207950705468372097879/1000000000000000000000000000) := Bounds.sqrt (source_moment_group4 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨4,by decide⟩))
  have h11 : Bounds v11 0 (276220665824705468372097879/1000000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨4,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨4,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (100087338685555544147003427/10000000000000000000000000000) (7182605450446714476199873/25000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (100087338685555544147003427/10000000000000000000000000000) (7390283142671714476199873/25000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (50087376825785516998082557/500000000000000000000000000000) (43693027943086170003076611/500000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group5 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨5,by decide⟩) (groupProfile ⟨5,by decide⟩)) 0 (25608092678236391693/500000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨5,by decide⟩)) (S := (groupProfile ⟨5,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full5 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨5,by decide⟩) (groupProfile ⟨5,by decide⟩) 1.22) (102201152950357662314827357/1000000000000000000000000000000) (88347230360266895379064463/1000000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (251589889/500000000)
  have h2 : Bounds v2 (251589889/500000000) (251589889/500000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (251589889/500000000) (503934547667/1000000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (15346983229/25000000000)
  have h4 : Bounds v4 (15346983229/25000000000) (15346983229/25000000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (9793806470481740124673299/12500000000000000000000000) (78350451763853920997386393/100000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (16083553695481740124673299/12500000000000000000000000) (128743906530553920997386393/100000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (50547292941946372424933421/5000000000000000000000000000) (6996951441877930488988391/625000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨5,by decide⟩) (groupProfile ⟨5,by decide⟩))
  have h10 : Bounds v10 0 (226309932076506053168154423/1000000000000000000000000000) := Bounds.sqrt (source_moment_group5 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨5,by decide⟩))
  have h11 : Bounds v11 0 (277730389950506053168154423/1000000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨5,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨5,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (50547292941946372424933421/5000000000000000000000000000) (5778510245150214839010717/20000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (50547292941946372424933421/5000000000000000000000000000) (5944652398930214839010717/20000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (102201152950357662314827357/1000000000000000000000000000000) (88347230360266895379064463/1000000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group6 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨6,by decide⟩) (groupProfile ⟨6,by decide⟩)) 0 (51892773619396852459/1000000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨6,by decide⟩)) (S := (groupProfile ⟨6,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full6 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨6,by decide⟩) (groupProfile ⟨6,by decide⟩) 1.22) (52120707021252710571434927/500000000000000000000000000000) (89301618406439513254614977/1000000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (510376407/1000000000)
  have h2 : Bounds v2 (510376407/1000000000) (510376407/1000000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (510376407/1000000000) (1022283943221/2000000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (31132960827/50000000000)
  have h4 : Bounds v4 (31132960827/50000000000) (31132960827/50000000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (3945437924172676677496521/5000000000000000000000000) (78908758483453533549930421/100000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (6497319959172676677496521/5000000000000000000000000) (130022955644503533549930421/100000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (102098684635261301265793321/10000000000000000000000000000) (22612687938174527573900943/2000000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨6,by decide⟩) (groupProfile ⟨6,by decide⟩))
  have h10 : Bounds v10 0 (113899927150324433887269149/500000000000000000000000000) := Bounds.sqrt (source_moment_group6 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨6,by decide⟩))
  have h11 : Bounds v11 0 (2792203121746488677745383/10000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨6,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨6,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (102098684635261301265793321/10000000000000000000000000000) (72631664035934032890372193/250000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (102098684635261301265793321/10000000000000000000000000000) (74708440958184032890372193/250000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (52120707021252710571434927/500000000000000000000000000000) (89301618406439513254614977/1000000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group7 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨7,by decide⟩) (groupProfile ⟨7,by decide⟩)) 0 (52564808062355213769/1000000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨7,by decide⟩)) (S := (groupProfile ⟨7,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full7 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨7,by decide⟩) (groupProfile ⟨7,by decide⟩) 1.22) (53147742327999291053671697/500000000000000000000000000000) (9024914460741310688459153/100000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (517573037/1000000000)
  have h2 : Bounds v2 (517573037/1000000000) (517573037/1000000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (517573037/1000000000) (1036698793111/2000000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (31571955257/50000000000)
  have h4 : Bounds v4 (31571955257/50000000000) (31571955257/50000000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (79463142722900155882430149/100000000000000000000000000) (1589262854458003117648603/2000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (131220446422900155882430149/100000000000000000000000000) (2625961647569003117648603/2000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (20619940315723378165700823/2000000000000000000000000000) (114172245546478396419504479/10000000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨7,by decide⟩) (groupProfile ⟨7,by decide⟩))
  have h10 : Bounds v10 0 (229270163916623075652461017/1000000000000000000000000000) := Bounds.sqrt (source_moment_group7 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨7,by decide⟩))
  have h11 : Bounds v11 0 (280690621790623075652461017/1000000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨7,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨7,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (20619940315723378165700823/2000000000000000000000000000) (58421569269054183058882293/200000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (20619940315723378165700823/2000000000000000000000000000) (60082990806854183058882293/200000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (53147742327999291053671697/500000000000000000000000000000) (9024914460741310688459153/100000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

theorem source_moment_group8 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨8,by decide⟩) (groupProfile ⟨8,by decide⟩)) 0 (26616100082692041421/500000000000000000000) := by
  constructor
  · exact source_moment_nonneg (by norm_num [groupTheta]) (by norm_num [groupProfile])
  · have h := source_moment_upper ha hb
      (Θ := (groupTheta ⟨8,by decide⟩)) (S := (groupProfile ⟨8,by decide⟩)) (by norm_num [groupTheta]) (by norm_num [groupProfile])
    convert h using 1 <;> norm_num [groupTheta, groupProfile]

theorem source_full8 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)  :
    Bounds (fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta ⟨8,by decide⟩) (groupProfile ⟨8,by decide⟩) 1.22) (108363312486997236544045807/1000000000000000000000000000000) (91189734519471358174376783/1000000000000000000000000000) := by
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := (N22bar n 12)+v0
  have h1 : Bounds v1 1 (2003/2000) := Bounds.add (show Bounds (N22bar n 12) 0 (3/2000) from ⟨(by unfold N22bar N12bar; positivity), (source_n22 ha hb).2.trans (by norm_num)⟩) h0 (by norm_num)
  let v2 : ℝ := (262384833/500000000)
  have h2 : Bounds v2 (262384833/500000000) (262384833/500000000) := Bounds.point _
  let v3 : ℝ := v1*v2
  have h3 : Bounds v3 (262384833/500000000) (525556820499/1000000000000) := Bounds.mul h1 h2 (by norm_num)
  let v4 : ℝ := (16005474813/25000000000)
  have h4 : Bounds v4 (16005474813/25000000000) (16005474813/25000000000) := Bounds.point _
  let v5 : ℝ := Real.sqrt v4
  have h5 : Bounds v5 (40006842930928703812359751/50000000000000000000000000) (80013685861857407624719503/100000000000000000000000000) := Bounds.sqrt h4 (by norm_num)
  let v6 : ℝ := v3+v5
  have h6 : Bounds v6 (66245326230928703812359751/50000000000000000000000000) (132569367911757407624719503/100000000000000000000000000) := Bounds.add h3 h5 (by norm_num)
  let v7 : ℝ := Real.sqrt (n : ℝ)
  have h7 : Bounds v7 115 (15909411522743385243468573/125000000000000000000000) := Bounds.sqrt (source_dimension ha hb) (by norm_num)
  let v8 : ℝ := 1/v7
  have h8 : Bounds v8 (15713969032896732137508313/2000000000000000000000000000) (10869565217391304347826087/1250000000000000000000000000) := Bounds.inv h7 (by norm_num)
  let v9 : ℝ := v6/v7
  have h9 : Bounds v9 (104097700496695524529831767/10000000000000000000000000000) (57638855613807568532486741/5000000000000000000000000000) := bounds_div h6 h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (momentAllowance n csC 0.011 1.22 1.12 (groupTheta ⟨8,by decide⟩) (groupProfile ⟨8,by decide⟩))
  have h10 : Bounds v10 0 (57680261011341697790656373/250000000000000000000000000) := Bounds.sqrt (source_moment_group8 ha hb) (by norm_num)
  let v11 : ℝ := v10+(sharpDeviation n csC 0.011 0.46 (groupTheta ⟨8,by decide⟩))
  have h11 : Bounds v11 0 (70535375479841697790656373/250000000000000000000000000) := Bounds.add h10 (show Bounds (sharpDeviation n csC 0.011 0.46 (groupTheta ⟨8,by decide⟩)) 0 (25710228937/500000000000) from ⟨(by unfold sharpDeviation; positivity), (source_deviation ha hb (groupTheta ⟨8,by decide⟩) (by norm_num [Bounds,groupTheta])).2.trans (by norm_num)⟩) (by norm_num)
  let v12 : ℝ := v11+v9
  have h12 : Bounds v12 (104097700496695524529831767/10000000000000000000000000000) (5873385460842566097382457/20000000000000000000000000) := Bounds.add h11 h9 (by norm_num)
  let v13 : ℝ := v12+(finiteEnergy n n 0.011)
  have h13 : Bounds v13 (104097700496695524529831767/10000000000000000000000000000) (6039527614622566097382457/20000000000000000000000000) := Bounds.add h12 (show Bounds (finiteEnergy n n 0.011) 0 (8307107689/1000000000000) from ⟨finiteEnergy_nonneg n n (by norm_num), source_finite_decimal ha⟩) (by norm_num)
  let v14 : ℝ := v13^2
  have h14 : Bounds v14 (108363312486997236544045807/1000000000000000000000000000000) (91189734519471358174376783/1000000000000000000000000000) := Bounds.pow h13 2 (by norm_num)
  convert h14 using 1 <;>
    simp only [v0, v1, v2, v3, v4, v5, v6, v7, v9, v10, v11, v12, v13, v14, fullFormula, xiNr, groupTheta] <;> ring

noncomputable def source_groupMoment {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate n 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
  have hr := source_rho ha hb
  have hγ := source_gamma ha hb (groupTheta g) G.window
  exact {
    delta_nonneg := by norm_num
    delta_lt := by norm_num
    k_gt := by norm_num
    k3_gt := by norm_num
    theta_lower := by norm_num
    v_pos := by intro θ hθ; norm_num
    supremum := fun θ hθ => by
      have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) hθ.1
      have hθ1 : θ ≤ 1 := hθ.2.trans (G.window.2.trans (by norm_num))
      exact (mul_le_mul_of_nonneg_right (BstLean.Part264.hsProfile_le (by omega) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := hr.2.trans_lt (by norm_num)
    ratio_gamma := hγ.2.trans (by norm_num)
    gap := lt_of_lt_of_le (by norm_num) (source_gap2 (hr.2.trans (by norm_num)))
    gap_gamma := lt_of_lt_of_le (by norm_num) (source_gap1 (hγ.2.trans (by norm_num))) }

theorem source_group_bounds {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {g : Fin 10} (hg : NeededGroup g) :
    Bounds (momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) 0 (3327793673/62500000000) ∧
    Bounds (bN n csC (groupTheta g)) 0 (813377071/500000000000) ∧
    Bounds (√(momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
      sharpDeviation n csC 0.011 0.46 (groupTheta g)) 0 (70542146573/250000000000) := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := source_moment_upper ha hb G.window G.profile_nonneg
  have hbN := source_bn_upper ha hb hΘ
  have hm0 := source_moment_nonneg (n := n) hΘ G.profile_nonneg
  have hmu : momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ (3327793673/62500000000) := by
    have := G.profile_le
    have := G.window.2
    linarith
  have hbNu : bN n csC (groupTheta g) ≤ (813377071/500000000000) := by
    have := G.window.2
    linarith
  have hs : √(momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) ≤
      (115374064209/500000000000) := sqrt_le_iff.mpr ⟨by norm_num, hmu.trans (by norm_num)⟩
  have hd := (source_deviation ha hb (groupTheta g) ⟨hΘ,G.window.2⟩).2
  refine ⟨⟨hm0,hmu⟩, ⟨source_bn_nonneg hΘ,hbNu⟩, ⟨?_, ?_⟩⟩
  · unfold sharpDeviation
    positivity
  · linarith

theorem source_group_parallel {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula n n 0.011
      (momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN n csC (groupTheta g))
      (√(momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation n csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ (3353042747/100000000000) := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hm,hbN,hcd⟩ := source_group_bounds ha hb hg
  exact (source_parallel ha hb hm hbN hcd
    ⟨le_trans (by norm_num) G.window.1,G.window.2⟩).2.trans (by norm_num)

theorem source_group_gap {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {g : Fin 10} (hg : NeededGroup g) :
    eMP n 0.011 (momentAllowance n csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN n csC (groupTheta g)) ≤ 1/10 := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hm,hbN,hcd⟩ := source_group_bounds ha hb hg
  exact (source_emp ha hb hm hbN hcd
    ⟨le_trans (by norm_num) G.window.1,G.window.2⟩).2.trans (by norm_num)

theorem source_group_full {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {g : Fin 10} (hg : NeededGroup g) :
    fullFormula n n 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g) 1.22 ≤ source_centres g := by
  fin_cases g <;> simp [NeededGroup] at hg
  · exact (source_full1 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full2 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full3 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full4 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full5 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full6 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full7 ha hb).2.trans (by norm_num [source_centres])
  · exact (source_full8 ha hb).2.trans (by norm_num [source_centres])

end BstLean.Part271.R4.A13225
