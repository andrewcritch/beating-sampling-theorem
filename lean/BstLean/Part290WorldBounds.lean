import BstLean.Part290WorldScale

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part140 BstLean.Part159 BstLean.Part233
open BstLean.Part228 BstLean.Part250
open BstLean.Part271.R3 (angularMomentCore angularMomentCore_formula j2Core j4Core
  jbCore aCore bCore offsetCore ba1Core ba2Core traceCore diagonalCore covariancePaymentCore normCore)
theorem perturbation_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (perturbation n) 0 (35212590144230769230769231/25000000000000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := (129/2000)
  have h0 : Bounds v0 (129/2000) (129/2000) := Bounds.point _
  let v1 : ℝ := v0*(1/(mW n : ℝ))
  have h1 : Bounds v1 0 (35212590144230769230769231/25000000000000000000000000000000000000000) := Bounds.mul h0 (inverse_width ha) (by norm_num)
  convert h1 using 1 <;>
    simp only [v0, v1, perturbation, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem nperturbation_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds ((n : ℝ)*perturbation n) 0 (112680288461538461538461539/10000000000000000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := (129/2000)
  have h0 : Bounds v0 (129/2000) (129/2000) := Bounds.point _
  let v2 : ℝ := v0*(((2*n : ℕ) : ℝ)/(mW n : ℝ))
  have h2 : Bounds v2 0 (225360576923076923076923077/10000000000000000000000000000000000000) := Bounds.mul h0 (dimension_width ha) (by norm_num)
  let v3 : ℝ := 2
  have h3 : Bounds v3 2 2 := Bounds.point _
  let v4 : ℝ := 1/v3
  have h4 : Bounds v4 (1/2) (1/2) := Bounds.inv h3 (by norm_num)
  let v5 : ℝ := v2/v3
  have h5 : Bounds v5 0 (112680288461538461538461539/10000000000000000000000000000000000000) := bounds_div h2 h4 (by norm_num)
  convert h5 using 1 <;>
    simp only [v0, v2, v3, v5, perturbation, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem centre_lower_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (centreLower n (1232/10^7)) (493606047264966690407989441/1000000000000000000000000000) (123403950000000000000000003/250000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v6 : ℝ := (77/625000)
  have h6 : Bounds v6 (77/625000) (77/625000) := Bounds.point _
  let v7 : ℝ := -v6
  have h7 : Bounds v7 (-77/625000) (-77/625000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h6
  let v8 : ℝ := kap1 (2*n)+v7
  have h8 : Bounds v8 (4936061/10000000) (2468079/5000000) := Bounds.add (kernel_window ha) h7 (by norm_num)
  let v9 : ℝ := Real.sqrt v8
  have h9 : Bounds v9 (702571064021284611288479541/1000000000000000000000000000) (70257796720364068074919469/100000000000000000000000000) := Bounds.sqrt h8 (by norm_num)
  let v10 : ℝ := Real.sqrt (perturbation n)
  have h10 : Bounds v10 0 (37530036048067296910137579/1000000000000000000000000000000000) := Bounds.sqrt (perturbation_bounds ha) (by norm_num)
  let v11 : ℝ := -v10
  have h11 : Bounds v11 (-37530036048067296910137579/1000000000000000000000000000000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h10
  let v12 : ℝ := v9+v11
  have h12 : Bounds v12 (70257102649124856322118263/100000000000000000000000000) (70257796720364068074919469/100000000000000000000000000) := Bounds.add h9 h11 (by norm_num)
  let v13 : ℝ := v12^2
  have h13 : Bounds v13 (493606047264966690407989441/1000000000000000000000000000) (123403950000000000000000003/250000000000000000000000000) := Bounds.pow h12 2 (by norm_num)
  convert h13 using 1 <;>
    simp only [v6, v7, v8, v9, v10, v11, v12, v13, centreLower, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem denominator_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (worldS n) (458648997351212901352022903/1000000000000000000000000000) (45865925288534119045622123/100000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v14 : ℝ := (22287/1000000)
  have h14 : Bounds v14 (22287/1000000) (22287/1000000) := Bounds.point _
  let v15 : ℝ := 1
  have h15 : Bounds v15 1 1 := Bounds.point _
  let v16 : ℝ := -v14
  have h16 : Bounds v16 (-22287/1000000) (-22287/1000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h14
  let v17 : ℝ := v15+v16
  have h17 : Bounds v17 (977713/1000000) (977713/1000000) := Bounds.add h15 h16 (by norm_num)
  let v18 : ℝ := (2469/5000)
  have h18 : Bounds v18 (2469/5000) (2469/5000) := Bounds.point _
  let v19 : ℝ := (99/8000)
  have h19 : Bounds v19 (99/8000) (99/8000) := Bounds.point _
  let v20 : ℝ := v18+v19
  have h20 : Bounds v20 (20247/40000) (20247/40000) := Bounds.add h18 h19 (by norm_num)
  let v21 : ℝ := v20^2
  have h21 : Bounds v21 (409941009/1600000000) (409941009/1600000000) := Bounds.pow h20 2 (by norm_num)
  let v22 : ℝ := 1/(centreLower n (1232/10^7))
  have h22 : Bounds v22 (101293354062005308582099679/50000000000000000000000000) (20259071085958598444020597/10000000000000000000000000) := Bounds.inv (centre_lower_bounds ha) (by norm_num)
  let v23 : ℝ := v21/(centreLower n (1232/10^7))
  have h23 : Bounds v23 (51905374711465880954377877/100000000000000000000000000) (519064002648787098647977097/1000000000000000000000000000) := bounds_div h21 h22 (by norm_num)
  let v24 : ℝ := -v23
  have h24 : Bounds v24 (-519064002648787098647977097/1000000000000000000000000000) (-51905374711465880954377877/100000000000000000000000000) := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg h23
  let v25 : ℝ := v17+v24
  have h25 : Bounds v25 (458648997351212901352022903/1000000000000000000000000000) (45865925288534119045622123/100000000000000000000000000) := Bounds.add h17 h24 (by norm_num)
  convert h25 using 1 <;>
    simp only [v14, v15, v16, v17, v18, v19, v20, v21, v23, v24, v25, worldS, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem kernel_error_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (kernelError n) 0 (1/3200000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v26 : ℝ := (1/50000)
  have h26 : Bounds v26 (1/50000) (1/50000) := Bounds.point _
  let v27 : ℝ := (1/(n : ℝ))^2
  have h27 : Bounds v27 0 (1/64000000) := Bounds.pow (inverse_n ha) 2 (by norm_num)
  let v28 : ℝ := v26*v27
  have h28 : Bounds v28 0 (1/3200000000000) := Bounds.mul h26 h27 (by norm_num)
  convert h28 using 1 <;>
    simp only [v26, v27, v28, kernelError, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem product_lower_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (productLower n (1232/10^7)) (2022793400251761008281373/1000000000000000000000000) (202291285042036309831530997/100000000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v29 : ℝ := (1001/1000)
  have h29 : Bounds v29 (1001/1000) (1001/1000) := Bounds.point _
  let v30 : ℝ := kap1 (2*n)+(kernelError n)
  have h30 : Bounds v30 (4937293/10000000) (1579964800001/3200000000000) := Bounds.add (kernel_window ha) (kernel_error_bounds ha) (by norm_num)
  let v31 : ℝ := v30^2
  have h31 : Bounds v31 (24376862167849/100000000000000) (121889100060654293437500049/500000000000000000000000000) := Bounds.pow h30 2 (by norm_num)
  let v32 : ℝ := v29*v31
  have h32 : Bounds v32 (24401239030016849/100000000000000000) (2440219783214298954618751/10000000000000000000000000) := Bounds.mul h29 h31 (by norm_num)
  let v33 : ℝ := 1/v32
  have h33 : Bounds v33 (512248941098854122115751/125000000000000000000000) (2561345344927627795639987/625000000000000000000000) := Bounds.inv h32 (by norm_num)
  let v34 : ℝ := (centreLower n (1232/10^7))/v32
  have h34 : Bounds v34 (2022793400251761008281373/1000000000000000000000000) (202291285042036309831530997/100000000000000000000000000) := bounds_div (centre_lower_bounds ha) h33 (by norm_num)
  convert h34 using 1 <;>
    simp only [v29, v30, v31, v32, v34, productLower, centreLower, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem product_upper_bounds {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (productUpper n (1232/10^7)) (20278550198560674803746301/10000000000000000000000000) (506993687246089414101561/250000000000000000000000) := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v6 : ℝ := (77/625000)
  have h6 : Bounds v6 (77/625000) (77/625000) := Bounds.point _
  let v35 : ℝ := kap1 (2*n)+v6
  have h35 : Bounds v35 (197541/400000) (2469311/5000000) := Bounds.add (kernel_window ha) h6 (by norm_num)
  let v36 : ℝ := Real.sqrt v35
  have h36 : Bounds v36 (7027463980697446449203541/10000000000000000000000000) (70275329952978520327040659/100000000000000000000000000) := Bounds.sqrt h35 (by norm_num)
  let v37 : ℝ := Real.sqrt (perturbation n)
  have h37 : Bounds v37 0 (37530036048067296910137579/1000000000000000000000000000000000) := Bounds.sqrt (perturbation_bounds ha) (by norm_num)
  let v38 : ℝ := v36+v37
  have h38 : Bounds v38 (7027463980697446449203541/10000000000000000000000000) (702753337059821251337703501/1000000000000000000000000000) := Bounds.add h36 h37 (by norm_num)
  let v39 : ℝ := v38^2
  have h39 : Bounds v39 (123463124999999999999999999/250000000000000000000000000) (493862252748714737005752281/1000000000000000000000000000) := Bounds.pow h38 2 (by norm_num)
  let v40 : ℝ := (999/1000)
  have h40 : Bounds v40 (999/1000) (999/1000) := Bounds.point _
  let v41 : ℝ := -(kernelError n)
  have h41 : Bounds v41 (-1/3200000000000) 0 := by simpa only [neg_div, neg_neg, neg_zero] using Bounds.neg (kernel_error_bounds ha)
  let v42 : ℝ := kap1 (2*n)+v41
  have h42 : Bounds v42 (1579933759999/3200000000000) (493739/1000000) := Bounds.add (kernel_window ha) h41 (by norm_num)
  let v43 : ℝ := v42^2
  have h43 : Bounds v43 (243768621678181419187500097/1000000000000000000000000000) (243778200121/1000000000000) := Bounds.pow h42 2 (by norm_num)
  let v44 : ℝ := v40*v43
  have h44 : Bounds v44 (60881213264125809442078149/250000000000000000000000000) (243534421920879/1000000000000000) := Bounds.mul h40 h43 (by norm_num)
  let v45 : ℝ := 1/v44
  have h45 : Bounds v45 (10265489290102143253170887/2500000000000000000000000) (41063570615027844020187901/10000000000000000000000000) := Bounds.inv h44 (by norm_num)
  let v46 : ℝ := v39/v44
  have h46 : Bounds v46 (20278550198560674803746301/10000000000000000000000000) (506993687246089414101561/250000000000000000000000) := bounds_div h39 h45 (by norm_num)
  convert h46 using 1 <;>
    simp only [v6, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v46, productUpper, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

end BstLean.Part290
