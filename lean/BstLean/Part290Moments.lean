import BstLean.Part290Bounds
import BstLean.Part290Scale

namespace BstLean.Part290
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218 BstLean.Part227
open BstLean.Part228 BstLean.Part250
open BstLean.Part271.R3 (angularMomentCore angularMomentCore_formula j2Core j4Core
  jbCore aCore bCore offsetCore ba1Core ba2Core traceCore diagonalCore covariancePaymentCore normCore)
theorem moment_0 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 0) 1 1 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v1 : ℝ := 1/v0
  have h1 : Bounds v1 1 1 := Bounds.inv h0 (by norm_num)
  let v2 : ℝ := v0/v0
  have h2 : Bounds v2 1 1 := bounds_div h0 h1 (by norm_num)
  convert h2 using 1 <;>
    simp only [v0, v2, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_1 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 1) 1 1 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v4 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h4 : Bounds v4 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v5 : ℝ := v4+v0
  have h5 : Bounds v5 1 1 := Bounds.add h4 h0 (by norm_num)
  let v6 : ℝ := v0*v5
  have h6 : Bounds v6 1 1 := Bounds.mul h0 h5 (by norm_num)
  let v7 : ℝ := 1/v6
  have h7 : Bounds v7 1 1 := Bounds.inv h6 (by norm_num)
  let v8 : ℝ := v0/v6
  have h8 : Bounds v8 1 1 := bounds_div h0 h7 (by norm_num)
  convert h8 using 1 <;>
    simp only [v0, v3, v4, v5, v6, v8, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_2 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 2) (299962504686914135733033369/100000000000000000000000000) 3 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v9 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h9 : Bounds v9 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v10 : ℝ := v9+v0
  have h10 : Bounds v10 1 1 := Bounds.add h9 h0 (by norm_num)
  let v11 : ℝ := v0*v10
  have h11 : Bounds v11 1 1 := Bounds.mul h0 h10 (by norm_num)
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v13 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h13 : Bounds v13 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v14 : ℝ := v13+v0
  have h14 : Bounds v14 1 (8001/8000) := Bounds.add h13 h0 (by norm_num)
  let v15 : ℝ := v11*v14
  have h15 : Bounds v15 1 (8001/8000) := Bounds.mul h11 h14 (by norm_num)
  let v16 : ℝ := 3
  have h16 : Bounds v16 3 3 := Bounds.point _
  let v17 : ℝ := 1/v15
  have h17 : Bounds v17 (99987501562304711911011123/100000000000000000000000000) 1 := Bounds.inv h15 (by norm_num)
  let v18 : ℝ := v16/v15
  have h18 : Bounds v18 (299962504686914135733033369/100000000000000000000000000) 3 := bounds_div h16 h17 (by norm_num)
  convert h18 using 1 <;>
    simp only [v0, v3, v9, v10, v11, v12, v13, v14, v15, v16, v18, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_3 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 3) (37485941600464150928896947/2500000000000000000000000) 15 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v19 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h19 : Bounds v19 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v20 : ℝ := v19+v0
  have h20 : Bounds v20 1 1 := Bounds.add h19 h0 (by norm_num)
  let v21 : ℝ := v0*v20
  have h21 : Bounds v21 1 1 := Bounds.mul h0 h20 (by norm_num)
  let v22 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h22 : Bounds v22 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v23 : ℝ := v22+v0
  have h23 : Bounds v23 1 (8001/8000) := Bounds.add h22 h0 (by norm_num)
  let v24 : ℝ := v21*v23
  have h24 : Bounds v24 1 (8001/8000) := Bounds.mul h21 h23 (by norm_num)
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v26 : ℝ := (1/((2*n : ℕ) : ℝ))*v25
  have h26 : Bounds v26 0 (1/4000) := Bounds.mul (inverse_dimension ha) h25 (by norm_num)
  let v27 : ℝ := v26+v0
  have h27 : Bounds v27 1 (4001/4000) := Bounds.add h26 h0 (by norm_num)
  let v28 : ℝ := v24*v27
  have h28 : Bounds v28 1 (32012001/32000000) := Bounds.mul h24 h27 (by norm_num)
  let v29 : ℝ := 15
  have h29 : Bounds v29 15 15 := Bounds.point _
  let v30 : ℝ := 1/v28
  have h30 : Bounds v30 (12495313866821383642965649/12500000000000000000000000) 1 := Bounds.inv h28 (by norm_num)
  let v31 : ℝ := v29/v28
  have h31 : Bounds v31 (37485941600464150928896947/2500000000000000000000000) 15 := bounds_div h29 h30 (by norm_num)
  convert h31 using 1 <;>
    simp only [v0, v3, v12, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v31, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_4 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 4) (104921290997175681720266351/1000000000000000000000000) 105 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v32 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h32 : Bounds v32 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v33 : ℝ := v32+v0
  have h33 : Bounds v33 1 1 := Bounds.add h32 h0 (by norm_num)
  let v34 : ℝ := v0*v33
  have h34 : Bounds v34 1 1 := Bounds.mul h0 h33 (by norm_num)
  let v35 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h35 : Bounds v35 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v36 : ℝ := v35+v0
  have h36 : Bounds v36 1 (8001/8000) := Bounds.add h35 h0 (by norm_num)
  let v37 : ℝ := v34*v36
  have h37 : Bounds v37 1 (8001/8000) := Bounds.mul h34 h36 (by norm_num)
  let v38 : ℝ := (1/((2*n : ℕ) : ℝ))*v25
  have h38 : Bounds v38 0 (1/4000) := Bounds.mul (inverse_dimension ha) h25 (by norm_num)
  let v39 : ℝ := v38+v0
  have h39 : Bounds v39 1 (4001/4000) := Bounds.add h38 h0 (by norm_num)
  let v40 : ℝ := v37*v39
  have h40 : Bounds v40 1 (32012001/32000000) := Bounds.mul h37 h39 (by norm_num)
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v42 : ℝ := (1/((2*n : ℕ) : ℝ))*v41
  have h42 : Bounds v42 0 (3/8000) := Bounds.mul (inverse_dimension ha) h41 (by norm_num)
  let v43 : ℝ := v42+v0
  have h43 : Bounds v43 1 (8003/8000) := Bounds.add h42 h0 (by norm_num)
  let v44 : ℝ := v40*v43
  have h44 : Bounds v44 1 (256192044003/256000000000) := Bounds.mul h40 h43 (by norm_num)
  let v45 : ℝ := 105
  have h45 : Bounds v45 105 105 := Bounds.point _
  let v46 : ℝ := 1/v44
  have h46 : Bounds v46 (49962519522464610342983977/50000000000000000000000000) 1 := Bounds.inv h44 (by norm_num)
  let v47 : ℝ := v45/v44
  have h47 : Bounds v47 (104921290997175681720266351/1000000000000000000000000) 105 := bounds_div h45 h46 (by norm_num)
  convert h47 using 1 <;>
    simp only [v0, v3, v12, v25, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v47, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_5 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 5) (94381970912002112491993719/100000000000000000000000) 945 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v48 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h48 : Bounds v48 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v49 : ℝ := v48+v0
  have h49 : Bounds v49 1 1 := Bounds.add h48 h0 (by norm_num)
  let v50 : ℝ := v0*v49
  have h50 : Bounds v50 1 1 := Bounds.mul h0 h49 (by norm_num)
  let v51 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h51 : Bounds v51 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v52 : ℝ := v51+v0
  have h52 : Bounds v52 1 (8001/8000) := Bounds.add h51 h0 (by norm_num)
  let v53 : ℝ := v50*v52
  have h53 : Bounds v53 1 (8001/8000) := Bounds.mul h50 h52 (by norm_num)
  let v54 : ℝ := (1/((2*n : ℕ) : ℝ))*v25
  have h54 : Bounds v54 0 (1/4000) := Bounds.mul (inverse_dimension ha) h25 (by norm_num)
  let v55 : ℝ := v54+v0
  have h55 : Bounds v55 1 (4001/4000) := Bounds.add h54 h0 (by norm_num)
  let v56 : ℝ := v53*v55
  have h56 : Bounds v56 1 (32012001/32000000) := Bounds.mul h53 h55 (by norm_num)
  let v57 : ℝ := (1/((2*n : ℕ) : ℝ))*v41
  have h57 : Bounds v57 0 (3/8000) := Bounds.mul (inverse_dimension ha) h41 (by norm_num)
  let v58 : ℝ := v57+v0
  have h58 : Bounds v58 1 (8003/8000) := Bounds.add h57 h0 (by norm_num)
  let v59 : ℝ := v56*v58
  have h59 : Bounds v59 1 (256192044003/256000000000) := Bounds.mul h56 h58 (by norm_num)
  let v60 : ℝ := 8
  have h60 : Bounds v60 8 8 := Bounds.point _
  let v61 : ℝ := (1/((2*n : ℕ) : ℝ))*v60
  have h61 : Bounds v61 0 (1/2000) := Bounds.mul (inverse_dimension ha) h60 (by norm_num)
  let v62 : ℝ := v61+v0
  have h62 : Bounds v62 1 (2001/2000) := Bounds.add h61 h0 (by norm_num)
  let v63 : ℝ := v59*v62
  have h63 : Bounds v63 1 (512640280050003/512000000000000) := Bounds.mul h59 h62 (by norm_num)
  let v64 : ℝ := 945
  have h64 : Bounds v64 945 945 := Bounds.point _
  let v65 : ℝ := 1/v63
  have h65 : Bounds v65 (799000811953457036969259/800000000000000000000000) 1 := Bounds.inv h63 (by norm_num)
  let v66 : ℝ := v64/v63
  have h66 : Bounds v66 (94381970912002112491993719/100000000000000000000000) 945 := bounds_div h64 h65 (by norm_num)
  convert h66 using 1 <;>
    simp only [v0, v3, v12, v25, v41, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v66, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_6 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 6) (20751064185524511928283441/2000000000000000000000) 10395 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v60 : ℝ := 8
  have h60 : Bounds v60 8 8 := Bounds.point _
  let v67 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h67 : Bounds v67 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v68 : ℝ := v67+v0
  have h68 : Bounds v68 1 1 := Bounds.add h67 h0 (by norm_num)
  let v69 : ℝ := v0*v68
  have h69 : Bounds v69 1 1 := Bounds.mul h0 h68 (by norm_num)
  let v70 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h70 : Bounds v70 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v71 : ℝ := v70+v0
  have h71 : Bounds v71 1 (8001/8000) := Bounds.add h70 h0 (by norm_num)
  let v72 : ℝ := v69*v71
  have h72 : Bounds v72 1 (8001/8000) := Bounds.mul h69 h71 (by norm_num)
  let v73 : ℝ := (1/((2*n : ℕ) : ℝ))*v25
  have h73 : Bounds v73 0 (1/4000) := Bounds.mul (inverse_dimension ha) h25 (by norm_num)
  let v74 : ℝ := v73+v0
  have h74 : Bounds v74 1 (4001/4000) := Bounds.add h73 h0 (by norm_num)
  let v75 : ℝ := v72*v74
  have h75 : Bounds v75 1 (32012001/32000000) := Bounds.mul h72 h74 (by norm_num)
  let v76 : ℝ := (1/((2*n : ℕ) : ℝ))*v41
  have h76 : Bounds v76 0 (3/8000) := Bounds.mul (inverse_dimension ha) h41 (by norm_num)
  let v77 : ℝ := v76+v0
  have h77 : Bounds v77 1 (8003/8000) := Bounds.add h76 h0 (by norm_num)
  let v78 : ℝ := v75*v77
  have h78 : Bounds v78 1 (256192044003/256000000000) := Bounds.mul h75 h77 (by norm_num)
  let v79 : ℝ := (1/((2*n : ℕ) : ℝ))*v60
  have h79 : Bounds v79 0 (1/2000) := Bounds.mul (inverse_dimension ha) h60 (by norm_num)
  let v80 : ℝ := v79+v0
  have h80 : Bounds v80 1 (2001/2000) := Bounds.add h79 h0 (by norm_num)
  let v81 : ℝ := v78*v80
  have h81 : Bounds v81 1 (512640280050003/512000000000000) := Bounds.mul h78 h80 (by norm_num)
  let v82 : ℝ := 10
  have h82 : Bounds v82 10 10 := Bounds.point _
  let v83 : ℝ := (1/((2*n : ℕ) : ℝ))*v82
  have h83 : Bounds v83 0 (1/1600) := Bounds.mul (inverse_dimension ha) h82 (by norm_num)
  let v84 : ℝ := v83+v0
  have h84 : Bounds v84 1 (1601/1600) := Bounds.add h83 h0 (by norm_num)
  let v85 : ℝ := v81*v84
  have h85 : Bounds v85 1 (50093816428226001159667969/50000000000000000000000000) := Bounds.mul h81 h84 (by norm_num)
  let v86 : ℝ := 10395
  have h86 : Bounds v86 10395 10395 := Bounds.point _
  let v87 : ℝ := 1/v85
  have h87 : Bounds v87 (49906359272545723733245409/50000000000000000000000000) 1 := Bounds.inv h85 (by norm_num)
  let v88 : ℝ := v86/v85
  have h88 : Bounds v88 (20751064185524511928283441/2000000000000000000000) 10395 := bounds_div h86 h87 (by norm_num)
  convert h88 using 1 <;>
    simp only [v0, v3, v12, v25, v41, v60, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v88, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_7 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 7) (134780831582222660538438537/1000000000000000000000) 135135 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v60 : ℝ := 8
  have h60 : Bounds v60 8 8 := Bounds.point _
  let v82 : ℝ := 10
  have h82 : Bounds v82 10 10 := Bounds.point _
  let v89 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h89 : Bounds v89 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v90 : ℝ := v89+v0
  have h90 : Bounds v90 1 1 := Bounds.add h89 h0 (by norm_num)
  let v91 : ℝ := v0*v90
  have h91 : Bounds v91 1 1 := Bounds.mul h0 h90 (by norm_num)
  let v92 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h92 : Bounds v92 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v93 : ℝ := v92+v0
  have h93 : Bounds v93 1 (8001/8000) := Bounds.add h92 h0 (by norm_num)
  let v94 : ℝ := v91*v93
  have h94 : Bounds v94 1 (8001/8000) := Bounds.mul h91 h93 (by norm_num)
  let v95 : ℝ := (1/((2*n : ℕ) : ℝ))*v25
  have h95 : Bounds v95 0 (1/4000) := Bounds.mul (inverse_dimension ha) h25 (by norm_num)
  let v96 : ℝ := v95+v0
  have h96 : Bounds v96 1 (4001/4000) := Bounds.add h95 h0 (by norm_num)
  let v97 : ℝ := v94*v96
  have h97 : Bounds v97 1 (32012001/32000000) := Bounds.mul h94 h96 (by norm_num)
  let v98 : ℝ := (1/((2*n : ℕ) : ℝ))*v41
  have h98 : Bounds v98 0 (3/8000) := Bounds.mul (inverse_dimension ha) h41 (by norm_num)
  let v99 : ℝ := v98+v0
  have h99 : Bounds v99 1 (8003/8000) := Bounds.add h98 h0 (by norm_num)
  let v100 : ℝ := v97*v99
  have h100 : Bounds v100 1 (256192044003/256000000000) := Bounds.mul h97 h99 (by norm_num)
  let v101 : ℝ := (1/((2*n : ℕ) : ℝ))*v60
  have h101 : Bounds v101 0 (1/2000) := Bounds.mul (inverse_dimension ha) h60 (by norm_num)
  let v102 : ℝ := v101+v0
  have h102 : Bounds v102 1 (2001/2000) := Bounds.add h101 h0 (by norm_num)
  let v103 : ℝ := v100*v102
  have h103 : Bounds v103 1 (512640280050003/512000000000000) := Bounds.mul h100 h102 (by norm_num)
  let v104 : ℝ := (1/((2*n : ℕ) : ℝ))*v82
  have h104 : Bounds v104 0 (1/1600) := Bounds.mul (inverse_dimension ha) h82 (by norm_num)
  let v105 : ℝ := v104+v0
  have h105 : Bounds v105 1 (1601/1600) := Bounds.add h104 h0 (by norm_num)
  let v106 : ℝ := v103*v105
  have h106 : Bounds v106 1 (50093816428226001159667969/50000000000000000000000000) := Bounds.mul h103 h105 (by norm_num)
  let v107 : ℝ := 12
  have h107 : Bounds v107 12 12 := Bounds.point _
  let v108 : ℝ := (1/((2*n : ℕ) : ℝ))*v107
  have h108 : Bounds v108 0 (3/4000) := Bounds.mul (inverse_dimension ha) h107 (by norm_num)
  let v109 : ℝ := v108+v0
  have h109 : Bounds v109 1 (4003/4000) := Bounds.add h108 h0 (by norm_num)
  let v110 : ℝ := v106*v109
  have h110 : Bounds v110 1 (1253284669763679266513443/1250000000000000000000000) := Bounds.mul h106 h109 (by norm_num)
  let v111 : ℝ := 135135
  have h111 : Bounds v111 135135 135135 := Bounds.point _
  let v112 : ℝ := 1/v110
  have h112 : Bounds v112 (24934478777189969389580519/25000000000000000000000000) 1 := Bounds.inv h110 (by norm_num)
  let v113 : ℝ := v111/v110
  have h113 : Bounds v113 (134780831582222660538438537/1000000000000000000000) 135135 := bounds_div h111 h112 (by norm_num)
  convert h113 using 1 <;>
    simp only [v0, v3, v12, v25, v41, v60, v82, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v113, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

theorem moment_8 {n : ℕ} (ha : 8000 ≤ n) :
    Bounds (angularMomentCore (2*n) 8) (100997251091961529065896243/50000000000000000000) 2027025 := by
  have hN : 0 < ((2*n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*n by omega)
  let v0 : ℝ := 1
  have h0 : Bounds v0 1 1 := Bounds.point _
  let v3 : ℝ := 0
  have h3 : Bounds v3 0 0 := Bounds.point _
  let v12 : ℝ := 2
  have h12 : Bounds v12 2 2 := Bounds.point _
  let v25 : ℝ := 4
  have h25 : Bounds v25 4 4 := Bounds.point _
  let v41 : ℝ := 6
  have h41 : Bounds v41 6 6 := Bounds.point _
  let v60 : ℝ := 8
  have h60 : Bounds v60 8 8 := Bounds.point _
  let v82 : ℝ := 10
  have h82 : Bounds v82 10 10 := Bounds.point _
  let v107 : ℝ := 12
  have h107 : Bounds v107 12 12 := Bounds.point _
  let v114 : ℝ := (1/((2*n : ℕ) : ℝ))*v3
  have h114 : Bounds v114 0 0 := Bounds.mul (inverse_dimension ha) h3 (by norm_num)
  let v115 : ℝ := v114+v0
  have h115 : Bounds v115 1 1 := Bounds.add h114 h0 (by norm_num)
  let v116 : ℝ := v0*v115
  have h116 : Bounds v116 1 1 := Bounds.mul h0 h115 (by norm_num)
  let v117 : ℝ := (1/((2*n : ℕ) : ℝ))*v12
  have h117 : Bounds v117 0 (1/8000) := Bounds.mul (inverse_dimension ha) h12 (by norm_num)
  let v118 : ℝ := v117+v0
  have h118 : Bounds v118 1 (8001/8000) := Bounds.add h117 h0 (by norm_num)
  let v119 : ℝ := v116*v118
  have h119 : Bounds v119 1 (8001/8000) := Bounds.mul h116 h118 (by norm_num)
  let v120 : ℝ := (1/((2*n : ℕ) : ℝ))*v25
  have h120 : Bounds v120 0 (1/4000) := Bounds.mul (inverse_dimension ha) h25 (by norm_num)
  let v121 : ℝ := v120+v0
  have h121 : Bounds v121 1 (4001/4000) := Bounds.add h120 h0 (by norm_num)
  let v122 : ℝ := v119*v121
  have h122 : Bounds v122 1 (32012001/32000000) := Bounds.mul h119 h121 (by norm_num)
  let v123 : ℝ := (1/((2*n : ℕ) : ℝ))*v41
  have h123 : Bounds v123 0 (3/8000) := Bounds.mul (inverse_dimension ha) h41 (by norm_num)
  let v124 : ℝ := v123+v0
  have h124 : Bounds v124 1 (8003/8000) := Bounds.add h123 h0 (by norm_num)
  let v125 : ℝ := v122*v124
  have h125 : Bounds v125 1 (256192044003/256000000000) := Bounds.mul h122 h124 (by norm_num)
  let v126 : ℝ := (1/((2*n : ℕ) : ℝ))*v60
  have h126 : Bounds v126 0 (1/2000) := Bounds.mul (inverse_dimension ha) h60 (by norm_num)
  let v127 : ℝ := v126+v0
  have h127 : Bounds v127 1 (2001/2000) := Bounds.add h126 h0 (by norm_num)
  let v128 : ℝ := v125*v127
  have h128 : Bounds v128 1 (512640280050003/512000000000000) := Bounds.mul h125 h127 (by norm_num)
  let v129 : ℝ := (1/((2*n : ℕ) : ℝ))*v82
  have h129 : Bounds v129 0 (1/1600) := Bounds.mul (inverse_dimension ha) h82 (by norm_num)
  let v130 : ℝ := v129+v0
  have h130 : Bounds v130 1 (1601/1600) := Bounds.add h129 h0 (by norm_num)
  let v131 : ℝ := v128*v130
  have h131 : Bounds v131 1 (50093816428226001159667969/50000000000000000000000000) := Bounds.mul h128 h130 (by norm_num)
  let v132 : ℝ := (1/((2*n : ℕ) : ℝ))*v107
  have h132 : Bounds v132 0 (3/4000) := Bounds.mul (inverse_dimension ha) h107 (by norm_num)
  let v133 : ℝ := v132+v0
  have h133 : Bounds v133 1 (4003/4000) := Bounds.add h132 h0 (by norm_num)
  let v134 : ℝ := v131*v133
  have h134 : Bounds v134 1 (1253284669763679266513443/1250000000000000000000000) := Bounds.mul h131 h133 (by norm_num)
  let v135 : ℝ := 14
  have h135 : Bounds v135 14 14 := Bounds.point _
  let v136 : ℝ := (1/((2*n : ℕ) : ℝ))*v135
  have h136 : Bounds v136 0 (7/8000) := Bounds.mul (inverse_dimension ha) h135 (by norm_num)
  let v137 : ℝ := v136+v0
  have h137 : Bounds v137 1 (8007/8000) := Bounds.add h136 h0 (by norm_num)
  let v138 : ℝ := v134*v137
  have h138 : Bounds v138 1 (50175251753988899434865691/50000000000000000000000000) := Bounds.mul h134 h137 (by norm_num)
  let v139 : ℝ := 2027025
  have h139 : Bounds v139 2027025 2027025 := Bounds.point _
  let v140 : ℝ := 1/v138
  have h140 : Bounds v140 (24912680182030692533613607/25000000000000000000000000) 1 := Bounds.inv h138 (by norm_num)
  let v141 : ℝ := v139/v138
  have h141 : Bounds v141 (100997251091961529065896243/50000000000000000000) 2027025 := bounds_div h139 h140 (by norm_num)
  convert h141 using 1 <;>
    simp only [v0, v3, v12, v25, v41, v60, v82, v107, v114, v115, v116, v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134, v135, v136, v137, v138, v139, v141, angularMomentCore_formula hN, BstLean.Part29.gaussMom, Nat.cast_mul, Nat.cast_ofNat] <;>
    norm_num [Finset.sum_range_succ, Finset.prod_range_succ, Nat.doubleFactorial,
      Nat.choose] <;> ring <;> simp

end BstLean.Part290
