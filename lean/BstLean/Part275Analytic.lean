import BstLean.Part275Charges

/-! Part 275 (plan part L1), steps 3 and 4.
`node_trace_charge` and `variance_cheby_num` from `8000 ≤ n`, with the charge
`880 / (n - 1)²` (the Part252 value `1e-5` holds from 12225; at 8000 the value is about
`1.38e-5`). The operator cap from a base `n0 ≥ 8000`, with a parameter cap: every
`cap` with `jBound n0² · n0 / (n0 - 321) ≤ cap · 15/16` is valid for `n ≥ n0`.
The cap `127/100` follows from base 8192; the cap `128/100` holds from 8000. -/
namespace BstLean.Part275
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
open BstLean.Part252 (variance_alg_low variance_alg_trace)
variable {n : ℕ}

lemma variance_cheby_num_8000 {m M D B k : ℝ} (hm : 8000 ≤ m) (hM : M = m ^ 2)
    (hD : D = m - 1) (hB : B ≤ m ^ 2 + 2 * m) (hk : 5 / 100 ≤ k) :
    M * B / (k * M * D) ^ 2 ≤ 440 / (m - 1) ^ 2 := by
  have hD0 : 7999 ≤ D := by rw [hD]; linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hk0 : 0 < k := by linarith
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  have h1 : M * B ≤ 11 / 10 * M ^ 2 := by
    rw [hM]
    have hB2 : B ≤ 11 / 10 * m ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hB2 (sq_nonneg m)
    nlinarith
  have hk2 : 25 / 10000 ≤ k ^ 2 := by nlinarith
  rw [← hD]
  have hMD : 0 ≤ M ^ 2 * D ^ 2 := by positivity
  calc M * B * D ^ 2 ≤ 11 / 10 * M ^ 2 * D ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg D)
    _ ≤ 440 * (k ^ 2 * (M ^ 2 * D ^ 2)) := by
        nlinarith [mul_le_mul_of_nonneg_right hk2 hMD]
    _ = 440 * (k * M * D) ^ 2 := by ring

theorem node_trace_charge_8000 (hn : 8000 ≤ n) {wr : WRet n} (hw : windowW wr)
    (hgeo : ∀ g < Js n, 0 ≤ nodeS (mkR wr (0, 0)) g ∧
      3969 / 10000 ≤ 1 - nodeS (mkR wr (0, 0)) g ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g ^ 2 ≤ 61 / 100) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 880 / ((n : ℝ) - 1) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : wr.2 ≠ 0 := sg_wr_ne hn1 hw
  set u : Fin n → ℝ := uHat (mkR wr ((0 : AHid n).1, 0)) with hud
  have hu : normSq u = 1 := BstLean.Part161.normSq_uHat (c := mkR wr ((0 : AHid n).1, 0)) hc
  set M : ℝ := ((mA n : ℕ) : ℝ) with hMd
  set D : ℝ := ((n - 1 : ℕ) : ℝ) with hDd
  have hMe : M = (n : ℝ) ^ 2 := by rw [hMd]; unfold mA; push_cast; ring
  have hDe : D = (n : ℝ) - 1 := by rw [hDd, Nat.cast_sub hn1]; simp
  have hM : 0 < M := by rw [hMe]; positivity
  have hD : 0 < D := by rw [hDe]; linarith
  -- the deterministic inclusion
  set T : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A | ∑ i, sg_phi1 u (A i) < 90 / 100 * M * D / n ∨
    210 / 100 * M * D / n < ∑ i, sg_phi2 u (A i)} with hT
  have hsub : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ⊆ T := by
    rintro A ⟨g, hg, hbad⟩
    set c := mkR wr (A, 0)
    have hc' : c.1.2 ≠ 0 := hc
    obtain ⟨hs0, hq, hqU⟩ := hgeo g hg
    change 0 ≤ nodeS c g at hs0
    change 3969 / 10000 ≤ 1 - nodeS c g ^ 2 at hq
    change 1 - nodeS c g ^ 2 ≤ 61 / 100 at hqU
    set s := nodeS c g
    have hs1 : s ^ 2 ≤ 1 := by linarith
    have hL := sg_vsig2_lower (by omega) c hc' hs0 hs1
    have hU := sg_vsig2_upper (by omega) c hc' hs1
    have e1 : ∑ i, (if 0 ≤ sg_z (uHat c) (A1 c i) then
        normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2 else 0) = ∑ i, sg_phi1 u (A i) := rfl
    have e2 : ∑ i, (normSq (A1 c i) - sg_z (uHat c) (A1 c i) ^ 2) = ∑ i, sg_phi2 u (A i) := rfl
    rw [e1] at hL; rw [e2] at hU
    rcases hbad with h | h
    · left
      by_contra hX
      push_neg at hX
      have := variance_alg_low hM hD hn0 hq hX
      linarith
    · right
      by_contra hY
      push_neg at hY
      have hY0 : 0 ≤ ∑ i, sg_phi2 u (A i) := Finset.sum_nonneg fun i _ => sg_phi2_nonneg hu _
      have := variance_alg_trace (q := 1 - s ^ 2) hM hD hn0 (by linarith) hY
      linarith
  have hTm : MeasurableSet T := by
    have h1 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => ∑ i, sg_phi1 u (A i)) :=
      Finset.measurable_sum _ fun i _ => (sg_meas_phi1 u).comp (measurable_pi_apply i)
    have h2 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => ∑ i, sg_phi2 u (A i)) :=
      Finset.measurable_sum _ fun i _ => (sg_meas_phi2 u).comp (measurable_pi_apply i)
    exact (measurableSet_lt h1 measurable_const).union (measurableSet_lt measurable_const h2)
  set μ := Measure.pi fun _ : Fin (mA n) => stdGauss (Fin n) with hμ
  set γ : ℝ := 2 / (n : ℝ) with hγ
  have hγ0 : 0 < γ := by positivity
  have hsγ : 0 < √γ := Real.sqrt_pos.mpr hγ0
  have hsγ2 : √γ ^ 2 = γ := Real.sq_sqrt hγ0.le
  set f : (Fin (mA n) → Fin n → ℝ) → Matrix (Fin (mA n)) (Fin n) ℝ :=
    fun G => Matrix.of fun i j => √γ * G i j with hfd
  have hf : Measurable f := by
    have hc : Continuous (fun G : Fin (mA n) → Fin n → ℝ => fun i j => √γ * G i j) := by fun_prop
    exact hc.measurable
  have hG : gaussMat (mA n) n γ = μ.map f := BstLean.Part167.gaussMat_rows γ
  have hrow : ∀ G i, f G i = √γ • G i := fun G i => by funext j; rfl
  obtain ⟨-, i1sq, b1⟩ := sg_int_bdd (sg_meas_phi1 u) (sg_phi1_nonneg hu) (sg_phi1_le hu)
  obtain ⟨-, i2sq, b2⟩ := sg_int_bdd (sg_meas_phi2 u) (sg_phi2_nonneg hu) (sg_phi2_le u)
  have hE1 := sg_int_phi1 hu
  have hE2 := (sg_int_phi2 hu).2
  set t₁ : ℝ := 5 / 100 * M * D
  set t₂ : ℝ := 5 / 100 * M * D
  have ht₁ : 0 < t₁ := by positivity
  have ht₂ : 0 < t₂ := by positivity
  have hpre : f ⁻¹' T ⊆ {G | t₁ ≤ |∑ i, sg_phi1 u (G i) - (mA n : ℕ) * ∫ g, sg_phi1 u g ∂stdGauss (Fin n)|} ∪
      {G | t₂ ≤ |∑ i, sg_phi2 u (G i) - (mA n : ℕ) * ∫ g, sg_phi2 u g ∂stdGauss (Fin n)|} := by
    intro G hGT
    simp only [Set.mem_preimage, hT, Set.mem_setOf_eq, hrow] at hGT
    simp_rw [sg_phi1_smul hsγ, sg_phi2_smul, hsγ2, ← Finset.mul_sum] at hGT
    rcases hGT with h | h
    · left
      simp only [Set.mem_setOf_eq]
      have hS : ∑ i, sg_phi1 u (G i) < 45 / 100 * M * D := by
        rw [hγ] at h
        have e : 90 / 100 * M * D / n = 2 / n * (45 / 100 * M * D) := by field_simp; ring
        rw [e] at h
        exact lt_of_mul_lt_mul_left h (by positivity)
      have hm : M * (D / 2) ≤ M * ∫ g, sg_phi1 u g ∂stdGauss (Fin n) :=
        mul_le_mul_of_nonneg_left (by rw [hDe]; exact hE1) hM.le
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      show t₁ ≤ M * ∫ g, sg_phi1 u g ∂stdGauss (Fin n) - ∑ i, sg_phi1 u (G i)
      have et : t₁ = 5 / 100 * M * D := rfl
      have e2 : M * (D / 2) = 50 / 100 * M * D := by ring
      linarith
    · right
      simp only [Set.mem_setOf_eq]
      have hS : 105 / 100 * M * D < ∑ i, sg_phi2 u (G i) := by
        rw [hγ] at h
        have e : 210 / 100 * M * D / n = 2 / n * (105 / 100 * M * D) := by field_simp; ring
        rw [e] at h
        exact lt_of_mul_lt_mul_left h (by positivity)
      refine le_trans ?_ (le_abs_self _)
      show t₂ ≤ ∑ i, sg_phi2 u (G i) - M * ∫ g, sg_phi2 u g ∂stdGauss (Fin n)
      rw [hE2, ← hDe]
      have et : t₂ = 5 / 100 * M * D := rfl
      linarith
  have hc1 := sg_cheb (m := mA n) (sg_meas_phi1 u) i1sq ht₁
  have hc2 := sg_cheb (m := mA n) (sg_meas_phi2 u) i2sq ht₂
  have hn1' := variance_cheby_num_8000 hnR hMe hDe b1 (k := 5 / 100) le_rfl
  have hn2' := variance_cheby_num_8000 hnR hMe hDe b2 (k := 5 / 100) (by norm_num)
  have hEμ : gaussMat (mA n) n γ {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤
      ENNReal.ofReal (880 / ((n : ℝ) - 1) ^ 2) := by
    refine (measure_mono hsub).trans ?_
    rw [hG, Measure.map_apply hf hTm]
    refine (measure_mono hpre).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add hc1 hc2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : ((mA n : ℕ) : ℝ) * (∫ g, sg_phi1 u g ^ 2 ∂stdGauss (Fin n)) / t₁ ^ 2 =
        M * (∫ g, sg_phi1 u g ^ 2 ∂stdGauss (Fin n)) / (5 / 100 * M * D) ^ 2 := rfl
    have e2 : ((mA n : ℕ) : ℝ) * (∫ g, sg_phi2 u g ^ 2 ∂stdGauss (Fin n)) / t₂ ^ 2 =
        M * (∫ g, sg_phi2 u g ^ 2 ∂stdGauss (Fin n)) / (5 / 100 * M * D) ^ 2 := rfl
    rw [e1, e2]
    have hsum : (440 : ℝ) / ((n : ℝ) - 1) ^ 2 + 440 / ((n : ℝ) - 1) ^ 2 =
        880 / ((n : ℝ) - 1) ^ 2 := by ring
    rw [← hsum]
    exact add_le_add hn1' hn2'
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hEμ

/-- The Part252 value `1e-5` of the node-trace charge, from 12225. -/
theorem nodeTraceCharge_le_part252 (hn : 12225 ≤ n) : 880 / ((n : ℝ) - 1) ^ 2 ≤ 1 / 10 ^ 5 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

/-- The node-trace charge is at most `1.38e-5` from 8000. -/
theorem nodeTraceCharge_le_8000 (hn : 8000 ≤ n) : 880 / ((n : ℝ) - 1) ^ 2 ≤ 138 / 10 ^ 7 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

/-! ### The operator cap with a parameter cap -/

open BstLean.Part153 BstLean.Part215 BstLean.Part252 in
theorem operator_cap_base {n0 n : ℕ} (h0 : 8000 ≤ n0) (hn : n0 ≤ n) {cap : ℝ}
    (hcap0 : 0 ≤ cap)
    (hcap : BstLean.Part273.jBound n0 ^ 2 * n0 / ((n0 : ℝ) - 321) ≤ cap * (15 / 16))
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    BstLean.Part219.operatorAllowance c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 2
      ≤ cap := by
  rw [← operatorCoefficient_eq]
  have h0r : (8000 : ℝ) ≤ n0 := by exact_mod_cast h0
  have hnr : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : 0 < (n0 : ℝ) - 321 := by linarith
  have hd : 0 < (n : ℝ) - 321 := by linarith
  let j := jS n 160 (6 / 1000)
  let I := ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 160 ∂stdGauss (Fin n)
  have hI : 0 ≤ I := integral_nonneg fun ξ => by positivity
  have hj0 : 0 ≤ j := jS_nonneg _ _ _
  have hj : j ≤ BstLean.Part273.jBound n0 := BstLean.Part273.jS_le_jBound h0 hn
  have hinv : τ ^ 320 * I ≤ ((n : ℝ) - 321)⁻¹ ^ 160 := by
    refine (invMoment_le (p := 160) (by omega) c hτ).2.trans ?_
    calc
      (∏ i ∈ Finset.range 160, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹)
          ≤ ∏ _i ∈ Finset.range 160, ((n : ℝ) - 321)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
        · have hi' : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
          exact inv_nonneg.mpr (by linarith)
        · have hi' : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
          exact inv_anti₀ hd (by linarith)
      _ = _ := by simp
  have he : operatorCoefficient c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 160 =
      20000 * ((n : ℝ) * j ^ 2) ^ 160 * (τ ^ 320 * I) := by
    rw [operatorCoefficient_power]
    unfold operatorBudget
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (sqrt_nonneg _) hj0) 320),
      ENNReal.toReal_ofReal hI]
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
    have hs : (√(n : ℝ) * j) ^ 320 = ((n : ℝ) * j ^ 2) ^ 160 := by
      rw [show (320 : ℕ) = 2 * 160 by norm_num, pow_mul, mul_pow, sq_sqrt (by positivity)]
    change τ ^ 320 * (((√(n : ℝ) * j) ^ 320 * I) / (1 / 20000)) = _
    rw [hs]
    ring
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hB0 : 0 ≤ BstLean.Part273.jBound n0 ^ 2 := sq_nonneg _
  have hcap' : BstLean.Part273.jBound n0 ^ 2 * n0 ≤ cap * (15 / 16) * ((n0 : ℝ) - 321) :=
    (div_le_iff₀ hd0).mp hcap
  have hratio : (n : ℝ) * j ^ 2 / ((n : ℝ) - 321) ≤ cap * (15 / 16) := by
    rw [div_le_iff₀ hd]
    have e1 : (n : ℝ) * j ^ 2 ≤ n * BstLean.Part273.jBound n0 ^ 2 :=
      mul_le_mul_of_nonneg_left hj2 (by positivity)
    have e2 : (n0 : ℝ) * (n * BstLean.Part273.jBound n0 ^ 2) ≤
        n0 * (cap * (15 / 16) * ((n : ℝ) - 321)) := by
      have k1 : (n : ℝ) * (BstLean.Part273.jBound n0 ^ 2 * n0) ≤
          n * (cap * (15 / 16) * ((n0 : ℝ) - 321)) :=
        mul_le_mul_of_nonneg_left hcap' (by positivity)
      have k2 : cap * (15 / 16) * ((n : ℝ) * ((n0 : ℝ) - 321)) ≤
          cap * (15 / 16) * ((n0 : ℝ) * ((n : ℝ) - 321)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      nlinarith
    have e3 : (n : ℝ) * BstLean.Part273.jBound n0 ^ 2 ≤ cap * (15 / 16) * ((n : ℝ) - 321) :=
      le_of_mul_le_mul_left e2 (by linarith)
    linarith
  have hpow : operatorCoefficient c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 160
      ≤ cap ^ 160 := by
    rw [he]
    calc
      20000 * ((n : ℝ) * j ^ 2) ^ 160 * (τ ^ 320 * I)
          ≤ 20000 * ((n : ℝ) * j ^ 2) ^ 160 * ((n : ℝ) - 321)⁻¹ ^ 160 :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg (by norm_num)
          (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg j)) 160))
      _ = 20000 * ((n : ℝ) * j ^ 2 / ((n : ℝ) - 321)) ^ 160 := by
        rw [div_eq_mul_inv, mul_pow]
        ring
      _ ≤ 20000 * (cap * (15 / 16) : ℝ) ^ 160 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio 160) (by norm_num)
      _ = (20000 * (15 / 16 : ℝ) ^ 160) * cap ^ 160 := by ring
      _ ≤ 1 * cap ^ 160 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hcap0 160)
      _ = cap ^ 160 := one_mul _
  exact le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) hcap0 hpow

theorem jBound_8192_le : BstLean.Part273.jBound 8192 ≤ 106888 / 100000 := by
  refine (BstLean.Part273.jBound_le_of_sqrt (s := 905 / 10) (by norm_num)
    (Real.le_sqrt_of_sq_le (by norm_num))).trans ?_
  norm_num

theorem cap_guard_8192 :
    BstLean.Part273.jBound 8192 ^ 2 * ((8192 : ℕ) : ℝ) / (((8192 : ℕ) : ℝ) - 321) ≤
      (127 / 100) * (15 / 16) := by
  have hj0 := BstLean.Part273.jBound_nonneg 8192
  have hj2 := pow_le_pow_left₀ hj0 jBound_8192_le 2
  rw [div_le_iff₀ (by norm_num)]
  norm_num at hj2 ⊢
  linarith

theorem cap_guard_8000 :
    BstLean.Part273.jBound 8000 ^ 2 * ((8000 : ℕ) : ℝ) / (((8000 : ℕ) : ℝ) - 321) ≤
      (128 / 100) * (15 / 16) := by
  have hj0 := BstLean.Part273.jBound_nonneg 8000
  have hj2 := pow_le_pow_left₀ hj0 BstLean.Part273.jBound_8000_le 2
  rw [div_le_iff₀ (by norm_num)]
  norm_num at hj2 ⊢
  linarith

/-- The Part252 operator cap `127/100` is the base-8192 instance. -/
theorem operator_cap_8192 {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    BstLean.Part219.operatorAllowance c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 2
      ≤ 127 / 100 :=
  operator_cap_base (by norm_num) hn (by norm_num) cap_guard_8192 c hτ

/-- From 8000 the operator cap is `128/100`. -/
theorem operator_cap_8000 {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    BstLean.Part219.operatorAllowance c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 2
      ≤ 128 / 100 :=
  operator_cap_base (le_refl 8000) hn (by norm_num) cap_guard_8000 c hτ

open BstLean.Part215 in
/-- The fourth-moment event on the operator event, from 8000 (cap `128/100 ≤ 13/10`). -/
theorem fourth_on_operator_event_8000 {n : ℕ} (hn : 8000 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {a : BstLean.Part215.AgentPair n}
    (ha : a ∈ operatorEvent c τ (6 / 1000) (ENNReal.ofReal (1 / 20000))) :
    ((c, τ), a) ∈ BstLean.Part245.MomentM12 n :=
  BstLean.Part252.fourth_of_operator_cap c τ (6 / 1000) (by norm_num) ha
    ((operator_cap_8000 hn c hτ).trans (by norm_num))

end BstLean.Part275
