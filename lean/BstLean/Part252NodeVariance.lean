import BstLean.Part172Sig
import BstLean.Part252TableNum

/-! A first-layer variance payment from dimension 12225. The bulk geometry
remains explicit and introduces no union over nodes. -/
namespace BstLean.Part252
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg mA gaussMat)
open BstLean.Part157 (Ret WRet AHid Js)
open BstLean.Part161 (uHat)
open BstLean.Part169 (A1 vsig2 nodeS)
open BstLean.Part170 (windowW mkR)
open BstLean.Part172
variable {n : ℕ}

lemma variance_alg_low {M D q X m : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hm : 0 < m) (hq : 3969 / 10000 ≤ q)
    (hX : 90 / 100 * M * D / m ≤ X) :
    17 / (100 * m) ≤ 2 / M * (q / (4 * D)) * X := by
  have e : 2 / M * (q / (4 * D)) * X = q * X / (2 * M * D) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_iff₀ hm] at hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ 90 / 100 * M * D := by positivity
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (mul_nonneg hX0 hm.le)]

lemma variance_alg_up {M D q Y m : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hm : 0 < m) (hq0 : 0 ≤ q) (hq : q ≤ 61 / 100) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 210 / 100 * M * D / m) :
    2 / M * (q / D) * Y ≤ 26 / (10 * m) := by
  have e : 2 / M * (q / D) * Y = 2 * q * Y / (M * D) := by field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [le_div_iff₀ hm] at hY
  nlinarith [mul_le_mul hq hY (by positivity) (by norm_num : (0 : ℝ) ≤ 61 / 100),
    mul_nonneg hq0 (mul_nonneg hY0 hm.le)]

lemma variance_alg_trace {M D q Y m : ℝ} (hM : 0 < M) (hD : 0 < D)
    (hm : 0 < m) (hq0 : 0 ≤ q)
    (hY : Y ≤ 210 / 100 * M * D / m) :
    2 / M * (q / D) * Y ≤ 42 / (10 * m) * q := by
  calc
    _ ≤ 2 / M * (q / D) * (210 / 100 * M * D / m) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    _ = _ := by field_simp; ring

lemma variance_cheby_num {m M D B k : ℝ} (hm : 12225 ≤ m) (hM : M = m ^ 2)
    (hD : D = m - 1) (hB : B ≤ m ^ 2 + 2 * m) (hk : 5 / 100 ≤ k) :
    M * B / (k * M * D) ^ 2 ≤ 5 / 10 ^ 6 := by
  have hD0 : 12224 ≤ D := by rw [hD]; linarith
  have hM0 : 0 < M := by rw [hM]; positivity
  have hk0 : 0 < k := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : M * B ≤ 11 / 10 * M ^ 2 := by
    rw [hM]
    have hB2 : B ≤ 11 / 10 * m ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hB2 (sq_nonneg m)
    nlinarith
  have hk2 : 25 / 10000 ≤ k ^ 2 := by nlinarith
  have hD2 : 12224 ^ 2 ≤ D ^ 2 := by nlinarith
  have h2 : 11 / 10 ≤ 5 / 10 ^ 6 * (k ^ 2 * D ^ 2) := by
    nlinarith [mul_le_mul hk2 hD2 (by norm_num) (by positivity)]
  calc M * B ≤ 11 / 10 * M ^ 2 := h1
    _ ≤ 5 / 10 ^ 6 * (k ^ 2 * D ^ 2) * M ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg M)
    _ = 5 / 10 ^ 6 * (k * M * D) ^ 2 := by ring

theorem node_trace_charge (hn : 12225 ≤ n) {wr : WRet n} (hw : windowW wr)
    (hgeo : ∀ g < Js n, 0 ≤ nodeS (mkR wr (0, 0)) g ∧
      3969 / 10000 ≤ 1 - nodeS (mkR wr (0, 0)) g ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g ^ 2 ≤ 61 / 100) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤ 1 / 10 ^ 5 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
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
  have hn1' := variance_cheby_num hnR hMe hDe b1 (k := 5 / 100) le_rfl
  have hn2' := variance_cheby_num hnR hMe hDe b2 (k := 5 / 100) (by norm_num)
  have hEμ : gaussMat (mA n) n γ {A₁ | ∃ g < Js n,
      vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g) < 17 / (100 * (n : ℝ)) ∨
      42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (A₁, 0)) g ^ 2) < vsig2 (mkR wr (A₁, 0)) (nodeS (mkR wr (A₁, 0)) g)} ≤
      ENNReal.ofReal (1 / 10 ^ 5) := by
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
    linarith
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hEμ


theorem row_node_geometry {wr : WRet 12225} (hw : windowW wr)
    (θ : AHid 12225) {g : ℕ} (hg : g < Js 12225) :
    0 ≤ nodeS (mkR wr θ) g ∧
      (3969 / 10000 : ℝ) ≤ 1 - nodeS (mkR wr θ) g ^ 2 ∧
      1 - nodeS (mkR wr θ) g ^ 2 ≤ 61 / 100 := by
  let c := mkR wr θ
  obtain ⟨hLH, hbulk, -⟩ := BstLean.Part169.bulk_of_window (by norm_num) c
    hw.1 hw.2.1 hw.2.2
  have hs := BstLean.Part169.nodeS_mem c hLH hg
  let ρ := BstLean.Part169.rhoR c
  have hρ2 : ρ ^ 2 = normSq c.1.2 + 12225 * BstLean.Part169.tauR c ^ 2 := by
    change (√(normSq c.1.2 + (12225 : ℝ) * BstLean.Part169.tauR c ^ 2)) ^ 2 = _
    rw [Real.sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))]
  have hτ : 0 < BstLean.Part169.tauR c := hw.1
  have hρ0 : 0 < ρ := by
    change 0 < √(normSq c.1.2 + (12225 : ℝ) * BstLean.Part169.tauR c ^ 2)
    exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos hτ)))
  let a := √(normSq c.1.2) / ρ
  let b := BstLean.Part169.tauR c / ρ
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hρ0.le
  have hb0 : 0 < b := div_pos hτ hρ0
  have hab : a ^ 2 + 12225 * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, Real.sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hρ2]
  have hθ : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) =
      12225 * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / ρ ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hθU : BstLean.Part150.thetaC c.1.2 (BstLean.Part169.tauR c) ≤ 55 / 100 := hw.2.2
  rw [hθ] at hθU
  have ha : 67 / 100 ≤ a := by nlinarith
  have hb : b ≤ 671 / 100000 := by nlinarith
  have hL : BstLean.Part169.nodeL c = a - 6 * b := by
    dsimp [BstLean.Part169.nodeL, a, b, ρ]
    ring
  have hs0 : 625 / 1000 ≤ nodeS c g := by rw [hL] at hs; linarith [hs.1]
  have hq : 3969 / 10000 ≤ BstLean.Part169.qB 12225 := by
    have hr := row_bulk_radius
    have hr2 := Real.sq_sqrt row_bulk_positive.le
    nlinarith [Real.sqrt_nonneg (BstLean.Part169.qB 12225)]
  exact ⟨by linarith, by linarith [hbulk _ hs.1 hs.2], by nlinarith⟩

theorem node_trace_charge_row {wr : WRet 12225} (hw : windowW wr) :
    (gaussMat (mA 12225) 12225 (2 / (12225 : ℝ))).real {X | ∃ g < Js 12225,
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) < 17 / (100 * (12225 : ℝ)) ∨
      42 / (10 * (12225 : ℝ)) * (1 - nodeS (mkR wr (X, 0)) g ^ 2) < vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g)} ≤
        1 / 10 ^ 5 :=
  node_trace_charge (by norm_num) hw (fun g hg => row_node_geometry hw (0, 0) hg)

end BstLean.Part252
