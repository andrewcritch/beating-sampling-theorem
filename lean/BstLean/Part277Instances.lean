import BstLean.Part277Energy

/-! Part 277, instances: the caps at the bases `8000`, `11883`, `12000`.
Window tops, the energy cap, the operator cap, the finite-centre cap and the lower energy
(`.665`) for the window `[.46, top]`. Rational witnesses were found by exact-rational scripts;
every hypothesis is discharged by `norm_num`. The 12225 instances reproduce the old constants. -/
namespace BstLean.Part277
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part182 BstLean.Part206
  BstLean.Part211 BstLean.Part219


/-! ### Base 8000 -/

theorem finite_centre_8000 {n : ℕ} (hn : 8000 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (10727/1000000 : ℝ) :=
  (finite_centre_upperP (n0 := 8000) (by norm_num) hn (r := (89442719/1000000 : ℝ)) (w := (522611/500000 : ℝ))
    (d := (1733/2000000 : ℝ)) (s1 := (710993/500000 : ℝ)) (s2 := (102163/62500 : ℝ)) (s3 := (878679/1000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)

theorem operator_allowance_8000 {n : ℕ} (hn : 8000 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤
      (1269/1000 : ℝ) :=
  operator_allowance_leP (n0 := 8000) (by norm_num) hn c hτ (J := (1069669/1000000 : ℝ))
    (fun m hm => (jS_le_jBoundRat (n0 := 8000) (by norm_num) hm (s := (894427/10000 : ℝ))
      (by norm_num) (Real.le_sqrt_of_sq_le (by norm_num))).trans
      (by unfold jBoundRat; norm_num))
    (by norm_num) (by norm_num)


theorem energy_lower_8000 {n : ℕ} (hn : 8000 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100 : ℝ) (527109/1000000)) :
    (0 ≤ meanLowerRoot n θ ∧
      0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 ∧
      0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) -
        2 / (n : ℝ) ^ 2)) - 2 * √(12 * BstLean.Part211.gPlus n) / n -
        finiteEnergy n n (11 / 1000) / √(n : ℝ)) ∧
    (665 / 1000 : ℝ) ≤ energyLower n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) θ := by
  have hK0 : (591017239/1000000000 : ℝ) ≤ kappa (1 - (527109/1000000 : ℝ)) := by
    have h : (1 : ℝ) - (527109/1000000 : ℝ) = (472891/1000000 : ℝ) := by norm_num
    rw [h]
    apply BstLean.Part253.kappa_lower_rational (s := (176224187/200000000 : ℝ)) <;> norm_num
  have hK1 : (334473953/500000000 : ℝ) ≤ kappa (29407/50000 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := (25273723/31250000 : ℝ)) <;> norm_num
  have h := energy_lower_dataP (n0 := 8000) (by norm_num) hn (θhi := (527109/1000000 : ℝ))
    (by norm_num) hw (t := (3464102/10^6 : ℝ)) (t2 := (1733551/500000 : ℝ)) (s1 := (1536867/2000000 : ℝ))
    (s2 := (25537/31250 : ℝ)) (K0 := (591017239/1000000000 : ℝ)) (K1 := (334473953/500000000 : ℝ)) (q1 := (29407/50000 : ℝ))
    (G := (100173281/100000000 : ℝ)) (g0 := (49913433/50000000 : ℝ)) (F := (10727/1000000 : ℝ))
    (r := (89442719/1000000 : ℝ)) (s0 := (9999999843/10000000000 : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) hK0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hK1 (by norm_num)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (finite_centre_8000 hn)
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpos : (0 : ℝ) ≤ (25537/31250 : ℝ) - 2 * (1733551/500000 : ℝ) / (8000 : ℕ) - (10727/1000000 : ℝ) / (89442719/1000000 : ℝ) := by
    norm_num
  refine ⟨⟨h1, h2, le_trans hpos h3⟩, le_trans (by norm_num) (h4 hpos)⟩


/-! ### Base 11883 -/

theorem finite_centre_11883 {n : ℕ} (hn : 11883 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (8771/1000000 : ℝ) :=
  (finite_centre_upperP (n0 := 11883) (by norm_num) hn (r := (109009173/1000000 : ℝ)) (w := (1037031/1000000 : ℝ))
    (d := (5833/10000000 : ℝ)) (s1 := (1421981/1000000 : ℝ)) (s2 := (32561/20000 : ℝ)) (s3 := (878679/1000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)

theorem operator_allowance_11883 {n : ℕ} (hn : 11883 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤
      (3059/2500 : ℝ) :=
  operator_allowance_leP (n0 := 11883) (by norm_num) hn c hτ (J := (1057829/1000000 : ℝ))
    (fun m hm => (jS_le_jBoundRat (n0 := 11883) (by norm_num) hm (s := (1090091/10000 : ℝ))
      (by norm_num) (Real.le_sqrt_of_sq_le (by norm_num))).trans
      (by unfold jBoundRat; norm_num))
    (by norm_num) (by norm_num)


theorem energy_lower_11883 {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100 : ℝ) (26169/50000)) :
    (0 ≤ meanLowerRoot n θ ∧
      0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 ∧
      0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) -
        2 / (n : ℝ) ^ 2)) - 2 * √(12 * BstLean.Part211.gPlus n) / n -
        finiteEnergy n n (11 / 1000) / √(n : ℝ)) ∧
    (665 / 1000 : ℝ) ≤ energyLower n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) θ := by
  have hK0 : (296733031/500000000 : ℝ) ≤ kappa (1 - (26169/50000 : ℝ)) := by
    have h : (1 : ℝ) - (26169/50000 : ℝ) = (23831/50000 : ℝ) := by norm_num
    rw [h]
    apply BstLean.Part253.kappa_lower_rational (s := (879109421/1000000000 : ℝ)) <;> norm_num
  have hK1 : (671302987/1000000000 : ℝ) ≤ kappa (3697/6250 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := (32251613/40000000 : ℝ)) <;> norm_num
  have h := energy_lower_dataP (n0 := 11883) (by norm_num) hn (θhi := (26169/50000 : ℝ))
    (by norm_num) hw (t := (3464102/10^6 : ℝ)) (t2 := (1733061/500000 : ℝ)) (s1 := (7701387/10000000 : ℝ))
    (s2 := (818853/1000000 : ℝ)) (K0 := (296733031/500000000 : ℝ)) (K1 := (671302987/1000000000 : ℝ)) (q1 := (3697/6250 : ℝ))
    (G := (100116641/100000000 : ℝ)) (g0 := (3995337/4000000 : ℝ)) (F := (8771/1000000 : ℝ))
    (r := (109009173/1000000 : ℝ)) (s0 := (9999999929/10000000000 : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) hK0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hK1 (by norm_num)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (finite_centre_11883 hn)
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpos : (0 : ℝ) ≤ (818853/1000000 : ℝ) - 2 * (1733061/500000 : ℝ) / (11883 : ℕ) - (8771/1000000 : ℝ) / (109009173/1000000 : ℝ) := by
    norm_num
  refine ⟨⟨h1, h2, le_trans hpos h3⟩, le_trans (by norm_num) (h4 hpos)⟩


/-! ### Base 12000 -/

theorem finite_centre_12000 {n : ℕ} (hn : 12000 ≤ n) :
    finiteEnergy n n (11 / 1000) ≤ (1091/125000 : ℝ) :=
  (finite_centre_upperP (n0 := 12000) (by norm_num) hn (r := (109544511/1000000 : ℝ)) (w := (1036849/1000000 : ℝ))
    (d := (361/625000 : ℝ)) (s1 := (1421981/1000000 : ℝ)) (s2 := (25436/15625 : ℝ)) (s3 := (878679/1000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)

theorem operator_allowance_12000 {n : ℕ} (hn : 12000 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤
      (6113/5000 : ℝ) :=
  operator_allowance_leP (n0 := 12000) (by norm_num) hn c hτ (J := (264393/250000 : ℝ))
    (fun m hm => (jS_le_jBoundRat (n0 := 12000) (by norm_num) hm (s := (219089/2000 : ℝ))
      (by norm_num) (Real.le_sqrt_of_sq_le (by norm_num))).trans
      (by unfold jBoundRat; norm_num))
    (by norm_num) (by norm_num)


theorem energy_lower_12000 {n : ℕ} (hn : 12000 ≤ n) {θ : ℝ}
    (hw : θ ∈ Icc (46 / 100 : ℝ) (16353/31250)) :
    (0 ≤ meanLowerRoot n θ ∧
      0 ≤ kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) - 2 / (n : ℝ) ^ 2 ∧
      0 ≤ √(gMinus n * (kappa (meanLowerRoot n θ ^ 2 / BstLean.Part211.gPlus n) -
        2 / (n : ℝ) ^ 2)) - 2 * √(12 * BstLean.Part211.gPlus n) / n -
        finiteEnergy n n (11 / 1000) / √(n : ℝ)) ∧
    (665 / 1000 : ℝ) ≤ energyLower n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n (11 / 1000)) θ := by
  have hK0 : (593521281/1000000000 : ℝ) ≤ kappa (1 - (16353/31250 : ℝ)) := by
    have h : (1 : ℝ) - (16353/31250 : ℝ) = (14897/31250 : ℝ) := by norm_num
    rw [h]
    apply BstLean.Part253.kappa_lower_rational (s := (7032511/8000000 : ℝ)) <;> norm_num
  have hK1 : (335675901/500000000 : ℝ) ≤ kappa (59159/100000 : ℝ) := by
    apply BstLean.Part253.kappa_lower_rational (s := (403119483/500000000 : ℝ)) <;> norm_num
  have h := energy_lower_dataP (n0 := 12000) (by norm_num) hn (θhi := (16353/31250 : ℝ))
    (by norm_num) hw (t := (3464102/10^6 : ℝ)) (t2 := (1733051/500000 : ℝ)) (s1 := (962721/1250000 : ℝ))
    (s2 := (818887/1000000 : ℝ)) (K0 := (593521281/1000000000 : ℝ)) (K1 := (335675901/500000000 : ℝ)) (q1 := (59159/100000 : ℝ))
    (G := (6257219/6250000 : ℝ)) (g0 := (99884561/100000000 : ℝ)) (F := (1091/125000 : ℝ))
    (r := (109544511/1000000 : ℝ)) (s0 := (999999993/1000000000 : ℝ))
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) hK0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hK1 (by norm_num)
    (le_sqrt_of_sq_le (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num)
    (finite_centre_12000 hn)
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpos : (0 : ℝ) ≤ (818887/1000000 : ℝ) - 2 * (1733051/500000 : ℝ) / (12000 : ℕ) - (1091/125000 : ℝ) / (109544511/1000000 : ℝ) := by
    norm_num
  refine ⟨⟨h1, h2, le_trans hpos h3⟩, le_trans (by norm_num) (h4 hpos)⟩

end BstLean.Part277
