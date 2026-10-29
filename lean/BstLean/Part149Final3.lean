import BstLean.Part149Final2
import BstLean.Part149Asm3

/-!
# Part 149, item 5: the program with the mean-field centre, computed in one pass over `A`

Do not use `sorry`, `native_decide` or `axiom`.

The output is `gOutB W A F` of `Part149Asm3`: the centre of the last hidden layer of `A` is the
mean-field centre `bMF = ψ_s(A₂ b1)`. The exact first-layer mean `b1`, the number `N2` and the
function `ψ_s` are ORACLES: this file gives no arithmetic program and no operation count.

* `okOutB149 n`: the success event `|gOutB − B| ≤ sd/2`.
* **`onePassA149_formula`**: `Pr(okOutB149 n) ≥ 1 − pFail3`, free parameters.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143 BstLean.Part145

variable {n : ℕ}

/-- The success event of the program with the mean-field centre. -/
def okOutB149 (n : ℕ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | |gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2}

lemma sq_add_le' {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 := by
  have e1 : (1 + η) * a ^ 2 + (1 + 1 / η) * b ^ 2 - (a + b) ^ 2 = (η * a - b) ^ 2 / η := by
    field_simp
    ring
  have : 0 ≤ (η * a - b) ^ 2 / η := by positivity
  linarith

/-- The bound of the failure probability, with free parameters. -/
noncomputable def pFail3 (n : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb
    εD εQ π₀ Dmax yhi ζ₃ η₃ dQb : ℝ) : ℝ :=
  1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 + ΔXb ^ 2 / ΔXmax ^ 2 +
    (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
      5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) +
    4 * ((1 + η₁) * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) + (1 + 1 / η₁) *
      ((1 + η₃) * (2 / (n : ℝ) * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
        (1 + 1 / η₃) * (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb))) /
      (θ * (4 / (n : ℝ) * (222757 / 1000000))) +
    2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      (4 * θ * (1 - θ) * (4 / (n : ℝ) * (222757 / 1000000)) ^ 2)

/-- **The program with the mean-field centre (one product with `A₂`, oracles for the first-layer
mean) succeeds**, formula with free parameters. For every `n ≥ 4096`:
`Pr_{W, A, F}(|gOutB − B| ≤ sd/2) ≥ 1 − pFail3`. -/
theorem onePassA149_formula (hn : 4096 ≤ n)
    {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax ρhi yhi ζ₃ η₃ dQb : ℝ}
    (hP : POK2 (6662 / 10000) (6969 / 10000) Δmax ΔXmax r₁ r₂ w g)
    (hP3 : POK3 (6969 / 10000) Δmax εD εQ π₀ Dmax ρhi yhi) (hζ₃ : 0 < ζ₃) (hη₃ : 0 < η₃)
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q)
    (hη : 0 < η) (hζ : 0 < ζ) (hζ₂ : 0 < ζ₂) (hη₁ : 0 < η₁) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hΔKb0 : 0 ≤ ΔKb) (hΔXb0 : 0 ≤ ΔXb)
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q)
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q)
    (hδb : cF2o (mA n) ≤ δb) :
    1 - pFail3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb ≤
      (mlpTriple 2 n).real (okOutB149 n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  have hcF := BstLean.Part136.cF2o_pos hmA
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hcc : c₀ ≤ c := by
    rw [hc, hc₀]; exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hc0 : 0 < c := lt_of_lt_of_le hc₀0 hcc
  set μ := mlpTriple 2 n with hμ
  -- the hidden event of `W`
  have hG1 : (hidGauss (2 * n) (mW n)).real (Gwin n)ᶜ ≤ 1 / 50000 / (n : ℝ) := by
    have h := Gwin_compl_n hn
    unfold cW at h
    have e : (15640 : ℝ) / 1073741824 / (n : ℝ) ≤ 1 / 50000 / (n : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hx0.le
    linarith
  have hbad2 := badT2_prob hn hG hwin hP.hΔmax hP.hΔXmax hΔKb0 hΔXb0 hΔK hK0 hΔX hX0 hG1
  have hbad3 := badT3_prob hn hG hwin hP3 hζ₃ hdQ hQ0 hG1
  have hbad : μ.real (goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax)ᶜ ≤
      1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 +
        ΔXb ^ 2 / ΔXmax ^ 2 +
      (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
        5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) := by
    have hsub : (goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax)ᶜ ⊆
        (goodT2 (Gwin n) Δmax ΔXmax)ᶜ ∪ (goodT3 (Gwin n) εD εQ Dmax)ᶜ := by
      intro t ht
      by_cases h2 : t ∈ goodT2 (Gwin n) Δmax ΔXmax
      · exact Or.inr fun h3 => ht ⟨h2, h3⟩
      · exact Or.inl h2
    have hm := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
    have hu := measureReal_union_le (μ := μ) (goodT2 (Gwin n) Δmax ΔXmax)ᶜ
      (goodT3 (Gwin n) εD εQ Dmax)ᶜ
    linarith
  -- the error
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hW := errVecAF_lint (goodEvFR hn) hn (by unfold Lam145R; norm_num) hΛi hΛ
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 7) (by norm_num) (η' := 1 / 29)
    (by norm_num)
  have hXA := XA145_R hn
  have hXF0 := XF_nonneg hn (ΛV := Lam145R) (by unfold Lam145R; norm_num) (1 / 20)
    (η := 1 / 7) (by norm_num) (η' := 1 / 29) (by norm_num)
  have hA := errA2_lint hn hG hwin hP hη hζ hζ₂ hΔK hK0 hΔX hX0 hδb
  have hB := errB_lint (ΔXmax := ΔXmax) hn hG hwin hP.hΔmax hP.hA1 hP.hA2 hP3 hζ₃ hdQ hQ0
  have hy1 : 0 < 1 - yhi := by linarith [hP3.hy1]
  have hxi0 : 0 ≤ xiB n εD π₀ ζ₃ dQb := by
    have h1 := hP3.hπ0
    have h2 : 0 < 1 - π₀ := by linarith [hP3.hπ1]
    have h3 := Kq_nonneg
    unfold xiB cQ3 cD3
    positivity
  have hEA0 : 0 ≤ EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb := by
    have hw := hP.hw
    have hg := hP.hg
    have := hP.hΔmax
    have := hP.hΔXmax
    have := hP.hr₁
    have hv : (0 : ℝ) ≤ 1 - 6662 / 10000 + Δmax := by linarith
    unfold EA2 kK2 kX2 kD2
    positivity
  set aE : ℝ := (1 + η₁) * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) + (1 + 1 / η₁) *
    ((1 + η₃) * (2 / (n : ℝ) * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
      (1 + 1 / η₃) * (2 / (n : ℝ) * (2 / (1 - yhi)) * xiB n εD π₀ ζ₃ dQb)) with haE
  have haE0 : 0 ≤ aE := by rw [haE]; positivity
  set err : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ :=
    fun t => (1 + η₁) * errGAG (Gwin n) t + (1 + 1 / η₁) *
      ((1 + η₃) * dOut2 (Gwin n) Δmax ΔXmax t +
        (1 + 1 / η₃) * dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t) with herr
  have hGn : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      0 ≤ errGAG (Gwin n) t := fun t => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have m1 := measurable_errGAG0 hG hn1
  have m2 := measurable_dOut2 hG hn1 Δmax ΔXmax
  have m3 := measurable_dOut3 hG hn1 Δmax ΔXmax εD εQ Dmax
  have merr : Measurable err :=
    (m1.const_mul _).add (((m2.const_mul _).add (m3.const_mul _)).const_mul _)
  have herr0 : ∀ t, 0 ≤ err t := fun t => by
    have := hGn t
    have := dOut2_nonneg (Gwin n) Δmax ΔXmax t
    have := dOut3_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax t
    simp only [herr]
    positivity
  have hE : ∫⁻ t, ENNReal.ofReal (err t) ∂μ ≤ ENNReal.ofReal aE := by
    have e : ∀ t, ENNReal.ofReal (err t) =
        ENNReal.ofReal (1 + η₁) * ENNReal.ofReal (errGAG (Gwin n) t) +
          (ENNReal.ofReal ((1 + 1 / η₁) * (1 + η₃)) *
              ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax t) +
            ENNReal.ofReal ((1 + 1 / η₁) * (1 + 1 / η₃)) *
              ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t)) := by
      intro t
      have := hGn t
      have := dOut2_nonneg (Gwin n) Δmax ΔXmax t
      have := dOut3_nonneg (Gwin n) Δmax ΔXmax εD εQ Dmax t
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [herr]
      ring
    have mm1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (errGAG (Gwin n) t)) :=
      ENNReal.measurable_ofReal.comp m1
    have mm2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (dOut2 (Gwin n) Δmax ΔXmax t)) :=
      ENNReal.measurable_ofReal.comp m2
    have mm3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (dOut3 (Gwin n) Δmax ΔXmax εD εQ Dmax t)) :=
      ENNReal.measurable_ofReal.comp m3
    rw [lintegral_congr e, lintegral_add_left (mm1.const_mul _),
      lintegral_add_left (mm2.const_mul _), lintegral_const_mul _ mm1,
      lintegral_const_mul _ mm2, lintegral_const_mul _ mm3]
    have hW' : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂μ ≤
        ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) :=
      hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXA (by positivity)))
    refine (add_le_add (mul_le_mul' le_rfl hW')
      (add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB))).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [haE]
    ring
  -- the spread
  have he0 := eDBq_nonneg (biasK (mF n)) (tau143sC n) (pWC n) n
  have heR := eD145_R hn
  set e : ℝ := eDBq (biasK (mF n)) (tau143sC n) (pWC n) n with hed
  have msd3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => sdn t.1 t.2.1 t.2.2) := measurable_sdn (mA := mA n) (mF := mF n) hN
  have hV : ∫⁻ t, ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) ∂μ ≤
      ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have mFs : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
    have mπ : Measurable (fun r : Rest (2 * n) (mW n) n (mA n) (mF n) =>
        (r.1, r.2.1, r.2.2.2)) := by fun_prop
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
    rw [hμ, e0, ← lawR_drop, lintegral_map mFs mπ]
    exact spread_L2_dist2 hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) (kernR hn)
  -- the assembly
  have h := ok_joint μ (G := goodT23 (Gwin n) Δmax ΔXmax εD εQ Dmax) (Z := ∅)
    (d := fun t => gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2)
    (sd := fun t => sdn t.1 t.2.1 t.2.2) (err := err)
    (fun t => sdn_nonneg' _ _ _) msd3 merr herr0
    (by
      intro t hg _
      have hW : t.1 ∈ goodWAG (Gwin n) := hg.1.1
      simp only [herr]
      unfold errGAG dOut2 dOut3
      rw [Set.indicator_of_mem hW, Set.indicator_of_mem hg.1, Set.indicator_of_mem hg]
      have s1 := sq_add_le' hη₃ (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2)
        (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2)
      have s2 := sq_add_le' hη₁ (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2)
        ((gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) +
          (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2))
      have e3 : gOutB t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2 =
          (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) +
            ((gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) +
              (gOutB t.1 t.2.1 t.2.2 - gOutA t.1 t.2.1 t.2.2)) := by ring
      have hp : (0 : ℝ) ≤ 1 + 1 / η₁ := by positivity
      have s3 := mul_le_mul_of_nonneg_left s1 hp
      rw [e3]
      linarith)
    (by simp) hc0 hθ0 hθ1 haE0 (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) hbad hE hV
  refine le_trans ?_ h
  -- from `c` to `c₀` and from `e` to its bound
  have t1 : 4 * aE / (θ * c) ≤ 4 * aE / (θ * c₀) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hcc hθ0.le)
  have he2 : (4 / (n : ℝ) * e) ^ 2 ≤ (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left heR (by positivity)) 2
  have t2 : 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2) ≤
      2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 / (4 * θ * (1 - θ) * c₀ ^ 2) := by
    have hden : 4 * θ * (1 - θ) * c₀ ^ 2 ≤ 4 * θ * (1 - θ) * c ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc₀0.le hcc 2) (by positivity)
    calc 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2)
        ≤ 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c₀ ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  unfold pFail3
  rw [← haE, ← hc₀]
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms onePassA149_formula
