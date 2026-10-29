import BstLean.Part151Weak

/-!
# Part 151, item 5: a Lean level with the Gaussian last step in the place of Chebyshev's
inequality

Role: `delegations/statements/p151-spec.md`, item 5.

The second-moment bounds of Parts 149 and 150 give the MEAN of the conditional variance `V′` on
the good event (`weakI`). Markov's inequality for `V′` gives no gain (`markov_no_gain`). The
moment form of the Gaussian step (`finalStepMoment`, constant `κ = 2/5`) gives:

* **`gaussLevel151_formula`**: for every `n ≥ 4096`, every measurable centre `bh` with the
  displacement bound `DispOK … ξ` of Part 150, and every estimator `g` equal to `gSampH bh k` on
  the good event: `Pr(|g − B| ≤ sd/2) ≥ 1 − pFail7`, where `pFail7` is the sum of
  (1) the probability of the bad event of Part 150 (unchanged);
  (2) Chebyshev's bound of `Pr(sd² < θ·c₀)`, `c₀ = (4/n)·0.222757`;
  (3) Chebyshev's bound of `Pr(|B′ − B| > ε_W·√(θc₀))` on the good event of `W`;
  (4) `κ·IA/((1/2 − ε_W)²·θ·c₀)`: the Gaussian step in moment form, for every constant `κ`
      with `2Φ̄(a) ≤ κ/a²` (`κ = 2/5`: `two_PhiBar_le_kap`).
* **`gaussLevel151`**: the straight-line program `fullProg150 k n n` of Part 150 (`J = n`
  atoms, `k ≥ 100n`) succeeds with probability at least `3/4` for every `n ≥ 16 384`
  (Part 150 has `7/10`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA gA measurable_gA qA qA_cast)
open BstLean.Part145
open BstLean.Part149
open BstLean.Part150

variable {k n : ℕ}

/-- The probability of the bad event of Part 150 (the same expression as in `frame150`). -/
noncomputable def badT (n : ℕ) (Δmax ΔXmax ΔKb ΔXb εD εQ π₀ Dmax ζ₃ dQb ξ D4 : ℝ) : ℝ :=
  1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + ΔKb ^ 2 / Δmax ^ 2 +
      ΔXb ^ 2 / ΔXmax ^ 2 +
    (1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + dQb ^ 2 / εQ ^ 2 +
      5 / (mA n : ℝ) / εD ^ 2 + xiB n εD π₀ ζ₃ dQb / Dmax ^ 2) + ξ / D4 ^ 2

/-- The bound of the failure probability with the Gaussian last step in moment form. -/
noncomputable def pFail7 (κ : ℝ) (n k : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃
    dQb ξ D4 y4 η₃ η₄ η₅ θ εW : ℝ) : ℝ :=
  badT n Δmax ΔXmax ΔKb ΔXb εD εQ π₀ Dmax ζ₃ dQb ξ D4 +
    2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      ((1 - θ) * (4 / (n : ℝ) * (222757 / 1000000))) ^ 2 +
    4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) /
      (εW ^ 2 * (θ * (4 / (n : ℝ) * (222757 / 1000000)))) +
    κ * IA n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD π₀ yhi ζ₃ dQb ξ y4 η₃ η₄ η₅ /
      ((1 / 2 - εW) ^ 2 * (θ * (4 / (n : ℝ) * (222757 / 1000000))))

/-- **A Lean success bound with the Gaussian last step (moment form)**, formula with free
parameters. `g` is any estimator equal to `gSampH bh k` on the good event of Part 150. -/
theorem gaussLevel151_formula {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k)
    {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD εQ π₀ Dmax ρhi yhi ζ₃ dQb : ℝ}
    (hP : POK2 (6662 / 10000) (6969 / 10000) Δmax ΔXmax r₁ r₂ w g)
    (hP3 : POK3 (6969 / 10000) Δmax εD εQ π₀ Dmax ρhi yhi) (hζ₃ : 0 < ζ₃)
    (hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dQ1 n (mA n) q ≤ dQb)
    (hQ0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dQ1 n (mA n) q)
    (hη : 0 < η) (hζ : 0 < ζ) (hζ₂ : 0 < ζ₂) (hΔKb0 : 0 ≤ ΔKb) (hΔXb0 : 0 ≤ ΔXb)
    (hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dK2 n (mA n) q ≤ ΔKb)
    (hK0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dK2 n (mA n) q)
    (hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → dX2 n (mA n) q ≤ ΔXb)
    (hX0 : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 → 0 ≤ dX2 n (mA n) q)
    (hδb : cF2o (mA n) ≤ δb)
    {bh : CMap n} (hbh : Measurable bh) {D4 y4 : ℝ} (hD4 : 0 < D4)
    (hy4 : (√yhi + D4) ^ 2 ≤ y4) (hy41 : y4 < 1) {ξ : ℝ} (hξ0 : 0 ≤ ξ)
    (hξ : DispOK n (Gwin n) εD εQ bh ξ) {η₃ η₄ η₅ : ℝ} (hη₃ : 0 < η₃) (hη₄ : 0 < η₄)
    (hη₅ : 0 < η₅) {θ εW : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hεW0 : 0 < εW) (hεW : εW < 1 / 2)
    (gE : Joint k n → ℝ)
    (hgE : ∀ p ∈ TXJ k (goodX234 n Δmax ΔXmax εD εQ Dmax bh D4),
      gE p = gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) :
    1 - pFail7 κ n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ dQb ξ D4 y4
        η₃ η₄ η₅ θ εW ≤
      (jointP k n).real {p | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK2_149 hn
  obtain ⟨_, c, e, -, -, -, -, hbadT, hV, hcc, he0, heR, -⟩ :=
    frame150 hn hP (η₄ := 1) one_pos hP3 hζ₃ (η₃ := 1) one_pos hdQ hQ0 hη hζ hζ₂ (η₁ := 1)
      one_pos (θ := 1 / 2) (by norm_num) (by norm_num) hΔKb0 hΔXb0 hΔK hK0 hΔX hX0 hδb hbh hD4
      hy4 hy41 hξ0 hξ
  set c₀ : ℝ := 4 / (n : ℝ) * (222757 / 1000000) with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set X := goodX234 n Δmax ΔXmax εD εQ Dmax bh D4 with hXdef
  have mX : MeasurableSet X :=
    ((goodX2_meas hG hn1 Δmax ΔXmax).inter (goodX3_meas hG hn1 εD εQ Dmax)).inter
      (measurableSet_le (measurable_dispH hbh) measurable_const)
  have hE := EX_meas (k := k) mX
  have hI := weakI hn hk hP hP3 hζ₃ hdQ hQ0 hη hζ hζ₂ hΔK hK0 hΔX hX0 hδb hbh hD4 hy4 hy41 hξ0
    hξ hη₃ hη₄ hη₅
  set I : ℝ := IA n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD π₀ yhi ζ₃ dQb ξ y4 η₃ η₄ η₅
    with hIdef
  have hI0 : 0 ≤ I := by
    have hy1 : 0 < 1 - yhi := by linarith [hP3.hy1]
    have hy41' : 0 < 1 - y4 := by linarith
    have hEA0 : 0 ≤ EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb := by
      have hw := hP.hw
      have hg := hP.hg
      have := hP.hΔmax
      have := hP.hΔXmax
      have := hP.hr₁
      have hv : (0 : ℝ) ≤ 1 - 6662 / 10000 + Δmax := by linarith
      unfold EA2 Part149.kK2 Part149.kX2 Part149.kD2
      positivity
    have hxi0 : 0 ≤ xiB n εD π₀ ζ₃ dQb := by
      have h1 := hP3.hπ0
      have h2 : 0 < 1 - π₀ := by linarith [hP3.hπ1]
      have h3 := Kq_nonneg
      unfold xiB cQ3 cD3
      positivity
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [hIdef]; unfold IA; positivity
  have hεA : 0 < 1 / 2 - εW := by linarith
  set d : ℝ := √(θ * c₀) with hd
  have hd0 : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = θ * c₀ := Real.sq_sqrt (by positivity)
  have hfin := finalStepMoment hκ (jointP k n)
    (fixP k n) (rowP n) measurable_restJ measurable_rowJ joint_map (measurable_linJ hbh k) hE
    (fun ω _ => vHat_nonneg bh k ω) (fun ω _ => linJ_gauss bh k ω) hI0 hI gE
    (fun p => Bn p.1.1 p.1.2.1 p.1.2.2) (fun p => gA p.1.1 p.1.2.1 p.1.2.2)
    (fun p => sdn p.1.1 p.1.2.1 p.1.2.2)
    (fun p hp => by rw [hgE p hp]; exact struct151 hn1 bh p)
    univ (fun _ _ => mem_univ _) εW hεA hd0
  -- (1) the bad event
  have t2 : (fixP k n).real (EX k X)ᶜ ≤
      badT n Δmax ΔXmax ΔKb ΔXb εD εQ π₀ Dmax ζ₃ dQb ξ D4 := by
    rw [fixP_eq_map, map_measureReal_apply measurable_restJ hE.compl]
    have e : restJ ⁻¹' (EX k X)ᶜ =
        {p : Joint k n | p.1 ∈ (goodT234 (Gwin n) Δmax ΔXmax εD εQ Dmax bh D4)ᶜ} := by
      ext p
      simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq]
      exact not_congr ⟨fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩, fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩⟩
    rw [e, jointP_fst]
    exact hbadT
  -- (2) the spread
  have msd3 : Measurable (fun t : Trip n => sdn t.1 t.2.1 t.2.2) :=
    measurable_sdn (mA := mA n) (mF := mF n) hN
  have t3 : (jointP k n).real ((univ : Set (Joint k n)) ∩
      {p | sdn p.1.1 p.1.2.1 p.1.2.2 < d}) ≤
      2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 / ((1 - θ) * c₀) ^ 2 := by
    have h1θ : 0 < 1 - θ := by linarith
    have hε : 0 < ((1 - θ) * c₀) ^ 2 := by positivity
    have mf : Measurable (fun t : Trip n =>
        ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
    have hm := markov_real (mlpTriple 2 n) mf hε
      (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) hV
    have hsub : ((univ : Set (Joint k n)) ∩ {p | sdn p.1.1 p.1.2.1 p.1.2.2 < d}) ⊆
        {p : Joint k n | p.1 ∈ {t : Trip n | ENNReal.ofReal (((1 - θ) * c₀) ^ 2) <
          ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2)}} := by
      rintro p ⟨-, hp⟩
      simp only [mem_ofPred_eq] at hp ⊢
      have h0 : 0 ≤ sdn p.1.1 p.1.2.1 p.1.2.2 := Real.sqrt_nonneg _
      have h2 : sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 < θ * c₀ := by
        rw [← hd2]; exact pow_lt_pow_left₀ hp h0 (by norm_num)
      have h3 : (1 - θ) * c₀ < c - sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 := by linarith
      have h4 : ((1 - θ) * c₀) ^ 2 < (sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2 := by
        have h5 : 0 < (1 - θ) * c₀ := by positivity
        have h6 := pow_lt_pow_left₀ h3 h5.le (n := 2) (by norm_num)
        have e6 : (sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2 =
            (c - sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2) ^ 2 := by ring
        rw [e6]; exact h6
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hε h4)).mpr h4
    refine (measureReal_mono hsub).trans ?_
    rw [jointP_fst]
    refine hm.trans ?_
    have he2 : (4 / (n : ℝ) * e) ^ 2 ≤ (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left heR (by positivity)) 2
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  -- (3) the `W` stage
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hW := errVecAF_lint (goodEvFR hn) hn (by unfold Lam145R; norm_num) hΛi hΛ
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 7) (by norm_num) (η' := 1 / 29)
    (by norm_num)
  have hXA := XA145_R hn
  have hW' : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) :=
    hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXA (by positivity)))
  have t1 : (jointP k n).real {p : Joint k n | restJ p ∈ EX k X ∧
      d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
      εW * sdn p.1.1 p.1.2.1 p.1.2.2 < |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ≤
      4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) / (εW * d) ^ 2 := by
    have hε : 0 < (εW * d) ^ 2 := by positivity
    have mf : Measurable (fun t : Trip n => ENNReal.ofReal (errGAG (Gwin n) t)) :=
      ENNReal.measurable_ofReal.comp (measurable_errGAG0 hG hn1)
    have hm := markov_real (mlpTriple 2 n) mf hε
      (by positivity : (0 : ℝ) ≤ 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) hW'
    have hsub : {p : Joint k n | restJ p ∈ EX k X ∧ d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
        εW * sdn p.1.1 p.1.2.1 p.1.2.2 <
          |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ⊆
        {p : Joint k n | p.1 ∈ {t : Trip n | ENNReal.ofReal ((εW * d) ^ 2) <
          ENNReal.ofReal (errGAG (Gwin n) t)}} := by
      rintro p ⟨hp1, hp2, hp3⟩
      simp only [mem_ofPred_eq]
      have hWg : p.1.1 ∈ goodWAG (Gwin n) := hp1.1.1.1
      have e : errGAG (Gwin n) p.1 =
          (gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2 := by
        unfold errGAG
        rw [indicator_of_mem hWg]
      rw [e]
      have h1 : εW * d ≤ εW * sdn p.1.1 p.1.2.1 p.1.2.2 :=
        mul_le_mul_of_nonneg_left hp2 hεW0.le
      have h2 : εW * d < |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2| :=
        lt_of_le_of_lt h1 hp3
      have h3 : (εW * d) ^ 2 < (gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2 := by
        rw [← sq_abs (gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2)]
        exact pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans hε h3)).mpr h3
    refine (measureReal_mono hsub).trans ?_
    rw [jointP_fst]
    exact hm
  -- assemble
  have hu : (1 : ℝ) ≤ (jointP k n).real {p | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} +
      (jointP k n).real {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|} := by
    have e : {p : Joint k n | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤
          sdn p.1.1 p.1.2.1 p.1.2.2 / 2} ∪
        {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
          |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|} = univ := by
      ext p
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      rw [show (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 =
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2 by ring]
      exact le_or_gt _ _
    have h1 := measureReal_union_le (μ := jointP k n)
      {p : Joint k n | |gE p - Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2}
      {p | (εW + (1 / 2 - εW)) * sdn p.1.1 p.1.2.1 p.1.2.2 <
        |gE p - Bn p.1.1 p.1.2.1 p.1.2.2|}
    rw [e] at h1
    simpa using h1
  have e1 : (εW * d) ^ 2 = εW ^ 2 * (θ * c₀) := by rw [mul_pow, hd2]
  have e4 : ((1 / 2 - εW) * d) ^ 2 = (1 / 2 - εW) ^ 2 * (θ * c₀) := by rw [mul_pow, hd2]
  rw [e1] at t1
  rw [e4] at hfin
  unfold pFail7
  rw [← hc₀, ← hIdef]
  linarith

end BstLean.Part151
