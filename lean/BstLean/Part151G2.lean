import BstLean.Part151G
import BstLean.Part151LevelK

/-!
# Part 151 (file `G2`): the unconditional level with the Gaussian step in moment form for the
`W` term too: success `≥ 4/5` for every `n ≥ 16 384`

Role: `delegations/statements/p151-spec.md`, item 5 ("sharper constants").

* `pFail7G`: `pFail7` of `Part151Level` with the `W` term multiplied by `κ`.
* **`gaussLevel151G_formula`**: `Pr(|g − B| ≤ sd/2) ≥ 1 − pFail7G κ`.
* `pFail7G_num`: at the parameters of `displaceSamp150`, `θ = 3/4`, `ε_W = 1/20`:
  `pFail7G κ ≤ 0.075586 + κ·(0.035431 + 0.32707)` for `n ≥ 16 384`, `k ≥ 100n`.
* `gaussLevel151G_of_kap`: the level `1 − (0.075586 + 0.362501·κ)`.
* **`gaussLevel151_45`**: the program `fullProg150 k n n` succeeds with probability at least
  `4/5`, for every `n ≥ 16 384`, `k ≥ 100n` (`κ = 1/3`).
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

section formula

variable {k n : ℕ}

/-- The bound of the failure probability with the Gaussian step in moment form for the `A`
term and for the `W` term. -/
noncomputable def pFail7G (κ : ℝ) (n k : ℕ) (Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD εQ π₀ Dmax yhi
    ζ₃ dQb ξ D4 y4 η₃ η₄ η₅ θ εW : ℝ) : ℝ :=
  badT n Δmax ΔXmax ΔKb ΔXb εD εQ π₀ Dmax ζ₃ dQb ξ D4 +
    2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      ((1 - θ) * (4 / (n : ℝ) * (222757 / 1000000))) ^ 2 +
    κ * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) /
      (εW ^ 2 * (θ * (4 / (n : ℝ) * (222757 / 1000000)))) +
    κ * IA n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD π₀ yhi ζ₃ dQb ξ y4 η₃ η₄ η₅ /
      ((1 / 2 - εW) ^ 2 * (θ * (4 / (n : ℝ) * (222757 / 1000000))))

/-- **A Lean success bound with the Gaussian step in moment form for BOTH the `A` term and the
`W` term**, formula with free parameters. `g` is any estimator equal to `gSampH bh k` on the good event of Part 150. -/
theorem gaussLevel151G_formula {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
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
    1 - pFail7G κ n k Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ dQb ξ D4 y4
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
  -- (3) the `W` stage, with the Gaussian step in moment form
  have t1 : (jointP k n).real {p : Joint k n | restJ p ∈ EX k X ∧
      d ≤ sdn p.1.1 p.1.2.1 p.1.2.2 ∧
      εW * sdn p.1.1 p.1.2.1 p.1.2.2 < |gA p.1.1 p.1.2.1 p.1.2.2 - Bn p.1.1 p.1.2.1 p.1.2.2|} ≤
      κ * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) / (εW * d) ^ 2 := by
    have h3 := wStageGauss151 (k := k) hκ hn (mul_pos hεW0 hd0)
    refine (measureReal_mono ?_).trans h3
    rintro p ⟨hp1, hp2, hp3⟩
    exact ⟨hp1.1.1.1, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hp2 hεW0.le) hp3⟩
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
  unfold pFail7G
  rw [← hc₀, ← hIdef]
  linarith


end formula

lemma A_term_eqG (a b ξ N k : ℝ) (hN : 0 < N) (hk : 0 < k) :
    ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * (2 / N * a) +
          (1 + 1 / (3 / 10)) * (2 / N * (2 / (1 - 8441 / 10000)) * b)) +
        (1 + 1 / (8 / 39)) * (2 / N * (2 / (1 - 9193 / 10000)) * ξ)) +
      (1 + 1 / (1 / 47)) * (4 / N / k)) /
      ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 / N * (222757 / 1000000)))) =
    ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * 2))) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * a +
      ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 1 / (3 / 10)) *
          (2 * (2 / (1 - 8441 / 10000)))))) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * b +
      ((1 + 1 / 47) * ((1 + 1 / (8 / 39)) * (2 * (2 / (1 - 9193 / 10000))))) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * ξ +
      ((1 + 1 / (1 / 47)) * 4) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * (1 / k) := by
  field_simp

lemma W_term_eqG (N : ℝ) (hN : 0 < N) :
    4849 / 20000 * (1 / N) * (4 / N) / ((1 / 20) ^ 2 * (3 / 4 * (4 / N * (222757 / 1000000)))) =
      4849 / 20000 / ((1 / 20) ^ 2 * (3 / 4 * (222757 / 1000000))) * (1 / N) := by
  field_simp

variable {k n : ℕ}

/-- **The numbers**: `pFail7G κ ≤ 0.075586 + κ·(0.035431 + 0.32707)` for `n ≥ 16 384`, `k ≥ 100n`, at the
parameters of `displaceSamp150`, `θ = 3/4`, `ε_W = 1/20`, `η₃ = 3/10`, `η₄ = 8/39`,
`η₅ = 1/47`. -/
theorem pFail7G_num {κ : ℝ} (hκ0 : 0 ≤ κ) (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {ξ : ℝ}
    (hξ : ξ ≤ 20 / (n : ℝ) ^ 2 + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2) :
    pFail7G κ n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000)
      (251 / 1000) (51 / 10) (56 / 1000) (1 / 10)
      (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
      (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
      (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8441 / 10000) (9 / 100)
      (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) ξ (1 / 25)
      (9193 / 10000) (3 / 10) (8 / 39) (1 / 47) (3 / 4) (1 / 20) ≤
      75586 / 1000000 + κ * (35431 / 1000000 + 32707 / 100000) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hs0 : 0 < √(n : ℝ) := by linarith
  have hkR : (1638400 : ℝ) ≤ k := by
    have : (100 * n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hx0.le
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 128 := by rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [ht, div_pow, one_pow, hsq]
  have hy : 1 / (n : ℝ) ≤ 1 / 16384 := one_div_le_one_div_of_le (by norm_num) hx
  have ht2' : t ^ 2 ≤ 1 / 16384 := by rw [ht2]; exact hy
  have ht20 : 0 ≤ t ^ 2 := sq_nonneg t
  have h1k : 1 / (k : ℝ) ≤ 1 / 1638400 := one_div_le_one_div_of_le (by norm_num) hkR
  set K : ℝ := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 with hKd
  set X : ℝ := 16034 / 100000 * t + 11363 / 1000 * t ^ 2 with hXd
  set δ : ℝ := 4728 / 1000 * t ^ 2 with hδd
  set Q : ℝ := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 with hQd
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hX0 : 0 ≤ X := by rw [hXd]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδd]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQd]; positivity
  have hK : K ≤ 3766027 / 1000000000 := by rw [hKd]; linarith
  have hX : X ≤ 1946199 / 1000000000 := by rw [hXd]; linarith
  have hδ : δ ≤ 288575 / 1000000000 := by rw [hδd]; linarith
  have hQ : Q ≤ 4942136 / 1000000000 := by rw [hQd]; linarith
  have hK2 : K ^ 2 ≤ (3766027 / 1000000000) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have hX2 : X ^ 2 ≤ (1946199 / 1000000000) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have hδ2 : δ ^ 2 ≤ (288575 / 1000000000) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have hQ2 : Q ^ 2 ≤ (4942136 / 1000000000) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  -- the constant of the stage of `A`
  set a : ℝ := EA2 (6662 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000)
    (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) K X δ with had
  have ha : a ≤ 8717411 / 1000000000 := by
    have cK : Part149.kK2 (6662 / 10000) (284 / 10000) (273 / 1000) (51 / 10) (1 / 10) ≤ 172 := by
      unfold Part149.kK2; norm_num
    have cX : Part149.kX2 (6662 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
        (1908 / 1000) (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) ≤ 1572 := by
      unfold Part149.kX2; norm_num
    have cD : Part149.kD2 (6662 / 10000) (284 / 10000) (1908 / 1000) (251 / 1000) (51 / 10)
        (56 / 1000) ≤ 3887 := by
      unfold Part149.kD2; norm_num
    rw [had]
    unfold EA2
    calc _ ≤ 172 * (3766027 / 1000000000) ^ 2 + 1572 * (1946199 / 1000000000) ^ 2 +
          3887 * (288575 / 1000000000) ^ 2 :=
          add_le_add (add_le_add (mul_le_mul cK hK2 (sq_nonneg _) (by norm_num))
            (mul_le_mul cX hX2 (sq_nonneg _) (by norm_num)))
            (mul_le_mul cD hδ2 (sq_nonneg _) (by norm_num))
      _ ≤ 8717411 / 1000000000 := by norm_num
  have hm5 : 5 / (mA n : ℝ) ≤ 5 / 16384 ^ 2 := by
    rw [mA_eqR]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hx 2)
  have hm50 : 0 ≤ 5 / (mA n : ℝ) := by rw [mA_eqR]; positivity
  set b : ℝ := xiB n (9 / 100) (88 / 100) (9 / 100) Q with hbd
  have hb : b ≤ 6053068 / 100000000000 := by
    have c1 : cQ3 (88 / 100) (9 / 100) ≤ 2304 / 1000 := by unfold cQ3 Kq; norm_num
    have c2 : cD3 (9 / 100) (88 / 100) (9 / 100) ≤ 2285 / 10 := by unfold cD3 Kq; norm_num
    rw [hbd]
    unfold xiB
    calc _ ≤ 2304 / 1000 * (4942136 / 1000000000) ^ 2 + 2285 / 10 * (5 / 16384 ^ 2) :=
          add_le_add (mul_le_mul c1 hQ2 (sq_nonneg _) (by norm_num))
            (mul_le_mul c2 hm5 hm50 (by norm_num))
      _ ≤ 6053068 / 100000000000 := by norm_num
  -- the displacement constant
  have hξ' : ξ ≤ 2677650 / 100000000000 := by
    have h1 : (20 : ℝ) / (n : ℝ) ^ 2 ≤ 20 / 16384 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
    have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (16384 * 128) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (mul_le_mul hx hs (by norm_num) hx0.le)
    have h3 : (3850 : ℝ) / (n : ℝ) ^ 2 ≤ 3850 / 16384 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
    have h4 : (20 : ℝ) / 16384 ^ 2 + 2592 / 100 / (16384 * 128) + 3850 / 16384 ^ 2 ≤
        2677650 / 100000000000 := by norm_num
    linarith
  -- (1) the bad event
  have h1 : badT n (284 / 10000) (635 / 10000) K X (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (9 / 100) Q ξ (1 / 25) ≤ 51189 / 1000000 := by
    unfold badT
    rw [← hbd]
    have p1 : (1 : ℝ) / 50000 / (n : ℝ) ≤ 1 / 50000 / 16384 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    have p2 : (68000000 : ℝ) / (qA n : ℝ) ^ 2 ≤ 68000000 / (10000 * 16384) ^ 2 := by
      rw [qA_cast]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) (by linarith) 2)
    have p3 : K ^ 2 / (284 / 10000 : ℝ) ^ 2 ≤ (3766027 / 1000000000) ^ 2 / (284 / 10000) ^ 2 :=
      div_le_div_of_nonneg_right hK2 (by norm_num)
    have p4 : X ^ 2 / (635 / 10000 : ℝ) ^ 2 ≤ (1946199 / 1000000000) ^ 2 / (635 / 10000) ^ 2 :=
      div_le_div_of_nonneg_right hX2 (by norm_num)
    have p5 : Q ^ 2 / (1 / 10 : ℝ) ^ 2 ≤ (4942136 / 1000000000) ^ 2 / (1 / 10) ^ 2 :=
      div_le_div_of_nonneg_right hQ2 (by norm_num)
    have p6 : 5 / (mA n : ℝ) / (9 / 100 : ℝ) ^ 2 ≤ 5 / 16384 ^ 2 / (9 / 100) ^ 2 :=
      div_le_div_of_nonneg_right hm5 (by norm_num)
    have p7 : b / (67 / 1000 : ℝ) ^ 2 ≤ 6053068 / 100000000000 / (67 / 1000) ^ 2 :=
      div_le_div_of_nonneg_right hb (by norm_num)
    have p8 : ξ / (1 / 25 : ℝ) ^ 2 ≤ 2677650 / 100000000000 / (1 / 25) ^ 2 :=
      div_le_div_of_nonneg_right hξ' (by norm_num)
    have p9 : (1 : ℝ) / 50000 / 16384 + 68000000 / (10000 * 16384) ^ 2 +
        (3766027 / 1000000000) ^ 2 / (284 / 10000) ^ 2 +
        (1946199 / 1000000000) ^ 2 / (635 / 10000) ^ 2 +
        (1 / 50000 / 16384 + 68000000 / (10000 * 16384) ^ 2 +
          (4942136 / 1000000000) ^ 2 / (1 / 10) ^ 2 + 5 / 16384 ^ 2 / (9 / 100) ^ 2 +
          6053068 / 100000000000 / (67 / 1000) ^ 2) +
        2677650 / 100000000000 / (1 / 25) ^ 2 ≤ 51189 / 1000000 := by norm_num
    linarith
  -- (2) the spread
  have h2 : 2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      ((1 - 3 / 4) * (4 / (n : ℝ) * (222757 / 1000000))) ^ 2 ≤ 24397 / 1000000 := by
    have e := spread_term_eq (√(n : ℝ)) hs0
    rw [hsq] at e
    rw [e]
    calc 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 / 4) * (222757 / 1000000)) ^ 2 * (1 / (n : ℝ))
        ≤ 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 / 4) * (222757 / 1000000)) ^ 2 * (1 / 16384) :=
          mul_le_mul_of_nonneg_left hy (by norm_num)
      _ ≤ 24397 / 1000000 := by norm_num
  -- (3) the `W` stage
  have h3 : 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) /
      ((1 / 20) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤ 35431 / 1000000 := by
    rw [W_term_eqG (n : ℝ) hx0]
    calc 4849 / 20000 / ((1 / 20 : ℝ) ^ 2 * (3 / 4 * (222757 / 1000000))) * (1 / (n : ℝ))
        ≤ 4849 / 20000 / ((1 / 20 : ℝ) ^ 2 * (3 / 4 * (222757 / 1000000))) * (1 / 16384) :=
          mul_le_mul_of_nonneg_left hy (by norm_num)
      _ ≤ 35431 / 1000000 := by norm_num
  -- (4) the Gaussian step
  have h4 : IA n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000)
      (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) K X δ (9 / 100) (88 / 100)
      (8441 / 10000) (9 / 100) Q ξ (9193 / 10000) (3 / 10) (8 / 39) (1 / 47) /
      ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤
      32707 / 100000 := by
    unfold IA
    rw [← had, ← hbd, A_term_eqG a b ξ (n : ℝ) (k : ℝ) hx0 hk0]
    have q1 := mul_le_mul_of_nonneg_left ha (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * 2))) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q2 := mul_le_mul_of_nonneg_left hb (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 1 / (3 / 10)) *
          (2 * (2 / (1 - 8441 / 10000)))))) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q3 := mul_le_mul_of_nonneg_left hξ' (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / 47) * ((1 + 1 / (8 / 39)) * (2 * (2 / (1 - 9193 / 10000))))) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q4 := mul_le_mul_of_nonneg_left h1k (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / (1 / 47)) * 4) /
        ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q5 : ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * 2))) /
          ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) *
          (8717411 / 1000000000 : ℝ) +
        ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 1 / (3 / 10)) *
            (2 * (2 / (1 - 8441 / 10000)))))) /
          ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) *
          (6053068 / 100000000000) +
        ((1 + 1 / 47) * ((1 + 1 / (8 / 39)) * (2 * (2 / (1 - 9193 / 10000))))) /
          ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) *
          (2677650 / 100000000000) +
        ((1 + 1 / (1 / 47)) * 4) /
          ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * (1 / 1638400) ≤
        32707 / 100000 := by norm_num
    linarith
  have h5 : κ * IA n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000)
      (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) K X δ (9 / 100) (88 / 100)
      (8441 / 10000) (9 / 100) Q ξ (9193 / 10000) (3 / 10) (8 / 39) (1 / 47) /
      ((1 / 2 - 1 / 20) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤
      κ * (32707 / 100000) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h4 hκ0
  have h3' : κ * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) /
      ((1 / 20) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤
      κ * (35431 / 1000000) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h3 hκ0
  unfold pFail7G
  linarith

/-- **The level as a function of the constant `κ` of the Gaussian tail** (`2Φ̄(a) ≤ κ/a²`): for
every `n ≥ 16 384`, `k ≥ 100n`, the program `fullProg150 k n n` succeeds with probability at
least `1 − (0.075586 + κ·(0.035431 + 0.32707))`. -/
theorem gaussLevel151G_of_kap {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hκ0 : 0 ≤ κ) (hn : 16384 ≤ n) (hk : 100 * n ≤ k) :
    1 - (75586 / 1000000 + κ * (35431 / 1000000 + 32707 / 100000)) ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [hnt]; field_simp
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA6 : 1000000 ≤ mA n := by
    unfold mA
    calc 1000000 ≤ 4096 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn4 2
  have hcF : cF2o (mA n) ≤ 4728 / 1000 * t ^ 2 := by
    have h1 := BstLean.Part136.cF2o_sq_le hmA6
    have h0 := (BstLean.Part136.cF2o_pos hmA).le
    rw [mA_eqR] at h1
    have h2 : (2235 : ℝ) / 100 / (n : ℝ) ^ 2 = 2235 / 100 * (t ^ 2) ^ 2 := by
      rw [ht2]; field_simp
    rw [h2] at h1
    have h3 : cF2o (mA n) ^ 2 ≤ (4728 / 1000 * t ^ 2) ^ 2 := by
      refine h1.trans ?_
      have : 0 ≤ (t ^ 2) ^ 2 := by positivity
      nlinarith
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (by positivity))
  have hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dK2 n (mA n) q ≤ 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dK2_le hn4 hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dX2 n (mA n) q ≤ 16034 / 100000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dX2_le hn4 hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dQ1 n (mA n) q ≤ 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dQ1_le hn4 hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hP : POK2 (6662 / 10000) (6969 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
      (1908 / 1000) (273 / 1000) (251 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hP3 : POK3 (6969 / 10000) (284 / 10000) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8517 / 10000) (8441 / 10000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hsq : √(8441 / 10000 : ℝ) ≤ 91876 / 100000 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hy4 : (√(8441 / 10000 : ℝ) + 1 / 25) ^ 2 ≤ 9193 / 10000 := by
    have h0 := Real.sqrt_nonneg (8441 / 10000 : ℝ)
    nlinarith
  -- the arithmetic centre
  have hlam : (0 : ℝ) < √(n : ℝ) / 10 := by positivity
  have hd := arith_dispOK2 hn4 (goodEvFR hn4).to0 (winOK2_149 hn4) (εD := 9 / 100)
    (εQ := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlam (σ := 2 / 5)
    (by norm_num) (sigma_ok hn4) (J := n) (by omega) (fun _ h1 h2 => dQ1_le hn4 h1 h2)
    (fun _ h1 h2 => dQ1_nonneg h1 h2 (by omega))
  have hξ0 : 0 ≤ xiArith2 n n (9 / 100) (1 / 10) (√(n : ℝ) / 10) (dQb149 n) (2 / 5) := by
    have h1 := xiBin2_nonneg n (σ := 2 / 5) (by norm_num) (mA n)
    have h2 := CQn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num) hlam
    have h3 := CEn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num)
    have h4 := C0n_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num) hlam
    unfold xiArith2
    positivity
  have hxi := xiA2_le hn4
  -- the program is the sample mean on the good event
  have hwin := winOK2_149 hn4
  have hgE : ∀ p ∈ TXJ k (goodX234 n (284 / 10000) (635 / 10000) (9 / 100) (1 / 10)
      (67 / 1000) (bTW n) (1 / 25)),
      (fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () =
        gSampH (bTW n) k p.1.1 p.1.2.1 p.1.2.2 p.2 := by
    intro p hp
    have hW : p.1.1 ∈ goodWAG (Gwin n) := hp.1.1.1
    have hτ : 0 < tauWA p.1.1 := (hwin (p.1.1.1, p.1.1.2.1) hW).2.1
    exact fullProg150_gSampH (k := k) (J := n) p.1.1 p.1.2.1 p.1.2.2 p.2 hτ
  have h := gaussLevel151G_formula hκ hn4 hk1 hP hP3 (ζ₃ := 9 / 100) (by norm_num)
    (dQb := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2) hdQ
    (fun q hq1 hq2 => dQ1_nonneg hq1 hq2 hn1)
    (η := 51 / 10) (by norm_num) (ζ := 56 / 1000) (by norm_num) (ζ₂ := 1 / 10) (by norm_num)
    (ΔKb := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2)
    (ΔXb := 16034 / 100000 * t + 11363 / 1000 * t ^ 2) (by positivity) (by positivity) hΔK
    (fun q hq1 hq2 => dK2_nonneg hq1 hq2 hn1) hΔX (fun q _ _ => dX2_nonneg hn1) hcF
    (measurable_bTW n) (D4 := 1 / 25) (y4 := 9193 / 10000) (by norm_num) hy4 (by norm_num) hξ0 hd
    (η₃ := 3 / 10) (by norm_num) (η₄ := 8 / 39) (by norm_num) (η₅ := 1 / 47) (by norm_num)
    (θ := 3 / 4) (by norm_num) (by norm_num) (εW := 1 / 20) (by norm_num) (by norm_num)
    (fun p : Joint k n => (fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) ()) hgE
  refine le_trans ?_ h
  have hnum := pFail7G_num hκ0 hn hk hxi
  rw [← ht] at hnum
  linarith


/-- **The unconditional Lean level with the Gaussian step in moment form for both terms: the
straight-line program `fullProg150 k n n` of Part 150 succeeds with probability at least `4/5`,
for every `n ≥ 16 384`, `k ≥ 100n`.** (Part 150: `7/10`; `gaussLevel151_third`: `0.786`.) -/
theorem gaussLevel151_45 (hn : 16384 ≤ n) (hk : 100 * n ≤ k) :
    4 / 5 ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have h := gaussLevel151G_of_kap (κ := 1 / 3) (fun a ha => two_PhiBar_le_third ha)
    (by norm_num) hn hk
  refine le_trans ?_ h
  norm_num

end BstLean.Part151
