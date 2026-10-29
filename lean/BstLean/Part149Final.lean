import BstLean.Part149Asm
import BstLean.Part149Win
import BstLean.Part145FinR

/-!
# Part 149, item 4: the program with no forward pass of `A` at a sampled input (exact centre)

Do not use `sorry`, `native_decide` or `axiom`.

Role: `delegations/statements/p149-spec.md`, item 4 (`twoStage149`). The program is IDEALIZED:
its stage for `A` uses the exact centre `b̄ = E_γ a₂(x(γ))` over the stand-in inputs of the `W`
stage (no arithmetic program for `b̄` is given). Its output is
`gOutA W A F = E_γ' F(A₃ b̄ + tauOut·γ')` (`Part149Asm`): forward passes of `F` only.

* `winOK149`: the window hypothesis `WinOK` for the event `Gwin n` of Part 145.
* `okOut149 n`: the event `|gOutA − B| ≤ sd/2` (the TRUE target `Bn` and the TRUE spread `sdn`).
* **`twoStage149_formula`**: the success probability with free parameters.
* **`twoStage149`**: `Pr(okOut149 n) ≥ 1 − (C₁/√n + C₂/n)` for every `n ≥ 4096`.
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

/-- The window hypothesis for the good hidden event `Gwin n` of Part 145. -/
theorem winOK149 (hn : 4096 ≤ n) :
    WinOK n (Gwin n) (462 / 1000) (6662 / 10000) (6969 / 10000) := by
  intro θ hθ
  obtain ⟨h1, h2, h3, h4⟩ := winA (goodEvFR hn).to0 hn hθ
  have hk := kk_win_sharp h3 h4
  exact ⟨h1, h2, h3, hk.1, hk.2⟩

/-- **The success event of the idealized program**: `|gOutA − B| ≤ sd/2`, with the true target
and the true spread. -/
def okOut149 (n : ℕ) :
    Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :=
  {t | |gOutA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2| ≤ sdn t.1 t.2.1 t.2.2 / 2}

/-- The bound of the failure probability, with free parameters. -/
noncomputable def pFail (n : ℕ) (Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ η₁ θ Δb δb : ℝ) : ℝ :=
  1 / 50000 / (n : ℝ) + 68000000 / (qA n : ℝ) ^ 2 + Δb ^ 2 / Δmax ^ 2 + δb ^ 2 / δmax ^ 2 +
    4 * ((1 + η₁) * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) + (1 + 1 / η₁) *
      (2 / (n : ℝ) * EA (6662 / 10000) Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb)) /
      (θ * (4 / (n : ℝ) * (222757 / 1000000))) +
    2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      (4 * θ * (1 - θ) * (4 / (n : ℝ) * (222757 / 1000000)) ^ 2)

lemma EA_nonneg {alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb : ℝ} (hv : 0 ≤ 1 - alo + δmax + Δmax)
    (hsu : 0 < su) (hη : 0 < η) (hζ : 0 < ζ) (hΔb : 0 ≤ Δb) :
    0 ≤ EA alo Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb := by
  unfold EA
  have : 0 ≤ Δb / su + Δb ^ 2 / ε₂ ^ 2 + δb ^ 2 / ε₁ ^ 2 := by positivity
  positivity

/-- **The idealized program with no forward pass of `A` at a sampled input succeeds**, formula
with free parameters. For every `n ≥ 4096`:
`Pr_{W, A, F}(|gOutA − B| ≤ sd/2) ≥ 1 − pFail`. -/
theorem twoStage149_formula (hn : 4096 ≤ n) {Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ η₁ θ Δb δb : ℝ}
    (hP : POK (462 / 1000) (6662 / 10000) (6969 / 10000) Δmax δmax ε₁ ε₂ su r₁ r₂)
    (hη : 0 < η) (hζ : 0 < ζ) (hη₁ : 0 < η₁) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hΔb : cF2o (mA n) + ((1 - (462 / 1000 : ℝ) ^ 2) / √(n : ℝ) + jCosC n) ≤ Δb)
    (hδb : cF2o (mA n) ≤ δb) :
    1 - pFail n Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ η₁ θ Δb δb ≤ (mlpTriple 2 n).real (okOut149 n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF : 1 ≤ mF n := by have := BstLean.Part132.mF_ge hn; omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hG := (goodEvFR hn).to0
  have hwin := winOK149 hn
  have hcF := BstLean.Part136.cF2o_pos hmA
  have hΔb0 : 0 < Δb := by
    have h1 := jCosC_nonneg n
    have h2 : 0 ≤ (1 - (462 / 1000 : ℝ) ^ 2) / √(n : ℝ) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    linarith
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
  have hbad := badT_prob hn hG hwin (by norm_num) (by norm_num) hP.hΔmax hP.hδmax hΔb hδb hG1
  -- the error
  obtain ⟨hΛi, hΛ⟩ := LamVR hn
  have hW := errVecAF_lint (goodEvFR hn) hn (by unfold Lam145R; norm_num) hΛi hΛ
    (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 7) (by norm_num) (η' := 1 / 29)
    (by norm_num)
  have hXA := XA145_R hn
  have hXF0 := XF_nonneg hn (ΛV := Lam145R) (by unfold Lam145R; norm_num) (1 / 20)
    (η := 1 / 7) (by norm_num) (η' := 1 / 29) (by norm_num)
  have hA := errA_lint hn hG hwin hP hη hζ hΔb hδb
  have hv₀0 : (0 : ℝ) ≤ 1 - 6662 / 10000 + δmax + Δmax := by
    have := hP.hΔmax; have := hP.hδmax
    linarith
  have hEA0 := EA_nonneg (ε₁ := ε₁) (ε₂ := ε₂) (r₁ := r₁) (r₂ := r₂) (δb := δb) hv₀0 hP.hsu hη hζ
    hΔb0.le
  set aE : ℝ := (1 + η₁) * (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) + (1 + 1 / η₁) *
    (2 / (n : ℝ) * EA (6662 / 10000) Δmax δmax ε₁ ε₂ su r₁ r₂ η ζ Δb δb) with haE
  have haE0 : 0 ≤ aE := by rw [haE]; positivity
  set err : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ :=
    fun t => (1 + η₁) * errGAG (Gwin n) t + (1 + 1 / η₁) * dOut (Gwin n) Δmax δmax t with herr
  have hGn : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      0 ≤ errGAG (Gwin n) t := fun t => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have m1 := measurable_errGAG0 hG hn1
  have m2 := measurable_dOut hG hn1 Δmax δmax
  have merr : Measurable err := (m1.const_mul _).add (m2.const_mul _)
  have herr0 : ∀ t, 0 ≤ err t := fun t => by
    have := hGn t
    have := dOut_nonneg (Gwin n) Δmax δmax t
    simp only [herr]
    positivity
  have hE : ∫⁻ t, ENNReal.ofReal (err t) ∂μ ≤ ENNReal.ofReal aE := by
    have e : ∀ t, ENNReal.ofReal (err t) =
        ENNReal.ofReal (1 + η₁) * ENNReal.ofReal (errGAG (Gwin n) t) +
          ENNReal.ofReal (1 + 1 / η₁) * ENNReal.ofReal (dOut (Gwin n) Δmax δmax t) := by
      intro t
      have := hGn t
      have := dOut_nonneg (Gwin n) Δmax δmax t
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    have mm1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (errGAG (Gwin n) t)) :=
      ENNReal.measurable_ofReal.comp m1
    have mm2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1 => ENNReal.ofReal (dOut (Gwin n) Δmax δmax t)) :=
      ENNReal.measurable_ofReal.comp m2
    rw [lintegral_congr e, lintegral_add_left (mm1.const_mul _), lintegral_const_mul _ mm1,
      lintegral_const_mul _ mm2]
    have hW' : ∫⁻ t, ENNReal.ofReal (errGAG (Gwin n) t) ∂μ ≤
        ENNReal.ofReal (4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ))) :=
      hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hXA (by positivity)))
    refine (add_le_add (mul_le_mul' le_rfl hW') (mul_le_mul' le_rfl hA)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
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
  have h := ok_joint μ (G := goodT (Gwin n) Δmax δmax) (Z := ∅)
    (d := fun t => gOutA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2)
    (sd := fun t => sdn t.1 t.2.1 t.2.2) (err := err)
    (fun t => sdn_nonneg' _ _ _) msd3 merr herr0
    (by
      intro t hg _
      have hW : t.1 ∈ goodWAG (Gwin n) := hg.1
      simp only [herr]
      unfold errGAG dOut
      rw [Set.indicator_of_mem hW, Set.indicator_of_mem hg]
      have e1 : (1 + η₁) * (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2 +
          (1 + 1 / η₁) * (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2) ^ 2 -
          (gOutA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2 =
          (η₁ * (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) -
            (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2)) ^ 2 / η₁ := by
        field_simp
        ring
      have : 0 ≤ (η₁ * (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) -
          (gOutA t.1 t.2.1 t.2.2 - gA t.1 t.2.1 t.2.2)) ^ 2 / η₁ := by positivity
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
  unfold pFail
  rw [← haE, ← hc₀]
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms winOK149
open BstLean.Part149 in
#print axioms twoStage149_formula
