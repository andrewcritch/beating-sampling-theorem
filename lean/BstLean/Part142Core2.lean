import BstLean.Part142Var2
import BstLean.Part142Dist

/-!
# Part 142, item 4: the assembly with the variance of the stand-in

Role: `delegations/statements/p142-spec.md`, item 4. `Part142Var2` replaces the second moment
`S = 4/n` of the stand-in by the mean variance `S·Vb n`, `Vb n ≤ 0.2736`, in the error term of
Parts 140 and 141 (`errSampleTailA142`, `XA142`). This file puts that into the assembly of
`Part142Core` and `Part142Dist`. The program is `arithProg141 k n` of Part 141, unchanged.

* **`progCore142v`**: `progCore142` with `XA142` in the place of `XA`.
* **`progRate142v`**: with `ζ = η = 1/20`, `η′ = 1/100`, a bound `p₁` of the bad hidden event
  and a bound `pS` of the spread event:
  `Pr(ok) ≥ 1 − (p₁ + (0.0002 + 2.56/(θ q₀))/n + (4/(θ q₀))/k + pS)`, `q₀ = 0.222757`.
* **`progDist142v`**: with the spread from the distance kernel, `‖kD − S(1 − Q)‖₂ ≤ S·e`,
  `e ≤ c_e/√n`: `pS = 3c_e²/((1 − θ)q₀)²/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

/-- **The headline in formula form with the variance of the stand-in.** As `progCore142`, with
`XA142` in the place of `XA`. -/
theorem progCore142v {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η')
    {p₁ pS : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    (hS : (mlpTriple 2 n).real
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤ pS) :
    1 - (p₁ + 68000000 / (qA n : ℝ) ^ 2 +
        4 * (XA142 n ζ η η' + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) + pS) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx0 : (0 : ℝ) < n := by have := nR_ge hn; linarith
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  set s : ℝ := θ * (4 / (n : ℝ) * (1 - kappa^[6] 0)) / 4 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  set μ := (mlpTriple 2 n).prod (gamK k n) with hμ
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtA_null hn k]
    rfl
  have h1' : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤ p₁ + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le
      (badA_prob_gen hn h1)
  have h2 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        s ≤ (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ≤
      (XA142 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
    have hT := errSampleTailA142 hn hζ0 hζ1 hη hη' hk hs0
    have hsub : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧
        s ≤ (gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2} ⊆
        {p | s ≤ errSA k n p} ∪ Z := by
      rintro p ⟨hg, he⟩
      by_cases hz : ∃ i, normSq (preA p.1.1 (p.2 i)) = 0
      · exact Or.inr ⟨hg, hz⟩
      · left
        push Not at hz
        change _ ≤ errSA k n p
        unfold errSA
        rw [Set.indicator_of_mem (show p.1.1 ∈ goodWA n from hg),
          ← gProgA_eq k p.1.1 p.1.2.1 p.1.2.2 p.2 hz]
        exact he
    calc _ ≤ μ.real ({p | s ≤ errSA k n p} ∪ Z) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real {p | s ≤ errSA k n p} + μ.real Z := measureReal_union_le _ _
      _ ≤ _ := by rw [hZ0, add_zero]; exact hT
  have h3 : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 < 4 * s} ≤ pS := by
    have e : (4 : ℝ) * s = θ * (4 / (n : ℝ) * (1 - kappa^[6] 0)) := by rw [hs]; ring
    rw [e]
    exact (prod_fst_real (mlpTriple 2 n) (gamK k n)
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))}).trans_le hS
  have h := ok_of_three μ
    (d := fun p => gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (fun p => sdn_nonneg' _ _ _) h1' h2 h3
  have e : (XA142 n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s =
      4 * (XA142 n ζ η η' + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) := by
    rw [hs]
    field_simp
  rw [e] at h
  exact h

/-- **The rate with the variance of the stand-in**, for a free `θ`, a bound `p₁` of the bad
hidden event and a bound `pS` of the spread event (`ζ = η = 1/20`, `η′ = 1/100`):
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (p₁ + (0.0002 + 2.56/(θ·0.222757))/n + (4/(θ·0.222757))/k + pS)`.
-/
theorem progRate142v {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    {p₁ pS : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    (hS : (mlpTriple 2 n).real
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤ pS) :
    1 - (p₁ + (2 / 10000 + 256 / 100 / (θ * (222757 / 1000000))) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ) + pS) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h := progCore142v hn hk hθ0 (ζ := 1 / 20) (by norm_num) (by norm_num) (η := 1 / 20)
    (by norm_num) (η' := 1 / 100) (by norm_num) h1 hS
  refine le_trans ?_ h
  have hX := XA142_le hn
  have hX0 := XA142_nonneg hn (1 / 20) (η := 1 / 20) (by norm_num) (η' := 1 / 100)
    (by norm_num)
  have t4 := qTerm_le hn
  have hk1 : (0 : ℝ) < (k : ℝ)⁻¹ := by positivity
  have tM : 4 * (XA142 n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) ≤
      256 / 100 / (θ * (222757 / 1000000)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ) := by
    have hden : θ * (222757 / 1000000) ≤ θ * (1 - kappa^[6] 0) :=
      mul_le_mul_of_nonneg_left hy hθ0.le
    have hnum : 0 ≤ 4 * (XA142 n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) := by positivity
    calc 4 * (XA142 n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0))
        ≤ 4 * (XA142 n (1 / 20) (1 / 20) (1 / 100) + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hden
      _ ≤ 4 * (64 / 100 * (1 / (n : ℝ)) + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
          field_simp
          ring
  have e1 : (2 / 10000 + 256 / 100 / (θ * (222757 / 1000000))) / (n : ℝ) =
      1 / 5000 * (1 / (n : ℝ)) + 256 / 100 / (θ * (222757 / 1000000)) / (n : ℝ) := by
    field_simp
    ring
  rw [e1]
  linarith

/-- **The rate from the distance kernel, with the variance of the stand-in.** For `n ≥ 4096`,
`k ≥ 1`, `0 < θ < 1`: if the bad hidden event has probability at most `p₁`,
`‖kD − S(1 − Q)‖₂ ≤ S·e` and `e ≤ c_e/√n`, then `Pr(|gProgA − B| ≤ sd/2) ≥
  1 − (p₁ + (0.0002 + 2.56/(θ q₀) + 3c_e²/((1 − θ)q₀)²)/n + (4/(θ q₀))/k)`, `q₀ = 0.222757`. -/
theorem progDist142v {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {p₁ : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    {e ce : ℝ} (he : 0 ≤ e) (hce : e ≤ ce / √(n : ℝ))
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    1 - (p₁ + (2 / 10000 + 256 / 100 / (θ * (222757 / 1000000)) +
          3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hS := spreadLow142_of hn he hD hθ1
  have h := progRate142v hn hk hθ0 h1 hS
  refine le_trans ?_ h
  have he2 : e ^ 2 ≤ ce ^ 2 / (n : ℝ) := by
    have h1 : e ^ 2 ≤ (ce / √(n : ℝ)) ^ 2 := pow_le_pow_left₀ he hce 2
    rwa [div_pow, Real.sq_sqrt hx0.le] at h1
  have hden : ((1 - θ) * (222757 / 1000000 : ℝ)) ^ 2 ≤ ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hy h1θ.le) 2
  have hpS : 3 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 ≤
      3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / (n : ℝ) := by
    calc 3 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2
        ≤ 3 * e ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ 3 * (ce ^ 2 / (n : ℝ)) / ((1 - θ) * (222757 / 1000000)) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have e1 : (2 / 10000 + 256 / 100 / (θ * (222757 / 1000000)) +
      3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2) / (n : ℝ) =
      (2 / 10000 + 256 / 100 / (θ * (222757 / 1000000))) / (n : ℝ) +
        3 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / (n : ℝ) := by ring
  rw [e1]
  linarith

/-- The bad hidden event of Part 140: `Pr(goodHat n fails) ≤ 0.002 + 70/n`. -/
lemma goodHat_compl {n : ℕ} (hn : 4096 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 2 / 1000 + 70 / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have := goodHat_prob hn
  rw [measureReal_compl (goodHat_meas hn1), probReal_univ]
  linarith

/-- **The headline with the Lipschitz links of the distance kernel and the variance of the
stand-in.** For every `n ≥ 4096`, `k ≥ 1`:
`Pr(|gProgA − B| ≤ sd/2) ≥ 1 − (0.002 + 572/n + 157/k)` (`θ = 0.115`). -/
theorem arithProgSucceeds142b {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    1 - (2 / 1000 + 572 / (n : ℝ) + 157 / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progDist142v hn hk (θ := 115 / 1000) (by norm_num) (by norm_num) (goodHat_compl hn)
    (eD142a_nonneg hn) (eD142a_scale hn) (kernDist142a hn)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 256 / 100 / (115 / 1000 * (222757 / 1000000 : ℝ)) +
      3 * (228 / 100 : ℝ) ^ 2 / ((1 - 115 / 1000) * (222757 / 1000000)) ^ 2) / (n : ℝ) ≤
      502 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (115 / 1000 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 157 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (572 : ℝ) / n = 70 / n + 502 / n := by ring
  rw [e3]
  linarith

end BstLean.Part142

open BstLean.Part142 in
#print axioms progCore142v
open BstLean.Part142 in
#print axioms progRate142v
open BstLean.Part142 in
#print axioms progDist142v
open BstLean.Part142 in
#print axioms arithProgSucceeds142b
