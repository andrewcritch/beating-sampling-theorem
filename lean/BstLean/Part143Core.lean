import BstLean.Part142Core2
import BstLean.Part143Spread

/-!
# Part 143: the assembly in formula form (levers 1 and 2)

Role: `delegations/statements/p143-spec.md`. The program is `arithProg141 k n` of Part 141,
unchanged; `okProgA k n` is the event `|gProgA − B| ≤ sd/2` of Part 141.

* `spreadLow143_of`: `Pr(sd² < θ·S·(1 − Q)) ≤ 2e²/((1 − θ)(1 − Q))²` from `‖kD − S(1 − Q)‖₂ ≤ S·e`
  (Part 142: the factor `3`).
* `progCore143`: `progCore142v` of Part 142 for an abstract constant `X` of the error tail.
* **`progDist143`**: if the bad hidden event has probability at most `p₁`, the error tail holds
  with a constant `X ≤ x_a/n`, `‖kD − S(1 − Q)‖₂ ≤ S·e` and `e ≤ c_e/√n`, then
  `Pr(ok) ≥ 1 − (p₁ + (0.0002 + 4x_a/(θ q₀) + 2c_e²/((1 − θ)q₀)²)/n + (4/(θ q₀))/k)`,
  `q₀ = 0.222757`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- **The spread from the distance kernel, with the factor 2.** For `n ≥ 4096`, `θ < 1`: if
`‖kD − S(1 − Q)‖₂ ≤ S·e` then `Pr_{W,A,F}(sd² < θ·S·(1 − Q)) ≤ 2e²/((1 − θ)(1 − Q))²`. -/
theorem spreadLow143_of {n : ℕ} (hn : 4096 ≤ n) {e : ℝ} (he : 0 ≤ e)
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e))
    {θ : ℝ} (hθ : θ < 1) :
    (mlpTriple 2 n).real
        {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤
      2 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hQ : kappa^[6] 0 ≤ 778 / 1000 := kappa6_zero_le
  have h1Q : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hc : (0 : ℝ) < 4 / (n : ℝ) * (1 - kappa^[6] 0) := by positivity
  have h := spreadLow_dist2 hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) hD hc hθ
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0]
  refine h.trans (le_of_eq ?_)
  field_simp

/-- **The headline in formula form for an abstract constant `X` of the error tail.** -/
theorem progCore143 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} {θ : ℝ} (hθ0 : 0 < θ) {X : ℝ}
    (hT : ∀ s : ℝ, 0 < s → ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (X + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s)
    {p₁ pS : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    (hS : (mlpTriple 2 n).real
      {t | sdn t.1 t.2.1 t.2.2 ^ 2 < θ * (4 / (n : ℝ) * (1 - kappa^[6] 0))} ≤ pS) :
    1 - (p₁ + 68000000 / (qA n : ℝ) ^ 2 +
        4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) + pS) ≤
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
      (X + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s := by
    have hT := hT s hs0
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
  have e : (X + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s =
      4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) := by
    rw [hs]
    field_simp
  rw [e] at h
  exact h


/-- **The rate from the distance kernel, in formula form.** For `n ≥ 4096`, `0 < θ < 1`: if
the bad hidden event has probability at most `p₁`, the error tail of the program holds with a
constant `X ≤ x_a·(1/n)`, `‖kD − S(1 − Q)‖₂ ≤ S·e` and `e ≤ c_e/√n`, then
`Pr(|gProgA − B| ≤ sd/2) ≥
  1 − (p₁ + (0.0002 + 4x_a/(θ q₀) + 2c_e²/((1 − θ)q₀)²)/n + (4/(θ q₀))/k)`, `q₀ = 0.222757`. -/
theorem progDist143 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {p₁ : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    {X xa : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ xa * (1 / (n : ℝ)))
    (hT : ∀ s : ℝ, 0 < s → ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (X + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s)
    {e ce : ℝ} (he : 0 ≤ e) (hce : e ≤ ce / √(n : ℝ))
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    1 - (p₁ + (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
          2 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hS := spreadLow143_of hn he hD hθ1
  have h := progCore143 hn hθ0 hT h1 hS
  refine le_trans ?_ h
  have t4 := qTerm_le hn
  have hk1 : (0 : ℝ) < (k : ℝ)⁻¹ := by positivity
  have tM : 4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) ≤
      4 * xa / (θ * (222757 / 1000000)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ) := by
    have hden : θ * (222757 / 1000000) ≤ θ * (1 - kappa^[6] 0) :=
      mul_le_mul_of_nonneg_left hy hθ0.le
    have hnum : 0 ≤ 4 * (X + (k : ℝ)⁻¹) := by positivity
    calc 4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0))
        ≤ 4 * (X + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hden
      _ ≤ 4 * (xa * (1 / (n : ℝ)) + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
          field_simp
  have he2 : e ^ 2 ≤ ce ^ 2 / (n : ℝ) := by
    have h1 : e ^ 2 ≤ (ce / √(n : ℝ)) ^ 2 := pow_le_pow_left₀ he hce 2
    rwa [div_pow, Real.sq_sqrt hx0.le] at h1
  have hden : ((1 - θ) * (222757 / 1000000 : ℝ)) ^ 2 ≤ ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hy h1θ.le) 2
  have hpS : 2 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2 ≤
      2 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / (n : ℝ) := by
    calc 2 * e ^ 2 / ((1 - θ) * (1 - kappa^[6] 0)) ^ 2
        ≤ 2 * e ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ 2 * (ce ^ 2 / (n : ℝ)) / ((1 - θ) * (222757 / 1000000)) ^ 2 :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have e1 : (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
      2 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2) / (n : ℝ) =
      1 / 5000 * (1 / (n : ℝ)) + 4 * xa / (θ * (222757 / 1000000)) / (n : ℝ) +
        2 * ce ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / (n : ℝ) := by
    field_simp
    ring
  rw [e1]
  linarith

end BstLean.Part143

open BstLean.Part143 in
#print axioms spreadLow143_of
open BstLean.Part143 in
#print axioms progCore143
open BstLean.Part143 in
#print axioms progDist143
