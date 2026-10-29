import BstLean.Part145Joint
import BstLean.Part145G5

/-!
# Part 145: the joint assembly for an abstract good hidden event

`progJointG0`: `progJoint145` of `Part145Joint` with an event `G` with `GoodEv0` (`Part145G5`)
in the place of `goodHat n`: the error is `errSAG G k`, the good event of `W` is `goodWAG G`.
The conclusion is about the same event `okProgA k n` of the same program `arithProg141 k n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143

/-- **`progJoint145` for an abstract good hidden event `G`** (`GoodEv0 n G`: measurable, window). For `n ≥ 4096`,
`k ≥ 1`, `0 < θ < 1`: if the bad hidden event has probability at most `p₁`, the mean squared
error of the program on the good event is at most `(X + 1/k)·(4/n)` with `0 ≤ X ≤ x_a·(1/n)`,
`‖kD − S(1 − Q)‖₂ ≤ S·e` and `e ≤ c_e/√n`, then
`Pr(|gProgA − B| ≤ sd/2) ≥
  1 − (p₁ + (0.0002 + 4x_a/(θ q₀) + 2c_e²/(4θ(1 − θ)q₀²))/n + (4/(θ q₀))/k)`, `q₀ = 0.222757`. -/
theorem progJointG0 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {p₁ : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p₁)
    {X xa : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ xa * (1 / (n : ℝ)))
    (hE : ∫⁻ p, ENNReal.ofReal (errSAG G k p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))))
    {e ce : ℝ} (he : 0 ≤ e) (hce : e ≤ ce / √(n : ℝ))
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    1 - (p₁ + (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
          2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgA k n) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set μ := (mlpTriple 2 n).prod (gamK k n) with hμ
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWAG G ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtAG0_null hn hG k]
    rfl
  have h1' : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G}ᶜ ≤ p₁ + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWAG G}).trans_le
      (badAG0_prob_gen hn hG h1)
  -- the spread under the product measure
  have msd3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => sdn t.1 t.2.1 t.2.2) := measurable_sdn (mA := mA n) (mF := mF n) hN
  have msd : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => sdn p.1.1 p.1.2.1 p.1.2.2) :=
    msd3.comp measurable_fst
  set Fs : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) with hFs
  have mFs : Measurable Fs :=
    ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
  have hL : ∫⁻ t, Fs t ∂mlpTriple 2 n ≤ ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have mπ : Measurable (fun r : Rest (2 * n) (mW n) n (mA n) (mF n) =>
        (r.1, r.2.1, r.2.2.2)) := by fun_prop
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
    rw [e0, ← lawR_drop, lintegral_map mFs mπ]
    exact spread_L2_dist2 hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) hD
  have hV : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ ≤
      ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have e2 : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ =
        ∫⁻ t, Fs t ∂mlpTriple 2 n := by
      have e3 : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ =
          ∫⁻ p, Fs p.1 ∂μ := rfl
      rw [e3, hμ, lintegral_prod (fun p => Fs p.1) (mFs.comp measurable_fst).aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
    rw [e2]
    exact hL
  have hX1 : 0 ≤ (X + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by positivity
  have h := ok_joint μ
    (G := {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G}) (Z := Z)
    (d := fun p => gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (err := errSAG G k)
    (fun p => sdn_nonneg' _ _ _) msd (measurable_errSAG0 hG hn1 k) (errSAG_nonneg G k)
    (by
      intro p hg hz
      have hg' : p.1.1 ∈ goodWAG G := hg
      have hz' : ¬ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0 := fun hh => hz ⟨hg', hh⟩
      push Not at hz'
      unfold errSAG
      rw [Set.indicator_of_mem hg', ← gProgA_eq k p.1.1 p.1.2.1 p.1.2.2 p.2 hz'])
    hZ0 hc0 hθ0 hθ1 hX1 (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) h1' hE hV
  refine le_trans ?_ h
  have t4 := qTerm_le hn
  have hk1 : (0 : ℝ) < (k : ℝ)⁻¹ := by positivity
  have tM : 4 * ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))) / (θ * c) ≤
      4 * xa / (θ * (222757 / 1000000)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ) := by
    have e5 : 4 * ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))) / (θ * c) =
        4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) := by
      rw [hc]
      field_simp
    rw [e5]
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
  have hpS : 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2) ≤
      2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) / (n : ℝ) := by
    have e6 : 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2) =
        2 * e ^ 2 / (4 * θ * (1 - θ) * (1 - kappa^[6] 0) ^ 2) := by
      rw [hc]
      field_simp
    rw [e6]
    have hden : 4 * θ * (1 - θ) * (222757 / 1000000 : ℝ) ^ 2 ≤
        4 * θ * (1 - θ) * (1 - kappa^[6] 0) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hy 2) (by positivity)
    calc 2 * e ^ 2 / (4 * θ * (1 - θ) * (1 - kappa^[6] 0) ^ 2)
        ≤ 2 * e ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ 2 * (ce ^ 2 / (n : ℝ)) / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have e1 : (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
      2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2)) / (n : ℝ) =
      1 / 5000 * (1 / (n : ℝ)) + 4 * xa / (θ * (222757 / 1000000)) / (n : ℝ) +
        2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) / (n : ℝ) := by
    field_simp
    ring
  rw [e1]
  linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms progJointG0
