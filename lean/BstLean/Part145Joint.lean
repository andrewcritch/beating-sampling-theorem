import BstLean.Part143Core
import BstLean.Part143Var2

/-!
# Part 145: the joint assembly of the error and the spread

Role: `delegations/statements/p145-spec.md`, item 2 (the lever "a lower spread threshold").
The program is `arithProg141 k n` of Part 141, unchanged; `okProgA k n` is the event
`|gProgA − B| ≤ sd/2` of Part 141.

Parts 139 to 143 use three events (`ok_of_three`): the good hidden event, `err² < θc/4` and
`sd² ≥ θc`; the price is `4·E err²/(θc) + E(sd² − c)²/((1 − θ)c)²`. Here ONE inequality replaces
the two last events: for `0 < θ < 1`, `c > 0` and `4e > s`:

`4e/(θc) + (s − c)²/(4θ(1 − θ)c²) ≥ 1`, because
`4(1 − θ)cs + (s − c)² − 4θ(1 − θ)c² = (s + c − 2θc)² ≥ 0`.

So the price is `4·E err²/(θc) + E(sd² − c)²/(4θ(1 − θ)c²)`: the factor `1/(1 − θ)²` of the
spread term becomes `1/(4θ(1 − θ))` (at `θ = 1/2`: `1` in the place of `4`).

* `joint_pt`: the inequality.
* `ok_joint`: the abstract assembly (Markov's inequality for the sum of the two terms).
* **`progJoint145`**: if the bad hidden event has probability at most `p₁`, the mean squared
  error of the program is at most `(X + 1/k)·(4/n)` with `X ≤ x_a/n`, `‖kD − S(1 − Q)‖₂ ≤ S·e` and
  `e ≤ c_e/√n`, then
  `Pr(ok) ≥ 1 − (p₁ + (0.0002 + 4x_a/(θ q₀) + 2c_e²/(4θ(1 − θ)q₀²))/n + (4/(θ q₀))/k)`,
  `q₀ = 0.222757`. Compare `progDist143` of Part 143: `2c_e²/((1 − θ)q₀)²`.
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

/-- **The joint inequality.** For `c > 0`, `0 < θ < 1` and `s < 4e`:
`1 ≤ 4/(θc)·e + 1/(4θ(1 − θ)c²)·(s − c)²`. -/
lemma joint_pt {c θ s e : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (he : s < 4 * e) :
    1 ≤ 4 / (θ * c) * e + 1 / (4 * θ * (1 - θ) * c ^ 2) * (s - c) ^ 2 := by
  have h1θ : 0 < 1 - θ := by linarith
  have hD : 0 < 4 * θ * (1 - θ) * c ^ 2 := by positivity
  have e1 : 4 / (θ * c) * e + 1 / (4 * θ * (1 - θ) * c ^ 2) * (s - c) ^ 2 - 1 =
      (16 * (1 - θ) * c * e + (s - c) ^ 2 - 4 * θ * (1 - θ) * c ^ 2) /
        (4 * θ * (1 - θ) * c ^ 2) := by
    field_simp
    ring
  have h2 : 0 ≤ 16 * (1 - θ) * c * e + (s - c) ^ 2 - 4 * θ * (1 - θ) * c ^ 2 := by
    have h3 : 4 * (1 - θ) * c * s ≤ 16 * (1 - θ) * c * e := by
      have : 0 < 4 * (1 - θ) * c := by positivity
      nlinarith
    nlinarith [sq_nonneg (s + c - 2 * θ * c)]
  have h3 := div_nonneg h2 hD.le
  rw [← e1] at h3
  linarith

/-- **The joint assembly.** `μ` a probability measure, `G` the good event, `Z` a null set,
`err ≥ 0` measurable with `d² ≤ err` on `G \ Z`, `sd ≥ 0` measurable, `c > 0`, `0 < θ < 1`. If
`μ(Gᶜ) ≤ p₁`, `E err ≤ a` and `E(sd² − c)² ≤ v`, then `|d| ≤ sd/2` with probability at least
`1 − (p₁ + 4a/(θc) + v/(4θ(1 − θ)c²))`. -/
lemma ok_joint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G Z : Set Ω} {d sd err : Ω → ℝ} (hsd : ∀ ω, 0 ≤ sd ω) (msd : Measurable sd)
    (merr : Measurable err) (herr0 : ∀ ω, 0 ≤ err ω)
    (hcov : ∀ ω, ω ∈ G → ω ∉ Z → d ω ^ 2 ≤ err ω) (hZ : μ.real Z = 0)
    {c θ p₁ a v : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (h1 : μ.real Gᶜ ≤ p₁)
    (hE : ∫⁻ ω, ENNReal.ofReal (err ω) ∂μ ≤ ENNReal.ofReal a)
    (hV : ∫⁻ ω, ENNReal.ofReal ((sd ω ^ 2 - c) ^ 2) ∂μ ≤ ENNReal.ofReal v) :
    1 - (p₁ + 4 * a / (θ * c) + v / (4 * θ * (1 - θ) * c ^ 2)) ≤
      μ.real {ω | |d ω| ≤ sd ω / 2} := by
  have h1θ : 0 < 1 - θ := by linarith
  set C1 : ℝ := 4 / (θ * c) with hC1
  set C2 : ℝ := 1 / (4 * θ * (1 - θ) * c ^ 2) with hC2
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  have hC20 : 0 ≤ C2 := by rw [hC2]; positivity
  set Φ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal C1 * ENNReal.ofReal (err ω) +
    ENNReal.ofReal C2 * ENNReal.ofReal ((sd ω ^ 2 - c) ^ 2) with hΦ
  have m1 : Measurable fun ω => ENNReal.ofReal C1 * ENNReal.ofReal (err ω) :=
    (ENNReal.measurable_ofReal.comp merr).const_mul _
  have m2 : Measurable fun ω => ENNReal.ofReal C2 * ENNReal.ofReal ((sd ω ^ 2 - c) ^ 2) :=
    (ENNReal.measurable_ofReal.comp (((msd.pow_const 2).sub measurable_const).pow_const 2)).const_mul
      _
  have mΦ : Measurable Φ := m1.add m2
  set OK : Set Ω := {ω | |d ω| ≤ sd ω / 2} with hOK
  have hsub : OKᶜ ⊆ Gᶜ ∪ (Z ∪ {ω | (1 : ℝ≥0∞) ≤ Φ ω}) := by
    intro ω hω
    by_cases hg : ω ∈ G
    swap
    · exact Or.inl hg
    by_cases hz : ω ∈ Z
    · exact Or.inr (Or.inl hz)
    refine Or.inr (Or.inr ?_)
    have hde := hcov ω hg hz
    have h0 := hsd ω
    have hlt : sd ω ^ 2 < 4 * err ω := by
      by_contra hcon
      apply hω
      change |d ω| ≤ sd ω / 2
      have hsq : d ω ^ 2 ≤ (sd ω / 2) ^ 2 := by nlinarith
      exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by positivity))
    have hp := joint_pt hc hθ0 hθ1 hlt
    change (1 : ℝ≥0∞) ≤ Φ ω
    rw [hΦ]
    simp only
    rw [← ENNReal.ofReal_mul hC10, ← ENNReal.ofReal_mul hC20,
      ← ENNReal.ofReal_add (mul_nonneg hC10 (herr0 ω)) (mul_nonneg hC20 (sq_nonneg _)),
      ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hint : ∫⁻ ω, Φ ω ∂μ ≤ ENNReal.ofReal (C1 * a + C2 * v) := by
    rw [hΦ, lintegral_add_left m1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_add (mul_nonneg hC10 ha) (mul_nonneg hC20 hv), ENNReal.ofReal_mul hC10,
      ENNReal.ofReal_mul hC20]
    exact add_le_add (mul_le_mul' le_rfl hE) (mul_le_mul' le_rfl hV)
  have hmark : μ {ω | (1 : ℝ≥0∞) ≤ Φ ω} ≤ ENNReal.ofReal (C1 * a + C2 * v) := by
    have h := mul_meas_ge_le_lintegral (μ := μ) mΦ 1
    rw [one_mul] at h
    exact h.trans hint
  have hmarkR : μ.real {ω | (1 : ℝ≥0∞) ≤ Φ ω} ≤ C1 * a + C2 * v := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmark
  have hle : μ.real OKᶜ ≤ p₁ + (C1 * a + C2 * v) := by
    calc μ.real OKᶜ ≤ μ.real (Gᶜ ∪ (Z ∪ {ω | (1 : ℝ≥0∞) ≤ Φ ω})) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real Gᶜ + μ.real (Z ∪ {ω | (1 : ℝ≥0∞) ≤ Φ ω}) := measureReal_union_le _ _
      _ ≤ μ.real Gᶜ + (μ.real Z + μ.real {ω | (1 : ℝ≥0∞) ≤ Φ ω}) :=
          add_le_add le_rfl (measureReal_union_le _ _)
      _ ≤ _ := by rw [hZ, zero_add]; exact add_le_add h1 hmarkR
  have hcompl : μ.real OK + μ.real OKᶜ ≥ 1 := by
    have a1 := measureReal_union_le (μ := μ) OK OKᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  have e1 : 4 * a / (θ * c) = C1 * a := by rw [hC1]; ring
  have e2 : v / (4 * θ * (1 - θ) * c ^ 2) = C2 * v := by rw [hC2]; ring
  rw [e1, e2]
  linarith

/-- **The rate of the program from the joint assembly, in formula form.** For `n ≥ 4096`,
`k ≥ 1`, `0 < θ < 1`: if the bad hidden event has probability at most `p₁`, the mean squared
error of the program on the good event is at most `(X + 1/k)·(4/n)` with `0 ≤ X ≤ x_a·(1/n)`,
`‖kD − S(1 − Q)‖₂ ≤ S·e` and `e ≤ c_e/√n`, then
`Pr(|gProgA − B| ≤ sd/2) ≥
  1 − (p₁ + (0.0002 + 4x_a/(θ q₀) + 2c_e²/(4θ(1 − θ)q₀²))/n + (4/(θ q₀))/k)`, `q₀ = 0.222757`. -/
theorem progJoint145 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {p₁ : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    {X xa : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ xa * (1 / (n : ℝ)))
    (hE : ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
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
    {p | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtA_null hn k]
    rfl
  have h1' : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤ p₁ + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le
      (badA_prob_gen hn h1)
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
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}) (Z := Z)
    (d := fun p => gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (err := errSA k n)
    (fun p => sdn_nonneg' _ _ _) msd (measurable_errSA hn1 k) (errSA_nonneg k n)
    (by
      intro p hg hz
      have hg' : p.1.1 ∈ goodWA n := hg
      have hz' : ¬ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0 := fun hh => hz ⟨hg', hh⟩
      push Not at hz'
      unfold errSA
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
#print axioms joint_pt
open BstLean.Part145 in
#print axioms ok_joint
open BstLean.Part145 in
#print axioms progJoint145
