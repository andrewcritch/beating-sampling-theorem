import BstLean.Part159Final
import BstLean.Part152All

/-!
# Part 159 (file `Win`): the two angle events and the retained World window

Role: `delegations/statements/p159-spec.md`, item 3 (the World stage toward the paper). Do not use
`sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:window` (the retained World window).

`χ_W² = |ĉ|²/(t_W|b_W|²)`, `ĉ = W₃ b_W`. The two angle events of the paper, written with no
division (both hold when `b_W = 0`):

* `Ethm D = {|ĉ|² ≤ (1 + 2√0.0045 + 0.009)·n·t_W|b_W|²}` (the paper's `E_{θ−}`);
* `Ethp D = {|ĉ|² ≥ (1 − 2√(12/n))·n·t_W|b_W|²}` (the paper's `E_{θ+}`).

For EVERY design (every measurable World centre):

* `ethm_charge`: `Pr(Ethmᶜ) ≤ e^{−0.0045 n}`; `ethp_charge`: `Pr(Ethpᶜ) ≤ e^{−12}`.

For a design with the computed centre `bhat` and the scalar `tauHat` (file `Hat`), `n ≥ 16 384`:

* `w0_window_hat`: on `HW n`: `τ₀ > 0`, `τ₀² = t_W|b_W|²·w₀` and `0.9967 ≤ w₀ ≤ 1.0544`
  (the paper has `0.977865 ≤ w₀ ≤ 1.065383` for its centre).
* `thetaIn D c = nτ₀²/(|ĉ|² + nτ₀²)` (the noise fraction `θ_in` of the stand-in input);
  `theta_window_hat`: on `HW n ∩ Ethm ∩ Ethp`: `0.4657 ≤ θ_in ≤ 0.5272`
  (the paper: `0.461033 < θ_in < 0.530036`, and the window `[0.46, 0.54]` of the Agent parts).
* `classifier_networks_conditional_agent_window`: the conditional theorem of file `Final` with
  the two angle events PROVED: the Agent hypotheses are needed only on retained data inside
  `HW n ∩ {H̄_W ≤ h_W} ∩ Ethm ∩ Ethp ∩ E_A`, and the event `E_A` needs
  `Pr(HW n ∩ Ethm ∩ Ethp ∩ E_Aᶜ) ≤ δ_extra − 6.16·10⁻⁶`.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat Bn136)
open BstLean.Part140
open BstLean.Part152 (chiSq_upper_LM chiSq_lower_LM)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-! ## The two angle events, every design -/

/-- `1 + 2√0.0045 + 0.009`. -/
noncomputable def cUp : ℝ := 1 + 2 * √(45 / 10000) + 9 / 1000

/-- **The angle event `E_{θ−}`**: `|ĉ|² ≤ (1 + 2√0.0045 + 0.009)·n·t_W|b_W|²`. -/
def Ethm (D : Centres n) : Set (Ret n) :=
  {c | normSq c.1.2 ≤ cUp * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1))}

/-- **The angle event `E_{θ+}`**: `|ĉ|² ≥ (1 − 2√(12/n))·n·t_W|b_W|²`. -/
def Ethp (D : Centres n) : Set (Ret n) :=
  {c | (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤ normSq c.1.2}

lemma measurable_BW (D : Centres n) :
    Measurable (fun c : Ret n => 2 / (mW n : ℝ) * normSq (D.bW c.1.1)) :=
  (measurable_normSq.comp (D.mbW.comp measurable_hidOf)).const_mul _

lemma measurable_chat : Measurable (fun c : Ret n => normSq c.1.2) :=
  measurable_normSq.comp (measurable_snd.comp measurable_fst)

lemma measurableSet_Ethm (D : Centres n) : MeasurableSet (Ethm D) :=
  measurableSet_le measurable_chat ((measurable_BW D).const_mul _)

lemma measurableSet_Ethp (D : Centres n) : MeasurableSet (Ethp D) :=
  measurableSet_le ((measurable_BW D).const_mul _) measurable_chat

/-- The Gaussian vector `ξ_W` of the noise has the standard Gaussian distribution. -/
lemma noiseC_xi (n : ℕ) : (noiseC n).map (fun x : Ret n => x.1.2) = stdGauss (Fin n) := by
  have e : (fun x : Ret n => x.1.2) = Prod.snd ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_snd measurable_fst]
  unfold noiseC cWm
  rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.map_snd_prod, measure_univ, one_smul]

/-- `|ĉ|² = t_W|b_W|²·|ξ_W|²` for the retained data built from the noise. -/
lemma normSq_chat (D : Centres n) (x : Ret n) :
    normSq (retVal D x).1.2 = 2 / (mW n : ℝ) * normSq (D.bW x.1.1) * normSq x.1.2 := by
  have e : (retVal D x).1.2 = cOf (2 / (mW n : ℝ)) (D.bW x.1.1) x.1.2 := rfl
  rw [e]
  unfold cOf
  rw [normSq_smul, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (normSq_nonneg _)]

/-- The measure of an event of `ξ_W` under the noise. -/
lemma noiseC_xi_real {T : Set (Fin n → ℝ)} (hT : MeasurableSet T) :
    (noiseC n).real ((fun x : Ret n => x.1.2) ⁻¹' T) = (stdGauss (Fin n)).real T := by
  have m : Measurable (fun x : Ret n => x.1.2) := measurable_snd.comp measurable_fst
  rw [← map_measureReal_apply m hT, noiseC_xi]

/-- **The charge of `E_{θ−}`** (Laurent–Massart, `x = 0.0045 n`): `Pr(E_{θ−}ᶜ) ≤ e^{−0.0045 n}`,
for every design and every `n`. -/
theorem ethm_charge (D : Centres n) :
    (retDist D).real (Ethm D)ᶜ ≤ exp (-(45 / 10000 * (n : ℝ))) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  set T : Set (Fin n → ℝ) := {ξ | (Fintype.card (Fin n) : ℝ) +
    2 * √((Fintype.card (Fin n) : ℝ) * (45 / 10000 * (n : ℝ))) + 2 * (45 / 10000 * (n : ℝ)) ≤
      ∑ i, ξ i ^ 2} with hT
  have mT : MeasurableSet T :=
    measurableSet_le measurable_const (measurable_normSq (ι := Fin n))
  have hsub : retVal D ⁻¹' (Ethm D)ᶜ ⊆ (fun x : Ret n => x.1.2) ⁻¹' T := by
    intro x hx
    have h1 : ¬ normSq (retVal D x).1.2 ≤
        cUp * n * (2 / (mW n : ℝ) * normSq (D.bW x.1.1)) := hx
    rw [normSq_chat] at h1
    have hK : (0 : ℝ) ≤ 2 / (mW n : ℝ) * normSq (D.bW x.1.1) :=
      mul_nonneg (by positivity) (normSq_nonneg _)
    have h2 : cUp * n < normSq x.1.2 := by
      by_contra h
      exact h1 (by nlinarith [mul_le_mul_of_nonneg_left (not_lt.mp h) hK])
    change (Fintype.card (Fin n) : ℝ) +
      2 * √((Fintype.card (Fin n) : ℝ) * (45 / 10000 * (n : ℝ))) + 2 * (45 / 10000 * (n : ℝ)) ≤
        ∑ i, x.1.2 i ^ 2
    have e1 : √((n : ℝ) * (45 / 10000 * (n : ℝ))) = √(45 / 10000) * n := by
      have : (n : ℝ) * (45 / 10000 * (n : ℝ)) = 45 / 10000 * (n : ℝ) ^ 2 := by ring
      rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq hn0]
    rw [Fintype.card_fin, e1]
    have e2 : (n : ℝ) + 2 * (√(45 / 10000) * n) + 2 * (45 / 10000 * (n : ℝ)) = cUp * n := by
      unfold cUp; ring
    rw [e2]
    exact h2.le
  rw [← noise_retVal D, map_measureReal_apply (measurable_retVal D) (measurableSet_Ethm D).compl]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [noiseC_xi_real mT]
  exact chiSq_upper_LM (ι := Fin n) (by positivity)

/-- **The charge of `E_{θ+}`** (Laurent–Massart, `x = 12`): `Pr(E_{θ+}ᶜ) ≤ e^{−12}`, for every
design and every `n ≥ 1`. -/
theorem ethp_charge (hn : 1 ≤ n) (D : Centres n) :
    (retDist D).real (Ethp D)ᶜ ≤ exp (-12) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set T : Set (Fin n → ℝ) := {ξ | ∑ i, ξ i ^ 2 ≤
    (Fintype.card (Fin n) : ℝ) - 2 * √((Fintype.card (Fin n) : ℝ) * 12)} with hT
  have mT : MeasurableSet T :=
    measurableSet_le (measurable_normSq (ι := Fin n)) measurable_const
  have hsub : retVal D ⁻¹' (Ethp D)ᶜ ⊆ (fun x : Ret n => x.1.2) ⁻¹' T := by
    intro x hx
    have h1 : ¬ (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW x.1.1)) ≤
        normSq (retVal D x).1.2 := hx
    rw [normSq_chat] at h1
    have hK : (0 : ℝ) ≤ 2 / (mW n : ℝ) * normSq (D.bW x.1.1) :=
      mul_nonneg (by positivity) (normSq_nonneg _)
    have h2 : normSq x.1.2 < (1 - 2 * √(12 / (n : ℝ))) * n := by
      by_contra h
      exact h1 (by nlinarith [mul_le_mul_of_nonneg_left (not_lt.mp h) hK])
    change ∑ i, x.1.2 i ^ 2 ≤
      (Fintype.card (Fin n) : ℝ) - 2 * √((Fintype.card (Fin n) : ℝ) * 12)
    have e1 : √((n : ℝ) * 12) = √(12 / (n : ℝ)) * n := by
      have : (n : ℝ) * 12 = 12 / (n : ℝ) * (n : ℝ) ^ 2 := by field_simp
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hnpos.le]
    rw [Fintype.card_fin, e1]
    have e2 : (n : ℝ) - 2 * (√(12 / (n : ℝ)) * n) = (1 - 2 * √(12 / (n : ℝ))) * n := by ring
    rw [e2]
    exact h2.le
  rw [← noise_retVal D, map_measureReal_apply (measurable_retVal D) (measurableSet_Ethp D).compl]
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [noiseC_xi_real mT]
  exact chiSq_lower_LM (ι := Fin n) (by norm_num)

/-! ## The window of `w₀` and of `θ_in` for the computed centre -/

/-- **The noise fraction of the stand-in input**: `θ_in = nτ₀²/(|ĉ|² + nτ₀²)`. -/
noncomputable def thetaIn (D : Design n) (c : Ret n) : ℝ :=
  n * D.tau0 c ^ 2 / (normSq c.1.2 + n * D.tau0 c ^ 2)

/-- The window of `t_W|b̂|²` for `n ≥ 16 384`: `0.48688·γ ≤ t_W|b̂|² ≤ 0.50077·γ`
(Part 140 has `0.48`, `0.508` for `n ≥ 4096`). -/
theorem Bh_window_16 (hn : 16384 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n) :
    2 / ((2 * n : ℕ) : ℝ) * (48688 / 100000) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (50077 / 100000) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn4; omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  obtain ⟨hB1, hB2⟩ := Bn136 hn4 hθ.1.1
  have hHB : Hh (2 * n) (mW n) θ = 2 / ((2 * n : ℕ) : ℝ) * BstLean.Part137.Bn (2 * n) (mW n) θ := by
    unfold Hh BstLean.Part137.Bn
    field_simp
  have hL : 2 / ((2 * n : ℕ) : ℝ) * (4936 / 10000) ≤ Hh (2 * n) (mW n) θ := by
    rw [hHB]; exact mul_le_mul_of_nonneg_left hB1 hγ.le
  have hU : Hh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (494 / 1000) := by
    rw [hHB]; exact mul_le_mul_of_nonneg_left hB2 hγ.le
  have hd : dist2 (2 * n) (mW n) θ ≤
      2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) := hθ.1.2
  have hξ : (3 / 4 / ((2 * n : ℕ) : ℝ) : ℝ) ≤ (4785 / 1000000) ^ 2 := by
    rw [hNcast, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨g1, g2⟩ := Bh_window_gen (N := 2 * n) (m := mW n) hN hm hL hU hd
    (sL := 70256 / 100000) (sU := 70286 / 100000) (sξ := 4785 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hξ (by norm_num)
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ hγ.le) g1
    norm_num
  · refine le_trans g2 (mul_le_mul_of_nonneg_left ?_ hγ.le)
    norm_num

/-- **The window of `w₀` for the computed centre, `n ≥ 16 384`**: on `goodHat n`:
`τ̂₀ > 0`, `τ̂₀² = t_W|b̂|²·w₀` and `0.9967 ≤ w₀ ≤ 1.0544`. -/
theorem w0H_window_16 (hn : 16384 ≤ n) {θ : WHid n} (hθ : θ ∈ goodHat n) :
    0 < tauHat (2 * n) (mW n) θ ∧
      tauHat (2 * n) (mW n) θ ^ 2 = Bh (2 * n) (mW n) θ * w0H (2 * n) (mW n) θ ∧
      9967 / 10000 ≤ w0H (2 * n) (mW n) θ ∧ w0H (2 * n) (mW n) θ ≤ 10544 / 10000 := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  obtain ⟨hb1, hb2⟩ := Bh_window_16 hn hθ
  refine ⟨tauHat_pos hn4 hθ, tauHat_sq hn4 hθ, ?_, ?_⟩
  · rw [w0H_eq, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    have h1 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000) ^ 2 := pow_le_pow_left₀ (by linarith) hk2 2
    have h2 : (9967 / 10000 + 1) * (2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2) ≤
        2 / ((2 * n : ℕ) : ℝ) * (48688 / 100000) := by
      have h3 : (9967 / 10000 + 1) * kap1 (2 * n) ^ 2 ≤ 48688 / 100000 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hγ.le]
    linarith
  · rw [w0H_eq, sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    have h1 : (49372 / 100000) ^ 2 ≤ kap1 (2 * n) ^ 2 := pow_le_pow_left₀ (by norm_num) hk1 2
    have h2 : 2 / ((2 * n : ℕ) : ℝ) * (50077 / 100000) ≤
        (10544 / 10000 + 1) * (2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2) := by
      have h3 : (50077 / 100000 : ℝ) ≤ (10544 / 10000 + 1) * kap1 (2 * n) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hγ.le]
    linarith

lemma sqrt45_bounds : (67082 / 1000000 : ℝ) ≤ √(45 / 10000) ∧ √(45 / 10000) ≤ 67083 / 1000000 :=
  ⟨Real.le_sqrt_of_sq_le (by norm_num), Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩⟩

lemma sqrt12n_le (hn : 16384 ≤ n) : √(12 / (n : ℝ)) ≤ 27064 / 1000000 := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The retained World window for the computed centre (every `n ≥ 16 384`)**
(Lemma `t7:p02:window` of the paper, for this design). `D` is a design with the World centre
`bhat` and the scalar `tauHat`. On `HW n`: `τ₀ > 0`, `τ₀² = t_W|b_W|²·w₀` with
`0.9967 ≤ w₀ ≤ 1.0544`. On `HW n ∩ E_{θ−} ∩ E_{θ+}`: `0.4657 ≤ θ_in ≤ 0.5272`. -/
theorem theta_window_hat (hn : 16384 ≤ n) (D : Design n) (hD : D.bW = bhat)
    (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1) {c : Ret n} (hc : c ∈ HW n) :
    0 < D.tau0 c ∧
      D.tau0 c ^ 2 = 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * w0H (2 * n) (mW n) c.1.1 ∧
      9967 / 10000 ≤ w0H (2 * n) (mW n) c.1.1 ∧ w0H (2 * n) (mW n) c.1.1 ≤ 10544 / 10000 ∧
      (c ∈ Ethm D.toCentres → 4657 / 10000 ≤ thetaIn D c) ∧
      (c ∈ Ethp D.toCentres → thetaIn D c ≤ 5272 / 10000) := by
  have hθ : c.1.1 ∈ goodHat n := hc
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨t1, t2, t3, t4⟩ := w0H_window_16 hn hθ
  have hBpos : 0 < Bh (2 * n) (mW n) c.1.1 := Bh_pos hn4 hθ
  have eB : 2 / (mW n : ℝ) * normSq (D.bW c.1.1) = Bh (2 * n) (mW n) c.1.1 := by
    rw [hD]; rfl
  refine ⟨by rw [hτ]; exact t1, by rw [hτ, eB]; exact t2, t3, t4, ?_, ?_⟩
  · intro hm
    have h1 : normSq c.1.2 ≤ cUp * n * Bh (2 * n) (mW n) c.1.1 := by
      have : normSq c.1.2 ≤ cUp * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) := hm
      rwa [eB] at this
    have hcu : cUp ≤ 1143166 / 1000000 := by
      unfold cUp
      have := sqrt45_bounds.2
      linarith
    unfold thetaIn
    rw [hτ, t2, le_div_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (Bh (2 * n) (mW n) c.1.1 * w0H (2 * n) (mW n) c.1.1) := by positivity
      linarith)]
    have hnB : 0 < (n : ℝ) * Bh (2 * n) (mW n) c.1.1 := by positivity
    have h2 : normSq c.1.2 ≤ 1143166 / 1000000 * ((n : ℝ) * Bh (2 * n) (mW n) c.1.1) := by
      have := mul_le_mul_of_nonneg_right hcu hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t3 hnB.le]
  · intro hp
    have h1 : (1 - 2 * √(12 / (n : ℝ))) * n * Bh (2 * n) (mW n) c.1.1 ≤ normSq c.1.2 := by
      have : (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤
          normSq c.1.2 := hp
      rwa [eB] at this
    have hcl : (945872 / 1000000 : ℝ) ≤ 1 - 2 * √(12 / (n : ℝ)) := by
      have := sqrt12n_le hn
      linarith
    unfold thetaIn
    rw [hτ, t2, div_le_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (Bh (2 * n) (mW n) c.1.1 * w0H (2 * n) (mW n) c.1.1) := by positivity
      linarith)]
    have hnB : 0 < (n : ℝ) * Bh (2 * n) (mW n) c.1.1 := by positivity
    have h2 : 945872 / 1000000 * ((n : ℝ) * Bh (2 * n) (mW n) c.1.1) ≤ normSq c.1.2 := by
      have := mul_le_mul_of_nonneg_right hcl hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t4 hnB.le]

/-! ## The conditional theorem with the two angle events proved -/

lemma exp_neg_12_le : exp (-12) ≤ 6145 / 10 ^ 9 := by
  have h1 : exp (-1) ≤ 1 / 2718281828 * 10 ^ 9 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have := Real.exp_one_gt_d9
    have h2 : (2718281828 / 10 ^ 9 : ℝ) ≤ exp 1 := by linarith
    refine (one_div_le_one_div_of_le (by norm_num) h2).trans (le_of_eq ?_)
    norm_num
  have h2 : exp (-12) = exp (-1) ^ 12 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  refine (pow_le_pow_left₀ (exp_pos _).le h1 12).trans ?_
  norm_num

lemma exp_neg_n_le (hn : 16384 ≤ n) : exp (-(45 / 10000 * (n : ℝ))) ≤ 1 / 10 ^ 9 := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : exp (-(45 / 10000 * (n : ℝ))) ≤ exp (-30) := exp_le_exp.2 (by linarith)
  have h2 : exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have := Real.exp_one_gt_d9
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h3 : exp (-30) = exp (-1) ^ 30 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h4 : exp (-1) ^ 30 ≤ (1 / 2 : ℝ) ^ 30 := pow_le_pow_left₀ (exp_pos _).le h2 30
  have h5 : (1 / 2 : ℝ) ^ 30 ≤ 1 / 10 ^ 9 := by norm_num
  linarith

/-- The charge of the two angle events for `n ≥ 16 384`: `e^{−0.0045 n} + e^{−12} ≤ 6.146·10⁻⁶`. -/
noncomputable def δAng : ℝ := 6146 / 10 ^ 9

/-- **The charge of the events other than the hidden event, with the two angle events proved.**
For every design and `n ≥ 16 384`: `Pr(H ∩ (E_{θ−} ∩ E_{θ+} ∩ E_A)ᶜ) ≤ 6.146·10⁻⁶ +
Pr(H ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ)`. -/
theorem extra_angle (hn : 16384 ≤ n) (D : Centres n) (H EA : Set (Ret n)) :
    (retDist D).real (H ∩ (Ethm D ∩ Ethp D ∩ EA)ᶜ) ≤
      δAng + (retDist D).real (H ∩ Ethm D ∩ Ethp D ∩ EAᶜ) := by
  have hsub : H ∩ (Ethm D ∩ Ethp D ∩ EA)ᶜ ⊆
      ((Ethm D)ᶜ ∪ (Ethp D)ᶜ) ∪ (H ∩ Ethm D ∩ Ethp D ∩ EAᶜ) := by
    intro c hc
    by_cases h1 : c ∈ Ethm D
    · by_cases h2 : c ∈ Ethp D
      · right
        exact ⟨⟨⟨hc.1, h1⟩, h2⟩, fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩⟩
      · left; right; exact h2
    · left; left; exact h1
  have h1 := ethm_charge D
  have h2 := ethp_charge (by omega : 1 ≤ n) D
  have h3 := exp_neg_12_le
  have h4 := exp_neg_n_le hn
  have h5 : (retDist D).real (H ∩ (Ethm D ∩ Ethp D ∩ EA)ᶜ) ≤
      (retDist D).real (Ethm D)ᶜ + (retDist D).real (Ethp D)ᶜ +
        (retDist D).real (H ∩ Ethm D ∩ Ethp D ∩ EAᶜ) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  unfold δAng
  norm_num at h3 h4 ⊢
  linarith

/-- **The conditional classifier theorem with ONLY Agent-side hypotheses, with the World window
(every `n ≥ 16 384`).** `D` is a design with the computed World centre `bhat` and the scalar
`tauHat`. The hidden World event `HW n`, its charge, the World frame bound, the Hellinger moment
and the two angle events `E_{θ−}`, `E_{θ+}` with their charges are PROVED. IF `E_A` is a measurable
event of the retained data with `Pr(HW n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A`,
`6.146·10⁻⁶ + δ_A ≤ δ_extra`, and on `HW n ∩ {H̄_W ≤ h_W} ∩ (E_{θ−} ∩ E_{θ+} ∩ E_A)` (where
`theta_window_hat` gives `0.4657 ≤ θ_in ≤ 0.5272`) the Agent frame bound and the Agent
replacement root hold, THEN the program succeeds with probability at least `99/100`. -/
theorem classifier_networks_conditional_agent_window (hn : 16384 ≤ n) (D : Design n)
    (hD : D.bW = bhat) (hτ : ∀ c : Ret n, D.tau0 c = tauHat (2 * n) (mW n) c.1.1) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist D.toCentres).real
      (HW n ∩ Ethm D.toCentres ∩ Ethp D.toCentres ∩ EAᶜ) ≤ δA)
    (hsum : δAng + δA ≤ δextraL)
    (hFA : FRAME_A_hyp D (cfL / n)
      (goodSet (HW n) (Ethm D.toCentres ∩ Ethp D.toCentres ∩ EA) (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL
      (goodSet (HW n) (Ethm D.toCentres ∩ Ethp D.toCentres ∩ EA) (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_agent hn D hD hτ t
    (((measurableSet_Ethm D.toCentres).inter (measurableSet_Ethp D.toCentres)).inter hEA)
    (((extra_angle hn D.toCentres (HW n) EA).trans (by linarith)).trans hsum) hFA hRA

end BstLean.Part159

open BstLean.Part159 in
#print axioms ethm_charge
open BstLean.Part159 in
#print axioms ethp_charge
open BstLean.Part159 in
#print axioms w0H_window_16
open BstLean.Part159 in
#print axioms theta_window_hat
open BstLean.Part159 in
#print axioms extra_angle
open BstLean.Part159 in
#print axioms classifier_networks_conditional_agent_window
