import BstLean.Part159PaperD

/-!
# Part 159 (file `Paper`): the World stage for the binomial centre and `τ₀` of the paper

Role: `delegations/statements/p159-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `theorem7-02-world.tex`, Inputs `t7:p02:input-hidden`, `t7:p02:input-frame`,
`t7:p02:input-scalars` and Lemma `t7:p02:moment`, for the World centre `b_W = bWp` and the scalar
`τ₀ = tau0p` of the paper's program (Part 157, file `Paper`).

Two hypotheses on the computed constants of the program remain. They are statements about real
numbers that depend on `n` only (no network):

* `ConstC n`: `(c̃_N − c_N)²·n²·m_W ≤ 10⁻¹²` (file `PaperC`);
* `ConstK n`: `(κ̃ − κ₁)²·m_W ≤ 10⁻⁸`, `κ₁ = κ(E_u κ(u₁))` (`kap1` of Part 140).

For every `n ≥ 16 384`, IF `ConstC n` and `ConstK n`:

* `GPap n = goodHat n ∩ goodS n ∩ goodAo n`: the hidden event; `pap_charge`:
  `Pr(GPapᶜ) ≤ 0.00163204 ≤ 0.001900001`.
* `pap_frame`: the frame bound `1.36/n ≤ 1.377/n` for the centre `b_W` on `GPap n`.
* `pap_window`, `pap_tau`, `pap_q`, `pap_qL2`: the hypotheses of `pert_moment`.
* `pap_moment`: a majorant of `E_u H_u²` with restricted mean `≤ 7.37·10⁻⁹ ≤ v_W`.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN mW_ge_pow42 cHat2)
open BstLean.Part140
open BstLean.Part143 (nsq_div_mW_le128)
open BstLean.Part156 BstLean.Part157

variable {n : ℕ}

/-- **The hypothesis on the computed constant `κ̃`** of the paper's program:
`(κ̃ − κ₁)²·m_W ≤ 10⁻⁸`, `κ₁ = kap1 (2n) = κ(E_u κ(u₁))`. -/
def ConstK (n : ℕ) : Prop := (kapT n - kap1 (2 * n)) ^ 2 * (mW n : ℝ) ≤ 1 / 10 ^ 8

/-- **The hidden World event for the centre of the paper.** -/
def GPap (n : ℕ) : Set (WHid n) := goodHat n ∩ goodS n ∩ goodAo n

lemma measurableSet_GPap (hn : 1 ≤ n) : MeasurableSet (GPap n) :=
  ((goodHat_meas hn).inter measurableSet_goodS).inter measurableSet_goodAo

/-- The bound of the hidden charge for the centre of the paper: `0.00163204`. -/
noncomputable def δPap : ℝ := 163204 / 10 ^ 8

lemma δPap_le : δPap ≤ δhidL := by unfold δPap δhidL; norm_num

/-- **The hidden charge for the centre of the paper**: `Pr((GPap n)ᶜ) ≤ 0.00163204`,
`n ≥ 16 384`. -/
theorem pap_charge (hn : 16384 ≤ n) : (hidGauss (2 * n) (mW n)).real (GPap n)ᶜ ≤ δPap := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h1 := hat_charge hn
  have h2 := goodS_charge (n := n) (by omega) hm
  have h3 := goodAo_charge hn4
  have hsub : (GPap n)ᶜ ⊆ ((goodHat n)ᶜ ∪ (goodS n)ᶜ) ∪ (goodAo n)ᶜ := by
    intro θ hθ
    simp only [GPap, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have h5 : (10 : ℝ) ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) ≤ 1 / 10 ^ 8 := by
    have e : (10 : ℝ) ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) =
        10 ^ 6 / ((n : ℝ) * (mW n : ℝ)) := by
      rw [hNcast]; field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  unfold δPap
  unfold δHat at h1
  have h6 : (163194 / 10 ^ 8 : ℝ) + 1 / 10 ^ 8 + 9 / 10 ^ 8 ≤ 163204 / 10 ^ 8 := by norm_num
  linarith

/-- `c = 2n/(S_W κ̃²)`: the calibration constant of the scalar `τ₀` of the paper. -/
noncomputable def ccP (n : ℕ) (θ : WHid n) : ℝ := 2 * (n : ℝ) / (SWp θ * kapT n ^ 2)

lemma measurable_ccP : Measurable (ccP n) :=
  measurable_const.div (measurable_SWp.mul_const _)

/-- `tau0p` in the form `√(B·max 0 (B·c − 1))`, `B = t_W|b_W|²`. -/
lemma tau0p_eq (θ : WHid n) :
    tau0p θ = √(2 / (mW n : ℝ) * normSq (bWp θ) *
      max 0 (2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ - 1)) := by
  unfold tau0p ccP
  congr 3
  ring

/-- The scalar of the paper where `B·c > 1`: `τ₀² = B(B·c − 1)` and `τ₀ > 0`. -/
lemma tau0p_of {θ : WHid n} (h1 : 1 < 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ) :
    tau0p θ ^ 2 = 2 / (mW n : ℝ) * normSq (bWp θ) *
      (2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ - 1) ∧ 0 < tau0p θ := by
  have hBnn : 0 ≤ 2 / (mW n : ℝ) * normSq (bWp θ) :=
    mul_nonneg (by positivity) (normSq_nonneg _)
  have hBpos : 0 < 2 / (mW n : ℝ) * normSq (bWp θ) := by
    rcases hBnn.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at h1; norm_num at h1
    · exact h0
  have hw : 0 < 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ - 1 := by linarith
  rw [tau0p_eq, max_eq_right hw.le]
  exact ⟨Real.sq_sqrt (mul_nonneg hBpos.le hw.le), Real.sqrt_pos.mpr (mul_pos hBpos hw)⟩

section consts

variable (hn : 13225 ≤ n) (hK : ConstK n)

include hn hK

/-- The window of `κ̃` from `ConstK`: `|κ̃ − κ₁| ≤ 10⁻⁴·√(1/m_W) ≤ 10⁻⁷`, so
`0.493719 ≤ κ̃ ≤ 0.493801`. -/
lemma kapT_window :
    |kapT n - kap1 (2 * n)| ≤ 1 / 10 ^ 4 * √(1 / (mW n : ℝ)) ∧
      493719 / 1000000 ≤ kapT n ∧ kapT n ≤ 493801 / 1000000 := by
  have hn4 : 4096 ≤ n := by omega
  have hmM := mW_ge_million hn4
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hmpos : (0 : ℝ) < mW n := by linarith
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  have hK' : (kapT n - kap1 (2 * n)) ^ 2 * (mW n : ℝ) ≤ 1 / 10 ^ 8 := hK
  have h1 : (kapT n - kap1 (2 * n)) ^ 2 ≤ (1 / 10 ^ 4 * √(1 / (mW n : ℝ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have e : (1 / 10 ^ 4 : ℝ) ^ 2 * (1 / (mW n : ℝ)) = 1 / 10 ^ 8 / (mW n : ℝ) := by ring
    rw [e, le_div_iff₀ hmpos]
    exact hK'
  have h2 : |kapT n - kap1 (2 * n)| ≤ 1 / 10 ^ 4 * √(1 / (mW n : ℝ)) :=
    abs_le_of_sq_le_sq h1 (by positivity)
  have h3 : √(1 / (mW n : ℝ)) ≤ 1 / 1000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hmpos]
    nlinarith
  have h4 := abs_le.mp h2
  refine ⟨h2, ?_, ?_⟩ <;> nlinarith

end consts

section world

variable (hn : 16384 ≤ n) (hC : ConstC n) (hK : ConstK n) {θ : WHid n} (hθ : θ ∈ GPap n)

include hn hC hK hθ

omit hK in
/-- The window of `B = t_W|b_W|²` on `GPap n`: `0.48687·γ ≤ B ≤ 0.50078·γ`. -/
lemma pap_B :
    2 / ((2 * n : ℕ) : ℝ) * (48687 / 100000) ≤ 2 / (mW n : ℝ) * normSq (bWp θ) ∧
      2 / (mW n : ℝ) * normSq (bWp θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * (50078 / 100000) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by rw [hNcast]; linarith
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  have ht : (0 : ℝ) ≤ 2 / (mW n : ℝ) := by positivity
  obtain ⟨hb1, hb2⟩ := Bh_window_16 hn hθ.1.1
  unfold Bh at hb1 hb2
  have hd := bWp_dist (by omega) hC hθ.1.2 hθ.2
  set δ := bWp θ - bhat θ with hδ
  have hdm : 2 / (mW n : ℝ) * normSq δ ≤ 2 / ((2 * n : ℕ) : ℝ) * (2 / 10 ^ 14) := by
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ hγ.le)
    rw [div_le_iff₀ hmpos]
    nlinarith
  have e1 : bWp θ = bhat θ + δ := by rw [hδ]; abel
  have e2 : bhat θ = bWp θ + (-δ) := by rw [hδ]; abel
  have hneg : normSq (-δ) = normSq δ := by simp [normSq]
  have h1 := normSq_add_eta (η := 1 / 10 ^ 6) (by norm_num) (bhat θ) δ
  rw [← e1] at h1
  have h2 := normSq_add_eta (η := 1 / 10 ^ 6) (by norm_num) (bWp θ) (-δ)
  rw [← e2, hneg] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 ht
  have h2' := mul_le_mul_of_nonneg_left h2 ht
  have hδ0 : 0 ≤ 2 / (mW n : ℝ) * normSq δ := mul_nonneg ht (normSq_nonneg _)
  set γ := (2 : ℝ) / ((2 * n : ℕ) : ℝ) with hγdef
  set Bb := 2 / (mW n : ℝ) * normSq (bWp θ) with hBb
  set Bh' := 2 / (mW n : ℝ) * normSq (bhat θ) with hBh
  set Dd := 2 / (mW n : ℝ) * normSq δ with hDd
  have h1'' : Bb ≤ (1 + 1 / 10 ^ 6) * Bh' + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
    have : 2 / (mW n : ℝ) * ((1 + 1 / 10 ^ 6) * normSq (bhat θ) +
        (1 + 1 / (1 / 10 ^ 6 : ℝ)) * normSq δ) =
        (1 + 1 / 10 ^ 6) * Bh' + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
      rw [hBh, hDd]; ring
    linarith
  have h2'' : Bh' ≤ (1 + 1 / 10 ^ 6) * Bb + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
    have : 2 / (mW n : ℝ) * ((1 + 1 / 10 ^ 6) * normSq (bWp θ) +
        (1 + 1 / (1 / 10 ^ 6 : ℝ)) * normSq δ) =
        (1 + 1 / 10 ^ 6) * Bb + (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd := by
      rw [hBb, hDd]; ring
    linarith
  have h3 : (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd ≤ γ * (3 / 10 ^ 8) := by
    have : (1 + 1 / (1 / 10 ^ 6 : ℝ)) * Dd ≤ (1 + 1 / (1 / 10 ^ 6 : ℝ)) * (γ * (2 / 10 ^ 14)) :=
      mul_le_mul_of_nonneg_left hdm (by norm_num)
    nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **The window of `B·c`** for the scalar of the paper on `GPap n`: `1.994 ≤ B·c ≤ 2.057`, and
`c ≥ 0`. -/
lemma pap_window :
    0 ≤ ccP n θ ∧ 1994 / 1000 ≤ 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ∧
      2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ≤ 2057 / 1000 := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hκ1, hκ2⟩ := kapT_window (by omega) hK
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hθ.1.2
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  obtain ⟨hB1, hB2⟩ := pap_B hn hC hθ
  rw [hNcast] at hB1 hB2
  set Bb := 2 / (mW n : ℝ) * normSq (bWp θ) with hBb
  have hκ0 : 0 < kapT n := by linarith
  have hSκ : 0 < SWp θ * kapT n ^ 2 := by positivity
  have hκsq1 : (493719 / 1000000 : ℝ) ^ 2 ≤ kapT n ^ 2 := pow_le_pow_left₀ (by norm_num) hκ1 2
  have hκsq2 : kapT n ^ 2 ≤ (493801 / 1000000 : ℝ) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
  have hSκ1 : 1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2 ≤ SWp θ * kapT n ^ 2 :=
    mul_le_mul hS1 hκsq1 (by norm_num) (by linarith)
  have hSκ2 : SWp θ * kapT n ^ 2 ≤ 2002 / 1000 * (493801 / 1000000 : ℝ) ^ 2 :=
    mul_le_mul hS2 hκsq2 (sq_nonneg _) (by norm_num)
  have hcc0 : 0 ≤ ccP n θ := by unfold ccP; positivity
  have e : Bb * ccP n θ = Bb * (2 * (n : ℝ)) / (SWp θ * kapT n ^ 2) := by
    unfold ccP; ring
  have hBn1 : 2 * (48687 / 100000 : ℝ) ≤ Bb * (2 * (n : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hB1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have e2 : 2 / (2 * (n : ℝ)) * (48687 / 100000) * (2 * (n : ℝ)) = 2 * (48687 / 100000) := by
      field_simp
    linarith
  have hBn2 : Bb * (2 * (n : ℝ)) ≤ 2 * (50078 / 100000 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hB2 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
    have e2 : 2 / (2 * (n : ℝ)) * (50078 / 100000) * (2 * (n : ℝ)) = 2 * (50078 / 100000) := by
      field_simp
    linarith
  refine ⟨hcc0, ?_, ?_⟩
  · rw [e, le_div_iff₀ hSκ]
    have : (1994 / 1000 : ℝ) * (2002 / 1000 * (493801 / 1000000 : ℝ) ^ 2) ≤
        2 * (48687 / 100000) := by norm_num
    nlinarith
  · rw [e, div_le_iff₀ hSκ]
    have : 2 * (50078 / 100000 : ℝ) ≤
        2057 / 1000 * (1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2) := by norm_num
    nlinarith

/-- The scalar of the paper on `GPap n`: `τ₀² = B(B·c − 1)` and `τ₀ > 0`. -/
lemma pap_tau :
    tau0p θ ^ 2 = 2 / (mW n : ℝ) * normSq (bWp θ) *
      (2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ - 1) ∧ 0 < tau0p θ := by
  obtain ⟨-, hA1, -⟩ := pap_window hn hC hK hθ
  exact tau0p_of (by linarith)

end world

/-- `q² = (2/S_W)(κ₁/κ̃)²` on `goodS n`, `q ≤ 1.001`, and
`|q − 1| ≤ 1.002·|S_W/2 − 1| + 4.07·|κ̃ − κ₁|` (every `n ≥ 13 225`). -/
lemma pap_q (hn : 13225 ≤ n) (hK : ConstK n) {θ : WHid n} (hθS : θ ∈ goodS n) :
    qOf n (ccP n) θ ≤ 1001 / 1000 ∧
      |qOf n (ccP n) θ - 1| ≤
        1002 / 1000 * |SWp θ / 2 - 1| + 407 / 100 * |kapT n - kap1 (2 * n)| := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hκ1, hκ2⟩ := kapT_window hn hK
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hθS
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 1998 / 1000 ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2002 / 1000 := by linarith
  have hκ0 : 0 < kapT n := by linarith
  have hk0 : 0 < kap1 (2 * n) := by linarith
  have hSκ : 0 < SWp θ * kapT n ^ 2 := by positivity
  have hκsq1 : (493719 / 1000000 : ℝ) ^ 2 ≤ kapT n ^ 2 := pow_le_pow_left₀ (by norm_num) hκ1 2
  have hSκ1 : 1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2 ≤ SWp θ * kapT n ^ 2 :=
    mul_le_mul hS1 hκsq1 (by norm_num) (by linarith)
  set q := qOf n (ccP n) θ with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 2 * kap1 (2 * n) ^ 2 / (SWp θ * kapT n ^ 2) := by
    rw [hq]
    unfold qOf
    rw [Real.sq_sqrt (by unfold ccP; positivity), hNcast]
    unfold ccP
    field_simp
  -- `q² − 1`
  have hnum : |2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2| ≤
      198 / 100 * |kapT n - kap1 (2 * n)| + 4878 / 10000 * |SWp θ / 2 - 1| := by
    have e : 2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2 =
        -(2 * (kapT n - kap1 (2 * n)) * (kapT n + kap1 (2 * n))) +
          -(2 * (SWp θ / 2 - 1) * kapT n ^ 2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_neg, abs_mul, abs_mul, abs_mul, abs_mul]
    have a1 : |kapT n + kap1 (2 * n)| ≤ 99 / 100 := by
      rw [abs_of_pos (by linarith)]
      linarith
    have a2 : |kapT n ^ 2| ≤ 2439 / 10000 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := pow_le_pow_left₀ hκ0.le hκ2 2
      nlinarith
    have a3 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [a3]
    have b1 : 2 * |kapT n - kap1 (2 * n)| * |kapT n + kap1 (2 * n)| ≤
        2 * |kapT n - kap1 (2 * n)| * (99 / 100) :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have b2 : 2 * |SWp θ / 2 - 1| * |kapT n ^ 2| ≤ 2 * |SWp θ / 2 - 1| * (2439 / 10000) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    linarith
  have hq21 : |q ^ 2 - 1| ≤
      407 / 100 * |kapT n - kap1 (2 * n)| + 1002 / 1000 * |SWp θ / 2 - 1| := by
    have e : q ^ 2 - 1 = (2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2) / (SWp θ * kapT n ^ 2) := by
      rw [hq2]; field_simp
    rw [e, abs_div, abs_of_pos hSκ, div_le_iff₀ hSκ]
    refine hnum.trans ?_
    have c1 : (487 / 1000 : ℝ) ≤ SWp θ * kapT n ^ 2 := by
      refine le_trans (by norm_num) hSκ1
    have d1 : 0 ≤ |kapT n - kap1 (2 * n)| := abs_nonneg _
    have d2 : 0 ≤ |SWp θ / 2 - 1| := abs_nonneg _
    nlinarith [mul_nonneg d1 (sub_nonneg.mpr c1), mul_nonneg d2 (sub_nonneg.mpr c1)]
  have hq1 : |q - 1| ≤ |q ^ 2 - 1| := by
    have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [e, abs_mul, abs_of_pos (by linarith : 0 < q + 1)]
    nlinarith [abs_nonneg (q - 1)]
  refine ⟨?_, by linarith⟩
  -- `q ≤ 1.001`
  have hq2le : q ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 := by
    rw [hq2, div_le_iff₀ hSκ]
    have h1 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hk0.le hk2 2
    have h2 : 2 * (4938 / 10000 : ℝ) ^ 2 ≤
        (1001 / 1000 : ℝ) ^ 2 * (1998 / 1000 * (493719 / 1000000 : ℝ) ^ 2) := by norm_num
    nlinarith
  exact le_of_abs_le (abs_le_of_sq_le_sq hq2le (by norm_num))

/-- The `L²` bound of the calibration ratio on `GPap n`: `ρ₂ = 0.0092·√(1/m_W)`. -/
noncomputable def ρPap (n : ℕ) : ℝ := 92 / 10000 * √(1 / (mW n : ℝ))

/-- **`‖1_{GPap}·(q − 1)‖₂ ≤ 0.0092·√(1/m_W)`** for the scalar of the paper (every
`n ≥ 13 225`). -/
theorem pap_qL2 (hn : 13225 ≤ n) (hK : ConstK n) :
    L2le (hidGauss (2 * n) (mW n)) ((GPap n).indicator fun θ => qOf n (ccP n) θ - 1)
      (ρPap n) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨hκe, -, -⟩ := kapT_window hn hK
  have hS := SWp_L2 (n := n) (by omega) hm
  have mS : Measurable (fun θ : WHid n => |SWp θ / 2 - 1|) :=
    ((measurable_SWp.div_const 2).sub_const 1).abs
  have hSabs : L2le (hidGauss (2 * n) (mW n)) (fun θ : WHid n => |SWp θ / 2 - 1|)
      (√(2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ)))) :=
    L2le.of_abs_le mS.aestronglyMeasurable hS fun θ => by rw [abs_abs]
  have h1 := hSabs.const_mul_nonneg (c := 1002 / 1000) (by norm_num)
  set c0 : ℝ := 407 / 100 * |kapT n - kap1 (2 * n)| with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; positivity
  have h2 := L2le.const (μ := hidGauss (2 * n) (mW n)) c0
  have h3 := h1.add' h2 (by positivity) (abs_nonneg _)
  have mq : Measurable ((GPap n).indicator fun θ => qOf n (ccP n) θ - 1) :=
    ((measurable_qOf measurable_ccP).sub_const 1).indicator (measurableSet_GPap (by omega))
  have h4 : L2le (hidGauss (2 * n) (mW n)) ((GPap n).indicator fun θ => qOf n (ccP n) θ - 1)
      (1002 / 1000 * √(2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) + |c0|) := by
    refine L2le.of_abs_le mq.aestronglyMeasurable h3 fun θ => ?_
    have hg0 : 0 ≤ 1002 / 1000 * |SWp θ / 2 - 1| + c0 := by positivity
    refine le_trans ?_ (le_abs_self _)
    by_cases hθ : θ ∈ GPap n
    · rw [Set.indicator_of_mem hθ]
      exact (pap_q hn hK hθ.1.2).2
    · rw [Set.indicator_of_notMem hθ, abs_zero]
      exact hg0
  refine h4.mono (by positivity) ?_
  unfold ρPap
  rw [abs_of_nonneg hc00]
  have e1 : √(2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) = √(1 / (n : ℝ)) * √(1 / (mW n : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity), hNcast]
    congr 1
    field_simp
  have e2 : √(1 / (n : ℝ)) ≤ 1 / 115 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hnpos]
    nlinarith
  have hr : 0 ≤ √(1 / (mW n : ℝ)) := Real.sqrt_nonneg _
  rw [e1]
  have h5 : 1002 / 1000 * (√(1 / (n : ℝ)) * √(1 / (mW n : ℝ))) ≤
      1002 / 1000 * (1 / 115 * √(1 / (mW n : ℝ))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 hr) (by norm_num)
  have h6 : c0 ≤ 407 / 100 * (1 / 10 ^ 4 * √(1 / (mW n : ℝ))) :=
    mul_le_mul_of_nonneg_left hκe (by norm_num)
  nlinarith

/-- **The frame bound for the centre of the paper**: `1.36/n` on `GPap n`, `n ≥ 16 384`, IF
`ConstC n`. -/
theorem pap_frame (hn : 16384 ≤ n) (hC : ConstC n) {θ : WHid n} (hθ : θ ∈ GPap n)
    (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bWp θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      136 / 100 / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hm42 : (4398046511104 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_pow42 hn4
  have hmpos : (0 : ℝ) < mW n := by linarith
  have hd := bWp_dist (by omega) hC hθ.1.2 hθ.2
  refine pert_frame hn hθ.1.1 (e₁ := 645 / 10 ^ 4 * (n : ℝ) / (mW n : ℝ)) ?_ ?_ w
  · have h := nsq_div_mW_le128 hn
    have e : 645 / 10 ^ 4 * (n : ℝ) / (mW n : ℝ) =
        645 / 10 ^ 4 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) := by field_simp
    rw [e, div_le_iff₀ hnpos]
    have h2 : 1 / (128 * (n : ℝ)) ≤ 1 / (128 * 16384) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    nlinarith
  · refine hd.trans (le_of_eq ?_)
    field_simp

end BstLean.Part159

open BstLean.Part159 in
#print axioms pap_charge
open BstLean.Part159 in
#print axioms pap_window
open BstLean.Part159 in
#print axioms pap_tau
open BstLean.Part159 in
#print axioms pap_q
open BstLean.Part159 in
#print axioms pap_qL2
open BstLean.Part159 in
#print axioms pap_frame
