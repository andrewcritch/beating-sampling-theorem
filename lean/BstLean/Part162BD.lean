import BstLean.Part162Pap

/-!
# Part 162, item 3: removal and displacement prices; FL from the latitude moments only

Role: `delegations/statements/p162-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, proof of Proposition `t7:p07:FL`
("LG and Markov give `E_s β(s) ≤ B = 2·4^{−24} + β_low`"; the displacement price `𝒟`, with
Lemma `t7:p07:gaussian`, the mean shift and Cauchy–Schwarz in `s`).

* `idx_disp`: the displacement on one latitude, `H² ≤ β·[C Var λ/(2(1−η)σ_l²) +
  n Var S/(8(1−η)²σ_l⁴)]`.
* `markov_pow`, `removed_le`, `int_removed`: the removal price `Bpap`.
* `int_disp`: the displacement price `Dpap = √B·[C_A V_l/(2(1−η)σ_l²) + n V_S/(8(1−η)²σ_l⁴)]`.
* **`fluct_paper_mom`**: `FLUCT_chi_hyp` for `dPaper` from the latitude moments of `λ`, `σ`,
  `S`, the mass below the floor, `|c_A|² ≤ C_A`, and the numeric root sum.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

section idxD

variable {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν] {G : Set V}

/-- **The displacement on one latitude** (proof of Prop. `t7:p07:FL`, the price `𝒟`): with
`β = 1 − ν(G) ≤ η < 1`, `ψ ≥ σ_l > 0` on `G`, `C ≥ 0`:
`H²(N(E(φ|G)c, E(ψ²|G)), N((Eφ)c, Eψ²)) ≤ β·[C·Var φ/(2(1−η)σ_l²) + n·Var ψ²/(8(1−η)²σ_l⁴)]`
(with `|c|² = C`; Lemma `t7:p07:gaussian` and the mean shift). -/
lemma idx_disp (n : ℕ) (hG : MeasurableSet G) (hm : 0 < ν.real G) {φ ψ : V → ℝ}
    (mφ : Measurable φ) (mψ : Measurable ψ) {Mφ Mψ : ℝ} (bφ : ∀ v, |φ v| ≤ Mφ)
    (bψ : ∀ v, |ψ v| ≤ Mψ) {σl η C : ℝ} (hσl : 0 < σl) (hGψ : ∀ v ∈ G, σl ≤ ψ v)
    (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) (hC : 0 ≤ C) :
    BstLean.Part161.hellG2 n ((∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C)
        (∫ v, ψ v ^ 2 ∂nrm ν G) (∫ v, ψ v ^ 2 ∂ν) ≤
      (1 - ν.real G) * (C * (∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν) / (2 * (1 - η) * σl ^ 2) +
        n * (∫ v, (ψ v ^ 2 - ∫ w, ψ w ^ 2 ∂ν) ^ 2 ∂ν) / (8 * (1 - η) ^ 2 * σl ^ 4)) := by
  have hP := nrm_prob ν hG hm
  set m := ν.real G with hmd
  have hm1 : m ≤ 1 := measureReal_le_one
  have hη0 : 0 < 1 - η := by linarith
  set S0 := ∫ v, ψ v ^ 2 ∂nrm ν G
  set Sb := ∫ v, ψ v ^ 2 ∂ν
  have b2 := sq_bound_of_abs bψ
  have hS0 : σl ^ 2 ≤ S0 := (nrm_mean_mem hG hm (mψ.pow_const 2) b2 (hi := Mψ ^ 2)
    fun v hv => ⟨pow_le_pow_left₀ hσl.le (hGψ v hv) 2, by
      have := b2 v; rw [abs_of_nonneg (sq_nonneg _)] at this; exact this⟩).1
  have hS0p : 0 < S0 := lt_of_lt_of_le (by positivity) hS0
  have i2 : Integrable (fun v => ψ v ^ 2) ν := intB (mψ.pow_const 2) b2
  have hSb : m * S0 ≤ Sb := by
    have e : m * S0 = ∫ v, G.indicator (fun v => ψ v ^ 2) v ∂ν := by
      simp only [S0]; rw [integral_nrm ν hG hm, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
    rw [e]
    exact integral_mono (i2.indicator hG) i2 fun v => by
      by_cases hv : v ∈ G
      · simp [Set.indicator_of_mem hv]
      · simp only [Set.indicator_of_notMem hv]; exact sq_nonneg _
  have hSbp : 0 < Sb := lt_of_lt_of_le (by positivity) hSb
  have hd0 : 0 ≤ (∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C := by positivity
  have hH := BstLean.Part161.hellG2_le n hS0p hSbp hd0
  refine hH.trans ?_
  -- the two mean shifts
  have sh1 := mean_shift hG hm mφ bφ
  have sh2 := mean_shift hG hm (mψ.pow_const 2) b2
  rw [← hmd] at sh1 sh2
  set Vφ := ∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν
  set VS := ∫ v, (ψ v ^ 2 - ∫ w, ψ w ^ 2 ∂ν) ^ 2 ∂ν
  have hVφ : 0 ≤ Vφ := integral_nonneg fun v => sq_nonneg _
  have hVS : 0 ≤ VS := integral_nonneg fun v => sq_nonneg _
  have hmη : (1 - η) ≤ m := hη
  have hβ0 : 0 ≤ 1 - m := by linarith
  -- location term
  have t2 : (∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C / (2 * (S0 + Sb)) ≤
      (1 - m) * (C * Vφ / (2 * (1 - η) * σl ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    have k1 : (∫ v, φ v ∂nrm ν G - ∫ v, φ v ∂ν) ^ 2 * C ≤ (1 - m) / m * Vφ * C :=
      mul_le_mul_of_nonneg_right sh1 hC
    have k2 : (1 - m) / m * Vφ * C ≤ (1 - m) * (C * Vφ / (2 * (1 - η) * σl ^ 2)) *
        (2 * (S0 + Sb)) := by
      have h3 : (1 - η) * σl ^ 2 ≤ m * (S0 + Sb) := by
        have : (1 - η) * σl ^ 2 ≤ m * S0 := mul_le_mul hmη hS0 (by positivity) (by linarith)
        nlinarith
      have key : 1 / m ≤ (S0 + Sb) / ((1 - η) * σl ^ 2) := by
        rw [div_le_div_iff₀ hm (by positivity)]; linarith
      have hX : 0 ≤ (1 - m) * Vφ * C := by positivity
      calc (1 - m) / m * Vφ * C = (1 - m) * Vφ * C * (1 / m) := by ring
        _ ≤ (1 - m) * Vφ * C * ((S0 + Sb) / ((1 - η) * σl ^ 2)) :=
            mul_le_mul_of_nonneg_left key hX
        _ = (1 - m) * (C * Vφ / (2 * (1 - η) * σl ^ 2)) * (2 * (S0 + Sb)) := by
            field_simp
    linarith
  -- scale term
  have t1 : n * (S0 / Sb - 1) ^ 2 / (8 * (S0 / Sb)) ≤
      (1 - m) * (n * VS / (8 * (1 - η) ^ 2 * σl ^ 4)) := by
    have e : n * (S0 / Sb - 1) ^ 2 / (8 * (S0 / Sb)) = n * (S0 - Sb) ^ 2 / (8 * (S0 * Sb)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have k1 : (S0 - Sb) ^ 2 ≤ (1 - m) / m * VS := by
      have := sh2; rw [sub_sq'] at this ⊢; linarith
    have k3 : (1 - η) ^ 2 * σl ^ 4 ≤ m * (S0 * Sb) := by
      have q1 : (1 - η) * σl ^ 2 ≤ m * S0 := mul_le_mul hmη hS0 (by positivity) (by linarith)
      have q2 : (1 - η) * σl ^ 2 ≤ Sb := q1.trans hSb
      have : (1 - η) ^ 2 * σl ^ 4 = ((1 - η) * σl ^ 2) * ((1 - η) * σl ^ 2) := by ring
      rw [this]
      calc ((1 - η) * σl ^ 2) * ((1 - η) * σl ^ 2) ≤ (m * S0) * Sb :=
            mul_le_mul q1 q2 (by positivity) (by positivity)
        _ = m * (S0 * Sb) := by ring
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc n * (S0 - Sb) ^ 2 ≤ n * ((1 - m) / m * VS) := mul_le_mul_of_nonneg_left k1 hn0
      _ = (1 - m) * (n * VS) / m := by ring
      _ ≤ (1 - m) * (n * VS / (8 * (1 - η) ^ 2 * σl ^ 4)) * (8 * (S0 * Sb)) := by
        rw [div_le_iff₀ hm]
        have h0 : 0 ≤ (1 - m) * (n * VS) := by positivity
        have e2 : (1 - m) * (n * VS / (8 * (1 - η) ^ 2 * σl ^ 4)) * (8 * (S0 * Sb)) * m =
            (1 - m) * (n * VS) * (m * (S0 * Sb) / ((1 - η) ^ 2 * σl ^ 4)) := by
          field_simp
        rw [e2]
        have : 1 ≤ m * (S0 * Sb) / ((1 - η) ^ 2 * σl ^ 4) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith
  linarith

end idxD

/-- Markov: `ν(|Y| > w) ≤ E|Y|^p / w^p` for a bounded measurable `Y`, `w > 0`. -/
lemma markov_pow {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν]
    {Y : V → ℝ} (hY : Measurable Y) {M : ℝ} (hM : ∀ v, |Y v| ≤ M) {w : ℝ} (hw : 0 < w) (p : ℕ) :
    ν.real {v | w < |Y v|} ≤ (∫ v, |Y v| ^ p ∂ν) / w ^ p := by
  have hi : Integrable (fun v => |Y v| ^ p) ν := intB (hY.abs.pow_const p) (abs_pow_bound hM p)
  have h := mul_meas_ge_le_integral_of_nonneg (μ := ν)
    (Filter.Eventually.of_forall fun v => pow_nonneg (abs_nonneg (Y v)) p) hi (w ^ p)
  have hsub : {v | w < |Y v|} ⊆ {v | w ^ p ≤ |Y v| ^ p} := fun v hv =>
    pow_le_pow_left₀ hw.le (le_of_lt hv) p
  rw [le_div_iff₀ (pow_pos hw p), mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg hw.le p)).trans h

section paperBD

open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161

variable {n : ℕ}

/-- **The removed mass on one latitude** (proof of Prop. `t7:p07:FL`): Markov on the two windows
and the mass below the floor. -/
lemma removed_le (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl : ℝ} (hwl : 0 < wl)
    (hws : 0 < ws) (p : ℕ) (a : Ix n) :
    removed (stdGauss (Fin (n - 1))) (goodP D c wl ws σl) a ≤
      (∫ v, |lA D c a v - lbar D c a| ^ p ∂stdGauss (Fin (n - 1))) / wl ^ p +
        (∫ v, |sgA D c a v - gbar D c a| ^ p ∂stdGauss (Fin (n - 1))) / ws ^ p +
        (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} := by
  set ν := stdGauss (Fin (n - 1))
  have hsub : {v | (a, v) ∉ goodP D c wl ws σl} ⊆
      ({v | wl < |lA D c a v - lbar D c a|} ∪ {v | ws < |sgA D c a v - gbar D c a|}) ∪
        {v | sgA D c a v < σl} := by
    intro v hv
    simp only [goodP, Set.mem_setOf_eq, not_and_or, not_le] at hv
    rcases hv with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hgb : ∀ a, |gbar D c a| ≤ lipSig D c := fun a => by
    unfold gbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sgA D c a v| ∂ν ≤ ∫ _v, lipSig D c ∂ν :=
          integral_mono (intB (measurable_sgA_left D c a).abs (M := lipSig D c) fun v => by
            rw [abs_abs]; exact abs_sgA_le hn D c a v) (integrable_const _) (abs_sgA_le hn D c a)
      _ = lipSig D c := by simp
  have hlb : ∀ a, |lbar D c a| ≤ lipLam D c := fun a => by
    unfold lbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |lA D c a v| ∂ν ≤ ∫ _v, lipLam D c ∂ν :=
          integral_mono (intB (measurable_lA_left D c a).abs (M := lipLam D c) fun v => by
            rw [abs_abs]; exact abs_lA_le hn D c a v) (integrable_const _) (abs_lA_le hn D c a)
      _ = lipLam D c := by simp
  have m1 := markov_pow (ν := ν) ((measurable_lA_left D c a).sub_const (lbar D c a))
    (M := lipLam D c + lipLam D c) (fun v => (abs_sub _ _).trans
      (by linarith [abs_lA_le hn D c a v, hlb a])) hwl p
  have m2 := markov_pow (ν := ν) ((measurable_sgA_left D c a).sub_const (gbar D c a))
    (M := lipSig D c + lipSig D c) (fun v => (abs_sub _ _).trans
      (by linarith [abs_sgA_le hn D c a v, hgb a])) hws p
  calc removed ν (goodP D c wl ws σl) a = ν.real {v | (a, v) ∉ goodP D c wl ws σl} := rfl
    _ ≤ ν.real (({v | wl < |lA D c a v - lbar D c a|} ∪ {v | ws < |sgA D c a v - gbar D c a|}) ∪
        {v | sgA D c a v < σl}) := measureReal_mono hsub
    _ ≤ ν.real ({v | wl < |lA D c a v - lbar D c a|} ∪ {v | ws < |sgA D c a v - gbar D c a|}) +
        ν.real {v | sgA D c a v < σl} := measureReal_union_le _ _
    _ ≤ ν.real {v | wl < |lA D c a v - lbar D c a|} + ν.real {v | ws < |sgA D c a v - gbar D c a|} +
        ν.real {v | sgA D c a v < σl} := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ _ := by gcongr

/-- The removal price `B = (τ_{l,q}/w_l)^q + (τ_{s,q}/w_s)^q + β_low` (paper: `2·4^{−24} + β_low`
with `q = 24`, `w = 4τ_24`). -/
noncomputable def Bpap (wl ws tl ts βlow : ℝ) (q : ℕ) : ℝ := (tl / wl) ^ q + (ts / ws) ^ q + βlow

/-- The displacement price `𝒟 = √B·[C_A V_l/(2(1−η)σ_l²) + n V_S/(8(1−η)²σ_l⁴)]`. -/
noncomputable def Dpap (n : ℕ) (B CA Vl VS η σl : ℝ) : ℝ :=
  √B * (CA * Vl / (2 * (1 - η) * σl ^ 2) + n * VS / (8 * (1 - η) ^ 2 * σl ^ 4))

/-- **The removal price** for the paper's good set. -/
lemma int_removed (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl : ℝ} (hwl : 0 < wl)
    (hws : 0 < ws) (q : ℕ) {tl ts βlow : ℝ}
    (hlq : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl ^ q)
    (hsq : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts ^ q)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow) :
    ∫ a, removed (stdGauss (Fin (n - 1))) (goodP D c wl ws σl) a ∂muI n ≤
      Bpap wl ws tl ts βlow q := by
  set ν := stdGauss (Fin (n - 1))
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mYs : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => sgA D c p.1 p.2 - gbar D c p.1) :=
    (measurable_sgA D c).sub ((measurable_gbar D c).comp measurable_fst)
  have mYl : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => lA D c p.1 p.2 - lbar D c p.1) :=
    (measurable_lA D c).sub ((measurable_lbar D c).comp measurable_fst)
  have mMl := mInt (mYl.abs.pow_const q)
  have mMs := mInt (mYs.abs.pow_const q)
  have mmass : Measurable (fun a => ν.real {v | sgA D c a v < σl}) :=
    (measurable_measure_prodMk_left (ν := ν)
      (measurableSet_lt (measurable_sgA D c) measurable_const)).ennreal_toReal
  have hgb : ∀ a, |gbar D c a| ≤ lipSig D c := fun a => by
    unfold gbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sgA D c a v| ∂ν ≤ ∫ _v, lipSig D c ∂ν :=
          integral_mono (intB (measurable_sgA_left D c a).abs (M := lipSig D c) fun v => by
            rw [abs_abs]; exact abs_sgA_le hn D c a v) (integrable_const _) (abs_sgA_le hn D c a)
      _ = lipSig D c := by simp
  have hlb : ∀ a, |lbar D c a| ≤ lipLam D c := fun a => by
    unfold lbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |lA D c a v| ∂ν ≤ ∫ _v, lipLam D c ∂ν :=
          integral_mono (intB (measurable_lA_left D c a).abs (M := lipLam D c) fun v => by
            rw [abs_abs]; exact abs_lA_le hn D c a v) (integrable_const _) (abs_lA_le hn D c a)
      _ = lipLam D c := by simp
  have bInt : ∀ {f : (Fin (n - 1) → ℝ) → ℝ} {M : ℝ}, Measurable f → (∀ v, 0 ≤ f v) →
      (∀ v, f v ≤ M) → 0 ≤ ∫ v, f v ∂ν ∧ ∫ v, f v ∂ν ≤ M := fun {f} {M} hf h0 hM => by
    refine ⟨integral_nonneg h0, ?_⟩
    calc ∫ v, f v ∂ν ≤ ∫ _v, M ∂ν :=
          integral_mono (intB hf (M := M) fun v => by rw [abs_of_nonneg (h0 v)]; exact hM v)
            (integrable_const _) hM
      _ = M := by simp
  have bMl : ∀ a, |∫ v, |lA D c a v - lbar D c a| ^ q ∂ν| ≤ (2 * lipLam D c) ^ q := fun a => by
    obtain ⟨h0, h1⟩ := bInt (M := (2 * lipLam D c) ^ q)
      (((measurable_lA_left D c a).sub_const (lbar D c a)).abs.pow_const q)
      (fun v => pow_nonneg (abs_nonneg _) _) (fun v => pow_le_pow_left₀ (abs_nonneg _)
        ((abs_sub _ _).trans (by linarith [abs_lA_le hn D c a v, hlb a])) q)
    rw [abs_of_nonneg h0]; exact h1
  have bMs : ∀ a, |∫ v, |sgA D c a v - gbar D c a| ^ q ∂ν| ≤ (2 * lipSig D c) ^ q := fun a => by
    obtain ⟨h0, h1⟩ := bInt (M := (2 * lipSig D c) ^ q)
      (((measurable_sgA_left D c a).sub_const (gbar D c a)).abs.pow_const q)
      (fun v => pow_nonneg (abs_nonneg _) _) (fun v => pow_le_pow_left₀ (abs_nonneg _)
        ((abs_sub _ _).trans (by linarith [abs_sgA_le hn D c a v, hgb a])) q)
    rw [abs_of_nonneg h0]; exact h1
  have iMl : Integrable (fun a => ∫ v, |lA D c a v - lbar D c a| ^ q ∂ν) (muI n) := intB mMl bMl
  have iMs : Integrable (fun a => ∫ v, |sgA D c a v - gbar D c a| ^ q ∂ν) (muI n) := intB mMs bMs
  have imass : Integrable (fun a => ν.real {v | sgA D c a v < σl}) (muI n) :=
    intB mmass (M := 1) fun a => by
      rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have irem : Integrable (fun a => removed ν (goodP D c wl ws σl) a) (muI n) :=
    intB (measurable_removed ν (measurableSet_goodP D c wl ws σl)) (M := 1) fun a => by
      rw [abs_of_nonneg (removed_nonneg _ _ _)]; exact removed_le_one _ _ _
  have isum := ((iMl.div_const (wl ^ q)).add (iMs.div_const (ws ^ q))).add imass
  refine (integral_mono irem isum (fun a => removed_le hn D c hwl hws q a)).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (f := fun a => (∫ v, |lA D c a v - lbar D c a| ^ q ∂ν) / wl ^ q +
      (∫ v, |sgA D c a v - gbar D c a| ^ q ∂ν) / ws ^ q)
      ((iMl.div_const _).add (iMs.div_const _)) imass,
    integral_add (f := fun a => (∫ v, |lA D c a v - lbar D c a| ^ q ∂ν) / wl ^ q)
      (iMl.div_const _) (iMs.div_const _), integral_div, integral_div]
  unfold Bpap
  rw [div_pow, div_pow]
  gcongr

/-- **The displacement price** for the paper's split data: `E_K H²(Q_a, Q̄_a) ≤ 𝒟`. -/
lemma int_disp (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (h0 : 0 < η) (h1 : η < 1)
    (hσl : 0 < σl) {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) {B Vl VS : ℝ} (hB0 : 0 ≤ B)
    (hVl0 : 0 ≤ Vl) (hVS0 : 0 ≤ VS)
    (hB : ∫ a, removed (stdGauss (Fin (n - 1))) (goodP D c wl ws σl) a ∂muI n ≤ B)
    (hVl : ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vl ^ 2)
    (hVS : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2) :
    ∫ a in keptIx D c (dPaper D c wl ws σl η h0 h1), hellG2 n
      (((dPaper D c wl ws σl η h0 h1).lam0 a - (dPaper D c wl ws σl η h0 h1).lamb a) ^ 2 *
        normSq c.2.1.2) ((dPaper D c wl ws σl η h0 h1).S0 a) ((dPaper D c wl ws σl η h0 h1).Sb a)
        ∂muI n ≤ Dpap n B CA Vl VS η σl := by
  set ν := stdGauss (Fin (n - 1)) with hν
  set d := dPaper D c wl ws σl η h0 h1 with hd
  set K := keptIx D c d with hK
  have mK : MeasurableSet K := measurableSet_keptSet ν d.mgood (measurableSet_bulkIx D c) d.eta
  have hCA0 : 0 ≤ CA := (normSq_nonneg _).trans hCA
  have hη0 : 0 < 1 - η := by linarith
  have mS : ∀ a, Measurable (fun v => sgA D c a v) := fun a => measurable_sgA_left D c a
  have mLa : ∀ a, Measurable (fun v => lA D c a v) := fun a => measurable_lA_left D c a
  have bS : ∀ a v, |sgA D c a v| ≤ lipSig D c := abs_sgA_le hn D c
  have bLa : ∀ a v, |lA D c a v| ≤ lipLam D c := abs_lA_le hn D c
  set c1 := CA / (2 * (1 - η) * σl ^ 2) with hc1
  set c2 := (n : ℝ) / (8 * (1 - η) ^ 2 * σl ^ 4) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  set VL : Ix n → ℝ := fun a => ∫ v, (lA D c a v - lbar D c a) ^ 2 ∂ν with hVLd
  set VSf : Ix n → ℝ := fun a => ∫ v, (sA D c a v - ∫ w, sA D c a w ∂ν) ^ 2 ∂ν with hVSf
  set β : Ix n → ℝ := fun a => removed ν (goodP D c wl ws σl) a with hβ
  have mInt : ∀ {F : Ix n × (Fin (n - 1) → ℝ) → ℝ}, Measurable F →
      Measurable (fun a => ∫ v, F (a, v) ∂ν) := fun hF =>
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have mVL : Measurable VL :=
    mInt (((measurable_lA D c).sub ((measurable_lbar D c).comp measurable_fst)).pow_const 2)
  have mSbar : Measurable (fun a => ∫ w, sA D c a w ∂ν) := mInt (measurable_sA D c)
  have mVS : Measurable VSf :=
    mInt (((measurable_sA D c).sub (mSbar.comp measurable_fst)).pow_const 2)
  have mβ : Measurable β := measurable_removed ν (measurableSet_goodP D c wl ws σl)
  -- bounds
  have hlb : ∀ a, |lbar D c a| ≤ lipLam D c := fun a => by
    unfold lbar
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |lA D c a v| ∂ν ≤ ∫ _v, lipLam D c ∂ν :=
          integral_mono (intB (mLa a).abs (M := lipLam D c) fun v => by
            rw [abs_abs]; exact bLa a v) (integrable_const _) (bLa a)
      _ = lipLam D c := by simp
  have bsA : ∀ a v, |sA D c a v| ≤ lipSig D c ^ 2 := fun a v => by
    rw [sA_eq]; exact sq_bound_of_abs (bS a) v
  have hsb : ∀ a, |∫ w, sA D c a w ∂ν| ≤ lipSig D c ^ 2 := fun a => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |sA D c a v| ∂ν ≤ ∫ _v, lipSig D c ^ 2 ∂ν :=
          integral_mono (intB ((measurable_sA_left D c a).abs) (M := lipSig D c ^ 2) fun v => by
            rw [abs_abs]; exact bsA a v) (integrable_const _) (bsA a)
      _ = _ := by simp
  have bInt : ∀ {f : (Fin (n - 1) → ℝ) → ℝ} {M : ℝ}, Measurable f → (∀ v, 0 ≤ f v) →
      (∀ v, f v ≤ M) → 0 ≤ ∫ v, f v ∂ν ∧ ∫ v, f v ∂ν ≤ M := fun {f} {M} hf h0 hM => by
    refine ⟨integral_nonneg h0, ?_⟩
    calc ∫ v, f v ∂ν ≤ ∫ _v, M ∂ν :=
          integral_mono (intB hf (M := M) fun v => by rw [abs_of_nonneg (h0 v)]; exact hM v)
            (integrable_const _) hM
      _ = M := by simp
  set KL := (2 * lipLam D c) ^ 2
  set KS := (2 * lipSig D c ^ 2) ^ 2
  have bVL : ∀ a, 0 ≤ VL a ∧ VL a ≤ KL := fun a =>
    bInt (M := KL) (((mLa a).sub_const _).pow_const 2) (fun v => sq_nonneg _) (fun v => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [bLa a v, hlb a])) 2)
  have bVS : ∀ a, 0 ≤ VSf a ∧ VSf a ≤ KS := fun a =>
    bInt (M := KS) (((measurable_sA_left D c a).sub_const _).pow_const 2) (fun v => sq_nonneg _)
      (fun v => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
          (by linarith [bsA a v, hsb a])) 2)
  have bβ : ∀ a, 0 ≤ β a ∧ β a ≤ 1 := fun a => ⟨removed_nonneg _ _ _, removed_le_one _ _ _⟩
  -- per index
  have hpt : ∀ a ∈ K, hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2) (d.S0 a) (d.Sb a) ≤
      β a * (c1 * VL a + c2 * VSf a) := by
    intro a ha
    obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
    have h := idx_disp n (measurableSet_slice d a) hm (mLa a) (mS a) (bLa a) (bS a) hσl
      (fun v hv => (hGψ v hv).2) hm1 h1 (normSq_nonneg c.2.1.2)
    have e1 : d.lamb a = ∫ v, lA D c a v ∂ν := rfl
    have e2 : d.Sb a = ∫ v, sgA D c a v ^ 2 ∂ν := rfl
    rw [hl, e1, hS, e2]
    refine h.trans ?_
    have hr : 1 - ν.real (slice d a) = β a := by
      rw [slice_real, sub_sub_cancel]; rfl
    rw [hr]
    refine mul_le_mul_of_nonneg_left ?_ (bβ a).1
    have k1 : normSq c.2.1.2 * (∫ v, (lA D c a v - ∫ w, lA D c a w ∂ν) ^ 2 ∂ν) /
        (2 * (1 - η) * σl ^ 2) ≤ c1 * VL a := by
      rw [hc1, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCA (bVL a).1) (by positivity)
    have k2 : (n : ℝ) * (∫ v, (sgA D c a v ^ 2 - ∫ w, sgA D c a w ^ 2 ∂ν) ^ 2 ∂ν) /
        (8 * (1 - η) ^ 2 * σl ^ 4) = c2 * VSf a := by
      rw [hc2, div_mul_eq_mul_div]; rfl
    linarith
  -- integration
  have iH : IntegrableOn (fun a => hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2)
      (d.S0 a) (d.Sb a)) K (muI n) := by
    have mH : Measurable (fun a => hellG2 n ((d.lam0 a - d.lamb a) ^ 2 * normSq c.2.1.2)
        (d.S0 a) (d.Sb a)) :=
      (measurable_hellG2 n).comp ((((d.mlam0.sub d.mlamb).pow_const 2).mul_const _).prodMk
        (d.mS0.prodMk d.mSb))
    refine (intB mH (M := 2) fun a => ?_).integrableOn
    rw [abs_of_nonneg (hellG2_nonneg n (mul_nonneg (sq_nonneg _) (normSq_nonneg _)) _ _)]
    exact hellG2_le_two n _ _ _
  have iR : Integrable (fun a => β a * (c1 * VL a + c2 * VSf a)) (muI n) :=
    intB (mβ.mul ((mVL.const_mul _).add (mVS.const_mul _))) (M := 1 * (c1 * KL + c2 * KS))
      fun a => by
        rw [abs_mul, abs_of_nonneg (bβ a).1, abs_of_nonneg (by
          have := (bVL a).1; have := (bVS a).1; positivity)]
        exact mul_le_mul (bβ a).2 (by nlinarith [(bVL a).2, (bVS a).2]) (by
          have := (bVL a).1; have := (bVS a).1; positivity) zero_le_one
  have hR0 : ∀ a, 0 ≤ β a * (c1 * VL a + c2 * VSf a) := fun a => by
    have := (bβ a).1; have := (bVL a).1; have := (bVS a).1; positivity
  have hβ2 : ∫ a, β a ^ 2 ∂muI n ≤ (√B) ^ 2 := by
    rw [Real.sq_sqrt hB0]
    refine le_trans (integral_mono (intB (mβ.pow_const 2) (M := 1) fun a => by
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [(bβ a).1, (bβ a).2])
      (intB mβ (M := 1) fun a => by rw [abs_of_nonneg (bβ a).1]; exact (bβ a).2)
      fun a => by nlinarith [(bβ a).1, (bβ a).2]) hB
  have cs1 : ∫ a, β a * VL a ∂muI n ≤ √B * Vl :=
    cs_root (muI n) mβ mVL (M := 1 + KL) (fun a => (bβ a).1) (fun a => (bVL a).1)
      (fun a => by linarith [(bβ a).2, (bVL a).1, (bVL a).2, sq_nonneg (2 * lipLam D c)])
      (fun a => by linarith [(bVL a).2]) (Real.sqrt_nonneg _) hVl0 hβ2 hVl
  have cs2 : ∫ a, β a * VSf a ∂muI n ≤ √B * VS :=
    cs_root (muI n) mβ mVS (M := 1 + KS) (fun a => (bβ a).1) (fun a => (bVS a).1)
      (fun a => by linarith [(bβ a).2, (bVS a).1, (bVS a).2, sq_nonneg (2 * lipSig D c ^ 2)])
      (fun a => by linarith [(bVS a).2]) (Real.sqrt_nonneg _) hVS0 hβ2 hVS
  have iBL : Integrable (fun a => β a * VL a) (muI n) :=
    intB (mβ.mul mVL) (M := 1 * KL) fun a => by
      rw [abs_mul, abs_of_nonneg (bβ a).1, abs_of_nonneg (bVL a).1]
      exact mul_le_mul (bβ a).2 (bVL a).2 (bVL a).1 zero_le_one
  have iβS : Integrable (fun a => β a * VSf a) (muI n) :=
    intB (mβ.mul mVS) (M := 1 * KS) fun a => by
      rw [abs_mul, abs_of_nonneg (bβ a).1, abs_of_nonneg (bVS a).1]
      exact mul_le_mul (bβ a).2 (bVS a).2 (bVS a).1 zero_le_one
  calc _ ≤ ∫ a in K, β a * (c1 * VL a + c2 * VSf a) ∂muI n :=
        setIntegral_mono_on iH iR.integrableOn mK hpt
    _ ≤ ∫ a, β a * (c1 * VL a + c2 * VSf a) ∂muI n :=
        setIntegral_le_integral iR (Filter.Eventually.of_forall hR0)
    _ = c1 * ∫ a, β a * VL a ∂muI n + c2 * ∫ a, β a * VSf a ∂muI n := by
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iBL.const_mul _)
          (iβS.const_mul _)]
        congr 1; funext a; ring
    _ ≤ c1 * (√B * Vl) + c2 * (√B * VS) := by gcongr
    _ = Dpap n B CA Vl VS η σl := by unfold Dpap; rw [hc1, hc2]; ring

/-- **Proposition FL (the three fluctuation roots) for the paper's split data, from the latitude
moments only.** The hypotheses are the interface of Proposition `t7:p07:LG` and of the mass
bound `t7:p07:mass-low` (moments of `λ`, `σ`, `S = σ²` on the latitude spheres, and the mass of
`{σ < σ_l}`), the norm bound `|c_A|² ≤ C_A` (event `E_{c_A}`), and the numeric root sum. THEN
`FLUCT_chi_hyp D c (dPaper …) ε₀ (2w_l) σ_l² h_fl`, with `B = Bpap`, `Dd = Dpap`. -/
theorem fluct_paper_mom (hn : 1 ≤ n) (D : Design n) (c : Ret n) {wl ws σl η : ℝ} (hwl : 0 < wl)
    (hws : 0 < ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1) (hcA : 0 < normSq c.2.1.2)
    {CA : ℝ} (hCA : normSq c.2.1.2 ≤ CA) (hε : eps0 ws σl < 1)
    {Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βlow hfl : ℝ} (q : ℕ) (hVs0 : 0 ≤ Vs) (hVl0 : 0 ≤ Vl)
    (hVS0 : 0 ≤ VS) (hts8 : 0 < ts8) (hts12 : 0 < ts12) (htl8 : 0 < tl8) (htl12 : 0 < tl12)
    (htlq : 0 ≤ tlq) (htsq : 0 ≤ tsq) (hβl : 0 ≤ βlow)
    (hVs : ∫ a, (∫ v, (sgA D c a v - gbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vs ^ 2)
    (hVl : ∫ a, (∫ v, (lA D c a v - lbar D c a) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ Vl ^ 2)
    (hVS : ∫ a, (∫ v, (sA D c a v - ∫ w, sA D c a w ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
    (hs8 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts8 ^ 8)
    (hs12 : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ ts12 ^ 12)
    (hl8 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl8 ^ 8)
    (hl12 : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tl12 ^ 12)
    (hlq : ∫ a, ∫ v, |lA D c a v - lbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tlq ^ q)
    (hsq : ∫ a, ∫ v, |sgA D c a v - gbar D c a| ^ q ∂stdGauss (Fin (n - 1)) ∂muI n ≤ tsq ^ q)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < σl} ∂muI n ≤ βlow)
    (hsum : √(2 * (1 + η⁻¹) * Bpap wl ws tlq tsq βlow q) +
        √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
        (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
          (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
        (cVw ws σl * ((1 - η)⁻¹ * Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
        (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * ts8))
        (√CA / σl * ((iotaP η 8 + c2η η) * tl8))
        (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
        (√CA / σl * ((iotaP η 12 + c2η η) * tl12))) +
        √(Dpap n (Bpap wl ws tlq tsq βlow q) CA Vl VS η σl) ≤ hfl) :
    FLUCT_chi_hyp D c (dPaper D c wl ws σl η h0 h1) (eps0 ws σl) (2 * wl) (σl ^ 2) hfl := by
  have hB := int_removed hn D c hwl hws q hlq hsq hmass (σl := σl)
  have hB0 : 0 ≤ Bpap wl ws tlq tsq βlow q := by unfold Bpap; positivity
  have hD := int_disp hn D c h0 h1 hσl hCA hB0 hVl0 hVS0 hB hVl hVS (wl := wl) (ws := ws)
  exact fluct_paper hn D c hwl.le hws hσl h0 h1 hcA hCA hε hVs0 hVl0 hts8 hts12 htl8 htl12
    hVs hVl hs8 hs12 hl8 hl12 hB hD hsum

end paperBD

end BstLean.Part162

open BstLean.Part162 in
#print axioms fluct_paper_mom
