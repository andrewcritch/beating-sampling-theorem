import BstLean.Part150Disp

/-!
# Part 150, item 5: the sampling error for a program with ANOTHER centre

The text of `Part149Samp` (`sampB_lint`) for a generic measurable centre map `bh`.

* `preH bh W A γ = A₃·bh + tauOutOf n bh·γ`: one input of `F`.
* `gSampH bh k W A F γ = (1/k)·Σ_i F(preH bh W A γ_i)`: the output with `k` forward passes of `F`.
* **`sampH_lint`**: `E[1_X·(gSampH − gOutH)²] ≤ 4/n/k` on a measurable set `X` on which
  `|bh|² ≤ m_A/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141
open BstLean.Part149

section meas

variable {n : ℕ}

/-- One input of `F` for the centre `bh`. -/
noncomputable def preH (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (γ : Fin n → ℝ) : Fin n → ℝ :=
  A.2.2.mulVec (bh (W, thA A)) + tauOutOf n (bh (W, thA A)) • γ

/-- **The output with `k` forward passes of `F`**, for the centre `bh`. -/
noncomputable def gSampH (bh : CMap n) {mF : ℕ} (k : ℕ) (W : MlpParam (2 * n) (mW n) n)
    (A : MlpParam n (mA n) n) (F : MlpParam n mF 1) (γ : Fin k → Fin n → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ i, evF F (preH bh W A (γ i))

lemma measurable_bhWA {bh : CMap n} (hbh : Measurable bh) :
    Measurable (fun q : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n => bh (q.1, thA q.2)) :=
  hbh.comp (measurable_fst.prodMk (measurable_thA.comp measurable_snd))

lemma measurable_preH {bh : CMap n} (hbh : Measurable bh) :
    Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) × (Fin n → ℝ) =>
      preH bh q.1.1 q.1.2 q.2) := by
  unfold preH
  have hb : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
      (Fin n → ℝ) => bh (q.1.1, thA q.1.2)) := by
    have hf : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
        (Fin n → ℝ) => q.1) := measurable_fst
    have h := (measurable_bhWA hbh).comp hf
    simp only [Function.comp_def] at h
    exact h
  have hA : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n) ×
      (Fin n → ℝ) => q.1.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hmv := (BstLean.Part134.measurable_mulVec_joint (n := n) (m := mA n)).comp (hA.prodMk hb)
  simp only [Function.comp_def] at hmv
  have hτ := (measurable_tauOutOf (n := n) (m := mA n)).comp hb
  simp only [Function.comp_def] at hτ
  exact hmv.add (hτ.smul measurable_snd)

lemma measurable_preH_WA (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) :
    Measurable (preH bh W A) := by
  unfold preH
  exact measurable_const.add (measurable_const_smul _)

lemma measurable_gSampH {bh : CMap n} (hbh : Measurable bh) (k : ℕ) :
    Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) => gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold gSampH
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have h0 : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ((p.1.1, p.1.2.1), p.2 i)) :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  have h1 := (measurable_preH hbh).comp h0
  simp only [Function.comp_def] at h1
  exact measurable_evF_comp (measurable_snd.comp (measurable_snd.comp measurable_fst)) h1


end meas

section joint

variable {n : ℕ}

/-- The function `γ ↦ F(preH bh W A γ)` is square-integrable. -/
lemma memLp_evF_preH (bh : CMap n) {mF : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n mF 1) :
    MemLp (fun γ : Fin n → ℝ => evF F (preH bh W A γ)) 2 (stdGauss (Fin n)) := by
  have hmeas : Measurable (fun γ : Fin n → ℝ => evF F (preH bh W A γ)) :=
    (measurable_evF F).comp (measurable_preH_WA bh W A)
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  obtain ⟨C, hC0, hC⟩ := evF_growth F
  have hg := (gauss_shift_normSq (A.2.2.mulVec (bh (W, thA A))) (tauOutOf n (bh (W, thA A)))).1
  have iG : Integrable (fun γ : Fin n → ℝ => C * (1 + normSq (preH bh W A γ))) (stdGauss (Fin n)) :=
    ((integrable_const (1 : ℝ)).add hg).const_mul C
  refine Integrable.mono' iG (hmeas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun γ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hC _

/-- The second moment of one point of the sample, on the set `X`. -/
noncomputable def LsH (bh : CMap n) (X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ≥0∞ :=
  ({t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      (t.1, thA t.2.1) ∈ X}).indicator
    (fun t => ∫⁻ γ, ENNReal.ofReal (evF t.2.2 (preH bh t.1 t.2.1 γ) ^ 2) ∂stdGauss (Fin n)) t

lemma measurable_LsH {bh : CMap n} (hbh : Measurable bh)
    {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hX : MeasurableSet X) : Measurable (LsH bh X) := by
  unfold LsH
  have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin n → ℝ) =>
      ENNReal.ofReal (evF q.1.2.2 (preH bh q.1.1 q.1.2.1 q.2) ^ 2)) := by
    have h0 : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) => ((q.1.1, q.1.2.1), q.2)) :=
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
    have h1 := (measurable_preH hbh).comp h0
    simp only [Function.comp_def] at h1
    exact ENNReal.measurable_ofReal.comp ((measurable_evF_comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)) h1).pow_const 2)
  refine hj.lintegral_prod_right'.indicator ?_
  exact (measurable_fst.prodMk (measurable_thA.comp (measurable_fst.comp measurable_snd))) hX

/-- `E[LsB] ≤ 4/n`. -/
lemma lint_LsH (hn : 1 ≤ n) {bh : CMap n} (hbh : Measurable bh) {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hX : MeasurableSet X)
    (hb : ∀ x ∈ X, normSq (bh x) ≤ (mA n : ℝ) / n) :
    ∫⁻ t, LsH bh X t ∂mlpTriple 2 n ≤ ENNReal.ofReal (4 / (n : ℝ)) := by
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by
    unfold mF
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnR _)).ne'
  have mL := measurable_LsH hbh hX
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  rw [e0, lintegral_prod _ mL.aemeasurable]
  have inner : ∀ W : MlpParam (2 * n) (mW n) n,
      ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, LsH bh X (W, p)
          ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤ ENNReal.ofReal (4 / (n : ℝ)) := by
    intro W
    have mgW : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 => LsH bh X (W, p)) :=
      mL.comp measurable_prodMk_left
    have h4 := lint_assoc4 (gaussMat (mA n) n (2 / (n : ℝ)))
      (gaussMat (mA n) (mA n) (2 / (mA n : ℝ))) (gaussMat n (mA n) (2 / (mA n : ℝ)))
      (mlpGauss n (mF n) 1) mgW
    have e1 : (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) =
        ((gaussMat (mA n) n (2 / (n : ℝ))).prod ((gaussMat (mA n) (mA n) (2 / (mA n : ℝ))).prod
          (gaussMat n (mA n) (2 / (mA n : ℝ))))).prod (mlpGauss n (mF n) 1) := rfl
    rw [e1, h4]
    have each : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
        ∫⁻ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
          LsH bh X (W, (θ.1, θ.2, y.1), y.2)
          ∂((gaussMat n (mA n) (2 / (mA n : ℝ))).prod (mlpGauss n (mF n) 1)) ≤
        ENNReal.ofReal (4 / (n : ℝ)) := by
      intro θ
      by_cases hx : ((W, θ) : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ∈ X
      · have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
            LsH bh X (W, (θ.1, θ.2, y.1), y.2) =
              ∫⁻ γ, ENNReal.ofReal (evF y.2 (y.1.mulVec (bh (W, θ)) +
                tauOutOf n (bh (W, θ)) • γ) ^ 2) ∂stdGauss (Fin n) := by
          intro y
          unfold LsH
          rw [Set.indicator_of_mem (show ((W, (θ.1, θ.2, y.1), y.2) : MlpParam (2 * n) (mW n) n ×
            MlpParam n (mA n) n × MlpParam n (mF n) 1) ∈ {t : MlpParam (2 * n) (mW n) n ×
              MlpParam n (mA n) n × MlpParam n (mF n) 1 | (t.1, thA t.2.1) ∈ X} from hx)]
          rfl
        simp_rw [e]
        have hbx : normSq (bh (W, θ)) ≤ (mA n : ℝ) / n := hb (W, θ) hx
        have h := sampB_second (n := n) (m := mA n) (mF := mF n) hn hmA hmF
          (b := bh (W, θ)) hbx
        exact le_of_eq h
      · have e : ∀ y : Matrix (Fin n) (Fin (mA n)) ℝ × MlpParam n (mF n) 1,
            LsH bh X (W, (θ.1, θ.2, y.1), y.2) = 0 := by
          intro y
          unfold LsH
          rw [Set.indicator_of_notMem (show ((W, (θ.1, θ.2, y.1), y.2) :
            MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ∉
              {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
                (t.1, thA t.2.1) ∈ X} from hx)]
        simp_rw [e]
        simp
    refine (lintegral_mono each).trans ?_
    simp
  refine (lintegral_mono inner).trans ?_
  simp

/-- **The sampling error of the program with the mean-field centre.** For `n ≥ 1`, `k ≥ 1` and a
measurable set `X` of `(W, (A₁, A₂))` on which `|bMF|² ≤ m_A/n`:
`E[1_X·(gSampB − gOutB)²] ≤ 4/n/k`, the mean over `(W, A, F)` and the `k` Gaussian vectors. -/
theorem sampH_lint {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) {bh : CMap n}
    (hbh : Measurable bh)
    {X : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (hX : MeasurableSet X)
    (hb : ∀ x ∈ X, normSq (bh x) ≤ (mA n : ℝ) / n) :
    ∫⁻ p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ),
      ENNReal.ofReal (({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
        (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2) p)
      ∂((mlpTriple 2 n).prod (gamK k n)) ≤ ENNReal.ofReal (4 / (n : ℝ) / k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have mT : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X} :=
    ((measurable_fst.comp measurable_fst).prodMk (measurable_thA.comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))) hX
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) =>
      ENNReal.ofReal (({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
        (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2) p)) :=
    ENNReal.measurable_ofReal.comp ((((measurable_gSampH hbh k).sub
      ((measurable_gOutH hbh).comp measurable_fst)).pow_const 2).indicator mT)
  rw [lintegral_prod _ mf.aemeasurable]
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
        (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2) (t, γ))
        ∂gamK k n ≤ ENNReal.ofReal ((k : ℝ)⁻¹) * LsH bh X t := by
    rintro ⟨W, A, F⟩
    by_cases hx : ((W, thA A) : MlpParam (2 * n) (mW n) n × HidParam n (mA n)) ∈ X
    · have e1 : ∀ γ : Fin k → Fin n → ℝ,
          ({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
          (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2)
          ((W, A, F), γ) = ((k : ℝ)⁻¹ * ∑ i, evF F (preH bh W A (γ i)) -
            ∫ γ, evF F (preH bh W A γ) ∂stdGauss (Fin n)) ^ 2 := by
        intro γ
        rw [Set.indicator_of_mem (show (((W, A, F), γ) : (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) ∈
            {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
              MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X} from hx)]
        rfl
      simp_rw [e1]
      have e2 : LsH bh X (W, A, F) =
          ∫⁻ γ, ENNReal.ofReal (evF F (preH bh W A γ) ^ 2) ∂stdGauss (Fin n) := by
        unfold LsH
        rw [Set.indicator_of_mem (show ((W, A, F) : MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) ∈ {t : MlpParam (2 * n) (mW n) n ×
            MlpParam n (mA n) n × MlpParam n (mF n) 1 | (t.1, thA t.2.1) ∈ X} from hx)]
      rw [e2]
      exact iid_mean_sq_L2 (stdGauss (Fin n))
        ((measurable_evF F).comp (measurable_preH_WA bh W A)) (memLp_evF_preH bh W A F) hk
    · have e1 : ∀ γ : Fin k → Fin n → ℝ,
          ({p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X}).indicator
          (fun p => (gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 - gOutH bh p.1.1 p.1.2.1 p.1.2.2) ^ 2)
          ((W, A, F), γ) = 0 := by
        intro γ
        rw [Set.indicator_of_notMem (show (((W, A, F), γ) : (MlpParam (2 * n) (mW n) n ×
          MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) ∉
            {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
              MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | (p.1.1, thA p.1.2.1) ∈ X} from hx)]
      simp_rw [e1]
      simp
  refine (lintegral_mono key).trans ?_
  rw [lintegral_const_mul _ (measurable_LsH hbh hX)]
  refine (mul_le_mul' le_rfl (lint_LsH hn hbh hX hb)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end joint

end BstLean.Part150

open BstLean.Part150 in
#print axioms sampH_lint
