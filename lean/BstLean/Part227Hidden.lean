import BstLean.Part143HidC2
import BstLean.Part204All

/-! Part 227: variable hidden thresholds with the exact World width. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140 BstLean.Part143 BstLean.Part157 BstLean.Part159

/-- The strict hidden kernel event has a variable Markov payment. -/
theorem goodHid_charge {n : ℕ} (hn : 4096 ≤ n) {sp p₂ : ℝ}
    (hsp : 0 < sp) (hp₂ : 0 < p₂) :
    (hidGauss (2 * n) (mW n)).real (goodHid (2 * n) (mW n) (sp ^ 2) p₂)ᶜ ≤
      372 / 1000 * sp ^ 2 + 448 / 1000 * p₂ := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hN8 : 8192 ≤ 2 * n := by omega
  have hm' : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hN' : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast hN
  have hc := BstLean.Part133.cF2o_pos hm
  have hcF : cF2o (mW n) ^ 2 =
      (6 * (1 + 5 / (mW n : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (mW n : ℝ) := by
    unfold cF2o
    rw [Real.sq_sqrt (by positivity)]
    ring
  let B : ℝ := ((mW n : ℝ) / ((2 * n : ℕ) : ℝ) * cF2o (mW n)) ^ 2
  have hB0 : 0 < B := by dsimp [B]; positivity
  have h2 : 0 ≤ ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) := by positivity
  obtain ⟨iK, eK⟩ := errK_mean143 (m := mW n) hN hm
  obtain ⟨iD, eD⟩ := errD_mean143 (m := mW n) hN hm
  have eK' : ∫ θ, errK θ ∂hidGauss (2 * n) (mW n) ≤ 372 / 1000 * B := by
    refine eK.trans ?_
    dsimp [B]
    rw [mul_pow, hcF]
    have h := mul_le_mul_of_nonneg_left (cK143_le hN8 hmM) h2
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_)) <;> ring
  have eD' : ∫ θ, errD θ ∂hidGauss (2 * n) (mW n) ≤ 448 / 1000 * B := by
    refine eD.trans ?_
    dsimp [B]
    rw [mul_pow, hcF]
    have h := mul_le_mul_of_nonneg_left (cD143_le hmM) h2
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_)) <;> ring
  have m1 := markov_ge (hidGauss (2 * n) (mW n)) errK_nonneg iK
    (B := 372 / 1000 * B) (p := 372 / 1000 * sp ^ 2) (by positivity) (by positivity) eK'
  have m2 := markov_ge (hidGauss (2 * n) (mW n)) errD_nonneg iD
    (B := 448 / 1000 * B) (p := 448 / 1000 * p₂) (by positivity) (by positivity) eD'
  rw [mul_div_mul_left _ _ (by norm_num : (372 / 1000 : ℝ) ≠ 0)] at m1
  rw [mul_div_mul_left _ _ (by norm_num : (448 / 1000 : ℝ) ≠ 0)] at m2
  have hsub : (goodHid (2 * n) (mW n) (sp ^ 2) p₂)ᶜ ⊆
      {θ | B / sp ^ 2 ≤ errK θ} ∪ {θ | B / p₂ ≤ errD θ} := by
    intro θ hθ
    simpa only [goodHid, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_lt,
      Set.mem_union, B] using hθ
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add m1 m2))

/-- One squared-deviation payment bounds both tails. -/
theorem abs_charge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {a e : ℝ}
    (hf : L2le μ f a) (he : 0 < e) :
    μ.real {x | |f x| ≤ e}ᶜ ≤ a ^ 2 / e ^ 2 := by
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun x => f x ^ 2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hf.int_sq
    (e ^ 2)
  have hsub : {x | |f x| ≤ e}ᶜ ⊆ {x | e ^ 2 ≤ f x ^ 2} := by
    intro x hx
    change ¬ |f x| ≤ e at hx
    have hx' : e ≤ |f x| := (not_le.mp hx).le
    change e ^ 2 ≤ f x ^ 2
    rw [← sq_abs (f x)]
    exact pow_le_pow_left₀ he.le hx' 2
  have hμ := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  rw [le_div_iff₀ (sq_pos_of_pos he)]
  nlinarith [hf.le, mul_le_mul_of_nonneg_left hμ (sq_nonneg e)]

/-- The additional norm event keeps the source centre in its deviation. -/
def goodB (n : ℕ) (e : ℝ) : Set (WHid n) :=
  {θ | |Bh (2 * n) (mW n) θ - 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)| ≤
    2 / ((2 * n : ℕ) : ℝ) * e}

lemma goodB_meas {n : ℕ} (hn : 1 ≤ n) (e : ℝ) : MeasurableSet (goodB n e) :=
  measurableSet_le ((measurable_Bh (by omega)).sub_const _).abs measurable_const

theorem goodB_charge {n : ℕ} (hn : 4096 ≤ n) {e : ℝ} (he : 0 < e) :
    (hidGauss (2 * n) (mW n)).real (goodB n e)ᶜ ≤
      (1716 / 1000) ^ 2 / ((mW n : ℝ) * e ^ 2) := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  have h := abs_charge (bhatNorm_L2_143 hN hm) (mul_pos hγ he)
  change (hidGauss (2 * n) (mW n)).real (goodB n e)ᶜ ≤ _ at h
  refine h.trans ?_
  have heq : (2 / ((2 * n : ℕ) : ℝ) * cB143 (2 * n) (mW n)) ^ 2 /
      (2 / ((2 * n : ℕ) : ℝ) * e) ^ 2 = cB143 (2 * n) (mW n) ^ 2 / e ^ 2 := by
    field_simp
  rw [heq]
  have hc := div_le_div_of_nonneg_right (cB143_sq_le (N := 2 * n) (by omega) hmM)
    (sq_nonneg e)
  refine hc.trans ?_
  have hnum : (2944 / 1000 : ℝ) ≤ (1716 / 1000) ^ 2 := by norm_num
  exact (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hnum (by positivity)) (sq_nonneg e)).trans_eq (by ring)

/-- All six hidden events use the same Gaussian distribution and width. -/
def hidden (n : ℕ) (sp p₂ Xc dT eB : ℝ) : Set (WHid n) :=
  ((((goodHid (2 * n) (mW n) (sp ^ 2) p₂ ∩ goodDist n Xc) ∩ goodT n dT) ∩
    goodS n) ∩ goodAo n) ∩ goodB n eB

lemma hidden_meas {n : ℕ} (hn : 1 ≤ n) (sp p₂ Xc dT eB : ℝ) :
    MeasurableSet (hidden n sp p₂ Xc dT eB) :=
  (((((goodHid_meas (by omega) _ _).inter (goodDist_meas hn Xc)).inter
    (goodT_meas hn dT)).inter measurableSet_goodS).inter measurableSet_goodAo).inter
      (goodB_meas hn eB)

noncomputable def hiddenCharge (n : ℕ) (sp p₂ Xc dT eB : ℝ) : ℝ :=
  372 / 1000 * sp ^ 2 + 448 / 1000 * p₂ +
    31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (Xc - 8 / 25) ^ 2 +
    4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * dT) +
    10 ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) + 9 / 10 ^ 8 +
    (1716 / 1000) ^ 2 / ((mW n : ℝ) * eB ^ 2)

theorem hidden_charge {n : ℕ} (hn : 4096 ≤ n) {sp p₂ Xc dT eB : ℝ}
    (hsp : 0 < sp) (hp₂ : 0 < p₂) (hXc : 8 / 25 < Xc)
    (hdT : 0 < dT) (heB : 0 < eB) :
    (hidGauss (2 * n) (mW n)).real (hidden n sp p₂ Xc dT eB)ᶜ ≤
      hiddenCharge n sp p₂ Xc dT eB := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hsub : (hidden n sp p₂ Xc dT eB)ᶜ ⊆
      (((((goodHid (2 * n) (mW n) (sp ^ 2) p₂)ᶜ ∪ (goodDist n Xc)ᶜ) ∪
        (goodT n dT)ᶜ) ∪ (goodS n)ᶜ) ∪ (goodAo n)ᶜ) ∪ (goodB n eB)ᶜ := by
    intro θ hθ
    simpa only [hidden, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or,
      Set.mem_union] using hθ
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have hu := measureReal_union_le (μ := hidGauss (2 * n) (mW n))
  exact (hu _ _).trans (add_le_add
    ((hu _ _).trans (add_le_add
      ((hu _ _).trans (add_le_add
        ((hu _ _).trans (add_le_add
          ((hu _ _).trans (add_le_add (goodHid_charge hn hsp hp₂)
            (goodDist_prob143s hn hXc))) (goodT_prob143 hn hdT)))
              (goodS_charge (by omega) hm))) (goodAo_charge hn))) (goodB_charge hn heB))

/-- Tightening the source thresholds gives inclusion, with no transfer of its payment. -/
theorem hidden_subset_GPap {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hXc : Xc ≤ 3 / 4) (hdT : dT ≤ 1 / 400000) :
    hidden n sp p₂ Xc dT eB ⊆ GPap n := by
  intro θ hθ
  have hK := hθ.1.1.1.1.1.1
  have hD := hθ.1.1.1.1.1.2
  have hT := hθ.1.1.1.2
  have hB : 0 ≤ ((mW n : ℝ) / ((2 * n : ℕ) : ℝ) * cF2o (mW n)) ^ 2 := sq_nonneg _
  have hs : (4 / 100 : ℝ) ^ 2 ≤ sp ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hsp 2
  have hk : θ ∈ good136 n := by
    constructor
    · exact lt_of_lt_of_le hK
        (div_le_div_of_nonneg_left hB (by norm_num) hs)
    · exact lt_of_lt_of_le hD
        (div_le_div_of_nonneg_left hB (by norm_num) hp₂)
  have hx : θ ∈ goodDist n (3 / 4) := by
    exact hθ.1.1.1.1.2.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hXc (by positivity)) (by positivity))
  have ht : θ ∈ goodT n (1 / 400000) :=
    hT.trans (mul_le_mul_of_nonneg_left hdT (sq_nonneg _))
  exact ⟨⟨⟨⟨hk, hx⟩, ht⟩, hθ.1.1.2⟩, hθ.1.2⟩

theorem retained_hidden_charge {n : ℕ} (hn : 4096 ≤ n) (D : Centres n)
    {sp p₂ Xc dT eB : ℝ} (hsp : 0 < sp) (hp₂ : 0 < p₂)
    (hXc : 8 / 25 < Xc) (hdT : 0 < dT) (heB : 0 < eB) :
    (retDist D).real (Hof (hidden n sp p₂ Xc dT eB))ᶜ ≤
      hiddenCharge n sp p₂ Xc dT eB := by
  rw [hid_charge D (hidden_meas (by omega) _ _ _ _ _)]
  exact hidden_charge hn hsp hp₂ hXc hdT heB

end BstLean.Part227
#print axioms BstLean.Part227.goodHid_charge
#print axioms BstLean.Part227.abs_charge
#print axioms BstLean.Part227.goodB_charge
#print axioms BstLean.Part227.hidden_charge
#print axioms BstLean.Part227.hidden_subset_GPap
#print axioms BstLean.Part227.retained_hidden_charge
