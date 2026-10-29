import BstLean.Part182Mask2

/-!
# Part 185 (file `D3`): the lower tail of the second-layer overlap count of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

* `d3_overlap_lo`: Hoeffding lower tail: `Pr(#{i : (Gu)_i > 0, (Gu')_i > 0} < M(κ̇(q)/2 − η))
  ≤ exp(−2η²M)` (applied to `1 − mk_ov`); `d3_overlap_lo_ge` with a lower bound `q ≥ q₋`.
* `d3_tail_d_upper`: `Pr(|ReLU(A₁x) − ReLU(A₁x')| ≥ √(2n(1 − κ(c))) + 2υ√γ) ≤ e^{−τ}`.
* `d3_cos_ge`: `a·b/(|a||b|) ≥ (2a₋² − d₊²)/(2a₊²)` from `a₋ ≤ |a|, |b| ≤ a₊`, `|a − b| ≤ d₊`,
  `d₊² ≤ 2a₋²`.
* `d3_overlap_tail_lo`: the first-layer event `a, a' ≠ 0`, `cos(a, a') ≥ c₁⁻` fails with
  probability `≤ 5e^{−τ}`, `c₁⁻ = (2a₋² − d₊²)/(2a₊²)`.
* **`d3_mask_second_tail_lo`**: `Pr(tr(D₂D₂') < m(κ̇(c₁⁻)/2 − η)) ≤ 5e^{−τ} + e^{−2η²m}`.
-/

namespace BstLean.Part185

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask mask_nonneg)
open BstLean.Part153 (nrm nuA nrm_nonneg nrm_sq)
open BstLean.Part182

/-- **Hoeffding lower tail of the overlap count.** -/
theorem d3_overlap_lo {M k : ℕ} {v : ℝ} (hv : 0 < v) {u u' : Fin k → ℝ} (hu : u ≠ 0)
    (hu' : u' ≠ 0) {η : ℝ} (hη : 0 ≤ η) :
    (gaussMat M k v).real {G | ∑ i, mask ((G *ᵥ u) i) * mask ((G *ᵥ u') i) <
      (M : ℝ) * (kdot ((∑ j, u j * u' j) / (√(normSq u) * √(normSq u'))) / 2 - η)} ≤
      exp (-2 * η ^ 2 * M) := by
  have hP : IsProbabilityMeasure (stdGauss (Fin k)) := by unfold stdGauss; infer_instance
  set f : (Fin k → ℝ) → ℝ := fun w => 1 - mk_ov u u' w with hf
  have hfm : Measurable f := measurable_const.sub (mk_measurable_ov u u')
  have h := mk_rows_hoeff (M := M) v hfm (fun x => by simp only [hf]; linarith [mk_ov_le_one u u' x])
    (fun x => by simp only [hf]; linarith [mk_ov_nonneg u u' x]) hη
  have hint : Integrable (fun ξ => mk_ov u u' (Real.sqrt v • ξ)) (stdGauss (Fin k)) := by
    refine Integrable.of_bound ((mk_measurable_ov u u').comp (measurable_const_smul _)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mk_ov_nonneg _ _ _)]
    exact mk_ov_le_one _ _ _
  have hmean : ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) =
      1 - kdot ((∑ j, u j * u' j) / (√(normSq u) * √(normSq u'))) / 2 := by
    simp only [hf]
    rw [integral_sub (integrable_const _) hint, integral_const, mk_ov_mean hv hu hu']
    simp
  rw [hmean] at h
  refine le_trans (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)) h
  simp only [Set.mem_ofPred_eq] at hG ⊢
  have e : ∑ i, f (rowOf i G) = (M : ℝ) - ∑ i, mask ((G *ᵥ u) i) * mask ((G *ᵥ u') i) := by
    simp only [hf, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    congr 1
  rw [e]
  linarith

/-- The same with a lower bound `q₋ ≤ q` of the cosine (`κ̇` is monotone). -/
theorem d3_overlap_lo_ge {M k : ℕ} {v : ℝ} (hv : 0 < v) {u u' : Fin k → ℝ} (hu : u ≠ 0)
    (hu' : u' ≠ 0) {ql η : ℝ} (hq : ql ≤ (∑ j, u j * u' j) / (√(normSq u) * √(normSq u')))
    (hql : -1 ≤ ql) (hη : 0 ≤ η) :
    (gaussMat M k v).real {G | ∑ i, mask ((G *ᵥ u) i) * mask ((G *ᵥ u') i) <
      (M : ℝ) * (kdot ql / 2 - η)} ≤ exp (-2 * η ^ 2 * M) := by
  obtain ⟨hlo, hhi⟩ := mk_cos_mem hu hu'
  have hk : kdot ql ≤ kdot ((∑ j, u j * u' j) / (√(normSq u) * √(normSq u'))) :=
    kdot_monotoneOn ⟨hql, by linarith⟩ ⟨hlo, hhi⟩ hq
  refine le_trans (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)) (d3_overlap_lo hv hu hu' hη)
  simp only [Set.mem_ofPred_eq] at hG ⊢
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  nlinarith

variable {n : ℕ}

/-- **Upper tail of `|a − a'|`**: `Pr(|ReLU(A₁x) − ReLU(A₁x')| ≥ √(2n(1 − κ(c))) + 2υ√γ) ≤ e^{−τ}`. -/
theorem d3_tail_d_upper (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {M | √(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ))) ≤ nmD x x' M} ≤
        Real.exp (-τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  obtain ⟨hi, hS⟩ := nmD_mom (m := mA n) hv hx hx'
  have e : ((mA n : ℕ) : ℝ) * (2 / (n : ℝ) * (1 - kappa (x ⬝ᵥ x'))) =
      2 * n * (1 - kappa (x ⬝ᵥ x')) := by
    unfold mA; push_cast; field_simp
  rw [e] at hS
  have h := nm_upper (L := 2) zero_le_two (nmD_lip hx hx') hv.le (fun M => nrm_nonneg _) hi hS
    (t := 2 * (√(2 * τ) * √(2 / (n : ℝ)))) (by positivity)
  rw [nm_exp_eq hn two_pos hτ] at h
  exact h

/-- **The deterministic lower overlap bound.** -/
theorem d3_cos_ge {m : ℕ} {a b : Fin m → ℝ} {am ap dp : ℝ} (ham : 0 < am)
    (h1 : am ≤ nrm a) (h2 : nrm a ≤ ap) (h3 : am ≤ nrm b) (h4 : nrm b ≤ ap)
    (h5 : nrm (a - b) ≤ dp) (h6 : dp ^ 2 ≤ 2 * am ^ 2) :
    (2 * am ^ 2 - dp ^ 2) / (2 * ap ^ 2) ≤ (a ⬝ᵥ b) / (nrm a * nrm b) := by
  have ha0 : 0 < nrm a := lt_of_lt_of_le ham h1
  have hb0 : 0 < nrm b := lt_of_lt_of_le ham h3
  have hab : 0 < nrm a * nrm b := mul_pos ha0 hb0
  have hap : 0 < ap := lt_of_lt_of_le ha0 h2
  have hS := nm_normSq_sub a b
  rw [← nrm_sq, ← nrm_sq, ← nrm_sq] at hS
  have hd0 : 0 ≤ nrm (a - b) := BstLean.Part153.nrm_nonneg _
  have hd2 : nrm (a - b) ^ 2 ≤ dp ^ 2 := pow_le_pow_left₀ hd0 h5 2
  have ha2 : am ^ 2 ≤ nrm a ^ 2 := pow_le_pow_left₀ ham.le h1 2
  have hb2 : am ^ 2 ≤ nrm b ^ 2 := pow_le_pow_left₀ ham.le h3 2
  have hdot : (2 * am ^ 2 - dp ^ 2) / 2 ≤ a ⬝ᵥ b := by linarith
  have hN : 0 ≤ (2 * am ^ 2 - dp ^ 2) / 2 := by linarith
  have hup : nrm a * nrm b ≤ ap ^ 2 := by
    rw [sq]; exact mul_le_mul h2 h4 hb0.le hap.le
  rw [div_le_div_iff₀ (by positivity) hab]
  have : (2 * am ^ 2 - dp ^ 2) * (nrm a * nrm b) ≤ (2 * am ^ 2 - dp ^ 2) * ap ^ 2 :=
    mul_le_mul_of_nonneg_left hup (by linarith)
  nlinarith

/-- **The lower overlap event of Lemma TI** (five tails). -/
theorem d3_overlap_tail_lo (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (ham : 0 < √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ)))
    (h6 : (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      {M | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
        (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
            (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
          (2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2) ≤
        (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M))} ≤
      5 * Real.exp (-τ) := by
  set ap := √(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ)) with hap
  set am := √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ)) with ham'
  set dp := √(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ))) with hdp'
  set μ := gaussMat (mA n) n (2 / (n : ℝ))
  set U1 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ap ≤ nmA x M}
  set U2 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ap ≤ nmA x' M}
  set L1 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmA x M ≤ am}
  set L2 := {M : Matrix (Fin (mA n)) (Fin n) ℝ | nmA x' M ≤ am}
  set Dd := {M : Matrix (Fin (mA n)) (Fin n) ℝ | dp ≤ nmD x x' M}
  have hsub : {M | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
      (2 * am ^ 2 - dp ^ 2) / (2 * ap ^ 2) ≤
        (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M))} ⊆ U1 ∪ U2 ∪ L1 ∪ L2 ∪ Dd := by
    intro M hM
    by_contra hc
    simp only [Set.mem_union, not_or, U1, U2, L1, L2, Dd, Set.mem_ofPred_eq, not_le] at hc
    obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
    apply hM
    refine ⟨ham.trans c3, ham.trans c4, ?_⟩
    have e : nmD x x' M = nrm (reluV (M *ᵥ x) - reluV (M *ᵥ x')) := rfl
    rw [e] at c5
    exact d3_cos_ge ham c3.le c1.le c4.le c2.le c5.le h6
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have u1 := nm_tail_a_upper hn hx hτ
  have u2 := nm_tail_a_upper hn hx' hτ
  have l1 := nm_tail_a_lower hn hx hτ
  have l2 := nm_tail_a_lower hn hx' hτ
  have d1 := d3_tail_d_upper hn hx hx' hτ
  calc μ.real (U1 ∪ U2 ∪ L1 ∪ L2 ∪ Dd)
      ≤ μ.real (U1 ∪ U2 ∪ L1 ∪ L2) + μ.real Dd := measureReal_union_le _ _
    _ ≤ μ.real (U1 ∪ U2 ∪ L1) + μ.real L2 + μ.real Dd := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ μ.real (U1 ∪ U2) + μ.real L1 + μ.real L2 + μ.real Dd := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ μ.real U1 + μ.real U2 + μ.real L1 + μ.real L2 + μ.real Dd := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ 5 * Real.exp (-τ) := by linarith

/-- **The second-layer overlap lower tail under `nuA`**, on the event `cos(a, a') ≥ q₋`. -/
theorem d3_mask_second_joint_lo (x x' : Fin n → ℝ) {ql η : ℝ} (hql : -1 ≤ ql) (hη : 0 ≤ η) :
    (nuA n).real {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧ ql ≤ cosA x x' θ.1 ∧
      cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot ql / 2 - η)} ≤
      exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧ ql ≤ cosA x x' θ.1 ∧
      cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot ql / 2 - η)} with hS
  have hSm : MeasurableSet S := by
    have h1 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => nmA x θ.1) := (measurable_nmA x).comp measurable_fst
    have h2 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => nmA x' θ.1) := (measurable_nmA x').comp measurable_fst
    have h3 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => cosA x x' θ.1) :=
      (measurable_cosA x x').comp measurable_fst
    exact (measurableSet_lt measurable_const h1).inter ((measurableSet_lt measurable_const h2).inter
      ((measurableSet_le measurable_const h3).inter
        (measurableSet_lt (measurable_cnt2 x x') measurable_const)))
  have hB : 0 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := (exp_pos _).le
  rw [Measure.real]
  unfold nuA
  rw [Measure.prod_apply hSm]
  have hle : ∫⁻ A, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A ⁻¹' S)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ∫⁻ _A, ENNReal.ofReal (exp (-2 * η ^ 2 * (mA n : ℕ))) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
    refine lintegral_mono fun A => ?_
    by_cases hA : 0 < nmA x A ∧ 0 < nmA x' A ∧ ql ≤ cosA x x' A
    · obtain ⟨h1, h2, h3⟩ := hA
      have ha : reluV (A *ᵥ x) ≠ 0 := by
        intro h0; rw [nmA, h0] at h1; simp [nrm, normSq] at h1
      have ha' : reluV (A *ᵥ x') ≠ 0 := by
        intro h0; rw [nmA, h0] at h2; simp [nrm, normSq] at h2
      have hq : ql ≤ (∑ j, reluV (A *ᵥ x) j * reluV (A *ᵥ x') j) /
          (√(normSq (reluV (A *ᵥ x))) * √(normSq (reluV (A *ᵥ x')))) := h3
      have hm0 : 0 < mA n := by
        rcases Nat.eq_zero_or_pos (mA n) with h | h
        · exfalso; apply ha; funext i; exact absurd i.2 (by omega)
        · exact h
      have hv : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
        have : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm0
        positivity
      have hm := d3_overlap_lo_ge (M := mA n) hv ha ha' hq hql hη
      have e : Prod.mk A ⁻¹' S = {B | ∑ i, mask ((B *ᵥ reluV (A *ᵥ x)) i) *
          mask ((B *ᵥ reluV (A *ᵥ x')) i) < ((mA n : ℕ) : ℝ) * (kdot ql / 2 - η)} := by
        ext B
        simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, cnt2]
        constructor
        · intro h; exact h.2.2.2
        · intro h; exact ⟨h1, h2, h3, h⟩
      rw [e, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hm
    · have e : Prod.mk A ⁻¹' S = ∅ := by
        ext B
        simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hA ⟨h.1, h.2.1, h.2.2.1⟩
      rw [e, measure_empty]
      exact bot_le
  rw [lintegral_const, measure_univ, mul_one] at hle
  calc (∫⁻ A, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (ENNReal.ofReal (exp (-2 * η ^ 2 * (mA n : ℕ)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = exp (-2 * η ^ 2 * (mA n : ℕ)) := ENNReal.toReal_ofReal hB

/-- `c₁⁻ = (2a₋² − d₊²)/(2a₊²)`. -/
noncomputable def d3_c1lo (n : ℕ) (τ c : ℝ) : ℝ :=
  (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
      (√(2 * n * (1 - kappa c)) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
    (2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2)

/-- **The second-layer overlap lower tail of Lemma TI**:
`Pr_{A₁,A₂}(tr(D₂D₂') < m(κ̇(c₁⁻)/2 − η)) ≤ 5e^{−τ} + e^{−2η²m}`. -/
theorem d3_mask_second_tail_lo (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {τ η : ℝ} (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (ham : 0 < √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ)))
    (h6 : (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2) :
    (nuA n).real {θ | cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n τ (x ⬝ᵥ x')) / 2 - η)} ≤
      5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  set c1 := d3_c1lo n τ (x ⬝ᵥ x') with hc1d
  have hc1n : -1 ≤ c1 := by
    rw [hc1d]; unfold d3_c1lo
    have h0 : 0 ≤ 2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
      (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 := by linarith
    have : 0 ≤ (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
      (√(2 * n * (1 - kappa (x ⬝ᵥ x'))) + 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
      (2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2) := div_nonneg h0 (by positivity)
    linarith
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  set Bad := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
        c1 ≤ (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M))} with hBad
  have hfirst := d3_overlap_tail_lo hn hx hx' hτ ham h6
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot c1 / 2 - η)} ⊆
      (Bad ×ˢ Set.univ) ∪ {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧ c1 ≤ cosA x x' θ.1 ∧
        cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot c1 / 2 - η)} := by
    intro θ hθ
    by_cases h : θ.1 ∈ Bad
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · right
      simp only [hBad, Set.mem_ofPred_eq, not_not] at h
      exact ⟨h.1, h.2.1, h.2.2, hθ⟩
  have hprod : (nuA n).real (Bad ×ˢ Set.univ) = (gaussMat (mA n) n (2 / (n : ℝ))).real Bad := by
    unfold nuA
    rw [Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rfl
  calc (nuA n).real {θ | cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot c1 / 2 - η)}
      ≤ (nuA n).real ((Bad ×ˢ Set.univ) ∪ {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧
          c1 ≤ cosA x x' θ.1 ∧ cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot c1 / 2 - η)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (nuA n).real (Bad ×ˢ Set.univ) + (nuA n).real {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧
          c1 ≤ cosA x x' θ.1 ∧ cnt2 x x' θ < ((mA n : ℕ) : ℝ) * (kdot c1 / 2 - η)} :=
        measureReal_union_le _ _
    _ ≤ 5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) := by
        rw [hprod]
        exact add_le_add hfirst (d3_mask_second_joint_lo x x' hc1n hη)

end BstLean.Part185

open BstLean.Part185 in
#print axioms d3_overlap_lo
open BstLean.Part185 in
#print axioms d3_mask_second_tail_lo
