import BstLean.Part167XY
import BstLean.Part167End

/-!
# Part 167 (file `Fin`): the end theorems with Lemma LJ in its Jacobian form or its `X`/`Y` form

No proof is left open; no `native_decide` or `axiom` is used.

Lean's constants for the transverse step (`C = (π/2)(E|g|^{128})^{1/128}`, Part 162's Poincaré) are
larger than the paper's `k_ℓ`, so the `K_ℓ²` that the `X`/`Y` route can reach is about `4.6`,
above Part 166's `4.53`. This file therefore charges the certificate event at `K2 = 4.7`:
`(0.619·4.7/C_f)^{64} ≤ 5·10⁻⁴`, `(0.619·4.7/(3.26))^{64} ≤ 7·10⁻⁴`, charge `12·10⁻⁴`.

* **`classifier_paper_JM47`**: Part 166's end theorem with `JM_hyp n 4.7`; room `roomE`.
* **`classifier_paper_XY80k`**: the same with `XY_hyp n X2 Y2` and `K2XY n X2 Y2 ≤ 4.7`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (muI Ix BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part153 (nuA)
open BstLean.Part166 (psiK psiK_nonneg fK sK winC certI Cf Scert measurableSet_Scert
  markov12 theta_mom measurable_psiK_f measurable_psiK_s goodD pow64_le
  certs_of_goodD)
open BstLean.Part165 (roomC roomC_ge classifier_paper_root80k)

variable {n : ℕ}

lemma delta_f_47 : (619 / 1000 * (47 / 10) / Cf : ℝ) ^ 64 ≤ 5 / 10000 := by
  have h1 : (619 / 1000 * (47 / 10) / Cf : ℝ) ≤ 8879 / 10000 := by unfold Cf; norm_num
  refine pow64_le (by unfold Cf; positivity) ?_ (b := 3864 / 10000) (by norm_num)
  exact (pow_le_pow_left₀ (by unfold Cf; positivity) h1 8).trans (by norm_num)

lemma delta_s_47 : (619 / 1000 * (47 / 10) / (326 / 100) : ℝ) ^ 64 ≤ 7 / 10000 := by
  have h1 : (619 / 1000 * (47 / 10) / (326 / 100) : ℝ) ≤ 8925 / 10000 := by norm_num
  refine pow64_le (by positivity) ?_ (b := 4026 / 10000) (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) h1 8).trans (by norm_num)

/-- **The charge of `E_lat` from the a.e. form of Lemma LJ**: `≤ 12·10⁻⁴` for every World value. -/
theorem cert_charge_47 (hn : 80000 ≤ n) (hLJ : LJae_hyp n (47 / 10)) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ Scert n} ≤ 12 / 10000 := by
  have hn0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hw : winC c τ
  · have hsub : {θ | ((c, τ), θ) ∉ Scert n} ⊆
        {θ | ENNReal.ofReal ((Cf / n) ^ 12) < certI fK ((c, τ), θ)} ∪
        {θ | ENNReal.ofReal ((326 / 100 * (2 / n) / n) ^ 12) < certI sK ((c, τ), θ)} := by
      intro θ hθ
      simp only [Scert, Set.mem_ofPred_eq, not_imp, not_and_or, not_le] at hθ
      rcases hθ.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 := charge_one_ae hn hw measurable_psiK_f (K := 47 / 10 / n) (C := Cf / n)
      (by positivity) (by unfold Cf; positivity) (fun a v hv => by
        have := (hLJ c τ hw a v hv).1
        rwa [mul_div_assoc] at this)
    have h2 := charge_one_ae hn hw measurable_psiK_s (K := 2 / n * (47 / 10) / n)
      (C := 326 / 100 * (2 / n) / n) (by positivity) (by positivity) (fun a v hv => by
        have := (hLJ c τ hw a v hv).2
        rwa [mul_assoc, mul_div_assoc] at this)
    have e1 : 619 / 1000 * (47 / 10 / n) / (Cf / n) = 619 / 1000 * (47 / 10) / Cf := by
      field_simp
    have e2 : 619 / 1000 * (2 / n * (47 / 10) / n) / (326 / 100 * (2 / n) / n) =
        619 / 1000 * (47 / 10) / (326 / 100 : ℝ) := by
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    have hU : nuA n {θ | ((c, τ), θ) ∉ Scert n} ≤
        ENNReal.ofReal (5 / 10000) + ENNReal.ofReal (7 / 10000) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact h1.trans (ENNReal.ofReal_le_ofReal delta_f_47)
      · exact h2.trans (ENNReal.ofReal_le_ofReal delta_s_47)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hU
    have := ENNReal.toReal_le_of_le_ofReal (by norm_num) hU
    rw [measureReal_def]
    linarith
  · have e : {θ | ((c, τ), θ) ∉ Scert n} = ∅ := by
      ext θ
      simp only [Scert, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun h => absurd h hw
    rw [e]
    simp only [measureReal_empty]
    norm_num

/-- **The charge of `E_lat` on the retained data** from `LJae_hyp n 4.53`. -/
theorem cert_ret_charge_47 (hn : 80000 ≤ n) (hLJ : LJae_hyp n (47 / 10))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (Scert n))ᶜ ≤
      12 / 10000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_Scert n) (by norm_num) (fun c τ _ => cert_charge_47 hn hLJ c τ)

/-- The room that remains: `roomC − 12·10⁻⁴`. -/
noncomputable def roomE : ℝ := roomC - 12 / 10000

theorem roomE_ge : (1792 : ℝ) / 10 ^ 6 ≤ roomE := by
  unfold roomE; have := roomC_ge; linarith

/-- **The classifier theorem with Lemma LJ in its Jacobian form at `K2 = 4.7`** (every
`n ≥ 80 000`, floor `d_low = 0.22005`). -/
theorem classifier_paper_JM47 (hn : 80000 ≤ n) (hJM : JM_hyp n (47 / 10))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  have hLJ : LJae_hyp n (47 / 10) := LJae_of_JM (by omega) hJM
  have hS : MeasurableSet (agentEv D (Scert n)) := measurableSet_agentEv D (measurableSet_Scert n)
  have hC := cert_ret_charge_47 hn hLJ fT wT hf hw
  refine classifier_paper_root80k hn fT wT hf hw t (hEA.inter hS) (δA := δA + 12 / 10000)
    ?_ ?_ (fun c hc => ⟨(certs_of_goodD hn fT wT hf hw hc).1,
      (certs_of_goodD hn fT wT hf hw hc).2, hB c hc⟩)
  · rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hC
  · unfold roomE at hroom; linarith

/-- **The classifier theorem with Lemma LJ reduced to the moments `X` and `Y`.** -/
theorem classifier_paper_XY80k (hn : 80000 ≤ n) {X2 Y2 : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2)
    (hXY : XY_hyp n X2 Y2) (hK : K2XY n X2 Y2 ≤ 47 / 10)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_JM47 hn (JM_mono (by unfold K2XY; positivity) hK (JM_of_XY (by omega) hX2 hY2 hXY))
    fT wT hf hw t hEA hA hroom hB

end BstLean.Part167
