import BstLean.Part166Tr
import BstLean.Part166Mk
import BstLean.Part166Th

/-!
# Part 166 (file `End`): the certificate event, its charge from Lemma LJ, and the end theorem

No proof is left open; no `native_decide` or `axiom` is used.

* `winC ĉ τ`: the World window `τ > 0`, `0.46 ≤ θ_in ≤ 0.55`.
* `LJ_hyp n K2`: **the per-input weight moment of Lemma LJ** (paper `t7:p07:LJ` with Lemma J and
  the tangential identity): for every World value in the window and every input `(a, v)`,
  `E_{A₁,A₂} Ψ_f^{64} ≤ ((1 − s²)·K2/n)^{64}` and `E_{A₁,A₂} Ψ_σ^{64} ≤ ((1 − s²)·γ_A·K2/n)^{64}`
  (order `ℓ = 128` of `|P_lat 𝒥ᵀy|/|y|`; `K2` stands for `K_ℓ²`).
* `Scert n`: the certificate event (Prop. `t7:p07:LG`, `E_lat`) at `C_f = 3.27675`,
  `C_σ = 3.26γ_A`; **`cert_charge`**: from `LJ_hyp n 4.53`, `Pr(E_latᶜ) ≤ 12·10⁻⁵` for every
  World value (Markov at order 64 with the latitude moment `theta_mom`, `Θ = 0.619`).
* **`certs_of_goodD`**: on the good set, Part 165's two certificates `‖Ψ_λ‖₁₂ ≤ 5.1/n`,
  `‖Ψ_σ‖₁₂ ≤ 3.26γ_A/n` hold (`e_b ≥ 0.6425` from Part 160's `eb16_lower`).
* **`classifier_paper_LJ80k`**: Part 165's `classifier_paper_root80k` with the two certificates
  replaced by `LJ_hyp n (453/100)`; room `roomD = roomC − 12·10⁻⁵ ≥ 0.002872`.
-/

namespace BstLean.Part166

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (xLat hhMat uHat consV muI latC lamX sigX Ix BIAS_hyp)
open BstLean.Part162 (xLatH tanSq psiA dPaper)
open BstLean.Part153 (nuA)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
open BstLean.Part165 (goodC roomC roomC_ge classifier_paper_root80k)

variable {n : ℕ}

/-- The World window. -/
def winC (c : Fin n → ℝ) (τ : ℝ) : Prop :=
  0 < τ ∧ 46 / 100 ≤ thetaC c τ ∧ thetaC c τ ≤ 55 / 100

/-- The order-12 certificate integral of `Ψ` at the key (in `ℝ≥0∞`). -/
noncomputable def certI (Φ : AgFam n → (Fin n → ℝ) → ℝ) (k : AgFam n) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ v, ENNReal.ofReal (psiK Φ k a v ^ 12) ∂stdGauss (Fin (n - 1)) ∂muI n

/-- `C_f = 5.1·0.6425`. -/
noncomputable def Cf : ℝ := 327675 / 100000

/-- **The certificate event `E_lat`** as a family of Agent events: in the window, both
order-12 certificates hold. -/
def Scert (n : ℕ) : Set (AgFam n) :=
  {k | winC k.1.1 k.1.2 →
    certI fK k ≤ ENNReal.ofReal ((Cf / n) ^ 12) ∧
    certI sK k ≤ ENNReal.ofReal ((326 / 100 * (2 / n) / n) ^ 12)}

/-- **Lemma LJ (per-input weight moment, order 128), as a hypothesis.** -/
def LJ_hyp (n : ℕ) (K2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ),
    ∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K2 / n) ^ 64) ∧
    ∫⁻ θ, ENNReal.ofReal (psiK sK ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * (2 / n) * K2 / n) ^ 64)

/-! ## Measurability -/

lemma measurable_certI {Φ : AgFam n → (Fin n → ℝ) → ℝ}
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2)) :
    Measurable (certI Φ) := by
  have h1 : Measurable (fun p : (AgFam n × Ix n) × (Fin (n - 1) → ℝ) =>
      ENNReal.ofReal (psiK Φ p.1.1 p.1.2 p.2 ^ 12)) := by
    have hm : Measurable (fun p : (AgFam n × Ix n) × (Fin (n - 1) → ℝ) =>
        ((p.1.1, p.1.2, p.2) : AgFam n × Ix n × (Fin (n - 1) → ℝ))) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h2 := hΦ.comp hm
    rw [Function.comp_def] at h2
    exact ENNReal.measurable_ofReal.comp (h2.pow_const 12)
  have h3 := h1.lintegral_prod_right' (ν := stdGauss (Fin (n - 1)))
  exact h3.lintegral_prod_right' (ν := muI n)

lemma measurable_thetaC_key : Measurable (fun k : AgFam n => thetaC k.1.1 k.1.2) := by
  unfold thetaC
  exact (measurable_const.mul ((measurable_snd.comp measurable_fst).pow_const 2)).div
    (measurable_rhoC_key.pow_const 2)

lemma measurableSet_Scert (n : ℕ) : MeasurableSet (Scert n) := by
  have hw : MeasurableSet {k : AgFam n | winC k.1.1 k.1.2} :=
    (measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)).inter
      ((measurableSet_le measurable_const measurable_thetaC_key).inter
      (measurableSet_le measurable_thetaC_key measurable_const))
  have hf : MeasurableSet {k : AgFam n | certI fK k ≤ ENNReal.ofReal ((Cf / n) ^ 12)} :=
    measurableSet_le (measurable_certI measurable_psiK_f) measurable_const
  have hs : MeasurableSet {k : AgFam n |
      certI sK k ≤ ENNReal.ofReal ((326 / 100 * (2 / n) / n) ^ 12)} :=
    measurableSet_le (measurable_certI measurable_psiK_s) measurable_const
  have e : Scert n = {k : AgFam n | winC k.1.1 k.1.2}ᶜ ∪
      ({k : AgFam n | certI fK k ≤ ENNReal.ofReal ((Cf / n) ^ 12)} ∩
        {k : AgFam n | certI sK k ≤ ENNReal.ofReal ((326 / 100 * (2 / n) / n) ^ 12)}) := by
    ext k
    simp only [Scert, Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff]
    tauto
  rw [e]
  exact hw.compl.union (hf.inter hs)

/-! ## The charge of one certificate (Markov at order 64) -/

/-- **One certificate from the per-input moment**: if `E_A Ψ^{64} ≤ ((1 − s²)·K)^{64}` for every
input, then `Pr_A(certificate integral > C^{12}) ≤ (0.619·K/C)^{64}` (`n ≥ 80 000`, window). -/
theorem charge_one (hn : 80000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ)
    {Φ : AgFam n → (Fin n → ℝ) → ℝ}
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hyp : ∀ (a : Ix n) (v : Fin (n - 1) → ℝ),
      ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)) :
    nuA n {θ | ENNReal.ofReal (C ^ 12) < certI Φ ((c, τ), θ)} ≤
      ENNReal.ofReal ((619 / 1000 * K / C) ^ 64) := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  have hm : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
      × Ix n × (Fin (n - 1) → ℝ) => psiK Φ ((c, τ), z.1) z.2.1 z.2.2) := by
    have hk : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × Ix n × (Fin (n - 1) → ℝ) =>
        ((((c, τ), z.1) : AgFam n), z.2.1, z.2.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
    have h2 := hΦ.comp hk
    rw [Function.comp_def] at h2
    exact h2
  have hM := markov12 (nuA n) (muI n) (stdGauss (Fin (n - 1)))
    (fun θ a v => psiK Φ ((c, τ), θ) a v) hm (fun _ _ _ => psiK_nonneg _ _ _ _)
    (p := 64) (by norm_num) hC
  refine hM.trans ?_
  -- the numerator
  have hnum : ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      ENNReal.ofReal ((619 / 1000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
    calc ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ ∫⁻ a, ∫⁻ _v : Fin (n - 1) → ℝ,
            ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)
            ∂stdGauss (Fin (n - 1)) ∂muI n :=
          lintegral_mono fun a => lintegral_mono fun v => hyp a v
      _ = ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) *
            ENNReal.ofReal (K ^ 64) ∂muI n := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const, measure_univ, mul_one, mul_pow,
            ENNReal.ofReal_mul (by positivity)]
      _ = (∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) ∂muI n) *
            ENNReal.ofReal (K ^ 64) := by
          rw [lintegral_mul_const]
          exact ENNReal.measurable_ofReal.comp ((measurable_const.sub
            ((measurable_latitude_comp measurable_const measurable_const measurable_id).pow_const 2)).pow_const 64)
      _ ≤ ENNReal.ofReal ((619 / 1000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
          gcongr
          exact theta_mom hn c hτ hθ0 hθ1
  calc (∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n) / ENNReal.ofReal (C ^ 64)
      ≤ ENNReal.ofReal ((619 / 1000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) /
          ENNReal.ofReal (C ^ 64) := by gcongr
    _ = ENNReal.ofReal ((619 / 1000 * K / C) ^ 64) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
        rw [div_pow (619 / 1000 * K) C 64, mul_pow (619 / 1000 : ℝ) K 64]

/-- `δ_f`, `δ_σ`: the two Markov charges at `K2 = 4.53`. -/
lemma pow64_le {x b c : ℝ} (_hx : 0 ≤ x) (h8 : x ^ 8 ≤ b) (hb : b ^ 8 ≤ c) : x ^ 64 ≤ c := by
  have e : x ^ 64 = (x ^ 8) ^ 8 := by rw [← pow_mul]
  rw [e]
  exact (pow_le_pow_left₀ (by positivity) h8 8).trans hb

lemma delta_f_le : (619 / 1000 * (453 / 100) / Cf : ℝ) ^ 64 ≤ 5 / 100000 := by
  have h1 : (619 / 1000 * (453 / 100) / Cf : ℝ) ≤ 856 / 1000 := by unfold Cf; norm_num
  refine pow64_le (by unfold Cf; positivity) ?_ (b := 2883 / 10000) (by norm_num)
  exact (pow_le_pow_left₀ (by unfold Cf; positivity) h1 8).trans (by norm_num)

lemma delta_s_le : (619 / 1000 * (453 / 100) / (326 / 100) : ℝ) ^ 64 ≤ 7 / 100000 := by
  have h1 : (619 / 1000 * (453 / 100) / (326 / 100) : ℝ) ≤ 861 / 1000 := by norm_num
  refine pow64_le (by positivity) ?_ (b := 3021 / 10000) (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) h1 8).trans (by norm_num)

/-- **The charge of `E_lat`**: from `LJ_hyp n 4.53`, for every World value with `τ > 0`,
`Pr_A((ĉ, τ, A) ∉ Scert) ≤ 12·10⁻⁵` (`n ≥ 80 000`). -/
theorem cert_charge (hn : 80000 ≤ n) (hLJ : LJ_hyp n (453 / 100)) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ Scert n} ≤ 12 / 100000 := by
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
    have h1 := charge_one hn hw measurable_psiK_f (K := 453 / 100 / n) (C := Cf / n)
      (by positivity) (by unfold Cf; positivity) (fun a v => by
        have := (hLJ c τ hw a v).1
        rwa [mul_div_assoc] at this)
    have h2 := charge_one hn hw measurable_psiK_s (K := 2 / n * (453 / 100) / n)
      (C := 326 / 100 * (2 / n) / n) (by positivity) (by positivity) (fun a v => by
        have := (hLJ c τ hw a v).2
        rwa [mul_assoc, mul_div_assoc] at this)
    have e1 : 619 / 1000 * (453 / 100 / n) / (Cf / n) = 619 / 1000 * (453 / 100) / Cf := by
      field_simp
    have e2 : 619 / 1000 * (2 / n * (453 / 100) / n) / (326 / 100 * (2 / n) / n) =
        619 / 1000 * (453 / 100) / (326 / 100 : ℝ) := by
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    have hU : nuA n {θ | ((c, τ), θ) ∉ Scert n} ≤
        ENNReal.ofReal (5 / 100000) + ENNReal.ofReal (7 / 100000) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact h1.trans (ENNReal.ofReal_le_ofReal delta_f_le)
      · exact h2.trans (ENNReal.ofReal_le_ofReal delta_s_le)
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

/-- **The charge of `E_lat` on the retained data**: `Pr((agentEv D (Scert n))ᶜ) ≤ 12·10⁻⁵`. -/
theorem cert_ret_charge (hn : 80000 ≤ n) (hLJ : LJ_hyp n (453 / 100)) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (Scert n))ᶜ ≤
      12 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_Scert n) (by norm_num) (fun c τ _ => cert_charge hn hLJ c τ)

/-! ## The certificates on the good set -/

/-- The good set of the new end theorem. -/
def goodD (n : ℕ) (D : Design n) (EA : Set (Ret n)) : Set (Ret n) :=
  goodC n D (EA ∩ agentEv D (Scert n))

/-- **Part 165's two certificates on the good set.** -/
theorem certs_of_goodD (hn : 80000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodD n (paperDesign n fT wT hf hw) EA) :
    (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
    (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) := by
  set D := paperDesign n fT wT hf hw with hDd
  have hn16 : 16384 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD := paperDesign_agentCentre fT wT hf hw
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hS : agKey D c ∈ Scert n := hc.2.1.2.1.1.1.2 hτ
  obtain ⟨hcf, hcs⟩ := hS ⟨hτ, hθ0, hθ1⟩
  set k := agKey D c with hk
  have hmk : ∀ {Φ : AgFam n → (Fin n → ℝ) → ℝ},
      Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2) →
      Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) => psiK Φ k z.1 z.2 ^ 12) := by
    intro Φ hΦ
    have hm : Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) =>
        ((k, z.1, z.2) : AgFam n × Ix n × (Fin (n - 1) → ℝ))) :=
      measurable_const.prodMk (measurable_fst.prodMk measurable_snd)
    have h2 := hΦ.comp hm
    rw [Function.comp_def] at h2
    exact h2.pow_const 12
  -- σ
  have hsig : ∫ a, ∫ v, psiK sK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK sK k a v ^ 12)
      (hmk measurable_psiK_s) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _) (by positivity) hcs
  have hfK : ∫ a, ∫ v, psiK fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (Cf / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK fK k a v ^ 12)
      (hmk measurable_psiK_f) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _)
      (by unfold Cf; positivity) hcf
  refine ⟨?_, ?_⟩
  · -- the energy lower bound `e_b ≥ 0.6425`
    have hG := goodC16_of_goodA hn16 fT wT hf hw hc
    have hU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hc.2.2.1.2 hτ
    have hlo := eb16_lower hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hU
    have hb : D.bA c.1 c.2.1.1 =
        (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
    rw [← hb] at hlo
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    rw [hmA] at hlo
    set e := normSq (D.bA c.1 c.2.1.1) / n with he
    have he0 : 257 / 400 ≤ e := by
      rw [he, le_div_iff₀ hn0]
      have h2 : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) ≤
          2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      have l : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) = 257 / 400 * n := by field_simp
      have r : 2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) =
          normSq (D.bA c.1 c.2.1.1) := by field_simp
      linarith
    have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he0
    have hpt : ∀ a v, psiA (lamX D c) D c a v ^ 12 = (e⁻¹) ^ 12 * psiK fK k a v ^ 12 := by
      intro a v
      have h := psiA_lam_eq (by omega) D hD c a v
      rw [← he] at h
      rw [← h, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hepos.ne', one_pow, one_mul]
    simp_rw [hpt, integral_const_mul]
    calc (e⁻¹) ^ 12 * ∫ a, ∫ v, psiK fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ (e⁻¹) ^ 12 * (Cf / n) ^ 12 := mul_le_mul_of_nonneg_left hfK (by positivity)
      _ = (Cf / e / n) ^ 12 := by rw [← mul_pow]; congr 1; field_simp
      _ ≤ (51 / 10 / n) ^ 12 := by
          apply pow_le_pow_left₀ (by unfold Cf; positivity)
          apply div_le_div_of_nonneg_right _ hn0.le
          rw [div_le_iff₀ hepos]
          unfold Cf
          linarith
  · simp_rw [psiA_sig_eq D hD c]
    exact hsig

/-! ## The end theorem -/

/-- The room that remains: `roomC − 12·10⁻⁵`. -/
noncomputable def roomD : ℝ := roomC - 12 / 100000

theorem roomD_ge : (2872 : ℝ) / 10 ^ 6 ≤ roomD := by
  unfold roomD; have := roomC_ge; linarith

/-- **The classifier theorem with the two order-12 certificates replaced by Lemma LJ (every
`n ≥ 80 000`, floor `d_low = 0.22005`).** IF Lemma LJ holds in the form `LJ_hyp n 4.53`, `E_A` is
measurable with `Pr(HP ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomD`, and `BIAS_hyp` holds on the good
set `goodD`, THEN success has probability `≥ 99/100` for the actual random networks. -/
theorem classifier_paper_LJ80k (hn : 80000 ≤ n) (hLJ : LJ_hyp n (453 / 100))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomD)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  have hS : MeasurableSet (agentEv D (Scert n)) := measurableSet_agentEv D (measurableSet_Scert n)
  have hC := cert_ret_charge hn hLJ fT wT hf hw
  refine classifier_paper_root80k hn fT wT hf hw t (hEA.inter hS) (δA := δA + 12 / 100000)
    ?_ ?_ (fun c hc => ⟨(certs_of_goodD hn fT wT hf hw hc).1,
      (certs_of_goodD hn fT wT hf hw hc).2, hB c hc⟩)
  · rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hC
  · unfold roomD at hroom; linarith

end BstLean.Part166
