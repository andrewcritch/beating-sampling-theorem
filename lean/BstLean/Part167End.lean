import BstLean.Part167Red

/-!
# Part 167 (file `End`): the certificate charge from the a.e. form, and the end theorem with
Lemma LJ in its paper (Jacobian) form

No proof is left open; no `native_decide` or `axiom` is used.

* **`charge_one_ae`**: Part 166's `charge_one` with the per-input moment asked only for `v ≠ 0`
  (a null set of directions for the standard Gaussian vector).
* **`cert_charge_ae`**, **`cert_ret_charge_ae`**: the charge `12·10⁻⁵` of `E_lat` from
  `LJae_hyp n 4.53`.
* **`classifier_paper_JM80k`**: Part 166's `classifier_paper_LJ80k` with `LJ_hyp n 4.53`
  replaced by `JM_hyp n 4.53` (Lemma LJ in its paper form, on the explicit Jacobian).
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
  markov12 theta_mom measurable_psiK_f measurable_psiK_s delta_f_le delta_s_le goodD
  certs_of_goodD roomD roomD_ge)
open BstLean.Part165 (classifier_paper_root80k)

variable {n : ℕ}

/-- Almost every standard Gaussian direction is nonzero (`n ≥ 2`). -/
lemma ae_ne_zero_dir (hn : 2 ≤ n) : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
  have w0 : (Pi.single (⟨0, by omega⟩ : Fin (n - 1)) (1 : ℝ) : Fin (n - 1) → ℝ) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  filter_upwards [lin_ne_zero_ae w0] with v hv h0
  apply hv
  rw [h0]; simp

/-- **One certificate from the per-input moment for `v ≠ 0`** (Part 166's `charge_one`, a.e.). -/
theorem charge_one_ae (hn : 80000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ)
    {Φ : AgFam n → (Fin n → ℝ) → ℝ}
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hyp : ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
      ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)) :
    nuA n {θ | ENNReal.ofReal (C ^ 12) < certI Φ ((c, τ), θ)} ≤
      ENNReal.ofReal ((619 / 1000 * K / C) ^ 64) := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  have hdir := ae_ne_zero_dir (n := n) (by omega)
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
  have hnum : ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      ENNReal.ofReal ((619 / 1000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
    calc ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ ∫⁻ a, ∫⁻ _v : Fin (n - 1) → ℝ,
            ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)
            ∂stdGauss (Fin (n - 1)) ∂muI n :=
          lintegral_mono fun a => lintegral_mono_ae (hdir.mono fun v hv => hyp a v hv)
      _ = ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) *
            ENNReal.ofReal (K ^ 64) ∂muI n := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const, measure_univ, mul_one, mul_pow,
            ENNReal.ofReal_mul (by positivity)]
      _ = (∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) ∂muI n) *
            ENNReal.ofReal (K ^ 64) := by
          rw [lintegral_mul_const]
          exact ENNReal.measurable_ofReal.comp ((measurable_const.sub
            ((measurable_latitude_comp measurable_const measurable_const
              measurable_id).pow_const 2)).pow_const 64)
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

/-- **The charge of `E_lat` from the a.e. form of Lemma LJ**: `≤ 12·10⁻⁵` for every World value. -/
theorem cert_charge_ae (hn : 80000 ≤ n) (hLJ : LJae_hyp n (453 / 100)) (c : Fin n → ℝ) (τ : ℝ) :
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
    have h1 := charge_one_ae hn hw measurable_psiK_f (K := 453 / 100 / n) (C := Cf / n)
      (by positivity) (by unfold Cf; positivity) (fun a v hv => by
        have := (hLJ c τ hw a v hv).1
        rwa [mul_div_assoc] at this)
    have h2 := charge_one_ae hn hw measurable_psiK_s (K := 2 / n * (453 / 100) / n)
      (C := 326 / 100 * (2 / n) / n) (by positivity) (by positivity) (fun a v hv => by
        have := (hLJ c τ hw a v hv).2
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

/-- **The charge of `E_lat` on the retained data** from `LJae_hyp n 4.53`. -/
theorem cert_ret_charge_ae (hn : 80000 ≤ n) (hLJ : LJae_hyp n (453 / 100))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (Scert n))ᶜ ≤
      12 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_Scert n) (by norm_num) (fun c τ _ => cert_charge_ae hn hLJ c τ)

/-- **The classifier theorem with Lemma LJ in its paper form (`n ≥ 80 000`, floor
`d_low = 0.22005`).** IF the Jacobian moment `JM_hyp n 4.53` holds (Lemma LJ at `ℓ = 128` for
`y = b̂, r̂`), `E_A` is measurable with `Pr(HP ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomD`, and
`BIAS_hyp` holds on the good set `goodD`, THEN success has probability `≥ 99/100`. -/
theorem classifier_paper_JM80k (hn : 80000 ≤ n) (hJM : JM_hyp n (453 / 100))
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
  have hLJ : LJae_hyp n (453 / 100) := LJae_of_JM (by omega) hJM
  have hS : MeasurableSet (agentEv D (Scert n)) := measurableSet_agentEv D (measurableSet_Scert n)
  have hC := cert_ret_charge_ae hn hLJ fT wT hf hw
  refine classifier_paper_root80k hn fT wT hf hw t (hEA.inter hS) (δA := δA + 12 / 100000)
    ?_ ?_ (fun c hc => ⟨(certs_of_goodD hn fT wT hf hw hc).1,
      (certs_of_goodD hn fT wT hf hw hc).2, hB c hc⟩)
  · rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hC
  · unfold roomD at hroom; linarith

end BstLean.Part167
