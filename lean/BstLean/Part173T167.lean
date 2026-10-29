import BstLean.Part173T166
import BstLean.Part167All

/-!
# Part 173 (file `T167`): Part 167's results that need `n ≥ 80 000`, re-proved for `n ≥ 59 000`

No proof is left open; no `native_decide` or `axiom` is used.

This file was made by copying every theorem of Part 167 whose statement or proof uses `80000`,
replacing `80000` by `59000` and the tag `80k` by `59k`, and then repairing the proofs that fail.
The copies live in `BstLean.Part173.N59` and shadow the originals there; definitions are NOT copied
(the copies use Part 167's definitions; the only new definition of this chain is `roomE59`). The
docstrings are Part 167's, with `80 000` replaced by `59 000`; other numbers in the docstrings can
be Part 167's. The Lean statements are authoritative.

`charge_one_ae` with `Θ = 0.6222`; new `delta_f_59` (`≤ 7·10⁻⁴`), `delta_s_59` (`≤ 9.6·10⁻⁴`); the certificate charge is `≤ 17·10⁻⁴` (was `12·10⁻⁴`); NEW definition `roomE59 := roomC − 17·10⁻⁴` (`roomE59_ge`: `≥ 0.001292`; Part 167's `roomE = roomC − 12·10⁻⁴ ≥ 0.001792`), used in place of `roomE` in every later statement. Part 167's `cert_charge_ae`, `cert_ret_charge_ae`, `classifier_paper_JM80k` (the `K² = 4.53` route) are not copied.
-/

namespace BstLean.Part173.N59

-- ===== from Part167End.lean =====
section SPart167End
open BstLean.Part167
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
/-- **One certificate from the per-input moment for `v ≠ 0`** (Part 166's `charge_one`, a.e.). -/
theorem charge_one_ae (hn : 59000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ)
    {Φ : AgFam n → (Fin n → ℝ) → ℝ}
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hyp : ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
      ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)) :
    nuA n {θ | ENNReal.ofReal (C ^ 12) < certI Φ ((c, τ), θ)} ≤
      ENNReal.ofReal ((6222 / 10000 * K / C) ^ 64) := by
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
      ENNReal.ofReal ((6222 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
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
      _ ≤ ENNReal.ofReal ((6222 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
          gcongr
          exact theta_mom hn c hτ hθ0 hθ1
  calc (∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n) / ENNReal.ofReal (C ^ 64)
      ≤ ENNReal.ofReal ((6222 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) /
          ENNReal.ofReal (C ^ 64) := by gcongr
    _ = ENNReal.ofReal ((6222 / 10000 * K / C) ^ 64) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
        rw [div_pow (6222 / 10000 * K) C 64, mul_pow (6222 / 10000 : ℝ) K 64]

end SPart167End

-- ===== from Part167Fin.lean =====
section SPart167Fin
open BstLean.Part167
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
/-- Part 167's `delta_f_47` with the latitude moment `Θ = 0.6222` (`n ≥ 59 000`). -/
lemma delta_f_59 : (6222 / 10000 * (47 / 10) / Cf : ℝ) ^ 64 ≤ 70 / 100000 := by
  have h1 : (6222 / 10000 * (47 / 10) / Cf : ℝ) ≤ 8925 / 10000 := by unfold Cf; norm_num
  have h0 : (0 : ℝ) ≤ 6222 / 10000 * (47 / 10) / Cf := by unfold Cf; positivity
  calc (6222 / 10000 * (47 / 10) / Cf : ℝ) ^ 64 ≤ (8925 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ h0 h1 64
    _ ≤ 70 / 100000 := by norm_num

/-- Part 167's `delta_s_47` with `Θ = 0.6222`. -/
lemma delta_s_59 : (6222 / 10000 * (47 / 10) / (326 / 100) : ℝ) ^ 64 ≤ 96 / 100000 := by
  have h1 : (6222 / 10000 * (47 / 10) / (326 / 100) : ℝ) ≤ 8971 / 10000 := by norm_num
  calc (6222 / 10000 * (47 / 10) / (326 / 100) : ℝ) ^ 64 ≤ (8971 / 10000 : ℝ) ^ 64 :=
        pow_le_pow_left₀ (by norm_num) h1 64
    _ ≤ 96 / 100000 := by norm_num

/-- Part 167's `roomE` with the certificate charge `17·10⁻⁴` in place of `12·10⁻⁴` (the larger
latitude moment `Θ = 0.6222` at `n ≥ 59 000`). A new definition of Part 173. -/
noncomputable def roomE59 : ℝ := roomC - 17 / 10000

theorem roomE59_ge : (1292 : ℝ) / 10 ^ 6 ≤ roomE59 := by
  unfold roomE59; have := roomC_ge; linarith

/-- **The charge of `E_lat` from the a.e. form of Lemma LJ**: `≤ 12·10⁻⁴` for every World value. -/
theorem cert_charge_47 (hn : 59000 ≤ n) (hLJ : LJae_hyp n (47 / 10)) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ Scert n} ≤ 17 / 10000 := by
  have hn0 : (0 : ℝ) < n := by
    have : (59000 : ℝ) ≤ n := by exact_mod_cast hn
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
    have e1 : 6222 / 10000 * (47 / 10 / n) / (Cf / n) = 6222 / 10000 * (47 / 10) / Cf := by
      field_simp
    have e2 : 6222 / 10000 * (2 / n * (47 / 10) / n) / (326 / 100 * (2 / n) / n) =
        6222 / 10000 * (47 / 10) / (326 / 100 : ℝ) := by
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    have hU : nuA n {θ | ((c, τ), θ) ∉ Scert n} ≤
        ENNReal.ofReal (70 / 100000) + ENNReal.ofReal (96 / 100000) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact h1.trans (ENNReal.ofReal_le_ofReal delta_f_59)
      · exact h2.trans (ENNReal.ofReal_le_ofReal delta_s_59)
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
theorem cert_ret_charge_47 (hn : 59000 ≤ n) (hLJ : LJae_hyp n (47 / 10))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (Scert n))ᶜ ≤
      17 / 10000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_Scert n) (by norm_num) (fun c τ _ => cert_charge_47 hn hLJ c τ)

/-- **The classifier theorem with Lemma LJ in its Jacobian form at `K2 = 4.7`** (every
`n ≥ 59 000`, floor `d_low = 0.22005`). -/
theorem classifier_paper_JM47 (hn : 59000 ≤ n) (hJM : JM_hyp n (47 / 10))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE59)
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
  refine classifier_paper_root59k hn fT wT hf hw t (hEA.inter hS) (δA := δA + 17 / 10000)
    ?_ ?_ (fun c hc => ⟨(certs_of_goodD hn fT wT hf hw hc).1,
      (certs_of_goodD hn fT wT hf hw hc).2, hB c hc⟩)
  · rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hC
  · unfold roomE59 at hroom; linarith

/-- **The classifier theorem with Lemma LJ reduced to the moments `X` and `Y`.** -/
theorem classifier_paper_XY59k (hn : 59000 ≤ n) {X2 Y2 : ℝ} (hX2 : 0 < X2) (hY2 : 0 < Y2)
    (hXY : XY_hyp n X2 Y2) (hK : K2XY n X2 Y2 ≤ 47 / 10)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE59)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_JM47 hn (JM_mono (by unfold K2XY; positivity) hK (JM_of_XY (by omega) hX2 hY2 hXY))
    fT wT hf hw t hEA hA hroom hB

end SPart167Fin

-- ===== from Part167Y.lean =====
section SPart167Y
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask mask_nonneg mask_sq measurable_mask)
variable {n m : ℕ}
open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC)
open BstLean.Part157 (latitude)
open BstLean.Part53 (unitF53)
/-- **The masked Frobenius moment is proved**: `Ymom ≤ Y2n^{64}` for every `n ≥ 59 000`. -/
theorem Y_bound (hn : 59000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ) (a : Ix n)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    Ymom c τ a v ≤ ENNReal.ofReal (Y2n n ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hc := window_c_ne hn1 hw
  obtain ⟨hu, hw1, huw⟩ := frame_orth hn1 hc hv
  set s := latitude (n := n) (√(normSq c)) τ a with hsdef
  have hs : s ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  set cc := √(1 - s ^ 2)
  have hsc : s ^ 2 + cc ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  have hc' : (rc c).1.2 ≠ 0 := hc
  have hx : xLat (rc c) s (unitF53 v) = s • uHat (rc c) + cc • dirW (rc c) (unitF53 v) :=
    BstLean.Part161.xLat_eq hn1 hc' s (unitF53 v)
  have hx1 : normSq (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) = 1 := by
    rw [normSq_two, hu, hw1, huw]; linarith
  unfold Ymom
  rw [← hsdef, hx]
  have hpt : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      ENNReal.ofReal (frobSq (Pmat (uHat (rc c)) (dirW (rc c) (unitF53 v)) *
        (D1A1 A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)))ᵀ) ^ 64) ≤
      ENNReal.ofReal (Qf A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) ^ 64) := fun A₁ =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (frobSq_nonneg _)
      (frob_le_Q hu hw1 huw hsc A₁) 64)
  refine (lintegral_mono hpt).trans ?_
  have hnR : (59000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hM := Y2n_pos (n := n) (by omega)
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hd : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; simp
  have hτ : 64 / Y2n n * (2 / (n : ℝ)) =
      64 / (1001 / 1000 * (((mA n : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) / 2)) := by
    unfold Y2n; field_simp
  refine Q_mom hn1 hx1 hγ hM ?_ ?_
  · rw [hτ, hmA, hd, div_lt_iff₀ (by nlinarith)]
    nlinarith
  · rw [hτ]
    exact Y_num (d := n - 1) (m := mA n) (by omega) (by unfold mA; nlinarith)

theorem XY_of_X (hn : 59000 ≤ n) {X2 : ℝ} (h : X_hyp n X2) : XY_hyp n X2 (Y2n n) :=
  fun c τ hw a v hv => ⟨(h c τ hw a v hv).1, (h c τ hw a v hv).2, Y_bound hn hw a hv⟩

open BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157 BstLean.Part160 in
open BstLean.Part161 (BIAS_hyp) in
open BstLean.Part162 (dPaper) in
open BstLean.Part166 (goodD) in
/-- **The classifier theorem with Lemma LJ reduced to the plane moment `X` alone** (`Y` and `Z`
are proved; every `n ≥ 59 000`, floor `d_low = 0.22005`, room `roomE ≥ 0.001792`). -/
theorem classifier_paper_X59k (hn : 59000 ≤ n) {X2 : ℝ} (hX2 : 0 < X2) (hX : X_hyp n X2)
    (hK : K2XY n X2 (Y2n n) ≤ 47 / 10)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE59)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_XY59k hn hX2 (Y2n_pos (by omega)) (XY_of_X hn hX) hK fT wT hf hw t hEA hA
    hroom hB

end SPart167Y

end BstLean.Part173.N59
