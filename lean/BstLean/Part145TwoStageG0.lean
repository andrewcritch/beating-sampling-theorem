import BstLean.Part145TwoStage
import BstLean.Part145JointG0

/-!
# Part 145: the measurable success event and the two-stage form for an abstract event `G`

The statements of `Part145TwoStage` (`okProgE`, `progJointE145`, `twoStageProg145`) for a good
hidden event `G` with `GoodEv0 n G` (`Part145G5`): `okProgEG G k`, `progJointEG0`,
`twoStageProgG0`. `ok_jointE` and `map_wfag` are those of `Part145TwoStage`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143

/-- The measurable event inside `okProgA k n`: `W` good, no zero point, and the sample estimate
within `sd/2` of `B`. -/
def okProgEG {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) (k : ℕ) :
    Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | p.1.1 ∈ goodWAG G ∧ (∀ i, normSq (preA p.1.1 (p.2 i)) ≠ 0) ∧
    |gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
      sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

lemma okProgEG_sub {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) (k : ℕ) :
    okProgEG G k ⊆ okProgA k n := by
  rintro p ⟨_, hz, hok⟩
  change |gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2
  rw [gProgA_eq k p.1.1 p.1.2.1 p.1.2.2 p.2 hz]
  exact hok

lemma okProgEG_meas {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    (k : ℕ) : MeasurableSet (okProgEG G k) := by
  have hN : 1 ≤ 2 * n := by omega
  have m1 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G} :=
    (measurable_fst.comp measurable_fst) (goodWAG0_meas hG hn)
  have m2 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
      ∀ i, normSq (preA p.1.1 (p.2 i)) ≠ 0} := by
    have e : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        ∀ i, normSq (preA p.1.1 (p.2 i)) ≠ 0} =
        ⋂ i : Fin k, {p | normSq (preA p.1.1 (p.2 i)) = 0}ᶜ := by
      ext p; simp
    rw [e]
    refine MeasurableSet.iInter fun i => ?_
    have hm : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => normSq (preA p.1.1 (p.2 i))) :=
      measurable_normSq.comp (measurable_preA.comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)))
    exact (hm (measurableSet_singleton 0)).compl
  have m3 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
      |gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} :=
    measurableSet_le (((measurable_gSampleA k).sub
      ((BstLean.Part131.measurable_Bn hN).comp measurable_fst)).abs)
      (((measurable_sdn (mA := mA n) (mF := mF n) hN).comp measurable_fst).div_const 2)
  exact m1.inter (m2.inter m3)

/-- **`progJoint145` for the measurable event `okProgEG G k`** (the same hypotheses and the same
bound). -/
theorem progJointEG0 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    {p₁ : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p₁)
    {X xa : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ xa * (1 / (n : ℝ)))
    (hE : ∫⁻ p, ENNReal.ofReal (errSAG G k p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))))
    {e ce : ℝ} (he : 0 ≤ e) (hce : e ≤ ce / √(n : ℝ))
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    1 - (p₁ + (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
          2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgEG G k) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hy0 : (0 : ℝ) < 1 - kappa^[6] 0 := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  set c : ℝ := 4 / (n : ℝ) * (1 - kappa^[6] 0) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set μ := (mlpTriple 2 n).prod (gamK k n) with hμ
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWAG G ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtAG0_null hn hG k]
    rfl
  have h1' : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G}ᶜ ≤ p₁ + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWAG G}).trans_le
      (badAG0_prob_gen hn hG h1)
  -- the spread under the product measure
  have msd3 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => sdn t.1 t.2.1 t.2.2) := measurable_sdn (mA := mA n) (mF := mF n) hN
  have msd : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => sdn p.1.1 p.1.2.1 p.1.2.2) :=
    msd3.comp measurable_fst
  set Fs : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal ((sdn t.1 t.2.1 t.2.2 ^ 2 - c) ^ 2) with hFs
  have mFs : Measurable Fs :=
    ENNReal.measurable_ofReal.comp (((msd3.pow_const 2).sub measurable_const).pow_const 2)
  have hL : ∫⁻ t, Fs t ∂mlpTriple 2 n ≤ ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have mπ : Measurable (fun r : Rest (2 * n) (mW n) n (mA n) (mF n) =>
        (r.1, r.2.1, r.2.2.2)) := by fun_prop
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
        ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
    rw [e0, ← lawR_drop, lintegral_map mFs mπ]
    exact spread_L2_dist2 hn1 hN hmF (by positivity : (0 : ℝ) ≤ 4 / (n : ℝ) * e) hD
  have hV : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ ≤
      ENNReal.ofReal (2 * (4 / (n : ℝ) * e) ^ 2) := by
    have e2 : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ =
        ∫⁻ t, Fs t ∂mlpTriple 2 n := by
      have e3 : ∫⁻ p, ENNReal.ofReal ((sdn p.1.1 p.1.2.1 p.1.2.2 ^ 2 - c) ^ 2) ∂μ =
          ∫⁻ p, Fs p.1 ∂μ := rfl
      rw [e3, hμ, lintegral_prod (fun p => Fs p.1) (mFs.comp measurable_fst).aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
    rw [e2]
    exact hL
  have hX1 : 0 ≤ (X + (k : ℝ)⁻¹) * (4 / (n : ℝ)) := by positivity
  have h := ok_jointE μ
    (G := {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G}) (Z := Z)
    (d := fun p => gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (err := errSAG G k)
    (fun p => sdn_nonneg' _ _ _) msd (measurable_errSAG0 hG hn1 k) (errSAG_nonneg G k)
    (by
      intro p hg _
      have hg' : p.1.1 ∈ goodWAG G := hg
      unfold errSAG
      rw [Set.indicator_of_mem hg'])
    hZ0 hc0 hθ0 hθ1 hX1 (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) h1' hE hV
  have hsubE : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G} ∧ p ∉ Z ∧
      |gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} ⊆ okProgEG G k := by
    rintro p ⟨hg, hz, hok⟩
    have hg' : p.1.1 ∈ goodWAG G := hg
    refine ⟨hg', fun i hi => hz ⟨hg', i, hi⟩, hok⟩
  refine le_trans ?_ (h.trans (measureReal_mono hsubE (measure_ne_top _ _)))
  have t4 := qTerm_le hn
  have hk1 : (0 : ℝ) < (k : ℝ)⁻¹ := by positivity
  have tM : 4 * ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))) / (θ * c) ≤
      4 * xa / (θ * (222757 / 1000000)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ) := by
    have e5 : 4 * ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))) / (θ * c) =
        4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0)) := by
      rw [hc]
      field_simp
    rw [e5]
    have hden : θ * (222757 / 1000000) ≤ θ * (1 - kappa^[6] 0) :=
      mul_le_mul_of_nonneg_left hy hθ0.le
    have hnum : 0 ≤ 4 * (X + (k : ℝ)⁻¹) := by positivity
    calc 4 * (X + (k : ℝ)⁻¹) / (θ * (1 - kappa^[6] 0))
        ≤ 4 * (X + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_left hnum (by positivity) hden
      _ ≤ 4 * (xa * (1 / (n : ℝ)) + (k : ℝ)⁻¹) / (θ * (222757 / 1000000)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by
          field_simp
  have he2 : e ^ 2 ≤ ce ^ 2 / (n : ℝ) := by
    have h1 : e ^ 2 ≤ (ce / √(n : ℝ)) ^ 2 := pow_le_pow_left₀ he hce 2
    rwa [div_pow, Real.sq_sqrt hx0.le] at h1
  have hpS : 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2) ≤
      2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) / (n : ℝ) := by
    have e6 : 2 * (4 / (n : ℝ) * e) ^ 2 / (4 * θ * (1 - θ) * c ^ 2) =
        2 * e ^ 2 / (4 * θ * (1 - θ) * (1 - kappa^[6] 0) ^ 2) := by
      rw [hc]
      field_simp
    rw [e6]
    have hden : 4 * θ * (1 - θ) * (222757 / 1000000 : ℝ) ^ 2 ≤
        4 * θ * (1 - θ) * (1 - kappa^[6] 0) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hy 2) (by positivity)
    calc 2 * e ^ 2 / (4 * θ * (1 - θ) * (1 - kappa^[6] 0) ^ 2)
        ≤ 2 * e ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ 2 * (ce ^ 2 / (n : ℝ)) / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp
  have e1 : (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
      2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2)) / (n : ℝ) =
      1 / 5000 * (1 / (n : ℝ)) + 4 * xa / (θ * (222757 / 1000000)) / (n : ℝ) +
        2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) / (n : ℝ) := by
    field_simp
    ring
  rw [e1]
  linarith




/-- **Two stages for the program.** If the measurable event `okProgEG G k` has joint probability
at least `1 − p`, then for `q > 0`:
`Pr_{W,F}(Pr_{A,γ}(|gProgA − B| ≤ sd/2) > 1 − q) ≥ 1 − p/q`. -/
theorem twoStageProgG0 {n : ℕ} (hn : 1 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    (hG : GoodEv0 n G) {k : ℕ} {p q : ℝ} (hq : 0 < q)
    (hp : 1 - p ≤ ((mlpTriple 2 n).prod (gamK k n)).real (okProgEG G k)) :
    1 - p / q ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
        {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  have mπ : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
      (MlpParam n (mA n) n × (Fin k → Fin n → ℝ)) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) := by
    fun_prop
  have hE := okProgEG_meas hG hn k
  have hE' : MeasurableSet ((fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
      (MlpParam n (mA n) n × (Fin k → Fin n → ℝ)) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) ⁻¹'
        okProgEG G k) := mπ hE
  have hmap : ((lawWF (2 * n) (mW n) n (mF n)).prod
      ((mlpGauss n (mA n) n).prod (gamK k n))).map
      (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
        (MlpParam n (mA n) n × (Fin k → Fin n → ℝ)) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) =
      (mlpTriple 2 n).prod (gamK k n) :=
    map_wfag (mlpGauss (2 * n) (mW n) n) (mlpGauss n (mA n) n) (mlpGauss n (mF n) 1) (gamK k n)
  have hp' : 1 - p ≤ ((lawWF (2 * n) (mW n) n (mF n)).prod
      ((mlpGauss n (mA n) n).prod (gamK k n))).real
      ((fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
        (MlpParam n (mA n) n × (Fin k → Fin n → ℝ)) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) ⁻¹'
          okProgEG G k) := by
    rw [← map_measureReal_apply mπ hE, hmap]
    exact hp
  have h := twoStage (lawWF (2 * n) (mW n) n (mF n))
    ((mlpGauss n (mA n) n).prod (gamK k n)) hE' hq hp'
  refine h.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro x hx
  have hx' : 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
      {y | ((x.1, y.1, x.2), y.2) ∈ okProgEG G k} := hx
  refine lt_of_lt_of_le hx' (measureReal_mono ?_ (measure_ne_top _ _))
  intro y hy
  exact okProgEG_sub G k hy

end BstLean.Part145

open BstLean.Part145 in
#print axioms okProgEG_meas
open BstLean.Part145 in
#print axioms progJointEG0
open BstLean.Part145 in
#print axioms twoStageProgG0
