import BstLean.Part139TwoStage
import BstLean.Part145FinalM

/-!
# Part 145, item 4 (optional): the two-stage form (the order of Option A) for the program

Role: `delegations/statements/p145-spec.md`, item 4; `MM.md`, Option A: "for most `(W, F)`
there is `g_{W,F}` such that for most `A`: `|g_{W,F}(A) − B| ≤ ε·sd`". Here `g_{W,F}(A)` is the
OUTPUT OF THE PROGRAM `arithProg141 k n` (with its `k` Gaussian vectors `γ`), and "most `A`" is
a probability over `A` and `γ`. Parts 139 to 141 have this form only for estimates with an exact
mean over the stand-in (no samples).

* `okProgE k n`: a measurable event inside `okProgA k n`: `W` is in the good event `goodWA n`, no
  point is zero before the normalization, and the sample estimate `gSampleA` is within `sd/2`
  of `B`. On it the program output equals `gSampleA` (`gProgA_eq`).
* `ok_jointE`, `progJointE145`: the joint assembly of `Part145Joint` for the event `okProgE`.
* `map_wfag`: `((W, F), (A, γ)) ↦ ((W, A, F), γ)` keeps the product distribution.
* `twoStageProg145`: from `Pr(okProgE) ≥ 1 − p`:
  `Pr_{W,F}(Pr_{A,γ}(|gProgA − B| ≤ sd/2) > 1 − q) ≥ 1 − p/q` (Markov's inequality).
* **`optA145M`**: every `n ≥ 9216`, `k ≥ 1`, `q > 0`:
  `Pr_{W,F}(Pr_{A,γ}(ok) > 1 − q) ≥ 1 − (0.000775 + 83.22/n + 32.1/k)/q`.
* `optA145M_16`: every `n ≥ 16384`: the same with `66.39/n` (the constants of Part 143 at
  `16384`, the joint assembly).
* **Levels** (`k ≥ 100n`): `optA145M_levels_16`: `(93/100, 93/100)` for every `n ≥ 16384`;
  `optA145M_levels`: `(9/10, 9/10)` for every `n ≥ 9216`.
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
def okProgE (k n : ℕ) : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
    MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ)) :=
  {p | p.1.1 ∈ goodWA n ∧ (∀ i, normSq (preA p.1.1 (p.2 i)) ≠ 0) ∧
    |gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
      sdn p.1.1 p.1.2.1 p.1.2.2 / 2}

lemma okProgE_sub (k n : ℕ) : okProgE k n ⊆ okProgA k n := by
  rintro p ⟨_, hz, hok⟩
  change |gProgA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
    sdn p.1.1 p.1.2.1 p.1.2.2 / 2
  rw [gProgA_eq k p.1.1 p.1.2.1 p.1.2.2 p.2 hz]
  exact hok

lemma okProgE_meas {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : MeasurableSet (okProgE k n) := by
  have hN : 1 ≤ 2 * n := by omega
  have m1 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} :=
    (measurable_fst.comp measurable_fst) (goodWA_meas hn)
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

/-- `ok_joint` for the smaller event "good, not in the null set, and `|d| ≤ sd/2`". -/
lemma ok_jointE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G Z : Set Ω} {d sd err : Ω → ℝ} (hsd : ∀ ω, 0 ≤ sd ω) (msd : Measurable sd)
    (merr : Measurable err) (herr0 : ∀ ω, 0 ≤ err ω)
    (hcov : ∀ ω, ω ∈ G → ω ∉ Z → d ω ^ 2 ≤ err ω) (hZ : μ.real Z = 0)
    {c θ p₁ a v : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (h1 : μ.real Gᶜ ≤ p₁)
    (hE : ∫⁻ ω, ENNReal.ofReal (err ω) ∂μ ≤ ENNReal.ofReal a)
    (hV : ∫⁻ ω, ENNReal.ofReal ((sd ω ^ 2 - c) ^ 2) ∂μ ≤ ENNReal.ofReal v) :
    1 - (p₁ + 4 * a / (θ * c) + v / (4 * θ * (1 - θ) * c ^ 2)) ≤
      μ.real {ω | ω ∈ G ∧ ω ∉ Z ∧ |d ω| ≤ sd ω / 2} := by
  classical
  set d' : Ω → ℝ := fun ω => if ω ∈ G ∧ ω ∉ Z then d ω else sd ω + 1 with hd'
  have h := ok_joint μ (G := G) (Z := Z) (d := d') hsd msd merr herr0
    (by
      intro ω hg hz
      have e : d' ω = d ω := by rw [hd']; simp [hg, hz]
      rw [e]
      exact hcov ω hg hz)
    hZ hc hθ0 hθ1 ha hv h1 hE hV
  refine h.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro ω hω
  have hω' : |d' ω| ≤ sd ω / 2 := hω
  by_cases hgz : ω ∈ G ∧ ω ∉ Z
  · have e : d' ω = d ω := by rw [hd']; simp [hgz]
    rw [e] at hω'
    exact ⟨hgz.1, hgz.2, hω'⟩
  · exfalso
    have e : d' ω = sd ω + 1 := by rw [hd']; simp [hgz]
    rw [e] at hω'
    have h0 := hsd ω
    rw [abs_of_nonneg (by linarith)] at hω'
    linarith

/-- **`progJoint145` for the measurable event `okProgE k n`** (the same hypotheses and the same
bound). -/
theorem progJointE145 {n : ℕ} (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) {p₁ : ℝ} (h1 : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ p₁)
    {X xa : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ xa * (1 / (n : ℝ)))
    (hE : ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((X + (k : ℝ)⁻¹) * (4 / (n : ℝ))))
    {e ce : ℝ} (he : 0 ≤ e) (hce : e ≤ ce / √(n : ℝ))
    (hD : L2le ((lawU2 (2 * n)).prod (lawR (2 * n) (mW n) n (mA n) (mF n)))
      (fun ω : ((Fin (2 * n) → ℝ) × (Fin (2 * n) → ℝ)) × Rest (2 * n) (mW n) n (mA n) (mF n) =>
        kD ω - 4 / (n : ℝ) * (1 - kappa^[6] 0)) (4 / (n : ℝ) * e)) :
    1 - (p₁ + (2 / 10000 + 4 * xa / (θ * (222757 / 1000000)) +
          2 * ce ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2)) / (n : ℝ) +
        4 / (θ * (222757 / 1000000)) / (k : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real (okProgE k n) := by
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
    {p | p.1.1 ∈ goodWA n ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have hZ0 : μ.real Z = 0 := by
    rw [measureReal_def, zeroPtA_null hn k]
    rfl
  have h1' : μ.real
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}ᶜ ≤ p₁ + 68000000 / (qA n : ℝ) ^ 2 :=
    (prod_fst_real (mlpTriple 2 n) (gamK k n) {t | t.1 ∉ goodWA n}).trans_le
      (badA_prob_gen hn h1)
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
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n}) (Z := Z)
    (d := fun p => gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2)
    (sd := fun p => sdn p.1.1 p.1.2.1 p.1.2.2) (err := errSA k n)
    (fun p => sdn_nonneg' _ _ _) msd (measurable_errSA hn1 k) (errSA_nonneg k n)
    (by
      intro p hg _
      have hg' : p.1.1 ∈ goodWA n := hg
      unfold errSA
      rw [Set.indicator_of_mem hg'])
    hZ0 hc0 hθ0 hθ1 hX1 (by positivity : (0 : ℝ) ≤ 2 * (4 / (n : ℝ) * e) ^ 2) h1' hE hV
  have hsubE : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ) | p ∈ {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWA n} ∧ p ∉ Z ∧
      |gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 - Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤
        sdn p.1.1 p.1.2.1 p.1.2.2 / 2} ⊆ okProgE k n := by
    rintro p ⟨hg, hz, hok⟩
    have hg' : p.1.1 ∈ goodWA n := hg
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


section maps

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ] (μ : Measure α) (ν : Measure β) (τ : Measure γ) (Γ : Measure δ)
  [SFinite μ] [SFinite ν] [SFinite τ] [SFinite Γ]

/-- `((w, f), (a, g)) ↦ ((w, (a, f)), g)` maps `(μ ⊗ τ) ⊗ (ν ⊗ Γ)` to `(μ ⊗ (ν ⊗ τ)) ⊗ Γ`. -/
lemma map_wfag :
    ((μ.prod τ).prod (ν.prod Γ)).map
        (fun p : (α × γ) × (β × δ) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) =
      (μ.prod (ν.prod τ)).prod Γ := by
  have h1 : (((μ.prod τ).prod ν).prod Γ).map MeasurableEquiv.prodAssoc =
      (μ.prod τ).prod (ν.prod Γ) := Measure.prodAssoc_prod
  have h2 := Measure.map_prod_map ((μ.prod τ).prod ν) Γ
    (f := fun p : (α × γ) × β => (p.1.1, (p.2, p.1.2))) (g := id) (by fun_prop) measurable_id
  rw [Measure.map_id, map_wfa μ ν τ] at h2
  rw [h2, ← h1, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
  have h3 : ((fun p : (α × γ) × (β × δ) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) ∘
      (MeasurableEquiv.prodAssoc : ((α × γ) × β) × δ ≃ᵐ (α × γ) × (β × δ))) =
      Prod.map (fun p : (α × γ) × β => (p.1.1, (p.2, p.1.2))) id := by
    funext p
    rfl
  rw [h3]

end maps

/-- **Two stages for the program.** If the measurable event `okProgE k n` has joint probability
at least `1 − p`, then for `q > 0`:
`Pr_{W,F}(Pr_{A,γ}(|gProgA − B| ≤ sd/2) > 1 − q) ≥ 1 − p/q`. -/
theorem twoStageProg145 {n : ℕ} (hn : 1 ≤ n) {k : ℕ} {p q : ℝ} (hq : 0 < q)
    (hp : 1 - p ≤ ((mlpTriple 2 n).prod (gamK k n)).real (okProgE k n)) :
    1 - p / q ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
        {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  have mπ : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
      (MlpParam n (mA n) n × (Fin k → Fin n → ℝ)) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) := by
    fun_prop
  have hE := okProgE_meas hn k
  have hE' : MeasurableSet ((fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
      (MlpParam n (mA n) n × (Fin k → Fin n → ℝ)) => ((p.1.1, (p.2.1, p.1.2)), p.2.2)) ⁻¹'
        okProgE k n) := mπ hE
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
          okProgE k n) := by
    rw [← map_measureReal_apply mπ hE, hmap]
    exact hp
  have h := twoStage (lawWF (2 * n) (mW n) n (mF n))
    ((mlpGauss n (mA n) n).prod (gamK k n)) hE' hq hp'
  refine h.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro x hx
  have hx' : 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
      {y | ((x.1, y.1, x.2), y.2) ∈ okProgE k n} := hx
  refine lt_of_lt_of_le hx' (measureReal_mono ?_ (measure_ne_top _ _))
  intro y hy
  exact okProgE_sub k n hy

/-- **Item 4 (`optA145M`): the two-stage form for the program, every `n ≥ 9216`.** For `k ≥ 1`
and `q > 0`:
`Pr_{W,F}(Pr_{A,γ}(|gProgA − B| ≤ sd/2) > 1 − q) ≥ 1 − (0.000775 + 83.22/n + 32.1/k)/q`. -/
theorem optA145M {n : ℕ} (hn : 9216 ≤ n) {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : 0 < q) :
    1 - (775 / 1000000 + 8322 / 100 / (n : ℝ) + 321 / 10 / (k : ℝ)) / q ≤
      (lawWF (2 * n) (mW n) n (mF n)).real
        {x | 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
          {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  refine twoStageProg145 (by omega) hq ?_
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hG : (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤
      775 / 1000000 + 1959 / 100 / (n : ℝ) := by
    have h := goodHat_compl145M hn
    unfold cExtra145M at h
    exact h
  have h := progJointE145 hn4 hk (θ := 14 / 25) (by norm_num) (by norm_num) hG
    (XAL_nonneg hn4 L145M_nonneg (1 / 20) (η := 1 / 19) (by norm_num) (η' := 1 / 39)
      (by norm_num))
    (XAL145_M hn)
    (errSampleA145M_lint hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)
    (eD143_nonneg n) (eD145_M hn) (kernDist143 hn4)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 4 * (444 / 1000) / (14 / 25 * (222757 / 1000000 : ℝ)) +
      2 * (10989 / 10000 : ℝ) ^ 2 / (4 * (14 / 25) * (1 - 14 / 25) * (222757 / 1000000) ^ 2)) /
        (n : ℝ) ≤ 6363 / 100 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (14 / 25 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 321 / 10 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (8322 : ℝ) / 100 / n = 1959 / 100 / n + 6363 / 100 / n := by ring
  rw [e3]
  linarith

/-- The two-stage form with the constants of Part 143 at `16384`: every `n ≥ 16384`, `k ≥ 1`,
`q > 0`: `Pr_{W,F}(Pr_{A,γ}(ok) > 1 − q) ≥ 1 − (0.000775 + 66.39/n + 32.1/k)/q`. -/
theorem optA145M_16 {n : ℕ} (hn : 16384 ≤ n) {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : 0 < q) :
    1 - (775 / 1000000 + 6639 / 100 / (n : ℝ) + 321 / 10 / (k : ℝ)) / q ≤
      (lawWF (2 * n) (mW n) n (mF n)).real
        {x | 1 - q < ((mlpGauss n (mA n) n).prod (gamK k n)).real
          {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  refine twoStageProg145 (by omega) hq ?_
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := progJointE145 hn4 hk (θ := 14 / 25) (by norm_num) (by norm_num)
    (goodHat_compl143f hn)
    (XAL_nonneg hn4 L143_nonneg (1 / 20) (η := 1 / 28) (by norm_num) (η' := 1 / 36)
      (by norm_num))
    (XAL143_16 hn)
    (errSampleA143_lint hn (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk)
    (eD143_nonneg n) (eD143_16 hn) (kernDist143 hn4)
  refine le_trans ?_ h
  have e1 : (2 / 10000 + 4 * (3815 / 10000) / (14 / 25 * (222757 / 1000000 : ℝ)) +
      2 * (9903 / 10000 : ℝ) ^ 2 / (4 * (14 / 25) * (1 - 14 / 25) * (222757 / 1000000) ^ 2)) /
        (n : ℝ) ≤ 5235 / 100 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hx0.le
    norm_num
  have e2 : 4 / (14 / 25 * (222757 / 1000000 : ℝ)) / (k : ℝ) ≤ 321 / 10 / (k : ℝ) := by
    apply div_le_div_of_nonneg_right _ hk0.le
    norm_num
  have e3 : (6639 : ℝ) / 100 / n = 1404 / 100 / n + 5235 / 100 / n := by ring
  rw [e3]
  linarith

/-- **Levels `(93/100, 93/100)` for every `n ≥ 16384`, `k ≥ 100n`**: with probability at least
`93/100` over `(W, F)`, the program succeeds with probability above `93/100` over `A` and `γ`. -/
theorem optA145M_levels_16 {n : ℕ} (hn : 16384 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    93 / 100 ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 93 / 100 < ((mlpGauss n (mA n) n).prod (gamK k n)).real
        {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have h := optA145M_16 hn (k := k) (by omega) (q := 7 / 100) (by norm_num)
  have e : (1 : ℝ) - 7 / 100 = 93 / 100 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  have a1 : (6639 : ℝ) / 100 / n ≤ 6639 / 100 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (321 : ℝ) / 10 / k ≤ 321 / 10 / (100 * 16384) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have : (775 / 1000000 + 6639 / 100 / (n : ℝ) + 321 / 10 / (k : ℝ)) / (7 / 100) ≤ 7 / 100 := by
    rw [div_le_iff₀ (by norm_num)]
    norm_num at a1 a2 ⊢
    linarith
  linarith

/-- **Levels `(9/10, 9/10)` for every `n ≥ 9216`, `k ≥ 100n`.** -/
theorem optA145M_levels {n : ℕ} (hn : 9216 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    9 / 10 ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 9 / 10 < ((mlpGauss n (mA n) n).prod (gamK k n)).real
        {y | ((x.1, y.1, x.2), y.2) ∈ okProgA k n}} := by
  have hx : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (100 : ℝ) * n ≤ k := by exact_mod_cast hk
  have h := optA145M hn (k := k) (by omega) (q := 1 / 10) (by norm_num)
  have e : (1 : ℝ) - 1 / 10 = 9 / 10 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  have a1 : (8322 : ℝ) / 100 / n ≤ 8322 / 100 / 9216 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have a2 : (321 : ℝ) / 10 / k ≤ 321 / 10 / (100 * 9216) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have : (775 / 1000000 + 8322 / 100 / (n : ℝ) + 321 / 10 / (k : ℝ)) / (1 / 10) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by norm_num)]
    norm_num at a1 a2 ⊢
    linarith
  linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms okProgE_meas
open BstLean.Part145 in
#print axioms progJointE145
open BstLean.Part145 in
#print axioms map_wfag
open BstLean.Part145 in
#print axioms twoStageProg145
open BstLean.Part145 in
#print axioms optA145M
open BstLean.Part145 in
#print axioms optA145M_16
open BstLean.Part145 in
#print axioms optA145M_levels_16
open BstLean.Part145 in
#print axioms optA145M_levels
