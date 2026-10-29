import BstLean.Part167All

/-!
# Part 168 (file `Pol`): the polar step for the rows of `A₁` in the frame (sub-lemma 5)

No proof is left open; no `native_decide` or `axiom` is used.

Each row of `A₁` is written in the frame as `W_i = (z_i, t_i, Γ_i)` with distribution
`ν = N(0,1) ⊗ N(0,1) ⊗ N(0, I_d)` (Part 167, `gaussMat_frame`). Write `Γ_i = |G'_i|·G_i/|G_i|` with
`G_i, G'_i` independent standard Gaussian vectors (Part 162, `polar_swap_map`).

* **`pi_prod_le`**: `∫ f d(μ⊗ν)^{⊗m} ≤ ∫∫ f(a,b) dν^{⊗m} dμ^{⊗m}` (no measurability needed).
* **`rows_pol_le`**: `∫ F dν^{⊗m} ≤ ∫_Z ∫_T ∫_{G'} ∫_G F(Z, T, |G'|·G/|G|)`.
* **`polar_core`**: if a coefficient vector `κ(W)` depends on `W` only through
  `(z_i, t_i, |Γ_i|²)` and `|κ(W)|² ≤ B`, then
  `E|Σ_i κ_i(W) Γ_i|^{128} ≤ ((d+128)/(d−1))^{64} · B^{64} · m^{1/q}(d + 128q)^{64}`.
  This is the paper's `r^{sph}` (uniform directions given `𝓕_x`) and `M_ℓ` (maximum row length).
-/

namespace BstLean.Part168

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part162 (radF_sq radF_nonneg radF_unitF radF_unitF_le polar_swap_map
  dirsum_le_sqrt radF_sum_le integrable_radF_pow)
open BstLean.Part167 (Mx max_mom Mx_nonneg measurable_Mx)

variable {m d : ℕ}

/-- **Product of rows ≤ iterated integral** (Tonelli inequality, no measurability). -/
lemma pi_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν] (f : (Fin m → α × β) → ℝ≥0∞) :
    ∫⁻ x, f x ∂Measure.pi (fun _ : Fin m => μ.prod ν) ≤
      ∫⁻ a, ∫⁻ b, f (fun i => (a i, b i)) ∂Measure.pi (fun _ : Fin m => ν)
        ∂Measure.pi (fun _ : Fin m => μ) := by
  have he := measurePreserving_arrowProdEquivProdArrow α β (Fin m) (fun _ => μ) (fun _ => ν)
  have hs := MeasurePreserving.symm _ he
  rw [← hs.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  exact lintegral_prod_le _

/-- The polar row map `(z, t, g', g) ↦ (z, t, |g'|·g/|g|)`. -/
noncomputable def rowPol : ℝ × ℝ × (Fin d → ℝ) × (Fin d → ℝ) → ℝ × ℝ × (Fin d → ℝ) :=
  fun p => (p.1, p.2.1, radF53 p.2.2.1 • unitF53 p.2.2.2)

lemma measurable_phi : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
    radF53 p.1 • unitF53 p.2) :=
  (measurable_radF.comp measurable_fst).smul (measurable_unitF.comp measurable_snd)

lemma measurable_rowPol : Measurable (rowPol (d := d)) := by
  unfold rowPol
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_phi.comp (measurable_snd.comp measurable_snd)))

/-- `polar_swap_map` with the radius first. -/
lemma polar_swap' : ((stdGauss (Fin d)).prod (stdGauss (Fin d))).map
    (fun p : (Fin d → ℝ) × (Fin d → ℝ) => radF53 p.1 • unitF53 p.2) = stdGauss (Fin d) := by
  have hsw : ((stdGauss (Fin d)).prod (stdGauss (Fin d))).map Prod.swap =
      (stdGauss (Fin d)).prod (stdGauss (Fin d)) := Measure.prod_swap
  conv_rhs => rw [← polar_swap_map (d := d), ← hsw]
  rw [Measure.map_map (by
    exact (measurable_radF.comp measurable_snd).smul (measurable_unitF.comp measurable_fst))
    measurable_swap]
  rfl

/-- **One row in polar form.** -/
lemma rowPol_map : ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod
      ((stdGauss (Fin d)).prod (stdGauss (Fin d))))).map rowPol =
    (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin d))) := by
  conv_rhs => rw [← polar_swap' (d := d), ← Measure.map_id (μ := gaussianReal 0 1)]
  rw [Measure.map_prod_map _ _ measurable_id measurable_phi,
    Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap measurable_phi)]
  rfl

/-- **The rows in polar form, as an upper bound for any integrand.** -/
lemma rows_pol_le (F : (Fin m → ℝ × ℝ × (Fin d → ℝ)) → ℝ≥0∞) :
    ∫⁻ W, F W ∂Measure.pi (fun _ : Fin m =>
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin d)))) ≤
    ∫⁻ Z, ∫⁻ T, ∫⁻ G', ∫⁻ G, F (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i)))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
      ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
      ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1) := by
  rw [← rowPol_map (d := d)]
  rw [← Measure.pi_map_pi (fun _ => measurable_rowPol.aemeasurable)]
  refine (lintegral_map_le _ (measurable_pi_iff.mpr fun i =>
    measurable_rowPol.comp (measurable_pi_apply i)).aemeasurable).trans ?_
  refine (pi_prod_le _ _ _).trans (lintegral_mono fun Z => ?_)
  refine (pi_prod_le _ _ _).trans (lintegral_mono fun T => ?_)
  refine (pi_prod_le _ _ _).trans (lintegral_mono fun G' => le_of_eq ?_)
  rfl

/-- A standard Gaussian vector in dimension `d ≥ 1` is almost surely not `0`. -/
lemma stdGauss_zero (hd : 1 ≤ d) : stdGauss (Fin d) {0} = 0 := by
  classical
  have hw : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, by omega⟩
    simp at this
  have h := BstLean.Part167.lin_ne_zero_ae (ι := Fin d) hw
  rw [ae_iff] at h
  refine measure_mono_null (fun ξ (hξ : ξ = 0) => ?_) h
  simp [hξ]

lemma ae_all_ne (hd : 1 ≤ d) :
    ∀ᵐ G ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)), ∀ i, G i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have := Measure.pi_eval_preimage_null (fun _ : Fin m => stdGauss (Fin d)) (i := i)
    (stdGauss_zero hd)
  rw [ae_iff]
  simpa [Set.preimage, not_not] using this

lemma normSq_eq_radF (v : Fin d → ℝ) : normSq v = radF53 v ^ 2 := (radF_sq v).symm

lemma normSq_smul (r : ℝ) (v : Fin d → ℝ) : normSq (r • v) = r ^ 2 * normSq v := by
  unfold normSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- The Gaussian chi moment in Bochner form: `E|g|^{128} ≤ (d + 128)^{64}`. -/
lemma radF128_le (hd : 1 ≤ d) :
    ∫ g, radF53 g ^ 128 ∂stdGauss (Fin d) ≤ ((d : ℝ) + 128) ^ 64 := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hI := integrable_radF_pow (d := d) 128
  have hc := BstLean.Part166.chi_mom (ι := Fin d) 64
  have e : ∀ g : Fin d → ℝ, radF53 g ^ 128 = (∑ i, g i ^ 2) ^ 64 := fun g => by
    rw [show (128 : ℕ) = 2 * 64 from rfl, pow_mul, radF_sq]
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun g => by positivity)]
  simp_rw [e]
  refine hc.trans (le_of_eq ?_)
  simp only [Fintype.card_fin]
  norm_num

/-- **The polar step.** -/
theorem polar_core (hm : 0 < m) (hd : 2 ≤ d) {q : ℕ} (hq : 1 ≤ q)
    (κ : (Fin m → ℝ × ℝ × (Fin d → ℝ)) → Fin m → ℝ)
    (hκ : ∀ W W' : Fin m → ℝ × ℝ × (Fin d → ℝ), (∀ i, (W i).1 = (W' i).1 ∧
      (W i).2.1 = (W' i).2.1 ∧ normSq (W i).2.2 = normSq (W' i).2.2) → κ W = κ W')
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ W, normSq (κ W) ≤ B) :
    ∫⁻ W, ENNReal.ofReal (normSq (∑ i, κ W i • (W i).2.2) ^ 64) ∂Measure.pi (fun _ : Fin m =>
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (stdGauss (Fin d)))) ≤
      ENNReal.ofReal (((d : ℝ) + 128) ^ 64 / ((d : ℝ) - 1) ^ 64 * B ^ 64 *
        ((m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 128 * q) ^ 64)) := by
  have hd1 : 1 ≤ d := by omega
  have hNe : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set K : ℝ := ((d : ℝ) + 128) ^ 64 / ((d : ℝ) - 1) ^ 64 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; apply div_nonneg <;> apply pow_nonneg <;> linarith
  refine (rows_pol_le _).trans ?_
  -- the inner bound
  have hin : ∀ (Z T : Fin m → ℝ) (G' : Fin m → Fin d → ℝ),
      ∫⁻ G, ENNReal.ofReal (normSq (∑ i, κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i •
        ((fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i).2.2) ^ 64)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      ENNReal.ofReal (K * B ^ 64) * ENNReal.ofReal (Mx hm G' ^ 128) := by
    intro Z T G'
    set e : Fin d → ℝ := unitF53 (fun _ => (1 : ℝ)) with he
    have hne1 : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    have hen : normSq e = 1 := by rw [normSq_eq_radF, he, radF_unitF hne1]; norm_num
    set W0 : Fin m → ℝ × ℝ × (Fin d → ℝ) := fun i => (Z i, T i, radF53 (G' i) • e)
    set κ0 := κ W0
    set c : Fin m → ℝ := fun i => κ0 i * radF53 (G' i) with hc
    have hae : ∀ᵐ G ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)),
        ENNReal.ofReal (normSq (∑ i, κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i •
          ((fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) i).2.2) ^ 64) =
        ENNReal.ofReal (radF53 (∑ i, c i • unitF53 (G i)) ^ 128) := by
      filter_upwards [ae_all_ne (m := m) hd1] with G hG
      have hk : κ (fun i => (Z i, T i, radF53 (G' i) • unitF53 (G i))) = κ0 := by
        refine hκ _ _ fun i => ⟨rfl, rfl, ?_⟩
        simp only [W0]
        rw [normSq_smul, normSq_smul, hen, normSq_eq_radF (unitF53 (G i)), radF_unitF (hG i)]
        ring
      rw [hk]
      have hs : ∑ i, κ0 i • (radF53 (G' i) • unitF53 (G i)) = ∑ i, c i • unitF53 (G i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
      have e2 : normSq (∑ i, κ0 i • (radF53 (G' i) • unitF53 (G i))) ^ 64 =
          radF53 (∑ i, c i • unitF53 (G i)) ^ 128 := by
        rw [hs, normSq_eq_radF, ← pow_mul]
      exact congrArg ENNReal.ofReal e2
    rw [lintegral_congr_ae hae]
    -- integrability
    have hmeas : Measurable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • unitF53 (G i)) ^ 128) :=
      (measurable_radF.comp (Finset.measurable_sum _ fun i _ =>
        (measurable_unitF.comp (measurable_pi_apply i)).const_smul (c i))).pow_const 128
    have hbd : ∀ G : Fin m → Fin d → ℝ, radF53 (∑ i, c i • unitF53 (G i)) ^ 128 ≤
        (∑ i, |c i|) ^ 128 := by
      intro G
      refine pow_le_pow_left₀ (radF_nonneg _) ((radF_sum_le c _).trans ?_) 128
      refine Finset.sum_le_sum fun i _ => ?_
      have := radF_unitF_le (G i)
      have := abs_nonneg (c i)
      nlinarith
    have hI : Integrable (fun G : Fin m → Fin d → ℝ => radF53 (∑ i, c i • unitF53 (G i)) ^ 128)
        (Measure.pi (fun _ : Fin m => stdGauss (Fin d))) := by
      refine (integrable_const ((∑ i, |c i|) ^ 128)).mono' hmeas.aestronglyMeasurable
        (ae_of_all _ fun G => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (radF_nonneg _) _)]
      exact hbd G
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun G => pow_nonneg (radF_nonneg _) _),
      ← ENNReal.ofReal_mul (mul_nonneg hK0 (pow_nonneg hB0 _))]
    refine ENNReal.ofReal_le_ofReal ((dirsum_le_sqrt (by omega) hd c (by norm_num)).trans ?_)
    -- constants
    have hsq : √((d : ℝ) - 1) ^ 128 = ((d : ℝ) - 1) ^ 64 := by
      rw [show (128 : ℕ) = 2 * 64 from rfl, pow_mul, Real.sq_sqrt (by linarith)]
    rw [hsq]
    have hR := radF128_le hd1
    have hcM : radF53 c ^ 2 ≤ Mx hm G' ^ 2 * B := by
      rw [radF_sq]
      have h1 : ∀ i, c i ^ 2 ≤ Mx hm G' ^ 2 * κ0 i ^ 2 := by
        intro i
        have hr : radF53 (G' i) ≤ Mx hm G' :=
          Finset.le_sup' (fun i => radF53 (G' i)) (Finset.mem_univ i)
        have hr0 := radF_nonneg (G' i)
        simp only [hc, mul_pow]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 hr 2) (sq_nonneg _)
      calc ∑ i, c i ^ 2 ≤ ∑ i, Mx hm G' ^ 2 * κ0 i ^ 2 := Finset.sum_le_sum fun i _ => h1 i
        _ = Mx hm G' ^ 2 * normSq κ0 := by rw [← Finset.mul_sum]; rfl
        _ ≤ Mx hm G' ^ 2 * B := mul_le_mul_of_nonneg_left (hB W0) (sq_nonneg _)
    have hc128 : radF53 c ^ 128 ≤ B ^ 64 * Mx hm G' ^ 128 := by
      have := pow_le_pow_left₀ (sq_nonneg _) hcM 64
      calc radF53 c ^ 128 = (radF53 c ^ 2) ^ 64 := by rw [← pow_mul]
        _ ≤ (Mx hm G' ^ 2 * B) ^ 64 := this
        _ = B ^ 64 * Mx hm G' ^ 128 := by rw [mul_pow, ← pow_mul]; ring
    have hd1R : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    calc (∫ g, radF53 g ^ 128 ∂stdGauss (Fin d)) / ((d : ℝ) - 1) ^ 64 * radF53 c ^ 128
        ≤ ((d : ℝ) + 128) ^ 64 / ((d : ℝ) - 1) ^ 64 * (B ^ 64 * Mx hm G' ^ 128) := by
          exact mul_le_mul (div_le_div_of_nonneg_right hR (pow_nonneg hd1R.le _)) hc128
            (pow_nonneg (radF_nonneg c) _) hK0
      _ = K * B ^ 64 * Mx hm G' ^ 128 := by rw [hK]; ring
  -- integrate out
  set Mm : ℝ := (m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 128 * q) ^ 64
  have hG' : ∫⁻ G', ENNReal.ofReal (K * B ^ 64) * ENNReal.ofReal (Mx hm G' ^ 128)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤ ENNReal.ofReal (K * B ^ 64 * Mm) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul (mul_nonneg hK0 (pow_nonneg hB0 _))]
    exact mul_le_mul_right (max_mom hm hq) _
  calc _ ≤ ∫⁻ Z, ∫⁻ T, ENNReal.ofReal (K * B ^ 64 * Mm)
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)
        ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1) :=
        lintegral_mono fun Z => lintegral_mono fun T =>
          (lintegral_mono fun G' => hin Z T G').trans hG'
    _ = ENNReal.ofReal (K * B ^ 64 * Mm) := by simp
end BstLean.Part168
