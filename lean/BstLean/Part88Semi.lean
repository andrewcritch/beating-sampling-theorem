import BstLean.Part88Defs
import BstLean.Part84Remez
import BstLean.Part84Tail

/-!
# Part 88, the sphere step (`SemiStep`)

Semicircle average over the scale, the Christoffel bound (`ChrisIface`), polar independence
(Part 53), then Markov and Chebyshev.
-/

namespace BstLean.Part88

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part78 (Good good_coord markov_gt)
open BstLean.Part81 (WIdx)
open BstLean.Part84

/-! ## Elementary facts -/

private lemma ofReal_integral_le' {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ENNReal.ofReal (∫ x, g x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
  by_cases hi : Integrable g ν
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hg)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le

lemma Sodd_nonneg (D : ℕ) : 0 ≤ Sodd D := by
  unfold Sodd
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

lemma SS_ge_one (D : ℕ) (ξ : ℝ) : 1 ≤ SS D ξ := by
  unfold SS
  have h1 : (0 : ℝ) ≤ ((D / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 := mul_nonneg (sq_nonneg ξ) (Sodd_nonneg D)
  nlinarith

lemma SS_mono (D : ℕ) {x ξ : ℝ} (h : |x| ≤ ξ) : SS D x ≤ SS D ξ := by
  unfold SS
  have h2 : x ^ 2 ≤ ξ ^ 2 := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)
  have h3 := mul_le_mul_of_nonneg_right h2 (Sodd_nonneg D)
  nlinarith

lemma young (a b θ : ℝ) (hθ : 0 < θ) :
    (a + b) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + 1 / θ) * b ^ 2 := by
  have hu : 0 < 1 / θ := by positivity
  have hθu : θ * (1 / θ) = 1 := by field_simp
  have h := mul_nonneg hu.le (sq_nonneg (θ * a - b))
  have e : 1 / θ * (θ * a - b) ^ 2 =
      θ * a ^ 2 * (θ * (1 / θ)) - 2 * a * b * (θ * (1 / θ)) + 1 / θ * b ^ 2 := by ring
  rw [e, hθu] at h
  nlinarith

lemma u_bounds (β c : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hc2 : -1 ≤ c) (hc1 : c ≤ 1) :
    (1 - β) ^ 2 ≤ (1 + β * c) ^ 2 ∧ (1 + β * c) ^ 2 ≤ (1 + β) ^ 2 := by
  constructor
  · have h := mul_nonneg (mul_nonneg hβ.le (by linarith : (0 : ℝ) ≤ 1 + c))
      (by nlinarith : (0 : ℝ) ≤ 2 - β * (1 - c))
    nlinarith
  · have h := mul_nonneg (mul_nonneg hβ.le (by linarith : (0 : ℝ) ≤ 1 - c))
      (by nlinarith : (0 : ℝ) ≤ 2 + β * (1 + c))
    nlinarith

/-- Chebyshev for the radius ratio. -/
lemma rad_tail (ι : Type) [Fintype ι] (hN : 0 < Fintype.card ι) (η : ℝ) (hη : 0 < η) :
    stdGauss ι {Z : ι → ℝ | η < |(radF53 Z / Real.sqrt (Fintype.card ι)) ^ 2 - 1|} ≤
      ENNReal.ofReal (2 / ((Fintype.card ι : ℝ) * η ^ 2)) := by
  have hN' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hq : Good (stdGauss ι) (fun Z : ι → ℝ => ∑ i, Z i ^ 2) :=
    Good.sum _ fun α _ => (good_coord α).pow 2
  have hg : Good (stdGauss ι)
      (fun Z : ι → ℝ => ((∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)) ^ 2) :=
    (hq.sub (Good.const _)).pow 2
  have hm := markov_gt (μ := stdGauss ι) (fun Z => sq_nonneg _) hg.integrable
    (t := ((Fintype.card ι : ℝ) * η) ^ 2) (by positivity) (chi_sq_var ι).le
  have he : 2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) * η) ^ 2 =
      2 / ((Fintype.card ι : ℝ) * η ^ 2) := by field_simp
  rw [he] at hm
  refine le_trans (measure_mono ?_) hm
  intro Z hZ
  simp only [Set.mem_ofPred_eq] at hZ ⊢
  have hs : (radF53 Z / Real.sqrt (Fintype.card ι)) ^ 2 - 1 =
      ((∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)) / (Fintype.card ι : ℝ) := by
    unfold radF53
    rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Real.sq_sqrt hN'.le]
    field_simp
  rw [hs, abs_div, abs_of_pos hN', lt_div_iff₀ hN'] at hZ
  have h : |(Fintype.card ι : ℝ) * η| < |(∑ i, Z i ^ 2) - (Fintype.card ι : ℝ)| := by
    rw [abs_of_pos (by positivity)]; linarith
  exact sq_lt_sq.mpr h

/-! ## Step A: the generic transfer -/

set_option maxHeartbeats 1600000 in
lemma semi_transfer {ι : Type} [Fintype ι] (hN : 0 < Fintype.card ι) (H : ℝ → (ι → ℝ) → ℝ)
    (D : ℕ) (hC : ChrisIface D)
    (hscal : ∀ (s t : ℝ) (W : ι → ℝ), H s (t • W) = H (s * t) W)
    (hpoly : ∀ W : ι → ℝ, ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧ ∀ s : ℝ, q.eval s = H s W)
    (hmeas : ∀ s : ℝ, Measurable (H s))
    (lam β ξ Bd : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) (hξ2 : ξ ≤ 1 / 2) (hξβ : ξ * β ≤ 1 / 100)
    (hν : 2 / ((Fintype.card ι : ℝ) * (19 / 10 * ξ * β) ^ 2) < 1)
    (hint : ∀ θ : ℝ,
      Integrable (fun W : ι → ℝ => H (lam * (1 + β * Real.cos θ)) W ^ 2) (stdGauss ι) ∧
      ∫ W : ι → ℝ, H (lam * (1 + β * Real.cos θ)) W ^ 2 ∂stdGauss ι ≤ Bd) :
    ∫⁻ W, ENNReal.ofReal (H lam (Real.sqrt (Fintype.card ι) • unitF53 W) ^ 2) ∂stdGauss ι ≤
      ENNReal.ofReal (SS D ξ * Bd /
        ((1 - ξ ^ 2) * (1 - 2 / ((Fintype.card ι : ℝ) * (19 / 10 * ξ * β) ^ 2)))) := by
  classical
  have hN' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set sN : ℝ := Real.sqrt N with hsNdef
  have hsN : 0 < sN := Real.sqrt_pos.mpr hN'
  have hηpos : 0 < 19 / 10 * ξ * β := by positivity
  set η : ℝ := 19 / 10 * ξ * β with hηdef
  set ν : ℝ := 2 / (N * η ^ 2) with hνdef
  have hν0 : 0 ≤ ν := by positivity
  have hξsq : 0 < 1 - ξ ^ 2 := by nlinarith
  have hSS0 : 0 ≤ SS D ξ := le_trans zero_le_one (SS_ge_one D ξ)
  have hβne : β ≠ 0 := hβ.ne'
  have hcont : ∀ W : ι → ℝ, Continuous fun s => H s W := by
    intro W
    obtain ⟨q, -, hq⟩ := hpoly W
    have : (fun s => H s W) = fun s => q.eval s := funext fun s => (hq s).symm
    rw [this]
    exact q.continuous
  have hHm : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  obtain ⟨lt, hlt⟩ : ∃ lt : ℝ → ℝ, lt = fun θ => lam * (1 + β * Real.cos θ) := ⟨_, rfl⟩
  have hlta : ∀ θ, lt θ = lam * (1 + β * Real.cos θ) := fun θ => by rw [hlt]
  have hltm : Measurable lt := by
    rw [hlt]
    exact (continuous_const.mul (continuous_const.add
      (continuous_const.mul Real.continuous_cos))).measurable
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → (ι → ℝ) → ℝ≥0∞,
    Φ = fun θ V => ENNReal.ofReal (H (lt θ) V ^ 2 * Real.sin θ ^ 2) := ⟨_, rfl⟩
  have hΦa : ∀ θ V, Φ θ V = ENNReal.ofReal (H (lt θ) V ^ 2 * Real.sin θ ^ 2) :=
    fun θ V => by rw [hΦ]
  have hΦm : Measurable (fun p : ℝ × (ι → ℝ) => Φ p.1 p.2) := by
    have h1 : Measurable (fun p : ℝ × (ι → ℝ) => H (lt p.1) p.2) :=
      hHm.comp ((hltm.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable (fun p : ℝ × (ι → ℝ) => H (lt p.1) p.2 ^ 2 * Real.sin p.1 ^ 2) :=
      (h1.pow_const 2).mul ((Real.continuous_sin.measurable.comp measurable_fst).pow_const 2)
    simp only [hΦa]
    exact h2.ennreal_ofReal
  obtain ⟨F, hF⟩ : ∃ F : (ι → ℝ) → ℝ → ℝ≥0∞,
    F = fun ω ρ => ∫⁻ θ in Set.Ioc (0 : ℝ) Real.pi, Φ θ (ρ • ω) := ⟨_, rfl⟩
  have hFa : ∀ ω ρ, F ω ρ = ∫⁻ θ in Set.Ioc (0 : ℝ) Real.pi, Φ θ (ρ • ω) :=
    fun ω ρ => by rw [hF]
  have hFm : Measurable (Function.uncurry F) := by
    have h3 : Measurable (fun q : ((ι → ℝ) × ℝ) × ℝ => Φ q.2 (q.1.2 • q.1.1)) :=
      hΦm.comp (measurable_snd.prodMk
        ((measurable_snd.comp measurable_fst).smul (measurable_fst.comp measurable_fst)))
    have h4 := h3.lintegral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) Real.pi))
    have e : Function.uncurry F = fun x : (ι → ℝ) × ℝ =>
        ∫⁻ y in Set.Ioc (0 : ℝ) Real.pi, Φ y (x.2 • x.1) := by
      funext x; obtain ⟨a, b⟩ := x; simp only [Function.uncurry_apply_pair, hFa]
    rw [e]; exact h4
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = ENNReal.ofReal (SS D ξ * (2 / Real.pi)) := ⟨_, rfl⟩
  have hKtop : K ≠ ⊤ := by rw [hK]; exact ENNReal.ofReal_ne_top
  -- the pointwise Christoffel step
  have hkey : ∀ (ω W' : ι → ℝ), |(radF53 W' / sN) ^ 2 - 1| ≤ η →
      ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (H lam (sN • ω) ^ 2) ≤
        K * F ω (radF53 W') := by
    intro ω W' hg
    have hr0 : 0 ≤ radF53 W' / sN := div_nonneg (Real.sqrt_nonneg _) hsN.le
    set r : ℝ := radF53 W' / sN with hr
    obtain ⟨h1, h2⟩ := abs_le.mp hg
    have hη' : η ≤ 19 / 1000 := by rw [hηdef]; nlinarith
    have hr99 : 99 / 100 ≤ r := by
      by_contra h
      have h' : r < 99 / 100 := not_le.mp h
      nlinarith
    have hrpos : 0 < r := by linarith
    have hrne : r ≠ 0 := hrpos.ne'
    have hrr : 19 / 10 ≤ r * (1 + r) := by nlinarith
    have he0 : 0 ≤ ξ * β := by positivity
    set x0 : ℝ := (1 / r - 1) / β with hx0def
    have hx0 : |x0| ≤ ξ := by
      rw [hx0def, abs_div, abs_of_pos hβ, div_le_iff₀ hβ]
      have e : 1 / r - 1 = (1 - r) / r := by field_simp
      rw [e, abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
      have hp := mul_nonneg he0 (sub_nonneg.mpr hrr)
      rw [abs_le]
      constructor
      · by_contra h
        have h' : 0 < r - 1 - ξ * β * r := by linarith [not_le.mp h]
        have := mul_pos h' (by linarith : (0 : ℝ) < 1 + r)
        nlinarith
      · by_contra h
        have h' : 0 < 1 - r - ξ * β * r := by linarith [not_le.mp h]
        have := mul_pos h' (by linarith : (0 : ℝ) < 1 + r)
        nlinarith
    obtain ⟨q, hqd, hqe⟩ := hpoly (sN • ω)
    have hch := hC q hqd (lam * r) β x0 (hx0.trans hξ2)
    have hc1 : lam * r * (1 + β * x0) = lam := by
      rw [hx0def]; field_simp; ring
    rw [hc1] at hch
    have hrs : radF53 W' • ω = r • (sN • ω) := by
      rw [smul_smul, hr, div_mul_cancel₀ _ hsN.ne']
    have hev : ∀ θ : ℝ, q.eval (lam * r * (1 + β * Real.cos θ)) =
        H (lt θ) (radF53 W' • ω) := by
      intro θ
      rw [hqe, hrs, hscal (lt θ) r (sN • ω)]
      congr 1
      rw [hlta]; ring
    simp only [hev, hqe] at hch
    set I : ℝ := ∫ θ in (0 : ℝ)..Real.pi,
      H (lt θ) (radF53 W' • ω) ^ 2 * Real.sin θ ^ 2 with hI
    have hI0 : 0 ≤ I :=
      intervalIntegral.integral_nonneg Real.pi_pos.le (fun θ _ => by positivity)
    have hx2 : x0 ^ 2 ≤ ξ ^ 2 := sq_le_sq' (neg_le_of_abs_le hx0) (le_of_abs_le hx0)
    have hreal : (1 - ξ ^ 2) * H lam (sN • ω) ^ 2 ≤ SS D ξ * (2 / Real.pi) * I := by
      have a1 : (1 - ξ ^ 2) * H lam (sN • ω) ^ 2 ≤ H lam (sN • ω) ^ 2 * (1 - x0 ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg (H lam (sN • ω)))]
      have a2 : SS D x0 * (2 / Real.pi * I) ≤ SS D ξ * (2 / Real.pi * I) :=
        mul_le_mul_of_nonneg_right (SS_mono D hx0)
          (mul_nonneg (div_nonneg zero_le_two Real.pi_pos.le) hI0)
      calc (1 - ξ ^ 2) * H lam (sN • ω) ^ 2 ≤ SS D ξ * (2 / Real.pi * I) :=
            a1.trans (hch.trans a2)
        _ = SS D ξ * (2 / Real.pi) * I := by ring
    have hIle : ENNReal.ofReal I ≤ F ω (radF53 W') := by
      rw [hI, intervalIntegral.integral_of_le Real.pi_pos.le, hFa]
      simp only [hΦa]
      exact ofReal_integral_le' (fun θ => by positivity)
    calc ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (H lam (sN • ω) ^ 2)
        = ENNReal.ofReal ((1 - ξ ^ 2) * H lam (sN • ω) ^ 2) :=
          (ENNReal.ofReal_mul hξsq.le).symm
      _ ≤ ENNReal.ofReal (SS D ξ * (2 / Real.pi) * I) := ENNReal.ofReal_le_ofReal hreal
      _ = K * ENNReal.ofReal I := by
          rw [hK]
          exact ENNReal.ofReal_mul (mul_nonneg hSS0 (div_nonneg zero_le_two Real.pi_pos.le))
      _ ≤ K * F ω (radF53 W') := by gcongr
  -- the probability of a good radius
  have hgood : ENNReal.ofReal (1 - ν) ≤
      stdGauss ι {W' : ι → ℝ | |(radF53 W' / sN) ^ 2 - 1| ≤ η} := by
    have hbad := rad_tail ι hN η hηpos
    have hun : (1 : ℝ≥0∞) ≤ stdGauss ι {W' : ι → ℝ | |(radF53 W' / sN) ^ 2 - 1| ≤ η} +
        stdGauss ι {W' : ι → ℝ | η < |(radF53 W' / sN) ^ 2 - 1|} := by
      rw [← measure_univ (μ := stdGauss ι)]
      refine (measure_mono ?_).trans (measure_union_le _ _)
      intro Z _
      by_cases h : |(radF53 Z / sN) ^ 2 - 1| ≤ η
      · exact Or.inl h
      · exact Or.inr (not_le.mp h)
    calc ENNReal.ofReal (1 - ν) = ENNReal.ofReal 1 - ENNReal.ofReal ν :=
          ENNReal.ofReal_sub _ hν0
      _ = 1 - ENNReal.ofReal ν := by rw [ENNReal.ofReal_one]
      _ ≤ _ := tsub_le_iff_right.mpr (hun.trans (add_le_add le_rfl hbad))
  -- per direction
  have hω : ∀ ω : ι → ℝ, ENNReal.ofReal (1 - ν) *
      (ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (H lam (sN • ω) ^ 2)) ≤
      ∫⁻ W', K * F ω (radF53 W') ∂stdGauss ι := by
    intro ω
    set c0 : ℝ≥0∞ := ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (H lam (sN • ω) ^ 2) with hc0
    have hGm : Measurable (fun W' : ι → ℝ => K * F ω (radF53 W')) :=
      measurable_const.mul (hFm.comp (measurable_const.prodMk BstLean.Part53.measurable_radF))
    have hmk := mul_meas_ge_le_lintegral (μ := stdGauss ι) hGm c0
    calc ENNReal.ofReal (1 - ν) * c0
        ≤ stdGauss ι {W' : ι → ℝ | |(radF53 W' / sN) ^ 2 - 1| ≤ η} * c0 := by gcongr
      _ ≤ stdGauss ι {W' : ι → ℝ | c0 ≤ K * F ω (radF53 W')} * c0 := by
          exact mul_le_mul (measure_mono fun W' h => hkey ω W' h) le_rfl bot_le bot_le
      _ = c0 * stdGauss ι {W' : ι → ℝ | c0 ≤ K * F ω (radF53 W')} := mul_comm _ _
      _ ≤ _ := hmk
  -- the scale integral
  have hθ : ∀ θ : ℝ, ∫⁻ W, Φ θ W ∂stdGauss ι ≤
      ENNReal.ofReal (Real.sin θ ^ 2) * ENNReal.ofReal Bd := by
    intro θ
    obtain ⟨hi, hb⟩ := hint θ
    rw [← hlta] at hi hb
    have e : ∀ W : ι → ℝ, Φ θ W =
        ENNReal.ofReal (Real.sin θ ^ 2) * ENNReal.ofReal (H (lt θ) W ^ 2) := fun W => by
      rw [hΦa, mul_comm, ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun W => sq_nonneg _)]
    gcongr
  have hsin : ∫⁻ θ in Set.Ioc (0 : ℝ) Real.pi, ENNReal.ofReal (Real.sin θ ^ 2) =
      ENNReal.ofReal (Real.pi / 2) := by
    have hcs : Continuous fun θ : ℝ => Real.sin θ ^ 2 := Real.continuous_sin.pow 2
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcs.intervalIntegrable 0 Real.pi).1) (Filter.Eventually.of_forall fun θ => sq_nonneg _),
      ← intervalIntegral.integral_of_le Real.pi_pos.le, integral_sin_sq]
    congr 1
    simp
  have hBd0 : 0 ≤ Bd := le_trans (integral_nonneg fun W => sq_nonneg _) (hint 0).2
  have hmain : ENNReal.ofReal (1 - ν) * (ENNReal.ofReal (1 - ξ ^ 2) *
      ∫⁻ W, ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2) ∂stdGauss ι) ≤
      ENNReal.ofReal (SS D ξ * Bd) := by
    calc ENNReal.ofReal (1 - ν) * (ENNReal.ofReal (1 - ξ ^ 2) *
          ∫⁻ W, ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2) ∂stdGauss ι)
        = ∫⁻ W, ENNReal.ofReal (1 - ν) * (ENNReal.ofReal (1 - ξ ^ 2) *
            ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2)) ∂stdGauss ι := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ W, ∫⁻ W', K * F (unitF53 W) (radF53 W') ∂stdGauss ι ∂stdGauss ι :=
          lintegral_mono fun W => hω (unitF53 W)
      _ = ∫⁻ W, K * F (unitF53 W) (radF53 W) ∂stdGauss ι :=
          (BstLean.Part53.gauss_polar_gen (fun ω ρ => K * F ω ρ)
            (measurable_const.mul hFm)).symm
      _ = K * ∫⁻ W, (∫⁻ θ in Set.Ioc (0 : ℝ) Real.pi, Φ θ W) ∂stdGauss ι := by
          rw [lintegral_const_mul' _ _ hKtop]
          simp only [hFa, rad_smul_unit]
      _ = K * ∫⁻ θ in Set.Ioc (0 : ℝ) Real.pi, ∫⁻ W, Φ θ W ∂stdGauss ι := by
          rw [lintegral_lintegral_swap]
          exact (hΦm.comp measurable_swap).aemeasurable
      _ ≤ K * ∫⁻ θ in Set.Ioc (0 : ℝ) Real.pi,
            ENNReal.ofReal (Real.sin θ ^ 2) * ENNReal.ofReal Bd := by
          gcongr with θ
          exact hθ θ
      _ = K * (ENNReal.ofReal (Real.pi / 2) * ENNReal.ofReal Bd) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hsin]
      _ = ENNReal.ofReal (SS D ξ * Bd) := by
          rw [hK, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (mul_nonneg hSS0 (div_nonneg zero_le_two Real.pi_pos.le))]
          congr 1
          have := Real.pi_pos.ne'
          field_simp
  have hν1 : 0 < 1 - ν := by linarith
  have hZ : 0 < (1 - ξ ^ 2) * (1 - ν) := mul_pos hξsq hν1
  rw [ENNReal.ofReal_div_of_pos hZ]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hZ)) (Or.inl ENNReal.ofReal_ne_top)]
  refine le_trans (le_of_eq ?_) hmain
  rw [ENNReal.ofReal_mul hξsq.le]
  ring

/-! ## The sphere step -/

set_option maxHeartbeats 1600000 in
theorem semiStep (n d k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (w c1 cV efl cE : ℝ) (hc1 : 0 ≤ c1)
    (hcV : 0 ≤ cV) (hcE : 0 ≤ cE) (hcard : 1 ≤ Fintype.card (WIdx n d))
    (hG : GM88 n d k w c1 cV efl cE) (hC1 : ChrisIface k) (hC2 : ChrisIface (2 * k))
    (hRad : RadPoly n d) (hPoly : PolyRep n d) : SemiStep n d k w c1 cV efl cE := by
  classical
  intro P hP lam hlam ε κ β ξ θ hε hκ hefl hβ hβ1 hξ hξ2 hξβ hθ hν hwU hwL
  obtain ⟨L, Vb, hL, hwin, hdrift⟩ := hG P hP
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have hinv0 : 0 < 1 / (n : ℝ) := by positivity
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlam
  have hβsq : (1 : ℝ) ≤ (1 + β) ^ 2 := by nlinarith
  have hw1 : 1 / (n : ℝ) ≤ w / n := by nlinarith
  have hwin0 : |lam ^ 2 - 1| ≤ w / (n : ℝ) := hlam.trans hw1
  -- the window
  have hwinθ : ∀ θ' : ℝ, |(lam * (1 + β * Real.cos θ')) ^ 2 - 1| ≤ w / (n : ℝ) := by
    intro θ'
    obtain ⟨hu2, hu1⟩ := u_bounds β (Real.cos θ') hβ hβ1 (Real.neg_one_le_cos θ')
      (Real.cos_le_one θ')
    rw [mul_pow, abs_le]
    constructor
    · have : (1 - 1 / (n : ℝ)) * (1 - β) ^ 2 ≤ lam ^ 2 * (1 + β * Real.cos θ') ^ 2 :=
        mul_le_mul (by linarith) hu2 (sq_nonneg _) (sq_nonneg _)
      linarith
    · have : lam ^ 2 * (1 + β * Real.cos θ') ^ 2 ≤ (1 + 1 / (n : ℝ)) * (1 + β) ^ 2 :=
        mul_le_mul (by linarith) hu1 (sq_nonneg _) (by positivity)
      linarith
  set cstar : ℝ := Vb lam with hcstar
  have hcs : (1 - efl) * L ≤ cstar := (hwin lam hwin0).1
  have hDpos : (0 : ℝ) < DW n d := by
    unfold DW; exact_mod_cast (show 0 < Fintype.card (WIdx n d) by omega)
  set Z : ℝ := (1 - ξ ^ 2) * (1 - nuB n d β ξ) with hZdef
  have hZ : 0 < Z := mul_pos (by nlinarith) (by linarith)
  have hν' : 2 / ((Fintype.card (WIdx n d) : ℝ) * (19 / 10 * ξ * β) ^ 2) < 1 := hν
  set G1 : (WIdx n d → ℝ) → ℝ := fun W => errW P lam W ^ 2 with hG1
  set G2 : (WIdx n d → ℝ) → ℝ := fun W => (VW P lam W - cstar) ^ 2 with hG2
  -- Step A, error
  have hT1 : ∫⁻ W, ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W)) ∂stdGauss (WIdx n d) ≤
      ENNReal.ofReal (SS k ξ * (c1 / n * L) / Z) := by
    refine semi_transfer (ι := WIdx n d) (by omega) (fun s W => errW P s W) k hC1
      (fun s t W => errW_smul P s t W) ?_ (fun s => (BW_meas k hPoly P hP s).sub_const _)
      lam β ξ (c1 / n * L) hβ hξ hξ2 hξβ hν' ?_
    · intro W
      obtain ⟨⟨qB, hd, he⟩, -⟩ := hRad k P hP W
      refine ⟨qB - Polynomial.C (g0P d P),
        (Polynomial.natDegree_sub_le _ _).trans (max_le hd (by simp)), fun s => ?_⟩
      simp only [errW, Polynomial.eval_sub, Polynomial.eval_C, he]
    · intro θ'
      have h := hwin _ (hwinθ θ')
      exact ⟨h.2.1, h.2.2.2.1⟩
  -- Step A, variance
  have htB0 : 0 ≤ tB n β := by
    unfold tB
    have : 0 < (1 - β) ^ 2 := by nlinarith
    have : 0 ≤ (1 + β) ^ 2 - 1 := by linarith
    positivity
  have hint2 : ∀ θ' : ℝ,
      Integrable (fun W : WIdx n d → ℝ => (VW P (lam * (1 + β * Real.cos θ')) W - cstar) ^ 2)
        (stdGauss (WIdx n d)) ∧
      ∫ W : WIdx n d → ℝ, (VW P (lam * (1 + β * Real.cos θ')) W - cstar) ^ 2
        ∂stdGauss (WIdx n d) ≤ cVe n k c1 cV cE β θ / n * L ^ 2 := by
    intro θ'
    obtain ⟨hu2, hu1⟩ := u_bounds β (Real.cos θ') hβ hβ1 (Real.neg_one_le_cos θ')
      (Real.cos_le_one θ')
    have hl2 : (lam * (1 + β * Real.cos θ')) ^ 2 = lam ^ 2 * (1 + β * Real.cos θ') ^ 2 := by ring
    have hd := hdrift lam (lam * (1 + β * Real.cos θ')) hwin0 (hwinθ θ')
    obtain ⟨-, -, hi2, -, hb2⟩ := hwin (lam * (1 + β * Real.cos θ')) (hwinθ θ')
    set l' : ℝ := lam * (1 + β * Real.cos θ') with hl'
    set u : ℝ := (1 + β * Real.cos θ') ^ 2 with hu
    have hβ0 : 0 < (1 - β) ^ 2 := by nlinarith
    have ht : |l' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (l' ^ 2) ≤ tB n β := by
      by_cases hlam0 : lam = 0
      · have : l' = 0 := by rw [hl', hlam0, zero_mul]
        rw [this, hlam0]; simpa using htB0
      · have hlp : 0 < lam ^ 2 := by positivity
        have hm : lam ^ 2 * (1 - β) ^ 2 ≤ min (lam ^ 2) (l' ^ 2) := by
          refine le_min ?_ ?_
          · have : (1 - β) ^ 2 ≤ 1 := by nlinarith
            nlinarith
          · rw [hl2]; exact mul_le_mul_of_nonneg_left hu2 hlp.le
        have hmpos : 0 < min (lam ^ 2) (l' ^ 2) := lt_of_lt_of_le (by positivity) hm
        rw [div_le_iff₀ hmpos]
        have habs : |l' ^ 2 - lam ^ 2| ≤ lam ^ 2 * ((1 + β) ^ 2 - 1) := by
          rw [hl2, abs_le]
          have e1 := mul_le_mul_of_nonneg_left hu1 hlp.le
          have e2 := mul_le_mul_of_nonneg_left hu2 hlp.le
          have e3 := mul_nonneg hlp.le (sq_nonneg β)
          constructor <;> nlinarith
        calc |l' ^ 2 - lam ^ 2| * Real.sqrt n
            ≤ lam ^ 2 * ((1 + β) ^ 2 - 1) * Real.sqrt n :=
              mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg _)
          _ = tB n β * (lam ^ 2 * (1 - β) ^ 2) := by
              unfold tB
              have hb1 : (1 : ℝ) - β ≠ 0 := by linarith
              field_simp
          _ ≤ tB n β * min (lam ^ 2) (l' ^ 2) := mul_le_mul_of_nonneg_left hm htB0
    have ht0 : 0 ≤ |l' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (l' ^ 2) :=
      div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
        (le_min (sq_nonneg _) (sq_nonneg _))
    set t' : ℝ := |l' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (l' ^ 2) with ht'
    have hdr : |Vb l' - cstar| ≤ DrF n k c1 cE β * L := by
      refine hd.trans (mul_le_mul_of_nonneg_right ?_ hL)
      unfold DrF
      have hkt : (k : ℝ) * t' ≤ k * tB n β := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
      have hp : (1 + (k : ℝ) * t') ^ (2 * k) ≤ (1 + k * tB n β) ^ (2 * k) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have := mul_le_mul_of_nonneg_right (sub_le_sub_right hp 1) hcE
      linarith
    set b : ℝ := DrF n k c1 cE β * L with hb
    have hsq : (Vb l' - cstar) ^ 2 ≤ b ^ 2 :=
      sq_le_sq' (neg_le_of_abs_le hdr) (le_of_abs_le hdr)
    have h1θ : 0 ≤ 1 + 1 / θ := by positivity
    have hpt : ∀ W : WIdx n d → ℝ, (VW P l' W - cstar) ^ 2 ≤
        (1 + θ) * (VW P l' W - Vb l') ^ 2 + (1 + 1 / θ) * b ^ 2 := by
      intro W
      have hy := young (VW P l' W - Vb l') (Vb l' - cstar) θ hθ
      have e : VW P l' W - cstar = (VW P l' W - Vb l') + (Vb l' - cstar) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hsq h1θ
      linarith
    have hgi : Integrable (fun W : WIdx n d → ℝ =>
        (1 + θ) * (VW P l' W - Vb l') ^ 2 + (1 + 1 / θ) * b ^ 2) (stdGauss (WIdx n d)) :=
      (hi2.const_mul _).add (integrable_const _)
    have hi : Integrable (fun W : WIdx n d → ℝ => (VW P l' W - cstar) ^ 2)
        (stdGauss (WIdx n d)) := by
      refine Integrable.mono' hgi
        (((VW_meas k hn hPoly P hP l').sub_const _).pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun W => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt W
    refine ⟨hi, ?_⟩
    calc ∫ W : WIdx n d → ℝ, (VW P l' W - cstar) ^ 2 ∂stdGauss (WIdx n d)
        ≤ ∫ W : WIdx n d → ℝ, ((1 + θ) * (VW P l' W - Vb l') ^ 2 + (1 + 1 / θ) * b ^ 2)
            ∂stdGauss (WIdx n d) := integral_mono hi hgi hpt
      _ = (1 + θ) * ∫ W : WIdx n d → ℝ, (VW P l' W - Vb l') ^ 2 ∂stdGauss (WIdx n d) +
            (1 + 1 / θ) * b ^ 2 := by
          rw [integral_add (hi2.const_mul _) (integrable_const _), integral_const_mul,
            integral_const]
          simp
      _ ≤ (1 + θ) * (cV / n * L ^ 2) + (1 + 1 / θ) * b ^ 2 := by
          have := mul_le_mul_of_nonneg_left hb2 (by linarith : (0 : ℝ) ≤ 1 + θ)
          linarith
      _ = cVe n k c1 cV cE β θ / n * L ^ 2 := by
          simp only [cVe, hb]
          field_simp
  have hT2 : ∫⁻ W, ENNReal.ofReal (G2 (Real.sqrt (DW n d) • unitF53 W)) ∂stdGauss (WIdx n d) ≤
      ENNReal.ofReal (SS (2 * k) ξ * (cVe n k c1 cV cE β θ / n * L ^ 2) / Z) := by
    refine semi_transfer (ι := WIdx n d) (by omega) (fun s W => VW P s W - cstar) (2 * k) hC2
      (fun s t W => by simp only [VW_smul]) ?_
      (fun s => (VW_meas k hn hPoly P hP s).sub_const _)
      lam β ξ (cVe n k c1 cV cE β θ / n * L ^ 2) hβ hξ hξ2 hξβ hν' hint2
    intro W
    obtain ⟨-, ⟨qV, hd, he⟩⟩ := hRad k P hP W
    refine ⟨qV - Polynomial.C cstar,
      (Polynomial.natDegree_sub_le _ _).trans (max_le hd (by simp)), fun s => ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_C, he]
  -- Step C
  have hBm := BW_meas k hPoly P hP lam
  have hVm := VW_meas k hn hPoly P hP lam
  have hG1m : Measurable G1 := (hBm.sub_const _).pow_const 2
  have hG2m : Measurable G2 := (hVm.sub_const _).pow_const 2
  have hsm : Measurable (fun W : WIdx n d → ℝ => Real.sqrt (DW n d) • unitF53 W) :=
    (BstLean.Part53.measurable_unitF (ι := WIdx n d)).const_smul (Real.sqrt (DW n d))
  have hm1 : Measurable (fun W : WIdx n d → ℝ =>
      ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG1m.comp hsm)
  have hm2 : Measurable (fun W : WIdx n d → ℝ =>
      ENNReal.ofReal (G2 (Real.sqrt (DW n d) • unitF53 W))) :=
    ENNReal.measurable_ofReal.comp (hG2m.comp hsm)
  have hδ : 0 < 1 - efl - κ := by linarith
  have hSS1 : 0 ≤ SS k ξ := le_trans zero_le_one (SS_ge_one k ξ)
  have hSS2 : 0 ≤ SS (2 * k) ξ := le_trans zero_le_one (SS_ge_one (2 * k) ξ)
  have hcVe : 0 ≤ cVe n k c1 cV cE β θ := by
    unfold cVe
    have h1θ : 0 ≤ 1 + 1 / θ := by positivity
    have : 0 ≤ (n : ℝ) * DrF n k c1 cE β ^ 2 := by positivity
    have := mul_nonneg h1θ this
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + θ) hcV
    linarith
  have ht1 : 0 ≤ SS k ξ * c1 / (n * (ε ^ 2 * κ)) / Z := by positivity
  have ht2 : 0 ≤ SS (2 * k) ξ * cVe n k c1 cV cE β θ / (n * (1 - efl - κ) ^ 2) / Z := by
    positivity
  rcases hL.eq_or_lt with hL0 | hLpos
  · -- `L = 0`
    have hz : ∫⁻ W, ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W))
        ∂stdGauss (WIdx n d) = 0 := by
      apply le_antisymm _ bot_le
      refine hT1.trans (le_of_eq (ENNReal.ofReal_eq_zero.mpr (le_of_eq ?_)))
      rw [← hL0]; simp
    have hae := (lintegral_eq_zero_iff hm1).mp hz
    refine le_trans (le_of_eq (measure_mono_null ?_ (ae_iff.mp hae))) bot_le
    intro W hW
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le, hG1] at hW ⊢
    have := VW_nonneg P lam (Real.sqrt (DW n d) • unitF53 W)
    have h2 : 0 ≤ ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) := by positivity
    exact lt_of_le_of_lt h2 hW
  · -- `L > 0`
    have hθ1 : 0 < ε ^ 2 * κ * L := by positivity
    have hθ2 : 0 < ((1 - efl - κ) * L) ^ 2 := by positivity
    have hsub : {W : WIdx n d → ℝ | ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) <
          errW P lam (Real.sqrt (DW n d) • unitF53 W) ^ 2} ⊆
        {W | ENNReal.ofReal (ε ^ 2 * κ * L) ≤
            ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W))} ∪
        {W | ENNReal.ofReal (((1 - efl - κ) * L) ^ 2) ≤
            ENNReal.ofReal (G2 (Real.sqrt (DW n d) • unitF53 W))} := by
      intro W hW
      simp only [Set.mem_ofPred_eq] at hW
      by_cases hV : VW P lam (Real.sqrt (DW n d) • unitF53 W) < κ * L
      · right
        apply ENNReal.ofReal_le_ofReal
        simp only [hG2]
        have h1 : (1 - efl - κ) * L ≤ cstar - VW P lam (Real.sqrt (DW n d) • unitF53 W) := by
          nlinarith
        have h0 : 0 ≤ (1 - efl - κ) * L := by positivity
        nlinarith
      · left
        apply ENNReal.ofReal_le_ofReal
        simp only [hG1]
        have hV' := not_lt.mp hV
        have : ε ^ 2 * (κ * L) ≤ ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) :=
          mul_le_mul_of_nonneg_left hV' (by positivity)
        nlinarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have hM1 := (meas_ge_le_lintegral_div hm1.aemeasurable
      (by simpa using hθ1) ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT1 _)
    have hM2 := (meas_ge_le_lintegral_div hm2.aemeasurable
      (by simpa using hθ2) ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hT2 _)
    rw [← ENNReal.ofReal_div_of_pos hθ1] at hM1
    rw [← ENNReal.ofReal_div_of_pos hθ2] at hM2
    have hp : pS n d k c1 cV efl cE β ξ θ ε κ =
        SS k ξ * c1 / (n * (ε ^ 2 * κ)) / Z +
          SS (2 * k) ξ * cVe n k c1 cV cE β θ / (n * (1 - efl - κ) ^ 2) / Z := by
      unfold pS; rw [hZdef, add_div]
    rw [hp, ENNReal.ofReal_add ht1 ht2]
    have hZne := hZ.ne'
    have hLne := hLpos.ne'
    have hεne := hε.ne'
    have hκne := hκ.ne'
    have hδne := hδ.ne'
    have hnne := hnR.ne'
    refine add_le_add (hM1.trans (le_of_eq ?_)) (hM2.trans (le_of_eq ?_))
    · congr 1
      field_simp
    · congr 1
      field_simp

end BstLean.Part88

#print axioms BstLean.Part88.semiStep
