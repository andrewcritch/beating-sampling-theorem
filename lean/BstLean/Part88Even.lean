import BstLean.Part88Semi
import BstLean.Part33Euler

/-!
# Part 88, the sphere step with parity (`SemiStepE`)

The semicircle average is over `lam²`. The average over the direction of `W` is symmetric under
`W ↦ −W`, and `H s (−W) = H (−s) W`, so the even and the odd part of `s ↦ H s W` are polynomials
in `s²` of half the degree. The Christoffel bound is applied to each of them.
-/

namespace BstLean.Part88

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part78 (Good good_coord markov_gt)
open BstLean.Part81 (WIdx)
open BstLean.Part84

/-- The scale ratio bound inside the semicircle window (in the variable `lam²`). -/
noncomputable def tBE (n : ℕ) (β : ℝ) : ℝ := β * Real.sqrt n / (1 - β)

/-- The drift of the centre inside the window (relative to `L`). -/
noncomputable def DrFE (n k : ℕ) (c1 cE β : ℝ) : ℝ :=
  ((1 + k * tBE n β) ^ (2 * k) - 1) * cE + 2 * c1 / n

noncomputable def cVeE (n k : ℕ) (c1 cV cE β θ : ℝ) : ℝ :=
  (1 + θ) * cV + (1 + 1 / θ) * (n * DrFE n k c1 cE β ^ 2)

/-- The bound for the probability that the radius ratio is not good. -/
noncomputable def nuBE (n d : ℕ) (β ξ : ℝ) : ℝ := 2 / (DW n d * (99 / 100 * ξ * β) ^ 2)

/-- The Christoffel constant of the even/odd transfer for degree `D ≥ 1`. -/
noncomputable def SE (D : ℕ) (β ξ : ℝ) : ℝ := max (SS (D / 2) ξ) ((1 + 3 * β) * SS ((D - 1) / 2) ξ)

noncomputable def pSE (n d k : ℕ) (c1 cV efl cE β ξ θ ε κ : ℝ) : ℝ :=
  (SE k β ξ * c1 / (n * (ε ^ 2 * κ)) +
    SE (2 * k) β ξ * cVeE n k c1 cV cE β θ / (n * (1 - efl - κ) ^ 2)) /
    ((1 - ξ ^ 2) * (1 - nuBE n d β ξ))

def SemiStepE (n d k : ℕ) (w c1 cV efl cE : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ k → ∀ lam : ℝ, |lam ^ 2 - 1| ≤ 1 / (n : ℝ) →
    ∀ ε κ β ξ θ : ℝ, 0 < ε → 0 < κ → efl + κ < 1 → 0 < β → β ≤ 1 / 4 → 0 < ξ → ξ ≤ 1 / 2 →
      ξ * β ≤ 1 / 100 → 0 < θ → nuBE n d β ξ < 1 →
      (1 + 1 / (n : ℝ)) * (1 + β) ≤ 1 + w / n →
      1 - w / n ≤ (1 - 1 / (n : ℝ)) * (1 - β) →
      stdGauss (WIdx n d) {W | ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) <
          errW P lam (Real.sqrt (DW n d) • unitF53 W) ^ 2} ≤
        ENNReal.ofReal (pSE n d k c1 cV efl cE β ξ θ ε κ)

/-! ## Elementary facts -/

private lemma ofReal_integral_leE {α : Type*} [MeasurableSpace α] {ν : Measure α} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) : ENNReal.ofReal (∫ x, g x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
  by_cases hi : Integrable g ν
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hg)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le

lemma parity_sum (c : ℕ → ℝ) (s : ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), c i * s ^ i =
      ∑ j ∈ Finset.range m, c (2 * j) * (s ^ 2) ^ j +
        s * ∑ j ∈ Finset.range m, c (2 * j + 1) * (s ^ 2) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- The even and the odd part of a polynomial, as polynomials in `s²`. -/
lemma parity_split (q : Polynomial ℝ) (D : ℕ) (hq : q.natDegree ≤ D) :
    ∃ a b : Polynomial ℝ, a.natDegree ≤ D / 2 ∧ b.natDegree ≤ (D - 1) / 2 ∧
      ∀ s : ℝ, q.eval s = a.eval (s ^ 2) + s * b.eval (s ^ 2) := by
  refine ⟨∑ j ∈ Finset.range (D + 1), Polynomial.C (q.coeff (2 * j)) * Polynomial.X ^ j,
    ∑ j ∈ Finset.range (D + 1), Polynomial.C (q.coeff (2 * j + 1)) * Polynomial.X ^ j, ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    by_cases h : j ≤ D / 2
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    by_cases h : j ≤ (D - 1) / 2
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · intro s
    rw [Polynomial.eval_eq_sum_range' (show q.natDegree < 2 * (D + 1) by omega), parity_sum]
    simp [Polynomial.eval_finsetSum]

lemma unitF53_neg {ι : Type} [Fintype ι] (W : ι → ℝ) : unitF53 (-W) = -unitF53 W := by
  unfold unitF53
  simp [smul_neg]

lemma lintegral_neg_stdGauss {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ W, f (-W) ∂stdGauss ι = ∫⁻ W, f W ∂stdGauss ι := by
  classical
  calc ∫⁻ W, f (-W) ∂stdGauss ι = ∫⁻ W, f W ∂((stdGauss ι).map (fun z => -z)) :=
        (lintegral_map hf measurable_neg).symm
    _ = _ := by rw [BstLean.Part33.stdGauss_neg_invariant]

/-! ## Step A: the generic transfer with parity -/

set_option maxHeartbeats 3200000 in
lemma semi_transferE {ι : Type} [Fintype ι] (hN : 0 < Fintype.card ι) (H : ℝ → (ι → ℝ) → ℝ)
    (D : ℕ) (hC : ∀ D' : ℕ, ChrisIface D')
    (hscal : ∀ (s t : ℝ) (W : ι → ℝ), H s (t • W) = H (s * t) W)
    (hpoly : ∀ W : ι → ℝ, ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧ ∀ s : ℝ, q.eval s = H s W)
    (hmeas : ∀ s : ℝ, Measurable (H s))
    (lam β ξ Bd : ℝ) (hβ : 0 < β) (hβ4 : β ≤ 1 / 4) (hξ : 0 < ξ) (hξ2 : ξ ≤ 1 / 2)
    (hξβ : ξ * β ≤ 1 / 100)
    (hν : 2 / ((Fintype.card ι : ℝ) * (99 / 100 * ξ * β) ^ 2) < 1)
    (hint : ∀ θ : ℝ,
      Integrable (fun W : ι → ℝ => H (|lam| * Real.sqrt (1 + β * Real.cos θ)) W ^ 2)
        (stdGauss ι) ∧
      ∫ W : ι → ℝ, H (|lam| * Real.sqrt (1 + β * Real.cos θ)) W ^ 2 ∂stdGauss ι ≤ Bd) :
    ∫⁻ W, ENNReal.ofReal (H lam (Real.sqrt (Fintype.card ι) • unitF53 W) ^ 2) ∂stdGauss ι ≤
      ENNReal.ofReal (SE D β ξ * Bd /
        ((1 - ξ ^ 2) * (1 - 2 / ((Fintype.card ι : ℝ) * (99 / 100 * ξ * β) ^ 2)))) := by
  classical
  have hN' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set sN : ℝ := Real.sqrt N with hsNdef
  have hsN : 0 < sN := Real.sqrt_pos.mpr hN'
  have hηpos : 0 < 99 / 100 * ξ * β := by positivity
  set η : ℝ := 99 / 100 * ξ * β with hηdef
  set ν : ℝ := 2 / (N * η ^ 2) with hνdef
  have hν0 : 0 ≤ ν := by positivity
  have hξsq : 0 < 1 - ξ ^ 2 := by nlinarith
  have hSa0 : 0 ≤ SS (D / 2) ξ := le_trans zero_le_one (SS_ge_one _ ξ)
  have hSb0 : 0 ≤ SS ((D - 1) / 2) ξ := le_trans zero_le_one (SS_ge_one _ ξ)
  have hSEa : SS (D / 2) ξ ≤ SE D β ξ := le_max_left _ _
  have hSEb : (1 + 3 * β) * SS ((D - 1) / 2) ξ ≤ SE D β ξ := le_max_right _ _
  have hSE0 : 0 ≤ SE D β ξ := hSa0.trans hSEa
  have hβne : β ≠ 0 := hβ.ne'
  have hcont : ∀ W : ι → ℝ, Continuous fun s => H s W := by
    intro W
    obtain ⟨q, -, hq⟩ := hpoly W
    have : (fun s => H s W) = fun s => q.eval s := funext fun s => (hq s).symm
    rw [this]
    exact q.continuous
  have hHm : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  -- the symmetrized square
  obtain ⟨G, hG⟩ : ∃ G : ℝ → (ι → ℝ) → ℝ, G = fun s V => H s V ^ 2 + H s (-V) ^ 2 := ⟨_, rfl⟩
  have hGa : ∀ s V, G s V = H s V ^ 2 + H s (-V) ^ 2 := fun s V => by rw [hG]
  have hG0 : ∀ s V, 0 ≤ G s V := fun s V => by rw [hGa]; positivity
  have hGm : Measurable (Function.uncurry G) := by
    have h1 : Measurable (fun p : ℝ × (ι → ℝ) => H p.1 (-p.2)) :=
      hHm.comp (measurable_fst.prodMk measurable_snd.neg)
    have e : Function.uncurry G = fun p : ℝ × (ι → ℝ) => H p.1 p.2 ^ 2 + H p.1 (-p.2) ^ 2 := by
      funext p; obtain ⟨a, b⟩ := p; simp only [Function.uncurry_apply_pair, hGa]
    rw [e]
    exact (hHm.pow_const 2).add (h1.pow_const 2)
  obtain ⟨lt, hlt⟩ : ∃ lt : ℝ → ℝ, lt = fun θ => |lam| * Real.sqrt (1 + β * Real.cos θ) :=
    ⟨_, rfl⟩
  have hlta : ∀ θ, lt θ = |lam| * Real.sqrt (1 + β * Real.cos θ) := fun θ => by rw [hlt]
  have hu0 : ∀ θ : ℝ, 1 - β ≤ 1 + β * Real.cos θ := by
    intro θ
    have := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hβ.le
    linarith
  have hltsq : ∀ θ, lt θ ^ 2 = lam ^ 2 * (1 + β * Real.cos θ) := by
    intro θ
    rw [hlta, mul_pow, sq_abs, Real.sq_sqrt (by linarith [hu0 θ])]
  have hltm : Measurable lt := by
    rw [hlt]
    exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.add
      (continuous_const.mul Real.continuous_cos)))).measurable
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → (ι → ℝ) → ℝ≥0∞,
    Φ = fun θ V => ENNReal.ofReal (G (lt θ) V * Real.sin θ ^ 2) := ⟨_, rfl⟩
  have hΦa : ∀ θ V, Φ θ V = ENNReal.ofReal (G (lt θ) V * Real.sin θ ^ 2) :=
    fun θ V => by rw [hΦ]
  have hΦm : Measurable (fun p : ℝ × (ι → ℝ) => Φ p.1 p.2) := by
    have h1 : Measurable (fun p : ℝ × (ι → ℝ) => G (lt p.1) p.2) :=
      hGm.comp ((hltm.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable (fun p : ℝ × (ι → ℝ) => G (lt p.1) p.2 * Real.sin p.1 ^ 2) :=
      h1.mul ((Real.continuous_sin.measurable.comp measurable_fst).pow_const 2)
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
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0∞, K = ENNReal.ofReal (SE D β ξ * (2 / Real.pi)) := ⟨_, rfl⟩
  have hKtop : K ≠ ⊤ := by rw [hK]; exact ENNReal.ofReal_ne_top
  -- the pointwise Christoffel step
  have hkey : ∀ (ω W' : ι → ℝ), |(radF53 W' / sN) ^ 2 - 1| ≤ η →
      ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (G lam (sN • ω)) ≤
        K * F ω (radF53 W') := by
    intro ω W' hg
    set r : ℝ := radF53 W' / sN with hr
    set ρ : ℝ := r ^ 2 with hρ
    obtain ⟨h1, h2⟩ := abs_le.mp hg
    have he0 : 0 ≤ ξ * β := by positivity
    have hη' : η ≤ 99 / 10000 := by rw [hηdef]; nlinarith
    have hηe : η ≤ ξ * β := by rw [hηdef]; nlinarith
    have hρ99 : 99 / 100 ≤ ρ := by linarith
    have hρpos : 0 < ρ := by linarith
    have hρne : ρ ≠ 0 := hρpos.ne'
    set x0 : ℝ := (1 / ρ - 1) / β with hx0def
    have hx0 : |x0| ≤ ξ := by
      rw [hx0def, abs_div, abs_of_pos hβ, div_le_iff₀ hβ]
      have e : 1 / ρ - 1 = (1 - ρ) / ρ := by field_simp
      rw [e, abs_div, abs_of_pos hρpos, div_le_iff₀ hρpos]
      have hp := mul_nonneg he0 (sub_nonneg.mpr hρ99)
      rw [abs_le]
      constructor <;> nlinarith
    have hx0' : |x0| ≤ 1 / 2 := hx0.trans hξ2
    have hx2 : x0 ^ 2 ≤ ξ ^ 2 := sq_le_sq' (neg_le_of_abs_le hx0) (le_of_abs_le hx0)
    obtain ⟨q, hqd, hqe⟩ := hpoly (sN • ω)
    obtain ⟨a, b, hda, hdb, hab⟩ := parity_split q D hqd
    set c : ℝ := lam ^ 2 * ρ with hc
    have hGV : ∀ s t : ℝ, G s (t • (sN • ω)) =
        2 * (a.eval ((s * t) ^ 2) ^ 2 + (s * t) ^ 2 * b.eval ((s * t) ^ 2) ^ 2) := by
      intro s t
      have e : (s * -t) ^ 2 = (s * t) ^ 2 := by ring
      rw [hGa, ← neg_smul, hscal s t (sN • ω), hscal s (-t) (sN • ω), ← hqe, ← hqe, hab, hab, e]
      ring
    have hG1 : G lam (sN • ω) =
        2 * (a.eval (lam ^ 2) ^ 2 + lam ^ 2 * b.eval (lam ^ 2) ^ 2) := by
      have := hGV lam 1
      rwa [one_smul, mul_one] at this
    have hrs : radF53 W' • ω = r • (sN • ω) := by
      rw [smul_smul, hr, div_mul_cancel₀ _ hsN.ne']
    have hGθ : ∀ θ : ℝ, G (lt θ) (radF53 W' • ω) * Real.sin θ ^ 2 =
        2 * (a.eval (c * (1 + β * Real.cos θ)) ^ 2 +
          c * (1 + β * Real.cos θ) * b.eval (c * (1 + β * Real.cos θ)) ^ 2) *
          Real.sin θ ^ 2 := by
      intro θ
      have e : (lt θ * r) ^ 2 = c * (1 + β * Real.cos θ) := by
        rw [mul_pow, hltsq, hc]; ring
      rw [hrs, hGV, e]
    have hca := hC (D / 2) a hda c β x0 hx0'
    have hcb := hC ((D - 1) / 2) b hdb c β x0 hx0'
    have hc1 : c * (1 + β * x0) = lam ^ 2 := by
      rw [hx0def, hc]; field_simp; ring
    rw [hc1] at hca hcb
    obtain ⟨fa, hfa⟩ : ∃ fa : ℝ → ℝ, fa = fun θ =>
      a.eval (c * (1 + β * Real.cos θ)) ^ 2 * Real.sin θ ^ 2 := ⟨_, rfl⟩
    obtain ⟨fb, hfb⟩ : ∃ fb : ℝ → ℝ, fb = fun θ =>
      b.eval (c * (1 + β * Real.cos θ)) ^ 2 * Real.sin θ ^ 2 := ⟨_, rfl⟩
    have hinner : Continuous fun θ : ℝ => c * (1 + β * Real.cos θ) :=
      continuous_const.mul (continuous_const.add (continuous_const.mul Real.continuous_cos))
    have hfac : Continuous fa := by
      rw [hfa]
      exact ((a.continuous.comp hinner).pow 2).mul (Real.continuous_sin.pow 2)
    have hfbc : Continuous fb := by
      rw [hfb]
      exact ((b.continuous.comp hinner).pow 2).mul (Real.continuous_sin.pow 2)
    set Ia : ℝ := ∫ θ in (0 : ℝ)..Real.pi, fa θ with hIa
    set Ib : ℝ := ∫ θ in (0 : ℝ)..Real.pi, fb θ with hIb
    have hIa0 : 0 ≤ Ia :=
      intervalIntegral.integral_nonneg Real.pi_pos.le (fun θ _ => by rw [hfa]; positivity)
    have hIb0 : 0 ≤ Ib :=
      intervalIntegral.integral_nonneg Real.pi_pos.le (fun θ _ => by rw [hfb]; positivity)
    have hca' : a.eval (lam ^ 2) ^ 2 * (1 - x0 ^ 2) ≤ SS (D / 2) ξ * (2 / Real.pi * Ia) := by
      have e : (∫ θ in (0 : ℝ)..Real.pi,
          a.eval (c * (1 + β * Real.cos θ)) ^ 2 * Real.sin θ ^ 2) = Ia := by rw [hIa, hfa]
      rw [e] at hca
      exact hca.trans (mul_le_mul_of_nonneg_right (SS_mono _ hx0)
        (mul_nonneg (div_nonneg zero_le_two Real.pi_pos.le) hIa0))
    have hcb' : b.eval (lam ^ 2) ^ 2 * (1 - x0 ^ 2) ≤
        SS ((D - 1) / 2) ξ * (2 / Real.pi * Ib) := by
      have e : (∫ θ in (0 : ℝ)..Real.pi,
          b.eval (c * (1 + β * Real.cos θ)) ^ 2 * Real.sin θ ^ 2) = Ib := by rw [hIb, hfb]
      rw [e] at hcb
      exact hcb.trans (mul_le_mul_of_nonneg_right (SS_mono _ hx0)
        (mul_nonneg (div_nonneg zero_le_two Real.pi_pos.le) hIb0))
    set I : ℝ := ∫ θ in (0 : ℝ)..Real.pi,
      G (lt θ) (radF53 W' • ω) * Real.sin θ ^ 2 with hI
    have h3β : 0 < 1 + 3 * β := by linarith
    set κ0 : ℝ := lam ^ 2 / (1 + 3 * β) with hκ0
    have hκ00 : 0 ≤ κ0 := by positivity
    have hρβ : 1 - β / 2 ≤ ρ := by nlinarith
    have hI2 : 2 * (Ia + κ0 * Ib) ≤ I := by
      have e1 : 2 * (Ia + κ0 * Ib) = ∫ θ in (0 : ℝ)..Real.pi, 2 * (fa θ + κ0 * fb θ) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          (hfac.intervalIntegrable _ _) ((hfbc.const_mul κ0).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul]
      have hgc : Continuous fun θ : ℝ => 2 * (a.eval (c * (1 + β * Real.cos θ)) ^ 2 +
          c * (1 + β * Real.cos θ) * b.eval (c * (1 + β * Real.cos θ)) ^ 2) *
          Real.sin θ ^ 2 :=
        (continuous_const.mul (((a.continuous.comp hinner).pow 2).add
          (hinner.mul ((b.continuous.comp hinner).pow 2)))).mul (Real.continuous_sin.pow 2)
      rw [e1, hI]
      simp only [hGθ]
      refine intervalIntegral.integral_mono_on Real.pi_pos.le
        ((continuous_const.mul (hfac.add (hfbc.const_mul κ0))).intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _) (fun θ _ => ?_)
      rw [hfa, hfb]
      have hu := hu0 θ
      have hk : κ0 ≤ c * (1 + β * Real.cos θ) := by
        rw [hκ0, div_le_iff₀ h3β, hc]
        have h5 : 1 ≤ ρ * (1 + β * Real.cos θ) * (1 + 3 * β) := by
          have h6 : (1 - β / 2) * (1 - β) ≤ ρ * (1 + β * Real.cos θ) :=
            mul_le_mul hρβ hu (by linarith) hρpos.le
          have h7 : 1 ≤ (1 - β / 2) * (1 - β) * (1 + 3 * β) := by
            nlinarith [mul_nonneg hβ.le (by linarith : (0 : ℝ) ≤ 1 / 4 - β),
              mul_nonneg (mul_nonneg hβ.le hβ.le) hβ.le]
          exact h7.trans (mul_le_mul_of_nonneg_right h6 h3β.le)
        have := mul_le_mul_of_nonneg_left h5 (sq_nonneg lam)
        nlinarith
      have hbb : 0 ≤ b.eval (c * (1 + β * Real.cos θ)) ^ 2 * Real.sin θ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hk hbb
      simp only
      nlinarith
    have hI0 : 0 ≤ I :=
      intervalIntegral.integral_nonneg Real.pi_pos.le
        (fun θ _ => mul_nonneg (hG0 _ _) (sq_nonneg _))
    have hπ : 0 ≤ 2 / Real.pi := div_nonneg zero_le_two Real.pi_pos.le
    have hreal : (1 - ξ ^ 2) * G lam (sN • ω) ≤ SE D β ξ * (2 / Real.pi) * I := by
      have hA0 : 0 ≤ a.eval (lam ^ 2) ^ 2 := sq_nonneg _
      have hB0 : 0 ≤ lam ^ 2 * b.eval (lam ^ 2) ^ 2 := by positivity
      have a1 : (1 - ξ ^ 2) * G lam (sN • ω) ≤
          2 * (a.eval (lam ^ 2) ^ 2 * (1 - x0 ^ 2) +
            lam ^ 2 * (b.eval (lam ^ 2) ^ 2 * (1 - x0 ^ 2))) := by
        rw [hG1]
        nlinarith [mul_le_mul_of_nonneg_right hx2 hA0, mul_le_mul_of_nonneg_right hx2 hB0]
      have a2 : lam ^ 2 * (b.eval (lam ^ 2) ^ 2 * (1 - x0 ^ 2)) ≤
          SE D β ξ * (2 / Real.pi * (κ0 * Ib)) := by
        have s1 := mul_le_mul_of_nonneg_left hcb' (sq_nonneg lam)
        have e : lam ^ 2 * (SS ((D - 1) / 2) ξ * (2 / Real.pi * Ib)) =
            (1 + 3 * β) * SS ((D - 1) / 2) ξ * (2 / Real.pi * (κ0 * Ib)) := by
          rw [hκ0]; field_simp
        rw [e] at s1
        exact s1.trans (mul_le_mul_of_nonneg_right hSEb
          (mul_nonneg hπ (mul_nonneg hκ00 hIb0)))
      have a3 : a.eval (lam ^ 2) ^ 2 * (1 - x0 ^ 2) ≤ SE D β ξ * (2 / Real.pi * Ia) :=
        hca'.trans (mul_le_mul_of_nonneg_right hSEa (mul_nonneg hπ hIa0))
      have a4 : SE D β ξ * (2 / Real.pi) * (2 * (Ia + κ0 * Ib)) ≤
          SE D β ξ * (2 / Real.pi) * I :=
        mul_le_mul_of_nonneg_left hI2 (mul_nonneg hSE0 hπ)
      linarith
    have hIle : ENNReal.ofReal I ≤ F ω (radF53 W') := by
      rw [hI, intervalIntegral.integral_of_le Real.pi_pos.le, hFa]
      simp only [hΦa]
      exact ofReal_integral_leE (fun θ => mul_nonneg (hG0 _ _) (sq_nonneg _))
    calc ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (G lam (sN • ω))
        = ENNReal.ofReal ((1 - ξ ^ 2) * G lam (sN • ω)) :=
          (ENNReal.ofReal_mul hξsq.le).symm
      _ ≤ ENNReal.ofReal (SE D β ξ * (2 / Real.pi) * I) := ENNReal.ofReal_le_ofReal hreal
      _ = K * ENNReal.ofReal I := by
          rw [hK]
          exact ENNReal.ofReal_mul (mul_nonneg hSE0 hπ)
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
      (ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (G lam (sN • ω))) ≤
      ∫⁻ W', K * F ω (radF53 W') ∂stdGauss ι := by
    intro ω
    set c0 : ℝ≥0∞ := ENNReal.ofReal (1 - ξ ^ 2) * ENNReal.ofReal (G lam (sN • ω)) with hc0
    have hGm' : Measurable (fun W' : ι → ℝ => K * F ω (radF53 W')) :=
      measurable_const.mul (hFm.comp (measurable_const.prodMk BstLean.Part53.measurable_radF))
    have hmk := mul_meas_ge_le_lintegral (μ := stdGauss ι) hGm' c0
    calc ENNReal.ofReal (1 - ν) * c0
        ≤ stdGauss ι {W' : ι → ℝ | |(radF53 W' / sN) ^ 2 - 1| ≤ η} * c0 := by gcongr
      _ ≤ stdGauss ι {W' : ι → ℝ | c0 ≤ K * F ω (radF53 W')} * c0 := by
          exact mul_le_mul (measure_mono fun W' h => hkey ω W' h) le_rfl bot_le bot_le
      _ = c0 * stdGauss ι {W' : ι → ℝ | c0 ≤ K * F ω (radF53 W')} := mul_comm _ _
      _ ≤ _ := hmk
  -- the scale integral
  have hθ : ∀ θ : ℝ, ∫⁻ W, Φ θ W ∂stdGauss ι ≤
      ENNReal.ofReal (Real.sin θ ^ 2) * (2 * ENNReal.ofReal Bd) := by
    intro θ
    obtain ⟨hi, hb⟩ := hint θ
    rw [← hlta] at hi hb
    have hm0 : Measurable (fun W : ι → ℝ => ENNReal.ofReal (H (lt θ) W ^ 2)) :=
      ((hmeas (lt θ)).pow_const 2).ennreal_ofReal
    have e : ∀ W : ι → ℝ, Φ θ W =
        ENNReal.ofReal (Real.sin θ ^ 2) * (ENNReal.ofReal (H (lt θ) W ^ 2) +
          ENNReal.ofReal (H (lt θ) (-W) ^ 2)) := fun W => by
      rw [hΦa, hGa, mul_comm, ENNReal.ofReal_mul (sq_nonneg _),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm0,
      lintegral_neg_stdGauss (fun W => ENNReal.ofReal (H (lt θ) W ^ 2)) hm0, ← two_mul,
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
  -- the symmetry of the direction integral
  have hsym : ∫⁻ W, ENNReal.ofReal (G lam (sN • unitF53 W)) ∂stdGauss ι =
      2 * ∫⁻ W, ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2) ∂stdGauss ι := by
    have hm0 : Measurable (fun W : ι → ℝ => ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2)) :=
      (((hmeas lam).comp ((BstLean.Part53.measurable_unitF (ι := ι)).const_smul sN)).pow_const
        2).ennreal_ofReal
    have e : ∀ W : ι → ℝ, ENNReal.ofReal (G lam (sN • unitF53 W)) =
        ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2) +
          ENNReal.ofReal (H lam (sN • unitF53 (-W)) ^ 2) := fun W => by
      rw [hGa, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), unitF53_neg, smul_neg]
    simp only [e]
    rw [lintegral_add_left hm0,
      lintegral_neg_stdGauss (fun W => ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2)) hm0,
      ← two_mul]
  have hmain : ENNReal.ofReal (1 - ν) * (ENNReal.ofReal (1 - ξ ^ 2) *
      ∫⁻ W, ENNReal.ofReal (G lam (sN • unitF53 W)) ∂stdGauss ι) ≤
      2 * ENNReal.ofReal (SE D β ξ * Bd) := by
    calc ENNReal.ofReal (1 - ν) * (ENNReal.ofReal (1 - ξ ^ 2) *
          ∫⁻ W, ENNReal.ofReal (G lam (sN • unitF53 W)) ∂stdGauss ι)
        = ∫⁻ W, ENNReal.ofReal (1 - ν) * (ENNReal.ofReal (1 - ξ ^ 2) *
            ENNReal.ofReal (G lam (sN • unitF53 W))) ∂stdGauss ι := by
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
            ENNReal.ofReal (Real.sin θ ^ 2) * (2 * ENNReal.ofReal Bd) := by
          gcongr with θ
          exact hθ θ
      _ = K * (ENNReal.ofReal (Real.pi / 2) * (2 * ENNReal.ofReal Bd)) := by
          rw [lintegral_mul_const' _ _ (by simp [ENNReal.mul_eq_top]), hsin]
      _ = 2 * ENNReal.ofReal (SE D β ξ * Bd) := by
          have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [hK, e2, ← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (mul_nonneg hSE0 (div_nonneg zero_le_two Real.pi_pos.le)),
            ← ENNReal.ofReal_mul zero_le_two]
          congr 1
          have := Real.pi_pos.ne'
          field_simp
  have hν1 : 0 < 1 - ν := by linarith
  have hZ : 0 < (1 - ξ ^ 2) * (1 - ν) := mul_pos hξsq hν1
  rw [ENNReal.ofReal_div_of_pos hZ]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hZ)) (Or.inl ENNReal.ofReal_ne_top)]
  rw [hsym] at hmain
  have h2 : (2 : ℝ≥0∞) * ((∫⁻ W, ENNReal.ofReal (H lam (sN • unitF53 W) ^ 2) ∂stdGauss ι) *
      ENNReal.ofReal ((1 - ξ ^ 2) * (1 - ν))) ≤ 2 * ENNReal.ofReal (SE D β ξ * Bd) := by
    refine le_trans (le_of_eq ?_) hmain
    rw [ENNReal.ofReal_mul hξsq.le]
    ring
  have h3 : (2⁻¹ : ℝ≥0∞) * _ ≤ 2⁻¹ * _ := mul_le_mul le_rfl h2 bot_le bot_le
  have hcc : ∀ x : ℝ≥0∞, 2⁻¹ * (2 * x) = x := fun x => by
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rwa [hcc, hcc] at h3

/-! ## The sphere step -/

set_option maxHeartbeats 1600000 in
theorem semiStepE (n d k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (w c1 cV efl cE : ℝ) (hc1 : 0 ≤ c1)
    (hcV : 0 ≤ cV) (hcE : 0 ≤ cE) (hcard : 1 ≤ Fintype.card (WIdx n d))
    (hG : GM88 n d k w c1 cV efl cE) (hC : ∀ D : ℕ, ChrisIface D)
    (hRad : RadPoly n d) (hPoly : PolyRep n d) : SemiStepE n d k w c1 cV efl cE := by
  classical
  intro P hP lam hlam ε κ β ξ θ hε hκ hefl hβ hβ4 hξ hξ2 hξβ hθ hν hwU hwL
  obtain ⟨L, Vb, hL, hwin, hdrift⟩ := hG P hP
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnR]; exact hn1
  have hinv0 : 0 < 1 / (n : ℝ) := by positivity
  have hβ1 : β < 1 := by linarith
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlam
  have hlam0 : 0 ≤ lam ^ 2 := sq_nonneg lam
  have hw1 : 1 / (n : ℝ) ≤ w / n := by nlinarith
  have hwin0 : |lam ^ 2 - 1| ≤ w / (n : ℝ) := hlam.trans hw1
  have hu : ∀ θ' : ℝ, 1 - β ≤ 1 + β * Real.cos θ' ∧ 1 + β * Real.cos θ' ≤ 1 + β := by
    intro θ'
    have e1 := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ') hβ.le
    have e2 := mul_le_mul_of_nonneg_left (Real.cos_le_one θ') hβ.le
    constructor <;> linarith
  have hsq : ∀ θ' : ℝ, (|lam| * Real.sqrt (1 + β * Real.cos θ')) ^ 2 =
      lam ^ 2 * (1 + β * Real.cos θ') := by
    intro θ'
    rw [mul_pow, sq_abs, Real.sq_sqrt (by linarith [(hu θ').1])]
  -- the window
  have hwinθ : ∀ θ' : ℝ, |(|lam| * Real.sqrt (1 + β * Real.cos θ')) ^ 2 - 1| ≤ w / (n : ℝ) := by
    intro θ'
    obtain ⟨hu2, hu1⟩ := hu θ'
    rw [hsq, abs_le]
    constructor
    · have : (1 - 1 / (n : ℝ)) * (1 - β) ≤ lam ^ 2 * (1 + β * Real.cos θ') :=
        mul_le_mul (by linarith) hu2 (by linarith) hlam0
      linarith
    · have : lam ^ 2 * (1 + β * Real.cos θ') ≤ (1 + 1 / (n : ℝ)) * (1 + β) :=
        mul_le_mul (by linarith) hu1 (by linarith) (by positivity)
      linarith
  set cstar : ℝ := Vb lam with hcstar
  have hcs : (1 - efl) * L ≤ cstar := (hwin lam hwin0).1
  have hDpos : (0 : ℝ) < DW n d := by
    unfold DW; exact_mod_cast (show 0 < Fintype.card (WIdx n d) by omega)
  set Z : ℝ := (1 - ξ ^ 2) * (1 - nuBE n d β ξ) with hZdef
  have hZ : 0 < Z := mul_pos (by nlinarith) (by linarith)
  have hν' : 2 / ((Fintype.card (WIdx n d) : ℝ) * (99 / 100 * ξ * β) ^ 2) < 1 := hν
  set G1 : (WIdx n d → ℝ) → ℝ := fun W => errW P lam W ^ 2 with hG1
  set G2 : (WIdx n d → ℝ) → ℝ := fun W => (VW P lam W - cstar) ^ 2 with hG2
  -- Step A, error
  have hT1 : ∫⁻ W, ENNReal.ofReal (G1 (Real.sqrt (DW n d) • unitF53 W)) ∂stdGauss (WIdx n d) ≤
      ENNReal.ofReal (SE k β ξ * (c1 / n * L) / Z) := by
    refine semi_transferE (ι := WIdx n d) (by omega) (fun s W => errW P s W) k hC
      (fun s t W => errW_smul P s t W) ?_ (fun s => (BW_meas k hPoly P hP s).sub_const _)
      lam β ξ (c1 / n * L) hβ hβ4 hξ hξ2 hξβ hν' ?_
    · intro W
      obtain ⟨⟨qB, hd, he⟩, -⟩ := hRad k P hP W
      refine ⟨qB - Polynomial.C (g0P d P),
        (Polynomial.natDegree_sub_le _ _).trans (max_le hd (by simp)), fun s => ?_⟩
      simp only [errW, Polynomial.eval_sub, Polynomial.eval_C, he]
    · intro θ'
      have h := hwin _ (hwinθ θ')
      exact ⟨h.2.1, h.2.2.2.1⟩
  -- Step A, variance
  have h1β : 0 < 1 - β := by linarith
  have htB0 : 0 ≤ tBE n β := by
    unfold tBE
    positivity
  have hint2 : ∀ θ' : ℝ,
      Integrable (fun W : WIdx n d → ℝ =>
        (VW P (|lam| * Real.sqrt (1 + β * Real.cos θ')) W - cstar) ^ 2)
        (stdGauss (WIdx n d)) ∧
      ∫ W : WIdx n d → ℝ, (VW P (|lam| * Real.sqrt (1 + β * Real.cos θ')) W - cstar) ^ 2
        ∂stdGauss (WIdx n d) ≤ cVeE n k c1 cV cE β θ / n * L ^ 2 := by
    intro θ'
    obtain ⟨hu2, hu1⟩ := hu θ'
    have hl2 := hsq θ'
    have hd := hdrift lam (|lam| * Real.sqrt (1 + β * Real.cos θ')) hwin0 (hwinθ θ')
    obtain ⟨-, -, hi2, -, hb2⟩ := hwin (|lam| * Real.sqrt (1 + β * Real.cos θ')) (hwinθ θ')
    set l' : ℝ := |lam| * Real.sqrt (1 + β * Real.cos θ') with hl'
    have ht : |l' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (l' ^ 2) ≤ tBE n β := by
      by_cases hlam0' : lam = 0
      · have : l' = 0 := by rw [hl', hlam0', abs_zero, zero_mul]
        rw [this, hlam0']; simpa using htB0
      · have hlp : 0 < lam ^ 2 := by positivity
        have hm : lam ^ 2 * (1 - β) ≤ min (lam ^ 2) (l' ^ 2) := by
          refine le_min ?_ ?_
          · nlinarith
          · rw [hl2]; exact mul_le_mul_of_nonneg_left hu2 hlp.le
        have hmpos : 0 < min (lam ^ 2) (l' ^ 2) := lt_of_lt_of_le (by positivity) hm
        rw [div_le_iff₀ hmpos]
        have habs : |l' ^ 2 - lam ^ 2| ≤ lam ^ 2 * β := by
          rw [hl2, abs_le]
          have e1 := mul_le_mul_of_nonneg_left hu1 hlp.le
          have e2 := mul_le_mul_of_nonneg_left hu2 hlp.le
          constructor <;> nlinarith
        calc |l' ^ 2 - lam ^ 2| * Real.sqrt n
            ≤ lam ^ 2 * β * Real.sqrt n :=
              mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg _)
          _ = tBE n β * (lam ^ 2 * (1 - β)) := by
              unfold tBE
              have hb1 : (1 : ℝ) - β ≠ 0 := h1β.ne'
              field_simp
          _ ≤ tBE n β * min (lam ^ 2) (l' ^ 2) := mul_le_mul_of_nonneg_left hm htB0
    have ht0 : 0 ≤ |l' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (l' ^ 2) :=
      div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
        (le_min (sq_nonneg _) (sq_nonneg _))
    set t' : ℝ := |l' ^ 2 - lam ^ 2| * Real.sqrt n / min (lam ^ 2) (l' ^ 2) with ht'
    have hdr : |Vb l' - cstar| ≤ DrFE n k c1 cE β * L := by
      refine hd.trans (mul_le_mul_of_nonneg_right ?_ hL)
      unfold DrFE
      have hkt : (k : ℝ) * t' ≤ k * tBE n β := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
      have hp : (1 + (k : ℝ) * t') ^ (2 * k) ≤ (1 + k * tBE n β) ^ (2 * k) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have := mul_le_mul_of_nonneg_right (sub_le_sub_right hp 1) hcE
      linarith
    set b : ℝ := DrFE n k c1 cE β * L with hb
    have hsq' : (Vb l' - cstar) ^ 2 ≤ b ^ 2 :=
      sq_le_sq' (neg_le_of_abs_le hdr) (le_of_abs_le hdr)
    have h1θ : 0 ≤ 1 + 1 / θ := by positivity
    have hpt : ∀ W : WIdx n d → ℝ, (VW P l' W - cstar) ^ 2 ≤
        (1 + θ) * (VW P l' W - Vb l') ^ 2 + (1 + 1 / θ) * b ^ 2 := by
      intro W
      have hy := young (VW P l' W - Vb l') (Vb l' - cstar) θ hθ
      have e : VW P l' W - cstar = (VW P l' W - Vb l') + (Vb l' - cstar) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hsq' h1θ
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
      _ = cVeE n k c1 cV cE β θ / n * L ^ 2 := by
          simp only [cVeE, hb]
          field_simp
  have hT2 : ∫⁻ W, ENNReal.ofReal (G2 (Real.sqrt (DW n d) • unitF53 W)) ∂stdGauss (WIdx n d) ≤
      ENNReal.ofReal (SE (2 * k) β ξ * (cVeE n k c1 cV cE β θ / n * L ^ 2) / Z) := by
    refine semi_transferE (ι := WIdx n d) (by omega) (fun s W => VW P s W - cstar) (2 * k) hC
      (fun s t W => by simp only [VW_smul]) ?_
      (fun s => (VW_meas k hn hPoly P hP s).sub_const _)
      lam β ξ (cVeE n k c1 cV cE β θ / n * L ^ 2) hβ hβ4 hξ hξ2 hξβ hν' hint2
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
  have hSS1 : 0 ≤ SE k β ξ :=
    (le_trans zero_le_one (SS_ge_one _ ξ)).trans (le_max_left _ _)
  have hSS2 : 0 ≤ SE (2 * k) β ξ :=
    (le_trans zero_le_one (SS_ge_one _ ξ)).trans (le_max_left _ _)
  have hcVe : 0 ≤ cVeE n k c1 cV cE β θ := by
    unfold cVeE
    have h1θ : 0 ≤ 1 + 1 / θ := by positivity
    have : 0 ≤ (n : ℝ) * DrFE n k c1 cE β ^ 2 := by positivity
    have := mul_nonneg h1θ this
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + θ) hcV
    linarith
  have ht1 : 0 ≤ SE k β ξ * c1 / (n * (ε ^ 2 * κ)) / Z := by positivity
  have ht2 : 0 ≤ SE (2 * k) β ξ * cVeE n k c1 cV cE β θ / (n * (1 - efl - κ) ^ 2) / Z := by
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
    have hp : pSE n d k c1 cV efl cE β ξ θ ε κ =
        SE k β ξ * c1 / (n * (ε ^ 2 * κ)) / Z +
          SE (2 * k) β ξ * cVeE n k c1 cV cE β θ / (n * (1 - efl - κ) ^ 2) / Z := by
      unfold pSE; rw [hZdef, add_div]
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

#print axioms BstLean.Part88.semiStepE
