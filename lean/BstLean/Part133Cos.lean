import BstLean.Part133Four

/-!
# Part 133, link `W₃`: the cosine after one Gaussian matrix and the normalization, in `L²`

Role: `delegations/statements/p133-spec.md`. Paper source: `onW4c-cx.md` §4, "Link `W_3`"
(T4(8)). The Lean proof is NOT the paper's proof: it uses no inverse moment of a chi-square
variable. It uses the pointwise bound `cos_pt` and the second and fourth central moments of
`|M w|²`.

* `L2le.add'`: the triangle inequality in `L²` with bounds `0 ≤ a`, `0 ≤ b`.
* `cos_pt`: for `a, b ≥ 0`, `|τ| ≤ 1`, `|T| ≤ 1`, `T = c/(a·b)` if `a·b > 0`:
  `|T − τ| ≤ |E| + E² + (17/4)·((a² − 1)² + (b² − 1)²)`, `E = c − τ·(a² + b²)/2`.
* **`lin_cos_L2`**: for nonzero `h, h'` and an `n × k` Gaussian matrix `M` of entry variance
  `v > 0`: the `L²` norm of `⟨sphPt (M h), sphPt (M h')⟩ − cos(h, h')` is at most
  `(1 − cos²(h, h'))/√n + (19/2)·√(12 + 48/n)/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part133

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part130 BstLean.Part131 BstLean.Part132

variable {n k : ℕ}

/-! ## The triangle inequality with bounds that may be zero -/

/-- **The triangle inequality in `L²`**, for bounds `0 ≤ a`, `0 ≤ b`. -/
theorem L2le.add' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {a b : ℝ}
    (hf : L2le μ f a) (hg : L2le μ g b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    L2le μ (fun ω => f ω + g ω) (a + b) := by
  have key : ∀ ε : ℝ, 0 < ε → L2le μ (fun ω => f ω + g ω) (a + ε + (b + ε)) := fun ε hε =>
    (hf.mono ha (by linarith)).add (hg.mono hb (by linarith)) (by linarith) (by linarith)
  refine ⟨(key 1 one_pos).aesm, (key 1 one_pos).int_sq, ?_⟩
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hd : 0 < 4 * (a + b) + 4 := by linarith
  set ε := min 1 (δ / (4 * (a + b) + 4)) with hε
  have hε0 : 0 < ε := lt_min one_pos (div_pos hδ hd)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε * (4 * (a + b) + 4) ≤ δ := by
    have : ε ≤ δ / (4 * (a + b) + 4) := min_le_right _ _
    rwa [le_div_iff₀ hd] at this
  have := (key ε hε0).le
  nlinarith

/-! ## The pointwise bound -/

lemma fin_arith {t e D m Q : ℝ} (hm0 : 0 ≤ m) (hDm : D ≤ m)
    (hDQ : D ≤ Q) (hmQ : m ^ 2 ≤ Q) (hmain : t ≤ (e + D) * (1 + m) + 2 * m ^ 2) :
    t ≤ e + e ^ 2 + 17 / 4 * Q := by
  have h1 : e * m ≤ e ^ 2 + m ^ 2 / 4 := by nlinarith [sq_nonneg (e - m / 2)]
  have h2 : D * m ≤ m ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hDm) hm0]
  have e3 : (e + D) * (1 + m) = e + D + e * m + D * m := by ring
  linarith

lemma sqrt_dev {a : ℝ} (ha : 0 ≤ a) : (a - 1) ^ 2 ≤ (a ^ 2 - 1) ^ 2 := by
  have e : (a ^ 2 - 1) ^ 2 - (a - 1) ^ 2 = (a - 1) ^ 2 * (a ^ 2 + 2 * a) := by ring
  have := mul_nonneg (sq_nonneg (a - 1)) (by positivity : 0 ≤ a ^ 2 + 2 * a)
  linarith

/-- `|1 − a·b| ≤ m` if `|a² − 1| ≤ m` and `|b² − 1| ≤ m` (`a, b ≥ 0`). -/
lemma one_sub_mul_le {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : |a ^ 2 - 1| ≤ m)
    (hw : |b ^ 2 - 1| ≤ m) : |1 - a * b| ≤ m := by
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (a - b)]
  · by_contra hcon
    have hcon' : a * b < 1 - m := by linarith [not_le.mp hcon]
    have h1m : 0 < 1 - m := lt_of_le_of_lt (mul_nonneg ha hb) hcon'
    have ha2 : 1 - m ≤ a ^ 2 := by linarith
    have hb2 : 1 - m ≤ b ^ 2 := by linarith
    have h3 : (1 - m) * (1 - m) ≤ a ^ 2 * b ^ 2 := mul_le_mul ha2 hb2 h1m.le (sq_nonneg a)
    have hpp : (a * b) * (a * b) < (1 - m) * (1 - m) :=
      mul_lt_mul'' hcon' hcon' (mul_nonneg ha hb) (mul_nonneg ha hb)
    have e : a ^ 2 * b ^ 2 = (a * b) * (a * b) := by ring
    linarith

/-- `(a − b)²/2 ≤ m` if `|a² − 1| ≤ m` and `|b² − 1| ≤ m` (`a, b ≥ 0`). -/
lemma half_sq_sub_le {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : |a ^ 2 - 1| ≤ m)
    (hw : |b ^ 2 - 1| ≤ m) : (a - b) ^ 2 / 2 ≤ m := by
  have hab : |a - b| ≤ a + b := abs_le.2 ⟨by linarith, by linarith⟩
  have h1 : (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
      abs_of_nonneg (add_nonneg ha hb), ← sq_abs (a - b), sq]
    exact mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  have h2 : |a ^ 2 - b ^ 2| ≤ |a ^ 2 - 1| + |b ^ 2 - 1| := by
    have := abs_sub (a ^ 2 - 1) (b ^ 2 - 1)
    rwa [show a ^ 2 - 1 - (b ^ 2 - 1) = a ^ 2 - b ^ 2 by ring] at this
  linarith

/-- The pointwise bound of a cosine `T = c/(a·b)` against a reference `τ`; `a`, `b` are the two
normalized norms. It holds at `a·b = 0` too. -/
lemma cos_pt {a b c τ T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : |τ| ≤ 1)
    (hT : |T| ≤ 1) (hTeq : 0 < a * b → T = c / (a * b)) :
    |T - τ| ≤ |c - τ * ((a ^ 2 + b ^ 2) / 2)| + (c - τ * ((a ^ 2 + b ^ 2) / 2)) ^ 2 +
      17 / 4 * ((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) := by
  obtain ⟨E, hE⟩ : ∃ E, E = c - τ * ((a ^ 2 + b ^ 2) / 2) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2 := ⟨_, rfl⟩
  rw [← hE, ← hQ]
  have hT2 : |T - τ| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hE0 := abs_nonneg E
  have hE2 := sq_nonneg E
  have hEE : |E| ^ 2 = E ^ 2 := sq_abs E
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | hp
  · have hQ1 : 1 ≤ Q := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · rw [hQ, h]; nlinarith [sq_nonneg (b ^ 2 - 1)]
      · rw [hQ, h]; nlinarith [sq_nonneg (a ^ 2 - 1)]
    linarith
  · obtain ⟨p, hpdef⟩ : ∃ p, p = a * b := ⟨_, rfl⟩
    rw [← hpdef] at hp hTeq
    have hp0 : p ≠ 0 := hp.ne'
    have hTp : (T - τ) * p = c - τ * p := by
      rw [hTeq hp]; field_simp
    have key : T - τ = (c - τ * p) * (2 - p) + (T - τ) * (1 - p) ^ 2 := by
      linear_combination (2 - p) * hTp
    obtain ⟨m, hm⟩ : ∃ m, m = max |a ^ 2 - 1| |b ^ 2 - 1| := ⟨_, rfl⟩
    have hu : |a ^ 2 - 1| ≤ m := hm ▸ le_max_left _ _
    have hw : |b ^ 2 - 1| ≤ m := hm ▸ le_max_right _ _
    have hm0 : 0 ≤ m := (abs_nonneg _).trans hu
    have hmQ : m ^ 2 ≤ Q := by
      rcases max_cases |a ^ 2 - 1| |b ^ 2 - 1| with h | h
      · rw [hm, h.1, sq_abs, hQ]; linarith [sq_nonneg (b ^ 2 - 1)]
      · rw [hm, h.1, sq_abs, hQ]; linarith [sq_nonneg (a ^ 2 - 1)]
    have h1p : |1 - p| ≤ m := hpdef ▸ one_sub_mul_le ha hb hu hw
    obtain ⟨D, hD⟩ : ∃ D, D = (a - b) ^ 2 / 2 := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hDm : D ≤ m := hD ▸ half_sq_sub_le ha hb hu hw
    have hDQ : D ≤ Q := by
      have h1 := sqrt_dev ha
      have h2 := sqrt_dev hb
      have e3 : 2 * (a - 1) ^ 2 + 2 * (b - 1) ^ 2 - (a - b) ^ 2 = (a + b - 2) ^ 2 := by ring
      have := sq_nonneg (a + b - 2)
      rw [hD, hQ]; linarith
    have hcτ : |c - τ * p| ≤ |E| + D := by
      have e : c - τ * p = E + τ * D := by rw [hE, hD, hpdef]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hD0]
      have := mul_le_of_le_one_left hD0 hτ
      linarith
    have h2p : |2 - p| ≤ 1 + m := by
      have := abs_add_le (1 : ℝ) (1 - p)
      rw [show (1 : ℝ) + (1 - p) = 2 - p by ring, abs_one] at this
      linarith
    have h1p2 : (1 - p) ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs (1 - p)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1p 2
    have hmain : |T - τ| ≤ (|E| + D) * (1 + m) + 2 * m ^ 2 := by
      have i1 : |c - τ * p| * |2 - p| ≤ (|E| + D) * (1 + m) :=
        mul_le_mul hcτ h2p (abs_nonneg _) (by linarith)
      have i2 : |T - τ| * (1 - p) ^ 2 ≤ 2 * m ^ 2 :=
        mul_le_mul hT2 h1p2 (sq_nonneg _) (by norm_num)
      have i3 : |T - τ| ≤ |c - τ * p| * |2 - p| + |T - τ| * (1 - p) ^ 2 := by
        conv_lhs => rw [key]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (1 - p))]
      linarith
    have := fin_arith (e := |E|) hm0 hDm hDQ hmQ hmain
    rw [hEE] at this
    exact this

/-! ## The `L²` norms of the three terms -/

lemma measurable_normSq_mulVec (w : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin n) (Fin k) ℝ => normSq (M.mulVec w)) :=
  measurable_normSq.comp (measurable_mulVec_right w)

lemma measurable_dotp_mulVec (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin n) (Fin k) ℝ => dotp (M.mulVec h) (M.mulVec h')) :=
  measurable_dotp_comp (measurable_mulVec_right h) (measurable_mulVec_right h')

/-- The square of the normalized deviation of `|M w|²` has `L²` norm `|w|⁴·√(12 + 48/n)/n`. -/
lemma dev_sq_L2 {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (w : Fin k → ℝ) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        ((normSq (M.mulVec w) - (n : ℝ) * (v * normSq w)) / ((n : ℝ) * v)) ^ 2)
      (normSq w ^ 2 * (√(12 + 48 / (n : ℝ)) / (n : ℝ))) := by
  obtain ⟨hi, he⟩ := lin_sq_four (m := n) hv.le w
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      (((normSq (M.mulVec w) - (n : ℝ) * (v * normSq w)) / ((n : ℝ) * v)) ^ 2) ^ 2 =
        (normSq (M.mulVec w) - (n : ℝ) * (v * normSq w)) ^ 4 / ((n : ℝ) * v) ^ 4 := fun M => by
    ring
  refine L2le.mk' ?_ ?_ ?_
  · exact ((((measurable_normSq_mulVec w).sub_const _).div_const _).pow_const 2).aestronglyMeasurable
  · simp only [e]
    exact hi.div_const _
  · simp only [e]
    have hsq : (√(12 + 48 / (n : ℝ))) ^ 2 = 12 + 48 / (n : ℝ) := Real.sq_sqrt (by positivity)
    have e2 : (normSq w ^ 2 * (√(12 + 48 / (n : ℝ)) / (n : ℝ))) ^ 2 =
        normSq w ^ 4 * ((12 + 48 / (n : ℝ)) / (n : ℝ) ^ 2) := by
      rw [mul_pow, div_pow, hsq]; ring
    rw [integral_div, he, e2]
    apply le_of_eq
    field_simp

/-- The normalized `c − τ·p⁺` has `L²` norm `(1 − τ²)/√n`. -/
lemma ctp_L2 {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ} (hh : normSq h = 1)
    (hh' : normSq h' = 1) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ => (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) / ((n : ℝ) * v))
      ((1 - dotp h h' ^ 2) / √(n : ℝ)) := by
  obtain ⟨hi, he⟩ := lin_ctp_var (m := n) hv.le hh hh'
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      ((dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) / ((n : ℝ) * v)) ^ 2 =
      (dotp (M.mulVec h) (M.mulVec h') -
        dotp h h' * ((normSq (M.mulVec h) + normSq (M.mulVec h')) / 2)) ^ 2 / ((n : ℝ) * v) ^ 2 :=
    fun M => by ring
  refine L2le.mk' ?_ ?_ ?_
  · exact (((measurable_dotp_mulVec h h').sub (((measurable_normSq_mulVec h).add
      (measurable_normSq_mulVec h')).div_const _ |>.const_mul _)).div_const _).aestronglyMeasurable
  · simp only [e]
    exact hi.div_const _
  · simp only [e]
    rw [integral_div, he, div_pow, Real.sq_sqrt hn0.le]
    apply le_of_eq
    field_simp

lemma normSq_add_eq {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (a + b) = normSq a + normSq b + 2 * dotp a b := by
  have h1 := polar a b
  have h2 := parallelogram a b
  linarith

lemma normSq_sub_eq {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (a - b) = normSq a + normSq b - 2 * dotp a b := by
  have h1 := polar a b
  have h2 := parallelogram a b
  linarith

/-! ## The unit case -/

theorem lin_cos_unit_L2 {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - dotp h h')
      ((1 - dotp h h' ^ 2) / √(n : ℝ) + 19 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set τ := dotp h h' with hτdef
  set s := (n : ℝ) * v with hs
  have hs0 : 0 < s := mul_pos hn0 hv
  set K := √(12 + 48 / (n : ℝ)) / (n : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hτ : |τ| ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rwa [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
  have hτ' := abs_le.mp hτ
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have ha1 : 0 ≤ (1 - τ ^ 2) / √(n : ℝ) := by positivity
  -- the three functions
  have hE : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2))
      ((1 - τ ^ 2) / √(n : ℝ)) :=
    (ctp_L2 hv hn hh hh').congr_fun fun M => by
      rw [← hs, ← hτdef]
      field_simp
  have hEabs := L2le.of_abs_le hE.aesm.norm hE (fun M => by
    simp only [Real.norm_eq_abs, abs_abs]; exact le_refl _)
  -- the square of the first function
  have nP : normSq (h + h') = 2 + 2 * τ := by rw [normSq_add_eq, hh, hh']; ring
  have nM : normSq (h - h') = 2 - 2 * τ := by rw [normSq_sub_eq, hh, hh']; ring
  have hP : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) ^ 2) ((2 + 2 * τ) ^ 2 * K) := by
    have := dev_sq_L2 hv hn (h + h')
    rw [nP, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; rw [hs]; field_simp
  have hMi : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ)) ^ 2) ((2 - 2 * τ) ^ 2 * K) := by
    have := dev_sq_L2 hv hn (h - h')
    rw [nM, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; rw [hs]; field_simp
  have hg := (hP.const_mul_nonneg (c := (1 - τ) ^ 2 / 8) (by positivity)).add'
    (hMi.const_mul_nonneg (c := (1 + τ) ^ 2 / 8) (by positivity)) (by positivity) (by positivity)
  have hE2 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) ^ 2) K := by
    have hE2' := L2le.of_abs_le (hE.aesm.pow 2) hg (fun M => ?_)
    · refine hE2'.mono (by positivity) ?_
      have : (1 - τ) ^ 2 / 8 * ((2 + 2 * τ) ^ 2 * K) + (1 + τ) ^ 2 / 8 * ((2 - 2 * τ) ^ 2 * K) =
          (1 - τ ^ 2) ^ 2 * K := by ring
      rw [this]
      have h1 : (1 - τ ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg τ]
      nlinarith
    · obtain ⟨x, hx⟩ : ∃ x, x = normSq (M.mulVec (h + h')) / s - (2 + 2 * τ) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, y = normSq (M.mulVec (h - h')) / s - (2 - 2 * τ) := ⟨_, rfl⟩
      have e : dotp (M.mulVec h) (M.mulVec h') / s -
          τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2) =
          ((1 - τ) * x - (1 + τ) * y) / 4 := by
        rw [hx, hy, Matrix.mulVec_add, Matrix.mulVec_sub, normSq_add_eq, normSq_sub_eq]
        field_simp
        ring
      show |(dotp (M.mulVec h) (M.mulVec h') / s -
          τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) ^ 2| ≤
        |(1 - τ) ^ 2 / 8 * (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) ^ 2 +
          (1 + τ) ^ 2 / 8 * (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ)) ^ 2|
      rw [abs_of_nonneg (sq_nonneg _), e, ← hx, ← hy]
      refine le_trans ?_ (le_abs_self _)
      have e2 : (1 - τ) ^ 2 / 8 * x ^ 2 + (1 + τ) ^ 2 / 8 * y ^ 2 -
          (((1 - τ) * x - (1 + τ) * y) / 4) ^ 2 = (((1 - τ) * x + (1 + τ) * y) / 4) ^ 2 := by
        ring
      have := sq_nonneg (((1 - τ) * x + (1 + τ) * y) / 4)
      linarith
  -- Q
  have hA : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hn h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hn h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hQ := hA.add' hB hK0 hK0
  have htot := (hEabs.add' hE2 ha1 hK0).add' (hQ.const_mul_nonneg (c := 17 / 4) (by norm_num))
    (by positivity) (by positivity)
  have hmeas : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) (gaussMat n k v) :=
    ((measurable_dotp_sphPt h h').sub_const _).aestronglyMeasurable
  refine (L2le.of_abs_le hmeas htot (fun M => ?_)).congr_bound (by rw [hK]; ring)
  -- the pointwise bound
  have hX0 : 0 ≤ normSq (M.mulVec h) := normSq_nonneg _
  have hY0 : 0 ≤ normSq (M.mulVec h') := normSq_nonneg _
  have hsqpos : 0 < √s := Real.sqrt_pos.mpr hs0
  have hab : √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) =
      nrm (M.mulVec h) * nrm (M.mulVec h') / s := by
    rw [Real.sqrt_div hX0, Real.sqrt_div hY0]
    unfold nrm
    field_simp
    rw [Real.sq_sqrt hs0.le]; ring
  have hCle := abs_dotp_le_nrm (M.mulVec h) (M.mulVec h')
  have hc : |dotp (M.mulVec h) (M.mulVec h') / s| ≤
      √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) := by
    rw [hab, abs_div, abs_of_pos hs0]
    exact div_le_div_of_nonneg_right hCle hs0.le
  have hT : |dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))| ≤ 1 :=
    abs_le.2 ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
  have hTeq : 0 < √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) →
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) = dotp (M.mulVec h) (M.mulVec h') / s /
        (√(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s)) := by
    intro hpos
    have hx : normSq (M.mulVec h) ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hy : normSq (M.mulVec h') ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, mul_zero] at hpos
      exact lt_irrefl _ hpos
    rw [dotp_sphPt _ _ hx hy, hab]
    have := (nrm_pos_of_ne hx).ne'
    have := (nrm_pos_of_ne hy).ne'
    field_simp
  have hpt := cos_pt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hτ hT hTeq
  rw [Real.sq_sqrt (div_nonneg hX0 hs0.le), Real.sq_sqrt (div_nonneg hY0 hs0.le)] at hpt
  exact hpt.trans (le_abs_self _)

/-! ## The general case -/

/-- **Link `W₃` in `L²`.** For nonzero `h, h'`, an `n × k` Gaussian matrix `M` with entry variance
`v > 0`: `‖⟨sphPt (M h), sphPt (M h')⟩ − cos(h, h')‖₂ ≤ (1 − cos²)/√n + (19/2)·√(12 + 48/n)/n`. -/
theorem lin_cos_L2 {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (h h' : Fin k → ℝ)
    (hh : normSq h ≠ 0) (hh' : normSq h' ≠ 0) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h')
      ((1 - cosv h h' ^ 2) / √(n : ℝ) + 19 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ)) := by
  have hp := nrm_pos_of_ne hh
  have hp' := nrm_pos_of_ne hh'
  set g : Fin k → ℝ := (1 / nrm h) • h with hg
  set g' : Fin k → ℝ := (1 / nrm h') • h' with hg'
  have hg1 : normSq g = 1 := by
    rw [hg, normSq_smul, ← nrm_sq h]; field_simp
  have hg1' : normSq g' = 1 := by
    rw [hg', normSq_smul, ← nrm_sq h']; field_simp
  have hcos : dotp g g' = cosv h h' := by
    rw [hg, hg', dotp_smul_smul]; unfold cosv; field_simp
  have e : h = nrm h • g := by
    rw [hg, smul_smul]; field_simp; simp
  have e' : h' = nrm h' • g' := by
    rw [hg', smul_smul]; field_simp; simp
  have key := lin_cos_unit_L2 (n := n) hv hn hg1 hg1'
  rw [hcos] at key
  refine key.congr_fun fun M => ?_
  have e1 : M.mulVec h = nrm h • M.mulVec g := by
    conv_lhs => rw [e]
    rw [Matrix.mulVec_smul]
  have e2 : M.mulVec h' = nrm h' • M.mulVec g' := by
    conv_lhs => rw [e']
    rw [Matrix.mulVec_smul]
  rw [e1, e2, sphPt_smul hp, sphPt_smul hp']

end BstLean.Part133

open BstLean.Part133 in
#print axioms cos_pt
open BstLean.Part133 in
#print axioms lin_cos_unit_L2
open BstLean.Part133 in
#print axioms lin_cos_L2
