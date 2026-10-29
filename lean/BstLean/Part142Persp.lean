import BstLean.Part133All

/-!
# Part 142: the distance form `Φ_G` and its Lipschitz bound

Role: `delegations/statements/p142-spec.md`, item 2 (sharper kernel bounds). New in this part
(not in the paper sources): the realized spread is bounded through the DISTANCE kernel
`D(u, u′) = (k(u, u) + k(u′, u′))/2 − k(u, u′)`. This file has the pointwise tools.

* `bG G = 1 − 2·G(0) + G(−1)`.
* `phiD G y y′ = (|y|² + |y′|²)/2 − Ψ_G(y, y′)`: the distance form.
* `perspD_abs`: for a reference point `(p, c)` with `0 ≤ c ≤ p` and a point `(p′, c′)` of the
  cone: `|(p′ − L_G(p′, c′)) − (p − L_G(p, c))| ≤ |(p′ − c′) − (p − c)| + bG G·|p′ − p|`.
* `phiD_abs_sub`, `phiD_L2_core`: the same for two vectors, pointwise and in `L²`.
* `delta_abs`, `delta_L2_core`: the term `(|y| − |y′|)²/2`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133

/-- `b_G = 1 − 2·G(0) + G(−1)`. -/
noncomputable def bG (G : ℝ → ℝ) : ℝ := 1 - 2 * G 0 + G (-1)

/-- The slope `g₀ = G(0) − G(−1)` of the chord of `G` on `[−1, 0]`. -/
lemma g0_mem {G : ℝ → ℝ} (hG : KGood G) : 0 ≤ G 0 - G (-1) ∧ G 0 - G (-1) ≤ 1 := by
  have h1 := hG.mono (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_refl _, by norm_num⟩)
    KGood.zero_mem (by norm_num)
  have h2 := hG.lip (t := -1) (s := 0) (le_refl _) (by norm_num) (by norm_num)
  constructor <;> linarith

/-- `G(s) ≥ G(0) + g₀·s` on `[0, 1]`. -/
lemma chord_right {G : ℝ → ℝ} (hG : KGood G) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    G 0 + (G 0 - G (-1)) * s ≤ G s := by
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hc := hG.conv.2 (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_refl _, by norm_num⟩)
    (show s ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hs1⟩)
    (show (0 : ℝ) ≤ s / (1 + s) by positivity) (show (0 : ℝ) ≤ 1 / (1 + s) by positivity)
    (by field_simp; ring)
  have e : (s / (1 + s)) • (-1 : ℝ) + (1 / (1 + s)) • s = 0 := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  have h2 : G 0 * (1 + s) ≤ s * G (-1) + G s := by
    have := mul_le_mul_of_nonneg_right hc h1s.le
    have e2 : (s / (1 + s) * G (-1) + 1 / (1 + s) * G s) * (1 + s) = s * G (-1) + G s := by
      field_simp
    linarith
  linarith

/-- `G(s) ≤ G(0) + g₀·s` on `[−1, 0]`. -/
lemma chord_left {G : ℝ → ℝ} (hG : KGood G) {s : ℝ} (hs0 : -1 ≤ s) (hs1 : s ≤ 0) :
    G s ≤ G 0 + (G 0 - G (-1)) * s := by
  have hc := hG.conv.2 (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨le_refl _, by norm_num⟩)
    KGood.zero_mem (show (0 : ℝ) ≤ -s by linarith) (show (0 : ℝ) ≤ 1 + s by linarith) (by ring)
  have e : (-s) • (-1 : ℝ) + (1 + s) • (0 : ℝ) = s := by
    simp only [smul_eq_mul]
    ring
  rw [e] at hc
  simp only [smul_eq_mul] at hc
  linarith

lemma bG_nonneg {G : ℝ → ℝ} (hG : KGood G) : 0 ≤ bG G := by
  have h := chord_right hG (s := 1) (by norm_num) (le_refl _)
  rw [hG.one] at h
  unfold bG
  linarith

lemma bG_le_one {G : ℝ → ℝ} (hG : KGood G) : bG G ≤ 1 := by
  have h0 := hG.nonneg_on KGood.zero_mem
  have h1 := (g0_mem hG).1
  unfold bG
  linarith

/-- One direction of `perspD_abs`: the reference point `(p, c)` has `0 ≤ c ≤ p`. -/
lemma perspD_upper {G : ℝ → ℝ} (hG : KGood G) {p c p' c' : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ p)
    (hp' : 0 ≤ p') (hc' : |c'| ≤ p') :
    (p' - persp G p' c') - (p - persp G p c) ≤ |(p' - c') - (p - c)| + bG G * |p' - p| := by
  have hp : 0 ≤ p := hc0.trans hc
  -- the reference cosine
  obtain ⟨τ, hτ0, hτ1, hcτ⟩ : ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ c = τ * p := by
    rcases eq_or_lt_of_le hp with h | h
    · refine ⟨0, le_refl _, zero_le_one, ?_⟩
      rw [← h] at hc ⊢
      linarith
    · exact ⟨c / p, div_nonneg hc0 hp, (div_le_one h).2 hc, by field_simp⟩
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ :=
    hG.support (show τ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, hτ1⟩)
  have h1 : persp G p c = a * p + b * c := persp_eq heq hcτ
  have h2 := persp_ge hab hp' hc'
  have hg := g0_mem hG
  have hab1 : a + b ≤ 1 := by
    have := hab 1 ⟨by norm_num, le_refl _⟩
    rw [hG.one] at this
    linarith
  have habm : a - b ≤ G (-1) := by
    have := hab (-1) ⟨le_refl _, by norm_num⟩
    linarith
  have hGτ := chord_right hG hτ0 hτ1
  -- `b ≥ g₀`
  have hbg : G 0 - G (-1) ≤ b := by nlinarith
  -- `a + b ≥ G(0) + g₀`
  have hlow : G 0 + (G 0 - G (-1)) ≤ a + b := by nlinarith
  have hι0 : 0 ≤ 1 - a - b := by linarith
  have hιb : 1 - a - b ≤ bG G := by unfold bG; linarith
  have hbb := bG_nonneg hG
  have e : (p' - (a * p' + b * c')) - (p - (a * p + b * c)) =
      (1 - a - b) * (p' - p) + b * ((p' - c') - (p - c)) := by ring
  have t1 : (1 - a - b) * (p' - p) ≤ bG G * |p' - p| := by
    calc (1 - a - b) * (p' - p) ≤ (1 - a - b) * |p' - p| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hι0
      _ ≤ bG G * |p' - p| := mul_le_mul_of_nonneg_right hιb (abs_nonneg _)
  have t2 : b * ((p' - c') - (p - c)) ≤ |(p' - c') - (p - c)| := by
    calc b * ((p' - c') - (p - c)) ≤ b * |(p' - c') - (p - c)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hb0
      _ ≤ 1 * |(p' - c') - (p - c)| := mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ = _ := one_mul _
  linarith

/-- **The Lipschitz bound of `π − L_G(π, c)`** in the variables `π − c` and `π`. The reference
point `(p, c)` has `0 ≤ c ≤ p`; the point `(p′, c′)` is any point of the cone `|c′| ≤ p′`. -/
lemma perspD_abs {G : ℝ → ℝ} (hG : KGood G) {p c p' c' : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ p)
    (hp' : 0 ≤ p') (hc' : |c'| ≤ p') :
    |(p' - persp G p' c') - (p - persp G p c)| ≤ |(p' - c') - (p - c)| + bG G * |p' - p| := by
  have hp : 0 ≤ p := hc0.trans hc
  have hg := g0_mem hG
  have hbb := bG_nonneg hG
  rw [abs_le]
  refine ⟨?_, perspD_upper hG hc0 hc hp' hc'⟩
  rcases le_or_gt 0 c' with h | h
  · -- exchange the two points
    have hc'p : c' ≤ p' := (le_abs_self _).trans hc'
    have habs : |c| ≤ p := by rw [abs_of_nonneg hc0]; exact hc
    have := perspD_upper hG h hc'p hp habs
    rw [abs_sub_comm (p - c), abs_sub_comm p] at this
    linarith
  · -- `c′ < 0`: the chord of `G` on `[−1, 0]`
    have hp'pos : 0 < p' := by
      rcases eq_or_lt_of_le hp' with h0 | h0
      · rw [← h0] at hc'
        have : c' = 0 := abs_nonpos_iff.mp hc'
        linarith
      · exact h0
    have hs := div_mem_Icc hp' hc'
    have hsneg : c' / p' ≤ 0 := (div_neg_of_neg_of_pos h hp'pos).le
    have hl := chord_left hG hs.1 hsneg
    have h1 : persp G p' c' ≤ G 0 * p' + (G 0 - G (-1)) * c' := by
      unfold persp
      have := mul_le_mul_of_nonneg_left hl hp'
      have e : p' * (G 0 + (G 0 - G (-1)) * (c' / p')) = G 0 * p' + (G 0 - G (-1)) * c' := by
        field_simp
      linarith
    have h2 : G 0 * p + (G 0 - G (-1)) * c ≤ persp G p c := by
      rcases eq_or_lt_of_le hp with h0 | h0
      · have hc00 : c = 0 := by rw [← h0] at hc; linarith
        rw [← h0, hc00]
        simp [persp]
      · unfold persp
        have hr := chord_right hG (div_nonneg hc0 hp) ((div_le_one h0).2 hc)
        have := mul_le_mul_of_nonneg_left hr hp
        have e : p * (G 0 + (G 0 - G (-1)) * (c / p)) = G 0 * p + (G 0 - G (-1)) * c := by
          field_simp
        linarith
    have e : (p' - (G 0 * p' + (G 0 - G (-1)) * c')) - (p - (G 0 * p + (G 0 - G (-1)) * c)) =
        bG G * (p' - p) + (G 0 - G (-1)) * ((p' - c') - (p - c)) := by
      unfold bG; ring
    have t1 : -(bG G * |p' - p|) ≤ bG G * (p' - p) := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le (p' - p)) hbb
      linarith
    have t2 : -|(p' - c') - (p - c)| ≤ (G 0 - G (-1)) * ((p' - c') - (p - c)) := by
      have h3 : -((G 0 - G (-1)) * |(p' - c') - (p - c)|) ≤
          (G 0 - G (-1)) * ((p' - c') - (p - c)) := by
        have := mul_le_mul_of_nonneg_left (neg_abs_le ((p' - c') - (p - c))) hg.1
        linarith
      have h4 : (G 0 - G (-1)) * |(p' - c') - (p - c)| ≤ 1 * |(p' - c') - (p - c)| :=
        mul_le_mul_of_nonneg_right hg.2 (abs_nonneg _)
      linarith
    linarith

/-! ## Two vectors -/

variable {ι : Type*} [Fintype ι]

/-- **The distance form** `Φ_G(y, y′) = (|y|² + |y′|²)/2 − Ψ_G(y, y′)`. For `G = id` it is
`|y − y′|²/2`; for unit vectors it is `1 − G(⟨y, y′⟩)`. -/
noncomputable def phiD (G : ℝ → ℝ) (y y' : ι → ℝ) : ℝ := (normSq y + normSq y') / 2 - psi G y y'

/-- `(|y|² + |y′|²)/2 − ⟨y, y′⟩ = |y − y′|²/2`. -/
noncomputable def eD (y y' : ι → ℝ) : ℝ := (normSq y + normSq y') / 2 - dotp y y'

/-- `(|y|² + |y′|²)/2 − |y||y′| = (|y| − |y′|)²/2`. -/
noncomputable def dlt (y y' : ι → ℝ) : ℝ := (normSq y + normSq y') / 2 - nrm y * nrm y'

lemma phiD_unit (G : ℝ → ℝ) {x x' : ι → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    phiD G x x' = 1 - G (dotp x x') := by
  unfold phiD
  rw [psi_unit G hx hx', hx, hx']
  norm_num

lemma eD_eq (y y' : ι → ℝ) : eD y y' = normSq (y - y') / 2 := by
  unfold eD normSq dotp
  have : ∀ i, (y - y') i ^ 2 = y i ^ 2 + y' i ^ 2 - 2 * (y i * y' i) := fun i => by
    simp only [Pi.sub_apply]; ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma eD_nonneg (y y' : ι → ℝ) : 0 ≤ eD y y' := by
  rw [eD_eq]
  have := normSq_nonneg (y - y')
  positivity

lemma dlt_nonneg (y y' : ι → ℝ) : 0 ≤ dlt y y' := by
  unfold dlt
  linarith [nrm_mul_le y y']

lemma dlt_eq (y y' : ι → ℝ) : dlt y y' = (nrm y - nrm y') ^ 2 / 2 := by
  unfold dlt
  rw [← nrm_sq y, ← nrm_sq y']
  ring

/-- **The Lipschitz bound of the distance form**, against a reference `(P, p̄, t)` with
`p̄ ≥ 0`, `0 ≤ t ≤ 1`: `|Φ_G(y, y′) − (P − p̄·G(t))| ≤
  |e − (P − p̄t)| + b_G·|p⁺ − P| + (2 + b_G)·|δ − (P − p̄)|`, with `e = |y − y′|²/2`,
`p⁺ = (|y|² + |y′|²)/2`, `δ = (|y| − |y′|)²/2`. -/
lemma phiD_abs_sub {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) {P pb t : ℝ} (hpb : 0 ≤ pb)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |phiD G y y' - (P - pb * G t)| ≤ |eD y y' - (P - pb * t)| +
      bG G * |(normSq y + normSq y') / 2 - P| + (2 + bG G) * |dlt y y' - (P - pb)| := by
  have hbb := bG_nonneg hG
  have h := perspD_abs hG (p := pb) (c := pb * t) (p' := nrm y * nrm y') (c' := dotp y y')
    (mul_nonneg hpb ht0) (by nlinarith) (nrm_mul_nonneg y y') (abs_dotp_le_nrm y y')
  rw [persp_mul, ← psi_eq_persp] at h
  set Pi0 := nrm y * nrm y' with hPi0
  set pp := (normSq y + normSq y') / 2 with hpp
  have e1 : phiD G y y' - (P - pb * G t) =
      (dlt y y' - (P - pb)) + ((Pi0 - psi G y y') - (pb - pb * G t)) := by
    unfold phiD dlt; ring
  have e2 : (Pi0 - dotp y y') - (pb - pb * t) =
      (eD y y' - (P - pb * t)) - (dlt y y' - (P - pb)) := by
    unfold eD dlt; ring
  have e3 : Pi0 - pb = (pp - P) - (dlt y y' - (P - pb)) := by
    unfold dlt; ring
  rw [e2, e3] at h
  rw [e1]
  have a1 := abs_add_le (dlt y y' - (P - pb)) ((Pi0 - psi G y y') - (pb - pb * G t))
  have a2 := abs_sub (eD y y' - (P - pb * t)) (dlt y y' - (P - pb))
  have a3 := abs_sub (pp - P) (dlt y y' - (P - pb))
  have a4 := mul_le_mul_of_nonneg_left a3 hbb
  nlinarith [abs_nonneg (dlt y y' - (P - pb))]

/-- **The Lipschitz bound of the distance form, second form**: against a reference `(P, p̄, t)`
with `0 ≤ p̄ ≤ P`, `0 ≤ t ≤ 1`: `|Φ_G(y, y′) − (P − p̄·G(t))| ≤
  |e − (P − p̄t)| + b_G·|p⁺ − P| + G(0)·(δ + (P − p̄))`, with `e = |y − y′|²/2`,
`p⁺ = (|y|² + |y′|²)/2`, `δ = (|y| − |y′|)²/2`. -/
lemma phiD_abs_sub2 {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) {P pb t : ℝ} (hpb : 0 ≤ pb)
    (hP : pb ≤ P) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |phiD G y y' - (P - pb * G t)| ≤ |eD y y' - (P - pb * t)| +
      bG G * |(normSq y + normSq y') / 2 - P| + G 0 * (dlt y y' + (P - pb)) := by
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  set Pi0 := nrm y * nrm y' with hPi0
  set pp := (normSq y + normSq y') / 2 with hpp
  set c := dotp y y' with hc
  have hPi00 : 0 ≤ Pi0 := nrm_mul_nonneg y y'
  have hcPi : |c| ≤ Pi0 := abs_dotp_le_nrm y y'
  have hPipp : Pi0 ≤ pp := nrm_mul_le y y'
  have hcpp : |c| ≤ pp := hcPi.trans hPipp
  have hpp0 : 0 ≤ pp := hPi00.trans hPipp
  have hP0 : 0 ≤ P := hpb.trans hP
  have hcb0 : 0 ≤ pb * t := mul_nonneg hpb ht0
  have hcbpb : pb * t ≤ pb := by nlinarith
  have hcbabs : |pb * t| ≤ pb := by rw [abs_of_nonneg hcb0]; exact hcbpb
  have hcbabsP : |pb * t| ≤ P := hcbabs.trans hP
  -- the main term
  have h1 := perspD_abs hG (p := P) (c := pb * t) (p' := pp) (c' := c) hcb0
    (hcbpb.trans hP) hpp0 hcpp
  -- the two corrections
  have h2a := persp_le hG hpp0 hcpp hPi00 hcPi
  have h2b := persp_le hG hPi00 hcPi hpp0 hcpp
  have h3a := persp_le hG hP0 hcbabsP hpb hcbabs
  have h3b := persp_le hG hpb hcbabs hP0 hcbabsP
  simp only [sub_self, abs_zero, add_zero] at h2a h2b h3a h3b
  rw [abs_of_nonneg (by linarith : 0 ≤ pp - Pi0)] at h2a
  rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ pp - Pi0)] at h2b
  rw [abs_of_nonneg (by linarith : 0 ≤ P - pb)] at h3a
  rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ P - pb)] at h3b
  have e1 : phiD G y y' - (P - pb * G t) =
      ((pp - persp G pp c) - (P - persp G P (pb * t))) + (persp G pp c - persp G Pi0 c) -
        (persp G P (pb * t) - persp G pb (pb * t)) := by
    unfold phiD
    rw [psi_eq_persp, persp_mul]
    ring
  have e2 : (pp - c) - (P - pb * t) = eD y y' - (P - pb * t) := by unfold eD; rfl
  have e3 : dlt y y' = pp - Pi0 := rfl
  rw [e2] at h1
  rw [e1, e3]
  have hA := abs_le.mp h1
  rw [abs_le]
  constructor
  · nlinarith [hA.1, mul_nonneg hG0 (by linarith : 0 ≤ pp - Pi0),
      mul_nonneg hG0 (by linarith : 0 ≤ P - pb)]
  · nlinarith [hA.2, mul_nonneg hG0 (by linarith : 0 ≤ pp - Pi0),
      mul_nonneg hG0 (by linarith : 0 ≤ P - pb)]

/-- The term `δ = (|y| − |y′|)²/2` against `(a₀ − b₀)²/2`, `a₀, b₀ > 0`. -/
lemma delta_abs (y y' : ι → ℝ) {a₀ b₀ : ℝ} (ha : 0 < a₀) (hb : 0 < b₀) :
    |dlt y y' - (a₀ - b₀) ^ 2 / 2| ≤
      (normSq y - a₀ ^ 2) ^ 2 / a₀ ^ 2 + (normSq y' - b₀ ^ 2) ^ 2 / b₀ ^ 2 +
        (|normSq y - a₀ ^ 2| / a₀ + |normSq y' - b₀ ^ 2| / b₀) * |a₀ - b₀| := by
  rw [dlt_eq]
  set x := nrm y with hx
  set x' := nrm y' with hx'
  have hx0 : 0 ≤ x := nrm_nonneg y
  have hx0' : 0 ≤ x' := nrm_nonneg y'
  have ex : normSq y = x ^ 2 := (nrm_sq y).symm
  have ex' : normSq y' = x' ^ 2 := (nrm_sq y').symm
  rw [ex, ex']
  -- `|x − a₀| ≤ |x² − a₀²|/a₀`
  have hu : |x - a₀| ≤ |x ^ 2 - a₀ ^ 2| / a₀ := by
    rw [le_div_iff₀ ha]
    have e : x ^ 2 - a₀ ^ 2 = (x - a₀) * (x + a₀) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x + a₀)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have hw : |x' - b₀| ≤ |x' ^ 2 - b₀ ^ 2| / b₀ := by
    rw [le_div_iff₀ hb]
    have e : x' ^ 2 - b₀ ^ 2 = (x' - b₀) * (x' + b₀) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x' + b₀)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  set U := |x ^ 2 - a₀ ^ 2| / a₀ with hU
  set W := |x' ^ 2 - b₀ ^ 2| / b₀ with hW
  have hU0 : 0 ≤ U := by positivity
  have hW0 : 0 ≤ W := by positivity
  have eU : (x ^ 2 - a₀ ^ 2) ^ 2 / a₀ ^ 2 = U ^ 2 := by
    rw [hU, div_pow, sq_abs]
  have eW : (x' ^ 2 - b₀ ^ 2) ^ 2 / b₀ ^ 2 = W ^ 2 := by
    rw [hW, div_pow, sq_abs]
  rw [eU, eW]
  set u := x - a₀ with hu'
  set w := x' - b₀ with hw'
  have e : (x - x') ^ 2 / 2 - (a₀ - b₀) ^ 2 / 2 = (u - w) ^ 2 / 2 + (u - w) * (a₀ - b₀) := by
    rw [hu', hw']; ring
  rw [e]
  have huw : |u - w| ≤ U + W := (abs_sub u w).trans (add_le_add hu hw)
  have h1 : (u - w) ^ 2 / 2 ≤ U ^ 2 + W ^ 2 := by
    have : (u - w) ^ 2 ≤ (U + W) ^ 2 := by
      rw [← sq_abs (u - w)]
      exact pow_le_pow_left₀ (abs_nonneg _) huw 2
    nlinarith [sq_nonneg (U - W)]
  have h2 : |(u - w) * (a₀ - b₀)| ≤ (U + W) * |a₀ - b₀| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right huw (abs_nonneg _)
  have h3 : 0 ≤ (u - w) ^ 2 / 2 := by positivity
  calc |(u - w) ^ 2 / 2 + (u - w) * (a₀ - b₀)|
      ≤ |(u - w) ^ 2 / 2| + |(u - w) * (a₀ - b₀)| := abs_add_le _ _
    _ ≤ U ^ 2 + W ^ 2 + (U + W) * |a₀ - b₀| := by
        rw [abs_of_nonneg h3]; linarith

/-! ## The `L²` forms -/

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma L2le.abs' {f : Ω → ℝ} {a : ℝ} (h : L2le μ f a) : L2le μ (fun ω => |f ω|) a :=
  L2le.of_abs_le (continuous_abs.comp_aestronglyMeasurable h.aesm) h
    (fun ω => le_of_eq (abs_abs _))

/-- **From `L²` bounds of `e`, `p⁺`, `δ` to an `L²` bound of the distance form.** -/
lemma phiD_L2_core {G : ℝ → ℝ} (hG : KGood G) {Y Y' : Ω → ι → ℝ}
    (hm : AEStronglyMeasurable (fun ω => phiD G (Y ω) (Y' ω)) μ) {P pb t ae ap ad : ℝ}
    (hpb : 0 ≤ pb) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hE : L2le μ (fun ω => eD (Y ω) (Y' ω) - (P - pb * t)) ae)
    (hP : L2le μ (fun ω => (normSq (Y ω) + normSq (Y' ω)) / 2 - P) ap)
    (hD : L2le μ (fun ω => dlt (Y ω) (Y' ω) - (P - pb)) ad)
    (hae : 0 ≤ ae) (hap : 0 ≤ ap) (had : 0 ≤ ad) :
    L2le μ (fun ω => phiD G (Y ω) (Y' ω) - (P - pb * G t))
      (ae + bG G * ap + (2 + bG G) * ad) := by
  have hbb := bG_nonneg hG
  have h1 := (L2le.abs' hE).add0 ((L2le.abs' hP).const_mul_nonneg hbb) hae
    (mul_nonneg hbb hap)
  have h2 := h1.add0 ((L2le.abs' hD).const_mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + bG G))
    (by positivity) (by positivity)
  refine L2le.of_abs_le (hm.sub aestronglyMeasurable_const) h2 (fun ω => ?_)
  exact (phiD_abs_sub hG (Y ω) (Y' ω) hpb ht0 ht1).trans (le_abs_self _)

/-- **From `L²` bounds of `e`, `p⁺`, `δ` to an `L²` bound of the distance form, second form.**
-/
lemma phiD_L2_core2 {G : ℝ → ℝ} (hG : KGood G) {Y Y' : Ω → ι → ℝ}
    (hm : AEStronglyMeasurable (fun ω => phiD G (Y ω) (Y' ω)) μ) {P pb t ae ap ad : ℝ}
    (hpb : 0 ≤ pb) (hPb : pb ≤ P) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hE : L2le μ (fun ω => eD (Y ω) (Y' ω) - (P - pb * t)) ae)
    (hP : L2le μ (fun ω => (normSq (Y ω) + normSq (Y' ω)) / 2 - P) ap)
    (hD : L2le μ (fun ω => dlt (Y ω) (Y' ω) + (P - pb)) ad)
    (hae : 0 ≤ ae) (hap : 0 ≤ ap) (had : 0 ≤ ad) :
    L2le μ (fun ω => phiD G (Y ω) (Y' ω) - (P - pb * G t))
      (ae + bG G * ap + G 0 * ad) := by
  have hbb := bG_nonneg hG
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have h1 := (L2le.abs' hE).add0 ((L2le.abs' hP).const_mul_nonneg hbb) hae
    (mul_nonneg hbb hap)
  have h2 := h1.add0 (hD.const_mul_nonneg hG0) (by positivity) (by positivity)
  refine L2le.of_abs_le (hm.sub aestronglyMeasurable_const) h2 (fun ω => ?_)
  exact (phiD_abs_sub2 hG (Y ω) (Y' ω) hpb hPb ht0 ht1).trans (le_abs_self _)

/-- **The term `δ` in `L²`**, from second and fourth central moments of the two squared norms:
`‖δ − (a₀ − b₀)²/2‖₂ ≤ c₄/a₀² + c₄′/b₀² + (c₂/a₀ + c₂′/b₀)·|a₀ − b₀|`. -/
lemma delta_L2_core {Y Y' : Ω → ι → ℝ}
    (hm : AEStronglyMeasurable (fun ω => dlt (Y ω) (Y' ω)) μ) {a₀ b₀ c2 c2' c4 c4' : ℝ}
    (ha : 0 < a₀) (hb : 0 < b₀)
    (h2 : L2le μ (fun ω => normSq (Y ω) - a₀ ^ 2) c2)
    (h2' : L2le μ (fun ω => normSq (Y' ω) - b₀ ^ 2) c2')
    (h4 : L2le μ (fun ω => (normSq (Y ω) - a₀ ^ 2) ^ 2) c4)
    (h4' : L2le μ (fun ω => (normSq (Y' ω) - b₀ ^ 2) ^ 2) c4')
    (hc2 : 0 ≤ c2) (hc2' : 0 ≤ c2') (hc4 : 0 ≤ c4) (hc4' : 0 ≤ c4') :
    L2le μ (fun ω => dlt (Y ω) (Y' ω) - (a₀ - b₀) ^ 2 / 2)
      (c4 / a₀ ^ 2 + c4' / b₀ ^ 2 + (c2 / a₀ + c2' / b₀) * |a₀ - b₀|) := by
  have k4 := (h4.const_mul_nonneg (c := 1 / a₀ ^ 2) (by positivity))
  have k4' := (h4'.const_mul_nonneg (c := 1 / b₀ ^ 2) (by positivity))
  have k2 := ((L2le.abs' h2).const_mul_nonneg (c := 1 / a₀) (by positivity))
  have k2' := ((L2le.abs' h2').const_mul_nonneg (c := 1 / b₀) (by positivity))
  have s1 := k4.add0 k4' (by positivity) (by positivity)
  have s2 := (k2.add0 k2' (by positivity) (by positivity)).const_mul_nonneg
    (c := |a₀ - b₀|) (abs_nonneg _)
  have s3 := s1.add0 s2 (by positivity) (by positivity)
  refine (L2le.of_abs_le (hm.sub aestronglyMeasurable_const) s3 (fun ω => ?_)).congr_bound
    (by ring)
  have hd := delta_abs (Y ω) (Y' ω) ha hb
  change |dlt (Y ω) (Y' ω) - (a₀ - b₀) ^ 2 / 2| ≤ _
  refine (hd.trans (le_of_eq ?_)).trans (le_abs_self _)
  ring

end L2

end BstLean.Part142

open BstLean.Part142 in
#print axioms perspD_abs
open BstLean.Part142 in
#print axioms phiD_abs_sub
open BstLean.Part142 in
#print axioms phiD_L2_core
open BstLean.Part142 in
#print axioms delta_L2_core
open BstLean.Part142 in
#print axioms phiD_L2_core2
