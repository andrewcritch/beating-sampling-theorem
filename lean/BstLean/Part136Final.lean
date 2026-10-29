import BstLean.Part136Kern
import BstLean.Part136Kappa3

/-!
# Part 136, items 3 and 4: the size of the stand-in factor `λ₁` for the World network

Role: `delegations/statements/p136-spec.md`. The World network at the widths of the Focus:
`N = 2n` inputs, hidden width `m = mW n = ⌈n^{7/2}⌉`. `θ = (M₁, M₂)`, `h = hid2 M₁ M₂`,
`h̄ = hbar (uniformSphere (2n)) h`.

* `lam_num`: the frame bound `C/n` on the good event, from a polynomial model of `κ∘κ` and
  rational certificates.
* `good136 n`: the good event of `(M₁, M₂)`, with `p₁ = 0.0016`, `p₂ = 0.0004`.
* `good136_prob`: its probability is at least `0.998`; `good136_prob_W`: the same as an event of
  the whole World network.
* **`lamOne136`**: for every `n ≥ 4096`, on `good136 n`: `h̄ ≠ 0`, the hypothesis `hL` of
  Part 134 holds with `L = (99/100)/n`, and `lamOne ≤ (99/100)/n`.
  `lamOne136_8192`: `(17/25)/n` for `n ≥ 8192`; `lamOne136_16384`: `(13/25)/n` for `n ≥ 16384`.
  (The paper has `1.1764/n`, `0.7698/n`, `0.5628/n`.)
* `lamOne136_hs`: the simpler route (Hilbert–Schmidt bound of the whole remainder): `(43/25)/n`.
* **`standIn136`**, `standInVar136`: `s1_mse_mlp`, `s1_var_mlp` of Part 134 with this bound.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part136

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134

/-! ## Numbers -/

lemma sqrt6_le : √6 ≤ 24495 / 10000 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

lemma sqrt3_le : √3 ≤ 17321 / 10000 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- `(cF2o m)² ≤ 22.35/m` for `m ≥ 10⁶`. -/
lemma cF2o_sq_le {m : ℕ} (hm : 1000000 ≤ m) : cF2o m ^ 2 ≤ 2235 / 100 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have k1 := kappa_zero_le
  have k0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  have s6 := sqrt6_le
  have s60 : 0 ≤ √6 := Real.sqrt_nonneg _
  unfold cF2o
  rw [Real.sq_sqrt (by positivity)]
  have h1 : 5 / (m : ℝ) ≤ 5 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm'
  have h2 : (5 * kappa 0 + √6) ^ 2 ≤ (5 * (31831 / 100000) + 24495 / 10000) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  nlinarith

lemma mW_sq_ge (n : ℕ) : n ^ 7 ≤ mW n ^ 2 := (mW_le_iff n (mW n)).mp le_rfl

lemma mW_ge_million {n : ℕ} (hn : 4096 ≤ n) : 1000000 ≤ mW n := by
  by_contra h
  have h1 : mW n < 1000000 := by omega
  have h2 : mW n ^ 2 < 1000000 ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : 4096 ^ 7 ≤ n ^ 7 := Nat.pow_le_pow_left hn 7
  have h4 := mW_sq_ge n
  have h5 : (1000000 : ℕ) ^ 2 ≤ 4096 ^ 7 := by norm_num
  omega

/-- `n²/mW n ≤ r₀` if `1 ≤ r₀²·n₀³` and `n ≥ n₀`. -/
lemma ratio_le {n n0 : ℕ} (hn0 : 1 ≤ n0) (hn : n0 ≤ n) {r0 : ℝ} (hr0 : 0 ≤ r0)
    (hr : 1 ≤ r0 ^ 2 * (n0 : ℝ) ^ 3) : (n : ℝ) ^ 2 / (mW n : ℝ) ≤ r0 := by
  have hn0' : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hsq : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast mW_sq_ge n
  have hmpos : (0 : ℝ) < mW n := by
    have h7 : (0 : ℝ) < (n : ℝ) ^ 7 := by positivity
    have h2 : (0 : ℝ) < (mW n : ℝ) ^ 2 := lt_of_lt_of_le h7 hsq
    have h0 : (0 : ℝ) ≤ mW n := Nat.cast_nonneg _
    rcases h0.eq_or_lt with h | h
    · rw [← h] at h2; norm_num at h2
    · exact h
  have h3 : (n0 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hn' 3
  have key : ((n : ℝ) ^ 2 / (mW n : ℝ)) ^ 2 ≤ r0 ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have e : ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 3 = (n : ℝ) ^ 7 := by ring
    have h4 : (n : ℝ) ^ 7 ≤ r0 ^ 2 * (mW n : ℝ) ^ 2 * (n : ℝ) ^ 3 := by
      have h5 : (mW n : ℝ) ^ 2 ≤ r0 ^ 2 * (n : ℝ) ^ 3 * (mW n : ℝ) ^ 2 := by
        have : 1 ≤ r0 ^ 2 * (n : ℝ) ^ 3 :=
          hr.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
        nlinarith [sq_nonneg (mW n : ℝ)]
      nlinarith
    have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
    have : ((n : ℝ) ^ 2) ^ 2 * (n : ℝ) ^ 3 ≤ r0 ^ 2 * (mW n : ℝ) ^ 2 * (n : ℝ) ^ 3 := by
      rw [e]; exact h4
    exact le_of_mul_le_mul_right this hn3
  exact le_of_abs_le (abs_le_of_sq_le_sq key hr0)

/-- `n·√(15/(N(N+2)(N+4))) ≤ k₆` for `N = 2n`, `n ≥ n₀`, if `15/(8n₀) ≤ k₆²`. -/
lemma n_e6_le {x x0 k6 : ℝ} (hx0 : 0 < x0) (hx : x0 ≤ x) (hk60 : 0 ≤ k6)
    (hk6 : 15 / (8 * x0) ≤ k6 ^ 2) :
    x * √(15 / (2 * x * (2 * x + 2) * (2 * x + 4))) ≤ k6 := by
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hk60)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  refine le_trans ?_ hk6
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  have h8 : 8 * x ^ 3 ≤ 2 * x * (2 * x + 2) * (2 * x + 4) := by
    nlinarith [sq_nonneg x]
  have h3 : x ^ 2 * x0 ≤ x ^ 3 := by
    have := mul_le_mul_of_nonneg_left hx (sq_nonneg x)
    nlinarith
  nlinarith

/-! ## The frame bound from rational certificates -/

/-- **The frame bound `C/n` on the good event**, for every `n ≥ n₀ ≥ 4096`, from a polynomial
model of `κ∘κ` (`hmodel`) and rational certificates: `r₀ ≥ n₀^{−3/2}`, `k₀² ≥ 22.35·r₀`,
`k₆² ≥ 15/(8n₀)`, `D₀ = k₀/sp + η·(1.7321/2) + K₃·k₆` (a bound of `n·dK`), and the final
inequality `hC`. The first Markov probability is `p₁ = sp²`. -/
theorem lam_num {n n0 : ℕ} (hn0 : 4096 ≤ n0) (hn : n0 ≤ n)
    {b c2 η K₃ r0 k0 k6 sp ε₁ ε₂ s p₂ D0 C : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 3017 / 10000) (hc2 : 0 ≤ c2) (hη : 0 ≤ η) (hK₃ : 0 ≤ K₃)
    (hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - c2 * t ^ 2| ≤ η * t ^ 2 + K₃ * |t| ^ 3)
    (hr0 : 0 ≤ r0) (hr : 1 ≤ r0 ^ 2 * (n0 : ℝ) ^ 3)
    (hk0 : 0 ≤ k0) (hk : 2235 / 100 * r0 ≤ k0 ^ 2)
    (hk60 : 0 ≤ k6) (hk6 : 15 / (8 * (n0 : ℝ)) ≤ k6 ^ 2)
    (hsp : 0 < sp) (hp₂ : 0 < p₂) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hD0 : D0 = k0 / sp + η * (17321 / 20000) + K₃ * k6)
    (hDq : D0 / (n0 : ℝ) < 49372 / 100000)
    (hs : 0 < s)
    (hsle : s ≤ 1 - ε₁ - (49376 / 100000 + c2 / (2 * (n0 : ℝ)) + ε₂) ^ 2 /
      (49372 / 100000 - D0 / (n0 : ℝ)))
    (hC : (3017 / 20000 + c2 / (2 * (n0 : ℝ)) + D0) / s + D0 ^ 2 / ((n0 : ℝ) * ε₂ ^ 2) +
      2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2) ≤ C)
    {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHid (2 * n) (mW n) (sp ^ 2) p₂) :
    hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) ≠ 0 ∧ ∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) (hid2 θ.1 θ.2 u) j * w j) ^ 2
          ∂uniformSphere (2 * n) ≤ C / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn4 : 4096 ≤ n := hn0.trans hn
  have hn0' : (4096 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0pos : (0 : ℝ) < n0 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hcF := cF2o_pos hm
  have hcF2 := cF2o_sq_le hmM
  have hrat := ratio_le (by omega : 1 ≤ n0) hn hr0 hr
  have s3 := sqrt3_le
  have s30 : 0 ≤ √3 := Real.sqrt_nonneg _
  -- `n·cF2o ≤ k₀`
  have hncF : (n : ℝ) * cF2o (mW n) ≤ k0 := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hk0)
    rw [mul_pow]
    have h1 : (n : ℝ) ^ 2 * cF2o (mW n) ^ 2 ≤ (n : ℝ) ^ 2 * (2235 / 100 / (mW n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcF2 (sq_nonneg _)
    have e : (n : ℝ) ^ 2 * (2235 / 100 / (mW n : ℝ)) =
        2235 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
    rw [e] at h1
    have h2 : 2235 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) ≤ 2235 / 100 * r0 :=
      mul_le_mul_of_nonneg_left hrat (by norm_num)
    linarith
  have hne6 := n_e6_le hn0pos hn' hk60 hk6
  have hD0nn : 0 ≤ D0 := by rw [hD0]; positivity
  -- `dK ≤ D₀/n`
  have hsqrt : √(sp ^ 2) = sp := Real.sqrt_sq hsp.le
  have hdKn : dK (2 * n) (mW n) (sp ^ 2) η K₃ ≤ D0 / (n : ℝ) := by
    unfold dK
    rw [hsqrt, hNcast, le_div_iff₀ hnpos, hD0]
    have e : (cF2o (mW n) / sp + η * (√3 / (2 * (n : ℝ))) +
        K₃ * √(15 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 4)))) * (n : ℝ) =
        (n : ℝ) * cF2o (mW n) / sp + η * (√3 / 2) +
          K₃ * ((n : ℝ) * √(15 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 4)))) := by
      field_simp
    rw [e]
    have h1 : (n : ℝ) * cF2o (mW n) / sp ≤ k0 / sp := div_le_div_of_nonneg_right hncF hsp.le
    have h2 : η * (√3 / 2) ≤ η * (17321 / 20000) :=
      mul_le_mul_of_nonneg_left (by linarith) hη
    have h3 := mul_le_mul_of_nonneg_left hne6 hK₃
    linarith
  have hdK0 : 0 ≤ dK (2 * n) (mW n) (sp ^ 2) η K₃ := by unfold dK; positivity
  have hdKn0 : dK (2 * n) (mW n) (sp ^ 2) η K₃ ≤ D0 / (n0 : ℝ) :=
    hdKn.trans (div_le_div_of_nonneg_left hD0nn hn0pos hn')
  have hq0 : 0 < 49372 / 100000 - D0 / (n0 : ℝ) := by linarith
  have hc2n : c2 / ((2 * n : ℕ) : ℝ) ≤ c2 / (2 * (n0 : ℝ)) := by
    rw [hNcast]
    exact div_le_div_of_nonneg_left hc2 (by positivity) (by linarith)
  have hc2n0 : 0 ≤ c2 / ((2 * n : ℕ) : ℝ) := by positivity
  have hsle' : s ≤ 1 - ε₁ - (49376 / 100000 + c2 / ((2 * n : ℕ) : ℝ) + ε₂) ^ 2 /
      (49372 / 100000 - dK (2 * n) (mW n) (sp ^ 2) η K₃) := by
    have mono : (49376 / 100000 + c2 / ((2 * n : ℕ) : ℝ) + ε₂) ^ 2 /
        (49372 / 100000 - dK (2 * n) (mW n) (sp ^ 2) η K₃) ≤
        (49376 / 100000 + c2 / (2 * (n0 : ℝ)) + ε₂) ^ 2 / (49372 / 100000 - D0 / (n0 : ℝ)) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2) hq0
        (by linarith)
    linarith
  obtain ⟨g1, g2⟩ := frame_of_good hN hm (by positivity : (0 : ℝ) < sp ^ 2) hp₂ hε₁ hε₂
    hb0 hc2 hη hK₃ hmodel (lt_of_le_of_lt hdKn0 hDq) hs hsle' hθ
  refine ⟨g1, fun w => (g2 w).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _)
  rw [hNcast]
  -- the three terms
  have hnn : (n0 : ℝ) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hn' hnpos.le
  have t1 : (b / (2 * (n : ℝ)) + c2 * (2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2))) +
      dK (2 * n) (mW n) (sp ^ 2) η K₃) / s ≤
      (3017 / 20000 + c2 / (2 * (n0 : ℝ)) + D0) / s / (n : ℝ) := by
    rw [div_right_comm]
    refine div_le_div_of_nonneg_right ?_ hs.le
    rw [add_div, add_div]
    have h1 : b / (2 * (n : ℝ)) ≤ 3017 / 20000 / (n : ℝ) := by
      have e1 : b / (2 * (n : ℝ)) = b / 2 / (n : ℝ) := by rw [div_div]
      rw [e1]
      exact div_le_div_of_nonneg_right (by linarith) hnpos.le
    have h2 : c2 * (2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2))) ≤ c2 / (2 * (n0 : ℝ)) / (n : ℝ) := by
      have e2 : c2 / (2 * (n0 : ℝ)) / (n : ℝ) = c2 * (1 / (2 * (n0 : ℝ) * (n : ℝ))) := by
        rw [div_div, mul_one_div]
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ hc2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have t2 : dK (2 * n) (mW n) (sp ^ 2) η K₃ ^ 2 / ε₂ ^ 2 ≤
      D0 ^ 2 / ((n0 : ℝ) * ε₂ ^ 2) / (n : ℝ) := by
    have h1 : dK (2 * n) (mW n) (sp ^ 2) η K₃ ^ 2 ≤ (D0 / (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hdK0 hdKn 2
    have h2 : (D0 / (n : ℝ)) ^ 2 ≤ D0 ^ 2 / ((n0 : ℝ) * (n : ℝ)) := by
      rw [div_pow]
      refine div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
      rw [sq]
      exact hnn
    have e : D0 ^ 2 / ((n0 : ℝ) * ε₂ ^ 2) / (n : ℝ) =
        D0 ^ 2 / ((n0 : ℝ) * (n : ℝ)) / ε₂ ^ 2 := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (h1.trans h2) (by positivity)
  have t3 : cF2o (mW n) ^ 2 / p₂ / ε₁ ^ 2 ≤
      2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2) / (n : ℝ) := by
    have h1 : cF2o (mW n) ^ 2 ≤ 2235 / 100 * r0 / ((n0 : ℝ) * (n : ℝ)) := by
      refine hcF2.trans ?_
      have h2 : 1 / (mW n : ℝ) ≤ r0 / ((n0 : ℝ) * (n : ℝ)) := by
        have e : 1 / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / ((n : ℝ) * (n : ℝ)) := by
          field_simp
        rw [e]
        have h3 : (n : ℝ) ^ 2 / (mW n : ℝ) / ((n : ℝ) * (n : ℝ)) ≤ r0 / ((n : ℝ) * (n : ℝ)) :=
          div_le_div_of_nonneg_right hrat (by positivity)
        have h4 : r0 / ((n : ℝ) * (n : ℝ)) ≤ r0 / ((n0 : ℝ) * (n : ℝ)) :=
          div_le_div_of_nonneg_left hr0 (by positivity)
            (mul_le_mul_of_nonneg_right hn' hnpos.le)
        linarith
      have e1 : 2235 / 100 / (mW n : ℝ) = 2235 / 100 * (1 / (mW n : ℝ)) := by ring
      have e2 : 2235 / 100 * r0 / ((n0 : ℝ) * (n : ℝ)) =
          2235 / 100 * (r0 / ((n0 : ℝ) * (n : ℝ))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have e : 2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2) / (n : ℝ) =
        2235 / 100 * r0 / ((n0 : ℝ) * (n : ℝ)) / p₂ / ε₁ ^ 2 := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h1 hp₂.le) (by positivity)
  have hCn : ((3017 / 20000 + c2 / (2 * (n0 : ℝ)) + D0) / s + D0 ^ 2 / ((n0 : ℝ) * ε₂ ^ 2) +
      2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2)) / (n : ℝ) ≤ C / (n : ℝ) :=
    div_le_div_of_nonneg_right hC hnpos.le
  rw [add_div, add_div] at hCn
  linarith

/-! ## The good event at the widths of the Focus -/

/-- **The good event of `(M₁, M₂)`** for the World network of dimension `n`: `goodHid` with
`p₁ = (4/100)² = 0.0016` and `p₂ = 0.0004`. -/
def good136 (n : ℕ) : Set (HidParam (2 * n) (mW n)) :=
  goodHid (2 * n) (mW n) ((4 / 100) ^ 2) (4 / 10000)

theorem good136_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (good136 n) :=
  goodHid_meas (by omega) _ _

/-- The good event has probability at least `0.998`. -/
theorem good136_prob {n : ℕ} (hn : 4096 ≤ n) :
    998 / 1000 ≤ (hidGauss (2 * n) (mW n)).real (good136 n) := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have h := goodHid_prob (N := 2 * n) (m := mW n) (by omega) hm
    (by norm_num : (0 : ℝ) < (4 / 100) ^ 2) (by norm_num : (0 : ℝ) < 4 / 10000)
  unfold good136
  refine le_trans (by norm_num) h

/-- The good event as an event of the whole World network `W = (M₁, M₂, M₃)`. -/
theorem good136_prob_W {n : ℕ} (hn : 4096 ≤ n) :
    998 / 1000 ≤ (mlpGauss (2 * n) (mW n) n).real
      {W : MlpParam (2 * n) (mW n) n | (W.1, W.2.1) ∈ good136 n} := by
  have hmS := good136_meas (n := n) (by omega)
  have e : {W : MlpParam (2 * n) (mW n) n | (W.1, W.2.1) ∈ good136 n} =
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) ⁻¹' good136 n := rfl
  have hmap : (mlpGauss (2 * n) (mW n) n).map
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) = hidGauss (2 * n) (mW n) := by
    unfold mlpGauss hidGauss
    have h1 : (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) =
        Prod.map id Prod.fst := by
      funext W; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod]
    simp
  have hf : Measurable (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  rw [e, ← map_measureReal_apply hf hmS, hmap]
  exact good136_prob hn

/-! ## The headlines -/

/-- **Theorem S2 in Lean (item 3).** For every `n ≥ 4096`, on the good event of `(M₁, M₂)`
(probability at least `0.998`): `h̄ ≠ 0`, the unit residual directions have the frame bound
`(99/100)/n` (the hypothesis `hL` of Part 134), and `λ₁ ≤ (99/100)/n`. -/
theorem lamOne136 {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n) :
    hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) ≠ 0 ∧
    (∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) (hid2 θ.1 θ.2 u) j * w j) ^ 2
          ∂uniformSphere (2 * n) ≤ 99 / 100 / (n : ℝ) * ∑ j, w j ^ 2) ∧
    lamOne (uniformSphere (2 * n)) (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2))
      (hid2 θ.1 θ.2) ≤ 99 / 100 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  obtain ⟨h1, h2⟩ := lam_num (n := n) (n0 := 4096) le_rfl hn (b := b) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 1 / 262144) (k0 := 5771 / 625000) (k6 := 5349 / 250000)
    (sp := 4 / 100)
    (ε₁ := 37 / 1000) (ε₂ := 19 / 1000) (s := 10759 / 25000) (p₂ := 4 / 10000)
    (D0 := 4805289 / 20000000) (C := 99 / 100)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hθ
  exact ⟨h1, h2, lamOne_le _ _ _ (by positivity) h2⟩

/-- The same for `n ≥ 8192`, with the constant `17/25 = 0.68`. -/
theorem lamOne136_8192 {n : ℕ} (hn : 8192 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n) :
    hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) ≠ 0 ∧
    (∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) (hid2 θ.1 θ.2 u) j * w j) ^ 2
          ∂uniformSphere (2 * n) ≤ 17 / 25 / (n : ℝ) * ∑ j, w j ^ 2) ∧
    lamOne (uniformSphere (2 * n)) (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2))
      (hid2 θ.1 θ.2) ≤ 17 / 25 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : (8192 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  obtain ⟨h1, h2⟩ := lam_num (n := n) (n0 := 8192) (by norm_num) hn (b := b) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 1 / 741455) (k0 := 6863 / 1250000) (k6 := 15129 / 1000000)
    (sp := 4 / 100)
    (ε₁ := 24 / 1000) (ε₂ := 12 / 1000) (s := 45787 / 100000) (p₂ := 4 / 10000)
    (D0 := 2883553 / 20000000) (C := 17 / 25)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hθ
  exact ⟨h1, h2, lamOne_le _ _ _ (by positivity) h2⟩

/-- The same for `n ≥ 16384`, with the constant `13/25 = 0.52`. -/
theorem lamOne136_16384 {n : ℕ} (hn : 16384 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ good136 n) :
    hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) ≠ 0 ∧
    (∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) (hid2 θ.1 θ.2 u) j * w j) ^ 2
          ∂uniformSphere (2 * n) ≤ 13 / 25 / (n : ℝ) * ∑ j, w j ^ 2) ∧
    lamOne (uniformSphere (2 * n)) (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2))
      (hid2 θ.1 θ.2) ≤ 13 / 25 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : (16384 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  obtain ⟨h1, h2⟩ := lam_num (n := n) (n0 := 16384) (by norm_num) hn (b := b) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 1 / 2097152) (k0 := 16323 / 5000000) (k6 := 5349 / 500000)
    (sp := 4 / 100)
    (ε₁ := 15 / 1000) (ε₂ := 8 / 1000) (s := 9501 / 20000) (p₂ := 4 / 10000)
    (D0 := 347041 / 4000000) (C := 13 / 25)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hθ
  exact ⟨h1, h2, lamOne_le _ _ _ (by positivity) h2⟩

/-- **The simpler route** (no quadratic feature, no cubic bound of `κ∘κ`: the model
`0 ≤ κ(κ(t)) − q − b·t ≤ (8/25)·t²` of `kk_two` and the Hilbert–Schmidt bound of the remainder):
for every `n ≥ 4096`, on the same good event, the frame bound `(43/25)/n`. -/
theorem lamOne136_hs {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ good136 n) :
    hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) ≠ 0 ∧
    (∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) (hid2 θ.1 θ.2 u) j * w j) ^ 2
          ∂uniformSphere (2 * n) ≤ 43 / 25 / (n : ℝ) * ∑ j, w j ^ 2) := by
  obtain ⟨b, hb0, hb1, hb⟩ := kk_two
  have hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - 0 * t ^ 2| ≤ 8 / 25 * t ^ 2 + 0 * |t| ^ 3 := by
    intro t ht
    have h := hb t ht
    rw [zero_mul, zero_mul, sub_zero, add_zero, abs_of_nonneg h.1]
    exact h.2
  exact lam_num (n := n) (n0 := 4096) le_rfl hn (b := b) (c2 := 0)
    (η := 8 / 25) (K₃ := 0) (r0 := 1 / 262144) (k0 := 5771 / 625000) (k6 := 1)
    (sp := 4 / 100)
    (ε₁ := 34 / 1000) (ε₂ := 25 / 1000) (s := 42079 / 100000) (p₂ := 4 / 10000)
    (D0 := 63497 / 125000) (C := 43 / 25)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hθ

/-- **The stand-in theorem with the bound inserted (item 4), mean squared error.** For every
`n ≥ 4096`, every `(M₁, M₂)` in the good event, `b = h̄`, and every bounded measurable `φ`:
`E_{M₃} (E_{μ_W} φ − E_{ν_{M₃ h̄}} φ)² ≤ ((99/100)/n) · E_c Var_{ν_c} φ`. -/
theorem standIn136 {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2))
          (M₃.mulVec (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)))) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) c]
        ∂cDist n (2 / (mW n : ℝ)) (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) := by
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨h1, h2, -⟩ := lamOne136 hn hθ
  exact s1_mse_mlp (by omega) θ.1 θ.2 h1 hφ (by positivity) h2

/-- **The stand-in theorem with the bound inserted, conditional variance.** For every `n ≥ 4096`,
every `(M₁, M₂)` in the good event, `b = h̄`, every `c` and every bounded measurable `φ`:
`Var(E_{μ_W} φ | M₃ h̄ = c) ≤ ((99/100)/n) · Var_{ν_c} φ`. -/
theorem standInVar136 {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ good136 n) (c : Fin n → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    Var[fun M' => ∫ x, φ x ∂muWn ((θ.1, θ.2,
          glue (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) c
            (M' * projPerp (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)))) :
          MlpParam (2 * n) (mW n) n);
        gaussMat n (mW n) (2 / (mW n : ℝ))] ≤
      99 / 100 / (n : ℝ) *
        Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2)) c] := by
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨-, h2, -⟩ := lamOne136 hn hθ
  exact s1_var_mlp (by omega) θ.1 θ.2 _ c hφ (by positivity) h2

end BstLean.Part136
