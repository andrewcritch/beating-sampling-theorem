import BstLean.Part167Grad

/-!
# Part 167 (file `Red`): Lemma LJ reduced to a moment of the explicit Jacobian

No proof is left open; no `native_decide` or `axiom` is used.

* `JM_hyp n K2`: **Lemma LJ in its paper form** at `ℓ = 128`: for a World value in the window,
  a unit input `x = xLat(s, v/|v|)` of latitude `s` (`v ≠ 0`), the plane `span(u, x)` with
  orthonormal pair `(u, w)`, and `y ∈ {b̂, r̂(x)}`:
  `E_{A₁,A₂} |P_lat 𝒥(x)ᵀ y|^{128} ≤ K2^{64}` (that is, `‖|P_lat𝒥ᵀy|/|y|‖_{L^128} ≤ √K2 = K_128`).
  There is no derivative, no `tanSq` and no null set in this statement.
* `LJae_hyp n K2`: Part 166's `LJ_hyp` for every direction `v ≠ 0` (an a.e. form).
* **`LJae_of_JM`**: `JM_hyp n K2 → LJae_hyp n K2` (Lemma J a.e. in the weights, Part 167 `J`,
  and the tangential identity, Part 167 `Grad`).
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix xLat hhMat uHat consV hh_normSq normSq_consV)
open BstLean.Part162 (xLatH tanSq xLatH_eq dirW latitude_sq_le radF_pos radF_sq)
open BstLean.Part166 (bK bhat fK sK psiK repK latK winC LJ_hyp)
open BstLean.Part151 (jac)
open BstLean.Part153 (nuA jac_smul)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

/-- A retained-data value that carries only the World centre `ĉ`. -/
noncomputable def rc (c : Fin n → ℝ) : Ret n := repK ((c, 0), 0)

lemma gF_smul (k : AgFam n) {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) : gF k (t • x) = gF k x := by
  unfold gF; rw [jac_smul _ _ ht]

lemma gS_smul (k : AgFam n) {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) : gS k (t • x) = gS k x := by
  unfold gS; rw [jac_smul _ _ ht, rK_smul k ht, bhat_smul ht]

/-- **Lemma LJ (paper form, order 128, for `y = b̂` and `y = r̂`), as a hypothesis on the
explicit Jacobian `𝒥(x) = D₂A₂D₁A₁`.** -/
def JM_hyp (n : ℕ) (K2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    ∫⁻ θ, ENNReal.ofReal (latSq (gF ((c, τ), θ)
        (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 64) ∂nuA n ≤ ENNReal.ofReal (K2 ^ 64) ∧
    ∫⁻ θ, ENNReal.ofReal (latSq (gS ((c, τ), θ)
        (xLat (rc c) (latitude (n := n) (√(normSq c)) τ a) (unitF53 v)))
        (uHat (rc c)) (dirW (rc c) (unitF53 v)) ^ 64) ∂nuA n ≤ ENNReal.ofReal (K2 ^ 64)

/-- Part 166's `LJ_hyp` for every direction `v ≠ 0`. -/
def LJae_hyp (n : ℕ) (K2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    ∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K2 / n) ^ 64) ∧
    ∫⁻ θ, ENNReal.ofReal (psiK sK ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * (2 / n) * K2 / n) ^ 64)

lemma LJae_of_LJ {K2 : ℝ} (h : LJ_hyp n K2) : LJae_hyp n K2 :=
  fun c τ hw a v _ => h c τ hw a v

/-- `|xLatH c s v|² = |v|²` for `s² ≤ 1`. -/
lemma normSq_xLatH (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) (v : Fin (n - 1) → ℝ) :
    normSq (xLatH c s v) = normSq v := by
  unfold xLatH
  rw [hh_normSq, normSq_consV hn]
  have h1 : normSq (√(1 - s ^ 2) • v) = (1 - s ^ 2) * normSq v := by
    unfold normSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Real.sq_sqrt (by linarith), Finset.mul_sum]
  have h2 : radF53 v ^ 2 = normSq v := radF_sq v
  rw [h1, mul_pow, h2]; ring

lemma xLatH_ne_zero (hn : 1 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1) {v : Fin (n - 1) → ℝ}
    (hv : v ≠ 0) : xLatH c s v ≠ 0 := by
  intro h0
  have h1 := normSq_xLatH hn c hs v
  rw [h0] at h1
  have h2 : normSq v = 0 := by rw [← h1]; simp [normSq]
  apply hv
  funext j
  have := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i)) |>.mp h2 j
    (Finset.mem_univ j)
  simpa using this

lemma window_c_ne {c : Fin n → ℝ} {τ : ℝ} (hn : 1 ≤ n) (hw : winC c τ) : c ≠ 0 := by
  obtain ⟨hτ, _, hθ1⟩ := hw
  intro h0
  subst h0
  unfold BstLean.Part150.thetaC BstLean.Part150.rhoC at hθ1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : normSq (0 : Fin n → ℝ) = 0 := by simp [normSq]
  rw [e, zero_add, Real.sq_sqrt (by positivity), div_self (by positivity)] at hθ1
  norm_num at hθ1

/-- **Lemma LJ in Part 166's form follows from its paper form** (for `v ≠ 0`). -/
theorem LJae_of_JM (hn : 1 ≤ n) {K2 : ℝ} (hJM : JM_hyp n K2) :
    LJae_hyp n K2 := by
  intro c τ hw a v hv
  obtain ⟨hJf, hJs⟩ := hJM c τ hw a v hv
  have hc : c ≠ 0 := window_c_ne hn hw
  set s := latitude (n := n) (√(normSq c)) τ a with hsdef
  have hs : s ^ 2 ≤ 1 := latitude_sq_le _ _ _
  set x := xLat (rc c) s (unitF53 v) with hx
  set y := xLatH (rc c) s v with hy
  have hyx : y = radF53 v • x := xLatH_eq _ _ _
  have hy0 : y ≠ 0 := xLatH_ne_zero hn _ hs hv
  have hae := noKink_nuA hn hy0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1s : 0 ≤ 1 - s ^ 2 := by linarith
  have hvpos : 0 < radF53 v := radF_pos hv
  refine ⟨?_, ?_⟩
  · calc ∫⁻ θ, ENNReal.ofReal (psiK fK ((c, τ), θ) a v ^ 64) ∂nuA n
        ≤ ∫⁻ θ, ENNReal.ofReal (((1 - s ^ 2) / n) ^ 64) *
            ENNReal.ofReal (latSq (gF ((c, τ), θ) x) (uHat (rc c)) (dirW (rc c) (unitF53 v))
              ^ 64) ∂nuA n := by
          refine lintegral_mono_ae (hae.mono fun θ hθ => ?_)
          have h := psiK_f_le ((c, τ), θ) a v hn hc hv hθ
          have e1 : gF ((c, τ), θ) (xLatH (repK ((c, τ), θ)) (latK ((c, τ), θ) a) v) =
              gF ((c, τ), θ) x := by
            change gF ((c, τ), θ) y = gF ((c, τ), θ) x
            rw [hyx, gF_smul _ hvpos]
          rw [e1] at h
          have hnn : (0 : ℝ) ≤ ((1 - s ^ 2) / n) ^ 64 := pow_nonneg (div_nonneg h1s hn0.le) 64
          rw [← ENNReal.ofReal_mul hnn]
          refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
          change ((1 - s ^ 2) * latSq (gF ((c, τ), θ) x) (uHat (rc c))
            (dirW (rc c) (unitF53 v)) / n) ^ 64 = _
          rw [← mul_pow]; congr 1; ring
      _ = ENNReal.ofReal (((1 - s ^ 2) / n) ^ 64) *
            ∫⁻ θ, ENNReal.ofReal (latSq (gF ((c, τ), θ) x) (uHat (rc c))
              (dirW (rc c) (unitF53 v)) ^ 64) ∂nuA n :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (((1 - s ^ 2) / n) ^ 64) * ENNReal.ofReal (K2 ^ 64) := by gcongr
      _ = ENNReal.ofReal (((1 - s ^ 2) * K2 / n) ^ 64) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]; congr 2; ring
  · have hm : (2 / (mA n : ℝ)) = 2 / n / n := by
      unfold mA; push_cast; field_simp
    calc ∫⁻ θ, ENNReal.ofReal (psiK sK ((c, τ), θ) a v ^ 64) ∂nuA n
        ≤ ∫⁻ θ, ENNReal.ofReal (((1 - s ^ 2) * (2 / n) / n) ^ 64) *
            ENNReal.ofReal (latSq (gS ((c, τ), θ) x) (uHat (rc c)) (dirW (rc c) (unitF53 v))
              ^ 64) ∂nuA n := by
          refine lintegral_mono_ae (hae.mono fun θ hθ => ?_)
          have h := psiK_s_le ((c, τ), θ) a v hn hc hv hθ
          have e1 : gS ((c, τ), θ) (xLatH (repK ((c, τ), θ)) (latK ((c, τ), θ) a) v) =
              gS ((c, τ), θ) x := by
            change gS ((c, τ), θ) y = gS ((c, τ), θ) x
            rw [hyx, gS_smul _ hvpos]
          rw [e1] at h
          have hnn : (0 : ℝ) ≤ ((1 - s ^ 2) * (2 / n) / n) ^ 64 :=
            pow_nonneg (div_nonneg (mul_nonneg h1s (by positivity)) hn0.le) 64
          rw [← ENNReal.ofReal_mul hnn]
          refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
          change ((1 - s ^ 2) * (2 / (mA n : ℝ)) * latSq (gS ((c, τ), θ) x) (uHat (rc c))
            (dirW (rc c) (unitF53 v))) ^ 64 = _
          rw [← mul_pow, hm]; congr 1; ring
      _ = ENNReal.ofReal (((1 - s ^ 2) * (2 / n) / n) ^ 64) *
            ∫⁻ θ, ENNReal.ofReal (latSq (gS ((c, τ), θ) x) (uHat (rc c))
              (dirW (rc c) (unitF53 v)) ^ 64) ∂nuA n :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (((1 - s ^ 2) * (2 / n) / n) ^ 64) * ENNReal.ofReal (K2 ^ 64) := by
          gcongr
      _ = ENNReal.ofReal (((1 - s ^ 2) * (2 / n) * K2 / n) ^ 64) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]; congr 2; ring

end BstLean.Part167
