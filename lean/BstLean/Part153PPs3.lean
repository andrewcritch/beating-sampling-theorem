import BstLean.Part153PPs2

/-!
# Part 153, Lemma PP: the numeric corollary and the covariance bound on the event

Paper source: `proofs/option-n/theorem5-05-covariance.tex`, Lemma PP and the sentence
"On `E_{Pp}`: `‖t_A Cov_x(a₂)‖_op ≤ Ξ ≤ M_P γ_A/n`".

* §1 `gaussMomConst_160_le`: `𝔪_160 ≤ 18`; `jS_160_le`: `jS n 160 (6/1000) ≤ 10692/10000` for
  `n ≥ 8192`.
* §2 **`lemmaPP_numeric`**: for `n ≥ 8192`: `Pr(Ξ₄ > (127/100)·(2/n)/n) ≤ 5·10⁻⁵`.
* §3 **`cov_le_of_Xi4`**, **`var_lip_le_of_Xi4`**, `cov_le_on_event`, `var_lip_le_on_event`: the
  covariance bound on the event.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac mask)

/-! ## §1 Numeric bounds -/

/-- `𝔪_160 ≤ 18` (from `P! ≤ P^P`: `𝔪_P ≤ √(2P)`). -/
lemma gaussMomConst_160_le : gaussMomConst 160 ≤ 18 := by
  have h0 := gaussMomConst_nonneg 160
  have hp := gaussMomConst_pow (P := 160) (by norm_num)
  have hf : ((Nat.factorial 160 : ℕ) : ℝ) ≤ (160 : ℝ) ^ 160 := by
    have := Nat.factorial_le_pow 160
    exact_mod_cast this
  have h1 : gaussMomConst 160 ^ (2 * 160) ≤ (18 : ℝ) ^ (2 * 160) := by
    rw [hp]
    calc (2 : ℝ) ^ 160 * ((Nat.factorial 160 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 160 * (160 : ℝ) ^ 160 :=
          mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (320 : ℝ) ^ 160 := by rw [← mul_pow]; norm_num
      _ ≤ (324 : ℝ) ^ 160 := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (18 : ℝ) ^ (2 * 160) := by rw [pow_mul]; norm_num
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) (by norm_num : (0 : ℝ) ≤ 18)
    (by norm_num : (2 * 160 : ℕ) ≠ 0)
  linarith

lemma exp_neg_15_le : Real.exp (-15) ≤ 4 / 10 ^ 7 := by
  have h1 : (2.7 : ℝ) ^ 15 ≤ Real.exp 15 := by
    have e : Real.exp 15 = Real.exp 1 ^ 15 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 15
  rw [Real.exp_neg]
  calc (Real.exp 15)⁻¹ ≤ ((2.7 : ℝ) ^ 15)⁻¹ := inv_anti₀ (by positivity) h1
    _ ≤ 4 / 10 ^ 7 := by norm_num

/-- `jS n 160 (6/1000) ≤ 1.0692` for `n ≥ 8192`. -/
lemma jS_160_le {n : ℕ} (hn : 8192 ≤ n) : jS n 160 (6 / 1000) ≤ 10692 / 10000 := by
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs90 : (90 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := gaussMomConst_nonneg 160
  have hg := gaussMomConst_160_le
  obtain ⟨g, hgdef⟩ : ∃ g, g = gaussMomConst 160 := ⟨_, rfl⟩
  rw [← hgdef] at hg0 hg
  -- the atoms
  have hr0 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hr : √(2 : ℝ) ≤ 141422 / 100000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hq0 : (0 : ℝ) ≤ √(1 + 2 * (6 / 1000)) := Real.sqrt_nonneg _
  have hq : √(1 + 2 * (6 / 1000) : ℝ) ≤ 1006 / 1000 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hu0 : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have hu : 1 / √(n : ℝ) ≤ 1 / 90 := one_div_le_one_div_of_le (by norm_num) hs90
  have hw0 : (0 : ℝ) ≤ g / n := by positivity
  have hw : g / (n : ℝ) ≤ 18 / 8192 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    linarith
  have hgu0 : (0 : ℝ) ≤ g / √(n : ℝ) := by positivity
  have hgu : g / √(n : ℝ) ≤ 1 / 5 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    linarith
  have he0 : 0 ≤ epsS n 160 (6 / 1000) := (Real.exp_pos _).le
  have he : epsS n 160 (6 / 1000) ≤ 4 / 10 ^ 7 := by
    refine le_trans ?_ exp_neg_15_le
    unfold epsS
    rw [show ((160 : ℕ) : ℝ) = 160 by norm_num]
    refine Real.exp_le_exp.2 ?_
    have : (8192 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
    have h15 : (15 : ℝ) ≤ (6 / 1000) ^ 2 * (n : ℝ) ^ 2 / 160 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    linarith
  obtain ⟨r2, hr2⟩ : ∃ r2, r2 = √(2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, q = √(1 + 2 * (6 / 1000) : ℝ) := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u, u = 1 / √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = g / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨gu, hgud⟩ : ∃ gu, gu = g / √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = epsS n 160 (6 / 1000) := ⟨_, rfl⟩
  have key : jS n 160 (6 / 1000) = (q + r2 * u + r2 * w + e * (r2 * (1 + u + w))) ^ 2 +
      (1 + r2 * w) * (r2 * (1 + gu)) * u := by
    unfold jS n2S n1S b2S rcS rchiS
    rw [← hgdef, ← hed, hqd, hr2, hud, hwd, hgud]
    ring
  rw [key]
  rw [← hr2] at hr0 hr
  rw [← hqd] at hq0 hq
  rw [← hud] at hu0 hu
  rw [← hwd] at hw0 hw
  rw [← hgud] at hgu0 hgu
  rw [← hed] at he0 he
  have h1 : r2 * u ≤ 141422 / 100000 * (1 / 90) := mul_le_mul hr hu hu0 (by norm_num)
  have h2 : r2 * w ≤ 141422 / 100000 * (18 / 8192) := mul_le_mul hr hw hw0 (by norm_num)
  have h10 : 0 ≤ r2 * u := mul_nonneg hr0 hu0
  have h20 : 0 ≤ r2 * w := mul_nonneg hr0 hw0
  have hb0 : 0 ≤ r2 * (1 + u + w) := mul_nonneg hr0 (by linarith)
  have hb : r2 * (1 + u + w) ≤ 15 / 10 := by
    have : r2 * (1 + u + w) ≤ 141422 / 100000 * (1 + 1 / 90 + 18 / 8192) :=
      mul_le_mul hr (by linarith) (by linarith) (by norm_num)
    refine this.trans ?_
    norm_num
  have heb : e * (r2 * (1 + u + w)) ≤ 4 / 10 ^ 7 * (15 / 10) :=
    mul_le_mul he hb hb0 (by norm_num)
  have heb0 : 0 ≤ e * (r2 * (1 + u + w)) := mul_nonneg he0 hb0
  have hn20 : 0 ≤ q + r2 * u + r2 * w + e * (r2 * (1 + u + w)) := by linarith
  have hn2 : q + r2 * u + r2 * w + e * (r2 * (1 + u + w)) ≤ 102483 / 100000 := by
    norm_num at h1 h2 heb ⊢
    linarith
  have hn2sq := pow_le_pow_left₀ hn20 hn2 2
  have hrc0 : 0 ≤ 1 + r2 * w := by linarith
  have hrc : 1 + r2 * w ≤ 100311 / 100000 := by
    norm_num at h2 ⊢
    linarith
  have hrchi0 : 0 ≤ r2 * (1 + gu) := mul_nonneg hr0 (by linarith)
  have hrchi : r2 * (1 + gu) ≤ 16971 / 10000 := by
    have : r2 * (1 + gu) ≤ 141422 / 100000 * (1 + 1 / 5) :=
      mul_le_mul hr (by linarith) (by linarith) (by norm_num)
    refine this.trans ?_
    norm_num
  have hprod : (1 + r2 * w) * (r2 * (1 + gu)) ≤ 100311 / 100000 * (16971 / 10000) :=
    mul_le_mul hrc hrchi hrchi0 (by norm_num)
  have hprod0 : 0 ≤ (1 + r2 * w) * (r2 * (1 + gu)) := mul_nonneg hrc0 hrchi0
  have hpu : (1 + r2 * w) * (r2 * (1 + gu)) * u ≤ 100311 / 100000 * (16971 / 10000) * (1 / 90) :=
    mul_le_mul hprod hu hu0 (by norm_num)
  norm_num at hn2sq hpu ⊢
  linarith

/-! ## §2 The numeric corollary -/

/-- **Lemma PP, the numeric corollary at the paper's parameters** (`P = 160`, `η = 6/1000`,
`M_P = 127/100`): for `n ≥ 8192`, `Pr(Ξ₄ > (127/100)·γ_A/n) ≤ 5·10⁻⁵`, `γ_A = 2/n`. -/
theorem lemmaPP_numeric {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {θ | (127 / 100 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤ 5 / 100000 := by
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lemmaPP_Xi4_sharp (n := n) (P := 160) (by norm_num) (by omega) c hτ
    (M := 127 / 100) (by norm_num) (η := 6 / 1000) (by norm_num)
  refine h.trans ?_
  rw [show ((160 : ℕ) : ℝ) = 160 by norm_num]
  have hj0 := jS_nonneg n 160 (6 / 1000)
  have hj := jS_160_le hn
  have hj2 : jS n 160 (6 / 1000) ^ 2 ≤ (10692 / 10000) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hd : (0 : ℝ) < ((n : ℝ) - 1 - 2 * 160) * (127 / 100) := by
    have : (0 : ℝ) < (n : ℝ) - 1 - 2 * 160 := by linarith
    positivity
  have hratio : jS n 160 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 160) * (127 / 100)) ≤
      15 / 16 := by
    rw [div_le_iff₀ hd]
    have h1 : jS n 160 (6 / 1000) ^ 2 * n ≤ (10692 / 10000) ^ 2 * n :=
      mul_le_mul_of_nonneg_right hj2 (by linarith)
    refine h1.trans ?_
    norm_num
    linarith
  have hr0 : 0 ≤ jS n 160 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 160) * (127 / 100)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hd.le
  calc (jS n 160 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 160) * (127 / 100))) ^ 160
      ≤ (15 / 16 : ℝ) ^ 160 := pow_le_pow_left₀ hr0 hratio 160
    _ ≤ 5 / 100000 := by norm_num

/-! ## §3 The covariance bound on the event -/

section cov

variable {n : ℕ}

/-- **The covariance bound from a bound of `Ξ₄`**: if `Ξ₄ ≤ K` then for every `w`:
`t_A·Var_ξ ⟨w, h₂(x)⟩ ≤ K·|w|²`. -/
theorem cov_le_of_Xi4 (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {K : ℝ}
    (hΞ : Xi4 A₁ A₂ c τ ≤ K) (w : Fin (mA n) → ℝ) :
    2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      K * normSq w :=
  (cov_hid2_le hn A₁ A₂ c hτ w).trans
    (mul_le_mul_of_nonneg_right ((XiS_le_Xi4 hn A₁ A₂ c hτ).trans hΞ) (normSq_nonneg w))

/-- **The variance of a Lipschitz function from a bound of `Ξ₄`**: if `Ξ₄ ≤ K` then for every
`φ` with `EuLip φ Lφ`: `Var_ξ φ(√t_A·h₂(x)) ≤ Lφ²·K`. -/
theorem var_lip_le_of_Xi4 (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {K : ℝ}
    (hΞ : Xi4 A₁ A₂ c τ ≤ K) {φ : (Fin (mA n) → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ)
    (hφ : EuLip φ Lφ) :
    ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * K :=
  (lemmaS_jac hn A₁ A₂ c hτ hL hφ).2.trans
    (mul_le_mul_of_nonneg_left ((XiS_le_Xi4 hn A₁ A₂ c hτ).trans hΞ) (sq_nonneg _))

/-- **The covariance bound on the event `E_{Pp}`**: for `n ≥ 8192` and every `θ = (A₁, A₂)`
outside the set of `lemmaPP_numeric`: `t_A·Var_ξ ⟨w, h₂(x)⟩ ≤ (127/100)·(2/n)/n·|w|²`. -/
theorem cov_le_on_event (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (hθ : θ ∉ {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (127 / 100 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ}) (w : Fin (mA n) → ℝ) :
    2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 θ.1 θ.2 (sphPt (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ hid2 θ.1 θ.2 (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      (127 / 100 : ℝ) * (2 / (n : ℝ)) / n * normSq w :=
  cov_le_of_Xi4 (by omega) θ.1 θ.2 c hτ (not_lt.mp hθ) w

/-- **The variance of a Lipschitz function on the event `E_{Pp}`**: for `n ≥ 8192` and every
`θ = (A₁, A₂)` outside the set of `lemmaPP_numeric`:
`Var_ξ φ(√t_A·h₂(x)) ≤ Lφ²·(127/100)·(2/n)/n`. -/
theorem var_lip_le_on_event (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (hθ : θ ∉ {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (127 / 100 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ})
    {φ : (Fin (mA n) → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) :
    ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 θ.1 θ.2 (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 θ.1 θ.2 (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * ((127 / 100 : ℝ) * (2 / (n : ℝ)) / n) :=
  var_lip_le_of_Xi4 (by omega) θ.1 θ.2 c hτ (not_lt.mp hθ) hL hφ

end cov

end BstLean.Part153

open BstLean.Part153 in
#print axioms gaussMomConst_160_le
open BstLean.Part153 in
#print axioms jS_160_le
open BstLean.Part153 in
#print axioms lemmaPP_numeric
open BstLean.Part153 in
#print axioms cov_le_of_Xi4
open BstLean.Part153 in
#print axioms var_lip_le_of_Xi4
open BstLean.Part153 in
#print axioms cov_le_on_event
open BstLean.Part153 in
#print axioms var_lip_le_on_event
