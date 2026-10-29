import BstLean.Part159Pert
import BstLean.Part159Frame
import BstLean.Part159Q1

/-!
# Part 159 (file `PaperC`): the binomial World centre of the paper is near the computed centre

Role: `delegations/statements/p159-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `theorem7-01-statement-program.tex`, step 2 (the binomial centre `b_W`), and
`theorem7-02-world.tex`, Input `t7:p02:input-hidden`.

`bWp` (Part 157) is the binomial World centre of the paper:
`b_{W,i} = B_J[z ↦ ReLU(c̃_N·(W₂ρ)_i + s_W z)]`, `J = ⌈√m_W⌉`, `ρ_j = |row_j(W₁)|`. The computed
centre of Parts 137, 140 is `b̂_i = ψ_s(c_N·(W₂ρ)_i)` with the exact constant `c_N` and the
Gaussian smoothing `ψ_s`.

* `ConstC n`: the hypothesis on the computed constant `c̃_N` of the paper's program:
  `(c̃_N − c_N)²·n·m_W ≤ 10⁻¹⁷`. It is a statement about two real numbers (no network). It is
  proved in file `Pi` for every `n ≥ 13 225`.
* `goodS n`: the hidden event `|S_W/2 − 1| ≤ 1/1000`; `goodAo n`: the hidden event
  `t_W|W₂ρ|² ≤ 10⁸`. `goodS_charge`, `goodAo_charge`.
* `bWp_coord`: the distance of one coordinate (binomial replacement lemma of Part 150 and the
  Lipschitz property of `ψ_s`).
* **`bWp_dist`**: for `n ≥ 13 225`, on `goodS n ∩ goodAo n`, IF `ConstC n`:
  `t_W|b_W − b̂|² ≤ γ·0.0645/m_W`.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le)
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part137 (bhat cN sS h1bar GamS GamS_L2x GamS_nonneg psiS mW_ge_pow42)
open BstLean.Part141 (aOf sOf rowS rowS_nonneg aOf_mul aOf_cN sOf_cN sOf_sq cN_nonneg cN_sq_le
  cN_le_half GamS_rowS psiS_lip_x psiS_lip_s aOne_mean GamS_mean measurable_aOf)
open BstLean.Part150 (binMean lemmaBF1_paper c1F kappa4 c1F_kappa4_le c1F_nonneg kappa4_nonneg)
open BstLean.Part157

variable {n : ℕ}

/-- **The hypothesis on the computed constant `c̃_N`** of the paper's program:
`(c̃_N − c_N)²·n·m_W ≤ 10⁻¹⁷`, `c_N = E_u ReLU(u₁)` on the unit sphere of `ℝ^{2n}`. -/
def ConstC (n : ℕ) : Prop := (cNt n - cN (2 * n)) ^ 2 * (n : ℝ) * (mW n : ℝ) ≤ 1 / 10 ^ 17

/-- The hidden event `|S_W/2 − 1| ≤ 1/1000`. -/
def goodS (n : ℕ) : Set (WHid n) := {θ | |SWp θ / 2 - 1| ≤ 1 / 1000}

/-- The hidden event `t_W|W₂ρ|² ≤ 10⁸`, `ρ_j = |row_j(W₁)|`. -/
def goodAo (n : ℕ) : Set (WHid n) := {θ | 2 / (mW n : ℝ) * normSq (aOf 1 θ) ≤ 10 ^ 8}

lemma measurableSet_goodS : MeasurableSet (goodS n) :=
  measurableSet_le ((measurable_SWp.div_const 2).sub_const 1).abs measurable_const

lemma measurableSet_goodAo : MeasurableSet (goodAo n) :=
  measurableSet_le ((measurable_normSq.comp (measurable_aOf 1)).const_mul _) measurable_const

lemma SWp_nonneg (θ : WHid n) : 0 ≤ SWp θ := by
  unfold SWp
  exact div_nonneg (rowS_nonneg _) (Nat.cast_nonneg _)

lemma sWp_nonneg (θ : WHid n) : 0 ≤ sWp θ := Real.sqrt_nonneg _

/-- `S_W/2 − 1 = (Γ* − γ)/γ`. -/
lemma SWp_half (hn : 1 ≤ n) (hm : 1 ≤ mW n) (θ : WHid n) :
    SWp θ / 2 - 1 = (GamS θ.1 - 2 / ((2 * n : ℕ) : ℝ)) / (2 / ((2 * n : ℕ) : ℝ)) := by
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
  rw [GamS_rowS (by omega) hm]
  unfold SWp
  field_simp

/-- `‖S_W/2 − 1‖₂ ≤ √(2/(N m_W))` over the hidden matrices. -/
lemma SWp_L2 (hn : 1 ≤ n) (hm : 1 ≤ mW n) :
    L2le (hidGauss (2 * n) (mW n)) (fun θ : WHid n => SWp θ / 2 - 1)
      (√(2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ)))) := by
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
  have h1 := (GamS_L2x (N := 2 * n) (m := mW n) (by omega) hm).comp_fst
    (ν := gaussMat (mW n) (mW n) (2 / (mW n : ℝ)))
  have h2 := h1.const_mul_nonneg (c := 1 / (2 / ((2 * n : ℕ) : ℝ))) (by positivity)
  have h3 : L2le (hidGauss (2 * n) (mW n)) (fun θ : WHid n =>
      1 / (2 / ((2 * n : ℕ) : ℝ)) * (GamS θ.1 - 2 / ((2 * n : ℕ) : ℝ)))
      (1 / (2 / ((2 * n : ℕ) : ℝ)) *
        (2 / ((2 * n : ℕ) : ℝ) * √(2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))))) := h2
  refine (h3.congr_fun fun θ => ?_).congr_bound ?_
  · rw [SWp_half hn hm]
    field_simp
  · field_simp

/-- **The charge of `goodS`**: `Pr(|S_W/2 − 1| > 1/1000) ≤ 10⁶·2/(N m_W)`. -/
theorem goodS_charge (hn : 1 ≤ n) (hm : 1 ≤ mW n) :
    (hidGauss (2 * n) (mW n)).real (goodS n)ᶜ ≤
      10 ^ 6 * (2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) := by
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
  have hL := SWp_L2 hn hm
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := hidGauss (2 * n) (mW n))
    (f := fun θ : WHid n => (SWp θ / 2 - 1) ^ 2)
    (Filter.Eventually.of_forall fun θ => sq_nonneg _) hL.int_sq ((1 / 1000) ^ 2)
  have hsub : (goodS n)ᶜ ⊆ {θ : WHid n | (1 / 1000 : ℝ) ^ 2 ≤ (SWp θ / 2 - 1) ^ 2} := by
    intro θ hθ
    have h1 : ¬ |SWp θ / 2 - 1| ≤ 1 / 1000 := hθ
    have h2 : (1 / 1000 : ℝ) ≤ |SWp θ / 2 - 1| := (not_le.mp h1).le
    change (1 / 1000 : ℝ) ^ 2 ≤ (SWp θ / 2 - 1) ^ 2
    rw [← sq_abs (SWp θ / 2 - 1)]
    exact pow_le_pow_left₀ (by norm_num) h2 2
  have hle := measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)
  have hb := hL.le
  rw [Real.sq_sqrt (by positivity)] at hb
  nlinarith

/-- **The charge of `goodAo`**: `Pr(t_W|W₂ρ|² > 10⁸) ≤ 9·10⁻⁸`. -/
theorem goodAo_charge (hn : 4096 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodAo n)ᶜ ≤ 9 / 10 ^ 8 := by
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast hN
  obtain ⟨i1, e1⟩ := aOne_mean (N := 2 * n) (m := mW n) hN hm
  obtain ⟨-, e2⟩ := GamS_mean (N := 2 * n) (m := mW n) hN hm
  have hs : √(1 + 5 / (mW n : ℝ)) ≤ 9 / 8 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have : 5 / (mW n : ℝ) ≤ 5 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm6
    linarith
  have hmean : ∫ θ : WHid n, 2 / (mW n : ℝ) * normSq (aOf 1 θ) ∂hidGauss (2 * n) (mW n) ≤ 9 := by
    rw [e1]
    have h3 : 2 / ((2 * n : ℕ) : ℝ) * √(1 + 5 / (mW n : ℝ)) ≤ 2 / ((2 * n : ℕ) : ℝ) * (9 / 8) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have h4 : 4 * ((2 * n : ℕ) : ℝ) * (2 / ((2 * n : ℕ) : ℝ) * (9 / 8)) = 9 := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left (e2.trans h3)
      (by positivity : (0 : ℝ) ≤ 4 * ((2 * n : ℕ) : ℝ))]
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := hidGauss (2 * n) (mW n))
    (f := fun θ : WHid n => 2 / (mW n : ℝ) * normSq (aOf 1 θ))
    (Filter.Eventually.of_forall fun θ => mul_nonneg (by positivity) (normSq_nonneg _)) i1
    (10 ^ 8)
  have hsub : (goodAo n)ᶜ ⊆
      {θ : WHid n | (10 : ℝ) ^ 8 ≤ 2 / (mW n : ℝ) * normSq (aOf 1 θ)} := by
    intro θ hθ
    have h1 : ¬ 2 / (mW n : ℝ) * normSq (aOf 1 θ) ≤ 10 ^ 8 := hθ
    exact (not_le.mp h1).le
  have hle := measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)
  nlinarith

/-! ## One coordinate -/

/-- The computed centre written with `aOf`, `sS`. -/
lemma bhat_apply (hn : 1 ≤ n) (θ : WHid n) (i : Fin (mW n)) :
    bhat θ i = psiS (sS θ.1) (aOf (cN (2 * n)) θ i) := by
  rw [aOf_cN (by omega)]
  rfl

/-- **The distance of one coordinate of the binomial centre to the computed centre.** -/
theorem bWp_coord (hn : 1 ≤ n) (hJ : 1 ≤ JW n) (θ : WHid n) (i : Fin (mW n)) :
    |bWp θ i - bhat θ i| ≤ c1F kappa4 (JW n) * sWp θ / (JW n) +
      |cNt n - cN (2 * n)| * |aOf 1 θ i| + |sWp θ - sS θ.1| := by
  rw [bhat_apply hn]
  have h1 := lemmaBF1_paper hJ (aOf (cNt n) θ i) (sWp_nonneg θ)
  have h2 := psiS_lip_x (sWp θ) (aOf (cNt n) θ i) (aOf (cN (2 * n)) θ i)
  have h3 := psiS_lip_s (sWp θ) (sS θ.1) (aOf (cN (2 * n)) θ i)
  have e : aOf (cNt n) θ i - aOf (cN (2 * n)) θ i = (cNt n - cN (2 * n)) * aOf 1 θ i := by
    rw [aOf_mul (cNt n), aOf_mul (cN (2 * n))]
    ring
  rw [e, abs_mul] at h2
  have e2 : bWp θ i - psiS (sS θ.1) (aOf (cN (2 * n)) θ i) =
      (binMean (JW n) (fun z => relu (aOf (cNt n) θ i + sWp θ * z)) -
        psiS (sWp θ) (aOf (cNt n) θ i)) +
      (psiS (sWp θ) (aOf (cNt n) θ i) - psiS (sWp θ) (aOf (cN (2 * n)) θ i)) +
      (psiS (sWp θ) (aOf (cN (2 * n)) θ i) - psiS (sS θ.1) (aOf (cN (2 * n)) θ i)) := by
    unfold bWp
    ring
  rw [e2]
  have h4 := abs_add_three
    (binMean (JW n) (fun z => relu (aOf (cNt n) θ i + sWp θ * z)) -
      psiS (sWp θ) (aOf (cNt n) θ i))
    (psiS (sWp θ) (aOf (cNt n) θ i) - psiS (sWp θ) (aOf (cN (2 * n)) θ i))
    (psiS (sWp θ) (aOf (cN (2 * n)) θ i) - psiS (sS θ.1) (aOf (cN (2 * n)) θ i))
  linarith

/-! ## The smoothing widths -/

/-- `s_W² ≤ S_W/(2n)`. -/
lemma sWp_sq_le (hn : 1 ≤ n) (θ : WHid n) : sWp θ ^ 2 ≤ SWp θ / (2 * (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hS := SWp_nonneg θ
  have hd : dNt n ≤ 1 / (2 * (n : ℝ)) := by
    unfold dNt
    nlinarith [sq_nonneg (cNt n)]
  unfold sWp
  rcases le_total 0 (SWp θ * dNt n) with h | h
  · rw [Real.sq_sqrt h]
    calc SWp θ * dNt n ≤ SWp θ * (1 / (2 * (n : ℝ))) := mul_le_mul_of_nonneg_left hd hS
      _ = SWp θ / (2 * (n : ℝ)) := by ring
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    have : 0 ≤ SWp θ / (2 * (n : ℝ)) := by positivity
    simpa using this

/-- **The two smoothing widths are close**: `(s_W − s)² ≤ 9·(c̃_N − c_N)²` if `n ≥ 13 225`,
`1.998 ≤ S_W ≤ 2.002` and `|c̃_N − c_N| ≤ c_N/100`. -/
theorem sWp_sub_sq (hn : 13225 ≤ n) (hm : 1 ≤ mW n) (θ : WHid n) (hS1 : 1998 / 1000 ≤ SWp θ)
    (hS2 : SWp θ ≤ 2002 / 1000) (hd1 : |cNt n - cN (2 * n)| ≤ cN (2 * n) / 100) :
    (sWp θ - sS θ.1) ^ 2 ≤ 9 * (cNt n - cN (2 * n)) ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hcw⟩ := cN_even_window hn
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = cN (2 * n) := ⟨_, rfl⟩
  rw [← hc] at hd1 hcw ⊢
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = cNt n - c := ⟨_, rfl⟩
  rw [← hd] at hd1 ⊢
  have hc0 : 0 ≤ c := by rw [hc]; exact cN_nonneg _
  have hct : cNt n = c + d := by rw [hd]; ring
  obtain ⟨hda, hdb⟩ := abs_le.mp hd1
  -- `c̃² ≤ 1.0201·c²`, `(2c + d)² ≤ 4.0401·c²`
  have hct2 : cNt n ^ 2 ≤ (101 / 100 * c) ^ 2 := by
    rw [hct]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2cd : (2 * c + d) ^ 2 ≤ (201 / 100 * c) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hX : c ^ 2 * (n : ℝ) ≤ 8 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hcw
    linarith
  -- `dNt ≥ 0.33/n`
  have hdN : 33 / 100 / (n : ℝ) ≤ dNt n := by
    unfold dNt
    rw [div_le_iff₀ hnpos]
    have e : (1 / (2 * (n : ℝ)) - 2 * cNt n ^ 2) * (n : ℝ) = 1 / 2 - 2 * (cNt n ^ 2 * (n : ℝ)) := by
      field_simp
    rw [e]
    have h1 : cNt n ^ 2 * (n : ℝ) ≤ (101 / 100 * c) ^ 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hct2 hnpos.le
    nlinarith
  have hdN0 : 0 ≤ dNt n := le_trans (by positivity) hdN
  have hSpos : 0 < SWp θ := by linarith
  have hst2 : sWp θ ^ 2 = SWp θ * dNt n := by
    unfold sWp
    exact Real.sq_sqrt (mul_nonneg hSpos.le hdN0)
  have hst0 : 0 ≤ sWp θ := sWp_nonneg θ
  have hs0 : 0 ≤ sS θ.1 := Real.sqrt_nonneg _
  have hs2 : sS θ.1 ^ 2 = SWp θ * (1 / (2 * (n : ℝ)) - 2 * c ^ 2) := by
    have h := sOf_sq (N := 2 * n) (m := mW n) hN hm (cN_nonneg _) le_rfl θ
    rw [sOf_cN hN hm] at h
    rw [h, hNcast, hc]
    unfold SWp
    field_simp
  have hlow : 65 / 100 / (n : ℝ) ≤ sWp θ ^ 2 := by
    rw [hst2]
    have h1 : 1998 / 1000 * (33 / 100 / (n : ℝ)) ≤ SWp θ * dNt n :=
      mul_le_mul hS1 hdN (by positivity) hSpos.le
    have h0 : 65 / 100 / (n : ℝ) ≤ 1998 / 1000 * (33 / 100 / (n : ℝ)) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by norm_num) hnpos.le
    exact h0.trans h1
  have hdiff : sWp θ ^ 2 - sS θ.1 ^ 2 = -(2 * SWp θ * d * (2 * c + d)) := by
    rw [hst2, hs2]
    unfold dNt
    rw [hct]
    ring
  have hkey : (sWp θ - sS θ.1) ^ 2 * sWp θ ^ 2 ≤ (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 := by
    have e : (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 = (sWp θ - sS θ.1) ^ 2 * (sWp θ + sS θ.1) ^ 2 := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact pow_le_pow_left₀ hst0 (by linarith) 2
  have hsq : (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 * (n : ℝ) ≤ 53 / 10 * d ^ 2 := by
    rw [hdiff, neg_sq]
    have e : (2 * SWp θ * d * (2 * c + d)) ^ 2 * (n : ℝ) =
        4 * SWp θ ^ 2 * ((2 * c + d) ^ 2 * (n : ℝ)) * d ^ 2 := by ring
    rw [e]
    have h1 : SWp θ ^ 2 ≤ (2002 / 1000) ^ 2 := pow_le_pow_left₀ hSpos.le hS2 2
    have h2 : (2 * c + d) ^ 2 * (n : ℝ) ≤ (201 / 100) ^ 2 * (8 / 100) := by
      have h3 := mul_le_mul_of_nonneg_right h2cd hnpos.le
      nlinarith
    have h4 : 4 * SWp θ ^ 2 * ((2 * c + d) ^ 2 * (n : ℝ)) ≤
        4 * (2002 / 1000) ^ 2 * ((201 / 100) ^ 2 * (8 / 100)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (by positivity) (by norm_num)
    have h5 : (4 * (2002 / 1000) ^ 2 * ((201 / 100) ^ 2 * (8 / 100)) : ℝ) ≤ 53 / 10 := by norm_num
    exact mul_le_mul_of_nonneg_right (h4.trans h5) (sq_nonneg _)
  -- conclude
  have h6 : (sWp θ - sS θ.1) ^ 2 * (65 / 100 / (n : ℝ)) ≤ (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 :=
    (mul_le_mul_of_nonneg_left hlow (sq_nonneg _)).trans hkey
  have h7 : (sWp θ - sS θ.1) ^ 2 * (65 / 100) ≤ (sWp θ ^ 2 - sS θ.1 ^ 2) ^ 2 * (n : ℝ) := by
    have h8 := mul_le_mul_of_nonneg_right h6 hnpos.le
    have e : (sWp θ - sS θ.1) ^ 2 * (65 / 100 / (n : ℝ)) * (n : ℝ) =
        (sWp θ - sS θ.1) ^ 2 * (65 / 100) := by field_simp
    rw [e] at h8
    exact h8
  nlinarith [sq_nonneg d, sq_nonneg (sWp θ - sS θ.1)]

end BstLean.Part159

open BstLean.Part159 in
#print axioms goodS_charge
open BstLean.Part159 in
#print axioms goodAo_charge
open BstLean.Part159 in
#print axioms bWp_coord
open BstLean.Part159 in
#print axioms sWp_sub_sq
