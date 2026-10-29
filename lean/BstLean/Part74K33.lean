import BstLean.Part69Weights
import BstLean.Part74Defs

/-!
# Part 74: the kernels at `d = 3` and the reduction of the read weights at `(3, 3)`

* `k1_74`, `k2_74`, `k3_74`: the kernels `k_j(x, y)` at `d = 3`, `j = 1, 2, 3`.
* `beta1_74e`, `beta2_74e`, `beta3_74e`, `tau33_74e`: `β_j` and `τ` at `d = 3` as explicit functions
  of `s = v·x`, `B = Σ v_i² x_i²`, `C = Σ v_i³ x_i³`, `Σ x_i⁴`, `Σ x_i⁶`, `p₄(v)`, `p₆(v)`.
* `wRK33_74`: every weight `wRK (surrRK n K t v) 3 v κ` is
  `wickC i l · (1/𝒟)^l · ∫ τ^l s^{c₁} β₂^{c₂} β₃^{c₃} dQ`, `c_j` the letter counts of the word.
* `odd33_74`: this integral is `0` when `c₁ + c₃` is odd.
-/

namespace BstLean.Part74

open MeasureTheory
open BstLean.Part56
open BstLean.Part69

variable {n : ℕ}

/-! ## The kernels at `d = 3` -/

theorem hval3_74 (u : Fin n → ℝ) :
    BstLean.Part58.Kappa.hval 3 u =
      ((∑ i, u i) ^ 3 + 3 * (∑ i, u i) * (∑ i, u i ^ 2) + 2 * ∑ i, u i ^ 3) / 6 := by
  classical
  have he := BstLean.Part61.W.hval_euler 3 u
  have h2 := hval2_69 u
  have hd : ∀ i, MvPolynomial.eval u (MvPolynomial.pderiv i
      (MvPolynomial.hsymm (Fin n) ℝ 3)) =
        BstLean.Part58.Kappa.hval 2 u + u i * ((∑ l, u l) + u i) := by
    intro i
    rw [BstLean.Part58.Kappa.pderiv_hsymm_succ i 2, BstLean.Part58.Kappa.pderiv_hsymm_succ i 1,
      MvPolynomial.hsymm_one]
    simp [MvPolynomial.pderiv_X, Pi.single_apply, BstLean.Part58.Kappa.hval]
  simp only [hd] at he
  have : ∑ i, u i * (BstLean.Part58.Kappa.hval 2 u + u i * ((∑ l, u l) + u i)) =
      (∑ i, u i) * BstLean.Part58.Kappa.hval 2 u + (∑ i, u i) * (∑ i, u i ^ 2) +
        ∑ i, u i ^ 3 := by
    have hpt : ∀ i, u i * (BstLean.Part58.Kappa.hval 2 u + u i * ((∑ l, u l) + u i)) =
        u i * BstLean.Part58.Kappa.hval 2 u + (∑ l, u l) * u i ^ 2 + u i ^ 3 := fun i => by ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [this, h2] at he
  push_cast at he
  linarith

theorem k1_74 (x y : Fin n → ℝ) : kJ 3 1 x y = ∑ i, x i * y i :=
  BstLean.Part56.kJ_one 3 (by norm_num) x y

theorem k2_74 (x y : Fin n → ℝ) :
    kJ 3 2 x y = ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2 := by
  rw [BstLean.Part61.W.kJ_hval (d := 3) 2 (by norm_num) x y, hval2_69]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

theorem k3_74 (x y : Fin n → ℝ) :
    kJ 3 3 x y = ((∑ i, x i * y i) ^ 3 + 3 * (∑ i, x i * y i) * (∑ i, x i ^ 2 * y i ^ 2) +
      2 * ∑ i, x i ^ 3 * y i ^ 3) / 6 := by
  rw [BstLean.Part61.W.kJ_hval (d := 3) 3 le_rfl x y, hval3_74]
  have e2 : ∑ i, (x i * y i) ^ 2 = ∑ i, x i ^ 2 * y i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, (x i * y i) ^ 3 = ∑ i, x i ^ 3 * y i ^ 3 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e2, e3]

/-- `k₀` does not depend on its arguments. -/
theorem k0_74 (x y v : Fin n → ℝ) : kJ 3 0 x y = kJ 3 0 v v := by
  unfold kJ
  apply Finset.sum_congr rfl
  intro p _
  rw [BstLean.Part56.MomProg.phiB_zero_indep x v p, BstLean.Part56.MomProg.phiB_zero_indep y v p]

/-! ## `β_j` and `τ` at `d = 3` -/

/-- `B = Σ v_i² x_i²` is `Part69.wv69`; `C = Σ v_i³ x_i³`; `Σ x_i⁶`. -/
noncomputable def cv74 (v x : Fin n → ℝ) : ℝ := ∑ i, v i ^ 3 * x i ^ 3
noncomputable def x6_74 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 6

/-- `β₂ = (s² + B)/(1 + p₄)`. -/
noncomputable def beta2_74 (v x : Fin n → ℝ) : ℝ :=
  (sv69 v x ^ 2 + wv69 v x) / (1 + pw v 4)

/-- `β₃ = (s³ + 3 s B + 2 C)/(1 + 3 p₄ + 2 p₆)`. -/
noncomputable def beta3_74 (v x : Fin n → ℝ) : ℝ :=
  (sv69 v x ^ 3 + 3 * sv69 v x * wv69 v x + 2 * cv74 v x) / (1 + 3 * pw v 4 + 2 * pw v 6)

/-- `τ = 5/3 + Σx⁴ + Σx⁶/3 − s² − (s²+B)²/(2(1+p₄)) − (s³+3sB+2C)²/(6(1+3p₄+2p₆))`. -/
noncomputable def tau33_74 (v x : Fin n → ℝ) : ℝ :=
  5 / 3 + x4_69 x + x6_74 x / 3 - sv69 v x ^ 2 -
    (sv69 v x ^ 2 + wv69 v x) ^ 2 / (2 * (1 + pw v 4)) -
    (sv69 v x ^ 3 + 3 * sv69 v x * wv69 v x + 2 * cv74 v x) ^ 2 /
      (6 * (1 + 3 * pw v 4 + 2 * pw v 6))

theorem pw_even_nonneg74 (v : Fin n → ℝ) (e : ℕ) : 0 ≤ pw v (2 * e) :=
  Finset.sum_nonneg fun i _ => by rw [pow_mul]; positivity

theorem pw4_nonneg74 (v : Fin n → ℝ) : 0 ≤ pw v 4 := pw_even_nonneg74 v 2
theorem pw6_nonneg74 (v : Fin n → ℝ) : 0 ≤ pw v 6 := pw_even_nonneg74 v 3

theorem k2vv_74 (v : Fin n → ℝ) (hv : UnitV v) : kJ 3 2 v v = (1 + pw v 4) / 2 := by
  rw [k2_74, unit_dot69 v hv]
  unfold pw
  congr 2
  · norm_num
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem k3vv_74 (v : Fin n → ℝ) (hv : UnitV v) :
    kJ 3 3 v v = (1 + 3 * pw v 4 + 2 * pw v 6) / 6 := by
  rw [k3_74, unit_dot69 v hv]
  unfold pw
  have e2 : ∑ i, v i ^ 2 * v i ^ 2 = ∑ i, v i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, v i ^ 3 * v i ^ 3 = ∑ i, v i ^ 6 := Finset.sum_congr rfl fun i _ => by ring
  rw [e2, e3]; ring

theorem beta1_74e (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    betaJ 3 1 v x = sv69 v x := by
  unfold betaJ sv69
  rw [k1_74, k1_74, unit_dot69 v hv, div_one]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem beta2_74e (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    betaJ 3 2 v x = beta2_74 v x := by
  unfold betaJ beta2_74
  rw [k2vv_74 v hv, k2_74]
  have hq := pw4_nonneg74 v
  unfold sv69 wv69
  have e1 : ∑ i, x i * v i = ∑ i, v i * x i := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, x i ^ 2 * v i ^ 2 = ∑ i, v i ^ 2 * x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  field_simp

theorem beta3_74e (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    betaJ 3 3 v x = beta3_74 v x := by
  unfold betaJ beta3_74
  rw [k3vv_74 v hv, k3_74]
  have hq := pw4_nonneg74 v
  have hr := pw6_nonneg74 v
  unfold sv69 wv69 cv74
  have e1 : ∑ i, x i * v i = ∑ i, v i * x i := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, x i ^ 2 * v i ^ 2 = ∑ i, v i ^ 2 * x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, x i ^ 3 * v i ^ 3 = ∑ i, v i ^ 3 * x i ^ 3 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3]
  have : (0 : ℝ) < 1 + 3 * pw v 4 + 2 * pw v 6 := by linarith
  field_simp

/-- `τ` at `d = 3` on the unit sphere. -/
theorem tau33_74e (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    tauR 3 v x = tau33_74 v x := by
  have hv' := unit_dot69 v hv
  have hx' : ∑ i, x i * x i = 1 := by simpa [sq] using hx
  unfold tauR KR
  rw [show Finset.Icc 1 3 = {1, 2, 3} by rfl, Finset.sum_insert (by decide),
    Finset.sum_pair (by norm_num)]
  rw [k1_74, k1_74, k1_74, hv', hx', k2vv_74 v hv, k2_74, k2_74, k3vv_74 v hv, k3_74, k3_74]
  have hq := pw4_nonneg74 v
  have hr := pw6_nonneg74 v
  have : (0 : ℝ) < 1 + 3 * pw v 4 + 2 * pw v 6 := by linarith
  unfold tau33_74 sv69 wv69 cv74 x4_69 x6_74
  have e1 : ∑ i, x i * v i = ∑ i, v i * x i := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, x i ^ 2 * v i ^ 2 = ∑ i, v i ^ 2 * x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, x i ^ 3 * v i ^ 3 = ∑ i, v i ^ 3 * x i ^ 3 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i, x i ^ 2 * x i ^ 2 = ∑ i, x i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
  have e6 : ∑ i, x i ^ 3 * x i ^ 3 = ∑ i, x i ^ 6 := Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3, e4, e6, hx']
  field_simp
  ring

/-! ## The reduction of the weights -/

theorem prod_word74 {m : ℕ} (w : Fin m → Fin 4) (f : ℕ → ℝ) :
    ∏ r, f (w r) = f 0 ^ (Finset.univ.filter fun r => w r = 0).card *
      f 1 ^ (Finset.univ.filter fun r => w r = 1).card *
      f 2 ^ (Finset.univ.filter fun r => w r = 2).card *
      f 3 ^ (Finset.univ.filter fun r => w r = 3).card := by
  rw [← Finset.prod_fiberwise' Finset.univ w (fun j : Fin 4 => f j)]
  simp only [Finset.prod_const, Fin.prod_univ_four]
  rfl

/-- The letter counts of a word sum to its length. -/
theorem card_word74 {m : ℕ} (w : Fin m → Fin 4) :
    (Finset.univ.filter fun r => w r = 0).card + (Finset.univ.filter fun r => w r = 1).card +
      (Finset.univ.filter fun r => w r = 2).card + (Finset.univ.filter fun r => w r = 3).card =
        m := by
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := w)
    (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_four] at this
  omega

/-- The letter counts of a key at `(3, 3)`: `c₀ + c₁ + c₂ + c₃ = i − 2l`. -/
theorem cnt_sum74 (κ : KeyRK 3 3) :
    cnt69 κ 0 + cnt69 κ 1 + cnt69 κ 2 + cnt69 κ 3 = (κ.1.1 : ℕ) - 2 * (κ.1.2 : ℕ) :=
  card_word74 κ.2

/-- The integrand of a read weight. -/
noncomputable def integrand33_74 (v : Fin n → ℝ) (l c1 c2 c3 : ℕ) (x : Fin n → ℝ) : ℝ :=
  tau33_74 v x ^ l * sv69 v x ^ c1 * beta2_74 v x ^ c2 * beta3_74 v x ^ c3

theorem integrand33_cont74 (v : Fin n → ℝ) (l c1 c2 c3 : ℕ) :
    Continuous (integrand33_74 v l c1 c2 c3) := by
  unfold integrand33_74 tau33_74 beta2_74 beta3_74 sv69 wv69 cv74 x4_69 x6_74
  fun_prop

/-- **The reduction.** Every weight at `(3, 3)` is
`wickC i l · (1/𝒟)^l · ∫ τ^l s^{c₁} β₂^{c₂} β₃^{c₃} dQ`. -/
theorem wRK33_74 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (κ : KeyRK 3 3) :
    wRK (surrRK n K t v) 3 v κ =
      wickC κ.1.1 κ.1.2 * (1 / BstLean.Part36.DD n 3) ^ (κ.1.2 : ℕ) *
        ∫ x, integrand33_74 v (κ.1.2 : ℕ) (cnt69 κ 1) (cnt69 κ 2) (cnt69 κ 3) x
          ∂surrRK n K t v := by
  have hS := MomProg.surrRK_sphLaw (by omega : 1 ≤ n) K t ht v
  obtain ⟨⟨i, l⟩, w⟩ := κ
  have hprod : ∀ x, ∏ r, betaJ 3 (w r : ℕ) v x =
      sv69 v x ^ cnt69 (⟨(i, l), w⟩ : KeyRK 3 3) 1 *
        beta2_74 v x ^ cnt69 (⟨(i, l), w⟩ : KeyRK 3 3) 2 *
        beta3_74 v x ^ cnt69 (⟨(i, l), w⟩ : KeyRK 3 3) 3 := by
    intro x
    rw [prod_word74 w (fun j => betaJ 3 j v x)]
    rw [MomProg.betaJ_zero (d := 3) v hv x, beta1_74e v hv x, beta2_74e v hv x,
      beta3_74e v hv x, one_pow, one_mul]
    rfl
  unfold wRK
  rw [MomProg.sg_sq (by omega)]
  congr 1
  apply integral_congr_ae
  filter_upwards [hS.sphere] with x hx
  simp only [hprod]
  rw [tau33_74e v hv x hx]
  unfold integrand33_74
  ring

/-- The integrand is odd when `c₁ + c₃` is odd, so its surrogate integral is `0`. -/
theorem odd33_74 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ)
    (l c1 c2 c3 : ℕ) (hodd : Odd (c1 + c3)) :
    ∫ x, integrand33_74 v l c1 c2 c3 x ∂surrRK n K t v = 0 := by
  apply antipodal_odd69 hn K t ht v (integrand33_cont74 v l c1 c2 c3)
  intro x
  have hs : sv69 v (-x) = - sv69 v x := by unfold sv69; simp
  have hw : wv69 v (-x) = wv69 v x := by unfold wv69; simp
  have hc : cv74 v (-x) = - cv74 v x := by
    unfold cv74; simp [Odd.neg_pow (by decide : Odd 3)]
  have h4 : x4_69 (-x) = x4_69 x := by
    unfold x4_69; simp [Even.neg_pow (by decide : Even 4)]
  have h6 : x6_74 (-x) = x6_74 x := by
    unfold x6_74; simp [Even.neg_pow (by decide : Even 6)]
  have hb2 : beta2_74 v (-x) = beta2_74 v x := by unfold beta2_74; rw [hs, hw]; ring
  have hb3 : beta3_74 v (-x) = - beta3_74 v x := by unfold beta3_74; rw [hs, hw, hc]; ring
  have ht' : tau33_74 v (-x) = tau33_74 v x := by
    unfold tau33_74; rw [hs, hw, hc, h4, h6]; ring
  unfold integrand33_74
  rw [hs, hb2, hb3, ht', neg_pow (sv69 v x), neg_pow (beta3_74 v x)]
  have : (-1 : ℝ) ^ c1 * (-1) ^ c3 = -1 := by rw [← pow_add]; exact hodd.neg_one_pow
  linear_combination (tau33_74 v x ^ l * sv69 v x ^ c1 * beta2_74 v x ^ c2 *
    beta3_74 v x ^ c3) * this

/-- `𝒟 = n · C(n+3, 3) = n (n+1)(n+2)(n+3)/6` at `d = 3`. -/
theorem DD3_74 : BstLean.Part36.DD n 3 =
    (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) / 6 := by
  rw [BstLean.Part36.DD_eq]
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
  norm_num [Nat.descFactorial_succ] at h
  have h1 : (n + 3).choose 3 * 6 = (n + 3) * (n + 2) * (n + 1) := by nlinarith [h]
  have h2 : ((n + 3).choose 3 : ℝ) * 6 = ((n : ℝ) + 3) * (n + 2) * (n + 1) := by
    exact_mod_cast h1
  have : ((n + 3).choose 3 : ℝ) = ((n : ℝ) + 3) * (n + 2) * (n + 1) / 6 := by
    rw [← h2]; ring
  rw [this]; ring

theorem wickC_21_74 : wickC 2 1 = 1 := by unfold wickC; norm_num [Nat.factorial]
theorem wickC_31_74 : wickC 3 1 = 3 := by unfold wickC; norm_num [Nat.factorial]
theorem wickC_i0_74 (i : ℕ) : wickC i 0 = 1 := by
  unfold wickC
  have := Nat.factorial_pos i
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul, Nat.sub_zero,
    mul_zero]
  rw [div_self (by positivity)]

end BstLean.Part74

#print axioms BstLean.Part74.k3_74
#print axioms BstLean.Part74.tau33_74e
#print axioms BstLean.Part74.wRK33_74
#print axioms BstLean.Part74.odd33_74
#print axioms BstLean.Part74.DD3_74
