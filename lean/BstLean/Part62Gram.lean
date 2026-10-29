import BstLean.Part36Hermite
import BstLean.Part29GaussProd

/-!
# Part 62: an explicit one-dimensional Gram bound (replaces the compactness constant of Part 48)

`Part48Hyper.pdH` obtains `λ > 0` with `E_x(Σ_{b=1}^s r_b (x^b − m_b))² ≥ λ Σ r_b²` from a
compactness minimum, so its fourth-moment constant has no formula. This file proves the same bound
with the explicit value `lamE H = 1 / ((H + 1) (1 + H·H!)^{2H})`, for every `s ≤ H`.

Route.
1. `fischer_sq`: for `q = Σ_{b ≤ s} ρ_b x^b`, `E q² = Σ_{c ≤ s} c! u_c²` with
   `u_c = Σ_b ρ_b lap1 b c` (`Part36.hermite1`, the Gaussian–Fischer identity).
2. With `ρ_0 = −Σ_{b ≥ 1} r_b m_b`, `u_0 = 0` and `u_c = Σ_{b ≥ 1} r_b lap1 b c` for `c ≥ 1`.
3. `lap1` is unit lower triangular with entries in `[0, H!]` (`lap1_le_fact`), so back substitution
   (`tri_bound`) gives `r_c² ≤ M^{2(s−c)} Σ u²`, `M = 1 + H·H!`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part62

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (gaussMom gaussMom_eq)
open BstLean.Part36 (lap1 lap1_self lap1_zero lap1_eq_zero hermite1)

lemma int_pow1' (b : ℕ) : Integrable (fun x : ℝ => x ^ b) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
    (μ := gaussianReal 0 1) (by simp) b

lemma lap1_nonneg (a c : ℕ) : 0 ≤ lap1 a c := by
  unfold lap1; split_ifs <;> positivity

lemma lap1_le_fact (a c : ℕ) : lap1 a c ≤ a.factorial := by
  unfold lap1
  split_ifs
  · apply div_le_self (by positivity)
    have h1 : (1 : ℝ) ≤ (c.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((a - c) / 2) := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ (((a - c) / 2).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  · positivity

/-- **Gaussian–Fischer quadratic form**: `E(Σ_{b≤s} ρ_b x^b)² = Σ_{c≤s} c! (Σ_b ρ_b lap1 b c)²`. -/
lemma fischer_sq (s : ℕ) (ρ : ℕ → ℝ) :
    ∫ x, (∑ b ∈ Finset.range (s + 1), ρ b * x ^ b) ^ 2 ∂gaussianReal 0 1 =
      ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) *
        (∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c) ^ 2 := by
  have hsq : ∀ x : ℝ, (∑ b ∈ Finset.range (s + 1), ρ b * x ^ b) ^ 2 =
      ∑ a ∈ Finset.range (s + 1), ∑ b ∈ Finset.range (s + 1), (ρ a * ρ b) * x ^ (a + b) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pow_add]; ring
  simp_rw [hsq]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (int_pow1' _).const_mul _]
  have hin : ∀ a ∈ Finset.range (s + 1), ∫ x, ∑ b ∈ Finset.range (s + 1), (ρ a * ρ b) * x ^ (a + b)
      ∂gaussianReal 0 1 = ∑ b ∈ Finset.range (s + 1), (ρ a * ρ b) *
        ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * lap1 a c * lap1 b c := by
    intro a ha
    rw [integral_finsetSum _ fun b _ => (int_pow1' _).const_mul _]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [integral_const_mul, gaussMom_eq]
    congr 1
    have ha' := Finset.mem_range.mp ha
    exact (hermite1 a b s (by omega)).symm
  rw [Finset.sum_congr rfl hin]
  have e1 : ∀ a b : ℕ, (ρ a * ρ b) * ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * lap1 a c * lap1 b c
      = ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * (ρ a * lap1 a c) * (ρ b * lap1 b c) := by
    intro a b; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  have e2 : ∀ c : ℕ, (c.factorial : ℝ) * (∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c) ^ 2 =
      ∑ a ∈ Finset.range (s + 1), ∑ b ∈ Finset.range (s + 1),
        (c.factorial : ℝ) * (ρ a * lap1 a c) * (ρ b * lap1 b c) := by
    intro c; rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e1, e2]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma sum_range_zero_Icc (s : ℕ) (f : ℕ → ℝ) :
    ∑ b ∈ Finset.range (s + 1), f b = f 0 + ∑ b ∈ Finset.Icc 1 s, f b := by
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  have : Finset.Icc 1 s = (Finset.range s).image (· + 1) := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨b - 1, by omega, by omega⟩
    · rintro ⟨i, h1, rfl⟩; omega
  rw [this, Finset.sum_image (fun i _ j _ h => by simpa using h)]

/-- **Back substitution** for a unit lower-triangular matrix with entries bounded by `L`. -/
lemma tri_bound (s : ℕ) (T : ℕ → ℕ → ℝ) (L M : ℝ) (hL : 0 ≤ L) (hM : 1 + s * L ≤ M)
    (hdiag : ∀ c, T c c = 1) (hlow : ∀ b c, b < c → T b c = 0)
    (hb : ∀ b ∈ Finset.Icc 1 s, ∀ c ∈ Finset.Icc 1 s, |T b c| ≤ L)
    (r : ℕ → ℝ) (A : ℝ) (hA : ∀ c ∈ Finset.Icc 1 s, |∑ b ∈ Finset.Icc 1 s, r b * T b c| ≤ A) :
    ∀ c ∈ Finset.Icc 1 s, |r c| ≤ M ^ (s - c) * A := by
  have hM1 : 1 ≤ M := by have : 0 ≤ (s : ℝ) * L := by positivity
                         linarith
  intro c hc
  induction hj : s - c using Nat.strong_induction_on generalizing c with
  | _ j ih =>
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA c hc)
  set F := (Finset.Icc 1 s).filter (fun b => c < b) with hF
  have hsplit : ∑ b ∈ Finset.Icc 1 s, r b * T b c = r c + ∑ b ∈ F, r b * T b c := by
    have hpt : ∀ b ∈ Finset.Icc 1 s, r b * T b c =
        (if b = c then r c else 0) + (if c < b then r b * T b c else 0) := by
      intro b _
      rcases lt_trichotomy b c with h | h | h
      · rw [hlow b c h, if_neg (by omega), if_neg (by omega)]; ring
      · subst h; rw [hdiag, if_pos rfl, if_neg (lt_irrefl _)]; ring
      · rw [if_neg (by omega), if_pos h]; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq' _ _ _, if_pos hc,
      hF, Finset.sum_filter]
  have hu := hA c hc
  rw [hsplit] at hu
  have hrc : |r c| ≤ A + ∑ b ∈ F, |r b| * L := by
    have h1 : |r c| ≤ |r c + ∑ b ∈ F, r b * T b c| + |∑ b ∈ F, r b * T b c| := by
      have := abs_sub (r c + ∑ b ∈ F, r b * T b c) (∑ b ∈ F, r b * T b c)
      simpa using this
    have h2 : |∑ b ∈ F, r b * T b c| ≤ ∑ b ∈ F, |r b| * L := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hbF => ?_)
      have hbF' := Finset.mem_filter.mp hbF
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb b hbF'.1 c hc) (abs_nonneg _)
    linarith
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · have hFe : F = ∅ := by
      rw [hF, Finset.filter_eq_empty_iff]
      intro b hbI
      have := Finset.mem_Icc.mp hbI
      omega
    rw [hFe, Finset.sum_empty, add_zero] at hrc
    rw [hj0, pow_zero, one_mul]; exact hrc
  · have hterm : ∀ b ∈ F, |r b| * L ≤ L * (M ^ (j - 1) * A) := by
      intro b hbF
      have hbF' := Finset.mem_filter.mp hbF
      have hbs := Finset.mem_Icc.mp hbF'.1
      have hlt : s - b < j := by omega
      have := ih (s - b) hlt b hbF'.1 rfl
      have hpow : M ^ (s - b) ≤ M ^ (j - 1) := pow_le_pow_right₀ hM1 (by omega)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_right hpow hA0)) hL
    have hcard : (F.card : ℝ) ≤ s := by
      have : F.card ≤ (Finset.Icc 1 s).card := Finset.card_filter_le _ _
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact_mod_cast this
    have hsum : ∑ b ∈ F, |r b| * L ≤ s * (L * (M ^ (j - 1) * A)) := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have hMj : M ^ j = M * M ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hp1 : 1 ≤ M ^ (j - 1) := one_le_pow₀ hM1
    have hP0 : 0 ≤ M ^ (j - 1) * A := by positivity
    calc |r c| ≤ A + s * (L * (M ^ (j - 1) * A)) := by linarith
      _ ≤ M ^ (j - 1) * A + (s * L) * (M ^ (j - 1) * A) := by
          have : A ≤ M ^ (j - 1) * A := by nlinarith
          nlinarith
      _ = (1 + s * L) * (M ^ (j - 1) * A) := by ring
      _ ≤ M * (M ^ (j - 1) * A) := mul_le_mul_of_nonneg_right hM hP0
      _ = M ^ j * A := by rw [hMj]; ring

/-- The explicit Gram constant `λ_H = 1 / ((H + 1)(1 + H·H!)^{2H})`. -/
noncomputable def lamE (H : ℕ) : ℝ := 1 / (((H : ℝ) + 1) * (1 + (H : ℝ) * (H.factorial : ℝ)) ^ (2 * H))

lemma lamE_pos (H : ℕ) : 0 < lamE H := by unfold lamE; positivity

/-- **Explicit one-dimensional Gram bound** (replaces `Part48Hyper.pdH`). -/
theorem pdH_explicit (H s : ℕ) (hs : s ≤ H) (r : ℕ → ℝ) :
    lamE H * ∑ b ∈ Finset.Icc 1 s, r b ^ 2 ≤
      ∫ x, (∑ b ∈ Finset.Icc 1 s, r b * (x ^ b - gaussMom b)) ^ 2 ∂gaussianReal 0 1 := by
  classical
  set ρ : ℕ → ℝ := fun b => if b = 0 then -∑ b' ∈ Finset.Icc 1 s, r b' * gaussMom b' else r b
    with hρ
  have hρI : ∀ b ∈ Finset.Icc 1 s, ρ b = r b := by
    intro b hb; have := (Finset.mem_Icc.mp hb).1; simp [hρ]; omega
  have hq : ∀ x : ℝ, ∑ b ∈ Finset.Icc 1 s, r b * (x ^ b - gaussMom b) =
      ∑ b ∈ Finset.range (s + 1), ρ b * x ^ b := by
    intro x
    rw [sum_range_zero_Icc]
    have e3 : ∑ b ∈ Finset.Icc 1 s, ρ b * x ^ b = ∑ b ∈ Finset.Icc 1 s, r b * x ^ b :=
      Finset.sum_congr rfl fun b hb => by rw [hρI b hb]
    rw [e3]
    have e4 : ρ 0 = -∑ b' ∈ Finset.Icc 1 s, r b' * gaussMom b' := by simp [hρ]
    rw [e4, pow_zero, mul_one]
    simp_rw [mul_sub_left_distrib]
    rw [Finset.sum_sub_distrib]
    ring
  simp_rw [hq]
  rw [fischer_sq]
  set u : ℕ → ℝ := fun c => ∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c with hu
  have huI : ∀ c ∈ Finset.Icc 1 s, u c = ∑ b ∈ Finset.Icc 1 s, r b * lap1 b c := by
    intro c hc
    have hc1 := (Finset.mem_Icc.mp hc).1
    simp only [hu]
    rw [sum_range_zero_Icc, lap1_eq_zero (Or.inl (by omega)), mul_zero, zero_add]
    exact Finset.sum_congr rfl fun b hb => by rw [hρI b hb]
  set S := ∑ c ∈ Finset.Icc 1 s, u c ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlow : S ≤ ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * u c ^ 2 := by
    rw [sum_range_zero_Icc]
    have h0 : 0 ≤ ((0 : ℕ).factorial : ℝ) * u 0 ^ 2 := by positivity
    have : S ≤ ∑ c ∈ Finset.Icc 1 s, (c.factorial : ℝ) * u c ^ 2 := by
      refine Finset.sum_le_sum fun c _ => ?_
      have : (1 : ℝ) ≤ c.factorial := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
      nlinarith [sq_nonneg (u c)]
    linarith
  -- back substitution
  set M : ℝ := 1 + (H : ℝ) * (H.factorial : ℝ) with hM
  have hM1 : 1 ≤ M := by have : 0 ≤ (H : ℝ) * (H.factorial : ℝ) := by positivity
                         linarith
  have htri := tri_bound s lap1 (H.factorial : ℝ) M (by positivity)
    (by rw [hM]; have : (s : ℝ) ≤ H := by exact_mod_cast hs
        have : (s : ℝ) * (H.factorial : ℝ) ≤ (H : ℝ) * (H.factorial : ℝ) :=
          mul_le_mul_of_nonneg_right this (by positivity)
        linarith)
    lap1_self (fun b c h => lap1_eq_zero (Or.inl h))
    (fun b hb c _ => by
      rw [abs_of_nonneg (lap1_nonneg b c)]
      have hb' := (Finset.mem_Icc.mp hb).2
      refine (lap1_le_fact b c).trans ?_
      exact_mod_cast Nat.factorial_le (hb'.trans hs))
    r (Real.sqrt S) (fun c hc => by
      rw [← huI c hc]
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun c => u c ^ 2) (fun _ _ => sq_nonneg _) hc)
  have hr2 : ∀ c ∈ Finset.Icc 1 s, r c ^ 2 ≤ M ^ (2 * H) * S := by
    intro c hc
    have h1 := htri c hc
    have h2 : r c ^ 2 ≤ (M ^ (s - c) * Real.sqrt S) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [mul_pow, Real.sq_sqrt hS0, ← pow_mul] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 ?_) hS0)
    omega
  have hsum : ∑ c ∈ Finset.Icc 1 s, r c ^ 2 ≤ ((H : ℝ) + 1) * (M ^ (2 * H) * S) := by
    refine (Finset.sum_le_sum hr2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simp only [Nat.card_Icc, add_tsub_cancel_right]
    have : (s : ℝ) ≤ H := by exact_mod_cast hs
    linarith
  have hpos : 0 < ((H : ℝ) + 1) * M ^ (2 * H) := by positivity
  have hl : lamE H = 1 / (((H : ℝ) + 1) * M ^ (2 * H)) := by rw [lamE, hM]
  rw [hl, one_div, ← div_eq_inv_mul, div_le_iff₀ hpos]
  calc ∑ c ∈ Finset.Icc 1 s, r c ^ 2 ≤ ((H : ℝ) + 1) * (M ^ (2 * H) * S) := hsum
    _ = S * (((H : ℝ) + 1) * M ^ (2 * H)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hlow hpos.le

end BstLean.Part62
