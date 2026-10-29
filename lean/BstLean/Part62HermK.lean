import BstLean.Part62Gram

/-!
# Part 62: Hermite functions through `lap1`, and a one-dimensional weighted fourth-moment bound

The one-dimensional part of omEX-opus-prover Theorem K, without Hermite orthogonality from Mathlib.

* `hco c b`: the coefficient of `x^b` in the probabilists' Hermite polynomial `He_c`
  (`(−1)^k c!/(b! 2^k k!)`, `c − b = 2k`); `He c x = Σ_{b ≤ c} hco c b x^b`.
* `pow_eq_sum_He`: `x^b = Σ_{c ≤ b} lap1 b c · He c x` (inverse of `hco`; alternating binomial sum).
* `He4_eq`: `E He_c⁴ = E4 c`, an exact finite sum of Gaussian moments; `He4_le_gH` a cruder bound.
* `KCrit H κ γ` (criterion C1): `κ ≥ 5`, `E He_c⁴ ≤ (c!)² γ_c²` for `1 ≤ c ≤ H`, and
  `2 (Σ_{1≤c≤H} γ_c/κ^c)² ≤ 1`. `kapE_crit`: `κ = kapE H = max 5 (2 Σ_c √(E4 c)/c!)` satisfies it.
* `oneD_weighted`: under `KCrit H κ γ`, for `q = Σ_{b ≤ s} ρ_b x^b`, `s ≤ H`,
  `u_c = Σ_b ρ_b lap1 b c`: `E q⁴ ≤ (Σ_{c ≤ s} κ^c c! u_c²)²` (Lemma L1 with `a = 2`; the
  mean-zero part through the weighted Cauchy–Schwarz `B² ≤ W · Σ_c He_c²/(κ^c c!)`).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part62

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (gaussMom gaussMom_eq)
open BstLean.Part36 (lap1 lap1_self lap1_zero lap1_eq_zero hermite1)

/-- The coefficient of `x^b` in `He_c`. -/
noncomputable def hco (c b : ℕ) : ℝ :=
  if b ≤ c ∧ Even (c - b) then
    (-1 : ℝ) ^ ((c - b) / 2) * (c.factorial : ℝ) /
      ((b.factorial : ℝ) * 2 ^ ((c - b) / 2) * (((c - b) / 2).factorial : ℝ))
  else 0

/-- The probabilists' Hermite function `He_c(x) = Σ_{b ≤ c} hco c b x^b`. -/
noncomputable def He (c : ℕ) (x : ℝ) : ℝ := ∑ b ∈ Finset.range (c + 1), hco c b * x ^ b

lemma hco_self (c : ℕ) : hco c c = 1 := by
  simp [hco, Nat.factorial_ne_zero]

lemma hco_eq_zero {c b : ℕ} (h : c < b ∨ ¬ Even (c - b)) : hco c b = 0 := by
  unfold hco
  apply if_neg
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · omega
  · exact h h2

lemma lap1_two (b' l m : ℕ) (hl : l ≤ m) :
    lap1 (b' + 2 * m) (b' + 2 * l) =
      ((b' + 2 * m).factorial : ℝ) /
        (((b' + 2 * l).factorial : ℝ) * 2 ^ (m - l) * ((m - l).factorial : ℝ)) := by
  unfold lap1
  have e : b' + 2 * m - (b' + 2 * l) = 2 * (m - l) := by omega
  rw [if_pos ⟨by omega, by rw [e]; exact even_two_mul _⟩, e,
    Nat.mul_div_cancel_left _ (by norm_num)]

lemma hco_two (b' l : ℕ) :
    hco (b' + 2 * l) b' =
      (-1 : ℝ) ^ l * ((b' + 2 * l).factorial : ℝ) /
        ((b'.factorial : ℝ) * 2 ^ l * (l.factorial : ℝ)) := by
  unfold hco
  have e : b' + 2 * l - b' = 2 * l := by omega
  rw [if_pos ⟨by omega, by rw [e]; exact even_two_mul _⟩, e,
    Nat.mul_div_cancel_left _ (by norm_num)]

/-- `Σ_{l ≤ m} (−1)^l C(m, l) = [m = 0]`. -/
lemma alt_choose (m : ℕ) :
    ∑ l ∈ Finset.range (m + 1), (-1 : ℝ) ^ l * (m.choose l : ℝ) = if m = 0 then 1 else 0 := by
  have h := Int.alternating_sum_range_choose (n := m)
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast] at h'
  rw [h']
  split_ifs <;> simp

/-- The inverse relation: `Σ_c lap1 b c · hco c b' = [b = b']` for `b' ≤ b`. -/
lemma lap1_hco (b b' : ℕ) (hb : b' ≤ b) :
    ∑ c ∈ Finset.range (b + 1), lap1 b c * hco c b' = if b' = b then 1 else 0 := by
  classical
  by_cases hpar : Even (b - b')
  · obtain ⟨m, hm⟩ := hpar
    have hbm : b = b' + 2 * m := by omega
    subst hbm
    set f : ℕ → ℝ := fun c => lap1 (b' + 2 * m) c * hco c b' with hf
    have himg : ∑ c ∈ Finset.range (b' + 2 * m + 1), f c =
        ∑ l ∈ Finset.range (m + 1), f (b' + 2 * l) := by
      rw [← Finset.sum_image (s := Finset.range (m + 1)) (g := fun l => b' + 2 * l)
        (fun x _ y _ h => by simp only at h; omega)]
      symm
      apply Finset.sum_subset
      · intro c hc
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
        have := Finset.mem_range.mp hl
        exact Finset.mem_range.mpr (by omega)
      · intro c hc hcn
        have hc' := Finset.mem_range.mp hc
        simp only [hf]
        by_cases h1 : b' ≤ c ∧ Even (c - b')
        · exfalso
          obtain ⟨h1a, ⟨l, hl⟩⟩ := h1
          apply hcn
          exact Finset.mem_image.mpr ⟨l, Finset.mem_range.mpr (by omega), by omega⟩
        · rw [hco_eq_zero (by
            by_contra hh
            push Not at hh
            exact h1 ⟨by omega, hh.2⟩), mul_zero]
    rw [himg]
    have hterm : ∀ l ∈ Finset.range (m + 1), f (b' + 2 * l) =
        ((b' + 2 * m).factorial : ℝ) / ((b'.factorial : ℝ) * 2 ^ m * (m.factorial : ℝ)) *
          ((-1 : ℝ) ^ l * (m.choose l : ℝ)) := by
      intro l hl
      have hlm : l ≤ m := by have := Finset.mem_range.mp hl; omega
      simp only [hf]
      rw [lap1_two b' l m hlm, hco_two]
      have hch : (m.choose l : ℝ) * (l.factorial : ℝ) * ((m - l).factorial : ℝ) = m.factorial := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hlm
      have h2 : (2 : ℝ) ^ m = 2 ^ (m - l) * 2 ^ l := by
        rw [← pow_add]; congr 1; omega
      have hf1 : ((b' + 2 * l).factorial : ℝ) ≠ 0 := by positivity
      have hf2 : ((m - l).factorial : ℝ) ≠ 0 := by positivity
      have hf3 : (l.factorial : ℝ) ≠ 0 := by positivity
      have hf4 : (b'.factorial : ℝ) ≠ 0 := by positivity
      have hf5 : (m.choose l : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hlm).ne'
      rw [h2, ← hch]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, alt_choose]
    by_cases hm0 : m = 0
    · subst hm0; simp [Nat.factorial_ne_zero]
    · rw [if_neg hm0, mul_zero, if_neg (by omega)]
  · rw [if_neg (by rintro rfl; exact hpar (by simp))]
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_range.mp hc
    by_cases h1 : b' ≤ c ∧ Even (c - b')
    · rw [lap1_eq_zero (Or.inr (by
        intro he
        apply hpar
        have : b - b' = (b - c) + (c - b') := by omega
        rw [this]; exact he.add h1.2)), zero_mul]
    · rw [hco_eq_zero (by
        by_contra hh
        push Not at hh
        exact h1 ⟨by omega, hh.2⟩), mul_zero]

/-- **Monomials in the Hermite basis**: `x^b = Σ_{c ≤ b} lap1 b c · He c x`. -/
lemma pow_eq_sum_He (b : ℕ) (x : ℝ) :
    x ^ b = ∑ c ∈ Finset.range (b + 1), lap1 b c * He c x := by
  classical
  have e1 : ∀ c ∈ Finset.range (b + 1), lap1 b c * He c x =
      ∑ b' ∈ Finset.range (b + 1), (lap1 b c * hco c b') * x ^ b' := by
    intro c hc
    have hc' := Finset.mem_range.mp hc
    rw [He, Finset.mul_sum]
    have hsub : Finset.range (c + 1) ⊆ Finset.range (b + 1) :=
      Finset.range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub (fun b' hb' hb'n => by
      have : c < b' := by
        have := Finset.mem_range.mp hb'; have := hb'n; simp at hb'n; omega
      rw [hco_eq_zero (Or.inl this)]; ring)]
    exact Finset.sum_congr rfl fun b' _ => by ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ b' ∈ Finset.range (b + 1), ∑ c ∈ Finset.range (b + 1), (lap1 b c * hco c b') * x ^ b' =
      (if b' = b then 1 else 0) * x ^ b' := by
    intro b' hb'
    rw [← Finset.sum_mul, lap1_hco b b' (by have := Finset.mem_range.mp hb'; omega)]
  rw [Finset.sum_congr rfl e2]
  simp [Finset.sum_ite_eq']

/-- `q = Σ_b ρ_b x^b = Σ_c u_c He_c(x)` with `u_c = Σ_b ρ_b lap1 b c`. -/
lemma poly_eq_sum_He (s : ℕ) (ρ : ℕ → ℝ) (x : ℝ) :
    ∑ b ∈ Finset.range (s + 1), ρ b * x ^ b =
      ∑ c ∈ Finset.range (s + 1), (∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c) * He c x := by
  have e1 : ∀ b ∈ Finset.range (s + 1), ρ b * x ^ b =
      ∑ c ∈ Finset.range (s + 1), ρ b * lap1 b c * He c x := by
    intro b hb
    have hb' := Finset.mem_range.mp hb
    rw [pow_eq_sum_He, Finset.mul_sum]
    have hsub : Finset.range (b + 1) ⊆ Finset.range (s + 1) :=
      Finset.range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub (fun c hc hcn => by
      have : b < c := by simp at hcn; omega
      rw [lap1_eq_zero (Or.inl this)]; ring)]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]

lemma He_zero (x : ℝ) : He 0 x = 1 := by simp [He, hco_self]

lemma int_poly1' (p : Polynomial ℝ) : Integrable (fun x => p.eval x) (gaussianReal 0 1) := by
  rw [show (fun x => p.eval x) = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i from
    funext fun x => Polynomial.eval_eq_sum_range x]
  exact integrable_finsetSum _ fun i _ => (int_pow1' i).const_mul _

lemma int_polypow (p : Polynomial ℝ) (k : ℕ) :
    Integrable (fun x => (p.eval x) ^ k) (gaussianReal 0 1) := by
  have := int_poly1' (p ^ k); simpa only [Polynomial.eval_pow] using this

lemma pow4_sum_le' {β : Type*} (S : Finset β) (u : β → ℝ) :
    (∑ i ∈ S, u i) ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ i ∈ S, u i ^ 4 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := S) (f := u)
  have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => u i ^ 2)
  have h0 : 0 ≤ (∑ i ∈ S, u i) ^ 2 := sq_nonneg _
  calc (∑ i ∈ S, u i) ^ 4 = ((∑ i ∈ S, u i) ^ 2) ^ 2 := by ring
    _ ≤ ((S.card : ℝ) * ∑ i ∈ S, u i ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (S.card : ℝ) ^ 2 * (∑ i ∈ S, u i ^ 2) ^ 2 := by ring
    _ ≤ (S.card : ℝ) ^ 2 * ((S.card : ℝ) * ∑ i ∈ S, (u i ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        rw [← mul_assoc, ← pow_succ]; congr 1
        refine Finset.sum_congr rfl fun i _ => by ring

lemma gaussMom_nonneg (k : ℕ) : 0 ≤ gaussMom k := by
  unfold gaussMom; split_ifs <;> positivity

lemma He_poly (c : ℕ) : ∃ p : Polynomial ℝ, ∀ x, He c x = p.eval x :=
  ⟨∑ b ∈ Finset.range (c + 1), Polynomial.C (hco c b) * Polynomial.X ^ b, fun x => by
    simp [He, Polynomial.eval_finsetSum]⟩

/-- `E He_c⁴ ≤ (c+1)³ Σ_b hco(c,b)⁴ E x^{4b}`. -/
lemma He4_le (c : ℕ) : ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤
    ((c : ℝ) + 1) ^ 3 * ∑ b ∈ Finset.range (c + 1), hco c b ^ 4 * gaussMom (4 * b) := by
  have hpt : ∀ x, He c x ^ 4 ≤ ((c : ℝ) + 1) ^ 3 * ∑ b ∈ Finset.range (c + 1), hco c b ^ 4 * x ^ (4 * b) := by
    intro x
    have := pow4_sum_le' (Finset.range (c + 1)) (fun b => hco c b * x ^ b)
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_pow, ← pow_mul, mul_comm b 4]
  obtain ⟨p, hp⟩ := He_poly c
  have hi : Integrable (fun x => He c x ^ 4) (gaussianReal 0 1) := by
    simp_rw [hp]; exact int_polypow p 4
  have hi2 : Integrable (fun x : ℝ => ((c : ℝ) + 1) ^ 3 *
      ∑ b ∈ Finset.range (c + 1), hco c b ^ 4 * x ^ (4 * b)) (gaussianReal 0 1) :=
    (integrable_finsetSum _ fun b _ => (int_pow1' _).const_mul _).const_mul _
  refine (integral_mono hi hi2 hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_finsetSum _ fun b _ => (int_pow1' _).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, gaussMom_eq]

/-- `gH c = (c+1)³ Σ_b hco(c,b)⁴ E x^{4b} / (c!)²`, so `E He_c⁴ ≤ (c!)² gH c`. -/
noncomputable def gH (c : ℕ) : ℝ :=
  ((c : ℝ) + 1) ^ 3 * (∑ b ∈ Finset.range (c + 1), hco c b ^ 4 * gaussMom (4 * b)) /
    (c.factorial : ℝ) ^ 2

lemma gH_nonneg (c : ℕ) : 0 ≤ gH c := by
  unfold gH
  have : 0 ≤ ∑ b ∈ Finset.range (c + 1), hco c b ^ 4 * gaussMom (4 * b) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (by positivity) (gaussMom_nonneg _)
  positivity

lemma He4_le_gH (c : ℕ) : ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤ (c.factorial : ℝ) ^ 2 * gH c := by
  refine (He4_le c).trans (le_of_eq ?_)
  unfold gH
  have : (c.factorial : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp

/-- The exact fourth moment `E He_c⁴ = Σ_{b₁..b₄} Π hco(c, bᵢ) · E x^{b₁+b₂+b₃+b₄}`. -/
noncomputable def E4 (c : ℕ) : ℝ :=
  ∑ b1 ∈ Finset.range (c + 1), ∑ b2 ∈ Finset.range (c + 1), ∑ b3 ∈ Finset.range (c + 1),
    ∑ b4 ∈ Finset.range (c + 1),
      hco c b1 * hco c b2 * hco c b3 * hco c b4 * gaussMom (b1 + b2 + b3 + b4)

lemma He4_eq (c : ℕ) : ∫ x, He c x ^ 4 ∂gaussianReal 0 1 = E4 c := by
  have e : ∀ x : ℝ, He c x ^ 4 = ∑ b1 ∈ Finset.range (c + 1), ∑ b2 ∈ Finset.range (c + 1),
      ∑ b3 ∈ Finset.range (c + 1), ∑ b4 ∈ Finset.range (c + 1),
        (hco c b1 * hco c b2 * hco c b3 * hco c b4) * x ^ (b1 + b2 + b3 + b4) := by
    intro x
    have h4 : He c x ^ 4 = (He c x * He c x) * (He c x * He c x) := by ring
    rw [h4, He, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b1 _ => Finset.sum_congr rfl fun b2 _ =>
      Finset.sum_congr rfl fun b3 _ => Finset.sum_congr rfl fun b4 _ => ?_
    simp only [pow_add]; ring
  simp_rw [e]
  unfold E4
  have hi : ∀ (k : ℕ) (a : ℝ), Integrable (fun x : ℝ => a * x ^ k) (gaussianReal 0 1) :=
    fun k a => (int_pow1' k).const_mul a
  rw [integral_finsetSum _ fun b1 _ => integrable_finsetSum _ fun b2 _ =>
    integrable_finsetSum _ fun b3 _ => integrable_finsetSum _ fun b4 _ => hi _ _]
  refine Finset.sum_congr rfl fun b1 _ => ?_
  rw [integral_finsetSum _ fun b2 _ => integrable_finsetSum _ fun b3 _ =>
    integrable_finsetSum _ fun b4 _ => hi _ _]
  refine Finset.sum_congr rfl fun b2 _ => ?_
  rw [integral_finsetSum _ fun b3 _ => integrable_finsetSum _ fun b4 _ => hi _ _]
  refine Finset.sum_congr rfl fun b3 _ => ?_
  rw [integral_finsetSum _ fun b4 _ => hi _ _]
  refine Finset.sum_congr rfl fun b4 _ => ?_
  rw [integral_const_mul, gaussMom_eq]

/-- Cauchy–Schwarz under `N(0,1)`. -/
lemma cs1 (f g : ℝ → ℝ) (hf : Integrable (fun x => f x ^ 2) (gaussianReal 0 1))
    (hg : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hfg : Integrable (fun x => f x * g x) (gaussianReal 0 1)) :
    (∫ x, f x * g x ∂gaussianReal 0 1) ^ 2 ≤
      (∫ x, f x ^ 2 ∂gaussianReal 0 1) * ∫ x, g x ^ 2 ∂gaussianReal 0 1 := by
  have hquad (t : ℝ) : 0 ≤ (∫ x, f x ^ 2 ∂gaussianReal 0 1) * (t * t) +
      (2 * ∫ x, f x * g x ∂gaussianReal 0 1) * t + (∫ x, g x ^ 2 ∂gaussianReal 0 1) := by
    have h : 0 ≤ ∫ x, (t * f x + g x) ^ 2 ∂gaussianReal 0 1 := integral_nonneg fun _ => sq_nonneg _
    have he : (fun x => (t * f x + g x) ^ 2) = fun x =>
        (t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x)) + g x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t ^ 2 * f x ^ 2) (gaussianReal 0 1) := hf.const_mul _
    have i2 : Integrable (fun x => (2 * t) * (f x * g x)) (gaussianReal 0 1) := hfg.const_mul _
    have i12 : Integrable (fun x => t ^ 2 * f x ^ 2 + (2 * t) * (f x * g x)) (gaussianReal 0 1) :=
      i1.add i2
    rw [he, integral_add i12 hg, integral_add i1 i2, integral_const_mul,
      integral_const_mul] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

/-- **The criterion (C1)** for `κ` at degree `H`: `κ ≥ 5`, `γ ≥ 0`, `E He_c⁴ ≤ (c!)² γ_c²` for
`1 ≤ c ≤ H`, and `2 (Σ_{1≤c≤H} γ_c/κ^c)² ≤ 1`. -/
def KCrit (H : ℕ) (κ : ℝ) (γ : ℕ → ℝ) : Prop :=
  5 ≤ κ ∧ (∀ c, 0 ≤ γ c) ∧
    (∀ c ∈ Finset.Icc 1 H, ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤ (c.factorial : ℝ) ^ 2 * γ c ^ 2) ∧
    2 * (∑ c ∈ Finset.Icc 1 H, γ c / κ ^ c) ^ 2 ≤ 1

/-- The explicit general `κ_H = max 5 (2 Σ_{1≤c≤H} √(E He_c⁴)/c!)`, with the exact moments `E4`. -/
noncomputable def kapE (H : ℕ) : ℝ :=
  max 5 (2 * ∑ c ∈ Finset.Icc 1 H, Real.sqrt (E4 c) / (c.factorial : ℝ))

lemma E4_nonneg (c : ℕ) : 0 ≤ E4 c := by
  rw [← He4_eq]; exact integral_nonneg fun _ => by positivity

lemma kapE_crit (H : ℕ) : KCrit H (kapE H) (fun c => Real.sqrt (E4 c) / (c.factorial : ℝ)) := by
  have hk5 : 5 ≤ kapE H := le_max_left _ _
  refine ⟨hk5, fun c => by positivity, fun c _ => ?_, ?_⟩
  · rw [div_pow, Real.sq_sqrt (E4_nonneg c), He4_eq]
    have : (c.factorial : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp; rfl
  set A := ∑ c ∈ Finset.Icc 1 H, Real.sqrt (E4 c) / (c.factorial : ℝ) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun c _ => by positivity
  have hkA : 2 * A ≤ kapE H := le_max_right _ _
  have hk0 : 0 < kapE H := by linarith
  have hle : ∑ c ∈ Finset.Icc 1 H, Real.sqrt (E4 c) / (c.factorial : ℝ) / kapE H ^ c ≤
      A / kapE H := by
    rw [hA, Finset.sum_div]
    refine Finset.sum_le_sum fun c hc => ?_
    have hc1 := (Finset.mem_Icc.mp hc).1
    apply div_le_div_of_nonneg_left (by positivity) hk0
    calc kapE H = kapE H ^ 1 := (pow_one _).symm
      _ ≤ kapE H ^ c := pow_le_pow_right₀ (by linarith) hc1
  have h0 : 0 ≤ ∑ c ∈ Finset.Icc 1 H, Real.sqrt (E4 c) / (c.factorial : ℝ) / kapE H ^ c :=
    Finset.sum_nonneg fun c _ => by positivity
  have hhalf : A / kapE H ≤ 1 / 2 := by
    rw [div_le_iff₀ hk0]; linarith
  have := pow_le_pow_left₀ h0 (hle.trans hhalf) 2
  linarith

/-- `E[He_a² He_c²] ≤ a! γ_a c! γ_c` when `E He⁴ ≤ (c!)² γ²` (Cauchy–Schwarz). -/
lemma He22_le (a c : ℕ) (γa γc : ℝ) (ha0 : 0 ≤ γa) (hc0 : 0 ≤ γc)
    (ha : ∫ x, He a x ^ 4 ∂gaussianReal 0 1 ≤ (a.factorial : ℝ) ^ 2 * γa ^ 2)
    (hc : ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤ (c.factorial : ℝ) ^ 2 * γc ^ 2) :
    ∫ x, He a x ^ 2 * He c x ^ 2 ∂gaussianReal 0 1 ≤
      ((a.factorial : ℝ) * γa) * ((c.factorial : ℝ) * γc) := by
  obtain ⟨pa, hpa⟩ := He_poly a
  obtain ⟨pc, hpc⟩ := He_poly c
  have h := cs1 (fun x => He a x ^ 2) (fun x => He c x ^ 2)
    (by simp_rw [hpa, ← pow_mul]; exact int_polypow pa _)
    (by simp_rw [hpc, ← pow_mul]; exact int_polypow pc _)
    (by simp_rw [hpa, hpc]; have := int_poly1' (pa ^ 2 * pc ^ 2); simpa using this)
  have e4 : ∀ d : ℕ, (fun x => (He d x ^ 2) ^ 2) = fun x => He d x ^ 4 := fun d => by
    funext x; ring
  simp only [e4] at h
  have hsq : (∫ x, He a x ^ 2 * He c x ^ 2 ∂gaussianReal 0 1) ^ 2 ≤
      (((a.factorial : ℝ) * γa) * ((c.factorial : ℝ) * γc)) ^ 2 := by
    refine h.trans ?_
    have e : (((a.factorial : ℝ) * γa) * ((c.factorial : ℝ) * γc)) ^ 2 =
        ((a.factorial : ℝ) ^ 2 * γa ^ 2) * ((c.factorial : ℝ) ^ 2 * γc ^ 2) := by ring
    rw [e]
    apply mul_le_mul ha hc (integral_nonneg fun _ => by positivity) (by positivity)
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

/-- **Weighted mean-zero fourth moment**: with `W = Σ_{1≤c≤s} κ^c c! u_c²` and
`Γ = Σ_{1≤c≤H} γ_c/κ^c` (`E He_c⁴ ≤ (c!)² γ_c²`), `E(Σ_{1≤c≤s} u_c He_c)⁴ ≤ Γ² W²`. -/
lemma B4_He (H s : ℕ) (hs : s ≤ H) (κ : ℝ) (hκ : 0 < κ) (γ : ℕ → ℝ) (hγ0 : ∀ c, 0 ≤ γ c)
    (hγ : ∀ c ∈ Finset.Icc 1 H, ∫ x, He c x ^ 4 ∂gaussianReal 0 1 ≤ (c.factorial : ℝ) ^ 2 * γ c ^ 2)
    (u : ℕ → ℝ) :
    ∫ x, (∑ c ∈ Finset.Icc 1 s, u c * He c x) ^ 4 ∂gaussianReal 0 1 ≤
      (∑ c ∈ Finset.Icc 1 H, γ c / κ ^ c) ^ 2 *
        (∑ c ∈ Finset.Icc 1 s, κ ^ c * (c.factorial : ℝ) * u c ^ 2) ^ 2 := by
  set wt : ℕ → ℝ := fun c => κ ^ c * (c.factorial : ℝ) with hwt
  have hwt0 : ∀ c, 0 < wt c := fun c => by simp only [hwt]; positivity
  set W := ∑ c ∈ Finset.Icc 1 s, κ ^ c * (c.factorial : ℝ) * u c ^ 2 with hW
  set S : ℝ → ℝ := fun x => ∑ c ∈ Finset.Icc 1 s, He c x ^ 2 / wt c with hS
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun c _ =>
    div_nonneg (sq_nonneg _) (hwt0 c).le
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun c _ => by positivity
  -- pointwise Cauchy–Schwarz
  have hpt2 : ∀ x, (∑ c ∈ Finset.Icc 1 s, u c * He c x) ^ 2 ≤ W * S x := by
    intro x
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 s)
      (fun c => u c * Real.sqrt (wt c)) (fun c => He c x / Real.sqrt (wt c))
    have e1 : ∀ c ∈ Finset.Icc 1 s, u c * Real.sqrt (wt c) * (He c x / Real.sqrt (wt c)) =
        u c * He c x := fun c _ => by
      have : Real.sqrt (wt c) ≠ 0 := (Real.sqrt_pos.mpr (hwt0 c)).ne'
      field_simp
    have e2 : ∀ c ∈ Finset.Icc 1 s, (u c * Real.sqrt (wt c)) ^ 2 = κ ^ c * (c.factorial : ℝ) * u c ^ 2 :=
      fun c _ => by rw [mul_pow, Real.sq_sqrt (hwt0 c).le]; simp only [hwt]; ring
    have e3 : ∀ c ∈ Finset.Icc 1 s, (He c x / Real.sqrt (wt c)) ^ 2 = He c x ^ 2 / wt c :=
      fun c _ => by rw [div_pow, Real.sq_sqrt (hwt0 c).le]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
    exact h
  have hpt : ∀ x, (∑ c ∈ Finset.Icc 1 s, u c * He c x) ^ 4 ≤ W ^ 2 * S x ^ 2 := by
    intro x
    have := pow_le_pow_left₀ (sq_nonneg _) (hpt2 x) 2
    calc (∑ c ∈ Finset.Icc 1 s, u c * He c x) ^ 4 = ((∑ c ∈ Finset.Icc 1 s, u c * He c x) ^ 2) ^ 2 := by
          ring
      _ ≤ (W * S x) ^ 2 := this
      _ = W ^ 2 * S x ^ 2 := by ring
  choose P hP using He_poly
  have hiL : Integrable (fun x => (∑ c ∈ Finset.Icc 1 s, u c * He c x) ^ 4) (gaussianReal 0 1) := by
    have := int_polypow (∑ c ∈ Finset.Icc 1 s, Polynomial.C (u c) * P c) 4
    simpa [Polynomial.eval_finsetSum, hP] using this
  have hi22 : ∀ a c, Integrable (fun x => He a x ^ 2 * He c x ^ 2) (gaussianReal 0 1) := by
    intro a c
    have := int_poly1' (P a ^ 2 * P c ^ 2)
    simpa [hP] using this
  have hSsq : ∀ x, S x ^ 2 = ∑ a ∈ Finset.Icc 1 s, ∑ c ∈ Finset.Icc 1 s,
      (1 / (wt a * wt c)) * (He a x ^ 2 * He c x ^ 2) := by
    intro x
    simp only [hS]
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    field_simp
  have hiR : Integrable (fun x => W ^ 2 * S x ^ 2) (gaussianReal 0 1) := by
    simp_rw [hSsq]
    exact (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
      (hi22 a c).const_mul _).const_mul _
  refine (integral_mono hiL hiR hpt).trans ?_
  rw [integral_const_mul]
  simp_rw [hSsq]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => (hi22 a c).const_mul _]
  have hES : ∑ a ∈ Finset.Icc 1 s, ∫ x, ∑ c ∈ Finset.Icc 1 s,
      (1 / (wt a * wt c)) * (He a x ^ 2 * He c x ^ 2) ∂gaussianReal 0 1 ≤
      (∑ c ∈ Finset.Icc 1 s, γ c / κ ^ c) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [integral_finsetSum _ fun c _ => (hi22 a c).const_mul _]
    refine Finset.sum_le_sum fun c hc => ?_
    rw [integral_const_mul]
    have hH : ∀ d ∈ Finset.Icc 1 s, d ∈ Finset.Icc 1 H := fun d hd => by
      have := Finset.mem_Icc.mp hd; exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans hs⟩
    have h := He22_le a c (γ a) (γ c) (hγ0 a) (hγ0 c) (hγ a (hH a ha)) (hγ c (hH c hc))
    have hpos : 0 < wt a * wt c := mul_pos (hwt0 a) (hwt0 c)
    calc 1 / (wt a * wt c) * ∫ x, He a x ^ 2 * He c x ^ 2 ∂gaussianReal 0 1
        ≤ 1 / (wt a * wt c) * (((a.factorial : ℝ) * γ a) * ((c.factorial : ℝ) * γ c)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = γ a / κ ^ a * (γ c / κ ^ c) := by
          simp only [hwt]
          have : (a.factorial : ℝ) ≠ 0 := by positivity
          have : (c.factorial : ℝ) ≠ 0 := by positivity
          have : κ ^ a ≠ 0 := by positivity
          have : κ ^ c ≠ 0 := by positivity
          field_simp
  have hmono : ∑ c ∈ Finset.Icc 1 s, γ c / κ ^ c ≤ ∑ c ∈ Finset.Icc 1 H, γ c / κ ^ c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hs)
      (fun c _ _ => div_nonneg (hγ0 c) (by positivity))
  have hm0 : 0 ≤ ∑ c ∈ Finset.Icc 1 s, γ c / κ ^ c :=
    Finset.sum_nonneg fun c _ => div_nonneg (hγ0 c) (by positivity)
  calc W ^ 2 * ∑ a ∈ Finset.Icc 1 s, ∫ x, ∑ c ∈ Finset.Icc 1 s,
        (1 / (wt a * wt c)) * (He a x ^ 2 * He c x ^ 2) ∂gaussianReal 0 1
      ≤ W ^ 2 * (∑ c ∈ Finset.Icc 1 s, γ c / κ ^ c) ^ 2 := mul_le_mul_of_nonneg_left hES (sq_nonneg _)
    _ ≤ W ^ 2 * (∑ c ∈ Finset.Icc 1 H, γ c / κ ^ c) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0 hmono 2) (sq_nonneg _)
    _ = _ := by ring

/-- The arithmetic of the one-dimensional step (omEX-opus-prover, Lemma L1, with `a = 2`). -/
lemma L1_arith (u0 V F T3 W Γ κ : ℝ) (hV : 0 ≤ V) (hF0 : 0 ≤ F) (hF : F ≤ Γ ^ 2 * W ^ 2)
    (hT : T3 ^ 2 ≤ V * F) (hW : κ * V ≤ W) (hκ : 5 ≤ κ) (hΓ : 2 * Γ ^ 2 ≤ 1) :
    u0 ^ 4 + 6 * u0 ^ 2 * V + 4 * u0 * T3 + F ≤ (u0 ^ 2 + W) ^ 2 := by
  have h1 : (4 * u0 * T3) ^ 2 ≤ (4 * u0 ^ 2 * V + F) ^ 2 := by
    have : (4 * u0 * T3) ^ 2 = 16 * u0 ^ 2 * T3 ^ 2 := by ring
    rw [this]
    have h16 : 16 * u0 ^ 2 * T3 ^ 2 ≤ 16 * u0 ^ 2 * (V * F) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    nlinarith [sq_nonneg (4 * u0 ^ 2 * V - F)]
  have h2 : 4 * u0 * T3 ≤ 4 * u0 ^ 2 * V + F := (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have hW0 : 0 ≤ W := le_trans (by nlinarith) hW
  have h3 : 10 * u0 ^ 2 * V ≤ 2 * u0 ^ 2 * W := by
    have : 10 * V ≤ 2 * W := by nlinarith
    nlinarith [sq_nonneg u0]
  have h4 : 2 * F ≤ W ^ 2 := by
    have : 2 * (Γ ^ 2 * W ^ 2) ≤ W ^ 2 := by nlinarith [sq_nonneg W]
    linarith
  nlinarith

/-- **One-dimensional weighted fourth moment** (Lemma L1 of omEX-opus-prover with the explicit
any `κ ≥ 5` that satisfies the criterion `KCrit H κ γ`): for `q = Σ_{b ≤ s} ρ_b x^b`, `s ≤ H`,
and `u_c = Σ_b ρ_b lap1 b c`, `E q⁴ ≤ (Σ_{c ≤ s} κ^c c! u_c²)²`. -/
theorem oneD_weighted (H s : ℕ) (hs : s ≤ H) (κ : ℝ) (γ : ℕ → ℝ) (hK : KCrit H κ γ)
    (ρ : ℕ → ℝ) :
    ∫ x, (∑ b ∈ Finset.range (s + 1), ρ b * x ^ b) ^ 4 ∂gaussianReal 0 1 ≤
      (∑ c ∈ Finset.range (s + 1), κ ^ c * (c.factorial : ℝ) *
        (∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c) ^ 2) ^ 2 := by
  obtain ⟨hκ5, hγ0, hγ, hΓ⟩ := hK
  set u : ℕ → ℝ := fun c => ∑ b ∈ Finset.range (s + 1), ρ b * lap1 b c with hu
  set u0 := u 0 with hu0
  set qP : Polynomial ℝ := ∑ b ∈ Finset.range (s + 1), Polynomial.C (ρ b) * Polynomial.X ^ b with hqP
  have hq : ∀ x, ∑ b ∈ Finset.range (s + 1), ρ b * x ^ b = qP.eval x := by
    intro x; simp [hqP, Polynomial.eval_finsetSum]
  set B : ℝ → ℝ := fun x => qP.eval x - u0 with hB
  have hBP : ∀ k, Integrable (fun x => B x ^ k) (gaussianReal 0 1) := by
    intro k
    have := int_polypow (qP - Polynomial.C u0) k
    simpa [hB] using this
  have hBHe : ∀ x, B x = ∑ c ∈ Finset.Icc 1 s, u c * He c x := by
    intro x
    simp only [hB]
    rw [← hq, poly_eq_sum_He, sum_range_zero_Icc, He_zero, mul_one]
    ring
  -- mean
  have hEq : ∫ x, qP.eval x ∂gaussianReal 0 1 = u0 := by
    simp_rw [← hq]
    rw [integral_finsetSum _ fun b _ => (int_pow1' b).const_mul _]
    simp only [hu0, hu]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, gaussMom_eq, lap1_zero]
  have hiq : Integrable (fun x => qP.eval x) (gaussianReal 0 1) := int_poly1' qP
  have hEB : ∫ x, B x ∂gaussianReal 0 1 = 0 := by
    simp only [hB]
    rw [integral_sub hiq (integrable_const _), hEq, integral_const]
    simp
  -- second moment
  have hEq2 : ∫ x, (qP.eval x) ^ 2 ∂gaussianReal 0 1 =
      ∑ c ∈ Finset.range (s + 1), (c.factorial : ℝ) * u c ^ 2 := by
    simp_rw [← hq]; exact fischer_sq s ρ
  set V := ∑ c ∈ Finset.Icc 1 s, (c.factorial : ℝ) * u c ^ 2 with hV
  have hqB : ∀ x, qP.eval x = u0 + B x := fun x => by simp only [hB]; ring
  have hEB2 : ∫ x, B x ^ 2 ∂gaussianReal 0 1 = V := by
    have e : ∀ x, (qP.eval x) ^ 2 = u0 ^ 2 + 2 * u0 * B x + B x ^ 2 := fun x => by rw [hqB]; ring
    simp_rw [e] at hEq2
    have j1 : Integrable (fun x => 2 * u0 * B x) (gaussianReal 0 1) :=
      ((hBP 1).const_mul (2 * u0)).congr (by filter_upwards with x; simp)
    have j01 : Integrable (fun x => u0 ^ 2 + 2 * u0 * B x) (gaussianReal 0 1) :=
      (integrable_const _).add j1
    rw [integral_add j01 (hBP 2), integral_add (integrable_const _) j1, integral_const_mul, hEB,
      integral_const, sum_range_zero_Icc] at hEq2
    simp only [probReal_univ, smul_eq_mul, one_mul, Nat.factorial_zero, Nat.cast_one,
      mul_zero, add_zero] at hEq2
    rw [hV]; linarith
  -- fourth moment of B
  set F := ∫ x, B x ^ 4 ∂gaussianReal 0 1 with hFdef
  set W := ∑ c ∈ Finset.Icc 1 s, κ ^ c * (c.factorial : ℝ) * u c ^ 2 with hW
  have hF : F ≤ (∑ c ∈ Finset.Icc 1 H, γ c / κ ^ c) ^ 2 * W ^ 2 := by
    rw [hFdef]; simp_rw [hBHe]; exact B4_He H s hs κ (by linarith) γ hγ0 hγ u
  have hF0 : 0 ≤ F := integral_nonneg fun x => by positivity
  set T3 := ∫ x, B x ^ 3 ∂gaussianReal 0 1 with hT3def
  have hT3 : T3 ^ 2 ≤ V * F := by
    have h := cs1 B (fun x => B x ^ 2) (hBP 2) (by simpa [← pow_mul] using hBP 4)
      (by simpa [← pow_succ'] using hBP 3)
    have e1 : (fun x => B x * B x ^ 2) = fun x => B x ^ 3 := by funext x; ring
    have e2 : (fun x => (B x ^ 2) ^ 2) = fun x => B x ^ 4 := by funext x; ring
    simp only [e1, e2] at h
    rw [← hEB2]; exact h
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun c _ => by positivity
  -- the fourth moment of q
  have hq4 : ∫ x, (∑ b ∈ Finset.range (s + 1), ρ b * x ^ b) ^ 4 ∂gaussianReal 0 1 =
      u0 ^ 4 + 6 * u0 ^ 2 * V + 4 * u0 * T3 + F := by
    simp_rw [hq, hqB]
    have e : ∀ x, (u0 + B x) ^ 4 = u0 ^ 4 + ((4 * u0 ^ 3) * B x + ((6 * u0 ^ 2) * B x ^ 2 +
        ((4 * u0) * B x ^ 3 + B x ^ 4))) := fun x => by ring
    simp_rw [e]
    have i1 : Integrable (fun x => (4 * u0 ^ 3) * B x) (gaussianReal 0 1) :=
      ((hBP 1).const_mul (4 * u0 ^ 3)).congr (by filter_upwards with x; simp)
    have i2 : Integrable (fun x => (6 * u0 ^ 2) * B x ^ 2) (gaussianReal 0 1) :=
      (hBP 2).const_mul _
    have i3 : Integrable (fun x => (4 * u0) * B x ^ 3) (gaussianReal 0 1) := (hBP 3).const_mul _
    have i34 : Integrable (fun x => (4 * u0) * B x ^ 3 + B x ^ 4) (gaussianReal 0 1) :=
      i3.add (hBP 4)
    have i234 : Integrable (fun x => (6 * u0 ^ 2) * B x ^ 2 + ((4 * u0) * B x ^ 3 + B x ^ 4))
      (gaussianReal 0 1) := i2.add i34
    have i1234 : Integrable (fun x => (4 * u0 ^ 3) * B x + ((6 * u0 ^ 2) * B x ^ 2 +
      ((4 * u0) * B x ^ 3 + B x ^ 4))) (gaussianReal 0 1) := i1.add i234
    rw [integral_add (integrable_const _) i1234, integral_add i1 i234, integral_add i2 i34,
      integral_add i3 (hBP 4), integral_const_mul, integral_const_mul, integral_const_mul, hEB,
      hEB2, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hq4]
  -- weights
  have hWV : κ * V ≤ W := by
    rw [hV, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hc1 := (Finset.mem_Icc.mp hc).1
    have : κ ≤ κ ^ c := by
      calc κ = κ ^ 1 := (pow_one _).symm
        _ ≤ κ ^ c := pow_le_pow_right₀ (by linarith) hc1
    have h0 : 0 ≤ (c.factorial : ℝ) * u c ^ 2 := by positivity
    nlinarith
  have hsum : ∑ c ∈ Finset.range (s + 1), κ ^ c * (c.factorial : ℝ) * u c ^ 2 = u0 ^ 2 + W := by
    rw [sum_range_zero_Icc]; simp [hu0]; rfl
  rw [hsum]
  exact L1_arith u0 V F T3 W _ κ hV0 hF0 hF hT3 hWV hκ5 hΓ


end BstLean.Part62
