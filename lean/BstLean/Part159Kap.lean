import BstLean.Part159Asin
import BstLean.Part159Pi
import BstLean.Part159Paper

/-!
# Part 159 (file `Kap`): the hypothesis `ConstK` on the constant `κ̃` is PROVED for `n ≥ 13 225`

Role: `delegations/statements/p159-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `theorem7-01-statement-program.tex`, step 1:
`κ̃ = (√(1 − r̃²) + r̃(π̃/2 + Q_{T_κ}(r̃)))/π̃`, `r̃ = 2N·c̃_N²`. The exact value is
`κ₁ = κ(r)`, `r = 2N·c_N² = E_u κ(u₁)` (file `Q1`), `κ(t) = (√(1 − t²) + t(π/2 + arcsin t))/π`.

* `Tkap_spec`: `T_κ ≥ 1` and `0.355·0.1014^{T_κ} ≤ 10⁻⁵/n²`.
* `arcsin_lip`, `sqrt_lip`: the two Lipschitz bounds on `[0, 1/2]`.
* `kappa_pert`: the perturbation of the formula of `κ` (real numbers only).
* `kapT_close`: `|κ̃ − κ₁| ≤ 2·10⁻⁵/n²` for `n ≥ 13 225`.
* **`constK`**: `ConstK n` for every `n ≥ 13 225`.
-/

namespace BstLean.Part159

open Real Set
open BstLean.Part130
open BstLean.Part137 (cN q1)
open BstLean.Part140 (kap1)
open BstLean.Part141 (cN_nonneg cN_le_half)
open BstLean.Part157 (cNt piT rNt kapT Tkap QTsum)

/-- The defining property of `T_κ`. -/
theorem Tkap_spec {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ Tkap n ∧ (355 / 1000 : ℝ) * (1014 / 10000) ^ Tkap n ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hε : (0 : ℝ) < 1 / (10 ^ 5 * (n : ℝ) ^ 2) / (355 / 1000) := by positivity
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1014 / 10000 : ℝ) < 1)
  have hne : {T : ℕ | 1 ≤ T ∧
      (355 / 1000 : ℝ) * (1014 / 10000) ^ T ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2)}.Nonempty := by
    refine ⟨T + 1, by omega, ?_⟩
    have h1 : (1014 / 10000 : ℝ) ^ (T + 1) ≤ (1014 / 10000 : ℝ) ^ T :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [lt_div_iff₀ (by norm_num)] at hT
    linarith
  exact Nat.sInf_mem hne

/-- The inverse sine on `[0, 1/2]`: `0 ≤ arcsin b − arcsin a ≤ 2(b − a)` for `0 ≤ a ≤ b ≤ 1/2`. -/
lemma arcsin_lip {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    0 ≤ arcsin b - arcsin a ∧ arcsin b - arcsin a ≤ 2 * (b - a) := by
  have hd : ∀ y ∈ Icc a b, HasDerivAt arcsin (1 / √(1 - y ^ 2)) y := fun y hy =>
    Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])
  have hsq : ∀ y ∈ Icc a b, (1 : ℝ) / 2 ≤ √(1 - y ^ 2) := by
    intro y hy
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [hy.1, hy.2]
  constructor
  · have h := le_of_hasDeriv_nonneg hab hd (fun y _ => by positivity)
    linarith
  · have h := le_of_hasDeriv_nonneg (f := fun y => 2 * y - arcsin y)
      (f' := fun y => 2 * 1 - 1 / √(1 - y ^ 2)) hab
      (fun y hy => ((hasDerivAt_id y).const_mul 2).sub (hd y hy))
      (fun y hy => by
        have h1 := hsq y (Ioo_subset_Icc_self hy)
        have h2 : 1 / √(1 - y ^ 2) ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) h1
        norm_num at h2 ⊢
        linarith)
    linarith

/-- `|√(1 − a²) − √(1 − b²)| ≤ |a − b|` for `a, b ∈ [0, 1/2]`. -/
lemma sqrt_lip {a b : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) (hb : 0 ≤ b) (hb2 : b ≤ 1 / 2) :
    |√(1 - a ^ 2) - √(1 - b ^ 2)| ≤ |a - b| := by
  have hA : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hB : (0 : ℝ) ≤ 1 - b ^ 2 := by nlinarith
  have hsA : (1 : ℝ) / 2 ≤ √(1 - a ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsB : (1 : ℝ) / 2 ≤ √(1 - b ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have e : (√(1 - a ^ 2) - √(1 - b ^ 2)) * (√(1 - a ^ 2) + √(1 - b ^ 2)) =
      (b - a) * (b + a) := by
    have h1 := Real.mul_self_sqrt hA
    have h2 := Real.mul_self_sqrt hB
    nlinarith
  have h3 : |√(1 - a ^ 2) - √(1 - b ^ 2)| * (√(1 - a ^ 2) + √(1 - b ^ 2)) =
      |b - a| * (b + a) := by
    have := congrArg abs e
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < √(1 - a ^ 2) + √(1 - b ^ 2)),
      abs_of_nonneg (by linarith : 0 ≤ b + a)] at this
    exact this
  have h4 : 0 ≤ |√(1 - a ^ 2) - √(1 - b ^ 2)| := abs_nonneg _
  have h5 : 0 ≤ |b - a| := abs_nonneg _
  rw [abs_sub_comm a b]
  nlinarith

/-- **The perturbation of the formula of `κ`** (real numbers). -/
lemma kappa_pert {r rt P Pt Q S St as ast dr dp dq : ℝ}
    (hr1 : 0 ≤ r) (hr2 : r ≤ 1 / 2)
    (hP1 : 314 / 100 ≤ P) (hP2 : P ≤ 315 / 100) (hPt1 : 313 / 100 ≤ Pt) (hPt2 : Pt ≤ 316 / 100)
    (hS1 : 0 ≤ S) (hS2 : S ≤ 1) (has1 : 0 ≤ as) (has2 : as ≤ 1)
    (hQ1 : 0 ≤ Q) (hQ2 : Q ≤ 2)
    (hdr : |rt - r| ≤ dr) (hdp : |Pt - P| ≤ dp) (hS : |St - S| ≤ dr)
    (hq : |Q - ast| ≤ dq) (ha : |ast - as| ≤ 2 * dr) :
    |(St + rt * (Pt / 2 + Q)) / Pt - (S + r * (P / 2 + as)) / P| ≤ 2 * dr + dp + dq := by
  have hdr0 : 0 ≤ dr := (abs_nonneg _).trans hdr
  have hdp0 : 0 ≤ dp := (abs_nonneg _).trans hdp
  have hdq0 : 0 ≤ dq := (abs_nonneg _).trans hq
  have hPpos : 0 < P := by linarith
  have hPtpos : 0 < Pt := by linarith
  set num := S + r * (P / 2 + as) with hnum
  set numt := St + rt * (Pt / 2 + Q) with hnumt
  have hnum0 : 0 ≤ num := by rw [hnum]; positivity
  have hnum2 : num ≤ 3 := by
    rw [hnum]
    nlinarith [mul_le_mul hr2 (by linarith : P / 2 + as ≤ 3) (by linarith) (by norm_num :
      (0 : ℝ) ≤ 1 / 2)]
  have hdiff : numt - num = (St - S) + (rt - r) * (Pt / 2 + Q) +
      r * ((Pt - P) / 2 + (Q - ast) + (ast - as)) := by
    rw [hnum, hnumt]; ring
  have hB : |Pt / 2 + Q| ≤ 4 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h1 : |(rt - r) * (Pt / 2 + Q)| ≤ dr * 4 := by
    rw [abs_mul]
    exact mul_le_mul hdr hB (abs_nonneg _) hdr0
  have h2 : |r * ((Pt - P) / 2 + (Q - ast) + (ast - as))| ≤ 1 / 2 * (dp / 2 + dq + 2 * dr) := by
    rw [abs_mul, abs_of_nonneg hr1]
    have h3 : |(Pt - P) / 2 + (Q - ast) + (ast - as)| ≤ dp / 2 + dq + 2 * dr := by
      have := abs_add_three ((Pt - P) / 2) (Q - ast) (ast - as)
      have h4 : |(Pt - P) / 2| ≤ dp / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
      linarith
    exact mul_le_mul hr2 h3 (abs_nonneg _) (by norm_num)
  have hΔ : |numt - num| ≤ 6 * dr + dp + dq := by
    rw [hdiff]
    have := abs_add_three (St - S) ((rt - r) * (Pt / 2 + Q))
      (r * ((Pt - P) / 2 + (Q - ast) + (ast - as)))
    linarith
  have e : numt / Pt - num / P = (numt - num) / Pt + num * (P - Pt) / (P * Pt) := by
    field_simp
    ring
  rw [e]
  have t1 : |(numt - num) / Pt| ≤ (6 * dr + dp + dq) / (313 / 100) := by
    rw [abs_div, abs_of_pos hPtpos]
    exact div_le_div₀ (by positivity) hΔ (by norm_num) hPt1
  have t2 : |num * (P - Pt) / (P * Pt)| ≤ 3 * dp / (314 / 100 * (313 / 100)) := by
    rw [abs_div, abs_mul, abs_of_nonneg hnum0, abs_of_pos (mul_pos hPpos hPtpos), abs_sub_comm]
    exact div_le_div₀ (by positivity) (mul_le_mul hnum2 hdp (abs_nonneg _) (by norm_num))
      (by norm_num) (mul_le_mul hP1 hPt1 (by norm_num) hPpos.le)
  refine (abs_add_le _ _).trans ?_
  have e1 : (6 * dr + dp + dq) / (313 / 100) = 600 / 313 * dr + 100 / 313 * dp +
      100 / 313 * dq := by ring
  have e2 : 3 * dp / (314 / 100 * (313 / 100)) = 30000 / 98282 * dp := by ring
  rw [e1] at t1
  rw [e2] at t2
  nlinarith

lemma QTsum_nonneg (T : ℕ) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ QTsum T v := by
  rw [QTsum_eq]
  exact Finset.sum_nonneg fun j _ => div_nonneg (mul_nonneg (bB_pos j).le (pow_nonneg hv _))
    (by positivity)

/-- `κ(t) = (√(1 − t²) + t(π/2 + arcsin t))/π`. -/
lemma kappa_arcsin (t : ℝ) : kappa t = (√(1 - t ^ 2) + t * (π / 2 + arcsin t)) / π := by
  unfold kappa
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  congr 2
  ring

/-- **The computed constant `κ̃` against `κ₁`**: `|κ̃ − κ₁| ≤ 6·10⁻²⁴/n² + 10⁻²³/n² + 10⁻⁵/n²`
for every `n ≥ 13 225`. -/
theorem kapT_close {n : ℕ} (hn : 13225 ≤ n) :
    |kapT n - kap1 (2 * n)| ≤
      2 * (3 / (10 ^ 24 * (n : ℝ) ^ 2)) + 1 / (10 ^ 23 * (n : ℝ) ^ 2) +
        1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hpi1 := Real.pi_gt_d6
  have hpi2 := Real.pi_lt_d2
  -- `r`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = cN (2 * n) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact cN_nonneg _
  have hc1 : c ≤ 1 / 2 := by rw [hc]; exact cN_le_half (by omega)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 2 * (2 * (n : ℝ)) * c ^ 2 := ⟨_, rfl⟩
  have hq : q1 (e0 (2 * n)) = r := by
    rw [q1_eq_cN (by omega), hNcast, hr, hc]
  obtain ⟨hw1, hw2⟩ := rN_window (N := 2 * n) (by omega)
  rw [hNcast, ← hc, ← hr] at hw1 hw2
  have hr1 : 317 / 1000 ≤ r := by
    refine le_trans ?_ hw1
    rw [div_le_div_iff₀ (by norm_num) Real.pi_pos]
    linarith
  have hr2 : r ≤ 31835 / 100000 := by
    refine hw2.trans ?_
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  -- `r̃`
  have hcl := cNt_close hn1
  rw [← hc] at hcl
  obtain ⟨ct, hct⟩ : ∃ ct : ℝ, ct = cNt n := ⟨_, rfl⟩
  rw [← hct] at hcl
  obtain ⟨-, hcw⟩ := cN_even_window hn
  rw [← hc] at hcw
  have hcn : c ^ 2 * (n : ℝ) ≤ 8 / 100 := by
    rw [le_div_iff₀ (by positivity)] at hcw
    linarith only [hcw]
  obtain ⟨rt, hrt⟩ : ∃ rt : ℝ, rt = rNt n := ⟨_, rfl⟩
  have hrte : rt = 2 * (2 * (n : ℝ)) * ct ^ 2 := by rw [hrt, hct]; rfl
  have hdr : |rt - r| ≤ 3 / (10 ^ 24 * (n : ℝ) ^ 2) := by
    have e : rt - r = 2 * (2 * (n : ℝ)) * ((ct - c) * (ct + c)) := by rw [hrte, hr]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (2 * (n : ℝ))), abs_mul]
    have hsm : c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ≤ c / 100 :=
      div_le_div_of_nonneg_left hc0 (by norm_num) (by nlinarith)
    have h1 : |ct + c| ≤ 201 / 100 * c := by
      have h2 := abs_add_le (ct - c) (2 * c)
      have e2 : ct - c + 2 * c = ct + c := by ring
      rw [e2, abs_of_nonneg (by linarith only [hc0] : (0 : ℝ) ≤ 2 * c)] at h2
      linarith only [h2, hcl, hsm]
    have h3 : |ct - c| * |ct + c| ≤ c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * (201 / 100 * c) :=
      mul_le_mul hcl h1 (abs_nonneg _) (by positivity)
    have h4 : 2 * (2 * (n : ℝ)) * (c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * (201 / 100 * c)) ≤
        3 / (10 ^ 24 * (n : ℝ) ^ 2) := by
      have e3 : 2 * (2 * (n : ℝ)) * (c / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * (201 / 100 * c)) =
          (c ^ 2 * (n : ℝ)) * (804 / 100 / (3 * 10 ^ 23)) / (n : ℝ) ^ 2 := by
        field_simp
        ring
      rw [e3, div_le_div_iff₀ (by positivity) (by positivity)]
      have h5 : c ^ 2 * (n : ℝ) * (804 / 100 / (3 * 10 ^ 23)) ≤
          8 / 100 * (804 / 100 / (3 * 10 ^ 23)) :=
        mul_le_mul_of_nonneg_right hcn (by norm_num)
      have h6 : (8 : ℝ) / 100 * (804 / 100 / (3 * 10 ^ 23)) ≤ 3 / 10 ^ 24 := by norm_num
      have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      nlinarith
    exact (mul_le_mul_of_nonneg_left h3 (by positivity)).trans h4
  have hdrs : 3 / (10 ^ 24 * (n : ℝ) ^ 2) ≤ 1 / 10 ^ 23 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_pos hnpos hnpos]
  obtain ⟨hrta, hrtb⟩ := abs_le.mp hdr
  have hrt1 : 316 / 1000 ≤ rt := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 1 / 1000 := by norm_num
    linarith
  have hrt2 : rt ≤ 3184 / 10000 := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 5 / 100000 := by norm_num
    linarith
  -- `π̃`
  have hdp := piT_close hn1
  obtain ⟨Pt, hPt⟩ : ∃ Pt : ℝ, Pt = piT n := ⟨_, rfl⟩
  rw [← hPt] at hdp
  have hdps : 1 / (10 ^ 23 * (n : ℝ) ^ 2) ≤ 1 / 10 ^ 23 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨hPa, hPb⟩ := abs_le.mp hdp
  have hPt1 : 313 / 100 ≤ Pt := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 1 / 1000 := by norm_num
    linarith
  have hPt2 : Pt ≤ 316 / 100 := by
    have : (1 : ℝ) / 10 ^ 23 ≤ 1 / 1000 := by norm_num
    linarith
  have hr0 : (0 : ℝ) ≤ r := le_trans (by norm_num) hr1
  have hrh : r ≤ 1 / 2 := hr2.trans (by norm_num)
  have hrt0 : (0 : ℝ) ≤ rt := le_trans (by norm_num) hrt1
  have hrth : rt ≤ 1 / 2 := hrt2.trans (by norm_num)
  have hrtlt : rt < 1 := lt_of_le_of_lt hrt2 (by norm_num)
  -- the square roots and the inverse sines
  have hS := sqrt_lip (a := rt) (b := r) hrt0 hrth hr0 hrh
  have has := arcsin_lip (a := 0) (b := r) le_rfl hr0 hrh
  rw [Real.arcsin_zero, sub_zero, sub_zero] at has
  have hast : |arcsin rt - arcsin r| ≤ 2 * (3 / (10 ^ 24 * (n : ℝ) ^ 2)) := by
    rcases le_total r rt with h | h
    · obtain ⟨a1, a2⟩ := arcsin_lip (a := r) (b := rt) hr0 h hrth
      rw [abs_of_nonneg a1]
      have h5 : rt - r ≤ 3 / (10 ^ 24 * (n : ℝ) ^ 2) := (le_abs_self _).trans hdr
      linarith only [a2, h5]
    · obtain ⟨a1, a2⟩ := arcsin_lip (a := rt) (b := r) hrt0 h hrh
      rw [abs_sub_comm, abs_of_nonneg a1]
      have h5 : r - rt ≤ 3 / (10 ^ 24 * (n : ℝ) ^ 2) := by
        have h6 := neg_abs_le (rt - r)
        linarith only [h6, hdr]
      linarith only [a2, h5]
  -- the partial sum
  obtain ⟨hT1, hT2⟩ := Tkap_spec hn1
  obtain ⟨q1', q2'⟩ := QTsum_err hT1 (v := rt) hrt0 hrtlt
  have hrt2sq : rt ^ 2 ≤ 1014 / 10000 :=
    (pow_le_pow_left₀ hrt0 hrt2 2).trans (by norm_num)
  have htail : rt * (rt ^ 2) ^ Tkap n / (1 - rt ^ 2) ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
    refine le_trans ?_ hT2
    have h1 : (rt ^ 2) ^ Tkap n ≤ (1014 / 10000 : ℝ) ^ Tkap n :=
      pow_le_pow_left₀ (sq_nonneg _) hrt2sq _
    have h2 : (0 : ℝ) < 1 - rt ^ 2 := by linarith only [hrt2sq]
    rw [div_le_iff₀ h2]
    have h3 : rt ≤ 355 / 1000 * (1 - rt ^ 2) := by linarith only [hrt2sq, hrt2]
    have hp : (0 : ℝ) ≤ (1014 / 10000 : ℝ) ^ Tkap n := by positivity
    have hp2 : (0 : ℝ) ≤ (rt ^ 2) ^ Tkap n := by positivity
    calc rt * (rt ^ 2) ^ Tkap n ≤ 355 / 1000 * (1 - rt ^ 2) * (rt ^ 2) ^ Tkap n :=
          mul_le_mul_of_nonneg_right h3 hp2
      _ ≤ 355 / 1000 * (1 - rt ^ 2) * (1014 / 10000 : ℝ) ^ Tkap n :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 355 / 1000 * (1014 / 10000 : ℝ) ^ Tkap n * (1 - rt ^ 2) := by ring
  have hQabs : |QTsum (Tkap n) rt - arcsin rt| ≤ 1 / (10 ^ 5 * (n : ℝ) ^ 2) := by
    rw [abs_sub_comm, abs_of_nonneg q1']
    exact q2'.trans htail
  have hQ0 := QTsum_nonneg (Tkap n) (v := rt) hrt0
  have hastle : arcsin rt ≤ 1 := by
    obtain ⟨-, a2⟩ := arcsin_lip (a := 0) (b := rt) le_rfl hrt0 hrth
    rw [Real.arcsin_zero, sub_zero, sub_zero] at a2
    linarith only [a2, hrth]
  have hQ2 : QTsum (Tkap n) rt ≤ 2 := by linarith only [q1', hastle]
  -- assemble
  have hS1 : (0 : ℝ) ≤ √(1 - r ^ 2) := Real.sqrt_nonneg _
  have hS2 : √(1 - r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    nlinarith only [sq_nonneg r]
  have key := kappa_pert (r := r) (rt := rt) (P := π) (Pt := Pt) (Q := QTsum (Tkap n) rt)
    (S := √(1 - r ^ 2)) (St := √(1 - rt ^ 2)) (as := arcsin r) (ast := arcsin rt)
    (dr := 3 / (10 ^ 24 * (n : ℝ) ^ 2)) (dp := 1 / (10 ^ 23 * (n : ℝ) ^ 2))
    (dq := 1 / (10 ^ 5 * (n : ℝ) ^ 2))
    hr0 hrh (by linarith only [hpi1]) (by linarith only [hpi2]) hPt1 hPt2 hS1 hS2 has.1
    (by linarith only [has.2, hrh])
    hQ0 hQ2 hdr hdp (hS.trans hdr) hQabs hast
  have e1 : kapT n = (√(1 - rt ^ 2) + rt * (Pt / 2 + QTsum (Tkap n) rt)) / Pt := by
    rw [hrt, hPt]; rfl
  have e2 : kap1 (2 * n) = (√(1 - r ^ 2) + r * (π / 2 + arcsin r)) / π := by
    unfold kap1
    rw [hq, kappa_arcsin]
  rw [e1, e2]
  exact key

/-- **The hypothesis `ConstK n` holds for every `n ≥ 13 225`.** -/
theorem constK {n : ℕ} (hn : 13225 ≤ n) : ConstK n := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hk := kapT_close hn
  have hm2 : mW n ≤ n ^ 4 := by
    rw [mW_le_iff]
    calc n ^ 7 ≤ n ^ 7 * n := Nat.le_mul_of_pos_right _ (by omega)
      _ = (n ^ 4) ^ 2 := by ring
  have hm2' : (mW n : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) ≤ mW n := Nat.cast_nonneg _
  have hB : |kapT n - kap1 (2 * n)| ≤ 2 / (10 ^ 5 * (n : ℝ) ^ 2) := by
    refine hk.trans (le_of_eq_of_le (b := (2 * (3 / 10 ^ 24) + 1 / 10 ^ 23 + 1 / 10 ^ 5) /
      (n : ℝ) ^ 2) ?_ ?_)
    · field_simp
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      nlinarith
  have hsq : (kapT n - kap1 (2 * n)) ^ 2 ≤ (2 / (10 ^ 5 * (n : ℝ) ^ 2)) ^ 2 := by
    rw [← sq_abs (kapT n - kap1 (2 * n))]
    exact pow_le_pow_left₀ (abs_nonneg _) hB 2
  unfold ConstK
  have h1 : (kapT n - kap1 (2 * n)) ^ 2 * (mW n : ℝ) ≤
      (2 / (10 ^ 5 * (n : ℝ) ^ 2)) ^ 2 * (n : ℝ) ^ 4 :=
    mul_le_mul hsq hm2' hm0 (sq_nonneg _)
  refine h1.trans (le_of_eq_of_le (b := (4 : ℝ) / 10 ^ 10) ?_ (by norm_num))
  field_simp
  norm_num

end BstLean.Part159

open BstLean.Part159 in
#print axioms Tkap_spec
open BstLean.Part159 in
#print axioms kappa_pert
open BstLean.Part159 in
#print axioms kapT_close
open BstLean.Part159 in
#print axioms constK
