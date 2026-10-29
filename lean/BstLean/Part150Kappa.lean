import BstLean.Part150BF

/-!
# Part 150, item 2: Region A with the paper's constant `κ_4 = −ln cos 1 − 1/2`

Paper source: `onW45-opus-prover.md` §2, Lemma B-F, Step 2 ("`(−ln cos u − u²/2)/u⁴` is
nondecreasing"). The paper uses the positive Taylor coefficients of `tan`; the Lean proof uses
three derivative steps:
`χ(u) = u(1/cos²u − 1) − 3(tan u − u) ≥ 0`, then `φ(u) = u(tan u − u) − 4h(u) ≥ 0`, then
`h(u)/u⁴` is nondecreasing on `(0, 1]`, with `h(u) = −ln cos u − u²/2`.

* `kappa4 = −ln cos 1 − 1/2`; `hK_le : h(u) ≤ κ_4·u⁴` for `0 ≤ u ≤ 1`.
* **`regA_kappa4 : RegA kappa4`**.
* **`lemmaBF1_paper`**, **`lemmaBF2_paper`**: Lemma B-F with `c1F kappa4 J` (the paper's `c_1(J)`,
  the same formula) and `c2F kappa4 J` (the paper's `c_2(J)` with `56807/(6750π³)` in the place of
  `7ζ(3)/π³`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

/-- The constant `κ_4 = −ln cos 1 − 1/2` of the paper (`0.115626…`). -/
noncomputable def kappa4 : ℝ := -Real.log (Real.cos 1) - 1 / 2

/-- `h(u) = −ln cos u − u²/2`. -/
noncomputable def hK (u : ℝ) : ℝ := -Real.log (Real.cos u) - u ^ 2 / 2

lemma cos_pos_Ico {u : ℝ} (h0 : 0 ≤ u) (h1 : u < π / 2) : 0 < Real.cos u :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩

/-- A function with `f 0 = 0` and a nonnegative derivative on `[0, b)` is nonnegative there. -/
lemma nonneg_on_Ico {f f' : ℝ → ℝ} {b : ℝ} (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → x < b → HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 ≤ x → x < b → 0 ≤ f' x) : ∀ x, 0 ≤ x → x < b → 0 ≤ f x := by
  have hm : MonotoneOn f (Ico 0 b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 b)
      (fun x hx => (hd x hx.1 hx.2).continuousAt.continuousWithinAt)
      (fun x hx => ?_) ?_
    · rw [interior_Ico] at hx
      exact (hd x hx.1.le hx.2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hd x hx.1.le hx.2).deriv]
      exact hpos x hx.1.le hx.2
  intro x hx0 hxb
  have := hm (show (0 : ℝ) ∈ Ico 0 b from ⟨le_rfl, lt_of_le_of_lt hx0 hxb⟩)
    (show x ∈ Ico 0 b from ⟨hx0, hxb⟩) hx0
  rwa [h0] at this

lemma hasDerivAt_hK {x : ℝ} (h0 : 0 ≤ x) (h1 : x < π / 2) :
    HasDerivAt hK (Real.tan x - x) x := by
  have hc := cos_pos_Ico h0 h1
  have hl := (Real.hasDerivAt_cos x).log hc.ne'
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) x x := by
    have := (hasDerivAt_pow 2 x).div_const 2
    convert this using 1; ring
  have := hl.neg.sub h2
  have e : Real.tan x - x = -(-Real.sin x / Real.cos x) - x := by
    rw [Real.tan_eq_sin_div_cos]; ring
  rw [e]
  exact this

lemma hasDerivAt_inv_cos_sq {x : ℝ} (hc : 0 < Real.cos x) :
    HasDerivAt (fun u : ℝ => 1 / Real.cos u ^ 2) (2 * Real.sin x / Real.cos x ^ 3) x := by
  have h := ((Real.hasDerivAt_cos x).pow 2).inv (pow_pos hc 2).ne'
  have e : (fun u : ℝ => 1 / Real.cos u ^ 2) = fun u => (Real.cos u ^ 2)⁻¹ := by
    funext u; rw [one_div]
  rw [e]
  convert h using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- `χ(u) = u(1/cos²u − 1) − 3(tan u − u) ≥ 0` on `[0, π/2)`. -/
lemma chi_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < π / 2) :
    0 ≤ x * (1 / Real.cos x ^ 2 - 1) - 3 * (Real.tan x - x) := by
  refine nonneg_on_Ico (b := π / 2)
    (f := fun u => u * (1 / Real.cos u ^ 2 - 1) - 3 * (Real.tan u - u))
    (f' := fun u => (1 * (1 / Real.cos u ^ 2 - 1) + u * (2 * Real.sin u / Real.cos u ^ 3 - 0)) -
      3 * (1 / Real.cos u ^ 2 - 1)) (by simp) ?_ ?_ x h0 h1
  · intro u hu0 hu1
    have hc := cos_pos_Ico hu0 hu1
    have ht := Real.hasDerivAt_tan hc.ne'
    exact ((hasDerivAt_id u).mul ((hasDerivAt_inv_cos_sq hc).sub (hasDerivAt_const u (1 : ℝ)))).sub
      ((ht.sub (hasDerivAt_id u)).const_mul 3)
  · intro u hu0 hu1
    have hc := cos_pos_Ico hu0 hu1
    have hs : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith [Real.pi_pos])
    have hsu : Real.sin u ≤ u := Real.sin_le hu0
    have hc1 : Real.cos u ≤ 1 := Real.cos_le_one u
    have hsc : Real.sin u * Real.cos u ≤ u := by nlinarith
    have hsq : Real.sin u ^ 2 = 1 - Real.cos u ^ 2 := by
      have := Real.sin_sq_add_cos_sq u; linarith
    have e : (1 * (1 / Real.cos u ^ 2 - 1) + u * (2 * Real.sin u / Real.cos u ^ 3 - 0)) -
        3 * (1 / Real.cos u ^ 2 - 1) =
        2 * Real.sin u * (u - Real.sin u * Real.cos u) / Real.cos u ^ 3 := by
      field_simp
      nlinarith [hsq]
    rw [e]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (by linarith)) (pow_pos hc 3).le

lemma hK_zero : hK 0 = 0 := by simp [hK]

/-- `φ(u) = u(tan u − u) − 4h(u) ≥ 0` on `[0, π/2)`. -/
lemma phi_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < π / 2) :
    0 ≤ x * (Real.tan x - x) - 4 * hK x := by
  refine nonneg_on_Ico (b := π / 2)
    (f := fun u => u * (Real.tan u - u) - 4 * hK u)
    (f' := fun u => (1 * (Real.tan u - u) + u * (1 / Real.cos u ^ 2 - 1)) -
      4 * (Real.tan u - u)) (by simp [hK_zero]) ?_ ?_ x h0 h1
  · intro u hu0 hu1
    have hc := cos_pos_Ico hu0 hu1
    have ht := Real.hasDerivAt_tan hc.ne'
    exact ((hasDerivAt_id u).mul (ht.sub (hasDerivAt_id u))).sub
      ((hasDerivAt_hK hu0 hu1).const_mul 4)
  · intro u hu0 hu1
    have := chi_nonneg hu0 hu1
    linarith

lemma hK_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ hK u := by
  have hu : u < π / 2 := by linarith [Real.pi_gt_three]
  have hc := cos_pos_Ico h0 hu
  have hle : Real.cos u ≤ rexp (-(u ^ 2 / 2)) :=
    cos_le_exp (by rw [abs_of_nonneg h0]; linarith)
  have := (Real.log_le_iff_le_exp hc).mpr hle
  unfold hK; linarith

/-- `h(u) ≤ κ_4·u⁴` for `0 ≤ u ≤ 1`. -/
theorem hK_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : hK u ≤ kappa4 * u ^ 4 := by
  rcases h0.eq_or_lt with rfl | hpos
  · simp [hK_zero]
  have h1pi : (1 : ℝ) < π / 2 := by linarith [Real.pi_gt_three]
  have hd : ∀ x ∈ Ioc (0 : ℝ) 1, HasDerivAt (fun u => hK u / u ^ 4)
      (((Real.tan x - x) * x ^ 4 - hK x * (4 * x ^ 3)) / (x ^ 4) ^ 2) x := by
    intro x hx
    have h4 : HasDerivAt (fun u : ℝ => u ^ 4) (4 * x ^ 3) x := by
      simpa using hasDerivAt_pow 4 x
    exact (hasDerivAt_hK hx.1.le (lt_of_le_of_lt hx.2 h1pi)).div h4 (pow_pos hx.1 4).ne'
  have hm : MonotoneOn (fun u => hK u / u ^ 4) (Ioc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) ?_
    · rw [interior_Ioc] at hx
      exact (hd x ⟨hx.1, hx.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hd x ⟨hx.1, hx.2.le⟩).deriv]
      have hφ := phi_nonneg hx.1.le (lt_trans hx.2 h1pi)
      have e : (Real.tan x - x) * x ^ 4 - hK x * (4 * x ^ 3) =
          x ^ 3 * (x * (Real.tan x - x) - 4 * hK x) := by ring
      rw [e]
      exact div_nonneg (mul_nonneg (pow_pos hx.1 3).le hφ) (by positivity)
  have := hm (show u ∈ Ioc (0 : ℝ) 1 from ⟨hpos, h1⟩) (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 from
    ⟨zero_lt_one, le_rfl⟩) h1
  have e1 : hK 1 / 1 ^ 4 = kappa4 := by simp [hK, kappa4]
  simp only at this
  rw [e1, div_le_iff₀ (pow_pos hpos 4)] at this
  exact this

lemma kappa4_nonneg : 0 ≤ kappa4 := by
  have := hK_nonneg (u := 1) zero_le_one le_rfl
  simpa [hK, kappa4] using this

/-- **Region A holds with the paper's constant `κ_4`.** -/
theorem regA_kappa4 : RegA kappa4 := by
  intro J u hu0 hu1
  have hu : u < π / 2 := by linarith [Real.pi_gt_three]
  have hc := cos_pos_Ico hu0 hu
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hh0 := hK_nonneg hu0 hu1
  have hh1 := hK_le hu0 hu1
  have ecos : Real.cos u ^ J = rexp (-((J : ℝ) * u ^ 2 / 2)) * rexp (-((J : ℝ) * hK u)) := by
    rw [← Real.exp_add, ← Real.exp_log hc, ← Real.exp_nat_mul]
    congr 1
    unfold hK; ring
  rw [ecos]
  have h1 : 1 - rexp (-((J : ℝ) * hK u)) ≤ (J : ℝ) * hK u := by
    have := Real.add_one_le_exp (-((J : ℝ) * hK u)); linarith
  have h2 : (J : ℝ) * hK u ≤ J * (kappa4 * u ^ 4) := mul_le_mul_of_nonneg_left hh1 hJ0
  have hE : 0 < rexp (-((J : ℝ) * u ^ 2 / 2)) := Real.exp_pos _
  calc rexp (-((J : ℝ) * u ^ 2 / 2)) - rexp (-((J : ℝ) * u ^ 2 / 2)) * rexp (-((J : ℝ) * hK u))
      = rexp (-((J : ℝ) * u ^ 2 / 2)) * (1 - rexp (-((J : ℝ) * hK u))) := by ring
    _ ≤ rexp (-((J : ℝ) * u ^ 2 / 2)) * (J * (kappa4 * u ^ 4)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hE.le
    _ = kappa4 * J * u ^ 4 * rexp (-((J : ℝ) * u ^ 2 / 2)) := by ring

/-- **Lemma B-F (i) with the paper's constant**: `c1F kappa4 J` is the paper's `c_1(J)`. -/
theorem lemmaBF1_paper {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z)) - psiS s a| ≤ c1F kappa4 J * s / J :=
  lemmaBF1_gen kappa4_nonneg regA_kappa4 hJ a hs

/-- **Lemma B-F (ii) with the paper's Region A constant** (`56807/(6750π³)` in the place of
`7ζ(3)/π³`). -/
theorem lemmaBF2_paper {J : ℕ} (hJ : 1 ≤ J) (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    |binMean J (fun z => relu (a + s * z) ^ 2) - ∫ z, relu (a + s * z) ^ 2 ∂gaussianReal 0 1| ≤
      c2F kappa4 J * s ^ 2 / J :=
  lemmaBF2_gen kappa4_nonneg regA_kappa4 hJ a hs

end BstLean.Part150
