import BstLean.Part263Energy
import BstLean.Part264Operator
import BstLean.Part264FiniteCentre
import BstLean.Part273Moment

/-! Part 277, caps: the energy, operator and finite-centre caps on a base dimension `n0 ≥ 8000`.
Each lemma `fooP` states `X n ≤ cap` for `n0 ≤ n`, with the cap an explicit rational function
of `n0` and of rational witnesses. The witnesses carry rational hypotheses that `norm_num`
checks at an instance. The old lemmas at 12225 are instances. -/
namespace BstLean.Part277
open Real MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part153 BstLean.Part154
  BstLean.Part211 BstLean.Part215 BstLean.Part219
open BstLean.Part29 (stdGauss)

/-! ## Energy allowance -/

theorem energyBound_anti {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) :
    BstLean.Part263.energyBound n ≤ BstLean.Part263.energyBound n0 := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n0 := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hL : BstLean.Part263.layerBound n ≤ BstLean.Part263.layerBound n0 := by
    unfold BstLean.Part263.layerBound
    gcongr
  have hL0 : 0 ≤ BstLean.Part263.layerBound n := by
    unfold BstLean.Part263.layerBound; positivity
  unfold BstLean.Part263.energyBound
  gcongr

/-- The energy allowance on `n ≥ n0`, with the explicit cap `Part263.energyBound n0`. -/
theorem energy_allowance_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ BstLean.Part263.energyBound n0 :=
  (BstLean.Part263.energy_allowance_bound (by omega)).trans (energyBound_anti h8 hn)

theorem energyBound_8000_le : BstLean.Part263.energyBound 8000 ≤ (262607 / 10 ^ 8 : ℝ) := by
  unfold BstLean.Part263.energyBound BstLean.Part263.layerBound; norm_num
theorem energyBound_11883_le : BstLean.Part263.energyBound 11883 ≤ (176765 / 10 ^ 8 : ℝ) := by
  unfold BstLean.Part263.energyBound BstLean.Part263.layerBound; norm_num
theorem energyBound_12000_le : BstLean.Part263.energyBound 12000 ≤ (175041 / 10 ^ 8 : ℝ) := by
  unfold BstLean.Part263.energyBound BstLean.Part263.layerBound; norm_num
theorem energyBound_12225_le :
    BstLean.Part263.energyBound 12225 ≤ (1718175627 / 10 ^ 12 : ℝ) := by
  unfold BstLean.Part263.energyBound BstLean.Part263.layerBound; norm_num

/-- The old `Part263.energy_allowance_le`, as an instance (same constant). -/
theorem energy_allowance_12225 {n : ℕ} (hn : 12225 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ (1718175627 / 10 ^ 12 : ℝ) :=
  (energy_allowance_leP (by norm_num) hn).trans energyBound_12225_le

theorem energy_allowance_11883 {n : ℕ} (hn : 11883 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ (176765 / 10 ^ 8 : ℝ) :=
  (energy_allowance_leP (by norm_num) hn).trans energyBound_11883_le

theorem energy_allowance_12000 {n : ℕ} (hn : 12000 ≤ n) :
    BstLean.Part222.energyAllowance n ≤ (175041 / 10 ^ 8 : ℝ) :=
  (energy_allowance_leP (by norm_num) hn).trans energyBound_12000_le

/-! ## Operator allowance -/

theorem inverse_product_upperP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) :
    (∏ i ∈ Finset.range 160, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹) ≤
      (((n : ℝ) - 321)⁻¹) ^ 160 := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ ∏ _i ∈ Finset.range 160, ((n : ℝ) - 321)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hiR : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
        apply inv_nonneg.mpr
        linarith
      · intro i hi
        have hiR : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
        apply inv_anti₀ (by linarith : (0 : ℝ) < n - 321)
        linarith
    _ = _ := by simp

/-- **The operator allowance on `n ≥ n0`.** `J` bounds `jS m 160 .006` for every `m ≥ n0`.
The cap `K` satisfies `((n0/(n0-321)) J²)^160 · 20000 ≤ K^160`. -/
theorem operator_allowance_leP {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {J K : ℝ}
    (hJ : ∀ m : ℕ, n0 ≤ m → jS m 160 0.006 ≤ J) (hK0 : 0 ≤ K)
    (hK : (((n0 : ℝ) / ((n0 : ℝ) - 321)) * J ^ 2) ^ 160 * 20000 ≤ K ^ 160) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ K := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) hK0
  rw [BstLean.Part253.operator_squared_power]
  let I : ℝ := ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 160 ∂stdGauss (Fin n)
  have hI0 : 0 ≤ I := integral_nonneg
    (fun _ => pow_nonneg (inv_nonneg.mpr (normSq_nonneg _)) 160)
  have hI : τ ^ 320 * I ≤ (((n : ℝ) - 321)⁻¹) ^ 160 := by
    have h := (invMoment_le (by omega : 2 * 160 + 1 < n) c hτ).2
    exact h.trans (inverse_product_upperP h8 hn)
  have he : (operatorBudget c τ 0.006 / ENNReal.ofReal (1 / 20000)).toReal =
      (√(n : ℝ) * jS n 160 0.006) ^ 320 * I * 20000 := by
    unfold operatorBudget
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg
        (mul_nonneg (sqrt_nonneg _) (jS_nonneg _ _ _)) 320), ENNReal.toReal_ofReal hI0,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
    dsimp [I]
    ring
  have hj := hJ n hn
  have hj0 := jS_nonneg n 160 0.006
  have hp : (√(n : ℝ) * jS n 160 0.006) ^ 320 =
      ((n : ℝ) * jS n 160 0.006 ^ 2) ^ 160 := by
    rw [show 320 = 2 * 160 by rfl, pow_mul, mul_pow, sq_sqrt hn0]
  have hp1 : ((n : ℝ) * jS n 160 0.006 ^ 2) ^ 160 ≤
      ((n : ℝ) * J ^ 2) ^ 160 := by gcongr
  have hratio : (n : ℝ) / ((n : ℝ) - 321) ≤ (n0 : ℝ) / ((n0 : ℝ) - 321) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < n - 321) (by linarith : (0 : ℝ) < n0 - 321)]
    nlinarith
  have hratio0 : 0 ≤ (n : ℝ) / ((n : ℝ) - 321) :=
    div_nonneg hn0 (by linarith)
  rw [he, hp]
  calc
    _ = (((n : ℝ) * jS n 160 0.006 ^ 2) ^ 160 * (τ ^ 320 * I)) * 20000 := by ring
    _ ≤ (((n : ℝ) * J ^ 2) ^ 160 * (((n : ℝ) - 321)⁻¹) ^ 160) * 20000 := by
      have ht0 : 0 ≤ τ ^ 320 * I := mul_nonneg (pow_nonneg hτ.le _) hI0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hp1 hI ht0 (pow_nonneg (by positivity) 160)) (by norm_num)
    _ = ((n : ℝ) / ((n : ℝ) - 321) * J ^ 2) ^ 160 * 20000 := by
      rw [← mul_pow]
      congr 2
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (((n0 : ℝ) / ((n0 : ℝ) - 321)) * J ^ 2) ^ 160 * 20000 := by gcongr
    _ ≤ K ^ 160 := hK

/-- `jBound n0` with `√n0` replaced by a rational lower bound `s`. -/
noncomputable def jBoundRat (n0 : ℕ) (s : ℝ) : ℝ :=
  (1006 / 1000 + 141422 / 100000 * (1 / s) + 141422 / 100000 * (18 / (n0 : ℝ)) +
    15 / 10 ^ 7) ^ 2 +
  (1 + 141422 / 100000 * (18 / (n0 : ℝ))) * (141422 / 100000 * (1 + 18 / s)) * (1 / s)

theorem jBound_le_rat {n0 : ℕ} (h8 : 8000 ≤ n0) {s : ℝ} (hs0 : 0 < s)
    (hs : s ≤ √(n0 : ℝ)) : BstLean.Part273.jBound n0 ≤ jBoundRat n0 s := by
  have hN : (8000 : ℝ) ≤ n0 := by exact_mod_cast h8
  have hn0 : (0 : ℝ) < n0 := by linarith
  have hs1 : 1 / √(n0 : ℝ) ≤ 1 / s := one_div_le_one_div_of_le hs0 hs
  have hs18 : 18 / √(n0 : ℝ) ≤ 18 / s := div_le_div_of_nonneg_left (by norm_num) hs0 hs
  have hq0 : 0 ≤ 1 / √(n0 : ℝ) := by positivity
  unfold BstLean.Part273.jBound jBoundRat
  gcongr

theorem jS_le_jBoundRat {n0 n : ℕ} (h8 : 8000 ≤ n0) (hn : n0 ≤ n) {s : ℝ} (hs0 : 0 < s)
    (hs : s ≤ √(n0 : ℝ)) : jS n 160 0.006 ≤ jBoundRat n0 s := by
  have h := BstLean.Part273.jS_le_jBound h8 hn
  norm_num only at h ⊢
  exact h.trans (jBound_le_rat h8 hs0 hs)

/-- The old `Part264.operator_allowance_le`, as an instance of `operator_allowance_leP`. -/
theorem operator_allowance_12225 {n : ℕ} (hn : 12225 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ 1.22 :=
  operator_allowance_leP (n0 := 12225) (by norm_num) hn c hτ (J := 1.055)
    (fun m hm => (BstLean.Part264.jS_mono hm).trans BstLean.Part253.jS_upper)
    (by norm_num) (by norm_num)

end BstLean.Part277
