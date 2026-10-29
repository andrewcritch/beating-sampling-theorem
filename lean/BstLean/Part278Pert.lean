import BstLean.Part278Mix

/-!
# Part 278 (O3, location table): the perturbation of `f̃` by the odd rule

Paper: `theorem7-08-bias.tex`, Lemma `t7:p08:odd` (the location part).

* `binMean_relu_pert`: `|B_J ReLU(x′ + σ′Z) − B_J ReLU(x + σZ)| ≤ |x′ − x| + |σ′ − σ|`.
* `mom_err`: for odd `n ≥ 8001`, `|ā^{st}_i − ā_i| ≤ ε a_i` and `|ē^{st}_i − ē_i| ≤ 3ε a_i²`,
  `ε = 10⁻⁹⁰ n⁻¹⁰`, `a_i = |s||α_i| + κ_i`.
* `odd_fPass_err`: if `A₂` has operator bound `O` (`OpB`), then
  `|f̃^{st}(s) − f̃(s)| ≤ √(2O²ε²Q + 4ε(7 + ε)Q)/√n`, `Q = Σ_i a_i²`.

The energy table `ω̃` is not treated here.
-/

namespace BstLean.Part278

open Real MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53)
open BstLean.Part130 (relu normSq normSq_nonneg mA measurable_relu)
open BstLean.Part150 (binMean binMean_sub binMean_abs_le binMean_mono binMean_add binMean_const
  binMean_const_mul binMean_sq)
open BstLean.Part157 (Ret)
open BstLean.Part169 (A2 bR Jz OpB a1Bar e1Bar)
open BstLean.Part272 (vsig2G betaG fPassG a1St e1St alphaE kappaE a1Bar_reduce e1Bar_reduce
  integrable_coord_comp relu_bound)

variable {n : ℕ}

theorem relu_lip (x y : ℝ) : |relu x - relu y| ≤ |x - y| := by
  unfold relu; rw [max_comm 0 x, max_comm 0 y]; exact abs_max_sub_max_le_abs x y 0

theorem binMean_abs_z {J : ℕ} (hJ : 1 ≤ J) : binMean J (fun z => |z|) ≤ 1 := by
  have h : ∀ z : ℝ, |z| ≤ 1 / 2 + 1 / 2 * z ^ 2 := fun z => by
    nlinarith [sq_abs z, sq_nonneg (|z| - 1)]
  calc binMean J (fun z => |z|) ≤ binMean J (fun z => 1 / 2 + 1 / 2 * z ^ 2) := binMean_mono J h
    _ = 1 := by rw [binMean_add, binMean_const, binMean_const_mul, binMean_sq hJ]; norm_num

theorem binMean_relu_pert {J : ℕ} (hJ : 1 ≤ J) (x x' σ σ' : ℝ) :
    |binMean J (fun z => relu (x' + σ' * z)) - binMean J (fun z => relu (x + σ * z))| ≤
      |x' - x| + |σ' - σ| := by
  rw [← binMean_sub]
  refine (binMean_abs_le J _).trans ?_
  calc binMean J (fun z => |relu (x' + σ' * z) - relu (x + σ * z)|)
      ≤ binMean J (fun z => |x' - x| + |σ' - σ| * |z|) := binMean_mono J fun z => by
        refine (relu_lip _ _).trans ?_
        rw [show x' + σ' * z - (x + σ * z) = (x' - x) + (σ' - σ) * z by ring]
        exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_mul]))
    _ = |x' - x| + |σ' - σ| * binMean J (fun z => |z|) := by
        rw [binMean_add, binMean_const, binMean_const_mul]
    _ ≤ |x' - x| + |σ' - σ| := by
        nlinarith [binMean_abs_z hJ, abs_nonneg (σ' - σ)]

theorem sqrt_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : |√x - √y| ≤ √|x - y| := by
  apply Real.abs_le_sqrt
  have h1 : |√x - √y| ≤ √x + √y := by
    rw [abs_le]; constructor <;> linarith [sqrt_nonneg x, sqrt_nonneg y]
  have h2 : |x - y| = |√x - √y| * (√x + √y) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ √x + √y), ← abs_mul]
    congr 1
    rw [show (√x - √y) * (√x + √y) = √x ^ 2 - √y ^ 2 by ring, sq_sqrt hx, sq_sqrt hy]
  rw [h2, ← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- The variance term under a perturbation of the two moment vectors. -/
theorem vsig_diff {m : ℕ} (x x' y y' : Fin m → ℝ) :
    |max 0 (2 / (m : ℝ) * (∑ i, y' i - normSq x')) - max 0 (2 / (m : ℝ) * (∑ i, y i - normSq x))|
      ≤ 2 / (m : ℝ) * (∑ i, |y' i - y i| + ∑ i, |x' i - x i| * (2 * |x i| + |x' i - x i|)) := by
  have hm : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hm]
  refine mul_le_mul_of_nonneg_left ?_ hm
  have e : ∑ i, y' i - normSq x' - (∑ i, y i - normSq x) =
      ∑ i, (y' i - y i) - ∑ i, (x' i - x i) * (x' i - x i + 2 * x i) := by
    unfold normSq
    have h2 : ∑ i, (x' i - x i) * (x' i - x i + 2 * x i) = ∑ i, x' i ^ 2 - ∑ i, x i ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, Finset.sum_sub_distrib]
    ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |x' i - x i + 2 * x i| ≤ |x' i - x i| + |2 * x i| := abs_add_le _ _
    _ = 2 * |x i| + |x' i - x i| := by rw [abs_mul, abs_two]; ring

/-- **The location table under a perturbation of the moment vectors.** -/
theorem fPassG_pert (hJ : 1 ≤ Jz n) (a a' e e' : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ)
    {O : ℝ} (hO : OpB (A2 c) O) :
    |fPassG a' e' c s - fPassG a e c s| ≤
      √(2 * (O ^ 2 * normSq (a' c s - a c s)) +
        2 * (mA n : ℝ) * |vsig2G a' e' c s - vsig2G a e c s|) / √(n : ℝ) := by
  obtain ⟨d, hd⟩ : ∃ d : Fin (mA n) → ℝ, ∀ j, d j = betaG a' e' c s j - betaG a e c s j :=
    ⟨_, fun j => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin (mA n) → ℝ, u = (A2 c).mulVec (a' c s - a c s) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = |√(vsig2G a' e' c s) - √(vsig2G a e c s)| := ⟨_, rfl⟩
  have hv0 : ∀ (a e : Ret n → ℝ → Fin (mA n) → ℝ), 0 ≤ vsig2G a e c s :=
    fun a e => le_max_left _ _
  have htv : t ≤ √|vsig2G a' e' c s - vsig2G a e c s| := by
    rw [ht]; exact sqrt_sub_le (hv0 _ _) (hv0 _ _)
  have ht0 : 0 ≤ t := by rw [ht]; exact abs_nonneg _
  have ht2 : t ^ 2 ≤ |vsig2G a' e' c s - vsig2G a e c s| := by
    calc t ^ 2 ≤ (√|vsig2G a' e' c s - vsig2G a e c s|) ^ 2 := pow_le_pow_left₀ ht0 htv 2
      _ = _ := sq_sqrt (abs_nonneg _)
  have hdj : ∀ j, |d j| ≤ |u j| + t := by
    intro j
    have h := binMean_relu_pert hJ ((A2 c).mulVec (a c s) j) ((A2 c).mulVec (a' c s) j)
      (√(vsig2G a e c s)) (√(vsig2G a' e' c s))
    have hu' : u j = (A2 c).mulVec (a' c s) j - (A2 c).mulVec (a c s) j := by
      rw [hu, Matrix.mulVec_sub]; rfl
    rw [hd j, hu', ht]
    exact h
  have hd2 : ∑ j, d j ^ 2 ≤ 2 * (O ^ 2 * normSq (a' c s - a c s)) +
      2 * (mA n : ℝ) * |vsig2G a' e' c s - vsig2G a e c s| := by
    have h1 : ∀ j, d j ^ 2 ≤ 2 * u j ^ 2 + 2 * t ^ 2 := by
      intro j
      have h := hdj j
      have h0 : 0 ≤ |d j| := abs_nonneg _
      have hsq : d j ^ 2 ≤ (|u j| + t) ^ 2 := by
        rw [← sq_abs (d j)]; exact pow_le_pow_left₀ h0 h 2
      nlinarith [sq_abs (u j), sq_nonneg (|u j| - t)]
    calc ∑ j, d j ^ 2 ≤ ∑ j, (2 * u j ^ 2 + 2 * t ^ 2) := Finset.sum_le_sum fun j _ => h1 j
      _ = 2 * normSq u + 2 * (mA n : ℝ) * t ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          unfold normSq
          rw [Finset.mul_sum]
          ring
      _ ≤ _ := by
          have h3 := hO (a' c s - a c s)
          rw [← hu] at h3
          have hm0 : (0:ℝ) ≤ mA n := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left ht2 hm0]
  have hB0 : 0 ≤ normSq (bR c) := normSq_nonneg _
  have hdiff : fPassG a' e' c s - fPassG a e c s =
      (∑ j, d j * bR c j) / (√(n : ℝ) * √(normSq (bR c))) := by
    unfold fPassG
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd j]; ring
  rw [hdiff]
  have hn0 : (0:ℝ) ≤ √(n : ℝ) := sqrt_nonneg _
  have hCS : |∑ j, d j * bR c j| ≤ √(∑ j, d j ^ 2) * √(normSq (bR c)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |d j|) (fun j => |bR c j|)
    simp only [sq_abs] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun j _ => abs_mul _ _
  rcases hB0.eq_or_lt with h0 | hpos
  · rw [← h0, sqrt_zero, mul_zero, div_zero, abs_zero]
    positivity
  · have hb : 0 < √(normSq (bR c)) := sqrt_pos.mpr hpos
    rcases (sqrt_nonneg (n : ℝ)).eq_or_lt with hn | hn
    · rw [← hn, zero_mul, div_zero, abs_zero]; positivity
    · rw [abs_div, abs_of_pos (mul_pos hn hb), div_le_div_iff₀ (mul_pos hn hb) hn]
      calc |∑ j, d j * bR c j| * √(n : ℝ)
          ≤ √(∑ j, d j ^ 2) * √(normSq (bR c)) * √(n : ℝ) :=
            mul_le_mul_of_nonneg_right hCS hn0
        _ ≤ √(2 * (O ^ 2 * normSq (a' c s - a c s)) +
              2 * (mA n : ℝ) * |vsig2G a' e' c s - vsig2G a e c s|) * √(normSq (bR c)) *
              √(n : ℝ) := by
            gcongr
        _ = _ := by ring

/-! ## The moment errors of the stated rule -/

/-- `ε = 10⁻⁹⁰ n⁻¹⁰`. -/
noncomputable def epsO (n : ℕ) : ℝ := 1 / 10 ^ 90 * (n : ℝ) ^ (-10 : ℝ)

/-- The scale `a_i = |s||α_i| + κ_i` of row `i` at the latitude `s`. -/
noncomputable def aw (c : Ret n) (s : ℝ) (i : Fin (mA n)) : ℝ := |s| * |alphaE c i| + kappaE c i

theorem mom_err (hn : 8001 ≤ n) (ho : Odd n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    |a1St c s i - a1Bar c s i| ≤ epsO n * aw c s i ∧
    |e1St c s i - e1Bar c s i| ≤ 3 / 10 ^ 90 * (n : ℝ) ^ (-10 : ℝ) * aw c s i ^ 2 := by
  have hne : ¬ Even n := Nat.not_even_iff_odd.mpr ho
  have hκ : 0 ≤ kappaE c i := sqrt_nonneg _
  have hk : 0 ≤ √(1 - s ^ 2) * kappaE c i := mul_nonneg (sqrt_nonneg _) hκ
  have hm : |s * alphaE c i| ≤ aw c s i := by
    unfold aw; rw [abs_mul]; linarith
  have hs1 : √(1 - s ^ 2) ≤ 1 :=
    (sqrt_le_sqrt (by nlinarith [sq_nonneg s] : 1 - s ^ 2 ≤ 1)).trans_eq sqrt_one
  have hka : √(1 - s ^ 2) * kappaE c i ≤ aw c s i := by
    unfold aw
    have := mul_le_of_le_one_left hκ hs1
    have := mul_nonneg (abs_nonneg s) (abs_nonneg (alphaE c i))
    linarith
  obtain ⟨hA, hE⟩ := odd_rule_err hn ho (s * alphaE c i) hk hm hka
  have hsph := sph_oddRef (by omega : 9 ≤ n) ho (s * alphaE c i) hk
  constructor
  · rw [a1St, if_neg hne, a1Bar_reduce (by omega), hsph.1]
    exact hA
  · rw [e1St, if_neg hne, e1Bar_reduce (by omega), hsph.2]
    exact hE

theorem a1Bar_le (hn : 2 ≤ n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    |a1Bar c s i| ≤ 2 * aw c s i := by
  have hκ : 0 ≤ kappaE c i := sqrt_nonneg _
  have hk : 0 ≤ √(1 - s ^ 2) * kappaE c i := mul_nonneg (sqrt_nonneg _) hκ
  have hs1 : √(1 - s ^ 2) ≤ 1 :=
    (sqrt_le_sqrt (by nlinarith [sq_nonneg s] : 1 - s ^ 2 ≤ 1)).trans_eq sqrt_one
  have hka : √(1 - s ^ 2) * kappaE c i ≤ kappaE c i := mul_le_of_le_one_left hκ hs1
  have hma : |s * alphaE c i| ≤ |s| * |alphaE c i| := le_of_eq (abs_mul _ _)
  rw [a1Bar_reduce hn]
  have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Set.Icc (-1:ℝ) 1 :=
    fun v => BstLean.Part272.coord_mem v _
  have hI : Integrable (fun v => relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
      unitF53 v ⟨0, by omega⟩)) (stdGauss (Fin (n-1))) :=
    integrable_coord_comp _ (g := fun z => relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i * z))
      (measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id)))
      (relu_bound _ _ hk)
  rw [abs_of_nonneg (integral_nonneg fun v => le_max_left _ _)]
  have hle : ∀ v : Fin (n-1) → ℝ, relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
      unitF53 v ⟨0, by omega⟩) ≤ 2 * aw c s i := by
    intro v
    unfold relu aw
    have h0 := mul_nonneg (abs_nonneg s) (abs_nonneg (alphaE c i))
    apply max_le (by linarith)
    have : √(1 - s ^ 2) * kappaE c i * unitF53 v ⟨0, by omega⟩ ≤ √(1 - s ^ 2) * kappaE c i := by
      nlinarith [(hTm v).2]
    linarith [le_abs_self (s * alphaE c i)]
  calc ∫ v, relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i * unitF53 v ⟨0, by omega⟩)
        ∂stdGauss (Fin (n-1))
      ≤ ∫ _v : Fin (n-1) → ℝ, 2 * aw c s i ∂stdGauss (Fin (n-1)) :=
        integral_mono hI (integrable_const _) hle
    _ = 2 * aw c s i := by simp

/-- **O3 (location table).** The stated `f̃(s)` against the exact-moment `f̃(s)` for odd `n`. -/
theorem odd_fPass_err (hn : 8001 ≤ n) (ho : Odd n) (hJ : 1 ≤ Jz n) (c : Ret n) (s : ℝ) {O : ℝ}
    (hO : OpB (A2 c) O) :
    |fPassG a1St e1St c s - fPassG a1Bar e1Bar c s| ≤
      √(2 * (O ^ 2 * (epsO n ^ 2 * ∑ i, aw c s i ^ 2)) +
        4 * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2)) / √(n : ℝ) := by
  have hε0 : 0 ≤ epsO n := by unfold epsO; positivity
  have hε3 : 3 / 10 ^ 90 * (n : ℝ) ^ (-10 : ℝ) = 3 * epsO n := by unfold epsO; ring
  have hmom := fun i => mom_err hn ho c s i
  have haw0 : ∀ i, 0 ≤ aw c s i := fun i => by
    unfold aw; exact add_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sqrt_nonneg _)
  have hm0 : (0 : ℝ) < mA n := by
    have : 0 < mA n := by unfold mA; exact pow_pos (by omega) 2
    exact_mod_cast this
  refine (fPassG_pert hJ a1Bar a1St e1Bar e1St c s hO).trans ?_
  apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
  apply sqrt_le_sqrt
  have h1 : normSq (a1St c s - a1Bar c s) ≤ epsO n ^ 2 * ∑ i, aw c s i ^ 2 := by
    unfold normSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := (hmom i).1
    rw [Pi.sub_apply, ← sq_abs (a1St c s i - a1Bar c s i), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : |vsig2G a1St e1St c s - vsig2G a1Bar e1Bar c s| ≤
      2 / (mA n : ℝ) * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2) := by
    refine (vsig_diff (a1Bar c s) (a1St c s) (e1Bar c s) (e1St c s)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hs1 : ∑ i, |e1St c s i - e1Bar c s i| ≤ ∑ i, 3 * epsO n * aw c s i ^ 2 :=
      Finset.sum_le_sum fun i _ => by rw [← hε3]; exact (hmom i).2
    have hs2 : ∑ i, |a1St c s i - a1Bar c s i| * (2 * |a1Bar c s i| + |a1St c s i - a1Bar c s i|)
        ≤ ∑ i, epsO n * (4 + epsO n) * aw c s i ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hA := (hmom i).1
      have hB := a1Bar_le (by omega) c s i
      have hd0 := abs_nonneg (a1St c s i - a1Bar c s i)
      calc |a1St c s i - a1Bar c s i| * (2 * |a1Bar c s i| + |a1St c s i - a1Bar c s i|)
          ≤ (epsO n * aw c s i) * (2 * (2 * aw c s i) + epsO n * aw c s i) :=
            mul_le_mul hA (by linarith) (by positivity)
              (mul_nonneg hε0 (haw0 i))
        _ = epsO n * (4 + epsO n) * aw c s i ^ 2 := by ring
    rw [← Finset.mul_sum] at hs1 hs2
    nlinarith
  have hO2 : 0 ≤ O ^ 2 := sq_nonneg O
  have hmm : (mA n : ℝ) * (mA n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hm0.ne'
  have e2 : 2 * (mA n : ℝ) * (2 / (mA n : ℝ) * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2)) =
      4 * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2) := by
    calc _ = 4 * (epsO n * (7 + epsO n) * ∑ i, aw c s i ^ 2) * ((mA n : ℝ) * (mA n : ℝ)⁻¹) := by
          ring
      _ = _ := by rw [hmm, mul_one]
  have h3 := mul_le_mul_of_nonneg_left h1 hO2
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * (mA n : ℝ))
  rw [e2] at h4
  linarith

end BstLean.Part278
