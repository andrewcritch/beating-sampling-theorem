import BstLean.Part130Layer
import BstLean.Part182Bern
import BstLean.Part152Op
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Part 184 (file `DS`): groundwork for an ε-net lower bound on the smallest singular value

No proof is left open; no `native_decide` or `axiom` is used.

Purpose: the Davidson–Szarek substitute for TI-lite's E block (a later part). General lemmas:

* `chernoff_factor`, `chi_lower_std`: `Pr(|ξ|² ≤ (1 − δ)K) ≤ e^{−Kδ²/4}` for a standard Gaussian
  vector (`0 ≤ δ ≤ 1`; Chernoff at `λ = δ/2`, `e^{δ − δ²/2} ≤ 1 + δ`).
* **(D1) `chi_lower_gm`**: for `G ~ gaussMat K d v`, `x ≠ 0`:
  `Pr(|Gx|² ≤ (1 − δ)vK|x|²) ≤ e^{−Kδ²/4}`.
* **(D2) `gridNet`, `card_gridNet`, `gridNet_cover`**: the grid `(ε/√d){−N, …, N}^d`,
  `N = ⌈√d/ε⌉`, has at most `(2N + 1)^d` points and is an `ε`-net of the unit ball.
* **(D3) `smin_net`**: `Pr(∃ x, |x| = 1, |Gx| < √((1 − δ)vK)(1 − ε) − sε) ≤
  (2⌈√d/ε⌉ + 1)^d e^{−Kδ²/4} + Pr(‖G‖_op > s)`.
* **(D4) `gram_two_sided`**: `lo|z|² ≤ |Gz|² ≤ hi|z|²` for all `z` implies
  `|⟨Gp, Gq⟩ − ((hi + lo)/2)⟨p, q⟩| ≤ ((hi − lo)/2)|p||q|`.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130

lemma exp_sub_half_sq_le {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : exp (δ - δ ^ 2 / 2) ≤ 1 + δ := by
  set y := δ - δ ^ 2 / 2 with hy
  have hy0 : 0 ≤ y := by nlinarith
  have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; nlinarith
  have hb := Real.exp_bound hy1 (n := 4) (by norm_num)
  have hs : ∑ i ∈ Finset.range 4, y ^ i / (Nat.factorial i) = 1 + y + y ^ 2 / 2 + y ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs, abs_of_nonneg hy0] at hb
  have hb' := (abs_le.mp hb).2
  norm_num [Nat.factorial] at hb'
  have key : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 * (5 / 96) ≤ 1 + δ := by
    rw [hy]
    have h3 : 0 ≤ δ ^ 3 := by positivity
    nlinarith [mul_nonneg h3 h0, mul_nonneg (mul_nonneg h3 h0) h0,
      mul_nonneg (mul_nonneg h3 h0) (sub_nonneg.mpr h1),
      mul_nonneg h3 (sub_nonneg.mpr h1), mul_nonneg (mul_nonneg (mul_nonneg h3 h0) h0) h0,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h3 h0) h0) h0) h0]
  linarith

/-- The one-coordinate Chernoff factor: `e^{δ(1−δ)/2}/√(1+δ) ≤ e^{−δ²/4}`. -/
lemma chernoff_factor {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    exp (δ / 2 * (1 - δ)) * (1 / √(1 + δ)) ≤ exp (-(δ ^ 2 / 4)) := by
  have hs : 0 < √(1 + δ) := Real.sqrt_pos.mpr (by linarith)
  have h2 : exp (δ / 2 - δ ^ 2 / 4) ≤ √(1 + δ) := by
    have e : exp (δ - δ ^ 2 / 2) = exp (δ / 2 - δ ^ 2 / 4) * exp (δ / 2 - δ ^ 2 / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show exp (δ / 2 - δ ^ 2 / 4) = √(exp (δ - δ ^ 2 / 2)) by
      rw [e, Real.sqrt_mul_self (by positivity)]]
    exact Real.sqrt_le_sqrt (exp_sub_half_sq_le h0 h1)
  rw [mul_one_div, div_le_iff₀ hs]
  calc exp (δ / 2 * (1 - δ)) = exp (-(δ ^ 2 / 4)) * exp (δ / 2 - δ ^ 2 / 4) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ exp (-(δ ^ 2 / 4)) * √(1 + δ) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The chi-square lower tail** for a standard Gaussian vector:
`Pr(|ξ|² ≤ (1 − δ)K) ≤ e^{−Kδ²/4}`, `0 ≤ δ ≤ 1`. -/
theorem chi_lower_std (K : ℕ) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (stdGauss (Fin K)).real {ξ | normSq ξ ≤ (1 - δ) * K} ≤ exp (-(K * δ ^ 2 / 4)) := by
  have hP : IsProbabilityMeasure (stdGauss (Fin K)) := inferInstance
  set t : ℝ := -(δ / 2) with htd
  have ht : t ≤ 0 := by rw [htd]; linarith
  have hmX : Measurable (fun ξ : Fin K → ℝ => normSq ξ) := by
    unfold normSq; fun_prop
  have hint : Integrable (fun ξ : Fin K → ℝ => exp (t * normSq ξ)) (stdGauss (Fin K)) := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : 0 ≤ normSq ξ := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have h := measure_le_le_exp_mul_mgf (μ := stdGauss (Fin K)) (X := fun ξ => normSq ξ)
    ((1 - δ) * K) ht hint
  have hmgf : mgf (fun ξ : Fin K → ℝ => normSq ξ) (stdGauss (Fin K)) t = (1 / √(1 + δ)) ^ K := by
    unfold mgf
    have e : (fun ξ : Fin K → ℝ => exp (t * normSq ξ)) = fun ξ => ∏ i, exp (t * ξ i ^ 2) := by
      funext ξ; unfold normSq; rw [Finset.mul_sum, Real.exp_sum]
    rw [e]
    unfold stdGauss
    rw [integral_fintype_prod_eq_prod (fun _ x => exp (t * x ^ 2))]
    have hg := (BstLean.Part182.bn_gauss_exp (a := t) (by rw [htd]; linarith)).2
    rw [hg, show 1 - 2 * t = 1 + δ by rw [htd]; ring]
    simp
  rw [hmgf] at h
  refine h.trans ?_
  have hc := chernoff_factor h0 h1
  calc exp (-t * ((1 - δ) * K)) * (1 / √(1 + δ)) ^ K
      = (exp (δ / 2 * (1 - δ)) * (1 / √(1 + δ))) ^ K := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; rw [htd]; ring
    _ ≤ (exp (-(δ ^ 2 / 4))) ^ K := pow_le_pow_left₀ (by positivity) hc K
    _ = exp (-(K * δ ^ 2 / 4)) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma measurable_normSq {k : ℕ} : Measurable (fun z : Fin k → ℝ => normSq z) := by
  unfold normSq; fun_prop

lemma normSq_smul' {k : ℕ} (c : ℝ) (z : Fin k → ℝ) : normSq (c • z) = c ^ 2 * normSq z := by
  unfold normSq; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- **(D1) The chi-square lower tail for a Gaussian matrix**: for `x ≠ 0`, `v > 0`,
`Pr(|Gx|² ≤ (1 − δ)·v·K·|x|²) ≤ e^{−Kδ²/4}`. -/
theorem chi_lower_gm {K d : ℕ} {v : ℝ} (hv : 0 < v) {x : Fin d → ℝ} (hx : normSq x ≠ 0)
    {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    (gaussMat K d v).real {G | normSq (G *ᵥ x) ≤ (1 - δ) * v * K * normSq x} ≤
      exp (-(K * δ ^ 2 / 4)) := by
  have hx0 : 0 < normSq x := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hx)
  set S : Set (Fin K → ℝ) := {z | normSq z ≤ (1 - δ) * v * K * normSq x} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_normSq measurable_const
  have hmv : Measurable (fun G : Matrix (Fin K) (Fin d) ℝ => G.mulVec x) := by fun_prop
  have e1 : {G : Matrix (Fin K) (Fin d) ℝ | normSq (G *ᵥ x) ≤ (1 - δ) * v * K * normSq x} =
      (fun G : Matrix (Fin K) (Fin d) ℝ => G.mulVec x) ⁻¹' S := rfl
  rw [e1, ← map_measureReal_apply hmv hSm, gaussMat_mulVec,
    map_measureReal_apply (by fun_prop) hSm]
  refine le_of_eq_of_le ?_ (chi_lower_std K h0 h1)
  congr 1
  ext ξ
  simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [normSq_smul', mul_pow, Real.sq_sqrt hv.le, Real.sq_sqrt hx0.le]
  constructor
  · intro h
    have : v * normSq x * normSq ξ ≤ v * normSq x * ((1 - δ) * K) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · intro h
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ v * normSq x)
    nlinarith

/-! ## (D2) A grid net of the unit ball -/

/-- The number of grid steps per half-axis: `⌈√d/ε⌉`. -/
noncomputable def gridN (d : ℕ) (ε : ℝ) : ℕ := ⌈√(d : ℝ) / ε⌉₊

/-- The grid `(ε/√d)·{−N, …, N}^d`, `N = ⌈√d/ε⌉`. -/
noncomputable def gridNet (d : ℕ) (ε : ℝ) : Finset (Fin d → ℝ) :=
  Finset.univ.image (fun k : Fin d → Fin (2 * gridN d ε + 1) =>
    fun i => (((k i : ℕ) : ℝ) - gridN d ε) * (ε / √(d : ℝ)))

lemma card_gridNet (d : ℕ) (ε : ℝ) : (gridNet d ε).card ≤ (2 * gridN d ε + 1) ^ d := by
  unfold gridNet
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ]

/-- **(D2) The grid net covers the unit ball at distance `ε`.** -/
theorem gridNet_cover {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {x : Fin d → ℝ}
    (hx : normSq x ≤ 1) : ∃ y ∈ gridNet d ε, normSq (x - y) ≤ ε ^ 2 := by
  set N := gridN d ε with hNd
  have hd0 : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  set h := ε / √(d : ℝ) with hhd
  have hh : 0 < h := div_pos hε hd0
  have hN : √(d : ℝ) / ε ≤ N := Nat.le_ceil _
  have hxi : ∀ i, |x i| ≤ 1 := fun i => by
    have : x i ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)) hx
    exact abs_le_one_iff_mul_self_le_one.mpr (by nlinarith)
  have hz : ∀ i, |x i / h| ≤ N := fun i => by
    rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
    calc |x i| ≤ 1 := hxi i
      _ = √(d : ℝ) / ε * h := by rw [hhd]; field_simp
      _ ≤ N * h := mul_le_mul_of_nonneg_right hN hh.le
  set f : Fin d → ℤ := fun i => ⌊x i / h⌋ with hf
  have hf1 : ∀ i, -(N : ℤ) ≤ f i := fun i => by
    rw [hf, Int.le_floor]; push_cast; linarith [(abs_le.mp (hz i)).1]
  have hf2 : ∀ i, f i ≤ N := fun i => by
    have : (f i : ℝ) ≤ N := (Int.floor_le _).trans (abs_le.mp (hz i)).2
    exact_mod_cast this
  let k : Fin d → Fin (2 * N + 1) := fun i => ⟨(f i + N).toNat, by
    have h3 := hf2 i
    have h4 := hf1 i
    omega⟩
  refine ⟨fun i => (((k i : ℕ) : ℝ) - N) * h, ?_, ?_⟩
  · unfold gridNet
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  · have hk : ∀ i, (((k i : ℕ) : ℝ) - N) * h = (f i : ℝ) * h := fun i => by
      have h4 := hf1 i
      have e : ((k i : ℕ) : ℤ) = f i + N := by simp [k]; omega
      have e' : ((k i : ℕ) : ℝ) = (f i : ℝ) + N := by exact_mod_cast e
      rw [e']; ring
    unfold normSq
    calc ∑ i, (x - fun i => (((k i : ℕ) : ℝ) - N) * h) i ^ 2 ≤ ∑ _i : Fin d, h ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [Pi.sub_apply]
          rw [hk i]
          have a1 : (f i : ℝ) ≤ x i / h := Int.floor_le _
          have a2 : x i / h < f i + 1 := Int.lt_floor_add_one _
          have b1 : (f i : ℝ) * h ≤ x i := by rwa [le_div_iff₀ hh] at a1
          have b2 : x i < (f i + 1) * h := by rwa [div_lt_iff₀ hh] at a2
          have c0 : 0 ≤ x i - f i * h := by linarith
          have c1 : x i - f i * h ≤ h := by nlinarith
          nlinarith
      _ = ε ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hhd, div_pow,
            Real.sq_sqrt (by positivity)]
          field_simp

/-! ## (D3) The smallest singular value on the unit sphere -/

lemma sqrt_normSq_add_le {k : ℕ} (a b : Fin k → ℝ) :
    √(normSq (a + b)) ≤ √(normSq a) + √(normSq b) := by
  have hA : 0 ≤ normSq a := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ normSq b := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, a i * b i ≤ √(normSq a) * √(normSq b) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
    simpa [normSq] using this
  rw [Real.sqrt_le_left (by positivity)]
  have e : normSq (a + b) = normSq a + 2 * ∑ i, a i * b i + normSq b := by
    unfold normSq
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  rw [e]
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- **(D3) The ε-net lower bound on the smallest singular value**: with the grid net of (D2),
for `0 ≤ δ ≤ 1`, `0 < ε < 1` and any level `s`,
`Pr(∃ x, |x| = 1, |Gx| < √((1 − δ)vK)·(1 − ε) − sε) ≤ (2⌈√d/ε⌉ + 1)^d·e^{−Kδ²/4} + Pr(‖G‖ > s)`. -/
theorem smin_net {K d : ℕ} {v : ℝ} (hv : 0 < v) (hd : 1 ≤ d) {δ ε s : ℝ} (h0 : 0 ≤ δ)
    (h1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (gaussMat K d v).real {G | ∃ x : Fin d → ℝ, normSq x = 1 ∧
        √(normSq (G *ᵥ x)) < √((1 - δ) * v * K) * (1 - ε) - s * ε} ≤
      (2 * gridN d ε + 1) ^ d * exp (-(K * δ ^ 2 / 4)) +
        (gaussMat K d v).real {G | s < BstLean.Part152.opN G} := by
  have hP : IsProbabilityMeasure (gaussMat K d v) := by unfold gaussMat; infer_instance
  set net := (gridNet d ε).filter (fun y => normSq y ≠ 0) with hnet
  set c := (1 - δ) * v * K with hcd
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    rw [hcd]; have : 0 ≤ 1 - δ := by linarith
    positivity
  have hsub : {G : Matrix (Fin K) (Fin d) ℝ | ∃ x : Fin d → ℝ, normSq x = 1 ∧
        √(normSq (G *ᵥ x)) < √c * (1 - ε) - s * ε} ⊆
      (⋃ y ∈ net, {G : Matrix (Fin K) (Fin d) ℝ | normSq (G *ᵥ y) ≤ c * normSq y}) ∪
        {G | s < BstLean.Part152.opN G} := by
    intro G ⟨x, hx, hlt⟩
    by_contra hno
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists,
      not_lt] at hno
    obtain ⟨hy, hop⟩ := hno
    obtain ⟨y, hyn, hxy⟩ := gridNet_cover hd hε0 (le_of_eq hx)
    have hxy' : √(normSq (x - y)) ≤ ε := by
      rw [Real.sqrt_le_left hε0.le]; exact hxy
    have hy1 : 1 - ε ≤ √(normSq y) := by
      have := sqrt_normSq_add_le y (x - y)
      rw [add_sub_cancel, hx, Real.sqrt_one] at this
      linarith
    have hy0 : normSq y ≠ 0 := by
      intro h0'; rw [h0', Real.sqrt_zero] at hy1; linarith
    have hyc : c * normSq y < normSq (G *ᵥ y) := not_le.mp (hy y (by
      rw [hnet, Finset.mem_filter]; exact ⟨hyn, hy0⟩))
    have hGy : √c * √(normSq y) ≤ √(normSq (G *ᵥ y)) := by
      rw [← Real.sqrt_mul hc0]; exact Real.sqrt_le_sqrt hyc.le
    have hGd : √(normSq (G *ᵥ (x - y))) ≤ s * ε := by
      have h2 := BstLean.Part152.mulVec_le_opN G (x - y)
      have h3 : 0 ≤ BstLean.Part152.opN G := BstLean.Part152.opN_nonneg G
      calc √(normSq (G *ᵥ (x - y))) ≤ BstLean.Part152.opN G * √(normSq (x - y)) := h2
        _ ≤ s * ε := mul_le_mul hop hxy' (Real.sqrt_nonneg _) (h3.trans hop)
    have htri := sqrt_normSq_add_le (G *ᵥ x) (G *ᵥ (y - x))
    rw [← Matrix.mulVec_add, add_sub_cancel] at htri
    have hneg : normSq (G *ᵥ (y - x)) = normSq (G *ᵥ (x - y)) := by
      rw [show y - x = -(x - y) by abel, Matrix.mulVec_neg]
      unfold normSq; simp
    rw [hneg] at htri
    have hc1 : √c * (1 - ε) ≤ √c * √(normSq y) := mul_le_mul_of_nonneg_left hy1 (Real.sqrt_nonneg _)
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  gcongr
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ y ∈ net, (gaussMat K d v).real {G | normSq (G *ᵥ y) ≤ c * normSq y}
      ≤ ∑ _y ∈ net, exp (-(K * δ ^ 2 / 4)) := Finset.sum_le_sum fun y hy => by
        rw [hnet, Finset.mem_filter] at hy
        exact chi_lower_gm hv hy.2 h0 h1
    _ = net.card * exp (-(K * δ ^ 2 / 4)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * gridN d ε + 1) ^ d * exp (-(K * δ ^ 2 / 4)) := by
        gcongr
        have := (Finset.card_filter_le (gridNet d ε) (fun y => normSq y ≠ 0)).trans
          (card_gridNet d ε)
        exact_mod_cast this

/-! ## (D4) The two-sided Gram bound -/

lemma normSq_eq_dot {k : ℕ} (z : Fin k → ℝ) : normSq z = z ⬝ᵥ z := by
  unfold normSq dotProduct; exact Finset.sum_congr rfl fun i _ => by ring

/-- **(D4) The two-sided Gram bound**: if `lo|z|² ≤ |Gz|² ≤ hi|z|²` for every `z`, then
`|⟨Gp, Gq⟩ − ((hi + lo)/2)⟨p, q⟩| ≤ ((hi − lo)/2)|p||q|`. -/
theorem gram_two_sided {K d : ℕ} (G : Matrix (Fin K) (Fin d) ℝ) {lo hi : ℝ}
    (hlo : ∀ z, lo * normSq z ≤ normSq (G *ᵥ z)) (hhi : ∀ z, normSq (G *ᵥ z) ≤ hi * normSq z)
    (p q : Fin d → ℝ) :
    |(G *ᵥ p) ⬝ᵥ (G *ᵥ q) - (hi + lo) / 2 * (p ⬝ᵥ q)| ≤
      (hi - lo) / 2 * √(normSq p) * √(normSq q) := by
  -- step 1: the unscaled bound
  have step1 : ∀ p q : Fin d → ℝ, |(G *ᵥ p) ⬝ᵥ (G *ᵥ q) - (hi + lo) / 2 * (p ⬝ᵥ q)| ≤
      (hi - lo) / 4 * (normSq p + normSq q) := by
    intro p q
    have a1 := hlo (p + q); have a2 := hhi (p + q)
    have a3 := hlo (p - q); have a4 := hhi (p - q)
    simp only [normSq_eq_dot, Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
      dotProduct_add, sub_dotProduct, dotProduct_sub] at a1 a2 a3 a4 ⊢
    rw [dotProduct_comm (G *ᵥ q) (G *ᵥ p), dotProduct_comm q p] at a1 a2 a3 a4
    rw [abs_le]; constructor <;> nlinarith
  by_cases hp : normSq p = 0
  · have : p = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (p j))).mp hp i
        (Finset.mem_univ i)
      simpa using this
    subst this; simp [normSq]
  by_cases hq : normSq q = 0
  · have : q = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (q j))).mp hq i
        (Finset.mem_univ i)
      simpa using this
    subst this; simp [normSq]
  have hp0 : 0 < normSq p := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hp)
  have hq0 : 0 < normSq q := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hq)
  set P := √(normSq p) with hPd
  set Q := √(normSq q) with hQd
  have hP : 0 < P := Real.sqrt_pos.mpr hp0
  have hQ : 0 < Q := Real.sqrt_pos.mpr hq0
  set l := √(Q / P) with hld
  have hl : 0 < l := Real.sqrt_pos.mpr (div_pos hQ hP)
  have hl2 : l ^ 2 = Q / P := Real.sq_sqrt (div_pos hQ hP).le
  have h := step1 (l • p) (l⁻¹ • q)
  have e1 : (G *ᵥ (l • p)) ⬝ᵥ (G *ᵥ (l⁻¹ • q)) = (G *ᵥ p) ⬝ᵥ (G *ᵥ q) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]
  have e2 : (l • p) ⬝ᵥ (l⁻¹ • q) = p ⬝ᵥ q := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hl.ne', one_mul]
  have e3 : normSq (l • p) + normSq (l⁻¹ • q) = 2 * (P * Q) := by
    rw [normSq_smul', normSq_smul', inv_pow, hl2, ← Real.sq_sqrt hp0.le, ← Real.sq_sqrt hq0.le,
      ← hPd, ← hQd]
    field_simp
    ring
  rw [e1, e2, e3] at h
  calc _ ≤ (hi - lo) / 4 * (2 * (P * Q)) := h
    _ = (hi - lo) / 2 * P * Q := by ring

end BstLean.Part184

#print axioms BstLean.Part184.chi_lower_gm
#print axioms BstLean.Part184.gridNet_cover
#print axioms BstLean.Part184.smin_net
#print axioms BstLean.Part184.gram_two_sided
