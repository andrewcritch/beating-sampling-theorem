import BstLean.Part84Defs

/-!
# Part 84, the Gaussian model given the constant column (`gaussModel`)

Assembly of `GaussModel` from the interfaces of `Part84Defs`: representation, scale comparison,
decorrelation, Fubini, sphere moments, the scale defect, polynomial representation in `W`, and the
fourth-moment constant.
-/

namespace BstLean.Part84

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (frob IsSymmT Tens varU)
open BstLean.Part53 (heatA tinner p4)
open BstLean.Part81 (JJ WIdx pf kap eD)

/-! ## General facts -/

lemma sq_shift_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) (c : ℝ) :
    Integrable (fun x => (f x - c) ^ 2) μ ∧
    ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂μ - 2 * c * ∫ x, f x ∂μ + c ^ 2 := by
  have e : (fun x => (f x - c) ^ 2) = fun x => f x ^ 2 - 2 * c * f x + c ^ 2 := by
    funext x; ring
  rw [e]
  refine ⟨(hf2.sub (hf.const_mul _)).add (integrable_const _), ?_⟩
  have h1 : ∫ x, (f x ^ 2 - 2 * c * f x + c ^ 2) ∂μ =
      ∫ x, (f x ^ 2 - 2 * c * f x) ∂μ + ∫ _x, c ^ 2 ∂μ :=
    integral_add (hf2.sub (hf.const_mul _)) (integrable_const _)
  have h2 : ∫ x, (f x ^ 2 - 2 * c * f x) ∂μ = ∫ x, f x ^ 2 ∂μ - ∫ x, 2 * c * f x ∂μ :=
    integral_sub hf2 (hf.const_mul _)
  rw [h1, h2, integral_const_mul, integral_const]
  simp

lemma sq_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h := (sq_shift_integral μ f hf hf2 (∫ x, f x ∂μ)).2
  have h0 : 0 ≤ ∫ x, (f x - ∫ x, f x ∂μ) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  nlinarith

lemma var_le_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    ∫ x, (f x - ∫ x, f x ∂μ) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
  have h := (sq_shift_integral μ f hf hf2 (∫ x, f x ∂μ)).2
  nlinarith [sq_nonneg (∫ x, f x ∂μ)]

/-! ## Real inequalities -/

lemma bern84 (y : ℝ) (hy0 : 0 ≤ y) (k : ℕ) : (1 - 2 * k * y) * (1 + y) ^ (2 * k) ≤ 1 := by
  have hy1 : (0 : ℝ) < 1 + y := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb := one_add_mul_le_pow (a := -(y / (1 + y)))
    (by have : y / (1 + y) ≤ 1 := by rw [div_le_one hy1]; linarith
        linarith) (2 * k)
  have hu : y / (1 + y) ≤ y := div_le_self hy0 (by linarith)
  have h1u : 1 + -(y / (1 + y)) = 1 / (1 + y) := by field_simp; ring
  rw [h1u] at hb
  have hpp : 0 < (1 + y) ^ (2 * k) := by positivity
  have h5 : (1 / (1 + y)) ^ (2 * k) * (1 + y) ^ (2 * k) = 1 := by
    rw [← mul_pow, one_div, inv_mul_cancel₀ hy1.ne']; simp
  have h6 : 1 - 2 * k * y ≤ (1 / (1 + y)) ^ (2 * k) := by
    refine le_trans ?_ hb
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hu hk0]
  calc (1 - 2 * k * y) * (1 + y) ^ (2 * k)
      ≤ (1 / (1 + y)) ^ (2 * k) * (1 + y) ^ (2 * k) :=
        mul_le_mul_of_nonneg_right h6 hpp.le
    _ = 1 := h5

lemma pw84 (y : ℝ) (hy0 : 0 ≤ y) (k : ℕ) (hk : 1 ≤ k) :
    (1 + y) ^ (2 * k) + (y / k) ^ 2 * (1 + y) ^ k ≤ (1 + y) ^ (2 * k + 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hu1 : 1 ≤ (1 + y) ^ k := one_le_pow₀ (by linarith)
  have hyk : (y / k) ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ (by positivity) (div_le_self hy0 hk1) 2
  have e1 : (1 + y) ^ (2 * k) = ((1 + y) ^ k) ^ 2 := by rw [mul_comm, pow_mul]
  rw [pow_add, e1]
  generalize (1 + y) ^ k = u at hu1
  have huu : u ≤ u ^ 2 := by nlinarith
  have hm : (y / k) ^ 2 * u ≤ y ^ 2 * u ^ 2 :=
    mul_le_mul hyk huu (by linarith) (sq_nonneg y)
  nlinarith [mul_nonneg (sq_nonneg u) hy0]

lemma sqpw84 (y E : ℝ) (k : ℕ) :
    ((1 + y) ^ (2 * k + 2) * E) ^ 2 = (1 + y) ^ (4 * k + 4) * E ^ 2 := by
  have : 4 * k + 4 = (2 * k + 2) * 2 := by ring
  rw [this, pow_mul, mul_pow]

lemma sq_sub_le84 (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-! ## Tensor side -/

variable {n d k : ℕ}

lemma frob_nonneg' {c : ℕ} (G : (Fin c → Fin n) → ℝ) : 0 ≤ frob G := by
  unfold frob; exact Finset.sum_nonneg fun w _ => sq_nonneg _

lemma en_nonneg (s : ℝ) (hs : 0 ≤ s) (A : Tens n) : 0 ≤ en k s A := by
  unfold en
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (frob_nonneg' _)

lemma p4_nonneg (x : Fin n → ℝ) : 0 ≤ p4 x := by
  unfold p4; exact Finset.sum_nonneg fun i _ => by positivity

lemma aK_nonneg (n d k : ℕ) : 0 ≤ aK n d k := by unfold aK; positivity

lemma aK_sq (n d k : ℕ) :
    aK n d k ^ 2 = 100 / 81 * (k : ℝ) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 / n := by
  unfold aK
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  ring

lemma cont_heat (A : Tens n) (s : (Fin n → ℝ) → ℝ) (hs : Continuous s) (c : ℕ)
    (w : Fin c → Fin n) : Continuous (fun x => heatA k (s x) A c w) := by
  unfold heatA
  fun_prop

lemma cont_hmean (A : Tens n) (s : (Fin n → ℝ) → ℝ) (hs : Continuous s) :
    Continuous (fun x => hmean k (s x) A) := by
  unfold hmean; exact cont_heat A s hs 0 _

lemma cont_en (A : Tens n) (s : (Fin n → ℝ) → ℝ) (hs : Continuous s) :
    Continuous (fun x => en k (s x) A) := by
  unfold en frob
  refine continuous_finsetSum _ fun c _ => ?_
  refine (continuous_const.mul (hs.pow c)).mul ?_
  exact continuous_finsetSum _ fun w _ => (cont_heat A s hs c w).pow 2

/-- Step 0: the second moment of `F_x - c` over `W`. -/
lemma step0 {P : MvPolynomial (Fin n) ℝ} {A : Tens n} (hR : Rep84 n d k P A) (lam : ℝ)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun W : WIdx n d → ℝ => (FW P lam W x - c) ^ 2) (stdGauss (WIdx n d)) ∧
    ∫ W : WIdx n d → ℝ, (FW P lam W x - c) ^ 2 ∂stdGauss (WIdx n d) =
      en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - c) ^ 2 := by
  obtain ⟨-, -, h3, h4⟩ := hR
  obtain ⟨i1, e1⟩ := h3 lam x
  obtain ⟨i2, e2⟩ := h4 lam x x
  have i2' : Integrable (fun W : WIdx n d → ℝ => FW P lam W x ^ 2) (stdGauss (WIdx n d)) := by
    simpa [sq] using i2
  have e2' : ∫ W : WIdx n d → ℝ, FW P lam W x ^ 2 ∂stdGauss (WIdx n d) =
      en k (lam ^ 2 * kap d x x) A + hmean k (lam ^ 2 * kap d x x) A ^ 2 := by
    have : (fun W : WIdx n d → ℝ => FW P lam W x ^ 2) =
        fun W => FW P lam W x * FW P lam W x := by funext W; ring
    rw [this, e2, Finset.sum_range_succ']
    have hI : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by ext; simp
    unfold en
    rw [hI, Finset.sum_Ico_eq_sum_range]
    congr 1
    · simp only [Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [add_comm 1 c]
      have : tinner (heatA k (lam ^ 2 * kap d x x) A (c + 1))
          (heatA k (lam ^ 2 * kap d x x) A (c + 1)) =
          frob (heatA k (lam ^ 2 * kap d x x) A (c + 1)) := by
        unfold tinner frob; exact Finset.sum_congr rfl fun w _ => by ring
      rw [this]; ring
    · have h0 : heatA k (lam ^ 2 * kap d x x) A 0 default = hmean k (lam ^ 2 * kap d x x) A := by
        unfold hmean; exact congrArg _ (Subsingleton.elim _ _)
      have ht0 : tinner (heatA k (lam ^ 2 * kap d x x) A 0)
          (heatA k (lam ^ 2 * kap d x x) A 0) = hmean k (lam ^ 2 * kap d x x) A ^ 2 := by
        unfold tinner; rw [Fintype.sum_unique, h0]; ring
      rw [ht0]; simp
  have h := sq_shift_integral (stdGauss (WIdx n d)) (fun W => FW P lam W x) i1 i2' c
  refine ⟨h.1, ?_⟩
  rw [h.2, e2', e1]; ring

/-- Step 1: pointwise bounds on the sphere. -/
lemma ptwise (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 1 ≤ n) (hSc : ScaleIface n k)
    (hDel : DeltaIface n d) (A : Tens n) (hA : ∀ j, IsSymmT (A j)) (lam : ℝ)
    (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ)) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2 ≤
      (aK n d k * n * p4 x / k) ^ 2 * (1 + aK n d k * n * p4 x) ^ k * en k (eD d) A ∧
    en k (lam ^ 2 * kap d x x) A ≤ (1 + aK n d k * n * p4 x) ^ (2 * k) * en k (eD d) A ∧
    (1 - 2 * k * (aK n d k * n * p4 x)) * en k (eD d) A ≤ en k (lam ^ 2 * kap d x x) A ∧
    0 ≤ en k (lam ^ 2 * kap d x x) A ∧
    (en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2
      ≤ (1 + aK n d k * n * p4 x) ^ (4 * k + 4) * en k (eD d) A ^ 2 := by
  obtain ⟨hs9, hse⟩ := hDel lam hlam x hx
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have hp4 := p4_nonneg x
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hE : 0 ≤ en k (eD d) A := en_nonneg _ (by linarith) A
  have hv : 0 ≤ en k (lam ^ 2 * kap d x x) A := en_nonneg _ (by linarith) A
  have hyeq : aK n d k * n * p4 x =
      k * ((2 * (d : ℝ) + 2) * p4 x * Real.sqrt n / (9 / 10)) := by
    have h1 : (n : ℝ) / Real.sqrt n = Real.sqrt n := Real.div_sqrt
    have h2 : aK n d k * n * p4 x =
        10 / 9 * k * (2 * (d : ℝ) + 2) * ((n : ℝ) / Real.sqrt n) * p4 x := by
      unfold aK; ring
    rw [h2, h1]; ring
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = aK n d k * n * p4 x := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = lam ^ 2 * kap d x x := ⟨_, rfl⟩
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = en k (eD d) A := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℝ, v = en k s A := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q : ℝ, q = (hmean k s A - hmean k (eD d) A) ^ 2 := ⟨_, rfl⟩
  rw [← hy, ← hs, ← hEd, ← hvd, ← hqd]
  rw [← hy] at hyeq
  rw [← hs] at hs9 hse hv
  rw [← hEd] at hE
  rw [← hvd] at hv
  have hy0 : 0 ≤ y := by rw [hyeq]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = |s - eD d| * Real.sqrt n / (9 / 10) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hkt : (k : ℝ) * t ≤ y := by
    rw [hyeq]
    have : t ≤ (2 * (d : ℝ) + 2) * p4 x * Real.sqrt n / (9 / 10) := by
      rw [ht]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hse (Real.sqrt_nonneg _)) (by norm_num)
    exact mul_le_mul_of_nonneg_left this hk0.le
  have htk : t ≤ y / k := by rw [le_div_iff₀ hk0]; linarith
  have hkt0 : (0 : ℝ) ≤ 1 + k * t := by positivity
  have hle : 1 + (k : ℝ) * t ≤ 1 + y := by linarith
  obtain ⟨h1, h2⟩ := hSc A hA (eD d) s (9 / 10) (by norm_num) (by linarith) hs9
  obtain ⟨-, h3⟩ := hSc A hA s (eD d) (9 / 10) (by norm_num) hs9 (by linarith)
  rw [abs_sub_comm] at h3
  rw [← ht, ← hEd] at h1 h2
  rw [← ht, ← hEd, ← hvd] at h3
  rw [← hqd] at h1
  rw [← hvd] at h2
  have R1 : q ≤ (y / k) ^ 2 * (1 + y) ^ k * E :=
    h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ ht0 htk 2) (pow_le_pow_left₀ hkt0 hle k)
        (pow_nonneg hkt0 k) (sq_nonneg _)) hE)
  have R2 : v ≤ (1 + y) ^ (2 * k) * E :=
    h2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkt0 hle _) hE)
  have R3' : E ≤ (1 + y) ^ (2 * k) * v :=
    h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkt0 hle _) hv)
  have hB := bern84 y hy0 k
  have R3 : (1 - 2 * k * y) * E ≤ v := by
    by_cases hc : 0 ≤ 1 - 2 * k * y
    · calc (1 - 2 * k * y) * E
          ≤ (1 - 2 * k * y) * ((1 + y) ^ (2 * k) * v) :=
            mul_le_mul_of_nonneg_left R3' hc
        _ = ((1 - 2 * k * y) * (1 + y) ^ (2 * k)) * v := by ring
        _ ≤ 1 * v := mul_le_mul_of_nonneg_right hB hv
        _ = v := one_mul _
    · rw [not_le] at hc
      nlinarith
  refine ⟨R1, R2, R3, hv, ?_⟩
  have hq0 : 0 ≤ q := by rw [hqd]; exact sq_nonneg _
  have hsum : v + q ≤ (1 + y) ^ (2 * k + 2) * E :=
    calc v + q ≤ (1 + y) ^ (2 * k) * E + (y / k) ^ 2 * (1 + y) ^ k * E := add_le_add R2 R1
      _ = ((1 + y) ^ (2 * k) + (y / k) ^ 2 * (1 + y) ^ k) * E := by ring
      _ ≤ (1 + y) ^ (2 * k + 2) * E := mul_le_mul_of_nonneg_right (pw84 y hy0 k hk) hE
  rw [← sqpw84]
  exact pow_le_pow_left₀ (add_nonneg hv hq0) hsum 2

/-- Steps 1 and 2: the facts over the sphere. -/
lemma sigmaFacts (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hSc : ScaleIface n k) (hMom : MomIface n) (hDel : DeltaIface n d)
    (ha : 4 * (4 * (k : ℝ) + 5) ^ 2 * aK n d k ≤ 1 / 2)
    (A : Tens n) (hA : ∀ j, IsSymmT (A j)) (lam : ℝ) (hlam : |lam ^ 2 - 1| ≤ 1 / (n : ℝ)) :
    Integrable (fun x : Fin n → ℝ => en k (lam ^ 2 * kap d x x) A) (uniformSphere n) ∧
    Integrable (fun x : Fin n → ℝ => hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A)
      (uniformSphere n) ∧
    Integrable (fun x : Fin n → ℝ => (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2)
      (uniformSphere n) ∧
    ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2 ∂uniformSphere n ≤
      260 * (2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A ∧
    ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ≤ 2 * en k (eD d) A ∧
    (1 - 12 * k * aK n d k) * en k (eD d) A ≤
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ∧
    Integrable (fun x : Fin n → ℝ => (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2) (uniformSphere n) ∧
    ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2 ∂uniformSphere n ≤
      2 * en k (eD d) A ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have ha0 := aK_nonneg n d k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : 0 ≤ en k (eD d) A :=
    en_nonneg _ (by linarith [BstLean.Part81.one_le_eD d hd]) A
  have hcs : Continuous (fun x : Fin n → ℝ => lam ^ 2 * kap d x x) :=
    continuous_const.mul (BstLean.Part81.cont_kap_diag d)
  have hcv := cont_en (k := k) A _ hcs
  have hcm := (cont_hmean (k := k) A _ hcs).sub
    (continuous_const (y := hmean k (eD d) A))
  have iv := BstLean.Part78.sph_int hn hcv
  have im := BstLean.Part78.sph_int hn hcm
  have iq := BstLean.Part78.sph_int hn (hcm.pow 2)
  have ivq := BstLean.Part78.sph_int hn ((hcv.add (hcm.pow 2)).pow 2)
  have hpt := (BstLean.Part29.uniformSphere_ae_sphere n).mono fun x hx =>
    ptwise hd hk hn hSc hDel A hA lam hlam x hx
  have hy0 : ∀ x : Fin n → ℝ, 0 ≤ aK n d k * n * p4 x := fun x =>
    mul_nonneg (mul_nonneg ha0 (Nat.cast_nonneg n)) (p4_nonneg x)
  -- moments
  obtain ⟨iA, mA, -⟩ := hMom _ ha0 0 (4 * k + 4)
  have iA' : Integrable (fun x : Fin n → ℝ => (1 + aK n d k * n * p4 x) ^ (4 * k + 4))
      (uniformSphere n) := by
    simpa only [pow_zero, one_mul] using iA
  have c1 : (((4 * k + 4 : ℕ) : ℝ) + 1) = 4 * k + 5 := by push_cast; ring
  rw [c1] at mA
  have I1 : ∫ x : Fin n → ℝ, (1 + aK n d k * n * p4 x) ^ (4 * k + 4) ∂uniformSphere n ≤ 2 := by
    have := mA ha
    linarith
  obtain ⟨iB, -, -⟩ := hMom _ ha0 0 (2 * k)
  have iB' : Integrable (fun x : Fin n → ℝ => (1 + aK n d k * n * p4 x) ^ (2 * k))
      (uniformSphere n) := by
    simpa only [pow_zero, one_mul] using iB
  have I2 : ∫ x : Fin n → ℝ, (1 + aK n d k * n * p4 x) ^ (2 * k) ∂uniformSphere n ≤ 2 :=
    (integral_mono iB' iA' (fun x => pow_le_pow_right₀ (by linarith [hy0 x]) (by omega))).trans I1
  obtain ⟨iC, -, mC⟩ := hMom _ ha0 2 k
  have d7 : (4 * 2 - 1).doubleFactorial = 105 := by decide
  have I3 : ∫ x : Fin n → ℝ, (aK n d k * n * p4 x) ^ 2 * (1 + aK n d k * n * p4 x) ^ k
      ∂uniformSphere n ≤ 210 * aK n d k ^ 2 := by
    have h := mC (by
      push_cast
      nlinarith [mul_nonneg ha0 (sq_nonneg (k : ℝ)), mul_nonneg ha0 hk0.le, ha0])
    rw [d7] at h
    push_cast at h
    linarith
  obtain ⟨iD, -, mD⟩ := hMom _ ha0 1 0
  have iD' : Integrable (fun x : Fin n → ℝ => aK n d k * n * p4 x) (uniformSphere n) := by
    simpa only [pow_zero, mul_one, pow_one] using iD
  have d3 : (4 * 1 - 1).doubleFactorial = 3 := by decide
  have I4 : ∫ x : Fin n → ℝ, aK n d k * n * p4 x ∂uniformSphere n ≤ 6 * aK n d k := by
    have h := mD (by norm_num)
    rw [d3] at h
    simp only [pow_zero, mul_one, pow_one] at h
    push_cast at h
    linarith
  -- (b)
  have Hq : ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2
      ∂uniformSphere n ≤ 260 * (2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A := by
    have efun : (fun x : Fin n → ℝ => (aK n d k * n * p4 x / k) ^ 2 *
        (1 + aK n d k * n * p4 x) ^ k * en k (eD d) A) =
        fun x => en k (eD d) A / k ^ 2 *
          ((aK n d k * n * p4 x) ^ 2 * (1 + aK n d k * n * p4 x) ^ k) := by
      funext x; ring
    have ib : Integrable (fun x : Fin n → ℝ => (aK n d k * n * p4 x / k) ^ 2 *
        (1 + aK n d k * n * p4 x) ^ k * en k (eD d) A) (uniformSphere n) := by
      rw [efun]; exact iC.const_mul _
    have hDE : 0 ≤ (2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A := by positivity
    calc ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2
          ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, (aK n d k * n * p4 x / k) ^ 2 *
            (1 + aK n d k * n * p4 x) ^ k * en k (eD d) A ∂uniformSphere n :=
          integral_mono_ae iq ib (hpt.mono fun x h => h.1)
      _ = en k (eD d) A / k ^ 2 * ∫ x : Fin n → ℝ, (aK n d k * n * p4 x) ^ 2 *
            (1 + aK n d k * n * p4 x) ^ k ∂uniformSphere n := by
          rw [efun, integral_const_mul]
      _ ≤ en k (eD d) A / k ^ 2 * (210 * aK n d k ^ 2) :=
          mul_le_mul_of_nonneg_left I3 (by positivity)
      _ = 21000 / 81 * ((2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A) := by
          rw [aK_sq]; field_simp; ring
      _ ≤ 260 * (2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A := by
          have : 260 * (2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A =
              260 * ((2 * (d : ℝ) + 2) ^ 2 / n * en k (eD d) A) := by ring
          rw [this]; nlinarith
  -- (c)
  have Hv : ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n ≤
      2 * en k (eD d) A :=
    calc ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, (1 + aK n d k * n * p4 x) ^ (2 * k) * en k (eD d) A
            ∂uniformSphere n :=
          integral_mono_ae iv (iB'.mul_const _) (hpt.mono fun x h => h.2.1)
      _ = (∫ x : Fin n → ℝ, (1 + aK n d k * n * p4 x) ^ (2 * k) ∂uniformSphere n) *
            en k (eD d) A := integral_mul_const _ _
      _ ≤ 2 * en k (eD d) A := mul_le_mul_of_nonneg_right I2 hE
  -- (d)
  have Hfl : (1 - 12 * k * aK n d k) * en k (eD d) A ≤
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n := by
    have il0 : Integrable (fun x : Fin n → ℝ => 1 - 2 * (k : ℝ) * (aK n d k * n * p4 x))
        (uniformSphere n) := (integrable_const (1 : ℝ)).sub (iD'.const_mul _)
    have e0 : ∫ x : Fin n → ℝ, (1 - 2 * (k : ℝ) * (aK n d k * n * p4 x)) ∂uniformSphere n =
        1 - 2 * k * ∫ x : Fin n → ℝ, aK n d k * n * p4 x ∂uniformSphere n := by
      have h1 : ∫ x : Fin n → ℝ, (1 - 2 * (k : ℝ) * (aK n d k * n * p4 x)) ∂uniformSphere n =
          ∫ _x : Fin n → ℝ, (1 : ℝ) ∂uniformSphere n -
            ∫ x : Fin n → ℝ, 2 * (k : ℝ) * (aK n d k * n * p4 x) ∂uniformSphere n :=
        integral_sub (integrable_const (1 : ℝ)) (iD'.const_mul _)
      rw [h1, integral_const_mul, integral_const]; simp
    calc (1 - 12 * k * aK n d k) * en k (eD d) A
        ≤ (1 - 2 * k * ∫ x : Fin n → ℝ, aK n d k * n * p4 x ∂uniformSphere n) *
            en k (eD d) A :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [mul_le_mul_of_nonneg_left I4 hk0.le]) hE
      _ = ∫ x : Fin n → ℝ, (1 - 2 * (k : ℝ) * (aK n d k * n * p4 x)) * en k (eD d) A
            ∂uniformSphere n := by
          rw [integral_mul_const, e0]
      _ ≤ ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n :=
          integral_mono_ae (il0.mul_const _) iv (hpt.mono fun x h => h.2.2.1)
  -- (e)
  have Hvq : ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
      (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2 ∂uniformSphere n ≤
      2 * en k (eD d) A ^ 2 :=
    calc ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
          (hmean k (lam ^ 2 * kap d x x) A - hmean k (eD d) A) ^ 2) ^ 2 ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, (1 + aK n d k * n * p4 x) ^ (4 * k + 4) * en k (eD d) A ^ 2
            ∂uniformSphere n :=
          integral_mono_ae ivq (iA'.mul_const _) (hpt.mono fun x h => h.2.2.2.2)
      _ = (∫ x : Fin n → ℝ, (1 + aK n d k * n * p4 x) ^ (4 * k + 4) ∂uniformSphere n) *
            en k (eD d) A ^ 2 := integral_mul_const _ _
      _ ≤ 2 * en k (eD d) A ^ 2 := mul_le_mul_of_nonneg_right I1 (sq_nonneg _)
  exact ⟨iv, im, iq, Hq, Hv, Hfl, ivq, Hvq⟩

/-- **The Gaussian model given the constant column.** -/
theorem gaussModel (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 10 ≤ n) (CF K4 : ℝ) (hCF : 0 ≤ CF)
    (hK4 : 0 ≤ K4)
    (hRep : RepIface n d) (hSc : ScaleIface n k) (hDec : DecorIface n d CF) (hFub : FubIface n d)
    (hMom : MomIface n) (hDel : DeltaIface n d) (hPoly : PolyRep n d) (h4 : Fourth84 k K4)
    (ha : 4 * (4 * (k : ℝ) + 5) ^ 2 * aK n d k ≤ 1 / 2) :
    GaussModel n d k (c1F d CF) (K4 * (4 * CF + 2 * c1F d CF ^ 2 / n))
      (12 * k * aK n d k + c1F d CF / n) := by
  intro P hP lam hlam
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hprob := BstLean.Part29.uniformSphere_isProbability n hn1
  obtain ⟨A, hR⟩ := hRep k P hP
  have hA := hR.1
  have hg0 := hR.2.1
  have h3 := hR.2.2.1
  have hS0 := step0 hR lam
  obtain ⟨iv, im, iq, Hq, Hv, Hfl, ivq, Hvq⟩ :=
    sigmaFacts hd hk hn1 hSc hMom hDel ha A hA lam hlam
  have he : 1 ≤ eD d := BstLean.Part81.one_le_eD d hd
  have hE : 0 ≤ en k (eD d) A := en_nonneg _ (by linarith) A
  rw [← hg0] at im iq Hq ivq Hvq
  have herrdef : ∀ W : WIdx n d → ℝ, errW P lam W = BW P lam W - g0P d P := fun W => rfl
  clear hg0 hR
  generalize en k (eD d) A = E at *
  generalize g0P d P = g at *
  obtain ⟨P2, hP2def⟩ : ∃ P2 : MvPolynomial (Fin n) ℝ, P2 = (P - MvPolynomial.C g) ^ 2 :=
    ⟨_, rfl⟩
  have hP2 : P2.totalDegree ≤ 2 * k := by
    rw [hP2def]
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    have : (P - MvPolynomial.C g).totalDegree ≤ k :=
      (MvPolynomial.totalDegree_sub _ _).trans (by simp [hP])
    exact Nat.mul_le_mul_left 2 this
  have hFW2 : ∀ (W : WIdx n d → ℝ) (x : Fin n → ℝ),
      FW P2 lam W x = (FW P lam W x - g) ^ 2 := by
    intro W x; rw [hP2def]; simp [FW]
  obtain ⟨hQx, QB, hQBd, hQB⟩ := hPoly k P hP lam
  obtain ⟨-, QX, hQXd, hQX⟩ := hPoly (2 * k) P2 hP2 lam
  obtain ⟨fF, fB, fE⟩ := hFub P lam
  obtain ⟨fF2, fB2, fE2⟩ := hFub P2 lam
  obtain ⟨iD, hD⟩ := hDec k P hP lam
  obtain ⟨iDX, hDX⟩ := hDec (2 * k) P2 hP2 lam
  have degsub : ∀ Q : MvPolynomial (WIdx n d) ℝ, Q.totalDegree ≤ k →
      (Q - MvPolynomial.C g).totalDegree ≤ k := fun Q hQ =>
    (MvPolynomial.totalDegree_sub _ _).trans (by simp [hQ])
  have ic : ∀ (Q : MvPolynomial (WIdx n d) ℝ) (f : (WIdx n d → ℝ) → ℝ),
      (∀ W, f W = MvPolynomial.eval W Q) → Integrable f (stdGauss (WIdx n d)) := fun Q f h => by
    rw [show f = fun W => MvPolynomial.eval W Q from funext h]
    exact BstLean.Part59.gaussian_eval_integrable59x Q
  have herrQ : ∀ W : WIdx n d → ℝ,
      errW P lam W = MvPolynomial.eval W (QB - MvPolynomial.C g) := fun W => by
    rw [herrdef, map_sub, MvPolynomial.eval_C, hQB]
  have ierr2 : Integrable (fun W : WIdx n d → ℝ => errW P lam W ^ 2) (stdGauss (WIdx n d)) :=
    ic ((QB - MvPolynomial.C g) ^ 2) _ (fun W => by simp only [map_pow, herrQ])
  have ierr4 : Integrable (fun W : WIdx n d → ℝ => (errW P lam W ^ 2) ^ 2)
      (stdGauss (WIdx n d)) :=
    ic (((QB - MvPolynomial.C g) ^ 2) ^ 2) _ (fun W => by simp only [map_pow, herrQ])
  -- Step 3: the error
  have hDv : (fun x : Fin n → ℝ => ∫ W : WIdx n d → ℝ,
      (FW P lam W x - ∫ W' : WIdx n d → ℝ, FW P lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d)) = fun x => en k (lam ^ 2 * kap d x x) A := by
    funext x
    rw [(h3 lam x).2, (hS0 x _).2]; simp
  rw [hDv] at hD
  have hbar : (∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d)) - g =
      ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ∂uniformSphere n := by
    have e1 : (fun x : Fin n → ℝ => ∫ W : WIdx n d → ℝ, FW P lam W x ∂stdGauss (WIdx n d)) =
        fun x => (hmean k (lam ^ 2 * kap d x x) A - g) + g := by
      funext x; rw [(h3 lam x).2]; ring
    have e2 : ∫ x : Fin n → ℝ, ((hmean k (lam ^ 2 * kap d x x) A - g) + g) ∂uniformSphere n =
        ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ∂uniformSphere n +
          ∫ _x : Fin n → ℝ, g ∂uniformSphere n := integral_add im (integrable_const g)
    rw [fE, e1, e2, integral_const]; simp
  generalize hbb : (∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d)) = bbar at *
  have hb2 : (bbar - g) ^ 2 ≤ 260 * (2 * (d : ℝ) + 2) ^ 2 / n * E := by
    rw [hbar]
    exact (sq_integral_le _ _ im iq).trans Hq
  have hD' : ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ^ 2 ∂stdGauss (WIdx n d) ≤
      CF / n * (2 * E) :=
    calc ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ^ 2 ∂stdGauss (WIdx n d)
        ≤ CF / (eD d * n) * ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n := hD
      _ ≤ CF / (eD d * n) * (2 * E) := mul_le_mul_of_nonneg_left Hv (by positivity)
      _ ≤ CF / n * (2 * E) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left hCF hn0 (by nlinarith)) (by positivity)
  have iBc : Integrable (fun W : WIdx n d → ℝ => BW P lam W - bbar) (stdGauss (WIdx n d)) :=
    fB.sub (integrable_const _)
  have hBc0 : ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ∂stdGauss (WIdx n d) = 0 := by
    have h1 : ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ∂stdGauss (WIdx n d) =
        ∫ W : WIdx n d → ℝ, BW P lam W ∂stdGauss (WIdx n d) -
          ∫ _W : WIdx n d → ℝ, bbar ∂stdGauss (WIdx n d) :=
      integral_sub fB (integrable_const _)
    rw [h1, integral_const, hbb]; simp
  have Herr0 : ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d) =
      ∫ W : WIdx n d → ℝ, (BW P lam W - bbar) ^ 2 ∂stdGauss (WIdx n d) + (bbar - g) ^ 2 := by
    have h := (sq_shift_integral (stdGauss (WIdx n d)) (fun W => BW P lam W - bbar) iBc iD
      (g - bbar)).2
    have e : (fun W : WIdx n d → ℝ => errW P lam W ^ 2) =
        fun W => (BW P lam W - bbar - (g - bbar)) ^ 2 := by
      funext W; rw [herrdef]; ring
    rw [e, h, hBc0]; ring
  have Herr : ∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d) ≤
      c1F d CF / n * E := by
    have e : c1F d CF / n * E = 260 * (2 * (d : ℝ) + 2) ^ 2 / n * E + CF / n * (2 * E) := by
      unfold c1F; ring
    rw [Herr0, e]; linarith
  -- Step 4: the floor
  have hVW : ∀ W : WIdx n d → ℝ, VW P lam W = BW P2 lam W - errW P lam W ^ 2 := by
    intro W
    have i2 : Integrable (fun x : Fin n → ℝ => (FW P lam W x - g) ^ 2) (uniformSphere n) := by
      have : Integrable (fun x : Fin n → ℝ => FW P2 lam W x) (uniformSphere n) := fF2 W
      simpa only [hFW2] using this
    have h := (sq_shift_integral (uniformSphere n) (fun x => FW P lam W x - g)
      ((fF W).sub (integrable_const g)) i2 (errW P lam W)).2
    have e1 : ∫ x : Fin n → ℝ, (FW P lam W x - g) ∂uniformSphere n = errW P lam W := by
      have h1 : ∫ x : Fin n → ℝ, (FW P lam W x - g) ∂uniformSphere n =
          ∫ x : Fin n → ℝ, FW P lam W x ∂uniformSphere n - ∫ _x : Fin n → ℝ, g ∂uniformSphere n :=
        integral_sub (fF W) (integrable_const g)
      rw [h1, integral_const, herrdef]; simp [BW]
    have e2 : ∫ x : Fin n → ℝ, (FW P lam W x - g) ^ 2 ∂uniformSphere n = BW P2 lam W := by
      unfold BW; simp only [hFW2]
    have e3 : VW P lam W =
        ∫ x : Fin n → ℝ, (FW P lam W x - g - errW P lam W) ^ 2 ∂uniformSphere n := by
      unfold VW varU
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [herrdef, BW]; ring
    rw [e3, h, e1, e2]; ring
  have hXint : ∫ W : WIdx n d → ℝ, BW P2 lam W ∂stdGauss (WIdx n d) =
      ∫ x : Fin n → ℝ, en k (lam ^ 2 * kap d x x) A ∂uniformSphere n +
        ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 ∂uniformSphere n := by
    have e1 : (fun x : Fin n → ℝ => ∫ W : WIdx n d → ℝ, FW P2 lam W x ∂stdGauss (WIdx n d)) =
        fun x => en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 := by
      funext x; simp only [hFW2]; exact (hS0 x g).2
    rw [fE2, e1]
    exact integral_add iv iq
  have hq0 : 0 ≤ ∫ x : Fin n → ℝ, (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 ∂uniformSphere n :=
    integral_nonneg fun x => sq_nonneg _
  -- Step 5: the variance of `V`
  have hG : ∀ x : Fin n → ℝ, ∫ W : WIdx n d → ℝ,
      (FW P2 lam W x - ∫ W' : WIdx n d → ℝ, FW P2 lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d) ≤
      K4 * (en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 := by
    intro x
    obtain ⟨Q, hQd, hQ⟩ := hQx x
    have hfq : ∀ W : WIdx n d → ℝ,
        FW P2 lam W x = MvPolynomial.eval W ((Q - MvPolynomial.C g) ^ 2) := fun W => by
      rw [hFW2, map_pow, map_sub, MvPolynomial.eval_C, hQ]
    have i1 : Integrable (fun W : WIdx n d → ℝ => FW P2 lam W x) (stdGauss (WIdx n d)) :=
      ic _ _ hfq
    have i2 : Integrable (fun W : WIdx n d → ℝ => FW P2 lam W x ^ 2) (stdGauss (WIdx n d)) :=
      ic (((Q - MvPolynomial.C g) ^ 2) ^ 2) _ (fun W => by simp only [map_pow, hfq])
    have h44 := h4 (WIdx n d) (Q - MvPolynomial.C g) (degsub Q hQd)
    have e4 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (Q - MvPolynomial.C g) ^ 4) =
        fun W => FW P2 lam W x ^ 2 := by
      funext W; rw [hFW2, map_sub, MvPolynomial.eval_C, hQ]; ring
    have e2 : ∫ W : WIdx n d → ℝ, MvPolynomial.eval W (Q - MvPolynomial.C g) ^ 2
        ∂stdGauss (WIdx n d) =
        en k (lam ^ 2 * kap d x x) A + (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2 := by
      rw [← (hS0 x g).2]
      refine integral_congr_ae (ae_of_all _ fun W => ?_)
      simp only [map_sub, MvPolynomial.eval_C, hQ]
    rw [e4, e2] at h44
    exact (var_le_sq (stdGauss (WIdx n d)) _ i1 i2).trans h44
  have hGint : ∫ x : Fin n → ℝ, (∫ W : WIdx n d → ℝ,
      (FW P2 lam W x - ∫ W' : WIdx n d → ℝ, FW P2 lam W' x ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d)) ∂uniformSphere n ≤ K4 * (2 * E ^ 2) :=
    calc ∫ x : Fin n → ℝ, (∫ W : WIdx n d → ℝ,
          (FW P2 lam W x - ∫ W' : WIdx n d → ℝ, FW P2 lam W' x ∂stdGauss (WIdx n d)) ^ 2
          ∂stdGauss (WIdx n d)) ∂uniformSphere n
        ≤ ∫ x : Fin n → ℝ, K4 * (en k (lam ^ 2 * kap d x x) A +
            (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 ∂uniformSphere n :=
          integral_mono_of_nonneg
            (ae_of_all _ fun x => integral_nonneg fun W => sq_nonneg _)
            (ivq.const_mul K4) (ae_of_all _ hG)
      _ = K4 * ∫ x : Fin n → ℝ, (en k (lam ^ 2 * kap d x x) A +
            (hmean k (lam ^ 2 * kap d x x) A - g) ^ 2) ^ 2 ∂uniformSphere n :=
          integral_const_mul _ _
      _ ≤ K4 * (2 * E ^ 2) := mul_le_mul_of_nonneg_left Hvq hK4
  have hXvar : ∫ W : WIdx n d → ℝ,
      (BW P2 lam W - ∫ W' : WIdx n d → ℝ, BW P2 lam W' ∂stdGauss (WIdx n d)) ^ 2
      ∂stdGauss (WIdx n d) ≤ CF / n * (K4 * (2 * E ^ 2)) :=
    hDX.trans <|
      (mul_le_mul_of_nonneg_left hGint (by positivity)).trans <|
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hCF hn0 (by nlinarith)) (by positivity)
  have hY2 : ∫ W : WIdx n d → ℝ, (errW P lam W ^ 2) ^ 2 ∂stdGauss (WIdx n d) ≤
      K4 * (c1F d CF / n * E) ^ 2 := by
    have h44 := h4 (WIdx n d) (QB - MvPolynomial.C g) (degsub QB hQBd)
    have e4 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (QB - MvPolynomial.C g) ^ 4) =
        fun W => (errW P lam W ^ 2) ^ 2 := by
      funext W; rw [← herrQ]; ring
    have e2 : (fun W : WIdx n d → ℝ => MvPolynomial.eval W (QB - MvPolynomial.C g) ^ 2) =
        fun W => errW P lam W ^ 2 := by
      funext W; rw [← herrQ]
    rw [e4, e2] at h44
    exact h44.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun W => sq_nonneg _) Herr 2) hK4)
  have hYvar := var_le_sq (stdGauss (WIdx n d)) (fun W => errW P lam W ^ 2) ierr2 ierr4
  have hVQ : ∀ W : WIdx n d → ℝ, VW P lam W =
      MvPolynomial.eval W (QX - (QB - MvPolynomial.C g) ^ 2) := fun W => by
    rw [hVW, map_sub, map_pow, hQX, ← herrQ]
  generalize (∫ W : WIdx n d → ℝ, BW P2 lam W ∂stdGauss (WIdx n d)) = Xb at *
  generalize hYb : (∫ W : WIdx n d → ℝ, errW P lam W ^ 2 ∂stdGauss (WIdx n d)) = Yb at *
  have iYc : Integrable (fun W : WIdx n d → ℝ => (errW P lam W ^ 2 - Yb) ^ 2)
      (stdGauss (WIdx n d)) :=
    (sq_shift_integral (stdGauss (WIdx n d)) (fun W => errW P lam W ^ 2) ierr2 ierr4 Yb).1
  have iV : Integrable (fun W : WIdx n d → ℝ => (VW P lam W - (Xb - Yb)) ^ 2)
      (stdGauss (WIdx n d)) :=
    ic ((QX - (QB - MvPolynomial.C g) ^ 2 - MvPolynomial.C (Xb - Yb)) ^ 2) _
      (fun W => by simp only [map_pow, map_sub, MvPolynomial.eval_C, hVQ])
  have HV : ∫ W : WIdx n d → ℝ, (VW P lam W - (Xb - Yb)) ^ 2 ∂stdGauss (WIdx n d) ≤
      K4 * (4 * CF + 2 * c1F d CF ^ 2 / n) / n * E ^ 2 := by
    have hsum : ∫ W : WIdx n d → ℝ, (2 * (BW P2 lam W - Xb) ^ 2 +
        2 * (errW P lam W ^ 2 - Yb) ^ 2) ∂stdGauss (WIdx n d) =
        2 * ∫ W : WIdx n d → ℝ, (BW P2 lam W - Xb) ^ 2 ∂stdGauss (WIdx n d) +
        2 * ∫ W : WIdx n d → ℝ, (errW P lam W ^ 2 - Yb) ^ 2 ∂stdGauss (WIdx n d) := by
      have h1 : ∫ W : WIdx n d → ℝ, (2 * (BW P2 lam W - Xb) ^ 2 +
          2 * (errW P lam W ^ 2 - Yb) ^ 2) ∂stdGauss (WIdx n d) =
          ∫ W : WIdx n d → ℝ, 2 * (BW P2 lam W - Xb) ^ 2 ∂stdGauss (WIdx n d) +
          ∫ W : WIdx n d → ℝ, 2 * (errW P lam W ^ 2 - Yb) ^ 2 ∂stdGauss (WIdx n d) :=
        integral_add (iDX.const_mul 2) (iYc.const_mul 2)
      rw [h1, integral_const_mul, integral_const_mul]
    have hpw : ∀ W : WIdx n d → ℝ, (VW P lam W - (Xb - Yb)) ^ 2 ≤
        2 * (BW P2 lam W - Xb) ^ 2 + 2 * (errW P lam W ^ 2 - Yb) ^ 2 := by
      intro W
      rw [hVW]
      have := sq_sub_le84 (BW P2 lam W - Xb) (errW P lam W ^ 2 - Yb)
      have e : BW P2 lam W - errW P lam W ^ 2 - (Xb - Yb) =
          BW P2 lam W - Xb - (errW P lam W ^ 2 - Yb) := by ring
      rw [e]; exact this
    calc ∫ W : WIdx n d → ℝ, (VW P lam W - (Xb - Yb)) ^ 2 ∂stdGauss (WIdx n d)
        ≤ ∫ W : WIdx n d → ℝ, (2 * (BW P2 lam W - Xb) ^ 2 +
            2 * (errW P lam W ^ 2 - Yb) ^ 2) ∂stdGauss (WIdx n d) :=
          integral_mono_ae iV ((iDX.const_mul 2).add (iYc.const_mul 2)) (ae_of_all _ hpw)
      _ = 2 * ∫ W : WIdx n d → ℝ, (BW P2 lam W - Xb) ^ 2 ∂stdGauss (WIdx n d) +
          2 * ∫ W : WIdx n d → ℝ, (errW P lam W ^ 2 - Yb) ^ 2 ∂stdGauss (WIdx n d) := hsum
      _ ≤ 2 * (CF / n * (K4 * (2 * E ^ 2))) + 2 * (K4 * (c1F d CF / n * E) ^ 2) := by
          linarith [hXvar, hYvar.trans hY2]
      _ = K4 * (4 * CF + 2 * c1F d CF ^ 2 / n) / n * E ^ 2 := by
          field_simp; ring
  refine ⟨E, Xb - Yb, hE, ?_, ierr2, iV, Herr, HV⟩
  rw [hXint]
  linarith

end BstLean.Part84
