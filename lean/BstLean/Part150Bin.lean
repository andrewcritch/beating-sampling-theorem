import BstLean.Part150Norm2

/-!
# Part 150, item 5 (a part): the binomial centre against the paper's oracle centre, in mean

Role: `delegations/statements/p150-spec.md`, item 5. `bT` is the finite (binomial) centre and `bO`
the paper's oracle centre (`Part150CDefs`); `ρ = rhoC c τ`; `A₁ ∼ gaussMat m n (2/n)`,
`A₂ ∼ gaussMat m m (2/m)`.

* `measurable_bT`, `measurable_bO`, `measurable_rhoC`, `measurable_binDisp`: measurability.
* `bin_disp_pt`: for every `A₁`, `A₂`:
  `|(bT − bO)/ρ|² ≤ (3/ρ²)(m α² s̃² + (m/(2π))|s̃² − s²| + |A₂(h̃ − h̄)|²)`.
* `bin_disp_A2`: the mean over `A₂` for a fixed `A₁`:
  `≤ (3/ρ²)(kapF J·τ²‖A₁‖²_F + (α/π)|A₁c|²)`.
* **`bin_disp_mean`**: the mean over `A₁` and `A₂` is at most `(m/n)·xiBin J`,
  `xiBin J = 3(8α² + (2β + 4α + 2α²)/π)`, `α = alphaJ J`, `β = betaJ J`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part137 BstLean.Part141
open BstLean.Part132 (nrm nrm_nonneg nrm_sq)
open BstLean.Part136 (HidParam hidGauss)

variable {n m : ℕ}

/-! ## Measurability -/

lemma measurable_binMean_affine {X : Type*} [MeasurableSpace X] (J : ℕ) {g : ℝ → ℝ}
    (hg : Measurable g) {a s : X → ℝ} (ha : Measurable a) (hs : Measurable s) :
    Measurable (fun x => binMean J (fun z => g (a x + s x * z))) := by
  unfold binMean
  exact Finset.measurable_sum _ fun j _ => (hg.comp (ha.add (hs.mul_const _))).const_mul _

lemma measurable_entry150 (i : Fin m) (j : Fin n) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => A i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

lemma measurable_mRowX (i : Fin m) :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => mRow x.2.1 x.1.1 i) := by
  have h := (BstLean.Part149.measurable_mulVec_joint (m := m) (k := n)).comp
    ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst) :
      Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => (x.2.1, x.1.1)))
  exact (measurable_pi_apply i).comp h

lemma measurable_sRowX (i : Fin m) :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => sRow x.2.1 x.1.2 i) := by
  unfold sRow
  refine (measurable_snd.comp measurable_fst).mul (Real.continuous_sqrt.measurable.comp ?_)
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_entry150 i j).comp (measurable_fst.comp measurable_snd)).pow_const 2

lemma measurable_hT (J : ℕ) :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => hT J x.2.1 x.1.1 x.1.2) :=
  measurable_pi_iff.mpr fun i =>
    measurable_binMean_affine J measurable_relu (measurable_mRowX i) (measurable_sRowX i)

lemma measurable_sT (J : ℕ) :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => sT J x.2.1 x.1.1 x.1.2) := by
  have hg : Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => gT J x.2.1 x.1.1 x.1.2) := by
    unfold gT
    exact (Finset.measurable_sum _ fun i _ =>
      measurable_binMean_affine J (measurable_relu.pow_const 2) (measurable_mRowX i)
        (measurable_sRowX i)).const_mul _
  have hh : Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m =>
      ∑ i, hT J x.2.1 x.1.1 x.1.2 i ^ 2) :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp (measurable_hT J)).pow_const 2
  unfold sT sT2
  exact Real.continuous_sqrt.measurable.comp (hg.sub (hh.const_mul _))

/-- The finite centre is measurable in `(c, τ, A₁, A₂)`. -/
theorem measurable_bT (J₁ J₂ : ℕ) :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => bT J₁ J₂ x.2.1 x.2.2 x.1.1 x.1.2) := by
  have hmv := (BstLean.Part149.measurable_mulVec_joint (m := m) (k := m)).comp
    ((measurable_snd.comp measurable_snd).prodMk (measurable_hT J₁) :
      Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => (x.2.2, hT J₁ x.2.1 x.1.1 x.1.2)))
  exact measurable_pi_iff.mpr fun j =>
    measurable_binMean_affine J₂ measurable_relu ((measurable_pi_apply j).comp hmv)
      (measurable_sT J₁)

lemma measurable_hO :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => hO x.2.1 x.1.1 x.1.2) :=
  measurable_pi_iff.mpr fun i => by
    have h := measurable_psiS.comp ((measurable_sRowX (n := n) (m := m) i).prodMk
      (measurable_mRowX i))
    exact h

lemma measurable_sO :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => sO x.2.1 x.1.1 x.1.2) := by
  have hi : ∀ i : Fin m, Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m =>
      ∫ z, relu (mRow x.2.1 x.1.1 i + sRow x.2.1 x.1.2 i * z) ^ 2 ∂gaussianReal 0 1) := by
    intro i
    have hF : Measurable (fun q : (((Fin n → ℝ) × ℝ) × HidParam n m) × ℝ =>
        relu (mRow q.1.2.1 q.1.1.1 i + sRow q.1.2.1 q.1.1.2 i * q.2) ^ 2) :=
      (measurable_relu.comp (((measurable_mRowX i).comp measurable_fst).add
        (((measurable_sRowX i).comp measurable_fst).mul measurable_snd))).pow_const 2
    exact hF.stronglyMeasurable.integral_prod_right'.measurable
  have hg : Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => gO x.2.1 x.1.1 x.1.2) := by
    unfold gO
    exact (Finset.measurable_sum _ fun i _ => hi i).const_mul _
  have hh : Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m =>
      ∑ i, hO x.2.1 x.1.1 x.1.2 i ^ 2) :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_hO).pow_const 2
  unfold sO sO2
  exact Real.continuous_sqrt.measurable.comp (hg.sub (hh.const_mul _))

/-- The paper's oracle centre is measurable in `(c, τ, A₁, A₂)`. -/
theorem measurable_bO :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => bO x.2.1 x.2.2 x.1.1 x.1.2) := by
  have hmv := (BstLean.Part149.measurable_mulVec_joint (m := m) (k := m)).comp
    ((measurable_snd.comp measurable_snd).prodMk measurable_hO :
      Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m => (x.2.2, hO x.2.1 x.1.1 x.1.2)))
  exact measurable_pi_iff.mpr fun j => by
    have h := measurable_psiS.comp ((measurable_sO (n := n) (m := m)).prodMk
      ((measurable_pi_apply j).comp hmv))
    exact h

theorem measurable_rhoC : Measurable (fun x : (Fin n → ℝ) × ℝ => rhoC x.1 x.2) := by
  unfold rhoC
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_normSq.comp measurable_fst).add ((measurable_snd.pow_const 2).const_mul _))

/-- The squared scaled displacement is measurable in `(c, τ, A₁, A₂)`. -/
theorem measurable_binDispX (J : ℕ) :
    Measurable (fun x : ((Fin n → ℝ) × ℝ) × HidParam n m =>
      normSq ((1 / rhoC x.1.1 x.1.2) • (bT J J x.2.1 x.2.2 x.1.1 x.1.2 -
        bO x.2.1 x.2.2 x.1.1 x.1.2))) :=
  measurable_normSq.comp
    (((measurable_const.div (measurable_rhoC.comp measurable_fst))).smul
      ((measurable_bT J J).sub measurable_bO))

/-- For fixed `c, τ, A₁`: measurable in `A₂`. -/
theorem measurable_binDisp (J : ℕ) (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ))) := by
  have h0 : Measurable (fun A₂ : Matrix (Fin m) (Fin m) ℝ => (((c, τ), (A₁, A₂)) :
      ((Fin n → ℝ) × ℝ) × HidParam n m)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have h1 := (measurable_bT (n := n) (m := m) J J).comp h0
  simp only [Function.comp_def] at h1
  have h2 := (measurable_bO (n := n) (m := m)).comp h0
  simp only [Function.comp_def] at h2
  have h3 : Measurable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      (1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)) := by
    have h12 : Measurable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
        bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) := h1.sub h2
    exact (measurable_const (a := 1 / rhoC c τ)).smul h12
  exact measurable_normSq.comp h3

/-! ## The pointwise bound -/

lemma sqrt_sub_sq_le (a b : ℝ) : (√a - √b) ^ 2 ≤ |a - b| := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · have hx := Real.sqrt_nonneg a
    have hy := Real.sqrt_nonneg b
    have e : a - b = (√a - √b) * (√a + √b) := by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
    have h1 : |√a - √b| ≤ √a + √b := by rw [abs_le]; constructor <;> linarith
    calc (√a - √b) ^ 2 = |√a - √b| * |√a - √b| := by rw [← sq, sq_abs]
      _ ≤ |√a - √b| * (√a + √b) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |a - b| := by rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ √a + √b)]
  · rw [Real.sqrt_eq_zero_of_nonpos hb.le, sub_zero, Real.sq_sqrt ha,
      abs_of_nonneg (by linarith)]
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos ha.le, zero_sub, neg_sq, Real.sq_sqrt hb,
      abs_of_nonpos (by linarith)]
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos ha.le, Real.sqrt_eq_zero_of_nonpos hb.le]
    simp

/-- The pointwise bound of the scaled displacement. -/
theorem bin_disp_pt {J : ℕ} (hJ : 1 ≤ J) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)) ≤
      3 / rhoC c τ ^ 2 * ((m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ +
        (m : ℝ) / (2 * π) * |sT2 J A₁ c τ - sO2 A₁ c τ| +
        normSq (A₂.mulVec (hT J A₁ c τ - hO A₁ c τ))) := by
  have hpi := Real.pi_pos
  have h := (centre150_second J hJ A₁ A₂ c τ).2
  set X := nrm (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) with hX
  set N := nrm (A₂.mulVec (hT J A₁ c τ - hO A₁ c τ)) with hN
  have hX0 : 0 ≤ X := nrm_nonneg _
  have hN0 : 0 ≤ N := nrm_nonneg _
  have hα := alphaJ_nonneg J
  have hs2 := sT2_nonneg J A₁ c τ
  have hsT : sT J A₁ c τ ^ 2 = sT2 J A₁ c τ := Real.sq_sqrt hs2
  have hsT0 : 0 ≤ sT J A₁ c τ := Real.sqrt_nonneg _
  have hΔ : |sT J A₁ c τ - sO A₁ c τ| ^ 2 ≤ |sT2 J A₁ c τ - sO2 A₁ c τ| := by
    rw [sq_abs]; exact sqrt_sub_sq_le _ _
  set Δ := |sT J A₁ c τ - sO A₁ c τ| with hΔd
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0
  have hu0 := Real.sqrt_nonneg (m : ℝ)
  have hφ0 : 0 ≤ 1 / √(2 * π) := by positivity
  have hφ : (1 / √(2 * π)) ^ 2 = 1 / (2 * π) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  set φ := 1 / √(2 * π) with hφd
  set p := √(m : ℝ) * (alphaJ J * sT J A₁ c τ) with hp
  set q := √(m : ℝ) * (φ * Δ) with hq
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hXle : X ≤ p + q + N := by rw [hp, hq]; linarith
  have h1 : X ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + N ^ 2) := by
    have : X ^ 2 ≤ (p + q + N) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
    nlinarith [sq_nonneg (p - q), sq_nonneg (q - N), sq_nonneg (p - N)]
  have ep : p ^ 2 = (m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ := by
    rw [hp, mul_pow, mul_pow, hu, hsT]; ring
  have eq' : q ^ 2 ≤ (m : ℝ) / (2 * π) * |sT2 J A₁ c τ - sO2 A₁ c τ| := by
    rw [hq, mul_pow, mul_pow, hu, hφ]
    have : (m : ℝ) * (1 / (2 * π) * Δ ^ 2) = (m : ℝ) / (2 * π) * Δ ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hΔ (by positivity)
  rw [normSq_smul, ← nrm_sq (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ),
    ← nrm_sq (A₂.mulVec (hT J A₁ c τ - hO A₁ c τ)), ← hX, ← hN]
  have e3 : (1 / rhoC c τ) ^ 2 * X ^ 2 = 1 / rhoC c τ ^ 2 * X ^ 2 := by rw [div_pow, one_pow]
  rw [e3]
  have hr0 : 0 ≤ 1 / rhoC c τ ^ 2 := by positivity
  calc 1 / rhoC c τ ^ 2 * X ^ 2 ≤ 1 / rhoC c τ ^ 2 * (3 * (p ^ 2 + q ^ 2 + N ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hr0
    _ ≤ 1 / rhoC c τ ^ 2 * (3 * ((m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ +
          (m : ℝ) / (2 * π) * |sT2 J A₁ c τ - sO2 A₁ c τ| + N ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hr0
        linarith
    _ = _ := by ring

/-! ## The mean over `A₂` -/

lemma int_affine_sq (a s : ℝ) : ∫ z, (a + s * z) ^ 2 ∂gaussianReal 0 1 = a ^ 2 + s ^ 2 := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have h2 : ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [BstLean.Part29.gaussMom_eq 2]
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
  have e2 : (fun z : ℝ => (a + s * z) ^ 2) = fun z => (a ^ 2 + (2 * a * s) * z) + s ^ 2 * z ^ 2 := by
    funext z; ring
  have hl : Integrable (fun z : ℝ => a ^ 2 + (2 * a * s) * z) (gaussianReal 0 1) :=
    (integrable_const _).add (h1.const_mul _)
  have hlv : ∫ z : ℝ, a ^ 2 + (2 * a * s) * z ∂gaussianReal 0 1 = a ^ 2 := by
    rw [integral_add (integrable_const _) (h1.const_mul _), integral_const_mul,
      integral_id_gaussianReal]
    simp
  rw [e2, integral_add hl ((integrable_pow_gauss 2).const_mul _), hlv, integral_const_mul, h2]
  ring

lemma hO_sq_sum_le (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∑ i, hO A₁ c τ i ^ 2 ≤ normSq (A₁.mulVec c) + τ ^ 2 * froSq A₁ := by
  have h : ∀ i, hO A₁ c τ i ^ 2 ≤ mRow A₁ c i ^ 2 + sRow A₁ τ i ^ 2 := by
    intro i
    have h1 := psiS_sq_le (sRow A₁ τ i) (mRow A₁ c i)
    have hd : Integrable (fun z : ℝ => (mRow A₁ c i + sRow A₁ τ i * z) ^ 2) (gaussianReal 0 1) := by
      have := integrable_shift_sq 0
      have h1' : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by
        simpa using integrable_pow_gauss 1
      have hh := ((integrable_const (mRow A₁ c i ^ 2)).add
        (h1'.const_mul (2 * mRow A₁ c i * sRow A₁ τ i))).add
        ((integrable_pow_gauss 2).const_mul (sRow A₁ τ i ^ 2))
      refine hh.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply]; ring
    have h2 : ∫ z, relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 ∂gaussianReal 0 1 ≤
        ∫ z, (mRow A₁ c i + sRow A₁ τ i * z) ^ 2 ∂gaussianReal 0 1 :=
      integral_mono (integrable_relu_shift_sq _ _) hd fun z => relu_sq_le _
    rw [int_affine_sq] at h2
    exact h1.trans h2
  calc ∑ i, hO A₁ c τ i ^ 2 ≤ ∑ i, (mRow A₁ c i ^ 2 + sRow A₁ τ i ^ 2) :=
        Finset.sum_le_sum fun i _ => h i
    _ = normSq (A₁.mulVec c) + τ ^ 2 * froSq A₁ := by
        rw [Finset.sum_add_distrib, sum_sRow_sq]; rfl

/-- The mean over `A₂`, first form. -/
theorem bin_disp_A2_aux (hm : 1 ≤ m) {J : ℕ} (hJ : 1 ≤ J) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ)) ≤
      ENNReal.ofReal (3 / rhoC c τ ^ 2 * ((m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ +
        (m : ℝ) / (2 * π) * |sT2 J A₁ c τ - sO2 A₁ c τ| +
        2 * normSq (hT J A₁ c τ - hO A₁ c τ))) := by
  have hpi := Real.pi_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 := sT2_nonneg J A₁ c τ
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ +
      (m : ℝ) / (2 * π) * |sT2 J A₁ c τ - sO2 A₁ c τ| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨e, he⟩ : ∃ e : Fin m → ℝ, e = hT J A₁ c τ - hO A₁ c τ := ⟨_, rfl⟩
  have hr0 : 0 ≤ 3 / rhoC c τ ^ 2 := by positivity
  obtain ⟨hint, hval⟩ := layer_lin_sq (m := m) (k := m) (v := 2 / (m : ℝ)) (by positivity) e
  have hi2 : Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e))) (gaussMat m m (2 / (m : ℝ))) :=
    ((integrable_const K).add hint).const_mul _
  have hcK : ∫ _A₂ : Matrix (Fin m) (Fin m) ℝ, K ∂gaussMat m m (2 / (m : ℝ)) = K := by simp
  have hm2 : (m : ℝ) * (2 / (m : ℝ) * normSq e) = 2 * normSq e := by field_simp
  have hv2 : ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, 3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e))
      ∂gaussMat m m (2 / (m : ℝ)) = 3 / rhoC c τ ^ 2 * (K + 2 * normSq e) := by
    rw [integral_const_mul, integral_add (integrable_const K) hint, hval, hcK, hm2]
  have hpt : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ,
      normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)) ≤
        3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e)) := by
    intro A₂
    have h := bin_disp_pt hJ A₁ A₂ c τ
    rw [← hK, ← he] at h
    exact h
  rw [← hK, ← he]
  calc ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ))
      ≤ ∫⁻ A₂, ENNReal.ofReal (3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e)))
        ∂gaussMat m m (2 / (m : ℝ)) :=
        lintegral_mono fun A₂ => ENNReal.ofReal_le_ofReal (hpt A₂)
    _ = ENNReal.ofReal (3 / rhoC c τ ^ 2 * (K + 2 * normSq e)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi2
          (Filter.Eventually.of_forall fun A₂ => mul_nonneg hr0
            (add_nonneg hK0 (normSq_nonneg _))), hv2]

/-- The real inequality behind `bin_disp_A2`. -/
lemma bin_real_ineq {mR α β τ F H P S D E ip : ℝ} (hm : 0 < mR) (hα : 0 ≤ α) (hip : 0 ≤ ip)
    (hF0 : 0 ≤ F) (hH0 : 0 ≤ H)
    (hS : S ≤ 2 / mR * (τ ^ 2 * F))
    (hD : D ≤ β * (2 / mR) * τ ^ 2 * F + 2 / mR * (2 * (α * τ * √F) * √H + α ^ 2 * τ ^ 2 * F))
    (hE : E ≤ α ^ 2 * τ ^ 2 * F) (hH : H ≤ P + τ ^ 2 * F) :
    mR * α ^ 2 * S + mR * (ip / 2) * D + 2 * E ≤
      (4 * α ^ 2 + (β + 2 * α + α ^ 2) * ip) * τ ^ 2 * F + α * ip * P := by
  have hm2 : mR * (2 / mR) = 2 := by field_simp
  have hFs : √F ^ 2 = F := Real.sq_sqrt hF0
  have hHs : √H ^ 2 = H := Real.sq_sqrt hH0
  have t1 : mR * α ^ 2 * S ≤ 2 * α ^ 2 * τ ^ 2 * F := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ mR * α ^ 2)
    calc mR * α ^ 2 * S ≤ mR * α ^ 2 * (2 / mR * (τ ^ 2 * F)) := this
      _ = (mR * (2 / mR)) * (α ^ 2 * τ ^ 2 * F) := by ring
      _ = _ := by rw [hm2]; ring
  have am0 : 2 * (τ * √F) * √H ≤ τ ^ 2 * F + H := by
    nlinarith [sq_nonneg (τ * √F - √H)]
  have am : 2 * (α * τ * √F) * √H ≤ α * (τ ^ 2 * F + H) := by
    have := mul_le_mul_of_nonneg_left am0 hα
    calc 2 * (α * τ * √F) * √H = α * (2 * (τ * √F) * √H) := by ring
      _ ≤ _ := this
  have am2 : α * (τ ^ 2 * F + H) ≤ α * (2 * τ ^ 2 * F + P) :=
    mul_le_mul_of_nonneg_left (by linarith) hα
  have t2 : mR * (ip / 2) * D ≤
      ip * (β * τ ^ 2 * F + α * (2 * τ ^ 2 * F + P) + α ^ 2 * τ ^ 2 * F) := by
    have h1 := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ mR * (ip / 2))
    refine h1.trans ?_
    have e1 : mR * (ip / 2) * (β * (2 / mR) * τ ^ 2 * F +
        2 / mR * (2 * (α * τ * √F) * √H + α ^ 2 * τ ^ 2 * F)) =
        (mR * (2 / mR)) * (ip / 2) * (β * τ ^ 2 * F + 2 * (α * τ * √F) * √H +
          α ^ 2 * τ ^ 2 * F) := by ring
    rw [e1, hm2]
    have : 2 * (ip / 2) * (β * τ ^ 2 * F + 2 * (α * τ * √F) * √H + α ^ 2 * τ ^ 2 * F) =
        ip * (β * τ ^ 2 * F + 2 * (α * τ * √F) * √H + α ^ 2 * τ ^ 2 * F) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hip
  have e4 : (4 * α ^ 2 + (β + 2 * α + α ^ 2) * ip) * τ ^ 2 * F + α * ip * P =
      4 * α ^ 2 * τ ^ 2 * F +
        ip * (β * τ ^ 2 * F + α * (2 * τ ^ 2 * F + P) + α ^ 2 * τ ^ 2 * F) := by ring
  rw [e4]
  linarith

/-- The coefficient of `τ²‖A₁‖²_F`. -/
noncomputable def kapF (J : ℕ) : ℝ :=
  4 * alphaJ J ^ 2 + (betaJ J + 2 * alphaJ J + alphaJ J ^ 2) / π

/-- **The mean over `A₂` of the scaled displacement**, for a fixed `A₁`. -/
theorem bin_disp_A2 (hm : 1 ≤ m) {J : ℕ} (hJ : 1 ≤ J) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ)) ≤
      ENNReal.ofReal (3 / rhoC c τ ^ 2 * (kapF J * τ ^ 2 * froSq A₁ +
        alphaJ J / π * normSq (A₁.mulVec c))) := by
  have hpi := Real.pi_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨he, _, _, hsle, hsd⟩ := centre150_first hJ A₁ c hτ
  have hHle := hO_sq_sum_le A₁ c τ
  have hen : normSq (hT J A₁ c τ - hO A₁ c τ) ≤ alphaJ J ^ 2 * τ ^ 2 * froSq A₁ := he
  have hr := bin_real_ineq (ip := 1 / π) hmR (alphaJ_nonneg J) (by positivity)
    (froSq_nonneg A₁) (Finset.sum_nonneg fun i _ => sq_nonneg (hO A₁ c τ i)) hsle hsd hen hHle
  refine (bin_disp_A2_aux hm hJ A₁ c τ).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : (m : ℝ) / (2 * π) = (m : ℝ) * (1 / π / 2) := by ring
  have e2 : kapF J * τ ^ 2 * froSq A₁ + alphaJ J / π * normSq (A₁.mulVec c) =
      (4 * alphaJ J ^ 2 + (betaJ J + 2 * alphaJ J + alphaJ J ^ 2) * (1 / π)) * τ ^ 2 * froSq A₁ +
        alphaJ J * (1 / π) * normSq (A₁.mulVec c) := by
    unfold kapF; ring
  rw [e1, e2]
  exact hr

/-! ## The mean over `A₁` -/

lemma froSq_integral (hn : 1 ≤ n) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => froSq A₁) (gaussMat m n (2 / (n : ℝ))) ∧
    ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, froSq A₁ ∂gaussMat m n (2 / (n : ℝ)) = 2 * m := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, froSq A₁ =
      ∑ j : Fin n, normSq (A₁.mulVec (Pi.single j 1)) := by
    intro A₁
    unfold froSq normSq
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_single_one]
    rfl
  have hl := fun j : Fin n => layer_lin_sq (m := m) (k := n) (v := 2 / (n : ℝ)) (by positivity)
    (Pi.single j 1)
  have hs : ∀ j : Fin n, normSq (Pi.single j (1 : ℝ) : Fin n → ℝ) = 1 := by
    intro j
    unfold normSq
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  simp_rw [e]
  refine ⟨integrable_finsetSum _ fun j _ => (hl j).1, ?_⟩
  rw [integral_finsetSum _ fun j _ => (hl j).1]
  simp_rw [(hl _).2, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The constant of the binomial displacement. -/
noncomputable def xiBin (J : ℕ) : ℝ :=
  3 * (8 * alphaJ J ^ 2 + (2 * betaJ J + 4 * alphaJ J + 2 * alphaJ J ^ 2) / π)

lemma xiBin_nonneg (J : ℕ) : 0 ≤ xiBin J := by
  have := alphaJ_nonneg J
  have := betaJ_nonneg J
  unfold xiBin; positivity

/-- **The mean over `A₁` and `A₂` of the scaled displacement of the binomial centre from the
paper's oracle centre**: at most `(m/n)·xiBin J`. -/
theorem bin_disp_mean (hn : 1 ≤ n) (hm : 1 ≤ m) {J : ℕ} (hJ : 1 ≤ J) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) :
    ∫⁻ A₁, ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ)) ∂gaussMat m n (2 / (n : ℝ)) ≤
      ENNReal.ofReal ((m : ℝ) / n * xiBin J) := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hα := alphaJ_nonneg J
  have hβ := betaJ_nonneg J
  have hρ := rhoC_pos hn c hτ
  have hρ2 := rhoC_sq c τ
  have hc0 := normSq_nonneg c
  have hk0 : 0 ≤ kapF J := by unfold kapF; positivity
  obtain ⟨hFi, hFv⟩ := froSq_integral (m := m) hn
  obtain ⟨hPi, hPv⟩ := layer_lin_sq (m := m) (k := n) (v := 2 / (n : ℝ)) (by positivity) c
  have hr0 : 0 ≤ 3 / rhoC c τ ^ 2 := by positivity
  have hi : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      3 / rhoC c τ ^ 2 * (kapF J * τ ^ 2 * froSq A₁ + alphaJ J / π * normSq (A₁.mulVec c)))
      (gaussMat m n (2 / (n : ℝ))) :=
    ((hFi.const_mul _).add (hPi.const_mul _)).const_mul _
  have hv : ∫ A₁ : Matrix (Fin m) (Fin n) ℝ,
      3 / rhoC c τ ^ 2 * (kapF J * τ ^ 2 * froSq A₁ + alphaJ J / π * normSq (A₁.mulVec c))
      ∂gaussMat m n (2 / (n : ℝ)) =
      3 / rhoC c τ ^ 2 * (kapF J * τ ^ 2 * (2 * m) +
        alphaJ J / π * ((m : ℝ) * (2 / (n : ℝ) * normSq c))) := by
    rw [integral_const_mul, integral_add (hFi.const_mul _) (hPi.const_mul _), integral_const_mul,
      integral_const_mul, hFv, hPv]
  calc ∫⁻ A₁, ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ)) ∂gaussMat m n (2 / (n : ℝ))
      ≤ ∫⁻ A₁, ENNReal.ofReal (3 / rhoC c τ ^ 2 * (kapF J * τ ^ 2 * froSq A₁ +
          alphaJ J / π * normSq (A₁.mulVec c))) ∂gaussMat m n (2 / (n : ℝ)) :=
        lintegral_mono fun A₁ => bin_disp_A2 hm hJ A₁ c hτ.le
    _ = ENNReal.ofReal (3 / rhoC c τ ^ 2 * (kapF J * τ ^ 2 * (2 * m) +
          alphaJ J / π * ((m : ℝ) * (2 / (n : ℝ) * normSq c)))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun A₁ => mul_nonneg hr0
            (add_nonneg (mul_nonneg (mul_nonneg hk0 (sq_nonneg _)) (froSq_nonneg A₁))
              (mul_nonneg (by positivity) (normSq_nonneg _)))), hv]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hρ 2), hρ2]
        set a := alphaJ J / π with ha
        have ha0 : 0 ≤ a := by positivity
        set κ' := 4 * alphaJ J ^ 2 + (betaJ J + alphaJ J ^ 2) / π with hκ'
        have hκ0 : 0 ≤ κ' := by positivity
        have ek : kapF J = κ' + 2 * a := by unfold kapF; rw [hκ', ha]; field_simp; ring
        have ex : xiBin J = 3 * (2 * κ' + 4 * a) := by
          unfold xiBin; rw [hκ', ha]; field_simp; ring
        rw [ek, ex]
        set d := (m : ℝ) / n with hd
        have hd0 : 0 ≤ d := by positivity
        have em : (m : ℝ) = d * n := by rw [hd]; field_simp
        rw [em]
        set T := (n : ℝ) * τ ^ 2 with hT
        have hT0 : 0 ≤ T := by positivity
        set C := normSq c with hC
        have e1 : 3 * ((κ' + 2 * a) * τ ^ 2 * (2 * (d * n)) +
            a * (d * n * (2 / (n : ℝ) * C))) = 3 * d * (2 * κ' * T + a * (4 * T + 2 * C)) := by
          rw [hT]; field_simp; ring
        rw [e1]
        have : d * (3 * (2 * κ' + 4 * a)) * (C + T) - 3 * d * (2 * κ' * T + a * (4 * T + 2 * C)) =
            3 * d * (2 * κ' * C + 2 * a * C) := by ring
        have h0 : 0 ≤ 3 * d * (2 * κ' * C + 2 * a * C) := by positivity
        linarith

end BstLean.Part150

open BstLean.Part150 in
#print axioms measurable_bT
open BstLean.Part150 in
#print axioms measurable_bO
open BstLean.Part150 in
#print axioms measurable_rhoC
open BstLean.Part150 in
#print axioms measurable_binDispX
open BstLean.Part150 in
#print axioms measurable_binDisp
open BstLean.Part150 in
#print axioms bin_disp_pt
open BstLean.Part150 in
#print axioms bin_disp_A2_aux
open BstLean.Part150 in
#print axioms bin_disp_A2
open BstLean.Part150 in
#print axioms bin_disp_mean
