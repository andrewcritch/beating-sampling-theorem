import BstLean.Part153PP
import BstLean.Part153Energy
import BstLean.Part152GC
import BstLean.Part131Integrable

/-!
# Part 177 (file `EnMom`): the energy moment of the second hidden layer

No proof is left open; no `native_decide` or `axiom` is used.

* `gaussConc_mat_mgf`: the sharp mgf bound `E exp(λ(g − E g)) ≤ exp(λ²vL²/2)` for a
  Frobenius-Lipschitz function of a Gaussian matrix (Part 152 transported to `gaussMat`).
* `mom_of_lip`: `E g^p ≤ M^p·exp(p²vL²/(2M²))` for `g ≥ 0` Lipschitz with `E g ≤ M`.
* `layer_mom`: `E|ReLU(M y)|^{2q} ≤ ((m/2)v|y|²)^q·exp(4q²/m)`.
* **`hid2_mom`**: `E_{nuA n} (|h₂(x)|²/n)^q ≤ |x|^{2q}·exp(8q²/n²)`; `hid2_mom_unit` for `|x| ≤ 1`.
-/

namespace BstLean.Part177

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open Matrix
open BstLean.Part153 (nuA)

section mgf
variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

/-- The sharp mgf bound for a Frobenius-Lipschitz function of a Gaussian matrix. -/
theorem gaussConc_mat_mgf (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) (lam : ℝ) :
    Integrable g (gaussMat m k v) ∧ Integrable (fun M => Real.exp (lam * g M)) (gaussMat m k v) ∧
    ∫ M, Real.exp (lam * (g M - ∫ M, g M ∂gaussMat m k v)) ∂gaussMat m k v ≤
      Real.exp (lam ^ 2 * (v * L ^ 2) / 2) := by
  have hgc := BstLean.Part148.matLip_continuous hL
  set T : (Fin m × Fin k → ℝ) → Matrix (Fin m) (Fin k) ℝ :=
    fun ξ => Matrix.of fun i j => Real.sqrt v * ξ (i, j) with hT
  have mT : Measurable T := measurable_ofFlat _
  have hf : BstLean.Part148.EuLip (fun ξ => g (T ξ)) (√v * L) := BstLean.Part152.flat_euLip hL hv
  obtain ⟨i1, i2, h⟩ := BstLean.Part152.gaussConc_mgf_sharp
    (mul_nonneg (Real.sqrt_nonneg v) hL0) hf lam
  have hG : gaussMat m k v = (stdGauss (Fin m × Fin k)).map T := rfl
  have eI : ∫ M, g M ∂gaussMat m k v = ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k) := by
    rw [hG]; exact integral_map mT.aemeasurable hgc.measurable.aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · rw [hG]; exact (integrable_map_measure hgc.aestronglyMeasurable mT.aemeasurable).2 i1
  · rw [hG]
    exact (integrable_map_measure (by fun_prop) mT.aemeasurable).2 i2
  · rw [eI]
    have e2 : ∫ M, Real.exp (lam * (g M - ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k))) ∂gaussMat m k v
        = ∫ ξ, Real.exp (lam * (g (T ξ) - ∫ ξ, g (T ξ) ∂stdGauss (Fin m × Fin k)))
          ∂stdGauss (Fin m × Fin k) := by
      rw [hG]; exact integral_map mT.aemeasurable (by fun_prop)
    rw [e2]
    refine h.trans (le_of_eq ?_)
    rw [mul_pow, Real.sq_sqrt hv]

end mgf

/-- `y^p ≤ M^p·exp(p·y/M − p)` for `y ≥ 0`, `M > 0`. -/
lemma pow_le_exp {y M : ℝ} (hy : 0 ≤ y) (hM : 0 < M) (p : ℕ) :
    y ^ p ≤ M ^ p * Real.exp (p * y / M - p) := by
  have h1 : y / M ≤ Real.exp (y / M - 1) := by
    have := Real.add_one_le_exp (y / M - 1); linarith
  have h2 : (y / M) ^ p ≤ Real.exp (y / M - 1) ^ p :=
    pow_le_pow_left₀ (div_nonneg hy hM.le) h1 p
  rw [← Real.exp_nat_mul] at h2
  have e : (p : ℝ) * (y / M - 1) = p * y / M - p := by ring
  rw [e, div_pow] at h2
  rwa [div_le_iff₀ (by positivity), mul_comm] at h2


section mom
variable {m k : ℕ} {g : Matrix (Fin m) (Fin k) ℝ → ℝ} {L : ℝ}

/-- **Moments of a nonnegative Lipschitz function of a Gaussian matrix from its mean bound**:
`E g^p ≤ M^p·exp(p²·vL²/(2M²))` if `E g ≤ M`, `M > 0`. -/
theorem mom_of_lip (hL0 : 0 ≤ L)
    (hL : ∀ M M' : Matrix (Fin m) (Fin k) ℝ,
      |g M - g M'| ≤ L * √(∑ i, ∑ j, (M i j - M' i j) ^ 2))
    {v : ℝ} (hv : 0 ≤ v) (h0 : ∀ M, 0 ≤ g M) {Mb : ℝ} (hMb : 0 < Mb)
    (hmean : ∫ M, g M ∂gaussMat m k v ≤ Mb) (p : ℕ) :
    Integrable (fun M => g M ^ p) (gaussMat m k v) ∧
    ∫ M, g M ^ p ∂gaussMat m k v ≤ Mb ^ p * Real.exp ((p : ℝ) ^ 2 * (v * L ^ 2) / (2 * Mb ^ 2)) := by
  have hgc := BstLean.Part148.matLip_continuous hL
  set lam : ℝ := p / Mb with hlam
  have hl0 : 0 ≤ lam := by positivity
  obtain ⟨i1, i2, h⟩ := gaussConc_mat_mgf hL0 hL hv lam
  set μ := ∫ M, g M ∂gaussMat m k v with hμ
  have hpt : ∀ M, g M ^ p ≤ Mb ^ p * Real.exp (-p) * Real.exp (lam * g M) := fun M => by
    have := pow_le_exp (h0 M) hMb p
    rw [mul_assoc, ← Real.exp_add]
    refine this.trans (le_of_eq ?_)
    congr 2; rw [hlam]; ring
  have iP : Integrable (fun M => g M ^ p) (gaussMat m k v) :=
    Integrable.mono' (i2.const_mul _) (hgc.measurable.pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => by
        rw [Real.norm_of_nonneg (pow_nonneg (h0 M) p)]; exact hpt M)
  refine ⟨iP, ?_⟩
  have e : ∫ M, Real.exp (lam * g M) ∂gaussMat m k v =
      Real.exp (lam * μ) * ∫ M, Real.exp (lam * (g M - μ)) ∂gaussMat m k v := by
    rw [← integral_const_mul]
    congr 1; funext M; rw [← Real.exp_add]; congr 1; ring
  have hE : ∫ M, Real.exp (lam * g M) ∂gaussMat m k v ≤
      Real.exp (lam * Mb) * Real.exp (lam ^ 2 * (v * L ^ 2) / 2) := by
    rw [e]
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hmean hl0)) h
      (integral_nonneg fun _ => (Real.exp_pos _).le) (Real.exp_pos _).le
  calc ∫ M, g M ^ p ∂gaussMat m k v
      ≤ ∫ M, Mb ^ p * Real.exp (-p) * Real.exp (lam * g M) ∂gaussMat m k v :=
        integral_mono iP (i2.const_mul _) hpt
    _ = Mb ^ p * Real.exp (-p) * ∫ M, Real.exp (lam * g M) ∂gaussMat m k v :=
        integral_const_mul _ _
    _ ≤ Mb ^ p * Real.exp (-p) * (Real.exp (lam * Mb) * Real.exp (lam ^ 2 * (v * L ^ 2) / 2)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = Mb ^ p * Real.exp ((p : ℝ) ^ 2 * (v * L ^ 2) / (2 * Mb ^ 2)) := by
        rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [hlam]; field_simp; ring

end mom


section layer
variable {m k : ℕ}

lemma layer_lip (y : Fin k → ℝ) (M M' : Matrix (Fin m) (Fin k) ℝ) :
    |√(normSq (reluV (M *ᵥ y))) - √(normSq (reluV (M' *ᵥ y)))| ≤
      √(normSq y) * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
  have h1 := BstLean.Part153.abs_nrm_sub_le (reluV (M *ᵥ y)) (reluV (M' *ᵥ y))
  have h2 := BstLean.Part153.nrm_reluV_sub_le (M *ᵥ y) (M' *ᵥ y)
  have h3 := BstLean.Part131.normSq_mulVec_le (M - M') y
  rw [Matrix.sub_mulVec] at h3
  have e : BstLean.Part131.frob (M - M') = ∑ i, ∑ j, (M i j - M' i j) ^ 2 := by
    unfold BstLean.Part131.frob; simp [Matrix.sub_apply]
  rw [e] at h3
  have h4 : BstLean.Part153.nrm (M *ᵥ y - M' *ᵥ y) ≤
      √(normSq y) * √(∑ i, ∑ j, (M i j - M' i j) ^ 2) := by
    unfold BstLean.Part153.nrm
    rw [← Real.sqrt_mul (normSq_nonneg y)]
    exact Real.sqrt_le_sqrt (h3.trans (le_of_eq (mul_comm _ _)))
  exact h1.trans (h2.trans h4)

/-- **The moments of one ReLU layer**: `E|ReLU(M y)|^{2q} ≤ ((m/2)v|y|²)^q·exp(4q²/m)`. -/
theorem layer_mom (hm : 1 ≤ m) (y : Fin k → ℝ) {v : ℝ} (hv : 0 < v) (q : ℕ) :
    Integrable (fun M => normSq (reluV (M *ᵥ y)) ^ q) (gaussMat m k v) ∧
    ∫ M, normSq (reluV (M *ᵥ y)) ^ q ∂gaussMat m k v ≤
      ((m : ℝ) / 2 * (v * normSq y)) ^ q * Real.exp (4 * (q : ℝ) ^ 2 / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set g : Matrix (Fin m) (Fin k) ℝ → ℝ := fun M => √(normSq (reluV (M *ᵥ y))) with hg
  have hgL := layer_lip (m := m) y
  have hgc := BstLean.Part148.matLip_continuous hgL
  have hg2 : ∀ M, g M ^ 2 = normSq (reluV (M *ᵥ y)) := fun M => Real.sq_sqrt (normSq_nonneg _)
  rcases eq_or_lt_of_le (normSq_nonneg y) with hy | hy
  · -- `y = 0`: the integrand is `0^q`
    have hz : ∀ M : Matrix (Fin m) (Fin k) ℝ, normSq (reluV (M *ᵥ y)) = 0 := fun M => by
      have a := BstLean.Part153.normSq_reluV_le (M *ᵥ y)
      have b := BstLean.Part131.normSq_mulVec_le M y
      rw [← hy, mul_zero] at b
      exact le_antisymm (a.trans b) (normSq_nonneg _)
    simp_rw [hz]
    refine ⟨integrable_const _, ?_⟩
    rw [integral_const, probReal_univ, one_smul, ← hy]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simp
    · rw [zero_pow hq.ne', mul_zero, mul_zero, zero_pow hq.ne', zero_mul]
  · obtain ⟨iS, eS⟩ := layer_relu_sq (m := m) hv.le y
    obtain ⟨ig, -, -⟩ := gaussConc_mat_mgf (Real.sqrt_nonneg _) hgL hv.le 0
    set Mb : ℝ := √((m : ℝ) / 2 * (v * normSq y)) with hMb
    have hMb0 : 0 < Mb := Real.sqrt_pos.2 (by positivity)
    have hJ : (∫ M, g M ∂gaussMat m k v) ^ 2 ≤ ∫ M, g M ^ 2 ∂gaussMat m k v := by
      have i2 : Integrable (fun M => g M ^ 2) (gaussMat m k v) := by simp_rw [hg2]; exact iS
      exact (convexOn_pow 2).map_integral_le (μ := gaussMat m k v) (f := g)
        (continuous_pow 2).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun M => Set.mem_Ici.mpr (Real.sqrt_nonneg _)) ig i2
    have hmean : ∫ M, g M ∂gaussMat m k v ≤ Mb := by
      simp_rw [hg2] at hJ
      rw [eS] at hJ
      rw [hMb]
      exact Real.le_sqrt_of_sq_le hJ
    obtain ⟨iP, hP⟩ := mom_of_lip (Real.sqrt_nonneg _) hgL hv.le (fun M => Real.sqrt_nonneg _)
      hMb0 hmean (2 * q)
    have e1 : (fun M => g M ^ (2 * q)) = fun M => normSq (reluV (M *ᵥ y)) ^ q := funext fun M => by
      rw [pow_mul, hg2]
    rw [e1] at iP
    have e2 : ∫ M, g M ^ (2 * q) ∂gaussMat m k v = ∫ M, normSq (reluV (M *ᵥ y)) ^ q ∂gaussMat m k v := by
      rw [e1]
    rw [e2] at hP
    refine ⟨iP, hP.trans (le_of_eq ?_)⟩
    have hMb2 : Mb ^ 2 = (m : ℝ) / 2 * (v * normSq y) := Real.sq_sqrt (by positivity)
    rw [pow_mul, hMb2]
    congr 2
    rw [Real.sq_sqrt (normSq_nonneg y)]
    push_cast
    field_simp
    ring

end layer


section hid2
variable {n : ℕ}

lemma continuous_hid2_joint (x : Fin n → ℝ) :
    Continuous (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      normSq (hid2 θ.1 θ.2 x)) := by
  show Continuous (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      normSq (reluV (θ.2 *ᵥ reluV (θ.1 *ᵥ x))))
  exact continuous_normSq.comp (continuous_reluV.comp (Continuous.matrix_mulVec continuous_snd
    (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const))))

/-- **The energy moment of the second hidden layer** at a fixed input `x`:
`E_{(A₁,A₂)} |h₂(x)|^{2q} ≤ (n|x|²)^q·exp(8q²/n²)`. -/
theorem hid2_mom_raw (hn : 1 ≤ n) (x : Fin n → ℝ) (q : ℕ) :
    Integrable (fun θ => normSq (hid2 θ.1 θ.2 x) ^ q) (nuA n) ∧
    ∫ θ, normSq (hid2 θ.1 θ.2 x) ^ q ∂(nuA n) ≤
      ((n : ℝ) * normSq x) ^ q * Real.exp (8 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hm1 : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ hn
  set μ₁ := gaussMat (mA n) n (2 / (n : ℝ))
  set μ₂ := gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))
  set F : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ :=
    fun θ => normSq (hid2 θ.1 θ.2 x) ^ q with hF
  have hFc : Continuous F := (continuous_hid2_joint x).pow q
  have hF0 : ∀ θ, 0 ≤ F θ := fun θ => pow_nonneg (normSq_nonneg _) q
  set e : ℝ := Real.exp (4 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  -- the inner (second-layer) bound
  have hin : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      Integrable (fun A₂ => F (A₁, A₂)) μ₂ ∧
      ∫ A₂, F (A₁, A₂) ∂μ₂ ≤ e * normSq (reluV (A₁ *ᵥ x)) ^ q := by
    intro A₁
    obtain ⟨i, h⟩ := layer_mom (m := mA n) hm1 (reluV (A₁ *ᵥ x))
      (v := 2 / ((mA n : ℕ) : ℝ)) (by positivity) q
    refine ⟨i, h.trans (le_of_eq ?_)⟩
    rw [he, hmA]
    have : ((n : ℝ) ^ 2) / 2 * (2 / (n : ℝ) ^ 2 * normSq (reluV (A₁ *ᵥ x))) =
        normSq (reluV (A₁ *ᵥ x)) := by field_simp
    rw [this]; ring
  obtain ⟨i1, h1⟩ := layer_mom (m := mA n) hm1 x (v := 2 / (n : ℝ)) (by positivity) q
  have h1' : ∫ A₁, normSq (reluV (A₁ *ᵥ x)) ^ q ∂μ₁ ≤ ((n : ℝ) * normSq x) ^ q * e := by
    refine h1.trans (le_of_eq ?_)
    rw [he, hmA]
    congr 2; field_simp
  -- lintegral form
  have hL : ∫⁻ θ, ENNReal.ofReal (F θ) ∂(nuA n) ≤
      ENNReal.ofReal (e * (((n : ℝ) * normSq x) ^ q * e)) := by
    change ∫⁻ θ, ENNReal.ofReal (F θ) ∂(μ₁.prod μ₂) ≤ _
    rw [lintegral_prod _ hFc.measurable.ennreal_ofReal.aemeasurable]
    calc ∫⁻ A₁, ∫⁻ A₂, ENNReal.ofReal (F (A₁, A₂)) ∂μ₂ ∂μ₁
        ≤ ∫⁻ A₁, ENNReal.ofReal (e * normSq (reluV (A₁ *ᵥ x)) ^ q) ∂μ₁ := by
          refine lintegral_mono fun A₁ => ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hin A₁).1
            (Filter.Eventually.of_forall fun A₂ => hF0 _)]
          exact ENNReal.ofReal_le_ofReal (hin A₁).2
      _ = ENNReal.ofReal (∫ A₁, e * normSq (reluV (A₁ *ᵥ x)) ^ q ∂μ₁) := by
          rw [ofReal_integral_eq_lintegral_ofReal (i1.const_mul e)
            (Filter.Eventually.of_forall fun A₁ => mul_nonneg he0 (pow_nonneg (normSq_nonneg _) q))]
      _ ≤ _ := by
          rw [integral_const_mul]
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1' he0)
  have hI : Integrable F (nuA n) := by
    refine ⟨hFc.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hF0)]
    exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0)
    hFc.measurable.aestronglyMeasurable]
  refine (ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg he0 (mul_nonneg (pow_nonneg (mul_nonneg hn0.le (normSq_nonneg x)) q) he0)) hL).trans (le_of_eq ?_)
  rw [he, mul_comm, mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- **The energy moment** `E (|h₂(x)|²/n)^q ≤ |x|^{2q}·exp(8q²/n²)` over `(A₁, A₂) ∼ nuA n`. -/
theorem hid2_mom (hn : 1 ≤ n) (x : Fin n → ℝ) (q : ℕ) :
    Integrable (fun θ => (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q) (nuA n) ∧
    ∫ θ, (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q ∂(nuA n) ≤
      normSq x ^ q * Real.exp (8 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨i, h⟩ := hid2_mom_raw hn x q
  have e : (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q) =
      fun θ => normSq (hid2 θ.1 θ.2 x) ^ q * ((n : ℝ) ^ q)⁻¹ := by
    funext θ; rw [div_pow, div_eq_mul_inv]
  rw [e]
  refine ⟨i.mul_const _, ?_⟩
  rw [integral_mul_const]
  calc (∫ θ, normSq (hid2 θ.1 θ.2 x) ^ q ∂(nuA n)) * ((n : ℝ) ^ q)⁻¹
      ≤ ((n : ℝ) * normSq x) ^ q * Real.exp (8 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2) * ((n : ℝ) ^ q)⁻¹ :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [mul_pow]; field_simp

/-- The energy moment at a point of the closed unit ball: `E (|h₂(x)|²/n)^q ≤ exp(8q²/n²)`. -/
theorem hid2_mom_unit (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : normSq x ≤ 1) (q : ℕ) :
    Integrable (fun θ => (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q) (nuA n) ∧
    ∫ θ, (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q ∂(nuA n) ≤
      Real.exp (8 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  obtain ⟨i, h⟩ := hid2_mom hn x q
  refine ⟨i, h.trans ?_⟩
  have : normSq x ^ q ≤ 1 := pow_le_one₀ (normSq_nonneg x) hx
  nlinarith [Real.exp_pos (8 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2)]

end hid2

end BstLean.Part177
