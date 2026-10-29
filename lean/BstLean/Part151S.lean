import BstLean.Part151Poinc2

/-!
# Part 151: Lemma S, the Poincaré inequality across the point `y = 0`

Role: Lemma S of `proofs/option-n/theorem5-04-standin-structure.tex`. `Υ` is bounded and is
Lipschitz away from the origin (not near it: `Υ(y) = φ(q(y/|y|))` in the paper). With
`y = c + τξ`, `ξ` a standard Gaussian vector of `ℝⁿ`, `n ≥ 3`:
`Var Υ(y) ≤ τ²·E Γ(y)` for every `Γ ≥ |∇Υ|²` almost everywhere.

* `gradSq_le_pt`: a function with `|h z − h x| ≤ C|z − x|` for all `z`, differentiable at `x`,
  has `|∇h(x)|² ≤ C²`.
* `cutV ρ ε x = min(1, max(0, ρ(x)/ε − 1))`: the cut-off function.
* `lemmaS_core`: the abstract form, with a Lipschitz "radius" `ρ` and the hypothesis
  `Pr(ρ ≤ 2ε)/ε² → 0`.
* `ball_prob_le`: `Pr(|c + τξ| ≤ r) ≤ (2r/τ)³` for `n ≥ 3`.
* **`lemmaS`**: Lemma S.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part132 (nrm)
open BstLean.Part148 (EuLip en en_nonneg en_smul)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The gradient of a function with a pointwise Lipschitz bound -/

/-- If `|h z − h x| ≤ C·|z − x|` for every `z` and `h` is differentiable at `x`, then
`|∇h(x)|² ≤ C²`. -/
lemma gradSq_le_pt {h : (ι → ℝ) → ℝ} {x : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : DifferentiableAt ℝ h x)
    (hb : ∀ z, |h z - h x| ≤ C * √(∑ i, (z i - x i) ^ 2)) : gradSq h x ≤ C ^ 2 := by
  set g : ι → ℝ := fun i => fderiv ℝ h x (Pi.single i 1) with hg
  have hlin : ∀ w : ι → ℝ, fderiv ℝ h x w = w ⬝ᵥ g := by
    intro w
    have h' := (fderiv ℝ h x).toLinearMap.pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h'
    rw [h']
    simp only [dotProduct, hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hdd : HasDerivAt (fun t : ℝ => h (x + t • g)) (fderiv ℝ h x g) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • g) g 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add x
      simpa using this
    have h2 : HasFDerivAt h (fderiv ℝ h x) (x + (0 : ℝ) • g) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have ht := hdd.tendsto_slope_zero_right
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (h (x + (0 + t) • g) - h (x + (0 : ℝ) • g)) ≤
      C * en g := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have ht0' : (0 : ℝ) < t := ht0
    have h' := hb (x + t • g)
    have e : √(∑ i, ((x + t • g) i - x i) ^ 2) = t * en g := by
      have : (fun i => ((x + t • g) i - x i) ^ 2) = fun i => (t • g) i ^ 2 := by
        funext i; simp
      rw [this]
      have := en_smul t g
      unfold en at this ⊢
      rw [this, abs_of_pos ht0']
    rw [e] at h'
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    have h3 : h (x + t • g) - h x ≤ C * (t * en g) := (le_abs_self _).trans h'
    rw [inv_mul_le_iff₀ ht0']
    linarith
  have hle : fderiv ℝ h x g ≤ C * en g := le_of_tendsto ht hbound
  rw [hlin g] at hle
  have hgg : g ⬝ᵥ g = en g ^ 2 := by
    unfold en
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hgg] at hle
  have hen := en_nonneg g
  have hlt : en g ≤ C := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have e2 : gradSq h x = en g ^ 2 := by
    rw [← hgg]
    unfold gradSq
    simp only [dotProduct, hg]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  exact pow_le_pow_left₀ hen hlt 2

/-! ## The cut-off function -/

/-- `χ_ε = min(1, max(0, ρ/ε − 1))`: `0` where `ρ ≤ ε`, `1` where `ρ ≥ 2ε`. -/
noncomputable def cutV (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ := min 1 (max 0 (ρ x / ε - 1))

omit [Fintype ι] [DecidableEq ι] in
lemma cutV_nonneg (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (x : ι → ℝ) : 0 ≤ cutV ρ ε x :=
  le_min zero_le_one (le_max_left _ _)

omit [Fintype ι] [DecidableEq ι] in
lemma cutV_le_one (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (x : ι → ℝ) : cutV ρ ε x ≤ 1 := min_le_left _ _

omit [Fintype ι] [DecidableEq ι] in
lemma cutV_zero {ρ : (ι → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε) {x : ι → ℝ} (h : ρ x ≤ ε) :
    cutV ρ ε x = 0 := by
  unfold cutV
  have : ρ x / ε - 1 ≤ 0 := by
    have := (div_le_one hε).mpr h
    linarith
  rw [max_eq_left this]
  exact min_eq_right zero_le_one

omit [Fintype ι] [DecidableEq ι] in
lemma cutV_one {ρ : (ι → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε) {x : ι → ℝ} (h : 2 * ε ≤ ρ x) :
    cutV ρ ε x = 1 := by
  unfold cutV
  have : 1 ≤ ρ x / ε - 1 := by
    have : 2 ≤ ρ x / ε := by rw [le_div_iff₀ hε]; exact h
    linarith
  rw [max_eq_right (le_trans zero_le_one this)]
  exact min_eq_left this

lemma clamp_lip (a b : ℝ) : |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  have h1 := abs_min_sub_min_le_max 1 (max 0 a) 1 (max 0 b)
  have h2 := abs_max_sub_max_le_abs a b 0
  rw [max_comm a 0, max_comm b 0] at h2
  simp only [sub_self, abs_zero] at h1
  exact h1.trans (max_le (abs_nonneg _) h2)

omit [DecidableEq ι] in
lemma cutV_lip {ρ : (ι → ℝ) → ℝ} {K : ℝ} (hρ : EuLip ρ K) {ε : ℝ} (hε : 0 < ε) (x x' : ι → ℝ) :
    |cutV ρ ε x - cutV ρ ε x'| ≤ K / ε * √(∑ i, (x i - x' i) ^ 2) := by
  unfold cutV
  refine (clamp_lip _ _).trans ?_
  have e : ρ x / ε - 1 - (ρ x' / ε - 1) = (ρ x - ρ x') / ε := by ring
  rw [e, abs_div, abs_of_pos hε, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (hρ x x') hε.le

/-- `Υ_ε = U·χ_ε`. -/
noncomputable def cutF (U ρ : (ι → ℝ) → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ := U x * cutV ρ ε x

section core

variable {ρ U G : (ι → ℝ) → ℝ} {K Bd : ℝ}

omit [DecidableEq ι] in
/-- The cut-off function `Υ_ε` is globally Lipschitz. -/
lemma cutF_lip (hK : 0 ≤ K) (hρ : EuLip ρ K) (hUb : ∀ x, |U x| ≤ Bd) {ε L : ℝ} (hε : 0 < ε)
    (hL0 : 0 ≤ L)
    (hL : ∀ x x', ε ≤ ρ x → ε ≤ ρ x' → |U x - U x'| ≤ L * √(∑ i, (x i - x' i) ^ 2)) :
    EuLip (cutF U ρ ε) (L + Bd * (K / ε)) := by
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hUb 0)
  intro x x'
  set D := √(∑ i, (x i - x' i) ^ 2) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hV := cutV_lip hρ hε x x'
  rw [← hD] at hV
  have hKe : 0 ≤ K / ε := div_nonneg hK hε.le
  unfold cutF
  by_cases h1 : ε ≤ ρ x
  · by_cases h2 : ε ≤ ρ x'
    · have e : U x * cutV ρ ε x - U x' * cutV ρ ε x' =
          (U x - U x') * cutV ρ ε x + U x' * (cutV ρ ε x - cutV ρ ε x') := by ring
      rw [e]
      have a1 : |(U x - U x') * cutV ρ ε x| ≤ L * D := by
        rw [abs_mul, abs_of_nonneg (cutV_nonneg ρ ε x)]
        calc |U x - U x'| * cutV ρ ε x ≤ |U x - U x'| * 1 :=
              mul_le_mul_of_nonneg_left (cutV_le_one ρ ε x) (abs_nonneg _)
          _ ≤ L * D := by rw [mul_one]; exact hL x x' h1 h2
      have a2 : |U x' * (cutV ρ ε x - cutV ρ ε x')| ≤ Bd * (K / ε * D) := by
        rw [abs_mul]
        exact mul_le_mul (hUb x') hV (abs_nonneg _) hBd
      have := abs_add_le ((U x - U x') * cutV ρ ε x) (U x' * (cutV ρ ε x - cutV ρ ε x'))
      nlinarith
    · have hz := cutV_zero hε (not_le.mp h2).le
      rw [hz, mul_zero, sub_zero]
      have a2 : |U x * cutV ρ ε x| ≤ Bd * (K / ε * D) := by
        rw [abs_mul]
        have : |cutV ρ ε x| ≤ K / ε * D := by rw [hz] at hV; simpa using hV
        exact mul_le_mul (hUb x) this (abs_nonneg _) hBd
      have : 0 ≤ L * D := mul_nonneg hL0 hD0
      nlinarith
  · have hz := cutV_zero hε (not_le.mp h1).le
    rw [hz, mul_zero, zero_sub, abs_neg]
    have a2 : |U x' * cutV ρ ε x'| ≤ Bd * (K / ε * D) := by
      rw [abs_mul]
      have : |cutV ρ ε x'| ≤ K / ε * D := by
        rw [hz, zero_sub, abs_neg] at hV; exact hV
      exact mul_le_mul (hUb x') this (abs_nonneg _) hBd
    have : 0 ≤ L * D := mul_nonneg hL0 hD0
    nlinarith

lemma gradSq_congr_nhds {f g : (ι → ℝ) → ℝ} {x : ι → ℝ} (h : f =ᶠ[𝓝 x] g) :
    gradSq f x = gradSq g x := by
  unfold gradSq
  rw [h.fderiv_eq]

/-- The gradient of the cut-off function, at a point where `|∇U|² ≤ G` and where
`Υ_{ε/2}` is differentiable. -/
lemma gradSq_cutF (hK : 0 ≤ K) (hρ : EuLip ρ K) (hUb : ∀ x, |U x| ≤ Bd) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {x : ι → ℝ} (hGx : gradSq U x ≤ G x)
    (hdx : DifferentiableAt ℝ (cutF U ρ (ε / 2)) x) :
    gradSq (cutF U ρ ε) x ≤ (1 + δ) * G x +
      (1 + 1 / δ) * (Bd * (K / ε)) ^ 2 * ({x | ρ x ≤ 2 * ε}).indicator (fun _ => (1 : ℝ)) x := by
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hUb 0)
  have hρc : Continuous ρ := hρ.continuous hK
  have hG0 : 0 ≤ G x := (gradSq_nonneg U x).trans hGx
  have hC0 : 0 ≤ Bd * (K / ε) := mul_nonneg hBd (div_nonneg hK hε.le)
  by_cases hbig : ρ x ≤ 2 * ε
  swap
  · -- outside the annulus the cut-off function is `U`
    rw [indicator_of_notMem (by simpa using hbig), mul_zero, add_zero]
    have hopen : {z | 2 * ε < ρ z} ∈ 𝓝 x :=
      (isOpen_lt continuous_const hρc).mem_nhds (not_le.mp hbig)
    have heq : cutF U ρ ε =ᶠ[𝓝 x] U := by
      filter_upwards [hopen] with z hz
      unfold cutF
      rw [cutV_one hε (le_of_lt hz), mul_one]
    rw [gradSq_congr_nhds heq]
    nlinarith
  rw [indicator_of_mem (by simpa using hbig), mul_one]
  by_cases hf : DifferentiableAt ℝ (cutF U ρ ε) x
  swap
  · have : gradSq (cutF U ρ ε) x = 0 := by
      unfold gradSq
      rw [fderiv_zero_of_not_differentiableAt hf]
      simp
    rw [this]
    have : 0 ≤ (1 + 1 / δ) * (Bd * (K / ε)) ^ 2 := by positivity
    have : 0 ≤ (1 + δ) * G x := by positivity
    linarith
  -- the function `g = Υ_ε − χ_ε(x)·U`
  set v : ℝ := cutV ρ ε x with hv
  have hv0 : 0 ≤ v := cutV_nonneg ρ ε x
  have hv1 : v ≤ 1 := cutV_le_one ρ ε x
  have hUd : v = 0 ∨ DifferentiableAt ℝ U x := by
    by_cases h1 : ρ x ≤ ε
    · exact Or.inl (cutV_zero hε h1)
    · refine Or.inr ?_
      have hopen : {z | ε < ρ z} ∈ 𝓝 x :=
        (isOpen_lt continuous_const hρc).mem_nhds (not_le.mp h1)
      have heq : cutF U ρ (ε / 2) =ᶠ[𝓝 x] U := by
        filter_upwards [hopen] with z hz
        unfold cutF
        have hz' : ε < ρ z := hz
        rw [cutV_one (by positivity) (by linarith), mul_one]
      exact heq.differentiableAt_iff.mp hdx
  set g : (ι → ℝ) → ℝ := fun z => cutF U ρ ε z - v * U z with hgdef
  have hgb : ∀ z, |g z - g x| ≤ Bd * (K / ε) * √(∑ i, (z i - x i) ^ 2) := by
    intro z
    have e : g z - g x = U z * (cutV ρ ε z - cutV ρ ε x) := by
      simp only [hgdef, cutF, hv]; ring
    rw [e, abs_mul, mul_assoc]
    exact mul_le_mul (hUb z) (cutV_lip hρ hε z x) (abs_nonneg _) hBd
  rcases hUd with hv00 | hU
  · -- `χ_ε(x) = 0`: `g = Υ_ε`
    have e : g = cutF U ρ ε := by
      funext z; simp only [hgdef, hv00, zero_mul, sub_zero]
    rw [e] at hgb
    have h1 := gradSq_le_pt hC0 hf hgb
    have : 0 ≤ (1 + δ) * G x := by positivity
    have h2 : (Bd * (K / ε)) ^ 2 ≤ (1 + 1 / δ) * (Bd * (K / ε)) ^ 2 := by
      have : 0 ≤ 1 / δ * (Bd * (K / ε)) ^ 2 := by positivity
      nlinarith
    linarith
  · have hgd : DifferentiableAt ℝ g x := hf.sub (hU.const_mul v)
    have h1 := gradSq_le_pt hC0 hgd hgb
    have hfd : fderiv ℝ (cutF U ρ ε) x = fderiv ℝ g x + v • fderiv ℝ U x := by
      have e : cutF U ρ ε = fun z => g z + v * U z := by
        funext z; simp only [hgdef]; ring
      have h2 : fderiv ℝ (fun z => g z + v * U z) x =
          fderiv ℝ g x + fderiv ℝ (fun z => v * U z) x := fderiv_add hgd (hU.const_mul v)
      rw [e, h2, fderiv_const_mul hU]
    have hpt : ∀ i, (fderiv ℝ (cutF U ρ ε) x (Pi.single i 1)) ^ 2 ≤
        (1 + 1 / δ) * (fderiv ℝ g x (Pi.single i 1)) ^ 2 +
          (1 + δ) * (fderiv ℝ U x (Pi.single i 1)) ^ 2 := by
      intro i
      rw [hfd]
      rw [show (fderiv ℝ g x + v • fderiv ℝ U x) (Pi.single i 1) =
        fderiv ℝ g x (Pi.single i 1) + v * fderiv ℝ U x (Pi.single i 1) from rfl]
      set a := fderiv ℝ g x (Pi.single i 1)
      set b := fderiv ℝ U x (Pi.single i 1)
      have hq : 0 ≤ (a - δ * (v * b)) ^ 2 / δ := by positivity
      have e : (1 + 1 / δ) * a ^ 2 + (1 + δ) * (v * b) ^ 2 - (a + v * b) ^ 2 =
          (a - δ * (v * b)) ^ 2 / δ := by
        field_simp
        ring
      have hvb : (v * b) ^ 2 ≤ b ^ 2 := by
        rw [mul_pow]
        have : v ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg b]
      have : (1 + δ) * (v * b) ^ 2 ≤ (1 + δ) * b ^ 2 :=
        mul_le_mul_of_nonneg_left hvb (by positivity)
      linarith
    have hsum : gradSq (cutF U ρ ε) x ≤ (1 + 1 / δ) * gradSq g x + (1 + δ) * gradSq U x := by
      unfold gradSq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hpt i
    have h3 : (1 + 1 / δ) * gradSq g x ≤ (1 + 1 / δ) * (Bd * (K / ε)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : (1 + δ) * gradSq U x ≤ (1 + δ) * G x :=
      mul_le_mul_of_nonneg_left hGx (by positivity)
    linarith

/-- **Lemma S, abstract form.** `ρ` is a Lipschitz "radius", `U` is bounded, measurable and
Lipschitz on every set `{ρ ≥ ε}`, `G ≥ |∇U|²` almost everywhere, and
`Pr(ρ ≤ 2ε)/ε² → 0` along `ε = 1/(j + 1)`. Then `Var U ≤ E G`. -/
theorem lemmaS_core (hK : 0 ≤ K) (hρ : EuLip ρ K) (hUm : Measurable U)
    (hUb : ∀ x, |U x| ≤ Bd)
    (hU : ∀ ε, 0 < ε → ∃ L, 0 ≤ L ∧ ∀ x x', ε ≤ ρ x → ε ≤ ρ x' →
      |U x - U x'| ≤ L * √(∑ i, (x i - x' i) ^ 2))
    (hG : Integrable G (stdGauss ι)) (hGb : ∀ᵐ x ∂stdGauss ι, gradSq U x ≤ G x)
    (hP : Tendsto (fun j : ℕ => (stdGauss ι).real {x | ρ x ≤ 2 * (1 / ((j : ℝ) + 1))} /
      (1 / ((j : ℝ) + 1)) ^ 2) atTop (𝓝 0)) :
    ∫ x, (U x - ∫ y, U y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤ ∫ x, G x ∂stdGauss ι := by
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans (hUb 0)
  have hρc : Continuous ρ := hρ.continuous hK
  set I := ∫ x, G x ∂stdGauss ι with hI
  have hI0 : 0 ≤ I := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hGb] with x hx using (gradSq_nonneg U x).trans hx
  set e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with he
  have he0 : ∀ j, 0 < e j := fun j => by simp only [he]; positivity
  have he1 : ∀ j, e j ≤ 1 := fun j => by
    simp only [he]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  set f : ℕ → (ι → ℝ) → ℝ := fun j => cutF U ρ (e j) with hf
  have hfm : ∀ j, Measurable (f j) := fun j => by
    simp only [hf]
    unfold cutF cutV
    exact hUm.mul (measurable_const.min (measurable_const.max
      ((hρc.measurable.div_const _).sub_const _)))
  have hfb : ∀ j x, |f j x| ≤ Bd := fun j x => by
    simp only [hf, cutF]
    rw [abs_mul, abs_of_nonneg (cutV_nonneg ρ _ x)]
    calc |U x| * cutV ρ (e j) x ≤ |U x| * 1 :=
          mul_le_mul_of_nonneg_left (cutV_le_one ρ _ x) (abs_nonneg _)
      _ ≤ Bd := by rw [mul_one]; exact hUb x
  -- the origin has probability zero
  have hsm : ∀ j, MeasurableSet {x | ρ x ≤ 2 * e j} := fun j =>
    measurableSet_le hρc.measurable measurable_const
  have hzero : (stdGauss ι) {x | ρ x ≤ 0} = 0 := by
    have hZm : MeasurableSet {x | ρ x ≤ 0} := measurableSet_le hρc.measurable measurable_const
    have hle : ∀ j : ℕ, (stdGauss ι).real {x | ρ x ≤ 0} ≤
        (stdGauss ι).real {x | ρ x ≤ 2 * e j} / (e j) ^ 2 := by
      intro j
      have h1 : (stdGauss ι).real {x | ρ x ≤ 0} ≤ (stdGauss ι).real {x | ρ x ≤ 2 * e j} := by
        refine measureReal_mono ?_
        intro x hx
        have hx' : ρ x ≤ 0 := hx
        have := he0 j
        show ρ x ≤ 2 * e j
        linarith
      have h2 : (stdGauss ι).real {x | ρ x ≤ 2 * e j} ≤
          (stdGauss ι).real {x | ρ x ≤ 2 * e j} / (e j) ^ 2 := by
        rw [le_div_iff₀ (by have := he0 j; positivity)]
        have h3 : (e j) ^ 2 ≤ 1 := by have := he0 j; have := he1 j; nlinarith
        have h4 : 0 ≤ (stdGauss ι).real {x | ρ x ≤ 2 * e j} := measureReal_nonneg
        nlinarith
      exact h1.trans h2
    have hlim : (stdGauss ι).real {x | ρ x ≤ 0} ≤ 0 :=
      ge_of_tendsto' hP hle
    have h0 : (stdGauss ι).real {x | ρ x ≤ 0} = 0 := le_antisymm hlim measureReal_nonneg
    rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h0
  have hpos : ∀ᵐ x ∂stdGauss ι, 0 < ρ x := by
    rw [ae_iff]
    have : {a | ¬0 < ρ a} = {x | ρ x ≤ 0} := by ext x; simp
    rw [this]; exact hzero
  have hetend : Tendsto e atTop (𝓝 0) := by
    simp only [he]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- eventually `f j x = U x`
  have hev : ∀ᵐ x ∂stdGauss ι, ∀ᶠ j in atTop, f j x = U x := by
    filter_upwards [hpos] with x hx
    have h1 : ∀ᶠ j in atTop, e j < ρ x / 2 := hetend.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h1] with j hj
    simp only [hf, cutF]
    rw [cutV_one (he0 j) (by linarith), mul_one]
  -- convergence of the means
  set mj : ℕ → ℝ := fun j => ∫ x, f j x ∂stdGauss ι with hmj
  set m : ℝ := ∫ x, U x ∂stdGauss ι with hm
  have hmt : Tendsto mj atTop (𝓝 m) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Bd)
      (fun j => (hfm j).aestronglyMeasurable) (integrable_const _)
      (fun j => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb j x) ?_
    filter_upwards [hev] with x hx
    exact tendsto_nhds_of_eventually_eq hx
  have hmjb : ∀ j, |mj j| ≤ Bd := fun j => by
    simp only [hmj]
    have h1 := norm_integral_le_of_norm_le_const (μ := stdGauss ι) (f := f j) (C := Bd)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb j x)
    rw [Real.norm_eq_abs] at h1
    simpa using h1
  have hvt : Tendsto (fun j => ∫ x, (f j x - mj j) ^ 2 ∂stdGauss ι) atTop
      (𝓝 (∫ x, (U x - m) ^ 2 ∂stdGauss ι)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (2 * Bd) ^ 2)
      (fun j => (((hfm j).sub_const _).pow_const 2).aestronglyMeasurable) (integrable_const _)
      (fun j => Eventually.of_forall fun x => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hfb j x
      have h2 := hmjb j
      have h3 : |f j x - mj j| ≤ 2 * Bd := by
        have := abs_sub (f j x) (mj j)
        linarith
      calc (f j x - mj j) ^ 2 = |f j x - mj j| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * Bd) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    · filter_upwards [hev] with x hx
      have h1 : Tendsto (fun j => f j x) atTop (𝓝 (U x)) := tendsto_nhds_of_eventually_eq hx
      exact (h1.sub hmt).pow 2
  -- the bound for each `j` and each `δ`
  have hstep : ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, ∫ x, (f j x - mj j) ^ 2 ∂stdGauss ι ≤
      (1 + δ) * I + (1 + 1 / δ) * (Bd * K) ^ 2 *
        ((stdGauss ι).real {x | ρ x ≤ 2 * e j} / (e j) ^ 2) := by
    intro δ hδ j
    obtain ⟨L, hL0, hL⟩ := hU (e j) (he0 j)
    obtain ⟨L2, hL20, hL2⟩ := hU (e j / 2) (by have := he0 j; positivity)
    have hlip := cutF_lip hK hρ hUb (he0 j) hL0 hL
    have hlip2 := cutF_lip hK hρ hUb (by have := he0 j; positivity : 0 < e j / 2) hL20 hL2
    have hLL : 0 ≤ L + Bd * (K / e j) := by
      have := he0 j; positivity
    have hLL2 : 0 ≤ L2 + Bd * (K / (e j / 2)) := by
      have := he0 j; positivity
    have hae := hlip2.ae_diff hLL2
    set Γ : (ι → ℝ) → ℝ := fun x => (1 + δ) * G x +
      (1 + 1 / δ) * (Bd * (K / e j)) ^ 2 *
        ({x | ρ x ≤ 2 * e j}).indicator (fun _ => (1 : ℝ)) x with hΓ
    have hΓi : Integrable Γ (stdGauss ι) :=
      (hG.const_mul _).add (((integrable_const (1 : ℝ)).indicator (hsm j)).const_mul _)
    have hb : ∀ᵐ x ∂stdGauss ι, ∑ i, (fderiv ℝ (f j) x (Pi.single i 1)) ^ 2 ≤ Γ x := by
      filter_upwards [hGb, hae] with x hx hdx
      exact gradSq_cutF hK hρ hUb (he0 j) hδ hx hdx
    have hp := poincare_lip_le hLL hlip hΓi hb
    refine hp.trans (le_of_eq ?_)
    simp only [hΓ]
    rw [integral_add (hG.const_mul _)
      (((integrable_const (1 : ℝ)).indicator (hsm j)).const_mul _), integral_const_mul,
      integral_const_mul, integral_indicator_const (1 : ℝ) (hsm j), smul_eq_mul, mul_one]
    have hej := (he0 j).ne'
    have e2 : (Bd * (K / e j)) ^ 2 = (Bd * K) ^ 2 / (e j) ^ 2 := by field_simp
    rw [e2]
    ring
  -- the limit in `j`
  have hδ : ∀ δ : ℝ, 0 < δ → ∫ x, (U x - m) ^ 2 ∂stdGauss ι ≤ (1 + δ) * I := by
    intro δ hδ
    have hr : Tendsto (fun j : ℕ => (1 + δ) * I + (1 + 1 / δ) * (Bd * K) ^ 2 *
        ((stdGauss ι).real {x | ρ x ≤ 2 * e j} / (e j) ^ 2)) atTop
        (𝓝 ((1 + δ) * I + (1 + 1 / δ) * (Bd * K) ^ 2 * 0)) :=
      (hP.const_mul _).const_add _
    rw [mul_zero, add_zero] at hr
    exact le_of_tendsto_of_tendsto' hvt hr (hstep δ hδ)
  -- the limit in `δ`
  by_contra hcon
  push Not at hcon
  set V := ∫ x, (U x - m) ^ 2 ∂stdGauss ι with hV
  have hd : 0 < (V - I) / (2 * (I + 1)) := by
    have : 0 < V - I := by linarith
    positivity
  have h1 := hδ _ hd
  have h2 : (V - I) / (2 * (I + 1)) * I ≤ (V - I) / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ V - I := by linarith
    nlinarith
  linarith

end core

end BstLean.Part151
