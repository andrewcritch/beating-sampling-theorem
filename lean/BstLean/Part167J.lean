import BstLean.Part166All

/-!
# Part 167 (file `J`): Lemma J almost everywhere in the weights, at a fixed input

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, proof of Proposition `t7:p07:LG`
(Lemma J: `∇f = 𝒥ᵀb̂/√n`, `∇z = 𝒥ᵀr̂/√n`), for one FIXED input `y ≠ 0` and random weights.

* `NoKink A₁ A₂ y`: no first-layer preactivation at `y` is `0`, and either the first hidden
  vector is `0` or no second-layer preactivation at `y` is `0`.
* **`hid2_eventuallyEq_jac`**: on `NoKink`, the feature map equals the linear map
  `z ↦ 𝒥(y) z` near `y` (`𝒥 = D₂A₂D₁A₁`, Part 151's `jac`).
* **`noKink_ae`**: for a fixed `y ≠ 0`, `NoKink A₁ A₂ y` holds for almost every pair of
  independent Gaussian matrices (any variances `v₁, v₂ > 0`); in particular for `nuA n`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (jac mask mask_of_pos mask_of_nonpos rowL rowL_apply rowL_single)
open BstLean.Part148 (stdGauss_ac)

/-! ## §1 Null hyperplanes for the standard Gaussian vector -/

section null

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonzero linear form of a standard Gaussian vector is almost surely not `0`. -/
lemma lin_ne_zero_ae {w : ι → ℝ} (hw : w ≠ 0) :
    ∀ᵐ ξ ∂stdGauss ι, ∑ l, w l * ξ l ≠ 0 := by
  refine (stdGauss_ac (ι := ι)) ?_
  set L : (ι → ℝ) →L[ℝ] ℝ := ∑ l, w l • (ContinuousLinearMap.proj l : (ι → ℝ) →L[ℝ] ℝ) with hL
  have hLa : ∀ ξ, L ξ = ∑ l, w l * ξ l := by
    intro ξ; simp [hL]
  obtain ⟨l0, hl0⟩ : ∃ l0, w l0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  have hker : LinearMap.ker L.toLinearMap ≠ ⊤ := by
    intro htop
    have hm : (Pi.single l0 (1 : ℝ) : ι → ℝ) ∈ LinearMap.ker L.toLinearMap := by
      rw [htop]; exact Submodule.mem_top
    have h0 := LinearMap.mem_ker.mp hm
    change L (Pi.single l0 1) = 0 at h0
    rw [hLa] at h0
    simp [Pi.single_apply] at h0
    exact hl0 h0
  have hnull := Measure.addHaar_submodule (volume : Measure (ι → ℝ)) _ hker
  refine measure_mono_null ?_ hnull
  intro ξ hξ
  have hξ' : ∑ l, w l * ξ l = 0 := by
    simpa only [mem_compl_iff, mem_ofPred_eq, not_not] using hξ
  show ξ ∈ LinearMap.ker L.toLinearMap
  rw [LinearMap.mem_ker]
  change L ξ = 0
  rw [hLa]; exact hξ'

end null

/-! ## §2 A row of a Gaussian matrix against a fixed nonzero vector -/

section row

variable {m k : ℕ}

lemma measurable_mulVec_apply (y : Fin k → ℝ) (i : Fin m) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => (M *ᵥ y) i) := by
  have : Continuous (fun M : Matrix (Fin m) (Fin k) ℝ => (M *ᵥ y) i) := by
    simp only [mulVec, dotProduct]
    fun_prop
  exact this.measurable

/-- **For a fixed `y ≠ 0`, `(M y)_i ≠ 0` for almost every Gaussian matrix `M`.** -/
lemma gaussMat_row_ne {v : ℝ} (hv : 0 < v) {y : Fin k → ℝ} (hy : y ≠ 0) (i : Fin m) :
    ∀ᵐ M ∂gaussMat m k v, (M *ᵥ y) i ≠ 0 := by
  unfold gaussMat
  have hmeas : Measurable (fun ξ : Fin m × Fin k → ℝ => Matrix.of fun i j => √v * ξ (i, j)) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact (measurable_pi_apply (i, j)).const_mul _
  rw [ae_map_iff hmeas.aemeasurable (p := fun M : Matrix (Fin m) (Fin k) ℝ => (M *ᵥ y) i ≠ 0)
    (measurableSet_eq_fun (measurable_mulVec_apply y i) measurable_const).compl]
  set w : Fin m × Fin k → ℝ := fun p => if p.1 = i then y p.2 else 0 with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hy
    funext l
    have := congrFun h (i, l)
    simpa [hw] using this
  filter_upwards [lin_ne_zero_ae hw0] with ξ hξ
  have e1 : ((Matrix.of fun i j => √v * ξ (i, j)) *ᵥ y) i = √v * ∑ l, y l * ξ (i, l) := by
    simp only [mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ p, w p * ξ p = ∑ l, y l * ξ (i, l) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · simp [hw]
    · intro b _ hb
      simp [hw, hb]
    · simp
  have e : ((Matrix.of fun i j => √v * ξ (i, j)) *ᵥ y) i = √v * ∑ p, w p * ξ p := by
    rw [e1, e2]
  show ((Matrix.of fun i j => √v * ξ (i, j)) *ᵥ y) i ≠ 0
  rw [e]
  exact mul_ne_zero (Real.sqrt_pos.mpr hv).ne' hξ

end row

/-! ## §3 The condition `NoKink` and the local linearity of the feature map -/

section kink

variable {k m₁ m₂ : ℕ}

/-- **No kink at `y`**: no first-layer preactivation is `0`, and either the first hidden vector
is `0` or no second-layer preactivation is `0`. -/
def NoKink (A₁ : Matrix (Fin m₁) (Fin k) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y : Fin k → ℝ) : Prop :=
  (∀ i, (A₁ *ᵥ y) i ≠ 0) ∧
    (reluV (A₁ *ᵥ y) = 0 ∨ ∀ j, (A₂ *ᵥ reluV (A₁ *ᵥ y)) j ≠ 0)

lemma continuous_mulVec_apply' {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (i : Fin p) :
    Continuous (fun z : Fin q → ℝ => (A *ᵥ z) i) := by
  simp only [mulVec, dotProduct]; fun_prop

/-- Near a point where no first-layer preactivation is `0`, the first layer is linear:
`reluV (A₁ z) = D₁ A₁ z`. -/
lemma relu1_eventually {A₁ : Matrix (Fin m₁) (Fin k) ℝ} {y : Fin k → ℝ}
    (h : ∀ i, (A₁ *ᵥ y) i ≠ 0) :
    ∀ᶠ z in 𝓝 y, ∀ i, reluV (A₁ *ᵥ z) i = mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ z) i := by
  rw [eventually_all]
  intro i
  have hc := (continuous_mulVec_apply' A₁ i).continuousAt (x := y)
  rcases lt_or_gt_of_ne (h i) with hneg | hpos
  · filter_upwards [hc.eventually (gt_mem_nhds hneg)] with z hz
    rw [mask_of_nonpos hneg.le, zero_mul]
    exact relu_of_nonpos hz.le
  · filter_upwards [hc.eventually (lt_mem_nhds hpos)] with z hz
    rw [mask_of_pos hpos, one_mul]
    exact relu_of_nonneg hz.le

/-- The masked first layer as a matrix map: `(D₁A₁ z)`. -/
lemma masked_eq (A₁ : Matrix (Fin m₁) (Fin k) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y z : Fin k → ℝ) (j : Fin m₂) :
    (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ z) i)) j =
      ∑ l, (∑ i, A₂ j i * mask ((A₁ *ᵥ y) i) * A₁ i l) * z l := by
  simp only [mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Local linearity (Lemma J at a fixed input)**: on `NoKink`, `hid2 A₁ A₂ z = 𝒥(y) z` for
every `z` near `y`. -/
theorem hid2_eventuallyEq_jac {A₁ : Matrix (Fin m₁) (Fin k) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {y : Fin k → ℝ} (h : NoKink A₁ A₂ y) :
    hid2 A₁ A₂ =ᶠ[𝓝 y] fun z => jac A₁ A₂ y *ᵥ z := by
  obtain ⟨h1, h2⟩ := h
  have hr := relu1_eventually h1
  -- the masked first layer
  set g : (Fin k → ℝ) → Fin m₁ → ℝ := fun z i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ z) i with hg
  have hgy : g y = reluV (A₁ *ᵥ y) := by
    funext i
    rcases lt_or_gt_of_ne (h1 i) with hneg | hpos
    · simp [hg, mask_of_nonpos hneg.le, reluV, relu_of_nonpos hneg.le]
    · simp [hg, mask_of_pos hpos, reluV, relu_of_nonneg hpos.le]
  have hjac : ∀ z j, (jac A₁ A₂ y *ᵥ z) j =
      mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) * (A₂ *ᵥ g z) j := by
    intro z j
    rw [masked_eq]
    simp only [jac, mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rcases h2 with h0 | h2
  · -- all first-layer units are inactive: `g ≡ 0`
    have hmask : ∀ i, mask ((A₁ *ᵥ y) i) = 0 := by
      intro i
      have hi := congrFun h0 i
      simp only [reluV, Pi.zero_apply] at hi
      rcases lt_or_gt_of_ne (h1 i) with hneg | hpos
      · exact mask_of_nonpos hneg.le
      · exfalso; rw [relu_of_nonneg hpos.le] at hi; exact (h1 i) hi
    filter_upwards [hr] with z hz
    funext j
    rw [hjac]
    have hgz : g z = 0 := by funext i; simp [hg, hmask i]
    have hrz : reluV (A₁ *ᵥ z) = 0 := by funext i; rw [hz i, hmask i, zero_mul]; rfl
    unfold hid2
    rw [hrz, hgz]
    simp [reluV, relu_of_nonpos le_rfl]
  · -- second layer: signs constant near `y`
    have hev2 : ∀ᶠ z in 𝓝 y, ∀ j, relu ((A₂ *ᵥ g z) j) =
        mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) * (A₂ *ᵥ g z) j := by
      rw [eventually_all]
      intro j
      have hc : ContinuousAt (fun z => (A₂ *ᵥ g z) j) y := by
        have : Continuous (fun z => (A₂ *ᵥ g z) j) := by
          simp only [hg, mulVec, dotProduct]; fun_prop
        exact this.continuousAt
      have hval : (A₂ *ᵥ g y) j = (A₂ *ᵥ reluV (A₁ *ᵥ y)) j := by rw [hgy]
      rcases lt_or_gt_of_ne (h2 j) with hneg | hpos
      · rw [← hval] at hneg
        filter_upwards [hc.eventually (gt_mem_nhds hneg)] with z hz
        rw [mask_of_nonpos (by rw [← hval]; exact hneg.le), zero_mul]
        exact relu_of_nonpos hz.le
      · rw [← hval] at hpos
        filter_upwards [hc.eventually (lt_mem_nhds hpos)] with z hz
        rw [mask_of_pos (by rw [← hval]; exact hpos), one_mul]
        exact relu_of_nonneg hz.le
    filter_upwards [hr, hev2] with z hz hz2
    funext j
    rw [hjac]
    have hrz : reluV (A₁ *ᵥ z) = g z := funext hz
    unfold hid2
    rw [hrz]
    exact hz2 j

end kink

/-! ## §4 `NoKink` almost everywhere in the weights -/

section ae

variable {k m₁ m₂ : ℕ}

lemma measurable_mulVec_joint' {p q r : ℕ} :
    Measurable (fun θ : Matrix (Fin p) (Fin q) ℝ × Matrix (Fin r) (Fin p) ℝ =>
      (θ.1, θ.2)) := measurable_id

/-- **Lemma J almost everywhere in the weights**: for a fixed `y ≠ 0` and independent Gaussian
matrices with variances `v₁, v₂ > 0`, `NoKink A₁ A₂ y` holds almost surely. -/
theorem noKink_ae {v₁ v₂ : ℝ} (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) {y : Fin k → ℝ} (hy : y ≠ 0) :
    ∀ᵐ θ ∂(gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂), NoKink θ.1 θ.2 y := by
  -- first layer
  have h1 : ∀ᵐ θ ∂(gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂), ∀ i, (θ.1 *ᵥ y) i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_fst).ae (gaussMat_row_ne hv₁ hy i)
  -- second layer
  have hc1 : Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      reluV (θ.1 *ᵥ y)) := by
    unfold reluV relu
    refine continuous_pi fun i => ?_
    have : Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
        (θ.1 *ᵥ y) i) := by simp only [mulVec, dotProduct]; fun_prop
    exact continuous_const.max this
  have h2 : ∀ j, ∀ᵐ θ ∂(gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂),
      reluV (θ.1 *ᵥ y) = 0 ∨ (θ.2 *ᵥ reluV (θ.1 *ᵥ y)) j ≠ 0 := by
    intro j
    have hc2 : Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
        (θ.2 *ᵥ reluV (θ.1 *ᵥ y)) j) := by
      simp only [mulVec, dotProduct]
      refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_apply i).comp ((continuous_apply j).comp continuous_snd)).mul
        ((continuous_apply i).comp hc1)
    have hS : MeasurableSet {θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ |
        reluV (θ.1 *ᵥ y) = 0 ∨ (θ.2 *ᵥ reluV (θ.1 *ᵥ y)) j ≠ 0} :=
      (measurableSet_eq_fun hc1.measurable measurable_const).union
        (measurableSet_eq_fun hc2.measurable measurable_const).compl
    rw [Measure.ae_prod_iff_ae_ae hS]
    refine Filter.Eventually.of_forall fun A₁ => ?_
    by_cases h0 : reluV (A₁ *ᵥ y) = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inl h0
    · filter_upwards [gaussMat_row_ne hv₂ h0 j] with A₂ hA₂
      exact Or.inr hA₂
  have h2' : ∀ᵐ θ ∂(gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂),
      ∀ j, reluV (θ.1 *ᵥ y) = 0 ∨ (θ.2 *ᵥ reluV (θ.1 *ᵥ y)) j ≠ 0 := ae_all_iff.mpr h2
  filter_upwards [h1, h2'] with θ hθ1 hθ2
  refine ⟨hθ1, ?_⟩
  by_cases h0 : reluV (θ.1 *ᵥ y) = 0
  · exact Or.inl h0
  · exact Or.inr fun j => (hθ2 j).resolve_left h0

/-- `NoKink` for the Agent weights `nuA n` at a fixed input `y ≠ 0` (`n ≥ 1`). -/
theorem noKink_nuA {n : ℕ} (hn : 1 ≤ n) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∀ᵐ θ ∂BstLean.Part153.nuA n, NoKink θ.1 θ.2 y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    unfold mA; have : 0 < n ^ 2 := by positivity
    exact_mod_cast this
  exact noKink_ae (by positivity) (by positivity) hy

end ae

end BstLean.Part167
