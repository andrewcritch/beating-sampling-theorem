import BstLean.Part170Lam

/-!
# Part 170 (file `Dec`): the exact-rule location error = fluctuation + bias, at a fixed `A₁`

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "The plane conditioning and the location fluctuation":
`√n|b|Δ_f^exact = N_f^fl + N_f^b`, and Lemma `t7:p08:fl`.

At a fixed retained value `c` (World data and `A₁`) and a fixed node `g`, the error is a function
of the second-layer matrix `M = A₂` (`withA2 c M`). Part 167's `plane_split` writes
`M = reb h c₁ (reb r c₂ N)` with `h` the vector that the centre `b` reads (`b_j` is a function of
`(Mh)_j`), `r = res h ā`, plane coordinates `c₁ = cOf t h ξ₁`, `c₂ = cOf t r ξ₂` and an independent
Gaussian matrix `N`.

* `withA2 c M`, `hB c`, `Mpl`: the retained value with second layer `M`; `h = hT n A₁ ĉ τ₀`; the
  matrix of the plane split.
* `Mpl_mulVec`: `Mpl N y = Mpl 0 y + N (perp r (perp h y))`.
* `exFn_eq`: `exFn = κ Σ_j b_j (E_v ReLU((M a₁(x_v))_j) − ψ_ς((Mā)_j))`, `κ = n/(√n|b|)`.
* `exFn_Mpl`: at fixed plane coordinates, `exFn` is the function `flE` of `N` of file `Fl`.
* `biasF c g ξ₁ ξ₂ = E_N exFn`: **the conditional mean of the exact-rule error given the plane
  coordinates** (the paper's `nΔ_f^b`).
* **`exFn_mom`**: on `‖A₁‖_op ≤ O`, at a node with `s² ≤ 1`, if
  `E_{ξ₁,ξ₂} biasF⁸ ≤ B⁸` then `E_{A₂} exFn⁸ ≤ (F_fl + B)⁸`,
  `F_fl = (π/2)·1.8·√n·√(t_A·O²/(n − 2))/2`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part134 (res lam projPerp glue)
open BstLean.Part167 (perp)
open BstLean.Part162 (gmom gmom_nonneg)
open BstLean.Part157 (cOf reb)
open BstLean.Part150 (hT sT)
open BstLean.Part136 (HidParam)

variable {n : ℕ}

/-- The retained value `c` with the second-layer matrix replaced by `M`. -/
noncomputable def withA2 (c : Ret n) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : Ret n :=
  (c.1, (((A1 c, M), c.2.1.2), c.2.2))

lemma measurable_withA2 (c : Ret n) : Measurable (withA2 c) := by
  unfold withA2
  exact measurable_const.prodMk (((measurable_const.prodMk measurable_id).prodMk
    measurable_const).prodMk measurable_const)

/-- The vector that the centre reads: `b_j` is a function of `(A₂ h)_j`. -/
noncomputable def hB (c : Ret n) : Fin (mA n) → ℝ := hT n (A1 c) c.1.2 (tau0p c.1.1)

/-- The centre as a function of `M h`. -/
noncomputable def bOfY (c : Ret n) (y : Fin (mA n) → ℝ) : Fin (mA n) → ℝ :=
  fun j => BstLean.Part150.binMean n (fun z => relu (y j + sT n (A1 c) c.1.2 (tau0p c.1.1) * z)) /
    BstLean.Part150.rhoC c.1.2 (tau0p c.1.1)

lemma bR_withA2 (c : Ret n) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    bR (withA2 c M) = bOfY c (M *ᵥ hB c) := rfl

lemma vmean_aLat (c : Ret n) (s : ℝ) :
    vmean (stdGauss (Fin (n - 1))) (aLat c s) = a1Bar c s := rfl

/-- The matrix of the plane split. -/
noncomputable def Mpl (h r c₁ c₂ : Fin (mA n) → ℝ) (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ := reb h c₁ (reb r c₂ N)

lemma Mpl_mulVec (h r c₁ c₂ : Fin (mA n) → ℝ) (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (y : Fin (mA n) → ℝ) :
    Mpl h r c₁ c₂ N *ᵥ y = Mpl h r c₁ c₂ 0 *ᵥ y + N *ᵥ perp r (perp h y) := by
  unfold Mpl reb glue
  simp only [Matrix.add_mulVec, Matrix.add_mul, Matrix.zero_mul, add_zero,
    ← Matrix.mulVec_mulVec, BstLean.Part167.projPerp_mulVec]
  abel

lemma perp_zero' (b : Fin (mA n) → ℝ) : perp b 0 = 0 := by
  unfold perp; simp

/-- **The location error as a function of the second layer.** -/
lemma exFn_eq (_hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    exFn (withA2 c M) g = (n : ℝ) / (√(n : ℝ) * √(normSq (bR (withA2 c M)))) *
      ∑ j, bR (withA2 c M) j * (∫ v, relu ((M *ᵥ aLat c (nodeS c g) v) j)
        ∂stdGauss (Fin (n - 1)) -
        BstLean.Part137.psiS √(vsig2 c (nodeS c g)) ((M *ᵥ a1Bar c (nodeS c g)) j)) := by
  set s := nodeS c g
  set b := bR (withA2 c M)
  have hint : ∀ j, Integrable (fun v => relu ((M *ᵥ aLat c s v) j) * b j)
      (stdGauss (Fin (n - 1))) := fun j =>
    int_comp_bdd (f := fun y => relu ((M *ᵥ y) j) * b j) (measurable_aLat c s) hK
      ((continuous_relu.comp ((continuous_apply j).comp (Continuous.matrix_mulVec
        continuous_const continuous_id))).mul continuous_const)
  have hf : fbarS (withA2 c M) s = (∑ j, (∫ v, relu ((M *ᵥ aLat c s v) j)
      ∂stdGauss (Fin (n - 1))) * b j) / (√(n : ℝ) * √(normSq b)) := by
    have e : ∀ v, fX (withA2 c M) (xLat (withA2 c M) s (unitF53 v)) =
        (∑ j, relu ((M *ᵥ aLat c s v) j) * b j) / (√(n : ℝ) * √(normSq b)) := fun v => rfl
    unfold fbarS
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_div,
      integral_finsetSum _ fun j _ => hint j]
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  have hg : fGauss (withA2 c M) s = (∑ j, BstLean.Part137.psiS √(vsig2 c s)
      ((M *ᵥ a1Bar c s) j) * b j) / (√(n : ℝ) * √(normSq b)) := rfl
  unfold exFn
  rw [show nodeS (withA2 c M) g = s from rfl, hf, hg]
  rw [show ∀ X Y D : ℝ, (n : ℝ) * (X / D - Y / D) = (n : ℝ) / D * (X - Y) from fun X Y D => by ring,
    ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **At fixed plane coordinates the error is the function `flE` of the transverse matrix.** -/
lemma exFn_Mpl (hn : 1 ≤ n) (c : Ret n) (g : ℕ) {K : ℝ}
    (hK : ∀ v, ‖aLat c (nodeS c g) v‖ ≤ K) (c₁ c₂ : Fin (mA n) → ℝ)
    (N : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    exFn (withA2 c (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ N)) g =
      flE (stdGauss (Fin (n - 1))) (aLat c (nodeS c g)) (hB c)
        (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ 0)
        (bOfY c (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ 0 *ᵥ hB c))
        (fun j => BstLean.Part137.psiS √(vsig2 c (nodeS c g))
          ((Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ 0 *ᵥ a1Bar c (nodeS c g)) j))
        ((n : ℝ) / (√(n : ℝ) * √(normSq (bOfY c (Mpl (hB c)
          (res (hB c) (a1Bar c (nodeS c g))) c₁ c₂ 0 *ᵥ hB c))))) N := by
  set s := nodeS c g
  set h := hB c
  set r := res h (a1Bar c s)
  rw [exFn_eq hn c g hK, bR_withA2]
  have eh : Mpl h r c₁ c₂ N *ᵥ h = Mpl h r c₁ c₂ 0 *ᵥ h := by
    rw [Mpl_mulVec, perp_self, perp_zero', Matrix.mulVec_zero, add_zero]
  have ea : Mpl h r c₁ c₂ N *ᵥ a1Bar c s = Mpl h r c₁ c₂ 0 *ᵥ a1Bar c s := by
    rw [Mpl_mulVec, perp_perp_res, Matrix.mulVec_zero, add_zero]
  rw [eh, ea]
  unfold flE
  rw [vmean_aLat]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [Mpl_mulVec]
  rfl

/-- The entry variance of `A₂`: `t_A = 2/m_A`. -/
noncomputable def tA (n : ℕ) : ℝ := 2 / ((mA n : ℕ) : ℝ)

/-- **The conditional mean of the exact-rule location error given the plane coordinates**
`(ξ₁, ξ₂)` (the paper's `nΔ_f^b`). -/
noncomputable def biasF (c : Ret n) (g : ℕ) (ξ₁ ξ₂ : Fin (mA n) → ℝ) : ℝ :=
  ∫ N, exFn (withA2 c (Mpl (hB c) (res (hB c) (a1Bar c (nodeS c g)))
    (cOf (tA n) (hB c) ξ₁) (cOf (tA n) (res (hB c) (a1Bar c (nodeS c g))) ξ₂) N)) g
    ∂gaussMat (mA n) (mA n) (tA n)

/-- `(x + y)⁸ ≤ (A + B)⁷/A⁷·|x|⁸ + (A + B)⁷/B⁷·|y|⁸` (convexity; Minkowski in `L⁸`). -/
lemma pow8_split (x y : ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (x + y) ^ 8 ≤ (A + B) ^ 7 / A ^ 7 * |x| ^ 8 + (A + B) ^ 7 / B ^ 7 * |y| ^ 8 := by
  have hAB : 0 < A + B := add_pos hA hB
  set l := A / (A + B) with hl
  have hl0 : 0 < l := div_pos hA hAB
  have hl1 : 0 < 1 - l := by rw [hl, sub_pos, div_lt_one hAB]; linarith
  have e1 : 1 - l = B / (A + B) := by rw [hl]; field_simp; ring
  have hc := (convexOn_pow (𝕜 := ℝ) 8).2 (Set.mem_Ici.mpr (div_nonneg (abs_nonneg x) hl0.le))
    (Set.mem_Ici.mpr (div_nonneg (abs_nonneg y) hl1.le)) hl0.le hl1.le (by ring)
  simp only [smul_eq_mul] at hc
  have e2 : l * (|x| / l) + (1 - l) * (|y| / (1 - l)) = |x| + |y| := by field_simp
  rw [e2] at hc
  have h0 : (x + y) ^ 8 ≤ (|x| + |y|) ^ 8 := by
    rw [← Even.pow_abs (by decide) (x + y)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_add_le x y) 8
  refine h0.trans (hc.trans (le_of_eq ?_))
  rw [e1, hl]
  field_simp

lemma gmom8_le : gmom 8 ≤ (18 / 10) ^ 8 := by
  have h := BstLean.Part162.gmom_even 4
  rw [show (2 * 4 : ℕ) = 8 from rfl] at h
  rw [h]
  simp [Finset.prod_range_succ]
  norm_num

/-- The fluctuation allowance `F_fl = (π/2)·1.8·√n·√(t_A·O²/(n − 2))/2`. -/
noncomputable def Ffl (n : ℕ) (O : ℝ) : ℝ :=
  π / 2 * (18 / 10) * √(n : ℝ) * √(tA n * (O ^ 2 / ((n : ℝ) - 2))) / 2

lemma kappa_b_le (n : ℕ) (b : Fin (mA n) → ℝ) :
    |(n : ℝ) / (√(n : ℝ) * √(normSq b))| * √(normSq b) ≤ √(n : ℝ) := by
  by_cases hb : √(normSq b) = 0
  · rw [hb]; simp
  · have hb0 : 0 < √(normSq b) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hb)
    by_cases hn0 : (n : ℝ) = 0
    · rw [hn0]; simp
    · have hn' : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn0))
      rw [abs_of_nonneg (by positivity)]
      have e : (n : ℝ) / (√(n : ℝ) * √(normSq b)) * √(normSq b) = (n : ℝ) / √(n : ℝ) := by
        field_simp
      rw [e, Real.div_sqrt]

/-- **The eighth moment of the exact-rule location error over `A₂`, at a fixed `A₁`**: on
`‖A₁‖_op ≤ O`, at a node with `s_g² ≤ 1`, if the bias (the conditional mean given the plane
coordinates) has `E_{ξ₁,ξ₂} biasF⁸ ≤ B⁸`, then `E_{A₂} exFn⁸ ≤ (F_fl + B)⁸`. -/
theorem exFn_mom (hn : 3 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 < O)
    (h1 : OpB (A1 c) O) {B : ℝ} (hB0 : 0 < B)
    (hBias : ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
      ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)) :
    ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal ((Ffl n O + B) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  set s := nodeS c g with hsd
  set h := hB c
  set r := res h (a1Bar c s)
  set Λ := O ^ 2 / ((n : ℝ) - 2) with hΛd
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hΛ0 : 0 ≤ Λ := by positivity
  have htA : 0 < tA n := by
    unfold tA; have : 0 < mA n := by unfold mA; positivity
    positivity
  have hK := aLat_bdd hn1 c hs hO.le h1
  have hΛ : ∀ e, ∫ v, (e ⬝ᵥ (aLat c s v - vmean (stdGauss (Fin (n - 1))) (aLat c s))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ Λ * normSq e := cov_bound hn c hs hO.le h1
  set A := Ffl n O with hAd
  have hA : 0 < A := by
    rw [hAd]; unfold Ffl
    have : 0 < √(tA n * (O ^ 2 / ((n : ℝ) - 2))) := Real.sqrt_pos.mpr (by positivity)
    have : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    positivity
  set k₁ := (A + B) ^ 7 / A ^ 7
  set k₂ := (A + B) ^ 7 / B ^ 7
  have hk₁ : 0 ≤ k₁ := by positivity
  have hk₂ : 0 ≤ k₂ := by positivity
  -- the plane split
  have mF : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => ENNReal.ofReal (exFn (withA2 c p.2.2) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exFn_comp ((measurable_withA2 c).comp
      (measurable_snd.comp measurable_snd)) measurable_const).pow_const 8)
  have hps := BstLean.Part167.plane_split (q := mA n) (tA n) h (a1Bar c s) mF
  have e0 : ∫⁻ M, ENNReal.ofReal (exFn (withA2 c M) g ^ 8) ∂gaussMat (mA n) (mA n) (tA n) =
      ∫⁻ M, (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
        ENNReal.ofReal (exFn (withA2 c p.2.2) g ^ 8)) (M *ᵥ h, M *ᵥ a1Bar c s, M)
        ∂gaussMat (mA n) (mA n) (tA n) := rfl
  rw [e0, hps]
  simp only
  -- the inner bound at fixed plane coordinates
  have hin : ∀ ξ₁ ξ₂ : Fin (mA n) → ℝ, ∫⁻ N, ENNReal.ofReal (exFn (withA2 c
      (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) := by
    intro ξ₁ ξ₂
    set c₁ := cOf (tA n) h ξ₁
    set c₂ := cOf (tA n) r ξ₂
    set M₀ := Mpl h r c₁ c₂ 0
    set b₀ := bOfY c (M₀ *ᵥ h)
    set ψ₀ : Fin (mA n) → ℝ := fun j => BstLean.Part137.psiS √(vsig2 c s) ((M₀ *ᵥ a1Bar c s) j)
    set κ₀ := (n : ℝ) / (√(n : ℝ) * √(normSq b₀))
    set E := flE (stdGauss (Fin (n - 1))) (aLat c s) h M₀ b₀ ψ₀ κ₀
    have hE : ∀ N, exFn (withA2 c (reb h c₁ (reb r c₂ N))) g = E N := fun N =>
      exFn_Mpl hn1 c g hK c₁ c₂ N
    have hmE : ∫ N, E N ∂gaussMat (mA n) (mA n) (tA n) = biasF c g ξ₁ ξ₂ := by
      unfold biasF
      exact integral_congr_ae (Filter.Eventually.of_forall fun N => (hE N).symm)
    simp_rw [hE]
    have hc := continuous_flE (measurable_aLat c s) hK hΛ0 hΛ h M₀ b₀ ψ₀ κ₀
    have hpt : ∀ N, ENNReal.ofReal (E N ^ 8) ≤ ENNReal.ofReal k₁ *
        ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8) +
        ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
      intro N
      rw [← ENNReal.ofReal_mul hk₁, ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hk₂ (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := pow8_split (E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n))
        (∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)) hA hB0
      rw [sub_add_cancel, hmE] at this
      have e8 : |biasF c g ξ₁ ξ₂| ^ 8 = biasF c g ξ₁ ξ₂ ^ 8 := (by decide : Even 8).pow_abs _
      rw [e8] at this
      rw [hmE]
      exact this
    have mfl : Measurable (fun N => ENNReal.ofReal
        (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)) :=
      ENNReal.measurable_ofReal.comp (((hc.measurable.sub_const _).abs).pow_const 8)
    have hfl := fl_mom (measurable_aLat c s) hK hΛ0 hΛ h M₀ b₀ ψ₀ κ₀ htA.le
    have hfl' : (π / 2) ^ 8 * (gmom 8 * (|κ₀| * √(normSq b₀) * √(tA n * Λ) / 2) ^ 8) ≤ A ^ 8 := by
      have h1' : |κ₀| * √(normSq b₀) * √(tA n * Λ) / 2 ≤ √(n : ℝ) * √(tA n * Λ) / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (kappa_b_le n b₀)
          (Real.sqrt_nonneg _)) (by norm_num)
      have h2' := gmom8_le
      have h3 : (|κ₀| * √(normSq b₀) * √(tA n * Λ) / 2) ^ 8 ≤ (√(n : ℝ) * √(tA n * Λ) / 2) ^ 8 :=
        pow_le_pow_left₀ (by positivity) h1' 8
      have h4 : gmom 8 * (|κ₀| * √(normSq b₀) * √(tA n * Λ) / 2) ^ 8 ≤
          (18 / 10) ^ 8 * (√(n : ℝ) * √(tA n * Λ) / 2) ^ 8 :=
        mul_le_mul h2' h3 (by positivity) (by positivity)
      have e : A ^ 8 = (π / 2) ^ 8 * ((18 / 10) ^ 8 * (√(n : ℝ) * √(tA n * Λ) / 2) ^ 8) := by
        rw [hAd]; unfold Ffl; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    calc ∫⁻ N, ENNReal.ofReal (E N ^ 8) ∂gaussMat (mA n) (mA n) (tA n)
        ≤ ∫⁻ N, (ENNReal.ofReal k₁ *
          ENNReal.ofReal (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8) +
          ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8)) ∂gaussMat (mA n) (mA n) (tA n) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal k₁ * ∫⁻ N, ENNReal.ofReal
            (|E N - ∫ N', E N' ∂gaussMat (mA n) (mA n) (tA n)| ^ 8)
            ∂gaussMat (mA n) (mA n) (tA n) + ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ mfl]
      _ ≤ ENNReal.ofReal k₁ * ENNReal.ofReal (A ^ 8) +
            ENNReal.ofReal (k₂ * biasF c g ξ₁ ξ₂ ^ 8) := by
          gcongr
          exact hfl.trans (ENNReal.ofReal_le_ofReal hfl')
      _ = _ := by
          rw [← ENNReal.ofReal_mul hk₁, ENNReal.ofReal_mul hk₂]
  -- the outer integrals
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (exFn (withA2 c
        (reb h (cOf (tA n) h ξ₁) (reb r (cOf (tA n) r ξ₂) N))) g ^ 8)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, (ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ *
          ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) :=
        lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hin ξ₁ ξ₂
    _ = ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ∫⁻ ξ₁, ∫⁻ ξ₂,
          ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
        have e1 : ∀ ξ₁ : Fin (mA n) → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ *
            ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8)) ∂stdGauss (Fin (mA n)) =
            ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ∫⁻ ξ₂,
              ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n)) := by
          intro ξ₁
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [e1]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (k₁ * A ^ 8) + ENNReal.ofReal k₂ * ENNReal.ofReal (B ^ 8) := by
        gcongr
    _ = ENNReal.ofReal ((A + B) ^ 8) := by
        rw [← ENNReal.ofReal_mul hk₂, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hA7 : A ^ 7 ≠ 0 := by positivity
        have hB7 : B ^ 7 ≠ 0 := by positivity
        simp only [k₁, k₂]
        field_simp

end BstLean.Part170
