import BstLean.Part272Coord
import BstLean.Part73Orth

/-!
# Part 272 (V3b): reduce `a1Bar` and `e1Bar` to the coordinate law

`uEff c = H e₀` is the axis that Lean uses: `uHat c` when `ĉ ≠ 0` (`uEff_eq`) and `−e₀` when
`ĉ = 0` (`uEff_zero`). `alphaE c i = a_i·uEff`, `kappaE c i = √max(0, |a_i|² − alphaE²)`.

`a1Bar_reduce`, `e1Bar_reduce`: the exact sphere moments are the moments of
`ReLU(s·α + √(1 − s²)·κ·T)` with `T` the first coordinate of a uniform direction in `ℝ^{n−1}`.
These hold for every retained value, including `ĉ = 0` and `|s| ≥ 1`.
-/

namespace BstLean.Part272

open Real MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part130 (relu normSq e0 measurable_relu normSq_nonneg normSq_eq_zero mA)
open BstLean.Part157 (Ret)
open BstLean.Part161 (hhMat uHat xLat consV hh_mulVec hh_normSq hh_e0 hh_symm stdGauss_map_hh
  measurable_hh e0_dot e0_apply_sq_sum normSq_uHat consV_zero)
open BstLean.Part169 (A1 a1Bar e1Bar)

variable {n : ℕ}

/-- The axis used by Lean: `H e₀` with `H = hhMat (uHat c)`. -/
noncomputable def uEff (c : Ret n) : Fin n → ℝ := (hhMat (uHat c)).mulVec (e0 n)

/-- `α_i = a_i·uEff`. -/
noncomputable def alphaE (c : Ret n) (i : Fin (mA n)) : ℝ := ∑ j, A1 c i j * uEff c j

/-- `κ_i = √max(0, |a_i|² − α_i²)`. -/
noncomputable def kappaE (c : Ret n) (i : Fin (mA n)) : ℝ :=
  √(max 0 (∑ j, A1 c i j ^ 2 - alphaE c i ^ 2))

theorem uEff_eq (c : Ret n) (hc : c.1.2 ≠ 0) : uEff c = uHat c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i; exact i.elim0
  · exact hh_e0 hn (normSq_uHat hc)

theorem uEff_zero (c : Ret n) (hc : c.1.2 = 0) : uEff c = -e0 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i; exact i.elim0
  have hu : uHat c = 0 := by simp [uHat, hc]
  have h0 : e0 n ⟨0, hn⟩ = 1 := by simp [e0]
  unfold uEff
  rw [hu, hh_mulVec, sub_zero, e0_dot hn, e0_apply_sq_sum hn, h0]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The reflection is symmetric for the scalar product. -/
theorem hh_dot_symm {k : ℕ} (u x y : Fin k → ℝ) :
    ∑ i, (hhMat u).mulVec x i * y i = ∑ i, x i * (hhMat u).mulVec y i := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hh_symm u j i]
  ring

theorem sum_split (hn : 1 ≤ n) (f : Fin n → ℝ) :
    ∑ i, f i = f ⟨0, by omega⟩ + ∑ j : Fin (n-1), f ⟨j+1, by omega⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n-1, by omega⟩
  rw [Fin.sum_univ_succ]
  rfl

theorem sum_consV (hn : 1 ≤ n) (b : Fin n → ℝ) (z : ℝ) (g : Fin (n-1) → ℝ) :
    ∑ i, b i * consV z g i =
      b ⟨0, by omega⟩ * z + ∑ j : Fin (n-1), b ⟨j+1, by omega⟩ * g j := by
  rw [sum_split hn]
  congr 1
  all_goals first
    | rw [consV_zero hn]
    | (refine Finset.sum_congr rfl fun j _ => ?_; simp [consV])
    | simp [consV]

/-- The tail of `H a_i`. -/
noncomputable def wTail (c : Ret n) (i : Fin (mA n)) : Fin (n-1) → ℝ :=
  fun j => (hhMat (uHat c)).mulVec (A1 c i) ⟨j+1, by omega⟩

theorem hA0 (hn : 1 ≤ n) (c : Ret n) (i : Fin (mA n)) :
    (hhMat (uHat c)).mulVec (A1 c i) ⟨0, by omega⟩ = alphaE c i := by
  rw [← e0_dot hn ((hhMat (uHat c)).mulVec (A1 c i)), ← hh_dot_symm (uHat c) (e0 n) (A1 c i)]
  unfold alphaE uEff
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The row preactivation at the latitude point. -/
theorem row_xLat (hn : 1 ≤ n) (c : Ret n) (s : ℝ) (V : Fin (n-1) → ℝ) (i : Fin (mA n)) :
    (A1 c).mulVec (xLat c s V) i = s * alphaE c i + √(1 - s^2) * ∑ j, wTail c i j * V j := by
  have h1 : (A1 c).mulVec (xLat c s V) i =
      ∑ l, (hhMat (uHat c)).mulVec (A1 c i) l * consV s (√(1-s^2) • V) l := by
    rw [hh_dot_symm]; rfl
  rw [h1, sum_consV hn, hA0 hn, Finset.mul_sum, mul_comm (alphaE c i) s]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, wTail]
  ring

theorem normSq_wTail (hn : 1 ≤ n) (c : Ret n) (i : Fin (mA n)) :
    normSq (wTail c i) = ∑ j, A1 c i j ^ 2 - alphaE c i ^ 2 := by
  have h := hh_normSq (uHat c) (A1 c i)
  unfold normSq at h
  rw [sum_split hn, hA0 hn] at h
  unfold normSq
  simp only [wTail]
  linarith

theorem kappaE_eq (hn : 1 ≤ n) (c : Ret n) (i : Fin (mA n)) :
    kappaE c i = √(normSq (wTail c i)) := by
  unfold kappaE
  rw [← normSq_wTail hn, max_eq_right (normSq_nonneg _)]

/-- `⟨w, x⟩ = |w|·(H x)₀` with `H` the reflection that sends `e₀` to `w/|w|`. -/
theorem dot_rot {k : ℕ} (hk : 1 ≤ k) (w x : Fin k → ℝ) :
    ∑ j, w j * x j =
      √(normSq w) * (hhMat ((√(normSq w))⁻¹ • w)).mulVec x ⟨0, by omega⟩ := by
  by_cases hw : w = 0
  · subst hw; simp [normSq]
  have hpos : 0 < normSq w :=
    lt_of_le_of_ne (normSq_nonneg w) (fun h => hw (normSq_eq_zero h.symm))
  have hs : √(normSq w) ≠ 0 := (sqrt_pos.mpr hpos).ne'
  have hu : normSq ((√(normSq w))⁻¹ • w) = 1 := by
    have e : normSq ((√(normSq w))⁻¹ • w) = ((√(normSq w))⁻¹)^2 * normSq w := by
      unfold normSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, inv_pow, sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  rw [← e0_dot hk ((hhMat ((√(normSq w))⁻¹ • w)).mulVec x),
    ← hh_dot_symm ((√(normSq w))⁻¹ • w) (e0 k) x, hh_e0 hk hu, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem unitF_hh {k : ℕ} (u v : Fin k → ℝ) :
    unitF53 ((hhMat u).mulVec v) = (hhMat u).mulVec (unitF53 v) := by
  unfold unitF53
  have h := hh_normSq u v
  unfold normSq at h
  rw [h, Matrix.mulVec_smul]

theorem integral_rot {k : ℕ} (u : Fin k → ℝ) {F : (Fin k → ℝ) → ℝ} (hF : Measurable F) :
    ∫ v, F ((hhMat u).mulVec v) ∂stdGauss (Fin k) = ∫ v, F v ∂stdGauss (Fin k) := by
  rw [← integral_map (measurable_hh u).aemeasurable hF.aestronglyMeasurable, stdGauss_map_hh]

/-- An auxiliary affine composition. -/
noncomputable def rowG (φ : ℝ → ℝ) (a t r T : ℝ) : ℝ := φ (a + t * (r * T))

/-- **The reduction** for any measurable `φ`. -/
theorem row_reduce (hn : 2 ≤ n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) (φ : ℝ → ℝ)
    (hφ : Measurable φ) :
    ∫ v, φ ((A1 c).mulVec (xLat c s (unitF53 v)) i) ∂stdGauss (Fin (n - 1)) =
      ∫ v, φ (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
        unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n - 1)) := by
  have hpt : ∀ v : Fin (n-1) → ℝ, φ ((A1 c).mulVec (xLat c s (unitF53 v)) i) =
      rowG φ (s * alphaE c i) (√(1 - s^2)) (√(normSq (wTail c i)))
        (unitF53 ((hhMat ((√(normSq (wTail c i)))⁻¹ • wTail c i)).mulVec v) ⟨0, by omega⟩) := by
    intro v
    rw [row_xLat (by omega), dot_rot (by omega) (wTail c i), unitF_hh]
    rfl
  have hG : Measurable (fun T => rowG φ (s * alphaE c i) (√(1 - s^2))
      (√(normSq (wTail c i))) T) :=
    hφ.comp (measurable_const.add (measurable_const.mul (measurable_const.mul measurable_id)))
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_rot ((√(normSq (wTail c i)))⁻¹ • wTail c i)
      (F := fun v => rowG φ (s * alphaE c i) (√(1 - s^2)) (√(normSq (wTail c i)))
        (unitF53 v ⟨0, by omega⟩))
      (hG.comp ((measurable_pi_apply _).comp measurable_unitF))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [rowG, kappaE_eq (by omega : 1 ≤ n), mul_assoc]

/-- **V3b (first moment).** -/
theorem a1Bar_reduce (hn : 2 ≤ n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    a1Bar c s i = ∫ v, relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
      unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n - 1)) :=
  row_reduce hn c s i relu measurable_relu

/-- **V3b (second moment).** -/
theorem e1Bar_reduce (hn : 2 ≤ n) (c : Ret n) (s : ℝ) (i : Fin (mA n)) :
    e1Bar c s i = ∫ v, relu (s * alphaE c i + √(1 - s ^ 2) * kappaE c i *
      unitF53 v ⟨0, by omega⟩) ^ 2 ∂stdGauss (Fin (n - 1)) :=
  row_reduce hn c s i (fun x => relu x ^ 2) (measurable_relu.pow_const 2)

end BstLean.Part272

#print axioms BstLean.Part272.a1Bar_reduce
#print axioms BstLean.Part272.e1Bar_reduce
