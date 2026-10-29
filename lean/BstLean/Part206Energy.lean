import BstLean.Part206Transfer
import BstLean.Part154Lip

/-! Retained-data energy reductions for the actual oracle centre. The second
layer distribution is integrated in full before any event is applied. -/
namespace BstLean.Part206
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130
open BstLean.Part150 (gO hO bO)
open BstLean.Part153 (nrm Pb)

/-- Jensen for a real mean under a probability distribution. -/
theorem mean_sq_le_second {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hi : Integrable f μ)
    (hi2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let e := ∫ x, f x ∂μ
  have h0 : 0 ≤ ∫ x, (f x - e) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (f x - e))
  have he : (fun x => (f x - e) ^ 2) =
      fun x => f x ^ 2 - 2 * e * f x + e ^ 2 := by funext x; ring
  rw [he, integral_add (f := fun x => f x ^ 2 - 2 * e * f x)
    (g := fun _ => e ^ 2) (hi2.sub (hi.const_mul (2 * e))) (integrable_const _),
    integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * e * f x)
      hi2 (hi.const_mul (2 * e)), integral_const_mul, integral_const] at h0
  simp only [probReal_univ, one_smul] at h0
  change e ^ 2 ≤ _
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * e * e + e ^ 2 at h0
  nlinarith

/-- The kernel energy increases with its mean energy coordinate. -/
theorem kernel_energy_upper {G B scale gUpper rUpper : ℝ}
    (hG : 0 < G) (hB : 0 ≤ B) (hBG : B ≤ G)
    (hscale : 0 ≤ scale) (hUpper : G ≤ scale * gUpper)
    (hr : B / G ≤ rUpper) (hr1 : rUpper ≤ 1) :
    G * kappa (B / G) ≤ scale * gUpper * kappa rUpper := by
  have hr0 : 0 ≤ B / G := div_nonneg hB hG.le
  have hrG : B / G ≤ 1 := (div_le_one hG).mpr hBG
  have hk := kappa_monotoneOn ⟨by linarith, hrG⟩ ⟨by linarith, hr1⟩ hr
  have hk0 := (kappa_mem (by linarith : -1 ≤ rUpper) hr1).1
  exact (mul_le_mul_of_nonneg_left hk hG.le).trans
    (mul_le_mul_of_nonneg_right hUpper hk0)

/-- An upper energy and a mean-energy ratio bound control the actual second moment. -/
theorem oracle_second_upper {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {scale gUpper rUpper : ℝ} (hG : 0 < gO A c τ)
    (hscale : 0 ≤ scale) (hUpper : gO A c τ ≤ scale * gUpper)
    (hr : (2 / (m : ℝ) * normSq (hO A c τ)) / gO A c τ ≤ rUpper)
    (hr1 : rUpper ≤ 1) :
    (∫ M, Pb A c τ M ^ 2 ∂gaussMat m m (2 / (m : ℝ))) ≤
      scale * gUpper * kappa rUpper := by
  rw [(BstLean.Part153.rb_eq hm A c τ).2]
  exact kernel_energy_upper hG (BstLean.Part153.GamBar_nonneg A c τ)
    (BstLean.Part153.GamBar_le A c τ) hscale hUpper hr hr1

/-- The upper bound uses the original mean-threshold event, not a new event. -/
theorem oracle_energy_upper {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) {scale gUpper rUpper dev : ℝ}
    (hG : 0 < gO A c τ) (hscale : 0 ≤ scale)
    (hUpper : gO A c τ ≤ scale * gUpper)
    (hr : (2 / (m : ℝ) * normSq (hO A c τ)) / gO A c τ ≤ rUpper)
    (hr1 : rUpper ≤ 1)
    (hEvent : Pb A c τ M ≤ (∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ))) + dev) :
    Pb A c τ M ≤ √(scale * gUpper * kappa rUpper) + dev := by
  have hi := (BstLean.Part154.Pb_var hm A c τ).1
  have hi2 := (BstLean.Part153.rb_eq hm A c τ).1
  have hJ := mean_sq_le_second hi hi2
  have hS := oracle_second_upper hm A c τ hG hscale hUpper hr hr1
  have hmean : (∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ))) ≤
      √(scale * gUpper * kappa rUpper) := by
    have hsq := hJ.trans hS
    have hnn : 0 ≤ (∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ))) :=
      integral_nonneg (BstLean.Part153.Pb_nonneg A c τ)
    have hb : 0 ≤ scale * gUpper * kappa rUpper := (sq_nonneg _).trans hsq
    nlinarith [sq_sqrt hb, sqrt_nonneg (scale * gUpper * kappa rUpper)]
  linarith

/-- The lower mean retains the variance correction inside the kernel bracket. -/
theorem oracle_mean_lower {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    {scale gLower rLower : ℝ} (hG : 0 < gO A c τ)
    (hscale : 0 ≤ scale) (hLower : scale * gLower ≤ gO A c τ)
    (hr0 : -1 ≤ rLower)
    (hr : rLower ≤ (2 / (m : ℝ) * normSq (hO A c τ)) / gO A c τ)
    (hBracket : 0 ≤ kappa rLower - 2 / (m : ℝ)) :
    √(scale * gLower * (kappa rLower - 2 / (m : ℝ))) ≤
      ∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ)) := by
  obtain ⟨_, _, hv⟩ := BstLean.Part154.Pb_var hm A c τ
  rw [BstLean.Part153.GamS_eq_gO hm, (BstLean.Part153.rb_eq hm A c τ).2] at hv
  have hratio1 : (2 / (m : ℝ) * normSq (hO A c τ)) / gO A c τ ≤ 1 :=
    (div_le_one hG).mpr (BstLean.Part153.GamBar_le A c τ)
  have hratio0 := div_nonneg (BstLean.Part153.GamBar_nonneg A c τ) hG.le
  have hk := kappa_monotoneOn ⟨hr0, hr.trans hratio1⟩
    ⟨by linarith, hratio1⟩ hr
  have h1 := mul_le_mul_of_nonneg_left hk hG.le
  have h2 := mul_le_mul_of_nonneg_right hLower hBracket
  have hs : scale * gLower * (kappa rLower - 2 / (m : ℝ)) ≤
      (∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ))) ^ 2 := by nlinarith
  have hmean : 0 ≤ ∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ)) :=
    integral_nonneg (BstLean.Part153.Pb_nonneg A c τ)
  exact (sqrt_le_sqrt hs).trans_eq (sqrt_sq hmean)

/-- A finite centre perturbation transfers upper and lower energy roots. -/
theorem energy_roots_transfer {k : ℕ} (bo b : Fin k → ℝ)
    {s lower upper finite : ℝ} (hs : 0 ≤ s)
    (hLower : lower ≤ s * nrm bo) (hUpper : s * nrm bo ≤ upper)
    (hFinite : s * nrm (b - bo) ≤ finite) (hGuard : 0 ≤ lower - finite) :
    (lower - finite) ^ 2 ≤ s ^ 2 * normSq b ∧
    s ^ 2 * normSq b ≤ (upper + finite) ^ 2 := by
  have h := abs_le.mp (BstLean.Part153.abs_nrm_sub_le b bo)
  have h1 := mul_le_mul_of_nonneg_left h.1 hs
  have h2 := mul_le_mul_of_nonneg_left h.2 hs
  have hl : lower - finite ≤ s * nrm b := by linarith
  have hu : s * nrm b ≤ upper + finite := by linarith
  have hl2 := pow_le_pow_left₀ hGuard hl 2
  have hu2 := pow_le_pow_left₀ (mul_nonneg hs (BstLean.Part153.nrm_nonneg b)) hu 2
  simpa only [mul_pow, BstLean.Part153.nrm_sq] using And.intro hl2 hu2

/-- The actual computed centre has the lower energy bound with a checked root guard. -/
theorem lower_energy_actual {n m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ)
    {scale gLower rLower dev finite : ℝ} (hs : 0 < scale)
    (hG : 0 < gO A c τ) (hLower : scale * gLower ≤ gO A c τ)
    (hr0 : -1 ≤ rLower)
    (hr : rLower ≤ (2 / (m : ℝ) * normSq (hO A c τ)) / gO A c τ)
    (hBracket : 0 ≤ kappa rLower - 2 / (m : ℝ))
    (hEvent : (∫ M, Pb A c τ M ∂gaussMat m m (2 / (m : ℝ))) - dev ≤ Pb A c τ M)
    (hFinite : √(2 / (m : ℝ)) / √scale * nrm (b - bO A M c τ) ≤ finite)
    (hGuard : 0 ≤ √(gLower * (kappa rLower - 2 / (m : ℝ))) - dev / √scale - finite) :
    (√(gLower * (kappa rLower - 2 / (m : ℝ))) - dev / √scale - finite) ^ 2 ≤
      (2 / (m : ℝ)) * normSq b / scale := by
  have hMean := oracle_mean_lower hm A c τ hG hs.le hLower hr0 hr hBracket
  rw [mul_assoc, sqrt_mul hs.le] at hMean
  have he : √(2 / (m : ℝ)) / √scale * nrm (bO A M c τ) = Pb A c τ M / √scale := by
    unfold Pb
    ring
  have hO : √(gLower * (kappa rLower - 2 / (m : ℝ))) - dev / √scale ≤
      √(2 / (m : ℝ)) / √scale * nrm (bO A M c τ) := by
    rw [he, le_div_iff₀ (sqrt_pos.mpr hs)]
    have he' : (√(gLower * (kappa rLower - 2 / (m : ℝ))) - dev / √scale) * √scale =
        √scale * √(gLower * (kappa rLower - 2 / (m : ℝ))) - dev := by
      field_simp
    rw [he']
    linarith
  have hNorm := mul_le_mul_of_nonneg_left
    (abs_le.mp (BstLean.Part153.abs_nrm_sub_le b (bO A M c τ))).1
    (show 0 ≤ √(2 / (m : ℝ)) / √scale by positivity)
  have hB : √(gLower * (kappa rLower - 2 / (m : ℝ))) - dev / √scale - finite ≤
      √(2 / (m : ℝ)) / √scale * nrm b := by linarith
  have hB2 := pow_le_pow_left₀ hGuard hB 2
  simpa only [mul_pow, div_pow, sq_sqrt (by positivity : 0 ≤ (2 : ℝ) / m),
    sq_sqrt hs.le, BstLean.Part153.nrm_sq, div_mul_eq_mul_div] using hB2

#print axioms mean_sq_le_second
#print axioms kernel_energy_upper
#print axioms oracle_second_upper
#print axioms oracle_energy_upper
#print axioms oracle_mean_lower
#print axioms energy_roots_transfer
#print axioms lower_energy_actual
end BstLean.Part206
