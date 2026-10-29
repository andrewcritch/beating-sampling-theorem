import BstLean.Part228Certified
import BstLean.Part228Window

/-! The certified normalized root bounds the existing retained-network root. -/
namespace BstLean.Part228
open Real MeasureTheory
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 BstLean.Part161

theorem chernoffExponent_normalized_scale (n : ℕ) {a τ θ b u : ℝ}
    (hτ : τ ≠ 0) (hθ : θ ≠ 0)
    (hratio : a^2 * θ = n*τ^2*(1-θ)) :
    chernoffExponent n a τ b (u/(2*τ^2)) = normalizedExponent n θ b u := by
  have ha : 2*(u/(2*τ^2))*τ^2 = u := by field_simp
  have hb : 2*(u/(2*τ^2))*endpointRatio b*τ^2 = endpointRatio b*u := by
    field_simp
  unfold chernoffExponent normalizedExponent
  rw [ha, hb]
  have he : u/(2*τ^2)*a^2/(1-u) = n*(1-θ)*u/(2*θ*(1-u)) := by
    have hr : a^2/τ^2 = n*(1-θ)/θ := by
      apply (div_eq_div_iff (pow_ne_zero 2 hτ) hθ).mpr
      nlinarith only [hratio]
    calc
      _ = (a^2/τ^2)*u/(2*(1-u)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [hr]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  rw [he]
  ring

theorem frontierTailRoot_normalized {n : ℕ} (hn : 4096 ≤ n) (D : Design n) (c : Ret n)
    (hW : WINDOW D c) :
    frontierTailRoot D c =
      √(2*normalizedTailMass n
        (n*D.tau0 c^2/(normSq c.1.2+n*D.tau0 c^2))
        (√(1-n*D.tau0 c^2/(normSq c.1.2+n*D.tau0 c^2)) -
          6*√((n*D.tau0 c^2/(normSq c.1.2+n*D.tau0 c^2))/n))
        (√(1-n*D.tau0 c^2/(normSq c.1.2+n*D.tau0 c^2)) +
          6*√((n*D.tau0 c^2/(normSq c.1.2+n*D.tau0 c^2))/n))
        (-(8/√(n : ℝ))) (8/√(n : ℝ))) := by
  let a : ℝ := √(normSq c.1.2)
  let τ : ℝ := D.tau0 c
  let S : ℝ := normSq c.1.2+n*τ^2
  let θ : ℝ := n*τ^2/S
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hτ : 0 < τ := hW.2.1
  have hS : 0 < S := add_pos_of_nonneg_of_pos (normSq_nonneg _)
    (mul_pos hn0 (sq_pos_of_pos hτ))
  have hθ : 0 < θ := div_pos (mul_pos hn0 (sq_pos_of_pos hτ)) hS
  have ha : a^2 = normSq c.1.2 := sq_sqrt (normSq_nonneg _)
  have h1 : 1-θ = a^2/S := by
    dsimp only [θ]
    field_simp [hS.ne']
    dsimp only [S]
    rw [ha]
    ring
  have h2 : θ/n = τ^2/S := by dsimp [θ]; field_simp
  have hcentre : √(1-θ) = a/√S := by
    rw [h1, sqrt_div (sq_nonneg a), sqrt_sq (sqrt_nonneg _)]
  have hscale : √(θ/n) = τ/√S := by
    rw [h2, sqrt_div (sq_nonneg τ), sqrt_sq hτ.le]
  have hlo : bulkLower D c = √(1-θ)-6*√(θ/n) := by
    rw [hcentre, hscale]
    dsimp [bulkLower, a, S, τ]
    ring
  have hhi : bulkUpper D c = √(1-θ)+6*√(θ/n) := by
    rw [hcentre, hscale]
    dsimp [bulkUpper, a, S, τ]
    ring
  have hratio : a^2*θ = n*τ^2*(1-θ) := by rw [h1]; dsimp [θ]; ring
  have hex : a^2/(2*τ^2) = n*(1-θ)/(2*θ) := by
    apply (div_eq_div_iff (by positivity : (2*τ^2:ℝ) ≠ 0)
      (by positivity : (2*θ:ℝ) ≠ 0)).mpr
    nlinarith only [hratio]
  have hd := bulk_domain_explicit hn D c hW
  unfold frontierTailRoot bulkTailRoot bulkTailMass latitudeTailMass
  rw [chernoffMajorant_eq_exp n hd.lower_axial hd.lower_transverse,
    chernoffMajorant_eq_exp n hd.upper_axial hd.upper_transverse]
  change √(2*(exp (-(a^2/(2*τ^2))) +
    exp (chernoffExponent n a τ (bulkLower D c) (-(8/√(n : ℝ))/(2*τ^2))) +
    exp (chernoffExponent n a τ (bulkUpper D c) ((8/√(n : ℝ))/(2*τ^2))))) = _
  rw [chernoffExponent_normalized_scale n hτ.ne' hθ.ne' hratio,
    chernoffExponent_normalized_scale n hτ.ne' hθ.ne' hratio, hex, hlo, hhi]
  rfl

/-- The existing actual root is below the cap throughout the new dimension range. -/
theorem frontierTailRoot_lt {n : ℕ} (hn : 8000 ≤ n) (D : Design n) (c : Ret n)
    (hW : WINDOW D c) : frontierTailRoot D c < 1/10^8 := by
  rw [frontierTailRoot_normalized (by omega) D c hW]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hS : 0 < normSq c.1.2+n*D.tau0 c^2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg _)
      (mul_pos hn0 (sq_pos_of_pos hW.2.1))
  exact normalized_bulk_root_lt hn ((le_div_iff₀ hS).mpr hW.2.2.1)
    ((div_le_iff₀ hS).mpr hW.2.2.2)

/-- The replacement statement retains the actual root and supplies its cap separately. -/
theorem replacement_root_certified {n : ℕ} (hn : 8000 ≤ n) (D : Design n) (t : ℝ)
    (c : Ret n) (hW : WINDOW D c) (d : SplitData n) {ε δ slow hfl hb : ℝ}
    (hF : FLUCT_chi_hyp D c d ε δ slow hfl) (hB : BIAS_hyp D c d hb) :
    |√(QStand D t c)-√(qTilde D t c)| ≤ hfl+hb+frontierTailRoot D c ∧
      frontierTailRoot D c < 1/10^8 :=
  ⟨replacement_root_frontier (by omega) D t c hW d hF hB,
    frontierTailRoot_lt hn D c hW⟩

end BstLean.Part228
