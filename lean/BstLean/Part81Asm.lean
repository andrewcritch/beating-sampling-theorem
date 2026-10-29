import BstLean.Part81Core
import BstLean.Part81Num
import BstLean.Part81Var4
import BstLean.Part81KerGen
import BstLean.Part81KD
import BstLean.Part78Final3

/-!
# Part 81: assembly — from the mean bounds and the variance bound to the failure probability on the
coefficient sphere, map degree `d ≥ 2`, radius level `δ = 1/n`
-/

namespace BstLean.Part81

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU)
open BstLean.Part59 (polyEval TopNZ g0Q BP varP)
open BstLean.Part78 (nsq frobH trH)

/-- **Assembly, `d ≥ 2`**: radius level `1/n`, `TQ = t n`, `T2 = n`. -/
theorem fail81_asm (n d : ℕ) (hn : 100 ≤ n) (hd : 2 ≤ d)
    {α β M1 E2 UA Uv cW c1 κ ε ε₁ lam t : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hM1 : 0 ≤ M1) (hE2 : 0 ≤ E2) (hUA : 0 ≤ UA) (hUv : 0 ≤ Uv)
    (hM : MB n d α β M1 E2 UA Uv) (hV : VarBoundW n d α β cW) (hcW : 0 ≤ cW)
    (hc1 : M1 ≤ c1 * α) (hc1' : E2 ≤ c1 * β) (hc10 : 0 ≤ c1)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1) (ht : 0 < t)
    (hnum : 11 / 10 * ε₁ ^ 2 + (22 + 22 * (409 / 100) * eD d ^ 2 + ε ^ 2 * t / lam) *
        (1 / (n : ℝ)) / β ≤ ε ^ 2 * (1 - lam) * κ)
    (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n d 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal ((4 + c1 / ε₁ ^ 2 + cW / (1 - κ) ^ 2 + (4 * UA + Uv) / t +
        (4 * M1 + E2) * (1 / (n : ℝ))) * (1 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn1
  have hDge := DD_ge_of_two_le n d hd
  have hδ0 : (0 : ℝ) < 1 / n := by positivity
  have hδ : (1 : ℝ) / n ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have h1κ : 0 < 1 - κ := by linarith
  have key := fail81_core n d hn1 (δ := 1 / (n : ℝ)) (TQ := t * n) (T2 := n) (ε := ε) hα hβ hM1 hE2
    hUA hUv hM hV hcW hc1 hc1' hc10 hκ0 hκ hε₁ hlam0 hlam1 (by positivity) hnpos hδ0 hδ
    (by
      have e : (11 / 10 * ε₁ ^ 2 + (22 * (1 / (n : ℝ)) ^ 2 * n +
          22 * (409 / 100) * eD d ^ 2 * (1 / (n : ℝ)) ^ 2 * (n : ℝ) +
          ε ^ 2 * (1 / (n : ℝ)) ^ 2 * (t * n) / lam) / β) =
          11 / 10 * ε₁ ^ 2 + (22 + 22 * (409 / 100) * eD d ^ 2 + ε ^ 2 * t / lam) *
            (1 / (n : ℝ)) / β := by
        field_simp
      rw [e]; exact hnum) c hc
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have t1 : 2 / DD n d / (1 / (n : ℝ)) ^ 2 ≤ 4 * (1 / n) := by
    have e : 2 / DD n d / (1 / (n : ℝ)) ^ 2 = 2 * (n : ℝ) ^ 2 / DD n d := by
      field_simp
    rw [e, div_le_iff₀ hD]
    have h2 : 4 * (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) ≤
        4 * (1 / (n : ℝ)) * DD n d := mul_le_mul_of_nonneg_left hDge (by positivity)
    have h3 : 4 * (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) =
        2 * (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by field_simp; ring
    nlinarith
  have t2 : c1 / (n * ε₁ ^ 2) = c1 / ε₁ ^ 2 * (1 / n) := by field_simp
  have t3 : cW / (n * (1 - κ) ^ 2) = cW / (1 - κ) ^ 2 * (1 / n) := by field_simp
  have t4 : (4 * UA + Uv) / (t * n) = (4 * UA + Uv) / t * (1 / n) := by field_simp
  have t5 : (4 * M1 + E2) / (n * (n : ℝ)) = (4 * M1 + E2) * (1 / n) * (1 / n) := by field_simp
  rw [t2, t3, t4, t5]
  linarith

end BstLean.Part81

#print axioms BstLean.Part81.fail81_asm
