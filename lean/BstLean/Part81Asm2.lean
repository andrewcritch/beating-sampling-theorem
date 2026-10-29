import BstLean.Part81CoreW
import BstLean.Part81Rad
import BstLean.Part81Asm

/-!
# Part 81: assembly with the eighth-moment radius tail and adjustable weights, map degree `d ≥ 2`

Radius level `δ = 1/(k n)`, `TQ = t n`, `T2 = n`. The radius term is `27200 k⁸/n⁴`.
-/

namespace BstLean.Part81

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU)
open BstLean.Part59 (polyEval TopNZ g0Q BP varP)
open BstLean.Part78 (nsq frobH trH)

theorem fail81_asm2 (n d : ℕ) (hn : 100 ≤ n) (hd : 2 ≤ d)
    {α β M1 E2 UA Uv cW c1 κ ε ε₁ lam t μ k : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hM1 : 0 ≤ M1) (hE2 : 0 ≤ E2) (hUA : 0 ≤ UA) (hUv : 0 ≤ Uv)
    (hM : MB n d α β M1 E2 UA Uv) (hV : VarBoundW n d α β cW) (hcW : 0 ≤ cW)
    (hc1 : M1 ≤ c1 * α) (hc1' : E2 ≤ c1 * β) (hc10 : 0 ≤ c1)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1) (ht : 0 < t)
    (hμ : 0 < μ) (hk : 1 ≤ k)
    (hnum : (1 + μ) * ε₁ ^ 2 + (2 * (1 + 1 / μ) * (1 + 409 / 100 * eD d ^ 2) + ε ^ 2 * t / lam) *
        (1 / (k ^ 2 * (n : ℝ))) / β ≤ ε ^ 2 * (1 - lam) * κ)
    (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
      ε ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n d 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal ((27200 * k ^ 8 * (1 / (n : ℝ)) ^ 3 + c1 / ε₁ ^ 2 + cW / (1 - κ) ^ 2 +
        (4 * UA + Uv) / t + (4 * M1 + E2) * (1 / (n : ℝ))) * (1 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hk0 : 0 < k := by linarith
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn1
  have hDge := DD_ge_of_two_le n d hd
  have hD3 : (n : ℝ) ^ 3 / 2 ≤ DD n d := by
    refine le_trans ?_ hDge
    nlinarith [mul_pos hnpos hnpos]
  have hD4000 : 4000 ≤ DD n d := by
    refine le_trans ?_ hD3
    have : (100 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn' 3
    linarith
  have hδ0 : (0 : ℝ) < 1 / (k * n) := by positivity
  have hδ : (1 : ℝ) / (k * n) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h1κ : 0 < 1 - κ := by linarith
  have hRad0 : 0 ≤ 1700 / DD n d ^ 4 / (1 / (k * (n : ℝ))) ^ 8 := by positivity
  have key := fail81_coreW n d hn1 (δ := 1 / (k * (n : ℝ))) (TQ := t * n) (T2 := n) (ε := ε)
    (μ := μ) hα hβ hM1 hE2 hUA hUv hM hV hcW hc1 hc1' hc10 hκ0 hκ hε₁ hlam0 hlam1 (by positivity)
    hnpos hδ0 hδ hμ hRad0 (radTail8 n d hn1 hD4000 _ hδ0)
    (by
      have e : ((1 + μ) * ε₁ ^ 2 + (2 * (1 + 1 / μ) * ((1 / (k * (n : ℝ))) ^ 2 * n +
          (409 / 100) * eD d ^ 2 * (1 / (k * (n : ℝ))) ^ 2 * (n : ℝ)) +
          ε ^ 2 * (1 / (k * (n : ℝ))) ^ 2 * (t * n) / lam) / β) =
          (1 + μ) * ε₁ ^ 2 + (2 * (1 + 1 / μ) * (1 + 409 / 100 * eD d ^ 2) + ε ^ 2 * t / lam) *
            (1 / (k ^ 2 * (n : ℝ))) / β := by
        field_simp
      rw [e]; exact hnum) c hc
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have t1 : 1700 / DD n d ^ 4 / (1 / (k * (n : ℝ))) ^ 8 ≤
      27200 * k ^ 8 * (1 / (n : ℝ)) ^ 3 * (1 / n) := by
    have e : 1700 / DD n d ^ 4 / (1 / (k * (n : ℝ))) ^ 8 = 1700 * k ^ 8 * (n : ℝ) ^ 8 / DD n d ^ 4 := by
      field_simp
    have hD4 : ((n : ℝ) ^ 3 / 2) ^ 4 ≤ DD n d ^ 4 := pow_le_pow_left₀ (by positivity) hD3 4
    rw [e, div_le_iff₀ (by positivity)]
    have h2 : 27200 * k ^ 8 * (1 / (n : ℝ)) ^ 3 * (1 / n) * ((n : ℝ) ^ 3 / 2) ^ 4 ≤
        27200 * k ^ 8 * (1 / (n : ℝ)) ^ 3 * (1 / n) * DD n d ^ 4 :=
      mul_le_mul_of_nonneg_left hD4 (by positivity)
    have h3 : 27200 * k ^ 8 * (1 / (n : ℝ)) ^ 3 * (1 / n) * ((n : ℝ) ^ 3 / 2) ^ 4 =
        1700 * k ^ 8 * (n : ℝ) ^ 8 := by field_simp; ring
    linarith
  have t2 : c1 / (n * ε₁ ^ 2) = c1 / ε₁ ^ 2 * (1 / n) := by field_simp
  have t3 : cW / (n * (1 - κ) ^ 2) = cW / (1 - κ) ^ 2 * (1 / n) := by field_simp
  have t4 : (4 * UA + Uv) / (t * n) = (4 * UA + Uv) / t * (1 / n) := by field_simp
  have t5 : (4 * M1 + E2) / (n * (n : ℝ)) = (4 * M1 + E2) * (1 / n) * (1 / n) := by field_simp
  rw [t2, t3, t4, t5]
  linarith

end BstLean.Part81

#print axioms BstLean.Part81.fail81_asm2
