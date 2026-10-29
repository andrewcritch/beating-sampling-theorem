import BstLean.Part81Defs
import BstLean.Part81K3
import BstLean.Part81UX
import BstLean.Part78Sharp
import BstLean.Part78Final

/-!
# Part 81, the kernel constants at map degree `d = 2`

The degree-`d` objects of `Part81Defs` coincide at `d = 2` with the objects of `Part78Defs`.
This file transfers the Part 78 results, and proves the sharper variance bound
`kk2 − tG² ≤ 15/(4(n+2)(n+4)) ≤ 15/(4n²)`.
-/

namespace BstLean.Part81.K2

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part81 BstLean.Part81.K3

variable {n : ℕ}

lemma kap_two (x y : Fin n → ℝ) : kap 2 x y = BstLean.Part78.kap x y := rfl

lemma tG_two (n : ℕ) : tG n 2 = BstLean.Part78.tG n := rfl

lemma mm1_two (n : ℕ) : mm1 n 2 = BstLean.Part78.mm1 n := rfl

lemma kk2_two (n : ℕ) : kk2 n 2 = BstLean.Part78.kk2 n := rfl

lemma ss2_two (n : ℕ) : ss2 n 2 = BstLean.Part78.ss2 n := rfl

lemma featOp_two (n : ℕ) (CF : ℝ) : FeatOp n 2 CF ↔ BstLean.Part78.FeatOp n CF := Iff.rfl

/-- `kk2 − tG² ≤ 15/(4(n+2)(n+4))`. -/
lemma kk2_var (hn : 1 ≤ n) :
    BstLean.Part78.kk2 n - BstLean.Part78.tG n ^ 2
      ≤ 15 / 4 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have kc : Continuous (fun x : Fin n → ℝ => BstLean.Part78.kap x x) :=
    BstLean.Part78.kap_diag_cont
  have iK : Integrable (fun x : Fin n → ℝ => BstLean.Part78.kap x x) (uniformSphere n) :=
    BstLean.Part78.sph_int hn kc
  have iK2 : Integrable (fun x : Fin n → ℝ => BstLean.Part78.kap x x ^ 2) (uniformSphere n) :=
    BstLean.Part78.sph_int hn (kc.pow 2)
  have ex : ∀ c : ℝ, ∫ x, (BstLean.Part78.kap x x - c) ^ 2 ∂uniformSphere n
      = BstLean.Part78.kk2 n - 2 * c * BstLean.Part78.tG n + c ^ 2 := by
    intro c
    have e : ∀ x : Fin n → ℝ, (BstLean.Part78.kap x x - c) ^ 2
        = BstLean.Part78.kap x x ^ 2 - 2 * c * BstLean.Part78.kap x x + c ^ 2 :=
      fun x => by ring
    simp_rw [e]
    have hA : ∫ x, (BstLean.Part78.kap x x ^ 2 - 2 * c * BstLean.Part78.kap x x + c ^ 2)
          ∂uniformSphere n
        = ∫ x, (BstLean.Part78.kap x x ^ 2 - 2 * c * BstLean.Part78.kap x x) ∂uniformSphere n
          + ∫ _x : Fin n → ℝ, c ^ 2 ∂uniformSphere n :=
      integral_add (iK2.sub (iK.const_mul _)) (integrable_const _)
    have hB : ∫ x, (BstLean.Part78.kap x x ^ 2 - 2 * c * BstLean.Part78.kap x x) ∂uniformSphere n
        = ∫ x, BstLean.Part78.kap x x ^ 2 ∂uniformSphere n
          - ∫ x, 2 * c * BstLean.Part78.kap x x ∂uniformSphere n :=
      integral_sub iK2 (iK.const_mul _)
    rw [hA, hB, integral_const_mul]
    simp [BstLean.Part78.kk2, BstLean.Part78.tG]
  have h := ex (3 / 2)
  have hle : ∫ x, (BstLean.Part78.kap x x - 3 / 2) ^ 2 ∂uniformSphere n
      ≤ ∫ x, 1 / 4 * q6 x ∂uniformSphere n := by
    apply integral_mono_ae
      (BstLean.Part78.sph_int hn ((kc.sub continuous_const).pow 2))
      ((BstLean.Part78.sph_int hn q6_cont).const_mul _)
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    show (BstLean.Part78.kap x x - 3 / 2) ^ 2 ≤ 1 / 4 * q6 x
    rw [BstLean.Part78.kap_diag_sphere x hx]
    have a3 := q4_sq_le_q6 x hx
    nlinarith
  rw [integral_const_mul, integral_q6 hn] at hle
  have e3 : (1 / 4 : ℝ) * (15 / (((n : ℝ) + 2) * ((n : ℝ) + 4)))
      = 15 / 4 / (((n : ℝ) + 2) * ((n : ℝ) + 4)) := by ring
  rw [e3] at hle
  nlinarith [sq_nonneg (BstLean.Part78.tG n - 3 / 2)]

end BstLean.Part81.K2

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part81.K2 BstLean.Part81.K3

/-- **Feature operator bound at `d = 2`**, with constant `1`. -/
theorem featOp2 (n : ℕ) (hn : 1 ≤ n) : FeatOp n 2 1 :=
  (featOp_two n 1).mpr (BstLean.Part78.featOp1 n hn)

/-- **Sphere constants at `d = 2`.** -/
theorem sphC2 (n : ℕ) (hn : 1000 ≤ n) :
    SphC n 2 1 (501 / 500) (3 / 2) (15 / (4 * (n : ℝ))) 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨htG, hmm, hk, -, hs0, hs, -⟩ := BstLean.Part78.part78_sphere n hn
  have hvar := K2.kk2_var hn1
  have hB : 3 / (2 * ((n : ℝ) + 2)) ≤ 3 / 2 / (n : ℝ) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpos : 0 ≤ 3 / (2 * ((n : ℝ) + 2)) := by positivity
  rw [SphC, eD_two, tG_two, mm1_two, kk2_two, ss2_two]
  refine ⟨?_, ?_, ?_, ?_, hs0, hs, hk, ?_, ?_⟩
  · rw [htG]; linarith
  · rw [htG]; linarith
  · rw [hmm]; positivity
  · rw [hmm]
  · refine hvar.trans ?_
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro x hx
    have hd := BstLean.Part78.kap_diag_sphere x hx
    have a3 := BstLean.Part78.q4_le_one x hx
    have a4 := BstLean.Part78.q4_nonneg x
    have hin := BstLean.Part78.inner_kap hn1 x
    rw [hx] at hin
    have h1n : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]; linarith
    have h1p : 0 ≤ 1 / (n : ℝ) := by positivity
    simp only [kap_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd]; linarith
    · rw [hd]; linarith
    · rw [hin]; exact h1p
    · rw [hin, hd]; linarith

end BstLean.Part81

#print axioms BstLean.Part81.featOp2
#print axioms BstLean.Part81.sphC2
