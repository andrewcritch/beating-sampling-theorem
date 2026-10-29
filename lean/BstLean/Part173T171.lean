import BstLean.Part173T170
import BstLean.Part171All

/-!
# Part 173 (file `T171`): Part 171's results that need `n ≥ 80 000`, re-proved for `n ≥ 59 000`

No proof is left open; no `native_decide` or `axiom` is used.

This file was made by copying every theorem of Part 171 whose statement or proof uses `80000`,
replacing `80000` by `59000` and the tag `80k` by `59k`, and then repairing the proofs that fail.
The copies live in `BstLean.Part173.N59` and shadow the originals there; definitions are NOT copied
(the copies use Part 171's definitions; the only new definition of this chain is `roomE59`). The
docstrings are Part 171's, with `80 000` replaced by `59 000`; other numbers in the docstrings can
be Part 171's. The Lean statements are authoritative.

Changed constants: `√n ≥ 242` in `r_facts`; `numF`, `BiasMomF`: `B_f = 0.0047` (`270/n`); `numW`, `BiasMomW`: `B_ω = 0.0048` (`280/n`); statistics charge `≤ 10⁻⁴`; the linear condition `A_ω + 8.08A_f ≤ 0.620`; the room `roomE59`.
-/

namespace BstLean.Part173.N59

-- ===== from Part171Stat.lean =====
section SPart171Stat
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (biasF biasW tA BiasMomF BiasMomW opSet windowW mkR node_bulk)
variable {n : ℕ}
/-- **The location bias moments on the statistics event.** -/
theorem biasMomF_of_stat (hn : 59000 ≤ n) {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
    (hSm : 0 < Smin) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n Smin Smax Dm Hm Vm Pm) {z₁ z₂ : ℝ} (hz1 : 0 < z₁) (hz2 : 0 < z₂)
    (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hA0 : 0 < AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 < AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 < AF2 √Smin Dm) {B : ℝ}
    (hB : ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AF1 √Smin Dm Vm Pm (√(tA n) * O) * z₁ + AF2 √Smin Dm * z₂) ^ 8 ≤ B ^ 8) :
    BiasMomF O Gb B := by
  intro wr hw g hg A₁ hA₁ hG
  have hn1 : 1 ≤ n := by omega
  set c := mkR wr (A₁, 0)
  have hs := node_bulk hn hw (A₁, 0) hg
  have h1 : OpB (A1 c) O := hA₁
  have H := hGb hG g hg
  set A₀ := AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  set A₁' := AF1 √Smin Dm Vm Pm (√(tA n) * O)
  set A₂ := AF2 √Smin Dm
  set K := (n : ℝ) ^ 4 * ((mA n : ℕ) : ℝ) ^ 3
  have hK : 0 ≤ K := by positivity
  set F : Fin (mA n) → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → ℝ := fun j p =>
    (A₀ + A₁' * √(p.1 j ^ 2 + p.2 j ^ 2) + A₂ * √(p.1 j ^ 2 + p.2 j ^ 2) ^ 2) ^ 8 with hFd
  have hF : ∀ j, Measurable (F j) := fun j => by
    simp only [hFd]
    refine Measurable.pow_const ?_ 8
    have hq : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => p.1 j ^ 2 + p.2 j ^ 2) := by
      fun_prop
    exact (measurable_const.add (measurable_const.mul hq.sqrt)).add
      (measurable_const.mul (hq.sqrt.pow_const 2))
  have hF0 : ∀ j p, 0 ≤ F j p := fun j p => by simp only [hFd]; positivity
  have hQ : 0 ≤ (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8 := by positivity
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasF c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (K * ∑ j, F j (ξ₁, ξ₂)) ∂stdGauss (Fin (mA n))
          ∂stdGauss (Fin (mA n)) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ENNReal.ofReal_le_ofReal ?_
        exact node_biasF hn1 c g hs hO h1 hSm H ξ₁ ξ₂
    _ ≤ ENNReal.ofReal (K * (mA n : ℕ) * (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8) :=
        lint_sum_bound hK hQ hF hF0 fun j => zeta_poly j hA0 hA1 hA2 hz1 hz2 hz1' hz2'
    _ ≤ ENNReal.ofReal (B ^ 8) := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le ?_ hB)
        simp only [K]; ring

/-- **The energy bias moments on the statistics event.** -/
theorem biasMomW_of_stat (hn : 59000 ≤ n) {O : ℝ} (hO : 0 ≤ O) {Smin Smax Dm Hm Vm Pm : ℝ}
    (hSm : 0 < Smin) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEv n Smin Smax Dm Hm Vm Pm) {z₁ z₂ : ℝ} (hz1 : 0 < z₁) (hz2 : 0 < z₂)
    (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hA0 : 0 < AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 < AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) (hA2 : 0 < AW2 Dm Pm (√(tA n) * O))
    {B : ℝ}
    (hB : ((mA n : ℕ) : ℝ) ^ 8 * (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm +
      AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O) * z₁ + AW2 Dm Pm (√(tA n) * O) * z₂) ^ 8 ≤ B ^ 8) :
    BiasMomW O Gb B := by
  intro wr hw g hg A₁ hA₁ hG
  have hn1 : 1 ≤ n := by omega
  set c := mkR wr (A₁, 0)
  have hs := node_bulk hn hw (A₁, 0) hg
  have h1 : OpB (A1 c) O := hA₁
  have H := hGb hG g hg
  set A₀ := AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  set A₁' := AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)
  set A₂ := AW2 Dm Pm (√(tA n) * O)
  set K := ((mA n : ℕ) : ℝ) ^ 7
  have hK : 0 ≤ K := by positivity
  set F : Fin (mA n) → (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) → ℝ := fun j p =>
    (A₀ + A₁' * √(p.1 j ^ 2 + p.2 j ^ 2) + A₂ * √(p.1 j ^ 2 + p.2 j ^ 2) ^ 2) ^ 8 with hFd
  have hF : ∀ j, Measurable (F j) := fun j => by
    simp only [hFd]
    refine Measurable.pow_const ?_ 8
    have hq : Measurable (fun p : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ) => p.1 j ^ 2 + p.2 j ^ 2) := by
      fun_prop
    exact (measurable_const.add (measurable_const.mul hq.sqrt)).add
      (measurable_const.mul (hq.sqrt.pow_const 2))
  have hF0 : ∀ j p, 0 ≤ F j p := fun j p => by simp only [hFd]; positivity
  have hQ : 0 ≤ (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8 := by positivity
  calc ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW c g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n))
      ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (K * ∑ j, F j (ξ₁, ξ₂)) ∂stdGauss (Fin (mA n))
          ∂stdGauss (Fin (mA n)) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ENNReal.ofReal_le_ofReal ?_
        exact node_biasW hn1 c g hs hO h1 hSm H ξ₁ ξ₂
    _ ≤ ENNReal.ofReal (K * (mA n : ℕ) * (A₀ + A₁' * z₁ + A₂ * z₂) ^ 8) :=
        lint_sum_bound hK hQ hF hF0 fun j => zeta_poly j hA0 hA1 hA2 hz1 hz2 hz1' hz2'
    _ ≤ ENNReal.ofReal (B ^ 8) := by
        refine ENNReal.ofReal_le_ofReal (le_of_eq_of_le ?_ hB)
        simp only [K]; ring

end SPart171Stat

-- ===== from Part171Num.lean =====
section SPart171Num
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part170 (tA)
variable {n : ℕ}
/-- The quantities in terms of `r = √n`. -/
lemma r_facts (hn : 59000 ≤ n) :
    242 ≤ √(n : ℝ) ∧ √(n : ℝ) ^ 2 = n ∧
    √(SminN n) = 1 / (√5 * √(n : ℝ)) ∧ √(SmaxN n) = √5 / √(n : ℝ) ∧
    tA n = 2 / √(n : ℝ) ^ 4 ∧ √(tA n) = √2 / √(n : ℝ) ^ 2 ∧
    O1n n = √2 * (√(n : ℝ) + 2) ∧ √(DmN n) = 4 / √(n : ℝ) ^ 3 ∧ √(VmN n) = 8 / √(n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set r := √(n : ℝ) with hrd
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr : 242 ≤ r := by
    rw [hrd, Real.le_sqrt (by norm_num) hn0.le]
    have : (59000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  refine ⟨hr, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SminN
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
  · unfold SmaxN; rw [Real.sqrt_div' _ hn0.le]
  · unfold tA; rw [hmA, ← hr2]; ring
  · unfold tA
    rw [hmA, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hn0.le, ← hr2]
  · unfold O1n
    rw [Real.sqrt_div' _ hn0.le, ← hrd]
    field_simp
    linear_combination (-1 : ℝ) * hr2
  · unfold DmN
    rw [Real.sqrt_div' _ (by positivity), show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), ← hr2, show (r ^ 2) ^ 3 = (r ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  · unfold VmN
    rw [Real.sqrt_div' _ (by positivity), show (64 : ℝ) = 8 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), ← hr2, show (r ^ 2) ^ 4 = (r ^ 4) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]

/-- **The location numerical condition** (`B_f = 0.004`). -/
theorem numF (hn : 59000 ≤ n) :
    0 < AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) ∧
    0 < AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) ∧
    0 < AF2 √(SminN n) (DmN n) ∧
    ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 *
      (AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) +
        AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AF2 √(SminN n) (DmN n) * (754 / 100)) ^ 8 ≤ (47 / 10000) ^ 8 := by
  obtain ⟨hr, hr2, hsm, -, htA, hstA, hO, hD, hV⟩ := r_facts hn
  obtain ⟨h5a, h5b, h2a, h2b⟩ := sqrt_consts
  obtain ⟨hφ0, hφ0', hφ1, hφ1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set r := √(n : ℝ)
  have hr0 : 0 < r := by linarith
  have hs5 : (0 : ℝ) < √5 := by positivity
  have hs2 : (0 : ℝ) < √2 := by positivity
  have h52 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the coefficients in terms of r
  have eΓ : tA n * O1n n ^ 2 + SmaxN n = 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 := by
    rw [htA, hO]; unfold SmaxN; rw [← hr2]; rw [mul_pow, h22]; ring
  have eC : √(tA n) * O1n n = 2 * (r + 2) / r ^ 2 := by
    rw [hstA, hO]; field_simp; rw [h22]
  have eD : DmN n = 16 / r ^ 6 := by unfold DmN; rw [← hr2]; ring
  have eV : VmN n = 64 / r ^ 8 := by unfold VmN; rw [← hr2]; ring
  have eP : PmN n = 1 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
  have hΓle : 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 ≤ 10 / r ^ 2 := by
    have h1 : 4 * (r + 2) ^ 2 / r ^ 4 ≤ 5 / r ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 4 * (r + 2) ^ 2 ≤ 5 * r ^ 2 := by nlinarith
      calc 4 * (r + 2) ^ 2 * r ^ 2 ≤ 5 * r ^ 2 * r ^ 2 := by gcongr
        _ = 5 * r ^ 4 := by ring
    have e : (10 : ℝ) / r ^ 2 = 5 / r ^ 2 + 5 / r ^ 2 := by ring
    linarith
  have hCle : 2 * (r + 2) / r ^ 2 ≤ 3 / r := by
    rw [div_le_div_iff₀ (by positivity) hr0]; nlinarith
  -- A₀
  have eA0 : AF0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) =
      8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 := by
    rw [← AF0_eq _ _ _ _ hs5.ne' hs2.ne' hr0.ne', ← eΓ]
    unfold AF0 AF0'; rw [hsm, eD, eV, eP]
  have eA1 : AF1 √(SminN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) =
      160 * phiG 1 / r ^ 5 + 4 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8 := by
    rw [← AF1_eq _ _ _ _ h52 hr0.ne', ← eC]
    unfold AF1 AF1'; rw [hsm, hD, hV, eP]
  have eA2 : AF2 √(SminN n) (DmN n) = 8 * √2 * √5 * phiG 0 / r ^ 5 := by
    rw [← AF2_eq _ _ _ hs5.ne' hr0.ne']
    unfold AF2 AF2'; rw [hsm, eD]
  rw [eA0, eA1, eA2]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  -- the bound r³·Q ≤ K/r²
  have b0 : 3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 ≤ 1 / r ^ 5 := by
    have h1 : 3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) ≤
        3 / 2 * √5 * phiG 0 * (10 / r ^ 2) := by gcongr
    have h2 : 3 / 2 * √5 * phiG 0 * (10 / r ^ 2) ≤ r ^ 2 := by
      rw [show 3 / 2 * √5 * phiG 0 * (10 / r ^ 2) = 15 * √5 * phiG 0 / r ^ 2 by ring,
        div_le_iff₀ (by positivity)]
      have hm0 := mul_le_mul h5b hφ0' hφ0.le (by norm_num)
      have hm : √5 * phiG 0 ≤ 1 := by linarith only [hm0]
      have hr4 : (242 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
      have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
      rw [e]
      have e2 : 15 * √5 * phiG 0 = 15 * (√5 * phiG 0) := by ring
      rw [e2]
      linarith only [hm, hr4]
    calc _ ≤ r ^ 2 / r ^ 7 := by gcongr; exact h1.trans h2
      _ = 1 / r ^ 5 := by field_simp
  have b1 : 4 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8 ≤ 1 / r ^ 5 := by
    have h1 : 4 * √2 * (2 * (r + 2) / r ^ 2) ≤ 4 * √2 * (3 / r) := by gcongr
    have h2 : 4 * √2 * (3 / r) ≤ r ^ 3 := by
      rw [show 4 * √2 * (3 / r) = 12 * √2 / r by ring, div_le_iff₀ hr0]
      have hr4 : (242 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
      have e : r ^ 3 * r = r ^ 4 := by ring
      rw [e]
      linarith only [hr4, h2b]
    calc _ ≤ r ^ 3 / r ^ 8 := by gcongr; exact h1.trans h2
      _ = 1 / r ^ 5 := by field_simp
  have e53 : √5 ^ 3 / √2 = 5 * √5 / √2 := by rw [pow_succ, h52]
  have k53 : 5 * √5 / √2 ≤ 15812 / 10000 * 5 := by
    rw [div_le_iff₀ hs2]; linarith only [h5b, h2a]
  set Q := 8 * √5 * phiG 0 / r ^ 5 + 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 +
        3 / 2 * √5 * phiG 0 * (4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2) / r ^ 7 +
      (160 * phiG 1 / r ^ 5 + 4 * √2 * (2 * (r + 2) / r ^ 2) / r ^ 8) * (211 / 100) +
      8 * √2 * √5 * phiG 0 / r ^ 5 * (754 / 100) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hQle : Q ≤ 27 / 100 / r ^ 5 * 1000 := by
    have t1 : 8 * √5 * phiG 0 ≤ 8 * (22361 / 10000) * (39895 / 100000) := by gcongr
    have t2 : 32 * √5 ^ 3 / √2 * phiG 0 ≤ 32 * (15812 / 10000 * 5) * (39895 / 100000) := by
      rw [show 32 * √5 ^ 3 / √2 * phiG 0 = 32 * (√5 ^ 3 / √2) * phiG 0 by ring, e53]
      gcongr
    have t3 : 160 * phiG 1 ≤ 160 * (24198 / 100000) := by gcongr
    have t4 : 8 * √2 * √5 * phiG 0 ≤ 8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) := by
      gcongr
    have hr5 : 0 < r ^ 5 := by positivity
    have : Q ≤ (8 * (22361 / 10000) * (39895 / 100000) + 32 * (15812 / 10000 * 5) * (39895 / 100000) +
        1 + (160 * (24198 / 100000) + 1) * (211 / 100) +
        8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) * (754 / 100)) / r ^ 5 := by
      rw [hQ]
      have a1 : 8 * √5 * phiG 0 / r ^ 5 ≤ 8 * (22361 / 10000) * (39895 / 100000) / r ^ 5 := by gcongr
      have a2 : 32 * √5 ^ 3 / √2 * phiG 0 / r ^ 5 ≤
          32 * (15812 / 10000 * 5) * (39895 / 100000) / r ^ 5 := by gcongr
      have a3 : 160 * phiG 1 / r ^ 5 ≤ 160 * (24198 / 100000) / r ^ 5 := by gcongr
      have a4 : 8 * √2 * √5 * phiG 0 / r ^ 5 ≤
          8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 5 := by gcongr
      have e : (8 * (22361 / 10000) * (39895 / 100000) + 32 * (15812 / 10000 * 5) * (39895 / 100000) +
          1 + (160 * (24198 / 100000) + 1) * (211 / 100) +
          8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) * (754 / 100)) / r ^ 5 =
          8 * (22361 / 10000) * (39895 / 100000) / r ^ 5 +
            32 * (15812 / 10000 * 5) * (39895 / 100000) / r ^ 5 + 1 / r ^ 5 +
            (160 * (24198 / 100000) / r ^ 5 + 1 / r ^ 5) * (211 / 100) +
            8 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 5 * (754 / 100) := by
        ring
      rw [e]
      linarith [b0, b1, a1, a2, a3, a4]
    refine this.trans ?_
    rw [show (27 : ℝ) / 100 / r ^ 5 * 1000 = 270 / r ^ 5 by ring]
    gcongr
    norm_num
  -- (n m)⁴ Q⁸ = (r³Q)⁸ and r³Q ≤ 270/r² ≤ 0.004
  clear_value Q
  have hnm : (n : ℝ) * ((mA n : ℕ) : ℝ) = r ^ 6 := by rw [hmA, ← hr2]; ring
  rw [hnm, show (r ^ 6) ^ 4 * Q ^ 8 = (r ^ 3 * Q) ^ 8 by ring]
  refine pow_le_pow_left₀ (by positivity) ?_ 8
  calc r ^ 3 * Q ≤ r ^ 3 * (27 / 100 / r ^ 5 * 1000) := by gcongr
    _ = 270 / r ^ 2 := by field_simp; ring
    _ ≤ 47 / 10000 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul hr hr (by norm_num) hr0.le
      have e : r ^ 2 = r * r := by ring
      rw [e]
      linarith only [this]

/-- **The energy numerical condition** (`B_ω = 0.02`). -/
theorem numW (hn : 59000 ≤ n) :
    0 < AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) ∧
    0 < AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) ∧
    0 < AW2 (DmN n) (PmN n) (√(tA n) * O1n n) ∧
    ((mA n : ℕ) : ℝ) ^ 8 *
      (AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) +
        AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) * (211 / 100) +
        AW2 (DmN n) (PmN n) (√(tA n) * O1n n) * (754 / 100)) ^ 8 ≤ (48 / 10000) ^ 8 := by
  obtain ⟨hr, hr2, hsm, hsp, htA, hstA, hO, hD, hV⟩ := r_facts hn
  obtain ⟨h5a, h5b, h2a, h2b⟩ := sqrt_consts
  obtain ⟨hφ0, hφ0', hφ1, hφ1'⟩ := BstLean.Part154.phiG_bounds_NumA
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  set r := √(n : ℝ)
  have hr0 : 0 < r := by linarith
  have hs5 : (0 : ℝ) < √5 := by positivity
  have hs2 : (0 : ℝ) < √2 := by positivity
  have h52 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have eΓ : tA n * O1n n ^ 2 + SmaxN n = 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 := by
    rw [htA, hO]; unfold SmaxN; rw [← hr2]; rw [mul_pow, h22]; ring
  have eC : √(tA n) * O1n n = 2 * (r + 2) / r ^ 2 := by
    rw [hstA, hO]; field_simp; rw [h22]
  have eD : DmN n = 16 / r ^ 6 := by unfold DmN; rw [← hr2]; ring
  have eV : VmN n = 64 / r ^ 8 := by unfold VmN; rw [← hr2]; ring
  have eP : PmN n = 1 / r ^ 8 := by unfold PmN; rw [← hr2]; ring
  have hΓle : 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 ≤ 10 / r ^ 2 := by
    have h1 : 4 * (r + 2) ^ 2 / r ^ 4 ≤ 5 / r ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 4 * (r + 2) ^ 2 ≤ 5 * r ^ 2 := by nlinarith
      calc 4 * (r + 2) ^ 2 * r ^ 2 ≤ 5 * r ^ 2 * r ^ 2 := by gcongr
        _ = 5 * r ^ 4 := by ring
    have e : (10 : ℝ) / r ^ 2 = 5 / r ^ 2 + 5 / r ^ 2 := by ring
    linarith
  have hCle : 2 * (r + 2) / r ^ 2 ≤ 3 / r := by
    rw [div_le_div_iff₀ (by positivity) hr0]; nlinarith
  set Γ := 4 * (r + 2) ^ 2 / r ^ 4 + 5 / r ^ 2 with hΓd
  set C := 2 * (r + 2) / r ^ 2 with hCd
  have hΓ0 : 0 ≤ Γ := by positivity
  have hC0 : 0 ≤ C := by positivity
  have eA0 : AW0 √(SminN n) (tA n * O1n n ^ 2 + SmaxN n) (DmN n) (VmN n) (PmN n) =
      (16 + 160 * phiG 1) / r ^ 6 + 4 * Γ / r ^ 8 := by
    rw [← AW0_eq _ _ _ h52 hr0.ne', eΓ]
    unfold AW0 AW0'; rw [hsm, eD, eV, eP]
  have eA1 : AW1 √(SminN n) √(SmaxN n) (DmN n) (VmN n) (PmN n) (√(tA n) * O1n n) =
      32 * √2 * √5 * phiG 0 / r ^ 6 + 4 * √2 * √5 * C / r ^ 9 := by
    rw [← AW1_eq _ _ _ _ hs5.ne' hr0.ne', eC]
    unfold AW1 AW1'; rw [hsm, hsp, hD, hV, eP]
  have eA2 : AW2 (DmN n) (PmN n) (√(tA n) * O1n n) = 16 / r ^ 6 + 1 / r ^ 8 * (28 * C ^ 2) := by
    unfold AW2; rw [eD, eP, eC]
  rw [eA0, eA1, eA2]
  refine ⟨by positivity, by positivity, by positivity, ?_⟩
  have hr4 : (242 : ℝ) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by norm_num) hr 4
  have b0 : 4 * Γ / r ^ 8 ≤ 1 / r ^ 6 := by
    have : 4 * Γ ≤ r ^ 2 := by
      have e40 : (40 : ℝ) / r ^ 2 = 4 * (10 / r ^ 2) := by ring
      have h1 : 4 * Γ ≤ 40 / r ^ 2 := by rw [e40]; linarith only [hΓle]
      have h2 : 40 / r ^ 2 ≤ r ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 4 * Γ / r ^ 8 ≤ r ^ 2 / r ^ 8 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have b1 : 4 * √2 * √5 * C / r ^ 9 ≤ 1 / r ^ 6 := by
    have h0 : √2 * √5 ≤ 4 := by nlinarith only [h2b, h5b, hs2, hs5]
    have : 4 * √2 * √5 * C ≤ r ^ 3 := by
      have h1 : 4 * √2 * √5 * C ≤ 4 * 4 * (3 / r) := by
        rw [show 4 * √2 * √5 * C = 4 * (√2 * √5) * C by ring]; gcongr
      have h2 : 4 * 4 * (3 / r) ≤ r ^ 3 := by
        rw [show 4 * 4 * (3 / r) = 48 / r by ring, div_le_iff₀ hr0]
        have e : r ^ 3 * r = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 4 * √2 * √5 * C / r ^ 9 ≤ r ^ 3 / r ^ 9 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have b2 : 1 / r ^ 8 * (28 * C ^ 2) ≤ 1 / r ^ 6 := by
    have hC2 : C ^ 2 ≤ (3 / r) ^ 2 := pow_le_pow_left₀ hC0 hCle 2
    have : 28 * C ^ 2 ≤ r ^ 2 := by
      have h2 : 28 * (3 / r) ^ 2 ≤ r ^ 2 := by
        rw [div_pow, show 28 * (3 ^ 2 / r ^ 2) = 252 / r ^ 2 by ring, div_le_iff₀ (by positivity)]
        have e : r ^ 2 * r ^ 2 = r ^ 4 := by ring
        rw [e]; linarith only [hr4]
      linarith
    calc 1 / r ^ 8 * (28 * C ^ 2) ≤ 1 / r ^ 8 * r ^ 2 := by gcongr
      _ = 1 / r ^ 6 := by field_simp
  have t3 : 160 * phiG 1 ≤ 160 * (24198 / 100000) := by gcongr
  have t4 : 32 * √2 * √5 * phiG 0 ≤ 32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) := by
    gcongr
  have hr6 : 0 < r ^ 6 := by positivity
  set Q := (16 + 160 * phiG 1) / r ^ 6 + 4 * Γ / r ^ 8 +
      (32 * √2 * √5 * phiG 0 / r ^ 6 + 4 * √2 * √5 * C / r ^ 9) * (211 / 100) +
      (16 / r ^ 6 + 1 / r ^ 8 * (28 * C ^ 2)) * (754 / 100) with hQ
  have hQle : Q ≤ 280 / r ^ 6 := by
    have a0 : (16 + 160 * phiG 1) / r ^ 6 ≤ (16 + 160 * (24198 / 100000)) / r ^ 6 := by gcongr
    have a1 : 32 * √2 * √5 * phiG 0 / r ^ 6 ≤
        32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 := by gcongr
    have hsum : (16 + 160 * (24198 / 100000)) / r ^ 6 + 1 / r ^ 6 +
        (32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 + 1 / r ^ 6) * (211 / 100) +
        (16 / r ^ 6 + 1 / r ^ 6) * (754 / 100) ≤ 280 / r ^ 6 := by
      rw [show (16 + 160 * (24198 / 100000)) / r ^ 6 + 1 / r ^ 6 +
        (32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) / r ^ 6 + 1 / r ^ 6) * (211 / 100) +
        (16 / r ^ 6 + 1 / r ^ 6) * (754 / 100) = ((16 + 160 * (24198 / 100000)) + 1 +
        (32 * (14143 / 10000) * (22361 / 10000) * (39895 / 100000) + 1) * (211 / 100) +
        (16 + 1) * (754 / 100)) / r ^ 6 by ring]
      gcongr
      norm_num
    rw [hQ]
    linarith [a0, a1, b0, b1, b2, hsum]
  have hQ0 : 0 ≤ Q := by rw [hQ, hΓd, hCd]; positivity
  clear_value Q
  rw [hmA, ← hr2, show ((r ^ 2) ^ 2) ^ 8 * Q ^ 8 = (r ^ 4 * Q) ^ 8 by ring]
  refine pow_le_pow_left₀ (by positivity) ?_ 8
  calc r ^ 4 * Q ≤ r ^ 4 * (280 / r ^ 6) := by gcongr
    _ = 280 / r ^ 2 := by field_simp
    _ ≤ 48 / 10000 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul hr hr (by norm_num) hr0.le
      have e : r ^ 2 = r * r := by ring
      rw [e]
      linarith only [this]

end SPart171Num

-- ===== from Part171End.lean =====
section SPart171End
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW)
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **The location bias moments** on every `Gb ⊆ StatEvN n` (`B_f = 0.004`). -/
theorem biasMomF_stat (hn : 59000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEvN n) : BiasMomF (O1n n) Gb (47 / 10000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numF hn
  exact biasMomF_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hGb (by norm_num) (by norm_num)
    z1_pow z2_pow h0 h1 h2 h3

/-- **The energy bias moments** on every `Gb ⊆ StatEvN n` (`B_ω = 0.02`). -/
theorem biasMomW_stat (hn : 59000 ≤ n) {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)}
    (hGb : Gb ⊆ StatEvN n) : BiasMomW (O1n n) Gb (48 / 10000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numW hn
  exact biasMomW_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hGb (by norm_num) (by norm_num)
    z1_pow z2_pow h0 h1 h2 h3

/-- **The classifier theorem with the bias moments proved** (every `n ≥ 59 000`). Remaining
hypotheses: a measurable first-layer event family `Gb ⊆ StatEvN n` with charge `≤ 0.0006` in the
World window. -/
theorem classifier_paper_stat59k (hn : 59000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb)
    (hsub : Gb ⊆ StatEvN n)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ 1 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_bias_num59k hn t hGb hδG (biasMomF_stat hn hsub)
    (biasMomW_stat hn hsub)

end SPart171End

-- ===== from Part171Meas.lean =====
section SPart171Meas
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part134 (res lam)
open BstLean.Part167 (perp)
open BstLean.Part170 (hB tA aLat windowW mkR measurable_mkR)
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **The classifier theorem with the bias moments proved and `Gb = StatEvN n`** (every
`n ≥ 59 000`). The only remaining hypothesis is the charge of the statistics event `StatEvN n`
(`≤ 0.0006`) at every World datum in the window. -/
theorem classifier_paper_statN59k (hn : 59000 ≤ n) (t : ℝ)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ StatEvN n} ≤ 1 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_stat59k hn t (measurableSet_StatEvN n) subset_rfl hδG

end SPart171Meas

-- ===== from Part171Op.lean =====
section SPart171Op
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  biasF biasW measurable_mkR)
open BstLean.Part153 (nuA)
variable {n : ℕ}
/-- **On the operator event, `ς² ≤ 5/n`.** -/
lemma vsig2_upper (hn : 59000 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1)
    (h1 : OpB (A1 c) (O1n n)) : vsig2 c s ≤ SmaxN n := by
  have hle := vsig2_le (by omega) c hs
  have hop := opN_le_of_OpB (O1n_nonneg n) h1
  have hn0 : (59000 : ℝ) ≤ n := by exact_mod_cast hn
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hop2 : BstLean.Part152.opN (A1 c) ^ 2 ≤ O1n n ^ 2 :=
    pow_le_pow_left₀ (BstLean.Part152.opN_nonneg _) hop 2
  have hO2 : O1n n ^ 2 ≤ 2 * (n : ℝ) * (1 + 2 / 100) := by
    obtain ⟨hr, hr2, -, -, -, -, hO, -, -⟩ := r_facts hn
    rw [hO, mul_pow, Real.sq_sqrt (by norm_num)]
    set r := √(n : ℝ)
    rw [← hr2]
    nlinarith
  have hs0 : 0 ≤ 1 - s ^ 2 := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h1' : (1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      (n : ℝ) * (2 * (n : ℝ) * (1 + 2 / 100)) := by
    have a1 : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have a2 : (n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2 ≤ (n : ℝ) * (2 * (n : ℝ) * (1 + 2 / 100)) :=
      mul_le_mul_of_nonneg_left (hop2.trans hO2) (by positivity)
    have a3 : 0 ≤ (n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2 := by positivity
    nlinarith
  refine hle.trans ?_
  rw [hmA]
  unfold SmaxN
  calc 2 / (n : ℝ) ^ 2 * ((1 - s ^ 2) * ((n : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) / ((n : ℝ) - 1))
      ≤ 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (2 * (n : ℝ) * (1 + 2 / 100)) / ((n : ℝ) - 1)) := by
        gcongr
    _ = (408 / 100) / ((n : ℝ) - 1) := by field_simp; ring
    _ ≤ 5 / (n : ℝ) := by
        rw [div_le_div_iff₀ hn1 (by positivity)]
        nlinarith

/-- **The location bias moments on `StatEvOp`.** -/
theorem biasMomF_statOp (hn : 59000 ≤ n) : BiasMomF (O1n n) (StatEvOp n) (47 / 10000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numF hn
  have hS : StatEvOp n ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆ StatEvN n := by
    rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
    obtain ⟨a, b, d, e, f⟩ := hG hA g hg
    exact ⟨a, vsig2_upper hn _ (node_bulk hn hw (A₁, 0) hg) hA, b, d, e, f⟩
  have H := biasMomF_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hS (by norm_num)
    (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

/-- **The energy bias moments on `StatEvOp`.** -/
theorem biasMomW_statOp (hn : 59000 ≤ n) : BiasMomW (O1n n) (StatEvOp n) (48 / 10000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numW hn
  have hS : StatEvOp n ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆ StatEvN n := by
    rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
    obtain ⟨a, b, d, e, f⟩ := hG hA g hg
    exact ⟨a, vsig2_upper hn _ (node_bulk hn hw (A₁, 0) hg) hA, b, d, e, f⟩
  have H := biasMomW_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) hS (by norm_num)
    (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

/-- **The classifier theorem with the bias moments proved** (every `n ≥ 59 000`). The only
remaining hypothesis: at every World datum in the window, the Agent probability that
`‖A₁‖_op ≤ O₁` and some node `g < J_s` fails `LowStat` is at most `0.0006`. -/
theorem classifier_paper_statOp59k (hn : 59000 ≤ n) (t : ℝ)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ StatEvOp n} ≤ 1 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_bias_num59k hn t (measurableSet_StatEvOp n) hδG
    (biasMomF_statOp hn) (biasMomW_statOp hn)

end SPart171Op

-- ===== from Part171Fin.lean =====
section SPart171Fin
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  measurable_mkR)
open BstLean.Part153 (nuA)
variable {n : ℕ}
lemma statOp2_sub (hn : 59000 ≤ n) :
    StatEvOp2 n ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆ StatEvN n := by
  rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
  obtain ⟨a, b, d, f⟩ := hG hA g hg
  have hs := node_bulk hn hw (A₁, 0) hg
  have hU := hUN_eq_DstN (by omega) (mkR wr (A₁, 0)) g hs (O1n_nonneg n) hA
  exact ⟨a, vsig2_upper hn _ hs hA, b, hU ▸ b, d, f⟩

theorem biasMomF_statOp2 (hn : 59000 ≤ n) : BiasMomF (O1n n) (StatEvOp2 n) (47 / 10000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numF hn
  have H := biasMomF_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) (statOp2_sub hn)
    (by norm_num) (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

theorem biasMomW_statOp2 (hn : 59000 ≤ n) : BiasMomW (O1n n) (StatEvOp2 n) (48 / 10000) := by
  obtain ⟨h0, h1, h2, h3⟩ := numW hn
  have H := biasMomW_of_stat hn (O1n_nonneg n) (SminN_pos (by omega)) (statOp2_sub hn)
    (by norm_num) (by norm_num) z1_pow z2_pow h0 h1 h2 h3
  intro wr hw g hg A₁ hA hG
  exact H wr hw g hg A₁ hA ⟨hG, hA, hw⟩

/-- **The classifier theorem with the bias moments proved** (every `n ≥ 59 000`). The only
remaining hypothesis: at every World datum in the window, the Agent probability that
`‖A₁‖_op ≤ O₁` and some node `g < J_s` fails one of `1/(5n) ≤ ς²`, `DstN ≤ 16/n³`,
`V2N ≤ 64/n⁴`, `piN ≤ 1/n⁴` is at most `0.0006`. -/
theorem classifier_paper_final59k (hn : 59000 ≤ n) (t : ℝ)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ StatEvOp2 n} ≤ 1 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_bias_num59k hn t (measurableSet_StatEvOp2 n) hδG
    (biasMomF_statOp2 hn) (biasMomW_statOp2 hn)

end SPart171Fin

-- ===== from Part171Gen.lean =====
section SPart171Gen
open BstLean.Part171
open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA BiasMomF BiasMomW windowW mkR node_bulk opSet measurableSet_opSet
  measurable_mkR)
open BstLean.Part153 (nuA)
variable {n : ℕ}
lemma statOpG_sub (hn : 59000 ≤ n) (Sm Dm Vm Pm : ℝ) :
    StatEvOpG n Sm Dm Vm Pm ∩ {p | p.2 ∈ opSet n (O1n n) ∧ windowW p.1} ⊆
      StatEv n Sm (SmaxN n) Dm Dm Vm Pm := by
  rintro ⟨wr, A₁⟩ ⟨hG, hA, hw⟩ g hg
  obtain ⟨a, b, d, f⟩ := hG hA g hg
  have hs := node_bulk hn hw (A₁, 0) hg
  have hU := hUN_eq_DstN (by omega) (mkR wr (A₁, 0)) g hs (O1n_nonneg n) hA
  exact ⟨a, vsig2_upper hn _ hs hA, b, hU ▸ b, d, f⟩

/-- **The classifier theorem with free thresholds** (every `n ≥ 59 000`). -/
theorem classifier_paper_gen59k (hn : 59000 ≤ n) (t : ℝ) {Sm Dm Vm Pm z₁ z₂ : ℝ} (hSm : 0 < Sm)
    (hz1 : 0 < z₁) (hz2 : 0 < z₂) (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8)
    (hF0 : 0 < AF0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm)
    (hF1 : 0 < AF1 √Sm Dm Vm Pm (√(tA n) * O1n n)) (hF2 : 0 < AF2 √Sm Dm)
    (hF : ((n : ℝ) * ((mA n : ℕ) : ℝ)) ^ 4 * (AF0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm +
      AF1 √Sm Dm Vm Pm (√(tA n) * O1n n) * z₁ + AF2 √Sm Dm * z₂) ^ 8 ≤ (47 / 10000) ^ 8)
    (hW0 : 0 < AW0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm)
    (hW1 : 0 < AW1 √Sm √(SmaxN n) Dm Vm Pm (√(tA n) * O1n n))
    (hW2 : 0 < AW2 Dm Pm (√(tA n) * O1n n))
    (hW : ((mA n : ℕ) : ℝ) ^ 8 * (AW0 √Sm (tA n * O1n n ^ 2 + SmaxN n) Dm Vm Pm +
      AW1 √Sm √(SmaxN n) Dm Vm Pm (√(tA n) * O1n n) * z₁ +
      AW2 Dm Pm (√(tA n) * O1n n) * z₂) ^ 8 ≤ (48 / 10000) ^ 8)
    (hδG : ∀ wr : WRet n, windowW wr →
      (nuA n).real {θ | (wr, θ.1) ∉ StatEvOpG n Sm Dm Vm Pm} ≤ 1 / 10000) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have HF := biasMomF_of_stat hn (O1n_nonneg n) hSm (statOpG_sub hn Sm Dm Vm Pm) hz1 hz2
    hz1' hz2' hF0 hF1 hF2 hF
  have HW := biasMomW_of_stat hn (O1n_nonneg n) hSm (statOpG_sub hn Sm Dm Vm Pm) hz1 hz2
    hz1' hz2' hW0 hW1 hW2 hW
  refine classifier_paper_bias_num59k hn t (measurableSet_StatEvOpG n Sm Dm Vm Pm)
    hδG ?_ ?_
  · intro wr hw g hg A₁ hA hG
    exact HF wr hw g hg A₁ hA ⟨hG, hA, hw⟩
  · intro wr hw g hg A₁ hA hG
    exact HW wr hw g hg A₁ hA ⟨hG, hA, hw⟩

end SPart171Gen

end BstLean.Part173.N59
