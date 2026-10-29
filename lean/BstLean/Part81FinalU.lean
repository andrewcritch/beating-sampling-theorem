import BstLean.Part81Asm2
import BstLean.Part81UY
import BstLean.Part81NumM
import BstLean.Part81Cost
import BstLean.Part81Final3

/-!
# Part 81: Theorem 4 at `d_f = 2` and every map degree `d ≥ 4`, uniform `D`, `ε = 1/2`,
failure `≤ 1/100`, every `n ≥ 8200` — one threshold for all these degrees

This file is generated from a template (the constants are computed by a script with exact rational
arithmetic; Lean checks every inequality). Inputs: the feature operator bound `featOpU`
(`CF = 101/100`, every degree), the moment form of the sphere constants `sphMU`, `ss2U8`, and
`41 / 24 ≤ e_d ≤ 1719 / 1000`.
Floor `8541 / 5000‖a‖² + 11673 / 2000‖H‖²`; `c₁ = 16187 / 5000`; `c_V ≈ 17.90`;
`κ = 17 / 50`, `ε₁ = 1419 / 5000`, `λ = 1 / 100`, `t = 40`, `k = 5`, `μ = 1 / 50`.
-/

namespace BstLean.Part81

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU heavyCount)
open BstLean.Part59
open BstLean.Part78 (nsq frobH trH)

theorem part81_sphMU4 (n d : ℕ) (hd : 4 ≤ d) (hn : 8200 ≤ n) :
    SphM n d (101 / 100) (1071 / 1000) (4093 / 1000) 119 2212 :=
  sphM_setS2 (ss2U8 n d (by omega) (by omega))
    (sphMU n d (by omega) (by omega) (101 / 100) (by norm_num) (by norm_num) (featOpU n d (by omega)))

theorem part81_mbU4 (n d : ℕ) (hd : 4 ≤ d) (hn : 8200 ≤ n) :
    MB n d (8541 / 5000) (11673 / 2000) (101 / 100) (2 * (1071 / 1000) + (4093 / 1000) ^ 2) (eD d + (4093 / 1000) / (n : ℝ)) (119 / (n : ℝ) + 2 * (eD d ^ 2 + 2 * eD d * ((4093 / 1000) / (n : ℝ)) + 119 / (n : ℝ) ^ 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (8200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8200 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have he_lo : 41 / 24 ≤ eD d := eD_four_le d hd
  have he_hi : eD d ≤ 1719 / 1000 := eD_le d
  have he0 : 0 ≤ eD d := by linarith
  have e3 : (4093 / 1000 : ℝ) / n = 4093 / 1000 * (1 / n) := by ring
  have e1 : (1071 / 1000 : ℝ) / n = 1071 / 1000 * (1 / n) := by ring
  have eM : (101 / 100 : ℝ) / n = 101 / 100 * (1 / n) := by ring
  have e2 : (119 : ℝ) / n = 119 * (1 / n) := by ring
  have e22 : (119 : ℝ) / (n : ℝ) ^ 2 = 119 * (1 / n) ^ 2 := by ring
  have e33 : (2212 : ℝ) / (n : ℝ) ^ 3 = 2212 * (1 / n) ^ 3 := by ring
  refine mbM_of n d hn1 he0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (part81_sphMU4 n d hd hn)
    (meanIds n d hn1 BstLean.Part78.wickTwoPoint) ?_ ?_
  · rw [eM]; linarith
  · rw [e1]
    have : (41 / 24) ^ 2 ≤ eD d ^ 2 := pow_le_pow_left₀ (by norm_num) he_lo 2
    norm_num at this
    linarith

theorem part81_varBoundWU4 (n d : ℕ) (hd : 4 ≤ d) (hn : 8200 ≤ n) :
    VarBoundW n d (8541 / 5000) (11673 / 2000)
      (1 / 2 * (4 * (101 / 100) * (1733 / 1000) * (4184 / 1000) * (5891 / 5000 + 9 / 25000)) + 1 / 2 * (4 * (101 / 100) * (1589 / 5000))) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (8200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8200 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have he_lo : 41 / 24 ≤ eD d := eD_four_le d hd
  have he_hi : eD d ≤ 1719 / 1000 := eD_le d
  have he0 : 0 ≤ eD d := by linarith
  have e3 : (4093 / 1000 : ℝ) / n = 4093 / 1000 * (1 / n) := by ring
  have e1 : (1071 / 1000 : ℝ) / n = 1071 / 1000 * (1 / n) := by ring
  have eM : (101 / 100 : ℝ) / n = 101 / 100 * (1 / n) := by ring
  have e2 : (119 : ℝ) / n = 119 * (1 / n) := by ring
  have e22 : (119 : ℝ) / (n : ℝ) ^ 2 = 119 * (1 / n) ^ 2 := by ring
  have e33 : (2212 : ℝ) / (n : ℝ) ^ 3 = 2212 * (1 / n) ^ 3 := by ring
  have hF := featOpU n d (by omega)
  have hnn : (n : ℝ) * (2212 * (1 / (n : ℝ)) ^ 3 + ((4093 / 1000) * (1 / (n : ℝ))) ^ 3) =
      (2212 + (4093 / 1000) ^ 3) * (1 / (n : ℝ)) ^ 2 := by field_simp
  refine varBoundWM_of n d hn1 (η := 7 / 200) he0 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (part81_sphMU4 n d hd hn) (part81_mbU4 n d hd hn)
    (wQId n d hn1 BstLean.Part78.wickTwoPoint)
    (varBoundK n d hn1 (101 / 100) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin)
    (varBoundK2 n d hn1 (101 / 100) 3 (1733 / 1000) (35 / 2) (4184 / 1000) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) BstLean.Part78.poincareMv2 hF
      BstLean.Part78.affFourth3 BstLean.Part78.deg2Fourth BstLean.Part78.gaussLin
      BstLean.Part78.wickTwoPoint)
    (by norm_num) (by linarith) (by norm_num) ?_ ?_ (by norm_num) ?_ (by norm_num)
  · rw [e33, e3, e22, e1, hnn]
    set x := 1 / (n : ℝ)
    set e := eD d
    have hxx : x ^ 2 ≤ (1 / 8200) ^ 2 := pow_le_pow_left₀ hx0.le hx 2
    have hx3 : x ^ 3 ≤ (1 / 8200) ^ 3 := pow_le_pow_left₀ hx0.le hx 3
    have hee : e ^ 2 ≤ (1719 / 1000) ^ 2 := pow_le_pow_left₀ he0 he_hi 2
    have hex : e * x ≤ 1719 / 1000 * (1 / 8200) := mul_le_mul he_hi hx hx0.le (by norm_num)
    have hex2 : e * x ^ 2 ≤ 1719 / 1000 * (1 / 8200) ^ 2 := mul_le_mul he_hi hxx (by positivity) (by norm_num)
    have heex : e ^ 2 * x ≤ (1719 / 1000) ^ 2 * (1 / 8200) := mul_le_mul hee hx hx0.le (by norm_num)
    norm_num at hxx hx3 hee hex hex2 heex
    nlinarith
  · rw [e3, e22, eM]
    set x := 1 / (n : ℝ)
    set e := eD d
    have hxx : x ^ 2 ≤ (1 / 8200) ^ 2 := pow_le_pow_left₀ hx0.le hx 2
    have hx3 : x ^ 3 ≤ (1 / 8200) ^ 3 := pow_le_pow_left₀ hx0.le hx 3
    have hee : e ^ 2 ≤ (1719 / 1000) ^ 2 := pow_le_pow_left₀ he0 he_hi 2
    have hex : e * x ≤ 1719 / 1000 * (1 / 8200) := mul_le_mul he_hi hx hx0.le (by norm_num)
    have hex2 : e * x ^ 2 ≤ 1719 / 1000 * (1 / 8200) ^ 2 := mul_le_mul he_hi hxx (by positivity) (by norm_num)
    have heex : e ^ 2 * x ≤ (1719 / 1000) ^ 2 * (1 / 8200) := mul_le_mul hee hx hx0.le (by norm_num)
    norm_num at hxx hx3 hee hex hex2 heex
    nlinarith
  · rw [e2, e3, e22]
    set x := 1 / (n : ℝ)
    set e := eD d
    have hxx : x ^ 2 ≤ (1 / 8200) ^ 2 := pow_le_pow_left₀ hx0.le hx 2
    have hx3 : x ^ 3 ≤ (1 / 8200) ^ 3 := pow_le_pow_left₀ hx0.le hx 3
    have hee : e ^ 2 ≤ (1719 / 1000) ^ 2 := pow_le_pow_left₀ he0 he_hi 2
    have hex : e * x ≤ 1719 / 1000 * (1 / 8200) := mul_le_mul he_hi hx hx0.le (by norm_num)
    have hex2 : e * x ^ 2 ≤ 1719 / 1000 * (1 / 8200) ^ 2 := mul_le_mul he_hi hxx (by positivity) (by norm_num)
    have heex : e ^ 2 * x ≤ (1719 / 1000) ^ 2 * (1 / 8200) := mul_le_mul hee hx hx0.le (by norm_num)
    norm_num at hxx hx3 hee hex hex2 heex
    nlinarith

/-- Failure `≤ 1/100` at `ε = 1/2`, every map degree `d ≥ 4`, every `n ≥ 8200`. -/
theorem part81_ge4_fail (n d : ℕ) (hd : 4 ≤ d) (hn : 8200 ≤ n) (c : Mono n 2 → ℝ) (hc : TopNZ 2 c) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
      (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
        (BP (uniformSphere n) 2 c (unitOfD Z) - g0Q n d 2 c (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (1 / 100) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (8200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 < 1 / (n : ℝ) := by positivity
  have hx : 1 / (n : ℝ) ≤ 1 / 8200 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; linarith
  have he_lo : 41 / 24 ≤ eD d := eD_four_le d hd
  have he_hi : eD d ≤ 1719 / 1000 := eD_le d
  have he0 : 0 ≤ eD d := by linarith
  have e3 : (4093 / 1000 : ℝ) / n = 4093 / 1000 * (1 / n) := by ring
  have e1 : (1071 / 1000 : ℝ) / n = 1071 / 1000 * (1 / n) := by ring
  have eM : (101 / 100 : ℝ) / n = 101 / 100 * (1 / n) := by ring
  have e2 : (119 : ℝ) / n = 119 * (1 / n) := by ring
  have e22 : (119 : ℝ) / (n : ℝ) ^ 2 = 119 * (1 / n) ^ 2 := by ring
  have e33 : (2212 : ℝ) / (n : ℝ) ^ 3 = 2212 * (1 / n) ^ 3 := by ring
  have hUA0 : 0 ≤ (eD d + (4093 / 1000) / (n : ℝ)) := by positivity
  have hUv0 : 0 ≤ (119 / (n : ℝ) + 2 * (eD d ^ 2 + 2 * eD d * ((4093 / 1000) / (n : ℝ)) + 119 / (n : ℝ) ^ 2)) := by positivity
  refine (fail81_asm2 n d (by omega) (by omega) (c1 := 16187 / 5000) (κ := 17 / 50)
    (ε := 1 / 2) (ε₁ := 1419 / 5000) (lam := 1 / 100) (t := 40) (μ := 1 / 50) (k := 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hUA0 hUv0
    (part81_mbU4 n d hd hn) (part81_varBoundWU4 n d hd hn) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ c hc).trans (ENNReal.ofReal_le_ofReal ?_)
  · have e : (1 : ℝ) / ((5) ^ 2 * (n : ℝ)) = 1 / (5) ^ 2 * (1 / n) := by
      field_simp
    rw [e]
    have hee : eD d ^ 2 ≤ (1719 / 1000) ^ 2 := pow_le_pow_left₀ he0 he_hi 2
    have hA : (2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * eD d ^ 2) +
        (1 / 2) ^ 2 * (40) / (1 / 100)) ≤ 2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * (1719 / 1000) ^ 2) +
        (1 / 2) ^ 2 * (40) / (1 / 100) := by
      have := mul_le_mul_of_nonneg_left hee (by norm_num : (0:ℝ) ≤ 2 * (1 + 1 / (1 / 50 : ℝ)) * (409 / 100))
      linarith
    have hA0 : (0:ℝ) ≤ 2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * (1719 / 1000) ^ 2) +
        (1 / 2) ^ 2 * (40) / (1 / 100) := by norm_num
    have : (2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * eD d ^ 2) +
        (1 / 2) ^ 2 * (40) / (1 / 100)) * (1 / (5) ^ 2 * (1 / (n : ℝ))) / (11673 / 2000) ≤
        49 / 25000 := by
      rw [div_le_iff₀ (by norm_num)]
      calc _ ≤ (2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * (1719 / 1000) ^ 2) +
            (1 / 2) ^ 2 * (40) / (1 / 100)) * (1 / (5) ^ 2 * (1 / (n : ℝ))) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ ≤ (2 * (1 + 1 / (1 / 50 : ℝ)) * (1 + 409 / 100 * (1719 / 1000) ^ 2) +
            (1 / 2) ^ 2 * (40) / (1 / 100)) * (1 / (5) ^ 2 * (1 / 8200)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (by norm_num)) hA0
        _ ≤ _ := by norm_num
    nlinarith
  · rw [e3, e2, e22]
    set x := 1 / (n : ℝ)
    set e := eD d
    have hxx : x ^ 2 ≤ (1 / 8200) ^ 2 := pow_le_pow_left₀ hx0.le hx 2
    have hx3 : x ^ 3 ≤ (1 / 8200) ^ 3 := pow_le_pow_left₀ hx0.le hx 3
    have hee : e ^ 2 ≤ (1719 / 1000) ^ 2 := pow_le_pow_left₀ he0 he_hi 2
    have hex : e * x ≤ 1719 / 1000 * (1 / 8200) := mul_le_mul he_hi hx hx0.le (by norm_num)
    have hex2 : e * x ^ 2 ≤ 1719 / 1000 * (1 / 8200) ^ 2 := mul_le_mul he_hi hxx (by positivity) (by norm_num)
    have heex : e ^ 2 * x ≤ (1719 / 1000) ^ 2 * (1 / 8200) := mul_le_mul hee hx hx0.le (by norm_num)
    norm_num at hxx hx3 hee hex hex2 heex
    have hU : (4 * (e + (4093 / 1000) * x) + (119 * x + 2 * (e ^ 2 + 2 * e * ((4093 / 1000) * x) + 119 * x ^ 2))) / (40) ≤ 1601 / 5000 := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    have hS : 27200 * (5 : ℝ) ^ 8 * x ^ 3 + 16187 / 5000 / (1419 / 5000 : ℝ) ^ 2 +
        (1 / 2 * (4 * (101 / 100) * (1733 / 1000) * (4184 / 1000) * (5891 / 5000 + 9 / 25000)) + 1 / 2 * (4 * (101 / 100) * (1589 / 5000))) / (1 - 17 / 50 : ℝ) ^ 2 +
        (4 * (e + (4093 / 1000) * x) + (119 * x + 2 * (e ^ 2 + 2 * e * ((4093 / 1000) * x) + 119 * x ^ 2))) / (40) +
        (4 * (101 / 100) + (2 * (1071 / 1000) + (4093 / 1000) ^ 2)) * x ≤ 817 / 10 := by
      have h1 : (16187 / 5000 : ℝ) / (1419 / 5000) ^ 2 ≤ 201 / 5 := by norm_num
      have h2 : ((1 / 2 * (4 * (101 / 100) * (1733 / 1000) * (4184 / 1000) * (5891 / 5000 + 9 / 25000)) + 1 / 2 * (4 * (101 / 100) * (1589 / 5000))) : ℝ) / (1 - 17 / 50) ^ 2 ≤ 4111 / 100 := by norm_num
      nlinarith
    have hS0 : (0 : ℝ) ≤ 817 / 10 := by norm_num
    calc _ ≤ 817 / 10 * x := mul_le_mul_of_nonneg_right hS hx0.le
      _ ≤ 817 / 10 * (1 / 8200) := mul_le_mul_of_nonneg_left hx hS0
      _ ≤ 1 / 100 := by norm_num

/-- **Theorem 4 at `d_f = 2`, every map degree `d ≥ 4`, uniform `D`, `ε = 1/2`, failure
`≤ 1/100`, every `n ≥ 8200`.** The threshold does not depend on `d`. -/
theorem part81_ge4 :
    ∀ d : ℕ, 4 ≤ d → ∀ n : ℕ, 8200 ≤ n → ∃ pg : Prog (In59 n d 2) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d 2 → ℝ, pg.eval v () = g0Q n d 2 (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d 2 (1 / 2) ∧
      ∀ c : Mono n 2 → ℝ, TopNZ 2 c →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) 2 c (unitOfD Z) <
            (BP (uniformSphere n) 2 c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  intro d hd n hn
  obtain ⟨pg, h0, hread, hspec, hcost, heval⟩ := prog81_unif n d (by omega) (by omega) (1 / 2)
  refine ⟨pg, h0, hread, hspec, hcost, ?_⟩
  intro c hc
  simp only [heval]
  exact part81_ge4_fail n d hd hn c hc

end BstLean.Part81

#print axioms BstLean.Part81.part81_ge4
