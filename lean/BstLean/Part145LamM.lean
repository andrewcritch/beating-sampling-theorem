import BstLean.Part143Var2

/-!
# Part 145 (file `LamM`): the frame constant for `n ≥ 9216`

`9216 = 96²`, `9216^{3/2} = 884736`. `frameHat145M`: for every `n ≥ 9216` and
`θ ∈ goodHat n`, `E_u ⟨ê(u), w⟩² ≤ (L145M/n)·|w|²` with `L145M = 1497/1000`. The proof is the
proof of `frameHat143` with `frameB_num` called at `n₀ = 9216`: `r₀ = 1/884736`,
`k₀ = 5027/1000000`, `k₆ = 14264/1000000`, `ε₁ = 163/10000`, `ε₂ = 91/10000`,
`s = 4568/10000`. The infimum of the certificate over `ε₁`, `ε₂` is larger than `1.49659`, thus
`1497/1000` is the smallest constant with three decimal digits that this proof gives.
`errSampleTailA145M`, `errSampleA145M_lint`: the error bounds of Part 142 with `XAL L145M`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142
open BstLean.Part143

/-- The frame constant of the computed centre for `n ≥ 9216`. -/
noncomputable def L145M : ℝ := 1497 / 1000

lemma L145M_nonneg : 0 ≤ L145M := by unfold L145M; norm_num

/-- **The frame bound for the computed centre, `n ≥ 9216`**: `E_u ⟨ê(u), w⟩² ≤ (1.497/n)·|w|²`. -/
theorem frameHat145M {n : ℕ} (hn16 : 9216 ≤ n) {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ goodHat n) (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      L145M / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn : 4096 ≤ n := by omega
  unfold L145M
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  obtain ⟨hBl, -⟩ := Bh_hat hn hθ
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  -- the three hypotheses on the centre
  have hξ : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 ≤
      (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * ((3 / 8) / (n : ℝ)) := by
    have hd : dist2 (2 * n) (mW n) θ ≤
        2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) := hθ.1.2
    have e : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 =
        normSq (bhat θ - hbarW θ) := by
      rw [normSq_sub_comm]
      rfl
    rw [e]
    unfold dist2 at hd
    rw [hNcast] at hd ⊢
    have h1 : normSq (bhat θ - hbarW θ) ≤
        (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (3 / 4 / (2 * (n : ℝ)))) := by
      have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
      have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ - hbarW θ)) =
          normSq (bhat θ - hbarW θ) := by field_simp
      linarith
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  have hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 ∂uniformSphere (2 * n) ≤
      ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 * ((1 / 400000) / (n : ℝ)) := by
    have hT : (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) := hθ.2
    have e : ∀ u : Fin (2 * n) → ℝ, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 =
        ((mW n : ℝ) / 2) ^ 2 *
          (That (2 * n) (mW n) u θ - 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 := by
      intro u
      have e1 : That (2 * n) (mW n) u θ =
          2 / (mW n : ℝ) * ∑ j, hid2 θ.1 θ.2 u j * bhat θ j := rfl
      rw [e1]
      field_simp
    simp_rw [e]
    rw [integral_const_mul]
    change ((mW n : ℝ) / 2) ^ 2 * errT θ ≤ _
    have h1 : errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      linarith
    refine (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans (le_of_eq ?_)
    rw [hNcast]
    field_simp
  have hβb : (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ normSq (bhat θ) := by
    unfold Bh at hBl
    rw [hNcast] at hBl ⊢
    have := mul_le_mul_of_nonneg_left hBl (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ)) = normSq (bhat θ) := by
      field_simp
    have e3 : (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (48 / 100)) =
        (mW n : ℝ) / (2 * (n : ℝ)) * (48 / 100) := by field_simp
    linarith
  have hsle : (4568 : ℝ) / 10000 ≤
      1 - 163 / 10000 - (kap1 (2 * n) + 91 / 10000) ^ 2 / (48 / 100) := by
    have h1 : (kap1 (2 * n) + 91 / 10000) ^ 2 ≤ (4938 / 10000 + 91 / 10000) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (kap1 (2 * n) + 91 / 10000) ^ 2 / (48 / 100) ≤
        (4938 / 10000 + 91 / 10000) ^ 2 / (48 / 100) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h3 : (4938 / 10000 + 91 / 10000 : ℝ) ^ 2 / (48 / 100) ≤ 5269 / 10000 := by norm_num
    linarith
  exact frameB_num (n := n) (n0 := 9216) (by norm_num) hn16 (b := b) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 1 / 884736) (k0 := 5027 / 1000000)
    (k6 := 14264 / 1000000) (sp := 4 / 100) (ε₁ := 163 / 10000) (ε₂ := 91 / 10000)
    (s := 4568 / 10000)
    (p₂ := 4 / 10000) (D0 := 2644933 / 20000000) (C := 1497 / 1000) (ξ₀ := 3 / 8)
    (a := kap1 (2 * n)) (dT := 1 / 400000) (β := 48 / 100)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) hsle (by norm_num) hθ.1.1 hξ hX hβb w

lemma frameL_145M {n : ℕ} (hn : 9216 ≤ n) : FrameL L145M n :=
  fun _ hθ w => frameHat145M hn hθ w

/-- **The error bound of Part 142 for `n ≥ 9216`, with the stand-in factor `L145M = 141/100`.** -/
theorem errSampleTailA145M {n : ℕ} (hn : 9216 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs : 0 < s) :
    ((mlpTriple 2 n).prod (gamK k n)).real {p | s ≤ errSA k n p} ≤
      (XAL L145M n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ)) / s :=
  errSampleTailAL (by omega) L145M_nonneg (fun _ hθ w => frameHat145M hn hθ w)
    hζ0 hζ1 hη hη' hk hs

/-- The lintegral form for `n ≥ 9216`. -/
theorem errSampleA145M_lint {n : ℕ} (hn : 9216 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSA k n p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XAL L145M n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) :=
  errSampleAL_lint (by omega) L145M_nonneg (frameL_145M hn) hζ0 hζ1 hη hη' hk

end BstLean.Part145

open BstLean.Part145 in
#print axioms frameHat145M
open BstLean.Part145 in
#print axioms errSampleTailA145M
open BstLean.Part145 in
#print axioms errSampleA145M_lint
