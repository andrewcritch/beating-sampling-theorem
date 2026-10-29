import BstLean.Part63Cert
import BstLean.Part66Defs

/-!
# Part 66: Theorem 4 with the small-ball level as a parameter, and certificates at `tW`

Copy of `Part63Final.part63_fail_g0` / `part63_general`, with the hard-coded level `tsb63 k (δ/2)`
replaced by a parameter `t` and the hypothesis `SBLevel (2k) (δ/2) t`.

* `Nfail66 d k K ε δ t`, `N59t d k K ε t`: the thresholds as functions of the level `t`.
* `part66T4_general_of`: Theorem 4 at threshold `N59t d k K ε t`, for every level `t > 0` with
  `SBLevel (2k) (1/200) t`.
* `N59W d k K ε = N59t d k K ε (tW (2k) (1/200))`, and the certificates `N59W_22`, `N59W_33`,
  `N59W_13` at `K = 2`, `ε = 1/2`.

The instantiation with `Part66Level.sb_level_weighted` is in `Part66T4Inst`.
Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part66

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part59
open BstLean.Part63
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono frob Tens TSymm heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (g0 lemmaR53 gaussPolar53)

/-- The failure threshold of `g₀` at failure `δ`, `p = δ/2`, `s = t/32`, for a level `t`. -/
noncomputable def Nfail66 (d k : ℕ) (K ε δ t : ℝ) : ℕ :=
  nfail63 ε δ (δ / 2) (t / 32) (C1_63 d k K) (C2_63 d k K) (max 1 40) (n2_63 d k K)

/-- The threshold of Theorem 4 for a level `t`: `max(Nfail66(δ = 1/100), 3k + 6d + 20, 100)`. -/
noncomputable def N59t (d k : ℕ) (K ε t : ℝ) : ℕ :=
  max (max (Nfail66 d k K ε (1 / 100) t) (3 * k + 6 * d + 20)) 100

/-- The threshold of Theorem 4 at the weighted-rotation level `tW (2k) (1/200)`. -/
noncomputable def N59W (d k : ℕ) (K ε : ℝ) : ℕ := N59t d k K ε (tW (2 * k) (1 / 200))

/-- The error and the floor for `g₀` from any small-ball level `t`. -/
theorem part66_fail_g0 (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * k) (δ / 2) t) :
    ∀ n : ℕ, Nfail66 d k K ε δ t ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ μ k f0 T (unitOfD Z) <
            (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  have hE := propE63 d k hd hk K
  have hF := propF63 d k hd hk K
  have h1 := propT1s63 d k hd hk K (CE63 d k K) 1 hE (lemmaR53 k) gaussPolar53
  have hV := lemmaV63 d k hd hk K
  obtain ⟨hC2, hRT⟩ := radialTail63 d k hd hk K (CV63 d k K) 1 hV (lemmaH59 d k hk) (lemmaRp59 k)
    gaussPolar53 CR63 CR63_nonneg (fun r n d hn => radial_moment63 r n d hn)
  have h2 := propT2s_of d k hk K _ hF _ _ hC2 hRT (δ / 2) _ hSB ht
  exact fail63 d k K ε δ (δ / 2) _ _ _ _ _ hε (by positivity) (by positivity) (by linarith) h1 h2

/-- **Theorem 4 from any small-ball level** `t` at degree `2k` and probability `1/200`, with
threshold `N59t d k K ε t`. -/
theorem part66T4_general_of (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * k) (1 / 200) t) :
    100 ≤ N59t d k K ε t ∧ ∀ n : ℕ, N59t d k K ε t ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  have hSB' : SBLevel (2 * k) (1 / 100 / 2) t := by
    rw [show (1 / 100 / 2 : ℝ) = 1 / 200 by norm_num]; exact hSB
  have hfail := part66_fail_g0 k d hd hk K ε (1 / 100) hε (by norm_num) t ht hSB'
  refine ⟨le_max_right _ _, fun n hn => ?_⟩
  have hnf : Nfail66 d k K ε (1 / 100) t ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : 3 * k + 6 * d + 20 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) (le_trans (le_max_right _ _) hn)
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n d k hn1 hd hk
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 k ε pg.cost hcost
    ((costG59_lt_twoPp n d k hd hnc).trans_le (twoPp_le_baselineF n d k ε)), ?_⟩
  intro μ hμ c hc
  have hCT := coefTens59
  obtain ⟨hTs, -, htop⟩ := hCT n k c
  have heval : ∀ M : CoefIdxD n d → ℝ,
      pg.eval (inp59 c M) () = g0 n d k (c default) (tensOf k c) M := by
    intro M
    rw [hspec, (cv59_inp k c M).1, (cv59_inp k c M).2, lemmaQ59]
  simp only [heval, BP_eq59 hCT, varP_eq59 hCT]
  exact hfail n hnf μ hμ (c default) (tensOf k c) hTs (htop hc)

/-! ## Certificates at the weighted level -/

/-- A sufficient condition for `N59t d k K ε t ≤ B`. -/
lemma N59t_le_of (d k : ℕ) (K ε t : ℝ) (B : ℕ) (h100 : 100 ≤ B) (hc : 3 * k + 6 * d + 20 ≤ B)
    (hF : nF63 d k K ≤ B)
    (hA : Afail63 ε (t / 32) (C1_63 d k K) (C2_63 d k K) / (1 / 100 - 1 / 100 / 2)
      ≤ (B : ℝ) - 1) :
    N59t d k K ε t ≤ B := by
  unfold N59t Nfail66 nfail63 n2_63
  have hceil : ⌈Afail63 ε (t / 32) (C1_63 d k K) (C2_63 d k K) /
      (1 / 100 - 1 / 100 / 2)⌉₊ ≤ B - 1 := by
    apply Nat.ceil_le.mpr
    have : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [this]; exact hA
  refine max_le (max_le (max_le (max_le (by omega) (max_le (max_le hF (by omega)) (by omega))) (by omega))
    hc) h100

/-- **Certificate**: `N59W 2 2 2 (1/2) ≤ 10^62` (`(d_M, d_f) = (2, 2)`, `K = 2`, `ε = 1/2`). -/
theorem N59W_22 : N59W 2 2 2 (1 / 2) ≤ 10 ^ 62 := by
  apply N59t_le_of
  · norm_num
  · norm_num
  · exact (nF63_22).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_22, C2_63_22]
    unfold tW
    norm_num

/-- **Certificate**: `N59W 3 3 2 (1/2) ≤ 10^102` (`(d_M, d_f) = (3, 3)`, `K = 2`, `ε = 1/2`). -/
theorem N59W_33 : N59W 3 3 2 (1 / 2) ≤ 10 ^ 102 := by
  apply N59t_le_of
  · norm_num
  · norm_num
  · exact (nF63_33).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_33, C2_63_33]
    unfold tW
    norm_num

/-- **Certificate**: `N59W 1 3 2 (1/2) ≤ 10^99` (`(d_M, d_f) = (1, 3)`, `K = 2`, `ε = 1/2`). -/
theorem N59W_13 : N59W 1 3 2 (1 / 2) ≤ 10 ^ 99 := by
  apply N59t_le_of
  · norm_num
  · norm_num
  · exact (nF63_13).trans (by norm_num)
  · unfold Afail63 C1_63
    rw [CE63_13, C2_63_13]
    unfold tW
    norm_num

end BstLean.Part66
