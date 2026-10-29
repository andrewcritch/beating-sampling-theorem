import BstLean.Part72E
import BstLean.Part72Floor
import BstLean.Part72LemmaV
import BstLean.Part72T1
import BstLean.Part72T2
import BstLean.Part72Radial
import BstLean.Part71Final

/-!
# Part 72: Theorem 4 under the moment conditions `Good72` (`part72_general`)

A copy of `Part71Final.lean` with `ChiLaw n μ K` replaced by `Good72 n d k μ w F Em`. The chain:
`propE72`, `propF72`, `lemmaV72`, `propT1s72`, `radialTail72`, `propT2s72`, `fail72`. Unchanged
pieces are reused: Lemmas R, R+, H, the radial moments `CR63`, the program `g₀` and its cost
(`prog59_exists`), Part 66's ordered-node level `tO`.

* `N72 d k w F Em ε`: the explicit threshold.
* `part72_general`: Theorem 4's conclusion for every `μ` with `Good72 n d k μ w F Em`,
  `n ≥ N72 d k w F Em ε`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72
open BstLean.Part71

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part59
open BstLean.Part63
open BstLean.Part66 (tO tO_pos sb_level_ordered)
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono frob Tens TSymm heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (g0 lemmaR53 gaussPolar53)

/-- **The failure bound with its explicit threshold** (copy of `Part71.fail71` for a class `L`). -/
theorem fail72 (L : DistClass) (d k : ℕ) (ε δ p s C1 C2 : ℝ) (n1 n2 : ℕ) (hε : 0 < ε) (hs : 0 < s) (hp0 : 0 ≤ p) (hp : p < δ)
    (h1 : PropT1_72 L d k C1 n1) (h2 : PropT2_72 L d k p s C2 n2) :
    ∀ n : ℕ, nfail63 ε δ p s C1 C2 n1 n2 ≤ n → ∀ μ : Measure (Fin n → ℝ), L n μ →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ μ k f0 T (unitOfD Z) <
            (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  set A : ℝ := |C2| / s + |C1| / (ε ^ 2 * s) with hA
  have hA0 : 0 ≤ A := by positivity
  intro n hn μ hμ f0 T hT hTk
  change max (max n1 n2) (⌈A / (δ - p)⌉₊ + 1) ≤ n at hn
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : ⌈A / (δ - p)⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℕ) ≤ n := le_trans (by omega) hn3
    exact_mod_cast this
  have hc : 0 < ε ^ 2 * s := by positivity
  have hb1 := h1 n hn1 μ hμ f0 T hT hTk (ε ^ 2 * s) hc
  have hb2 := h2 n hn2 μ hμ f0 T hT hTk
  refine le_trans (measure_mono (fail_subset59 (d := d) μ k f0 T ε s)) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add hb2 hb1) ?_
  have hδp : 0 < δ - p := by linarith
  have hnA : A / (δ - p) < n := by
    have h := Nat.le_ceil (A / (δ - p))
    have : ((⌈A / (δ - p)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn3
    push_cast at this
    linarith
  have hAn : A / n ≤ δ - p := by
    rw [div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hδp] at hnA
    linarith
  have e1 : C2 / (n * s) ≤ |C2| / s / n := by
    rw [div_div, mul_comm s]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have e2 : C1 / (n * (ε ^ 2 * s)) ≤ |C1| / (ε ^ 2 * s) / n := by
    rw [div_div, mul_comm (ε ^ 2 * s)]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have hAn' : A / n = |C2| / s / n + |C1| / (ε ^ 2 * s) / n := by rw [hA, add_div]
  have hsum : p + C2 / (n * s) + C1 / (n * (ε ^ 2 * s)) ≤ δ := by linarith
  calc ENNReal.ofReal (p + C2 / (n * s)) + ENNReal.ofReal (C1 / (n * (ε ^ 2 * s)))
      ≤ ENNReal.ofReal (max (p + C2 / (n * s)) 0 + max (C1 / (n * (ε ^ 2 * s))) 0) := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
        gcongr <;> exact le_max_left _ _
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        have hC1' : 0 ≤ |C1| / (ε ^ 2 * s) / n := by positivity
        have hC2' : 0 ≤ |C2| / s / n := by positivity
        have : max (p + C2 / (n * s)) 0 ≤ p + |C2| / s / n :=
          max_le (by linarith) (by linarith)
        have : max (C1 / (n * (ε ^ 2 * s))) 0 ≤ |C1| / (ε ^ 2 * s) / n :=
          max_le e2 hC1'
        linarith


/-- `C₁ = 2.5(k+1)²·|C_E|`. -/
noncomputable def C1_72 (d k : ℕ) (w F : ℕ → ℝ) : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 * |CE72 d k w F|

/-- `C₂ = C2rad63 k C_V CR63`. -/
noncomputable def C2_72 (d k : ℕ) (w : ℕ → ℝ) : ℝ := C2rad63 k (CV72 d k w) CR63

/-- `n₂ = max(max(n_F, max(1, 40)), 1)`. -/
noncomputable def n2_72 (d k : ℕ) (w : ℕ → ℝ) (Em : ℝ) : ℕ := max (max (nF72 d k w Em) (max 1 40)) 1

/-- The failure threshold of `g₀` at failure `δ`, `p = δ/2`, `s = t/32`, for a level `t`. -/
noncomputable def Nfail72 (d k : ℕ) (w F : ℕ → ℝ) (Em ε δ t : ℝ) : ℕ :=
  nfail63 ε δ (δ / 2) (t / 32) (C1_72 d k w F) (C2_72 d k w) (max 1 40) (n2_72 d k w Em)

/-- The threshold for a level `t`: `max(Nfail72(δ = 1/100), 3k + 6d + 20, 100)`. -/
noncomputable def N72t (d k : ℕ) (w F : ℕ → ℝ) (Em ε t : ℝ) : ℕ :=
  max (max (Nfail72 d k w F Em ε (1 / 100) t) (3 * k + 6 * d + 20)) 100

/-- **The explicit threshold of Theorem 4 under `Good72`**, at Part 66's level `tO (2k) (1/200)`. -/
noncomputable def N72 (d k : ℕ) (w F : ℕ → ℝ) (Em ε : ℝ) : ℕ :=
  N72t d k w F Em ε (tO (2 * k) (1 / 200))

/-- The error and the floor for `g₀` from any small-ball level `t`. -/
theorem part72_fail_g0 (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (w F : ℕ → ℝ) (Em ε δ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hEm : 0 ≤ Em) (hε : 0 < ε) (hδ : 0 < δ)
    (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * k) (δ / 2) t) :
    ∀ n : ℕ, Nfail72 d k w F Em ε δ t ≤ n → ∀ μ : Measure (Fin n → ℝ), Good72 n d k μ w F Em →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ μ k f0 T (unitOfD Z) <
            (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  have hL := goodClass_sph d k w F Em
  have hE := propE72 d k hd w F Em hw
  have hF := propF72 d k hd hk w F Em hw hEm
  have h1 := propT1s72 _ hL d k hd hk (CE72 d k w F) 1 hE (lemmaR53 k) gaussPolar53
  have hV := lemmaV72 d k hd hk w F Em hw
  obtain ⟨hC2, hRT⟩ := radialTail72 _ hL d k hd hk (CV72 d k w) 1 hV (lemmaH59 d k hk) (lemmaRp59 k)
    gaussPolar53 CR63 CR63_nonneg (fun r n d hn => radial_moment63 r n d hn)
  have h2 := propT2s72 _ hL d k hk _ hF _ _ hC2 hRT (δ / 2) _ hSB ht
  exact fail72 _ d k ε δ (δ / 2) _ _ _ _ _ hε (by positivity) (by positivity) (by linarith) h1 h2

/-- **Theorem 4 under the moment conditions `Good72`, from any small-ball level** `t` at degree
`2k` and probability `1/200`, with threshold `N72t d k w F Em ε t`. -/
theorem part72_general_of (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (w F : ℕ → ℝ) (Em ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hEm : 0 ≤ Em) (hε : 0 < ε)
    (t : ℝ) (ht : 0 < t) (hSB : SBLevel (2 * k) (1 / 200) t) :
    100 ≤ N72t d k w F Em ε t ∧ ∀ n : ℕ, N72t d k w F Em ε t ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), Good72 n d k μ w F Em →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  have hSB' : SBLevel (2 * k) (1 / 100 / 2) t := by
    rw [show (1 / 100 / 2 : ℝ) = 1 / 200 by norm_num]; exact hSB
  have hfail := part72_fail_g0 k d hd hk w F Em ε (1 / 100) hw hEm hε (by norm_num) t ht hSB'
  refine ⟨le_max_right _ _, fun n hn => ?_⟩
  have hnf : Nfail72 d k w F Em ε (1 / 100) t ≤ n :=
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

/-- **Theorem 4 under the moment conditions `Good72`**, threshold `N72 d k w F Em ε`. -/
theorem part72_general (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (w F : ℕ → ℝ) (Em ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hEm : 0 ≤ Em) (hε : 0 < ε) :
    100 ≤ N72 d k w F Em ε ∧ ∀ n : ℕ, N72 d k w F Em ε ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), Good72 n d k μ w F Em →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) :=
  part72_general_of k d hd hk w F Em ε hw hEm hε _ (tO_pos _ _ (by norm_num))
    (sb_level_ordered (2 * k) (by omega) (1 / 200) (by norm_num))

end BstLean.Part72
