import BstLean.Part59Final
import BstLean.Part62SmallBall
import BstLean.Part62Kappa5
import BstLean.Part63Error
import BstLean.Part63T1
import BstLean.Part63Floor
import BstLean.Part63LemmaV
import BstLean.Part63Radial
import BstLean.Part63RadMom

/-!
# Part 63: Theorem 4 (`Part59.part59_general`) with an explicit dimension threshold `N59`

Every existential constant of the Theorem 4 chain is replaced by a definition:

* `CE63` (Prop E, `Part63Error`), `C₁ = 2.5(k+1)²|C_E|` (Prop T1*, `Part63T1`),
  `nF63` (Prop F, `Part63Floor`), `CV63` (Lemma V, `Part63LemmaV`),
  `CR63` (radial moments, `Part63RadMom`; exact for `r ≤ 4`), `C2rad63` (radial tail, `Part63Radial`);
* the small-ball level `tsb63 k p`: `tK 5⁸ 4 p` at `k = 2`, `tK 5¹² 6 p` at `k = 3`, and `tExp (2k) p`
  otherwise (`Part62SmallBall`; no compactness constant);
* the failure threshold `nfail63` (copy of `Part59.fail59`) and the cost threshold `3k + 6d + 20`.

`part63_general` is the statement of `part59_general` with `n₀ = N59 d k K ε`.
Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part63

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part59
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono frob Tens TSymm heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (g0 lemmaR53 gaussPolar53)
open BstLean.Part62 (tK tExp tK_pos tExp_pos sb_level_explicit sb_level_5_4 sb_level_5_6)

/-- The level `A = |C₂|/s + |C₁|/(ε² s)` of the failure bound. -/
noncomputable def Afail63 (ε s C1 C2 : ℝ) : ℝ := |C2| / s + |C1| / (ε ^ 2 * s)

/-- The threshold of the failure bound: `max(n₁, n₂, ⌈A/(δ − p)⌉₊ + 1)`. -/
noncomputable def nfail63 (ε δ p s C1 C2 : ℝ) (n1 n2 : ℕ) : ℕ :=
  max (max n1 n2) (⌈Afail63 ε s C1 C2 / (δ - p)⌉₊ + 1)

/-- **The failure bound with its explicit threshold** (copy of `Part59.fail59`). -/
theorem fail63 (d k : ℕ) (K ε δ p s C1 C2 : ℝ) (n1 n2 : ℕ) (hε : 0 < ε) (hs : 0 < s) (hp0 : 0 ≤ p) (hp : p < δ)
    (h1 : PropT1_59 d k K C1 n1) (h2 : PropT2_59 d k K p s C2 n2) :
    ∀ n : ℕ, nfail63 ε δ p s C1 C2 n1 n2 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
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


/-- **The small-ball level** used for degree `2k`. -/
noncomputable def tsb63 (k : ℕ) (p : ℝ) : ℝ :=
  if k = 2 then tK (5 ^ 8) 4 p else if k = 3 then tK (5 ^ 12) 6 p else tExp (2 * k) p

lemma tsb63_pos (k : ℕ) (p : ℝ) (hp : 0 < p) : 0 < tsb63 k p := by
  unfold tsb63
  split_ifs
  · exact tK_pos _ (by norm_num) _ _ hp
  · exact tK_pos _ (by norm_num) _ _ hp
  · exact tExp_pos _ _ hp

lemma sb63 (k : ℕ) (p : ℝ) (hp : 0 < p) : SBLevel (2 * k) p (tsb63 k p) := by
  unfold tsb63
  split_ifs with h2 h3
  · subst h2; exact sb_level_5_4 p hp
  · subst h3; exact sb_level_5_6 p hp
  · exact sb_level_explicit _ p hp

/-- `C₁ = 2.5(k+1)²·|C_E|`. -/
noncomputable def C1_63 (d k : ℕ) (K : ℝ) : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2 * |CE63 d k K|

/-- `C₂ = k·2.5(k+1)²·|C_V|·Σ_{r=1}^{k} CR63(r)(5k²)^{2r}`. -/
noncomputable def C2_63 (d k : ℕ) (K : ℝ) : ℝ := C2rad63 k (CV63 d k K) CR63

/-- `n₂ = max(max(n_F, max(1, 40)), 1)` (Prop T2*). -/
noncomputable def n2_63 (d k : ℕ) (K : ℝ) : ℕ := max (max (nF63 d k K) (max 1 40)) 1

/-- **The failure threshold** of `g₀` at failure `δ`, `p = δ/2`, `s = tsb63 k p/32`. -/
noncomputable def Nfail63 (d k : ℕ) (K ε δ : ℝ) : ℕ :=
  nfail63 ε δ (δ / 2) (tsb63 k (δ / 2) / 32) (C1_63 d k K) (C2_63 d k K) (max 1 40) (n2_63 d k K)

/-- **The explicit threshold of Theorem 4**: `N59 = max(Nfail63(δ = 1/100), 3k + 6d + 20, 100)`. -/
noncomputable def N59 (d k : ℕ) (K ε : ℝ) : ℕ :=
  max (max (Nfail63 d k K ε (1 / 100)) (3 * k + 6 * d + 20)) 100

/-- **The error and the floor** for `g₀` (tensor form) with the explicit threshold. -/
theorem part63_fail_g0 (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ n : ℕ, Nfail63 d k K ε δ ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
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
  have ht := tsb63_pos k (δ / 2) (by positivity)
  have h2 := propT2s_of d k hk K _ hF _ _ hC2 hRT (δ / 2) _ (sb63 k (δ / 2) (by positivity)) ht
  exact fail63 d k K ε δ (δ / 2) _ _ _ _ _ hε (by positivity) (by positivity) (by linarith) h1 h2

/-- **Theorem 4 (DL2-G) with an explicit threshold.** The statement of `Part59.part59_general` with
`n₀ = N59 d k K ε`. -/
theorem part63_general (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε : ℝ) (hε : 0 < ε) :
    100 ≤ N59 d k K ε ∧ ∀ n : ℕ, N59 d k K ε ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  have hfail := part63_fail_g0 k d hd hk K ε (1 / 100) hε (by norm_num)
  refine ⟨le_max_right _ _, fun n hn => ?_⟩
  have hnf : Nfail63 d k K ε (1 / 100) ≤ n :=
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

end BstLean.Part63
