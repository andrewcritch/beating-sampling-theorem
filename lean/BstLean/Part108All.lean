import BstLean.Part108Sphere
import BstLean.Part108Gauss
import BstLean.Part108Pert
import BstLean.Part108TV
import BstLean.Part108Alg
import BstLean.Part108Meas
import BstLean.Part108Num

/-!
# Part 108: Theorem W8-S in Lean — sphere versions of `W`, `A`, `F`, the realized spread

Role: `delegations/statements/p108-spec.md`. Report: `delegations/answers/p108-spec-opus.md`.

`r = 2`, `d_A, d_F ∈ {3, 4}`, `n ≥ 4096`, `ε = 1/2`. `W` (`2n` inputs, degree `2d_A`), `A`, `F`
independent, each with the Bombieri–Weyl sphere distribution `bwSphere`; `k` blocks of random
inputs (a uniform unit vector of `ℝ^{2n}` and a standard Gaussian vector of `ℝⁿ` each).
The program is `gProgFix` of Part 106 (it reads the coefficients of degree `0` and `1` of `W`,
`A`, `F` and the blocks; noise level `τ² = (2d_A − 1)/D_W`).

* `w8s_general`: success probability at least `1 − delta108 n dA k θ ι` for every `1 ≤ k < n²`,
  `θ, ι ∈ (0, 1)`, and the cost comparison.
* `main108`: at least `99/100` for `5000 ≤ k < n²`.
* `main108_k1e6`: at least `199/200` for `10⁶ ≤ k < n²`.
* `nested108_general`, `nested108_k5000`, `nested108_k1e6`: the nested form by the Markov
  inequality.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Cost BstLean.Part105
open BstLean.Part106 (phiAF gProgFix gInVal tauPaperSq tauPaper)

variable {n dA dF k : ℕ}

/-- **The success event in the words of the north star**: `|g − B(W, A, F)| ≤ (1/2)·sd_μ`, with
`g` the value of the explicit program `gProgFix` on the coefficients of degree `0` and `1` of `W`,
on `A`, `F` and on the blocks `ω`; `B = ∫ F(A(x)) dμ_W`; `sd_μ² = Var_{μ_W}(F∘A)`. -/
def Good108 (hd : 1 ≤ 2 * dA) (W : CoefIdx (2 * n) n (2 * dA) → ℝ) (A : CoefIdx n n dA → ℝ)
    (F : CoefIdx n 1 dF → ℝ) (ω : Draws (2 * n) n k) : Prop :=
  |(gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).eval
        (gInVal (fun a => W (a, mono0 (2 * n) (2 * dA)))
          (fun a j => W (a, mono1 (2 * n) (2 * dA) hd j))
          0 A F (fun i => (ω i).1) (fun i => (ω i).2)) () -
      ∫ x, phiAF A F x ∂muW W| ≤
    1 / 2 * Real.sqrt (Var[phiAF A F; muW W])

lemma good_iff_succ (hd : 1 ≤ 2 * dA) (W : CoefIdx (2 * n) n (2 * dA) → ℝ)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) (ω : Draws (2 * n) n k) :
    Good108 hd W A F ω ↔ Succ W (tauPaper (2 * n) n (2 * dA)) (phiAF A F) ω := by
  have hm : Measurable (phiAF A F) := (BstLean.Part106.continuous_phiAF A F).measurable
  unfold Good108 Succ Err
  rw [BstLean.Part106.gProgFix_eval, ← BstLean.Part106.tauPaper_eq_sqrt (2 * n) n (2 * dA) hd,
    BstLean.Part106.gProg_eval_gVal, Bu_eq W hm, Vu_eq W hm]

/-- The cost comparison (as in `main_sphere` of Part 106; `1 ≤ k` is not needed). -/
theorem cost108 (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk2 : k < n ^ 2) (hdA : dA = 3 ∨ dA = 4)
    (hdF : dF = 3 ∨ dF = 4) (p : SProg (SampleIn 2 n dA dF) Unit)
    (hp : ∀ u W A F, p.eval (sampleVal u W A F) () =
      bwEval F (bwEval A (sphProj (bwEval W u))) 0) :
    (gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).cost < p.cost := by
  have h1 := BstLean.Part106.gProgFix_cost (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k
  have h2 := BstLean.Part106.gCost_lt_lower n (k + 1) dA dF hn (by omega) hdA hdF
  have h3 := BstLean.Part106.sample_lower p hp (by rcases hdA with h | h <;> omega)
    (by rcases hdF with h | h <;> omega)
  rw [BstLean.Part106.card_coefIdx] at h3
  have h4 : BstLean.Part106.gCost k 2 n dA dF + 1 ≤ BstLean.Part106.gCost (k + 1) 2 n dA dF := by
    unfold BstLean.Part106.gCost
    nlinarith
  omega

lemma eps2_pos1 (hn : 1 ≤ n) : 0 < eps2 n := by
  have : (0 : ℝ) < n := by exact_mod_cast hn
  unfold eps2
  positivity

lemma eps2_lt_one (hn : 1 ≤ n) : eps2 n < 1 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold eps2
  rw [div_lt_one (by positivity)]
  have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ h1
  nlinarith

/-- The joint statement in the form `Succ`, with the explicit bound `delta108`. -/
theorem joint_succ (hn : 4096 ≤ n) (hk : 1 ≤ k) (hk2 : k < n ^ 2) (hdA : dA = 3 ∨ dA = 4)
    (hdF : dF = 3 ∨ dF = 4) {θ ι : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hι : 0 < ι) (hι1 : ι < 1) :
    1 - delta108 n dA k θ ι ≤ (PS n dA dF k).real
      {p | Succ p.1.1 (tauPaper (2 * n) n (2 * dA)) (phiAF p.1.2.1 p.1.2.2) p.2} := by
  have hd : 1 ≤ dF := by rcases hdF with h | h <;> omega
  have hcore := core_gauss (k := k) linLaw108 (pertBound108 htailMom108 evalMom108 gMom108)
    measGen108 measPsi108 succParts108 hn hdA hd hk hθ hθ1 hι hι1
  have hfix := gauss_fixed (dF := dF) drawsTV108 measGen108 measPhi108 (by omega : 1 ≤ n)
    (η := 64 / 10 ^ 6) (ε2 := eps2 n) (by norm_num) (eps2_pos1 (by omega)) (eps2_lt_one (by omega))
    hcore (eta_num n k hn hk2)
  exact sphere_succ (by omega)
    (hfix.trans (total_le gMom108 n dA dF k hn hdA hdF hk hθ hθ1 hι hι1))

/-- **Theorem W8-S in Lean, with the explicit failure bound.** `r = 2`, `d_A, d_F ∈ {3, 4}`,
`n ≥ 4096`, `1 ≤ k < n²`, `θ, ι ∈ (0, 1)`. `W`, `A`, `F` independent with the Bombieri–Weyl
sphere distribution, and `k` independent blocks.
1. With probability at least `1 − delta108 n dA k θ ι`: `|g − B(W, A, F)| ≤ (1/2)·sd_μ`, `g` the
   value of the explicit program, `sd_μ` the standard deviation of `F(A(x))` under `μ_W` (the
   realized spread).
2. The cost of the program is below the cost of every program of the cost model that computes
   one sample `F(A(W(u)/|W(u)|))` for all inputs. -/
theorem w8s_general (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 1 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) {θ ι : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hι : 0 < ι) (hι1 : ι < 1) :
    1 - delta108 n dA k θ ι ≤
      (((bwSphere (2 * n) n (2 * dA)).prod ((bwSphere n n dA).prod (bwSphere n 1 dF))).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |(gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).eval
                (gInVal (fun a => p.1.1 (a, mono0 (2 * n) (2 * dA)))
                  (fun a j => p.1.1 (a, mono1 (2 * n) (2 * dA)
                    (by rcases hdA with h | h <;> omega) j))
                  0 p.1.2.1 p.1.2.2 (fun i => (p.2 i).1) (fun i => (p.2 i).2)) () -
              ∫ x, phiAF p.1.2.1 p.1.2.2 x ∂muW p.1.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF p.1.2.1 p.1.2.2; muW p.1.1])} ∧
    ∀ p : SProg (SampleIn 2 n dA dF) Unit,
      (∀ u W A F, p.eval (sampleVal u W A F) () =
        bwEval F (bwEval A (sphProj (bwEval W u))) 0) →
      (gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).cost < p.cost := by
  refine ⟨?_, fun p hp => cost108 n k dA dF hn hk2 hdA hdF p hp⟩
  have hd1 : 1 ≤ 2 * dA := by rcases hdA with h | h <;> omega
  refine le_trans (joint_succ (dF := dF) hn hk hk2 hdA hdF hθ hθ1 hι hι1) (le_of_eq ?_)
  congr 1
  ext p
  exact (good_iff_succ hd1 p.1.1 p.1.2.1 p.1.2.2 p.2).symm

/-- **Theorem W8-S in Lean** (`ε = 1/2`, failure probability `1/100`): `r = 2`,
`d_A, d_F ∈ {3, 4}`, every `n ≥ 4096`, every `5000 ≤ k < n²`. For `W`, `A`, `F` independent with
the Bombieri–Weyl sphere distribution and `k` independent blocks: with probability at least
`99/100`, `|g − B(W, A, F)| ≤ (1/2)·sd_μ` (`sd_μ` the realized spread); and the cost of the
program is below the cost of every program of the cost model that computes one sample exactly. -/
theorem main108 (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 5000 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    99 / 100 ≤
      (((bwSphere (2 * n) n (2 * dA)).prod ((bwSphere n n dA).prod (bwSphere n 1 dF))).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |(gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).eval
                (gInVal (fun a => p.1.1 (a, mono0 (2 * n) (2 * dA)))
                  (fun a j => p.1.1 (a, mono1 (2 * n) (2 * dA)
                    (by rcases hdA with h | h <;> omega) j))
                  0 p.1.2.1 p.1.2.2 (fun i => (p.2 i).1) (fun i => (p.2 i).2)) () -
              ∫ x, phiAF p.1.2.1 p.1.2.2 x ∂muW p.1.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF p.1.2.1 p.1.2.2; muW p.1.1])} ∧
    ∀ p : SProg (SampleIn 2 n dA dF) Unit,
      (∀ u W A F, p.eval (sampleVal u W A F) () =
        bwEval F (bwEval A (sphProj (bwEval W u))) 0) →
      (gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).cost < p.cost := by
  obtain ⟨h1, h2⟩ := w8s_general n k dA dF hn (by omega) hk2 hdA hdF
    (θ := 7 / 10) (ι := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨le_trans ?_ h1, h2⟩
  have := delta_k5000 n dA k hn hdA hk
  linarith

/-- **Theorem W8-S in Lean with `k ≥ 10⁶` samples**: the failure probability is at most `1/200`
(the paper value at `n = 4096` is `0.00431`). -/
theorem main108_k1e6 (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 10 ^ 6 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    199 / 200 ≤
      (((bwSphere (2 * n) n (2 * dA)).prod ((bwSphere n n dA).prod (bwSphere n 1 dF))).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |(gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).eval
                (gInVal (fun a => p.1.1 (a, mono0 (2 * n) (2 * dA)))
                  (fun a j => p.1.1 (a, mono1 (2 * n) (2 * dA)
                    (by rcases hdA with h | h <;> omega) j))
                  0 p.1.2.1 p.1.2.2 (fun i => (p.2 i).1) (fun i => (p.2 i).2)) () -
              ∫ x, phiAF p.1.2.1 p.1.2.2 x ∂muW p.1.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF p.1.2.1 p.1.2.2; muW p.1.1])} ∧
    ∀ p : SProg (SampleIn 2 n dA dF) Unit,
      (∀ u W A F, p.eval (sampleVal u W A F) () =
        bwEval F (bwEval A (sphProj (bwEval W u))) 0) →
      (gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).cost < p.cost := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  obtain ⟨h1, h2⟩ := w8s_general n k dA dF hn hk1 hk2 hdA hdF
    (θ := 17 / 20) (ι := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨le_trans ?_ h1, h2⟩
  have := delta_k1e6 n dA k hn hdA hk
  linarith

/-! ## The nested form -/

lemma measurableSet_succ (τ : ℝ) :
    MeasurableSet {p : Theta n dA dF × Draws (2 * n) n k |
      Succ p.1.1 τ (phiAF p.1.2.1 p.1.2.2) p.2} := by
  have hΦ : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) => phiAF p.1.2.1 p.1.2.2 p.2) := by
    have hm : Measurable (fun p : Theta n dA dF × (Fin n → ℝ) =>
        (((p.1.2.1, p.1.2.2), p.2) :
          ((CoefIdx n n dA → ℝ) × (CoefIdx n 1 dF → ℝ)) × (Fin n → ℝ))) :=
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
    exact (measPhi108 n dA dF).comp hm
  obtain ⟨hg, hB, hV⟩ := measGen108 (2 * n) n (2 * dA) k (Theta n dA dF) (fun t => t.1)
    (fun _ => τ) (fun t => phiAF t.2.1 t.2.2) measurable_fst measurable_const hΦ
  unfold Succ Err
  exact measurableSet_le ((hg.sub (hB.comp measurable_fst)).abs)
    (((hV.comp measurable_fst).sqrt).const_mul _)

/-- **The nested form from a joint bound** (Markov): if the joint success probability is at least
`1 − δ`, then with probability at least `1 − √δ` over `(W, F)`, the success probability over `A`
and the blocks is at least `1 − √δ`. -/
theorem nested_of_joint (hn : 1 ≤ n) (hd : 1 ≤ 2 * dA) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : 1 - δ ≤ (PS n dA dF k).real
      {p | Succ p.1.1 (tauPaper (2 * n) n (2 * dA)) (phiAF p.1.2.1 p.1.2.2) p.2}) :
    1 - Real.sqrt δ ≤
      ((bwSphere (2 * n) n (2 * dA)).prod (bwSphere n 1 dF)).real
        {wf | 1 - Real.sqrt δ ≤
          ((bwSphere n n dA).prod
            (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
            {aω | Good108 hd wf.1 aω.1 wf.2 aω.2}} := by
  have := drawM_prob (2 * n) n k (by omega)
  set τ := tauPaper (2 * n) n (2 * dA) with hτ
  set e : Theta n dA dF × Draws (2 * n) n k →
      ((CoefIdx (2 * n) n (2 * dA) → ℝ) × (CoefIdx n 1 dF → ℝ)) ×
        ((CoefIdx n n dA → ℝ) × Draws (2 * n) n k) :=
    fun p => ((p.1.1, p.1.2.2), (p.1.2.1, p.2)) with he
  have hem : Measurable e :=
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  set e' : ((CoefIdx (2 * n) n (2 * dA) → ℝ) × (CoefIdx n 1 dF → ℝ)) ×
        ((CoefIdx n n dA → ℝ) × Draws (2 * n) n k) → Theta n dA dF × Draws (2 * n) n k :=
    fun q => ((q.1.1, (q.2.1, q.1.2)), q.2.2) with he'
  have he'm : Measurable e' :=
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))).prodMk
      (measurable_snd.comp measurable_snd)
  set E : Set (Theta n dA dF × Draws (2 * n) n k) :=
    {p | Succ p.1.1 τ (phiAF p.1.2.1 p.1.2.2) p.2} with hE
  have hEm : MeasurableSet E := measurableSet_succ τ
  have hE'm : MeasurableSet (e' ⁻¹' E) := he'm hEm
  have hmap := rearr108 _ _ _ _ (bwSphere (2 * n) n (2 * dA)) (bwSphere n n dA) (bwSphere n 1 dF)
    (drawM (2 * n) n k)
  have hjoint : 1 - δ ≤ (((bwSphere (2 * n) n (2 * dA)).prod (bwSphere n 1 dF)).prod
      ((bwSphere n n dA).prod (drawM (2 * n) n k))).real (e' ⁻¹' E) := by
    rw [← hmap, map_measureReal_apply hem hE'm]
    exact h
  have hN := nested108 _ _ ((bwSphere (2 * n) n (2 * dA)).prod (bwSphere n 1 dF))
    ((bwSphere n n dA).prod (drawM (2 * n) n k)) (e' ⁻¹' E) δ hE'm hδ hjoint
  refine le_trans hN (le_of_eq ?_)
  congr 1
  ext wf
  simp only [Set.mem_ofPred_eq]
  have : {b : (CoefIdx n n dA → ℝ) × Draws (2 * n) n k | (wf, b) ∈ e' ⁻¹' E} =
      {aω | Good108 hd wf.1 aω.1 wf.2 aω.2} := by
    ext b
    exact (good_iff_succ hd wf.1 b.1 wf.2 b.2).symm
  rw [this]

/-- **The nested form with the explicit bound**: with probability at least `1 − √δ` over
`(W, F)`, the probability over `A` and the blocks of `|g − B| ≤ (1/2)·sd_μ` is at least `1 − √δ`,
`δ = delta108 n dA k θ ι`. -/
theorem nested108_general (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 1 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) {θ ι : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hι : 0 < ι) (hι1 : ι < 1) {δ : ℝ} (hδ : delta108 n dA k θ ι ≤ δ) (hδ0 : 0 ≤ δ) :
    1 - Real.sqrt δ ≤
      ((bwSphere (2 * n) n (2 * dA)).prod (bwSphere n 1 dF)).real
        {wf | 1 - Real.sqrt δ ≤
          ((bwSphere n n dA).prod
            (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
            {aω | Good108 (by rcases hdA with h | h <;> omega) wf.1 aω.1 wf.2 aω.2}} :=
  nested_of_joint (by omega) _ hδ0
    ((by linarith : 1 - δ ≤ 1 - delta108 n dA k θ ι).trans
      (joint_succ hn hk hk2 hdA hdF hθ hθ1 hι hι1))

/-- **The nested form, `k ≥ 10⁶`**: with probability at least `929/1000` over `(W, F)`, the
probability over `A` and the blocks of `|g − B| ≤ (1/2)·sd_μ` is at least `929/1000`. -/
theorem nested108_k1e6 (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 10 ^ 6 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    929 / 1000 ≤
      ((bwSphere (2 * n) n (2 * dA)).prod (bwSphere n 1 dF)).real
        {wf | 929 / 1000 ≤
          ((bwSphere n n dA).prod
            (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
            {aω | Good108 (by rcases hdA with h | h <;> omega) wf.1 aω.1 wf.2 aω.2}} := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have h := nested108_general n k dA dF hn hk1 hk2 hdA hdF (θ := 17 / 20) (ι := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (δ := 1 / 200)
    (delta_k1e6 n dA k hn hdA hk) (by norm_num)
  have hs : Real.sqrt (1 / 200) ≤ 71 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  refine le_trans (by linarith) (h.trans (measureReal_mono ?_))
  intro wf hwf
  simp only [Set.mem_ofPred_eq] at hwf ⊢
  linarith

/-- **The nested form, `k ≥ 5000`**: with probability at least `9/10` over `(W, F)`, the
probability over `A` and the blocks of `|g − B| ≤ (1/2)·sd_μ` is at least `9/10`. -/
theorem nested108_k5000 (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 5000 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) :
    9 / 10 ≤
      ((bwSphere (2 * n) n (2 * dA)).prod (bwSphere n 1 dF)).real
        {wf | 9 / 10 ≤
          ((bwSphere n n dA).prod
            (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
            {aω | Good108 (by rcases hdA with h | h <;> omega) wf.1 aω.1 wf.2 aω.2}} := by
  have h := nested108_general n k dA dF hn (by omega) hk2 hdA hdF (θ := 7 / 10) (ι := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (δ := 1 / 100)
    (delta_k5000 n dA k hn hdA hk) (by norm_num)
  have hs : Real.sqrt (1 / 100) ≤ 1 / 10 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  refine le_trans (by linarith) (h.trans (measureReal_mono ?_))
  intro wf hwf
  simp only [Set.mem_ofPred_eq] at hwf ⊢
  linarith

end BstLean.Part108

#print axioms BstLean.Part108.w8s_general
#print axioms BstLean.Part108.main108
#print axioms BstLean.Part108.main108_k1e6
#print axioms BstLean.Part108.nested108_general
#print axioms BstLean.Part108.nested108_k1e6
#print axioms BstLean.Part108.nested108_k5000
#print axioms BstLean.Part108.core_gauss
#print axioms BstLean.Part108.gauss_fixed
#print axioms BstLean.Part108.sphere_succ
