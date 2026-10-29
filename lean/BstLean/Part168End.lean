import BstLean.Part168X

/-!
# Part 168 (file `End`): the end theorem with Lemma LJ fully proved

No proof is left open; no `native_decide` or `axiom` is used.

* `X2q_pos`: `X2q n (qn n) > 0`.
* **`LJ_proved`**: `JM_hyp n (47/10)` for every `n ≥ 80 000`: Lemma LJ on the explicit Jacobian,
  with no hypothesis (`X_hyp_proved`, `Y_bound`, `K2_num`, `JM_of_XY`).
* **`classifier_paper_LG80k`**: Part 167's `classifier_paper_X80k` with `X_hyp` and the numerics
  `K2XY ≤ 4.7` removed. The remaining hypotheses are `BIAS_hyp` on the good set and the charge of
  the caller's `E_A` within `roomE ≥ 0.001792`. No new charge is added: `X` and `K2XY` are moment
  bounds over the weights, and the certificate event they feed (Part 166's `E_lat` at `K² = 4.7`,
  charge `12·10⁻⁴`) is already in `roomE`.
-/

namespace BstLean.Part168

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part167

variable {n : ℕ}

lemma X2q_pos (hn : 80000 ≤ n) : 0 < X2q n (qn n) := by
  unfold X2q
  have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    exact_mod_cast this
  have hB : 0 < BL (mA n) := by unfold BL; positivity
  have hR : 0 < ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) := Real.rpow_pos_of_pos hm0 _
  have h1 : 0 < (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) :=
    div_pos (by linarith) (by linarith)
  have h2 : 0 < ((n - 1 - 1 : ℕ) : ℝ) + 128 * (qn n : ℝ) := by positivity
  positivity

/-- **Lemma LJ is proved** (paper `t7:p07:LJ` at `ℓ = 128`, `K² ≤ 4.7`), every `n ≥ 80 000`. -/
theorem LJ_proved (hn : 80000 ≤ n) : JM_hyp n (47 / 10) :=
  JM_mono (by unfold K2XY; positivity) (K2_num hn)
    (JM_of_XY (by omega) (X2q_pos hn) (Y2n_pos (by omega))
      (XY_of_X hn (X_hyp_proved (by omega) (by have := q_ge hn; omega))))

open BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157 BstLean.Part160 in
open BstLean.Part161 (BIAS_hyp) in
open BstLean.Part162 (dPaper) in
open BstLean.Part166 (goodD) in
/-- **The classifier theorem with Proposition LG fully proved** (every `n ≥ 80 000`, floor
`d_low = 0.22005`, room `roomE ≥ 0.001792`). Remaining: `BIAS_hyp` on the good set, and the
charge of the caller's event `E_A` within `roomE`. -/
theorem classifier_paper_LG80k (hn : 80000 ≤ n)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_X80k hn (X2q_pos hn) (X_hyp_proved (by omega) (by have := q_ge hn; omega))
    (K2_num hn) fT wT hf hw t hEA hA hroom hB

end BstLean.Part168
