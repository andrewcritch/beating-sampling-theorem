import BstLean.Part151VA

/-!
# Part 151, Proposition VA (b), stage (b): joint measurability

Every quantity of the event `E` is an integral with parameters of a jointly measurable integrand.
The lemmas are in "composition form": `α` is any measurable space and `fW`, `fA`, `fθ`, `fc`,
`fσ`, `fη` are measurable maps from `α` to the variables. So one lemma gives the measurability in
all variables, and also in `c` alone with the other variables fixed.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part134 (lam res sig measurable_mulVec_joint)
open BstLean.Part136 (HidParam hidGauss continuous_hid2_joint measurable_lam2 measurable_res2
  measurable_sig2)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA measurable_cenA measurable_tauWA)
open BstLean.Part149 (thA tauOutOf measurable_thA measurable_tauOutOf)
open BstLean.Part150 (CMap)

section meas

variable {n : ℕ} {α : Type*} [MeasurableSpace α]

/-- An integral with a parameter of a jointly measurable function is measurable. -/
lemma meas_int {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] {g : α × X → ℝ}
    (hg : Measurable g) : Measurable (fun a => ∫ x, g (a, x) ∂μ) :=
  hg.stronglyMeasurable.integral_prod_right'.measurable

lemma meas_hid2v {d m : ℕ} {fθ : α → HidParam d m} {fy : α → Fin d → ℝ} (hθ : Measurable fθ)
    (hy : Measurable fy) : Measurable (fun a => hid2 (fθ a).1 (fθ a).2 (fy a)) :=
  (continuous_hid2_joint (N := d) (m := m)).measurable.comp (hθ.prodMk hy)

lemma meas_hid2 {d m : ℕ} {fθ : α → HidParam d m} {fy : α → Fin d → ℝ} (hθ : Measurable fθ)
    (hy : Measurable fy) (i : Fin m) : Measurable (fun a => hid2 (fθ a).1 (fθ a).2 (fy a) i) :=
  (measurable_pi_apply i).comp (meas_hid2v hθ hy)

variable {bh : CMap n} {fW : α → MlpParam (2 * n) (mW n) n} {fA : α → MlpParam n (mA n) n}

lemma meas_cenB (hbh : Measurable bh) (hW : Measurable fW) (hA : Measurable fA) :
    Measurable (fun a => cenB bh (fW a) (fA a)) :=
  hbh.comp (hW.prodMk (measurable_thA.comp hA))

lemma meas_cAv (hbh : Measurable bh) (hW : Measurable fW) (hA : Measurable fA) :
    Measurable (fun a => cAv bh (fW a) (fA a)) := by
  have h3 : Measurable (fun a => (fA a).2.2) := measurable_snd.comp (measurable_snd.comp hA)
  exact (measurable_mulVec_joint (n := n) (m := mA n)).comp (h3.prodMk (meas_cenB hbh hW hA))

lemma meas_sigP (hbh : Measurable bh) (hW : Measurable fW) (hA : Measurable fA) :
    Measurable (fun a => sigP bh (fW a) (fA a)) :=
  (measurable_tauOutOf (n := n) (m := mA n)).comp (meas_cenB hbh hW hA)

lemma meas_xIn {fξ : α → Fin n → ℝ} (hW : Measurable fW) (hξ : Measurable fξ) :
    Measurable (fun a => xIn (fW a) (fξ a)) :=
  measurable_sphPt.comp ((measurable_cenA.comp hW).add ((measurable_tauWA.comp hW).smul hξ))

lemma meas_a2v {fξ : α → Fin n → ℝ} (hW : Measurable fW) (hA : Measurable fA)
    (hξ : Measurable fξ) : Measurable (fun a => a2v (fW a) (fA a) (fξ a)) := by
  have hθ : Measurable (fun a => (((fA a).1, (fA a).2.1) : HidParam n (mA n))) :=
    (measurable_fst.comp hA).prodMk (measurable_fst.comp (measurable_snd.comp hA))
  exact meas_hid2v hθ (meas_xIn hW hξ)

lemma meas_lamX {fξ : α → Fin n → ℝ} (hbh : Measurable bh) (hW : Measurable fW)
    (hA : Measurable fA) (hξ : Measurable fξ) :
    Measurable (fun a => lamX bh (fW a) (fA a) (fξ a)) :=
  measurable_lam2.comp ((meas_cenB hbh hW hA).prodMk (meas_a2v hW hA hξ))

lemma meas_sigX {fξ : α → Fin n → ℝ} (hbh : Measurable bh) (hW : Measurable fW)
    (hA : Measurable fA) (hξ : Measurable fξ) :
    Measurable (fun a => sigX bh (fW a) (fA a) (fξ a)) := by
  have hr : Measurable (fun a => res (cenB bh (fW a) (fA a)) (a2v (fW a) (fA a) (fξ a))) :=
    measurable_res2.comp ((meas_cenB hbh hW hA).prodMk (meas_a2v hW hA hξ))
  have h : Measurable (fun a => Real.sqrt (2 / (mA n : ℝ)) *
      Real.sqrt (normSq (res (cenB bh (fW a) (fA a)) (a2v (fW a) (fA a) (fξ a))))) :=
    measurable_const.mul (measurable_normSq.comp hr).sqrt
  simpa only [sigX, sig] using h

/-- `λ(x)·c + σ(x)·η′` is jointly measurable. -/
lemma meas_Xc {fc : α → Fin n → ℝ} {fq : α → (Fin n → ℝ) × (Fin n → ℝ)} (hbh : Measurable bh)
    (hW : Measurable fW) (hA : Measurable fA) (hc : Measurable fc) (hq : Measurable fq) :
    Measurable (fun a => lamX bh (fW a) (fA a) (fq a).1 • fc a +
      sigX bh (fW a) (fA a) (fq a).1 • (fq a).2) :=
  ((meas_lamX hbh hW hA (measurable_fst.comp hq)).smul hc).add
    ((meas_sigX hbh hW hA (measurable_fst.comp hq)).smul (measurable_snd.comp hq))

lemma meas_Yc {fc : α → Fin n → ℝ} {fq : α → (Fin n → ℝ) × (Fin n → ℝ)} (hbh : Measurable bh)
    (hW : Measurable fW) (hA : Measurable fA) (hc : Measurable fc) (hq : Measurable fq) :
    Measurable (fun a => fc a + sigP bh (fW a) (fA a) • (fq a).2) :=
  hc.add ((meas_sigP hbh hW hA).smul (measurable_snd.comp hq))

variable {fθ : α → HidParam n (mF n)}

/-- `Δ_m` as a function of all variables and of `c`. -/
lemma meas_dMc {fc : α → Fin n → ℝ} (hbh : Measurable bh) (hW : Measurable fW)
    (hA : Measurable fA) (hθ : Measurable fθ) (hc : Measurable fc) (i : Fin (mF n)) :
    Measurable (fun a => dMc bh (fW a) (fA a) (fθ a) (fc a) i) := by
  have hf1 : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) => p.1) := measurable_fst
  have hf2 : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) => p.2) := measurable_snd
  have hg : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      hid2 (fθ p.1).1 (fθ p.1).2 (lamX bh (fW p.1) (fA p.1) p.2.1 • fc p.1 +
          sigX bh (fW p.1) (fA p.1) p.2.1 • p.2.2) i -
        hid2 (fθ p.1).1 (fθ p.1).2 (fc p.1 + sigP bh (fW p.1) (fA p.1) • p.2.2) i) :=
    (meas_hid2 (hθ.comp hf1)
      (meas_Xc hbh (hW.comp hf1) (hA.comp hf1) (hc.comp hf1) hf2) i).sub
      (meas_hid2 (hθ.comp hf1)
        (meas_Yc hbh (hW.comp hf1) (hA.comp hf1) (hc.comp hf1) hf2) i)
  exact meas_int (P2 n) hg

lemma meas_dM (hbh : Measurable bh) (hW : Measurable fW) (hA : Measurable fA)
    (hθ : Measurable fθ) (i : Fin (mF n)) :
    Measurable (fun a => dM bh (fW a) (fA a) (fθ a) i) :=
  meas_dMc hbh hW hA hθ (meas_cAv hbh hW hA) i

lemma meas_Dc (hbh : Measurable bh) (hW : Measurable fW) (hA : Measurable fA) :
    Measurable (fun a => Dc bh (fW a) (fA a)) := by
  have hf1 : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) => p.1) := measurable_fst
  have hf2 : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) => p.2) := measurable_snd
  have hg : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      normSq ((lamX bh (fW p.1) (fA p.1) p.2.1 • cAv bh (fW p.1) (fA p.1) +
          sigX bh (fW p.1) (fA p.1) p.2.1 • p.2.2) -
        (cAv bh (fW p.1) (fA p.1) + sigP bh (fW p.1) (fA p.1) • p.2.2))) :=
    measurable_normSq.comp
      ((meas_Xc hbh (hW.comp hf1) (hA.comp hf1)
        (meas_cAv hbh (hW.comp hf1) (hA.comp hf1)) hf2).sub
      (meas_Yc hbh (hW.comp hf1) (hA.comp hf1)
        (meas_cAv hbh (hW.comp hf1) (hA.comp hf1)) hf2))
  exact meas_int (P2 n) hg

/-- `z_F(c + σγ)` is jointly measurable. -/
lemma meas_zSv {m : ℕ} {gθ : α → HidParam n m} {fc : α → Fin n → ℝ} {fσ : α → ℝ}
    {fγ : α → Fin n → ℝ} (hθ : Measurable gθ) (hc : Measurable fc) (hσ : Measurable fσ)
    (hγ : Measurable fγ) : Measurable (fun a => zS (gθ a) (fc a) (fσ a) (fγ a)) :=
  meas_hid2v hθ (hc.add (hσ.smul hγ))

lemma meas_dSamp {m : ℕ} {gθ : α → HidParam n m} {fc : α → Fin n → ℝ} {fσ : α → ℝ} {k : ℕ}
    {fη : α → Fin k → Fin n → ℝ} (hθ : Measurable gθ) (hc : Measurable fc)
    (hσ : Measurable fσ) (hη : Measurable fη) (i : Fin m) :
    Measurable (fun a => dSamp (gθ a) (fc a) (fσ a) k (fη a) i) := by
  unfold dSamp
  refine Measurable.sub (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)) ?_
  · exact (measurable_pi_apply i).comp
      (meas_zSv hθ hc hσ ((measurable_pi_apply j).comp hη))
  · have hf1 : Measurable (fun p : α × (Fin n → ℝ) => p.1) := measurable_fst
    have hg : Measurable (fun p : α × (Fin n → ℝ) => zS (gθ p.1) (fc p.1) (fσ p.1) p.2 i) :=
      (measurable_pi_apply i).comp
        (meas_zSv (hθ.comp hf1) (hc.comp hf1) (hσ.comp hf1) measurable_snd)
    exact meas_int (stdGauss (Fin n)) hg

lemma meas_IzS {m : ℕ} {gθ : α → HidParam n m} {fc : α → Fin n → ℝ} {fσ : α → ℝ}
    (hθ : Measurable gθ) (hc : Measurable fc) (hσ : Measurable fσ) :
    Measurable (fun a => ∫ γ, normSq (zS (gθ a) (fc a) (fσ a) γ) ∂stdGauss (Fin n)) := by
  have hf1 : Measurable (fun p : α × (Fin n → ℝ) => p.1) := measurable_fst
  have hg : Measurable (fun p : α × (Fin n → ℝ) =>
      normSq (zS (gθ p.1) (fc p.1) (fσ p.1) p.2)) :=
    measurable_normSq.comp (meas_zSv (hθ.comp hf1) (hc.comp hf1) (hσ.comp hf1) measurable_snd)
  exact meas_int (stdGauss (Fin n)) hg

lemma meas_Ts {m : ℕ} {gθ : α → HidParam n m} {fc : α → Fin n → ℝ} {fσ : α → ℝ} {k : ℕ}
    {fη : α → Fin k → Fin n → ℝ} (hθ : Measurable gθ) (hc : Measurable fc)
    (hσ : Measurable fσ) (hη : Measurable fη) :
    Measurable (fun a => Ts (gθ a) (fc a) (fσ a) k (fη a)) := by
  unfold Ts normSq
  exact (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (meas_dSamp hθ hc hσ hη i).pow_const 2)).sqrt

lemma meas_dU (hbh : Measurable bh) (hW : Measurable fW) (hA : Measurable fA)
    (hθ : Measurable fθ) (i : Fin (mF n)) :
    Measurable (fun a => dU bh (fW a) (fA a) (fθ a) i) := by
  unfold dU
  refine Measurable.sub ?_ ?_
  · have hf1 : Measurable (fun p : α × (Fin n → ℝ) => p.1) := measurable_fst
    have hy : Measurable (fun p : α × (Fin n → ℝ) => mlpEval (fA p.1) (xIn (fW p.1) p.2)) :=
      (continuous_mlpEval_joint (k := n) (m := mA n) (q := n)).measurable.comp
        ((hA.comp hf1).prodMk (meas_xIn (hW.comp hf1) measurable_snd))
    exact meas_int (stdGauss (Fin n)) (meas_hid2 (hθ.comp hf1) hy i)
  · have hf1 : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) => p.1) := measurable_fst
    have hf2 : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) => p.2) := measurable_snd
    have hg : Measurable (fun p : α × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        hid2 (fθ p.1).1 (fθ p.1).2 (lamX bh (fW p.1) (fA p.1) p.2.1 • cAv bh (fW p.1) (fA p.1) +
          sigX bh (fW p.1) (fA p.1) p.2.1 • p.2.2) i) :=
      meas_hid2 (hθ.comp hf1)
        (meas_Xc hbh (hW.comp hf1) (hA.comp hf1) (meas_cAv hbh (hW.comp hf1) (hA.comp hf1)) hf2) i
    exact meas_int (P2 n) hg

lemma meas_TU {fA1 : α → Matrix (Fin (mA n)) (Fin n) ℝ}
    {fA2 : α → Matrix (Fin (mA n)) (Fin (mA n)) ℝ} {fA3 : α → Matrix (Fin n) (Fin (mA n)) ℝ}
    (hbh : Measurable bh) (hW : Measurable fW) (h1 : Measurable fA1) (h2 : Measurable fA2)
    (h3 : Measurable fA3) (hθ : Measurable fθ) :
    Measurable (fun a => TU bh (fW a) (fA1 a) (fA2 a) (fθ a) (fA3 a)) := by
  have hA' : Measurable (fun a => ((fA1 a, fA2 a, fA3 a) : MlpParam n (mA n) n)) :=
    h1.prodMk (h2.prodMk h3)
  have hd : ∀ i, Measurable (fun a => dU bh (fW a) (fA1 a, fA2 a, fA3 a) (fθ a) i) :=
    fun i => meas_dU hbh hW hA' hθ i
  have h : Measurable (fun a => √(2 / (mF n : ℝ) *
      ∑ i, dU bh (fW a) (fA1 a, fA2 a, fA3 a) (fθ a) i ^ 2)) :=
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => (hd i).pow_const 2)).sqrt
  simpa only [TU, normSq] using h

/-- `Φ_U` at `c`, as a function of all variables and of `c`. -/
lemma meas_PhiU {fc : α → Fin n → ℝ} (hbh : Measurable bh) (hW : Measurable fW)
    (hA : Measurable fA) (hθ : Measurable fθ) (hc : Measurable fc) :
    Measurable (fun a => PhiU bh (fW a) (fA a).1 (fA a).2.1 (fθ a) (fc a)) := by
  -- the inner integrand, on `(α × matrices) × ξ`
  have hf1 : Measurable (fun p : (α × Matrix (Fin n) (Fin (mA n)) ℝ) × (Fin n → ℝ) => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hM : Measurable (fun p : (α × Matrix (Fin n) (Fin (mA n)) ℝ) × (Fin n → ℝ) => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hξ : Measurable (fun p : (α × Matrix (Fin n) (Fin (mA n)) ℝ) × (Fin n → ℝ) => p.2) :=
    measurable_snd
  have hr : Measurable (fun p : (α × Matrix (Fin n) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      res (cenB bh (fW p.1.1) (fA p.1.1)) (a2v (fW p.1.1) (fA p.1.1) p.2)) :=
    measurable_res2.comp ((meas_cenB hbh (hW.comp hf1) (hA.comp hf1)).prodMk
      (meas_a2v (hW.comp hf1) (hA.comp hf1) hξ))
  have hy : Measurable (fun p : (α × Matrix (Fin n) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      lamX bh (fW p.1.1) (fA p.1.1) p.2 • fc p.1.1 +
        p.1.2 *ᵥ res (cenB bh (fW p.1.1) (fA p.1.1)) (a2v (fW p.1.1) (fA p.1.1) p.2)) :=
    ((meas_lamX hbh (hW.comp hf1) (hA.comp hf1) hξ).smul (hc.comp hf1)).add
      ((measurable_mulVec_joint (n := n) (m := mA n)).comp (hM.prodMk hr))
  have hj := (measurable_jacFro_joint (n := n) (m := mF n)).comp ((hθ.comp hf1).prodMk hy)
  have hg := (measurable_const (a := (2 / (mF n : ℝ)))).mul hj
  have h1 := meas_int (stdGauss (Fin n)) hg
  have h2 := meas_int (gaussMat n (mA n) (2 / (mA n : ℝ))) h1
  simp only [Function.comp_def, Pi.mul_apply, lamX, cenB, a2v, thA] at h2
  simp only [PhiU, yU, yG, lamU, rU, hU]
  exact h2

/-- The direction `w_×` as a function of all variables and of `c`. -/
lemma meas_wX {fc : α → Fin n → ℝ} {k : ℕ} {fη : α → Fin k → Fin n → ℝ} (hbh : Measurable bh)
    (hW : Measurable fW) (hA : Measurable fA) (hθ : Measurable fθ) (hη : Measurable fη)
    (hc : Measurable fc) (i : Fin (mF n)) :
    Measurable (fun a => wX bh (fW a) (fA a) (fθ a) k (fη a) (fc a) i) := by
  have hd : ∀ j, Measurable (fun a => dSamp (fθ a) (fc a) (sigP bh (fW a) (fA a)) k (fη a) j -
      dMc bh (fW a) (fA a) (fθ a) (fc a) j) := fun j =>
    (meas_dSamp hθ hc (meas_sigP hbh hW hA) hη j).sub (meas_dMc hbh hW hA hθ hc j)
  have hn : Measurable (fun a => (nrm (dSamp (fθ a) (fc a) (sigP bh (fW a) (fA a)) k (fη a) -
      dMc bh (fW a) (fA a) (fθ a) (fc a)))⁻¹) := by
    unfold nrm normSq
    exact ((Finset.measurable_sum _ fun j _ => (hd j).pow_const 2).sqrt).inv
  exact hn.mul (hd i)

end meas

end BstLean.Part151
