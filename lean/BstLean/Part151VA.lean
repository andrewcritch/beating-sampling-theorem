import BstLean.Part151Sharp
import BstLean.Part151U5
import BstLean.Part151ST2
import BstLean.Part151ON

/-!
# Part 151, Proposition VA (b), stage (a): the deterministic bound of the conditional variance

Role: `delegations/statements/p151-spec.md`, items 3 and 4. Paper source:
`proofs/option-n/theorem5-13-events-final.tex`, Proposition VA (b).

Variables: `W`, `A = (A₁, A₂, A₃)`, `θF = (F₁, F₂)`, `η`; `b = cenB bh W A`, `c_A = cAv bh W A`,
`σ_p = sigP bh W A`, `t_F = 2/m_F`.

* `wdir v`: the direction `v/|v|` (`0` for `v = 0`); `dMc`: `Δ_m` as a function of `c_A = c`;
  `wX`: the direction `w_×` of `Δ_s − Δ_m` as a function of `c`.
* `CrOK`: the hypothesis `‖C_r‖_op ≤ Mr`.
* `ellS`, `tauM`, `tauS`, `uU`, `tauU`, `vbar`: the thresholds.
* `GoodVA`: the list of the conditions that hold on the event `E` of the proof.
* **`vHat_le_of_good`**: under `GoodVA`: `V′ = t_F·|Δ̂′|² ≤ vbar`
  `= τ_U² + (τ_s + τ_m)² + 2(τ_s + τ_m)·u_U`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part132 (nrm nrm_sq nrm_nonneg)
open BstLean.Part134 (lam res sig)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part149 (thA tauOutOf)
open BstLean.Part150 (CMap)

/-! ## The direction of a vector -/

section dir

variable {ι : Type*} [Fintype ι]

/-- `v/|v|`, and `0` for `v = 0`. -/
noncomputable def wdir (v : ι → ℝ) : ι → ℝ := (nrm v)⁻¹ • v

lemma wdir_spec (v : ι → ℝ) : v = nrm v • wdir v := by
  unfold wdir
  rw [smul_smul]
  by_cases h : nrm v = 0
  · have h2 : normSq v = 0 := by rw [← nrm_sq, h]; norm_num
    have hv : v = 0 := by
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp h2 j
        (Finset.mem_univ j)
      simpa using this
    rw [hv]; simp
  · rw [mul_inv_cancel₀ h, one_smul]

lemma wdir_le (v : ι → ℝ) : normSq (wdir v) ≤ 1 := by
  unfold wdir
  rw [normSq_smul, ← nrm_sq v]
  by_cases h : nrm v = 0
  · rw [h]; norm_num
  · rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 h)]

end dir

section defs

variable {n : ℕ}

/-- `Δ_m` as a function of `c_A = c` (the other variables fixed). -/
noncomputable def dMc (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (θF : HidParam n (mF n)) (c : Fin n → ℝ) : Fin (mF n) → ℝ :=
  dPair (P2 n) (fun q => lamX bh W A q.1 • c + sigX bh W A q.1 • q.2)
    (fun q => c + sigP bh W A • q.2) θF

lemma dM_eq_dMc (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (θF : HidParam n (mF n)) : dM bh W A θF = dMc bh W A θF (cAv bh W A) := rfl

/-- The direction `w_×` of `Δ_s − Δ_m`, as a function of `c_A = c`. -/
noncomputable def wX (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (θF : HidParam n (mF n)) (k : ℕ) (η : Fin k → Fin n → ℝ) (c : Fin n → ℝ) :
    Fin (mF n) → ℝ :=
  wdir (dSamp θF c (sigP bh W A) k η - dMc bh W A θF c)

/-- **The hypothesis `‖C_r‖_op ≤ Mr`** (`C_r = t_A·E r rᵀ`, `r` the residual of `a₂(x)`). -/
def CrOK (bh : CMap n) (W : MlpParam (2 * n) (mW n) n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (Mr : ℝ) : Prop :=
  ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
    (∑ j, res (bh (W, (A₁, A₂))) (hU W A₁ A₂ ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      Mr * ∑ j, w j ^ 2

/-- A bound of the Lipschitz constant `ℓ_s` of the sampling term: `√(t_F·LF²·(2/n)/k)`. -/
noncomputable def ellS (n k : ℕ) (LF : ℝ) : ℝ := √(2 / (mF n : ℝ) * LF ^ 2 * (2 / (n : ℝ)) / k)

/-- `τ_m = √((1 + δ)²·(2/n)·D̄)`. -/
noncomputable def tauM (n : ℕ) (δ Dbar : ℝ) : ℝ := √((1 + δ) * (1 + δ) * (2 / (n : ℝ) * Dbar))

/-- `u_s = √(2L_c)·ℓ̄_s`. -/
noncomputable def uS (n k : ℕ) (LF Lc : ℝ) : ℝ := √(2 * Lc) * ellS n k LF

/-- `τ_s = √((1 + δ)²·(2/n)·Ē/k) + u_s`. -/
noncomputable def tauS (n k : ℕ) (δ Ebar LF Lc : ℝ) : ℝ :=
  √((1 + δ) * (1 + δ) * (2 / (n : ℝ) * Ebar) / k) + uS n k LF Lc

/-- `u_U = √(2L_c)·ℓ_U`. -/
noncomputable def uU (n : ℕ) (LF Mr Lc : ℝ) : ℝ := √(2 * Lc) * ellU n LF Mr

/-- `τ_U = √(Mr·2(1 + δ)²) + u_U`. -/
noncomputable def tauU (n : ℕ) (δ LF Mr Lc : ℝ) : ℝ :=
  √(Mr * (2 * (1 + δ) * (1 + δ))) + uU n LF Mr Lc

/-- The bound of the conditional variance: `τ_U² + (τ_s + τ_m)² + 2(τ_s + τ_m)·u_U`. -/
noncomputable def vbar (n k : ℕ) (δ Dbar Ebar LF Mr Lc : ℝ) : ℝ :=
  tauU n δ LF Mr Lc ^ 2 + (tauS n k δ Ebar LF Lc + tauM n δ Dbar) ^ 2 +
    2 * (tauS n k δ Ebar LF Lc + tauM n δ Dbar) * uU n LF Mr Lc

/-- The conditions that hold on the event `E` of Proposition VA, for one value of the
variables. -/
structure GoodVA (bh : CMap n) (k : ℕ) (δ Dbar Ebar LF Mr Lc : ℝ)
    (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) (θF : HidParam n (mF n))
    (η : Fin k → Fin n → ℝ) : Prop where
  hb : cenB bh W A ≠ 0
  hMr : CrOK bh W A.1 A.2.1 Mr
  hD : Dc bh W A ≤ Dbar
  hE : normSq (cAv bh W A) + n * sigP bh W A ^ 2 ≤ Ebar
  hTm : ¬ ((1 + δ) * (1 + δ) * (2 / (n : ℝ) * Dc bh W A) <
    2 / (mF n : ℝ) * normSq (dM bh W A θF))
  hFE : ¬ ((1 + δ) * (1 + δ) * (2 / (n : ℝ) * (normSq (cAv bh W A) + n * sigP bh W A ^ 2)) <
    2 / (mF n : ℝ) * ∫ γ, normSq (zS θF (cAv bh W A) (sigP bh W A) γ) ∂stdGauss (Fin n))
  hJU : ¬ (2 * (1 + δ) * (1 + δ) < PhiU bh W A.1 A.2.1 θF (cAv bh W A))
  hs : ¬ (√(2 / (mF n : ℝ) * ((∫ γ, normSq (zS θF (cAv bh W A) (sigP bh W A) γ)
      ∂stdGauss (Fin n)) / k)) + uS n k LF Lc ≤ Ts θF (cAv bh W A) (sigP bh W A) k η)
  hU : TU bh W A.1 A.2.1 θF A.2.2 <
      √(Mr * PhiU bh W A.1 A.2.1 θF (cAv bh W A)) + uU n LF Mr Lc ∧
    -(√(2 / (mF n : ℝ)) * ∑ i, wX bh W A θF k η (cAv bh W A) i * dU bh W A θF i) <
      uU n LF Mr Lc

lemma uS_nonneg (n k : ℕ) (LF Lc : ℝ) : 0 ≤ uS n k LF Lc := by unfold uS ellS; positivity

lemma uU_nonneg (n : ℕ) (LF Mr Lc : ℝ) : 0 ≤ uU n LF Mr Lc := by unfold uU ellU; positivity

/-- **Proposition VA (b), deterministic form.** If the conditions `GoodVA` hold, then
`V′ = t_F·|Δ̂′|² ≤ τ_U² + (τ_s + τ_m)² + 2(τ_s + τ_m)·u_U`. -/
theorem vHat_le_of_good (hn : 1 ≤ n) {bh : CMap n} {k : ℕ} (hk : 1 ≤ k)
    {δ Dbar Ebar LF Mr Lc : ℝ} (hδ : 0 < δ) (hMr0 : 0 ≤ Mr)
    {W : MlpParam (2 * n) (mW n) n} {A : MlpParam n (mA n) n} {θF : HidParam n (mF n)}
    {η : Fin k → Fin n → ℝ} (hg : GoodVA bh k δ Dbar Ebar LF Mr Lc W A θF η) :
    vHat bh k ((W, A, θF), η) ≤ vbar n k δ Dbar Ebar LF Mr Lc := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have htF : (0 : ℝ) ≤ 2 / (mF n : ℝ) := by positivity
  have hd2 : (0 : ℝ) ≤ (1 + δ) * (1 + δ) := by positivity
  set s := dS bh W A θF k η with hs
  set U := dU bh W A θF with hU
  set m := dM bh W A θF with hm
  set w := wX bh W A θF k η (cAv bh W A) with hw
  unfold vHat
  rw [lemmaST_b bh W A hn hg.hb θF k η]
  have hwspec : s - m = nrm (s - m) • w := wdir_spec (s - m)
  have h := lemmaST_c htF s U m w (nrm_nonneg _) hwspec (nrm_sq _)
  refine h.trans ?_
  -- the three terms
  have hDc0 : 0 ≤ Dc bh W A := integral_nonneg fun _ => normSq_nonneg _
  have hTm : √(2 / (mF n : ℝ) * normSq m) ≤ tauM n δ Dbar := by
    unfold tauM
    refine Real.sqrt_le_sqrt ?_
    have h1 := not_lt.mp hg.hTm
    have h2 : (1 + δ) * (1 + δ) * (2 / (n : ℝ) * Dc bh W A) ≤
        (1 + δ) * (1 + δ) * (2 / (n : ℝ) * Dbar) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg.hD (by positivity)) hd2
    exact h1.trans h2
  have hTs : √(2 / (mF n : ℝ) * normSq s) ≤ tauS n k δ Ebar LF Lc := by
    have h1 := (not_le.mp hg.hs).le
    have h2 := not_lt.mp hg.hFE
    have h3 : 2 / (mF n : ℝ) * ((∫ γ, normSq (zS θF (cAv bh W A) (sigP bh W A) γ)
        ∂stdGauss (Fin n)) / k) ≤ (1 + δ) * (1 + δ) * (2 / (n : ℝ) * Ebar) / k := by
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right (h2.trans ?_) hk0.le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg.hE (by positivity)) hd2
    have h4 := Real.sqrt_le_sqrt h3
    unfold tauS
    have e : √(2 / (mF n : ℝ) * normSq s) = Ts θF (cAv bh W A) (sigP bh W A) k η := rfl
    rw [e]
    linarith
  have hTU0 : 0 ≤ TU bh W A.1 A.2.1 θF A.2.2 := Real.sqrt_nonneg _
  have hPhi : PhiU bh W A.1 A.2.1 θF (cAv bh W A) ≤ 2 * (1 + δ) * (1 + δ) := not_lt.mp hg.hJU
  have hTU : TU bh W A.1 A.2.1 θF A.2.2 ≤ tauU n δ LF Mr Lc := by
    unfold tauU
    have h1 : √(Mr * PhiU bh W A.1 A.2.1 θF (cAv bh W A)) ≤
        √(Mr * (2 * (1 + δ) * (1 + δ))) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPhi hMr0)
    linarith [hg.hU.1]
  have hUsq : 2 / (mF n : ℝ) * normSq U ≤ tauU n δ LF Mr Lc ^ 2 := by
    have e : 2 / (mF n : ℝ) * normSq U = TU bh W A.1 A.2.1 θF A.2.2 ^ 2 := by
      unfold TU
      rw [Real.sq_sqrt (mul_nonneg htF (normSq_nonneg _))]
    rw [e]
    exact pow_le_pow_left₀ hTU0 hTU 2
  have huU := uU_nonneg n LF Mr Lc
  have hX : max 0 (-(√(2 / (mF n : ℝ)) * (U ⬝ᵥ w))) ≤ uU n LF Mr Lc := by
    refine max_le huU ?_
    have e : U ⬝ᵥ w = ∑ i, w i * U i := by
      simp only [dotProduct]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    exact hg.hU.2.le
  set a := √(2 / (mF n : ℝ) * normSq s) + √(2 / (mF n : ℝ) * normSq m) with ha
  have ha0 : 0 ≤ a := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have haτ : a ≤ tauS n k δ Ebar LF Lc + tauM n δ Dbar := by rw [ha]; linarith
  have hM0 : 0 ≤ max 0 (-(√(2 / (mF n : ℝ)) * (U ⬝ᵥ w))) := le_max_left _ _
  have h5 : a ^ 2 ≤ (tauS n k δ Ebar LF Lc + tauM n δ Dbar) ^ 2 := pow_le_pow_left₀ ha0 haτ 2
  have h6 : a * max 0 (-(√(2 / (mF n : ℝ)) * (U ⬝ᵥ w))) ≤
      (tauS n k δ Ebar LF Lc + tauM n δ Dbar) * uU n LF Mr Lc :=
    mul_le_mul haτ hX hM0 (ha0.trans haτ)
  unfold vbar
  nlinarith

end defs

end BstLean.Part151
