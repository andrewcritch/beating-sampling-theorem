import BstLean.Part59Defs
import BstLean.Part59Radial_Bounds

/-!
# Part 59, wave 1: The radial tail of Prop T2* — proved

Specification: `delegations/answers/p59-spec-opus.md` §3.10. Source: `omDL2-opus-prover.md` §3.3,
Prop T2*, "Second event".

Proof route.
* `Z = ‖Z‖W`, `σZ = λW`, `λ = lam59 n d Z` (`= Part53.T2Aux.radialScale`), `W = unitOfD Z`.
* Binomial expansion: `f(λy) − f(y) = Σ_{r=1}^k (λ−1)^r h_r(y)`, `h_r = fvA k (binA r (TF k f0 T))`
  (`λ^j − 1 = Σ_{r ≥ 1} C(j,r)(λ−1)^r`).
* `radDef59² = Var_x[Σ_r (λ−1)^r h_r(Wφ)] ≤ k Σ_r (λ−1)^{2r} G_r(W)`, `G_r(W) = Var_x h_r(Wφ(x))`
  (Part 53's `T2Aux.sd_sum_le`, `sd_mul`).
* `E_Z[(λ−1)^{2r} G_r(W)] = E(λ−1)^{2r}·E_W G_r(W)` (polar independence `hP`; Part 53's
  `T2Aux.polar_product`).
* `μ ↦ G_r(μW)` is a nonnegative polynomial of degree `≤ 2k` (`Part45DegDrop.var_poly45`-style), so
  Lemma R+ (`hRp`, `𝒟 ≥ 1000`) gives `E_W G_r(W) ≤ 2.5(k+1)² E_Z G_r(σZ)`; Lemma V (`hV`) and
  Lemma H (`hH`) give `E_Z G_r(σZ) ≤ C_V (5k²)^{2r} n^r N°(f)` (note `NcA n d k (TF k f0 T) = Ncirc`
  by `rfl`).
* `E(λ−1)^{2r} ≤ E(λ²−1)^{2r} ≤ C_r 𝒟^{−r}` (`Part59Radial_Moments`, by iterating Part 48's
  dimension-free fourth-moment bound on the normalized centered squared radius);
  `n^r/𝒟^r = N^{−r} ≤ 1/n` for `d ≥ 1`.
* Markov at level `sN°` (as in Part 53's `T2Aux.radialDefect_tail`). Take `n₀ ≥ max(nV, 40)`
  (`n ≥ 40` gives `𝒟 ≥ 1000`).

The theorem statement and frozen definitions are unchanged. The four `Part59Radial_*` helpers
import finished files of Parts 29–58 and `Part59Defs`; they import no other Part 59 wave-1 file.
The interface statements `hV`, `hH`, `hRp`, and `hP` remain hypotheses.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

/-- **Radial tail.** -/
theorem radialTail59_of (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K CV : ℝ) (nV : ℕ)
    (hV : LemmaV59 d k K CV nV) (hH : LemmaH59 d k) (hRp : LemmaRp59 k) (hP : GaussPolar53) :
    ∃ (C : ℝ) (n0 : ℕ), 0 ≤ C ∧ RadialTail59 d k K C n0 := by
  classical
  let CR := fun r => Classical.choose (radial_displacement_even_moment59x r)
  have hCR (r) : 0 ≤ CR r :=
    (Classical.choose_spec (radial_displacement_even_moment59x r)).1
  have hbR (r n d : ℕ) (hn : 1 ≤ n) :=
    (Classical.choose_spec (radial_displacement_even_moment59x r)).2 n d hn
  let R : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2
  let L := fun r => (5 * (k : ℝ) ^ 2) ^ (2 * r)
  let C : ℝ := (k : ℝ) * R * |CV| * ∑ r ∈ Finset.Icc 1 k, CR r * L r
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL (r) : 0 ≤ L r := by dsimp [L]; positivity
  have hC : 0 ≤ C := by
    apply mul_nonneg (by dsimp [R]; positivity)
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hCR r) (hL r)
  refine ⟨C, max nV 40, hC, ?_⟩
  intro n hn μ hμ f0 T hT hTk s hs
  have hnV : nV ≤ n := (le_max_left _ _).trans hn
  have hn40 : 40 ≤ n := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD := BstLean.Part36.DD_pos (d := d) hn1
  have hμS := upLaw_sphere59x hμ
  let := hμS.prob
  let A := BstLean.Part53.TF k f0 T
  have hA (j) : IsSymmT (A j) := BstLean.Part53.TF_symm k f0 T hT j
  let N := Ncirc n d k f0 T
  have hN : 0 < N := BstLean.Part53.Ncirc_pos hn1 k hk f0 T hTk
  have hNA : NcA n d k A = N := rfl
  let G := fun r (W : CoefIdxD n d → ℝ) => varU μ (fun x => fvA k (binA r A) (mapMD W x))
  have hGm (r) : Measurable (G r) := variance_fvA_measurable59x μ k (binA r A)
  have hG0 (r) (W) : 0 ≤ G r W := integral_nonneg fun _ => sq_nonneg _
  let F := fun r (Z : CoefIdxD n d → ℝ) => (lam59 n d Z - 1) ^ (2 * r) * G r (unitOfD Z)
  have hp0 (r) (Z : CoefIdxD n d → ℝ) : 0 ≤ (lam59 n d Z - 1) ^ (2 * r) := by
    rw [pow_mul]; positivity
  have hF0 (r) (Z) : 0 ≤ F r Z := mul_nonneg (hp0 r Z) (hG0 r _)
  have hFm (r) : Measurable (fun Z => ENNReal.ofReal (F r Z)) :=
    (((((BstLean.Part53.T2Aux.radialScale_continuous n d).measurable.sub measurable_const).pow_const _).mul
      ((hGm r).comp BstLean.Part53.T2Aux.measurable_unit))).ennreal_ofReal
  let Q := fun r => R * |CV| * CR r * L r / n * N
  have hQ (r) : 0 ≤ Q r := by
    have hc := hCR r
    have hl := hL r
    dsimp [Q]
    positivity
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 k) :
      (∫⁻ Z, ENNReal.ofReal (F r Z) ∂stdGauss (CoefIdxD n d)) ≤ ENNReal.ofReal (Q r) := by
    obtain ⟨hr1, hrk⟩ := Finset.mem_Icc.mp hr
    have hAr (j) : IsSymmT (binA r A j) := by
      intro σ w
      change (j.choose r : ℝ) * A j (w ∘ σ) = (j.choose r : ℝ) * A j w
      rw [hA j σ w]
    obtain ⟨hiG, hbG⟩ := hV n hnV μ hμ (binA r A) hAr
    have hNr : 0 ≤ NcA n d k (binA r A) := by
      unfold NcA frob
      exact Finset.sum_nonneg fun j _ => div_nonneg
        (Finset.sum_nonneg fun w _ => sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
    have hHb := hH n hn1 A hA r hr1 hrk
    rw [hNA] at hHb
    have hgauss : (∫ Z, G r (sg n d • Z) ∂stdGauss (CoefIdxD n d)) ≤
        |CV| * (L r * (n : ℝ) ^ r * N) :=
      hbG.trans ((mul_le_mul_of_nonneg_right (le_abs_self CV) hNr).trans
        (mul_le_mul_of_nonneg_left hHb (abs_nonneg CV)))
    have hang := angular_variance59x k hRp hP μ hμS hn1 (radial_card59x hd hn40) (binA r A) hiG
    have hang' : (∫⁻ Z, ENNReal.ofReal (G r (unitOfD Z)) ∂stdGauss (CoefIdxD n d)) ≤
        ENNReal.ofReal (R * (|CV| * (L r * (n : ℝ) ^ r * N))) :=
      hang.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hgauss hR))
    obtain ⟨hiR, hrad⟩ := hbR r n d hn1
    change (∫⁻ Z, ENNReal.ofReal ((lam59 n d Z - 1) ^ (2 * r) * G r (unitOfD Z))
      ∂stdGauss (CoefIdxD n d)) ≤ _
    rw [radial_product59x hP r (G r) (hGm r) (hG0 r) hiR]
    calc
      _ ≤ ENNReal.ofReal (CR r / DD n d ^ r) *
          ENNReal.ofReal (R * (|CV| * (L r * (n : ℝ) ^ r * N))) := by
        exact mul_le_mul (ENNReal.ofReal_le_ofReal hrad) hang' (by positivity) (by positivity)
      _ = ENNReal.ofReal ((CR r / DD n d ^ r) * (R * (|CV| * (L r * (n : ℝ) ^ r * N)))) :=
        (ENNReal.ofReal_mul (div_nonneg (hCR r) (pow_nonneg hD.le _))).symm
      _ ≤ ENNReal.ofReal (Q r) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ = (R * |CV| * CR r * L r * N) * ((n : ℝ) ^ r / DD n d ^ r) := by ring
          _ ≤ (R * |CV| * CR r * L r * N) * (1 / n) :=
            mul_le_mul_of_nonneg_left (radial_dimension_ratio59x hd hn1 r hr1)
              (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hR (abs_nonneg CV)) (hCR r)) (hL r)) hN.le)
          _ = Q r := by dsimp [Q]; ring
  let E := fun Z : CoefIdxD n d → ℝ => (k : ℝ) * ∑ r ∈ Finset.Icc 1 k, F r Z
  have hEm : Measurable (fun Z => ENNReal.ofReal (E Z)) := by
    have hf (r) : Measurable (F r) :=
      ((((BstLean.Part53.T2Aux.radialScale_continuous n d).measurable.sub measurable_const).pow_const _).mul
        ((hGm r).comp BstLean.Part53.T2Aux.measurable_unit))
    exact (measurable_const.mul (Finset.measurable_sum _ (fun r _ => hf r))).ennreal_ofReal
  have hbound : (∫⁻ Z, ENNReal.ofReal (E Z) ∂stdGauss (CoefIdxD n d)) ≤
      ENNReal.ofReal (C / n * N) := by
    calc
      _ = ENNReal.ofReal (k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
          ∫⁻ Z, ENNReal.ofReal (F r Z) ∂stdGauss (CoefIdxD n d) := by
        simp_rw [E, ENNReal.ofReal_mul (Nat.cast_nonneg k),
          ENNReal.ofReal_sum_of_nonneg (fun r _ => hF0 r _)]
        rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun r _ => hFm r)),
          lintegral_finsetSum _ (fun r _ => hFm r)]
      _ ≤ ENNReal.ofReal (k : ℝ) * ∑ r ∈ Finset.Icc 1 k, ENNReal.ofReal (Q r) := by
        gcongr
        exact hterm _ ‹_›
      _ = ENNReal.ofReal ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k, Q r) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => hQ r),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
      _ = _ := by
        congr 1
        dsimp [Q, C]
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
  have hsN : 0 < s * N := mul_pos hs hN
  have hsub : {Z : CoefIdxD n d → ℝ | Real.sqrt (s * N) ≤
      radDef59 μ k f0 T (unitOfD Z) (lam59 n d Z)} ⊆
      {Z | ENNReal.ofReal (s * N) ≤ ENNReal.ofReal (E Z)} := by
    intro Z hZ
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hZ)).mpr hZ
    rw [Real.sq_sqrt hsN.le] at hsq
    exact ENNReal.ofReal_le_ofReal (hsq.trans
      (radial_square_le59x μ hμS k f0 T (unitOfD Z) (lam59 n d Z)))
  apply le_trans (measure_mono hsub)
    ((meas_ge_le_lintegral_div hEm.aemeasurable (by simpa using hsN) ENNReal.ofReal_ne_top).trans ?_)
  apply le_trans (ENNReal.div_le_div_right hbound _)
  rw [← ENNReal.ofReal_div_of_pos hsN]
  apply ENNReal.ofReal_le_ofReal
  exact le_of_eq (by field_simp [hN.ne', hs.ne', hnR.ne'])

end BstLean.Part59
