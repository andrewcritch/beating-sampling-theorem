import BstLean.Part84Defs
import BstLean.Part81Bridge
import BstLean.Part53Polar
import BstLean.Part59LemmaQ_Bridge

/-!
# Part 84, polar reduction: `Pu_degree` and `polarRed`
-/

namespace BstLean.Part84

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM varU)
open BstLean.Part53 (unitF53 radF53 aH c0)
open BstLean.Part59 (polyEval g0Q BP varP shiftedPoly59x affine59x qH)
open BstLean.Part78 (zv)
open BstLean.Part81 (JJ WIdx pf eD)
open BstLean.Part81.Br (combEquiv combEquiv_apply comb_facts combEquiv_preserving)

variable {n d : ℕ}

/-! ## The degree of `Pu` -/

lemma affine_degree (i : Fin n) (t s : ℝ) : (affine59x i t s).totalDegree ≤ 1 := by
  unfold affine59x
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · simp
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

theorem Pu_degree (n d k : ℕ) (c : Mono n k → ℝ) (u : Fin n → ℝ) (ρ : ℝ) :
    (Pu n d k c u ρ).totalDegree ≤ k := by
  classical
  unfold Pu shiftedPoly59x
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro α _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (affine59x i (u i / Real.sqrt (∑ j, u j ^ 2 + ρ ^ 2)) (1 / Real.sqrt (DD n d)) ^
        α.2.val.count i).totalDegree ≤ α.2.val.count i := by
    intro i _
    refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    calc α.2.val.count i * _ ≤ α.2.val.count i * 1 :=
          Nat.mul_le_mul_left _ (affine_degree _ _ _)
      _ = _ := mul_one _
  refine (Finset.sum_le_sum h1).trans ?_
  have h2 : ∑ i : Fin n, α.2.val.count i = Multiset.card α.2.val :=
    Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
  rw [h2, α.2.2]
  exact Nat.lt_succ_iff.mp α.1.2

/-! ## Linearity of the split -/

lemma comb_smul (a : ℝ) (u : Fin n → ℝ) (W : WIdx n d → ℝ) :
    combEquiv n d (a • u, a • W) = a • combEquiv n d (u, W) := by
  funext α
  rw [Pi.smul_apply, combEquiv_apply, combEquiv_apply]
  cases (BstLean.Part81.Br.splitEquiv n d).symm α <;> simp

/-- The matrix `M(u, ρ, ω) = comb (u/r, (ρ/r) ω)`, `r = √(|u|² + ρ²)`. -/
noncomputable def Mof (n d : ℕ) (u : Fin n → ℝ) (ρ : ℝ) (ω : WIdx n d → ℝ) : CoefIdxD n d → ℝ :=
  combEquiv n d ((Real.sqrt (∑ j, u j ^ 2 + ρ ^ 2))⁻¹ • u,
    (ρ / Real.sqrt (∑ j, u j ^ 2 + ρ ^ 2)) • ω)

lemma measurable_Mof {α : Type*} [MeasurableSpace α] (u : Fin n → ℝ) {a : α → WIdx n d → ℝ}
    {b : α → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => Mof n d u (b x) (a x)) := by
  unfold Mof
  apply (combEquiv n d).measurable.comp
  apply Measurable.prodMk
  · fun_prop
  · fun_prop

lemma unitOf_comb (u : Fin n → ℝ) (W : WIdx n d → ℝ) :
    unitOfD (combEquiv n d (u, W)) = Mof n d u (radF53 W) (unitF53 W) := by
  unfold unitOfD Mof
  rw [(comb_facts u W).2.2, ← comb_smul]
  have hr : radF53 W ^ 2 = ∑ β, W β ^ 2 := by
    unfold radF53
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hr, one_div]
  congr 2
  by_cases h0 : radF53 W = 0
  · have hW : W = 0 := by
      have hs : ∑ β, W β ^ 2 = 0 := by rw [← hr, h0]; simp
      funext β
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs β (Finset.mem_univ β)
      simpa using this
    simp [hW, unitF53]
  · unfold unitF53
    rw [smul_smul]
    congr 1
    change _ = radF53 W / _ * (1 / radF53 W)
    field_simp

/-! ## Identification -/

lemma zv_smul (a : ℝ) (W : WIdx n d → ℝ) (p : JJ n d → ℝ) (i : Fin n) :
    zv (a • W) p i = a * zv W p i := by
  unfold zv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp [mul_assoc]

lemma eD_nonneg (d : ℕ) : 0 ≤ eD d := by
  unfold eD c0
  have h : (1 : ℝ) / ((0 : ℕ).factorial : ℝ) ≤
      ∑ j ∈ Finset.range (d + 1), 1 / (j.factorial : ℝ) :=
    Finset.single_le_sum (f := fun j : ℕ => 1 / (j.factorial : ℝ))
      (s := Finset.range (d + 1)) (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.succ_pos d))
  have h0 : (1 : ℝ) / ((0 : ℕ).factorial : ℝ) = 1 := by simp
  linarith

lemma DW_pos (hn : 1 ≤ n) (hd : 1 ≤ d) : 0 < DW n d := by
  unfold DW
  have : Nonempty (WIdx n d) := by
    refine ⟨⟨⟨⟨⟨1, by omega⟩, Sym.replicate 1 ⟨0, hn⟩⟩, ?_⟩, ⟨0, hn⟩⟩⟩
    intro h
    have h' := congrArg (fun q : Mono n d => (q.1 : ℕ)) h
    change (1 : ℕ) = 0 at h'
    omega
  exact_mod_cast Fintype.card_pos

lemma FW_ident (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (c : Mono n k → ℝ) (u : Fin n → ℝ) (ρ : ℝ)
    (ω : WIdx n d → ℝ) (x : Fin n → ℝ) :
    FW (Pu n d k c u ρ) (lam0 n d u ρ) (Real.sqrt (DW n d) • ω) x =
      polyEval k c (mapMD (Mof n d u ρ ω) x) := by
  unfold FW Pu
  rw [BstLean.Part59.shiftedPoly_eval59x]
  congr 1
  funext i
  unfold Mof
  rw [(comb_facts _ _).2.1 x i, zv_smul, zv_smul]
  have hD : Real.sqrt (DD n d) ≠ 0 :=
    (Real.sqrt_pos.mpr (BstLean.Part36.DD_pos hn)).ne'
  have hW : Real.sqrt (DW n d) ≠ 0 := (Real.sqrt_pos.mpr (DW_pos hn hd)).ne'
  unfold lam0
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hr : Real.sqrt (∑ j, u j ^ 2 + ρ ^ 2) = 0
  · simp [hr]
  · field_simp

lemma g0_ident (hn : 1 ≤ n) (k : ℕ) (c : Mono n k → ℝ) (u : Fin n → ℝ) (ρ : ℝ)
    (ω : WIdx n d → ℝ) :
    g0P d (Pu n d k c u ρ) = g0Q n d k c (Mof n d u ρ ω) := by
  unfold g0P Pu g0Q
  simp_rw [BstLean.Part59.shiftedPoly_eval59x]
  have hD : 0 < DD n d := BstLean.Part36.DD_pos hn
  have e1 : ∀ g : Fin n → ℝ, (fun i => u i / Real.sqrt (∑ j, u j ^ 2 + ρ ^ 2) +
      1 / Real.sqrt (DD n d) * (Real.sqrt (eD d) * g i)) =
      (fun i => u i / Real.sqrt (∑ j, u j ^ 2 + ρ ^ 2) +
        (Real.sqrt (eD d) / Real.sqrt (DD n d)) * g i) := by
    intro g; funext i; ring
  simp_rw [e1]
  rw [BstLean.Part59.polyEval_shift_integral59x]
  have e2 : (Real.sqrt (eD d) / Real.sqrt (DD n d)) ^ 2 = aH n d := by
    rw [div_pow, Real.sq_sqrt (eD_nonneg d), Real.sq_sqrt hD.le]
    rfl
  rw [e2]
  unfold Mof
  rw [(comb_facts _ _).1]
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp [div_eq_inv_mul]

/-- The failure set on matrices. -/
def Fail' (n d k : ℕ) (ε : ℝ) (c : Mono n k → ℝ) : Set (CoefIdxD n d → ℝ) :=
  {M | ε ^ 2 * varP (uniformSphere n) k c M <
    (BP (uniformSphere n) k c M - g0Q n d k c M) ^ 2}

lemma badSet_eq (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (ε : ℝ) (c : Mono n k → ℝ) (u : Fin n → ℝ)
    (ρ : ℝ) :
    badSet n d k ε c u ρ = {W | Mof n d u ρ (unitF53 W) ∈ Fail' n d k ε c} := by
  ext W
  unfold badSet Fail'
  simp only [Set.mem_ofPred_eq]
  have hF : FW (Pu n d k c u ρ) (lam0 n d u ρ) (Real.sqrt (DW n d) • unitF53 W) =
      fun x => polyEval k c (mapMD (Mof n d u ρ (unitF53 W)) x) := by
    funext x; exact FW_ident hn hd k c u ρ _ x
  unfold errW VW BW varP BP
  rw [hF, g0_ident hn k c u ρ (unitF53 W)]

/-! ## Measurability -/

lemma cont_qH (e : ℕ) (a : ℝ) : Continuous (fun t : ℝ => qH e t a) := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    match e with
    | 0 => simp only [qH]; exact continuous_const
    | 1 => simp only [qH]; exact continuous_id
    | e + 2 =>
      simp only [qH]
      have h1 := ih (e + 1) (by omega)
      have h2 := ih e (by omega)
      fun_prop

lemma cont_g0Q (k : ℕ) (c : Mono n k → ℝ) : Continuous (fun M : CoefIdxD n d → ℝ => g0Q n d k c M) := by
  unfold g0Q colM
  refine continuous_finsetSum _ fun α _ => continuous_const.mul ?_
  refine continuous_finsetProd _ fun i _ => ?_
  exact (cont_qH _ _).comp (continuous_apply _)

lemma cont_joint (k : ℕ) (c : Mono n k → ℝ) :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => polyEval k c (mapMD p.1 p.2)) := by
  classical
  unfold polyEval phiM
  simp_rw [BstLean.Part59.mono_powers59x, BstLean.Part49.mapMD_eq]
  unfold phiM
  simp_rw [BstLean.Part59.mono_powers59x]
  fun_prop

lemma meas_BP (hn : 1 ≤ n) (k : ℕ) (c : Mono n k → ℝ) :
    Measurable (fun M : CoefIdxD n d → ℝ => BP (uniformSphere n) k c M) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold BP
  exact ((cont_joint k c).stronglyMeasurable.integral_prod_right').measurable

lemma meas_varP (hn : 1 ≤ n) (k : ℕ) (c : Mono n k → ℝ) :
    Measurable (fun M : CoefIdxD n d → ℝ => varP (uniformSphere n) k c M) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold varP varU
  have hm : Measurable (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      (polyEval k c (mapMD p.1 p.2) - ∫ y, polyEval k c (mapMD p.1 y) ∂uniformSphere n) ^ 2) := by
    have h1 := (cont_joint (d := d) k c).measurable
    have h2 : Measurable (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
        ∫ y, polyEval k c (mapMD p.1 y) ∂uniformSphere n) :=
      (meas_BP (d := d) hn k c).comp measurable_fst
    exact (h1.sub h2).pow_const 2
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

lemma meas_Fail (hn : 1 ≤ n) (k : ℕ) (ε : ℝ) (c : Mono n k → ℝ) :
    MeasurableSet (Fail' n d k ε c) := by
  unfold Fail'
  exact measurableSet_lt ((meas_varP hn k c).const_mul _)
    (((meas_BP hn k c).sub (cont_g0Q k c).measurable).pow_const 2)

lemma meas_unitOfD : Measurable (unitOfD (n := n) (d := d)) := by
  unfold unitOfD
  fun_prop

lemma meas_SphereFail (hn : 1 ≤ n) (k : ℕ) (ε : ℝ) (c : Mono n k → ℝ) :
    MeasurableSet (SphereFail n d k ε c) := by
  have h : SphereFail n d k ε c = {Z | Z ≠ 0} ∩ unitOfD ⁻¹' Fail' n d k ε c := rfl
  rw [h]
  exact (measurableSet_singleton (0 : CoefIdxD n d → ℝ)).compl.inter
    (meas_unitOfD (meas_Fail hn k ε c))

/-! ## The polar reduction -/

/-- The indicator of failure as a function of the direction and the radius. -/
noncomputable def Gf (n d k : ℕ) (ε : ℝ) (c : Mono n k → ℝ) (u : Fin n → ℝ) :
    (WIdx n d → ℝ) → ℝ → ℝ≥0∞ :=
  fun ω ρ => (Fail' n d k ε c).indicator (fun _ => (1 : ℝ≥0∞)) (Mof n d u ρ ω)

lemma meas_Gf {α : Type*} [MeasurableSpace α] (hn : 1 ≤ n) (k : ℕ) (ε : ℝ) (c : Mono n k → ℝ)
    (u : Fin n → ℝ) {a : α → WIdx n d → ℝ} {b : α → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => Gf n d k ε c u (a x) (b x)) := by
  have h1 : Measurable (fun x => Mof n d u (b x) (a x)) :=
    measurable_Mof u ha hb
  have h2 : Measurable ((Fail' n d k ε c).indicator (fun _ : CoefIdxD n d → ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (meas_Fail hn k ε c)
  exact h2.comp h1

lemma lint_Gf {α : Type*} [MeasurableSpace α] (μ : Measure α) (hn : 1 ≤ n) (k : ℕ) (ε : ℝ)
    (c : Mono n k → ℝ) (u : Fin n → ℝ) {a : α → WIdx n d → ℝ} {b : α → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ x, Gf n d k ε c u (a x) (b x) ∂μ = μ {x | Mof n d u (b x) (a x) ∈ Fail' n d k ε c} := by
  have hs : MeasurableSet {x | Mof n d u (b x) (a x) ∈ Fail' n d k ε c} :=
    (measurable_Mof u ha hb) (meas_Fail hn k ε c)
  rw [← lintegral_indicator_one hs]
  apply lintegral_congr
  intro x
  unfold Gf
  by_cases h : Mof n d u (b x) (a x) ∈ Fail' n d k ε c
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem (show x ∈ {x | Mof n d u (b x) (a x) ∈ Fail' n d k ε c} from h)]
    rfl
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show x ∉ {x | Mof n d u (b x) (a x) ∈ Fail' n d k ε c} from h)]

theorem polarRed (n d k : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) : PolarRed n d k := by
  intro ε c
  have hSF := meas_SphereFail (d := d) hn k ε c
  rw [← (combEquiv_preserving (n := n) (d := d)).measure_preimage hSF.nullMeasurableSet,
    Measure.prod_apply ((combEquiv n d).measurable hSF)]
  apply lintegral_mono
  intro u
  have hGm : Measurable (Function.uncurry (Gf n d k ε c u)) :=
    meas_Gf hn k ε c u measurable_fst measurable_snd
  have hsw : Measurable (fun p : (WIdx n d → ℝ) × (WIdx n d → ℝ) =>
      Gf n d k ε c u (unitF53 p.1) (radF53 p.2)) :=
    meas_Gf hn k ε c u (BstLean.Part53.measurable_unitF.comp measurable_fst)
      (BstLean.Part53.measurable_radF.comp measurable_snd)
  calc stdGauss (WIdx n d) (Prod.mk u ⁻¹' (combEquiv n d ⁻¹' SphereFail n d k ε c))
      ≤ stdGauss (WIdx n d)
          {W | Mof n d u (radF53 W) (unitF53 W) ∈ Fail' n d k ε c} := by
        apply measure_mono
        intro W hW
        have h2 : unitOfD (combEquiv n d (u, W)) ∈ Fail' n d k ε c := hW.2
        rw [unitOf_comb] at h2
        exact h2
    _ = ∫⁻ W : WIdx n d → ℝ, Gf n d k ε c u (unitF53 W) (radF53 W) ∂stdGauss (WIdx n d) :=
        (lint_Gf _ hn k ε c u BstLean.Part53.measurable_unitF
          BstLean.Part53.measurable_radF).symm
    _ = ∫⁻ W : WIdx n d → ℝ, ∫⁻ W' : WIdx n d → ℝ, Gf n d k ε c u (unitF53 W) (radF53 W')
          ∂stdGauss (WIdx n d) ∂stdGauss (WIdx n d) :=
        BstLean.Part53.gauss_polar_gen (Gf n d k ε c u) hGm
    _ = ∫⁻ W' : WIdx n d → ℝ, ∫⁻ W : WIdx n d → ℝ, Gf n d k ε c u (unitF53 W) (radF53 W')
          ∂stdGauss (WIdx n d) ∂stdGauss (WIdx n d) :=
        lintegral_lintegral_swap hsw.aemeasurable
    _ = ∫⁻ W' : WIdx n d → ℝ, stdGauss (WIdx n d) (badSet n d k ε c u (radF53 W'))
          ∂stdGauss (WIdx n d) := by
        apply lintegral_congr
        intro W'
        rw [badSet_eq hn hd]
        exact lint_Gf _ hn k ε c u BstLean.Part53.measurable_unitF measurable_const

end BstLean.Part84
