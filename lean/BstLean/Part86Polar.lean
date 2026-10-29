import BstLean.Part86Defs
import BstLean.Part53Polar
import BstLean.Part56Orth_Projection

/-!
# Part 86, the polar reduction (`PolarRed86`)

`polarRed86`: the failure probability on the coefficient sphere is at most the average, over the
anchor coordinates `U` and an independent radius `ρ`, of the failure probability over the direction
of the residual coordinates `W`.

Route. `Φ(Z) = (Uof v Z, Wof E Z)` is measure preserving (`RotFacts`). `PsiZ` is a right inverse
of `Φ`. The failure set `A'` on the sphere is measurable. With
`D' = {(U, ρ, W) | PsiZ U (ρ • W/‖W‖) ∈ A'}` (measurable), the identification `Ident86` gives
`W ∈ badSet(U, ρ) ↔ (U, ρ, W) ∈ D'` for `ρ > 0`, `W ≠ 0`. Polar independence in the `W`-space
(`gauss_polar_gen`) then separates the radius of `W` from its direction.
-/

namespace BstLean.Part86.XPolar

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono colM Tens TSymm fval contr)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part56 (UnitV lawRK surrRK phiB kJ ancRK gLineW)

/-! ## Radius and direction -/

section polar

variable {ι : Type} [Fintype ι]

lemma radF53_smul86 (c : ℝ) (hc : 0 ≤ c) (Z : ι → ℝ) : radF53 (c • Z) = c * radF53 Z := by
  unfold radF53
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma radF53_pos86 {Z : ι → ℝ} (hZ : Z ≠ 0) : 0 < radF53 Z := by
  unfold radF53
  apply Real.sqrt_pos.mpr
  obtain ⟨i, hi⟩ : ∃ i, Z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hZ (funext h)
  exact lt_of_lt_of_le (by positivity)
    (Finset.single_le_sum (fun j _ => sq_nonneg (Z j)) (Finset.mem_univ i))

lemma radF53_zero86 : radF53 (0 : ι → ℝ) = 0 := by
  unfold radF53
  simp

lemma unitF53_eq86 (Z : ι → ℝ) : unitF53 Z = (1 / radF53 Z) • Z := rfl

lemma unitF53_smul86 (c : ℝ) (hc : 0 < c) (Z : ι → ℝ) : unitF53 (c • Z) = unitF53 Z := by
  rw [unitF53_eq86, unitF53_eq86, radF53_smul86 c hc.le]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h0 : radF53 Z = 0
  · simp [h0]
  · field_simp

lemma radF53_unit86 {Z : ι → ℝ} (hZ : Z ≠ 0) : radF53 (unitF53 Z) = 1 := by
  have hr := radF53_pos86 hZ
  rw [unitF53_eq86, radF53_smul86 _ (by positivity)]
  field_simp

lemma unitF53_idem86 (Z : ι → ℝ) : unitF53 (unitF53 Z) = unitF53 Z := by
  by_cases hZ : Z = 0
  · subst hZ
    have : unitF53 (0 : ι → ℝ) = 0 := by rw [unitF53_eq86]; simp
    rw [this, this]
  · have hr := radF53_pos86 hZ
    conv_lhs => rw [unitF53_eq86 Z]
    exact unitF53_smul86 _ (by positivity) Z

lemma unitF53_ne86 {Z : ι → ℝ} (hZ : Z ≠ 0) : unitF53 Z ≠ 0 := by
  intro h
  have h1 := radF53_unit86 hZ
  rw [h, radF53_zero86] at h1
  exact zero_ne_one h1

lemma smul_unit_ne86 {Z : ι → ℝ} (hZ : Z ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) : ρ • unitF53 Z ≠ 0 := by
  intro h
  have h1 : radF53 (ρ • unitF53 Z) = ρ := by
    rw [radF53_smul86 ρ hρ.le, radF53_unit86 hZ, mul_one]
  rw [h, radF53_zero86] at h1
  exact hρ.ne h1

lemma gauss_zero_null86 [Nonempty ι] : stdGauss ι {0} = 0 := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  apply measure_mono_null (t := (fun Z : ι → ℝ => Z i0) ⁻¹' {0})
  · intro Z hZ
    simp only [Set.mem_singleton_iff] at hZ
    simp [hZ]
  · unfold stdGauss
    rw [(measurePreserving_eval (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) i0).measure_preimage
      (measurableSet_singleton _).nullMeasurableSet]
    have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_singleton 0

end polar

/-! ## The right inverse of `Z ↦ (U, W)` -/

section psi

variable {n d : ℕ}

/-- The matrix with anchor coordinates `U` and residual coordinates `W`. -/
noncomputable def PsiZ (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ)
    (U : Fin (d + 1) × Fin n → ℝ) (W : JR n d × Fin n → ℝ) : CoefIdxD n d → ℝ :=
  fun α => ∑ j : Fin (d + 1), phiB d j v ⟨α.1, α.2.1⟩ / Real.sqrt (kJ d j v v) * U (j, α.2.2) +
    ∑ q, E q ⟨α.1, α.2.1⟩ * W (q, α.2.2)

lemma colM_PsiZ (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ)
    (U : Fin (d + 1) × Fin n → ℝ) (W : JR n d × Fin n → ℝ) (p : Mono n d) (i : Fin n) :
    colM (PsiZ v E U W) p i =
      ∑ j : Fin (d + 1), phiB d j v p / Real.sqrt (kJ d j v v) * U (j, i) +
        ∑ q, E q p * W (q, i) := rfl

lemma measurable_PsiZ (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) :
    Measurable (fun x : (Fin (d + 1) × Fin n → ℝ) × (JR n d × Fin n → ℝ) =>
      PsiZ v E x.1 x.2) := by
  unfold PsiZ
  fun_prop

lemma Uof_PsiZ (v : Fin n → ℝ) (hv : UnitV v) (E : JR n d → Mono n d → ℝ) (hE : RotE v E)
    (U : Fin (d + 1) × Fin n → ℝ) (W : JR n d × Fin n → ℝ) : Uof v (PsiZ v E U W) = U := by
  classical
  funext a
  obtain ⟨j, i⟩ := a
  have hk : 0 < kJ d j v v := BstLean.Part56.Orth.block_norm_pos v hv j (Nat.lt_succ_iff.mp j.2)
  have hs : 0 < Real.sqrt (kJ d j v v) := Real.sqrt_pos.mpr hk
  have hsq : Real.sqrt (kJ d j v v) * Real.sqrt (kJ d j v v) = kJ d j v v :=
    Real.mul_self_sqrt hk.le
  show ancRK (PsiZ v E U W) v j i / Real.sqrt (kJ d j v v) = U (j, i)
  have hanc : ancRK (PsiZ v E U W) v j i =
      ∑ p : Mono n d, (∑ j' : Fin (d + 1), phiB d j' v p / Real.sqrt (kJ d j' v v) * U (j', i) +
        ∑ q, E q p * W (q, i)) * phiB d j v p := rfl
  have h1 : ∑ p : Mono n d, (∑ j' : Fin (d + 1),
        phiB d j' v p / Real.sqrt (kJ d j' v v) * U (j', i) +
        ∑ q, E q p * W (q, i)) * phiB d j v p =
      ∑ j' : Fin (d + 1), U (j', i) / Real.sqrt (kJ d j' v v) *
          (∑ p : Mono n d, phiB d j' v p * phiB d j v p) +
        ∑ q, W (q, i) * ∑ p : Mono n d, E q p * phiB d j v p := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j' _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
  have h2 : ∑ q, W (q, i) * ∑ p : Mono n d, E q p * phiB d j v p = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [hE.2.1 q j (Finset.mem_range.mpr j.2), mul_zero]
  have h3 : ∑ j' : Fin (d + 1), U (j', i) / Real.sqrt (kJ d j' v v) *
      (∑ p : Mono n d, phiB d j' v p * phiB d j v p) =
      U (j, i) / Real.sqrt (kJ d j v v) * kJ d j v v := by
    rw [Finset.sum_eq_single j]
    · rfl
    · intro j' _ hne
      rw [BstLean.Part56.Orth.blocks_orthogonal (j' : ℕ) (j : ℕ) v
        (fun h => hne (Fin.ext h)), mul_zero]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  rw [hanc, h1, h2, h3, add_zero]
  have hgen : ∀ s k' : ℝ, 0 < s → s * s = k' → U (j, i) / s * k' / s = U (j, i) := by
    intro s k' hs0 h
    subst h
    field_simp
  exact hgen _ _ hs hsq

lemma Wof_PsiZ (v : Fin n → ℝ) (E : JR n d → Mono n d → ℝ) (hE : RotE v E)
    (U : Fin (d + 1) × Fin n → ℝ) (W : JR n d × Fin n → ℝ) : Wof E (PsiZ v E U W) = W := by
  classical
  funext a
  obtain ⟨q, i⟩ := a
  show ∑ p : Mono n d, E q p * colM (PsiZ v E U W) p i = W (q, i)
  simp only [colM_PsiZ]
  have h1 : ∑ p : Mono n d, E q p * (∑ j : Fin (d + 1),
        phiB d j v p / Real.sqrt (kJ d j v v) * U (j, i) + ∑ q', E q' p * W (q', i)) =
      ∑ j : Fin (d + 1), U (j, i) / Real.sqrt (kJ d j v v) *
          (∑ p : Mono n d, E q p * phiB d j v p) +
        ∑ q', W (q', i) * ∑ p : Mono n d, E q p * E q' p := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q' _
      apply Finset.sum_congr rfl
      intro p _
      ring
  have h2 : ∑ j : Fin (d + 1), U (j, i) / Real.sqrt (kJ d j v v) *
      (∑ p : Mono n d, E q p * phiB d j v p) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hE.2.1 q j (Finset.mem_range.mpr j.2), mul_zero]
  have h3 : ∑ q', W (q', i) * ∑ p : Mono n d, E q p * E q' p = W (q, i) := by
    rw [Finset.sum_eq_single q]
    · rw [hE.1 q q]; simp
    · intro q' _ hne
      rw [hE.1 q q']; simp [Ne.symm hne]
    · intro h
      exact (h (Finset.mem_univ q)).elim
  rw [h1, h2, h3, zero_add]

lemma Wof_zero (E : JR n d → Mono n d → ℝ) : Wof E (0 : CoefIdxD n d → ℝ) = 0 := by
  funext a
  simp [Wof, colM]

end psi

/-! ## Measurability of the failure set -/

section meas

variable {n d : ℕ}

lemma mapMD_joint86 :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => mapMD p.1 p.2) := by
  classical
  apply continuous_pi
  intro a
  unfold mapMD
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro β _
  apply Continuous.mul
  · unfold BstLean.Part36.coefD
    split_ifs
    · exact (continuous_apply _).comp continuous_fst
    · exact continuous_const
  · exact continuous_multiset_prod β.val (fun i _ => (continuous_apply i).comp continuous_snd)

lemma cont_fval_map86 (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Continuous (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) => fval k f0 T (mapMD p.1 p.2)) := by
  have hm := mapMD_joint86 (n := n) (d := d)
  unfold fval contr
  apply continuous_const.add
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro w _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro t _
  exact (continuous_apply _).comp hm

lemma meas_BofQ86 (μ : Measure (Fin n → ℝ)) [SFinite μ] (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Measurable (fun M : CoefIdxD n d → ℝ => BofQ μ k f0 T M) := by
  unfold BofQ
  exact ((cont_fval_map86 (d := d) k f0 T).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma meas_varFQ86 (μ : Measure (Fin n → ℝ)) [SFinite μ] (k : ℕ) (f0 : ℝ) (T : Tens n) :
    Measurable (fun M : CoefIdxD n d → ℝ => varFQ μ k f0 T M) := by
  have hB := meas_BofQ86 (d := d) μ k f0 T
  have hj : Measurable (fun p : (CoefIdxD n d → ℝ) × (Fin n → ℝ) =>
      (fval k f0 T (mapMD p.1 p.2) - BofQ μ k f0 T p.1) ^ 2) :=
    (((cont_fval_map86 (d := d) k f0 T).measurable).sub (hB.comp measurable_fst)).pow_const 2
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma meas_gLineW86 (μ : Measure (Fin n → ℝ)) (k : ℕ) (f0 : ℝ) (T : Tens n) (v : Fin n → ℝ) :
    Measurable (fun M : CoefIdxD n d → ℝ => gLineW μ k f0 T v M) := by
  classical
  unfold gLineW BstLean.Part56.gW
  apply Finset.measurable_sum
  intro κ _
  split_ifs
  · apply measurable_const.mul
    unfold contr
    apply Finset.measurable_sum
    intro w _
    apply measurable_const.mul
    apply Finset.measurable_prod
    intro r _
    unfold ancRK BstLean.Part53.linZ colM
    fun_prop
  · exact measurable_const

lemma meas_unitOfD86 : Measurable (unitOfD (n := n) (d := d)) := by
  unfold unitOfD
  exact (measurable_const.div (Real.continuous_sqrt.measurable.comp (by fun_prop))).smul
    measurable_id

lemma meas_SphereFail86 (k K : ℕ) (t : ℝ) (v : Fin n → ℝ) [SFinite (lawRK n t v)] (f0 : ℝ)
    (T : Tens n) : MeasurableSet (SphereFail86 n d k K t v f0 T) := by
  have hu := meas_unitOfD86 (n := n) (d := d)
  have hB := (meas_BofQ86 (d := d) (lawRK n t v) k f0 T).comp hu
  have hV := (meas_varFQ86 (d := d) (lawRK n t v) k f0 T).comp hu
  have hG := (meas_gLineW86 (d := d) (surrRK n K t v) k f0 T v).comp hu
  have h1 : MeasurableSet {Z : CoefIdxD n d → ℝ | Z ≠ 0} := (measurableSet_singleton 0).compl
  have h2 : MeasurableSet {Z : CoefIdxD n d → ℝ |
      (1 / 2 : ℝ) ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
        (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
          gLineW (surrRK n K t v) k f0 T v (unitOfD Z)) ^ 2} :=
    measurableSet_lt (hV.const_mul _) ((hB.sub hG).pow_const 2)
  exact h1.inter h2

end meas

/-! ## The failure set over the direction, and the identification -/

section main

variable {m d : ℕ}

/-- The failure set over the direction of `W`, for anchor coordinates `U` and a radius `ρ`. -/
def Bset (k K : ℕ) (t : ℝ) (v : Fin (m + 1) → ℝ) (E : JR (m + 1) d → Mono (m + 1) d → ℝ)
    (f0 : ℝ) (T : Tens (m + 1)) (U : Fin (d + 1) × Fin (m + 1) → ℝ) (ρ : ℝ) :
    Set (JR (m + 1) d × Fin (m + 1) → ℝ) :=
  badSet86 (modRK m d t v E) (gqRK m d K t v E)
    (PU k f0 T U (Real.sqrt (∑ a, U a ^ 2 + ρ ^ 2)) (1 / Real.sqrt (DD (m + 1) d)))
    (lam0 (DD (m + 1) d) (DWr (m + 1) (JR (m + 1) d)) U ρ)

lemma fail_to_Bset (k K : ℕ) (hId : Ident86 m d k K) (t : ℝ) (v : Fin (m + 1) → ℝ) (ht : 0 ≤ t)
    (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E) (f0 : ℝ)
    (T : Tens (m + 1)) (hT : TSymm k T) (Z : CoefIdxD (m + 1) d → ℝ)
    (hZ : Z ∈ SphereFail86 (m + 1) d k K t v f0 T) (hW : Wof E Z ≠ 0) :
    Wof E Z ∈ Bset k K t v E f0 T (Uof v Z) (radF53 (Wof E Z)) := by
  obtain ⟨h1, h2, h3⟩ := hId t v ht hv E hE f0 T hT Z hW
  have hlt := hZ.2
  rw [h1, h2, h3] at hlt
  exact hlt

lemma Bset_iff (k K : ℕ) (hId : Ident86 m d k K) (t : ℝ) (v : Fin (m + 1) → ℝ) (ht : 0 ≤ t)
    (hv : UnitV v) (E : JR (m + 1) d → Mono (m + 1) d → ℝ) (hE : RotE v E) (f0 : ℝ)
    (T : Tens (m + 1)) (hT : TSymm k T) (U : Fin (d + 1) × Fin (m + 1) → ℝ) (ρ : ℝ)
    (hρ : 0 < ρ) (W : JR (m + 1) d × Fin (m + 1) → ℝ) (hW : W ≠ 0) :
    PsiZ v E U (ρ • unitF53 W) ∈ SphereFail86 (m + 1) d k K t v f0 T ↔
      W ∈ Bset k K t v E f0 T U ρ := by
  have hU : Uof v (PsiZ v E U (ρ • unitF53 W)) = U := Uof_PsiZ v hv E hE U _
  have hWo : Wof E (PsiZ v E U (ρ • unitF53 W)) = ρ • unitF53 W := Wof_PsiZ v E hE U _
  have hr : radF53 (ρ • unitF53 W) = ρ := by
    rw [radF53_smul86 ρ hρ.le, radF53_unit86 hW, mul_one]
  have hu : unitF53 (ρ • unitF53 W) = unitF53 W := by
    rw [unitF53_smul86 ρ hρ, unitF53_idem86]
  have hne : ρ • unitF53 W ≠ 0 := smul_unit_ne86 hW hρ
  have hZne : PsiZ v E U (ρ • unitF53 W) ≠ 0 := by
    intro h0
    rw [h0, Wof_zero] at hWo
    exact hne hWo.symm
  have h := hId t v ht hv E hE f0 T hT (PsiZ v E U (ρ • unitF53 W)) (by rw [hWo]; exact hne)
  rw [hU, hWo, hr, hu] at h
  obtain ⟨h1, h2, h3⟩ := h
  constructor
  · intro hz
    have hlt := hz.2
    rw [h1, h2, h3] at hlt
    exact hlt
  · intro hb
    refine ⟨hZne, ?_⟩
    rw [h1, h2, h3]
    exact hb

/-- **Polar reduction.** The hypothesis `hJ` says that the residual index is not empty. -/
theorem polarRed86 (m d k K : ℕ) (hd : 1 ≤ d) (hJ : 0 < Fintype.card (JR (m + 1) d))
    (hRF : RotFacts (m + 1) d) (hId : Ident86 m d k K) : PolarRed86 m d k K := by
  classical
  intro t v ht hv E hE f0 T hT
  have : IsProbabilityMeasure (lawRK (m + 1) t v) :=
    (BstLean.Part50.binghamA_antipodal (by omega) (BstLean.Part56.rk1 t v)).sph.prob
  have : Nonempty (JR (m + 1) d) := Fintype.card_pos_iff.mp hJ
  have : Nonempty (JR (m + 1) d × Fin (m + 1)) := ⟨(Classical.arbitrary _, 0)⟩
  have hmp := (hRF v hv E hE).1
  set μU := stdGauss (Fin (d + 1) × Fin (m + 1)) with hμU
  set μW := stdGauss (JR (m + 1) d × Fin (m + 1)) with hμW
  set A' := SphereFail86 (m + 1) d k K t v f0 T with hA'
  have hAm : MeasurableSet A' := meas_SphereFail86 k K t v f0 T
  have hnull : μW {0} = 0 := gauss_zero_null86
  -- the parametrization
  let par : (Fin (d + 1) × Fin (m + 1) → ℝ) × ℝ × (JR (m + 1) d × Fin (m + 1) → ℝ) →
      CoefIdxD (m + 1) d → ℝ := fun x => PsiZ v E x.1 (x.2.1 • unitF53 x.2.2)
  have hpar : Measurable par := by
    have h1 : Measurable (fun x : (Fin (d + 1) × Fin (m + 1) → ℝ) × ℝ ×
        (JR (m + 1) d × Fin (m + 1) → ℝ) => (x.1, x.2.1 • unitF53 x.2.2)) :=
      measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).smul
          (BstLean.Part53.measurable_unitF.comp (measurable_snd.comp measurable_snd)))
    exact (measurable_PsiZ v E).comp h1
  set D' := par ⁻¹' A' with hD'
  have hDm : MeasurableSet D' := hpar hAm
  -- the set in the product space
  set C' : Set ((Fin (d + 1) × Fin (m + 1) → ℝ) × (JR (m + 1) d × Fin (m + 1) → ℝ)) :=
    {x | (x.1, radF53 x.2, x.2) ∈ D'} with hC'
  have hCm : MeasurableSet C' := by
    have h1 : Measurable (fun x : (Fin (d + 1) × Fin (m + 1) → ℝ) ×
        (JR (m + 1) d × Fin (m + 1) → ℝ) => (x.1, radF53 x.2, x.2)) :=
      measurable_fst.prodMk
        ((BstLean.Part53.measurable_radF.comp measurable_snd).prodMk measurable_snd)
    exact h1 hDm
  set Φ : (CoefIdxD (m + 1) d → ℝ) →
      (Fin (d + 1) × Fin (m + 1) → ℝ) × (JR (m + 1) d × Fin (m + 1) → ℝ) :=
    fun Z => (Uof v Z, Wof E Z) with hΦ
  -- step 1: the failure set is inside two preimages
  have hsub : A' ⊆ Φ ⁻¹' C' ∪ Φ ⁻¹' (Set.univ ×ˢ {0}) := by
    intro Z hZ
    by_cases hW : Wof E Z = 0
    · right
      exact ⟨Set.mem_univ _, hW⟩
    · left
      have hb := fail_to_Bset k K hId t v ht hv E hE f0 T hT Z hZ hW
      exact (Bset_iff k K hId t v ht hv E hE f0 T hT (Uof v Z) (radF53 (Wof E Z))
        (radF53_pos86 hW) (Wof E Z) hW).mpr hb
  have hstep1 : stdGauss (CoefIdxD (m + 1) d) A' ≤ (μU.prod μW) C' := by
    calc stdGauss (CoefIdxD (m + 1) d) A'
        ≤ stdGauss (CoefIdxD (m + 1) d) (Φ ⁻¹' C' ∪ Φ ⁻¹' (Set.univ ×ˢ {0})) := measure_mono hsub
      _ ≤ stdGauss (CoefIdxD (m + 1) d) (Φ ⁻¹' C') +
          stdGauss (CoefIdxD (m + 1) d) (Φ ⁻¹' (Set.univ ×ˢ {0})) := measure_union_le _ _
      _ = (μU.prod μW) C' + (μU.prod μW) (Set.univ ×ˢ {0}) := by
          rw [hmp.measure_preimage hCm.nullMeasurableSet,
            hmp.measure_preimage
              (MeasurableSet.univ.prod (measurableSet_singleton _)).nullMeasurableSet]
      _ = (μU.prod μW) C' := by
          rw [Measure.prod_prod, hnull, mul_zero, add_zero]
  -- step 2: slices
  have hstep2 : (μU.prod μW) C' = ∫⁻ U, μW (Prod.mk U ⁻¹' C') ∂μU := Measure.prod_apply hCm
  rw [hstep2] at hstep1
  refine hstep1.trans ?_
  apply lintegral_mono
  intro U
  show μW (Prod.mk U ⁻¹' C') ≤ ∫⁻ W', μW (Bset k K t v E f0 T U (radF53 W')) ∂μW
  -- step 3: polar independence at fixed `U`
  obtain ⟨F, hFdef⟩ : ∃ F : (JR (m + 1) d × Fin (m + 1) → ℝ) → ℝ → ℝ≥0∞,
      ∀ ω ρ, F ω ρ = D'.indicator (fun _ => (1 : ℝ≥0∞)) (U, ρ, ω) := ⟨_, fun _ _ => rfl⟩
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun x : (JR (m + 1) d × Fin (m + 1) → ℝ) × ℝ => (U, x.2, x.1)) :=
      measurable_const.prodMk (measurable_snd.prodMk measurable_fst)
    have h2 : Function.uncurry F = fun x : (JR (m + 1) d × Fin (m + 1) → ℝ) × ℝ =>
        D'.indicator (fun _ => (1 : ℝ≥0∞)) (U, x.2, x.1) := funext fun x => hFdef x.1 x.2
    rw [h2]
    exact (measurable_const.indicator hDm).comp h1
  have hmem : ∀ (ρ : ℝ) (W : JR (m + 1) d × Fin (m + 1) → ℝ),
      ((U, ρ, unitF53 W) ∈ D') ↔ ((U, ρ, W) ∈ D') := by
    intro ρ W
    show PsiZ v E U (ρ • unitF53 (unitF53 W)) ∈ A' ↔ PsiZ v E U (ρ • unitF53 W) ∈ A'
    rw [unitF53_idem86]
  have hS : MeasurableSet (Prod.mk U ⁻¹' C') := measurable_prodMk_left hCm
  have h3a : μW (Prod.mk U ⁻¹' C') = ∫⁻ W, F (unitF53 W) (radF53 W) ∂μW := by
    rw [← lintegral_indicator_one hS]
    apply lintegral_congr
    intro W
    by_cases hW : (U, radF53 W, W) ∈ D'
    · have h1 : W ∈ Prod.mk U ⁻¹' C' := hW
      have h2 : (U, radF53 W, unitF53 W) ∈ D' := (hmem _ _).mpr hW
      rw [hFdef, Set.indicator_of_mem h1, Set.indicator_of_mem h2]; rfl
    · have h1 : W ∉ Prod.mk U ⁻¹' C' := hW
      have h2 : (U, radF53 W, unitF53 W) ∉ D' := fun h => hW ((hmem _ _).mp h)
      rw [hFdef, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  have h3b : ∫⁻ W, F (unitF53 W) (radF53 W) ∂μW =
      ∫⁻ W, ∫⁻ W', F (unitF53 W) (radF53 W') ∂μW ∂μW :=
    BstLean.Part53.gauss_polar_gen F hFm
  have hFm2 : Measurable (Function.uncurry (fun (W W' : JR (m + 1) d × Fin (m + 1) → ℝ) =>
      F (unitF53 W) (radF53 W'))) := by
    have h1 : Measurable (fun x : (JR (m + 1) d × Fin (m + 1) → ℝ) ×
        (JR (m + 1) d × Fin (m + 1) → ℝ) => (unitF53 x.1, radF53 x.2)) :=
      (BstLean.Part53.measurable_unitF.comp measurable_fst).prodMk
        (BstLean.Part53.measurable_radF.comp measurable_snd)
    have h2 : Function.uncurry (fun (W W' : JR (m + 1) d × Fin (m + 1) → ℝ) =>
        F (unitF53 W) (radF53 W')) = fun x => Function.uncurry F (unitF53 x.1, radF53 x.2) := rfl
    rw [h2]
    exact hFm.comp h1
  have h3c : ∫⁻ W, ∫⁻ W', F (unitF53 W) (radF53 W') ∂μW ∂μW =
      ∫⁻ W', ∫⁻ W, F (unitF53 W) (radF53 W') ∂μW ∂μW :=
    lintegral_lintegral_swap hFm2.aemeasurable
  rw [h3a, h3b, h3c]
  -- step 4: for almost every radius, the inner integral is at most the measure of the bad set
  apply lintegral_mono_ae
  have hae : ∀ᵐ W' ∂μW, W' ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with W' hW'
  have hρ : 0 < radF53 W' := radF53_pos86 hW'
  set ρ := radF53 W' with hρdef
  set Sρ : Set (JR (m + 1) d × Fin (m + 1) → ℝ) := {W | (U, ρ, unitF53 W) ∈ D'} with hSρ
  have hSm : MeasurableSet Sρ := by
    have h1 : Measurable (fun W : JR (m + 1) d × Fin (m + 1) → ℝ => (U, ρ, unitF53 W)) :=
      measurable_const.prodMk (measurable_const.prodMk BstLean.Part53.measurable_unitF)
    exact h1 hDm
  have h4a : ∫⁻ W, F (unitF53 W) ρ ∂μW = μW Sρ := by
    rw [← lintegral_indicator_one hSm]
    apply lintegral_congr
    intro W
    by_cases hW : (U, ρ, unitF53 W) ∈ D'
    · have h1 : W ∈ Sρ := hW
      rw [hFdef, Set.indicator_of_mem h1, Set.indicator_of_mem hW]; rfl
    · have h1 : W ∉ Sρ := hW
      rw [hFdef, Set.indicator_of_notMem h1, Set.indicator_of_notMem hW]
  have hsub2 : Sρ ⊆ Bset k K t v E f0 T U ρ ∪ {0} := by
    intro W hW
    by_cases hW0 : W = 0
    · right
      exact hW0
    · left
      have h1 : (U, ρ, W) ∈ D' := (hmem ρ W).mp hW
      exact (Bset_iff k K hId t v ht hv E hE f0 T hT U ρ hρ W hW0).mp h1
  rw [h4a]
  calc μW Sρ ≤ μW (Bset k K t v E f0 T U ρ ∪ {0}) := measure_mono hsub2
    _ ≤ μW (Bset k K t v E f0 T U ρ) + μW {0} := measure_union_le _ _
    _ = μW (Bset k K t v E f0 T U ρ) := by rw [hnull, add_zero]

end main

end BstLean.Part86.XPolar

#print axioms BstLean.Part86.XPolar.polarRed86
