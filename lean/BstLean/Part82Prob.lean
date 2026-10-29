import BstLean.Part82Transfer
import BstLean.Part82Scal
import BstLean.Part78Prob

/-!
# Part 82: the probability bound in the split coordinates `(u, W)`

`uw_fail3`: on the events `‖u‖² ≤ 2n` and `|√𝒟/r − 1| ≤ δ`, the set of `(u, W)` where the sphere
program fails has probability at most the sum of the four conditional tails (floor, error, and the
variance and error tails of the two lower pieces).
-/

namespace BstLean.Part82

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part41 (varU)
open BstLean.Part78 (nsq frobH trH zv nsq_nonneg frobH_nonneg markov_gt)

variable {n : ℕ}

/-! ## Algebra of the pieces -/

lemma frobT_nonneg (T : T3 n) : 0 ≤ frobT T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _

lemma symT_zero : SymT (zeroT : T3 n) := fun _ _ _ => ⟨rfl, rfl⟩

lemma frobT_zero : frobT (zeroT : T3 n) = 0 := by simp [frobT, zeroT]

lemma trT_zero (i : Fin n) : trT (zeroT : T3 n) i = 0 := by simp [trT, zeroT]

lemma alphaV_zero (a : Fin n → ℝ) : alphaV a (zeroT : T3 n) = a := by
  funext i; simp [alphaV, trT_zero]

lemma H3U_symm (T : T3 n) (hT : SymT T) (u : Fin n → ℝ) : (H3U T u).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [H3U, Matrix.of_apply]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [(hT j i k).1]

lemma HU3_symm (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (T : T3 n) (hT : SymT T)
    (u : Fin n → ℝ) : (HU3 H T u).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [HU3, Matrix.of_apply]
  rw [hH.apply i j]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by rw [(hT j i k).1]

lemma cs_sum (f g : Fin n → ℝ) : (∑ j, f j * g j) ^ 2 ≤ (∑ j, f j ^ 2) * ∑ j, g j ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `‖2Hu‖² ≤ 4‖H‖²‖u‖²`. -/
lemma nsq_a2U (H : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    nsq (a2U H u) ≤ 4 * frobH H * nsq u := by
  unfold nsq a2U frobH
  have : ∀ i, (2 * ∑ j, H i j * u j) ^ 2 ≤ 4 * ((∑ j, H i j ^ 2) * ∑ j, u j ^ 2) := by
    intro i
    have := cs_sum (fun j => H i j) u
    nlinarith
  refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

/-- `‖T[u]‖² ≤ ‖T‖²‖u‖²` rowwise. -/
lemma row_T (T : T3 n) (u : Fin n → ℝ) (i : Fin n) :
    ∑ j, (∑ k, T i j k * u k) ^ 2 ≤ (∑ j, ∑ k, T i j k ^ 2) * nsq u := by
  unfold nsq
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => cs_sum (fun k => T i j k) u

/-- `‖3T[u,·,·]‖² ≤ 9‖T‖²‖u‖²`. -/
lemma frobH_H3U (T : T3 n) (u : Fin n → ℝ) : frobH (H3U T u) ≤ 9 * frobT T * nsq u := by
  unfold frobH H3U frobT
  simp only [Matrix.of_apply]
  have : ∀ i, ∑ j, (3 * ∑ k, T i j k * u k) ^ 2 ≤ 9 * ((∑ j, ∑ k, T i j k ^ 2) * nsq u) := by
    intro i
    have h := row_T T u i
    have e : ∑ j, (3 * ∑ k, T i j k * u k) ^ 2 = 9 * ∑ j, (∑ k, T i j k * u k) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]; linarith
  refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

/-- `‖3T[u,u,·]‖² ≤ 9‖T‖²‖u‖⁴`. -/
lemma nsq_a3U (T : T3 n) (u : Fin n → ℝ) : nsq (a3U T u) ≤ 9 * frobT T * nsq u ^ 2 := by
  have hu := nsq_nonneg u
  have : ∀ i, (a3U T u i) ^ 2 ≤ 9 * ((∑ j, ∑ k, T i j k ^ 2) * nsq u ^ 2) := by
    intro i
    have e : a3U T u i = 3 * ∑ j, u j * ∑ k, T i j k * u k := by
      unfold a3U
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h1 := cs_sum u (fun j => ∑ k, T i j k * u k)
    have h2 := row_T T u i
    have h3 : (∑ j, u j ^ 2) = nsq u := rfl
    rw [h3] at h1
    have h4 : nsq u * ∑ j, (∑ k, T i j k * u k) ^ 2 ≤
        nsq u * ((∑ j, ∑ k, T i j k ^ 2) * nsq u) := mul_le_mul_of_nonneg_left h2 hu
    rw [e]
    have e2 : (3 * ∑ j, u j * ∑ k, T i j k * u k) ^ 2 =
        9 * (∑ j, u j * ∑ k, T i j k * u k) ^ 2 := by ring
    rw [e2]
    nlinarith
  have hs : nsq (a3U T u) = ∑ i, (a3U T u i) ^ 2 := rfl
  rw [hs]
  refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
  unfold frobT
  rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

/-- `‖tr T‖² ≤ n‖T‖²`. -/
lemma nsq_trT (T : T3 n) : nsq (trT T) ≤ n * frobT T := by
  unfold nsq trT frobT
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (∑ j, T i j j) ^ 2 ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) * ∑ j, T i j j ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ∑ j, T i j j ^ 2 ≤ ∑ j, ∑ k, T i j k ^ 2 :=
    Finset.sum_le_sum fun j _ =>
      Finset.single_le_sum (f := fun k => T i j k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- `‖3T[u,u] + 5b‖² ≤ 18‖T‖²‖u‖⁴ + 50n‖T‖²`. -/
lemma nsq_alpha3 (T : T3 n) (u : Fin n → ℝ) :
    nsq (alphaV (a3U T u) T) ≤ 18 * frobT T * nsq u ^ 2 + 50 * n * frobT T := by
  have h1 := nsq_a3U T u
  have h2 := nsq_trT T
  have h3 : nsq (alphaV (a3U T u) T) ≤ 2 * nsq (a3U T u) + 50 * nsq (trT T) := by
    unfold nsq alphaV
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (a3U T u i - 5 * trT T i)]
  linarith

/-- `(b·u)² ≤ n‖T‖²‖u‖²`. -/
lemma bu_sq (T : T3 n) (u : Fin n → ℝ) :
    (∑ i, trT T i * u i) ^ 2 ≤ n * frobT T * nsq u := by
  have h1 := cs_sum (trT T) u
  have h2 := nsq_trT T
  have h3 : (∑ j, trT T j ^ 2) = nsq (trT T) := rfl
  have h4 : (∑ j, u j ^ 2) = nsq u := rfl
  rw [h3, h4] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (nsq_nonneg u))

/-- `‖H‖² ≤ 2‖H_u‖² + 18‖T‖²‖u‖²`. -/
lemma frobH_le (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (u : Fin n → ℝ) :
    frobH H ≤ 2 * frobH (HU3 H T u) + 18 * frobT T * nsq u := by
  have h1 := frobH_H3U T u
  have h2 : frobH H ≤ 2 * frobH (HU3 H T u) + 2 * frobH (H3U T u) := by
    unfold frobH HU3 H3U
    simp only [Matrix.of_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    nlinarith [sq_nonneg (H i j + 6 * ∑ k, T i j k * u k)]
  linarith

lemma Wf3_ge (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    555 / 100 * frobH H + 277 / 10 * frobT T ≤ Wf3 a H T := by
  unfold Wf3; nlinarith [nsq_nonneg (alphaV a T)]

lemma VG3_nonneg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (W : WIdx3 n → ℝ) :
    0 ≤ VG3 a H T W := by
  unfold VG3 varU; exact integral_nonneg fun _ => sq_nonneg _

/-! ## Continuity in `u` -/

lemma cont_aU3 (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    Continuous (fun u : Fin n → ℝ => aU3 ℓ H T u) := by
  refine continuous_pi fun i => ?_
  unfold aU3
  fun_prop

lemma cont_HU3 (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) :
    Continuous (fun u : Fin n → ℝ => HU3 H T u) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [HU3, Matrix.of_apply]
  fun_prop

lemma cont_a2U (H : Matrix (Fin n) (Fin n) ℝ) : Continuous (fun u : Fin n → ℝ => a2U H u) := by
  refine continuous_pi fun i => ?_
  unfold a2U
  fun_prop

lemma cont_a3U (T : T3 n) : Continuous (fun u : Fin n → ℝ => a3U T u) := by
  refine continuous_pi fun i => ?_
  unfold a3U
  fun_prop

lemma cont_H3U (T : T3 n) : Continuous (fun u : Fin n → ℝ => H3U T u) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [H3U, Matrix.of_apply]
  fun_prop

lemma cont_Wf3 (T : T3 n) :
    Continuous (fun q : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => Wf3 q.1 q.2 T) := by
  unfold Wf3 nsq frobH alphaV
  fun_prop

/-- `1/r` in the split coordinates. -/
noncomputable def sOf3 (p : (Fin n → ℝ) × (WIdx3 n → ℝ)) : ℝ :=
  1 / Real.sqrt (∑ i, p.1 i ^ 2 + ∑ β, p.2 β ^ 2)

/-- The floor at the point `u`. -/
noncomputable def WfU (ℓ : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (T : T3 n) (u : Fin n → ℝ) :
    ℝ := Wf3 (aU3 ℓ H T u) (HU3 H T u) T

set_option maxHeartbeats 3200000 in
/-- **The failure probability in the split coordinates, on the good radius event and
`‖u‖² ≤ 2n`.** -/
theorem uw_fail3 (hn : 1000000 ≤ n) {CF cK c1 κ ε ε₁ lam η m δ : ℝ}
    (hCF0 : 0 ≤ CF) (hCF : CF ≤ 4)
    (hG : GaussBds n CF) (hM : MeanIds3 n) (hR : RegIface3 n) (hV : VarBoundK3 n cK)
    (hcK : 0 ≤ cK)
    (hc1 : 101 / 100 * CF ≤ c1 * (164 / 100) ∧ 6 * CF + 907 / 100 ≤ c1 * (555 / 100) ∧
      55 * CF ≤ c1 * (277 / 10))
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε₁ : 0 < ε₁) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hη : 0 < η)
    (hm : 0 < m) (hδ : δ ≤ 1 / 100)
    (hnum : (1 + η) * ε₁ ^ 2 + (1 + 1 / η) * 4 * δ ^ 2 *
        (m * 95 * (n : ℝ) + 12 * (13 / 10 * (n : ℝ) ^ 2) + 102 * (73 / 1000 * (n : ℝ) ^ 2)) +
      ε ^ 2 * (2 / lam) * δ ^ 2 * (m * 95 * (n : ℝ) ^ 2) ≤ ε ^ 2 * (1 - lam) * κ)
    (f0 : ℝ) (ℓ₀ ℓ : Fin n → ℝ) (H₀ H : Matrix (Fin n) (Fin n) ℝ) (T₀ T : T3 n)
    (hH : H.IsSymm) (hT : SymT T) (ht : 0 < frobT T) (sD D : ℝ) (hsD : sD ^ 2 = D) (hD : D ≠ 0)
    (hℓ : ∀ i, ℓ₀ i = sD * ℓ i) (hHs : ∀ i j, H₀ i j = D * H i j)
    (hTs : ∀ i j k, T₀ i j k = D * sD * T i j k) :
    ((stdGauss (Fin n)).prod (stdGauss (WIdx3 n))) {p | nsq p.1 ≤ 2 * n ∧ |sD * sOf3 p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * (p.1 i + zv p.2 (pf3 x) i))) <
        ((∫ x, cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * (p.1 i + zv p.2 (pf3 x) i)) ∂uniformSphere n) -
          (cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * p.1 i) +
            5 / 3 / D * (trH H₀ + 3 * ∑ i, trT T₀ i * (sOf3 p * p.1 i)))) ^ 2} ≤
      ENNReal.ofReal (c1 / (n * ε₁ ^ 2) + cK * (185 / 100) / (n * (1 - κ) ^ 2) + 1 / m + 1 / m) := by
  have hn1 : 1 ≤ n := by omega
  have hn' : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  -- abbreviations
  set VGf : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ :=
    fun p => VG3 (aU3 ℓ H T p.1) (HU3 H T p.1) T p.2 with hVGf
  set EGf : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ :=
    fun p => errG3 (aU3 ℓ H T p.1) (HU3 H T p.1) T p.2 with hEGf
  set V2f : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ := fun p => VG3 (a2U H p.1) H zeroT p.2 with hV2f
  set E2f : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ := fun p => errG3 (a2U H p.1) H zeroT p.2 with hE2f
  set V3f : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ :=
    fun p => VG3 (a3U T p.1) (H3U T p.1) T p.2 with hV3f
  set E3f : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ :=
    fun p => errG3 (a3U T p.1) (H3U T p.1) T p.2 with hE3f
  set Wff : (Fin n → ℝ) × (WIdx3 n → ℝ) → ℝ := fun p => WfU ℓ H T p.1 with hWff
  have cmap1 : Continuous (fun p : (Fin n → ℝ) × (WIdx3 n → ℝ) =>
      (((aU3 ℓ H T p.1, HU3 H T p.1), p.2) :
        ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) × (WIdx3 n → ℝ))) :=
    (((cont_aU3 ℓ H T).comp continuous_fst).prodMk ((cont_HU3 H T).comp continuous_fst)).prodMk
      continuous_snd
  have cmap2 : Continuous (fun p : (Fin n → ℝ) × (WIdx3 n → ℝ) =>
      (((a2U H p.1, H), p.2) :
        ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) × (WIdx3 n → ℝ))) :=
    (((cont_a2U H).comp continuous_fst).prodMk continuous_const).prodMk continuous_snd
  have cmap3 : Continuous (fun p : (Fin n → ℝ) × (WIdx3 n → ℝ) =>
      (((a3U T p.1, H3U T p.1), p.2) :
        ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) × (WIdx3 n → ℝ))) :=
    (((cont_a3U T).comp continuous_fst).prodMk ((cont_H3U T).comp continuous_fst)).prodMk
      continuous_snd
  have cVG : Continuous VGf := (hR T).1.comp cmap1
  have cEG : Continuous EGf := (hR T).2.1.comp cmap1
  have cV2 : Continuous V2f := (hR zeroT).1.comp cmap2
  have cE2 : Continuous E2f := (hR zeroT).2.1.comp cmap2
  have cV3 : Continuous V3f := (hR T).1.comp cmap3
  have cE3 : Continuous E3f := (hR T).2.1.comp cmap3
  have cWf : Continuous Wff := by
    have : Continuous (fun p : (Fin n → ℝ) × (WIdx3 n → ℝ) =>
        ((aU3 ℓ H T p.1, HU3 H T p.1) : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ)) :=
      ((cont_aU3 ℓ H T).comp continuous_fst).prodMk ((cont_HU3 H T).comp continuous_fst)
    exact (cont_Wf3 T).comp this
  have cnu : Continuous (fun p : (Fin n → ℝ) × (WIdx3 n → ℝ) => nsq p.1) := by
    unfold nsq; fun_prop
  set BV : ℝ := m * 95 * (n : ℝ) ^ 2 with hBV
  set BE : ℝ := m * 95 * (n : ℝ) with hBE
  -- the bad set
  set E : Set ((Fin n → ℝ) × (WIdx3 n → ℝ)) :=
    {p | nsq p.1 ≤ 2 * n} ∩
    ((({p | VGf p < κ * Wff p} ∪ {p | ε₁ ^ 2 * Wff p < EGf p ^ 2}) ∪
      {p | BV * Wff p < V2f p + 5 * V3f p}) ∪
      {p | BE * Wff p < E2f p ^ 2 + 5 * E3f p ^ 2}) with hE
  have hEm : MeasurableSet E := by
    refine (measurableSet_le cnu.measurable measurable_const).inter ?_
    refine (((measurableSet_lt cVG.measurable (continuous_const.mul cWf).measurable).union
      (measurableSet_lt (continuous_const.mul cWf).measurable (cEG.pow 2).measurable)).union
      (measurableSet_lt (continuous_const.mul cWf).measurable
        (cV2.add (continuous_const.mul cV3)).measurable)).union
      (measurableSet_lt (continuous_const.mul cWf).measurable
        ((cE2.pow 2).add (continuous_const.mul (cE3.pow 2))).measurable)
  -- facts at one `u`
  have hfacts : ∀ u : Fin n → ℝ, nsq u ≤ 2 * n →
      0 < WfU ℓ H T u ∧
      (4 * nsq (alphaV (a2U H u) zeroT) + 19 * frobH H + 163 * frobT (zeroT : T3 n)) +
        5 * (4 * nsq (alphaV (a3U T u) T) + 19 * frobH (H3U T u) + 163 * frobT T) ≤
        95 * (n : ℝ) ^ 2 * WfU ℓ H T u ∧
      (101 / 100 * CF * nsq (alphaV (a2U H u) zeroT) + (6 * CF + 907 / 100) * frobH H +
          55 * CF * frobT (zeroT : T3 n)) / n +
        5 * ((101 / 100 * CF * nsq (alphaV (a3U T u) T) +
          (6 * CF + 907 / 100) * frobH (H3U T u) + 55 * CF * frobT T) / n) ≤
        95 * (n : ℝ) * WfU ℓ H T u ∧
      trH H ^ 2 ≤ 13 / 10 * (n : ℝ) ^ 2 * WfU ℓ H T u ∧
      (∑ i, trT T i * u i) ^ 2 ≤ 73 / 1000 * (n : ℝ) ^ 2 * WfU ℓ H T u := by
    intro u hu
    have hW := Wf3_ge (aU3 ℓ H T u) (HU3 H T u) T
    have hvu := frobH_nonneg (HU3 H T u)
    have hpos : 0 < WfU ℓ H T u := by unfold WfU; linarith
    have hX2 : nsq (alphaV (a2U H u) zeroT) ≤ 4 * frobH H * nsq u := by
      rw [alphaV_zero]; exact nsq_a2U H u
    have hX3 := nsq_alpha3 T u
    have hv3 := frobH_H3U T u
    have hvH := frobH_le H T u
    obtain ⟨s1, s2, s3, s4⟩ := scal_bounds (N := (n : ℝ)) (r := nsq u) (vH := frobH H)
      (vu := frobH (HU3 H T u)) (t := frobT T) (Wfu := WfU ℓ H T u) (CF := CF)
      (X2 := nsq (alphaV (a2U H u) zeroT)) (X3 := nsq (alphaV (a3U T u) T))
      (v3 := frobH (H3U T u)) hn' (nsq_nonneg u) hu hvu ht.le (frobH_nonneg H) hvH
      (by unfold WfU; exact hW) hCF0 hCF (nsq_nonneg _) (nsq_nonneg _) (frobH_nonneg _)
      hX2 (by linarith) hv3
    refine ⟨hpos, ?_, ?_, ?_, ?_⟩
    · rw [frobT_zero]; linarith
    · rw [frobT_zero]; simpa using s2
    · have := BstLean.Part78.trH_sq_le H
      linarith
    · have := bu_sq T u
      linarith
  -- the failure set is inside `E`
  have hsub : {p : (Fin n → ℝ) × (WIdx3 n → ℝ) | nsq p.1 ≤ 2 * n ∧ |sD * sOf3 p - 1| ≤ δ ∧
      ε ^ 2 * varU (uniformSphere n)
          (fun x => cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * (p.1 i + zv p.2 (pf3 x) i))) <
        ((∫ x, cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * (p.1 i + zv p.2 (pf3 x) i)) ∂uniformSphere n) -
          (cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * p.1 i) +
            5 / 3 / D * (trH H₀ + 3 * ∑ i, trT T₀ i * (sOf3 p * p.1 i)))) ^ 2} ⊆ E := by
    intro p hp
    obtain ⟨hu, hτ, hfail⟩ := hp
    refine ⟨hu, ?_⟩
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hnot
    obtain ⟨hpos, -, -, hTr, hBu⟩ := hfacts p.1 hu
    obtain ⟨hVS, heS⟩ := pw_core3 hn1 hR f0 ℓ₀ ℓ H₀ H T₀ T hH hT sD D (sOf3 p) hsD hD hℓ hHs hTs
      p.1 p.2 lam hlam0
    have heS' : (∫ x, cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * (p.1 i + zv p.2 (pf3 x) i))
          ∂uniformSphere n) -
        (cfun f0 ℓ₀ H₀ T₀ (fun i => sOf3 p * p.1 i) +
          5 / 3 / D * (trH H₀ + 3 * ∑ i, trT T₀ i * (sOf3 p * p.1 i))) =
        (sD * sOf3 p) * EGf p + (sD * sOf3 p) * (sD * sOf3 p - 1) * E2f p +
          (sD * sOf3 p) * ((sD * sOf3 p) ^ 2 - 1) * E3f p +
          5 / 3 * trH H * ((sD * sOf3 p) ^ 2 - 1) +
          5 * (∑ i, trT T i * p.1 i) * (sD * sOf3 p) * ((sD * sOf3 p) ^ 2 - 1) := heS
    have := det_core3 (ε := ε) (κ := κ) (ε₁ := ε₁) (η := η) (BV := BV) (BE := BE)
      (BT := 13 / 10 * (n : ℝ) ^ 2) (BB := 73 / 1000 * (n : ℝ) ^ 2)
      hτ hδ hlam0 hlam1 hη (VG3_nonneg _ _ _ _) (VG3_nonneg _ _ _ _) hpos.le hVS heS'
      g1 g2 g3 g4 hTr hBu hnum
    exact absurd hfail (not_lt.mpr this)
  refine (measure_mono hsub).trans ?_
  have : IsProbabilityMeasure (stdGauss (Fin n)) := inferInstance
  rw [Measure.prod_apply hEm]
  set bound : ℝ := c1 / (n * ε₁ ^ 2) + cK * (185 / 100) / (n * (1 - κ) ^ 2) + 1 / m + 1 / m
    with hbound
  have h1κ : 0 < 1 - κ := by linarith
  have hc10 : 0 ≤ c1 := by nlinarith [hc1.1]
  have hb0 : 0 ≤ bound := by rw [hbound]; positivity
  have hcond : ∀ u : Fin n → ℝ, stdGauss (WIdx3 n) (Prod.mk u ⁻¹' E) ≤ ENNReal.ofReal bound := by
    intro u
    by_cases hu : nsq u ≤ 2 * n
    swap
    · have : Prod.mk u ⁻¹' E = ∅ := by
        ext W
        simp only [hE, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd h hu
      rw [this]; simp
    obtain ⟨hpos, hMV, hME, -, -⟩ := hfacts u hu
    set Wu := WfU ℓ H T u with hWu
    have hHu := HU3_symm H hH T hT u
    -- full polynomial
    obtain ⟨gF, gE, -, gK⟩ := hG (aU3 ℓ H T u) (HU3 H T u) hHu T hT
    obtain ⟨i1, i2, i3, -⟩ := hM (aU3 ℓ H T u) (HU3 H T u) hHu T hT
    have gF' : Wu ≤ ∫ W, VG3 (aU3 ℓ H T u) (HU3 H T u) T W ∂stdGauss (WIdx3 n) := gF
    set mu := ∫ W, VG3 (aU3 ℓ H T u) (HU3 H T u) T W ∂stdGauss (WIdx3 n) with hmu
    -- floor (Chebyshev)
    have b1 : stdGauss (WIdx3 n) {W | VG3 (aU3 ℓ H T u) (HU3 H T u) T W < κ * Wu} ≤
        ENNReal.ofReal (cK * (185 / 100) / (n * (1 - κ) ^ 2)) := by
      have hint : Integrable (fun W => (VG3 (aU3 ℓ H T u) (HU3 H T u) T W - mu) ^ 2)
          (stdGauss (WIdx3 n)) := by
        have : (fun W => (VG3 (aU3 ℓ H T u) (HU3 H T u) T W - mu) ^ 2) =
            fun W => VG3 (aU3 ℓ H T u) (HU3 H T u) T W ^ 2 -
              2 * mu * VG3 (aU3 ℓ H T u) (HU3 H T u) T W + mu ^ 2 := by
          funext W; ring
        rw [this]; exact (i2.sub (i1.const_mul _)).add (integrable_const _)
      have hvar := hV (aU3 ℓ H T u) (HU3 H T u) hHu T hT
      have hB : ∫ W, (VG3 (aU3 ℓ H T u) (HU3 H T u) T W - mu) ^ 2 ∂stdGauss (WIdx3 n) ≤
          cK / n * (185 / 100 * Wu ^ 2) := by
        refine hvar.trans ?_
        exact mul_le_mul_of_nonneg_left gK (div_nonneg hcK hnpos.le)
      have htp : 0 < ((1 - κ) * Wu) ^ 2 := by positivity
      have hmk := markov_gt (μ := stdGauss (WIdx3 n))
        (fun W => sq_nonneg (VG3 (aU3 ℓ H T u) (HU3 H T u) T W - mu)) hint htp hB
      have hsub' : {W | VG3 (aU3 ℓ H T u) (HU3 H T u) T W < κ * Wu} ⊆
          {W | ((1 - κ) * Wu) ^ 2 < (VG3 (aU3 ℓ H T u) (HU3 H T u) T W - mu) ^ 2} := by
        intro W hW
        simp only [Set.mem_ofPred_eq] at hW ⊢
        have h3 : (1 - κ) * Wu < mu - VG3 (aU3 ℓ H T u) (HU3 H T u) T W := by nlinarith
        have h4 : 0 < (1 - κ) * Wu := by positivity
        nlinarith
      refine (measure_mono hsub').trans (hmk.trans (le_of_eq ?_))
      congr 1
      field_simp
    -- error (Markov)
    have b2 : stdGauss (WIdx3 n) {W | ε₁ ^ 2 * Wu < errG3 (aU3 ℓ H T u) (HU3 H T u) T W ^ 2} ≤
        ENNReal.ofReal (c1 / (n * ε₁ ^ 2)) := by
      have hB : ∫ W, errG3 (aU3 ℓ H T u) (HU3 H T u) T W ^ 2 ∂stdGauss (WIdx3 n) ≤
          c1 * Wu / n := by
        refine gE.trans ?_
        apply div_le_div_of_nonneg_right _ hnpos.le
        rw [hWu]; unfold WfU Wf3
        obtain ⟨q1, q2, q3⟩ := hc1
        have e1 := mul_le_mul_of_nonneg_right q1 (nsq_nonneg (alphaV (aU3 ℓ H T u) T))
        have e2 := mul_le_mul_of_nonneg_right q2 (frobH_nonneg (HU3 H T u))
        have e3 := mul_le_mul_of_nonneg_right q3 (frobT_nonneg T)
        linarith
      have hmk := markov_gt (μ := stdGauss (WIdx3 n))
        (fun W => sq_nonneg (errG3 (aU3 ℓ H T u) (HU3 H T u) T W)) i3
        (mul_pos (by positivity : (0 : ℝ) < ε₁ ^ 2) hpos) hB
      refine hmk.trans (le_of_eq ?_)
      congr 1
      field_simp
    -- the lower pieces
    have hH3 := H3U_symm T hT u
    obtain ⟨-, gE2, gU2, -⟩ := hG (a2U H u) H hH zeroT symT_zero
    obtain ⟨j1, -, j3, -⟩ := hM (a2U H u) H hH zeroT symT_zero
    obtain ⟨-, gE3, gU3, -⟩ := hG (a3U T u) (H3U T u) hH3 T hT
    obtain ⟨k1, -, k3, -⟩ := hM (a3U T u) (H3U T u) hH3 T hT
    have b3 : stdGauss (WIdx3 n) {W | BV * Wu <
        VG3 (a2U H u) H zeroT W + 5 * VG3 (a3U T u) (H3U T u) T W} ≤ ENNReal.ofReal (1 / m) := by
      have hB : ∫ W, (VG3 (a2U H u) H zeroT W + 5 * VG3 (a3U T u) (H3U T u) T W)
          ∂stdGauss (WIdx3 n) ≤ 95 * (n : ℝ) ^ 2 * Wu := by
        rw [integral_add j1 (k1.const_mul _), integral_const_mul]
        linarith
      have hmk := markov_gt (μ := stdGauss (WIdx3 n))
        (fun W => add_nonneg (VG3_nonneg (a2U H u) H zeroT W)
          (mul_nonneg (by norm_num) (VG3_nonneg (a3U T u) (H3U T u) T W)))
        (j1.add (k1.const_mul _)) (mul_pos (by rw [hBV]; positivity : 0 < BV) hpos) hB
      refine hmk.trans (le_of_eq ?_)
      congr 1
      rw [hBV]
      field_simp
    have b4 : stdGauss (WIdx3 n) {W | BE * Wu <
        errG3 (a2U H u) H zeroT W ^ 2 + 5 * errG3 (a3U T u) (H3U T u) T W ^ 2} ≤
        ENNReal.ofReal (1 / m) := by
      have hB : ∫ W, (errG3 (a2U H u) H zeroT W ^ 2 + 5 * errG3 (a3U T u) (H3U T u) T W ^ 2)
          ∂stdGauss (WIdx3 n) ≤ 95 * (n : ℝ) * Wu := by
        rw [integral_add j3 (k3.const_mul _), integral_const_mul]
        linarith
      have hmk := markov_gt (μ := stdGauss (WIdx3 n))
        (fun W => add_nonneg (sq_nonneg (errG3 (a2U H u) H zeroT W))
          (mul_nonneg (by norm_num) (sq_nonneg (errG3 (a3U T u) (H3U T u) T W))))
        (j3.add (k3.const_mul _)) (mul_pos (by rw [hBE]; positivity : 0 < BE) hpos) hB
      refine hmk.trans (le_of_eq ?_)
      congr 1
      rw [hBE]
      field_simp
    have hpre : Prod.mk u ⁻¹' E ⊆
        (({W | VG3 (aU3 ℓ H T u) (HU3 H T u) T W < κ * Wu} ∪
          {W | ε₁ ^ 2 * Wu < errG3 (aU3 ℓ H T u) (HU3 H T u) T W ^ 2}) ∪
          {W | BV * Wu < VG3 (a2U H u) H zeroT W + 5 * VG3 (a3U T u) (H3U T u) T W}) ∪
          {W | BE * Wu <
            errG3 (a2U H u) H zeroT W ^ 2 + 5 * errG3 (a3U T u) (H3U T u) T W ^ 2} := by
      intro W hW
      exact hW.2
    refine (measure_mono hpre).trans ?_
    have p1 : 0 ≤ c1 / (n * ε₁ ^ 2) := by positivity
    have p2 : 0 ≤ cK * (185 / 100) / (n * (1 - κ) ^ 2) := by positivity
    have p3 : 0 ≤ 1 / m := by positivity
    rw [hbound, ENNReal.ofReal_add (by positivity) p3, ENNReal.ofReal_add (by positivity) p3,
      ENNReal.ofReal_add p1 p2]
    refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans ?_) b3)) b4)
    rw [add_comm]
    exact add_le_add b2 b1
  refine (lintegral_mono hcond).trans ?_
  simp

end BstLean.Part82

#print axioms BstLean.Part82.uw_fail3
