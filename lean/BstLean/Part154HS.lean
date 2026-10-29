import BstLean.Part154App

/-!
# Part 154: Lemma HS: the event `E_H` (the fourth root of `‖H‖²_HS` is Lipschitz in `A₁`)
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

variable {n m : ℕ}

section abstractHS

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

/-- `(C_{uv})_{ij} = E u_i v_j`. -/
private noncomputable def cM (μ : Measure Ω) (u v : Ω → Fin k → ℝ) (i j : Fin k) : ℝ :=
  ∫ ω, u ω i * v ω j ∂μ

/-- `‖C_{uv}‖_F²`. -/
private noncomputable def fr (μ : Measure Ω) (u v : Ω → Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, cM μ u v i j ^ 2

/-- The centred map. -/
private noncomputable def cen (μ : Measure Ω) (w : Ω → Fin k → ℝ) : Ω → Fin k → ℝ :=
  fun ω i => w ω i - fbar μ w i

private lemma fr_nonneg (μ : Measure Ω) (u v : Ω → Fin k → ℝ) : 0 ≤ fr μ u v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma cs_of_quad {P Q R : ℝ} (h : ∀ s : ℝ, 0 ≤ P - 2 * s * Q + s ^ 2 * R) :
    Q ^ 2 ≤ P * R := by
  have h1 := discrim_le_zero (a := R) (b := -2 * Q) (c := P) (fun s => by
    have := h s
    linarith)
  unfold discrim at h1
  linarith

private lemma int3 (μ : Measure Ω) {f g h : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (a b : ℝ) :
    ∫ ω, f ω - a * g ω + b * h ω ∂μ = ∫ ω, f ω ∂μ - a * ∫ ω, g ω ∂μ + b * ∫ ω, h ω ∂μ := by
  have h1 := integral_add (μ := μ) (f := fun ω => f ω - a * g ω) (g := fun ω => b * h ω)
    (hf.sub (hg.const_mul a)) (hh.const_mul b)
  have h2 := integral_sub (μ := μ) (f := fun ω => f ω) (g := fun ω => a * g ω) hf
    (hg.const_mul a)
  rw [h1, h2, integral_const_mul, integral_const_mul]

private lemma kern (μ : Measure Ω) {a b c d : Ω → Fin k → ℝ}
    (ha : ∀ i, MemLp (fun ω => a ω i) 2 μ) (hb : ∀ i, MemLp (fun ω => b ω i) 2 μ)
    (hc : ∀ i, MemLp (fun ω => c ω i) 2 μ) (hd : ∀ i, MemLp (fun ω => d ω i) 2 μ) :
    (∀ ω, Integrable (fun ω' => (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j)) μ) ∧
    Integrable (fun ω => ∫ ω', (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j) ∂μ) μ ∧
    ∫ ω, ∫ ω', (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j) ∂μ ∂μ =
      ∑ i, ∑ j, cM μ a c i j * cM μ b d i j := by
  have e : ∀ ω ω', (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j) =
      ∑ i, ∑ j, (a ω i * c ω j) * (b ω' i * d ω' j) := by
    intro ω ω'
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hbd : ∀ i j, Integrable (fun ω => b ω i * d ω j) μ := fun i j =>
    (hb i).integrable_mul (hd j)
  have hac : ∀ i j, Integrable (fun ω => a ω i * c ω j) μ := fun i j =>
    (ha i).integrable_mul (hc j)
  have hin : ∀ ω, Integrable (fun ω' => ∑ i, ∑ j, (a ω i * c ω j) * (b ω' i * d ω' j)) μ :=
    fun ω => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hbd i j).const_mul _
  have ein : ∀ ω, ∫ ω', (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j) ∂μ =
      ∑ i, ∑ j, (a ω i * c ω j) * cM μ b d i j := by
    intro ω
    have e' : (fun ω' => (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j)) =
        fun ω' => ∑ i, ∑ j, (a ω i * c ω j) * (b ω' i * d ω' j) := funext (e ω)
    rw [e', integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hbd i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hbd i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl
  have hout : Integrable (fun ω => ∑ i, ∑ j, (a ω i * c ω j) * cM μ b d i j) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hac i j).mul_const _
  have eo : (fun ω => ∫ ω', (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j) ∂μ) =
      fun ω => ∑ i, ∑ j, (a ω i * c ω j) * cM μ b d i j := funext ein
  refine ⟨fun ω => ?_, ?_, ?_⟩
  · have e' : (fun ω' => (∑ i, a ω i * b ω' i) * (∑ j, c ω j * d ω' j)) =
        fun ω' => ∑ i, ∑ j, (a ω i * c ω j) * (b ω' i * d ω' j) := funext (e ω)
    rw [e']
    exact hin ω
  · rw [eo]
    exact hout
  · rw [eo, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hac i j).mul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hac i j).mul_const _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
    rfl

/-- `‖C_{uv}‖_F⁴ ≤ ‖C_{uu}‖_F²·‖C_{vv}‖_F²`. -/
private lemma fr_cs (μ : Measure Ω) {u v : Ω → Fin k → ℝ}
    (hu : ∀ i, MemLp (fun ω => u ω i) 2 μ) (hv : ∀ i, MemLp (fun ω => v ω i) 2 μ) :
    fr μ u v ^ 2 ≤ fr μ u u * fr μ v v := by
  obtain ⟨i1, o1, e1⟩ := kern μ hu hu hu hu
  obtain ⟨i2, o2, e2⟩ := kern μ hu hu hv hv
  obtain ⟨i3, o3, e3⟩ := kern μ hv hv hv hv
  have f1 : ∑ i, ∑ j, cM μ u u i j * cM μ u u i j = fr μ u u := by simp only [fr, sq]
  have f2 : ∑ i, ∑ j, cM μ u v i j * cM μ u v i j = fr μ u v := by simp only [fr, sq]
  have f3 : ∑ i, ∑ j, cM μ v v i j * cM μ v v i j = fr μ v v := by simp only [fr, sq]
  rw [f1] at e1
  rw [f2] at e2
  rw [f3] at e3
  apply cs_of_quad
  intro s
  have hp : 0 ≤ ∫ ω, ∫ ω', ((∑ i, u ω i * u ω' i) - s * ∑ i, v ω i * v ω' i) ^ 2 ∂μ ∂μ :=
    integral_nonneg fun ω => integral_nonneg fun ω' => sq_nonneg _
  have ein : ∀ ω, ∫ ω', ((∑ i, u ω i * u ω' i) - s * ∑ i, v ω i * v ω' i) ^ 2 ∂μ =
      (∫ ω', (∑ i, u ω i * u ω' i) * (∑ j, u ω j * u ω' j) ∂μ) -
        2 * s * (∫ ω', (∑ i, u ω i * u ω' i) * (∑ j, v ω j * v ω' j) ∂μ) +
        s ^ 2 * ∫ ω', (∑ i, v ω i * v ω' i) * (∑ j, v ω j * v ω' j) ∂μ := by
    intro ω
    rw [← int3 μ (i1 ω) (i2 ω) (i3 ω)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω' => ?_)
    simp only []
    ring
  have eo : (fun ω => ∫ ω', ((∑ i, u ω i * u ω' i) - s * ∑ i, v ω i * v ω' i) ^ 2 ∂μ) =
      fun ω => (∫ ω', (∑ i, u ω i * u ω' i) * (∑ j, u ω j * u ω' j) ∂μ) -
        2 * s * (∫ ω', (∑ i, u ω i * u ω' i) * (∑ j, v ω j * v ω' j) ∂μ) +
        s ^ 2 * ∫ ω', (∑ i, v ω i * v ω' i) * (∑ j, v ω j * v ω' j) ∂μ := funext ein
  rw [eo, int3 μ o1 o2 o3, e1, e2, e3] at hp
  exact hp

private lemma fr_symm (μ : Measure Ω) (u v : Ω → Fin k → ℝ) : fr μ v u = fr μ u v := by
  unfold fr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold cM
  simp only [mul_comm]

private lemma sqrt_fr_eq (μ : Measure Ω) (u v : Ω → Fin k → ℝ) :
    √(fr μ u v) = BstLean.Part153.nrm (fun p : Fin k × Fin k => cM μ u v p.1 p.2) := by
  unfold BstLean.Part153.nrm normSq fr
  rw [Fintype.sum_prod_type]

/-- The triangle inequality for `N(u) = ‖C_{uu}‖_F^{1/2}`. -/
private lemma N_tri (μ : Measure Ω) {u v w : Ω → Fin k → ℝ}
    (hu : ∀ i, MemLp (fun ω => u ω i) 2 μ) (hv : ∀ i, MemLp (fun ω => v ω i) 2 μ)
    (hw : ∀ ω i, w ω i = u ω i + v ω i) :
    √(√(fr μ w w)) ≤ √(√(fr μ u u)) + √(√(fr μ v v)) := by
  have hcM : ∀ i j, cM μ w w i j = cM μ u u i j + cM μ u v i j + cM μ v u i j + cM μ v v i j := by
    intro i j
    unfold cM
    have a1 : Integrable (fun ω => u ω i * u ω j) μ := (hu i).integrable_mul (hu j)
    have a2 : Integrable (fun ω => u ω i * v ω j) μ := (hu i).integrable_mul (hv j)
    have a3 : Integrable (fun ω => v ω i * u ω j) μ := (hv i).integrable_mul (hu j)
    have a4 : Integrable (fun ω => v ω i * v ω j) μ := (hv i).integrable_mul (hv j)
    have b1 := integral_add (μ := μ) (f := fun ω => u ω i * u ω j) (g := fun ω => u ω i * v ω j)
      a1 a2
    have b2 := integral_add (μ := μ) (f := fun ω => u ω i * u ω j + u ω i * v ω j)
      (g := fun ω => v ω i * u ω j) (a1.add a2) a3
    have b3 := integral_add (μ := μ)
      (f := fun ω => u ω i * u ω j + u ω i * v ω j + v ω i * u ω j)
      (g := fun ω => v ω i * v ω j) ((a1.add a2).add a3) a4
    rw [← b1, ← b2, ← b3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hw]
    ring
  have hF : (fun p : Fin k × Fin k => cM μ w w p.1 p.2) =
      (fun p : Fin k × Fin k => cM μ u u p.1 p.2) + (fun p => cM μ u v p.1 p.2) +
        (fun p => cM μ v u p.1 p.2) + (fun p => cM μ v v p.1 p.2) := by
    funext p
    simp only [Pi.add_apply]
    exact hcM p.1 p.2
  have h1 : √(fr μ w w) ≤ √(fr μ u u) + 2 * √(fr μ u v) + √(fr μ v v) := by
    have ha := BstLean.Part153.nrm_add_le
      ((fun p : Fin k × Fin k => cM μ u u p.1 p.2) + (fun p => cM μ u v p.1 p.2) +
        (fun p => cM μ v u p.1 p.2)) (fun p => cM μ v v p.1 p.2)
    have hb := BstLean.Part153.nrm_add_le
      ((fun p : Fin k × Fin k => cM μ u u p.1 p.2) + (fun p => cM μ u v p.1 p.2))
      (fun p => cM μ v u p.1 p.2)
    have hc := BstLean.Part153.nrm_add_le
      (fun p : Fin k × Fin k => cM μ u u p.1 p.2) (fun p => cM μ u v p.1 p.2)
    have n0 := sqrt_fr_eq μ w w
    have n1 := sqrt_fr_eq μ u u
    have n2 := sqrt_fr_eq μ u v
    have n3 := sqrt_fr_eq μ v u
    have n4 := sqrt_fr_eq μ v v
    rw [fr_symm μ u v] at n3
    rw [hF] at n0
    linarith
  set P := fr μ u u with hP
  set Q := fr μ u v with hQ
  set R := fr μ v v with hR
  have hP0 : 0 ≤ P := fr_nonneg _ _ _
  have hQ0 : 0 ≤ Q := fr_nonneg _ _ _
  have hR0 : 0 ≤ R := fr_nonneg _ _ _
  have hcs : Q ^ 2 ≤ P * R := fr_cs μ hu hv
  have hQle : Q ≤ √P * √R := by
    rw [← Real.sqrt_mul hP0, ← Real.sqrt_sq hQ0]
    exact Real.sqrt_le_sqrt hcs
  have hsQ : √Q ≤ √(√P) * √(√R) := by
    rw [← Real.sqrt_mul (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hQle
  have hp2 : √(√P) ^ 2 = √P := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hr2 : √(√R) ^ 2 = √R := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : √(fr μ w w) ≤ (√(√P) + √(√R)) ^ 2 := by nlinarith
  calc √(√(fr μ w w)) ≤ √((√(√P) + √(√R)) ^ 2) := Real.sqrt_le_sqrt h2
    _ = √(√P) + √(√R) := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- `N(w̃)⁴ ≤ (E|w|²)²`. -/
private lemma fr_cen_le (μ : Measure Ω) [IsProbabilityMeasure μ] {w : Ω → Fin k → ℝ}
    (hw : ∀ i, MemLp (fun ω => w ω i) 2 μ) :
    fr μ (cen μ w) (cen μ w) ≤ (∫ ω, normSq (w ω) ∂μ) ^ 2 := by
  have hc : ∀ i, MemLp (fun ω => cen μ w ω i) 2 μ := fun i => (hw i).sub (memLp_const _)
  have hwi : ∀ i, Integrable (fun ω => w ω i) μ := fun i => (hw i).integrable one_le_two
  have hw2 : ∀ i, Integrable (fun ω => w ω i ^ 2) μ := fun i => (hw i).integrable_sq
  have hc2 : ∀ i, Integrable (fun ω => cen μ w ω i ^ 2) μ := fun i => (hc i).integrable_sq
  set E : Fin k → ℝ := fun i => ∫ ω, w ω i ^ 2 ∂μ with hE
  set V : Fin k → ℝ := fun i => ∫ ω, cen μ w ω i ^ 2 ∂μ with hV
  have hV0 : ∀ i, 0 ≤ V i := fun i => integral_nonneg fun ω => sq_nonneg _
  have hVE : ∀ i, V i ≤ E i := by
    intro i
    have e1 : ∀ ω, cen μ w ω i ^ 2 = w ω i ^ 2 - 2 * fbar μ w i * w ω i + fbar μ w i ^ 2 := by
      intro ω
      unfold cen
      ring
    have e2 : V i = E i - 2 * fbar μ w i * (∫ ω, w ω i ∂μ) + fbar μ w i ^ 2 := by
      simp only [hV, hE]
      have e3 : ∫ ω, cen μ w ω i ^ 2 ∂μ =
          ∫ ω, w ω i ^ 2 - 2 * fbar μ w i * w ω i + fbar μ w i ^ 2 * (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by
          simp only [e1 ω, mul_one])
      rw [e3, int3 μ (hw2 i) (hwi i) (integrable_const (1 : ℝ))]
      simp
    have e4 : ∫ ω, w ω i ∂μ = fbar μ w i := rfl
    rw [e4] at e2
    nlinarith [sq_nonneg (fbar μ w i)]
  have hcov : ∀ i j, cM μ (cen μ w) (cen μ w) i j ^ 2 ≤ E i * E j := by
    intro i j
    have h1 : cM μ (cen μ w) (cen μ w) i j ^ 2 ≤ V i * V j := by
      apply cs_of_quad
      intro s
      have hp : 0 ≤ ∫ ω, (cen μ w ω i - s * cen μ w ω j) ^ 2 ∂μ :=
        integral_nonneg fun ω => sq_nonneg _
      have hij : Integrable (fun ω => cen μ w ω i * cen μ w ω j) μ :=
        (hc i).integrable_mul (hc j)
      have e3 : ∫ ω, (cen μ w ω i - s * cen μ w ω j) ^ 2 ∂μ =
          ∫ ω, cen μ w ω i ^ 2 - 2 * s * (cen μ w ω i * cen μ w ω j) +
            s ^ 2 * cen μ w ω j ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      rw [e3, int3 μ (hc2 i) hij (hc2 j)] at hp
      exact hp
    exact h1.trans (mul_le_mul (hVE i) (hVE j) (hV0 j) ((hV0 i).trans (hVE i)))
  have hsum : ∫ ω, normSq (w ω) ∂μ = ∑ i, E i := by
    unfold normSq
    rw [integral_finsetSum _ fun i _ => hw2 i]
  rw [hsum, sq, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcov i j

/-- `|N(ũ) − N(ṽ)| ≤ K` if `E|u − v|² ≤ K²` (both orders). -/
private lemma N_lip (μ : Measure Ω) [IsProbabilityMeasure μ] {u v : Ω → Fin k → ℝ}
    (hu : ∀ i, MemLp (fun ω => u ω i) 2 μ) (hv : ∀ i, MemLp (fun ω => v ω i) 2 μ) {K : ℝ}
    (hK : 0 ≤ K) (h1 : ∫ ω, normSq (fun i => u ω i - v ω i) ∂μ ≤ K ^ 2)
    (h2 : ∫ ω, normSq (fun i => v ω i - u ω i) ∂μ ≤ K ^ 2) :
    |√(√(fr μ (cen μ u) (cen μ u))) - √(√(fr μ (cen μ v) (cen μ v)))| ≤ K := by
  have hui : ∀ i, Integrable (fun ω => u ω i) μ := fun i => (hu i).integrable one_le_two
  have hvi : ∀ i, Integrable (fun ω => v ω i) μ := fun i => (hv i).integrable one_le_two
  have hcu : ∀ i, MemLp (fun ω => cen μ u ω i) 2 μ := fun i => (hu i).sub (memLp_const _)
  have hcv : ∀ i, MemLp (fun ω => cen μ v ω i) 2 μ := fun i => (hv i).sub (memLp_const _)
  have hd1 : ∀ i, MemLp (fun ω => u ω i - v ω i) 2 μ := fun i => (hu i).sub (hv i)
  have hd2 : ∀ i, MemLp (fun ω => v ω i - u ω i) 2 μ := fun i => (hv i).sub (hu i)
  have hcd1 : ∀ i, MemLp (fun ω => cen μ (fun ω i => u ω i - v ω i) ω i) 2 μ := fun i =>
    (hd1 i).sub (memLp_const _)
  have hcd2 : ∀ i, MemLp (fun ω => cen μ (fun ω i => v ω i - u ω i) ω i) 2 μ := fun i =>
    (hd2 i).sub (memLp_const _)
  have bnd : ∀ {d : Ω → Fin k → ℝ}, (∀ i, MemLp (fun ω => d ω i) 2 μ) →
      ∫ ω, normSq (d ω) ∂μ ≤ K ^ 2 → √(√(fr μ (cen μ d) (cen μ d))) ≤ K := by
    intro d hd hdK
    have h0 : 0 ≤ ∫ ω, normSq (d ω) ∂μ := integral_nonneg fun ω => normSq_nonneg _
    calc √(√(fr μ (cen μ d) (cen μ d))) ≤ √(√((∫ ω, normSq (d ω) ∂μ) ^ 2)) :=
          Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (fr_cen_le μ hd))
      _ = √(∫ ω, normSq (d ω) ∂μ) := by rw [Real.sqrt_sq h0]
      _ ≤ √(K ^ 2) := Real.sqrt_le_sqrt hdK
      _ = K := Real.sqrt_sq hK
  have t1 := N_tri μ (u := cen μ v) (v := cen μ (fun ω i => u ω i - v ω i)) (w := cen μ u)
    hcv hcd1 (by
      intro ω i
      unfold cen fbar
      rw [integral_sub (hui i) (hvi i)]
      ring)
  have t2 := N_tri μ (u := cen μ u) (v := cen μ (fun ω i => v ω i - u ω i)) (w := cen μ v)
    hcu hcd2 (by
      intro ω i
      unfold cen fbar
      rw [integral_sub (hvi i) (hui i)]
      ring)
  have b1 := bnd hd1 h1
  have b2 := bnd hd2 h2
  rw [abs_le]
  constructor <;> linarith

end abstractHS

private lemma continuous_fA_HS (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Continuous (fA A c τ) := by
  show Continuous (fun ξ : Fin n → ℝ => √(2 / (m : ℝ)) • reluV (A *ᵥ (c + τ • ξ)))
  exact (BstLean.Part153.continuous_h1 A c τ).const_smul (√(2 / (m : ℝ)))

private lemma fA_apply_HS (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ)
    (i : Fin m) : fA A c τ ξ i = √(2 / (m : ℝ)) * reluV (A *ᵥ (c + τ • ξ)) i := rfl

private lemma memLp_fA_HS (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (i : Fin m) :
    MemLp (fun ξ => fA A c τ ξ i) 2 (stdGauss (Fin n)) := by
  have hc : Continuous (fun ξ => fA A c τ ξ i) :=
    (continuous_apply i).comp (continuous_fA_HS A c τ)
  refine (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' ((BstLean.Part153.integrable_h1_sq A c τ).const_mul (2 / (m : ℝ)))
    (hc.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), fA_apply_HS, mul_pow,
    Real.sq_sqrt (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold normSq
  exact Finset.single_le_sum (f := fun i => reluV (A *ᵥ (c + τ • ξ)) i ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private lemma en_le_HS (c : Fin n → ℝ) (τ : ℝ) (A A' : Matrix (Fin m) (Fin n) ℝ) :
    ∫ ξ, normSq (fun i => fA A c τ ξ i - fA A' c τ ξ i) ∂stdGauss (Fin n) ≤
      2 / (m : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) * ∑ i, ∑ j, (A i j - A' i j) ^ 2 := by
  set S := ∑ i, ∑ j, (A i j - A' i j) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpt : ∀ ξ : Fin n → ℝ, normSq (fun i => fA A c τ ξ i - fA A' c τ ξ i) ≤
      2 / (m : ℝ) * (S * normSq (c + τ • ξ)) := by
    intro ξ
    have e0 : (fun i => fA A c τ ξ i - fA A' c τ ξ i) =
        √(2 / (m : ℝ)) • (reluV (A *ᵥ (c + τ • ξ)) - reluV (A' *ᵥ (c + τ • ξ))) := by
      funext i
      simp only [fA_apply_HS, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [e0, normSq_smul, Real.sq_sqrt (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : A *ᵥ (c + τ • ξ) - A' *ᵥ (c + τ • ξ) = (A - A') *ᵥ (c + τ • ξ) := by
      rw [Matrix.sub_mulVec]
    have hfro : opN (A - A') ≤ √S := by
      have := opN_le_frob (A - A')
      simpa [hS, Matrix.sub_apply] using this
    have h1 : nrm (reluV (A *ᵥ (c + τ • ξ)) - reluV (A' *ᵥ (c + τ • ξ))) ≤
        √S * nrm (c + τ • ξ) :=
      calc nrm (reluV (A *ᵥ (c + τ • ξ)) - reluV (A' *ᵥ (c + τ • ξ)))
          ≤ nrm (A *ᵥ (c + τ • ξ) - A' *ᵥ (c + τ • ξ)) := BstLean.Part153.nrm_reluV_sub_le _ _
        _ = nrm ((A - A') *ᵥ (c + τ • ξ)) := by rw [e]
        _ ≤ opN (A - A') * nrm (c + τ • ξ) := BstLean.Part153.nrm_mulVec_le _ _
        _ ≤ √S * nrm (c + τ • ξ) :=
          mul_le_mul_of_nonneg_right hfro (BstLean.Part153.nrm_nonneg _)
    have h2 := pow_le_pow_left₀ (BstLean.Part153.nrm_nonneg _) h1 2
    rw [BstLean.Part153.nrm_sq, mul_pow, BstLean.Part153.nrm_sq, Real.sq_sqrt hS0] at h2
    exact h2
  have hI := (BstLean.Part153.int_normSq_shift c τ)
  have hcont : Continuous (fun ξ : Fin n → ℝ => normSq (fun i => fA A c τ ξ i - fA A' c τ ξ i)) :=
    continuous_normSq.comp (continuous_pi fun i =>
      ((continuous_apply i).comp (continuous_fA_HS A c τ)).sub
        ((continuous_apply i).comp (continuous_fA_HS A' c τ)))
  have hdom : Integrable (fun ξ : Fin n → ℝ => 2 / (m : ℝ) * (S * normSq (c + τ • ξ)))
      (stdGauss (Fin n)) := (hI.1.const_mul S).const_mul _
  have hint : Integrable (fun ξ : Fin n → ℝ => normSq (fun i => fA A c τ ξ i - fA A' c τ ξ i))
      (stdGauss (Fin n)) :=
    Integrable.mono' hdom hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (normSq_nonneg _)]
      exact hpt ξ)
  calc ∫ ξ, normSq (fun i => fA A c τ ξ i - fA A' c τ ξ i) ∂stdGauss (Fin n)
      ≤ ∫ ξ, 2 / (m : ℝ) * (S * normSq (c + τ • ξ)) ∂stdGauss (Fin n) :=
        integral_mono hint hdom hpt
    _ = 2 / (m : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) * S := by
        rw [integral_const_mul, integral_const_mul, hI.2]
        ring

private lemma hsH_eq_HS (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    hsH A c τ = fr (stdGauss (Fin n)) (cen (stdGauss (Fin n)) (fA A c τ))
      (cen (stdGauss (Fin n)) (fA A c τ)) := rfl

private lemma hsH_nonneg_HS (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    0 ≤ hsH A c τ := by
  rw [hsH_eq_HS]
  exact fr_nonneg _ _ _

/-- `(E X)² ≤ E X²`. -/
private lemma sq_int_le_HS {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (h1 : Integrable X μ) (h2 : Integrable (fun ω => X ω ^ 2) μ) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂μ := by
  set e := ∫ ω, X ω ∂μ with he
  have hp : 0 ≤ ∫ ω, (X ω - e) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have e3 : ∫ ω, (X ω - e) ^ 2 ∂μ =
      ∫ ω, X ω ^ 2 - 2 * e * X ω + e ^ 2 * (fun _ => (1 : ℝ)) ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [mul_one]
      ring)
  rw [e3, int3 μ h2 h1 (integrable_const (1 : ℝ)), ← he] at hp
  simp at hp
  nlinarith

/-- `‖H‖_HS^{1/2} = (‖H‖²_HS)^{1/4}` is Lipschitz in `A₁` (Frobenius norm) with the constant
`√t·ρ`. -/
theorem hsH_lip (c : Fin n → ℝ) (τ : ℝ) (A A' : Matrix (Fin m) (Fin n) ℝ) :
    |√(√(hsH A c τ)) - √(√(hsH A' c τ))| ≤
      (√(2 / (m : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) * √(∑ i, ∑ j, (A i j - A' i j) ^ 2) := by
  set S := ∑ i, ∑ j, (A i j - A' i j) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hρ0 : 0 ≤ normSq c + (n : ℝ) * τ ^ 2 := add_nonneg (normSq_nonneg _) (by positivity)
  have hK : (√(2 / (m : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2) * √S) ^ 2 =
      2 / (m : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) * S := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hρ0, Real.sq_sqrt hS0]
  have h1 := en_le_HS c τ A A'
  have h2 := en_le_HS c τ A' A
  have hS' : ∑ i, ∑ j, (A' i j - A i j) ^ 2 = S :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hS'] at h2
  rw [← hK] at h1 h2
  rw [hsH_eq_HS, hsH_eq_HS]
  exact N_lip (stdGauss (Fin n)) (memLp_fA_HS A c τ) (memLp_fA_HS A' c τ) (by positivity) h1 h2

/-- The complement of `E_H` at the level `L_c`. -/
def BadH (n : ℕ) (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | ∫ A, √(√(hsH A c τ)) ∂gaussMat (mA n) n (2 / (n : ℝ)) +
      √(2 * Lc * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) <
    √(√(hsH A c τ))}

theorem EH_prob {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (BadH n c τ Lc) ≤ rexp (-Lc) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ0 : 0 ≤ normSq c + (n : ℝ) * τ ^ 2 := add_nonneg (normSq_nonneg _) (by positivity)
  exact BstLean.Part153.conc_upper_strict
    (g := fun A : Matrix (Fin (mA n)) (Fin n) ℝ => √(√(hsH A c τ)))
    (L := √(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) (by positivity)
    (hsH_lip c τ) (v := 2 / (n : ℝ)) (by positivity) hLc

/-- On `E_H`, with a bound `B` of the mean of `‖H‖²_HS`:
`‖H‖²_HS ≤ (B^{1/4} + 2√(2L_c)·ρ/n^{3/2})⁴`. -/
theorem EH_bound {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc) {B : ℝ}
    (hint : Integrable (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => hsH A₁ c τ)
      (gaussMat (mA n) n (2 / (n : ℝ))))
    (hB : ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ B)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A₁ ∉ BadH n c τ Lc) :
    hsH A₁ c τ ≤ (√(√B) + 2 * √(2 * Lc) * √(normSq c + (n : ℝ) * τ ^ 2) /
      ((n : ℝ) * √(n : ℝ))) ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set ρ2 := normSq c + (n : ℝ) * τ ^ 2 with hρ2
  have hρ0 : 0 ≤ ρ2 := add_nonneg (normSq_nonneg _) (by positivity)
  set ν := gaussMat (mA n) n (2 / (n : ℝ)) with hν
  set g : Matrix (Fin (mA n)) (Fin n) ℝ → ℝ := fun A => √(√(hsH A c τ)) with hg
  have hgc : Continuous g := BstLean.Part148.matLip_continuous (hsH_lip c τ)
  have hg0 : ∀ A, 0 ≤ g A := fun A => Real.sqrt_nonneg _
  have hg2 : ∀ A, g A ^ 2 = √(hsH A c τ) := fun A => Real.sq_sqrt (Real.sqrt_nonneg _)
  have hg4 : ∀ A, (g A ^ 2) ^ 2 = hsH A c τ := fun A => by
    rw [hg2, Real.sq_sqrt (hsH_nonneg_HS A c τ)]
  have hdom : Integrable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => 1 + hsH A c τ) ν :=
    (integrable_const (1 : ℝ)).add hint
  have hgi : Integrable g ν :=
    Integrable.mono' hdom hgc.aestronglyMeasurable (Filter.Eventually.of_forall fun A => by
      rw [Real.norm_of_nonneg (hg0 A), ← hg4 A]
      nlinarith [sq_nonneg (g A ^ 2 - 1), sq_nonneg (g A - 1), hg0 A, sq_nonneg (g A ^ 2)])
  have hg2i : Integrable (fun A => g A ^ 2) ν :=
    Integrable.mono' hdom (hgc.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun A => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← hg4 A]
        nlinarith [sq_nonneg (g A ^ 2 - 1), sq_nonneg (g A ^ 2)])
  have hg4i : Integrable (fun A => (g A ^ 2) ^ 2) ν := by
    simp only [hg4]
    exact hint
  have j1 := sq_int_le_HS ν hgi hg2i
  have j2 := sq_int_le_HS ν hg2i hg4i
  simp only [hg4] at j2
  set e := ∫ A, g A ∂ν with he
  have he0 : 0 ≤ e := integral_nonneg hg0
  have hB0 : 0 ≤ B := le_trans (sq_nonneg _) (j2.trans hB)
  have he4 : (e ^ 2) ^ 2 ≤ B :=
    (pow_le_pow_left₀ (sq_nonneg e) j1 2).trans (j2.trans hB)
  have he2 : e ^ 2 ≤ √B := by
    rw [← Real.sqrt_sq (sq_nonneg e)]
    exact Real.sqrt_le_sqrt he4
  have he1 : e ≤ √(√B) := by
    rw [← Real.sqrt_sq he0]
    exact Real.sqrt_le_sqrt he2
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hdev : √(2 * Lc * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √ρ2) =
      2 * √(2 * Lc) * √ρ2 / ((n : ℝ) * √(n : ℝ)) := by
    have h22 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
    have hsn : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    rw [hm, Real.sqrt_mul (by positivity) (2 / (n : ℝ)), Real.sqrt_div (by norm_num),
      Real.sqrt_div (by norm_num), Real.sqrt_sq hn0.le]
    have gen : ∀ a b r x y : ℝ, b * b = 2 → a * (b / x) * (b / y * r) = 2 * a * r / (y * x) := by
      intro a b r x y hb
      rw [← hb]
      ring
    exact gen _ _ _ _ _ h22
  have hA' : g A₁ ≤ e + √(2 * Lc * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √ρ2) := by
    exact not_lt.mp hA
  rw [hdev] at hA'
  have hdev0 : 0 ≤ 2 * √(2 * Lc) * √ρ2 / ((n : ℝ) * √(n : ℝ)) := by positivity
  have hfin : g A₁ ≤ √(√B) + 2 * √(2 * Lc) * √ρ2 / ((n : ℝ) * √(n : ℝ)) := by linarith
  calc hsH A₁ c τ = g A₁ ^ 4 := by rw [← hg4 A₁]; ring
    _ ≤ _ := pow_le_pow_left₀ (hg0 A₁) hfin 4

theorem measurableSet_BadH {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (Lc : ℝ) :
    MeasurableSet (BadH n c τ Lc) := by
  have hgc : Continuous (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => √(√(hsH A c τ))) :=
    BstLean.Part148.matLip_continuous (hsH_lip c τ)
  exact measurableSet_lt measurable_const hgc.measurable

end BstLean.Part154
