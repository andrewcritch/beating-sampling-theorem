import BstLean.Part107Sc

/-!
# Part 107 S(d): the instance — facts about `sphProj`, `kap`, `qLin`, `X1`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

lemma sphProj_coord {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : |sphProj y i| ≤ 1 := by
  unfold sphProj
  simp only [Pi.smul_apply, smul_eq_mul]
  have hS : |y i| ≤ Real.sqrt (∑ j, y j ^ 2) :=
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg (y j))
      (Finset.mem_univ i))
  rw [abs_mul, abs_of_nonneg (by positivity), one_div, inv_mul_eq_div]
  exact div_le_one_of_le₀ hS (Real.sqrt_nonneg _)

lemma dot_sphProj_self {n : ℕ} (y : Fin n → ℝ) :
    dot (sphProj y) (sphProj y) = (1 / Real.sqrt (∑ j, y j ^ 2)) ^ 2 * ∑ j, y j ^ 2 := by
  unfold dot sphProj
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sd_dot_sphProj_self_le {n : ℕ} (y : Fin n → ℝ) : dot (sphProj y) (sphProj y) ≤ 1 := by
  rw [dot_sphProj_self]
  have hS0 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [one_div, inv_pow, Real.sq_sqrt hS0]
  rcases eq_or_ne (∑ j, y j ^ 2) 0 with h | h
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

lemma dot_sphProj_self_eq {n : ℕ} (y : Fin n → ℝ) (hy : y ≠ 0) :
    dot (sphProj y) (sphProj y) = 1 := by
  rw [dot_sphProj_self]
  have hS0 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [one_div, inv_pow, Real.sq_sqrt hS0]
  have h : ∑ j, y j ^ 2 ≠ 0 := by
    intro h0
    apply hy
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (y j))).1 h0 j
      (Finset.mem_univ j)
    simpa using this
  rw [inv_mul_cancel₀ h]

lemma abs_dot_sphProj {n : ℕ} (y y' : Fin n → ℝ) : |dot (sphProj y) (sphProj y')| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  have e : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = dot x x := fun x => by unfold dot; simp [sq]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (sphProj y) (sphProj y')
  rw [e, e] at h
  have h1 := sd_dot_sphProj_self_le y
  have h2 := sd_dot_sphProj_self_le y'
  have h3 : 0 ≤ dot (sphProj y) (sphProj y) := by rw [← e]; positivity
  have h4 : 0 ≤ dot (sphProj y') (sphProj y') := by rw [← e]; positivity
  unfold dot at h ⊢
  unfold dot at h1 h2 h3 h4
  nlinarith

lemma dot_comm' {n : ℕ} (x y : Fin n → ℝ) : dot x y = dot y x := by
  unfold dot; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma kap_one (dA : ℕ) : kap dA 1 = (dA : ℝ) + 1 := by
  simp [kap]

lemma abs_kap_le (dA : ℕ) (τ : ℝ) (h : |τ| ≤ 1) : |kap dA τ| ≤ (dA : ℝ) + 1 := by
  unfold kap
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.range (dA + 1), |τ ^ j| ≤ ∑ j ∈ Finset.range (dA + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h
    _ = (dA : ℝ) + 1 := by simp

lemma sd_measurable_kap (dA : ℕ) : Measurable (kap dA) := by
  unfold kap
  exact Finset.measurable_sum _ fun j _ => measurable_id.pow_const j

/-- `x_W(u) = W(u)/|W(u)|`. -/
noncomputable def xi {N n dW : ℕ} (W : CoefIdx N n dW → ℝ) (u : Fin N → ℝ) : Fin n → ℝ :=
  sphProj (bwEval W u)

/-- `κ(x_W(u)·x_W(u′))`. -/
noncomputable def kW {N n dW : ℕ} (dA : ℕ) (W : CoefIdx N n dW → ℝ) (u u' : Fin N → ℝ) : ℝ :=
  kap dA (dot (xi W u) (xi W u'))

lemma measurable_xi {N n dW : ℕ} {α : Type*} [MeasurableSpace α] {F : α → CoefIdx N n dW → ℝ}
    {G : α → Fin N → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun a => xi (F a) (G a)) :=
  measurable_sphProj.comp (measurable_bwEval_comp hF hG)

lemma sd_measurable_qLin {n dA : ℕ} {α : Type*} [MeasurableSpace α] {F : α → CoefIdx n n dA → ℝ}
    {L G : α → Fin n → ℝ} (hF : Measurable F) (hL : Measurable L) (hG : Measurable G) :
    Measurable (fun a => qLin (F a) (L a) (G a)) :=
  measurable_dot2.comp (hL.prodMk (measurable_bwEval_comp hF hG))

lemma measurable_kW {N n dW : ℕ} (dA : ℕ) {α : Type*} [MeasurableSpace α]
    {F : α → CoefIdx N n dW → ℝ} {G G' : α → Fin N → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hG' : Measurable G') : Measurable (fun a => kW dA (F a) (G a) (G' a)) :=
  (sd_measurable_kap dA).comp (measurable_dot2.comp ((measurable_xi hF hG).prodMk
    (measurable_xi hF hG')))

lemma abs_kW_le {N n dW : ℕ} (dA : ℕ) (W : CoefIdx N n dW → ℝ) (u u' : Fin N → ℝ) :
    |kW dA W u u'| ≤ (dA : ℝ) + 1 :=
  abs_kap_le dA _ (abs_dot_sphProj _ _)

/-- The setting of `Part107Sa` holds for every `W`. -/
lemma setup_inst (hW : Wick107) {N n dW dA : ℕ} (Q : (CoefIdx n n dA → ℝ) × (Fin n → ℝ) → ℝ)
    (hQm : Measurable Q) (hQ0 : ∀ ω, 0 ≤ Q ω) (hQ4 : Integrable (fun ω => Q ω ^ 4) (AL n dA))
    (hQb : ∀ ω (x : Fin n → ℝ), (∀ i, |x i| ≤ 1) → |qLin ω.1 ω.2 x| ≤ Q ω)
    (W : CoefIdx N n dW → ℝ) :
    Setup (AL n dA) (fun θ u => qLin θ.1 θ.2 (xi W u)) Q (kW dA W) (n : ℝ)
      ((n : ℝ) * ((n : ℝ) + 2)) ((dA : ℝ) + 1) where
  hf := sd_measurable_qLin (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
    (measurable_xi measurable_const measurable_snd)
  hQm := hQm
  hQ0 := hQ0
  hQ4 := hQ4
  hfQ := fun θ u => hQb θ _ fun i => sphProj_coord _ i
  hκ := measurable_kW dA measurable_const measurable_fst measurable_snd
  hκC := abs_kW_le dA W
  hsymm := fun u u' => by unfold kW; rw [dot_comm']
  h2 := fun u1 u2 => (hW n dA (xi W u1) (xi W u2) (xi W u1) (xi W u1)).1
  h4 := fun u1 u2 u3 u4 => (hW n dA (xi W u1) (xi W u2) (xi W u3) (xi W u4)).2

/-- `X₁` as a difference of two integrals over `u`. -/
lemma sd_X1_eq {N n dW dA : ℕ} (hN : 1 ≤ N) (W : CoefIdx N n dW → ℝ) (A : CoefIdx n n dA → ℝ)
    (ℓ : Fin n → ℝ) (B : ℝ) (hB : ∀ x : Fin n → ℝ, (∀ i, |x i| ≤ 1) → |qLin A ℓ x| ≤ B) :
    X1 W A ℓ = ∫ u, qLin A ℓ (xi W u) ^ 2 ∂uniformSphere N -
      (∫ u, qLin A ℓ (xi W u) ∂uniformSphere N) ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  have hq : Measurable (fun x => qLin A ℓ x) :=
    sd_measurable_qLin measurable_const measurable_const measurable_id
  have hx : Measurable (fun u => sphProj (bwEval W u)) :=
    measurable_xi measurable_const measurable_id
  unfold X1 muW
  rw [variance_map hq.aemeasurable hx.aemeasurable]
  have hL2 : MemLp ((fun x => qLin A ℓ x) ∘ fun u => sphProj (bwEval W u)) 2 (uniformSphere N) :=
    MemLp.of_bound (hq.comp hx).aestronglyMeasurable B
      (ae_of_all _ fun u => by
        simpa using hB _ fun i => sphProj_coord _ i)
  rw [variance_eq_sub hL2]
  rfl

end BstLean.Part107
