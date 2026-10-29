import BstLean.Part78Defs

/-!
# Part 78: the Gaussian model given the constant column

From the exact conditional identities (`MeanIds`), the sphere constants (`SphereConsts`) and the
conditional variance bound (`VarBound`):

* `floor_le`: `E_W V ≥ (3/2)‖a‖² + 4.49‖H‖²` (`Wf a H`), `n ≥ 1000`.
* `err_le`: `E_W (B − g₀)² ≤ (‖a‖² + (2 S2 + 9/4)‖H‖²)/n`.
* `mean_upper`: `E_W V ≤ 1.51‖a‖² + 5.3‖H‖²`.
* `cheb_floor`, `markov_err`: the two conditional tails.
* `gauss_model`: the Gaussian-model theorem, for every `a` (that is, given `u`):
  failure `≤ c₁/(n ε² κ) + c_V/(n (1−κ)²)`, `c_V = cW`, `κ = 1 − θ`.
-/

namespace BstLean.Part78

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)

variable {n : ℕ}

lemma nsq_nonneg (a : Fin n → ℝ) : 0 ≤ nsq a := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma frobH_nonneg (H : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobH H :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma trH_sq_le (H : Matrix (Fin n) (Fin n) ℝ) : trH H ^ 2 ≤ n * frobH H := by
  have h1 : (∑ i, H i i) ^ 2 ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) * ∑ i, H i i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : ∑ i, H i i ^ 2 ≤ frobH H :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => H i j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold trH
  nlinarith

/-- The floor of `E_W V`. -/
noncomputable def Wf (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : ℝ := 3 / 2 * nsq a + 449 / 100 * frobH H

lemma Wf_nonneg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ Wf a H := by
  unfold Wf; nlinarith [nsq_nonneg a, frobH_nonneg H]

/-- **Conditional variance bound, floor form**: `Var_W V ≤ (cW/n) · Wf · E_W V`. -/
def VarBoundW (n : ℕ) (cW : ℝ) : Prop :=
  ∀ (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.IsSymm →
    ∫ W, (VG a H W - ∫ W', VG a H W' ∂stdGauss (WIdx n)) ^ 2 ∂stdGauss (WIdx n) ≤
      cW / (n : ℝ) * Wf a H * ∫ W, VG a H W ∂stdGauss (WIdx n)

lemma meas_le_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {S : Set α} {c : ℝ} (h : μ.real S ≤ c) : μ S ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ S)]
  exact ENNReal.ofReal_le_ofReal h

/-- Markov, strict form. -/
lemma markov_gt {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) {t B : ℝ} (ht : 0 < t) (hB : ∫ x, f x ∂μ ≤ B) :
    μ {x | t < f x} ≤ ENNReal.ofReal (B / t) := by
  apply meas_le_ofReal
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Filter.Eventually.of_forall hf0) hfi t
  have h2 : μ.real {x | t < f x} ≤ μ.real {x | t ≤ f x} :=
    measureReal_mono (fun x (hx : t < f x) => (le_of_lt hx : t ≤ f x))
  rw [le_div_iff₀ ht]
  nlinarith

lemma floor_le (hn : 1000 ≤ n) {S2 : ℝ} (hS : SphereConsts n S2) (hS2 : S2 ≤ 5) (hM : MeanIds n)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    Wf a H ≤ ∫ W, VG a H W ∂stdGauss (WIdx n) := by
  obtain ⟨htG, hm1, hk1, hk2, hs0, hs2, -⟩ := hS
  rw [(hM a H hH).2.2.2.1]
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 : 1 / (n : ℝ) ≤ 3 / (2 * ((n : ℝ) + 2)) := by
    rw [div_le_div_iff₀ hnpos (by positivity)]; nlinarith
  have h0 : 0 ≤ 3 / (2 * ((n : ℝ) + 2)) := by positivity
  have htG32 : 3 / 2 ≤ tG n := by rw [htG]; linarith
  have hA : 3 / 2 ≤ tG n - mm1 n := by rw [hm1, htG]; linarith
  have hS2n : S2 / (n : ℝ) ≤ 5 / 1000 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]; nlinarith
  have hB : 449 / 200 ≤ kk2 n - ss2 n := by nlinarith
  have hC : 0 ≤ kk2 n - tG n ^ 2 := by linarith
  unfold Wf
  nlinarith [mul_nonneg (sub_nonneg.2 hA) (nsq_nonneg a), mul_nonneg (sq_nonneg (trH H)) hC,
    mul_nonneg (frobH_nonneg H) (sub_nonneg.2 hB)]

lemma err_le (hn : 1000 ≤ n) {S2 : ℝ} (hS : SphereConsts n S2) (hM : MeanIds n)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ∫ W, errG a H W ^ 2 ∂stdGauss (WIdx n) ≤ (nsq a + (2 * S2 + 9 / 4) * frobH H) / n := by
  obtain ⟨htG, hm1, -, -, hs0, hs2, -⟩ := hS
  rw [(hM a H hH).2.2.2.2, hm1]
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hf := frobH_nonneg H
  have e0 : (tG n - 3 / 2) ^ 2 = 9 / (4 * ((n : ℝ) + 2) ^ 2) := by
    rw [htG]; field_simp; ring
  have e1 : (tG n - 3 / 2) ^ 2 ≤ 9 / (4 * (n : ℝ) ^ 2) := by
    rw [e0]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have e2 := trH_sq_le H
  have e3 : trH H ^ 2 * (tG n - 3 / 2) ^ 2 ≤ (n * frobH H) * (9 / (4 * (n : ℝ) ^ 2)) :=
    mul_le_mul e2 e1 (sq_nonneg _) (mul_nonneg hnpos.le hf)
  have e4 : (n * frobH H) * (9 / (4 * (n : ℝ) ^ 2)) = 9 / 4 * frobH H / n := by
    field_simp
  have e5 : 2 * frobH H * ss2 n ≤ 2 * frobH H * (S2 / n) :=
    mul_le_mul_of_nonneg_left hs2 (by linarith)
  have e6 : (nsq a + (2 * S2 + 9 / 4) * frobH H) / n =
      nsq a * (1 / n) + 2 * frobH H * (S2 / n) + 9 / 4 * frobH H / n := by
    field_simp; ring
  rw [e6]; linarith

lemma mean_upper (hn : 1000 ≤ n) {S2 : ℝ} (hS : SphereConsts n S2) (hM : MeanIds n)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    ∫ W, VG a H W ∂stdGauss (WIdx n) ≤ 151 / 100 * nsq a + 53 / 10 * frobH H := by
  obtain ⟨htG, hm1, hk1, hk2, hs0, hs2, -⟩ := hS
  rw [(hM a H hH).2.2.2.1]
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hf := frobH_nonneg H
  have ha := nsq_nonneg a
  have hq0 : 0 ≤ 3 / (4 * ((n : ℝ) + 2)) := by positivity
  have hq : 3 / (4 * ((n : ℝ) + 2)) ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hq' : 3 / (2 * ((n : ℝ) + 2)) = 2 * (3 / (4 * ((n : ℝ) + 2))) := by field_simp; ring
  have ht : tG n ≤ 1502 / 1000 := by rw [htG, hq']; linarith
  have ht0 : 3 / 2 ≤ tG n := by rw [htG, hq']; linarith
  have ht2 : tG n ^ 2 ≤ 2257 / 1000 := by nlinarith
  have hm0 : 0 ≤ mm1 n := by rw [hm1]; positivity
  have hnq : (n : ℝ) * (3 / (4 * ((n : ℝ) + 2))) ≤ 3 / 4 := by
    have : (n : ℝ) * (3 / (4 * ((n : ℝ) + 2))) = 3 * n / (4 * ((n : ℝ) + 2)) := by ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e2 := trH_sq_le H
  have hC0 : 0 ≤ kk2 n - tG n ^ 2 := by linarith
  have hC1 : kk2 n - tG n ^ 2 ≤ 3 / (4 * ((n : ℝ) + 2)) := by linarith
  have e3 : trH H ^ 2 * (kk2 n - tG n ^ 2) ≤ (n * frobH H) * (3 / (4 * ((n : ℝ) + 2))) :=
    mul_le_mul e2 hC1 hC0 (mul_nonneg hnpos.le hf)
  have e4 : (n * frobH H) * (3 / (4 * ((n : ℝ) + 2))) ≤ 3 / 4 * frobH H := by
    have : (n * frobH H) * (3 / (4 * ((n : ℝ) + 2))) =
        ((n : ℝ) * (3 / (4 * ((n : ℝ) + 2)))) * frobH H := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hnq hf
  have e5 : (tG n - mm1 n) * nsq a ≤ 151 / 100 * nsq a :=
    mul_le_mul_of_nonneg_right (by linarith) ha
  have e6 : 2 * frobH H * (kk2 n - ss2 n) ≤ 2 * frobH H * (2258 / 1000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

lemma varBoundW_of {cP : ℝ} (hn : 1000 ≤ n) {S2 : ℝ} (hS : SphereConsts n S2) (hS2 : S2 ≤ 5)
    (hM : MeanIds n) (hV : VarBound n cP) (hcP : 0 ≤ cP) : VarBoundW n (cP * (800 / 449)) := by
  intro a H hH
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfl := floor_le hn hS hS2 hM a H hH
  have hm0 : 0 ≤ ∫ W, VG a H W ∂stdGauss (WIdx n) := le_trans (Wf_nonneg a H) hfl
  refine (hV a H hH).trans ?_
  have hA8 : nsq a + 8 * frobH H ≤ 800 / 449 * Wf a H := by
    unfold Wf; nlinarith [nsq_nonneg a, frobH_nonneg H]
  have hc : 0 ≤ cP / (n : ℝ) := div_nonneg hcP hnpos.le
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA8 hc) hm0
  refine h1.trans (le_of_eq ?_)
  ring

lemma cheb_floor (hn : 1000 ≤ n) {S2 cW κ : ℝ} (hS : SphereConsts n S2) (hS2 : S2 ≤ 5)
    (hM : MeanIds n) (hV : VarBoundW n cW) (hcW : 0 ≤ cW) (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < Wf a H) :
    stdGauss (WIdx n) {W | VG a H W < κ * Wf a H} ≤
      ENNReal.ofReal (cW / (n * (1 - κ) ^ 2)) := by
  set m := ∫ W, VG a H W ∂stdGauss (WIdx n) with hm
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hfl : Wf a H ≤ m := floor_le hn hS hS2 hM a H hH
  have hmpos : 0 < m := lt_of_lt_of_le hpos hfl
  obtain ⟨hi1, hi2, -, -, -⟩ := hM a H hH
  have hint : Integrable (fun W => (VG a H W - m) ^ 2) (stdGauss (WIdx n)) := by
    have : (fun W => (VG a H W - m) ^ 2) = fun W => VG a H W ^ 2 - 2 * m * VG a H W + m ^ 2 := by
      funext W; ring
    rw [this]; exact (hi2.sub (hi1.const_mul _)).add (integrable_const _)
  have hvar := hV a H hH
  have hB : ∫ W, (VG a H W - m) ^ 2 ∂stdGauss (WIdx n) ≤ cW / n * m * m := by
    refine hvar.trans ?_
    have hc : 0 ≤ cW / (n : ℝ) := div_nonneg hcW hnpos.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfl hc) hmpos.le
  have h1κ : 0 < 1 - κ := by linarith
  have ht : 0 < ((1 - κ) * m) ^ 2 := by positivity
  have hmk := markov_gt (μ := stdGauss (WIdx n)) (fun W => sq_nonneg (VG a H W - m)) hint ht hB
  have hsub : {W | VG a H W < κ * Wf a H} ⊆ {W | ((1 - κ) * m) ^ 2 < (VG a H W - m) ^ 2} := by
    intro W hW
    simp only [Set.mem_ofPred_eq] at hW ⊢
    have h2 : VG a H W < κ * m := lt_of_lt_of_le hW (mul_le_mul_of_nonneg_left hfl hκ0)
    have h3 : (1 - κ) * m < m - VG a H W := by linarith
    have h4 : 0 < (1 - κ) * m := by positivity
    nlinarith
  refine (measure_mono hsub).trans (hmk.trans (le_of_eq ?_))
  congr 1
  field_simp

lemma markov_err (hn : 1000 ≤ n) {S2 c1 T : ℝ} (hS : SphereConsts n S2) (hM : MeanIds n)
    (hc1 : 2 / 3 ≤ c1) (hc1' : 2 * S2 + 9 / 4 ≤ 449 / 100 * c1) (hT : 0 < T)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < Wf a H) :
    stdGauss (WIdx n) {W | T * Wf a H < errG a H W ^ 2} ≤ ENNReal.ofReal (c1 / (n * T)) := by
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨-, -, hi3, -, -⟩ := hM a H hH
  have hB : ∫ W, errG a H W ^ 2 ∂stdGauss (WIdx n) ≤ c1 * Wf a H / n := by
    refine (err_le hn hS hM a H hH).trans ?_
    apply div_le_div_of_nonneg_right _ hnpos.le
    unfold Wf
    nlinarith [nsq_nonneg a, frobH_nonneg H]
  have hmk := markov_gt (μ := stdGauss (WIdx n)) (fun W => sq_nonneg (errG a H W)) hi3
    (mul_pos hT hpos) hB
  refine hmk.trans (le_of_eq ?_)
  congr 1
  field_simp

/-- **The Gaussian-model theorem, given the constant column** (for every `a = ℓ + 2Hu`):
failure `≤ c₁/(n ε² κ) + c_V/(n (1−κ)²)`, with `c_V = cW` and `κ = 1 − θ`. -/
theorem gauss_model (hn : 1000 ≤ n) {S2 cW c1 κ ε : ℝ} (hS : SphereConsts n S2) (hS2 : S2 ≤ 5)
    (hM : MeanIds n) (hV : VarBoundW n cW) (hcW : 0 ≤ cW)
    (hc1 : 2 / 3 ≤ c1) (hc1' : 2 * S2 + 9 / 4 ≤ 449 / 100 * c1)
    (hκ0 : 0 < κ) (hκ : κ < 1) (hε : 0 < ε)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hpos : 0 < frobH H) :
    stdGauss (WIdx n) {W | ε ^ 2 * VG a H W < errG a H W ^ 2} ≤
      ENNReal.ofReal (c1 / (n * (ε ^ 2 * κ)) + cW / (n * (1 - κ) ^ 2)) := by
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hW : 0 < Wf a H := by unfold Wf; nlinarith [nsq_nonneg a]
  have h1 := cheb_floor hn hS hS2 hM hV hcW hκ0.le hκ a H hH hW
  have h2 := markov_err hn (T := ε ^ 2 * κ) hS hM hc1 hc1' (by positivity) a H hH hW
  have hsub : {W | ε ^ 2 * VG a H W < errG a H W ^ 2} ⊆
      {W | ε ^ 2 * κ * Wf a H < errG a H W ^ 2} ∪ {W | VG a H W < κ * Wf a H} := by
    intro W hW'
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hW' ⊢
    by_cases h : VG a H W < κ * Wf a H
    · exact Or.inr h
    · left
      have : ε ^ 2 * (κ * Wf a H) ≤ ε ^ 2 * VG a H W :=
        mul_le_mul_of_nonneg_left (not_lt.mp h) (by positivity)
      linarith
  have hc10 : 0 ≤ c1 := by linarith
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h2 h1))

end BstLean.Part78

#print axioms BstLean.Part78.gauss_model
