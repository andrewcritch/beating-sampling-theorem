import BstLean.Part53T2_Tensor
import BstLean.Part53T2_Comparison

namespace BstLean.Part53.T2Aux

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Tens IsSymmT frob contr Mono)

variable {n d : ℕ}

noncomputable def singleFamily (j : ℕ) (U : (Fin j → Fin n) → ℝ) : Tens n :=
  fun c w => if h : c = j then U (fun t => w ⟨t.1, by omega⟩) else 0

private lemma singleFamily_at (j : ℕ) (U : (Fin j → Fin n) → ℝ) :
    singleFamily j U j = U := by
  funext w
  simp [singleFamily]

private lemma singleFamily_off (j c : ℕ) (U : (Fin j → Fin n) → ℝ) (h : c ≠ j) :
    singleFamily j U c = 0 := by
  funext w
  simp [singleFamily, h]

private lemma singleFamily_symm (j : ℕ) (U : (Fin j → Fin n) → ℝ)
    (hU : IsSymmT U) : ∀ c, IsSymmT (singleFamily j U c) := by
  intro c
  by_cases hc : c = j
  · subst c
    rw [singleFamily_at]
    exact hU
  · rw [singleFamily_off j c U hc]
    intro σ w
    rfl

private lemma singleFamily_eval (k j : ℕ) (hj : j ≤ k)
    (U : (Fin j → Fin n) → ℝ) (y : Fin n → ℝ) :
    fvA k (singleFamily j U) y = contr U (fun _ => y) := by
  classical
  unfold fvA
  rw [Finset.sum_eq_single j]
  · rw [singleFamily_at]
  · intro c _ hc
    rw [singleFamily_off j c U hc]
    simp [contr]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

private lemma singleFamily_frob (j c : ℕ) (U : (Fin j → Fin n) → ℝ) :
    frob (singleFamily j U c) = if c = j then frob U else 0 := by
  by_cases hc : c = j
  · subst c
    simp [singleFamily_at]
  · rw [singleFamily_off j c U hc, if_neg hc]
    simp [frob]

private lemma heatWeight_scale (v : ℝ) (c i : ℕ) :
    heatWeight v c i = v ^ i * heatWeight 1 c i := by
  unfold heatWeight
  rw [show v / 2 = v * (1 / 2) by ring, mul_pow]
  ring

private noncomputable def momentBudget (k : ℕ) (L : ℝ) : ℝ :=
  ∑ c ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
    (c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)

private lemma momentBudget_nonneg (k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    0 ≤ momentBudget k L := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- A raw homogeneous tensor has the Gaussian second-moment bound needed by the radial proof. -/
lemma raw_gaussian_moment (k : ℕ) (hW : LemmaW53 k) (hTr : LemmaTr53)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d j : ℕ), 1 ≤ n → j ≤ k →
      ∀ (U : (Fin j → Fin n) → ℝ), IsSymmT U →
      ∀ (ψ : Mono n d → ℝ), nsq ψ ≤ L →
      Integrable (fun Z => contr U (fun _ => linZ Z ψ) ^ 2) (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, contr U (fun _ => linZ Z ψ) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤
        C * (n : ℝ) ^ (j / 2) * frob U := by
  classical
  refine ⟨(k + 1 : ℕ) * momentBudget k L, by
    exact mul_nonneg (Nat.cast_nonneg _) (momentBudget_nonneg k L hL), ?_⟩
  intro n d j hn hj U hU ψ hψ
  let A := singleFamily j U
  let u := nsq ψ
  have hu : 0 ≤ u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hi, he⟩ := hW n d 1 A A (singleFamily_symm j U hU)
    (singleFamily_symm j U hU) ψ ψ
  have hself : (fun Z => fvA k A ((1 : ℝ) • linZ Z ψ) * fvA k A ((1 : ℝ) • linZ Z ψ)) =
      fun Z => contr U (fun _ => linZ Z ψ) ^ 2 := by
    funext Z
    simp only [one_smul, A, singleFamily_eval k j hj, pow_two]
  have hi' : Integrable (fun Z => contr U (fun _ => linZ Z ψ) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
    exact hself ▸ hi
  have he' : (∫ Z, contr U (fun _ => linZ Z ψ) ^ 2 ∂stdGauss (CoefIdxD n d)) =
      wpair k 1 A A ψ ψ := by
    calc
      _ = ∫ Z, fvA k A ((1 : ℝ) • linZ Z ψ) * fvA k A ((1 : ℝ) • linZ Z ψ)
          ∂stdGauss (CoefIdxD n d) := congrArg (fun f => ∫ Z, f Z ∂stdGauss (CoefIdxD n d)) hself.symm
      _ = _ := he
  refine ⟨hi', ?_⟩
  rw [he']
  have hup : ∑ p, ψ p * ψ p = u := by simp [u, nsq, pow_two]
  have hinner (c : ℕ) : tinner (heatA k u A c) (heatA k u A c) =
      frob (heatA k u A c) := by simp [tinner, frob, pow_two]
  simp only [wpair, one_pow, mul_one, one_mul]
  rw [show nsq ψ = u from rfl]
  simp_rw [hup]
  simp_rw [hinner]
  let F := (n : ℝ) ^ (j / 2) * frob U
  have hF : 0 ≤ F := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hterm (c i : ℕ) :
      (c.factorial : ℝ) * u ^ c *
        (heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i))) ≤
      ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F := by
    by_cases hij : c + 2 * i = j
    · rw [show frob (A (c + 2 * i)) = frob U by simp [A, singleFamily_frob, hij],
        heatWeight_scale, mul_pow]
      have hiJ : i ≤ j / 2 := by omega
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hp := pow_le_pow_right₀ hnR hiJ
      have huL := pow_le_pow_left₀ hu hψ (c + 2 * i)
      calc
        _ = ((c.factorial : ℝ) * heatWeight 1 c i ^ 2) *
            u ^ (c + 2 * i) * ((n : ℝ) ^ i * frob U) := by
          rw [pow_add, pow_mul]
          ring
        _ ≤ ((c.factorial : ℝ) * heatWeight 1 c i ^ 2) *
            L ^ (c + 2 * i) * F := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left huL (by positivity)
          · exact mul_le_mul_of_nonneg_right hp
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          · exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          · positivity
    · simp only [A, singleFamily_frob, if_neg hij, mul_zero]
      positivity
  have hsum (c : ℕ) :
      (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        (c.factorial : ℝ) * u ^ c *
          (heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i)))) ≤
      ∑ i ∈ Finset.range (k + 1),
        ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F := by
    have hs : (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F) ≤
        ∑ i ∈ Finset.range (k + 1),
          ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    exact (Finset.sum_le_sum (fun i _ => hterm c i)).trans hs
  calc
    _ ≤ ∑ c ∈ Finset.range (k + 1), (c.factorial : ℝ) * u ^ c *
        ((k + 1 : ℕ) * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
          heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i))) := by
      apply Finset.sum_le_sum
      intro c _
      have hb := frob_heatA_bound k c u A hTr
      calc
        _ = ((c.factorial : ℝ) * u ^ c) * frob (heatA k u A c) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hb
          (show 0 ≤ (c.factorial : ℝ) * u ^ c by positivity)
    _ = (k + 1 : ℕ) * ∑ c ∈ Finset.range (k + 1),
        ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
          (c.factorial : ℝ) * u ^ c *
            (heatWeight u c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (k + 1 : ℕ) * ∑ c ∈ Finset.range (k + 1),
        ∑ i ∈ Finset.range (k + 1),
          ((c.factorial : ℝ) * heatWeight 1 c i ^ 2 * L ^ (c + 2 * i)) * F :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hsum c)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [← Finset.sum_mul, momentBudget, F]
      ring

end BstLean.Part53.T2Aux
