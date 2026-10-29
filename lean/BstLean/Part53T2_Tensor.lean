import BstLean.Part53Defs
import BstLean.Part36Index

namespace BstLean.Part53.T2Aux

open MeasureTheory
open BstLean.Part36 (DD)
open BstLean.Part41 (Tens frob trL)
variable {n d : ℕ}

noncomputable def heatWeight (v : ℝ) (c i : ℕ) : ℝ :=
  (v / 2) ^ i / (i.factorial : ℝ) *
    (((c + 2 * i).factorial : ℝ) / (c.factorial : ℝ))

noncomputable def traceAt (A : Tens n) (c i : ℕ) : (Fin c → Fin n) → ℝ :=
  fun w => trL i (A (c + 2 * i)) (fun t => w ⟨t.1, by have := t.2; omega⟩)

private noncomputable def heatTail (k : ℕ) (v : ℝ) (A : Tens n) (c : ℕ) :
    (Fin c → Fin n) → ℝ := fun w =>
  ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
    heatWeight v c i * traceAt A c i w

lemma traceAt_frob (A : Tens n) (c i : ℕ) :
    frob (traceAt A c i) = frob (trL i (A (c + 2 * i))) := by
  classical
  let e : (Fin c → Fin n) ≃ (Fin (c + 2 * i - 2 * i) → Fin n) :=
    { toFun := fun w t => w ⟨t.1, by have := t.2; omega⟩
      invFun := fun w t => w ⟨t.1, by have := t.2; omega⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }
  exact e.sum_comp (fun w => (trL i (A (c + 2 * i)) w) ^ 2)

private lemma heatA_split (k c : ℕ) (hc : c ≤ k) (v : ℝ) (A : Tens n) :
    heatA k v A c = fun w => A c w + heatTail k v A c w := by
  classical
  funext w
  have h0 : 0 ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k) := by simp [hc]
  have hsum := Finset.sum_erase_add
    ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k))
    (fun i => heatWeight v c i * traceAt A c i w) h0
  have hz : heatWeight v c 0 * traceAt A c 0 w = A c w := by
    simp only [heatWeight, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      Nat.mul_zero, Nat.add_zero, div_self (by positivity : (c.factorial : ℝ) ≠ 0),
      one_mul, traceAt, trL, Fintype.sum_unique]
    congr 1
  change (∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
    heatWeight v c i * traceAt A c i w) = _
  rw [← hsum, hz]
  exact add_comm _ _

private lemma frob_add_sub_bound {c : ℕ} (A B : (Fin c → Fin n) → ℝ) :
    frob A ≤ 2 * frob (fun w => A w + B w) + 2 * frob B := by
  classical
  unfold frob
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w hw
  nlinarith [sq_nonneg (A w + 2 * B w)]

private lemma heatTail_frob (k c : ℕ) (v : ℝ) (A : Tens n) (hTr : LemmaTr53) :
    frob (heatTail k v A c) ≤ (k + 1 : ℕ) *
      ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
        (heatWeight v c i) ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i)) := by
  classical
  let S := ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0
  have hcard : S.card ≤ k + 1 := by
    exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
      ((Finset.card_filter_le _ _).trans_eq (Finset.card_range _))
  calc
    _ ≤ ∑ w : Fin c → Fin n, (k + 1 : ℕ) *
        ∑ i ∈ S, (heatWeight v c i * traceAt A c i w) ^ 2 := by
      unfold frob heatTail
      apply Finset.sum_le_sum
      intro w hw
      calc
        _ ≤ (S.card : ℝ) * ∑ i ∈ S, (heatWeight v c i * traceAt A c i w) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (Finset.sum_nonneg fun i hi => sq_nonneg _)
    _ = (k + 1 : ℕ) * ∑ i ∈ S, (heatWeight v c i) ^ 2 * frob (traceAt A c i) := by
      simp only [frob, mul_pow, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      rw [traceAt_frob]
      have ht := hTr n (c + 2 * i) i (A (c + 2 * i)) (by omega)
      exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (by ring)

private lemma heatWeight_div (v D : ℝ) (_hD : D ≠ 0) (c i : ℕ) :
    heatWeight (v / D) c i = heatWeight v c i / D ^ i := by
  unfold heatWeight
  rw [show v / D / 2 = (v / 2) / D by ring, div_pow]
  ring

/-- The raw coefficient recurrence, before the induction over tensor order. -/
lemma raw_coefficient_step (n d k c : ℕ) (hn : 1 ≤ n) (hc : 1 ≤ c)
    (hck : c ≤ k) (f0 : ℝ) (T : Tens n) (hTr : LemmaTr53) :
    frob (T c) / DD n d ^ c ≤ 2 * Ncirc n d k f0 T +
      2 * (k + 1 : ℕ) *
        ∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
          (heatWeight (c0 d) c i) ^ 2 * (n : ℝ) ^ i *
            (frob (T (c + 2 * i)) / DD n d ^ (c + 2 * i)) := by
  classical
  let A := TF k f0 T
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have hAc : A c = T c := by funext w; simp [A, TF, show c ≠ 0 by omega, hck]
  have hbound := frob_add_sub_bound (A c) (heatTail k (c0 d / DD n d) A c)
  rw [← heatA_split k c hck] at hbound
  have htail := heatTail_frob k c (c0 d / DD n d) A hTr
  have hcircle : frob (heatA k (c0 d / DD n d) A c) / DD n d ^ c ≤
      Ncirc n d k f0 T := by
    exact Finset.single_le_sum
      (f := fun j => frob (Tcirc n d k f0 T j) / DD n d ^ j)
      (fun j hj => div_nonneg (Finset.sum_nonneg fun w hw => sq_nonneg _)
        (pow_nonneg hD.le j)) (Finset.mem_Icc.mpr ⟨hc, hck⟩)
  rw [hAc] at hbound
  calc
    _ ≤ (2 * frob (heatA k (c0 d / DD n d) A c) +
        2 * frob (heatTail k (c0 d / DD n d) A c)) / DD n d ^ c :=
      div_le_div_of_nonneg_right hbound (pow_nonneg hD.le c)
    _ ≤ 2 * Ncirc n d k f0 T + 2 *
        (frob (heatTail k (c0 d / DD n d) A c) / DD n d ^ c) := by
      rw [add_div, mul_div_assoc, mul_div_assoc]
      linarith
    _ ≤ 2 * Ncirc n d k f0 T + 2 *
        (((k + 1 : ℕ) * ∑ i ∈ ((Finset.range (k + 1)).filter
          (fun i => c + 2 * i ≤ k)).erase 0,
          (heatWeight (c0 d / DD n d) c i) ^ 2 * (n : ℝ) ^ i *
            frob (A (c + 2 * i))) / DD n d ^ c) := by
      gcongr
    _ = _ := by
      rw [mul_div_assoc, Finset.sum_div, mul_assoc]
      congr 2
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hci := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hi)).2
      have hAi : A (c + 2 * i) = T (c + 2 * i) := by
        funext w
        simp only [A, TF, if_neg (by omega : c + 2 * i ≠ 0), if_pos hci]
      rw [hAi, heatWeight_div _ _ hD.ne', div_pow, pow_add, pow_mul]
      ring


private noncomputable def weightBudget (d k : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (k + 1),
    heatWeight (c0 d) c i ^ 2

private lemma weightBudget_nonneg (d k : ℕ) : 0 ≤ weightBudget d k := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma frob_heatA_bound (k c : ℕ) (v : ℝ) (A : Tens n) (hTr : LemmaTr53) :
    frob (heatA k v A c) ≤ (k + 1 : ℕ) *
      ∑ i ∈ (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k),
        heatWeight v c i ^ 2 * (n : ℝ) ^ i * frob (A (c + 2 * i)) := by
  classical
  let S := (Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)
  have hcard : S.card ≤ k + 1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  calc
    _ ≤ ∑ w : Fin c → Fin n, (k + 1 : ℕ) *
        ∑ i ∈ S, (heatWeight v c i * traceAt A c i w) ^ 2 := by
      unfold frob heatA
      apply Finset.sum_le_sum
      intro w _
      calc
        _ ≤ (S.card : ℝ) * ∑ i ∈ S, (heatWeight v c i * traceAt A c i w) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = (k + 1 : ℕ) * ∑ i ∈ S, heatWeight v c i ^ 2 * frob (traceAt A c i) := by
      simp only [frob, mul_pow, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      rw [traceAt_frob]
      have ht := hTr n (c + 2 * i) i (A (c + 2 * i)) (by omega)
      exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (by ring)

private lemma weightBudget_row (d k c : ℕ) (hc : c ≤ k) :
    (∑ i ∈ ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0,
      heatWeight (c0 d) c i ^ 2) ≤ weightBudget d k := by
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _))
    (fun _ _ _ => sq_nonneg _))
  exact Finset.single_le_sum
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.mem_range.mpr (by omega))

private lemma Ncirc_nonneg (n d k : ℕ) (f0 : ℝ) (T : Tens n) :
    0 ≤ Ncirc n d k f0 T := by
  unfold Ncirc
  exact Finset.sum_nonneg fun _ _ => div_nonneg
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (pow_nonneg (Nat.cast_nonneg _) _)

/-- A triangular estimate replaces the explicit inverse of the heat semigroup. -/
lemma raw_tensor_bound (d k : ℕ) (hTr : LemmaTr53) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (f0 : ℝ) (T : Tens n)
      (c : ℕ), 1 ≤ c → c ≤ k →
      frob (T c) / DD n d ^ c ≤
        C * (n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T := by
  classical
  have aux : ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (f0 : ℝ) (T : Tens n) (c : ℕ), 1 ≤ c → c ≤ k → k - c ≤ r →
      frob (T c) / DD n d ^ c ≤
        C * (n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T := by
    intro r
    induction r with
    | zero =>
        refine ⟨2, by norm_num, fun n hn f0 T c hc hck hr => ?_⟩
        have he : c = k := by omega
        subst c
        have hb := raw_coefficient_step n d k k hn hc le_rfl f0 T hTr
        have hs : ((Finset.range (k + 1)).filter (fun i => k + 2 * i ≤ k)).erase 0 = ∅ := by
          ext i
          simp
        simpa [hs] using hb
    | succ r ih =>
        obtain ⟨C, hC, hb⟩ := ih
        let H := weightBudget d k
        let C' := C + 2 + 2 * (k + 1 : ℕ) * H * C
        have hH : 0 ≤ H := weightBudget_nonneg d k
        have hCC : C ≤ C' := by
          dsimp [C']
          have hx : 0 ≤ 2 * (k + 1 : ℕ) * H * C := by positivity
          linarith
        refine ⟨C', by dsimp [C']; positivity, fun n hn f0 T c hc hck hr => ?_⟩
        have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have hN := Ncirc_nonneg n d k f0 T
        have hp : 1 ≤ (n : ℝ) ^ ((k - c) / 2) := one_le_pow₀ hnR
        by_cases hold : k - c ≤ r
        · exact (hb n hn f0 T c hc hck hold).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCC (by positivity)) hN)
        · let S := ((Finset.range (k + 1)).filter (fun i => c + 2 * i ≤ k)).erase 0
          have hs : (∑ i ∈ S, heatWeight (c0 d) c i ^ 2 * (n : ℝ) ^ i *
              (frob (T (c + 2 * i)) / DD n d ^ (c + 2 * i))) ≤
              H * (C * (n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T) := by
            calc
              _ ≤ ∑ i ∈ S, heatWeight (c0 d) c i ^ 2 *
                  (C * (n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T) := by
                apply Finset.sum_le_sum
                intro i hi
                have hi0 := (Finset.mem_erase.mp hi).1
                have hci := (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
                have hir : k - (c + 2 * i) ≤ r := by omega
                have hraw := hb n hn f0 T (c + 2 * i) (by omega) hci hir
                have he : i + (k - (c + 2 * i)) / 2 = (k - c) / 2 := by omega
                calc
                  _ ≤ heatWeight (c0 d) c i ^ 2 * (n : ℝ) ^ i *
                      (C * (n : ℝ) ^ ((k - (c + 2 * i)) / 2) * Ncirc n d k f0 T) :=
                    mul_le_mul_of_nonneg_left hraw (by positivity)
                  _ = _ := by
                    rw [show heatWeight (c0 d) c i ^ 2 * (n : ℝ) ^ i *
                        (C * (n : ℝ) ^ ((k - (c + 2 * i)) / 2) * Ncirc n d k f0 T) =
                        heatWeight (c0 d) c i ^ 2 * C *
                          ((n : ℝ) ^ i * (n : ℝ) ^ ((k - (c + 2 * i)) / 2)) *
                          Ncirc n d k f0 T by ring, ← pow_add, he]
                    ring
              _ = (∑ i ∈ S, heatWeight (c0 d) c i ^ 2) *
                  (C * (n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T) :=
                (Finset.sum_mul _ _ _).symm
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (weightBudget_row d k c hck) (by positivity)
          have hstep := raw_coefficient_step n d k c hn hc hck f0 T hTr
          calc
            _ ≤ 2 * Ncirc n d k f0 T + 2 * (k + 1 : ℕ) *
                (H * (C * (n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T)) :=
              hstep.trans (add_le_add le_rfl
                (mul_le_mul_of_nonneg_left hs
                  (show (0 : ℝ) ≤ 2 * (k + 1 : ℕ) by positivity)))
            _ ≤ (2 + 2 * (k + 1 : ℕ) * H * C) *
                ((n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T) := by
              have he := mul_le_mul_of_nonneg_right hp hN
              nlinarith only [he]
            _ ≤ C' * ((n : ℝ) ^ ((k - c) / 2) * Ncirc n d k f0 T) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              dsimp [C']
              linarith
            _ = _ := by ring
  obtain ⟨C, hC, hb⟩ := aux k
  exact ⟨C, hC, fun n hn f0 T c hc hck => hb n hn f0 T c hc hck (by omega)⟩

end BstLean.Part53.T2Aux
