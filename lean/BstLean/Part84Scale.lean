import BstLean.Part84Defs
import BstLean.Part53Floor_Heat
import BstLean.Part53Elem

/-!
# Part 84, `Scale`: the scale comparison on tensor families

`scaleIface : ScaleIface n K`. With `B = P_s A` and `δ = s' − s`, `P_{s'} A = P_δ B` (semigroup).
A weighted Cauchy–Schwarz inequality over the trace index `i`, with `‖tr^i T‖² ≤ n^i ‖T‖²`,
gives both bounds. The symmetry hypothesis is not used.
-/

namespace BstLean.Part84

open BstLean.Part41 (trL frob IsSymmT Tens)
open BstLean.Part53 (heatA LemmaTr53 lemmaTr53)
open BstLean.Part53.FloorHeat (heatWeight traceFamily traceFamily_frob heatA_shift heatA_correction)

variable {n : ℕ}

private lemma frob_nn {c : ℕ} (X : (Fin c → Fin n) → ℝ) : 0 ≤ frob X :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Weighted Cauchy–Schwarz. -/
private lemma wcs {ι : Type*} (S : Finset ι) (a x μ : ι → ℝ) (hμ : ∀ i ∈ S, 0 < μ i) :
    (∑ i ∈ S, a i * x i) ^ 2 ≤ (∑ i ∈ S, μ i) * ∑ i ∈ S, a i ^ 2 / μ i * x i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi; exact (hμ i hi).le
  · intro i hi; have := hμ i hi; positivity
  · intro i hi; have := (hμ i hi).ne'; apply le_of_eq; field_simp

private lemma heat_frob_le (c : ℕ) (v : ℝ) (B : Tens n) (S : Finset ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ i ∈ S, 0 < μ i) :
    frob (fun w : Fin c → Fin n => ∑ i ∈ S, heatWeight c i v * traceFamily i B c w) ≤
      (∑ i ∈ S, μ i) *
        ∑ i ∈ S, heatWeight c i v ^ 2 / μ i * ((n : ℝ) ^ i * frob (B (c + 2 * i))) := by
  have hμs : 0 ≤ ∑ i ∈ S, μ i := Finset.sum_nonneg (fun i hi => (hμ i hi).le)
  calc frob (fun w : Fin c → Fin n => ∑ i ∈ S, heatWeight c i v * traceFamily i B c w)
      ≤ ∑ w : Fin c → Fin n, (∑ i ∈ S, μ i) *
          ∑ i ∈ S, heatWeight c i v ^ 2 / μ i * traceFamily i B c w ^ 2 :=
        Finset.sum_le_sum (fun w _ => wcs S _ _ μ hμ)
    _ = (∑ i ∈ S, μ i) * ∑ i ∈ S, heatWeight c i v ^ 2 / μ i * frob (traceFamily i B c) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        rfl
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hμs
        apply Finset.sum_le_sum
        intro i hi
        rw [traceFamily_frob]
        have hh := lemmaTr53 n (c + 2 * i) i (B (c + 2 * i)) (by omega)
        exact mul_le_mul_of_nonneg_left hh (by have := hμ i hi; positivity)

private lemma geo (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (S : Finset ℕ) (hS : S ⊆ Finset.range (m + 1)) :
    ∑ i ∈ S, y ^ i ≤ (1 + y) ^ m := by
  calc ∑ i ∈ S, y ^ i ≤ ∑ i ∈ Finset.range (m + 1), y ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ ≤ ∑ i ∈ Finset.range (m + 1), y ^ i * 1 ^ (m - i) * (m.choose i) := by
        apply Finset.sum_le_sum; intro i hi
        have h1 : (1 : ℝ) ≤ m.choose i := by
          exact_mod_cast Nat.choose_pos (by have := Finset.mem_range.mp hi; omega)
        rw [one_pow, mul_one]
        exact le_mul_of_one_le_right (pow_nonneg hy i) h1
    _ = (1 + y) ^ m := by rw [add_comm 1 y, add_pow]

private lemma geo1 (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 m) :
    ∑ i ∈ S, y ^ i ≤ y * (1 + y) ^ m := by
  have hS' : S ⊆ Finset.Ico 1 (m + 1) := by
    intro i hi; have := Finset.mem_Icc.mp (hS hi); simp only [Finset.mem_Ico]; omega
  calc ∑ i ∈ S, y ^ i ≤ ∑ i ∈ Finset.Ico 1 (m + 1), y ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hS' (fun _ _ _ => by positivity)
    _ = y * ∑ j ∈ Finset.range m, y ^ j := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        simp [pow_add]
    _ ≤ y * (1 + y) ^ m :=
        mul_le_mul_of_nonneg_left
          (geo m y hy _ (Finset.range_subset_range.mpr (Nat.le_succ m))) hy

private lemma sum_inj_le (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j) (T U : Finset ℕ) (g : ℕ → ℕ)
    (hg : ∀ x ∈ T, ∀ y ∈ T, g x = g y → x = y) (hm : ∀ c ∈ T, g c ∈ U) :
    ∑ c ∈ T, β (g c) ≤ ∑ j ∈ U, β j := by
  rw [← Finset.sum_image hg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hβ _)
  intro j hj
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hj
  exact hm c hc

private lemma fact_le (c m : ℕ) : (c + m).factorial ≤ c.factorial * (c + m) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (c + m) ^ m ≤ (c + (m + 1)) ^ m := Nat.pow_le_pow_left (by omega) m
    calc (c + (m + 1)).factorial = (c + m + 1) * (c + m).factorial := Nat.factorial_succ _
      _ ≤ (c + m + 1) * (c.factorial * (c + (m + 1)) ^ m) :=
        Nat.mul_le_mul_left _ (ih.trans (Nat.mul_le_mul_left _ h1))
      _ = c.factorial * (c + (m + 1)) ^ (m + 1) := by rw [pow_succ]; ring

private lemma tsq (δ s0 : ℝ) (n : ℕ) :
    (|δ| * Real.sqrt n / s0) ^ 2 = δ ^ 2 * n / s0 ^ 2 := by
  rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- The coefficient bound for the mean. -/
private lemma coef_mean (i : ℕ) (δ s s0 : ℝ) (n : ℕ) (hs0 : 0 < s0) (hs : s0 ≤ s) :
    heatWeight 0 i δ ^ 2 * (n : ℝ) ^ i ≤
      (|δ| * Real.sqrt n / s0) ^ (2 * i) * (((0 + 2 * i).factorial : ℝ) * s ^ (0 + 2 * i)) := by
  have hs1 : 0 < s := hs0.trans_le hs
  have hI : (0 : ℝ) < (i.factorial : ℝ) := by positivity
  have hF : (0 : ℝ) < ((2 * i).factorial : ℝ) := by positivity
  have hnat : (2 * i).factorial ≤ 4 ^ i * (i.factorial * i.factorial) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show i ≤ 2 * i by omega)
    have h2 : (2 * i).choose i ≤ 2 ^ (2 * i) := Nat.choose_le_two_pow _ _
    have h3 : 2 * i - i = i := by omega
    rw [h3] at h1
    rw [← h1, mul_assoc, show (4 : ℕ) ^ i = 2 ^ (2 * i) by rw [pow_mul]; norm_num]
    exact Nat.mul_le_mul_right _ h2
  have hreal : ((2 * i).factorial : ℝ) ≤ 4 ^ i * ((i.factorial : ℝ) * i.factorial) := by
    exact_mod_cast hnat
  have hq : ((2 * i).factorial : ℝ) / (4 ^ i * ((i.factorial : ℝ) * i.factorial)) ≤ 1 :=
    (div_le_one (by positivity)).mpr hreal
  have hr : (1 : ℝ) ≤ ((s / s0) ^ 2) ^ i :=
    one_le_pow₀ (one_le_pow₀ ((one_le_div hs0).mpr hs))
  have hX : (0 : ℝ) ≤ (δ ^ 2 * n) ^ i * ((2 * i).factorial : ℝ) := by positivity
  have hL : heatWeight 0 i δ ^ 2 * (n : ℝ) ^ i =
      (δ ^ 2 * n) ^ i * ((2 * i).factorial : ℝ) *
        (((2 * i).factorial : ℝ) / (4 ^ i * ((i.factorial : ℝ) * i.factorial))) := by
    have e4 : (δ ^ 2 * n) ^ i = ((δ / 2) ^ i) ^ 2 * 4 ^ i * (n : ℝ) ^ i := by
      rw [← pow_mul, mul_comm i 2, pow_mul, ← mul_pow, ← mul_pow]; congr 1; ring
    have hQ : (4 : ℝ) ^ i ≠ 0 := by positivity
    unfold heatWeight
    simp only [zero_add, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [e4]
    generalize (δ / 2) ^ i = P
    generalize (4 : ℝ) ^ i = Q at hQ ⊢
    field_simp
  have hR : (|δ| * Real.sqrt n / s0) ^ (2 * i) *
      (((0 + 2 * i).factorial : ℝ) * s ^ (0 + 2 * i)) =
      (δ ^ 2 * n) ^ i * ((2 * i).factorial : ℝ) * ((s / s0) ^ 2) ^ i := by
    rw [pow_mul, tsq, zero_add, div_pow (δ ^ 2 * n), div_pow s s0, div_pow, pow_mul s 2 i]
    field_simp
  rw [hL, hR]
  calc _ ≤ (δ ^ 2 * n) ^ i * ((2 * i).factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left hq hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hr hX

/-- The coefficient bound for the energy. -/
private lemma coef_en (K c i : ℕ) (hci : c + 2 * i ≤ K) (s s' s0 : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hs0 : 0 < s0) (hs : s0 ≤ s) (hs' : s0 ≤ s') :
    (c.factorial : ℝ) * s' ^ c * heatWeight c i (s' - s) ^ 2 * (n : ℝ) ^ i ≤
      (1 + |s' - s| * Real.sqrt n / s0) ^ K *
        ((K * (|s' - s| * Real.sqrt n / s0) / 2) ^ i) ^ 2 *
        (((c + 2 * i).factorial : ℝ) * s ^ (c + 2 * i)) := by
  set δ := s' - s with hδ
  set t := |δ| * Real.sqrt n / s0 with ht
  have hs1 : 0 < s := hs0.trans_le hs
  have hs1' : 0 < s' := hs0.trans_le hs'
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have ht0 : 0 ≤ t := by positivity
  have hC : (0 : ℝ) < (c.factorial : ℝ) := by positivity
  have hI : (1 : ℝ) ≤ (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
  have hF : (0 : ℝ) < ((c + 2 * i).factorial : ℝ) := by positivity
  -- (a)
  have ha0 : s' ≤ (1 + t) * s := by
    have h1 : |δ| ≤ t * s0 := by
      rw [ht, div_mul_cancel₀ _ hs0.ne']
      exact le_mul_of_one_le_right (abs_nonneg _) hsq1
    have h2 : t * s0 ≤ t * s := mul_le_mul_of_nonneg_left hs ht0
    have h3 : δ ≤ |δ| := le_abs_self _
    have : s' = s + δ := by rw [hδ]; ring
    nlinarith
  have ha : s' ^ c ≤ (1 + t) ^ K * s ^ c := by
    calc s' ^ c ≤ ((1 + t) * s) ^ c := pow_le_pow_left₀ hs1'.le ha0 c
      _ = (1 + t) ^ c * s ^ c := mul_pow _ _ _
      _ ≤ (1 + t) ^ K * s ^ c :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by linarith) (by omega)) (by positivity)
  -- (b)
  have hb0 : δ ^ 2 * n / 4 ≤ t ^ 2 / 4 * s ^ 2 := by
    have h1 : δ ^ 2 * n = t ^ 2 * s0 ^ 2 := by
      rw [ht, tsq]; field_simp
    have h2 : s0 ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hs0.le hs 2
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg t)]
  have hb : (δ ^ 2 * n / 4) ^ i ≤ (t ^ 2 / 4 * s ^ 2) ^ i :=
    pow_le_pow_left₀ (by positivity) hb0 i
  -- (c)
  have hnat : (c + 2 * i).factorial ≤ c.factorial * (K ^ 2) ^ i := by
    refine (fact_le c (2 * i)).trans (Nat.mul_le_mul_left _ ?_)
    rw [← pow_mul]
    exact Nat.pow_le_pow_left hci _
  have hreal : ((c + 2 * i).factorial : ℝ) ≤ (c.factorial : ℝ) * ((K : ℝ) ^ 2) ^ i := by
    exact_mod_cast hnat
  have hc : ((c + 2 * i).factorial : ℝ) / ((c.factorial : ℝ) * (i.factorial : ℝ) ^ 2) ≤
      ((K : ℝ) ^ 2) ^ i := by
    rw [div_le_iff₀ (by positivity)]
    calc ((c + 2 * i).factorial : ℝ) ≤ (c.factorial : ℝ) * ((K : ℝ) ^ 2) ^ i := hreal
      _ = ((K : ℝ) ^ 2) ^ i * ((c.factorial : ℝ) * 1) := by ring
      _ ≤ ((K : ℝ) ^ 2) ^ i * ((c.factorial : ℝ) * (i.factorial : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hI) hC.le
  have hL : (c.factorial : ℝ) * s' ^ c * heatWeight c i δ ^ 2 * (n : ℝ) ^ i =
      s' ^ c * (δ ^ 2 * n / 4) ^ i *
        (((c + 2 * i).factorial : ℝ) / ((c.factorial : ℝ) * (i.factorial : ℝ) ^ 2)) *
        ((c + 2 * i).factorial : ℝ) := by
    have e4 : (δ ^ 2 * n / 4) ^ i = ((δ / 2) ^ i) ^ 2 * (n : ℝ) ^ i := by
      rw [← pow_mul, mul_comm i 2, pow_mul, ← mul_pow]; congr 1; ring
    unfold heatWeight
    rw [e4]
    generalize (δ / 2) ^ i = P
    field_simp
  rw [hL]
  calc s' ^ c * (δ ^ 2 * n / 4) ^ i *
        (((c + 2 * i).factorial : ℝ) / ((c.factorial : ℝ) * (i.factorial : ℝ) ^ 2)) *
        ((c + 2 * i).factorial : ℝ)
      ≤ ((1 + t) ^ K * s ^ c) * (t ^ 2 / 4 * s ^ 2) ^ i * ((K : ℝ) ^ 2) ^ i *
        ((c + 2 * i).factorial : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hF.le
        apply mul_le_mul _ hc (by positivity) (by positivity)
        exact mul_le_mul ha hb (by positivity) (by positivity)
    _ = _ := by
        have e2 : ((K * t / 2) ^ i) ^ 2 = (t ^ 2 / 4) ^ i * ((K : ℝ) ^ 2) ^ i := by
          rw [← pow_mul, mul_comm i 2, pow_mul, ← mul_pow]; congr 1; ring
        rw [e2, pow_add, pow_mul s 2 i, mul_pow]
        ring

private lemma pw (K : ℕ) (t : ℝ) (ht : 0 ≤ t) : (1 + t ^ 2) ^ (K / 2) ≤ (1 + K * t) ^ K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 : (1 : ℝ) ≤ 1 + K * t := by nlinarith
  have h2 : 1 + t ^ 2 ≤ (1 + K * t) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) ht, sq_nonneg t,
      mul_le_mul hk hk zero_le_one (by linarith : (0:ℝ) ≤ K),
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ K) ht) ht]
  calc (1 + t ^ 2) ^ (K / 2) ≤ ((1 + K * t) ^ 2) ^ (K / 2) :=
        pow_le_pow_left₀ (by positivity) h2 _
    _ = (1 + K * t) ^ (2 * (K / 2)) := (pow_mul _ _ _).symm
    _ ≤ (1 + K * t) ^ K := pow_le_pow_right₀ h1 (Nat.mul_div_le K 2)

private lemma pw2 (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + K * t / 2) ^ (K / 2) * (1 + t) ^ K * (1 + K * t / 2) ^ (K / 2) ≤
      (1 + K * t) ^ (2 * K) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hy : (1 : ℝ) ≤ 1 + K * t / 2 := by nlinarith
  have h2 : (1 + K * t / 2) * (1 + t) ≤ (1 + K * t) ^ 2 := by
    have hkt : t ≤ K * t := by nlinarith
    have hkk : (K : ℝ) * t ^ 2 ≤ (K : ℝ) ^ 2 * t ^ 2 := by
      have : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg t)
    nlinarith
  calc (1 + K * t / 2) ^ (K / 2) * (1 + t) ^ K * (1 + K * t / 2) ^ (K / 2)
      = (1 + K * t / 2) ^ (2 * (K / 2)) * (1 + t) ^ K := by rw [two_mul, pow_add]; ring
    _ ≤ (1 + K * t / 2) ^ K * (1 + t) ^ K :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hy (Nat.mul_div_le K 2)) (by positivity)
    _ = ((1 + K * t / 2) * (1 + t)) ^ K := (mul_pow _ _ _).symm
    _ ≤ ((1 + K * t) ^ 2) ^ K := pow_le_pow_left₀ (by positivity) h2 _
    _ = (1 + K * t) ^ (2 * K) := (pow_mul _ _ _).symm

/-- **Scale comparison** (tensor form). -/
theorem scaleIface (n K : ℕ) : ScaleIface n K := by
  intro A _ s s' s0 hs0 hs hs'
  have hs1 : 0 < s := hs0.trans_le hs
  have hs1' : 0 < s' := hs0.trans_le hs'
  have hen : 0 ≤ en K s A :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) (frob_nn _))
  by_cases hδ : s' = s
  · subst hδ
    refine ⟨?_, ?_⟩
    · rw [sub_self]; simp
    · simp
  by_cases hn : n = 0
  · subst hn
    have hfz : ∀ (c : ℕ) (_ : 1 ≤ c) (X : (Fin c → Fin 0) → ℝ), frob X = 0 :=
      fun c hc X => Finset.sum_eq_zero (fun w _ => (w ⟨0, hc⟩).elim0)
    have hez : ∀ r : ℝ, en K r A = 0 := by
      intro r
      apply Finset.sum_eq_zero
      intro c hc
      rw [hfz c (Finset.mem_Icc.mp hc).1, mul_zero]
    have hz : ∀ (j l : ℕ) (_ : 0 < l) (X : (Fin j → Fin 0) → ℝ) (w : Fin (j - 2 * l) → Fin 0),
        trL l X w = 0 :=
      fun j l hl X w => Finset.sum_eq_zero (fun c _ => (c ⟨0, hl⟩).elim0)
    have hm : hmean K s' A = hmean K s A := by
      unfold hmean heatA
      apply Finset.sum_congr rfl
      intro i _
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp
      · simp only [hz _ i hi0, mul_zero]
    rw [hez, hez, hm]
    simp
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hsq1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn1)
  have hδpos : 0 < |s' - s| := abs_pos.mpr (sub_ne_zero.mpr hδ)
  set t := |s' - s| * Real.sqrt n / s0 with ht
  have htpos : 0 < t := by positivity
  set B : Tens n := heatA K s A with hB
  set β : ℕ → ℝ := fun j => (j.factorial : ℝ) * s ^ j * frob (B j) with hβ
  have hβ0 : ∀ j, 0 ≤ β j := fun j => mul_nonneg (by positivity) (frob_nn _)
  have henβ : en K s A = ∑ j ∈ Finset.Icc 1 K, β j := rfl
  have hshift : ∀ c, heatA K s' A c = heatA K (s' - s) B c :=
    fun c => (heatA_shift K c s' s A).symm
  refine ⟨?_, ?_⟩
  · -- the mean
    set S0 := ((Finset.range (K + 1)).filter (fun i => 0 + 2 * i ≤ K)).erase 0 with hS0
    set w0 : Fin 0 → Fin n := fun i => i.elim0 with hw0
    have hdiff : hmean K s' A - hmean K s A =
        ∑ i ∈ S0, heatWeight 0 i (s' - s) * traceFamily i B 0 w0 := by
      unfold hmean
      rw [hshift 0]
      exact heatA_correction K 0 (s' - s) B (Nat.zero_le _) _
    have hμ : ∀ i ∈ S0, 0 < t ^ (2 * i) := fun i _ => by positivity
    have hf := heat_frob_le 0 (s' - s) B S0 (fun i => t ^ (2 * i)) hμ
    have hsingle : (hmean K s' A - hmean K s A) ^ 2 ≤
        frob (fun w : Fin 0 → Fin n =>
          ∑ i ∈ S0, heatWeight 0 i (s' - s) * traceFamily i B 0 w) := by
      rw [hdiff]
      exact Finset.single_le_sum
        (f := fun w : Fin 0 → Fin n =>
          (∑ i ∈ S0, heatWeight 0 i (s' - s) * traceFamily i B 0 w) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ w0)
    have hterm : ∑ i ∈ S0, heatWeight 0 i (s' - s) ^ 2 / t ^ (2 * i) *
        ((n : ℝ) ^ i * frob (B (0 + 2 * i))) ≤ ∑ i ∈ S0, β (0 + 2 * i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hc := coef_mean i (s' - s) s s0 n hs0 hs
      have hX := frob_nn (B (0 + 2 * i))
      rw [div_mul_eq_mul_div, div_le_iff₀ (hμ i hi)]
      calc heatWeight 0 i (s' - s) ^ 2 * ((n : ℝ) ^ i * frob (B (0 + 2 * i)))
          = (heatWeight 0 i (s' - s) ^ 2 * (n : ℝ) ^ i) * frob (B (0 + 2 * i)) := by ring
        _ ≤ (t ^ (2 * i) * (((0 + 2 * i).factorial : ℝ) * s ^ (0 + 2 * i))) *
              frob (B (0 + 2 * i)) := mul_le_mul_of_nonneg_right hc hX
        _ = β (0 + 2 * i) * t ^ (2 * i) := by rw [hβ]; ring
    have hsub : ∑ i ∈ S0, β (0 + 2 * i) ≤ en K s A := by
      rw [henβ]
      apply sum_inj_le β hβ0 S0 _ (fun i => 0 + 2 * i)
      · intro x _ y _ h; have h' : 0 + 2 * x = 0 + 2 * y := h; omega
      · intro i hi
        rw [hS0] at hi
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_Icc]; omega
    have hgeo : ∑ i ∈ S0, t ^ (2 * i) ≤ t ^ 2 * (1 + K * t) ^ K := by
      simp_rw [pow_mul]
      refine (geo1 (K / 2) (t ^ 2) (sq_nonneg t) S0 ?_).trans
        (mul_le_mul_of_nonneg_left (pw K t htpos.le) (sq_nonneg t))
      intro i hi
      rw [hS0] at hi
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_Icc]; omega
    calc (hmean K s' A - hmean K s A) ^ 2
        ≤ (∑ i ∈ S0, t ^ (2 * i)) * ∑ i ∈ S0, heatWeight 0 i (s' - s) ^ 2 / t ^ (2 * i) *
            ((n : ℝ) ^ i * frob (B (0 + 2 * i))) := hsingle.trans hf
      _ ≤ (t ^ 2 * (1 + K * t) ^ K) * en K s A :=
          mul_le_mul hgeo (hterm.trans hsub)
            (Finset.sum_nonneg (fun i hi => mul_nonneg (div_nonneg (sq_nonneg _) (hμ i hi).le)
              (mul_nonneg (by positivity) (frob_nn _)))) (by positivity)
  · -- the energy
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [en]
    set y : ℝ := K * t / 2 with hy
    have hypos : 0 < y := by positivity
    set R := Finset.range (K / 2 + 1) with hR
    have hstep : ∀ c ∈ Finset.Icc 1 K,
        (c.factorial : ℝ) * s' ^ c * frob (heatA K s' A c) ≤
          (1 + y) ^ (K / 2) * ((1 + t) ^ K *
            ∑ i ∈ R, if c + 2 * i ≤ K then y ^ i * β (c + 2 * i) else 0) := by
      intro c hc
      have hc1 := (Finset.mem_Icc.mp hc).1
      set Sc := (Finset.range (K + 1)).filter (fun i => c + 2 * i ≤ K) with hSc
      have hScR : Sc = R.filter (fun i => c + 2 * i ≤ K) := by
        ext i
        simp only [hSc, hR, Finset.mem_filter, Finset.mem_range]
        omega
      have hμ : ∀ i ∈ Sc, 0 < y ^ i := fun i _ => by positivity
      have hf : frob (heatA K (s' - s) B c) ≤ _ :=
        heat_frob_le c (s' - s) B Sc (fun i => y ^ i) hμ
      rw [hshift c]
      have hgeo : ∑ i ∈ Sc, y ^ i ≤ (1 + y) ^ (K / 2) := by
        apply geo _ _ hypos.le
        rw [hScR]; exact Finset.filter_subset _ _
      have hterm : (c.factorial : ℝ) * s' ^ c *
          ∑ i ∈ Sc, heatWeight c i (s' - s) ^ 2 / y ^ i *
            ((n : ℝ) ^ i * frob (B (c + 2 * i))) ≤
          (1 + t) ^ K * ∑ i ∈ R, if c + 2 * i ≤ K then y ^ i * β (c + 2 * i) else 0 := by
        rw [← Finset.sum_filter, ← hScR, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hci : c + 2 * i ≤ K := (Finset.mem_filter.mp hi).2
        have hce := coef_en K c i hci s s' s0 n hn1 hs0 hs hs'
        have hX := frob_nn (B (c + 2 * i))
        have hyi := hμ i hi
        rw [show (c.factorial : ℝ) * s' ^ c * (heatWeight c i (s' - s) ^ 2 / y ^ i *
            ((n : ℝ) ^ i * frob (B (c + 2 * i)))) =
            ((c.factorial : ℝ) * s' ^ c * heatWeight c i (s' - s) ^ 2 * (n : ℝ) ^ i) *
              frob (B (c + 2 * i)) / y ^ i by ring]
        rw [div_le_iff₀ hyi]
        calc _ ≤ ((1 + t) ^ K * (y ^ i) ^ 2 *
              (((c + 2 * i).factorial : ℝ) * s ^ (c + 2 * i))) * frob (B (c + 2 * i)) :=
              mul_le_mul_of_nonneg_right hce hX
          _ = _ := by rw [hβ]; ring
      calc (c.factorial : ℝ) * s' ^ c * frob (heatA K (s' - s) B c)
          ≤ (c.factorial : ℝ) * s' ^ c * ((∑ i ∈ Sc, y ^ i) *
              ∑ i ∈ Sc, heatWeight c i (s' - s) ^ 2 / y ^ i *
                ((n : ℝ) ^ i * frob (B (c + 2 * i)))) :=
            mul_le_mul_of_nonneg_left hf (by positivity)
        _ = (∑ i ∈ Sc, y ^ i) * ((c.factorial : ℝ) * s' ^ c *
              ∑ i ∈ Sc, heatWeight c i (s' - s) ^ 2 / y ^ i *
                ((n : ℝ) ^ i * frob (B (c + 2 * i)))) := by ring
        _ ≤ _ := mul_le_mul hgeo hterm
            (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i hi =>
              mul_nonneg (div_nonneg (sq_nonneg _) (hμ i hi).le)
                (mul_nonneg (by positivity) (frob_nn _))))) (by positivity)
    have hinner : ∀ i ∈ R,
        (∑ c ∈ Finset.Icc 1 K, if c + 2 * i ≤ K then y ^ i * β (c + 2 * i) else 0) ≤
          y ^ i * en K s A := by
      intro i _
      rw [← Finset.sum_filter, ← Finset.mul_sum, henβ]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_inj_le β hβ0 _ _ (fun c => c + 2 * i)
      · intro x _ z _ h; have h' : x + 2 * i = z + 2 * i := h; omega
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
        omega
    calc en K s' A
        ≤ ∑ c ∈ Finset.Icc 1 K, (1 + y) ^ (K / 2) * ((1 + t) ^ K *
            ∑ i ∈ R, if c + 2 * i ≤ K then y ^ i * β (c + 2 * i) else 0) :=
          Finset.sum_le_sum hstep
      _ = (1 + y) ^ (K / 2) * ((1 + t) ^ K * ∑ i ∈ R, ∑ c ∈ Finset.Icc 1 K,
            if c + 2 * i ≤ K then y ^ i * β (c + 2 * i) else 0) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (1 + y) ^ (K / 2) * ((1 + t) ^ K * ∑ i ∈ R, y ^ i * en K s A) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum hinner
      _ ≤ (1 + y) ^ (K / 2) * ((1 + t) ^ K * ((1 + y) ^ (K / 2) * en K s A)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (geo _ _ hypos.le R (le_refl _)) hen
      _ = ((1 + y) ^ (K / 2) * (1 + t) ^ K * (1 + y) ^ (K / 2)) * en K s A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pw2 K t htpos.le) hen

end BstLean.Part84
