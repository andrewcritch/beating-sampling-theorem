import BstLean.Part84Defs
import BstLean.Part53Elem
import BstLean.Part81KD
import BstLean.Part78Mean

/-!
# Part 84, `Mom`: sphere moments of `a n p₄` (`momIface`) and the scale defect (`deltaIface`)
-/

namespace BstLean.Part84

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part53 (p4)
open BstLean.Part81 (kap eD)

/-! ## Elementary facts -/

/-- A sequence with ratio `≤ θ ≤ 1/2` sums to at most `T 0 (1 + 2θ)`. -/
private lemma geo_sum (θ : ℝ) (h0 : 0 ≤ θ) (h : θ ≤ 1 / 2) : ∀ (m : ℕ) (T : ℕ → ℝ),
    (∀ i, 0 ≤ T i) → (∀ i, i < m → T (i + 1) ≤ θ * T i) →
    ∑ i ∈ Finset.range (m + 1), T i ≤ T 0 * (1 + 2 * θ) := by
  intro m
  induction m with
  | zero =>
    intro T hT _
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    nlinarith [hT 0]
  | succ m ih =>
    intro T hT hr
    rw [Finset.sum_range_succ']
    have h1 := ih (fun i => T (i + 1)) (fun i => hT (i + 1))
      (fun i hi => hr (i + 1) (by omega))
    have h2 := hr 0 (by omega)
    simp only [zero_add] at h1 h2
    have h3 : T 1 * (1 + 2 * θ) ≤ θ * T 0 * (1 + 2 * θ) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    nlinarith [hT 0, hT 1, mul_nonneg (hT 0) h0]

private lemma df_step (s : ℕ) :
    (4 * (s + 1) - 1).doubleFactorial = (4 * s + 3) * ((4 * s + 1) * (4 * s - 1).doubleFactorial) := by
  cases s with
  | zero => decide
  | succ t =>
    rw [show 4 * (t + 1 + 1) - 1 = (4 * t + 5) + 2 by omega, Nat.doubleFactorial_add_two,
      show 4 * t + 5 = (4 * (t + 1) - 1) + 2 by omega, Nat.doubleFactorial_add_two]
    have : 4 * (t + 1) - 1 + 2 = 4 * (t + 1) + 1 := by omega
    rw [this]

/-- The term `T_i = C(m,i) a^{i+j} (4(i+j)−1)!!`. -/
private noncomputable def TT (a : ℝ) (j m i : ℕ) : ℝ :=
  (m.choose i : ℝ) * a ^ (i + j) * ((4 * (i + j) - 1).doubleFactorial : ℝ)

private lemma TT_nonneg {a : ℝ} (ha : 0 ≤ a) (j m i : ℕ) : 0 ≤ TT a j m i := by
  unfold TT; positivity

private lemma TT_step (a : ℝ) (j m i : ℕ) (hi : i < m) :
    TT a j m (i + 1) * ((i : ℝ) + 1) =
      TT a j m i * (a * ((m : ℝ) - i) * ((4 * ((i : ℝ) + j) + 3) * (4 * ((i : ℝ) + j) + 1))) := by
  unfold TT
  have hc : ((m.choose (i + 1) : ℝ)) * ((i : ℝ) + 1) = (m.choose i : ℝ) * ((m : ℝ) - i) := by
    have := Nat.choose_succ_right_eq m i
    have h2 : ((m.choose (i + 1) * (i + 1) : ℕ) : ℝ) = ((m.choose i * (m - i) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub hi.le] at h2
    exact h2
  rw [show i + 1 + j = (i + j) + 1 by ring, df_step (i + j), pow_succ]
  push_cast
  linear_combination (a ^ (i + j) * a * ((4 * ((i : ℝ) + j) + 3) * ((4 * ((i : ℝ) + j) + 1) *
    ((4 * (i + j) - 1).doubleFactorial : ℝ)))) * hc

private lemma TT_ratio {a θ : ℝ} (ha : 0 ≤ a) (j m i : ℕ) (hi : i < m)
    (hθ : a * ((m : ℝ) - i) * ((4 * ((i : ℝ) + j) + 3) * (4 * ((i : ℝ) + j) + 1)) ≤
      θ * ((i : ℝ) + 1)) :
    TT a j m (i + 1) ≤ θ * TT a j m i := by
  have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h1 := TT_step a j m i hi
  have h2 := mul_le_mul_of_nonneg_left hθ (TT_nonneg ha j m i)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [h1]; linarith

/-! ## Sphere moments -/

private lemma cont_p4 (n : ℕ) : Continuous (p4 : (Fin n → ℝ) → ℝ) := by
  unfold p4; fun_prop

private lemma mom_pow (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) (q : ℕ) :
    (a * n) ^ q * ∫ x : Fin n → ℝ, p4 x ^ q ∂uniformSphere n ≤
      a ^ q * ((4 * q - 1).doubleFactorial : ℝ) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h := BstLean.Part53.lemmaS53 n hn q hq
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (a * n) ^ q)
    refine le_trans h2 (le_of_eq ?_)
    rw [mul_pow]
    field_simp

private lemma mom_sum (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 ≤ a) (j m : ℕ) :
    ∫ x : Fin n → ℝ, (a * n * p4 x) ^ j * (1 + a * n * p4 x) ^ m ∂uniformSphere n ≤
      ∑ i ∈ Finset.range (m + 1), TT a j m i := by
  have hpt : ∀ x : Fin n → ℝ, (a * n * p4 x) ^ j * (1 + a * n * p4 x) ^ m =
      ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * (a * n) ^ (i + j)) * p4 x ^ (i + j) := by
    intro x
    rw [add_comm 1, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_pow, mul_pow, mul_pow, pow_add, pow_add]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum (Finset.range (m + 1)) (f := fun i (x : Fin n → ℝ) =>
    ((m.choose i : ℝ) * (a * n) ^ (i + j)) * p4 x ^ (i + j)) (fun i _ =>
    (BstLean.Part78.sph_int hn ((cont_p4 n).pow (i + j))).const_mul _)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_const_mul]
  unfold TT
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mom_pow n hn a ha (i + j)) (by positivity)

theorem momIface (n : ℕ) (hn : 1 ≤ n) : MomIface n := by
  intro a ha j m
  refine ⟨?_, ?_, ?_⟩
  · exact BstLean.Part78.sph_int hn
      (((continuous_const.mul (cont_p4 n)).pow j).mul
        ((continuous_const.add (continuous_const.mul (cont_p4 n))).pow m))
  · intro hθ
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 := mom_sum n hn a ha 0 m
    simp only [pow_zero, one_mul] at h1
    refine le_trans h1 ?_
    have hg := geo_sum (4 * ((m : ℝ) + 1) ^ 2 * a) (by positivity) hθ m (TT a 0 m)
      (TT_nonneg ha 0 m) (fun i hi => TT_ratio ha 0 m i hi (by
        have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        have him : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
        have e1 : (4 * ((i : ℝ) + (0 : ℕ)) + 3) * (4 * ((i : ℝ) + (0 : ℕ)) + 1) ≤
            16 * ((i : ℝ) + 1) ^ 2 := by push_cast; nlinarith
        have e2 : ((m : ℝ) - i) * ((i : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 / 4 := by
          nlinarith [sq_nonneg ((m : ℝ) - i - (i + 1))]
        have e3 : a * ((m : ℝ) - i) * ((4 * ((i : ℝ) + (0 : ℕ)) + 3) * (4 * ((i : ℝ) + (0 : ℕ)) + 1)) ≤
            a * ((m : ℝ) - i) * (16 * ((i : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left e1 (mul_nonneg ha (by linarith))
        have e4 : a * (((m : ℝ) - i) * ((i : ℝ) + 1)) ≤ a * (((m : ℝ) + 1) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left e2 ha
        have e5 := mul_le_mul_of_nonneg_right e4 (by positivity : (0 : ℝ) ≤ 16 * ((i : ℝ) + 1))
        nlinarith))
    have h0 : TT a 0 m 0 = 1 := by simp [TT]
    rw [h0] at hg
    linarith
  · intro hθ
    refine le_trans (mom_sum n hn a ha j m) ?_
    have hg := geo_sum (1 / 2) (by norm_num) le_rfl m (TT a j m)
      (TT_nonneg ha j m) (fun i hi => TT_ratio ha j m i hi (by
        have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have him : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
        have e1 : (4 * ((i : ℝ) + j) + 3) * (4 * ((i : ℝ) + j) + 1) ≤
            16 * (((i : ℝ) + 1) * (((j : ℝ) + 1) * ((j : ℝ) + m + 1))) := by
          have ea : (i : ℝ) + j + 1 ≤ ((i : ℝ) + 1) * ((j : ℝ) + 1) := by nlinarith
          have eb : (i : ℝ) + j + 1 ≤ (j : ℝ) + m + 1 := by linarith
          have ec : ((i : ℝ) + j + 1) * ((i : ℝ) + j + 1) ≤
              (((i : ℝ) + 1) * ((j : ℝ) + 1)) * ((j : ℝ) + m + 1) :=
            mul_le_mul ea eb (by positivity) (by positivity)
          nlinarith
        have e3 : a * ((m : ℝ) - i) * ((4 * ((i : ℝ) + j) + 3) * (4 * ((i : ℝ) + j) + 1)) ≤
            a * ((m : ℝ) - i) * (16 * (((i : ℝ) + 1) * (((j : ℝ) + 1) * ((j : ℝ) + m + 1)))) :=
          mul_le_mul_of_nonneg_left e1 (mul_nonneg ha (by linarith))
        have e4 : a * ((m : ℝ) - i) * (16 * (((i : ℝ) + 1) * (((j : ℝ) + 1) * ((j : ℝ) + m + 1)))) ≤
            a * (m : ℝ) * (16 * (((i : ℝ) + 1) * (((j : ℝ) + 1) * ((j : ℝ) + m + 1)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) ha) (by positivity)
        have e5 := mul_le_mul_of_nonneg_right hθ (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)
        nlinarith))
    have h0 : TT a j m 0 = a ^ j * ((4 * j - 1).doubleFactorial : ℝ) := by simp [TT]
    rw [h0] at hg
    linarith

/-! ## The scale defect -/

private lemma p4_lower (n : ℕ) (hn : 1 ≤ n) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    1 / (n : ℝ) ≤ p4 x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => x i ^ 2)
  rw [hx] at h
  simp only [Finset.card_univ, Fintype.card_fin, ← pow_mul] at h
  rw [div_le_iff₀ hn0]
  unfold p4
  norm_num at h
  linarith

theorem deltaIface (n d : ℕ) (hd : 1 ≤ d) (hn : 10 ≤ n) : DeltaIface n d := by
  intro lam hlam x hx
  have hn0 : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hu0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hu1 : 1 / (n : ℝ) ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hp := p4_lower n (by omega) x hx
  have he1 := BstLean.Part81.one_le_eD d hd
  have he2 := BstLean.Part81.eD_le_two d
  have hk1 := BstLean.Part81.kap_diag_lower n d x hx
  have hU := (BstLean.Part53.lemmaU53 d n x hx).2
  have hk2 : kap d x x - eD d ≤ d * p4 x := by
    rw [BstLean.Part81.KD.kap_diag_phiSq, BstLean.Part81.eD]; linarith
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlam
  set u : ℝ := 1 / (n : ℝ) with hu
  set L : ℝ := lam ^ 2 with hL
  set κ : ℝ := kap d x x with hκ
  set e : ℝ := eD d with he
  set p : ℝ := p4 x with hp4
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hke : 0 ≤ κ - e := by linarith
  constructor
  · nlinarith [mul_nonneg hL0 (by linarith : (0 : ℝ) ≤ κ - 1)]
  · rw [abs_le]
    have a1 : L * (κ - e) ≤ 2 * (d * p) := by
      calc L * (κ - e) ≤ 2 * (κ - e) := mul_le_mul_of_nonneg_right (by linarith) hke
        _ ≤ 2 * (d * p) := by linarith
    have a2 : (L - 1) * e ≤ u * 2 := mul_le_mul hl2 he2 (by linarith) hu0.le
    have a3 : -(u * 2) ≤ (L - 1) * e := by
      have : (1 - L) * e ≤ u * 2 := mul_le_mul (by linarith) he2 (by linarith) hu0.le
      linarith
    have a4 : 0 ≤ L * (κ - e) := mul_nonneg hL0 hke
    have a5 : 0 ≤ d * p := mul_nonneg hd0 (by linarith)
    constructor <;> nlinarith

end BstLean.Part84
