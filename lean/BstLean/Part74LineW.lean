import BstLean.Part74Newton

/-!
# Part 74: the weights of the line program at a general degree pair `(d, k)`

`weightsGen74`: at every key `(i, l, j⃗)` with `2l ≤ i`, the engine value `wGen n K t v κ`
(`Part74LineDefs`) equals the surrogate weight `wRK (surrRK n K t v) d v κ`.

Route: `β_j = polyPN(AL sigX j)/(j! k_j(v,v))`; `τ = Σ_m tauC m · polyPN(tauL m)` over the `2d`
terms; `τ^l` is expanded over `μ : Fin l → Fin d ⊕ Fin d`; every list that occurs is homogeneous
(`UnifL`), so the generic engine theorem `surrL74` applies term by term.
-/

namespace BstLean.Part74

open MeasureTheory MvPolynomial
open BstLean.Part56 BstLean.Part56.MomProg
open BstLean.Part69

variable {n : ℕ}

/-! ## Homogeneous lists with no `s` factor -/

/-- Every term has `e = 0`, degree `D`, and at most `D` factors. -/
def UnifL (L : List TrmN) (D : ℕ) : Prop :=
  ∀ t ∈ L, t.2.1 = 0 ∧ mdeg t.2.2 = D ∧ t.2.2.length ≤ D

theorem unif_one : UnifL [(1, 0, [])] 0 := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  simp [mdeg]

theorem mdeg_append74 (M1 M2 : Mon) : mdeg (M1 ++ M2) = mdeg M1 + mdeg M2 := by simp [mdeg]

theorem unif_mulL {L1 L2 : List TrmN} {D1 D2 : ℕ} (h1 : UnifL L1 D1) (h2 : UnifL L2 D2) :
    UnifL (mulL L1 L2) (D1 + D2) := by
  intro t ht
  simp only [mulL, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht
  obtain ⟨a1, a2, a3⟩ := h1 s hs
  obtain ⟨b1, b2, b3⟩ := h2 u hu
  refine ⟨by simp [mulT, a1, b1], by simp [mulT, mdeg_append74, a2, b2], ?_⟩
  simp only [mulT, List.length_append]
  omega

theorem unif_powL {L : List TrmN} {D : ℕ} (h : UnifL L D) (k : ℕ) : UnifL (powL L k) (k * D) := by
  induction k with
  | zero => simpa [powL] using unif_one
  | succ k ih =>
    have := unif_mulL h ih
    rw [show (k + 1) * D = D + k * D by ring]
    exact this

theorem prodL_succ {m : ℕ} (Ls : Fin (m + 1) → List TrmN) :
    prodL Ls = mulL (Ls 0) (prodL fun r => Ls r.succ) := by
  simp [prodL, List.ofFn_succ]

theorem unif_prodL {m : ℕ} (Ls : Fin m → List TrmN) (Ds : Fin m → ℕ)
    (h : ∀ r, UnifL (Ls r) (Ds r)) : UnifL (prodL Ls) (∑ r, Ds r) := by
  induction m with
  | zero => simpa [prodL] using unif_one
  | succ m ih =>
    rw [prodL_succ, Fin.sum_univ_succ]
    exact unif_mulL (h 0) (ih _ _ fun r => h r.succ)

theorem polyPN_one74 (v : Fin n → ℝ) : polyPN v [(1, 0, [])] = 1 := by simp [polyPN, monP]

theorem polyPN_prodL (v : Fin n → ℝ) {m : ℕ} (Ls : Fin m → List TrmN) :
    polyPN v (prodL Ls) = ∏ r, polyPN v (Ls r) := by
  induction m with
  | zero => simpa [prodL] using polyPN_one74 v
  | succ m ih => rw [prodL_succ, polyPN_mulL, ih, Fin.prod_univ_succ]

/-- The index `j` of a term of `τ`. -/
def jm74 {d : ℕ} : Fin d ⊕ Fin d → ℕ
  | Sum.inl j => (j : ℕ) + 1
  | Sum.inr j => (j : ℕ) + 1

theorem jm74_le {d : ℕ} (m : Fin d ⊕ Fin d) : jm74 m ≤ d := by
  rcases m with j | j <;> simp only [jm74] <;> omega

theorem unif_sigX (j : ℕ) : UnifL (AL sigX j) j := fun t ht => by
  obtain ⟨h1, h2, _, h4⟩ := AL_sigX j t ht
  exact ⟨h1, by omega, h4⟩

theorem unif_tauL {d : ℕ} (m : Fin d ⊕ Fin d) : UnifL (tauL d m) (2 * jm74 m) := by
  rcases m with j | j
  · intro t ht
    obtain ⟨h1, h2, _, h4⟩ := AL_sigXX ((j : ℕ) + 1) t ht
    exact ⟨h1, h2, by simp only [jm74]; omega⟩
  · exact unif_powL (unif_sigX _) 2

/-! ## `𝒟` -/

theorem choose_prod74 (n d : ℕ) : ((n + d).choose d : ℝ) * (d.factorial : ℝ) =
    ∏ i ∈ Finset.range d, ((n : ℝ) + ((i : ℝ) + 1)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h : ((n + d + 1 : ℕ) : ℝ) * ((n + d).choose d : ℝ) =
        ((n + d + 1).choose (d + 1) : ℝ) * ((d + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (n + d) d
    rw [Finset.prod_range_succ, Nat.factorial_succ, ← add_assoc]
    push_cast at h ⊢
    linear_combination (-(d.factorial : ℝ)) * h + ((n : ℝ) + ((d : ℝ) + 1)) * ih

theorem DD_DDF74 (n d : ℕ) : BstLean.Part36.DD n d = DDF (n : ℝ) d := by
  rw [BstLean.Part36.DD_eq]
  unfold DDF
  rw [mul_div_assoc, ← choose_prod74 n d]
  have : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## The pointwise identities -/

theorem beta_pt74 {d k j : ℕ} (hj : j ≤ d) (hk : 1 ≤ k) (v x : Fin n → ℝ) :
    betaJ d j v x =
      eval x (polyPN v (AL sigX j)) / ((j.factorial : ℝ) * kvvF (pw v) d k j) := by
  unfold betaJ
  rw [kJ_xv74 hj x v, kJ_vv74' hj hk v, div_div]

theorem sum_Icc_fin74 (d : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 d, f j = ∑ j : Fin d, f ((j : ℕ) + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp

theorem tau_pt74 {d k : ℕ} (hk : 1 ≤ k) (v x : Fin n → ℝ) :
    tauR d v x = ∑ m : Fin d ⊕ Fin d, tauC (pw v) d k m * eval x (polyPN v (tauL d m)) := by
  unfold tauR KR
  rw [sum_Icc_fin74, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (j : ℕ) + 1 ≤ d := j.2
  simp only [tauC, tauL]
  rw [kJ_xx74 hj x v, kJ_xv74 hj x v, kJ_vv74' hj hk v, polyPN_powL, eval_pow]
  ring

theorem pow_sum74 {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (L : ℕ) :
    (∑ m, f m) ^ L = ∑ μ : Fin L → ι, ∏ a, f (μ a) := by
  have := Finset.prod_univ_sum (fun _ : Fin L => (Finset.univ : Finset ι)) (fun _ m => f m)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at this
  exact this

/-! ## The integral -/

theorem core74 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (d k L m : ℕ) (w : Fin m → Fin (d + 1)) (hk : 0 < L ∨ 0 < m → 1 ≤ k)
    (hdeg : 2 * L + m ≤ k) :
    ∫ x, tauR d v x ^ L * ∏ r, betaJ d (w r) v x ∂surrRK n K t v =
      (∑ μ : Fin L → Fin d ⊕ Fin d, (∏ a, tauC (pw v) d k (μ a)) *
        ILF (pw v) (W74 n K t) (Z69 n K t 0) (fuelF d k) (fuelG d k) (degD d k)
          (mulL (prodL fun a => tauL d (μ a)) (prodL fun r => AL sigX (w r)))) /
      (∏ r, (((w r : ℕ).factorial : ℝ) * kvvF (pw v) d k (w r))) := by
  classical
  have htau : ∀ x : Fin n → ℝ, tauR d v x ^ L =
      ∑ μ : Fin L → Fin d ⊕ Fin d, ∏ a,
        (tauC (pw v) d k (μ a) * eval x (polyPN v (tauL d (μ a)))) := by
    intro x
    have h0 : tauR d v x ^ L =
        (∑ m : Fin d ⊕ Fin d, tauC (pw v) d k m * eval x (polyPN v (tauL d m))) ^ L := by
      by_cases hL : L = 0
      · simp [hL]
      · rw [tau_pt74 (hk (Or.inl (by omega))) v x]
    rw [h0, pow_sum74]
  have hbeta : ∀ x : Fin n → ℝ, ∏ r, betaJ d (w r) v x =
      eval x (polyPN v (prodL fun r => AL sigX (w r))) /
        ∏ r, (((w r : ℕ).factorial : ℝ) * kvvF (pw v) d k (w r)) := by
    intro x
    rw [polyPN_prodL, map_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro r _
    exact beta_pt74 (Nat.lt_succ_iff.mp (w r).2) (hk (Or.inr (Fin.pos r))) v x
  have hpt : ∀ x : Fin n → ℝ, tauR d v x ^ L * ∏ r, betaJ d (w r) v x =
      (∑ μ : Fin L → Fin d ⊕ Fin d, (∏ a, tauC (pw v) d k (μ a)) *
        eval x (polyPN v (mulL (prodL fun a => tauL d (μ a))
          (prodL fun r => AL sigX (w r))))) /
      ∏ r, (((w r : ℕ).factorial : ℝ) * kvvF (pw v) d k (w r)) := by
    intro x
    rw [htau, hbeta, ← mul_div_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro μ _
    simp only [Finset.prod_mul_distrib, polyPN_mulL, eval_mul, polyPN_prodL, map_prod]
    ring
  simp only [hpt]
  rw [integral_div, integral_finsetSum _ fun μ _ =>
    (surr_int69 hn K t ht v (MvPolynomial.continuous_eval _)).const_mul _]
  congr 1
  apply Finset.sum_congr rfl
  intro μ _
  rw [integral_const_mul]
  congr 1
  -- the side conditions of the generic engine theorem
  have hU := unif_mulL (unif_prodL (fun a => tauL d (μ a)) (fun a => 2 * jm74 (μ a))
    fun a => unif_tauL (μ a)) (unif_prodL (fun r => AL sigX (w r)) (fun r => (w r : ℕ))
    fun r => unif_sigX _)
  set D := ∑ a, 2 * jm74 (μ a) + ∑ r, (w r : ℕ) with hD
  have h1 : ∑ a, 2 * jm74 (μ a) ≤ L * (2 * d) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin L)) (fun a => 2 * jm74 (μ a))
      (2 * d) (fun a _ => by have := jm74_le (μ a); omega)
    simpa using this
  have h2 : ∑ r, (w r : ℕ) ≤ m * d := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin m)) (fun r => (w r : ℕ))
      d (fun r _ => Nat.lt_succ_iff.mp (w r).2)
    simpa using this
  have hDk : D ≤ d * k := by
    have : L * (2 * d) + m * d = d * (2 * L + m) := by ring
    have h3 : d * (2 * L + m) ≤ d * k := Nat.mul_le_mul_left d hdeg
    omega
  have hdd : D ≤ 2 * degD d k := by unfold degD; omega
  refine surrL74 hn K t ht v hv (fuelF d k) (fuelG d k) (degD d k) _ ?_ ?_
  · intro s hs
    obtain ⟨a1, a2, a3⟩ := hU s hs
    refine ⟨by unfold tdeg; omega, ?_, by unfold fuelG; omega⟩
    unfold fuelF
    have : 2 * d * k = 2 * (d * k) := by ring
    omega
  · rcases Nat.even_or_odd D with he | ho
    · left; intro s hs
      obtain ⟨a1, a2, a3⟩ := hU s hs
      have : tdeg s = D := by unfold tdeg; omega
      rwa [this]
    · right; intro s hs
      obtain ⟨a1, a2, a3⟩ := hU s hs
      have : tdeg s = D := by unfold tdeg; omega
      rwa [this]

/-- **The weight formulas at a general degree pair `(d, k)`.** At every key `(i, l, j⃗)` with
`2l ≤ i` (the keys that `pg` reads), the engine value `wGen` is the surrogate weight. -/
theorem weightsGen74 {k d : ℕ} (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ)
    (hv : UnitV v) (κ : KeyRK k d) (hκ : 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ)) :
    wGen n K t v κ = wRK (surrRK n K t v) d v κ := by
  obtain ⟨⟨i, l⟩, w⟩ := κ
  simp only at hκ w
  have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.2
  unfold wGen wGenF wRK
  rw [MomProg.sg_sq (by omega), DD_DDF74, mul_div_assoc]
  congr 1
  exact (core74 hn K t ht v hv d k (l : ℕ) ((i : ℕ) - 2 * (l : ℕ)) w (by omega) (by omega)).symm

end BstLean.Part74

#print axioms BstLean.Part74.weightsGen74
