import BstLean.Part172Cls
import BstLean.Part172Grad

/-!
# Part 172 (file `Node`): the node statistics from the tangential statistics (deterministic)

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `t7:p08:statistics` (lines 2–3) and the Markov bound of `π_g`.

At a node with `‖A₁‖_op ≤ O₁` and `ς² ∈ [1/(5n), 12/(5n)]`, let `S = √wT` (the field
`Sfld t_A h r A₁` of `Part172Grad` on the latitude sphere) and `T = tanSq S`. If
`E_v T ≤ K₃` and `E_v (√T)^{2q} ≤ K₃^q` (`q = 2, 4, 8`), `K₃ = 32/(5n²)`, then
* **`V2N_of_tan`**: `V2N ≤ 64/n⁴` (given `DstN ≤ 16/n³`);
* **`piN_of_tan`**: `piN ≤ 1/n⁴`.
The route: Lemma LS (Part 162's `ls_lat`, `ls_lat_mom_sharp`) for `S`, then `mo_var_sq` and
`mo_eight_sq` for `wT = S²`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part134 (res)
open BstLean.Part161 (xLat momN)
open BstLean.Part162 (tanSq cLS cLS_pos ls_lat ls_lat_mom_sharp xLatH)
open BstLean.Part170 (hB tA aLat)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- `K₃ = 32/(5n²)`. -/
noncomputable def K3N (n : ℕ) : ℝ := 32 / (5 * (n : ℝ) ^ 2)

/-- The field `S` at a node. -/
noncomputable def SN (c : Ret n) (g : ℕ) : (Fin n → ℝ) → ℝ :=
  Sfld (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) (A1 c)

lemma SN_eq (c : Ret n) (g : ℕ) (v : Fin (n - 1) → ℝ) :
    SN c g (xLat c (nodeS c g) (unitF53 v)) = √(wT c g v) := by
  unfold SN Sfld wT aLat
  rw [Real.sqrt_mul (tA_nonneg n)]

/-! ## `momN` conversions -/

lemma nd_int_le_of_momN {f : (Fin (n - 1) → ℝ) → ℝ} {k : ℕ} (hk : 0 < k) {B : ℝ} (hB : 0 ≤ B)
    (h : momN (stdGauss (Fin (n - 1))) k f ≤ B) :
    ∫ v, |f v| ^ k ∂stdGauss (Fin (n - 1)) ≤ B ^ k := by
  unfold momN at h
  set I := ∫ v, |f v| ^ k ∂stdGauss (Fin (n - 1))
  have hI : 0 ≤ I := integral_nonneg fun _ => by positivity
  have e : I = (I ^ ((k : ℝ)⁻¹)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI, inv_mul_cancel₀ (by positivity), Real.rpow_one]
  rw [e]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hI _) h k

lemma nd_momN_le_of_int {f : (Fin (n - 1) → ℝ) → ℝ} {k : ℕ} (hk : 0 < k) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫ v, |f v| ^ k ∂stdGauss (Fin (n - 1)) ≤ B ^ k) :
    momN (stdGauss (Fin (n - 1))) k f ≤ B := by
  unfold momN
  have hI : 0 ≤ ∫ v, |f v| ^ k ∂stdGauss (Fin (n - 1)) := integral_nonneg fun _ => by positivity
  exact cl_rpow_le hk hI hB h

/-! ## The moments of `S − E S` -/

section node

variable (c : Ret n) (g : ℕ)

lemma nd_S_bdd (hn : 1 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n)) (v) :
    |√(wT c g v)| ≤ √(tA n * O1n n ^ 2) := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (wT_le hn c g hs h1 v)

/-- The centred moments of `S` from LS, order `2q`. -/
lemma nd_mom (hn : 80000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n)) {q : ℕ}
    (hq : 1 ≤ q) (hqn : 2 * q < n - 1) {K : ℝ} (hK : 0 ≤ K)
    (hT : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * q) ∂stdGauss (Fin (n - 1)) ≤ K ^ q) :
    ∫ v, (√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))) ^ (2 * q)
      ∂stdGauss (Fin (n - 1)) ≤ cLS q ^ (2 * q) * K ^ q * (((n : ℝ) - 1 - 2 * q)⁻¹) ^ q := by
  have hn2 : 2 ≤ n := by omega
  have hO : 0 ≤ O1n n := O1n_nonneg n
  have hL := S_lip (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) hO h1
  have hhom := S_hom (n := n) (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) (A1 c)
  have H := ls_lat_mom_sharp hn2 c hs (by positivity) hL (fun k y hk => hhom k y hk) hq hqn
  have hsq : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => √(BstLean.Part151.gradSq (fun w => SN c g (xLatH c (nodeS c g) w)) v -
        SN c g (xLat c (nodeS c g) (unitF53 v)) ^ 2)) ≤ √K := by
    refine nd_momN_le_of_int (by omega) (Real.sqrt_nonneg _) ?_
    rw [pow_mul, Real.sq_sqrt hK]
    exact hT
  have hn' : (0 : ℝ) < (n : ℝ) - 1 - 2 * q := by
    have : ((2 * q : ℕ) : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hqn
    push_cast at this
    rw [Nat.cast_sub (by omega)] at this
    push_cast at this; linarith
  have ha0 : 0 ≤ (((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have H2 : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => SN c g (xLat c (nodeS c g) (unitF53 v)) -
        ∫ w, SN c g (xLat c (nodeS c g) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ≤
      cLS q * (√K * (((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) := by
    refine H.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq ha0) (cLS_pos hq).le
  have H3 := nd_int_le_of_momN (by omega) (by
    have := (cLS_pos hq).le; positivity) H2
  simp_rw [SN_eq] at H3
  have e1 : ∀ v, (√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))) ^ (2 * q) =
      |√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))| ^ (2 * q) := fun v => by
    rw [pow_mul, pow_mul, sq_abs]
  simp_rw [e1]
  refine H3.trans (le_of_eq ?_)
  have hrr : ((((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) ^ 2 = ((n : ℝ) - 1 - 2 * q)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (√K) ^ (2 * q) = K ^ q := by rw [pow_mul, Real.sq_sqrt hK]
  have e3 : ((((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) ^ (2 * q) = (((n : ℝ) - 1 - 2 * q)⁻¹) ^ q := by
    rw [pow_mul, hrr]
  rw [mul_pow, mul_pow, e2, e3]
  ring

/-- The variance of `S` from LS (`p = 1`). -/
lemma nd_var (hn : 80000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n)) {K : ℝ}
    (hT : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ K) :
    ∫ v, (√(wT c g v) - ∫ w, √(wT c g w) ∂stdGauss (Fin (n - 1))) ^ 2
      ∂stdGauss (Fin (n - 1)) ≤ K / ((n : ℝ) - 2) := by
  have hn2 : 2 ≤ n := by omega
  have hO : 0 ≤ O1n n := O1n_nonneg n
  have hL := S_lip (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) hO h1
  have hhom := S_hom (n := n) (tA n) (hB c) (res (hB c) (a1Bar c (nodeS c g))) (A1 c)
  have H := ls_lat (Φ := SN c g) hn2 c hs (by positivity) hL (fun k y hk => hhom k y hk)
  have hT' : ∫ v, (BstLean.Part151.gradSq (fun w => SN c g (xLatH c (nodeS c g) w)) v -
      SN c g (xLat c (nodeS c g) (unitF53 v)) ^ 2) ∂stdGauss (Fin (n - 1)) ≤ K := hT
  have H' := H.trans hT'
  simp_rw [SN_eq] at H'
  have hn0 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [le_div_iff₀ hn0, mul_comm]
  exact H'

end node

/-! ## Numerics -/

lemma nd_numV {N x b D : ℝ} (hN : 80000 ≤ N) (hx0 : 0 ≤ x)
    (hx : x ≤ 42742 / 10000 * (32 / (5 * N ^ 2)) / (N - 5)) (hb0 : 0 ≤ b)
    (hb : b ^ 2 ≤ 4 * (12 / (5 * N)) * (32 / (5 * N ^ 2)) / (N - 2)) (hD0 : 0 ≤ D)
    (hD : D ≤ 16 / N ^ 3) :
    (x + b) ^ 2 + D ^ 2 ≤ 64 / N ^ 4 := by
  have hN0 : 0 < N := by linarith
  set w := 1 / N ^ 2 with hw
  have hw0 : 0 < w := by positivity
  have e64 : 64 / N ^ 4 = 64 * w ^ 2 := by rw [hw]; field_simp
  have hx' : x ≤ 1 / 1000 * w := by
    refine hx.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hb' : b ^ 2 ≤ 6145 / 100 * w ^ 2 := by
    refine hb.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hD' : D ≤ 1 / 1000 * w := by
    refine hD.trans ?_
    rw [hw, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hb8 : b ≤ 8 * w := by
    by_contra hcon
    have := not_le.mp hcon
    nlinarith
  rw [e64]
  nlinarith [mul_le_mul hx' hb8 hb0 (by positivity), mul_le_mul hx' hx' hx0 (by positivity),
    mul_le_mul hD' hD' hD0 (by positivity)]

lemma nd_numP {N α β γ den : ℝ} (hN : 80000 ≤ N) (hα0 : 0 ≤ α)
    (hα : α ≤ 1519 / 100 * (32 / (5 * N ^ 2)) / (N - 17)) (hβ0 : 0 ≤ β)
    (hβ : β ^ 2 ≤ 4 * (12 / (5 * N)) * (7905 / 1000) * (32 / (5 * N ^ 2)) / (N - 9))
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 32 / (5 * N ^ 2) / (N - 2)) (hden : 1 / (10 * N) - 16 / N ^ 3 ≤ den) :
    (α + β + γ) ^ 8 / den ^ 8 ≤ 1 / N ^ 4 := by
  have hN0 : 0 < N := by linarith
  set w := 1 / N with hw
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 / 80000 := by rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hN
  have hα' : α ≤ 13 / 10000 * w ^ 2 := by
    refine hα.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hγ' : γ ≤ 1 / 10000 * w ^ 2 := by
    refine hγ.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hβ' : β ^ 2 ≤ 4858 / 10 * w ^ 4 := by
    refine hβ.trans ?_
    rw [hw, div_le_iff₀ (by linarith)]
    field_simp
    nlinarith
  have hβ2 : β ≤ 2205 / 100 * w ^ 2 := by
    by_contra hcon
    have := not_le.mp hcon
    nlinarith
  have hden' : 998 / 10000 * w ≤ den := by
    refine le_trans ?_ hden
    rw [hw]
    rw [show 1 / (10 * N) - 16 / N ^ 3 = (N ^ 2 - 160) / (10 * N ^ 3) by field_simp; ring]
    rw [show 998 / 10000 * (1 / N) = 998 / (10000 * N) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hd0 : 0 < den := lt_of_lt_of_le (by positivity) hden'
  have hsum : α + β + γ ≤ 22064 / 1000 * w ^ 2 := by linarith
  have hs0 : 0 ≤ α + β + γ := by positivity
  have hsq : (α + β + γ) ^ 2 ≤ den ^ 2 * w := by
    have h1 : (α + β + γ) ^ 2 ≤ (22064 / 1000 * w ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hsum 2
    have h2 : (998 / 10000 * w) ^ 2 ≤ den ^ 2 := pow_le_pow_left₀ (by positivity) hden' 2
    have h3 : (22064 / 1000 * w ^ 2) ^ 2 ≤ (998 / 10000 * w) ^ 2 * w := by
      have : w ^ 3 * (w * (22064 / 1000) ^ 2) ≤ w ^ 3 * ((998 / 10000) ^ 2) := by
        gcongr; nlinarith
      nlinarith
    nlinarith
  have h8 : (α + β + γ) ^ 8 ≤ den ^ 8 * w ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hsq 4
    calc (α + β + γ) ^ 8 = ((α + β + γ) ^ 2) ^ 4 := by ring
      _ ≤ (den ^ 2 * w) ^ 4 := this
      _ = den ^ 8 * w ^ 4 := by ring
  rw [div_le_iff₀ (by positivity)]
  calc (α + β + γ) ^ 8 ≤ den ^ 8 * w ^ 4 := h8
    _ = 1 / N ^ 4 * den ^ 8 := by rw [hw]; ring

section node2

variable (c : Ret n) (g : ℕ)

lemma nd_mu (hn : 80000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ))) :
    (∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))) ^ 2 ≤ 12 / (5 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have h := mo_sq_int_le (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (nd_S_bdd c g hn1 hs h1)
  have e : ∫ v, √(wT c g v) ^ 2 ∂stdGauss (Fin (n - 1)) = ∫ v, wT c g v ∂stdGauss (Fin (n - 1)) :=
    integral_congr_ae (ae_of_all _ fun v => Real.sq_sqrt (wT_nonneg c g v))
  rw [e, int_wT_eq hn1 c g hs (O1n_nonneg n) h1] at h
  linarith [DstN_nonneg c g]

lemma nd_wT_S (hn : 1 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n)) (k : ℕ) :
    ∫ v, (wT c g v - ∫ w, wT c g w ∂stdGauss (Fin (n - 1))) ^ k ∂stdGauss (Fin (n - 1)) =
    ∫ v, (√(wT c g v) ^ 2 - ∫ w, √(wT c g w) ^ 2 ∂stdGauss (Fin (n - 1))) ^ k
      ∂stdGauss (Fin (n - 1)) := by
  have e : ∫ v, √(wT c g v) ^ 2 ∂stdGauss (Fin (n - 1)) = ∫ v, wT c g v ∂stdGauss (Fin (n - 1)) :=
    integral_congr_ae (ae_of_all _ fun v => Real.sq_sqrt (wT_nonneg c g v))
  rw [e]
  exact integral_congr_ae (ae_of_all _ fun v => by
    simp only; rw [Real.sq_sqrt (wT_nonneg c g v)])

/-- **`V2N ≤ 64/n⁴`** from the tangential statistics of `S` (paper `t7:p08:statistics`,
line 2). -/
theorem V2N_of_tan (hn : 80000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ))) (hDst : DstN c g ≤ DmN n)
    (hT1 : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ K3N n)
    (hT2 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 2) ∂stdGauss (Fin (n - 1)) ≤
      K3N n ^ 2) :
    V2N c g ≤ VmN n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 0 ≤ K3N n := by unfold K3N; positivity
  have h4 := nd_mom c g hn hs h1 (q := 2) (by norm_num) (by omega) hK hT2
  have h2 := nd_var c g hn hs h1 hT1
  have hμ := nd_mu c g hn hs h1 hσu
  set μ0 := ∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))
  set x := cLS 2 ^ 2 * K3N n * ((n : ℝ) - 5)⁻¹ with hx
  set y := √(K3N n / ((n : ℝ) - 2)) with hy
  have hn5 : (0 : ℝ) < (n : ℝ) - 5 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have h4' : ∫ v, (√(wT c g v) - μ0) ^ 4 ∂stdGauss (Fin (n - 1)) ≤ x ^ 2 := by
    refine h4.trans (le_of_eq ?_)
    rw [hx]; push_cast; ring_nf
  have h2' : ∫ v, (√(wT c g v) - μ0) ^ 2 ∂stdGauss (Fin (n - 1)) ≤ y ^ 2 := by
    rw [hy, Real.sq_sqrt (by positivity)]; exact h2
  have HV := mo_var_sq (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (nd_S_bdd c g hn1 hs h1) hx0 (Real.sqrt_nonneg _) h4' h2'
  rw [V2N_eq hn1 c g hs (O1n_nonneg n) h1, nd_wT_S c g hn1 hs h1]
  refine (add_le_add HV le_rfl).trans ?_
  unfold VmN
  have hc2 : cLS 2 ^ 2 ≤ 42742 / 10000 := by
    have := cLS2_le; have h0 := (cLS_pos (q := 2) (by norm_num)).le; nlinarith
  refine nd_numV hnR hx0 ?_ (by positivity) ?_ (DstN_nonneg c g) hDst
  · rw [hx, ← div_eq_mul_inv]
    unfold K3N
    gcongr
  · rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    change 2 ^ 2 * μ0 ^ 2 * (K3N n / ((n : ℝ) - 2)) ≤ _
    unfold K3N
    have : (2 : ℝ) ^ 2 * μ0 ^ 2 ≤ 4 * (12 / (5 * n)) := by nlinarith
    calc 2 ^ 2 * μ0 ^ 2 * (32 / (5 * (n : ℝ) ^ 2) / ((n : ℝ) - 2)) ≤
        4 * (12 / (5 * n)) * (32 / (5 * (n : ℝ) ^ 2) / ((n : ℝ) - 2)) := by gcongr
      _ = _ := by ring

/-- **`piN ≤ 1/n⁴`** from the tangential statistics of `S` (paper `t7:p08:statistics`, line 3,
and Markov of order eight). -/
theorem piN_of_tan (hn : 80000 ≤ n) (hs : nodeS c g ^ 2 ≤ 1) (h1 : OpB (A1 c) (O1n n))
    (hσl : SminN n ≤ vsig2 c (nodeS c g)) (hσu : vsig2 c (nodeS c g) ≤ 12 / (5 * (n : ℝ)))
    (hDst : DstN c g ≤ DmN n)
    (hT1 : ∫ v, tanSq (SN c g) c (nodeS c g) v ∂stdGauss (Fin (n - 1)) ≤ K3N n)
    (hT4 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 4) ∂stdGauss (Fin (n - 1)) ≤
      K3N n ^ 4)
    (hT8 : ∫ v, |√(tanSq (SN c g) c (nodeS c g) v)| ^ (2 * 8) ∂stdGauss (Fin (n - 1)) ≤
      K3N n ^ 8) :
    piN c g ≤ PmN n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hK : 0 ≤ K3N n := by unfold K3N; positivity
  have hK0 : 0 < K3N n := by unfold K3N; positivity
  have hm8 := nd_mom c g hn hs h1 (q := 8) (by norm_num) (by omega) hK hT8
  have hm4 := nd_mom c g hn hs h1 (q := 4) (by norm_num) (by omega) hK hT4
  have h2 := nd_var c g hn hs h1 hT1
  have hμ := nd_mu c g hn hs h1 hσu
  set μ0 := ∫ v, √(wT c g v) ∂stdGauss (Fin (n - 1))
  have hDlt : DstN c g < vsig2 c (nodeS c g) / 2 := by
    have : DmN n < SminN n / 2 := by
      unfold DmN SminN
      rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      have h3 : (160 : ℝ) * n < (n : ℝ) ^ 3 := by nlinarith [mul_pos hn0 hn0]
      nlinarith
    linarith
  have HP := piN_le hn1 c g hs (O1n_nonneg n) h1 hDlt
  rw [nd_wT_S c g hn1 hs h1] at HP
  have hn17 : (0 : ℝ) < (n : ℝ) - 17 := by linarith
  have hn9 : (0 : ℝ) < (n : ℝ) - 9 := by linarith
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  set α := cLS 8 ^ 2 * K3N n * ((n : ℝ) - 17)⁻¹ with hα
  set β := 2 * √(12 / (5 * (n : ℝ))) * (cLS 4 * √(K3N n) * √(((n : ℝ) - 9)⁻¹)) with hβ
  set γ := K3N n / ((n : ℝ) - 2) with hγ
  have hc8 := (cLS_pos (q := 8) (by norm_num))
  have hc4 := (cLS_pos (q := 4) (by norm_num))
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have h16 : ∫ v, (√(wT c g v) - μ0) ^ 16 ∂stdGauss (Fin (n - 1)) ≤ α ^ 8 := by
    refine hm8.trans (le_of_eq ?_)
    rw [hα]; push_cast; ring_nf
  have hμa : |μ0| ≤ √(12 / (5 * (n : ℝ))) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hμ
  have h8 : (2 * |μ0|) ^ 8 * ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤ β ^ 8 := by
    have hm4' : ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤
        cLS 4 ^ 8 * K3N n ^ 4 * (((n : ℝ) - 9)⁻¹) ^ 4 := by
      refine hm4.trans (le_of_eq ?_); push_cast; ring_nf
    have hI0 : 0 ≤ ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) :=
      integral_nonneg fun _ => by positivity
    calc (2 * |μ0|) ^ 8 * ∫ v, (√(wT c g v) - μ0) ^ 8 ∂stdGauss (Fin (n - 1)) ≤
        (2 * √(12 / (5 * (n : ℝ)))) ^ 8 * (cLS 4 ^ 8 * K3N n ^ 4 * (((n : ℝ) - 9)⁻¹) ^ 4) := by
          refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith [hμa]) 8) hm4' hI0
            (by positivity)
      _ = β ^ 8 := by
          rw [hβ]
          have e1 : √(K3N n) ^ 8 = K3N n ^ 4 := by
            rw [show √(K3N n) ^ 8 = (√(K3N n) ^ 2) ^ 4 by ring, Real.sq_sqrt hK]
          have e2 : √(((n : ℝ) - 9)⁻¹) ^ 8 = (((n : ℝ) - 9)⁻¹) ^ 4 := by
            rw [show √(((n : ℝ) - 9)⁻¹) ^ 8 = (√(((n : ℝ) - 9)⁻¹) ^ 2) ^ 4 by ring,
              Real.sq_sqrt (by positivity)]
          simp only [mul_pow, e1, e2]
  have HE := mo_eight_sq (μ := stdGauss (Fin (n - 1))) (measurable_wT c g).sqrt
    (nd_S_bdd c g hn1 hs h1) hα0 hβ0 hγ0 h16 h8 h2
  refine HP.trans ?_
  have hden : 1 / (10 * (n : ℝ)) - 16 / (n : ℝ) ^ 3 ≤ vsig2 c (nodeS c g) / 2 - DstN c g := by
    have e : SminN n / 2 = 1 / (10 * (n : ℝ)) := by unfold SminN; field_simp; ring
    have : DstN c g ≤ 16 / (n : ℝ) ^ 3 := hDst
    linarith
  have hd0 : 0 < vsig2 c (nodeS c g) / 2 - DstN c g := by linarith
  calc (∫ v, (√(wT c g v) ^ 2 - ∫ w, √(wT c g w) ^ 2 ∂stdGauss (Fin (n - 1))) ^ 8
        ∂stdGauss (Fin (n - 1))) / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 ≤
      (α + β + γ) ^ 8 / (vsig2 c (nodeS c g) / 2 - DstN c g) ^ 8 := by gcongr
    _ ≤ 1 / (n : ℝ) ^ 4 := by
      refine nd_numP hnR hα0.le ?_ hβ0.le ?_ hγ0.le le_rfl hden
      · have hc8' : cLS 8 ^ 2 ≤ 1519 / 100 :=
          (pow_le_pow_left₀ hc8.le cLS8_le 2).trans (by norm_num)
        rw [hα, ← div_eq_mul_inv]; unfold K3N; gcongr
      · have hc4' : cLS 4 ^ 2 ≤ 7905 / 1000 :=
          (pow_le_pow_left₀ hc4.le cLS4_le 2).trans (by norm_num)
        rw [hβ, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
          Real.sq_sqrt hK, Real.sq_sqrt (by positivity)]
        unfold K3N
        rw [div_eq_mul_inv _ ((n : ℝ) - 9)]
        have : (0:ℝ) ≤ 32 / (5 * (n : ℝ) ^ 2) := by positivity
        calc 2 ^ 2 * (12 / (5 * ↑n)) * (cLS 4 ^ 2 * (32 / (5 * ↑n ^ 2)) * ((n : ℝ) - 9)⁻¹) ≤
            2 ^ 2 * (12 / (5 * ↑n)) * (7905 / 1000 * (32 / (5 * ↑n ^ 2)) * ((n : ℝ) - 9)⁻¹) := by
              gcongr
          _ = _ := by ring
    _ = PmN n := by unfold PmN; rfl

end node2

end BstLean.Part172
