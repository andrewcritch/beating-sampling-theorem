import BstLean.Part81Defs
import BstLean.Part81Mean
import BstLean.Part78Gauss

/-!
# Part 81: mean bounds and the floor form of the variance bound, from sphere constants

Port of `Part78Gauss` (`floor_le`, `err_le`, `mean_upper`), `Part78Final2` (`kernel_int_le`) and
`Part78Final3` (`rT_int_le`, `varBoundW_of_K2`) with the numbers replaced by parameters.

* `mb_of`: `SphC` and `MeanIds` give `MB`.
* `varBoundW_of`: `SphC`, `MB`, `WQId`, `VarBoundK`, `VarBoundK2` give `VarBoundW`.
-/

namespace BstLean.Part81.Num

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part78 (nsq frobH trH nsq_nonneg frobH_nonneg trH_sq_le sph_int)

variable {n d : ℕ}

/-! ## Real arithmetic -/

lemma floor_real {t m1 k s2 e A v T2 μ σ α β : ℝ} (he : 0 ≤ e) (hA : 0 ≤ A) (hv : 0 ≤ v)
    (hT : 0 ≤ T2) (ht0 : e ≤ t) (hm1 : m1 ≤ μ) (hs1 : s2 ≤ σ) (hk0 : t ^ 2 ≤ k)
    (hα : α ≤ e - μ) (hβ : β ≤ 2 * (e ^ 2 - σ)) :
    α * A + β * v ≤ (t - m1) * A + T2 * (k - t ^ 2) + 2 * v * (k - s2) := by
  have h1 : 0 ≤ (t - m1 - α) * A := mul_nonneg (by linarith) hA
  have h2 : 0 ≤ T2 * (k - t ^ 2) := mul_nonneg hT (by linarith)
  have h3 : e ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ he ht0 2
  have h4 : 0 ≤ (2 * (k - s2) - β) * v := mul_nonneg (by linarith) hv
  linarith

lemma err_real {t m1 s2 e A v T2 N M1 S2 B1 : ℝ} (hN : 0 < N) (hA : 0 ≤ A) (hv : 0 ≤ v)
    (hT : T2 ≤ N * v) (ht0 : e ≤ t) (ht1 : t - e ≤ B1 / N)
    (hm1 : m1 ≤ M1 / N) (hs1 : s2 ≤ S2 / N) :
    A * m1 + 2 * v * s2 + T2 * (t - e) ^ 2 ≤ (M1 * A + (2 * S2 + B1 ^ 2) * v) / N := by
  have h3 : (t - e) ^ 2 ≤ (B1 / N) ^ 2 := pow_le_pow_left₀ (by linarith) ht1 2
  have h4 : T2 * (t - e) ^ 2 ≤ (N * v) * (B1 / N) ^ 2 :=
    mul_le_mul hT h3 (sq_nonneg _) (mul_nonneg hN.le hv)
  have e' : (M1 * A + (2 * S2 + B1 ^ 2) * v) / N =
      A * (M1 / N) + 2 * v * (S2 / N) + (N * v) * (B1 / N) ^ 2 := by
    field_simp; ring
  rw [e']
  have h5 := mul_le_mul_of_nonneg_left hm1 hA
  have h6 := mul_le_mul_of_nonneg_left hs1 hv
  linarith

lemma tr_var_real {T2 N v k t VK : ℝ} (hN : 0 < N) (hv : 0 ≤ v) (hT : T2 ≤ N * v)
    (hk0 : t ^ 2 ≤ k) (hk1 : k - t ^ 2 ≤ VK / N) : T2 * (k - t ^ 2) ≤ VK * v := by
  have c3 : T2 * (k - t ^ 2) ≤ (N * v) * (VK / N) :=
    mul_le_mul hT hk1 (by linarith) (mul_nonneg hN.le hv)
  have c3e : (N * v) * (VK / N) = VK * v := by field_simp
  rw [c3e] at c3
  exact c3

lemma upper_real {t m1 k s2 e A v T2 N B1 VK : ℝ} (hN : 0 < N) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hv : 0 ≤ v) (hT : T2 ≤ N * v) (ht0 : e ≤ t) (ht1 : t - e ≤ B1 / N)
    (hm0 : 0 ≤ m1) (hs0 : 0 ≤ s2) (hk0 : t ^ 2 ≤ k) (hk1 : k - t ^ 2 ≤ VK / N) :
    (t - m1) * A + T2 * (k - t ^ 2) + 2 * v * (k - s2) ≤
      (e + B1 / N) * A + (VK + 2 * ((e + B1 / N) ^ 2 + VK / N)) * v := by
  have h1 : (t - m1) * A ≤ (e + B1 / N) * A := mul_le_mul_of_nonneg_right (by linarith) hA
  have h2 := tr_var_real hN hv hT hk0 hk1
  have h3 : t ^ 2 ≤ (e + B1 / N) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h4 : 2 * v * (k - s2) ≤ 2 * v * ((e + B1 / N) ^ 2 + VK / N) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

lemma pt1 {A v T2 s t k1 k2x m1 s2 e sM w : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ v) (hT : 0 ≤ T2)
    (he : 0 ≤ e) (hes : e ≤ s) (hsM : s ≤ sM) (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2x)
    (hw : w = A * (s - 2 * k1 + m1) + T2 * (s - t) ^ 2 + 2 * v * (s ^ 2 - 2 * k2x + s2)) :
    (A + 4 * v * s) * w ≤ (A + 4 * v * e) * w +
      4 * v * ((s - e) * (A * (sM + m1) + 2 * v * (sM ^ 2 + s2)) +
        (sM - e) * (T2 * (s - t) ^ 2)) := by
  have hwU : w ≤ A * (s + m1) + T2 * (s - t) ^ 2 + 2 * v * (s ^ 2 + s2) := by
    rw [hw]
    have p1 := mul_nonneg hA hk1
    have p2 := mul_nonneg hv hk2
    linarith
  have hs2 : s ^ 2 ≤ sM ^ 2 := pow_le_pow_left₀ (by linarith) hsM 2
  have hU1 : A * (s + m1) + 2 * v * (s ^ 2 + s2) ≤ A * (sM + m1) + 2 * v * (sM ^ 2 + s2) := by
    have p1 := mul_le_mul_of_nonneg_left hsM hA
    have p2 := mul_le_mul_of_nonneg_left hs2 hv
    linarith
  have hT0 : 0 ≤ T2 * (s - t) ^ 2 := mul_nonneg hT (sq_nonneg _)
  have hδ : 0 ≤ s - e := by linarith
  have s1 : (s - e) * w ≤ (s - e) * (A * (s + m1) + T2 * (s - t) ^ 2 + 2 * v * (s ^ 2 + s2)) :=
    mul_le_mul_of_nonneg_left hwU hδ
  have s2' : (s - e) * (A * (s + m1) + 2 * v * (s ^ 2 + s2)) ≤
      (s - e) * (A * (sM + m1) + 2 * v * (sM ^ 2 + s2)) := mul_le_mul_of_nonneg_left hU1 hδ
  have s3 : (s - e) * (T2 * (s - t) ^ 2) ≤ (sM - e) * (T2 * (s - t) ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0
  have hq : (s - e) * w ≤ (s - e) * (A * (sM + m1) + 2 * v * (sM ^ 2 + s2)) +
      (sM - e) * (T2 * (s - t) ^ 2) := by linarith
  have e' : (A + 4 * v * s) * w = (A + 4 * v * e) * w + 4 * v * ((s - e) * w) := by ring
  rw [e']
  have := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ 4 * v)
  linarith

lemma fin1 {A v e α β K1a K1b m b sM μ σ VK T2 t m1 s2 k N : ℝ} (hN : 0 < N) (hA : 0 ≤ A)
    (hv : 0 ≤ v) (hT : T2 ≤ N * v) (he : 0 ≤ e) (ht0 : e ≤ t) (ht1 : t - e ≤ b)
    (hm0 : 0 ≤ m1) (hm1 : m1 ≤ μ) (hs0 : 0 ≤ s2) (hs1 : s2 ≤ σ) (hk0 : t ^ 2 ≤ k)
    (hk1 : k - t ^ 2 ≤ VK / N) (hesM : e ≤ sM) (hα : 0 < α) (hβ : 0 < β)
    (hfl : α * A + β * v ≤ m)
    (hK1a : 1 ≤ K1a * α) (hK1a' : 4 * e ≤ K1a * β)
    (hK1b : 4 * (2 * b * (sM ^ 2 + σ) + (sM - e) * VK) ≤ K1b * β ^ 2)
    (hK1b' : 2 * (b * (sM + μ)) ≤ K1b * (α * β)) (hK1b0 : 0 ≤ K1b) :
    (A + 4 * v * e) * m + 4 * v * ((t - e) * (A * (sM + m1) + 2 * v * (sM ^ 2 + s2)) +
      (sM - e) * (T2 * (k - t ^ 2))) ≤ (K1a + K1b) * (α * A + β * v) * m := by
  have hW0 : 0 ≤ α * A + β * v := add_nonneg (mul_nonneg hα.le hA) (mul_nonneg hβ.le hv)
  have hm0' : 0 ≤ m := hW0.trans hfl
  have hb0 : 0 ≤ b := by linarith
  have hsM0 : 0 ≤ sM := by linarith
  have c1 : A * (sM + m1) + 2 * v * (sM ^ 2 + s2) ≤ A * (sM + μ) + 2 * v * (sM ^ 2 + σ) := by
    have p1 := mul_le_mul_of_nonneg_left hm1 hA
    have p2 := mul_le_mul_of_nonneg_left hs1 hv
    linarith
  have c10 : 0 ≤ A * (sM + m1) + 2 * v * (sM ^ 2 + s2) :=
    add_nonneg (mul_nonneg hA (by linarith))
      (mul_nonneg (by linarith) (add_nonneg (sq_nonneg _) hs0))
  have c2 : (t - e) * (A * (sM + m1) + 2 * v * (sM ^ 2 + s2)) ≤
      b * (A * (sM + μ) + 2 * v * (sM ^ 2 + σ)) := mul_le_mul ht1 c1 c10 hb0
  have c3 := tr_var_real hN hv hT hk0 hk1
  have c4 : (sM - e) * (T2 * (k - t ^ 2)) ≤ (sM - e) * (VK * v) :=
    mul_le_mul_of_nonneg_left c3 (by linarith)
  have d1 : A + 4 * v * e ≤ K1a * (α * A + β * v) := by
    have p1 := mul_le_mul_of_nonneg_right hK1a hA
    have p2 := mul_le_mul_of_nonneg_right hK1a' hv
    linarith
  have d1' := mul_le_mul_of_nonneg_right d1 hm0'
  have d2 : 4 * v * (b * (A * (sM + μ) + 2 * v * (sM ^ 2 + σ)) + (sM - e) * (VK * v)) ≤
      K1b * ((α * A + β * v) * (α * A + β * v)) := by
    have p1 := mul_le_mul_of_nonneg_right hK1b (mul_nonneg hv hv)
    have p2 := mul_le_mul_of_nonneg_right hK1b' (mul_nonneg hA hv)
    have p3 : 0 ≤ K1b * (α * A) ^ 2 := mul_nonneg hK1b0 (sq_nonneg _)
    linarith
  have d3 : K1b * ((α * A + β * v) * (α * A + β * v)) ≤ K1b * ((α * A + β * v) * m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfl hW0) hK1b0
  have c5 := mul_le_mul_of_nonneg_left (add_le_add c2 c4) (by linarith : (0 : ℝ) ≤ 4 * v)
  linarith

lemma sqsplit {η : ℝ} (hη : 0 < η) (X Y : ℝ) :
    (X + Y) ^ 2 ≤ (1 + 1 / η) * X ^ 2 + (1 + η) * Y ^ 2 := by
  have h : (1 + 1 / η) * X ^ 2 + (1 + η) * Y ^ 2 - (X + Y) ^ 2 = (X - η * Y) ^ 2 / η := by
    field_simp; ring
  have h0 : 0 ≤ (X - η * Y) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
  linarith

lemma fin2 {A v e α β K2 η m b VK T2 t k N : ℝ} (hN : 0 < N) (hA : 0 ≤ A) (hv : 0 ≤ v)
    (hT : T2 ≤ N * v) (he : 0 ≤ e) (ht0 : e ≤ t) (ht1 : t - e ≤ b)
    (hk0 : t ^ 2 ≤ k) (hk1 : k - t ^ 2 ≤ VK / N) (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η)
    (hfl : α * A + β * v ≤ m)
    (hK2' : (1 + 1 / η) * VK + 4 * (1 + η) * ((e + b) ^ 2 + VK / N) ≤ 4 * K2 * (α * β))
    (hK20 : 0 ≤ K2) :
    (1 + 1 / η) * A * (T2 * (k - t ^ 2)) + 4 * (1 + η) * (v * A) * k ≤
      K2 * (α * A + β * v) * m := by
  have hW0 : 0 ≤ α * A + β * v := add_nonneg (mul_nonneg hα.le hA) (mul_nonneg hβ.le hv)
  have c3 := tr_var_real hN hv hT hk0 hk1
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  have hη2 : 0 ≤ 1 + η := by linarith
  have ht2 : t ^ 2 ≤ (e + b) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have kb : k ≤ (e + b) ^ 2 + VK / N := by linarith
  have b1 : (1 + 1 / η) * A * (T2 * (k - t ^ 2)) ≤ (1 + 1 / η) * A * (VK * v) :=
    mul_le_mul_of_nonneg_left c3 (mul_nonneg hη1 hA)
  have b2 : 4 * (1 + η) * (v * A) * k ≤ 4 * (1 + η) * (v * A) * ((e + b) ^ 2 + VK / N) :=
    mul_le_mul_of_nonneg_left kb
      (mul_nonneg (mul_nonneg (by norm_num) hη2) (mul_nonneg hv hA))
  have b3 := mul_le_mul_of_nonneg_right hK2' (mul_nonneg hA hv)
  have am : 4 * (α * β) * (A * v) ≤ (α * A + β * v) * (α * A + β * v) := by
    nlinarith [sq_nonneg (α * A - β * v)]
  have b4 := mul_le_mul_of_nonneg_left am hK20
  have b5 : K2 * ((α * A + β * v) * (α * A + β * v)) ≤ K2 * ((α * A + β * v) * m) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfl hW0) hK20
  linarith

/-! ## Integrals on the sphere -/

lemma wQ_nonneg (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    0 ≤ wQ d a H x := by
  unfold wQ; exact integral_nonneg fun _ => sq_nonneg _

lemma int_kap_centered (n d : ℕ) (hn1 : 1 ≤ n) :
    ∫ x, (kap d x x - tG n d) ^ 2 ∂uniformSphere n = kk2 n d - tG n d ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  have ck : Continuous (fun x : Fin n → ℝ => kap d x x) := cont_kap_diag d
  have e : ∀ x : Fin n → ℝ, (kap d x x - tG n d) ^ 2 =
      kap d x x ^ 2 - 2 * tG n d * kap d x x + tG n d ^ 2 := fun x => by ring
  simp only [e]
  rw [integral_add (f := fun x : Fin n → ℝ => kap d x x ^ 2 - 2 * tG n d * kap d x x)
      (g := fun _ => tG n d ^ 2)
      ((sph_int hn1 (ck.pow 2)).sub ((sph_int hn1 ck).const_mul _)) (integrable_const _),
    integral_sub (f := fun x : Fin n → ℝ => kap d x x ^ 2)
      (g := fun x : Fin n → ℝ => 2 * tG n d * kap d x x)
      (sph_int hn1 (ck.pow 2)) ((sph_int hn1 ck).const_mul _), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold kk2
  have : ∫ x, kap d x x ∂uniformSphere n = tG n d := rfl
  rw [this]; ring

lemma int_kap_shift (n d : ℕ) (hn1 : 1 ≤ n) (e : ℝ) :
    ∫ x, (kap d x x - e) ∂uniformSphere n = tG n d - e := by
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  rw [integral_sub (f := fun x : Fin n → ℝ => kap d x x) (g := fun _ => e)
    (sph_int hn1 (cont_kap_diag d)) (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rfl

/-- A point of the sphere exists, so `e_d ≤ sM`. -/
lemma e_le_sM (n d : ℕ) (hn : 1 ≤ n) {M1 S2 B1 VK sM : ℝ} (hS : SphC n d M1 S2 B1 VK sM) :
    eD d ≤ sM := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨x, hx⟩ := (BstLean.Part29.uniformSphere_ae_sphere n).exists
  have h := hS.2.2.2.2.2.2.2.2 x hx
  exact h.1.trans h.2.1

set_option maxHeartbeats 1600000 in
/-- `E_x[(‖a‖² + 4‖H‖²κ(x,x)) w(x)] ≤ (K1a + K1b) · Wf · E_W V`. -/
lemma kernel_int_le (n d : ℕ) (hn : 1 ≤ n) {M1 S2 B1 VK sM α β K1a K1b : ℝ}
    (he : 0 ≤ eD d) (hα : 0 < α) (hβ : 0 < β)
    (hS : SphC n d M1 S2 B1 VK sM) (hQ : WQId n d)
    (hK1a : 1 ≤ K1a * α) (hK1a' : 4 * eD d ≤ K1a * β)
    (hK1b : 4 * (2 * (B1 / (n : ℝ)) * (sM ^ 2 + S2 / (n : ℝ)) + (sM - eD d) * VK) ≤ K1b * β ^ 2)
    (hK1b' : 2 * ((B1 / (n : ℝ)) * (sM + M1 / (n : ℝ))) ≤ K1b * (α * β)) (hK1b0 : 0 ≤ K1b)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (hwc : Continuous (wQ d a H))
    (hwm : ∫ x, wQ d a H x ∂uniformSphere n = ∫ W, VG a H W ∂stdGauss (WIdx n d))
    (hfl : Wf α β a H ≤ ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d)) :
    ∫ x, (nsq a + 4 * frobH H * kap d x x) * wQ d a H x ∂uniformSphere n ≤
      (K1a + K1b) * Wf α β a H * ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hesM := e_le_sM n d hn hS
  obtain ⟨ht0, ht1, hm0, hm1, hs0, hs1, hk0, hk1, hsph⟩ := hS
  unfold Wf at hfl ⊢
  set m := ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d) with hm
  set A := nsq a with hA
  set v := frobH H with hv
  set T := trH H with hT
  have hA0 : 0 ≤ A := nsq_nonneg a
  have hv0 : 0 ≤ v := frobH_nonneg H
  have hTle : T ^ 2 ≤ n * v := trH_sq_le H
  have ck : Continuous (fun x : Fin n → ℝ => kap d x x) := cont_kap_diag d
  set C := A * (sM + mm1 n d) + 2 * v * (sM ^ 2 + ss2 n d) with hC
  have hpt : ∀ᵐ x ∂uniformSphere n, (A + 4 * v * kap d x x) * wQ d a H x ≤
      (A + 4 * v * eD d) * wQ d a H x +
        4 * v * ((kap d x x - eD d) * C + (sM - eD d) * (T ^ 2 * (kap d x x - tG n d) ^ 2)) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    obtain ⟨h1, h2, h3, -⟩ := hsph x hx
    exact pt1 hA0 hv0 (sq_nonneg T) he h1 h2 h3 (integral_nonneg fun _ => sq_nonneg _)
      (hQ a H hH x)
  have iw := sph_int hn hwc
  have ike : Integrable (fun x : Fin n → ℝ => kap d x x - eD d) (uniformSphere n) :=
    sph_int hn (ck.sub continuous_const)
  have ik2 : Integrable (fun x : Fin n → ℝ => (kap d x x - tG n d) ^ 2) (uniformSphere n) :=
    sph_int hn ((ck.sub continuous_const).pow 2)
  have hRHS : ∫ x, ((A + 4 * v * eD d) * wQ d a H x +
      4 * v * ((kap d x x - eD d) * C + (sM - eD d) * (T ^ 2 * (kap d x x - tG n d) ^ 2)))
        ∂uniformSphere n =
      (A + 4 * v * eD d) * m + 4 * v * ((tG n d - eD d) * C +
        (sM - eD d) * (T ^ 2 * (kk2 n d - tG n d ^ 2))) := by
    rw [integral_add (f := fun x : Fin n → ℝ => (A + 4 * v * eD d) * wQ d a H x)
        (g := fun x : Fin n → ℝ => 4 * v * ((kap d x x - eD d) * C +
          (sM - eD d) * (T ^ 2 * (kap d x x - tG n d) ^ 2)))
        (iw.const_mul _) (((ike.mul_const _).add ((ik2.const_mul _).const_mul _)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_add (f := fun x : Fin n → ℝ => (kap d x x - eD d) * C)
        (g := fun x : Fin n → ℝ => (sM - eD d) * (T ^ 2 * (kap d x x - tG n d) ^ 2))
        (ike.mul_const _) ((ik2.const_mul _).const_mul _), integral_mul_const,
      integral_const_mul, integral_const_mul, hwm, int_kap_shift n d hn,
      int_kap_centered n d hn]
  have hLHSi : Integrable (fun x : Fin n → ℝ => (A + 4 * v * kap d x x) * wQ d a H x)
      (uniformSphere n) :=
    sph_int hn ((continuous_const.add (continuous_const.mul ck)).mul hwc)
  have hRHSi : Integrable (fun x : Fin n → ℝ => (A + 4 * v * eD d) * wQ d a H x +
      4 * v * ((kap d x x - eD d) * C + (sM - eD d) * (T ^ 2 * (kap d x x - tG n d) ^ 2)))
      (uniformSphere n) :=
    (iw.const_mul _).add (((ike.mul_const _).add ((ik2.const_mul _).const_mul _)).const_mul _)
  have hI := integral_mono_ae hLHSi hRHSi hpt
  rw [hRHS] at hI
  refine hI.trans ?_
  exact fin1 hnpos hA0 hv0 hTle he ht0 ht1 hm0 hm1 hs0 hs1 hk0 hk1 hesM hα hβ hfl hK1a hK1a'
    hK1b hK1b' hK1b0

set_option maxHeartbeats 1600000 in
/-- The first-chaos term: `E_x Σ_i r_i(x)² ≤ K2 · Wf · E_W V`. -/
lemma rT_int_le (n d : ℕ) (hn : 1 ≤ n) {M1 S2 B1 VK sM α β η K2 : ℝ}
    (he : 0 ≤ eD d) (hα : 0 < α) (hβ : 0 < β) (hη : 0 < η)
    (hS : SphC n d M1 S2 B1 VK sM)
    (hK2' : (1 + 1 / η) * VK + 4 * (1 + η) * ((eD d + B1 / (n : ℝ)) ^ 2 + VK / (n : ℝ)) ≤
      4 * K2 * (α * β)) (hK20 : 0 ≤ K2)
    (a : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hfl : Wf α β a H ≤ ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d)) :
    ∫ x, ∑ i, rT d a H i x ^ 2 ∂uniformSphere n ≤
      K2 * Wf α β a H * ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨ht0, ht1, hm0, hm1, hs0, hs1, hk0, hk1, hsph⟩ := hS
  unfold Wf at hfl ⊢
  set m := ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d) with hm
  set A := nsq a with hA
  set v := frobH H with hv
  set T := trH H with hT
  have hA0 : 0 ≤ A := nsq_nonneg a
  have hv0 : 0 ≤ v := frobH_nonneg H
  have hTle : T ^ 2 ≤ n * v := trH_sq_le H
  have ck : Continuous (fun x : Fin n → ℝ => kap d x x) := cont_kap_diag d
  have cki := cont_kap_int (n := n) d hn
  have hη1 : 0 ≤ 1 + 1 / η := by positivity
  have hη2 : 0 ≤ 1 + η := by linarith
  have hHa : ∑ i, (∑ k, H i k * a k) ^ 2 ≤ v * A := by
    rw [hv, hA]; unfold frobH nsq
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hpt : ∀ᵐ x ∂uniformSphere n, ∑ i, rT d a H i x ^ 2 ≤
      (1 + 1 / η) * A * (T ^ 2 * (kap d x x - tG n d) ^ 2) +
        4 * (1 + η) * (v * A) * kap d x x ^ 2 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    obtain ⟨h1, h2, h3, h4⟩ := hsph x hx
    set k1 := ∫ y, kap d x y ∂uniformSphere n with hk1def
    have hY : (kap d x x - k1) ^ 2 ≤ kap d x x ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hterm : ∀ i, rT d a H i x ^ 2 ≤
        (1 + 1 / η) * (a i ^ 2 * (T ^ 2 * (kap d x x - tG n d) ^ 2)) +
        (1 + η) * (4 * ((∑ k, H i k * a k) ^ 2 * (kap d x x - k1) ^ 2)) := by
      intro i
      unfold rT
      refine (sqsplit hη (a i * (T * (kap d x x - tG n d)))
        (2 * (∑ k, H i k * a k) * (kap d x x - k1))).trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    have esum : ∑ i, ((1 + 1 / η) * (a i ^ 2 * (T ^ 2 * (kap d x x - tG n d) ^ 2)) +
        (1 + η) * (4 * ((∑ k, H i k * a k) ^ 2 * (kap d x x - k1) ^ 2))) =
        (1 + 1 / η) * ((∑ i, a i ^ 2) * (T ^ 2 * (kap d x x - tG n d) ^ 2)) +
        (1 + η) * (4 * ((∑ i, (∑ k, H i k * a k) ^ 2) * (kap d x x - k1) ^ 2)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [esum]
    have s1 : (∑ i, (∑ k, H i k * a k) ^ 2) * (kap d x x - k1) ^ 2 ≤
        (v * A) * kap d x x ^ 2 :=
      mul_le_mul hHa hY (sq_nonneg _) (mul_nonneg hv0 hA0)
    have e : ∑ i, a i ^ 2 = A := rfl
    rw [e]
    have s2 := mul_le_mul_of_nonneg_left s1 hη2
    linarith
  have crT : Continuous (fun x : Fin n → ℝ => ∑ i, rT d a H i x ^ 2) := by
    refine continuous_finsetSum _ fun i _ => ?_
    unfold rT
    exact ((continuous_const.mul (continuous_const.mul (ck.sub continuous_const))).add
      (continuous_const.mul (ck.sub cki))).pow 2
  have ik2 : Integrable (fun x : Fin n → ℝ => (kap d x x - tG n d) ^ 2) (uniformSphere n) :=
    sph_int hn ((ck.sub continuous_const).pow 2)
  have ikk : Integrable (fun x : Fin n → ℝ => kap d x x ^ 2) (uniformSphere n) :=
    sph_int hn (ck.pow 2)
  have hI : ∫ x, ∑ i, rT d a H i x ^ 2 ∂uniformSphere n ≤
      ∫ x, ((1 + 1 / η) * A * (T ^ 2 * (kap d x x - tG n d) ^ 2) +
        4 * (1 + η) * (v * A) * kap d x x ^ 2) ∂uniformSphere n :=
    integral_mono_ae (sph_int hn crT)
      (((ik2.const_mul (T ^ 2)).const_mul ((1 + 1 / η) * A)).add
        (ikk.const_mul (4 * (1 + η) * (v * A)))) hpt
  rw [integral_add
      (f := fun x : Fin n → ℝ => (1 + 1 / η) * A * (T ^ 2 * (kap d x x - tG n d) ^ 2))
      (g := fun x : Fin n → ℝ => 4 * (1 + η) * (v * A) * kap d x x ^ 2)
      ((ik2.const_mul (T ^ 2)).const_mul ((1 + 1 / η) * A))
      (ikk.const_mul (4 * (1 + η) * (v * A))),
    integral_const_mul, integral_const_mul, integral_const_mul, int_kap_centered n d hn] at hI
  have hkk2 : ∫ x, kap d x x ^ 2 ∂uniformSphere n = kk2 n d := rfl
  rw [hkk2] at hI
  refine hI.trans ?_
  exact fin2 hnpos hA0 hv0 hTle he ht0 ht1 hk0 hk1 hα hβ hη hfl hK2' hK20

end BstLean.Part81.Num

namespace BstLean.Part81

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part78 (nsq frobH trH nsq_nonneg frobH_nonneg trH_sq_le sph_int)

set_option linter.unusedVariables false in
/-- **Mean bounds from sphere constants.** -/
theorem mb_of (n d : ℕ) (hn : 1 ≤ n) {M1 S2 B1 VK sM α β : ℝ}
    (he : 0 ≤ eD d) (hM1 : 0 ≤ M1) (hS2 : 0 ≤ S2) (hB1 : 0 ≤ B1) (hVK : 0 ≤ VK)
    (hS : SphC n d M1 S2 B1 VK sM) (hM : MeanIds n d)
    (hα : α ≤ eD d - M1 / (n : ℝ)) (hβ : β ≤ 2 * (eD d ^ 2 - S2 / (n : ℝ))) :
    MB n d α β M1 (2 * S2 + B1 ^ 2) (eD d + B1 / (n : ℝ))
      (VK + 2 * ((eD d + B1 / (n : ℝ)) ^ 2 + VK / (n : ℝ))) := by
  intro a H hH
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨ht0, ht1, hm0, hm1, hs0, hs1, hk0, hk1, -⟩ := hS
  obtain ⟨i1, i2, i3, hV, hE⟩ := hM a H hH
  have hA0 : 0 ≤ nsq a := nsq_nonneg a
  have hv0 : 0 ≤ frobH H := frobH_nonneg H
  have hTle : trH H ^ 2 ≤ n * frobH H := trH_sq_le H
  refine ⟨i1, i2, i3, ?_, ?_, ?_⟩
  · rw [hV]; unfold Wf
    exact Num.floor_real he hA0 hv0 (sq_nonneg _) ht0 hm1 hs1 hk0 hα hβ
  · rw [hE]
    exact Num.err_real hnpos hA0 hv0 hTle ht0 ht1 hm1 hs1
  · rw [hV]
    exact Num.upper_real hnpos he hA0 hv0 hTle ht0 ht1 hm0 hs0 hk0 hk1

set_option linter.unusedVariables false in
/-- **From the two kernel forms to the floor form.** -/
theorem varBoundW_of (n d : ℕ) (hn : 1 ≤ n)
    {M1 S2 B1 VK sM α β E2 UA Uv c c' η K1a K1b K2 : ℝ}
    (he : 0 ≤ eD d) (hM1 : 0 ≤ M1) (hS2 : 0 ≤ S2) (hB1 : 0 ≤ B1) (hVK : 0 ≤ VK)
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hη : 0 < η)
    (hS : SphC n d M1 S2 B1 VK sM) (hMB : MB n d α β M1 E2 UA Uv) (hQ : WQId n d)
    (hK : VarBoundK n d c) (hK2 : VarBoundK2 n d c c')
    (hK1a : 1 ≤ K1a * α) (hK1a' : 4 * eD d ≤ K1a * β) (hK1a0 : 0 ≤ K1a)
    (hK1b : 4 * (2 * (B1 / (n : ℝ)) * (sM ^ 2 + S2 / (n : ℝ)) + (sM - eD d) * VK) ≤ K1b * β ^ 2)
    (hK1b' : 2 * ((B1 / (n : ℝ)) * (sM + M1 / (n : ℝ))) ≤ K1b * (α * β)) (hK1b0 : 0 ≤ K1b)
    (hK2' : (1 + 1 / η) * VK + 4 * (1 + η) * ((eD d + B1 / (n : ℝ)) ^ 2 + VK / (n : ℝ)) ≤
      4 * K2 * (α * β)) (hK20 : 0 ≤ K2) :
    VarBoundW n d α β (1 / 2 * (c * (K1a + K1b)) + 1 / 2 * (c' * K2)) := by
  intro a H hH
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hwc, hwm, -⟩ := hK a H hH
  have hfl := (hMB a H hH).2.2.2.1
  have h1 := Num.kernel_int_le n d hn he hα hβ hS hQ hK1a hK1a' hK1b hK1b' hK1b0 a H hH hwc hwm
    hfl
  have h2 := Num.rT_int_le n d hn he hα hβ hη hS hK2' hK20 a H hfl
  refine (hK2 a H hH).trans ?_
  have hcn : 0 ≤ c / (n : ℝ) := div_nonneg hc hnpos.le
  have hcn' : 0 ≤ c' / (n : ℝ) := div_nonneg hc' hnpos.le
  have g1 := mul_le_mul_of_nonneg_left h1 hcn
  have g2 := mul_le_mul_of_nonneg_left h2 hcn'
  have e : (1 / 2 * (c * (K1a + K1b)) + 1 / 2 * (c' * K2)) / (n : ℝ) * Wf α β a H *
      ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d) =
      1 / 2 * (c / (n : ℝ) * ((K1a + K1b) * Wf α β a H *
        ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d))) +
      1 / 2 * (c' / (n : ℝ) * (K2 * Wf α β a H *
        ∫ W : WIdx n d → ℝ, VG a H W ∂stdGauss (WIdx n d))) := by
    ring
  rw [e]
  linarith

end BstLean.Part81

#print axioms BstLean.Part81.mb_of
#print axioms BstLean.Part81.varBoundW_of
