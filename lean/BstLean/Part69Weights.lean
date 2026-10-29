import BstLean.Part69Mom
import BstLean.Part61LemmaW_Kernel
import BstLean.Part56Weights

/-!
# Part 69: the surrogate weights at `d = k = 2` in closed form

* `cross69`: `E_Q (u₁·x)²(u₂·x)²` (polarization of `dir4_69`).
* The kernels at `d = 2`: `k₁(x,y) = x·y`, `k₂(x,y) = ((x·y)² + Σ x_i²y_i²)/2`.
* The six moments `E s²`, `E s⁴`, `E w`, `E s²w`, `E w²`, `E Σx_i⁴` (`w = Σ v_i² x_i²`).
* `weights69`: `w69 n K t v κ = wRK (surrRK n K t v) 2 v κ` at every key with `2l ≤ i`.
-/

namespace BstLean.Part69

open MeasureTheory
open BstLean.Part56
open BstLean.Part29 (uniformSphere)

variable {n : ℕ}

/-- The polarized fourth moment. -/
noncomputable def phi69 (n : ℕ) (a b c1 c2 N1 N2 G : ℝ) : ℝ :=
  b * c1 ^ 2 * c2 ^ 2 +
    (a - b) / ((n : ℝ) - 1) *
      (c1 ^ 2 * (N2 - c2 ^ 2) + c2 ^ 2 * (N1 - c1 ^ 2) + 4 * c1 * c2 * (G - c1 * c2)) +
    (1 - 2 * a + b) / (((n : ℝ) - 1) * ((n : ℝ) + 1)) *
      ((N1 - c1 ^ 2) * (N2 - c2 ^ 2) + 2 * (G - c1 * c2) ^ 2)

theorem surr_int69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f (surrRK n K t v) :=
  integrable_cont_sph56 (MomProg.surrRK_sphLaw (by omega) K t ht v) hf

private theorem lin4_69 {μ : Measure (Fin n → ℝ)} (f g h k : (Fin n → ℝ) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) (hk : Integrable k μ) :
    ∫ x, f x + g x - 2 * h x - 2 * k x ∂μ =
      ∫ x, f x ∂μ + ∫ x, g x ∂μ - 2 * ∫ x, h x ∂μ - 2 * ∫ x, k x ∂μ := by
  rw [integral_sub (f := fun x => f x + g x - 2 * h x) ((hf.add hg).sub (hh.const_mul 2))
      (hk.const_mul 2),
    integral_sub (f := fun x => f x + g x) (hf.add hg) (hh.const_mul 2),
    integral_add hf hg, integral_const_mul, integral_const_mul]

/-- **`E_Q (u₁·x)²(u₂·x)² = Φ`.** -/
theorem cross69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (u1 u2 : Fin n → ℝ) :
    ∫ x, (∑ i, u1 i * x i) ^ 2 * (∑ i, u2 i * x i) ^ 2 ∂surrRK n K t v =
      phi69 n (a69 n K t) (b69 n K t) (∑ i, u1 i * v i) (∑ i, u2 i * v i)
        (∑ i, u1 i ^ 2) (∑ i, u2 i ^ 2) (∑ i, u1 i * u2 i) := by
  have hpt : ∀ x : Fin n → ℝ, (∑ i, u1 i * x i) ^ 2 * (∑ i, u2 i * x i) ^ 2 =
      ((∑ i, (u1 + u2) i * x i) ^ 4 + (∑ i, (u1 - u2) i * x i) ^ 4 -
        2 * (∑ i, u1 i * x i) ^ 4 - 2 * (∑ i, u2 i * x i) ^ 4) / 12 := by
    intro x
    simp only [Pi.add_apply, Pi.sub_apply, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  simp_rw [hpt]
  have hI : ∀ u : Fin n → ℝ, Integrable (fun x : Fin n → ℝ => (∑ i, u i * x i) ^ 4)
      (surrRK n K t v) := fun u => surr_int69 hn K t ht v (by fun_prop)
  rw [integral_div, lin4_69 _ _ _ _ (hI _) (hI _) (hI _) (hI _),
    dir4_69 hn K t ht v hv, dir4_69 hn K t ht v hv, dir4_69 hn K t ht v hv,
    dir4_69 hn K t ht v hv]
  simp only [Pi.add_apply, Pi.sub_apply, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, add_sq, sub_sq]
  have h2 : ∑ i, 2 * u1 i * u2 i = 2 * ∑ i, u1 i * u2 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  unfold phi69
  field_simp
  ring

/-! ## The kernels at `d = 2` -/

theorem hval2_69 (u : Fin n → ℝ) :
    BstLean.Part58.Kappa.hval 2 u = ((∑ i, u i) ^ 2 + ∑ i, u i ^ 2) / 2 := by
  classical
  have he := BstLean.Part61.W.hval_euler 2 u
  have hd : ∀ i, MvPolynomial.eval u (MvPolynomial.pderiv i
      (MvPolynomial.hsymm (Fin n) ℝ 2)) = (∑ l, u l) + u i := by
    intro i
    rw [BstLean.Part58.Kappa.pderiv_hsymm_succ i 1, MvPolynomial.hsymm_one]
    simp [MvPolynomial.pderiv_X, Pi.single_apply]
  simp only [hd] at he
  have : ∑ i, u i * ((∑ l, u l) + u i) = (∑ i, u i) ^ 2 + ∑ i, u i ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sq]
  rw [this] at he
  push_cast at he
  linarith

theorem k2_69 (x y : Fin n → ℝ) :
    kJ 2 2 x y = ((∑ i, x i * y i) ^ 2 + ∑ i, x i ^ 2 * y i ^ 2) / 2 := by
  rw [BstLean.Part61.W.kJ_hval (d := 2) 2 le_rfl x y, hval2_69]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

theorem k1_69 (x y : Fin n → ℝ) : kJ 2 1 x y = ∑ i, x i * y i :=
  BstLean.Part56.kJ_one 2 (by norm_num) x y

/-- `s = v·x`, `w = Σ v_i² x_i²`, `Σ x_i⁴`. -/
noncomputable def sv69 (v x : Fin n → ℝ) : ℝ := ∑ i, v i * x i
noncomputable def wv69 (v x : Fin n → ℝ) : ℝ := ∑ i, v i ^ 2 * x i ^ 2
noncomputable def x4_69 (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 4

theorem beta1_69 (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    betaJ 2 1 v x = sv69 v x := by
  have hv' : ∑ i, v i * v i = 1 := by simpa [UnitV, sq] using hv
  unfold betaJ sv69
  rw [k1_69, k1_69, hv', div_one]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem kvv69 (v : Fin n → ℝ) (hv : UnitV v) : kJ 2 2 v v = (1 + q69 v) / 2 := by
  have hv' : ∑ i, v i * v i = 1 := by simpa [UnitV, sq] using hv
  rw [k2_69, hv']
  unfold q69
  congr 2
  · norm_num
  · exact Finset.sum_congr rfl fun i _ => by ring

theorem q69_nonneg (v : Fin n → ℝ) : 0 ≤ q69 v :=
  Finset.sum_nonneg fun i _ => by positivity

theorem beta2_69 (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    betaJ 2 2 v x = (sv69 v x ^ 2 + wv69 v x) / (1 + q69 v) := by
  unfold betaJ
  rw [kvv69 v hv, k2_69]
  have hq := q69_nonneg v
  unfold sv69 wv69
  have e1 : ∑ i, x i * v i = ∑ i, v i * x i := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, x i ^ 2 * v i ^ 2 = ∑ i, v i ^ 2 * x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  field_simp

theorem tau69 (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    tauR 2 v x = 3 / 2 - sv69 v x ^ 2 + x4_69 x / 2 -
      (sv69 v x ^ 2 + wv69 v x) ^ 2 / (2 * (1 + q69 v)) := by
  have hv' : ∑ i, v i * v i = 1 := by simpa [UnitV, sq] using hv
  have hx' : ∑ i, x i * x i = 1 := by simpa [sq] using hx
  unfold tauR KR
  rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.sum_pair (by norm_num)]
  rw [k1_69, k1_69, k1_69, hv', hx', kvv69 v hv, k2_69, k2_69]
  have hq := q69_nonneg v
  unfold sv69 wv69 x4_69
  have e1 : ∑ i, x i * v i = ∑ i, v i * x i := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, x i ^ 2 * v i ^ 2 = ∑ i, v i ^ 2 * x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, x i ^ 2 * x i ^ 2 = ∑ i, x i ^ 4 := Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e3, hx']
  field_simp
  ring

/-! ## The six moments -/

/-- The coordinate vector `e_i`. -/
def ev69 (i : Fin n) : Fin n → ℝ := fun l => if l = i then 1 else 0

@[simp] theorem ev69_dot (i : Fin n) (x : Fin n → ℝ) : ∑ l, ev69 i l * x l = x i := by
  simp [ev69]

@[simp] theorem ev69_sq (i : Fin n) : ∑ l, ev69 i l ^ 2 = 1 := by simp [ev69]

@[simp] theorem ev69_ev (i j : Fin n) : ∑ l, ev69 i l * ev69 j l = if i = j then 1 else 0 := by
  simp [ev69, eq_comm]

theorem unit_dot69 (v : Fin n → ℝ) (hv : UnitV v) : ∑ i, v i * v i = 1 := by
  simpa [UnitV, sq] using hv

theorem psum69 (v : Fin n → ℝ) (hv : UnitV v) (A B C D : ℝ) :
    ∑ i, (A * v i ^ 6 + B * v i ^ 4 + C * v i ^ 2 + D) = A * r69 v + B * q69 v + C + n * D := by
  have hv' : ∑ i, v i ^ 2 = 1 := hv
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, r69, q69]
  ring

theorem mom_ii69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (i : Fin n) :
    ∫ x, x i ^ 2 ∂surrRK n K t v =
      v i ^ 2 * a69 n K t + (1 - v i ^ 2) * (1 - a69 n K t) / ((n : ℝ) - 1) := by
  have := dir2_69 hn K t ht v hv (ev69 i)
  simp only [ev69_dot, ev69_sq] at this
  rw [this]
  try simp [ev69]

theorem mom_cross69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (u1 u2 : Fin n → ℝ) (i j : Fin n) (hu1 : u1 = ev69 i) (hu2 : u2 = ev69 j) :
    ∫ x, x i ^ 2 * x j ^ 2 ∂surrRK n K t v =
      phi69 n (a69 n K t) (b69 n K t) (v i) (v j) 1 1 (if i = j then 1 else 0) := by
  have := cross69 hn K t ht v hv u1 u2
  subst hu1 hu2
  simp only [ev69_dot, ev69_sq, ev69_ev] at this
  rw [this]
  congr 2 <;> simp [ev69]

theorem mom_si69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (i : Fin n) :
    ∫ x, sv69 v x ^ 2 * x i ^ 2 ∂surrRK n K t v =
      phi69 n (a69 n K t) (b69 n K t) 1 (v i) 1 1 (v i) := by
  have := cross69 hn K t ht v hv v (ev69 i)
  simp only [ev69_dot, ev69_sq] at this
  unfold sv69
  rw [this, unit_dot69 v hv, show (∑ l, v l ^ 2) = 1 from hv]
  congr 1 <;> simp [ev69]

theorem mom_i4_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (i : Fin n) :
    ∫ x, x i ^ 4 ∂surrRK n K t v =
      v i ^ 4 * b69 n K t + 6 * v i ^ 2 * (1 - v i ^ 2) * (a69 n K t - b69 n K t) / ((n : ℝ) - 1) +
        3 * (1 - v i ^ 2) ^ 2 * (1 - 2 * a69 n K t + b69 n K t) /
          (((n : ℝ) - 1) * ((n : ℝ) + 1)) := by
  have := dir4_69 hn K t ht v hv (ev69 i)
  simp only [ev69_dot, ev69_sq] at this
  rw [this]
  try simp [ev69]

theorem I_s2_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, sv69 v x ^ 2 ∂surrRK n K t v = a69 n K t := by
  unfold sv69
  rw [dir2_69 hn K t ht v hv v, unit_dot69 v hv, show (∑ l, v l ^ 2) = 1 from hv]
  ring

theorem I_s4_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, sv69 v x ^ 4 ∂surrRK n K t v = b69 n K t := by
  unfold sv69
  rw [dir4_69 hn K t ht v hv v, unit_dot69 v hv, show (∑ l, v l ^ 2) = 1 from hv]
  ring

theorem I_w69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, wv69 v x ∂surrRK n K t v = Ew69 n (a69 n K t) (q69 v) := by
  unfold wv69
  rw [integral_finset_sum _ (fun i _ => (surr_int69 hn K t ht v (by fun_prop)))]
  simp only [integral_const_mul, mom_ii69 hn K t ht v hv]
  set a := a69 n K t
  set m := (n : ℝ) - 1
  have hpt : ∀ i, v i ^ 2 * (v i ^ 2 * a + (1 - v i ^ 2) * (1 - a) / m) =
      0 * v i ^ 6 + (a - (1 - a) / m) * v i ^ 4 + ((1 - a) / m) * v i ^ 2 + 0 := by
    intro i; ring
  simp only [hpt, psum69 v hv]
  unfold Ew69; ring

theorem I_sw69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, sv69 v x ^ 2 * wv69 v x ∂surrRK n K t v = Esw69 n (a69 n K t) (b69 n K t) (q69 v) := by
  unfold wv69
  simp only [Finset.mul_sum]
  have hpt : ∀ x : Fin n → ℝ, ∀ i, sv69 v x ^ 2 * (v i ^ 2 * x i ^ 2) =
      v i ^ 2 * (sv69 v x ^ 2 * x i ^ 2) := fun x i => by ring
  simp only [hpt]
  rw [integral_finset_sum _ (fun i _ => (surr_int69 hn K t ht v (by unfold sv69; fun_prop)))]
  simp only [integral_const_mul, mom_si69 hn K t ht v hv]
  set a := a69 n K t
  set b := b69 n K t
  set m := (n : ℝ) - 1
  set m2 := ((n : ℝ) - 1) * ((n : ℝ) + 1)
  have hpt2 : ∀ i, v i ^ 2 * phi69 n a b 1 (v i) 1 1 (v i) =
      0 * v i ^ 6 + (b - (a - b) / m) * v i ^ 4 + ((a - b) / m) * v i ^ 2 + 0 := by
    intro i; unfold phi69; ring
  simp only [hpt2, psum69 v hv]
  unfold Esw69; ring

theorem I_x4_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, x4_69 x ∂surrRK n K t v = Eq4_69 n (a69 n K t) (b69 n K t) (q69 v) := by
  unfold x4_69
  rw [integral_finset_sum _ (fun i _ => (surr_int69 hn K t ht v (by fun_prop)))]
  simp only [mom_i4_69 hn K t ht v hv]
  set a := a69 n K t
  set b := b69 n K t
  set m := (n : ℝ) - 1
  set m2 := ((n : ℝ) - 1) * ((n : ℝ) + 1)
  have hpt : ∀ i, v i ^ 4 * b + 6 * v i ^ 2 * (1 - v i ^ 2) * (a - b) / m +
      3 * (1 - v i ^ 2) ^ 2 * (1 - 2 * a + b) / m2 =
      0 * v i ^ 6 + (b - 6 * (a - b) / m + 3 * (1 - 2 * a + b) / m2) * v i ^ 4 +
        (6 * (a - b) / m - 6 * (1 - 2 * a + b) / m2) * v i ^ 2 + 3 * (1 - 2 * a + b) / m2 := by
    intro i; ring
  simp only [hpt, psum69 v hv]
  unfold Eq4_69
  simp only [m, m2]
  ring

theorem I_w2_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, wv69 v x ^ 2 ∂surrRK n K t v =
      Ew2_69 n (a69 n K t) (b69 n K t) (q69 v) (r69 v) := by
  have hsq : ∀ x : Fin n → ℝ, wv69 v x ^ 2 =
      ∑ i, ∑ j, v i ^ 2 * v j ^ 2 * (x i ^ 2 * x j ^ 2) := by
    intro x
    unfold wv69
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hsq]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => (surr_int69 hn K t ht v (by fun_prop))))]
  simp only [fun i => integral_finset_sum (μ := surrRK n K t v) Finset.univ
    (fun j _ => (surr_int69 hn K t ht v (f := fun x : Fin n → ℝ =>
      v i ^ 2 * v j ^ 2 * (x i ^ 2 * x j ^ 2)) (by fun_prop)))]
  simp only [integral_const_mul,
    fun i j => mom_cross69 hn K t ht v hv (ev69 i) (ev69 j) i j rfl rfl]
  set a := a69 n K t
  set b := b69 n K t
  set β := (a - b) / ((n : ℝ) - 1)
  set γ := (1 - 2 * a + b) / (((n : ℝ) - 1) * ((n : ℝ) + 1))
  have hpt : ∀ i j : Fin n, v i ^ 2 * v j ^ 2 *
      phi69 n a b (v i) (v j) 1 1 (if i = j then 1 else 0) =
      (((b - 6 * β + 3 * γ) * v i ^ 4 + (β - γ) * v i ^ 2) * v j ^ 4 +
        ((β - γ) * v i ^ 4 + γ * v i ^ 2) * v j ^ 2) +
        (if i = j then (4 * β - 4 * γ) * v i ^ 6 + 2 * γ * v i ^ 4 else 0) := by
    intro i j
    unfold phi69
    split_ifs with h
    · subst h; simp only [β, γ]; ring
    · simp only [β, γ]; ring
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.mul_sum]
  have hv' : ∑ i, v i ^ 2 = 1 := hv
  have hq : ∑ i, v i ^ 4 = q69 v := rfl
  simp only [hq, hv', mul_one]
  have hr : ∑ i, v i ^ 6 = r69 v := rfl
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, hv', hr]
  unfold Ew2_69
  simp only [β, γ]
  ring

/-! ## The weights -/

private theorem lin_69 {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ] (C c1 c2 c3 c4 c5 : ℝ)
    (f1 f2 f3 f4 f5 : (Fin n → ℝ) → ℝ) (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) :
    ∫ x, (C + c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x + c5 * f5 x) ∂μ =
      C + c1 * ∫ x, f1 x ∂μ + c2 * ∫ x, f2 x ∂μ + c3 * ∫ x, f3 x ∂μ + c4 * ∫ x, f4 x ∂μ +
        c5 * ∫ x, f5 x ∂μ := by
  have hC : Integrable (fun _ : Fin n → ℝ => C) μ := integrable_const C
  rw [integral_add (f := fun x => C + c1 * f1 x + c2 * f2 x + c3 * f3 x + c4 * f4 x)
      ((((hC.add (h1.const_mul c1)).add (h2.const_mul c2)).add (h3.const_mul c3)).add
        (h4.const_mul c4)) (h5.const_mul c5),
    integral_add (f := fun x => C + c1 * f1 x + c2 * f2 x + c3 * f3 x)
      (((hC.add (h1.const_mul c1)).add (h2.const_mul c2)).add (h3.const_mul c3))
        (h4.const_mul c4),
    integral_add (f := fun x => C + c1 * f1 x + c2 * f2 x)
      ((hC.add (h1.const_mul c1)).add (h2.const_mul c2)) (h3.const_mul c3),
    integral_add (f := fun x => C + c1 * f1 x) (hC.add (h1.const_mul c1)) (h2.const_mul c2),
    integral_add hC (h1.const_mul c1)]
  simp [integral_const_mul]

theorem antipodal_odd69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x, f x ∂surrRK n K t v = 0 := by
  have hA := BstLean.Part50.binghamKA_antipodal (by omega : 1 ≤ n) K (rk1 t v)
    (MomProg.rk1_psd t ht v)
  have h := hA.neg
  have e : ∫ x, f x ∂surrRK n K t v = ∫ x, f (-x) ∂surrRK n K t v := by
    conv_lhs => rw [← show (surrRK n K t v).map (fun x => -x) = surrRK n K t v from h]
    rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
  have e2 : ∫ x, f (-x) ∂surrRK n K t v = -∫ x, f x ∂surrRK n K t v := by
    simp only [hodd, integral_neg]
  linarith

theorem prod_word69 {m : ℕ} (w : Fin m → Fin 3) (f : ℕ → ℝ) :
    ∏ r, f (w r) = f 0 ^ (Finset.univ.filter fun r => w r = 0).card *
      f 1 ^ (Finset.univ.filter fun r => w r = 1).card *
      f 2 ^ (Finset.univ.filter fun r => w r = 2).card := by
  rw [← Finset.prod_fiberwise' Finset.univ w (fun j : Fin 3 => f j)]
  simp only [Finset.prod_const, Fin.prod_univ_three]
  rfl

theorem card_word69 {m : ℕ} (w : Fin m → Fin 3) :
    (Finset.univ.filter fun r => w r = 0).card + (Finset.univ.filter fun r => w r = 1).card +
      (Finset.univ.filter fun r => w r = 2).card = m := by
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := w)
    (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three] at this
  omega

theorem I_beta2_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, betaJ 2 2 v x ∂surrRK n K t v = A69 n (a69 n K t) (q69 v) := by
  have := (MomProg.surrRK_sphLaw (by omega : 1 ≤ n) K t ht v).prob
  have hpt : ∀ x, betaJ 2 2 v x = 0 + 1 / (1 + q69 v) * sv69 v x ^ 2 +
      1 / (1 + q69 v) * wv69 v x + 0 * 0 + 0 * 0 + 0 * 0 := by
    intro x; rw [beta2_69 v hv]; ring
  simp only [hpt]
  have hI0 : Integrable (fun _ : Fin n → ℝ => (0 : ℝ)) (surrRK n K t v) := integrable_const _
  rw [lin_69 0 _ _ 0 0 0 (fun x => sv69 v x ^ 2) (fun x => wv69 v x) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (surr_int69 hn K t ht v (by unfold sv69; fun_prop))
    (surr_int69 hn K t ht v (by unfold wv69; fun_prop)) hI0 hI0 hI0,
    I_s2_69 hn K t ht v hv, I_w69 hn K t ht v hv]
  unfold A69; ring

theorem I_beta22_69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, betaJ 2 2 v x ^ 2 ∂surrRK n K t v =
      H69 n (a69 n K t) (b69 n K t) (q69 v) (r69 v) := by
  have := (MomProg.surrRK_sphLaw (by omega : 1 ≤ n) K t ht v).prob
  have hpt : ∀ x, betaJ 2 2 v x ^ 2 = 0 + 1 / (1 + q69 v) ^ 2 * sv69 v x ^ 4 +
      2 / (1 + q69 v) ^ 2 * (sv69 v x ^ 2 * wv69 v x) + 1 / (1 + q69 v) ^ 2 * wv69 v x ^ 2 +
        0 * 0 + 0 * 0 := by
    intro x; rw [beta2_69 v hv, div_pow]; ring
  simp only [hpt]
  have hI0 : Integrable (fun _ : Fin n → ℝ => (0 : ℝ)) (surrRK n K t v) := integrable_const _
  rw [lin_69 0 _ _ _ 0 0 (fun x => sv69 v x ^ 4) (fun x => sv69 v x ^ 2 * wv69 v x)
    (fun x => wv69 v x ^ 2) (fun _ => 0) (fun _ => 0)
    (surr_int69 hn K t ht v (by unfold sv69; fun_prop))
    (surr_int69 hn K t ht v (by unfold sv69 wv69; fun_prop))
    (surr_int69 hn K t ht v (by unfold wv69; fun_prop)) hI0 hI0,
    I_s4_69 hn K t ht v hv, I_sw69 hn K t ht v hv, I_w2_69 hn K t ht v hv]
  unfold H69 Esq69; ring

theorem I_tau69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v) :
    ∫ x, tauR 2 v x ∂surrRK n K t v = R69 n (a69 n K t) (b69 n K t) (q69 v) (r69 v) := by
  have hS := MomProg.surrRK_sphLaw (by omega : 1 ≤ n) K t ht v
  have := hS.prob
  set D := 2 * (1 + q69 v)
  have hae : (fun x => tauR 2 v x) =ᵐ[surrRK n K t v] fun x =>
      3 / 2 + (-1) * sv69 v x ^ 2 + (1 / 2) * x4_69 x + (-1 / D) * sv69 v x ^ 4 +
        (-2 / D) * (sv69 v x ^ 2 * wv69 v x) + (-1 / D) * wv69 v x ^ 2 := by
    filter_upwards [hS.sphere] with x hx
    rw [tau69 v hv x hx]; simp only [D]; ring
  rw [integral_congr_ae hae,
    lin_69 _ _ _ _ _ _ (fun x => sv69 v x ^ 2) (fun x => x4_69 x) (fun x => sv69 v x ^ 4)
    (fun x => sv69 v x ^ 2 * wv69 v x) (fun x => wv69 v x ^ 2)
    (surr_int69 hn K t ht v (by unfold sv69; fun_prop))
    (surr_int69 hn K t ht v (by unfold x4_69; fun_prop))
    (surr_int69 hn K t ht v (by unfold sv69; fun_prop))
    (surr_int69 hn K t ht v (by unfold sv69 wv69; fun_prop))
    (surr_int69 hn K t ht v (by unfold wv69; fun_prop)),
    I_s2_69 hn K t ht v hv, I_x4_69 hn K t ht v hv, I_s4_69 hn K t ht v hv,
    I_sw69 hn K t ht v hv, I_w2_69 hn K t ht v hv]
  unfold R69 Esq69; simp only [D]; ring

/-- `E_Q[s^{c₁} β₂^{c₂}] = momC69 …` for `c₁ + c₂ ≤ 2`. -/
theorem I_mom69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (c1 c2 : ℕ) (hc : c1 + c2 ≤ 2) :
    ∫ x, sv69 v x ^ c1 * betaJ 2 2 v x ^ c2 ∂surrRK n K t v =
      momC69 n (a69 n K t) (b69 n K t) (q69 v) (r69 v) c1 c2 := by
  have := (MomProg.surrRK_sphLaw (by omega : 1 ≤ n) K t ht v).prob
  have hb2 : ∀ x, betaJ 2 2 v (-x) = betaJ 2 2 v x := by
    intro x; rw [beta2_69 v hv, beta2_69 v hv]; unfold sv69 wv69; simp
  have hs : ∀ x, sv69 v (-x) = - sv69 v x := by intro x; unfold sv69; simp
  have hcb : Continuous (fun x => betaJ 2 2 v x) := by
    have : (fun x => betaJ 2 2 v x) = fun x => (sv69 v x ^ 2 + wv69 v x) / (1 + q69 v) :=
      funext (beta2_69 v hv)
    rw [this]; unfold sv69 wv69; fun_prop
  have hcs : Continuous (fun x => sv69 v x) := by unfold sv69; fun_prop
  have hc1 : c1 ≤ 2 := by omega
  have hc2 : c2 ≤ 2 := by omega
  interval_cases c1 <;> interval_cases c2 <;> simp only [momC69] <;> norm_num <;>
    first
    | omega
    | exact I_beta2_69 hn K t ht v hv
    | exact I_beta22_69 hn K t ht v hv
    | exact I_s2_69 hn K t ht v hv
    | exact antipodal_odd69 hn K t ht v hcs hs
    | exact antipodal_odd69 hn K t ht v (hcs.mul hcb) (fun x => by rw [hs, hb2]; ring)
    | simp

theorem DD2_69 : BstLean.Part36.DD n 2 = (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  rw [BstLean.Part36.DD_eq, Nat.cast_choose_two]
  push_cast; ring

/-- **The weight formulas.** At every key `(i, l, j⃗)` with `2l ≤ i` (the keys that `pg` reads),
the surrogate weight `wRK (surrRK n K t v) 2 v κ` equals the closed form `w69 n K t v κ`, a
rational function of `a = E_Q s²`, `b = E_Q s⁴`, `q = Σ v_i⁴`, `r = Σ v_i⁶` and `n`. -/
theorem weights69 (hn : 2 ≤ n) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (v : Fin n → ℝ) (hv : UnitV v)
    (κ : KeyRK 2 2) (hκ : 2 * (κ.1.2 : ℕ) ≤ (κ.1.1 : ℕ)) :
    w69 n K t v κ = wRK (surrRK n K t v) 2 v κ := by
  have hP := (MomProg.surrRK_sphLaw (by omega : 1 ≤ n) K t ht v).prob
  obtain ⟨⟨i, l⟩, w⟩ := κ
  simp only at hκ
  have hi := i.isLt
  have hcw := card_word69 w
  have hprod : ∀ x, ∏ r, betaJ 2 (w r : ℕ) v x =
      sv69 v x ^ cnt69 (⟨(i, l), w⟩ : KeyRK 2 2) 1 *
        betaJ 2 2 v x ^ cnt69 (⟨(i, l), w⟩ : KeyRK 2 2) 2 := by
    intro x
    rw [prod_word69 w (fun j => betaJ 2 j v x)]
    rw [MomProg.betaJ_zero (d := 2) v hv x, beta1_69 v hv x, one_pow, one_mul]
    rfl
  unfold w69 wF69 wRK
  simp only [hprod]
  by_cases hl : (l : ℕ) = 0
  · rw [if_pos hl]
    simp only [hl, pow_zero, one_mul, mul_one]
    rw [I_mom69 hn K t ht v hv _ _ (by dsimp only [cnt69]; dsimp only at hcw; omega)]
    unfold wickC
    have := Nat.factorial_pos (i : ℕ)
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul, Nat.sub_zero,
      mul_zero]
    rw [div_self (by positivity), one_mul]
  · have hl1 : (l : ℕ) = 1 := by omega
    have hi2 : (i : ℕ) = 2 := by omega
    have hc1 : cnt69 (⟨(i, l), w⟩ : KeyRK 2 2) 1 = 0 := by dsimp only [cnt69]; dsimp only at hcw; omega
    have hc2 : cnt69 (⟨(i, l), w⟩ : KeyRK 2 2) 2 = 0 := by dsimp only [cnt69]; dsimp only at hcw; omega
    rw [if_neg hl, if_pos ⟨hi2, hl1⟩, hc1, hc2, hl1, hi2]
    simp only [pow_zero, mul_one, pow_one]
    rw [I_tau69 hn K t ht v hv, MomProg.sg_sq (by omega), DD2_69]
    unfold wickC
    norm_num
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    field_simp

end BstLean.Part69
