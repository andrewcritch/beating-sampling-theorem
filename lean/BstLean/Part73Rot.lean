import BstLean.Part73Orth
import BstLean.Part72Sub

/-!
# Part 73: directional moments of the two-subspace tilt, and the rotated tilt

Coordinates `Fin (b + r)`, `n = b + r`, `b + r ≤ L·b`, `b + r ≤ L·r`.

* `sphere_dirm_le`: `E_{σ_m} (a·y)^{2p} ≤ (2p−1)!!·‖a‖^{2p}/m^p` (Part 56's exact formula).
* `f1_dirm`: `E_{f1Tilt} (w·x)^{2p} ≤ (2p−1)!!·L^p/n^p` for every unit `w`, every real `c`
  (block uniformity, `(w·x)² ≤ (w_V·ξ)² + (w_⊥·η)²` on the sphere, and convexity of `t^p` with
  the weights `‖w_V‖²`, `‖w_⊥‖²`).
* `rot_dirm`: the same bound for `(f1Tilt b r c).map (O ·)`, `O` orthogonal (the bound is
  orientation free).
* `p4_of_dirm`: directional moments of order `4q` bound `E p₄^q` (coordinates are directions).
* `rot_good`: `Good72 n d k ((f1Tilt b r c).map (O ·)) (wG L) (Fov d L) L`,
  `wG L i = (8i−1)!!·L^{4i}`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part73

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (phiSq)
open BstLean.Part53 (c0 p4 unitF53 radF53)
open BstLean.Part72 (f1Tilt f1Z xV xP UV sum_split measurable_xV measurable_xP f1_sph
  f1_blockV f1_blockP sphere_integrable int_unit_comp rad_smul_unit good_of_ov Good72 Fov Mean
  f1_mean_zero)

private lemma sum_sq_nonneg {ι : Type} [Fintype ι] (z : ι → ℝ) : 0 ≤ ∑ j, z j ^ 2 :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma doubleFact_pos (p : ℕ) : (0 : ℝ) < ((2 * p - 1).doubleFactorial : ℝ) := by
  exact_mod_cast Nat.doubleFactorial_pos _

/-- `E_{σ_m} (a·y)^{2p} ≤ (2p−1)!!·‖a‖^{2p}/m^p`, `p ≥ 1`. -/
theorem sphere_dirm_le {m : ℕ} (hm : 1 ≤ m) (a : Fin m → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ∫ y, (∑ j, a j * y j) ^ (2 * p) ∂uniformSphere m ≤
      ((2 * p - 1).doubleFactorial : ℝ) * (∑ j, a j ^ 2) ^ p / (m : ℝ) ^ p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set s := ∑ j, a j ^ 2 with hs
  rcases eq_or_lt_of_le (sum_sq_nonneg a) with h0 | hpos
  · have ha : a = 0 := by
      funext j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).mp h0.symm j
        (Finset.mem_univ j)
      simpa using this
    subst ha
    have hp0 : 2 * p ≠ 0 := by omega
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_pow hp0, integral_zero]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (Nat.cast_nonneg _)
    apply pow_nonneg
    rw [hs]; exact sum_sq_nonneg _
  set v : Fin m → ℝ := fun j => a j / Real.sqrt s
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
  have hv : BstLean.Part56.UnitV v := by
    unfold BstLean.Part56.UnitV
    simp only [v, div_pow, ← Finset.sum_div]
    rw [Real.sq_sqrt hpos.le]
    exact div_self hpos.ne'
  have hav : ∀ y : Fin m → ℝ, (∑ j, a j * y j) ^ (2 * p) = s ^ p * (∑ j, v j * y j) ^ (2 * p) := by
    intro y
    have : ∑ j, a j * y j = Real.sqrt s * ∑ j, v j * y j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      simp only [v]; field_simp
    rw [this, mul_pow, pow_mul, Real.sq_sqrt hpos.le]
  simp_rw [hav]
  rw [integral_const_mul, BstLean.Part56.MomProg.sphere_directional_moment hm v hv p]
  have hg : BstLean.Part29.gaussMom (2 * p) = ((2 * p - 1).doubleFactorial : ℝ) := by
    unfold BstLean.Part29.gaussMom; simp
  rw [hg]
  have hrho : (m : ℝ) ^ p ≤ BstLean.Part36.rhoD (m : ℝ) p := by
    unfold BstLean.Part36.rhoD
    calc (m : ℝ) ^ p = ∏ _j ∈ Finset.range p, (m : ℝ) := by simp
      _ ≤ ∏ j ∈ Finset.range p, ((m : ℝ) + 2 * j) := by
        apply Finset.prod_le_prod₀ (fun _ _ => hmR.le) (fun j _ => by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith)
  have hmp : (0 : ℝ) < (m : ℝ) ^ p := by positivity
  rw [mul_div_assoc', mul_comm (s ^ p)]
  rw [div_le_div_iff₀ (lt_of_lt_of_le hmp hrho) hmp]
  have hD := doubleFact_pos p
  have := pow_pos hpos p
  nlinarith [mul_le_mul_of_nonneg_left hrho (le_of_lt (mul_pos hD this))]

private lemma rad_sq' {ι : Type} [Fintype ι] (z : ι → ℝ) : radF53 z ^ 2 = ∑ i, z i ^ 2 :=
  Real.sq_sqrt (sum_sq_nonneg z)

private lemma dot_unit' {ι : Type} [Fintype ι] (w z : ι → ℝ) :
    ∑ j, w j * z j = radF53 z * ∑ j, w j * unitF53 z j := by
  conv_lhs => rw [← rad_smul_unit z]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

/-- Convexity of `t^p` with weights `s`, `t`; the degenerate weights are handled by `κ = 0`. -/
private lemma split_pow {p : ℕ} (hp : 1 ≤ p) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) :
    ∃ κV κP : ℝ, 0 ≤ κV ∧ 0 ≤ κP ∧ κV * s ^ p ≤ s ∧ κP * t ^ p ≤ t ∧
      ∀ a e : ℝ, 0 ≤ a → 0 ≤ e → (s = 0 → a = 0) → (t = 0 → e = 0) →
        (a + e) ^ p ≤ κV * a ^ p + κP * e ^ p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rcases eq_or_lt_of_le hs with h0 | hs0
  · have ht1 : t = 1 := by linarith
    refine ⟨0, 1, le_rfl, zero_le_one, by simp [← h0], by simp [ht1], ?_⟩
    intro a e _ _ ha _
    rw [ha h0.symm]; simp
  rcases eq_or_lt_of_le ht with h0 | ht0
  · have hs1 : s = 1 := by linarith
    refine ⟨1, 0, zero_le_one, le_rfl, by simp [hs1], by simp [← h0], ?_⟩
    intro a e _ _ _ he
    rw [he h0.symm]; simp
  refine ⟨1 / s ^ q, 1 / t ^ q, by positivity, by positivity, ?_, ?_, ?_⟩
  · rw [pow_succ]; field_simp; exact le_refl _
  · rw [pow_succ]; field_simp; exact le_refl _
  · intro a e ha he _ _
    have h := (convexOn_pow (q + 1)).2 (x := a / s) (y := e / t)
      (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity)) hs ht hst
    simp only [smul_eq_mul] at h
    rw [mul_div_cancel₀ _ hs0.ne', mul_div_cancel₀ _ ht0.ne'] at h
    refine h.trans (le_of_eq ?_)
    rw [div_pow, div_pow, pow_succ s, pow_succ t]
    field_simp

private lemma dot_zero_of {m : ℕ} (a : Fin m → ℝ) (h : ∑ j, a j ^ 2 = 0) (y : Fin m → ℝ) :
    ∑ j, a j * y j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).mp h j
    (Finset.mem_univ j)
  have : a j = 0 := by simpa using this
  rw [this, zero_mul]

variable {b r : ℕ}

/-- **Directional moments of every order for the two-subspace tilt**, uniformly in `c`. -/
theorem f1_dirm (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (w : Fin (b + r) → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (p : ℕ) (hp : 1 ≤ p) :
    ∫ x, (∑ i, w i * x i) ^ (2 * p) ∂f1Tilt b r c ≤
      ((2 * p - 1).doubleFactorial : ℝ) * L ^ p / ((b + r : ℕ) : ℝ) ^ p := by
  have hbr : 1 ≤ b + r := by omega
  have hsph := f1_sph (b := b) (r := r) hbr c
  let := hsph.prob
  let wV : Fin b → ℝ := xV w
  let wP : Fin r → ℝ := xP w
  let GV : (Fin b → ℝ) → ℝ := fun y => ((∑ j, wV j * y j) ^ 2) ^ p
  let GP : (Fin r → ℝ) → ℝ := fun y => ((∑ j, wP j * y j) ^ 2) ^ p
  have hGV : Continuous GV := by fun_prop
  have hGP : Continuous GP := by fun_prop
  have hsplit : ∑ j, wV j ^ 2 + ∑ j, wP j ^ 2 = 1 := by
    have hs := sum_split (fun t => t ^ 2) w
    try simp only at hs
    rw [hw] at hs
    exact hs.symm
  have sV := sum_sq_nonneg wV
  have sP := sum_sq_nonneg wP
  obtain ⟨κV, κP, hκV, hκP, hκVs, hκPs, hκ⟩ := split_pow hp sV sP hsplit
  have hpt : ∀ᵐ x ∂f1Tilt b r c, (∑ i, w i * x i) ^ (2 * p) ≤
      κV * GV (unitF53 (xV x)) + κP * GP (unitF53 (xP x)) := by
    filter_upwards [hsph.sphere] with x hx
    have hs : ∑ i, w i * x i = ∑ j, wV j * xV x j + ∑ j, wP j * xP x j := by
      rw [Fin.sum_univ_add]; rfl
    rw [hs, dot_unit' wV (xV x), dot_unit' wP (xP x)]
    have hR : radF53 (xV x) ^ 2 + radF53 (xP x) ^ 2 = 1 := by
      rw [rad_sq', rad_sq']
      have h := sum_split (fun t => t ^ 2) x
      try simp only at h
      linarith
    simp only [GV, GP]
    have hA0 : ∑ j, wV j ^ 2 = 0 → (∑ j, wV j * unitF53 (xV x) j) ^ 2 = 0 := fun h => by
      rw [dot_zero_of wV h]; ring
    have hE0 : ∑ j, wP j ^ 2 = 0 → (∑ j, wP j * unitF53 (xP x) j) ^ 2 = 0 := fun h => by
      rw [dot_zero_of wP h]; ring
    set A := ∑ j, wV j * unitF53 (xV x) j
    set E := ∑ j, wP j * unitF53 (xP x) j
    set RV := radF53 (xV x)
    set RP := radF53 (xP x)
    have h2 : (RV * A + RP * E) ^ 2 ≤ A ^ 2 + E ^ 2 := by
      nlinarith [sq_nonneg (RV * E - RP * A)]
    calc (RV * A + RP * E) ^ (2 * p) = ((RV * A + RP * E) ^ 2) ^ p := by rw [pow_mul]
      _ ≤ (A ^ 2 + E ^ 2) ^ p := pow_le_pow_left₀ (sq_nonneg _) h2 p
      _ ≤ κV * (A ^ 2) ^ p + κP * (E ^ 2) ^ p := hκ _ _ (sq_nonneg _) (sq_nonneg _) hA0 hE0
  have hiV := int_unit_comp (μ := f1Tilt b r c) GV hGV xV measurable_xV
  have hiP := int_unit_comp (μ := f1Tilt b r c) GP hGP xP measurable_xP
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < ((b + r : ℕ) : ℝ) := by exact_mod_cast hbr
  have hL0 : 0 < L := by
    by_contra h; push Not at h
    have : L * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hbR.le
    linarith
  have e1 : 1 / (b : ℝ) ^ p ≤ L ^ p / ((b + r : ℕ) : ℝ) ^ p := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hnR.le hLb p
  have e2 : 1 / (r : ℝ) ^ p ≤ L ^ p / ((b + r : ℕ) : ℝ) ^ p := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hnR.le hLr p
  have hD := doubleFact_pos p
  have hGVi : ∀ y, GV y = (∑ j, wV j * y j) ^ (2 * p) := fun y => by simp only [GV]; rw [pow_mul]
  have hGPi : ∀ y, GP y = (∑ j, wP j * y j) ^ (2 * p) := fun y => by simp only [GP]; rw [pow_mul]
  have hwc : Continuous (fun x : Fin (b + r) → ℝ => (∑ i, w i * x i) ^ (2 * p)) := by fun_prop
  have hLn : 0 ≤ L ^ p / ((b + r : ℕ) : ℝ) ^ p := by positivity
  have hIV : ∫ y, GV y ∂uniformSphere b ≤
      ((2 * p - 1).doubleFactorial : ℝ) * (∑ j, wV j ^ 2) ^ p / (b : ℝ) ^ p := by
    simp_rw [hGVi]; exact sphere_dirm_le hb wV p hp
  have hIP : ∫ y, GP y ∂uniformSphere r ≤
      ((2 * p - 1).doubleFactorial : ℝ) * (∑ j, wP j ^ 2) ^ p / (r : ℝ) ^ p := by
    simp_rw [hGPi]; exact sphere_dirm_le hr wP p hp
  have hsVp : 0 ≤ (∑ j, wV j ^ 2) ^ p := pow_nonneg sV p
  have hsPp : 0 ≤ (∑ j, wP j ^ 2) ^ p := pow_nonneg sP p
  calc ∫ x, (∑ i, w i * x i) ^ (2 * p) ∂f1Tilt b r c
      ≤ ∫ x, κV * GV (unitF53 (xV x)) + κP * GP (unitF53 (xP x)) ∂f1Tilt b r c :=
        integral_mono_ae (sphere_integrable hsph hwc)
          ((hiV.const_mul _).add (hiP.const_mul _)) hpt
    _ = κV * (∫ y, GV y ∂uniformSphere b) + κP * ∫ y, GP y ∂uniformSphere r := by
        rw [integral_add (hiV.const_mul _) (hiP.const_mul _), integral_const_mul,
          integral_const_mul,
          f1_blockV hb c GV hGV (fun y => pow_nonneg (sq_nonneg _) p),
          f1_blockP hr c GP hGP (fun y => pow_nonneg (sq_nonneg _) p)]
    _ ≤ κV * (((2 * p - 1).doubleFactorial : ℝ) * (∑ j, wV j ^ 2) ^ p / (b : ℝ) ^ p) +
          κP * (((2 * p - 1).doubleFactorial : ℝ) * (∑ j, wP j ^ 2) ^ p / (r : ℝ) ^ p) := by
        gcongr
    _ = ((2 * p - 1).doubleFactorial : ℝ) * ((κV * (∑ j, wV j ^ 2) ^ p) * (1 / (b : ℝ) ^ p) +
          (κP * (∑ j, wP j ^ 2) ^ p) * (1 / (r : ℝ) ^ p)) := by ring
    _ ≤ ((2 * p - 1).doubleFactorial : ℝ) * ((∑ j, wV j ^ 2) * (L ^ p / ((b + r : ℕ) : ℝ) ^ p) +
          (∑ j, wP j ^ 2) * (L ^ p / ((b + r : ℕ) : ℝ) ^ p)) := by
        have := mul_nonneg hκV hsVp
        have := mul_nonneg hκP hsPp
        gcongr
    _ = ((2 * p - 1).doubleFactorial : ℝ) * L ^ p / ((b + r : ℕ) : ℝ) ^ p := by
        rw [← add_mul, hsplit]; ring

/-! ## The rotated tilt as a push-forward -/

variable {n : ℕ}

lemma dot_mulVec (O : Matrix (Fin n) (Fin n) ℝ) (w y : Fin n → ℝ) :
    ∑ i, w i * (O.mulVec y) i = ∑ j, (O.transpose.mulVec w) j * y j := by
  have h : w ⬝ᵥ O.mulVec y = (O.transpose.mulVec w) ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  simpa [dotProduct] using h

/-- The push-forward of a distribution carried by the sphere under `O` is carried by the sphere. -/
lemma map_sph {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : IsOrth O) : SphLaw n (μ.map (fun x => O.mulVec x)) := by
  have hm : Measurable (fun x : Fin n → ℝ => O.mulVec x) := by fun_prop
  let := hμ.prob
  refine ⟨inferInstance, ?_⟩
  rw [ae_map_iff hm.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
  filter_upwards [hμ.sphere] with x hx
  rw [orth_sumsq hO, hx]

/-- Directional moments move to the transposed direction. -/
lemma map_dir {μ : Measure (Fin n → ℝ)} (O : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) (m : ℕ) :
    ∫ x, (∑ i, w i * x i) ^ m ∂(μ.map (fun x => O.mulVec x)) =
      ∫ y, (∑ j, (O.transpose.mulVec w) j * y j) ^ m ∂μ := by
  rw [integral_map (by fun_prop)
    (by fun_prop : Continuous (fun x : Fin n → ℝ => (∑ i, w i * x i) ^ m)).aestronglyMeasurable]
  simp_rw [dot_mulVec]

/-- **Directional moments of the rotated tilt**, uniformly in `c` and in `O`. -/
theorem rot_dirm (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (O : Matrix (Fin (b + r)) (Fin (b + r)) ℝ)
    (hO : IsOrth O) (w : Fin (b + r) → ℝ) (hw : ∑ i, w i ^ 2 = 1) (p : ℕ) (hp : 1 ≤ p) :
    ∫ x, (∑ i, w i * x i) ^ (2 * p) ∂((f1Tilt b r c).map (fun x => O.mulVec x)) ≤
      ((2 * p - 1).doubleFactorial : ℝ) * L ^ p / ((b + r : ℕ) : ℝ) ^ p := by
  rw [map_dir]
  exact f1_dirm hb hr hLb hLr c _ (by rw [orth_sumsq hO.t, hw]) p hp

private lemma single_unit (i : Fin n) : ∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j ^ 2 = 1 := by
  classical
  simp [Pi.single_apply]

/-- **Directional moments of order `4q` bound the `p₄` moments.** -/
theorem p4_of_dirm {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (q : ℕ) (hq : 1 ≤ q) (K : ℝ)
    (hK : ∀ w : Fin n → ℝ, ∑ i, w i ^ 2 = 1 →
      ∫ x, (∑ i, w i * x i) ^ (4 * q) ∂μ ≤ K / (n : ℝ) ^ (2 * q)) (hn : 1 ≤ n) :
    ∫ x, p4 x ^ q ∂μ ≤ K / (n : ℝ) ^ q := by
  classical
  let := hμ.prob
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
  have hpt : ∀ x : Fin n → ℝ, p4 x ^ (s + 1) ≤ (n : ℝ) ^ s * ∑ i, x i ^ (4 * (s + 1)) := by
    intro x
    have h := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := fun i => x i ^ 4)
      (fun i _ => by positivity) s
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have hnr : (0 : ℝ) < (n : ℝ) ^ s := by positivity
    rw [div_le_iff₀ hnr] at h
    unfold p4
    simp_rw [pow_mul]
    linarith [mul_comm ((n : ℝ) ^ s) (∑ i, (x i ^ 4) ^ (s + 1))]
  have hcoord : ∀ i : Fin n, ∫ x, x i ^ (4 * (s + 1)) ∂μ ≤ K / (n : ℝ) ^ (2 * (s + 1)) := by
    intro i
    have h := hK (Pi.single i 1) (single_unit i)
    have he : ∀ x : Fin n → ℝ, ∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j * x j = x i := by
      intro x; simp [Pi.single_apply]
    simp_rw [he] at h
    exact h
  have hc : ∀ i : Fin n, Continuous (fun x : Fin n → ℝ => x i ^ (4 * (s + 1))) :=
    fun i => (continuous_apply i).pow _
  have hp4c : Continuous (fun x : Fin n → ℝ => p4 x ^ (s + 1)) := by unfold p4; fun_prop
  calc ∫ x, p4 x ^ (s + 1) ∂μ
      ≤ ∫ x, (n : ℝ) ^ s * ∑ i, x i ^ (4 * (s + 1)) ∂μ :=
        integral_mono (sphere_integrable hμ hp4c) (sphere_integrable hμ (by fun_prop)) hpt
    _ = (n : ℝ) ^ s * ∑ i, ∫ x, x i ^ (4 * (s + 1)) ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ (fun i _ => sphere_integrable hμ (hc i))]
    _ ≤ (n : ℝ) ^ s * ∑ _i : Fin n, K / (n : ℝ) ^ (2 * (s + 1)) := by
        gcongr with i
        exact hcoord i
    _ = K / (n : ℝ) ^ (s + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring

/-- The trace-moment weight of the rotated tilt, `wG L i = (8i−1)!!·L^{4i}`. -/
noncomputable def wG (L : ℝ) (i : ℕ) : ℝ := ((8 * i - 1).doubleFactorial : ℝ) * L ^ (4 * i)

lemma wG_nonneg (L : ℝ) (i : ℕ) : 0 ≤ wG L i := by
  unfold wG
  rw [pow_mul L 4 i, show L ^ 4 = (L ^ 2) ^ 2 by ring]
  positivity

/-- **The trace moments (P1) from directional moments.** If `E_μ (w·x)^{8i} ≤ K/n^{4i}` for every
unit `w`, then `E_μ δ°^{2i} ≤ K·d^{2i}/n^{2i}`. -/
theorem dev_of_dirm {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (hn : 1 ≤ n) (d i : ℕ) (hi : 1 ≤ i)
    (K : ℝ) (hK : ∀ w : Fin n → ℝ, ∑ j, w j ^ 2 = 1 →
      ∫ x, (∑ j, w j * x j) ^ (4 * (2 * i)) ∂μ ≤ K / (n : ℝ) ^ (2 * (2 * i))) :
    ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ ≤ K * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i) := by
  let := hμ.prob
  have hU := BstLean.Part53.lemmaU53 d
  have hδc : Continuous (fun x : Fin n → ℝ => (phiSq d x - c0 d) ^ (2 * i)) :=
    (BstLean.Part53.FloorCorrection.phiSq_continuous.sub continuous_const).pow _
  have hp4c : Continuous (fun x : Fin n → ℝ => p4 x ^ (2 * i)) := by unfold p4; fun_prop
  have hmono : ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂μ ≤
      ∫ x, (d : ℝ) ^ (2 * i) * p4 x ^ (2 * i) ∂μ := by
    apply integral_mono_ae (sphere_integrable hμ hδc) (sphere_integrable hμ (by fun_prop))
    filter_upwards [hμ.sphere] with x hx
    obtain ⟨h0, h1⟩ := hU n x hx
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 h1 _
  rw [integral_const_mul] at hmono
  have hp := p4_of_dirm hμ (2 * i) (by omega) K hK hn
  refine hmono.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans (le_of_eq ?_))
  ring

/-- **The rotated two-subspace tilt satisfies `Good72`**, uniformly in `c` and `O`, for every
`d ≥ 1` and `k`. -/
theorem rot_good (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (O : Matrix (Fin (b + r)) (Fin (b + r)) ℝ)
    (hO : IsOrth O) (d k : ℕ) (hd : 1 ≤ d) :
    Good72 (b + r) d k ((f1Tilt b r c).map (fun x => O.mulVec x)) (wG L) (Fov d L) L := by
  have hbr : 1 ≤ b + r := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < ((b + r : ℕ) : ℝ) := by exact_mod_cast hbr
  have hL0 : 0 < L := by
    by_contra h; push Not at h
    have : L * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hbR.le
    linarith
  have hsph := map_sph (f1_sph (b := b) (r := r) hbr c) O hO
  apply good_of_ov hsph d k hd (wG L) L
  · have hz : ∀ i, ∫ x, x i ∂((f1Tilt b r c).map (fun x => O.mulVec x)) = 0 := by
      intro i
      have h := map_dir (μ := f1Tilt b r c) O (Pi.single i 1) 1
      have he : ∀ x : Fin (b + r) → ℝ, ∑ j, (Pi.single i (1 : ℝ) : Fin (b + r) → ℝ) j * x j = x i := by
        intro x; simp [Pi.single_apply]
      simp_rw [he, pow_one] at h
      rw [h]
      let := (f1_sph (b := b) (r := r) hbr c).prob
      rw [integral_finsetSum _ (fun j _ => (sphere_integrable (f1_sph hbr c)
        (by fun_prop : Continuous (fun y : Fin (b + r) → ℝ => y j))).const_mul _)]
      simp [integral_const_mul, f1_mean_zero hbr c]
    have : Mean ((f1Tilt b r c).map (fun x => O.mulVec x)) = 0 := by unfold Mean; simp [hz]
    rw [this]; positivity
  · intro w hw
    have h := rot_dirm hb hr hLb hLr c O hO w hw 1 le_rfl
    refine h.trans (le_of_eq ?_)
    norm_num [Nat.doubleFactorial]
  · intro i hi _
    apply dev_of_dirm hsph hbr d i hi
    intro w hw
    have h := rot_dirm hb hr hLb hLr c O hO w hw (2 * (2 * i)) (by omega)
    rw [show 2 * (2 * (2 * i)) = 4 * (2 * i) by ring] at h
    refine h.trans (le_of_eq ?_)
    unfold wG
    rw [show 4 * (2 * i) - 1 = 8 * i - 1 by omega,
      show 2 * (2 * i) = 4 * i by ring]

end BstLean.Part73
