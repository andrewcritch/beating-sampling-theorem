import BstLean.Part167J

/-!
# Part 167 (file `Grad`): the realized `Ψ` through the explicit Jacobian (Lemma J + `tanSq_eq_proj`)

No proof is left open; no `native_decide` or `axiom` is used.

For a key `k = ((ĉ, τ₀), (A₁, A₂))`, an index `a` (latitude `s`) and a direction `v ≠ 0`, put
`y = xLatH c s v` (a positive multiple of the unit input `x = xLat c s (v/|v|)`). On `NoKink` at `y`:

* **`psiK_f_le`**: `Ψ_f(a, v)^{64} ≤ ((1 − s²)·latSq(𝒥ᵀb̂)/n)^{64}`;
* **`psiK_s_le`**: `Ψ_σ(a, v)^{64} ≤ ((1 − s²)·(2/m_A)·latSq(𝒥ᵀr̂)/1)^{64}`;

with `latSq g u w = |g|² − ⟨g, u⟩² − ⟨g, w⟩²` (`= |P_lat g|²`, `u` the World direction, `w` the unit
vector of `span(u, x)` orthogonal to `u`), `𝒥 = 𝒥(x)` (Part 151's `jac`), `b̂ = b/|b|`,
`r̂ = r(x)/|r(x)|` (`0` at `0`). This is the paper's identity `Ψ_φ = (1 − s²)|P_lat∇φ|²` with
`∇f = 𝒥ᵀb̂/√n`, `∇σ = √(2/m_A)𝒥ᵀr̂`.
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (Ix)
open BstLean.Part151 (jac rowL rowL_apply gradSq)
open BstLean.Part161 (xLat hhMat uHat consV)
open BstLean.Part162 (xLatH tanSq xLatH_eq dirW tanSq_eq_proj latitude_sq_le)
open BstLean.Part166 (bK bhat fK sK psiK repK latK FF SS fK_eq_FF sK_eq_SS)
open BstLean.Part53 (unitF53 radF53)

variable {n : ℕ}

/-! ## §1 Algebra -/

/-- `|g|² − ⟨g, u⟩² − ⟨g, w⟩²`: the squared norm of the part of `g` orthogonal to the
orthonormal pair `(u, w)`. -/
def latSq {ι : Type*} [Fintype ι] (g u w : ι → ℝ) : ℝ :=
  ∑ i, g i ^ 2 - (∑ i, g i * u i) ^ 2 - (∑ i, g i * w i) ^ 2

lemma latSq_smul {ι : Type*} [Fintype ι] (κ : ℝ) (g u w : ι → ℝ) :
    latSq (κ • g) u w = κ ^ 2 * latSq g u w := by
  unfold latSq
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ i, (κ * g i) ^ 2 = κ ^ 2 * ∑ i, g i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∀ z : ι → ℝ, ∑ i, κ * g i * z i = κ * ∑ i, g i * z i := by
    intro z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, e2]; ring

/-- `(√T)²` raised to an even power is at most `T` raised to it. -/
lemma sqrt_sq_pow_le (T : ℝ) : (√T ^ 2) ^ 64 ≤ T ^ 64 := by
  rcases le_or_gt 0 T with h | h
  · rw [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero'.mpr h.le]; simp; positivity

/-- `b̂` is either `0` or a unit vector. -/
lemma bhat_cases {m : ℕ} (b : Fin m → ℝ) : bhat b = 0 ∨ normSq (bhat b) = 1 := by
  rcases (normSq_nonneg b).eq_or_lt with h0 | h0
  · left
    have hb : b = 0 := by
      funext j
      have h := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (b i)) |>.mp
        (show ∑ i, b i ^ 2 = 0 from h0.symm) j (Finset.mem_univ j)
      simpa using h
    simp [bhat, hb]
  · right
    have e : normSq (bhat b) = (√(normSq b))⁻¹ ^ 2 * normSq b := by
      unfold bhat
      unfold normSq
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [← Finset.mul_sum]
    rw [e, inv_pow, Real.sq_sqrt h0.le]
    exact inv_mul_cancel₀ h0.ne'

lemma bhat_smul {m : ℕ} {t : ℝ} (ht : 0 < t) (b : Fin m → ℝ) : bhat (t • b) = bhat b := by
  unfold bhat
  have e : normSq (t • b) = t ^ 2 * normSq b := by
    unfold normSq; simp only [Pi.smul_apply, smul_eq_mul, mul_pow]; rw [Finset.mul_sum]
  rw [e, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, smul_smul, mul_inv]
  rcases (normSq_nonneg b).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · congr 1; field_simp

/-- `vecMul b M` written as a sum. -/
lemma sum_mulVec_mul {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (b : Fin p → ℝ) (d : Fin q → ℝ) :
    ∑ j, (M *ᵥ d) j * b j = ∑ l, vecMul b M l * d l := by
  simp only [mulVec, vecMul, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## §2 The tangential gradient from a derivative of the form `κ⟨g, ·⟩` -/

/-- **`tanSq` from a known derivative**: if `Φ` is positively 1-homogeneous and has derivative
`d ↦ κ·⟨g, d⟩` at `y = xLatH c s v` (`v ≠ 0`, `c ≠ 0`, `s² ≤ 1`), then
`tanSq Φ c s v = (1 − s²)·κ²·latSq g u w`. -/
theorem tanSq_of_hasFDerivAt (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {Φ : (Fin n → ℝ) → ℝ} (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) {Lc : (Fin n → ℝ) →L[ℝ] ℝ}
    (hd : HasFDerivAt Φ Lc (xLatH c s v)) {κ : ℝ} {g : Fin n → ℝ}
    (hL : ∀ d, Lc d = κ * ∑ l, g l * d l) :
    tanSq Φ c s v = (1 - s ^ 2) * (κ ^ 2 * latSq g (uHat c) (dirW c (unitF53 v))) := by
  rw [tanSq_eq_proj hn hc hs hhom hv hd.differentiableAt, hd.fderiv]
  simp only [hL]
  have e1 : ∀ i : Fin n, ∑ l, g l * (Pi.single i (1 : ℝ) : Fin n → ℝ) l = g i := by
    intro i; simp [Pi.single_apply]
  simp_rw [e1]
  unfold latSq
  have e2 : ∑ i, (κ * g i) ^ 2 = κ ^ 2 * ∑ i, g i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]; ring

/-! ## §3 Homogeneity and the two fields near `y` -/

lemma fK_hom (k : AgFam n) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) :
    fK k (t • x) = t * fK k x := by
  unfold fK
  rw [BstLean.Part153.hid2_smul _ _ ht.le, BstLean.Part162.lam_smul]; ring

lemma sK_hom (k : AgFam n) (t : ℝ) (x : Fin n → ℝ) (ht : 0 < t) :
    sK k (t • x) = t * sK k x := by
  unfold sK sig
  rw [BstLean.Part153.hid2_smul _ _ ht.le, BstLean.Part162.res_smul]
  have : normSq (t • res (bK k) (hid2 k.2.1 k.2.2 x)) =
      t ^ 2 * normSq (res (bK k) (hid2 k.2.1 k.2.2 x)) := by
    unfold normSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  ring

/-- The residual at the key in the `b̂` form: `r = h − ⟨h, b̂⟩ b̂`. -/
noncomputable def rK (k : AgFam n) (x : Fin n → ℝ) : Fin (mA n) → ℝ :=
  hid2 k.2.1 k.2.2 x - (∑ j, hid2 k.2.1 k.2.2 x j * bhat (bK k) j) • bhat (bK k)

lemma sK_eq_rK (k : AgFam n) (x : Fin n → ℝ) :
    sK k x = √(2 / (mA n : ℝ)) * √(normSq (rK k x)) := by
  rw [sK_eq_SS]; rfl

lemma rK_smul (k : AgFam n) {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    rK k (t • x) = t • rK k x := by
  unfold rK
  rw [BstLean.Part153.hid2_smul _ _ ht.le]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e : ∑ j, t * hid2 k.2.1 k.2.2 x j * bhat (bK k) j =
      t * ∑ j, hid2 k.2.1 k.2.2 x j * bhat (bK k) j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, smul_sub, smul_smul]

/-- `⟨r, b̂⟩ = 0`. -/
lemma rK_orth (k : AgFam n) (x : Fin n → ℝ) : ∑ j, rK k x j * bhat (bK k) j = 0 := by
  unfold rK
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  set h := hid2 k.2.1 k.2.2 x
  set b := bhat (bK k)
  have e : ∑ j, (h j - (∑ i, h i * b i) * b j) * b j =
      (∑ i, h i * b i) * (1 - normSq b) := by
    unfold normSq
    rw [mul_sub, mul_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  rcases bhat_cases (bK k) with h0 | h1
  · have : b = 0 := h0
    rw [this]; simp [normSq]
  · rw [h1]; ring

/-! ## §4 Derivatives -/

/-- The derivative of `z ↦ |M z|` at a point where `M y ≠ 0`: `d ↦ ⟨(M y)/|M y|, M d⟩`. -/
lemma hasFDerivAt_nrm_mulVec {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) {y : Fin q → ℝ}
    (hy : normSq (M *ᵥ y) ≠ 0) :
    ∃ Lc : (Fin q → ℝ) →L[ℝ] ℝ, HasFDerivAt (fun z => √(normSq (M *ᵥ z))) Lc y ∧
      ∀ d, Lc d = ∑ l, vecMul (bhat (M *ᵥ y)) M l * d l := by
  have hq : HasFDerivAt (fun z : Fin q → ℝ => normSq (M *ᵥ z))
      (∑ j, (2 * (M *ᵥ y) j) • rowL M j) y := by
    have e : (fun z : Fin q → ℝ => normSq (M *ᵥ z)) = fun z => ∑ j, rowL M j z * rowL M j z := by
      funext z; unfold normSq; simp_rw [rowL_apply, sq]
    rw [e]
    have hs := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin p)))
      (A := fun j (z : Fin q → ℝ) => rowL M j z * rowL M j z)
      (A' := fun j => (2 * (M *ᵥ y) j) • rowL M j) (x := y)
      (fun j _ => by
        have h1 := ((rowL M j).hasFDerivAt (x := y)).mul ((rowL M j).hasFDerivAt (x := y))
        convert h1 using 1
        rw [rowL_apply, two_mul, add_smul])
    exact hs
  refine ⟨(1 / (2 * √(normSq (M *ᵥ y)))) • ∑ j, (2 * (M *ᵥ y) j) • rowL M j, hq.sqrt hy, ?_⟩
  intro d
  have hpos : 0 < normSq (M *ᵥ y) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hsq : 0 < √(normSq (M *ᵥ y)) := Real.sqrt_pos.mpr hpos
  simp only [_root_.smul_apply, FunLike.coe_sum, Finset.sum_apply,
    smul_eq_mul, rowL_apply]
  rw [← sum_mulVec_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold bhat
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-! ## §5 The two bounds -/

variable (k : AgFam n) (a : Ix n) (v : Fin (n - 1) → ℝ)

/-- `𝒥ᵀ b̂` at the input `x`. -/
noncomputable def gF (x : Fin n → ℝ) : Fin n → ℝ := vecMul (bhat (bK k)) (jac k.2.1 k.2.2 x)

/-- `𝒥ᵀ r̂` at the input `x`. -/
noncomputable def gS (x : Fin n → ℝ) : Fin n → ℝ := vecMul (bhat (rK k x)) (jac k.2.1 k.2.2 x)

/-- **`Ψ_f` through the Jacobian (Lemma J + the tangential identity)**. -/
theorem psiK_f_le (hn : 1 ≤ n) (hc : k.1.1 ≠ 0) (hv : v ≠ 0)
    (hK : NoKink k.2.1 k.2.2 (xLatH (repK k) (latK k a) v)) :
    psiK fK k a v ^ 64 ≤ ((1 - latK k a ^ 2) *
      latSq (gF k (xLatH (repK k) (latK k a) v)) (uHat (repK k))
        (dirW (repK k) (unitF53 v)) / n) ^ 64 := by
  set y := xLatH (repK k) (latK k a) v with hy
  set J := jac k.2.1 k.2.2 y
  set b := bhat (bK k)
  have hev := hid2_eventuallyEq_jac hK
  have hloc : fK k =ᶠ[𝓝 y] fun z => (√(n : ℝ))⁻¹ * ∑ j, (J *ᵥ z) j * b j := by
    rw [fK_eq_FF]
    filter_upwards [hev] with z hz
    unfold FF
    rw [hz]
  set Lc : (Fin n → ℝ) →L[ℝ] ℝ :=
    (√(n : ℝ))⁻¹ • ∑ l, gF k y l • (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ) with hLc
  have hLa : ∀ d, Lc d = (√(n : ℝ))⁻¹ * ∑ l, gF k y l * d l := by
    intro d; simp [hLc]
  have hfun : (fun z => (√(n : ℝ))⁻¹ * ∑ j, (J *ᵥ z) j * b j) = fun z => Lc z := by
    funext z; rw [hLa, sum_mulVec_mul]; rfl
  have hd : HasFDerivAt (fK k) Lc y := by
    have h0 : HasFDerivAt (fun z => (√(n : ℝ))⁻¹ * ∑ j, (J *ᵥ z) j * b j) Lc y := by
      rw [hfun]; exact Lc.hasFDerivAt
    exact h0.congr_of_eventuallyEq hloc
  have hT := tanSq_of_hasFDerivAt hn hc (s := latK k a) (latitude_sq_le _ _ _) (fK_hom k) hv hd hLa
  unfold psiK
  refine (sqrt_sq_pow_le _).trans (le_of_eq ?_)
  rw [hT]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_pow, Real.sq_sqrt hn0.le]
  congr 1
  field_simp

/-- **`Ψ_σ` through the Jacobian.** -/
theorem psiK_s_le (hn : 1 ≤ n) (hc : k.1.1 ≠ 0) (hv : v ≠ 0)
    (hK : NoKink k.2.1 k.2.2 (xLatH (repK k) (latK k a) v)) :
    psiK sK k a v ^ 64 ≤ ((1 - latK k a ^ 2) * (2 / (mA n : ℝ)) *
      latSq (gS k (xLatH (repK k) (latK k a) v)) (uHat (repK k))
        (dirW (repK k) (unitF53 v))) ^ 64 := by
  set y := xLatH (repK k) (latK k a) v with hy
  set J := jac k.2.1 k.2.2 y
  set b := bhat (bK k)
  have hev := hid2_eventuallyEq_jac hK
  -- the residual as a matrix map near `y`
  set R : Matrix (Fin (mA n)) (Fin n) ℝ := J - Matrix.vecMulVec b (vecMul b J) with hR
  have hRz : ∀ z, hid2 k.2.1 k.2.2 z = J *ᵥ z → rK k z = R *ᵥ z := by
    intro z hz
    unfold rK
    rw [hz, hR, Matrix.sub_mulVec]
    congr 1
    funext j
    rw [Pi.smul_apply, smul_eq_mul, sum_mulVec_mul J b z]
    simp only [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hry : rK k y = R *ᵥ y := hRz y (hev.self_of_nhds)
  have hloc : sK k =ᶠ[𝓝 y] fun z => √(2 / (mA n : ℝ)) * √(normSq (R *ᵥ z)) := by
    filter_upwards [hev] with z hz
    rw [sK_eq_rK, hRz z hz]
  unfold psiK
  by_cases hr : normSq (rK k y) = 0
  · -- `r(y) = 0`: `σ` has a minimum `0` on the latitude cone at `v`, so `Ψ_σ = 0`
    have hsy : sK k y = 0 := by rw [sK_eq_rK, hr]; simp
    have hmin : IsLocalMin (fun w => sK k (xLatH (repK k) (latK k a) w)) v := by
      refine Filter.Eventually.of_forall fun w => ?_
      show sK k y ≤ sK k (xLatH (repK k) (latK k a) w)
      rw [hsy, sK_eq_rK]; positivity
    have hT : tanSq (sK k) (repK k) (latK k a) v = 0 := by
      unfold tanSq gradSq
      rw [hmin.fderiv_eq_zero]
      have hvpos : 0 < radF53 v := BstLean.Part162.radF_pos hv
      have hx : sK k (xLat (repK k) (latK k a) (unitF53 v)) = 0 := by
        have h1 := sK_hom k (radF53 v) (xLat (repK k) (latK k a) (unitF53 v)) hvpos
        rw [← xLatH_eq, ← hy, hsy] at h1
        have := (mul_eq_zero.mp h1.symm).resolve_left hvpos.ne'
        exact this
      rw [hx]; simp
    rw [hT]; simp; positivity
  · have hRy : normSq (R *ᵥ y) ≠ 0 := by rw [← hry]; exact hr
    obtain ⟨L0, hL0, hL0a⟩ := hasFDerivAt_nrm_mulVec R hRy
    have hd : HasFDerivAt (sK k) (√(2 / (mA n : ℝ)) • L0) y :=
      (hL0.const_mul (√(2 / (mA n : ℝ)))).congr_of_eventuallyEq hloc
    have hg : vecMul (bhat (R *ᵥ y)) R = gS k y := by
      unfold gS
      rw [← hry, hR, Matrix.vecMul_sub]
      have e : vecMul (bhat (rK k y)) (Matrix.vecMulVec b (vecMul b J)) = 0 := by
        funext l
        simp only [vecMul, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.zero_apply]
        have h0 := rK_orth k y
        have e2 : ∑ j, bhat (rK k y) j * (b j * ∑ i, b i * J i l) =
            (∑ j, rK k y j * b j) * ((√(normSq (rK k y)))⁻¹ * ∑ i, b i * J i l) := by
          unfold bhat
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e2, h0, zero_mul]
      rw [e, sub_zero]
    have hLa : ∀ d, (√(2 / (mA n : ℝ)) • L0) d = √(2 / (mA n : ℝ)) * ∑ l, gS k y l * d l := by
      intro d
      rw [_root_.smul_apply, hL0a, ← hg, smul_eq_mul]
    have hT := tanSq_of_hasFDerivAt hn hc (s := latK k a) (latitude_sq_le _ _ _) (sK_hom k) hv hd hLa
    refine (sqrt_sq_pow_le _).trans (le_of_eq ?_)
    rw [hT, Real.sq_sqrt (by positivity)]
    ring

end BstLean.Part167
