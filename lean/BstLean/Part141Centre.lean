import BstLean.Part141Atom

/-!
# Part 141, item 2 (`centreArith141`): the distance of a finite-ReLU-sum centre to the computed
centre `b̂ = ψ_s(M₂ h̄₁)` of Part 137

Role: `delegations/statements/p141-spec.md`, item 2. Paper sources: `onW8c-cx.md` §§2–3
(Lemma R; the rational repair of `c_N`).

`θ = (M₁, M₂)`, `t = 2/m`, `γ = 2/N`, `Γ* = GamS M₁ = Σ_j|row_j(M₁)|²/(mN)`.
The centre of the program is `b = bOf c p z θ`: `b_i = Σ_ℓ p_ℓ·relu(a_i + s̃·z_ℓ)` with
`a = M₂·(c·|row_j|)_j` and `s̃ = √(Σ_j|row_j|²·(1/(mN) − (2/m)c²))`. The hypotheses are:
`0 ≤ c ≤ c_N` and `|atomSum p z s x − ψ_s(x)| ≤ s·ε` for every `s ≥ 0` and every `x`.

* `aOf_cN`, `sOf_cN`: at `c = c_N` the two values are `M₂ h̄₁` and `s` of Part 137.
* **`centre_pt`**: for every `θ`:
  `t|b − b̂|² ≤ Γ*·(6ε² + 24·N·c_N·(c_N − c)) + 3(c_N − c)²·t|M₂ρ|²`, `ρ_j = |row_j(M₁)|`.
* `layer_sq`: `E|M h|² = m·v·|h|²` for a Gaussian matrix; `GamS_mean`, `aOne_mean`.
* **`centre_mean`**: `E_θ t|b − b̂|² ≤ γ·√(1 + 5/m)·(6ε² + 24·N·c_N·(c_N − c) + 12·N·(c_N − c)²)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140

variable {N m : ℕ}

/-! ## The constant `c_N` -/

lemma cN_nonneg (N : ℕ) : 0 ≤ cN N := gfun_nonneg _

/-- `c_N² ≤ 1/(4N)`. -/
lemma cN_sq_le (hN : 1 ≤ N) : cN N ^ 2 ≤ 1 / (4 * (N : ℝ)) := by
  have h := sphere_relu_mean_sq hN (e0 N)
  rw [Part137.normSq_e0 hN] at h
  exact h

lemma cN_le_half (hN : 1 ≤ N) : cN N ≤ 1 / 2 := by
  have h := cN_sq_le hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : 1 / (4 * (N : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  nlinarith [cN_nonneg N]

/-! ## The values of the first pass with a constant `c` -/

/-- The sum of the squared row lengths of `M₁`. -/
noncomputable def rowS (M₁ : Matrix (Fin m) (Fin N) ℝ) : ℝ := ∑ j, normSq (rowOf j M₁)

lemma rowS_nonneg (M₁ : Matrix (Fin m) (Fin N) ℝ) : 0 ≤ rowS M₁ :=
  Finset.sum_nonneg fun j _ => normSq_nonneg _

lemma GamS_rowS (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    GamS M₁ = rowS M₁ / ((m : ℝ) * N) := by
  rw [GamS_rows hN hm, rowS, Finset.sum_div]

lemma aOf_mul (c : ℝ) (θ : HidParam N m) (i : Fin m) : aOf c θ i = c * aOf 1 θ i := by
  unfold aOf
  simp only [Matrix.mulVec, dotProduct, one_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma aOf_cN (hN : 1 ≤ N) (θ : HidParam N m) : aOf (cN N) θ = θ.2.mulVec (h1bar θ.1) := by
  unfold aOf
  congr 1
  funext j
  rw [h1bar_eq hN]
  rfl

lemma normSq_h1bar (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    normSq (h1bar M₁) = cN N ^ 2 * rowS M₁ := by
  unfold normSq rowS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1bar_eq hN, mul_pow, nrm_sq]

/-- The argument of the square root in `sOf`. -/
lemma sOf_arg (hN : 1 ≤ N) (hm : 1 ≤ m) (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    rowS M₁ * (1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (cN N * cN N)) =
      GamS M₁ - 2 / (m : ℝ) * normSq (h1bar M₁) := by
  rw [GamS_rowS hN hm, normSq_h1bar hN]
  ring

lemma sOf_cN (hN : 1 ≤ N) (hm : 1 ≤ m) (θ : HidParam N m) : sOf (cN N) θ = sS θ.1 := by
  unfold sOf sS
  congr 1
  exact sOf_arg hN hm θ.1

lemma sOf_nonneg (c : ℝ) (θ : HidParam N m) : 0 ≤ sOf c θ := Real.sqrt_nonneg _

/-- The factor `1/(mN) − (2/m)c²` is nonnegative for `0 ≤ c ≤ c_N`. -/
lemma dfac_nonneg (hN : 1 ≤ N) (hm : 1 ≤ m) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ cN N) :
    0 ≤ 1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (c * c) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := cN_sq_le hN
  have h2 : c * c ≤ cN N ^ 2 := by nlinarith
  have h3 : 2 / (m : ℝ) * (c * c) ≤ 2 / (m : ℝ) * (1 / (4 * (N : ℝ))) :=
    mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)
  have e : 1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (1 / (4 * (N : ℝ))) = 1 / (2 * ((m : ℝ) * N)) := by
    field_simp
    ring
  have h4 : (0 : ℝ) ≤ 1 / (2 * ((m : ℝ) * N)) := by positivity
  linarith

lemma sOf_sq (hN : 1 ≤ N) (hm : 1 ≤ m) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ cN N)
    (θ : HidParam N m) :
    sOf c θ ^ 2 = rowS θ.1 * (1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (c * c)) := by
  unfold sOf
  exact Real.sq_sqrt (mul_nonneg (rowS_nonneg _) (dfac_nonneg hN hm hc0 hc1))

/-! ## The pointwise distance -/

lemma sq_add3 (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- **The distance of the centre of a finite ReLU sum to the computed centre, for every
`θ`.** -/
theorem centre_pt (hN : 1 ≤ N) (hm : 1 ≤ m) {L : ℕ} (p z : Fin L → ℝ) {c ε : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ cN N)
    (hε : ∀ s x : ℝ, 0 ≤ s → |atomSum p z s x - psiS s x| ≤ s * ε) (θ : HidParam N m) :
    2 / (m : ℝ) * normSq (bOf c p z θ - bhat θ) ≤
      GamS θ.1 * (6 * ε ^ 2 + 24 * (N : ℝ) * cN N * (cN N - c)) +
        3 * (cN N - c) ^ 2 * (2 / (m : ℝ) * normSq (aOf 1 θ)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN := cN_nonneg N
  set st : ℝ := sOf c θ with hst
  set s : ℝ := sOf (cN N) θ with hs
  set S : ℝ := rowS θ.1 with hS
  set G : ℝ := GamS θ.1 with hG
  have hS0 : 0 ≤ S := rowS_nonneg _
  have hst0 : 0 ≤ st := sOf_nonneg _ _
  have hs0 : 0 ≤ s := sOf_nonneg _ _
  have hstsq : st ^ 2 = S * (1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (c * c)) :=
    sOf_sq hN hm hc0 hc1 θ
  have hssq : s ^ 2 = S * (1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (cN N * cN N)) :=
    sOf_sq hN hm hcN le_rfl θ
  have hGS : G = S / ((m : ℝ) * N) := GamS_rowS hN hm θ.1
  have hSG : S = G * ((m : ℝ) * N) := by rw [hGS]; field_simp
  have hG0 : 0 ≤ G := GamS_nonneg _
  have hcc : c * c ≤ cN N * cN N := by nlinarith
  -- `s ≤ s̃`
  have hle : s ≤ st := by
    rw [hs, hst]
    unfold sOf
    refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ hS0)
    have : 2 / (m : ℝ) * (c * c) ≤ 2 / (m : ℝ) * (cN N * cN N) :=
      mul_le_mul_of_nonneg_left hcc (by positivity)
    linarith
  -- `s̃² ≤ Γ*`
  have hstG : st ^ 2 ≤ G := by
    rw [hstsq, hSG]
    have h1 : 0 ≤ G * ((m : ℝ) * N) * (2 / (m : ℝ) * (c * c)) := by positivity
    have e : G * ((m : ℝ) * N) * (1 / ((m : ℝ) * N)) = G := by field_simp
    nlinarith
  -- `(s̃ − s)² ≤ 4·N·Γ*·c_N·(c_N − c)`
  have hdiff : (st - s) ^ 2 ≤ 4 * (N : ℝ) * G * (cN N * (cN N - c)) := by
    have h1 : (st - s) ^ 2 ≤ st ^ 2 - s ^ 2 := by nlinarith
    have h2 : st ^ 2 - s ^ 2 = S * (2 / (m : ℝ)) * (cN N * cN N - c * c) := by
      rw [hstsq, hssq]; ring
    have h3 : cN N * cN N - c * c ≤ 2 * (cN N * (cN N - c)) := by nlinarith
    have h4 : S * (2 / (m : ℝ)) = 2 * (N : ℝ) * G := by
      rw [hSG]; field_simp
    have h5 : 0 ≤ 2 * (N : ℝ) * G := by positivity
    have h6 := mul_le_mul_of_nonneg_left h3 h5
    rw [h2, h4] at h1
    linarith
  -- one coordinate
  have hcoord : ∀ i : Fin m, (bOf c p z θ i - bhat θ i) ^ 2 ≤
      3 * (st ^ 2 * ε ^ 2 + (st - s) ^ 2) + 3 * (cN N - c) ^ 2 * aOf 1 θ i ^ 2 := by
    intro i
    set v : ℝ := aOf 1 θ i with hv
    have e1 : bOf c p z θ i = atomSum p z st (c * v) := by
      unfold bOf
      rw [aOf_mul]
    have e2 : bhat θ i = psiS s (cN N * v) := by
      unfold bhat
      rw [← aOf_cN hN, ← sOf_cN hN hm, aOf_mul]
    have b1 := hε st (c * v) hst0
    have b2 := psiS_lip_x st (c * v) (cN N * v)
    have b3 := psiS_lip_s st s (cN N * v)
    have e3 : |c * v - cN N * v| = (cN N - c) * |v| := by
      rw [← sub_mul, abs_mul, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ cN N - c)]
    have e4 : |st - s| = st - s := abs_of_nonneg (by linarith)
    rw [e3] at b2
    rw [e4] at b3
    have hε0 : 0 ≤ st * ε := (abs_nonneg _).trans b1
    have habs : |bOf c p z θ i - bhat θ i| ≤ st * ε + (cN N - c) * |v| + (st - s) := by
      rw [e1, e2]
      have : atomSum p z st (c * v) - psiS s (cN N * v) =
          (atomSum p z st (c * v) - psiS st (c * v)) +
            (psiS st (c * v) - psiS st (cN N * v)) +
            (psiS st (cN N * v) - psiS s (cN N * v)) := by ring
      rw [this]
      exact (abs_add_three _ _ _).trans (add_le_add (add_le_add b1 b2) b3)
    have hy0 : 0 ≤ (cN N - c) * |v| := mul_nonneg (by linarith) (abs_nonneg _)
    have hw0 : 0 ≤ st - s := by linarith
    have hsq : (bOf c p z θ i - bhat θ i) ^ 2 ≤
        (st * ε + (cN N - c) * |v| + (st - s)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hv2 : ((cN N - c) * |v|) ^ 2 = (cN N - c) ^ 2 * v ^ 2 := by
      rw [mul_pow, sq_abs]
    have h3 := sq_add3 (st * ε) ((cN N - c) * |v|) (st - s)
    rw [hv2, mul_pow] at h3
    refine (hsq.trans h3).trans (le_of_eq ?_)
    ring
  have hsum : normSq (bOf c p z θ - bhat θ) ≤
      (m : ℝ) * (3 * (st ^ 2 * ε ^ 2 + (st - s) ^ 2)) +
        3 * (cN N - c) ^ 2 * normSq (aOf 1 θ) := by
    have h1 : normSq (bOf c p z θ - bhat θ) = ∑ i, (bOf c p z θ i - bhat θ i) ^ 2 := rfl
    rw [h1]
    refine (Finset.sum_le_sum fun i _ => hcoord i).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have h2 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 / (m : ℝ))
  have e5 : 2 / (m : ℝ) * ((m : ℝ) * (3 * (st ^ 2 * ε ^ 2 + (st - s) ^ 2)) +
      3 * (cN N - c) ^ 2 * normSq (aOf 1 θ)) =
      6 * (st ^ 2 * ε ^ 2 + (st - s) ^ 2) +
        3 * (cN N - c) ^ 2 * (2 / (m : ℝ) * normSq (aOf 1 θ)) := by
    field_simp
    ring
  rw [e5] at h2
  have h7 : st ^ 2 * ε ^ 2 ≤ G * ε ^ 2 := mul_le_mul_of_nonneg_right hstG (sq_nonneg _)
  nlinarith

/-! ## The means over `θ` -/

/-- `E|M h|² = m·v·|h|²` for a Gaussian matrix `M` of entry variance `v`. -/
lemma layer_sq {k : ℕ} {v : ℝ} (hv : 0 ≤ v) (h : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => normSq (M.mulVec h)) (gaussMat m k v) ∧
      ∫ M : Matrix (Fin m) (Fin k) ℝ, normSq (M.mulVec h) ∂gaussMat m k v =
        (m : ℝ) * (v * normSq h) := by
  have hg : Measurable (fun y : Fin m → ℝ => normSq y) := measurable_normSq
  have e : ∀ ξ : Fin m → ℝ, normSq ((Real.sqrt v * Real.sqrt (normSq h)) • ξ) =
      (v * normSq h) * normSq ξ := by
    intro ξ
    rw [normSq_smul, sq_scale hv]
  refine ⟨layer_transfer_integrable v h hg ?_, ?_⟩
  · simp_rw [e]
    exact (gauss_normSq m).1.const_mul _
  · rw [layer_transfer v h hg]
    simp_rw [e]
    rw [integral_const_mul, (gauss_normSq m).2]
    ring

lemma measurable_rowS : Measurable (rowS : Matrix (Fin m) (Fin N) ℝ → ℝ) := by
  unfold rowS
  exact Finset.measurable_sum _ fun j _ => measurable_normSq.comp (measurable_rowOf j)

lemma measurable_aOf (c : ℝ) : Measurable (aOf c : HidParam N m → Fin m → ℝ) := by
  unfold aOf
  refine measurable_mulVec_joint.comp (measurable_snd.prodMk ?_)
  refine measurable_pi_iff.mpr fun j => ?_
  exact ((measurable_normSq.comp ((measurable_rowOf j).comp measurable_fst)).sqrt).const_mul c

lemma measurable_sOf (c : ℝ) : Measurable (sOf c : HidParam N m → ℝ) := by
  unfold sOf
  exact ((Finset.measurable_sum _ fun j _ =>
    measurable_normSq.comp ((measurable_rowOf j).comp measurable_fst)).mul_const _).sqrt

lemma measurable_atomSum {L : ℕ} (p z : Fin L → ℝ) :
    Measurable (fun q : ℝ × ℝ => atomSum p z q.1 q.2) := by
  unfold atomSum
  exact Finset.measurable_sum _ fun ℓ _ =>
    (measurable_relu.comp (measurable_snd.add (measurable_fst.mul_const _))).const_mul _

lemma measurable_bOf {L : ℕ} (c : ℝ) (p z : Fin L → ℝ) :
    Measurable (bOf c p z : HidParam N m → Fin m → ℝ) := by
  unfold bOf
  refine measurable_pi_iff.mpr fun i => ?_
  exact (measurable_atomSum p z).comp
    ((measurable_sOf c).prodMk ((measurable_pi_apply i).comp (measurable_aOf c)))

/-- `E_θ Γ* ≤ γ·√(1 + 5/m)`. -/
lemma GamS_mean (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun θ : HidParam N m => GamS θ.1) (hidGauss N m) ∧
      ∫ θ : HidParam N m, GamS θ.1 ∂hidGauss N m ≤ 2 / (N : ℝ) * √(1 + 5 / (m : ℝ)) := by
  have hL := ((GamS_L2 (m := m) hN hm).2).comp_fst (ν := gaussMat m m (2 / (m : ℝ)))
  have hi : Integrable (fun θ : HidParam N m => GamS θ.1) (hidGauss N m) := by
    unfold hidGauss
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hL.int_sq) hL.aesm
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (GamS_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (GamS θ.1 - 1)]
  refine ⟨hi, ?_⟩
  have h1 := sq_integral_le (ρ := hidGauss N m) (f := fun θ : HidParam N m => GamS θ.1)
    (by unfold hidGauss; exact hL.int_sq)
  have h2 : ∫ θ : HidParam N m, GamS θ.1 ^ 2 ∂hidGauss N m ≤
      (2 / (N : ℝ) * √(1 + 5 / (m : ℝ))) ^ 2 := by unfold hidGauss; exact hL.le
  have h0 : (0 : ℝ) ≤ 2 / (N : ℝ) * √(1 + 5 / (m : ℝ)) := by positivity
  exact (abs_le_of_sq_le_sq' (h1.trans h2) h0).2

/-- `E_θ t|M₂ρ|² = 4N·E Γ*`, `ρ_j = |row_j(M₁)|`. -/
lemma aOne_mean (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun θ : HidParam N m => 2 / (m : ℝ) * normSq (aOf 1 θ)) (hidGauss N m) ∧
      ∫ θ : HidParam N m, 2 / (m : ℝ) * normSq (aOf 1 θ) ∂hidGauss N m =
        4 * (N : ℝ) * ∫ θ : HidParam N m, GamS θ.1 ∂hidGauss N m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  obtain ⟨hGi, -⟩ := GamS_mean (m := m) hN hm
  have hrho : ∀ M₁ : Matrix (Fin m) (Fin N) ℝ,
      normSq (fun j => 1 * √(normSq (rowOf j M₁))) = rowS M₁ := by
    intro M₁
    unfold normSq rowS
    refine Finset.sum_congr rfl fun j _ => ?_
    show (1 * √(normSq (rowOf j M₁))) ^ 2 = normSq (rowOf j M₁)
    rw [one_mul, Real.sq_sqrt (normSq_nonneg _)]
  have hG1 : Integrable (fun M₁ : Matrix (Fin m) (Fin N) ℝ => GamS M₁)
      (gaussMat m N (2 / (N : ℝ))) := by
    have hL := (GamS_L2 (m := m) hN hm).2
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hL.int_sq) hL.aesm
      (Filter.Eventually.of_forall fun M₁ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (GamS_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (GamS M₁ - 1)]
  have step := prod_step (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    (f := fun θ : HidParam N m => 2 / (m : ℝ) * normSq (aOf 1 θ))
    ((measurable_normSq.comp (measurable_aOf 1)).const_mul _)
    (fun p => mul_nonneg h2 (normSq_nonneg _))
    (fun M₁ => 4 * (N : ℝ) * GamS M₁)
    (fun M₁ => by
      obtain ⟨hi, he⟩ := layer_sq (m := m) h2 (fun j => 1 * √(normSq (rowOf j M₁)))
      refine ⟨hi.const_mul _, ?_⟩
      have : ∫ y : Matrix (Fin m) (Fin m) ℝ, 2 / (m : ℝ) *
          normSq (aOf 1 ((M₁, y) : HidParam N m)) ∂gaussMat m m (2 / (m : ℝ)) =
          2 / (m : ℝ) * ∫ y : Matrix (Fin m) (Fin m) ℝ,
            normSq (y.mulVec (fun j => 1 * √(normSq (rowOf j M₁))))
            ∂gaussMat m m (2 / (m : ℝ)) := by
        rw [← integral_const_mul]
        rfl
      rw [this, he, hrho, GamS_rowS hN hm]
      field_simp
      ring)
    (hG1.const_mul _)
  refine ⟨step.1, ?_⟩
  have e := step.2
  unfold hidGauss
  rw [e, integral_const_mul]
  congr 1
  have step2 := prod_step (μ := gaussMat m N (2 / (N : ℝ))) (ν := gaussMat m m (2 / (m : ℝ)))
    (f := fun θ : HidParam N m => GamS θ.1)
    ((measurable_GamS hN).comp measurable_fst) (fun p => GamS_nonneg _)
    (fun M₁ => GamS M₁)
    (fun M₁ => show Integrable (fun _ : Matrix (Fin m) (Fin m) ℝ => GamS M₁) _ ∧
      ∫ _ : Matrix (Fin m) (Fin m) ℝ, GamS M₁ ∂gaussMat m m (2 / (m : ℝ)) = GamS M₁ from
      ⟨integrable_const _, by simp⟩) hG1
  exact step2.2.symm

/-- **`centre_mean`: the mean distance of the centre of a finite ReLU sum to the computed
centre.** -/
theorem centre_mean (hN : 1 ≤ N) (hm : 1 ≤ m) {L : ℕ} (p z : Fin L → ℝ) {c ε : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ cN N)
    (hε : ∀ s x : ℝ, 0 ≤ s → |atomSum p z s x - psiS s x| ≤ s * ε) :
    Integrable (fun θ : HidParam N m => 2 / (m : ℝ) * normSq (bOf c p z θ - bhat θ))
        (hidGauss N m) ∧
      ∫ θ : HidParam N m, 2 / (m : ℝ) * normSq (bOf c p z θ - bhat θ) ∂hidGauss N m ≤
        2 / (N : ℝ) * √(1 + 5 / (m : ℝ)) *
          (6 * ε ^ 2 + 24 * (N : ℝ) * cN N * (cN N - c) + 12 * (N : ℝ) * (cN N - c) ^ 2) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN := cN_nonneg N
  obtain ⟨hGi, hGm⟩ := GamS_mean (m := m) hN hm
  obtain ⟨hAi, hAm⟩ := aOne_mean (m := m) hN hm
  set α : ℝ := 6 * ε ^ 2 + 24 * (N : ℝ) * cN N * (cN N - c) with hα
  set β : ℝ := 3 * (cN N - c) ^ 2 with hβ
  have hα0 : 0 ≤ α := by
    have : 0 ≤ 24 * (N : ℝ) * cN N * (cN N - c) :=
      mul_nonneg (by positivity) (by linarith)
    rw [hα]; positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hdom : Integrable (fun θ : HidParam N m => GamS θ.1 * α +
      β * (2 / (m : ℝ) * normSq (aOf 1 θ))) (hidGauss N m) :=
    (hGi.mul_const _).add (hAi.const_mul _)
  have hmeas : Measurable (fun θ : HidParam N m =>
      2 / (m : ℝ) * normSq (bOf c p z θ - bhat θ)) :=
    (measurable_normSq.comp ((measurable_bOf c p z).sub (measurable_bhat hN))).const_mul _
  have hpt : ∀ θ : HidParam N m, 2 / (m : ℝ) * normSq (bOf c p z θ - bhat θ) ≤
      GamS θ.1 * α + β * (2 / (m : ℝ) * normSq (aOf 1 θ)) := fun θ =>
    centre_pt hN hm p z hc0 hc1 hε θ
  have hi : Integrable (fun θ : HidParam N m => 2 / (m : ℝ) * normSq (bOf c p z θ - bhat θ))
      (hidGauss N m) := by
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))]
    exact hpt θ
  refine ⟨hi, ?_⟩
  have hR : ∫ θ : HidParam N m, (GamS θ.1 * α + β * (2 / (m : ℝ) * normSq (aOf 1 θ)))
      ∂hidGauss N m = (∫ θ : HidParam N m, GamS θ.1 ∂hidGauss N m) * α +
        β * (4 * (N : ℝ) * ∫ θ : HidParam N m, GamS θ.1 ∂hidGauss N m) := by
    rw [integral_add (hGi.mul_const _) (hAi.const_mul _), integral_mul_const,
      integral_const_mul, hAm]
  have h1 := integral_mono hi hdom hpt
  rw [hR] at h1
  have hI0 : 0 ≤ ∫ θ : HidParam N m, GamS θ.1 ∂hidGauss N m :=
    integral_nonneg fun θ => GamS_nonneg _
  have h3 : (∫ θ : HidParam N m, GamS θ.1 ∂hidGauss N m) * (α + 4 * (N : ℝ) * β) ≤
      2 / (N : ℝ) * √(1 + 5 / (m : ℝ)) * (α + 4 * (N : ℝ) * β) :=
    mul_le_mul_of_nonneg_right hGm (by positivity)
  have e : α + 4 * (N : ℝ) * β =
      6 * ε ^ 2 + 24 * (N : ℝ) * cN N * (cN N - c) + 12 * (N : ℝ) * (cN N - c) ^ 2 := by
    rw [hα, hβ]; ring
  rw [e] at h3
  nlinarith

end BstLean.Part141

open BstLean.Part141 in
#print axioms centre_pt
open BstLean.Part141 in
#print axioms centre_mean
