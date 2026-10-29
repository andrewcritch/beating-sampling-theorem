import BstLean.Part136Det
import BstLean.Part133WorldR

/-!
# Part 136: the deterministic reduction on the sphere, and the quadratic bound of `κ∘κ`

Role: `delegations/statements/p136-spec.md`.

* `trS f`: `f` on the unit sphere and `0` elsewhere (a bounded measurable function that is equal
  to `f` almost everywhere for the uniform distribution on the sphere).
* `sphere_lin`: `E_u ⟨u, v⟩² = |v|²/N` (the kernel `(u, u′) ↦ ⟨u, u′⟩` has operator norm `1/N`).
* `quadF`, `quadF_dot`, `sphere_quad_frame`: the quadratic feature `u uᵀ − I/N`; its Gram kernel
  is `⟨u, u′⟩² − 1/N`; its frame bound is `2/(N(N + 2))`.
* `sphere_frame`: `det_frame` for a continuous feature map `h` on the sphere of `ℝ^N`, with
  `ℓ(u) = u`, `τ = 1/N` and `ℓ₂(u) = u uᵀ − I/N`, `τ₂ = 2/(N(N + 2))`.
* `kk_two`: `0 ≤ κ(κ(t)) − κ(κ(0)) − b·t ≤ (8/25)·t²` on `[−1, 1]`, with `0 ≤ b ≤ 3017/10000`
  (`b = (κ∘κ)′(0)`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part136

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134

variable {N m : ℕ}

/-- `f` on the unit sphere, `0` elsewhere. -/
noncomputable def trS (f : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) : ℝ :=
  if normSq u = 1 then f u else 0

lemma trS_of (f : (Fin N → ℝ) → ℝ) {u : Fin N → ℝ} (hu : normSq u = 1) : trS f u = f u := by
  simp [trS, hu]

lemma bm_trS {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) : BM (trS f) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin N => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  refine ⟨Measurable.ite (measurable_normSq (measurableSet_singleton 1)) hf.measurable
    measurable_const, max C 0, fun u => ?_⟩
  unfold trS
  split_ifs with hu
  · refine le_trans ?_ (le_max_left _ _)
    have hx : ∑ i, u i ^ 2 = 1 := hu
    rw [← Real.norm_eq_abs]
    apply hC
    apply Set.mem_image_of_mem
    constructor <;> intro i
    · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      rw [hx] at hi
      nlinarith [sq_nonneg (u i + 1)]
    · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
      rw [hx] at hi
      nlinarith [sq_nonneg (u i - 1)]
  · simp

/-- `E_u ⟨u, v⟩² = |v|²/N` on the unit sphere of `ℝ^N`. -/
lemma sphere_lin (hN : 1 ≤ N) (v : Fin N → ℝ) :
    ∫ u, (∑ i, u i * v i) ^ 2 ∂uniformSphere N = 1 / (N : ℝ) * ∑ i, v i ^ 2 := by
  have hmom := uniformSphere_moments N hN
  have e : ∀ u : Fin N → ℝ, (∑ i, u i * v i) ^ 2 = ∑ i, ∑ j, (u i * u j) * (v i * v j) := by
    intro u
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hi : ∀ i j, Integrable (fun u : Fin N → ℝ => (u i * u j) * (v i * v j))
      (uniformSphere N) := fun i j => (hmom.int2 i j).mul_const _
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  have : ∀ i : Fin N, ∫ u : Fin N → ℝ, ∑ j, (u i * u j) * (v i * v j) ∂uniformSphere N =
      1 / (N : ℝ) * v i ^ 2 := by
    intro i
    rw [integral_finsetSum _ fun j _ => hi i j]
    simp only [integral_mul_const, hmom.m2, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    ring
  simp_rw [this]
  rw [Finset.mul_sum]

/-! ## The quadratic feature `u ⊗ u − I/N` -/

lemma sum4Q (Q : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (((if i = j ∧ k = l then (1 : ℝ) else 0) +
      (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) *
      (Q i j * Q k l)) =
      (∑ i, Q i i) ^ 2 + ∑ i, ∑ j, Q i j ^ 2 + ∑ i, ∑ j, Q i j * Q j i := by
  have e1 : ∑ i, ∑ j, ∑ k, ∑ l, ((if i = j ∧ k = l then (1 : ℝ) else 0) *
      (Q i j * Q k l)) = (∑ i, Q i i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single k (fun l _ hl => ?_) (by simp)]
      · simp
      · simp [Ne.symm hl]
    · simp [Ne.symm hj]
  have e2 : ∑ i, ∑ j, ∑ k, ∑ l, ((if i = k ∧ j = l then (1 : ℝ) else 0) *
      (Q i j * Q k l)) = ∑ i, ∑ j, Q i j ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)]
    · rw [Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)]
      · simp; ring
      · simp [Ne.symm hl]
    · simp [Ne.symm hk]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, ((if i = l ∧ j = k then (1 : ℝ) else 0) *
      (Q i j * Q k l)) = ∑ i, ∑ j, Q i j * Q j i := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)]
    · rw [Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)]
      · simp
      · simp [Ne.symm hl]
    · simp [Ne.symm hk]
  simp only [add_mul, Finset.sum_add_distrib, e1, e2, e3]

/-- The quadratic feature of `u`: the entries of `u uᵀ − I/N`. -/
noncomputable def quadF (N : ℕ) (u : Fin N → ℝ) (p : Fin N × Fin N) : ℝ :=
  u p.1 * u p.2 - if p.1 = p.2 then 1 / (N : ℝ) else 0

/-- `⟨quadF u, quadF u′⟩ = ⟨u, u′⟩² − 1/N` for unit vectors. -/
lemma quadF_dot (hN : 1 ≤ N) {u u' : Fin N → ℝ} (hu : normSq u = 1) (hu' : normSq u' = 1) :
    ∑ p, quadF N u p * quadF N u' p = dotp u u' ^ 2 - 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ i, u i ^ 2 = 1 := hu
  have h2 : ∑ i, u' i ^ 2 = 1 := hu'
  rw [Fintype.sum_prod_type]
  simp only [quadF]
  have e : ∀ i j : Fin N, (u i * u j - if i = j then 1 / (N : ℝ) else 0) *
      (u' i * u' j - if i = j then 1 / (N : ℝ) else 0) =
      (u i * u' i) * (u j * u' j) - (if i = j then 1 / (N : ℝ) * (u' i * u' j) else 0) -
        (if i = j then 1 / (N : ℝ) * (u i * u j) else 0) +
        (if i = j then 1 / (N : ℝ) ^ 2 else 0) := by
    intro i j
    split_ifs <;> ring
  simp_rw [e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have e1 : ∑ i, ∑ j, (u i * u' i) * (u j * u' j) = dotp u u' ^ 2 := by
    unfold dotp
    rw [sq, Finset.sum_mul_sum]
  have e2 : ∑ i : Fin N, 1 / (N : ℝ) * (u' i * u' i) = 1 / (N : ℝ) := by
    rw [← Finset.mul_sum]
    have : ∑ i, u' i * u' i = 1 := by rw [← h2]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, mul_one]
  have e3 : ∑ i : Fin N, 1 / (N : ℝ) * (u i * u i) = 1 / (N : ℝ) := by
    rw [← Finset.mul_sum]
    have : ∑ i, u i * u i = 1 := by rw [← h1]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, mul_one]
  rw [e1, e2, e3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The quadratic feature is centred. -/
lemma quadF_mean (hN : 1 ≤ N) (p : Fin N × Fin N) :
    ∫ u, quadF N u p ∂uniformSphere N = 0 := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  unfold quadF
  rw [integral_sub (hmom.int2 p.1 p.2) (integrable_const _), hmom.m2]
  simp

/-- **The frame bound of the quadratic feature**: `E_u ⟨u uᵀ − I/N, Q⟩² ≤ 2|Q|²/(N(N + 2))`
(the kernel `(u, u′) ↦ ⟨u, u′⟩² − 1/N` has operator norm at most `2/(N(N + 2))`). -/
lemma sphere_quad_frame (hN : 1 ≤ N) (Q : Fin N × Fin N → ℝ) :
    ∫ u, (∑ p, quadF N u p * Q p) ^ 2 ∂uniformSphere N ≤
      2 / ((N : ℝ) * (N + 2)) * ∑ p, Q p ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set T : ℝ := ∑ i, Q (i, i) with hT
  set A : (Fin N → ℝ) → ℝ := fun u => ∑ i, ∑ j, Q (i, j) * (u i * u j) with hA
  have e0 : ∀ u : Fin N → ℝ, ∑ p, quadF N u p * Q p = A u - T / (N : ℝ) := by
    intro u
    rw [Fintype.sum_prod_type]
    simp only [quadF, hA, hT]
    have e : ∀ i j : Fin N, (u i * u j - if i = j then 1 / (N : ℝ) else 0) * Q (i, j) =
        Q (i, j) * (u i * u j) - (if i = j then 1 / (N : ℝ) * Q (i, j) else 0) := by
      intro i j
      split_ifs <;> ring
    simp_rw [e]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Finset.mul_sum]
    ring
  have iA2 : ∀ i j, Integrable (fun u : Fin N → ℝ => Q (i, j) * (u i * u j))
      (uniformSphere N) := fun i j => (hmom.int2 i j).const_mul _
  have iA : Integrable A (uniformSphere N) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA2 i j
  have mA : ∫ u, A u ∂uniformSphere N = T / (N : ℝ) := by
    simp only [hA]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iA2 i j]
    have : ∀ i : Fin N, ∫ u : Fin N → ℝ, ∑ j, Q (i, j) * (u i * u j) ∂uniformSphere N =
        Q (i, i) * (1 / (N : ℝ)) := by
      intro i
      rw [integral_finsetSum _ fun j _ => iA2 i j]
      simp only [integral_const_mul, hmom.m2, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    simp_rw [this]
    rw [← Finset.sum_mul, hT]
    ring
  have eA2 : ∀ u : Fin N → ℝ, A u ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l, (Q (i, j) * Q (k, l)) * (u i * u j * u k * u l) := by
    intro u
    rw [sq]
    simp only [hA, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have i4 : ∀ i j k l, Integrable (fun u : Fin N → ℝ =>
      (Q (i, j) * Q (k, l)) * (u i * u j * u k * u l)) (uniformSphere N) := fun i j k l =>
    (hmom.int4 i j k l).const_mul _
  have iAsq : Integrable (fun u => A u ^ 2) (uniformSphere N) := by
    simp_rw [eA2]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => i4 i j k l
  have mA2 : ∫ u, A u ^ 2 ∂uniformSphere N =
      (T ^ 2 + ∑ i, ∑ j, Q (i, j) ^ 2 + ∑ i, ∑ j, Q (i, j) * Q (j, i)) /
        ((N : ℝ) * (N + 2)) := by
    simp_rw [eA2]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => i4 i j k l]
    have s1 : ∀ i : Fin N, ∫ u : Fin N → ℝ, ∑ j, ∑ k, ∑ l,
        (Q (i, j) * Q (k, l)) * (u i * u j * u k * u l) ∂uniformSphere N =
        ∑ j, ∑ k, ∑ l, (((if i = j ∧ k = l then (1 : ℝ) else 0) +
        (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) *
        (Q (i, j) * Q (k, l))) / ((N : ℝ) * (N + 2)) := by
      intro i
      rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
        integrable_finsetSum _ fun l _ => i4 i j k l]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => i4 i j k l]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun l _ => i4 i j k l]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_const_mul, hmom.m4]
      ring
    simp only [s1, ← Finset.sum_div]
    rw [sum4Q (fun i j => Q (i, j))]
  have hS' : ∑ i, ∑ j, Q (i, j) * Q (j, i) ≤ ∑ i, ∑ j, Q (i, j) ^ 2 := by
    have h0 : 0 ≤ ∑ i, ∑ j, (Q (i, j) - Q (j, i)) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have e : ∀ i j : Fin N, (Q (i, j) - Q (j, i)) ^ 2 =
        Q (i, j) ^ 2 - 2 * (Q (i, j) * Q (j, i)) + Q (j, i) ^ 2 := fun i j => by ring
    simp_rw [e] at h0
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h0
    have hc : ∑ i, ∑ j, Q (j, i) ^ 2 = ∑ i, ∑ j, Q (i, j) ^ 2 := Finset.sum_comm
    rw [hc] at h0
    linarith
  have eS : ∑ p, Q p ^ 2 = ∑ i, ∑ j, Q (i, j) ^ 2 := Fintype.sum_prod_type _
  simp_rw [e0]
  have esq : ∀ u : Fin N → ℝ, (A u - T / (N : ℝ)) ^ 2 =
      A u ^ 2 - 2 * (T / (N : ℝ)) * A u + (T / (N : ℝ)) ^ 2 := fun u => by ring
  simp_rw [esq]
  have j1 : Integrable (fun u => A u ^ 2 - 2 * (T / (N : ℝ)) * A u) (uniformSphere N) :=
    iAsq.sub (iA.const_mul _)
  rw [integral_add j1 (integrable_const _), integral_sub iAsq (iA.const_mul _),
    integral_const_mul, mA, mA2, eS]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hD : (0 : ℝ) < (N : ℝ) * (N + 2) := by positivity
  have h1 : T ^ 2 / ((N : ℝ) * (N + 2)) ≤ (T / (N : ℝ)) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have h2 : (∑ i, ∑ j, Q (i, j) * Q (j, i)) / ((N : ℝ) * (N + 2)) ≤
      (∑ i, ∑ j, Q (i, j) ^ 2) / ((N : ℝ) * (N + 2)) :=
    div_le_div_of_nonneg_right hS' hD.le
  rw [add_div, add_div]
  have e3 : 2 / ((N : ℝ) * (N + 2)) * ∑ i, ∑ j, Q (i, j) ^ 2 =
      (∑ i, ∑ j, Q (i, j) ^ 2) / ((N : ℝ) * (N + 2)) +
        (∑ i, ∑ j, Q (i, j) ^ 2) / ((N : ℝ) * (N + 2)) := by ring
  rw [e3]
  nlinarith

/-- **The deterministic reduction on the sphere.** `h` is a continuous feature map on `ℝ^N`,
`μ` the uniform distribution on the unit sphere, `G(u, u′) = ⟨h(u), h(u′)⟩`, `t = ⟨u, u′⟩`. If
`‖G − a − c·t − c₂·(t² − 1/N)‖_{L²} ≤ Δ` and `‖G(u, u) − d‖_{L²} ≤ δ`, then `h̄ ≠ 0` and the unit
residual directions have the frame bound
`(c/N + 2c₂/(N(N + 2)) + Δ)/s + Δ²/ε₂² + δ²/ε₁²`. -/
theorem sphere_frame (hN : 1 ≤ N) {h : (Fin N → ℝ) → Fin m → ℝ} (hcont : Continuous h)
    {a c c₂ Δ d δ ε₁ ε₂ s : ℝ} (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) (hΔ : 0 ≤ Δ) (hε₁ : 0 < ε₁)
    (hε₂ : 0 < ε₂) (haΔ : Δ < a)
    (hD : ∫ uu, (dotp (h uu.1) (h uu.2) - a - c * dotp uu.1 uu.2 -
      c₂ * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ))) ^ 2 ∂lawU2 N ≤ Δ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂uniformSphere N ≤ δ ^ 2)
    (hs : 0 < s) (hsle : s ≤ d - ε₁ - (a + ε₂) ^ 2 / (a - Δ)) :
    hbar (uniformSphere N) h ≠ 0 ∧ ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, eDir (hbar (uniformSphere N) h) (h u) j * w j) ^ 2 ∂uniformSphere N ≤
        ((c * (1 / (N : ℝ)) + c₂ * (2 / ((N : ℝ) * (N + 2))) + Δ) / s + Δ ^ 2 / ε₂ ^ 2 +
          δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set hT : (Fin N → ℝ) → Fin m → ℝ := fun u j => trS (fun u => h u j) u with hhT
  set ℓT : (Fin N → ℝ) → Fin N → ℝ := fun u i => trS (fun u => u i) u with hℓT
  set qT : (Fin N → ℝ) → Fin N × Fin N → ℝ := fun u p => trS (fun u => quadF N u p) u with hqT
  have bh : ∀ j, BM (fun u => hT u j) := fun j =>
    bm_trS ((continuous_apply j).comp hcont)
  have bℓ : ∀ i, BM (fun u => ℓT u i) := fun i => bm_trS (continuous_apply i)
  have bq : ∀ p, BM (fun u => qT u p) := fun p => bm_trS (by
    unfold quadF
    exact ((continuous_apply p.1).mul (continuous_apply p.2)).sub continuous_const)
  have ptT : ∀ u : Fin N → ℝ, normSq u = 1 → hT u = h u ∧ ℓT u = u ∧ qT u = quadF N u := by
    intro u hu
    refine ⟨funext fun j => ?_, funext fun i => ?_, funext fun p => ?_⟩
    · simp only [hhT]; exact trS_of _ hu
    · simp only [hℓT]; exact trS_of _ hu
    · simp only [hqT]; exact trS_of _ hu
  have aeT : ∀ᵐ u ∂uniformSphere N, hT u = h u ∧ ℓT u = u ∧ qT u = quadF N u := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu using ptT u hu
  have ebar : hbar (uniformSphere N) hT = hbar (uniformSphere N) h := by
    funext j
    unfold hbar
    refine integral_congr_ae ?_
    filter_upwards [aeT] with u hu
    rw [hu.1]
  have hℓ0 : ∀ i, ∫ u, ℓT u i ∂uniformSphere N = 0 := by
    intro i
    rw [← hmom.m1 i]
    refine integral_congr_ae ?_
    filter_upwards [aeT] with u hu
    rw [hu.2.1]
  have hq0 : ∀ p, ∫ u, qT u p ∂uniformSphere N = 0 := by
    intro p
    rw [← quadF_mean hN p]
    refine integral_congr_ae ?_
    filter_upwards [aeT] with u hu
    rw [hu.2.2]
  have hτ : ∀ v : Fin N → ℝ, ∫ u, (∑ i, ℓT u i * v i) ^ 2 ∂uniformSphere N ≤
      1 / (N : ℝ) * ∑ i, v i ^ 2 := by
    intro v
    rw [← sphere_lin hN v]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [aeT] with u hu
    rw [hu.2.1]
  have hτ₂ : ∀ v : Fin N × Fin N → ℝ, ∫ u, (∑ p, qT u p * v p) ^ 2 ∂uniformSphere N ≤
      2 / ((N : ℝ) * (N + 2)) * ∑ p, v p ^ 2 := by
    intro v
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (sphere_quad_frame hN v)
    filter_upwards [aeT] with u hu
    rw [hu.2.2]
  have hD' : ∫ p, (∑ k, hT p.1 k * hT p.2 k - a - c * ∑ i, ℓT p.1 i * ℓT p.2 i -
      c₂ * ∑ i, qT p.1 i * qT p.2 i) ^ 2
      ∂((uniformSphere N).prod (uniformSphere N)) ≤ Δ ^ 2 := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hD
    have hu2 := lawU2_ae_unit hN
    unfold lawU2 at hu2
    filter_upwards [hu2] with uu huu
    rw [(ptT uu.1 huu.1).1, (ptT uu.1 huu.1).2.1, (ptT uu.2 huu.2).1, (ptT uu.2 huu.2).2.1,
      (ptT uu.1 huu.1).2.2, (ptT uu.2 huu.2).2.2, quadF_dot hN huu.1 huu.2]
    rfl
  have hd' : ∫ u, (normSq (hT u) - d) ^ 2 ∂uniformSphere N ≤ δ ^ 2 := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hd
    filter_upwards [aeT] with u hu
    rw [hu.1]
  obtain ⟨h1, h2⟩ := det_frame (uniformSphere N) bh bℓ bq hℓ0 hq0 (by positivity)
    (by positivity) hτ hτ₂ hc hc₂ hΔ hε₁ hε₂ haΔ hD' hd' hs hsle
  rw [ebar] at h1 h2
  refine ⟨h1, fun w => le_trans (le_of_eq (integral_congr_ae ?_)) (h2 w)⟩
  filter_upwards [aeT] with u hu
  rw [hu.1]

/-! ## The quadratic bound of `κ∘κ` -/

/-- `0 ≤ κ(κ(t)) − κ(κ(0)) − b·t ≤ (8/25)·t²` on `[−1, 1]`, with one slope `b`,
`0 ≤ b ≤ 3017/10000`. -/
theorem kk_two : ∃ b : ℝ, 0 ≤ b ∧ b ≤ 3017 / 10000 ∧ ∀ t ∈ Icc (-1 : ℝ) 1,
    0 ≤ kappa (kappa t) - kappa (kappa 0) - b * t ∧
    kappa (kappa t) - kappa (kappa 0) - b * t ≤ 8 / 25 * t ^ 2 := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (π - Real.arccos (kappa 0)) / π := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := hβ ▸ kappa_beta_bounds.1
  have hβ1 : β ≤ 6034 / 10000 := hβ ▸ kappa_beta_bounds.2
  -- the upper bound (the proof of `kk_quad` of Part 132, with the slope kept)
  have hup : ∀ t ∈ Icc (-1 : ℝ) 1,
      kappa (kappa t) ≤ kappa (kappa 0) + β / 2 * t + 8 / 25 * t ^ 2 := by
    intro t ht
    have hs := kappa_mem ht.1 ht.2
    have hU := kappa_le_quad ht.1 ht.2
    have hL := kappa_ge_lin ht.1 ht.2
    have h2 := kappa_le_quad_at hs.1 hs.2
    rw [← hβ] at h2
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = kappa t - kappa 0 := ⟨_, rfl⟩
    rw [← hδ] at h2
    have hδ1 : t / 2 ≤ δ := by linarith
    have hδ2 : δ ≤ t / 2 + t ^ 2 / 4 := by linarith
    have hsq : δ ^ 2 ≤ 9 / 16 * t ^ 2 := by
      rcases le_total 0 t with h0 | h0
      · have hδ0 : 0 ≤ δ := by linarith
        have hδ3 : δ ≤ 3 / 4 * t := by nlinarith [ht.2]
        have := mul_le_mul hδ3 hδ3 hδ0 (by linarith)
        nlinarith
      · have hδ0 : 0 ≤ -δ := by nlinarith [ht.1]
        have hδ3 : -δ ≤ -t / 2 := by linarith
        have := mul_le_mul hδ3 hδ3 hδ0 (by linarith)
        nlinarith [sq_nonneg t]
    have h3 : β * δ ≤ β * (t / 2 + t ^ 2 / 4) := mul_le_mul_of_nonneg_left hδ2 hβ0
    have h4 : β * t ^ 2 ≤ 6034 / 10000 * t ^ 2 := mul_le_mul_of_nonneg_right hβ1 (sq_nonneg t)
    nlinarith [sq_nonneg t]
  -- the supporting line at `0` has the same slope
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  obtain ⟨a', b', -, -, -, -, heq, hsup⟩ := hG.support (t := 0) ⟨by norm_num, by norm_num⟩
  simp only [Function.comp, mul_zero, add_zero] at heq hsup
  have hb' : b' = β / 2 := by
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      set e := b' - β / 2 with he
      have he0 : 0 < e := by linarith
      set t := min 1 e with ht
      have ht0 : 0 < t := lt_min one_pos he0
      have ht1 : t ≤ 1 := min_le_left _ _
      have hte : t ≤ e := min_le_right _ _
      have l := hsup t ⟨by linarith, ht1⟩
      have u := hup t ⟨by linarith, ht1⟩
      have h1 : e * t ≤ 8 / 25 * t ^ 2 := by
        have : b' * t = β / 2 * t + e * t := by rw [he]; ring
        linarith
      nlinarith
    · by_contra hlt
      rw [not_le] at hlt
      set e := β / 2 - b' with he
      have he0 : 0 < e := by linarith
      set t := min 1 e with ht
      have ht0 : 0 < t := lt_min one_pos he0
      have ht1 : t ≤ 1 := min_le_left _ _
      have hte : t ≤ e := min_le_right _ _
      have l := hsup (-t) ⟨by linarith, by linarith⟩
      have u := hup (-t) ⟨by linarith, by linarith⟩
      have h1 : e * t ≤ 8 / 25 * t ^ 2 := by
        have : b' * t = β / 2 * t - e * t := by rw [he]; ring
        nlinarith
      nlinarith
  refine ⟨β / 2, by linarith, by linarith, fun t ht => ⟨?_, ?_⟩⟩
  · have l := hsup t ht
    rw [hb', heq] at l
    linarith
  · have u := hup t ht
    linarith

end BstLean.Part136
