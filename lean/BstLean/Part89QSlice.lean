import BstLean.Part89QDefs
import BstLean.Part80MeanIds
import BstLean.Part80VarBound_B
import BstLean.Part80CondBounds

/-!
# Part 89: `quadSlice`, the variance bound in one slice at `d_f = 2`

In a slice `p` the distribution of `x` is `ν_p = map (X (p, ·)) γ`, a distribution on the sphere.
The polynomial is `FA f0 ℓ H mu ψ` with `mu x = Σ_j b_j(x) A_j`, `ψ x = lam·sc·ps x`. The floor of
`V̄` comes from `meanIdsA` and Bessel; the variance bound from `varBoundA3` after a rescaling that
makes `kA ≤ 2`.
-/

namespace BstLean.Part89

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (varU)
open BstLean.Part56 (integrable_cont_sph56)
open BstLean.Part78 (nsq frobH qfun aU zv)
open BstLean.Part80 (FA VA VbarA kA KA aA TaA S2A eA PhiA FeatOpA meanIdsA varBoundA3 besselA
  sq_int_le dbl_int cont_aA cont_kA cont_psi cont_mu cont_FA)
open BstLean.Part86

section abs
variable {n : ℕ} {J : Type} [Fintype J]

/-- `‖u‖² ≤ (1+η)‖v‖² + (1+1/η)‖u − v‖²`. -/
lemma nsq_young (u v : Fin n → ℝ) (η : ℝ) (hη : 0 < η) :
    nsq u ≤ (1 + η) * nsq v + (1 + 1 / η) * nsq (fun i => u i - v i) := by
  unfold nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : 0 ≤ (η * v i - (u i - v i)) ^ 2 / η := by positivity
  have e : (η * v i - (u i - v i)) ^ 2 / η =
      (1 + η) * v i ^ 2 + (1 + 1 / η) * (u i - v i) ^ 2 - u i ^ 2 := by
    field_simp; ring
  linarith

/-- The floor of `V̄`: `(1−Λ)(t A + 2 ‖H‖² t²) ≤ V̄`, `A = E‖a‖²`. -/
lemma floorA {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν) (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (mu : (Fin n → ℝ) → Fin n → ℝ)
    (ψ : (Fin n → ℝ) → J → ℝ) (hmu : Continuous mu) (hψ : Continuous ψ) (Lam t : ℝ)
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1) (ht : 0 ≤ t)
    (hF : FeatOpA ν ψ (Lam * t)) (hkt : ∀ᵐ x ∂ν, t ≤ kA ψ x) :
    (1 - Lam) * (t * ∫ x, nsq (aA ℓ H mu x) ∂ν) + 2 * (1 - Lam) * frobH H * t ^ 2 ≤
      VbarA ν f0 ℓ H mu ψ := by
  obtain ⟨-, -, -, -, hV⟩ := meanIdsA n J ν hν f0 ℓ H hH mu ψ hmu hψ
  have := hν.prob
  have hΓ : 0 ≤ Lam * t := mul_nonneg hL0 ht
  have sint {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable f ν :=
    integrable_cont_sph56 hν hf
  have sint2 {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : Integrable (fun x => f x ^ 2) ν :=
    sint (hf.pow 2)
  have hψq (q : J) : Continuous fun x => ψ x q := (continuous_apply q).comp hψ
  have ha (i : Fin n) : Continuous fun x => aA ℓ H mu x i := cont_aA hmu i
  have hk : Continuous (kA ψ) := continuous_finsetSum _ fun q _ => (hψq q).pow 2
  have hA : Continuous fun x => nsq (aA ℓ H mu x) :=
    continuous_finsetSum _ fun i _ => (ha i).pow 2
  have hA0 (x : Fin n → ℝ) : 0 ≤ nsq (aA ℓ H mu x) := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hv0 : 0 ≤ frobH H :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hTa : TaA ν ℓ H mu ψ = ∑ i, ∑ q, (∫ x, aA ℓ H mu x i * ψ x q ∂ν) ^ 2 := by
    have := dbl_int hν (R := Fin n × J) (fun r x => aA ℓ H mu x r.1 * ψ x r.2)
      (fun r => (ha r.1).mul (hψq r.2))
    rw [Fintype.sum_prod_type] at this
    rw [← this]
    unfold TaA KA
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
  have hS2 : S2A ν ψ = ∑ p, ∑ q, (∫ x, ψ x p * ψ x q ∂ν) ^ 2 := by
    have := dbl_int hν (R := J × J) (fun r x => ψ x r.1 * ψ x r.2)
      (fun r => (hψq r.1).mul (hψq r.2))
    rw [Fintype.sum_prod_type] at this
    rw [← this]
    unfold S2A KA
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => by ring
  have hAint : ∫ x, nsq (aA ℓ H mu x) ∂ν = ∑ i, ∫ x, aA ℓ H mu x i ^ 2 ∂ν := by
    unfold nsq
    exact integral_finsetSum _ fun i _ => sint2 (ha i)
  have heint : ∫ x, kA ψ x ∂ν = ∑ q, ∫ x, ψ x q ^ 2 ∂ν := by
    unfold kA
    exact integral_finsetSum _ fun q _ => sint2 (hψq q)
  have hTa1 : TaA ν ℓ H mu ψ ≤ Lam * t * ∫ x, nsq (aA ℓ H mu x) ∂ν := by
    rw [hTa, hAint, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => besselA hν hψ hΓ hF _ (ha i)
  have hS21 : S2A ν ψ ≤ Lam * t * ∫ x, kA ψ x ∂ν := by
    rw [hS2, heint, Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => besselA hν hψ hΓ hF _ (hψq p)
  have hAk : t * ∫ x, nsq (aA ℓ H mu x) ∂ν ≤ ∫ x, nsq (aA ℓ H mu x) * kA ψ x ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae ((sint hA).const_mul _) (sint (hA.mul hk)) (hkt.mono fun x hx => ?_)
    show t * nsq (aA ℓ H mu x) ≤ nsq (aA ℓ H mu x) * kA ψ x
    nlinarith [hA0 x]
  have het : t ≤ ∫ x, kA ψ x ∂ν := by
    have h : ∫ _x, t ∂ν ≤ ∫ x, kA ψ x ∂ν :=
      integral_mono_ae (integrable_const _) (sint hk) hkt
    simpa using h
  have hkk : t * ∫ x, kA ψ x ∂ν ≤ ∫ x, kA ψ x ^ 2 ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae ((sint hk).const_mul _) (sint (hk.pow 2)) (hkt.mono fun x hx => ?_)
    show t * kA ψ x ≤ kA ψ x ^ 2
    nlinarith
  have hvar : 0 ≤ varU ν (PhiA f0 ℓ H mu ψ) := integral_nonneg fun x => sq_nonneg _
  have hL : 0 ≤ 1 - Lam := by linarith
  have h1 : 0 ≤ (1 - Lam) * t * (∫ x, kA ψ x ∂ν - t) :=
    mul_nonneg (mul_nonneg hL ht) (by linarith)
  have h2 : 0 ≤ frobH H * ((∫ x, kA ψ x ^ 2 ∂ν - S2A ν ψ) - (1 - Lam) * t ^ 2) := by
    refine mul_nonneg hv0 ?_
    nlinarith
  rw [hV]
  nlinarith

/-- The variance bound in the abstract conditional model, with a floor level `t` and a ceiling
`K` of `kA`, and a bound `D` of the oscillation of `a`. -/
lemma varSliceA {ν : Measure (Fin n → ℝ)} (hν : SphLaw n ν) (f0 : ℝ) (ℓ : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (mu : (Fin n → ℝ) → Fin n → ℝ)
    (ψ : (Fin n → ℝ) → J → ℝ) (hmu : Continuous mu) (hψ : Continuous ψ) (Lam t K D η η' : ℝ)
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (ht : 0 ≤ t) (hK : 0 < K) (hη : 0 < η) (hη' : 0 < η')
    (hF : FeatOpA ν ψ (Lam * t)) (hkt : ∀ᵐ x ∂ν, t ≤ kA ψ x)
    (hkK : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → kA ψ x ≤ K)
    (hD : ∀ x y : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → ∑ i, y i ^ 2 = 1 →
      nsq (fun i => aA ℓ H mu x i - aA ℓ H mu y i) ≤ D) :
    ∫ W, (VA ν f0 ℓ H mu ψ W - VbarA ν f0 ℓ H mu ψ) ^ 2 ∂stdGauss (J × Fin n) ≤
      2 * Lam * (2 + η) * (1 + η') / (1 - Lam) * VbarA ν f0 ℓ H mu ψ ^ 2 +
      2 * Lam * t * ((2 + η) * (1 + 1 / η') * D + c0q η * (K / 2) * frobH H) *
        VbarA ν f0 ℓ H mu ψ := by
  have := hν.prob
  have hv0 : 0 ≤ frobH H :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = Real.sqrt (K / 2) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθd]; exact Real.sqrt_pos.2 (by linarith)
  have hθ2 : θ ^ 2 = K / 2 := by rw [hθd]; exact Real.sq_sqrt (by linarith)
  have hθne : θ ≠ 0 := hθ.ne'
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n → ℝ, ∀ i, ℓ' i = θ * ℓ i := ⟨fun i => θ * ℓ i, fun _ => rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin n) (Fin n) ℝ, ∀ i j, H' i j = θ ^ 2 * H i j :=
    ⟨fun i j => θ ^ 2 * H i j, fun _ _ => rfl⟩
  have hH's : H'.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply, hH', hH', hH.apply]
  obtain ⟨mu', hmu'⟩ : ∃ mu' : (Fin n → ℝ) → Fin n → ℝ, ∀ x i, mu' x i = mu x i / θ :=
    ⟨fun x i => mu x i / θ, fun _ _ => rfl⟩
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : (Fin n → ℝ) → J → ℝ, ∀ x q, ψ' x q = ψ x q / θ :=
    ⟨fun x q => ψ x q / θ, fun _ _ => rfl⟩
  have hmu'c : Continuous mu' := by
    refine continuous_pi fun i => ?_
    simp only [hmu']
    exact (cont_mu hmu i).div_const θ
  have hψ'c : Continuous ψ' := by
    refine continuous_pi fun q => ?_
    simp only [hψ']
    exact (cont_psi hψ q).div_const θ
  have hFA : FA f0 ℓ' H' mu' ψ' = FA f0 ℓ H mu ψ := by
    funext W x
    have hz (i : Fin n) : zv W (ψ' x) i = zv W (ψ x) i / θ := by
      unfold zv
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun q _ => by rw [hψ']; ring
    unfold FA qfun
    simp only [hz, hℓ', hH', hmu']
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun i _ => by field_simp
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by field_simp
  have hVA : VA ν f0 ℓ' H' mu' ψ' = VA ν f0 ℓ H mu ψ := by
    funext W; unfold VA; rw [hFA]
  have hVb : VbarA ν f0 ℓ' H' mu' ψ' = VbarA ν f0 ℓ H mu ψ := by
    unfold VbarA; rw [hVA]
  have hkA (x : Fin n → ℝ) : kA ψ' x = kA ψ x / θ ^ 2 := by
    unfold kA
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun q _ => by rw [hψ', div_pow]
  have haA (x : Fin n → ℝ) (i : Fin n) : aA ℓ' H' mu' x i = θ * aA ℓ H mu x i := by
    unfold aA aU
    have e : ∑ j, H' i j * mu' x j = θ * ∑ j, H i j * mu x j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hH', hmu']; field_simp
    rw [e, hℓ']; ring
  have hnsq (x : Fin n → ℝ) : nsq (aA ℓ' H' mu' x) = θ ^ 2 * nsq (aA ℓ H mu x) := by
    unfold nsq
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [haA]; ring
  have hfrob : frobH H' = θ ^ 4 * frobH H := by
    unfold frobH
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hH']; ring
  have hF' : FeatOpA ν ψ' (Lam * t / θ ^ 2) := by
    intro c
    have h := hF c
    have e : (fun x => (∑ q, c q * ψ' x q) ^ 2) = fun x => (∑ q, c q * ψ x q) ^ 2 / θ ^ 2 := by
      funext x
      rw [← div_pow, Finset.sum_div]
      congr 1
      exact Finset.sum_congr rfl fun q _ => by rw [hψ']; ring
    rw [e, integral_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right h (sq_nonneg θ)
  -- the sup of `‖a‖²`
  have hA : Continuous fun x => nsq (aA ℓ H mu x) :=
    continuous_finsetSum _ fun i _ => (cont_aA hmu i).pow 2
  have iA : Integrable (fun x => nsq (aA ℓ H mu x)) ν := integrable_cont_sph56 hν hA
  obtain ⟨Am, hAm⟩ : ∃ Am : ℝ, Am = ∫ x, nsq (aA ℓ H mu x) ∂ν := ⟨_, rfl⟩
  have hc1 : 0 ≤ 1 + 1 / η' := by positivity
  have hS (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
      nsq (aA ℓ H mu x) ≤ (1 + η') * Am + (1 + 1 / η') * D := by
    have h : ∫ _y, nsq (aA ℓ H mu x) ∂ν ≤
        ∫ y, ((1 + η') * nsq (aA ℓ H mu y) + (1 + 1 / η') * D) ∂ν := by
      refine integral_mono_ae (integrable_const _) ((iA.const_mul _).add (integrable_const _))
        (hν.sphere.mono fun y hy => ?_)
      have h1 := nsq_young (aA ℓ H mu x) (aA ℓ H mu y) η' hη'
      have h2 := mul_le_mul_of_nonneg_left (hD x y hx hy) hc1
      show nsq (aA ℓ H mu x) ≤ (1 + η') * nsq (aA ℓ H mu y) + (1 + 1 / η') * D
      linarith
    rw [integral_add (iA.const_mul _) (integrable_const _), integral_const_mul, ← hAm] at h
    simpa using h
  have hΓ : 0 ≤ Lam * t / θ ^ 2 := div_nonneg (mul_nonneg hL0 ht) (sq_nonneg θ)
  have hvb := varBoundA3 n J ν hν f0 ℓ' H' hH's mu' ψ' hmu'c hψ'c (Lam * t / θ ^ 2)
    (θ ^ 2 * ((1 + η') * Am + (1 + 1 / η') * D)) η hΓ hη hF' (fun x hx => by
      refine ⟨?_, ?_⟩
      · rw [hnsq]; exact mul_le_mul_of_nonneg_left (hS x hx) (sq_nonneg θ)
      · rw [hkA, div_le_iff₀ (by positivity)]
        have := hkK x hx
        linarith)
  rw [hVA, hVb, hfrob] at hvb
  have hfl := floorA hν f0 ℓ H hH mu ψ hmu hψ Lam t hL0 (by linarith) ht hF hkt
  rw [← hAm] at hfl
  obtain ⟨Vb, hVbd⟩ : ∃ Vb : ℝ, Vb = VbarA ν f0 ℓ H mu ψ := ⟨_, rfl⟩
  rw [← hVbd] at hvb hfl ⊢
  have hL : 0 < 1 - Lam := by linarith
  have hAm0 : 0 ≤ Am := by
    rw [hAm]; exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hp1 : 0 ≤ 2 * (1 - Lam) * frobH H * t ^ 2 := by positivity
  have hp2 : 0 ≤ (1 - Lam) * (t * Am) := by positivity
  have hVb0 : 0 ≤ Vb := by linarith
  have key : t * Am ≤ Vb / (1 - Lam) := by
    rw [le_div_iff₀ hL]
    linarith
  have hc : 0 ≤ 2 * Lam * (2 + η) * (1 + η') * Vb := by positivity
  have hm := mul_le_mul_of_nonneg_left key hc
  refine hvb.trans ?_
  have e1 : 2 * (Lam * t / θ ^ 2) * ((2 + η) * (θ ^ 2 * ((1 + η') * Am + (1 + 1 / η') * D)) +
      ((1 + 1 / η) * ((4184 / 1000) * (8 * (1733 / 1000))) + 8) * (θ ^ 4 * frobH H)) * Vb =
      2 * Lam * (2 + η) * (1 + η') * Vb * (t * Am) +
      2 * Lam * t * ((2 + η) * (1 + 1 / η') * D + c0q η * (θ ^ 2) * frobH H) * Vb := by
    unfold c0q
    field_simp
    ring
  have e2 : 2 * Lam * (2 + η) * (1 + η') / (1 - Lam) * Vb ^ 2 =
      2 * Lam * (2 + η) * (1 + η') * Vb * (Vb / (1 - Lam)) := by ring
  rw [e1, e2, hθ2]
  linarith

end abs

section model

variable {n : ℕ} {I J S G : Type} [Fintype I] [Fintype J] [MeasurableSpace S] [MeasurableSpace G]

/-- **The variance bound in one slice** at `d_f = 2`. -/
theorem quadSlice (M : Mod n I J S G) (d : ℕ) (Lam kmax : ℝ) (tau : S → ℝ)
    (hR : Reg M d)
    (hSph : ∀ᵐ p ∂M.pi, ∀ᵐ g ∂M.ga, ∑ i, M.X (p, g) i ^ 2 = 1)
    (hOp : SliceOpF M Lam tau)
    (hk : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → kapm M x x ≤ kmax)
    (hb : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → ∀ j, |M.b x j| ≤ 1)
    (hL0 : 0 ≤ Lam) (hL1 : Lam ≤ 1 / 2) (hkm : 0 < kmax) :
    QuadSlice M Lam tau kmax := by
  intro P f0 ℓ H A sc hH hQ lam η η' hη hη'
  obtain ⟨hpi, hga, hX, -, -, -⟩ := hR
  obtain ⟨-, hOp⟩ := hOp
  filter_upwards [hSph] with p hp
  obtain ⟨hτ0, hτk, hτop⟩ := hOp p
  obtain ⟨mu, hmua⟩ : ∃ mu : (Fin n → ℝ) → Fin n → ℝ, ∀ x i, mu x i = ∑ j, M.b x j * A j i :=
    ⟨fun x i => ∑ j, M.b x j * A j i, fun _ _ => rfl⟩
  obtain ⟨ψ, hψa⟩ : ∃ ψ : (Fin n → ℝ) → J → ℝ, ∀ x q, ψ x q = lam * sc * M.ps x q :=
    ⟨fun x q => lam * sc * M.ps x q, fun _ _ => rfl⟩
  have hbc (j : I) : Continuous fun x => M.b x j := by
    unfold Mod.b; exact MvPolynomial.continuous_eval _
  have hpc (q : J) : Continuous fun x => M.ps x q := by
    unfold Mod.ps; exact MvPolynomial.continuous_eval _
  have hmu : Continuous mu := by
    refine continuous_pi fun i => ?_
    simp only [hmua]
    exact continuous_finsetSum _ fun j _ => (hbc j).mul continuous_const
  have hψ : Continuous ψ := by
    refine continuous_pi fun q => ?_
    simp only [hψa]
    exact continuous_const.mul (hpc q)
  have hXp : Measurable (fun g => M.X (p, g)) := hX.comp measurable_prodMk_left
  obtain ⟨ν, hνd⟩ : ∃ ν : Measure (Fin n → ℝ), ν = Measure.map (fun g => M.X (p, g)) M.ga :=
    ⟨_, rfl⟩
  have hms : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ^ 2 = 1} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hν : SphLaw n ν := by
    rw [hνd]
    exact ⟨(Measure.isProbabilityMeasure_map_iff hXp.aemeasurable).2 hga,
      (ae_map_iff hXp.aemeasurable hms).2 hp⟩
  have hint (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) :
      ∫ x, f x ∂ν = ∫ g, f (M.X (p, g)) ∂M.ga := by
    rw [hνd]; exact integral_map hXp.aemeasurable hf.aestronglyMeasurable
  have hFm (W : J × Fin n → ℝ) (x : Fin n → ℝ) : Fm M P lam W x = FA f0 ℓ H mu ψ W x := by
    rw [hQ]
    unfold FA
    congr 1
    funext i
    have : zv W (ψ x) i = lam * sc * zv W (M.ps x) i := by
      unfold zv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [hψa]; ring
    rw [this, hmua]
  have hY (W : J × Fin n → ℝ) : Ysl M P lam W p = VA ν f0 ℓ H mu ψ W := by
    have c := cont_FA (f0 := f0) (ℓ := ℓ) hH hmu hψ W
    unfold VA varU
    rw [hint (fun x => (FA f0 ℓ H mu ψ W x - ∫ y, FA f0 ℓ H mu ψ W y ∂ν) ^ 2)
      ((c.sub continuous_const).pow 2), hint _ c]
    unfold Ysl msl Fs
    simp only [hFm]
  have hYb : Yb M P lam p = VbarA ν f0 ℓ H mu ψ := by
    unfold Yb VbarA
    simp only [hY]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = lam ^ 2 * sc ^ 2 * tau p := ⟨_, rfl⟩
  have hls : 0 ≤ lam ^ 2 * sc ^ 2 := by positivity
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg hls hτ0
  have hkA (x : Fin n → ℝ) : kA ψ x = lam ^ 2 * sc ^ 2 * kapm M x x := by
    unfold kA kapm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hψa]; ring
  have hF : FeatOpA ν ψ (Lam * t) := by
    intro c
    have hcc : Continuous fun x => (∑ q, c q * ψ x q) ^ 2 :=
      (continuous_finsetSum _ fun q _ => continuous_const.mul (cont_psi hψ q)).pow 2
    rw [hint _ hcc]
    have h := hτop c
    have e (g : G) : (∑ q, c q * ψ (M.X (p, g)) q) ^ 2 =
        (lam * sc) ^ 2 * (∑ q, c q * M.ps (M.X (p, g)) q) ^ 2 := by
      rw [← mul_pow, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun q _ => by rw [hψa]; ring
    simp only [e]
    rw [integral_const_mul]
    calc (lam * sc) ^ 2 * ∫ g, (∑ q, c q * M.ps (M.X (p, g)) q) ^ 2 ∂M.ga
        ≤ (lam * sc) ^ 2 * (Lam * tau p * ∑ q, c q ^ 2) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = Lam * t * ∑ q, c q ^ 2 := by rw [ht]; ring
  have hms2 : MeasurableSet {x : Fin n → ℝ | t ≤ kA ψ x} :=
    (isClosed_le continuous_const (cont_kA hψ)).measurableSet
  have hkt : ∀ᵐ x ∂ν, t ≤ kA ψ x := by
    rw [hνd]
    refine (ae_map_iff hXp.aemeasurable hms2).2 (hτk.mono fun g hg => ?_)
    rw [hkA, ht]
    exact mul_le_mul_of_nonneg_left hg hls
  have hv0 : 0 ≤ frobH H :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← ht]
  simp only [hY, hYb]
  refine ⟨?_, ?_⟩
  · have hfl := floorA hν f0 ℓ H hH mu ψ hmu hψ Lam t hL0 (by linarith) ht0 hF hkt
    have hAm0 : 0 ≤ ∫ x, nsq (aA ℓ H mu x) ∂ν :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hp2 : 0 ≤ (1 - Lam) * (t * ∫ x, nsq (aA ℓ H mu x) ∂ν) :=
      mul_nonneg (by linarith) (mul_nonneg ht0 hAm0)
    linarith
  · by_cases h0 : lam * sc = 0
    · have hc (W : J × Fin n → ℝ) : VA ν f0 ℓ H mu ψ W = VA ν f0 ℓ H mu ψ 0 := by
        unfold VA
        congr 1
        funext x
        unfold FA
        congr 1
        funext i
        simp [zv, hψa, h0]
      have hVb : VbarA ν f0 ℓ H mu ψ = VA ν f0 ℓ H mu ψ 0 := by
        unfold VbarA
        simp only [hc]
        simp
      have ht00 : t = 0 := by
        rw [ht, ← mul_pow, h0]; simp
      simp only [hc, hVb, sub_self, ht00]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, mul_zero,
        zero_mul, add_zero]
      exact mul_nonneg (div_nonneg (by positivity) (by linarith)) (sq_nonneg _)
    · have hls' : 0 < lam ^ 2 * sc ^ 2 := by
        rw [← mul_pow]; positivity
      have hK : 0 < lam ^ 2 * sc ^ 2 * kmax := mul_pos hls' hkm
      refine varSliceA hν f0 ℓ H hH mu ψ hmu hψ Lam t (lam ^ 2 * sc ^ 2 * kmax) (Dq H A) η η'
        hL0 hL1 ht0 hK hη hη' hF hkt (fun x hx => ?_) (fun x y hx hy => ?_)
      · rw [hkA]; exact mul_le_mul_of_nonneg_left (hk x hx) hls
      · have e1 (z : Fin n → ℝ) (i : Fin n) :
            ∑ l, H i l * mu z l = ∑ j, M.b z j * ∑ l, H i l * A j l := by
          simp only [hmua, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
        have e2 (i : Fin n) : aA ℓ H mu x i - aA ℓ H mu y i =
            2 * ∑ j, (M.b x j - M.b y j) * ∑ l, H i l * A j l := by
          unfold aA aU
          rw [e1, e1]
          simp only [sub_mul, Finset.sum_sub_distrib]
          ring
        have hcs : ∑ j, (M.b x j - M.b y j) ^ 2 ≤ 4 * (Fintype.card I : ℝ) := by
          have h : ∑ j : I, (M.b x j - M.b y j) ^ 2 ≤ ∑ _j : I, (4 : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := abs_le.1 (hb x hx j)
            have h2 := abs_le.1 (hb y hy j)
            nlinarith [h1.1, h1.2, h2.1, h2.2]
          simpa [mul_comm] using h
        unfold nsq Dq
        simp only [e2]
        calc ∑ i, (2 * ∑ j, (M.b x j - M.b y j) * ∑ l, H i l * A j l) ^ 2
            ≤ ∑ i, 16 * (Fintype.card I : ℝ) * ∑ j, (∑ l, H i l * A j l) ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
                (fun j => M.b x j - M.b y j) (fun j => ∑ l, H i l * A j l)
              have vn : 0 ≤ ∑ j, (∑ l, H i l * A j l) ^ 2 :=
                Finset.sum_nonneg fun j _ => sq_nonneg _
              have h3 := mul_le_mul_of_nonneg_right hcs vn
              have e : (2 * ∑ j, (M.b x j - M.b y j) * ∑ l, H i l * A j l) ^ 2 =
                  4 * (∑ j, (M.b x j - M.b y j) * ∑ l, H i l * A j l) ^ 2 := by ring
              rw [e]
              linarith
          _ = 16 * (Fintype.card I : ℝ) * ∑ j, ∑ i, (∑ l, H i l * A j l) ^ 2 := by
              rw [← Finset.mul_sum, Finset.sum_comm]

end model

#print axioms quadSlice

end BstLean.Part89
