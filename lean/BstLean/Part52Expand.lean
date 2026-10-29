import BstLean.Part52LemmaR
import BstLean.Part52Gauss
import BstLean.Part49Main
import BstLean.Part43Floor

/-!
# Part 52, wave 3: the chaos `X(Z) = E_μ ∏_t m(x)_{ι t}` and its moments (Lemma P, parts i–ii)

Fix distinct rows `ι : Fin k → Fin n` (injective). For `Z : CoefIdxD n d → ℝ` (not normalized):

* `hZ ι Z x = ∏_t m_Z(x)_{ι t}`; `Xc μ ι Z = E_μ hZ`; `Wc μ ι Z = E_μ hZ²`.
* `hZ_expand`: `hZ = Σ_{b : Fin k → Mono} zB ι b Z · phB b x`, `zB ι b Z = ∏_t Z_{(b t, ι t)}`.
* `EX2_ge_one`: `E_Z Xc² ≥ 1` (`E_Z Xc² = Σ_b G(b)²` and `G(const) = 1`).
* `EW_le`: `E_Z Wc ≤ (d+1)^k` (`E_Z Wc = E_μ ‖φ‖^{2k}` and `‖φ‖² ≤ d + 1` on the sphere).
* `XcPoly`: `Xc² = eval Z P` with `deg P ≤ 2k`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part52

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD mapMD monoVal)
open BstLean.Part41 (Mono phiM phiSq varU)
open BstLean.Part40 (SphLaw)

variable {n d k : ℕ}

/-- The coefficient index of monomial `u` in output `a`. -/
def idx (u : Mono n d) (a : Fin n) : CoefIdxD n d := ⟨u.1, (u.2, a)⟩

theorem idx_inj {u u' : Mono n d} {a a' : Fin n} (h : idx u a = idx u' a') : u = u' ∧ a = a' := by
  obtain ⟨i, s⟩ := u
  obtain ⟨i', s'⟩ := u'
  simp only [idx, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  have := eq_of_heq h2
  simp only [Prod.mk.injEq] at this
  exact ⟨by rw [this.1], this.2⟩

/-- `∏_t m_Z(x)_{ι t}`. -/
noncomputable def hZ (ι : Fin k → Fin n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ t, mapMD Z x (ι t)

/-- `∏_t Z_{(b t, ι t)}`. -/
def zB (ι : Fin k → Fin n) (b : Fin k → Mono n d) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∏ t, Z (idx (b t) (ι t))

/-- `∏_t φ_{b t}(x)`. -/
noncomputable def phB (b : Fin k → Mono n d) (x : Fin n → ℝ) : ℝ := ∏ t, phiM x (b t)

/-- `X(Z) = E_μ hZ`. -/
noncomputable def Xc (μ : Measure (Fin n → ℝ)) (ι : Fin k → Fin n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, hZ ι Z x ∂μ

/-- `W(Z) = E_μ hZ²`. -/
noncomputable def Wc (μ : Measure (Fin n → ℝ)) (ι : Fin k → Fin n) (Z : CoefIdxD n d → ℝ) : ℝ :=
  ∫ x, hZ ι Z x ^ 2 ∂μ

theorem hZ_expand (ι : Fin k → Fin n) (Z : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    hZ ι Z x = ∑ b : Fin k → Mono n d, zB ι b Z * phB b x := by
  unfold hZ
  simp_rw [BstLean.Part49.mapMD_eq]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro b _
  rw [zB, phB, ← Finset.prod_mul_distrib]
  rfl

theorem phB_continuous (b : Fin k → Mono n d) : Continuous (phB (n := n) b) :=
  continuous_finsetProd _ (fun t _ => BstLean.Part49.continuous_monoVal _)

theorem phB_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (b : Fin k → Mono n d) :
    Integrable (phB b) μ := by
  have := hμ.prob
  exact BstLean.Part49.sph_integrable hμ.sphere (phB_continuous b)

theorem phB2_integrable {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (b b' : Fin k → Mono n d) :
    Integrable (fun x => phB b x * phB b' x) μ := by
  have := hμ.prob
  exact BstLean.Part49.sph_integrable hμ.sphere ((phB_continuous b).mul (phB_continuous b'))

theorem hZ_continuous (ι : Fin k → Fin n) (Z : CoefIdxD n d → ℝ) : Continuous (hZ ι Z) :=
  continuous_finsetProd _ (fun t _ => BstLean.Part49.continuous_mapMD Z (ι t))

theorem Xc_expand {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (Z : CoefIdxD n d → ℝ) :
    Xc μ ι Z = ∑ b : Fin k → Mono n d, (∫ x, phB b x ∂μ) * zB ι b Z := by
  unfold Xc
  simp_rw [hZ_expand]
  rw [integral_finsetSum _ (fun b _ => (phB_integrable hμ b).const_mul _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul, mul_comm]

theorem Wc_expand {μ : Measure (Fin n → ℝ)} (hμ : SphLaw n μ) (ι : Fin k → Fin n)
    (Z : CoefIdxD n d → ℝ) :
    Wc μ ι Z = ∑ b : Fin k → Mono n d, ∑ b' : Fin k → Mono n d,
      (∫ x, phB b x * phB b' x ∂μ) * (zB ι b Z * zB ι b' Z) := by
  unfold Wc
  have h : ∀ x, hZ ι Z x ^ 2 = ∑ b : Fin k → Mono n d, ∑ b' : Fin k → Mono n d,
      (zB ι b Z * zB ι b' Z) * (phB b x * phB b' x) := by
    intro x
    rw [hZ_expand, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro b' _
    ring
  simp_rw [h]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _
    (fun b' _ => (phB2_integrable hμ b b').const_mul _))]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_finsetSum _ (fun b' _ => (phB2_integrable hμ b b').const_mul _)]
  apply Finset.sum_congr rfl; intro b' _
  rw [integral_const_mul, mul_comm]

theorem zB_pair_integrable (ι : Fin k → Fin n) (b b' : Fin k → Mono n d) :
    Integrable (fun Z => zB ι b Z * zB ι b' Z) (stdGauss (CoefIdxD n d)) :=
  pairProd_integrable (fun t => idx (b t) (ι t)) (fun t => idx (b' t) (ι t))

theorem zB_pair_moment (ι : Fin k → Fin n) (hι : Function.Injective ι) (b b' : Fin k → Mono n d) :
    ∫ Z, zB ι b Z * zB ι b' Z ∂stdGauss (CoefIdxD n d) = if b = b' then 1 else 0 := by
  classical
  have hrow : ∀ t t', idx (b t) (ι t) = idx (b' t') (ι t') → t = t' := by
    intro t t' h
    exact hι (idx_inj h).2
  have hinj : Function.Injective (fun t => idx (b t) (ι t)) := by
    intro t t' h
    exact hι (idx_inj h).2
  have h := pair_moment (fun t => idx (b t) (ι t)) (fun t => idx (b' t) (ι t)) hinj hrow
  unfold zB
  rw [h]
  have hiff : ((fun t => idx (b t) (ι t)) = fun t => idx (b' t) (ι t)) ↔ b = b' := by
    constructor
    · intro he
      funext t
      exact (idx_inj (congrFun he t)).1
    · intro he; rw [he]
  by_cases hbb : b = b'
  · rw [if_pos (hiff.mpr hbb), if_pos hbb]
  · rw [if_neg (fun h => hbb (hiff.mp h)), if_neg hbb]

/-- **Double sums under the Gaussian.** -/
theorem Ez_double (ι : Fin k → Fin n) (hι : Function.Injective ι)
    (A : (Fin k → Mono n d) → (Fin k → Mono n d) → ℝ) :
    ∫ Z, ∑ b : Fin k → Mono n d, ∑ b' : Fin k → Mono n d, A b b' * (zB ι b Z * zB ι b' Z)
      ∂stdGauss (CoefIdxD n d) = ∑ b : Fin k → Mono n d, A b b := by
  classical
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _
    (fun b' _ => (zB_pair_integrable ι b b').const_mul _))]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_finsetSum _ (fun b' _ => (zB_pair_integrable ι b b').const_mul _)]
  simp_rw [integral_const_mul, zB_pair_moment ι hι]
  simp

end BstLean.Part52
