import BstLean.Part86SliceOpA
import BstLean.Part81UX
import BstLean.Part56PropD_Kernel
import BstLean.Part56PropD_Split
import BstLean.Part56Weights
import BstLean.Part56Key_Projection
import BstLean.Part56Orth_Projection

/-!
# Part 86: the slice feature operator bound for `D_{t,v}` at every degree (`SliceOpRK`)

On the slice `x = S v + R w` (`w` uniform on the unit sphere of `v^⊥`, dimension `m`):
`τ(x) ≥ R²` and `E_w (c · ψ(x))² ≤ (C/m) R² ‖c‖²`, with `ψ` the residual feature.

* `sliceOpRK_fact`: `C = (101/100) (d+1)!`, for `d ≥ 1`, `m ≥ 5000`.
* `sliceOpRK`: `C = CL86 d`, for `d ≥ 2`, `m ≥ 5000`.

Route: `c · ψ(x) = c̃ · φ(x)` with `c̃ ⟂ φ_j(v)`; each degree block is a homogeneous polynomial that
vanishes at `v`; rotate to a basis with first vector `v` (the tensor norm is invariant), split off
the first coordinate (`Part86SliceOpA.claimJ`), and use the feature operator bound of the uniform
sphere of dimension `m` (`Part81.featOpU`).
-/

namespace BstLean.Part86.XSliceOp

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (monoVal)
open BstLean.Part41 (Mono phiM)
open BstLean.Part53 (unitF53)
open BstLean.Part56 (UnitV phiB kJ betaJ KR tauR polarPoint perpDir axialR axialS
  basisReconstruct tailReconstruct)
open BstLean.Part56.Orth (residualFeature blocks_orthogonal block_norm_pos)
open BstLean.Part86.SliceOpA

/-! ## §1 The residual feature paired with `c` -/

section resid

variable {n d : ℕ}

/-- `A_j = c · φ_j(v)`. -/
noncomputable def cdot (v : Fin n → ℝ) (c : Mono n d → ℝ) (j : ℕ) : ℝ :=
  ∑ p : Mono n d, c p * phiB d j v p

/-- The part of `c` in the span of the anchor features. -/
noncomputable def cpar (v : Fin n → ℝ) (c : Mono n d → ℝ) (p : Mono n d) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), cdot v c j / kJ d j v v * phiB d j v p

/-- The part of `c` orthogonal to the anchor features. -/
noncomputable def ctil (v : Fin n → ℝ) (c : Mono n d → ℝ) (p : Mono n d) : ℝ :=
  c p - cpar v c p

lemma phiB_mul_phiM (j : ℕ) (v x : Fin n → ℝ) (p : Mono n d) :
    phiB d j v p * phiM x p = phiB d j x p * phiB d j v p := by
  unfold phiB
  split_ifs <;> ring

lemma kJ_phiM (j : ℕ) (v x : Fin n → ℝ) :
    kJ d j x v = ∑ p : Mono n d, phiB d j v p * phiM x p := by
  unfold kJ
  exact Finset.sum_congr rfl (fun p _ => (phiB_mul_phiM j v x p).symm)

lemma resid_ctil (v x : Fin n → ℝ) (c : Mono n d → ℝ) :
    ∑ p, c p * residualFeature v x p = ∑ p, ctil v c p * phiM x p := by
  simp only [ctil, residualFeature, mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [cpar, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : ∑ p : Mono n d, c p * (betaJ d j v x * phiB d j v p) =
      betaJ d j v x * cdot v c j := by
    rw [cdot, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h2 : ∑ p : Mono n d, cdot v c j / kJ d j v v * phiB d j v p * phiM x p =
      cdot v c j / kJ d j v v * kJ d j x v := by
    rw [kJ_phiM (d := d) j v x, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [h1, h2, betaJ]
  ring

lemma cpar_dot (v : Fin n → ℝ) (hv : UnitV v) (c : Mono n d → ℝ) (j : ℕ) (hj : j ≤ d) :
    ∑ p : Mono n d, cpar v c p * phiB d j v p = cdot v c j := by
  simp only [cpar, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · have hk := block_norm_pos (d := d) v hv j hj
    have : ∑ p : Mono n d, cdot v c j / kJ d j v v * phiB d j v p * phiB d j v p =
        cdot v c j / kJ d j v v * kJ d j v v := by
      rw [kJ, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [this]
    field_simp
  · intro l _ hl
    have := blocks_orthogonal (d := d) l j v hl
    have e : ∑ p : Mono n d, cdot v c l / kJ d l v v * phiB d l v p * phiB d j v p =
        cdot v c l / kJ d l v v * ∑ p : Mono n d, phiB d l v p * phiB d j v p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [e, this, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

lemma ctil_dot (v : Fin n → ℝ) (hv : UnitV v) (c : Mono n d → ℝ) (j : ℕ) (hj : j ≤ d) :
    ∑ p : Mono n d, ctil v c p * phiB d j v p = 0 := by
  simp only [ctil, sub_mul, Finset.sum_sub_distrib]
  rw [cpar_dot v hv c j hj, cdot, sub_self]

lemma ctil_norm (v : Fin n → ℝ) (hv : UnitV v) (c : Mono n d → ℝ) :
    ∑ p, ctil v c p ^ 2 ≤ ∑ p, c p ^ 2 := by
  have hcross : ∑ p : Mono n d, ctil v c p * cpar v c p = 0 := by
    have : ∀ p : Mono n d, ctil v c p * cpar v c p =
        ∑ j ∈ Finset.range (d + 1), cdot v c j / kJ d j v v * (ctil v c p * phiB d j v p) := by
      intro p
      rw [cpar, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp only [this]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.mul_sum, ctil_dot v hv c j (by have := Finset.mem_range.mp hj; omega), mul_zero]
  have hc : ∀ p : Mono n d, c p ^ 2 =
      ctil v c p ^ 2 + 2 * (ctil v c p * cpar v c p) + cpar v c p ^ 2 := by
    intro p
    simp only [ctil]
    ring
  simp only [hc, Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
  have : 0 ≤ ∑ p : Mono n d, cpar v c p ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

/-- Degree blocks. -/
lemma sum_blocks (F : Mono n d → ℝ) :
    ∑ p, F p = ∑ j : Fin (d + 1), ∑ β : Sym (Fin n) j, F ⟨j, β⟩ :=
  Fintype.sum_sigma F

lemma block_dot (c : Mono n d → ℝ) (v : Fin n → ℝ) (j : Fin (d + 1)) :
    ∑ p : Mono n d, c p * phiB d j v p =
      ∑ β : Sym (Fin n) j, c ⟨j, β⟩ * monoVal v β.val := by
  classical
  rw [sum_blocks]
  rw [Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro β _
    simp [phiB, phiM]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro β _
    have : (l : ℕ) ≠ (j : ℕ) := fun h => hl (Fin.ext h)
    simp [phiB, this]
  · intro h
    exact absurd (Finset.mem_univ j) h

end resid

/-! ## §2 The coefficient vector in the rotated coordinates -/

theorem coefExists (m d : ℕ) (v : Fin (m + 1) → ℝ) (hv : UnitV v)
    (c : Mono (m + 1) d → ℝ) (O : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hrow : ∀ i i', ∑ l, O i l * O i' l = if i = i' then 1 else 0)
    (hO0 : ∀ i, O i 0 = v i)
    (S R : ℝ) (hS : |S| ≤ 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    ∃ a : Mono m d → ℝ, a default = 0 ∧
      ∑ q, a q ^ 2 ≤ ((d + 1).factorial : ℝ) * R ^ 2 * ∑ p, c p ^ 2 ∧
      ∀ ω : Fin m → ℝ,
        ∑ p, c p * residualFeature v
            (fun i => ∑ l, O i l * (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) l) p =
          ∑ q, a q * phiM ω q := by
  classical
  set ct := ctil v c with hct
  have hcl : ∀ j : Fin (d + 1), ∃ a : Mono m d → ℝ, a default = 0 ∧
      ∑ q, a q ^ 2 ≤ ((j : ℕ).factorial : ℝ) * R ^ 2 *
        ∑ β : Sym (Fin (m + 1)) j, ct ⟨j, β⟩ ^ 2 ∧
      ∀ ω : Fin m → ℝ,
        ∑ β : Sym (Fin (m + 1)) j, ct ⟨j, β⟩ *
            monoVal (fun i => ∑ l, O i l * (Fin.cons S (R • ω) : Fin (m + 1) → ℝ) l) β.val =
          ∑ q, a q * phiM ω q := by
    intro j
    have hjd : (j : ℕ) ≤ d := by have := j.2; omega
    apply claimJ m j d hjd (fun β => ct ⟨j, β⟩) O hrow _ S R hS hR0 hR1
    have h0 := ctil_dot v hv c j hjd
    rw [block_dot] at h0
    have hOv : (fun i => O i 0) = v := funext hO0
    rw [hOv]
    exact h0
  choose aj haj0 hajn haje using hcl
  refine ⟨fun q => ∑ j, aj j q, ?_, ?_, ?_⟩
  · exact Finset.sum_eq_zero (fun j _ => haj0 j)
  · have h1 : ∀ q : Mono m d, (∑ j, aj j q) ^ 2 ≤ ((d : ℝ) + 1) * ∑ j, aj j q ^ 2 := by
      intro q
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (d + 1))))
        (f := fun j => aj j q)
      simpa using this
    have hfac : ∀ j : Fin (d + 1), ((j : ℕ).factorial : ℝ) ≤ (d.factorial : ℝ) := by
      intro j
      exact_mod_cast Nat.factorial_le (by have := j.2; omega)
    have h2 : ∀ j : Fin (d + 1), ∑ q, aj j q ^ 2 ≤
        (d.factorial : ℝ) * R ^ 2 * ∑ β : Sym (Fin (m + 1)) j, ct ⟨j, β⟩ ^ 2 := by
      intro j
      refine (hajn j).trans ?_
      have hs : 0 ≤ ∑ β : Sym (Fin (m + 1)) j, ct ⟨j, β⟩ ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hR : 0 ≤ R ^ 2 := sq_nonneg R
      have := hfac j
      apply mul_le_mul_of_nonneg_right _ hs
      exact mul_le_mul_of_nonneg_right this hR
    calc ∑ q, (∑ j, aj j q) ^ 2 ≤ ∑ q, ((d : ℝ) + 1) * ∑ j, aj j q ^ 2 :=
          Finset.sum_le_sum (fun q _ => h1 q)
      _ = ((d : ℝ) + 1) * ∑ j, ∑ q, aj j q ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ ((d : ℝ) + 1) * ∑ j : Fin (d + 1),
            (d.factorial : ℝ) * R ^ 2 * ∑ β : Sym (Fin (m + 1)) j, ct ⟨j, β⟩ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun j _ => h2 j)
      _ = ((d + 1).factorial : ℝ) * R ^ 2 * ∑ p, ct p ^ 2 := by
          rw [sum_blocks (fun p => ct p ^ 2), ← Finset.mul_sum, Nat.factorial_succ]
          push_cast
          ring
      _ ≤ ((d + 1).factorial : ℝ) * R ^ 2 * ∑ p, c p ^ 2 := by
          apply mul_le_mul_of_nonneg_left (ctil_norm v hv c)
          positivity
  · intro ω
    rw [resid_ctil, sum_blocks]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← haje j ω]
    rfl

/-! ## §3 The basis with first vector `v` -/

section basis

variable {m : ℕ}
variable (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))

/-- The matrix of the basis: `O i l = (b l)_i`. -/
noncomputable def Omat (i l : Fin (m + 1)) : ℝ := (b l).ofLp i

lemma recon_sum (y : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    basisReconstruct b y i = ∑ l, Omat b i l * y l := by
  unfold basisReconstruct Omat
  rw [← b.sum_repr_symm (WithLp.toLp 2 y)]
  simp [mul_comm]

lemma Omat_row (i i' : Fin (m + 1)) :
    ∑ l, Omat b i l * Omat b i' l = if i = i' then 1 else 0 := by
  classical
  have h := b.sum_inner_mul_inner (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single i' (1 : ℝ))
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one,
    one_mul, conj_trivial] at h
  simp only [Omat]
  rw [h]
  simp [eq_comm]

lemma Omat_zero (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (i : Fin (m + 1)) :
    Omat b i 0 = v i := by
  simp [Omat, hb]

lemma polar_recon (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (a r : ℝ)
    (ω : Fin m → ℝ) :
    polarPoint v (tailReconstruct b ω) a r =
      fun i => ∑ l, Omat b i l * (Fin.cons (axialS a r) (axialR a r • ω) : Fin (m + 1) → ℝ) l := by
  funext i
  rw [← recon_sum, BstLean.Part56.basisReconstruct_cons b v hb,
    BstLean.Part56.tailReconstruct_smul]
  rfl

lemma continuous_tail : Continuous (tailReconstruct b) := by
  apply continuous_pi
  intro i
  simp only [tailReconstruct, recon_sum]
  apply continuous_finsetSum
  intro l _
  apply continuous_const.mul
  refine Fin.cases ?_ (fun k => ?_) l
  · simp only [Fin.cons_zero]; exact continuous_const
  · simp only [Fin.cons_succ]; exact continuous_apply k

/-- Averages over the perpendicular direction are averages over the uniform sphere of
dimension `m`. -/
lemma perp_lintegral (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v)
    (F : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F (perpDir v g) ∂stdGauss (Fin (m + 1)) =
      ∫⁻ ω, F (tailReconstruct b ω) ∂uniformSphere m := by
  rw [BstLean.Part56.perpDir_lintegral_tail b v hb F hF,
    BstLean.Part56.uniformSphere_lintegral_gauss m hm (fun ω => F (tailReconstruct b ω))
      (hF.comp (continuous_tail b).measurable)]

lemma perp_map (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) :
    (stdGauss (Fin (m + 1))).map (perpDir v) = (uniformSphere m).map (tailReconstruct b) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (BstLean.Part56.measurable_perpDir56 v),
    lintegral_map hF (continuous_tail b).measurable]
  exact perp_lintegral b hm v hb F hF

lemma perp_integral (hm : 1 ≤ m) (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v)
    (G : (Fin (m + 1) → ℝ) → ℝ) (hG : Measurable G) :
    ∫ g, G (perpDir v g) ∂stdGauss (Fin (m + 1)) =
      ∫ ω, G (tailReconstruct b ω) ∂uniformSphere m := by
  rw [← integral_map (BstLean.Part56.measurable_perpDir56 v).aemeasurable
      hG.aestronglyMeasurable,
    ← integral_map (continuous_tail b).measurable.aemeasurable hG.aestronglyMeasurable,
    perp_map b hm v hb]

end basis

/-! ## §4 The kernel diagonal on the slice -/

lemma tau_ge {n d : ℕ} (hd : 1 ≤ d) (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    ∑ i, x i ^ 2 - (∑ i, x i * v i) ^ 2 ≤ tauR d v x := by
  classical
  unfold tauR KR
  have hnn : ∀ j ∈ Finset.Icc 1 d,
      0 ≤ kJ d j x x - kJ d j x v * kJ d j x v / kJ d j v v := by
    intro j hj
    have hjd : j ≤ d := (Finset.mem_Icc.mp hj).2
    have hpos := block_norm_pos (d := d) v hv j hjd
    have hcs : kJ d j x v ^ 2 ≤ kJ d j x x * kJ d j v v := by
      simpa only [kJ, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq
        Finset.univ (phiB d j x) (phiB d j v)
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hpos).mpr
    simpa only [pow_two] using hcs
  have h1 := Finset.single_le_sum hnn (Finset.mem_Icc.mpr ⟨le_rfl, hd⟩)
  refine le_trans (le_of_eq ?_) h1
  rw [BstLean.Part56.kJ_one d hd, BstLean.Part56.kJ_one d hd, BstLean.Part56.kJ_one d hd]
  have hvv : ∑ a, v a * v a = 1 := by
    have : ∑ a, v a * v a = ∑ a, v a ^ 2 := Finset.sum_congr rfl (fun a _ => by ring)
    rw [this]; exact hv
  rw [hvv, div_one]
  have : ∑ a, x a * x a = ∑ a, x a ^ 2 := Finset.sum_congr rfl (fun a _ => by ring)
  rw [this]
  ring

lemma axialR_bounds (a r : ℝ) (hr : 0 ≤ r) : 0 ≤ axialR a r ∧ axialR a r ≤ 1 :=
  ⟨BstLean.Part56.axialR_nonneg a r hr, BstLean.Part56.axialR_le_one a r hr⟩

/-! ## §5 The slice operator bound -/

lemma continuous_phiM {n d : ℕ} (p : Mono n d) : Continuous (fun x : Fin n → ℝ => phiM x p) := by
  unfold phiM monoVal
  exact continuous_multiset_prod _ (fun i _ => continuous_apply i)

theorem SliceOpRK.mono {m d : ℕ} {C C' : ℝ} (h : SliceOpRK m d C) (hC : C ≤ C') (hm : 0 < m) :
    SliceOpRK m d C' := by
  intro v hv a r hr
  obtain ⟨h1, h2⟩ := h v hv a r hr
  refine ⟨h1, fun c => (h2 c).trans ?_⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 ≤ ∑ p, c p ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ hs
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact div_le_div_of_nonneg_right hC hm'.le

/-- **The slice feature operator bound**, constant `(101/100) (d+1)!`. -/
theorem sliceOpRK_fact (m d : ℕ) (hd : 1 ≤ d) (hm : 5000 ≤ m) :
    SliceOpRK m d (101 / 100 * ((d + 1).factorial : ℝ)) := by
  classical
  intro v hv a r hr
  have hm1 : 1 ≤ m := by omega
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  set S := axialS a r with hSdef
  set R := axialR a r with hRdef
  obtain ⟨hR0, hR1⟩ := axialR_bounds a r hr
  have hS : |S| ≤ 1 := BstLean.Part56.axialS_abs_le_one a r
  have hsph := BstLean.Part29.uniformSphere_ae_sphere m
  refine ⟨?_, ?_⟩
  · -- the kernel diagonal
    have hset : MeasurableSet {w : Fin (m + 1) → ℝ | R ^ 2 ≤ tauR d v (polarPoint v w a r)} := by
      apply IsClosed.measurableSet
      apply isClosed_le continuous_const
      apply (BstLean.Part56.continuous_tauR56 d v).comp
      unfold polarPoint
      fun_prop
    have hae : ∀ᵐ w ∂((stdGauss (Fin (m + 1))).map (perpDir v)),
        R ^ 2 ≤ tauR d v (polarPoint v w a r) := by
      rw [perp_map b hm1 v hb0]
      rw [ae_map_iff (continuous_tail b).measurable.aemeasurable hset]
      filter_upwards [hsph] with ω hω
      refine le_trans (le_of_eq ?_) (tau_ge hd v hv _)
      have hw2 : ∑ i, tailReconstruct b ω i ^ 2 = 1 := by
        rw [BstLean.Part56.tailReconstruct_sumsq, hω]
      have hwv : ∑ i, v i * tailReconstruct b ω i = 0 := by
        have := BstLean.Part56.basisReconstruct_axial b v hb0 (Fin.cons 0 ω)
        simp only [Fin.cons_zero] at this
        exact this
      have hvv : ∑ i, v i ^ 2 = 1 := hv
      have e1 : ∑ i, polarPoint v (tailReconstruct b ω) a r i ^ 2 = S ^ 2 + R ^ 2 := by
        have : ∀ i, polarPoint v (tailReconstruct b ω) a r i ^ 2 =
            S ^ 2 * v i ^ 2 + 2 * S * R * (v i * tailReconstruct b ω i) +
              R ^ 2 * tailReconstruct b ω i ^ 2 := by
          intro i
          simp only [polarPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hSdef, ← hRdef]
          ring
        simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hvv, hwv, hw2]
        ring
      have e2 : ∑ i, polarPoint v (tailReconstruct b ω) a r i * v i = S := by
        have : ∀ i, polarPoint v (tailReconstruct b ω) a r i * v i =
            S * v i ^ 2 + R * (v i * tailReconstruct b ω i) := by
          intro i
          simp only [polarPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hSdef, ← hRdef]
          ring
        simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hvv, hwv]
        ring
      rw [e1, e2]
      ring
    exact ae_of_ae_map (BstLean.Part56.measurable_perpDir56 v).aemeasurable hae
  · intro c
    obtain ⟨aq, haq0, haqn, haqe⟩ := coefExists m d v hv c (Omat b) (Omat_row b)
      (Omat_zero b v hb0) S R hS hR0 hR1
    -- the integrand as a function of the direction
    set G : (Fin (m + 1) → ℝ) → ℝ := fun w =>
      (∑ p, c p * residualFeature v (polarPoint v w a r) p) ^ 2 with hG
    have hGm : Measurable G := by
      apply Continuous.measurable
      simp only [hG, resid_ctil]
      apply Continuous.pow
      apply continuous_finsetSum
      intro p _
      apply continuous_const.mul
      apply (continuous_phiM p).comp
      unfold polarPoint
      fun_prop
    have h1 := perp_integral b hm1 v hb0 G hGm
    simp only [hG] at h1
    rw [h1]
    have h2 : ∀ ω : Fin m → ℝ,
        (∑ p, c p * residualFeature v (polarPoint v (tailReconstruct b ω) a r) p) ^ 2 =
          (∑ q : BstLean.Part81.JJ m d, aq q.1 * BstLean.Part81.pf ω q) ^ 2 := by
      intro ω
      rw [polar_recon b v hb0 a r ω, haqe ω, Fintype.sum_eq_add_sum_subtype_ne _ default, haq0,
        zero_mul, zero_add]
      rfl
    simp only [h2]
    have hf := BstLean.Part81.featOpU m d hm (fun q => aq q.1)
    refine hf.trans ?_
    have hsub : ∑ q : BstLean.Part81.JJ m d, aq q.1 ^ 2 ≤ ∑ q, aq q ^ 2 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun q => aq q ^ 2) default]
      have : 0 ≤ aq default ^ 2 := sq_nonneg _
      linarith
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hc0 : 0 ≤ ∑ p, c p ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc 101 / 100 / (m : ℝ) * ∑ q : BstLean.Part81.JJ m d, aq q.1 ^ 2
        ≤ 101 / 100 / (m : ℝ) * (((d + 1).factorial : ℝ) * R ^ 2 * ∑ p, c p ^ 2) := by
          apply mul_le_mul_of_nonneg_left (hsub.trans haqn)
          positivity
      _ = 101 / 100 * ((d + 1).factorial : ℝ) / (m : ℝ) * R ^ 2 * ∑ p, c p ^ 2 := by ring

/-! ## §6 The constant `CL86` -/

lemma dfact_ge (e : ℕ) : 3 * (e + 1).factorial ≤ (2 * e + 3).doubleFactorial := by
  induction e with
  | zero => decide
  | succ e ih =>
    have h1 : (2 * (e + 1) + 3).doubleFactorial = (2 * e + 5) * (2 * e + 3).doubleFactorial := by
      rw [show 2 * (e + 1) + 3 = (2 * e + 3) + 2 by ring, Nat.doubleFactorial_add_two]
    rw [h1, Nat.factorial_succ (e + 1)]
    calc 3 * ((e + 1 + 1) * (e + 1).factorial) = (e + 2) * (3 * (e + 1).factorial) := by ring
      _ ≤ (2 * e + 5) * (3 * (e + 1).factorial) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * e + 5) * (2 * e + 3).doubleFactorial := Nat.mul_le_mul_left _ ih

lemma CLn_ge (d : ℕ) (hd : 2 ≤ d) : 3 * (d + 1).factorial ≤ 2 * CLn d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hsum : (2 * (e + 2) - 1).doubleFactorial ≤
      ∑ b ∈ Finset.Icc 1 (e + 2), ((e + 2).choose b) ^ 2 * (2 * b - 1).doubleFactorial := by
    have := Finset.single_le_sum
      (f := fun b => ((e + 2).choose b) ^ 2 * (2 * b - 1).doubleFactorial)
      (s := Finset.Icc 1 (e + 2)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    simpa using this
  have hdf : 3 * (e + 1).factorial ≤ (2 * (e + 2) - 1).doubleFactorial := by
    rw [show 2 * (e + 2) - 1 = 2 * e + 3 by omega]
    exact dfact_ge e
  have heven : 2 * ((e + 2) * (e + 2 + 1) / 2) = (e + 2) * (e + 2 + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (e + 2))
  unfold CLn
  rw [← mul_assoc, heven]
  have hf : (e + 2 + 1).factorial = (e + 3) * ((e + 2) * (e + 1).factorial) := by
    rw [Nat.factorial_succ (e + 2), Nat.factorial_succ (e + 1)]
  rw [hf]
  calc 3 * ((e + 3) * ((e + 2) * (e + 1).factorial))
      = (e + 2) * (e + 2 + 1) * (3 * (e + 1).factorial) := by ring
    _ ≤ (e + 2) * (e + 2 + 1) * (2 * (e + 2) - 1).doubleFactorial :=
      Nat.mul_le_mul_left _ hdf
    _ ≤ _ := Nat.mul_le_mul_left _ hsum

/-- **The slice feature operator bound**, constant `CL86 d`, for `d ≥ 2`. -/
theorem sliceOpRK (m d : ℕ) (hd : 2 ≤ d) (hm : 5000 ≤ m) : SliceOpRK m d (CL86 d) := by
  apply SliceOpRK.mono (sliceOpRK_fact m d (by omega) hm) _ (by omega)
  have h := CLn_ge d hd
  have h' : (3 : ℝ) * ((d + 1).factorial : ℝ) ≤ 2 * (CLn d : ℝ) := by exact_mod_cast h
  unfold CL86
  have : (0 : ℝ) ≤ ((d + 1).factorial : ℝ) := by positivity
  linarith

end BstLean.Part86.XSliceOp

#print axioms BstLean.Part86.XSliceOp.sliceOpRK_fact
#print axioms BstLean.Part86.XSliceOp.sliceOpRK
