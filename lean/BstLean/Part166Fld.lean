import BstLean.Part165All

/-!
# Part 166 (file `Fld`): the two fields of Proposition LG as functions of the Agent key

No proof is left open; no `native_decide` or `axiom` is used.

The Agent key is `k = ((ĉ, τ₀), (A₁, A₂)) : AgFam n` (Part 160). For the paper's design the
realized certificate `Ψ` of Part 162 depends on the retained data only through this key.

* `bK k`: the Agent centre `b = (1/ρ)·b̃` of Part 154 at the key; `repK k`: a retained-data value
  with the key's `ĉ` and `(A₁, A₂)`; `latK k a`: the latitude of the index `a`.
* `fK k = √(e_b)·λ` (`f = ⟨a₂, b̂⟩/√n`, paper `t7:p07:fields`) and `sK k = σ` at the key.
* `psiK Φ k a v`: the realized `Ψ` at the key.
* **`measurable_psiK_f`, `measurable_psiK_s`**: `Ψ` is jointly measurable in `(k, a, v)`
  (via `measurable_fderiv_with_param` and continuous forms `FF`, `SS` of the fields).
* **`psiA_sig_eq`**, **`psiA_lam_eq`**: transfer to Part 162's `psiA` for the paper's design:
  `Ψ_σ = psiK sK`, `e_b·Ψ_λ = psiK fK`.
-/

namespace BstLean.Part166

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part150 (rhoC thetaC bT)
open BstLean.Part161 (xLat hhMat uHat consV muI latC lamX sigX Ix)
open BstLean.Part162 (xLatH tanSq psiA)
open BstLean.Part151 (gradSq)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part136 (HidParam)

variable {n : ℕ}

/-- The Agent centre at the key: `b = (1/ρ(ĉ, τ))·b̃(A₁, A₂, ĉ, τ)` (Part 154's centre). -/
noncomputable def bK (k : AgFam n) : Fin (mA n) → ℝ :=
  (1 / rhoC k.1.1 k.1.2) • bT n n k.2.1 k.2.2 k.1.1 k.1.2

/-- `b̂ = b/|b|` (`0` at `b = 0`). -/
noncomputable def bhat {m : ℕ} (b : Fin m → ℝ) : Fin m → ℝ := (√(normSq b))⁻¹ • b

/-- A retained-data value with the key's `ĉ` and `(A₁, A₂)` (other entries `0`). -/
noncomputable def repK (k : AgFam n) : Ret n := ((0, k.1.1), ((k.2, 0), 0))

/-- The latitude of the index `a` at the key. -/
noncomputable def latK (k : AgFam n) (a : Ix n) : ℝ := latitude (√(normSq k.1.1)) k.1.2 a

/-- `f = √(e_b)·λ = (|b|/√n)·⟨a₂(x), b⟩/|b|²` at the key. -/
noncomputable def fK (k : AgFam n) (x : Fin n → ℝ) : ℝ :=
  √(normSq (bK k)) / √(n : ℝ) * lam (bK k) (hid2 k.2.1 k.2.2 x)

/-- `σ(x) = √(2/m_A)·|r(x)|` at the key. -/
noncomputable def sK (k : AgFam n) (x : Fin n → ℝ) : ℝ :=
  sig (2 / (mA n : ℝ)) (bK k) (hid2 k.2.1 k.2.2 x)

/-- **The realized certificate density at the key**: `Ψ_Φ(a, v)`, the nonnegative part of the
squared tangential gradient on the latitude sphere (Part 162's `psiA`). -/
noncomputable def psiK (Φ : AgFam n → (Fin n → ℝ) → ℝ) (k : AgFam n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : ℝ :=
  √(tanSq (Φ k) (repK k) (latK k a) v) ^ 2

lemma psiK_nonneg (Φ : AgFam n → (Fin n → ℝ) → ℝ) (k : AgFam n) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : 0 ≤ psiK Φ k a v := sq_nonneg _

/-! ## Continuous forms -/

/-- The parameter of a field: `(b̂, (A₁, A₂))`. -/
abbrev QP (n : ℕ) : Type := (Fin (mA n) → ℝ) × HidParam n (mA n)

/-- `f` from `b̂`: `⟨a₂(x), b̂⟩/√n`. -/
noncomputable def FF (q : QP n) (x : Fin n → ℝ) : ℝ :=
  (√(n : ℝ))⁻¹ * ∑ j, hid2 q.2.1 q.2.2 x j * q.1 j

/-- `σ` from `b̂`: `√(2/m_A)·|a₂ − ⟨a₂, b̂⟩b̂|`. -/
noncomputable def SS (q : QP n) (x : Fin n → ℝ) : ℝ :=
  √(2 / (mA n : ℝ)) *
    √(normSq (hid2 q.2.1 q.2.2 x - (∑ j, hid2 q.2.1 q.2.2 x j * q.1 j) • q.1))

lemma lam_smul_eq {m : ℕ} (b h : Fin m → ℝ) :
    lam b h • b = (∑ j, h j * bhat b j) • bhat b := by
  unfold lam bhat
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rcases (normSq_nonneg b).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have hs : (0 : ℝ) < √(normSq b) := Real.sqrt_pos.mpr h0
    have hss : √(normSq b) * √(normSq b) = normSq b := Real.mul_self_sqrt h0.le
    have e : ∑ j, h j * ((√(normSq b))⁻¹ * b j) = (√(normSq b))⁻¹ * ∑ j, h j * b j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    field_simp
    rw [Real.sq_sqrt h0.le]; ring

lemma fK_eq_FF (k : AgFam n) : fK k = FF (bhat (bK k), k.2) := by
  funext x
  unfold fK FF lam bhat
  simp only [Pi.smul_apply, smul_eq_mul]
  set b := bK k
  set h := hid2 k.2.1 k.2.2 x
  rcases (normSq_nonneg b).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have hs : (0 : ℝ) < √(normSq b) := Real.sqrt_pos.mpr h0
    have hss : √(normSq b) * √(normSq b) = normSq b := Real.mul_self_sqrt h0.le
    have e : ∑ j, h j * ((√(normSq b))⁻¹ * b j) = (√(normSq b))⁻¹ * ∑ j, h j * b j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have key : ∀ r : ℝ, 0 < r → r / √(n : ℝ) * ((∑ j, h j * b j) / (r * r)) =
        (√(n : ℝ))⁻¹ * (r⁻¹ * ∑ j, h j * b j) := by
      intro r hr; field_simp
    have := key _ hs
    rw [hss] at this
    exact this

lemma sK_eq_SS (k : AgFam n) : sK k = SS (bhat (bK k), k.2) := by
  funext x
  unfold sK SS sig res
  rw [lam_smul_eq]

lemma continuous_hid2_joint :
    Continuous (fun p : HidParam n (mA n) × (Fin n → ℝ) => hid2 p.1.1 p.1.2 p.2) := by
  unfold hid2
  exact continuous_reluV.comp (Continuous.matrix_mulVec (continuous_snd.comp continuous_fst)
    (continuous_reluV.comp (Continuous.matrix_mulVec (continuous_fst.comp continuous_fst)
      continuous_snd)))

lemma continuous_FF : Continuous (fun p : QP n × (Fin n → ℝ) => FF p.1 p.2) := by
  unfold FF
  have h2 : Continuous (fun p : QP n × (Fin n → ℝ) => hid2 p.1.2.1 p.1.2.2 p.2) :=
    continuous_hid2_joint.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  refine continuous_const.mul (continuous_finsetSum _ fun j _ => ?_)
  exact ((continuous_apply j).comp h2).mul ((continuous_apply j).comp
    (continuous_fst.comp continuous_fst))

lemma continuous_normSq {ι : Type*} [Fintype ι] : Continuous (normSq : (ι → ℝ) → ℝ) := by
  unfold normSq; fun_prop

lemma continuous_SS : Continuous (fun p : QP n × (Fin n → ℝ) => SS p.1 p.2) := by
  unfold SS
  have h2 : Continuous (fun p : QP n × (Fin n → ℝ) => hid2 p.1.2.1 p.1.2.2 p.2) :=
    continuous_hid2_joint.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hb : Continuous (fun p : QP n × (Fin n → ℝ) => p.1.1) := continuous_fst.comp continuous_fst
  have hs : Continuous (fun p : QP n × (Fin n → ℝ) => ∑ j, hid2 p.1.2.1 p.1.2.2 p.2 j * p.1.1 j) :=
    continuous_finsetSum _ fun j _ => ((continuous_apply j).comp h2).mul
      ((continuous_apply j).comp hb)
  exact continuous_const.mul (Real.continuous_sqrt.comp (continuous_normSq.comp
    (h2.sub (hs.smul hb))))

/-! ## The frame maps -/

lemma continuous_consV :
    Continuous (fun p : ℝ × (Fin (n - 1) → ℝ) => consV (n := n) p.1 p.2) := by
  refine continuous_pi fun i => ?_
  unfold consV
  by_cases h : (i : ℕ) = 0
  · simp only [h, dite_true]; exact continuous_fst
  · simp only [h, dite_false]; exact (continuous_apply _).comp continuous_snd

/-- `xLatH` with the reflection as a free matrix. -/
noncomputable def xP (H : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (w : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  H.mulVec (consV (s * radF53 w) (√(1 - s ^ 2) • w))

/-- `xLat` with the reflection as a free matrix. -/
noncomputable def xQ (H : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (v : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  H.mulVec (consV s (√(1 - s ^ 2) • v))

lemma continuous_radF {ι : Type} [Fintype ι] : Continuous (radF53 (ι := ι)) := by
  unfold radF53; fun_prop

lemma continuous_xP :
    Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × ℝ) × (Fin (n - 1) → ℝ) =>
      xP p.1.1 p.1.2 p.2) := by
  unfold xP
  have hs : Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × ℝ) × (Fin (n - 1) → ℝ) => p.1.2) :=
    continuous_snd.comp continuous_fst
  exact Continuous.matrix_mulVec (continuous_fst.comp continuous_fst)
    (continuous_consV.comp ((hs.mul (continuous_radF.comp continuous_snd)).prodMk
      ((Real.continuous_sqrt.comp (continuous_const.sub (hs.pow 2))).smul continuous_snd)))

lemma continuous_xQ :
    Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × ℝ) × (Fin (n - 1) → ℝ) =>
      xQ p.1.1 p.1.2 p.2) := by
  unfold xQ
  have hs : Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × ℝ) × (Fin (n - 1) → ℝ) => p.1.2) :=
    continuous_snd.comp continuous_fst
  exact Continuous.matrix_mulVec (continuous_fst.comp continuous_fst)
    (continuous_consV.comp (hs.prodMk
      ((Real.continuous_sqrt.comp (continuous_const.sub (hs.pow 2))).smul continuous_snd)))

/-! ## Measurability of the parameter map -/

/-- The full parameter: `((b̂, (A₁, A₂)), (H, s))`. -/
abbrev PP (n : ℕ) : Type := QP n × (Matrix (Fin n) (Fin n) ℝ × ℝ)

/-- The parameter of the pair `(k, a)`. -/
noncomputable def parK (k : AgFam n) (a : Ix n) : PP n :=
  ((bhat (bK k), k.2), (hhMat (uHat (repK k)), latK k a))

lemma measurable_rhoC_key : Measurable (fun k : AgFam n => rhoC k.1.1 k.1.2) := by
  unfold rhoC
  have h1 : Measurable (fun k : AgFam n => normSq k.1.1) :=
    continuous_normSq.measurable.comp (measurable_fst.comp measurable_fst)
  exact (h1.add (measurable_const.mul ((measurable_snd.comp measurable_fst).pow_const 2))).sqrt

lemma measurable_bK : Measurable (bK (n := n)) := by
  unfold bK
  exact (measurable_const.div measurable_rhoC_key).smul (BstLean.Part150.measurable_bT (n := n) (m := mA n) n n)

lemma measurable_bhat {m : ℕ} : Measurable (bhat (m := m)) := by
  unfold bhat
  exact (continuous_normSq.measurable.sqrt.inv).smul measurable_id

lemma measurable_hhMat_key :
    Measurable (fun k : AgFam n => hhMat (uHat (repK k))) := by
  have hu : Measurable (fun k : AgFam n => uHat (repK k)) := by
    unfold uHat repK
    exact (continuous_normSq.measurable.comp (measurable_fst.comp measurable_fst)).sqrt.inv.smul
      (measurable_fst.comp measurable_fst)
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  unfold hhMat
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  refine measurable_const.sub ?_
  have hw : Measurable (fun k : AgFam n => e0 n - uHat (repK k)) := measurable_const.sub hu
  refine ((measurable_const.mul (continuous_normSq.measurable.comp hw).inv)).mul ?_
  exact ((measurable_pi_apply i).comp hw).mul ((measurable_pi_apply j).comp hw)

lemma measurable_parK : Measurable (fun z : AgFam n × Ix n => parK z.1 z.2) := by
  unfold parK
  refine ((measurable_bhat.comp (measurable_bK.comp measurable_fst)).prodMk
    (measurable_snd.comp measurable_fst)).prodMk
    ((measurable_hhMat_key.comp measurable_fst).prodMk ?_)
  unfold latK
  exact measurable_latitude_comp
    (continuous_normSq.measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sqrt
    (measurable_snd.comp (measurable_fst.comp measurable_fst)) measurable_snd

/-! ## Joint measurability of `Ψ` -/

lemma measurable_gradSq_param {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] [SecondCountableTopology P]
    {G : P → (Fin (n - 1) → ℝ) → ℝ} (hG : Continuous (Function.uncurry G)) :
    Measurable (fun z : P × (Fin (n - 1) → ℝ) => gradSq (G z.1) z.2) := by
  unfold gradSq
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_fderiv_apply_const_with_param ℝ hG (Pi.single i 1)).pow_const 2

lemma xLatH_eq_xP (c : Ret n) (s : ℝ) (w : Fin (n - 1) → ℝ) :
    xLatH c s w = xP (hhMat (uHat c)) s w := rfl

lemma xLat_eq_xQ (c : Ret n) (s : ℝ) (v : Fin (n - 1) → ℝ) :
    xLat c s v = xQ (hhMat (uHat c)) s v := rfl

/-- The field composed with the frame map, as a function of the full parameter. -/
noncomputable def GK (Φ₀ : QP n → (Fin n → ℝ) → ℝ) (P : PP n) (w : Fin (n - 1) → ℝ) : ℝ :=
  Φ₀ P.1 (xP P.2.1 P.2.2 w)

lemma continuous_GK {Φ₀ : QP n → (Fin n → ℝ) → ℝ}
    (hc : Continuous (fun p : QP n × (Fin n → ℝ) => Φ₀ p.1 p.2)) :
    Continuous (Function.uncurry (GK Φ₀)) := by
  have : Function.uncurry (GK Φ₀) = (fun p : QP n × (Fin n → ℝ) => Φ₀ p.1 p.2) ∘
      (fun z : PP n × (Fin (n - 1) → ℝ) => (z.1.1, xP z.1.2.1 z.1.2.2 z.2)) := by
    funext z; rfl
  rw [this]
  exact hc.comp ((continuous_fst.comp continuous_fst).prodMk
    (continuous_xP.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

lemma psiK_eq_GK {Φ : AgFam n → (Fin n → ℝ) → ℝ} {Φ₀ : QP n → (Fin n → ℝ) → ℝ}
    (hΦ : ∀ k, Φ k = Φ₀ (bhat (bK k), k.2)) (k : AgFam n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    psiK Φ k a v = √(gradSq (GK Φ₀ (parK k a)) v -
        Φ₀ (parK k a).1 (xQ (parK k a).2.1 (parK k a).2.2 (unitF53 v)) ^ 2) ^ 2 := by
  unfold psiK tanSq
  rw [hΦ k]
  simp only [xLatH_eq_xP, xLat_eq_xQ]
  rfl

lemma measurable_gradSq_GK {X : Type*} [MeasurableSpace X] {Φ₀ : QP n → (Fin n → ℝ) → ℝ}
    (hc : Continuous (fun p : QP n × (Fin n → ℝ) => Φ₀ p.1 p.2)) {φ : X → PP n}
    {w : X → Fin (n - 1) → ℝ} (hφ : Measurable φ) (hw : Measurable w) :
    Measurable (fun x => gradSq (GK Φ₀ (φ x)) (w x)) := by
  have h0 := measurable_gradSq_param (continuous_GK hc)
  have h1 : Measurable (fun x => (φ x, w x)) := hφ.prodMk hw
  have h2 := Measurable.comp h0 h1
  rw [Function.comp_def] at h2
  exact h2

/-- `Ψ` from a continuous field form `Φ₀` with `Φ k = Φ₀ (b̂, (A₁, A₂))`. -/
lemma measurable_psiK_of {Φ : AgFam n → (Fin n → ℝ) → ℝ} {Φ₀ : QP n → (Fin n → ℝ) → ℝ}
    (hΦ : ∀ k, Φ k = Φ₀ (bhat (bK k), k.2))
    (hc : Continuous (fun p : QP n × (Fin n → ℝ) => Φ₀ p.1 p.2)) :
    Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2) := by
  have e : (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2) =
      fun z => √(gradSq (GK Φ₀ (parK z.1 z.2.1)) z.2.2 -
        Φ₀ (parK z.1 z.2.1).1 (xQ (parK z.1 z.2.1).2.1 (parK z.1 z.2.1).2.2 (unitF53 z.2.2)) ^ 2)
          ^ 2 := funext fun z => psiK_eq_GK hΦ z.1 z.2.1 z.2.2
  rw [e]
  have hpar : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => parK z.1 z.2.1) := by
    unfold parK
    refine ((measurable_bhat.comp (measurable_bK.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_hhMat_key.comp measurable_fst).prodMk ?_)
    unfold latK
    exact measurable_latitude_comp
      (continuous_normSq.measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sqrt
      (measurable_snd.comp (measurable_fst.comp measurable_fst)) (measurable_fst.comp measurable_snd)
  have h1 : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) =>
      gradSq (GK Φ₀ (parK z.1 z.2.1)) z.2.2) :=
    measurable_gradSq_GK hc hpar (measurable_snd.comp measurable_snd)
  have hx : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) =>
      xQ (parK z.1 z.2.1).2.1 (parK z.1 z.2.1).2.2 (unitF53 z.2.2)) :=
    continuous_xQ.measurable.comp ((measurable_snd.comp hpar).prodMk
      (measurable_unitF.comp (measurable_snd.comp measurable_snd)))
  have h2 : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) =>
      Φ₀ (parK z.1 z.2.1).1 (xQ (parK z.1 z.2.1).2.1 (parK z.1 z.2.1).2.2 (unitF53 z.2.2))) :=
    hc.measurable.comp ((measurable_fst.comp hpar).prodMk hx)
  exact ((h1.sub (h2.pow_const 2)).sqrt).pow_const 2

theorem measurable_psiK_f :
    Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK fK z.1 z.2.1 z.2.2) :=
  measurable_psiK_of fK_eq_FF continuous_FF

theorem measurable_psiK_s :
    Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK sK z.1 z.2.1 z.2.2) :=
  measurable_psiK_of sK_eq_SS continuous_SS

end BstLean.Part166
