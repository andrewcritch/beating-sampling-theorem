import BstLean.Part272Even
import BstLean.Part272Reduce

/-!
# Part 272 (V4): the stated design, and its equality with `paperDesignP` for even `n`

Paper: `theorem7-01-statement-program.tex`, steps 4 and 5 (Decision A) and the sphere rule of
Lemma `t7:p01:moments` with the odd arithmetic rule.

Conventions (Decision A):
* `α_i = alphaE c i = a_i·u` with `u = uEff c` (`= ĉ/|ĉ|` for `ĉ ≠ 0`, `= −e₀` for `ĉ = 0`).
  The paper text `α_i = μ_i/|ĉ|` agrees for `ĉ ≠ 0` but gives `0` at `ĉ = 0`; see the report.
* `k_i = √(1 − s²)·κ_i` with Lean's `Real.sqrt`, which is the paper's `√max(0, ·)`.
* For odd `n` the sphere rule is the paper's arithmetic rule (`sphAodd`, `sphEodd`), with the
  two clips `max(0, ā)` and `max(ē, ā²)`, where `ā` is the clipped first moment.

`statedDesign_even`: for even `n ≥ 8`, `statedDesign n = paperDesignP n`.
-/

namespace BstLean.Part272

open Real MeasureTheory
open BstLean.Part130 (relu normSq mA measurable_relu continuous_normSq)
open BstLean.Part157 (Ret Design paperDesign ATsum QTsum)
open BstLean.Part150 (binMean measurable_binMean_affine)
open BstLean.Part161 (hhMat uHat)
open BstLean.Part169 (A1 A2 a1Bar e1Bar vsig2 Jz betaP beta2P bR fPass wPass passF passW nodeS
  paperDesignP measurable_passF measurable_passW measurable_hhMat measurable_uHat measurable_bR
  measurable_nodeS)

variable {n : ℕ}

/-! ## The odd arithmetic rule (transcription) -/

/-- `T_o = min{T ≥ 1 : 4^T ≥ 10¹¹⁰ n²⁰}`. -/
noncomputable def Todd (n : ℕ) : ℕ := sInf {T : ℕ | 1 ≤ T ∧ 10 ^ 110 * n ^ 20 ≤ 4 ^ T}

/-- `T_{π,o} = min{T ≥ 1 : 25^T ≥ 10¹¹⁰ n²⁰}`. -/
noncomputable def Tpio (n : ℕ) : ℕ := sInf {T : ℕ | 1 ≤ T ∧ 10 ^ 110 * n ^ 20 ≤ 25 ^ T}

/-- `π_o = 16 A_{T_{π,o}}(1/5) − 4 A_{T_{π,o}}(1/239)`. -/
noncomputable def piO (n : ℕ) : ℝ := 16 * ATsum (Tpio n) (1 / 5) - 4 * ATsum (Tpio n) (1 / 239)

/-- The arithmetic inverse sine for `v ≥ 0`: `Q_{T_o}(v)` on `[0, 1/2]`, and
`π_o/2 − 2Q_{T_o}(√((1 − v)/2))` above `1/2`. -/
noncomputable def asinPos (n : ℕ) (v : ℝ) : ℝ :=
  if v ≤ 1 / 2 then QTsum (Todd n) v else piO n / 2 - 2 * QTsum (Todd n) (√((1 - v) / 2))

/-- The arithmetic inverse sine with the sign restored for negative arguments. -/
noncomputable def asinO (n : ℕ) (v : ℝ) : ℝ := if 0 ≤ v then asinPos n v else -asinPos n (-v)

/-- `D₀ = 2`, `D_r = D_{r−1}(2r + 2)/(2r + 1)`. -/
noncomputable def DD : ℕ → ℝ
  | 0 => 2
  | r + 1 => DD r * (2 * ((r : ℝ) + 1) + 2) / (2 * ((r : ℝ) + 1) + 1)

/-- `K₀(d) = π_o/2 − arcsin_o d`, `K_r(d) = (2r−1)/(2r)·K_{r−1}(d) − d(1−d²)^{r−1/2}/(2r)`,
with `(1−d²)^{r−1/2} = (1−d²)^{r−1}·√(1−d²)`. -/
noncomputable def KK (n : ℕ) (d : ℝ) : ℕ → ℝ
  | 0 => piO n / 2 - asinO n d
  | r + 1 => (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * KK n d r -
      d * ((1 - d ^ 2) ^ r * √(1 - d ^ 2)) / (2 * ((r : ℝ) + 1))

/-- The odd first-moment combination `𝒩_P(mJ₀ + kJ₁)`, `P = (n−5)/2`, `𝒩_P = D_P/π_o`,
`J₀ = K_{P+1}(d)`, `J₁ = (1−d²)^{P+3/2}/(2P+3)`, `d = −m/k`. -/
noncomputable def oddA (n : ℕ) (m k : ℝ) : ℝ :=
  DD ((n - 5) / 2) / piO n * (m * KK n (-m / k) ((n - 5) / 2 + 1) +
    k * ((1 - (-m / k) ^ 2) ^ ((n - 5) / 2 + 1) * √(1 - (-m / k) ^ 2) /
      (2 * (((n - 5) / 2 : ℕ) : ℝ) + 3)))

/-- The odd second-moment combination `𝒩_P(m²J₀ + 2mkJ₁ + k²J₂)`, `J₂ = K_{P+1} − K_{P+2}`. -/
noncomputable def oddE (n : ℕ) (m k : ℝ) : ℝ :=
  DD ((n - 5) / 2) / piO n * (m ^ 2 * KK n (-m / k) ((n - 5) / 2 + 1) +
    2 * m * k * ((1 - (-m / k) ^ 2) ^ ((n - 5) / 2 + 1) * √(1 - (-m / k) ^ 2) /
      (2 * (((n - 5) / 2 : ℕ) : ℝ) + 3)) +
    k ^ 2 * (KK n (-m / k) ((n - 5) / 2 + 1) - KK n (-m / k) ((n - 5) / 2 + 2)))

/-- The odd first-moment rule with the four branches and the clip `max(0, ā)`. -/
noncomputable def sphAodd (n : ℕ) (m k : ℝ) : ℝ :=
  if k = 0 then relu m else if k ≤ m then m else if m ≤ -k then 0 else max 0 (oddA n m k)

/-- The odd second-moment rule with the four branches and the clip `max(ē, ā²)`. -/
noncomputable def sphEodd (n : ℕ) (m k : ℝ) : ℝ :=
  if k = 0 then relu m ^ 2 else if k ≤ m then m ^ 2 + k ^ 2 / ((n : ℝ) - 1) else
    if m ≤ -k then 0 else max (oddE n m k) (max 0 (oddA n m k) ^ 2)

/-! ## The stated first-layer moments and passes -/

/-- The stated `ā_i(s)`: the sphere rule at `m = s·α_i`, `k = √(1 − s²)·κ_i`. -/
noncomputable def a1St (c : Ret n) (s : ℝ) (i : Fin (mA n)) : ℝ :=
  if Even n then sphA n (s * alphaE c i) (√(1 - s ^ 2) * kappaE c i)
  else sphAodd n (s * alphaE c i) (√(1 - s ^ 2) * kappaE c i)

/-- The stated `ē_i(s)`. -/
noncomputable def e1St (c : Ret n) (s : ℝ) (i : Fin (mA n)) : ℝ :=
  if Even n then sphE n (s * alphaE c i) (√(1 - s ^ 2) * kappaE c i)
  else sphEodd n (s * alphaE c i) (√(1 - s ^ 2) * kappaE c i)

/-- The passes of Part 169 for general first-layer moment tables `a`, `e`. -/
noncomputable def vsig2G (a e : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ) : ℝ :=
  max 0 (2 / (mA n : ℝ) * (∑ i, e c s i - normSq (a c s)))

noncomputable def betaG (a e : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ)
    (j : Fin (mA n)) : ℝ :=
  binMean (Jz n) (fun z => relu ((A2 c).mulVec (a c s) j + √(vsig2G a e c s) * z))

noncomputable def beta2G (a e : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ)
    (j : Fin (mA n)) : ℝ :=
  binMean (Jz n) (fun z => relu ((A2 c).mulVec (a c s) j + √(vsig2G a e c s) * z) ^ 2)

noncomputable def fPassG (a e : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ) : ℝ :=
  (∑ j, betaG a e c s j * bR c j) / (√(n : ℝ) * √(normSq (bR c)))

noncomputable def wPassG (a e : Ret n → ℝ → Fin (mA n) → ℝ) (c : Ret n) (s : ℝ) : ℝ :=
  (∑ j, beta2G a e c s j) / (n : ℝ)

theorem fPass_eq_G (c : Ret n) (s : ℝ) : fPass c s = fPassG a1Bar e1Bar c s := rfl
theorem wPass_eq_G (c : Ret n) (s : ℝ) : wPass c s = wPassG a1Bar e1Bar c s := rfl

/-- The stated tables `f̃_g`, `ω̃_g`. -/
noncomputable def passFSt (c : Ret n) (g : ℕ) : ℝ := fPassG a1St e1St c (nodeS c g)
noncomputable def passWSt (c : Ret n) (g : ℕ) : ℝ := wPassG a1St e1St c (nodeS c g)

/-! ## Measurability -/

theorem measurable_JJ (P j : ℕ) : Measurable (JJ P j) := by
  unfold JJ
  exact Finset.measurable_sum _ fun r _ =>
    ((measurable_const.sub (measurable_id.pow_const _)).const_mul _).div_const _

theorem measurable_sphA (n : ℕ) : Measurable (fun p : ℝ × ℝ => sphA n p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => -p.1 / p.2) := measurable_fst.neg.div measurable_snd
  unfold sphA
  refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    (measurable_relu.comp measurable_fst) ?_
  refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_fst ?_
  refine Measurable.ite (measurableSet_le measurable_fst measurable_snd.neg) measurable_const ?_
  exact measurable_const.mul ((measurable_fst.mul ((measurable_JJ _ _).comp hd)).add
    (measurable_snd.mul ((measurable_JJ _ _).comp hd)))

theorem measurable_sphE (n : ℕ) : Measurable (fun p : ℝ × ℝ => sphE n p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => -p.1 / p.2) := measurable_fst.neg.div measurable_snd
  unfold sphE
  refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    ((measurable_relu.comp measurable_fst).pow_const 2) ?_
  refine Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    ((measurable_fst.pow_const 2).add ((measurable_snd.pow_const 2).div_const _)) ?_
  refine Measurable.ite (measurableSet_le measurable_fst measurable_snd.neg) measurable_const ?_
  exact measurable_const.mul
    ((((measurable_fst.pow_const 2).mul ((measurable_JJ _ _).comp hd)).add
      (((measurable_const.mul measurable_fst).mul measurable_snd).mul
        ((measurable_JJ _ _).comp hd))).add
      ((measurable_snd.pow_const 2).mul ((measurable_JJ _ _).comp hd)))

theorem measurable_QTsum (T : ℕ) : Measurable (QTsum T) := by
  unfold QTsum
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_id.pow_const _).const_mul _).div_const _

theorem measurable_asinO (n : ℕ) : Measurable (asinO n) := by
  have hP : Measurable (asinPos n) := by
    unfold asinPos
    exact Measurable.ite measurableSet_Iic (measurable_QTsum _)
      (measurable_const.sub (((measurable_QTsum _).comp
        ((measurable_const.sub measurable_id).div_const 2).sqrt).const_mul 2))
  unfold asinO
  exact Measurable.ite measurableSet_Ici hP (hP.comp measurable_neg).neg

theorem measurable_KK (n r : ℕ) : Measurable (fun d => KK n d r) := by
  induction r with
  | zero =>
    simp only [KK]
    exact measurable_const.sub (measurable_asinO n)
  | succ r ih =>
    simp only [KK]
    exact (ih.const_mul _).sub ((measurable_id.mul
      (((measurable_const.sub (measurable_id.pow_const 2)).pow_const r).mul
        (measurable_const.sub (measurable_id.pow_const 2)).sqrt)).div_const _)

theorem measurable_oddA (n : ℕ) : Measurable (fun p : ℝ × ℝ => oddA n p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => -p.1 / p.2) := measurable_fst.neg.div measurable_snd
  have hK : ∀ r, Measurable (fun p : ℝ × ℝ => KK n (-p.1 / p.2) r) :=
    fun r => (measurable_KK n r).comp hd
  have hw : Measurable (fun p : ℝ × ℝ => 1 - (-p.1 / p.2) ^ 2) :=
    measurable_const.sub (hd.pow_const 2)
  unfold oddA
  exact measurable_const.mul ((measurable_fst.mul (hK _)).add
    (measurable_snd.mul (((hw.pow_const _).mul hw.sqrt).div_const _)))

theorem measurable_oddE (n : ℕ) : Measurable (fun p : ℝ × ℝ => oddE n p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => -p.1 / p.2) := measurable_fst.neg.div measurable_snd
  have hK : ∀ r, Measurable (fun p : ℝ × ℝ => KK n (-p.1 / p.2) r) :=
    fun r => (measurable_KK n r).comp hd
  have hw : Measurable (fun p : ℝ × ℝ => 1 - (-p.1 / p.2) ^ 2) :=
    measurable_const.sub (hd.pow_const 2)
  unfold oddE
  exact measurable_const.mul
    ((((measurable_fst.pow_const 2).mul (hK _)).add
      (((measurable_const.mul measurable_fst).mul measurable_snd).mul
        (((hw.pow_const _).mul hw.sqrt).div_const _))).add
      ((measurable_snd.pow_const 2).mul ((hK _).sub (hK _))))

theorem measurable_sphAodd (n : ℕ) : Measurable (fun p : ℝ × ℝ => sphAodd n p.1 p.2) := by
  unfold sphAodd
  refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    (measurable_relu.comp measurable_fst) ?_
  refine Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_fst ?_
  refine Measurable.ite (measurableSet_le measurable_fst measurable_snd.neg) measurable_const ?_
  exact measurable_const.max (measurable_oddA n)

theorem measurable_sphEodd (n : ℕ) : Measurable (fun p : ℝ × ℝ => sphEodd n p.1 p.2) := by
  unfold sphEodd
  refine Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    ((measurable_relu.comp measurable_fst).pow_const 2) ?_
  refine Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    ((measurable_fst.pow_const 2).add ((measurable_snd.pow_const 2).div_const _)) ?_
  refine Measurable.ite (measurableSet_le measurable_fst measurable_snd.neg) measurable_const ?_
  exact (measurable_oddE n).max ((measurable_const.max (measurable_oddA n)).pow_const 2)

theorem measurable_A1 : Measurable (fun c : Ret n => A1 c) :=
  measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))

theorem measurable_A1_entry (i : Fin (mA n)) (j : Fin n) :
    Measurable (fun c : Ret n => A1 c i j) :=
  measurable_pi_iff.mp (measurable_pi_iff.mp measurable_A1 i) j

theorem measurable_uEff : Measurable (fun c : Ret n => uEff c) := by
  unfold uEff
  exact BstLean.Part149.measurable_mulVec_joint.comp
    ((measurable_hhMat.comp measurable_uHat).prodMk measurable_const)

theorem measurable_alphaE (i : Fin (mA n)) : Measurable (fun c : Ret n => alphaE c i) := by
  unfold alphaE
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_A1_entry i j).mul (measurable_pi_iff.mp measurable_uEff j)

theorem measurable_kappaE (i : Fin (mA n)) : Measurable (fun c : Ret n => kappaE c i) := by
  unfold kappaE
  exact (measurable_const.max ((Finset.measurable_sum _ fun j _ =>
    (measurable_A1_entry i j).pow_const 2).sub ((measurable_alphaE i).pow_const 2))).sqrt

theorem measurable_mk (i : Fin (mA n)) :
    Measurable (fun p : Ret n × ℝ =>
      (p.2 * alphaE p.1 i, √(1 - p.2 ^ 2) * kappaE p.1 i)) :=
  (measurable_snd.mul ((measurable_alphaE i).comp measurable_fst)).prodMk
    ((measurable_const.sub (measurable_snd.pow_const 2)).sqrt.mul
      ((measurable_kappaE i).comp measurable_fst))

theorem measurable_a1St (i : Fin (mA n)) :
    Measurable (fun p : Ret n × ℝ => a1St p.1 p.2 i) := by
  by_cases h : Even n
  · simp only [a1St, h, if_true]
    exact (measurable_sphA n).comp (measurable_mk i)
  · simp only [a1St, h, if_false]
    exact (measurable_sphAodd n).comp (measurable_mk i)

theorem measurable_e1St (i : Fin (mA n)) :
    Measurable (fun p : Ret n × ℝ => e1St p.1 p.2 i) := by
  by_cases h : Even n
  · simp only [e1St, h, if_true]
    exact (measurable_sphE n).comp (measurable_mk i)
  · simp only [e1St, h, if_false]
    exact (measurable_sphEodd n).comp (measurable_mk i)

section Gen

variable (a e : Ret n → ℝ → Fin (mA n) → ℝ)
  (hA : ∀ i, Measurable (fun p : Ret n × ℝ => a p.1 p.2 i))
  (hE : ∀ i, Measurable (fun p : Ret n × ℝ => e p.1 p.2 i))
include hA hE

theorem measurable_vsig2G {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => vsig2G a e (C x) (f x)) := by
  have hCf : Measurable (fun x => (C x, f x)) := hC.prodMk hf
  unfold vsig2G
  refine measurable_const.max (((Finset.measurable_sum _ fun i _ =>
    (hE i).comp hCf).sub ?_).const_mul _)
  unfold normSq
  exact Finset.measurable_sum _ fun i _ => ((hA i).comp hCf).pow_const 2

theorem measurable_A2aG {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) (j : Fin (mA n)) :
    Measurable (fun x => (A2 (C x)).mulVec (a (C x) (f x)) j) := by
  have hCf : Measurable (fun x => (C x, f x)) := hC.prodMk hf
  have hA2 : Measurable (fun x => A2 (C x)) :=
    measurable_snd.comp (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp hC)))
  have ha : Measurable (fun x => a (C x) (f x)) :=
    measurable_pi_iff.mpr fun i => (hA i).comp hCf
  exact (measurable_pi_apply j).comp
    (BstLean.Part149.measurable_mulVec_joint.comp (hA2.prodMk ha))

theorem measurable_fPassG {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => fPassG a e (C x) (f x)) := by
  unfold fPassG betaG
  have hb : Measurable (fun x => bR (C x)) := measurable_bR.comp hC
  refine (Finset.measurable_sum _ fun j _ => ?_).div
    (measurable_const.mul ((continuous_normSq.measurable.comp hb).sqrt))
  exact (measurable_binMean_affine (Jz n) measurable_relu (measurable_A2aG a e hA hE hC hf j)
    (measurable_vsig2G a e hA hE hC hf).sqrt).mul ((measurable_pi_apply j).comp hb)

theorem measurable_wPassG {β : Type*} [MeasurableSpace β] {C : β → Ret n} {f : β → ℝ}
    (hC : Measurable C) (hf : Measurable f) : Measurable (fun x => wPassG a e (C x) (f x)) := by
  unfold wPassG beta2G
  refine (Finset.measurable_sum _ fun j _ => ?_).div_const _
  exact measurable_binMean_affine (Jz n) (measurable_relu.pow_const 2)
    (measurable_A2aG a e hA hE hC hf j) (measurable_vsig2G a e hA hE hC hf).sqrt

end Gen

theorem measurable_passFSt (g : ℕ) : Measurable (fun c : Ret n => passFSt c g) :=
  measurable_fPassG a1St e1St measurable_a1St measurable_e1St measurable_id (measurable_nodeS g)

theorem measurable_passWSt (g : ℕ) : Measurable (fun c : Ret n => passWSt c g) :=
  measurable_wPassG a1St e1St measurable_a1St measurable_e1St measurable_id (measurable_nodeS g)

/-! ## The stated design -/

/-- **The stated program as a design** (Decision A). -/
noncomputable def statedDesign (n : ℕ) : Design n :=
  paperDesign n passFSt passWSt measurable_passFSt measurable_passWSt

theorem statedDesign_toCentres :
    (statedDesign n).toCentres = BstLean.Part157.paperCentres n := rfl

theorem statedDesign_tau0 : (statedDesign n).tau0 = (paperDesignP n).tau0 := rfl

theorem paperDesign_congr {f f' w w' : Ret n → ℕ → ℝ} (hf : f = f') (hw : w = w')
    (mf : ∀ g, Measurable (fun c => f c g)) (mw : ∀ g, Measurable (fun c => w c g))
    (mf' : ∀ g, Measurable (fun c => f' c g)) (mw' : ∀ g, Measurable (fun c => w' c g)) :
    paperDesign n f w mf mw = paperDesign n f' w' mf' mw' := by
  subst hf; subst hw; rfl

/-- For even `n ≥ 8` the stated moments are the exact moments. -/
theorem a1St_even (hn : 8 ≤ n) (he : Even n) (c : Ret n) (s : ℝ) : a1St c s = a1Bar c s := by
  funext i
  have hk : 0 ≤ √(1 - s ^ 2) * kappaE c i := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  rw [a1Bar_reduce (by omega), (sph_even hn he (s * alphaE c i) hk).1, a1St, if_pos he]

theorem e1St_even (hn : 8 ≤ n) (he : Even n) (c : Ret n) (s : ℝ) : e1St c s = e1Bar c s := by
  funext i
  have hk : 0 ≤ √(1 - s ^ 2) * kappaE c i := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  rw [e1Bar_reduce (by omega), (sph_even hn he (s * alphaE c i) hk).2, e1St, if_pos he]

/-- **V4.** For even `n ≥ 8` the stated design is `paperDesignP n`. -/
theorem statedDesign_even (hn : 8 ≤ n) (he : Even n) : statedDesign n = paperDesignP n := by
  have ha : a1St (n := n) = a1Bar := funext fun c => funext fun s => a1St_even hn he c s
  have he' : e1St (n := n) = e1Bar := funext fun c => funext fun s => e1St_even hn he c s
  unfold statedDesign paperDesignP
  refine paperDesign_congr ?_ ?_ _ _ _ _
  · funext c g
    simp only [passFSt, passF, fPass_eq_G, ha, he']
  · funext c g
    simp only [passWSt, passW, wPass_eq_G, ha, he']

end BstLean.Part272

#print axioms BstLean.Part272.statedDesign_even
