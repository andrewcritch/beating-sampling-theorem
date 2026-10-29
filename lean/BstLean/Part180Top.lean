import BstLean.Part180W20
import BstLean.Part180W128
import BstLean.Part180Split
import BstLean.Part177Split


/-!
# Part 180 (file `Top`): the top of the chain at `n ≥ 24 000` with the Lemma HQ root
(namespace `BstLean.Part179.N30.N27.N26.N24`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 179's file `TopN` at `n ≥ 24 000`, with Lemma HQ in the fluctuation root. The
namespace is a sub-namespace of Part 179's `N26` (inherited lemmas of the chain; local names shadow
them). Numbers: `W₂₀ ≤ (1.0174·θ/n)²⁰` (file `W20`); Lemma PP at order 800 with `η_PP = 0.004`:
`jS ≤ 1.0400`, `M = 1.0952`; mass constant `0.5884`, `s0W = 0.5088`; floor mass at `sd = 0.452`
`≤ 9.4·10⁻¹²`. Root pieces at `s ≥ 0.452`, `g² ≤ 2/24 000`: `priceC ≤ 374·g⁴`,
`cubP ≤ 240 000·g⁶` (`cubP_le`, weights `λ = 0.85`, `λ' = 0.64`), HQ middle root
`√(𝒞/4 + (3/4)·cubP) ≤ 869` (`rc_price24`), removal root `≤ 31`, displacement `≤ 207`, root sum
`≤ 1120` (units `10⁻⁶`, `root_core24`); split `0.00112 + 0.00533`; certificate with
`W₁₂₈ ≤ (1.0216τ²/ρ²)¹²⁸` (file `W128`): `Θ = 0.5452`, `K² ≤ 5`, charge `≤ 4·10⁻⁵`.
The theorems from `classifier_paper_free23_massW24` up take `hHQ : BstLean.Part180.HQ_stmt`.
The docstrings of copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N24

/-- The mean floor `s0W = 0.5095` (Part 175 had `0.5096`, valid from `45 000`). -/
noncomputable def s0W : ℝ := 5088 / 10000

/-- The numeric condition on `s0W` (`n ≥ 40 000`). -/
lemma s0W_cond {n : ℕ} (hn : 24000 ≤ n) :
    s0W ^ 2 ≤ 1 - 18334 / 1000 / (n : ℝ) * (2 + 18334 / 1000 / (n : ℝ)) -
      (8553 / 10000 + 46 / 10000) ^ 2 - 2 * (11911 / 10000) / n := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 24000 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hnR
  have e1 : 18334 / 1000 / (n : ℝ) = 18334 / 1000 * x := by rw [hx]; ring
  have e2 : 2 * (11911 / 10000) / (n : ℝ) = 2 * (11911 / 10000) * x := by rw [hx]; ring
  rw [e1, e2]
  unfold s0W
  nlinarith

section SMass
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr nuA jS)
open BstLean.Part134 (res sig)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA hE8_of_good CAn E0 E0_nonneg roomB roomB_ge)

open BstLean.Part175 (win528_goodA)

variable {n : ℕ}

/-! ## The radius moment `W₂₀` (the layered bound of file `W20`) -/

/-- **`E[(τ²/|y|²)²⁰] ≤ (1.013·θ/n)²⁰`** for `n ≥ 40 000`, `0.46 ≤ θ ≤ 0.528` (file `W20`). -/
theorem W20_le_528_24 (hn : 24000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (10174 / 10000 * (thetaC c τ / n)) ^ 20 :=
  BstLean.Part180.W20_le_24 hn c hτ hθ0 hθ1

/-! ## The event `SXM24` with the sharper Lemma PP constant -/

/-- **The event of the gradient moment of order 40 with `M = 1.0670`** (`n ≥ 40 000`): `X₂₀ ≤ (1.0670·n)²⁰·W₂₀`. -/
def SXM24 (n : ℕ) : Set (AgFam n) :=
  {x | XqN 20 x.2.1 x.2.2 x.1.1 x.1.2 ≤ (10952 / 10000 * (n : ℝ)) ^ 20 * WqN 20 x.1.1 x.1.2}

theorem measurableSet_SXM24 (n : ℕ) : MeasurableSet (SXM24 n) :=
  measurableSet_le (measurable_XqN_fam 20) ((measurable_WqN_fam 20).const_mul _)

/-- `𝔪₈₀₀ ≤ 24.33`: `2⁸⁰⁰·800! ≤ 24.33¹⁶⁰⁰`. -/
lemma gaussMomConst_800_le : BstLean.Part152.gaussMomConst 800 ≤ 2433 / 100 := by
  have hp := BstLean.Part152.gaussMomConst_pow (P := 800) (by norm_num)
  have hN : (2 ^ 200) ^ 4 * Nat.factorial 800 * (100 ^ 200) ^ 8 ≤ (2433 ^ 200) ^ 8 := by
    norm_num [Nat.factorial]
  have h1 : BstLean.Part152.gaussMomConst 800 ^ (2 * 800) ≤ (2433 / 100 : ℝ) ^ (2 * 800) := by
    rw [hp]
    have e1 : (2 : ℝ) ^ 800 = (2 ^ 200) ^ 4 := by rw [← pow_mul]
    have e2 : (2433 / 100 : ℝ) ^ (2 * 800) = ((2433 : ℝ) ^ 200) ^ 8 / ((100 : ℝ) ^ 200) ^ 8 := by
      rw [div_pow, ← pow_mul, ← pow_mul]
    rw [e1, e2, le_div_iff₀ (by positivity)]
    exact_mod_cast hN
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) (by norm_num : (0 : ℝ) ≤ 2433 / 100)
    (by norm_num : (2 * 800 : ℕ) ≠ 0)
  exact absurd h1 (not_le.mpr this)

lemma sqrt_eta20_le : √(1 + 2 * (4 / 1000) : ℝ) ≤ 1004 / 1000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

lemma epsS_800_le {n : ℕ} (hn : 24000 ≤ n) :
    BstLean.Part153.epsS n 800 (4 / 1000) ≤ 17 / 10 ^ 6 := by
  have hnr : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : exp (-1) ≤ 36788 / 100000 := by
    have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
  have h10 : exp (-11) ≤ 17 / 10 ^ 6 := by
    have e : exp (-11) = exp (-1) ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc exp (-1) ^ 11 ≤ (36788 / 100000 : ℝ) ^ 11 := pow_le_pow_left₀ (exp_pos _).le h1 11
      _ ≤ 17 / 10 ^ 6 := by norm_num
  refine le_trans ?_ h10
  unfold BstLean.Part153.epsS
  rw [show ((800 : ℕ) : ℝ) = 800 by norm_num]
  refine Real.exp_le_exp.2 ?_
  have : (24000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
  have h12 : (11 : ℝ) ≤ (4 / 1000) ^ 2 * (n : ℝ) ^ 2 / 800 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- `jS n 800 (2/1000) ≤ 1.02654` for `n ≥ 40 000`. -/
lemma jS_800_le_24000 (hn : 24000 ≤ n) : jS n 800 (4 / 1000) ≤ 104000 / 100000 := by
  have hnr : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (1549 / 10 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := BstLean.Part152.gaussMomConst_nonneg 800
  have hg := gaussMomConst_800_le
  have hu : 1 / √(n : ℝ) ≤ 1 / (1549 / 10) := one_div_le_one_div_of_le (by norm_num) hs
  have hw : BstLean.Part152.gaussMomConst 800 / (n : ℝ) ≤ (2433 / 100) / 24000 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : BstLean.Part152.gaussMomConst 800 / √(n : ℝ) ≤ (2433 / 100) / (1549 / 10) := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (BstLean.Part153.jS_le_atoms n 800 (4 / 1000) BstLean.Part153.sqrt_two_le
    sqrt_eta20_le hu hw hgu (epsS_800_le hn)).trans ?_
  norm_num

lemma pow_98760_le : (98760 / 100000 : ℝ) ^ 800 ≤ 5 / 100000 := by
  have : (98760 / 100000 : ℝ) ^ 800 = ((98760 / 100000 : ℝ) ^ 100) ^ 8 := by rw [← pow_mul]
  rw [this]
  norm_num

/-- **The charge of `SXM24 n`**: at most `5·10⁻⁵` (`n ≥ 40 000`, `τ > 0`; Markov over the
weights at order `1600`: `q = 20`, `P' = 40`, Lemma PP with `P = 800`, `η = 0.002`). -/
theorem SXM24_charge (hn : 24000 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXM24 n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXM24 n} =
      {θ | (10952 / 10000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (10952 / 10000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 40) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 800 (4 / 1000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 4 / 1000) hx) (M := 10952 / 10000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 800 (4 / 1000)
  have hj := jS_800_le_24000 hn
  have hj2 : jS n 800 (4 / 1000) ^ 2 ≤ (104000 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 800 (4 / 1000) ^ 2 / (10952 / 10000) ≤ 98760 / 100000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio (20 * 40)).trans pow_98760_le

theorem SXM24_ret_charge (hn : 24000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SXM24 n))ᶜ ≤
      5 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SXM24 n) (by norm_num) (fun c τ hτ => SXM24_charge hn c τ hτ)

/-- **The gradient moment of order 40 on `SXM24` in the window `θ ≤ 0.528`**:
`t_A²⁰·X₂₀ ≤ (0.5737·γ_A/n)²⁰` (`1.067·1.013·0.528 ≤ 0.5737`), for `n ≥ 40 000`. -/
theorem tX20_le_W24 (hn : 24000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM24 n) :
    (2 / (mA n : ℝ)) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (5884 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 20 A₁ A₂ c τ ≤ (10952 / 10000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_528_24 hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  have h3 : XqN 20 A₁ A₂ c τ ≤ (10952 / 10000 * (10174 / 10000) * thetaC c τ) ^ 20 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]; congr 1; field_simp
  have hB : 10952 / 10000 * (10174 / 10000) * thetaC c τ ≤ 5884 / 10000 := by nlinarith
  have h4 := pow_le_pow_left₀ (by positivity) hB 20
  rw [hmA]
  calc (2 / (n : ℝ) ^ 2) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (2 / (n : ℝ) ^ 2) ^ 20 * (5884 / 10000) ^ 20 :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (5884 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by rw [← mul_pow]; congr 1; field_simp


/-- **The mass bound of order 40 at `n ≥ 40 000`**:
`β(n, sd) = (π/2)⁴⁰·E|g|⁴⁰·(0.5737/(n(s0W − sd)²))²⁰`. -/
noncomputable def betaMW24 (n : ℕ) (sd : ℝ) : ℝ :=
  (π / 2) ^ 40 * gmom 40 * (5884 / 10000 / ((n : ℝ) * (s0W - sd) ^ 2)) ^ 20

lemma betaMW24_nonneg (n : ℕ) (sd : ℝ) : 0 ≤ betaMW24 n sd := by
  unfold betaMW24
  have := gmom_nonneg 40
  have h : 0 ≤ (5884 / 10000 / ((n : ℝ) * (s0W - sd) ^ 2)) ^ 20 := by
    rw [show (20 : ℕ) = 2 * 10 by norm_num, pow_mul]; positivity
  positivity

/-- **The mass below the floor from the moment of order 40 of `σ`**, for one retained value:
with the quantities of the frame events and the event `SXM24 n`, in the window `θ ≤ 0.528`,
`∫_a ν{σ < √γ_A·sd} ≤ betaMW24 n sd` for `0 ≤ sd < s0W`, `n ≥ 23 000`. -/
theorem mass_order40W24 (hn : 24000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hθ2 : thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 11911 / 10000 * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) ≤ 2 / (n : ℝ) * (7315 / 10000))
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ 485 / 1000 * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 18334 / 1000 / (n : ℝ))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM24 n)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0W) :
    ∫ a', (stdGauss (Fin (n - 1))).real {v | sgA D c a' v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMW24 n sd := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : c.1.2 ≠ 0 := c_ne_of_theta (by omega) hτ hθ1
  rw [BstLean.Part162.mass_eq_stand (by omega) D c hc hτ]
  -- the tail bound of order 40
  set A₁ := c.2.1.1.1
  set A₂ := c.2.1.1.2
  set b := D.bA c.1 c.2.1.1
  set τ := D.tau0 c
  have hX := tX20_le_W24 hn hτ hθ0 hθ2 hS
  set K : ℝ := (π / 2) ^ 40 * (gmom 40 * (5884 / 10000 * (2 / (n : ℝ)) / n) ^ 20) with hK
  have hT : ∀ g : ℝ, 0 < g → (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c.1.2 τ b ξ - ∫ ζ, sigD A₁ A₂ c.1.2 τ b ζ ∂stdGauss (Fin n)|} ≤
        K / g ^ 40 := by
    intro g hg
    have h := sigD_tail (q := 20) (by norm_num) (by omega) A₁ A₂ c.1.2 hτ hb hg
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hK]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (gmom_nonneg _)) (by positivity)
  have hXi' : XiS A₁ A₂ c.1.2 τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n := hXi
  have hm := mass_bound_gen (by omega) A₁ A₂ c.1.2 hτ hb hXi' heb hxi hN22
    (e1 := 8553 / 10000) (e2 := 46 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by rw [div_le_iff₀ hn0]; nlinarith) hsd0 hsd (by
      have := s0W_cond (by omega : 24000 ≤ n)
      unfold s0W at this ⊢
      linarith) hT
  have hset : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < √(2 / (n : ℝ)) * sd} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1)
        (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    simp only [Set.mem_ofPred_eq]
    set R := normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))))
    have hR : 0 ≤ R := normSq_nonneg _
    have hsig : sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) = √(2 / (mA n : ℝ)) * √R := rfl
    rw [hsig, ← Real.sqrt_mul (by positivity)]
    have e : √(2 / (n : ℝ)) * sd = √(2 / (n : ℝ) * sd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hsd0]
    rw [e]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  rw [hset]
  refine hm.trans (le_of_eq ?_)
  -- the value of `K / (√γ_A (s0W − sd))⁴⁰`
  have hd : 0 < s0W - sd := by linarith
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs40 : (√(2 / (n : ℝ)) * (s0W - sd)) ^ 40 = (2 / (n : ℝ)) ^ 20 * ((s0W - sd) ^ 2) ^ 20 := by
    rw [mul_pow, show (40 : ℕ) = 2 * 20 by norm_num, pow_mul, pow_mul, Real.sq_sqrt hγ.le]
  unfold s0W at hs40 hd ⊢
  rw [hs40, hK]
  unfold betaMW24 s0W
  field_simp

/-- **The mass below the floor on the good set**: `∫_a ν{σ < √γ_A·sd} ≤ betaMW24 n sd`. -/
theorem mass_of_goodCW24 (hn : 24000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodC n (paperDesign n fT wT hf hw) (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM24 n)))
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0W) :
    ∫ a, (stdGauss (Fin (n - 1))).real
        {v | sgA (paperDesign n fT wT hf hw) c a v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMW24 n sd := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hG := goodC16_of_goodA hn16 fT wT hf hw hc
  have hSc : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hc.2.2.1.1.2 hτ
  have hS20 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM24 n := hc.2.1.2.1.1.1.2 hτ
  have hθ2 := (win528_goodA hn16 fT wT hf hw _ hc).2.2
  obtain ⟨hxi, -, -, hpos, hX4, hN22, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have heb := eb16_sharp hn16 hτ hθ0 hθ1 hG hSc
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) :=
    paperDesign_agentCentre fT wT hf hw c
  rw [← hb] at hxi hpos heb
  have hXi := (BstLean.Part153.XiS_le_Xi4 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ).trans hX4
  exact mass_order40W24 hn D c hτ hθ0 hθ1 hθ2 hpos hXi heb hxi hN22 hS20 hsd0 hsd

/-- **The free-event classifier theorem with the sharper floor mass (every `n ≥ 40 000`).**
Part 174's `classifier_paper_free23_mass40P` with `s0W`, `betaMW24` and `mass_of_goodCW24`. The caller
event `E_A` is intersected with `agentEv D (SXM24 n)`, whose charge `5·10⁻⁵` is paid here: the room
for `E_A` is `roomC − 5·10⁻⁵`. -/
theorem classifier_paper_free23_massW24 (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM24 n))),
      ∃ (wl ws sd η CL CS E : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hsd0 : 0 < sd) (hsd : sd < s0W) (hE : 0 ≤ E)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12),
        0 < wl ∧ 0 < ws ∧ eps0 ws (√(2 / (n : ℝ)) * sd) < 1 ∧
        BstLean.Part180.rootFLH wl ws η (CAn n) (85 / 100) (64 / 100)
          (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          hE (betaMW24_nonneg n sd) hL12 hS12 hE8
          (mass_of_goodCW24 hn fT wT hf hw hc hsd0.le hsd)) ≤ 112 / 10 ^ 5 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws (√(2 / (n : ℝ)) * sd) η h0 h1)
          (533 / 10 ^ 5)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  set E1 := EA ∩ agentEv D (SXM24 n) with hE1
  have hE1m : MeasurableSet E1 := hEA.inter (measurableSet_agentEv D (measurableSet_SXM24 n))
  have hEA' : MeasurableSet (E1 ∩ agentEv D (SXqN n 20)) :=
    hE1m.inter (measurableSet_agentEv D (measurableSet_SXqN n 20))
  have hA' : (retDist (paperCentres n)).real (S ∩ (E1 ∩ agentEv D (SXqN n 20))ᶜ) ≤
      δA + 5 / 100000 + 5 / 100000 := by
    have hsub : S ∩ (E1 ∩ agentEv D (SXqN n 20))ᶜ ⊆
        ((S ∩ EAᶜ) ∪ (agentEv D (SXM24 n))ᶜ) ∪ (agentEv D (SXqN n 20))ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · by_cases h2 : c ∈ agentEv D (SXM24 n)
        · exact Or.inr fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl ⟨hc.1, h1⟩)
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have c1 := SX20_ret_charge (by omega) fT wT hf hw
    have c2 := SXM24_ret_charge hn fT wT hf hw
    have c3 := (measureReal_union_le (μ := retDist (paperCentres n)) (S ∩ EAᶜ)
      (agentEv D (SXM24 n))ᶜ)
    linarith
  have hroom' : δA + 5 / 100000 + 5 / 100000 ≤ roomB := by unfold roomC at hroom; linarith
  refine BstLean.Part180.classifier_paper_free23_cA8EH hHQ (by omega) fT wT hf hw t hEA' hA' hroom'
    (hfl := 112 / 10 ^ 5) (hb := 533 / 10 ^ 5) (by norm_num)
    fun c hc => ?_
  obtain ⟨wl, ws, sd, η, CL, CS, E, h0, h1, hCL, hCS, hsd0, hsd, hE, hE8, hL12, hS12, hwl, hws, hε,
    hroot, hbias⟩ := hM c hc
  have hσl : 0 < √(2 / (n : ℝ)) * sd := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  exact ⟨wl, ws, √(2 / (n : ℝ)) * sd, η, CL, CS, betaMW24 n sd, E, 85 / 100, 64 / 100, h0, h1, hCL, hCS,
    betaMW24_nonneg n sd, hE, hL12, hS12, hE8, mass_of_goodCW24 hn fT wT hf hw hc hsd0.le hsd, hwl, hws, hσl, hε,
    by norm_num, by norm_num, by norm_num, by norm_num, hroot, hbias⟩


end SMass

section SRoot
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part148 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper cLS kLSs gmom gmom_even LatMom)
open BstLean.Part162 (tK tK_nonneg priceC Bpap Dpap cVw cEw iotaP c2η c3η)
open BstLean.Part164 (goodA hE8_of_good CAn E0 E0_nonneg CAn_le E0_le)

section core2

variable {g s : ℝ}

/-! The pieces of the root sum at `η = 1/50` and `s ≥ 0.452` (Part 165's `rc_*` use `η = 10⁻⁴`
and the cruder `s ≥ 0.43`). -/

lemma rcQ_rho (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 24000) (hs : 452 / 1000 ≤ s) :
    35 / 2 * (g ^ 2 * g) / (g * s) = 35 / 2 / s * g ^ 2 ∧ 0 ≤ 35 / 2 / s * g ^ 2 ∧
    35 / 2 / s * g ^ 2 ≤ 38717 / 1000 * (2 / 24000) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  refine ⟨by field_simp, by positivity, ?_⟩
  have : 35 / 2 / s ≤ 38717 / 1000 := by
    rw [div_le_iff₀ hs0]; nlinarith
  calc 35 / 2 / s * g ^ 2 ≤ 38717 / 1000 * g ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg g)
    _ ≤ 38717 / 1000 * (2 / 24000) := by gcongr

lemma rcQ_iota8 : 0 ≤ iotaP (1 / 50) 8 ∧ iotaP (1 / 50) 8 ≤ 10026 / 10000 := by
  refine ⟨(BstLean.Part162.iotaP_pos (by norm_num) 8).le, ?_⟩
  by_contra h
  have h1 := pow_lt_pow_left₀ (not_le.mp h) (by norm_num) (by norm_num : (8 : ℕ) ≠ 0)
  rw [BstLean.Part162.iotaP_pow (by norm_num) (by norm_num)] at h1
  norm_num at h1

lemma rcQ_iota12 : 0 ≤ iotaP (1 / 50) 12 ∧ iotaP (1 / 50) 12 ≤ 10017 / 10000 := by
  refine ⟨(BstLean.Part162.iotaP_pos (by norm_num) 12).le, ?_⟩
  by_contra h
  have h1 := pow_lt_pow_left₀ (not_le.mp h) (by norm_num) (by norm_num : (12 : ℕ) ≠ 0)
  rw [BstLean.Part162.iotaP_pow (by norm_num) (by norm_num)] at h1
  norm_num at h1

lemma rcQ_c2 : 0 ≤ c2η (1 / 50) ∧ c2η (1 / 50) ≤ 142858 / 1000000 := by
  refine ⟨by unfold c2η; positivity, ?_⟩
  unfold c2η; exact sqrt_le_of_sq (by norm_num) (by norm_num)

lemma rcQ_sη : (98994 / 100000 : ℝ) ≤ √(1 - 1 / 50) := by
  rw [show (98994 / 100000 : ℝ) = √((98994 / 100000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma rcQ_c3 (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 24000) (hs : 452 / 1000 ≤ s) :
    0 ≤ c3η (1 / 50) (35 / 2 * (g ^ 2 * g)) (g * s) ∧
    c3η (1 / 50) (35 / 2 * (g ^ 2 * g)) (g * s) ≤ 16300 / 10000000 := by
  have hsη := rcQ_sη
  have hsη0 : 0 < √(1 - 1 / 50 : ℝ) := lt_of_lt_of_le (by norm_num) hsη
  obtain ⟨hρ, hρ0, hρ1⟩ := rcQ_rho hg hg0 hs
  have hc3e : c3η (1 / 50) (35 / 2 * (g ^ 2 * g)) (g * s) =
      35 / 2 / s * g ^ 2 / (2 * √(1 - 1 / 50)) := by
    unfold c3η; rw [← hρ]; field_simp
  rw [hc3e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  calc 35 / 2 / s * g ^ 2 ≤ 38717 / 1000 * (2 / 24000) := hρ1
    _ ≤ 16300 / 10000000 * (2 * (98994 / 100000)) := by norm_num
    _ ≤ 16300 / 10000000 * (2 * √(1 - 1 / 50)) := by gcongr

lemma rcQ_A {Vs : ℝ} (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 24000) (hs : 452 / 1000 ≤ s)
    (h0Vs : 0 ≤ Vs) (hVs : Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3) :
    0 ≤ cVw (35 / 2 * (g ^ 2 * g)) (g * s) * ((1 - 1 / 50)⁻¹ * Vs) ∧
    cVw (35 / 2 * (g ^ 2 * g)) (g * s) * ((1 - 1 / 50)⁻¹ * Vs) ≤
      1639 / 100 * (g ^ 2) ^ 2 := by
  obtain ⟨hρ, hρ0, hρ1⟩ := rcQ_rho hg hg0 hs
  have hAe : cVw (35 / 2 * (g ^ 2 * g)) (g * s) * ((1 - 1 / 50)⁻¹ * Vs) =
      4 * (1 + 35 / 2 / s * g ^ 2) ^ 2 / (g * s) ^ 2 * (50 / 49 * Vs) := by
    unfold cVw; rw [hρ]; norm_num
  rw [hAe]
  refine ⟨by positivity, ?_⟩
  set x := 35 / 2 / s * g ^ 2 with hxdef
  calc 4 * (1 + x) ^ 2 / (g * s) ^ 2 * (50 / 49 * Vs)
      ≤ 4 * (1 + 38717 / 1000 * (2 / 24000)) ^ 2 / (g * (452 / 1000)) ^ 2 *
        (50 / 49 * (81508 / 100000 * (g ^ 2) ^ 3)) := by
        gcongr
    _ = 4 * (1 + 38717 / 1000 * (2 / 24000)) ^ 2 / (452 / 1000) ^ 2 * (50 / 49) *
        (81508 / 100000) * (g ^ 2) ^ 2 := by field_simp
    _ ≤ 1639 / 100 * (g ^ 2) ^ 2 := by gcongr; norm_num

lemma rcQ_D {CA Vl : ℝ} (hg : 0 < g) (hs : 452 / 1000 ≤ s) (h0CA : 0 ≤ CA)
    (hCA : CA ≤ 1532 / 1000) (h0Vl : 0 ≤ Vl) (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2) :
    0 ≤ CA / (g * s) ^ 2 * ((1 - 1 / 50)⁻¹ * Vl) ∧
    CA / (g * s) ^ 2 * ((1 - 1 / 50)⁻¹ * Vl) ≤ 9757 / 1000 * g ^ 2 := by
  have hηi : (1 - 1 / 50 : ℝ)⁻¹ = 50 / 49 := by norm_num
  rw [hηi]
  refine ⟨by positivity, ?_⟩
  calc CA / (g * s) ^ 2 * (50 / 49 * Vl)
      ≤ 1532 / 1000 / (g * (452 / 1000)) ^ 2 * (50 / 49 * (127512 / 100000 * (g ^ 2) ^ 2)) := by
        gcongr
    _ = 1532 / 1000 / (452 / 1000) ^ 2 * (50 / 49) * (127512 / 100000) * g ^ 2 := by
        field_simp
    _ ≤ 9757 / 1000 * g ^ 2 := by gcongr; norm_num

lemma rcQ_e {p : ℕ} {t K ι₀ : ℝ} (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 24000) (hs : 452 / 1000 ≤ s)
    (hι : 0 ≤ iotaP (1 / 50) p ∧ iotaP (1 / 50) p ≤ ι₀) (ht : 0 ≤ t) (hK : t ≤ K * (g ^ 2 * g)) :
    0 ≤ cEw (35 / 2 * (g ^ 2 * g)) (g * s) *
        ((iotaP (1 / 50) p + c2η (1 / 50) + c3η (1 / 50) (35 / 2 * (g ^ 2 * g))
          (g * s)) * t) ∧
    cEw (35 / 2 * (g ^ 2 * g)) (g * s) *
        ((iotaP (1 / 50) p + c2η (1 / 50) + c3η (1 / 50) (35 / 2 * (g ^ 2 * g))
          (g * s)) * t) ≤
      2 * (1000 / 452 + 35 / 2 / (452 / 1000) ^ 2 * (2 / 24000)) *
        ((ι₀ + 142858 / 1000000 + 16300 / 10000000) * K) * g ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hK0 : 0 ≤ K := by
    by_contra hc
    have : K * (g ^ 2 * g) < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) (by positivity)
    linarith
  obtain ⟨hι0, hι1⟩ := hι
  obtain ⟨hc20, hc21⟩ := rcQ_c2
  obtain ⟨hc30, hc31⟩ := rcQ_c3 hg hg0 hs
  have hcEw : cEw (35 / 2 * (g ^ 2 * g)) (g * s) = 2 * (1 / s + 35 / 2 / s ^ 2 * g ^ 2) / g := by
    unfold cEw; field_simp
  have hq : 2 * (1 / s + 35 / 2 / s ^ 2 * g ^ 2) ≤
      2 * (1000 / 452 + 35 / 2 / (452 / 1000) ^ 2 * (2 / 24000)) := by
    have h1 : 1 / s ≤ 1000 / 452 := by rw [div_le_iff₀ hs0]; nlinarith
    have h2 : 35 / 2 / s ^ 2 ≤ 35 / 2 / (452 / 1000) ^ 2 := by gcongr
    have h3 : 35 / 2 / s ^ 2 * g ^ 2 ≤ 35 / 2 / (452 / 1000) ^ 2 * (2 / 24000) := by gcongr
    linarith
  rw [hcEw]
  refine ⟨by positivity, ?_⟩
  calc 2 * (1 / s + 35 / 2 / s ^ 2 * g ^ 2) / g *
        ((iotaP (1 / 50) p + c2η (1 / 50) + c3η (1 / 50) (35 / 2 * (g ^ 2 * g))
          (g * s)) * t)
      ≤ 2 * (1000 / 452 + 35 / 2 / (452 / 1000) ^ 2 * (2 / 24000)) / g *
        ((ι₀ + 142858 / 1000000 + 16300 / 10000000) * (K * (g ^ 2 * g))) := by
        gcongr <;> linarith [hι0.trans hι1]
    _ = _ := by field_simp

lemma rcQ_d {p : ℕ} {CA t K ι₀ : ℝ} (hg : 0 < g) (hs : 452 / 1000 ≤ s) (h0CA : 0 ≤ CA)
    (hCA : CA ≤ 1532 / 1000) (hι : 0 ≤ iotaP (1 / 50) p ∧ iotaP (1 / 50) p ≤ ι₀) (ht : 0 ≤ t)
    (hK : t ≤ K * g ^ 2) :
    0 ≤ √CA / (g * s) * ((iotaP (1 / 50) p + c2η (1 / 50)) * t) ∧
    √CA / (g * s) * ((iotaP (1 / 50) p + c2η (1 / 50)) * t) ≤
      12378 / 10000 / (452 / 1000) * ((ι₀ + 142858 / 1000000) * K) * g := by
  have hK0 : 0 ≤ K := by
    by_contra hc
    have : K * g ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) (by positivity)
    linarith
  obtain ⟨hι0, hι1⟩ := hι
  obtain ⟨hc20, hc21⟩ := rcQ_c2
  have hsCA : √CA ≤ 12378 / 10000 :=
    (Real.sqrt_le_sqrt hCA).trans (sqrt_le_of_sq (by norm_num) (by norm_num))
  refine ⟨by positivity, ?_⟩
  calc √CA / (g * s) * ((iotaP (1 / 50) p + c2η (1 / 50)) * t)
      ≤ 12378 / 10000 / (g * (452 / 1000)) * ((ι₀ + 142858 / 1000000) * (K * g ^ 2)) := by
        gcongr <;> linarith [hι0.trans hι1]
    _ = 12378 / 10000 / (452 / 1000) * ((ι₀ + 142858 / 1000000) * K) * g := by
        field_simp

lemma sqrt_le_sq' {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hy))

/-- **The cubic price at `g² = 2/n`** with `λ = 0.85`, `λ' = 0.64`: `cubP ≤ 240 000·g⁶`. -/
lemma cubP_le {n g ε A D e6 d6 : ℝ} (hg : 0 < g) (hnu : n * g ^ 2 = 2) (h0ε : 0 ≤ ε)
    (hε : ε ≤ 1421 / 100000) (h0A : 0 ≤ A) (hA : A ≤ 1639 / 100 * (g ^ 2) ^ 2) (h0D : 0 ≤ D)
    (hD : D ≤ 9757 / 1000 * g ^ 2) (h0e6 : 0 ≤ e6) (he6 : e6 ≤ 1561 / 100 * g ^ 2) (h0d6 : 0 ≤ d6)
    (hd6 : d6 ≤ 1203 / 100 * g) :
    BstLean.Part180.cubP n ε (85 / 100) (64 / 100) A D e6 d6 ≤ 240000 * (g ^ 2) ^ 3 := by
  set u := g ^ 2 with hud
  have hu : 0 < u := by positivity
  have h1ε : 0 < 1 - ε := by linarith
  have hk0 : 0 ≤ (1 + 3 * ε) / (4 * (1 - ε)) := by positivity
  have hk : (1 + 3 * ε) / (4 * (1 - ε)) ≤ 26442 / 100000 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hc0 : 0 ≤ 1 / (2 * (1 - ε)) := by positivity
  have hc : 1 / (2 * (1 - ε)) ≤ 507208 / 1000000 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsA : √A ≤ 40485 / 10000 * u :=
    sqrt_le_sq' (by positivity) (by nlinarith)
  have hsD : √D ≤ 31237 / 10000 * g := by
    apply sqrt_le_sq' (by positivity)
    rw [mul_pow, ← hud]; nlinarith
  have hε2 : (1 - 1421 / 100000 : ℝ) ^ 2 ≤ (1 - ε) ^ 2 := by
    apply pow_le_pow_left₀ (by norm_num); linarith
  have hn0 : 0 ≤ n := by
    by_contra h; have := not_le.mp h; nlinarith
  unfold BstLean.Part180.cubP
  have e1 : (n * ((1 + 3 * ε) / (4 * (1 - ε)))) ^ 3 * (A * √A * e6 ^ 3) / (64 / 100) ^ 2 ≤
      (n * (26442 / 100000)) ^ 3 * ((1639 / 100 * u ^ 2) * (40485 / 10000 * u) *
        (1561 / 100 * u) ^ 3) / (64 / 100) ^ 2 := by
    gcongr
  have e1' : (n * (26442 / 100000)) ^ 3 * ((1639 / 100 * u ^ 2) * (40485 / 10000 * u) *
        (1561 / 100 * u) ^ 3) / (64 / 100) ^ 2 =
      (26442 / 100000) ^ 3 * (1639 / 100 * (40485 / 10000) * (1561 / 100) ^ 3) / (64 / 100) ^ 2 *
        (n * u) ^ 3 * u ^ 3 := by ring
  have e2 : (1 / (2 * (1 - ε))) ^ 3 * (D * √D * d6 ^ 3) / (1 - 64 / 100) ^ 2 ≤
      (507208 / 1000000) ^ 3 * ((9757 / 1000 * u) * (31237 / 10000 * g) *
        (1203 / 100 * g) ^ 3) / (1 - 64 / 100) ^ 2 := by
    gcongr
  have e2' : (507208 / 1000000) ^ 3 * ((9757 / 1000 * u) * (31237 / 10000 * g) *
        (1203 / 100 * g) ^ 3) / (1 - 64 / 100 : ℝ) ^ 2 =
      (507208 / 1000000) ^ 3 * (9757 / 1000 * (31237 / 10000) * (1203 / 100) ^ 3) /
        (1 - 64 / 100) ^ 2 * u ^ 3 := by rw [hud]; ring
  have e3 : (n * A ^ 2 + 2 * A * D) / ((1 - ε) ^ 2 * (1 - 85 / 100) ^ 2) ≤
      (n * (1639 / 100 * u ^ 2) ^ 2 + 2 * (1639 / 100 * u ^ 2) * (9757 / 1000 * u)) /
        ((1 - 1421 / 100000) ^ 2 * (1 - 85 / 100) ^ 2) := by
    gcongr
  have e3' : (n * (1639 / 100 * u ^ 2) ^ 2 + 2 * (1639 / 100 * u ^ 2) * (9757 / 1000 * u)) /
        ((1 - 1421 / 100000 : ℝ) ^ 2 * (1 - 85 / 100) ^ 2) =
      ((1639 / 100) ^ 2 * (n * u) + 2 * (1639 / 100) * (9757 / 1000)) /
        ((1 - 1421 / 100000) ^ 2 * (1 - 85 / 100) ^ 2) * u ^ 3 := by ring
  rw [e1', hnu] at e1
  rw [e2'] at e2
  rw [e3', hnu] at e3
  have hu3 : 0 < u ^ 3 := by positivity
  calc _ ≤ ((26442 / 100000) ^ 3 * (1639 / 100 * (40485 / 10000) * (1561 / 100) ^ 3) /
          (64 / 100) ^ 2 * 2 ^ 3 * u ^ 3 + (507208 / 1000000) ^ 3 * (9757 / 1000 * (31237 / 10000) *
          (1203 / 100) ^ 3) / (1 - 64 / 100) ^ 2 * u ^ 3) / (85 / 100) ^ 2 +
        ((1639 / 100) ^ 2 * 2 + 2 * (1639 / 100) * (9757 / 1000)) /
          ((1 - 1421 / 100000) ^ 2 * (1 - 85 / 100) ^ 2) * u ^ 3 := by
        gcongr
    _ = (((26442 / 100000) ^ 3 * (1639 / 100 * (40485 / 10000) * (1561 / 100) ^ 3) /
          (64 / 100) ^ 2 * 2 ^ 3 + (507208 / 1000000) ^ 3 * (9757 / 1000 * (31237 / 10000) *
          (1203 / 100) ^ 3) / (1 - 64 / 100) ^ 2) / (85 / 100) ^ 2 +
        ((1639 / 100) ^ 2 * 2 + 2 * (1639 / 100) * (9757 / 1000)) /
          ((1 - 1421 / 100000) ^ 2 * (1 - 85 / 100) ^ 2)) * u ^ 3 := by ring
    _ ≤ 240000 * u ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ hu3.le
        norm_num


lemma rc_price24 {n : ℕ} {κ L ε E A D e4 d4 e6 d6 : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 24000) (h0κ : 0 ≤ κ) (h0L : 0 ≤ L) (h0ε : 0 ≤ ε) (h0E : 0 ≤ E)
    (h0A : 0 ≤ A) (h0D : 0 ≤ D) (h0e4 : 0 ≤ e4) (h0d4 : 0 ≤ d4) (h0e6 : 0 ≤ e6) (h0d6 : 0 ≤ d6)
    (hκ : κ ≤ 1000203 / 1000000) (hL : L ≤ 12666 / 100 * g) (hε : ε ≤ 1421 / 100000)
    (hE : E ≤ 55) (hA : A ≤ 1639 / 100 * (g ^ 2) ^ 2) (hD : D ≤ 9757 / 1000 * g ^ 2)
    (he4 : e4 ≤ 1293 / 100 * g ^ 2) (hd4 : d4 ≤ 996 / 100 * g) (he6 : e6 ≤ 1561 / 100 * g ^ 2)
    (hd6 : d6 ≤ 1203 / 100 * g) :
    √(priceC κ n L ε E A D e4 d4 e6 d6 / 4 +
      3 / 4 * BstLean.Part180.cubP n ε (85 / 100) (64 / 100) A D e6 d6) ≤ 869 / 10 ^ 6 := by
  have hC := cubP_le (n := (n : ℝ)) hg hgn h0ε hε h0A hA h0D hD h0e6 he6 h0d6 hd6
  have h1 := priceC_mono h0κ (Nat.cast_nonneg n) h0L h0ε h0E h0A h0D h0e4 h0d4 h0e6 h0d6 hκ hL hε
    hE hA hD he4 hd4 he6 hd6
  rw [priceC_scale hg hgn (by norm_num) (by norm_num)] at h1
  have hs : √((1639 / 100 : ℝ) * (9757 / 1000)) ≤ 1265 / 100 :=
    sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs0 : 0 ≤ √((1639 / 100 : ℝ) * (9757 / 1000)) := Real.sqrt_nonneg _
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  have hg0' : g ^ 2 ≤ 2 / 24000 := hg0
  have hF : (1000203 / 1000000 : ℝ) * g ^ 2 * ((1639 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
        (1639 / 100) * (9757 / 1000)) +
      (1000203 / 1000000 * (1639 / 100 + 9757 / 1000 + 12666 / 100 *
        √((1639 / 100 : ℝ) * (9757 / 1000)) * g ^ 2)) ^ 2 / 2 +
      g ^ 2 * (1000203 / 1000000 * (1639 / 100 + 9757 / 1000 + 12666 / 100 *
        √((1639 / 100 : ℝ) * (9757 / 1000)) * g ^ 2)) *
        (1000203 / 1000000 * ((1293 / 100) ^ 2 + (996 / 100) ^ 2 + 12666 / 100 * (996 / 100) *
          (1293 / 100) * g ^ 2)) ^ 2 / 6 +
      (g ^ 2) ^ 2 * (1000203 / 1000000 * ((1293 / 100) ^ 2 + (996 / 100) ^ 2 + 12666 / 100 *
        (996 / 100) * (1293 / 100) * g ^ 2)) ^ 4 / 24 +
      (g ^ 2) ^ 3 * (1000203 / 1000000 * ((1293 / 100) ^ 2 + (996 / 100) ^ 2 + 12666 / 100 *
        (996 / 100) * (1293 / 100) * g ^ 2)) ^ 2 *
        (1000203 / 1000000 * ((1561 / 100) ^ 2 + (1203 / 100) ^ 2 + 12666 / 100 * (1203 / 100) *
          (1561 / 100) * g ^ 2)) ^ 3 / 120 +
      55 * (g ^ 2) ^ 4 * (1000203 / 1000000 * ((1561 / 100) ^ 2 + (1203 / 100) ^ 2 +
        12666 / 100 * (1203 / 100) * (1561 / 100) * g ^ 2)) ^ 6 / 720 ≤ 374 := by
    calc _ ≤ (1000203 / 1000000 : ℝ) * (2 / 24000) * ((1639 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
            (1639 / 100) * (9757 / 1000)) +
          (1000203 / 1000000 * (1639 / 100 + 9757 / 1000 + 12666 / 100 * (1265 / 100) *
            (2 / 24000))) ^ 2 / 2 +
          (2 / 24000) * (1000203 / 1000000 * (1639 / 100 + 9757 / 1000 + 12666 / 100 *
            (1265 / 100) * (2 / 24000))) *
            (1000203 / 1000000 * ((1293 / 100) ^ 2 + (996 / 100) ^ 2 + 12666 / 100 * (996 / 100) *
              (1293 / 100) * (2 / 24000))) ^ 2 / 6 +
          (2 / 24000) ^ 2 * (1000203 / 1000000 * ((1293 / 100) ^ 2 + (996 / 100) ^ 2 +
            12666 / 100 * (996 / 100) * (1293 / 100) * (2 / 24000))) ^ 4 / 24 +
          (2 / 24000) ^ 3 * (1000203 / 1000000 * ((1293 / 100) ^ 2 + (996 / 100) ^ 2 +
            12666 / 100 * (996 / 100) * (1293 / 100) * (2 / 24000))) ^ 2 *
            (1000203 / 1000000 * ((1561 / 100) ^ 2 + (1203 / 100) ^ 2 + 12666 / 100 *
              (1203 / 100) * (1561 / 100) * (2 / 24000))) ^ 3 / 120 +
          55 * (2 / 24000) ^ 4 * (1000203 / 1000000 * ((1561 / 100) ^ 2 + (1203 / 100) ^ 2 +
            12666 / 100 * (1203 / 100) * (1561 / 100) * (2 / 24000))) ^ 6 / 720 := by
          gcongr
      _ ≤ 374 := by norm_num
  have h2 : priceC κ n L ε E A D e4 d4 e6 d6 ≤ (g ^ 2) ^ 2 * 374 :=
    h1.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  have h3 : priceC κ n L ε E A D e4 d4 e6 d6 / 4 +
      3 / 4 * BstLean.Part180.cubP n ε (85 / 100) (64 / 100) A D e6 d6 ≤ (g ^ 2) ^ 2 * (1085 / 10) := by
    have : (g ^ 2) ^ 2 * 374 / 4 + 3 / 4 * (240000 * (g ^ 2) ^ 3) ≤ (g ^ 2) ^ 2 * (1085 / 10) := by
      have : 3 / 4 * (240000 * (g ^ 2) ^ 3) ≤ (g ^ 2) ^ 2 * 15 := by
        have h4 : 0 ≤ (g ^ 2) ^ 2 := by positivity
        have : (g ^ 2) ^ 3 = (g ^ 2) ^ 2 * g ^ 2 := by ring
        rw [this]; nlinarith
      nlinarith
    linarith
  calc _ ≤ √((g ^ 2) ^ 2 * (1085 / 10)) := Real.sqrt_le_sqrt h3
    _ = g ^ 2 * √(1085 / 10) := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
    _ ≤ (2 / 24000) * (104164 / 10000) := by
        gcongr
        exact sqrt_le_of_sq (by norm_num) (by norm_num)
    _ ≤ 869 / 10 ^ 6 := by norm_num

lemma rc_B24 {tlq tsq βl : ℝ} (hg : 0 < g) (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g)) (h0β : 0 ≤ βl)
    (hβ : βl ≤ 94 / 10 ^ 13) :
    0 ≤ Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ∧
    Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ≤ 9405 / 10 ^ 15 := by
  unfold Bpap
  have hu : 0 < g ^ 2 := by positivity
  have h1 : tlq / (22 * g ^ 2) ≤ 53493 / 10000 / 22 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : tsq / (35 / 2 * (g ^ 2 * g)) ≤ 42768 / 10000 / (35 / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_pos hu hg]
  have h10 : 0 ≤ tlq / (22 * g ^ 2) := by positivity
  have h20 : 0 ≤ tsq / (35 / 2 * (g ^ 2 * g)) := by positivity
  refine ⟨by positivity, ?_⟩
  calc (tlq / (22 * g ^ 2)) ^ (2 * 12) + (tsq / (35 / 2 * (g ^ 2 * g))) ^ (2 * 12) + βl
      ≤ (53493 / 10000 / 22) ^ (2 * 12) + (42768 / 10000 / (35 / 2)) ^ (2 * 12) + 94 / 10 ^ 13 := by
        gcongr
    _ ≤ 9405 / 10 ^ 15 := by norm_num

lemma rc_R1_24 {B : ℝ} (h0B : 0 ≤ B) (hB : B ≤ 9405 / 10 ^ 15) :
    √(2 * (1 + (1 / 50 : ℝ)⁻¹) * B) ≤ 31 / 10 ^ 6 := by
  apply sqrt_le_of_sq (by norm_num)
  calc 2 * (1 + (1 / 50 : ℝ)⁻¹) * B ≤ 2 * (1 + (1 / 50 : ℝ)⁻¹) * (9405 / 10 ^ 15) := by gcongr
    _ ≤ (31 / 10 ^ 6) ^ 2 := by norm_num

lemma rc_Dp24 {n : ℕ} {B CA Vl VS : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 24000) (hs : 452 / 1000 ≤ s) (h0B : 0 ≤ B) (hB : B ≤ 9405 / 10 ^ 15)
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000) (h0Vl : 0 ≤ Vl)
    (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 2603 / 100 * (g ^ 2) ^ 4) :
    √(Dpap n B CA Vl VS (1 / 50) (g * s)) ≤ 207 / 10 ^ 6 := by
  unfold Dpap
  have hn' : (n : ℝ) = 2 / g ^ 2 := by field_simp; linarith
  have hsB : √B ≤ 30668 / 10 ^ 10 := (Real.sqrt_le_sqrt hB).trans
    (sqrt_le_of_sq (by norm_num) (by norm_num))
  have hsB0 : 0 ≤ √B := Real.sqrt_nonneg _
  have hu : 0 < g ^ 2 := by positivity
  have hT1 : CA * Vl / (2 * (1 - 1 / 50) * (g * s) ^ 2) ≤
      1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 50) * (452 / 1000) ^ 2) * g ^ 2 := by
    calc CA * Vl / (2 * (1 - 1 / 50) * (g * s) ^ 2)
        ≤ 1532 / 1000 * (127512 / 100000 * (g ^ 2) ^ 2) /
          (2 * (1 - 1 / 50) * (g * (452 / 1000)) ^ 2) := by gcongr
      _ = _ := by field_simp
  have hT2 : (n : ℝ) * VS / (8 * (1 - 1 / 50) ^ 2 * (g * s) ^ 4) ≤
      2 * (2603 / 100) / (8 * (1 - 1 / 50) ^ 2 * (452 / 1000) ^ 4) * g ^ 2 := by
    rw [hn']
    calc 2 / g ^ 2 * VS / (8 * (1 - 1 / 50) ^ 2 * (g * s) ^ 4)
        ≤ 2 / g ^ 2 * (2603 / 100 * (g ^ 2) ^ 4) /
          (8 * (1 - 1 / 50) ^ 2 * (g * (452 / 1000)) ^ 4) := by gcongr
      _ = _ := by field_simp
  have hsum : CA * Vl / (2 * (1 - 1 / 50) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 50) ^ 2 * (g * s) ^ 4) ≤ 1673 / 10 * g ^ 2 := by
    have e : 1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 50) * (452 / 1000) ^ 2) +
        2 * (2603 / 100) / (8 * (1 - 1 / 50) ^ 2 * (452 / 1000) ^ 4) ≤ (1673 / 10 : ℝ) := by
      norm_num
    nlinarith
  have hS0 : 0 ≤ CA * Vl / (2 * (1 - 1 / 50) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 50) ^ 2 * (g * s) ^ 4) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    positivity
  apply sqrt_le_of_sq (by norm_num)
  calc √B * (CA * Vl / (2 * (1 - 1 / 50) * (g * s) ^ 2) +
        (n : ℝ) * VS / (8 * (1 - 1 / 50) ^ 2 * (g * s) ^ 4))
      ≤ 30668 / 10 ^ 10 * (1673 / 10 * (2 / 24000)) := by
        gcongr
        exact hsum.trans (by gcongr)
    _ ≤ (207 / 10 ^ 6) ^ 2 := by norm_num

theorem root_core24 {n : ℕ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2) (hg0 : g ^ 2 ≤ 2 / 24000)
    (hs : 43 / 100 ≤ s) (hs' : 452 / 1000 ≤ s) {CA Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl : ℝ}
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000)
    (h0Vs : 0 ≤ Vs) (hVs : Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3)
    (h0Vl : 0 ≤ Vl) (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 2603 / 100 * (g ^ 2) ^ 4)
    (h0ts8 : 0 ≤ ts8) (hts8 : ts8 ≤ 25379 / 10000 * (g ^ 2 * g))
    (h0tl8 : 0 ≤ tl8) (htl8 : tl8 ≤ 31743 / 10000 * g ^ 2)
    (h0ts12 : 0 ≤ ts12) (hts12 : ts12 ≤ 30661 / 10000 * (g ^ 2 * g))
    (h0tl12 : 0 ≤ tl12) (htl12 : tl12 ≤ 38350 / 10000 * g ^ 2)
    (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g))
    (h0β : 0 ≤ βl) (hβ : βl ≤ 94 / 10 ^ 13) :
    BstLean.Part180.rootEH n (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) (1 / 50) CA (g * s)
      Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl (85 / 100) (64 / 100) ≤ 112 / 10 ^ 5 := by
  have hg0' : g ^ 2 ≤ 2 / 23000 := hg0.trans (by norm_num)
  obtain ⟨-, hε0, hε1⟩ := rc_eps hg hg0' hs
  obtain ⟨hκd, hκ1⟩ := rc_kappa hε0 hε1
  have hκ0 := (inv_pos.2 hκd).le
  obtain ⟨hL0, hL1⟩ := rc_L hg hs h0CA hCA
  have hnε := rc_neps (n := n) hg hgn hg0' hs
  have hEE := rc_EE hg hg0' hκ0 hκ1 hε0 hε1 hnε hL0 hL1
  obtain ⟨hA0, hA⟩ := rcQ_A hg hg0 hs' h0Vs hVs
  obtain ⟨hD0, hD⟩ := rcQ_D hg hs' h0CA hCA h0Vl hVl
  obtain ⟨he40, he4⟩ := rcQ_e hg hg0 hs' rcQ_iota8 h0ts8 hts8
  obtain ⟨he60, he6⟩ := rcQ_e hg hg0 hs' rcQ_iota12 h0ts12 hts12
  obtain ⟨hd40, hd4⟩ := rcQ_d hg hs' h0CA hCA rcQ_iota8 h0tl8 htl8
  obtain ⟨hd60, hd6⟩ := rcQ_d hg hs' h0CA hCA rcQ_iota12 h0tl12 htl12
  have hP := rc_price24 (n := n) hg hgn hg0 hκ0 hL0 hε0 (exp_pos _).le hA0 hD0 he40 hd40 he60 hd60
    hκ1 hL1 hε1 hEE hA hD (he4.trans (by gcongr; norm_num)) (hd4.trans (by gcongr; norm_num))
    (he6.trans (by gcongr; norm_num)) (hd6.trans (by gcongr; norm_num))
  obtain ⟨hB0, hB⟩ := rc_B24 hg h0tlq htlq h0tsq htsq h0β hβ
  have hR1 := rc_R1_24 hB0 hB
  have hR3 := rc_Dp24 (n := n) hg hgn hg0 hs' hB0 hB h0CA hCA h0Vl hVl h0VS hVS
  unfold BstLean.Part180.rootEH
  linarith

end core2

variable {n : ℕ}

lemma VS_bound {k E g : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 25379 / 10000 * (g ^ 2 * g)) (hE0 : 0 ≤ E)
    (hE : E ≤ 1005 / 1000 * g) : 4 * k ^ 2 * E ^ 2 ≤ 2603 / 100 * (g ^ 2) ^ 4 := by
  have h1 : k ^ 2 ≤ (25379 / 10000 * (g ^ 2 * g)) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have h2 : E ^ 2 ≤ (1005 / 1000 * g) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have h3 : 4 * k ^ 2 * E ^ 2 ≤ 4 * (25379 / 10000 * (g ^ 2 * g)) ^ 2 * (1005 / 1000 * g) ^ 2 := by
    have := mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have e : 4 * (25379 / 10000 * (g ^ 2 * g)) ^ 2 * (1005 / 1000 * g) ^ 2 =
      (4 * (25379 / 10000) ^ 2 * (1005 / 1000) ^ 2) * (g ^ 2) ^ 4 := by ring
  have hk' : (4 : ℝ) * (25379 / 10000) ^ 2 * (1005 / 1000) ^ 2 ≤ 2603 / 100 := by norm_num
  rw [e] at h3
  exact h3.trans (mul_le_mul_of_nonneg_right hk' (by positivity))

theorem rootFL_fixed24 (hn : 24000 ≤ n) {sd : ℝ} (hsd' : 452 / 1000 ≤ sd) {E : ℝ} (hE0 : 0 ≤ E)
    (hEle : E ≤ 1005 / 1000 * √(2 / (n : ℝ)))
    (hβ : betaMW24 n sd ≤ 94 / 10 ^ 13) (D : Design n) (c : Ret n)
    (hCL : (0 : ℝ) < 51 / 10) (hCS : (0 : ℝ) < 326 / 100 * (2 / n))
    (hL12 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12)
    (hS12 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12)
    (hE8 : ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E ^ 8)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < √(2 / (n : ℝ)) * sd}
      ∂muI n ≤ betaMW24 n sd) :
    BstLean.Part180.rootFLH (22 * √(2 / (n : ℝ)) ^ 2) (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (1 / 50)
      (CAn n) (85 / 100) (64 / 100) (latMomOfPsi12e (by omega) D c hCL hCS hE0 (betaMW24_nonneg n sd)
        hL12 hS12 hE8 hmass) ≤ 112 / 10 ^ 5 := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set g := √(2 / (n : ℝ)) with hgdef
  have hg2 : g ^ 2 = 2 / n := Real.sq_sqrt (by positivity)
  have hg : 0 < g := Real.sqrt_pos.mpr (by positivity)
  have hgn : (n : ℝ) * g ^ 2 = 2 := by rw [hg2]; field_simp
  have hg0 : g ^ 2 ≤ 2 / 24000 := by
    rw [hg2]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  set P := latMomOfPsi12e (by omega) D c hCL hCS hE0 (betaMW24_nonneg n sd)
    hL12 hS12 hE8 hmass with hP
  -- the two square roots
  have hCSn : √(326 / 100 * (2 / (n : ℝ)) / n) = √(163 / 100) * g ^ 2 := by
    rw [hg2, show 326 / 100 * (2 / (n : ℝ)) / n = 163 / 100 * (2 / n) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hCLn : √(51 / 10 / (n : ℝ)) = √(255 / 100) * g := by
    rw [hgdef, ← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hs1 : √(163 / 100 : ℝ) ≤ 1276715 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs2 : √(255 / 100 : ℝ) ≤ 1596872 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs10 : 0 ≤ √(163 / 100 : ℝ) := Real.sqrt_nonneg _
  have hs20 : 0 ≤ √(255 / 100 : ℝ) := Real.sqrt_nonneg _
  -- the factors `kLSs`
  have hk4 : kLSs n 4 ≤ 198779 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS4_le (by norm_num) (by norm_num)
  have hk6 : kLSs n 6 ≤ 240152 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS6_le (by norm_num) (by norm_num)
  have hk12 : kLSs n 12 ≤ 334984 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS12_le (by norm_num) (by norm_num)
  have hk40 : 0 ≤ kLSs n 4 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk60 : 0 ≤ kLSs n 6 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk120 : 0 ≤ kLSs n 12 :=
    (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  -- the fields
  have fS : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1276715 / 1000000) ≤ M →
      k * √(326 / 100 * (2 / (n : ℝ)) / n) ≤ M * (g ^ 2 * g) := by
    intro k K hk0 hk M hM
    rw [hCSn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(163 / 100) * g ^ 2) ≤ (K * g) * (1276715 / 1000000 * g ^ 2) := by gcongr
      _ = K * (1276715 / 1000000) * (g ^ 2 * g) := by ring
      _ ≤ M * (g ^ 2 * g) := by gcongr
  have fL : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1596872 / 1000000) ≤ M →
      k * √(51 / 10 / (n : ℝ)) ≤ M * g ^ 2 := by
    intro k K hk0 hk M hM
    rw [hCLn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(255 / 100) * g) ≤ (K * g) * (1596872 / 1000000 * g) := by gcongr
      _ = K * (1596872 / 1000000) * g ^ 2 := by ring
      _ ≤ M * g ^ 2 := by gcongr
  have hts8 : P.ts8 ≤ 25379 / 10000 * (g ^ 2 * g) := fS hk40 hk4 (by norm_num)
  have hts12 : P.ts12 ≤ 30661 / 10000 * (g ^ 2 * g) := fS hk60 hk6 (by norm_num)
  have htsq : P.tsq ≤ 42768 / 10000 * (g ^ 2 * g) := fS hk120 hk12 (by norm_num)
  have htl8 : P.tl8 ≤ 31743 / 10000 * g ^ 2 := fL hk40 hk4 (by norm_num)
  have htl12 : P.tl12 ≤ 38350 / 10000 * g ^ 2 := fL hk60 hk6 (by norm_num)
  have htlq : P.tlq ≤ 53493 / 10000 * g ^ 2 := fL hk120 hk12 (by norm_num)
  have hVs : P.Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3 := by
    change 326 / 100 * (2 / (n : ℝ)) / n / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 81508 / 100000 * (2 / (n : ℝ)) ^ 3 * (n - 2) = 652064 / 100000 * (n - 2) / n ^ 3 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 326 / 100 * (2 / (n : ℝ)) / n * n ^ 3 = 652 / 100 * n := by field_simp; ring
    rw [e2]
    nlinarith
  have hVl : P.Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2 := by
    change 51 / 10 / (n : ℝ) / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 127512 / 100000 * (2 / (n : ℝ)) ^ 2 * (n - 2) = 510048 / 100000 * (n - 2) / n ^ 2 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 51 / 10 / (n : ℝ) * n ^ 2 = 51 / 10 * n := by field_simp
    rw [e2]
    nlinarith
  have hVS : P.VS ≤ 2603 / 100 * (g ^ 2) ^ 4 := by
    change 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E ^ 2 ≤ _
    exact VS_bound (by positivity) (fS hk40 hk4 (M := 25379 / 10000) (by norm_num)) hE0 hEle
  have hβ' : P.βlow ≤ 94 / 10 ^ 13 := hβ
  have hn23 : 23000 ≤ n := le_trans (by norm_num) hn
  have hCA := CAn_le hn23
  have hCA0 : 0 ≤ CAn n := by unfold CAn BstLean.Part164.chiUp; positivity
  have hsd40 : (43 / 100 : ℝ) ≤ sd := le_trans (by norm_num) hsd'
  exact root_core24 hg hgn hg0 hsd40 hsd' hCA0 hCA P.hVs0 hVs P.hVl0 hVl P.hVS0 hVS P.hts8.le hts8 P.htl8.le
    htl8 P.hts12.le hts12 P.htl12.le htl12 P.htlq htlq P.htsq htsq P.hβl hβ'

theorem classifier_paper_root_gen24 (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) {sd : ℝ} (hsd : 452 / 1000 ≤ sd)
    (hsd' : sd < s0W) (hβ : betaMW24 n sd ≤ 94 / 10 ^ 13) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hE8E : ∀ c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM24 n)),
      ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
        (1005 / 1000 * √(2 / (n : ℝ))) ^ 8)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM24 n)),
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * sd)
          (1 / 50) (by norm_num) (by norm_num)) (533 / 10 ^ 5)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsd0 : 0 < sd := lt_of_lt_of_le (by norm_num) hsd
  have hsd40 : (43 / 100 : ℝ) ≤ sd := le_trans (by norm_num) hsd
  have hE0 : (0 : ℝ) ≤ 1005 / 1000 * √(2 / (n : ℝ)) := by positivity
  refine classifier_paper_free23_massW24 hHQ (by omega) fT wT hf hw t hEA hA hroom fun c hc => ?_
  obtain ⟨hL12, hS12, hbias⟩ := hM c hc
  have hCS : (0 : ℝ) < 326 / 100 * (2 / n) := by positivity
  refine ⟨22 * √(2 / (n : ℝ)) ^ 2, 35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ))), sd,
    1 / 50, 51 / 10, 326 / 100 * (2 / n), 1005 / 1000 * √(2 / (n : ℝ)), by norm_num, by norm_num,
    by norm_num, hCS, hsd0, hsd', hE0, hE8E c hc, hL12, hS12, by positivity, by positivity,
    eps0_fixed_lt (by omega) hsd40, ?_, hbias⟩
  exact rootFL_fixed24 hn hsd hE0 le_rfl hβ _ c (by norm_num) hCS hL12 hS12 _ _

theorem betaMP_452_24 (hn : 24000 ≤ n) : betaMW24 n (452 / 1000) ≤ 94 / 10 ^ 13 := by
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold betaMW24 s0W
  rw [gmom_40]
  have h1 : (π / 2) ^ 40 ≤ (15708 / 10000 : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) pi_half_le 40
  have h2 : 5884 / 10000 / ((n : ℝ) * (5088 / 10000 - 452 / 1000) ^ 2) ≤
      5884 / 10000 / ((24000 : ℝ) * (5088 / 10000 - 452 / 1000) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  have h3 := pow_le_pow_left₀ (by positivity) h2 20
  calc (π / 2) ^ 40 * 319830986772877770815625 *
        (5884 / 10000 / ((n : ℝ) * (5088 / 10000 - 452 / 1000) ^ 2)) ^ 20
      ≤ (15708 / 10000 : ℝ) ^ 40 * 319830986772877770815625 *
        (5884 / 10000 / ((24000 : ℝ) * (5088 / 10000 - 452 / 1000) ^ 2)) ^ 20 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) h3 (by positivity)
          (by positivity)
    _ ≤ 94 / 10 ^ 13 := by norm_num

theorem classifier_paper_root24k (hHQ : BstLean.Part180.HQ_stmt) (hn : 24000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hE8E : ∀ c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM24 n)),
      ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
        (1005 / 1000 * √(2 / (n : ℝ))) ^ 8)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM24 n)),
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (533 / 10 ^ 5)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_root_gen24 hHQ hn (by norm_num) (by unfold s0W; norm_num)
    (betaMP_452_24 hn) fT wT hf hw t hEA hA hroom hE8E hM


end SRoot



-- ===== from Part166Th.lean =====
section STh
open BstLean.Part166
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open scoped ENNReal
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part160 (WqN WqN_le exp_neg_13_le integrable_wqq)
open BstLean.Part161 (consV muI consV_map normSq_consV consV_add consV_smul measurable_consV
  stdGauss_normSq_zero)
open BstLean.Part157 (latitude)
/-- `W₁₂₈ ≤ (1.1467·τ²/(|c|² + nτ²))¹²⁸` for `n ≥ 40 000` and `0.46 ≤ θ ≤ 0.528`, for any vector
`c'` with `|c'|² = |c|²`. -/
lemma W128_le528 {n : ℕ} (hn : 24000 ≤ n) (c c' : Fin n → ℝ) (hc : normSq c' = normSq c) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 128 c' τ ≤ (10216 / 10000 * (τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))) ^ 128 :=
  BstLean.Part180.W128_le_24 hn c c' hc hτ hθ0 hθ1


open MeasureTheory in
/-- **The latitude moment bound in the window `θ ≤ 0.528`**: `E(1 − s²)⁶⁴ ≤ 0.6068⁶⁴` for
`n ≥ 40 000`, `0.46 ≤ θ ≤ 0.528`. -/
theorem theta_mom528 {n : ℕ} (hn : 24000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c τ) (hθ1 : BstLean.Part150.thetaC c τ ≤ 528 / 1000) :
    ∫⁻ a, ENNReal.ofReal ((1 - BstLean.Part157.latitude (n := n) (√(BstLean.Part130.normSq c)) τ a ^ 2) ^ 64)
        ∂(BstLean.Part161.muI n) ≤ ENNReal.ofReal ((5452 / 10000 : ℝ) ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  set a0 := √(normSq c) with ha0
  set c' : Fin n → ℝ := consV a0 0 with hc'
  have hcc : normSq c' = normSq c := by
    rw [hc', normSq_consV hn1, ha0, Real.sq_sqrt (normSq_nonneg c)]
    simp [normSq]
  set R : ℝ := normSq c + (n : ℝ) * τ ^ 2 with hR
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 10216 / 10000 * (τ ^ 2 / R) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (n : ℝ) + 2 * (128 : ℕ) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (B / A) ^ 64 := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hl2 : 0 ≤ lam / 2 := by linarith
  have hl2' : 0 ≤ (2 * lam)⁻¹ := inv_nonneg.mpr (by linarith)
  have hA128 : 0 ≤ A ^ 128 := pow_nonneg hA0.le _
  have hB128 : 0 ≤ B ^ 128 := pow_nonneg hB0.le _
  set f : (Fin n → ℝ) → ℝ := fun ξ => (τ ^ 2 * (normSq (c' + τ • ξ))⁻¹) ^ 128 with hf
  set g : (Fin n → ℝ) → ℝ := fun ξ => (normSq ξ) ^ 128 with hg
  set h : (Fin n → ℝ) → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (lam / 2 * f ξ) + ENNReal.ofReal ((2 * lam)⁻¹ * g ξ) with hh
  have hfm : Measurable f := by
    rw [hf]
    exact (measurable_const.mul ((measurable_normSq.comp
      (measurable_const.add (measurable_id.const_smul τ))).inv)).pow_const _
  have hgm : Measurable g := measurable_normSq.pow_const _
  have hhm : Measurable h :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)).add
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm))
  -- step 1: the pointwise bound off a null set
  have hnull : muI n {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} = 0 := by
    have e : {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} =
        Set.univ ×ˢ {G : Fin (n - 1) → ℝ | normSq G = 0} := by ext p; simp
    rw [e, muI, Measure.prod_prod, stdGauss_normSq_zero (by omega), mul_zero]
  have hae : ∀ᵐ p ∂(muI n), normSq p.2 ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with p hp
    exact hp
  have step1 : ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n) ≤
      ∫⁻ a, h (consV a.1 a.2) ∂(muI n) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨h0, h1⟩ := lat_pt hn1 a0 τ hτ p hp
    set x := τ ^ 2 * (normSq (c' + τ • consV (n := n) p.1 p.2))⁻¹ with hx
    set y := normSq (consV (n := n) p.1 p.2) with hy
    have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))
    have hy0 : 0 ≤ y := normSq_nonneg _
    have hp1 : (1 - latitude (n := n) a0 τ p ^ 2) ^ 64 ≤ x ^ 64 * y ^ 64 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 64
    have hamgm : x ^ 64 * y ^ 64 ≤ lam / 2 * x ^ 128 + (2 * lam)⁻¹ * y ^ 128 := by
      have hsq : 0 ≤ (lam * x ^ 64 - y ^ 64) ^ 2 := sq_nonneg _
      have e : lam / 2 * x ^ 128 + (2 * lam)⁻¹ * y ^ 128 - x ^ 64 * y ^ 64 =
          (lam * x ^ 64 - y ^ 64) ^ 2 / (2 * lam) := by
        field_simp; ring
      have : 0 ≤ (lam * x ^ 64 - y ^ 64) ^ 2 / (2 * lam) := div_nonneg hsq (by linarith)
      linarith
    rw [hh]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg hl2 (pow_nonneg hx0 _))
      (mul_nonneg hl2' (pow_nonneg hy0 _))]
    apply ENNReal.ofReal_le_ofReal
    exact hp1.trans hamgm
  -- step 2: the change of variables
  have step2 : ∫⁻ a, h (consV a.1 a.2) ∂(muI n) = ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := by
    rw [← consV_map hn1, lintegral_map hhm measurable_consV]
    rfl
  -- step 3: the two terms
  have hprob : IsProbabilityMeasure (BstLean.Part29.stdGauss (Fin n)) := by
    unfold BstLean.Part29.stdGauss; infer_instance
  have hfI : ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (A ^ 128) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_wqq (q := 128) (by omega) c' hτ)
      (ae_of_all _ fun ξ => BstLean.Part160.wqq_nonneg 128 c' τ ξ)]
    apply ENNReal.ofReal_le_ofReal
    have hW := W128_le528 hn c c' hcc hτ hθ0 hθ1
    rw [hA, hR]
    exact hW
  have hgI : ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (B ^ 128) := by
    have := chi_mom (ι := Fin n) 128
    simpa [hg, hB, normSq] using this
  have step3 : ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := by
    have hm1 : Measurable (fun ξ => ENNReal.ofReal (lam / 2 * f ξ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)
    show ∫⁻ ξ, (ENNReal.ofReal (lam / 2 * f ξ) + ENNReal.ofReal ((2 * lam)⁻¹ * g ξ))
      ∂(BstLean.Part29.stdGauss (Fin n)) ≤ _
    rw [lintegral_add_left hm1]
    simp_rw [ENNReal.ofReal_mul hl2, ENNReal.ofReal_mul hl2']
    rw [lintegral_const_mul _ hfm.ennreal_ofReal, lintegral_const_mul _ hgm.ennreal_ofReal]
    exact add_le_add (by gcongr) (by gcongr)
  -- step 4: the numbers
  have hval : lam / 2 * A ^ 128 + (2 * lam)⁻¹ * B ^ 128 = (A * B) ^ 64 := by
    have e1 : lam * A ^ 64 = B ^ 64 := by
      rw [hlam, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hA0.ne')]
    have e2 : lam / 2 * A ^ 128 = B ^ 64 * A ^ 64 / 2 := by
      rw [← e1]; ring
    have e3 : (2 * lam)⁻¹ * B ^ 128 = A ^ 64 * B ^ 64 / 2 := by
      rw [show B ^ 128 = B ^ 64 * B ^ 64 by ring, ← e1]; field_simp
    rw [e2, e3, mul_pow]; ring
  have hAB : A * B ≤ 5452 / 10000 := by
    have hθ : BstLean.Part150.thetaC c τ = (n : ℝ) * τ ^ 2 / R := by
      unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
      rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le)]
    rw [hθ, div_le_iff₀ hR0] at hθ1
    rw [hA, hB]
    push_cast
    rw [show 10216 / 10000 * (τ ^ 2 / R) * ((n : ℝ) + 2 * 128) =
      10216 / 10000 * (τ ^ 2 * ((n : ℝ) + 256)) / R by ring, div_le_iff₀ hR0]
    have hT := sq_nonneg τ
    have : τ ^ 2 * 256 ≤ 528 / 1000 * R * (256 / 24000) := by
      have : 24000 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR hT
      linarith
    linarith
  have hfinal : (A * B) ^ 64 ≤ (5452 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ (mul_nonneg hA0.le hB0.le) hAB 64
  calc ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n)
      ≤ ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := step1.trans step2.le
    _ ≤ ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := step3
    _ = ENNReal.ofReal ((A * B) ^ 64) := by
        rw [← ENNReal.ofReal_mul hl2, ← ENNReal.ofReal_mul hl2',
          ← ENNReal.ofReal_add (mul_nonneg hl2 hA128) (mul_nonneg hl2' hB128), hval]
    _ ≤ ENNReal.ofReal ((5452 / 10000 : ℝ) ^ 64) := ENNReal.ofReal_le_ofReal hfinal

end STh


section SCert
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (muI Ix BIAS_hyp lamX sigX)
open BstLean.Part162 (dPaper psiA)
open BstLean.Part153 (nuA)
open BstLean.Part166 (psiK psiK_nonneg fK sK winC certI Cf Scert measurableSet_Scert
  markov12 measurable_psiK_f measurable_psiK_s goodD measurable_certI measurable_thetaC_key pow64_le
  integral_le_of_lintegral psiA_lam_eq psiA_sig_eq)
open BstLean.Part165 (goodC roomC roomC_ge)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
open BstLean.Part175.N50 (winC528 Scert528 measurableSet_Scert528 scert_of_good528 roomF roomF_ge)
variable {n : ℕ}

/-- **One certificate from the per-input moment for `v ≠ 0`** (Part 166's `charge_one`, a.e.), in the window `θ ≤ 0.528` (`Θ = 0.6068`). -/
theorem charge_one_ae528 (hn : 24000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC528 c τ)
    {Φ : AgFam n → (Fin n → ℝ) → ℝ}
    (hΦ : Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2))
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hyp : ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
      ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n ≤
        ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)) :
    nuA n {θ | ENNReal.ofReal (C ^ 12) < certI Φ ((c, τ), θ)} ≤
      ENNReal.ofReal ((5452 / 10000 * K / C) ^ 64) := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hw
  have hdir := ae_ne_zero_dir (n := n) (by omega)
  have hm : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
      × Ix n × (Fin (n - 1) → ℝ) => psiK Φ ((c, τ), z.1) z.2.1 z.2.2) := by
    have hk : Measurable (fun z : (Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × Ix n × (Fin (n - 1) → ℝ) =>
        ((((c, τ), z.1) : AgFam n), z.2.1, z.2.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
    have h2 := hΦ.comp hk
    rw [Function.comp_def] at h2
    exact h2
  have hM := markov12 (nuA n) (muI n) (stdGauss (Fin (n - 1)))
    (fun θ a v => psiK Φ ((c, τ), θ) a v) hm (fun _ _ _ => psiK_nonneg _ _ _ _)
    (p := 64) (by norm_num) hC
  refine hM.trans ?_
  have hnum : ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
      ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      ENNReal.ofReal ((5452 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
    calc ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ ∫⁻ a, ∫⁻ _v : Fin (n - 1) → ℝ,
            ENNReal.ofReal (((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) * K) ^ 64)
            ∂stdGauss (Fin (n - 1)) ∂muI n :=
          lintegral_mono fun a => lintegral_mono_ae (hdir.mono fun v hv => hyp a v hv)
      _ = ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) *
            ENNReal.ofReal (K ^ 64) ∂muI n := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const, measure_univ, mul_one, mul_pow,
            ENNReal.ofReal_mul (by positivity)]
      _ = (∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) (√(normSq c)) τ a ^ 2) ^ 64) ∂muI n) *
            ENNReal.ofReal (K ^ 64) := by
          rw [lintegral_mul_const]
          exact ENNReal.measurable_ofReal.comp ((measurable_const.sub
            ((measurable_latitude_comp measurable_const measurable_const
              measurable_id).pow_const 2)).pow_const 64)
      _ ≤ ENNReal.ofReal ((5452 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) := by
          gcongr
          exact theta_mom528 hn c hτ hθ0 hθ1
  calc (∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (psiK Φ ((c, τ), θ) a v ^ 64) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n) / ENNReal.ofReal (C ^ 64)
      ≤ ENNReal.ofReal ((5452 / 10000 : ℝ) ^ 64) * ENNReal.ofReal (K ^ 64) /
          ENNReal.ofReal (C ^ 64) := by gcongr
    _ = ENNReal.ofReal ((5452 / 10000 * K / C) ^ 64) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
        rw [div_pow (5452 / 10000 * K) C 64, mul_pow (5452 / 10000 : ℝ) K 64]


/-- The `f` certificate charge with `Θ = 0.6068`. -/
lemma delta_f_24 : (5452 / 10000 * (5) / Cf : ℝ) ^ 64 ≤ 2 / 10 ^ 5 := by
  have h1 : (5452 / 10000 * (5) / Cf : ℝ) ≤ 8320 / 10000 := by unfold Cf; norm_num
  have h0 : (0 : ℝ) ≤ 5452 / 10000 * (5) / Cf := by unfold Cf; positivity
  calc (5452 / 10000 * (5) / Cf : ℝ) ^ 64 ≤ (8320 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ h0 h1 64
    _ ≤ 2 / 10 ^ 5 := by norm_num

/-- The `σ` certificate charge with `Θ = 0.6068`. -/
lemma delta_s_24 : (5452 / 10000 * (5) / (326 / 100) : ℝ) ^ 64 ≤ 2 / 10 ^ 5 := by
  have h1 : (5452 / 10000 * (5) / (326 / 100) : ℝ) ≤ 8363 / 10000 := by norm_num
  calc (5452 / 10000 * (5) / (326 / 100) : ℝ) ^ 64 ≤ (8363 / 10000 : ℝ) ^ 64 :=
        pow_le_pow_left₀ (by norm_num) h1 64
    _ ≤ 2 / 10 ^ 5 := by norm_num

/-- **The charge of `Scert528` from the a.e. form of Lemma LJ**: `≤ 34·10⁻⁵` for every World
value (`n ≥ 40 000`). -/
theorem cert_charge528 (hn : 24000 ≤ n) (hLJ : LJae_hyp n (5)) (c : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ Scert528 n} ≤ 4 / 10 ^ 5 := by
  have hn0 : (0 : ℝ) < n := by
    have : (24000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_cases hw : winC528 c τ
  · have hw' : winC c τ := ⟨hw.1, hw.2.1, hw.2.2.trans (by norm_num)⟩
    have hsub : {θ | ((c, τ), θ) ∉ Scert528 n} ⊆
        {θ | ENNReal.ofReal ((Cf / n) ^ 12) < certI fK ((c, τ), θ)} ∪
        {θ | ENNReal.ofReal ((326 / 100 * (2 / n) / n) ^ 12) < certI sK ((c, τ), θ)} := by
      intro θ hθ
      simp only [Scert528, Set.mem_ofPred_eq, not_imp, not_and_or, not_le] at hθ
      rcases hθ.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 := charge_one_ae528 hn hw measurable_psiK_f (K := 5 / n) (C := Cf / n)
      (by positivity) (by unfold Cf; positivity) (fun a v hv => by
        have := (hLJ c τ hw' a v hv).1
        rwa [mul_div_assoc] at this)
    have h2 := charge_one_ae528 hn hw measurable_psiK_s (K := 2 / n * (5) / n)
      (C := 326 / 100 * (2 / n) / n) (by positivity) (by positivity) (fun a v hv => by
        have := (hLJ c τ hw' a v hv).2
        rwa [mul_assoc, mul_div_assoc] at this)
    have e1 : 5452 / 10000 * (5 / n) / (Cf / n) = 5452 / 10000 * (5) / Cf := by
      field_simp
    have e2 : 5452 / 10000 * (2 / n * (5) / n) / (326 / 100 * (2 / n) / n) =
        5452 / 10000 * (5) / (326 / 100 : ℝ) := by
      field_simp
    rw [e1] at h1
    rw [e2] at h2
    have hU : nuA n {θ | ((c, τ), θ) ∉ Scert528 n} ≤
        ENNReal.ofReal (2 / 10 ^ 5) + ENNReal.ofReal (2 / 10 ^ 5) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
      · exact h1.trans (ENNReal.ofReal_le_ofReal delta_f_24)
      · exact h2.trans (ENNReal.ofReal_le_ofReal delta_s_24)
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)] at hU
    have := ENNReal.toReal_le_of_le_ofReal (by norm_num) hU
    rw [measureReal_def]
    linarith
  · have e : {θ | ((c, τ), θ) ∉ Scert528 n} = ∅ := by
      ext θ
      simp only [Scert528, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun h => absurd h hw
    rw [e]
    simp only [measureReal_empty]
    norm_num

/-- **The charge of `Scert528` on the retained data**. -/
theorem cert_ret_charge528 (hn : 24000 ≤ n) (hLJ : LJae_hyp n (5))
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (Scert528 n))ᶜ ≤
      4 / 10 ^ 5 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_Scert528 n) (by norm_num) (fun c τ _ => cert_charge528 hn hLJ c τ)

/-- **Part 165's two certificates on a good set that contains `agentEv D (Scert528 n)`.** -/
theorem certs_of_good528 (hn : 24000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {E : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) E)
    (hS0 : c ∈ agentEv (paperDesign n fT wT hf hw) (Scert528 n)) :
    (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
    (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
        ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) := by
  set D := paperDesign n fT wT hf hw with hDd
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD := paperDesign_agentCentre fT wT hf hw
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hS : agKey D c ∈ Scert528 n := hS0 hτ
  obtain ⟨hcf, hcs⟩ := hS ⟨hτ, hθ0, (BstLean.Part175.win528_goodA hn16 fT wT hf hw E hc).2.2⟩
  set k := agKey D c with hk
  have hmk : ∀ {Φ : AgFam n → (Fin n → ℝ) → ℝ},
      Measurable (fun z : AgFam n × Ix n × (Fin (n - 1) → ℝ) => psiK Φ z.1 z.2.1 z.2.2) →
      Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) => psiK Φ k z.1 z.2 ^ 12) := by
    intro Φ hΦ
    have hm : Measurable (fun z : Ix n × (Fin (n - 1) → ℝ) =>
        ((k, z.1, z.2) : AgFam n × Ix n × (Fin (n - 1) → ℝ))) :=
      measurable_const.prodMk (measurable_fst.prodMk measurable_snd)
    have h2 := hΦ.comp hm
    rw [Function.comp_def] at h2
    exact h2.pow_const 12
  -- σ
  have hsig : ∫ a, ∫ v, psiK sK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK sK k a v ^ 12)
      (hmk measurable_psiK_s) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _) (by positivity) hcs
  have hfK : ∫ a, ∫ v, psiK fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (Cf / n) ^ 12 :=
    integral_le_of_lintegral (muI n) (stdGauss (Fin (n - 1))) (fun a v => psiK fK k a v ^ 12)
      (hmk measurable_psiK_f) (fun _ _ => pow_nonneg (psiK_nonneg _ _ _ _) _)
      (by unfold Cf; positivity) hcf
  refine ⟨?_, ?_⟩
  · -- the energy lower bound `e_b ≥ 0.6425`
    have hG := goodC16_of_goodA hn16 fT wT hf hw hc
    have hU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hc.2.2.1.2 hτ
    have hlo := eb16_lower hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hU
    have hb : D.bA c.1 c.2.1.1 =
        (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
    rw [← hb] at hlo
    have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
    rw [hmA] at hlo
    set e := normSq (D.bA c.1 c.2.1.1) / n with he
    have he0 : 257 / 400 ≤ e := by
      rw [he, le_div_iff₀ hn0]
      have h2 : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) ≤
          2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      have l : 2 / (n : ℝ) * (257 / 400) * (n ^ 2 / 2) = 257 / 400 * n := by field_simp
      have r : 2 / (n : ℝ) ^ 2 * normSq (D.bA c.1 c.2.1.1) * (n ^ 2 / 2) =
          normSq (D.bA c.1 c.2.1.1) := by field_simp
      linarith
    have hepos : 0 < e := lt_of_lt_of_le (by norm_num) he0
    have hpt : ∀ a v, psiA (lamX D c) D c a v ^ 12 = (e⁻¹) ^ 12 * psiK fK k a v ^ 12 := by
      intro a v
      have h := psiA_lam_eq (by omega) D hD c a v
      rw [← he] at h
      rw [← h, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hepos.ne', one_pow, one_mul]
    simp_rw [hpt, integral_const_mul]
    calc (e⁻¹) ^ 12 * ∫ a, ∫ v, psiK fK k a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n
        ≤ (e⁻¹) ^ 12 * (Cf / n) ^ 12 := mul_le_mul_of_nonneg_left hfK (by positivity)
      _ = (Cf / e / n) ^ 12 := by rw [← mul_pow]; congr 1; field_simp
      _ ≤ (51 / 10 / n) ^ 12 := by
          apply pow_le_pow_left₀ (by unfold Cf; positivity)
          apply div_le_div_of_nonneg_right _ hn0.le
          rw [div_le_iff₀ hepos]
          unfold Cf
          linarith
  · simp_rw [psiA_sig_eq D hD c]
    exact hsig

end SCert

end BstLean.Part179.N30.N27.N26.N24
