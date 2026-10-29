import BstLean.Part188All
import BstLean.Part181Jen
import BstLean.Part182Ew
import BstLean.Part183D19
import BstLean.Part184Def




namespace BstLean.Part190.Frame16200
open BstLean.Part183 BstLean.Part183.F16250
open BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part160 (WqN)
open BstLean.Part176 (fL fL_mono fL_eq WqN_le_layer exp_neg_quart')

variable {n : ℕ}


noncomputable def epsF16200 (k : ℕ) : ℝ := 51 / 10000 * ((min k 10 : ℕ) : ℝ)

lemma epsF16200_mono (k : ℕ) : epsF16200 k ≤ epsF16200 (k + 1) := by
  unfold epsF16200
  have : ((min k 10 : ℕ) : ℝ) ≤ ((min (k + 1) 10 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 10 (Nat.le_succ k)
  linarith

lemma epsF16200_lt (k : ℕ) : epsF16200 k < 1 := by
  unfold epsF16200
  have : ((min k 10 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast min_le_right k 10
  linarith


lemma fL_eqF16200 {τ Q e : ℝ} (hQ : 0 < Q) (he : e < 1) :
    fL 20 τ Q e = (τ ^ 2 / Q) ^ 20 * (1 / ((1 - e) ^ 2) ^ 20) := by
  unfold fL
  have h1 : 0 < 1 - e := by linarith
  have : (1 - e) ^ 2 ≠ 0 := by positivity
  rw [show (1 : ℝ) / ((1 - e) ^ 2) ^ 20 = (1 / (1 - e) ^ 2) ^ 20 by rw [div_pow, one_pow],
    ← mul_pow]
  congr 1
  field_simp



noncomputable def CF16200 (e : ℝ) : ℝ := 1 / ((1 - e) ^ 2) ^ 20


noncomputable def PF16200 (e : ℝ) : ℝ := 1 / (1 + e ^ 2 * 15387 / 4 + (e ^ 2 * 15387 / 4) ^ 2 / 2) ^ 4

lemma sumF16200_le : ∑ k ∈ Finset.range 10, (CF16200 (epsF16200 (k + 1)) - CF16200 (epsF16200 k)) * PF16200 (epsF16200 k) ≤
    631 / 1250 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, epsF16200, CF16200, PF16200]
  norm_num


open BstLean.Part150 (thetaC rhoC) in

theorem W20_le_F16200 (hn : 16200 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (10212 / 10000 * (thetaC c τ / n)) ^ 20 :=
  BstLean.Part188.Chain.M.W20_le_528_22 hn c hτ hθ0 hθ1


section SXM
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr nuA jS)




def SXM16200 (n : ℕ) : Set (AgFam n) :=
  {x | XqN 20 x.2.1 x.2.2 x.1.1 x.1.2 ≤ (1120 / 1000 * (n : ℝ)) ^ 20 * WqN 20 x.1.1 x.1.2}

theorem measurableSet_SXM16200 (n : ℕ) : MeasurableSet (SXM16200 n) :=
  measurableSet_le (measurable_XqN_fam 20) ((measurable_WqN_fam 20).const_mul _)


lemma gaussMomConst_800_leF16200 : BstLean.Part152.gaussMomConst 800 ≤ 2433 / 100 := by
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

lemma sqrt_eta_leF16200 : √(1 + 2 * (56 / 10000) : ℝ) ≤ 10056 / 10000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

lemma epsS_800_leF16200 {n : ℕ} (hn : 16200 ≤ n) :
    BstLean.Part153.epsS n 800 (56 / 10000) ≤ 46 / 10 ^ 6 := by
  have hnr : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : exp (-1) ≤ 36788 / 100000 := by
    have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
  have h10 : exp (-10) ≤ 46 / 10 ^ 6 := by
    have e : exp (-10) = exp (-1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc exp (-1) ^ 10 ≤ (36788 / 100000 : ℝ) ^ 10 := pow_le_pow_left₀ (exp_pos _).le h1 10
      _ ≤ 46 / 10 ^ 6 := by norm_num
  refine le_trans ?_ h10
  unfold BstLean.Part153.epsS
  rw [show ((800 : ℕ) : ℝ) = 800 by norm_num]
  refine Real.exp_le_exp.2 ?_
  have : (16200 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
  have h12 : (10 : ℝ) ≤ (56 / 10000) ^ 2 * (n : ℝ) ^ 2 / 800 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith


lemma jS_800_le_16200 (hn : 16200 ≤ n) : jS n 800 (56 / 10000) ≤ 105150 / 100000 := by
  have hnr : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (12727 / 100 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := BstLean.Part152.gaussMomConst_nonneg 800
  have hg := gaussMomConst_800_leF16200
  have hu : 1 / √(n : ℝ) ≤ 1 / (12727 / 100) := one_div_le_one_div_of_le (by norm_num) hs
  have hw : BstLean.Part152.gaussMomConst 800 / (n : ℝ) ≤ (2433 / 100) / 16200 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : BstLean.Part152.gaussMomConst 800 / √(n : ℝ) ≤ (2433 / 100) / (12727 / 100) := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (BstLean.Part153.jS_le_atoms n 800 (56 / 10000) BstLean.Part153.sqrt_two_le
    sqrt_eta_leF16200 hu hw hgu (epsS_800_leF16200 hn)).trans ?_
  norm_num

lemma pow_98760_leF16200 : (98722 / 100000 : ℝ) ^ 800 ≤ 5 / 100000 := by
  have : (98722 / 100000 : ℝ) ^ 800 = ((98722 / 100000 : ℝ) ^ 100) ^ 8 := by rw [← pow_mul]
  rw [this]
  norm_num


theorem SXM16200_charge (hn : 16200 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXM16200 n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXM16200 n} =
      {θ | (1120 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (1120 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 40) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 800 (56 / 10000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 56 / 10000) hx) (M := 1120 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 800 (56 / 10000)
  have hj := jS_800_le_16200 hn
  have hj2 : jS n 800 (56 / 10000) ^ 2 ≤ (105150 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 800 (56 / 10000) ^ 2 / (1120 / 1000) ≤ 98722 / 100000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio (20 * 40)).trans pow_98760_leF16200

theorem SXM16200_ret_charge (hn : 16200 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SXM16200 n))ᶜ ≤
      5 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SXM16200 n) (by norm_num) (fun c τ hτ => SXM16200_charge hn c τ hτ)


theorem tX20_le_WF16200 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM16200 n) :
    (2 / (mA n : ℝ)) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (6040 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 20 A₁ A₂ c τ ≤ (1120 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_F16200 hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  have h3 : XqN 20 A₁ A₂ c τ ≤ (1120 / 1000 * (10212 / 10000) * thetaC c τ) ^ 20 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]; congr 1; field_simp
  have hB : 1120 / 1000 * (10212 / 10000) * thetaC c τ ≤ 6040 / 10000 := by nlinarith
  have h4 := pow_le_pow_left₀ (by positivity) hB 20
  rw [hmA]
  calc (2 / (n : ℝ) ^ 2) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (2 / (n : ℝ) ^ 2) ^ 20 * (6040 / 10000) ^ 20 :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (6040 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by rw [← mul_pow]; congr 1; field_simp



end SXM


open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part181 (xq_pt integrable_xq Xq_le_of_X20)
open BstLean.Part153 (XiS Xi4 jacT)
open BstLean.Part152 (opN opN_nonneg)



lemma X20_SXM16200 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM16200 n) :
    XqN 20 A₁ A₂ c τ ≤ (1120 / 1000 * (10212 / 10000) * thetaC c τ) ^ 20 := by
  have hn0 : (0 : ℝ) < n := by
    have : (16200 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : XqN 20 A₁ A₂ c τ ≤ (1120 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_F16200 hn c hτ hθ0 hθ1
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
  rw [← mul_pow]; congr 1; field_simp


theorem Xi4_SXM16200 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM16200 n) :
    Xi4 A₁ A₂ c τ ≤ 1120 / 1000 * (10212 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (16200 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1120 / 1000 * (10212 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; nlinarith
  have h20 := X20_SXM16200 hn hτ hθ0 (hθ1.trans hθh) h
  rw [← hB] at h20
  have h2 := Xq_le_of_X20 (q := 2) (by norm_num) (by omega) A₁ A₂ c hτ hBp h20
  have h4 : √(XqN 2 A₁ A₂ c τ) ≤ B := by
    rw [← Real.sqrt_sq hBp.le]; exact Real.sqrt_le_sqrt h2
  rw [Xi4_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 1120 / 1000 * (10212 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(XqN 2 A₁ A₂ c τ) ≤
      2 / (n : ℝ) ^ 2 * (1120 / 1000 * (10212 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp


theorem Xi8_SXM16200 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM16200 n) :
    Xi8 A₁ A₂ c τ ≤ 1120 / 1000 * (10212 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (16200 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1120 / 1000 * (10212 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; nlinarith
  have h20 := X20_SXM16200 hn hτ hθ0 (hθ1.trans hθh) h
  rw [← hB] at h20
  have h3 : XqN 4 A₁ A₂ c τ ≤ (B ^ 2) ^ 2 := by
    rw [← pow_mul]; exact Xq_le_of_X20 (q := 4) (by norm_num) (by omega) A₁ A₂ c hτ hBp h20
  have h4 : √(XqN 4 A₁ A₂ c τ) ≤ B ^ 2 := by
    rw [← Real.sqrt_sq (sq_nonneg B)]; exact Real.sqrt_le_sqrt h3
  have h4' : √(√(XqN 4 A₁ A₂ c τ)) ≤ B := by
    rw [← Real.sqrt_sq hBp.le]; exact Real.sqrt_le_sqrt h4
  rw [Xi8_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 1120 / 1000 * (10212 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(√(XqN 4 A₁ A₂ c τ)) ≤
      2 / (n : ℝ) ^ 2 * (1120 / 1000 * (10212 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4'.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp


theorem XiS_SXM16200 (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM16200 n) :
    XiS A₁ A₂ c τ ≤ 1120 / 1000 * (10212 / 10000) * θh * (2 / (n : ℝ)) / n :=
  (BstLean.Part153.XiS_le_Xi4 (by omega) A₁ A₂ c hτ).trans (Xi4_SXM16200 hn hτ hθ0 hθ1 hθh h)

end BstLean.Part190.Frame16200

open BstLean.Part190.Frame16200 in
#print axioms SXM16200_ret_charge
open BstLean.Part190.Frame16200 in
#print axioms XiS_SXM16200
open BstLean.Part190.Frame16200 in
#print axioms Xi8_SXM16200
open BstLean.Part190.Frame16200 in
#print axioms tX20_le_WF16200
