import BstLean.Part160ScLo
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Event
import BstLean.Part187R160Cov
import BstLean.Part187R160ScEv
import BstLean.Part187R160Sc
import BstLean.Part187R160ScTab

/-! Part 187 (file `Part187R160ScLo`): copy of `Part160ScLo` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC hO gO sO2 bO bT rhoC_sqP rhoC_posP)
open BstLean.Part153 (nrm nuA GoodAs Pb)
open BstLean.Part154 (GoodC16 csC)

variable {n : ℕ}

/-- `scUp ≤ u·γ_Aρ²` for `0.46 ≤ θ_in ≤ θhi ≤ 0.55`. -/
theorem scUp_le (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {θhi u : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θhi) (hhi : θhi ≤ 55 / 100)
    (hu : 1 - 3183 / 10000 + 31832 / 100000 * (55 / 100 / 16250) - (1 - θhi) / 2 -
      3183 / 10000 / 2 * (1 - θhi) ^ 2 ≤ u) :
    scUp n c τ ≤ u * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) := by
  obtain ⟨hR, -, -, hT⟩ := window_facts hn c hτ hθ0 (hθ1.trans hhi)
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 := normSq_nonneg c
  have hN : (1 - θhi) * (normSq c + (n : ℝ) * τ ^ 2) ≤ normSq c := by
    unfold thetaC at hθ1
    rw [rhoC_sqP, div_le_iff₀ hR] at hθ1
    linarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / π := ⟨_, rfl⟩
  obtain ⟨hp1, hp2⟩ := pi_inv_bounds
  rw [← hp] at hp1 hp2
  unfold scUp
  have e1 : τ ^ 2 / π = p * τ ^ 2 := by rw [hp]; ring
  have e2 : ∀ x : ℝ, x / (2 * π) = p / 2 * x := fun x => by rw [hp]; field_simp
  rw [e1, e2, ← hp]
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  rw [← hRd] at hR hN hT ⊢
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = normSq c := ⟨_, rfl⟩
  rw [← hNd] at hN hN0 ⊢
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - θhi := ⟨_, rfl⟩
  rw [← hq] at hN hu
  have hq0 : 0 ≤ q := by rw [hq]; linarith
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg τ
  have hNN : q ^ 2 * R ≤ N ^ 2 / R := by
    rw [le_div_iff₀ hR]
    have : (q * R) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
    nlinarith
  rw [show u * (2 / (n : ℝ) * R) = 2 / (n : ℝ) * (u * R) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have a1 : (1 - p) * R ≤ (1 - 3183 / 10000) * R := mul_le_mul_of_nonneg_right (by linarith) hR.le
  have a2 : p * τ ^ 2 ≤ 31832 / 100000 * (55 / 100 / 16250 * R) :=
    mul_le_mul hp2 hT hτ2 (by norm_num)
  have a3 : 3183 / 10000 / 2 * (q ^ 2 * R) ≤ p / 2 * (N ^ 2 / R) :=
    mul_le_mul (by linarith) hNN (by positivity) (by linarith)
  have a4 := mul_le_mul_of_nonneg_right hu hR.le
  nlinarith

/-- `scUp ≥ 0.3652·γ_Aρ²` in the window `0.46 ≤ θ_in ≤ 0.55`. -/
theorem scUp_ge (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    3652 / 10000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤ scUp n c τ := by
  obtain ⟨hR, hN, -, -⟩ := window_facts hn c hτ hθ0 hθ1
  have hN0 := normSq_nonneg c
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / π := ⟨_, rfl⟩
  obtain ⟨hp1, hp2⟩ := pi_inv_bounds
  rw [← hp] at hp1 hp2
  unfold scUp
  have e1 : τ ^ 2 / π = p * τ ^ 2 := by rw [hp]; ring
  have e2 : ∀ x : ℝ, x / (2 * π) = p / 2 * x := fun x => by rw [hp]; field_simp
  rw [e1, e2, ← hp]
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  rw [← hRd] at hR hN ⊢
  obtain ⟨N, hNd⟩ : ∃ N : ℝ, N = normSq c := ⟨_, rfl⟩
  rw [← hNd] at hN hN0 ⊢
  have hNN : N ^ 2 / R ≤ (54 / 100) ^ 2 * R := by
    rw [div_le_iff₀ hR]
    have : N ^ 2 ≤ (54 / 100 * R) ^ 2 := pow_le_pow_left₀ hN0 hN 2
    nlinarith
  rw [show 3652 / 10000 * (2 / (n : ℝ) * R) = 2 / (n : ℝ) * (3652 / 10000 * R) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have a1 : (1 - 31832 / 100000) * R ≤ (1 - p) * R :=
    mul_le_mul_of_nonneg_right (by linarith) hR.le
  have a2 : 0 ≤ p * τ ^ 2 := by positivity
  have a3 : p / 2 * (N ^ 2 / R) ≤ 31832 / 100000 / 2 * ((54 / 100) ^ 2 * R) :=
    mul_le_mul (by linarith) hNN (by positivity) (by norm_num)
  nlinarith

/-- Chebyshev for `s_h²` above `scUp`, in the window. -/
theorem SScU_cheb (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | 105 / 100 * scUp n c τ < sO2 A₁ c τ} ≤
      3630 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨hR, hN, hS, hT⟩ := window_facts hn c hτ hθ0 hθ1
  have hge := scUp_ge hn c hτ hθ0 hθ1
  have hmean := sO2_mean_upper hn1 hm c hτ
  obtain ⟨LS, hvar⟩ := BstLean.Part153.sO2_var (m := mA n) hn1 hm c τ
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = scUp n c τ := ⟨_, rfl⟩
  rw [← hL] at hge hmean ⊢
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hLτ : 1328 / 1000 * τ ^ 2 ≤ L := by
    refine le_trans ?_ hge
    have e : 3652 / 10000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) =
        7304 / 10000 * (normSq c + (n : ℝ) * τ ^ 2) / n := by ring
    rw [e, le_div_iff₀ hn0]
    nlinarith
  have hL0 : 0 < L := by nlinarith
  have hc0 : 0 < L / 20 := by positivity
  have hch := meas_ge_le_variance_div_sq LS hc0
  have hsub : {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | 105 / 100 * L < sO2 A₁ c τ} ⊆
      {A₁ | L / 20 ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ))|} := by
    intro A₁ hA
    have hA' : 105 / 100 * L < sO2 A₁ c τ := hA
    change L / 20 ≤ |sO2 A₁ c τ -
        ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, sO2 A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ))|
    refine le_trans ?_ (le_abs_self _)
    linarith
  have h1 : (gaussMat (mA n) n (2 / (n : ℝ))).real
      {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | 105 / 100 * L < sO2 A₁ c τ} ≤
      (ENNReal.ofReal (variance (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat (mA n) n (2 / (n : ℝ))) / (L / 20) ^ 2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hch)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at h1
  refine h1.trans ?_
  rw [hmA] at hvar
  have hw : 1 + 2 / (n : ℝ) ≤ 1 + 2 / 16250 := by
    have : 2 / (n : ℝ) ≤ 2 / 16250 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    linarith
  have hL2 : (1328 / 1000 * τ ^ 2 / 20) ^ 2 ≤ (L / 20) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc variance (fun A₁ : Matrix (Fin (mA n)) (Fin n) ℝ => sO2 A₁ c τ)
        (gaussMat (mA n) n (2 / (n : ℝ))) / (L / 20) ^ 2
      ≤ (16 * (1 + 2 / (n : ℝ)) * τ ^ 4 / (n : ℝ) ^ 2) / (L / 20) ^ 2 :=
        div_le_div_of_nonneg_right hvar (by positivity)
    _ ≤ (16 * (1 + 2 / 16250) * τ ^ 4 / (n : ℝ) ^ 2) / (1328 / 1000 * τ ^ 2 / 20) ^ 2 := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) hL2
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num))
          (by positivity)
    _ = (16 * (1 + 2 / 16250) * 400 / (1328 / 1000) ^ 2) / (n : ℝ) ^ 2 := by
        field_simp
        norm_num
    _ ≤ 3630 / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- **The charge of the event `SScU`**: `≤ 3630/n²`, every `c`, `τ > 0`, `n ≥ 16250`. -/
theorem SScU_charge (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SScU n} ≤ 3630 / (n : ℝ) ^ 2 := by
  by_cases hw : 46 / 100 ≤ thetaC c τ ∧ thetaC c τ ≤ 55 / 100
  · have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ((c, τ), θ) ∉ SScU n} =
        {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ | 105 / 100 * scUp n c τ < sO2 A₁ c τ} ×ˢ
          (Set.univ : Set (Matrix (Fin (mA n)) (Fin (mA n)) ℝ)) := by
      ext θ
      simp only [SScU, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true, not_forall,
        not_le]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · intro h; exact ⟨hw.1, hw.2, h⟩
    rw [e]
    unfold nuA
    rw [measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
    exact SScU_cheb hn c hτ hw.1 hw.2
  · have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
        ((c, τ), θ) ∉ SScU n} = ∅ := by
      ext θ
      simp only [SScU, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hw
    rw [e]
    simp only [measureReal_empty]
    positivity

theorem SScU_charge_num (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SScU n} ≤ 14 / 1000000 := by
  refine (SScU_charge hn c τ hτ).trans ?_
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The real-number core of the lower norm: from `E P² ≥ κl·G`, `Var P ≤ t Γ`,
`P ≥ E P − √(24 t)√Γ`, `Γ ≤ 1.001 G`, `t ≤ 2/16250²`: `P ≥ eo·√G`. -/
lemma pb_core {Γ rb2 E P G t κl eo : ℝ} (hG : 0 ≤ G) (ht0 : 0 ≤ t) (ht : t ≤ 2 / 16250 ^ 2)
    (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ 1001 / 1000 * G) (hrb : κl * G ≤ rb2) (hE : 0 ≤ E)
    (hvar : rb2 - E ^ 2 ≤ t * Γ) (hP : E - √(2 * 12 * t) * √Γ ≤ P) (_heo : 0 ≤ eo)
    (hnum : (eo + 43 / 100000) ^ 2 ≤ κl - 1001 / 1000 * (2 / 16250 ^ 2)) :
    eo * √G ≤ P := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √G := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = G := by rw [hs]; exact Real.sq_sqrt hG
  rw [← hs]
  have htΓ : t * Γ ≤ 2 / 16250 ^ 2 * (1001 / 1000 * G) := mul_le_mul ht hΓ hΓ0 (by norm_num)
  have h1 : (eo + 43 / 100000) * s ≤ E := by
    refine abs_le_of_sq_le_sq' ?_ hE |>.2
    rw [mul_pow, hs2]
    have := mul_le_mul_of_nonneg_right hnum hG
    nlinarith
  have h2 : √(2 * 12 * t) * √Γ ≤ 43 / 100000 * s := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hΓ0, hs2]
    nlinarith
  calc eo * s = (eo + 43 / 100000) * s - 43 / 100000 * s := by ring
    _ ≤ E - √(2 * 12 * t) * √Γ := sub_le_sub h1 h2
    _ ≤ P := hP

/-- **The lower norm of the oracle centre** on `GoodC16` and `SScU`, for
`0.46 ≤ θ_in ≤ θhi ≤ 0.55`, with free numbers: `𝖯_b ≥ eo·√(γ_A)·ρ`. -/
theorem Pb_lower_gen (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {θhi u w κl eo : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θhi) (hhi : θhi ≤ 55 / 100)
    (hu : 1 - 3183 / 10000 + 31832 / 100000 * (55 / 100 / 16250) - (1 - θhi) / 2 -
      3183 / 10000 / 2 * (1 - θhi) ^ 2 ≤ u)
    (hw0 : 0 < w) (hw : w ≤ 1 - 1 / 1000 - 105 / 100 * u)
    (hκ : κl ≤ 999 / 1000 * (3183 / 10000) + w / 2 + w ^ 2 * (3183 / 10000) / (2 * (1001 / 1000)))
    (heo : 0 ≤ eo) (hnum : (eo + 43 / 100000) ^ 2 ≤ κl - 1001 / 1000 * (2 / 16250 ^ 2))
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    eo * √(2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤ Pb A₁ c τ A₂ := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hAs : (A₁, A₂) ∈ GoodAs n c τ := h.1.1
  have hPb : A₂ ∉ BstLean.Part154.BadPb A₁ c τ 12 := h.1.2.2.2.2.1
  obtain ⟨hR, -, -, -⟩ := window_facts hn c hτ hθ0 (hθ1.trans hhi)
  have hE := energy16 hn hAs
  have hs1 : sO2 A₁ c τ ≤ 105 / 100 * scUp n c τ := hU hθ0 (hθ1.trans hhi)
  have hs2 := scUp_le hn c hτ hθ0 hθ1 hhi hu
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hGd]; positivity
  rw [← hGd] at hE hs2 ⊢
  obtain ⟨hEl, hEu⟩ := abs_le.mp hE
  obtain ⟨Γ, hΓd⟩ : ∃ Γ : ℝ, Γ = gO A₁ c τ := ⟨_, rfl⟩
  rw [← hΓd] at hEl hEu
  have hΓ0 : 0 < Γ := by nlinarith
  obtain ⟨S, hSd⟩ : ∃ S : ℝ, S = sO2 A₁ c τ := ⟨_, rfl⟩
  rw [← hSd] at hs1
  have hS0 : 0 ≤ S := by rw [hSd]; exact BstLean.Part153.sO2_nonneg A₁ c τ
  have hSu : S ≤ 105 / 100 * (u * G) := by linarith
  have hGb : 2 / ((mA n : ℕ) : ℝ) * normSq (hO A₁ c τ) = Γ - S := by
    rw [hΓd, hSd]; unfold sO2 normSq; ring
  have hGb0 : 0 ≤ Γ - S := by
    rw [← hGb]; exact BstLean.Part153.GamBar_nonneg A₁ c τ
  -- `Γ − S ≥ w G`
  have hwG : w * G ≤ Γ - S := by
    have := mul_le_mul_of_nonneg_right hw hG0.le
    nlinarith
  obtain ⟨hi, hrb⟩ := BstLean.Part153.rb_eq hm A₁ c τ
  rw [← hΓd, hGb] at hrb
  obtain ⟨hp1, hp2⟩ := pi_inv_bounds
  -- `κ(r) ≥ …`
  have hr0 : 0 ≤ (Γ - S) / Γ := div_nonneg hGb0 hΓ0.le
  have hr1 : (Γ - S) / Γ ≤ 1 := by rw [div_le_one hΓ0]; linarith
  have hk := kappa_lower_all (by linarith) hr1
  have hk' := mul_le_mul_of_nonneg_left hk hΓ0.le
  have e : Γ * (1 / π + (Γ - S) / Γ / 2 + ((Γ - S) / Γ) ^ 2 / (2 * π)) =
      Γ * (1 / π) + (Γ - S) / 2 + (Γ - S) ^ 2 / Γ * (1 / π) / 2 := by
    field_simp
  rw [e, ← hrb] at hk'
  have hsq : w ^ 2 * G / (1001 / 1000) ≤ (Γ - S) ^ 2 / Γ := by
    rw [div_le_div_iff₀ (by norm_num) hΓ0]
    have h1 : (w * G) ^ 2 ≤ (Γ - S) ^ 2 := pow_le_pow_left₀ (by positivity) hwG 2
    have h2 : w ^ 2 * G * Γ ≤ w ^ 2 * G * (1001 / 1000 * G) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hrbl : κl * G ≤ ∫ A₂, Pb A₁ c τ A₂ ^ 2
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) := by
    refine le_trans ?_ hk'
    have a1 : 999 / 1000 * G * (3183 / 10000) ≤ Γ * (1 / π) :=
      mul_le_mul (by linarith) hp1 (by norm_num) hΓ0.le
    have a2 : w ^ 2 * G / (1001 / 1000) * (3183 / 10000) ≤ (Γ - S) ^ 2 / Γ * (1 / π) :=
      mul_le_mul hsq hp1 (by norm_num) (by positivity)
    have a3 := mul_le_mul_of_nonneg_right hκ hG0.le
    have e3 : (999 / 1000 * (3183 / 10000) + w / 2 +
        w ^ 2 * (3183 / 10000) / (2 * (1001 / 1000))) * G =
        999 / 1000 * G * (3183 / 10000) + w * G / 2 +
          w ^ 2 * G / (1001 / 1000) * (3183 / 10000) / 2 := by ring
    linarith
  obtain ⟨hb1, hb2, hbv⟩ := BstLean.Part154.Pb_var hm A₁ c τ
  simp only [BstLean.Part154.BadPb, Set.mem_ofPred_eq, not_lt] at hPb
  rw [BstLean.Part153.GamS_eq_gO hm, ← hΓd] at hbv hPb
  have ht : 2 / ((mA n : ℕ) : ℝ) ≤ 2 / 16250 ^ 2 := by
    rw [hmA]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hnR 2)
  exact pb_core hG0.le (by positivity) ht hΓ0.le (by linarith) hrbl
    (integral_nonneg fun A₂ => BstLean.Part153.Pb_nonneg A₁ c τ A₂) hbv hPb heo hnum

/-- **A lower bound of the energy of the computed centre** on `GoodC16` and `SScU`, for
`0.46 ≤ θ_in ≤ θhi ≤ 0.55`, with free numbers: `t_A|b|² ≥ γ_A·(eo − 6·10⁻⁵)²`. -/
theorem eb16_lower_gen (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {θhi u w κl eo Elo : ℝ}
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θhi) (hhi : θhi ≤ 55 / 100)
    (hu : 1 - 3183 / 10000 + 31832 / 100000 * (55 / 100 / 16250) - (1 - θhi) / 2 -
      3183 / 10000 / 2 * (1 - θhi) ^ 2 ≤ u)
    (hw0 : 0 < w) (hw : w ≤ 1 - 1 / 1000 - 105 / 100 * u)
    (hκ : κl ≤ 999 / 1000 * (3183 / 10000) + w / 2 + w ^ 2 * (3183 / 10000) / (2 * (1001 / 1000)))
    (heo : 6 / 100000 ≤ eo) (hnum : (eo + 43 / 100000) ^ 2 ≤ κl - 1001 / 1000 * (2 / 16250 ^ 2))
    (hElo : Elo ≤ (eo - 6 / 100000) ^ 2)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * Elo ≤ 2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ1' : thetaC c τ ≤ 55 / 100 := hθ1.trans hhi
  have hρ := rhoC_posP hn1 c hτ
  have hρ2 := rhoC_sqP c τ
  have hP := Pb_lower_gen hn hτ hθ0 hθ1 hhi hu hw0 hw hκ (by linarith) hnum h hU
  obtain ⟨-, -, -, g4, -, -, -, -⟩ := BstLean.Part154.R.GoodC16_centre hn hn1 hτ h
    (BstLean.Part154.R.rhoBar_lt16 hn) (BstLean.Part154.R.eMP_le16 hn hθ0 hθ1') (θlo := 46 / 100) hθ0
  obtain ⟨hε0, hε⟩ := BstLean.Part154.R.epsJ_le16 hn
  have hrn : (127 : ℝ) ≤ √(n : ℝ) := by
    rw [show (127 : ℝ) = √(127 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hrn0 : 0 < √(n : ℝ) := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(2 / ((mA n : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 / ((mA n : ℕ) : ℝ) := by rw [hs]; exact Real.sq_sqrt (by positivity)
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = √(2 / (n : ℝ)) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Real.sqrt_pos.mpr (by positivity)
  have hg2 : g ^ 2 = 2 / (n : ℝ) := by rw [hg]; exact Real.sq_sqrt (by positivity)
  have hX : √(2 / (n : ℝ) / n) = g / √(n : ℝ) := by
    rw [hg, Real.sqrt_div (by positivity)]
  rw [← hs, hX] at g4
  have hPd : Pb A₁ c τ A₂ = s * nrm (bO A₁ A₂ c τ) := by rw [hs]; rfl
  have hGs : √(2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) = g * rhoC c τ := by
    rw [← hρ2, Real.sqrt_mul (by positivity), Real.sqrt_sq hρ.le, hg]
  rw [hPd, hGs] at hP
  obtain ⟨bo, hbo⟩ : ∃ bo, bo = bO A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨bt, hbt⟩ : ∃ bt, bt = bT n n A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = rhoC c τ := ⟨_, rfl⟩
  rw [← hbo, ← hbt, ← hρd] at g4
  rw [← hbo, ← hρd] at hP
  rw [← hbt, ← hρd]
  rw [← hρd] at hρ
  have hρi : 0 < 1 / ρ := by positivity
  have h1 : g * eo ≤ s * nrm ((1 / ρ) • bo) := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos hρi]
    have e : s * (1 / ρ * nrm bo) = s * nrm bo / ρ := by ring
    rw [e, le_div_iff₀ hρ]
    linarith
  have h2 : s * nrm ((1 / ρ) • bt - (1 / ρ) • bo) ≤ g * (6 / 100000) := by
    have e' : (1 / ρ) • bt - (1 / ρ) • bo = (1 / ρ) • (bt - bo) := by rw [smul_sub]
    rw [e', BstLean.Part153.nrm_smul, abs_of_pos hρi]
    have e2 : s * (1 / ρ * nrm (bt - bo)) = s * nrm (bt - bo) / ρ := by ring
    rw [e2]
    refine g4.trans ?_
    have h3 : BstLean.Part150.epsJ n n n (BstLean.Part153.wn n) csC (11 / 1000)
        (BstLean.Part154.deltaChi n 12) * (g / √(n : ℝ)) ≤ 752 / 100000 * (g / √(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hε (by positivity)
    refine h3.trans ?_
    rw [show (752 : ℝ) / 100000 * (g / √(n : ℝ)) = g * (752 / 100000 / √(n : ℝ)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hg0.le
    rw [div_le_iff₀ hrn0]
    linarith
  have h3 : g * (eo - 6 / 100000) ≤ s * nrm ((1 / ρ) • bt) := by
    have e' : (1 / ρ) • bo = (1 / ρ) • bt + ((1 / ρ) • bo - (1 / ρ) • bt) := by abel
    have h4 := BstLean.Part153.nrm_add_le ((1 / ρ) • bt) ((1 / ρ) • bo - (1 / ρ) • bt)
    rw [← e'] at h4
    have e'' : nrm ((1 / ρ) • bo - (1 / ρ) • bt) = nrm ((1 / ρ) • bt - (1 / ρ) • bo) := by
      unfold nrm normSq
      congr 1
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
    rw [e''] at h4
    have h5 := mul_le_mul_of_nonneg_left h4 hs0
    linarith
  have h4 := pow_le_pow_left₀ (mul_nonneg hg0.le (by linarith)) h3 2
  rw [mul_pow, mul_pow, hs2, BstLean.Part153.nrm_sq, hg2] at h4
  refine le_trans (mul_le_mul_of_nonneg_left hElo (by positivity)) ?_
  exact h4

/-- `t_A|b|² ≥ 0.6425·γ_A` on `GoodC16` and `SScU` for `0.46 ≤ θ_in ≤ 0.55`. -/
theorem eb16_lower (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 23 / 50 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 11 / 20)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (257 / 400) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 11 / 20) (u := 424483 / 1000000) (w := 138323 / 250000) (κl := 643299 / 1000000)
    (eo := 801629 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6802·γ_A` on `GoodC16` and `SScU` for `46/100 ≤ θ_in ≤ 47/100`. -/
theorem eb16_lower_46 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 23 / 50 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 47 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (3401 / 5000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 47 / 100) (u := 186003 / 500000) (w := 608393 / 1000000) (κl := 681027 / 1000000)
    (eo := 824813 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6753·γ_A` on `GoodC16` and `SScU` for `47/100 ≤ θ_in ≤ 48/100`. -/
theorem eb16_lower_47 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 12 / 25)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (6753 / 10000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 12 / 25) (u := 378677 / 1000000) (w := 601389 / 1000000) (κl := 338089 / 500000)
    (eo := 82187 / 100000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6705·γ_A` on `GoodC16` and `SScU` for `48/100 ≤ θ_in ≤ 49/100`. -/
theorem eb16_lower_48 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 12 / 25 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 49 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (1341 / 2000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 49 / 100) (u := 96329 / 250000) (w := 297209 / 500000) (κl := 671367 / 1000000)
    (eo := 818939 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6657·γ_A` on `GoodC16` and `SScU` for `49/100 ≤ θ_in ≤ 50/100`. -/
theorem eb16_lower_49 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 1 / 2)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (6657 / 10000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 1 / 2) (u := 97981 / 250000) (w := 587479 / 1000000) (κl := 333297 / 500000)
    (eo := 816021 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.661·γ_A` on `GoodC16` and `SScU` for `50/100 ≤ θ_in ≤ 51/100`. -/
theorem eb16_lower_50 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 1 / 2 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 51 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (661 / 1000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 51 / 100) (u := 398499 / 1000000) (w := 18143 / 31250) (κl := 33093 / 50000)
    (eo := 813117 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6563·γ_A` on `GoodC16` and `SScU` for `51/100 ≤ θ_in ≤ 52/100`. -/
theorem eb16_lower_51 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 13 / 25)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (6563 / 10000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 13 / 25) (u := 405043 / 1000000) (w := 71713 / 125000) (κl := 657163 / 1000000)
    (eo := 32409 / 40000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6517·γ_A` on `GoodC16` and `SScU` for `52/100 ≤ θ_in ≤ 53/100`. -/
theorem eb16_lower_52 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 13 / 25 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 53 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (6517 / 10000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 53 / 100) (u := 82311 / 200000) (w := 566867 / 1000000) (κl := 130501 / 200000)
    (eo := 807347 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.647·γ_A` on `GoodC16` and `SScU` for `53/100 ≤ θ_in ≤ 54/100`. -/
theorem eb16_lower_53 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 53 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 27 / 50)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (647 / 1000) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 27 / 50) (u := 83607 / 200000) (w := 560063 / 1000000) (κl := 647883 / 1000000)
    (eo := 804481 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

/-- `t_A|b|² ≥ 0.6425·γ_A` on `GoodC16` and `SScU` for `54/100 ≤ θ_in ≤ 55/100`. -/
theorem eb16_lower_54 (hn : 16250 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 27 / 50 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 11 / 20)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hU : ((c, τ), (A₁, A₂)) ∈ SScU n) :
    2 / (n : ℝ) * (257 / 400) ≤
      2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) :=
  eb16_lower_gen hn hτ (θhi := 11 / 20) (u := 424483 / 1000000) (w := 138323 / 250000) (κl := 643299 / 1000000)
    (eo := 801629 / 1000000) (le_trans (by norm_num) hθ0) hθ1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h hU

end BstLean.Part160.R

