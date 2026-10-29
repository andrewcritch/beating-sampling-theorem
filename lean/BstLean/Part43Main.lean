import BstLean.Part43Surr
import BstLean.Part43Mass
import BstLean.Part43Error
import BstLean.Part43Norm
import BstLean.Part43Upper
import BstLean.Part43Floor
import BstLean.Part43SmallBall
import BstLean.Part43MomProg
import BstLean.Part43GProg
import BstLean.Part43Budget
import BstLean.Part41Main
import BstLean.Part40Sign
import BstLean.Part36Index

/-!
# Part 43, wave 2: the failure bound and the per-case cost of Theorem G

Paper: the proof of Theorem G in `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`.
Specification: `delegations/answers/p43-spec-opus.md`. Proved here from the wave-1 statements.

* `kept43_exists`: Lemma `tail for Q̃` (Part 41's `tail_le`, `mass43`, `HR_nonneg`, `HR_symm`).
* `EV_lower`: Lemmas F and F′ give `E_Z Var_D 𝒫 ≥ 𝒩(f)/K_c`.
* `fail43`: on `E₁ ∩ E₂ ∩ E₃` (`radius_event`, `smallball43`, `upper_event43`), `norm_det43` and
  `radius_det` give `sd_D f(Mφ) ≥ γ √𝒩`; `surr_bias` moves the target to `B_Q̃`; Markov on the error
  (`errE43`, `errT43`) closes.
* `cost43`: `gProg43_exists`, `alloc43_le`, `budget43_le`.

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part43

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD rhoD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT mset wordOf Tens TSymm fval varU sdU
  levels cQ kapQ muQ aT Nn uJ Pcal r2 rhoZ cS Bfix Pn epsS baseline thetaT rhoBar Kc GamP etaR etaK Lk
  orbSize heavyCount bQ In41)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

/-- At an argmin, the program's shift is `θ − min θ`. -/
theorem bsh_eq_bmin (θ : Fin n → ℝ) (i0 : Fin n) (h : ∀ j, θ i0 ≤ θ j) :
    BstLean.Part42.bsh θ i0 = bmin θ := by
  have : Nonempty (Fin n) := ⟨i0⟩
  have hinf : (⨅ j, θ j) = θ i0 :=
    le_antisymm (ciInf_le (Set.finite_range θ).bddBelow i0) (le_ciInf h)
  funext i
  simp only [BstLean.Part42.bsh, bmin, hinf]

/-- **Lemma `tail for Q̃`**: an admissible kept set exists at every level, for every sign-symmetric law. -/
theorem kept43_exists (hn : 1 ≤ n) (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) (k : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hτ : 0 < tau43 n d k) (j l : ℕ) (hjl : (j, l) ∈ levels k) :
    ∃ K, KeepOK43 n d k μ ε j l K := by
  classical
  have hjl' : 2 * l < j := (Finset.mem_filter.mp hjl).2
  set s := j - 2 * l with hs
  have hs1 : 1 ≤ s := by omega
  set X : ℝ := Upp j d ^ 2 * (n : ℝ) ^ (k - s) / (4 * (s : ℕ) * 4 ^ l * tau43 n d k * epsS ε) with hX
  have heps : 0 < epsS ε := lt_min (by positivity) (by norm_num)
  have hU := Upp_one j d
  have hs0 : (0 : ℝ) < (s : ℕ) := by exact_mod_cast hs1
  have hcardpos : 1 ≤ Fintype.card (Sym (Mono n d) s) := Fintype.card_pos
  -- the residual of a kept set is the masked tensor of `tail_le`
  have hRR : ∀ K : Finset (Multiset (Mono n d)),
      (fun w : Fin s → Mono n d => RR μ K l w) = fun w => if mset w ∈ K then 0 else HR μ l w := by
    intro K; funext w; unfold RR HKR; split_ifs <;> ring
  have hH0 : ∀ w : Fin s → Mono n d, 0 ≤ HR μ l w := fun w => HR_nonneg hμ l w
  have hmass : (∑ w : Fin s → Mono n d, HR μ l w) ≤ Upp j d := by
    have := mass43 hd hμ j l hjl'
    unfold massR at this
    calc (∑ w : Fin s → Mono n d, HR μ l w) = ∑ w : Fin s → Mono n d, |HR μ l w| :=
          Finset.sum_congr rfl fun w _ => (abs_of_nonneg (hH0 w)).symm
      _ ≤ Upp j d := this
  have hsum0 : 0 ≤ ∑ w : Fin s → Mono n d, HR μ l w := Finset.sum_nonneg fun w _ => hH0 w
  · have hnpos : (0 : ℝ) < (n : ℝ) ^ (k - s) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hXpos : 0 < X := by rw [hX]; positivity
    have hO1 : 1 ≤ Ocnt43 n d k ε j l := by
      unfold Ocnt43
      exact le_min hcardpos (Nat.one_le_iff_ne_zero.mpr fun h0 => by
        rw [Nat.ceil_eq_zero] at h0; rw [← hs] at h0; linarith)
    obtain ⟨K, hKc, hKs, hKt, hK0⟩ := BstLean.Part41.tail_le (fun w : Fin s → Mono n d => HR μ l w) hH0
      (HR_symm μ l) (Ocnt43 n d k ε j l) hO1
    refine ⟨K, hKc, hKs, ?_⟩
    rw [hRR K]
    have hRHS : 0 ≤ tau43 n d k * epsS ε * (s : ℕ) * 4 ^ l / (n : ℝ) ^ (k - s) := by positivity
    by_cases hall : Fintype.card (Sym (Mono n d) s) ≤ Ocnt43 n d k ε j l
    · rw [hK0 hall]; exact hRHS
    · -- the quota is the ceiling
      have hO : Ocnt43 n d k ε j l = ⌈X⌉₊ := by
        unfold Ocnt43; rw [← hs]
        have : ⌈X⌉₊ < Fintype.card (Sym (Mono n d) s) := by
          by_contra hc; push Not at hc; apply hall; unfold Ocnt43; rw [← hs]; exact le_min le_rfl hc
        rw [hX] at this ⊢; exact min_eq_right this.le
      have hXO : X ≤ (Ocnt43 n d k ε j l : ℝ) := by rw [hO]; exact Nat.le_ceil X
      calc frob (fun w : Fin s → Mono n d => if mset w ∈ K then 0 else HR μ l w)
          ≤ (∑ w, HR μ l w) ^ 2 / (4 * (Ocnt43 n d k ε j l : ℝ)) := hKt
        _ ≤ Upp j d ^ 2 / (4 * X) := by
            apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hsum0 hmass 2) (by positivity)
            linarith
        _ = tau43 n d k * epsS ε * (s : ℕ) * 4 ^ l / (n : ℝ) ^ (k - s) := by
            rw [hX]; field_simp
        _ ≤ _ := le_rfl

/-- **Lemmas F and F′**: `E_Z Var_μ 𝒫 ≥ 𝒩(f)/K_c` for every sign-symmetric law on the sphere. -/
theorem EV_lower (hn : 1 ≤ n) (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) (k : ℕ)
    (T : Tens n) (hT : TSymm k T) (η : ℝ) (hη : 0 < η) (hθ : (1 + 1 / η) * thetaT n d k < 1)
    (hKc : 0 < Kc n d k η) :
    Nn n d k T ≤ Kc n d k η * ∫ Z, varU μ (Pcal k T Z) ∂stdGauss (CoefIdxD n d) := by
  obtain ⟨-, hint, hF⟩ := floorF43 hn hd hμ k T hT
  have := hμ.sph.prob
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpt : ∀ᵐ x ∂μ, Nn n d k T ≤ Kc n d k η *
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bq n d k T s (phiSq d x)) := by
    filter_upwards [hμ.sph.sphere] with x hx
    obtain ⟨h2, h3⟩ := phiSq_bounds hd x hx
    refine (cascade43 hn k T η hη hθ (phiSq d x) (by linarith) h3).trans ?_
    apply mul_le_mul_of_nonneg_left _ hKc.le
    apply Finset.sum_le_sum; intro s _
    have h0 : 0 ≤ (s.factorial : ℝ) * s * frob (bq n d k T s (phiSq d x)) := by
      have : 0 ≤ frob (bq n d k T s (phiSq d x)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    exact div_le_self h0 (one_le_pow₀ hn1)
  have hI : Integrable (fun x => Kc n d k η *
      ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bq n d k T s (phiSq d x))) μ :=
    (integrable_finsetSum _ fun s _ => (hint s).const_mul _).const_mul _
  calc Nn n d k T = ∫ _x, Nn n d k T ∂μ := by simp
    _ ≤ ∫ x, Kc n d k η * ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * frob (bq n d k T s (phiSq d x)) ∂μ :=
        integral_mono_ae (integrable_const _) hI hpt
    _ = Kc n d k η * ∑ s ∈ Finset.Icc 1 k, (s.factorial : ℝ) * s * ∫ x, frob (bq n d k T s (phiSq d x)) ∂μ := by
        rw [integral_const_mul, integral_finsetSum _ fun s _ => (hint s).const_mul _]
        congr 1; apply Finset.sum_congr rfl; intro s _; rw [integral_const_mul]
    _ ≤ Kc n d k η * ∫ Z, varU μ (Pcal k T Z) ∂stdGauss (CoefIdxD n d) :=
        mul_le_mul_of_nonneg_left hF hKc.le

/-- The kept sets of the surrogate satisfy `KeepOK43` at every level. -/
theorem keepSet43_ok (hn : 1 ≤ n) (hd : 1 ≤ d) {μ : Measure (Fin n → ℝ)} (hμ : SignSym n μ) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) (hτ : 0 < tau43 n d k) :
    ∀ jl ∈ levels k, KeepOK43 n d k μ ε jl.1 jl.2 (keepSet43 n d k μ ε jl.1 jl.2) := fun jl hjl =>
  Classical.epsilon_spec (kept43_exists hn hd hμ k ε hε hτ jl.1 jl.2 hjl)

set_option maxHeartbeats 1000000 in
/-- **The failure bound** of Theorem G: `Pr{fail} ≤ Φ43(n)` under `BudgetOK43`, for every `θ`. -/
theorem fail43 (hFr : FradeliziGauss) (k : ℕ) (hk : 2 ≤ k) (q : Params43) (hB : BudgetOK43 n d k q)
    (θ : Fin n → ℝ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) (hTk : 0 < frob (T k)) (ε : ℝ) (hε : 0 < ε) :
    stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧ ε ^ 2 * varFQ (BstLean.Part37.bingham n θ) k f0 T (unitOfD Z) <
      (BofQ (BstLean.Part37.bingham n θ) k f0 T (unitOfD Z) - gOf43 k θ ε f0 T (unitOfD Z)) ^ 2} ≤
      ENNReal.ofReal (Phi43 n d k q) := by
  obtain ⟨hn2, hd, hτ, hp0, hp1, hx, hβ, heta, hθ, hηr, hKc, hγ, -, -⟩ := hB
  have hn : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  set D := BstLean.Part37.bingham n θ with hDdef
  have hD : SignSym n D := BstLean.Part40.bingham_signSym hn θ
  set Q := surrT n θ ε with hQdef
  have hQ : SignSym n Q := surr_signSym hn θ ε
  set Kset := keepSet43 n d k Q ε with hKset
  have hKOK := keepSet43_ok hn hd hQ k ε hε hτ
  have hNn : 0 < Nn n d k T := BstLean.Part41.Nn_pos hn k hk1 T hTk
  set γ := gam43 n d k q with hγdef
  have hxi : (0 : ℝ) < 1 - xi43 := by unfold xi43; norm_num
  set E1 := {Z : CoefIdxD n d → ℝ | etaR n d q.x < |r2 Z / DD n d - 1|}
  set EV := ∫ Z, varU D (Pcal k T Z) ∂stdGauss (CoefIdxD n d) with hEV
  set E2 := {Z : CoefIdxD n d → ℝ | varU D (Pcal k T Z) < tsb k q.psb * EV}
  set E3 := {Z : CoefIdxD n d → ℝ | Real.sqrt (GamP n d k * Nn n d k T / q.beta) < upperSumQ D k T Z}
  set t := ((1 - xi43) * ε * γ) ^ 2 * Nn n d k T with ht
  have ht0 : 0 < t := by positivity
  set E4 := {Z : CoefIdxD n d → ℝ | t < (BofQ Q k f0 T (unitOfD Z) - gTCR Q k Kset f0 T (unitOfD Z)) ^ 2}
  have hEVl := EV_lower hn hd hD k T hT q.eta heta hθ hKc
  have hek0 : 0 ≤ etaK n d k q.x := by
    have he0 : 0 ≤ etaR n d q.x := by
      unfold etaR; have : (0 : ℝ) ≤ DD n d := Nat.cast_nonneg _
      positivity
    have hpos : 0 < (1 - etaR n d q.x) ^ k := pow_pos (by linarith) k
    have hle : (1 - etaR n d q.x) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hs0 : 0 < Real.sqrt ((1 - etaR n d q.x) ^ k) := Real.sqrt_pos.mpr hpos
    have hs1 : Real.sqrt ((1 - etaR n d q.x) ^ k) ≤ 1 := Real.sqrt_le_one.mpr hle
    unfold etaK
    have : 1 ≤ 1 / Real.sqrt ((1 - etaR n d q.x) ^ k) := by rw [le_div_iff₀ hs0]; linarith
    linarith
  have htsb : 0 ≤ tsb k q.psb := by
    by_contra hneg; push Not at hneg
    have h1 : Real.sqrt (tsb k q.psb / Kc n d k q.eta) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hneg.le hKc.le)
    have h2 : 0 ≤ etaK n d k q.x * Real.sqrt (GamP n d k / q.beta) := mul_nonneg hek0 (Real.sqrt_nonneg _)
    have h3 := hγ
    rw [hγdef] at h3; unfold gam43 at h3; rw [h1] at h3
    linarith
  have hsub : {Z : CoefIdxD n d → ℝ | Z ≠ 0 ∧ ε ^ 2 * varFQ D k f0 T (unitOfD Z) <
      (BofQ D k f0 T (unitOfD Z) - gOf43 k θ ε f0 T (unitOfD Z)) ^ 2} ⊆ E1 ∪ E2 ∪ E3 ∪ E4 := by
    intro Z ⟨hZ0, hZf⟩
    by_contra hcon
    simp only [E1, E2, E3, E4, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    have hnd := norm_det43 (d := d) hn hD.sph k f0 T Z hZ0
    have hrad : ∀ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| ≤ etaK n d k q.x := fun j hj =>
      BstLean.Part41.radius_det hn k q.x hx hηr Z h1 j (Finset.mem_Icc.mp hj).2
    have hek : 0 ≤ etaK n d k q.x := by
      have := BstLean.Part41.radius_det hn k q.x hx hηr Z h1 0 (Nat.zero_le _); simpa using this
    have hsum : ∑ j ∈ Finset.Icc 1 k, |rhoZ Z ^ j - 1| *
        (sdU D (uJ T j Z) / Real.sqrt (DD n d) ^ j) ≤ etaK n d k q.x * upperSumQ D k T Z := by
      unfold upperSumQ; rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hrad j hj)
        (div_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hV : tsb k q.psb * (Nn n d k T / Kc n d k q.eta) ≤ varU D (Pcal k T Z) := by
      refine le_trans ?_ h2
      apply mul_le_mul_of_nonneg_left _ htsb
      rw [div_le_iff₀ hKc]; linarith
    have hsdP : Real.sqrt (tsb k q.psb / Kc n d k q.eta) * Real.sqrt (Nn n d k T) ≤ sdU D (Pcal k T Z) := by
      unfold sdU
      rw [← Real.sqrt_mul (div_nonneg htsb hKc.le)]
      apply Real.sqrt_le_sqrt
      calc tsb k q.psb / Kc n d k q.eta * Nn n d k T = tsb k q.psb * (Nn n d k T / Kc n d k q.eta) := by ring
        _ ≤ _ := hV
    have hup : etaK n d k q.x * upperSumQ D k T Z ≤
        etaK n d k q.x * (Real.sqrt (GamP n d k / q.beta) * Real.sqrt (Nn n d k T)) := by
      apply mul_le_mul_of_nonneg_left _ hek
      have heq : Real.sqrt (GamP n d k * Nn n d k T / q.beta) =
          Real.sqrt (GamP n d k / q.beta) * Real.sqrt (Nn n d k T) := by
        rw [← Real.sqrt_mul' _ hNn.le]; congr 1; ring
      rw [← heq]; exact h3
    have hsdf : γ * Real.sqrt (Nn n d k T) ≤ Real.sqrt (varFQ D k f0 T (unitOfD Z)) := by
      rw [hγdef]; unfold gam43; nlinarith
    -- the bias of the surrogate
    have hbias := surr_bias hn θ ε hε k f0 T (unitOfD Z)
    rw [← hDdef, ← hQdef] at hbias
    have hetaQ : etaQ ε ≤ xi43 * ε := min_le_left _ _
    set S := Real.sqrt (varFQ D k f0 T (unitOfD Z)) with hS
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hvarS : varFQ D k f0 T (unitOfD Z) = S ^ 2 := by
        rw [hS, Real.sq_sqrt]; unfold varFQ varU; exact integral_nonneg fun _ => sq_nonneg _
    have hg : gOf43 k θ ε f0 T (unitOfD Z) = gTCR Q k Kset f0 T (unitOfD Z) := rfl
    rw [hg] at hZf
    set a := BofQ D k f0 T (unitOfD Z) - gTCR Q k Kset f0 T (unitOfD Z)
    set b := BofQ Q k f0 T (unitOfD Z) - gTCR Q k Kset f0 T (unitOfD Z)
    have hab : |a| ≤ |b| + xi43 * ε * S := by
      have : a = b + (BofQ D k f0 T (unitOfD Z) - BofQ Q k f0 T (unitOfD Z)) := by ring
      rw [this]
      refine (abs_add_le _ _).trans (add_le_add le_rfl (hbias.trans ?_))
      exact mul_le_mul_of_nonneg_right hetaQ hS0
    have hfa : ε * S < |a| := by
      have h' : (ε * S) ^ 2 < a ^ 2 := by rw [mul_pow, ← hvarS]; exact hZf
      by_contra hc; push Not at hc
      have := pow_le_pow_left₀ (abs_nonneg a) hc 2
      rw [sq_abs] at this; linarith
    have hb : (1 - xi43) * ε * γ * Real.sqrt (Nn n d k T) < |b| := by
      have h5 : (1 - xi43) * ε * (γ * Real.sqrt (Nn n d k T)) ≤ (1 - xi43) * ε * S :=
        mul_le_mul_of_nonneg_left hsdf (by positivity)
      linarith
    have : t < b ^ 2 := by
      have h0 : 0 ≤ (1 - xi43) * ε * γ * Real.sqrt (Nn n d k T) := by positivity
      have := pow_lt_pow_left₀ hb h0 (by norm_num : (2 : ℕ) ≠ 0)
      rw [sq_abs, mul_pow, Real.sq_sqrt hNn.le] at this
      rw [ht]; linarith
    linarith
  -- the error term
  obtain ⟨hEint, hEle⟩ := errE43 hn hd hQ.sph k Kset f0 T hT
  have hT2 := errT43 hn Q k Kset T ε (tau43 n d k) hτ.le (fun jl hjl => (hKOK jl hjl).2.2)
  have herr : stdGauss (CoefIdxD n d) E4 ≤
      ENNReal.ofReal (Lk k * tau43 n d k / ((1 - xi43) ^ 2 * γ ^ 2)) := by
    refine (BstLean.Part41.markov_lt _ _ hEint (fun Z => sq_nonneg _) t ht0).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_div_iff₀ ht0 (by positivity)]
    have hes : epsS ε ≤ ε ^ 2 := min_le_left _ _
    have h1 := hEle.trans hT2
    have hL : (0 : ℝ) ≤ Lk k * tau43 n d k := by positivity
    have h2 : Lk k * tau43 n d k * epsS ε * Nn n d k T ≤ Lk k * tau43 n d k * ε ^ 2 * Nn n d k T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hes hL) hNn.le
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity : (0 : ℝ) ≤ (1 - xi43) ^ 2 * γ ^ 2)
    calc _ ≤ Lk k * tau43 n d k * ε ^ 2 * Nn n d k T * ((1 - xi43) ^ 2 * γ ^ 2) := h3
      _ = Lk k * tau43 n d k * t := by rw [ht]; ring
  have hm1 : stdGauss (CoefIdxD n d) E1 ≤ ENNReal.ofReal (2 * Real.exp (-q.x)) :=
    BstLean.Part41.radius_event hn q.x hx
  have hm2 : stdGauss (CoefIdxD n d) E2 ≤ ENNReal.ofReal q.psb :=
    smallball43 hFr hn hd hD.sph k hk1 T q.psb hp0 hp1
  have hm3 : stdGauss (CoefIdxD n d) E3 ≤ ENNReal.ofReal q.beta := upper_event43 hn hd hD.sph k T hT q.beta hβ
  calc stdGauss (CoefIdxD n d) _ ≤ stdGauss (CoefIdxD n d) (E1 ∪ E2 ∪ E3 ∪ E4) := measure_mono hsub
    _ ≤ stdGauss (CoefIdxD n d) E1 + stdGauss (CoefIdxD n d) E2 + stdGauss (CoefIdxD n d) E3 +
        stdGauss (CoefIdxD n d) E4 := by
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-q.x)) + ENNReal.ofReal q.psb + ENNReal.ofReal q.beta +
        ENNReal.ofReal (Lk k * tau43 n d k / ((1 - xi43) ^ 2 * γ ^ 2)) := by gcongr
    _ = ENNReal.ofReal (Phi43 n d k q) := by
      rw [← ENNReal.ofReal_add (by positivity) hp0.le, ← ENNReal.ofReal_add (by positivity) hβ.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      unfold Phi43; congr 1; rw [← hγdef]; ring

/-- **The per-case program** of Theorem G: constants `0` and `1` only, the specification `GSpec43`,
and cost at most `(1 − ν) 𝔅(ε) − 1`. -/
theorem cost43 (k : ℕ) (hk : 2 ≤ k) (q : Params43) (hB : BudgetOK43 n d k q) (θ : Fin n → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ pg : Prog (In43 n d k) Unit, heavyCount pg = 0 ∧ GSpec43 pg (keepSet43 n d k (surrT n θ ε) ε) ∧
      (pg.cost : ℝ) ≤ (1 - nu43) * baseline n d ε - 1 := by
  obtain ⟨hn2, hd, hτ, -, -, -, -, -, -, -, -, -, hP, -⟩ := hB
  have hn : 1 ≤ n := by omega
  have hQ : SignSym n (surrT n θ ε) := surr_signSym hn θ ε
  have hKOK := keepSet43_ok hn hd hQ k ε hε hτ
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := gProg43_exists hn2 k (keepSet43 n d k (surrT n θ ε) ε)
    (fun jl hjl => (hKOK jl hjl).2.1)
  refine ⟨pg, hpg0, hpgs, ?_⟩
  have hc3 : ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * ((keepSet43 n d k (surrT n θ ε) ε jl.1 jl.2).card : ℝ) ≤
      ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) * (Ocnt43 n d k ε jl.1 jl.2 : ℝ) :=
    Finset.sum_le_sum fun jl hjl => mul_le_mul_of_nonneg_left (by exact_mod_cast (hKOK jl hjl).1)
      (BstLean.Part41.cS_nonneg hn2 _)
  have hc4 := alloc43_le hn2 k ε hε hτ
  have hc5 := budget43_le (d := d) hn2 k ε hε hP
  have hk3 : (0 : ℝ) ≤ (k : ℝ) ^ 3 * (n + 5) := by positivity
  have hB' : Bfix n k = 1 + ∑ jl ∈ levels k, cS n (jl.1 - 2 * jl.2) +
      ∑ j ∈ Finset.Icc 1 k, ∑ m ∈ Finset.Icc 1 (j / 2), (n : ℝ) ^ (j - 2 * m) * ((n : ℝ) ^ m - 1) +
      (k : ℝ) ^ 3 * (n + 5) + k * (n + 3) := rfl
  unfold gCost43 at hpgc
  linarith

end BstLean.Part43
