import BstLean.Part43Defs
import BstLean.Part37Series
import BstLean.Part41Consts
import BstLean.Part36Index
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Finsupp.Interval

/-!
# Part 43, wave 1: the one-time moment program (Lemmas ring, one-time cost)

Paper: `proofs/option-m/43-arbitrary-degree-every-diagonal-bingham.tex`. Specification:
`delegations/answers/p43-spec-opus.md`. Replace each `sorry` by a proof. Do not edit the statements.
Do not use `native_decide` or `axiom` anywhere.

Suggested route.
* `b' = θ' − θ'_{i0}` costs `n` subtractions; at an argmin `i0`, `b' ≥ 0`, `taylorExp ≥ 1`, `Z_K ≥ 1`.
* Every needed value `H^{Q̃}[w]` is `v(β, l) = N^{(K)}_{β,l}(b')/N^{(K)}_{0,0}(b')` (`2β` the exponent
  sum of `w`, `0` if odd). Compute the numerators by the truncated ring
  `ℚ[t, z_1, …, z_{⌊k/2⌋}]/(t^{K+1}, z_r^{d+1})` (dimension `deltaR`), the Gaussian lift
  `E_σ[u^α (b·u)^t] = ω_{|α|+t} E[g^{2α}(Σ bᵢgᵢ²)^t]` and the per-coordinate series
  `E[g^{2a} e^{t bᵢ g²} ∏_r (1 − z_r g²)^{−1}]`; one shared product, then one adjustment per value
  (the paper's `C_sh + Q_v V_once`). Build every rational constant from `1`
  (`Part41Consts.inline_consts`, `bR` bits for the ring constants).
* The weights: for each key, `κ μ |orbit q|` (height `< 2^{bQ}`) times
  `Σ_{o ∈ K} cnt(o, q) v(o)`, with `cnt ≤ k!` the number of words `c` with `2·mset c + q = o`; each kept
  orbit contributes to at most `2^s` keys.
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

/-! ## The shift and the normalization denominator -/

private lemma bsh_nonneg (θ : Fin n → ℝ) (i0 : Fin n)
    (hmin : ∀ j, θ i0 ≤ θ j) (j : Fin n) :
    0 ≤ BstLean.Part42.bsh θ i0 j :=
  sub_nonneg.mpr (hmin j)

private lemma qth_nonneg (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (x : Fin n → ℝ) : 0 ≤ BstLean.Part37.qth b x := by
  unfold BstLean.Part37.qth
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)

private lemma taylorExp_one_le (K : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    1 ≤ BstLean.Part37.taylorExp K s := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (K + 1)) =>
      div_nonneg (pow_nonneg hs j) (Nat.cast_nonneg j.factorial))
    (Finset.mem_range.mpr (show 0 < K + 1 by omega))
  simpa [BstLean.Part37.taylorExp] using h

private lemma sphere_cont_integrable (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma ZK_one_le (hn : 1 ≤ n) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (K : ℕ) : 1 ≤ BstLean.Part37.ZK n K b := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hi : Integrable (fun x => BstLean.Part37.taylorExp K (BstLean.Part37.qth b x))
      (uniformSphere n) := sphere_cont_integrable hn (by
    unfold BstLean.Part37.taylorExp BstLean.Part37.qth
    fun_prop)
  simpa [BstLean.Part37.ZK] using
    integral_mono (integrable_const (1 : ℝ)) hi
      (fun x => taylorExp_one_le K _ (qth_nonneg b hb x))

private lemma numK_nil_pos (hn : 1 ≤ n) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (K : ℕ) : 0 < BstLean.Part37.numK n K b [] := by
  rw [← BstLean.Part37.ZK_eq hn b K]
  exact lt_of_lt_of_le zero_lt_one (ZK_one_le hn b hb K)

private lemma integral_binghamK_nonneg (hn : 1 ≤ n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (K : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂BstLean.Part37.binghamK n K b) =
      (∫ x, f x * BstLean.Part37.taylorExp K (BstLean.Part37.qth b x)
        ∂uniformSphere n) / BstLean.Part37.ZK n K b := by
  have hz : 0 ≤ BstLean.Part37.ZK n K b := (ZK_one_le hn b hb K).trans' zero_le_one
  have hw : Continuous (fun x =>
      BstLean.Part37.taylorExp K (BstLean.Part37.qth b x) / BstLean.Part37.ZK n K b) := by
    unfold BstLean.Part37.taylorExp BstLean.Part37.qth
    fun_prop
  rw [BstLean.Part37.binghamK, integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal (by simp)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg
    (zero_le_one.trans (taylorExp_one_le K _ (qth_nonneg b hb _))) hz),
    smul_eq_mul, mul_comm _ (f _), ← mul_div_assoc]
  exact integral_div _ _

private lemma binghamK_wmono_nonneg (hn : 1 ≤ n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (K : ℕ) (w : List (Fin n)) :
    (∫ x, BstLean.Part37.wmono w x ∂BstLean.Part37.binghamK n K b) =
      BstLean.Part37.momK n K b w := by
  rw [integral_binghamK_nonneg hn b hb K, BstLean.Part37.numK_eq hn b K w,
    BstLean.Part37.ZK_eq hn b K]
  rfl

private lemma binghamK_odd_nonneg (hn : 1 ≤ n) (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (K r : ℕ) (τ : Fin r → Fin n)
    (ho : ∃ i, Odd (Finset.univ.filter fun s => τ s = i).card) :
    (∫ x, (∏ s, x (τ s)) ∂BstLean.Part37.binghamK n K b) = 0 := by
  classical
  rw [integral_binghamK_nonneg hn b hb K]
  have he : (fun x : Fin n → ℝ =>
      (∏ s, x (τ s)) * BstLean.Part37.taylorExp K (BstLean.Part37.qth b x)) =
      fun x => ∑ j ∈ Finset.range (K + 1),
        ((∏ s, x (τ s)) * BstLean.Part37.qth b x ^ j) / (j.factorial : ℝ) := by
    funext x
    simp [BstLean.Part37.taylorExp, Finset.mul_sum, mul_div_assoc]
  rw [he, integral_finsetSum]
  · simp_rw [integral_div, BstLean.Part37.sphere_odd_moment hn b r τ _ ho]
    simp
  · intro j _
    exact (BstLean.Part37.mono_qpow_integrable hn b r τ j).div_const _

/-! ## Composition with only the constants zero and one -/

private def Clean {ι κ : Type} (p : Prog ι κ) : Prop :=
  (∀ I ∈ p.body, BstLean.Part41.argHeavy I.a = 0 ∧ BstLean.Part41.argHeavy I.b = 0) ∧
    ∀ o, BstLean.Part41.argHeavy (p.out o) = 0

private lemma heavy_rename {ι κ : Type} (f : ι → κ) (a : Arg ι) :
    BstLean.Part41.argHeavy (a.rename f) = BstLean.Part41.argHeavy a := by
  cases a <;> rfl

private lemma heavy_clamp {ι : Type} (s : ℕ) (a : Arg ι)
    (h : BstLean.Part41.argHeavy a = 0) : BstLean.Part41.argHeavy (a.clamp s) = 0 := by
  cases a <;> simp_all [Arg.clamp, BstLean.Part41.argHeavy]
  split_ifs <;> rfl

private lemma heavy_subst {ι κ : Type} (f : ι → Arg κ) (s l : ℕ)
    (hf : ∀ i, BstLean.Part41.argHeavy (f i) = 0) (a : Arg ι)
    (h : BstLean.Part41.argHeavy a = 0) :
    BstLean.Part41.argHeavy (a.subst f s l) = 0 := by
  cases a <;> simp_all [Arg.subst, BstLean.Part41.argHeavy]
  split_ifs <;> rfl

private lemma clean_bind {ι κ ν : Type} {p : Prog ι κ} {q : Prog (ι ⊕ κ) ν}
    (hp : Clean p) (hq : Clean q) : Clean (p.bind q) := by
  have hf : ∀ i, BstLean.Part41.argHeavy (Sum.elim Arg.inp
      (fun k => (p.out k).clamp p.body.length) i) = 0 := by
    intro i
    cases i with
    | inl i => rfl
    | inr k => exact heavy_clamp _ _ (hp.2 k)
  constructor
  · intro I hI
    simp only [Prog.bind, List.mem_append, List.mem_map] at hI
    rcases hI with hI | ⟨J, hJ, rfl⟩
    · exact hp.1 I hI
    · exact ⟨heavy_subst _ _ _ hf _ (hq.1 J hJ).1,
        heavy_subst _ _ _ hf _ (hq.1 J hJ).2⟩
  · intro o
    exact heavy_subst _ _ _ hf _ (hq.2 o)

private lemma clean_mapIn {ι κ ν : Type} (f : ι → ν) {p : Prog ι κ}
    (hp : Clean p) : Clean (p.mapIn f) := by
  constructor
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    simpa [Instr.rename, heavy_rename] using hp.1 J hJ
  · intro o
    exact (heavy_rename _ _).trans (hp.2 o)

private lemma clean_par {ι κ : Type} [DecidableEq κ] (p : κ → Prog ι Unit)
    (hp : ∀ k, Clean (p k)) (l : List κ) : Clean (Prog.par p l) := by
  induction l with
  | nil => simp [Clean, Prog.par, Prog.ofArgs, BstLean.Part41.argHeavy]
  | cons k l ih =>
    apply clean_bind (hp k)
    constructor
    · exact (clean_mapIn Sum.inl ih).1
    · intro j
      dsimp
      split_ifs
      · rfl
      · exact (clean_mapIn Sum.inl ih).2 j

private lemma clean_heavyCount {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (hp : Clean p) : heavyCount p = 0 := by
  unfold heavyCount
  have hb : (p.body.map fun I => BstLean.Part41.argHeavy I.a +
      BstLean.Part41.argHeavy I.b).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hx
    simp [(hp.1 I hI).1, (hp.1 I hI).2]
  simp [hb, hp.2]

private noncomputable def shiftProg (i0 : Fin n) : Prog (Fin n) (Fin n) :=
  Prog.par (fun i => Prog.op1 .sub (.inp i) (.inp i0)) (List.finRange n)

private lemma shiftProg_clean (i0 : Fin n) : Clean (shiftProg i0) := by
  apply clean_par
  intro i
  simp [Clean, Prog.op1, BstLean.Part41.argHeavy]

private lemma shiftProg_heavyCount (i0 : Fin n) : heavyCount (shiftProg i0) = 0 :=
  clean_heavyCount (shiftProg_clean i0)

private lemma shiftProg_eval (i0 : Fin n) (θ : Fin n → ℝ) (j : Fin n) :
    (shiftProg i0).eval θ j = BstLean.Part42.bsh θ i0 j := by
  rw [shiftProg, eval_par_mem _ _ _ _ (List.mem_finRange j)]
  simp [Arg.eval, Op.eval, BstLean.Part42.bsh]

private lemma shiftProg_cost (i0 : Fin n) : (shiftProg i0).cost = n := by
  simp [shiftProg, cost_par]

/-! ## Exact realizability of the raw moment recursions

These lemmas do not give the shared ring computation's cost. They establish that the raw
moments are computed by arithmetic programs and that their rational constants can be inlined.
-/

private def Realizable {ι : Type} (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ p : Prog ι Unit, ∀ v, p.eval v () = f v

private lemma realizable_const {ι : Type} (q : ℚ) :
    Realizable (fun _ : ι → ℝ => (q : ℝ)) :=
  ⟨Prog.ofArgs (fun _ => .cst q), fun _ => rfl⟩

private lemma realizable_nat {ι : Type} (a : ℕ) :
    Realizable (fun _ : ι → ℝ => (a : ℝ)) := by
  simpa using realizable_const (ι := ι) (a : ℚ)

private lemma realizable_inp {ι : Type} (i : ι) : Realizable (fun v => v i) :=
  ⟨Prog.ofArgs (fun _ => .inp i), fun _ => rfl⟩

private lemma realizable_op {ι : Type} {f g : (ι → ℝ) → ℝ} (op : Op)
    (hf : Realizable f) (hg : Realizable g) : Realizable (fun v => op.eval (f v) (g v)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  let r : Prog (ι ⊕ (Unit ⊕ Unit)) Unit :=
    Prog.op1 op (.inp (.inr (.inl ()))) (.inp (.inr (.inr ())))
  refine ⟨(p.pair q).bind r, ?_⟩
  intro v
  simp [r, eval_bind, Arg.eval, hp, hq]

private lemma realizable_add {ι : Type} {f g : (ι → ℝ) → ℝ}
    (hf : Realizable f) (hg : Realizable g) : Realizable (fun v => f v + g v) :=
  realizable_op .add hf hg

private lemma realizable_mul {ι : Type} {f g : (ι → ℝ) → ℝ}
    (hf : Realizable f) (hg : Realizable g) : Realizable (fun v => f v * g v) :=
  realizable_op .mul hf hg

private lemma realizable_div {ι : Type} {f g : (ι → ℝ) → ℝ}
    (hf : Realizable f) (hg : Realizable g) : Realizable (fun v => f v / g v) :=
  realizable_op .div hf hg

private lemma realizable_pow {ι : Type} {f : (ι → ℝ) → ℝ}
    (hf : Realizable f) (a : ℕ) : Realizable (fun v => f v ^ a) := by
  induction a with
  | zero => simpa using realizable_nat (ι := ι) 1
  | succ a ih => simpa [pow_succ] using realizable_mul ih hf

private lemma realizable_sum {ι α : Type} (s : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ a ∈ s, Realizable (f a)) : Realizable (fun v => ∑ a ∈ s, f a v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realizable_nat (ι := ι) 0
  | @insert a s ha ih =>
    simpa [Finset.sum_insert ha] using
      realizable_add (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb])))

private lemma realizable_prod {ι α : Type} (s : Finset α) (f : α → (ι → ℝ) → ℝ)
    (hf : ∀ a ∈ s, Realizable (f a)) : Realizable (fun v => ∏ a ∈ s, f a v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realizable_nat (ι := ι) 1
  | @insert a s ha ih =>
    simpa [Finset.prod_insert ha] using
      realizable_mul (hf a (by simp)) (ih (fun b hb => hf b (by simp [hb])))

private lemma realizable_phiTab (K j : ℕ) :
    Realizable (fun b : Fin n → ℝ => BstLean.Part37.phiTab b K j) := by
  induction K generalizing j with
  | zero =>
    by_cases hj : j = 0
    · simpa [BstLean.Part37.phiTab, hj] using realizable_nat (ι := Fin n) 1
    · simpa [BstLean.Part37.phiTab, hj] using realizable_nat (ι := Fin n) 0
  | succ K ih =>
    by_cases hj : j ≤ K
    · simpa [BstLean.Part37.phiTab, hj] using ih j
    · simp only [BstLean.Part37.phiTab, ite_eq_right hj]
      apply realizable_div
      · apply realizable_sum
        intro a ha
        apply realizable_mul
        · apply realizable_mul
          · simpa using realizable_nat (ι := Fin n) (2 ^ a)
          · unfold BstLean.Part37.psum
            apply realizable_sum
            intro i hi
            exact realizable_pow (realizable_inp i) (a + 1)
        · exact ih (K - a)
      · simpa using realizable_nat (ι := Fin n) (K + 1)

private lemma realizable_phiW (w : List (Fin n)) (j : ℕ) :
    Realizable (fun b : Fin n → ℝ => BstLean.Part37.phiW b w j) := by
  induction w generalizing j with
  | nil => exact realizable_phiTab j j
  | cons i w ih =>
    change Realizable (fun b : Fin n → ℝ => ∑ r ∈ Finset.range (j + 1),
      (2 * b i) ^ r * BstLean.Part37.phiW b w (j - r))
    apply realizable_sum
    intro r hr
    exact realizable_mul
      (realizable_pow (realizable_mul (realizable_nat 2) (realizable_inp i)) r)
      (ih (j - r))

private lemma realizable_numK (K : ℕ) (w : List (Fin n)) :
    Realizable (fun b : Fin n → ℝ => BstLean.Part37.numK n K b w) := by
  unfold BstLean.Part37.numK
  apply realizable_mul
  · unfold BstLean.Part37.dfC
    apply realizable_prod
    intro i hi
    exact realizable_nat _
  · apply realizable_sum
    intro j hj
    apply realizable_div (realizable_phiW w j)
    unfold BstLean.Part37.rhoP
    apply realizable_prod
    intro r hr
    simpa using realizable_nat (ι := Fin n) (n + 2 * r)

private lemma realizable_momK (K : ℕ) (w : List (Fin n)) :
    Realizable (fun b : Fin n → ℝ => BstLean.Part37.momK n K b w) :=
  realizable_div (realizable_numK K w) (realizable_numK K [])

private lemma inline_any {ι κ : Type} [Fintype κ] (p : Prog ι κ) :
    ∃ p' : Prog ι κ, heavyCount p' = 0 ∧ ∀ v o, p'.eval v o = p.eval v o := by
  classical
  let ht (q : ℚ) := max (Nat.log 2 q.num.natAbs + 1) (Nat.log 2 q.den + 1)
  let β := (BstLean.Part41.heavyConsts p).toFinset.sup ht
  have hb : ∀ q ∈ BstLean.Part41.heavyConsts p,
      q.num.natAbs < 2 ^ β ∧ q.den < 2 ^ β := by
    intro q hq
    have hle : ht q ≤ β := Finset.le_sup (f := ht) (List.mem_toFinset.mpr hq)
    constructor
    · exact (Nat.lt_pow_succ_log_self (by decide) _).trans_le
        (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans hle))
    · exact (Nat.lt_pow_succ_log_self (by decide) _).trans_le
        (Nat.pow_le_pow_right (by decide) ((le_max_right _ _).trans hle))
  obtain ⟨p', hp', he, _⟩ := BstLean.Part41.inline_consts p β hb
  exact ⟨p', hp', he⟩

private lemma momK_prog_exists (K : ℕ) (w : List (Fin n)) :
    ∃ p : Prog (Fin n) Unit, heavyCount p = 0 ∧
      ∀ b, p.eval b () = BstLean.Part37.momK n K b w := by
  obtain ⟨p, he⟩ := realizable_momK K w
  obtain ⟨p', hp', he'⟩ := inline_any p
  exact ⟨p', hp', fun b => (he' b ()).trans (he b)⟩

/-! ## A finite monomial expansion of the tensor moments -/

private lemma monoVal_add (x : Fin n → ℝ) (s t : Multiset (Fin n)) :
    BstLean.Part36.monoVal x (s + t) =
      BstLean.Part36.monoVal x s * BstLean.Part36.monoVal x t := by
  simp [BstLean.Part36.monoVal, Multiset.map_add, Multiset.prod_add]

private lemma monoVal_sum {α : Type} (S : Finset α) (s : α → Multiset (Fin n))
    (x : Fin n → ℝ) :
    BstLean.Part36.monoVal x (∑ a ∈ S, s a) = ∏ a ∈ S, BstLean.Part36.monoVal x (s a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [BstLean.Part36.monoVal]
  | @insert a S ha ih => simp [Finset.sum_insert ha, Finset.prod_insert ha, monoVal_add, ih]

private noncomputable def rawHR {s : ℕ} (l : ℕ) (w : Fin s → Mono n d)
    (a : Fin l → Mono n d) : Multiset (Fin n) :=
  (∑ t, ((a t).2.1 + (a t).2.1)) + ∑ t, (w t).2.1

private noncomputable def rawQ {j : ℕ} (τ : Fin j → Fin n) : Multiset (Fin n) :=
  ∑ t, ({τ t} + {τ t})

private lemma HR_expansion {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) (x : Fin n → ℝ) :
    phiSq d x ^ l * ∏ t, phiM x (w t) =
      ∑ a : Fin l → Mono n d, BstLean.Part36.monoVal x (rawHR l w a) := by
  classical
  simp only [phiSq, Fintype.sum_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  simp [rawHR, monoVal_add, monoVal_sum, phiM, pow_two]

private lemma qth_expansion (b x : Fin n → ℝ) (j : ℕ) :
    BstLean.Part37.qth b x ^ j =
      ∑ τ : Fin j → Fin n, (∏ t, b (τ t)) * BstLean.Part36.monoVal x (rawQ τ) := by
  classical
  simp only [BstLean.Part37.qth, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [rawQ, monoVal_sum]
  simp only [BstLean.Part36.monoVal]
  simp [pow_two, Finset.prod_mul_distrib]

private lemma continuous_monoVal (s : Multiset (Fin n)) :
    Continuous (fun x : Fin n → ℝ => BstLean.Part36.monoVal x s) := by
  exact continuous_multiset_prod s (fun i _ => continuous_apply i)

private noncomputable def sphereMonoQ (n : ℕ) (s : Multiset (Fin n)) : ℚ :=
  (∏ i, if Even (s.count i) then ((s.count i - 1).doubleFactorial : ℚ) else 0) /
    ∏ r ∈ Finset.range (s.card / 2), ((n : ℚ) + 2 * r)

private lemma sphereMonoQ_cast (s : Multiset (Fin n)) :
    (sphereMonoQ n s : ℝ) = BstLean.Part36.gpm s / rhoD n (s.card / 2) := by
  classical
  simp [sphereMonoQ, BstLean.Part36.gpm, BstLean.Part29.gaussMom, rhoD, apply_ite]

private lemma sphere_monoVal (hn : 1 ≤ n) (s : Multiset (Fin n)) :
    (∫ x, BstLean.Part36.monoVal x s ∂uniformSphere n) = (sphereMonoQ n s : ℝ) := by
  rw [sphereMonoQ_cast]
  exact (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n s.card hn) s le_rfl).2

private lemma HR_numerator_expansion (hn : 1 ≤ n) (b : Fin n → ℝ)
    {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) (Kq : ℕ) :
    (∫ x, (phiSq d x ^ l * ∏ t, phiM x (w t)) *
      BstLean.Part37.taylorExp Kq (BstLean.Part37.qth b x) ∂uniformSphere n) =
      ∑ j ∈ Finset.range (Kq + 1), ∑ a : Fin l → Mono n d, ∑ τ : Fin j → Fin n,
        ((sphereMonoQ n (rawHR l w a + rawQ τ) : ℝ) / (j.factorial : ℝ)) * ∏ t, b (τ t) := by
  classical
  have hexp (x : Fin n → ℝ) :
      (phiSq d x ^ l * ∏ t, phiM x (w t)) *
        BstLean.Part37.taylorExp Kq (BstLean.Part37.qth b x) =
      ∑ j ∈ Finset.range (Kq + 1), ∑ a : Fin l → Mono n d, ∑ τ : Fin j → Fin n,
        (∏ t, b (τ t)) / (j.factorial : ℝ) *
          BstLean.Part36.monoVal x (rawHR l w a + rawQ τ) := by
    rw [HR_expansion]
    unfold BstLean.Part37.taylorExp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [qth_expansion, Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [monoVal_add]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro τ hτ
        rw [integral_const_mul, sphere_monoVal hn]
        ring
      · intro τ hτ
        exact (sphere_cont_integrable hn (continuous_monoVal _)).const_mul _
    · intro a ha
      exact integrable_finsetSum _ fun τ _ =>
        (sphere_cont_integrable hn (continuous_monoVal _)).const_mul _
  · intro j hj
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun τ _ =>
      (sphere_cont_integrable hn (continuous_monoVal _)).const_mul _

private lemma realizable_HR_numerator {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) (Kq : ℕ) :
    Realizable (fun b : Fin n → ℝ =>
      ∑ j ∈ Finset.range (Kq + 1), ∑ a : Fin l → Mono n d, ∑ τ : Fin j → Fin n,
        ((sphereMonoQ n (rawHR l w a + rawQ τ) : ℝ) / (j.factorial : ℝ)) * ∏ t, b (τ t)) := by
  apply realizable_sum
  intro j hj
  apply realizable_sum
  intro a ha
  apply realizable_sum
  intro τ hτ
  apply realizable_mul
  · apply realizable_div (realizable_const _) (realizable_nat _)
  · apply realizable_prod
    intro t ht
    exact realizable_inp (τ t)

private noncomputable def momentExpr {s : ℕ} (l : ℕ) (w : Fin s → Mono n d)
    (Kq : ℕ) (b : Fin n → ℝ) : ℝ :=
  (∑ j ∈ Finset.range (Kq + 1), ∑ a : Fin l → Mono n d, ∑ τ : Fin j → Fin n,
    ((sphereMonoQ n (rawHR l w a + rawQ τ) : ℝ) / (j.factorial : ℝ)) * ∏ t, b (τ t)) /
      BstLean.Part37.numK n Kq b []

private lemma realizable_momentExpr {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) (Kq : ℕ) :
    Realizable (momentExpr l w Kq) :=
  realizable_div (realizable_HR_numerator l w Kq) (realizable_numK Kq [])

private lemma momentExpr_eq (hn : 1 ≤ n) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    {s : ℕ} (l : ℕ) (w : Fin s → Mono n d) (Kq : ℕ) :
    momentExpr l w Kq b = HR (BstLean.Part37.binghamK n Kq b) l w := by
  unfold momentExpr HR
  rw [integral_binghamK_nonneg hn b hb Kq, HR_numerator_expansion hn b l w Kq,
    BstLean.Part37.ZK_eq hn b Kq]

private noncomputable def weightExpr {k : ℕ}
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (κ : KeyF n d k)
    (Kq : ℕ) (b : Fin n → ℝ) : ℝ :=
  if 2 * κ.2.1.1 = κ.1.1 then
    (kapQ n d κ.1.1 κ.2.1.1 : ℝ) *
      momentExpr (d := d) (s := κ.1.1 - 2 * κ.2.1.1) κ.2.1.1 (fun _ => default) Kq b
  else (kapQ n d κ.1.1 κ.2.1.1 : ℝ) * (muQ n d (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 : ℝ) *
    (orbSize κ.2.2.2.2.1 : ℝ) *
    trL κ.2.2.1.1
      (fun w : Fin (κ.1.1 - 2 * κ.2.1.1) → Mono n d =>
        if mset w ∈ K κ.1.1 κ.2.1.1 then momentExpr κ.2.1.1 w Kq b else 0)
      (wordOf _ κ.2.2.2.2.1)

private lemma weightExpr_eq (hn : 1 ≤ n) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    {k : ℕ} (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (κ : KeyF n d k) (Kq : ℕ) :
    weightExpr K κ Kq b = wKeyR (BstLean.Part37.binghamK n Kq b) K κ := by
  unfold weightExpr
  simp_rw [momentExpr_eq hn b hb]
  rfl

private lemma realizable_weightExpr {k : ℕ}
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (κ : KeyF n d k) (Kq : ℕ) :
    Realizable (weightExpr K κ Kq) := by
  classical
  unfold weightExpr
  split_ifs
  · exact realizable_mul (realizable_const _) (realizable_momentExpr _ _ _)
  · apply realizable_mul
    · apply realizable_mul
      · exact realizable_mul (realizable_const _) (realizable_const _)
      · exact realizable_nat _
    · unfold trL
      apply realizable_sum
      intro c hc
      dsimp only
      split_ifs
      · exact realizable_momentExpr _ _ _
      · simpa using realizable_nat (ι := Fin n) 0

/-- Correctness and constant inlining, without the shared ring algorithm's operation bound. -/
private lemma momProg43_exists_uncosted (hn : 1 ≤ n) (k : ℕ) (i0 : Fin n) (Kq : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d))) :
    ∃ pm : Prog (Fin n) (KeyF n d k), heavyCount pm = 0 ∧
      ∀ θ' : Fin n → ℝ, (∀ j, θ' i0 ≤ θ' j) → MomSpec43 pm K i0 Kq θ' := by
  classical
  choose p hp using fun κ : KeyF n d k => realizable_weightExpr K κ Kq
  let q := Prog.par p (Finset.univ : Finset (KeyF n d k)).toList
  let r := (shiftProg i0).bind (q.mapIn Sum.inr)
  obtain ⟨pm, hpm, he⟩ := inline_any r
  refine ⟨pm, hpm, ?_⟩
  intro θ' hmin κ hκ
  rw [he]
  simp only [r, eval_bind, eval_mapIn]
  have hshift : (shiftProg i0).eval θ' = BstLean.Part42.bsh θ' i0 :=
    funext (shiftProg_eval i0 θ')
  simp only [Function.comp_def, Sum.elim_inr, hshift]
  simp only [q]
  rw [eval_par_mem _ _ _ _ (by simp), hp]
  exact weightExpr_eq hn _ (bsh_nonneg θ' i0 hmin) K κ Kq


/-! ## Shared arithmetic on bounded coefficient tables -/

private lemma clean_sumArgs {ι : Type} (l : List (Arg ι))
    (hl : ∀ a ∈ l, BstLean.Part41.argHeavy a = 0) : Clean (Prog.sumArgs l) := by
  induction l with
  | nil => simp [Clean, Prog.sumArgs, Prog.ofArgs, BstLean.Part41.argHeavy]
  | cons a l ih =>
    cases l with
    | nil => exact ⟨by simp [Prog.sumArgs, Prog.ofArgs], fun _ => hl a (by simp)⟩
    | cons b l =>
      apply clean_bind (ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)))
      have ha := (heavy_rename (Sum.inl : ι → ι ⊕ Unit) a).trans (hl a (by simp))
      simpa [Clean, Prog.op1, BstLean.Part41.argHeavy] using ha

private lemma clean_sumProd {ι : Type} (l : List (Arg ι × Arg ι))
    (hl : ∀ ab ∈ l, BstLean.Part41.argHeavy ab.1 = 0 ∧
      BstLean.Part41.argHeavy ab.2 = 0) : Clean (Prog.sumProd l) := by
  apply clean_bind
  · apply clean_par
    intro j
    have h := hl (l.get j) (List.get_mem _ _)
    simpa [Clean, Prog.op1, BstLean.Part41.argHeavy] using h
  · apply clean_sumArgs
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    rfl

private def HasProg {ι κ : Type} (f : (ι → ℝ) → κ → ℝ) (c : ℕ) : Prop :=
  ∃ p : Prog ι κ, Clean p ∧ (∀ v k, p.eval v k = f v k) ∧ p.cost ≤ c

private lemma hp_args {ι κ : Type} (a : κ → Arg ι)
    (ha : ∀ k, BstLean.Part41.argHeavy (a k) = 0) :
    HasProg (fun v k => (a k).eval v []) 0 :=
  ⟨Prog.ofArgs a, ⟨by simp [Prog.ofArgs], ha⟩, fun _ _ => rfl, le_rfl⟩

private lemma hp_op {ι : Type} (op : Op) (a b : Arg ι)
    (ha : BstLean.Part41.argHeavy a = 0) (hb : BstLean.Part41.argHeavy b = 0) :
    HasProg (fun v (_ : Unit) => op.eval (a.eval v []) (b.eval v [])) 1 := by
  refine ⟨Prog.op1 op a b, ?_, ?_, le_rfl⟩
  · simpa [Clean, Prog.op1, BstLean.Part41.argHeavy] using And.intro ha hb
  · intro v k; exact eval_op1 _ _ _ _ _

private lemma hp_bind {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ}
    {g : ((ι ⊕ κ) → ℝ) → ν → ℝ} {a b : ℕ}
    (hf : HasProg f a) (hg : HasProg g b) :
    HasProg (fun v => g (Sum.elim v (f v))) (a + b) := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  obtain ⟨q, hq, eq, cq⟩ := hg
  refine ⟨p.bind q, clean_bind hp hq, ?_, ?_⟩
  · intro v k
    rw [eval_bind, eq]
    have he : p.eval v = f v := funext (ep v)
    rw [he]
  · rw [cost_bind]; omega

private lemma hp_par {ι κ : Type} [Fintype κ] [DecidableEq κ]
    {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : ∀ k, HasProg (fun v (_ : Unit) => f v k) c) :
    HasProg f (Fintype.card κ * c) := by
  classical
  choose p hp ep cp using hf
  refine ⟨Prog.par p Finset.univ.toList, clean_par p hp _, ?_, ?_⟩
  · intro v k
    rw [eval_par_mem _ _ _ _ (by simp), ep]
  · rw [cost_par]
    calc
      _ ≤ (Finset.univ.toList.map fun _ : κ => c).sum := by
        apply List.sum_le_sum
        intro k _; exact cp k
      _ = _ := by simp

private lemma hp_dot {ι κ : Type} [Fintype κ] (a b : κ → Arg ι)
    (ha : ∀ k, BstLean.Part41.argHeavy (a k) = 0) (hb : ∀ k, BstLean.Part41.argHeavy (b k) = 0) :
    HasProg (fun v (_ : Unit) => ∑ k, (a k).eval v [] * (b k).eval v [])
      (2 * Fintype.card κ - 1) := by
  classical
  let l := Finset.univ.toList.map fun k => (a k, b k)
  refine ⟨Prog.sumProd l, ?_, ?_, ?_⟩
  · apply clean_sumProd
    intro ab hab
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hab
    exact ⟨ha k, hb k⟩
  · intro v k
    simp [eval_sumProd, l, List.map_map, Function.comp_def, Finset.sum_map_toList]
  · simp [l, cost_sumProd]

private lemma hp_sum {ι κ : Type} [Fintype κ] (a : κ → Arg ι)
    (ha : ∀ k, BstLean.Part41.argHeavy (a k) = 0) :
    HasProg (fun v (_ : Unit) => ∑ k, (a k).eval v []) (Fintype.card κ - 1) := by
  classical
  let l := Finset.univ.toList.map a
  refine ⟨Prog.sumArgs l, ?_, ?_, ?_⟩
  · apply clean_sumArgs
    intro b hb
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
    exact ha k
  · intro v k
    simp [eval_sumArgs, l, List.map_map, Function.comp_def, Finset.sum_map_toList]
  · simp [l, cost_sumArgs]

private lemma hp_mono {ι κ : Type} {f : (ι → ℝ) → κ → ℝ} {a b : ℕ}
    (hf : HasProg f a) (h : a ≤ b) : HasProg f b := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  exact ⟨p, hp, ep, cp.trans h⟩

private lemma hp_congr {ι κ : Type} {f g : (ι → ℝ) → κ → ℝ} {a : ℕ}
    (hf : HasProg f a) (h : ∀ v k, f v k = g v k) : HasProg g a := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  exact ⟨p, hp, fun v k => (ep v k).trans (h v k), cp⟩

private lemma hp_pair {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ}
    {g : (ι → ℝ) → ν → ℝ} {a b : ℕ}
    (hf : HasProg f a) (hg : HasProg g b) :
    HasProg (fun v => Sum.elim (f v) (g v)) (a + b) := by
  obtain ⟨p, hp, ep, cp⟩ := hf
  obtain ⟨q, hq, eq, cq⟩ := hg
  refine ⟨p.pair q, ?_, ?_, ?_⟩
  · apply clean_bind hp
    constructor
    · exact (clean_mapIn Sum.inl hq).1
    · intro k
      cases k with
      | inl k => rfl
      | inr k => exact (clean_mapIn Sum.inl hq).2 k
  · intro v k; cases k <;> simp [ep, eq]
  · rw [cost_pair]; omega


private lemma hp_mapOut {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : HasProg f c) (r : ν → κ) : HasProg (fun v k => f v (r k)) c := by
  obtain ⟨p, hp, he, hc⟩ := hf
  exact ⟨p.mapOut r, ⟨hp.1, fun k => hp.2 (r k)⟩, fun v k => he v (r k), hc⟩

private lemma hp_mapIn {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : HasProg f c) (r : ι → ν) : HasProg (fun v k => f (v ∘ r) k) c := by
  obtain ⟨p, hp, he, hc⟩ := hf
  exact ⟨p.mapIn r, clean_mapIn r hp, fun v k => by rw [eval_mapIn, he],
    by simpa using hc⟩

private lemma hp_keep {ι κ : Type} {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (hf : HasProg f c) : HasProg (fun v => Sum.elim v (f v)) c := by
  obtain ⟨p, hp, he, hc⟩ := hf
  let q : Prog (ι ⊕ κ) (ι ⊕ κ) := Prog.ofArgs Arg.inp
  refine ⟨p.bind q, clean_bind hp ?_, ?_, ?_⟩
  · simp [q, Clean, Prog.ofArgs, BstLean.Part41.argHeavy]
  · intro v k
    rw [eval_bind]
    cases k <;> simp [q, Arg.eval, he]
  · simpa [q] using hc

private def tab {ι κ : Type} (f : (ι → ℝ) → ℕ → κ → ℝ) (K : ℕ)
    (v : ι → ℝ) (a : ℕ × κ) : ℝ := if a.1 ≤ K then f v a.1 a.2 else 0

private lemma hp_table {ι κ : Type} (f : (ι → ℝ) → ℕ → κ → ℝ)
    (g : ℕ → ((ι ⊕ (ℕ × κ)) → ℝ) → κ → ℝ) (c0 : ℕ) (c : ℕ → ℕ)
    (h0 : HasProg (fun v => f v 0) c0)
    (K : ℕ) (hs : ∀ k, k < K → HasProg (g k) (c k))
    (he : ∀ k, k < K → ∀ v a, g k (Sum.elim v (tab f k v)) a = f v (k + 1) a) :
    HasProg (tab f K) (c0 + ∑ k ∈ Finset.range K, c k) := by
  classical
  induction K with
  | zero =>
    have hz := hp_bind h0 (hp_args (fun a : ℕ × κ =>
      if a.1 = 0 then Arg.inp (Sum.inr a.2) else Arg.cst 0)
      (by intro a; split_ifs <;> rfl))
    apply hp_mono (hp_congr hz ?_) (by simp)
    intro v a
    simp only [Arg.eval, tab]
    by_cases h : a.1 = 0 <;> simp [h]
  | succ K ih =>
    obtain ⟨q, hq, eq, cq⟩ := hs K (by omega)
    let r : Prog (ι ⊕ (ℕ × κ)) (ℕ × κ) :=
      (q.bind (Prog.ofArgs (fun a : ℕ × κ =>
        if a.1 = K + 1 then Arg.inp (Sum.inr a.2)
        else Arg.inp (Sum.inl (Sum.inr a)))))
    have hr : Clean r := by
      apply clean_bind hq
      refine ⟨by simp [Prog.ofArgs], ?_⟩
      intro a
      change BstLean.Part41.argHeavy (if a.1 = K + 1 then Arg.inp (Sum.inr a.2)
        else Arg.inp (Sum.inl (Sum.inr a))) = 0
      split_ifs <;> rfl
    have er (v : (ι ⊕ (ℕ × κ)) → ℝ) (a : ℕ × κ) :
        r.eval v a = if a.1 = K + 1 then g K v a.2 else v (Sum.inr a) := by
      simp only [r, eval_bind, eval_ofArgs]
      split_ifs <;> simp [Arg.eval, eq]
    have hz : HasProg (fun v a => if a.1 = K + 1 then g K v a.2 else v (Sum.inr a))
        (c K) := ⟨r, hr, er, by simpa [r] using cq⟩
    have hi := ih (fun k hk => hs k (by omega)) (fun k hk => he k (by omega))
    apply hp_mono (hp_congr (hp_bind hi hz) ?_) (by rw [Finset.sum_range_succ]; omega)
    intro v a
    by_cases h : a.1 = K + 1
    · simp only [h, ite_true, he K (by omega), tab]
      simp
    · simp only [h, ite_false, Sum.elim_inr, tab]
      have hh : a.1 ≤ K + 1 ↔ a.1 ≤ K := by omega
      simp only [hh]

private lemma hp_bool_pair {ι : Type} {f g : (ι → ℝ) → ℝ} {a b : ℕ}
    (hf : HasProg (fun v (_ : Unit) => f v) a)
    (hg : HasProg (fun v (_ : Unit) => g v) b) :
    HasProg (fun v (t : Bool) => if t then g v else f v) (a + b) := by
  exact hp_congr (hp_mapOut (hp_pair hf hg)
    (fun t => if t then Sum.inr () else Sum.inl ()))
    (by intro v t; cases t <;> rfl)


private lemma antidiagonal_card_le {σ : Type} [DecidableEq σ]
    (E e : σ →₀ ℕ) (he : e ≤ E) :
    (Finset.HasAntidiagonal.antidiagonal e).card ≤ (Finset.Iic E).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ab hab
    apply Finset.mem_Iic.mpr
    have hsum : ab.1 + ab.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    rw [← hsum] at he
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ ab.2)).trans he
  · intro ab hab cd hcd hfst
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hcd' := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
    apply Prod.ext hfst
    exact add_left_cancel (hfst ▸ hab'.trans hcd'.symm)

private noncomputable def ringMulProg {σ : Type} [DecidableEq σ] (E : σ →₀ ℕ) :
    Prog ((σ →₀ ℕ) ⊕ (σ →₀ ℕ)) (σ →₀ ℕ) :=
  Prog.par (fun e => Prog.sumProd ((Finset.HasAntidiagonal.antidiagonal e).toList.map
    (fun ab => (Arg.inp (Sum.inl ab.1), Arg.inp (Sum.inr ab.2)))))
    (Finset.Iic E).toList

private lemma ringMulProg_clean {σ : Type} [DecidableEq σ] (E : σ →₀ ℕ) :
    Clean (ringMulProg E) := by
  apply clean_par
  intro e
  apply clean_sumProd
  intro ab hab
  obtain ⟨uv, huv, rfl⟩ := List.mem_map.mp hab
  exact ⟨rfl, rfl⟩

private lemma ringMulProg_eval {σ : Type} [DecidableEq σ] (E e : σ →₀ ℕ)
    (he : e ≤ E) (φ ψ : MvPowerSeries σ ℝ) :
    (ringMulProg E).eval
      (Sum.elim (fun a => MvPowerSeries.coeff a φ) (fun a => MvPowerSeries.coeff a ψ)) e =
      MvPowerSeries.coeff e (φ * ψ) := by
  rw [ringMulProg, eval_par_mem _ _ _ _ (Finset.mem_toList.mpr (Finset.mem_Iic.mpr he)),
    eval_sumProd, MvPowerSeries.coeff_mul]
  simp [List.map_map, Function.comp_def, Arg.eval, Finset.sum_map_toList]

private lemma ringMulProg_eval_outside {σ : Type} [DecidableEq σ] (E e : σ →₀ ℕ)
    (he : ¬e ≤ E) (v : ((σ →₀ ℕ) ⊕ (σ →₀ ℕ)) → ℝ) :
    (ringMulProg E).eval v e = 0 := by
  apply eval_par_not_mem
  simpa using he

private lemma ringMulProg_cost {σ : Type} [DecidableEq σ] (E : σ →₀ ℕ) :
    (ringMulProg E).cost ≤ 2 * (Finset.Iic E).card ^ 2 := by
  unfold ringMulProg
  rw [cost_par]
  calc
    _ ≤ ((Finset.Iic E).toList.map fun _ => 2 * (Finset.Iic E).card).sum := by
      apply List.sum_le_sum
      intro e he
      simp only [cost_sumProd, List.length_map, Finset.length_toList]
      have h := antidiagonal_card_le E e (Finset.mem_Iic.mp (Finset.mem_toList.mp he))
      omega
    _ = 2 * (Finset.Iic E).card ^ 2 := by simp [pow_two, Nat.mul_comm, Nat.mul_assoc]

private noncomputable def ringUpper (l d Kq : ℕ) : Fin (l + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cases Kq (fun _ => d))

private lemma ringUpper_card (l d Kq : ℕ) :
    (Finset.Iic (ringUpper l d Kq)).card = (Kq + 1) * (d + 1) ^ l := by
  rw [Finsupp.card_Iic]
  change (ringUpper l d Kq).prod (fun _ a => (Finset.Iic a).card) = _
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp [ringUpper, Fin.prod_univ_succ]

private lemma ringMulProg_cost_delta (d k Kq : ℕ) :
    (ringMulProg (ringUpper (k / 2) d Kq)).cost ≤ 2 * deltaR d k Kq ^ 2 := by
  simpa [ringUpper_card, deltaR] using ringMulProg_cost (ringUpper (k / 2) d Kq)

private def EqUpTo {σ : Type} (E : σ →₀ ℕ) (φ ψ : MvPowerSeries σ ℝ) : Prop :=
  ∀ e ≤ E, MvPowerSeries.coeff e φ = MvPowerSeries.coeff e ψ

private lemma EqUpTo.mul {σ : Type} [DecidableEq σ] {E : σ →₀ ℕ}
    {φ φ' ψ ψ' : MvPowerSeries σ ℝ} (hφ : EqUpTo E φ φ') (hψ : EqUpTo E ψ ψ') :
    EqUpTo E (φ * ψ) (φ' * ψ') := by
  intro e he
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hab' : ab.1 + ab.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have ha : ab.1 ≤ E := by
    rw [← hab'] at he
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ ab.2)).trans he
  have hb : ab.2 ≤ E := by
    rw [← hab'] at he
    exact (le_add_of_nonneg_left (by positivity : 0 ≤ ab.1)).trans he
  rw [hφ _ ha, hψ _ hb]

private lemma ringMulProg_eval_of_le {σ : Type} [DecidableEq σ] (E e : σ →₀ ℕ)
    (he : e ≤ E) (a b : (σ →₀ ℕ) → ℝ) (φ ψ : MvPowerSeries σ ℝ)
    (ha : ∀ f ≤ E, a f = MvPowerSeries.coeff f φ)
    (hb : ∀ f ≤ E, b f = MvPowerSeries.coeff f ψ) :
    (ringMulProg E).eval (Sum.elim a b) e = MvPowerSeries.coeff e (φ * ψ) := by
  rw [ringMulProg, eval_par_mem _ _ _ _ (Finset.mem_toList.mpr (Finset.mem_Iic.mpr he)),
    eval_sumProd, MvPowerSeries.coeff_mul]
  simp only [List.map_map, Function.comp_def, Arg.eval, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro uv huv
  have huv' : uv.1 + uv.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hu : uv.1 ≤ E := by
    rw [← huv'] at he
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ uv.2)).trans he
  have hv : uv.2 ≤ E := by
    rw [← huv'] at he
    exact (le_add_of_nonneg_left (by positivity : 0 ≤ uv.1)).trans he
  rw [ha _ hu, hb _ hv]

private noncomputable def ringProdProg {σ ι : Type} [DecidableEq σ]
    (E : σ →₀ ℕ) : List ι → Prog (ι × (σ →₀ ℕ)) (σ →₀ ℕ)
  | [] => Prog.ofArgs (fun e => .cst (if e = 0 then 1 else 0))
  | i :: L => (ringProdProg E L).bind ((ringMulProg E).mapIn
      (Sum.elim (fun e => Sum.inl (i, e)) Sum.inr))

private lemma ringProdProg_clean {σ ι : Type} [DecidableEq σ] (E : σ →₀ ℕ) (L : List ι) :
    Clean (ringProdProg E L) := by
  induction L with
  | nil =>
    constructor
    · simp [ringProdProg, Prog.ofArgs]
    · intro e
      change BstLean.Part41.argHeavy (Arg.cst (if e = 0 then (1 : ℚ) else 0)) = 0
      by_cases h : e = 0 <;> simp [h, BstLean.Part41.argHeavy]
  | cons i L ih =>
    exact clean_bind ih (clean_mapIn _ (ringMulProg_clean E))

private lemma ringProdProg_eval {σ ι : Type} [DecidableEq σ] (E e : σ →₀ ℕ)
    (he : e ≤ E) (L : List ι) (φ : ι → MvPowerSeries σ ℝ) :
    (ringProdProg E L).eval (fun ie => MvPowerSeries.coeff ie.2 (φ ie.1)) e =
      MvPowerSeries.coeff e (L.map φ).prod := by
  induction L generalizing e with
  | nil =>
    simp only [ringProdProg, eval_ofArgs, Arg.eval, List.map_nil, List.prod_nil,
      MvPowerSeries.coeff_one]
    split_ifs <;> norm_num
  | cons i L ih =>
    simp only [ringProdProg, eval_bind, eval_mapIn, List.map_cons, List.prod_cons]
    have hx : (Sum.elim (fun ie => MvPowerSeries.coeff ie.2 (φ ie.1))
        ((ringProdProg E L).eval (fun ie => MvPowerSeries.coeff ie.2 (φ ie.1))) ∘
        Sum.elim (fun f => Sum.inl (i, f)) Sum.inr) =
        Sum.elim (fun f => MvPowerSeries.coeff f (φ i))
          ((ringProdProg E L).eval (fun ie => MvPowerSeries.coeff ie.2 (φ ie.1))) := by
      funext u
      cases u <;> rfl
    rw [hx]
    change (ringMulProg E).eval
      (Sum.elim (fun f => MvPowerSeries.coeff f (φ i))
        ((ringProdProg E L).eval (fun ie => MvPowerSeries.coeff ie.2 (φ ie.1)))) e = _
    apply ringMulProg_eval_of_le E e he _ _ (φ i) (L.map φ).prod
    · intro f hf; rfl
    · intro f hf
      exact ih f hf

private lemma ringProdProg_cost {σ ι : Type} [DecidableEq σ] (E : σ →₀ ℕ) (L : List ι) :
    (ringProdProg E L).cost ≤ 2 * L.length * (Finset.Iic E).card ^ 2 := by
  induction L with
  | nil => simp [ringProdProg]
  | cons i L ih =>
    simp only [ringProdProg, cost_bind, cost_mapIn, List.length_cons]
    calc
      _ ≤ 2 * L.length * (Finset.Iic E).card ^ 2 + 2 * (Finset.Iic E).card ^ 2 :=
        Nat.add_le_add ih (ringMulProg_cost E)
      _ = _ := by ring

private def coeffDegree {σ : Type} [Fintype σ] (e : σ →₀ ℕ) : ℕ := ∑ i, e i

private lemma coeffDegree_strict {σ : Type} [Fintype σ] {a b : σ →₀ ℕ} (h : a < b) :
    coeffDegree a < coeffDegree b := by
  classical
  have hex : ∃ i, a i < b i := by
    by_contra hn
    push Not at hn
    exact not_le_of_gt h (show b ≤ a from hn)
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_lt_sum (fun j _ => h.le j) ⟨i, Finset.mem_univ i, hi⟩

private noncomputable def inverseOrder {σ : Type} [Fintype σ] [DecidableEq σ]
    (E : σ →₀ ℕ) : List (σ →₀ ℕ) :=
  (Finset.Iic E).toList.mergeSort (fun a b => coeffDegree a ≤ coeffDegree b)

private lemma inverseOrder_perm {σ : Type} [Fintype σ] [DecidableEq σ] (E : σ →₀ ℕ) :
    (inverseOrder E).Perm (Finset.Iic E).toList :=
  List.mergeSort_perm _ _

private lemma inverseOrder_sorted {σ : Type} [Fintype σ] [DecidableEq σ] (E : σ →₀ ℕ) :
    (inverseOrder E).Pairwise (fun a b => coeffDegree a ≤ coeffDegree b) := by
  simpa only [inverseOrder, decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun a b : σ →₀ ℕ => decide (coeffDegree a ≤ coeffDegree b))
    (fun a b c hab hbc => by
      simpa using le_trans (by simpa using hab : coeffDegree a ≤ coeffDegree b)
        (by simpa using hbc : coeffDegree b ≤ coeffDegree c))
    (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using
      (le_total (coeffDegree a) (coeffDegree b))) (Finset.Iic E).toList

private lemma inverseOrder_dependency {σ : Type} [Fintype σ] [DecidableEq σ]
    (E : σ →₀ ℕ) {e f : σ →₀ ℕ} (he : e ≤ E) (hf : f < e) :
    (inverseOrder E).idxOf f < (inverseOrder E).idxOf e := by
  let L := inverseOrder E
  have heL : e ∈ L := (inverseOrder_perm E).mem_iff.mpr
    (Finset.mem_toList.mpr (Finset.mem_Iic.mpr he))
  have hfL : f ∈ L := (inverseOrder_perm E).mem_iff.mpr
    (Finset.mem_toList.mpr (Finset.mem_Iic.mpr (hf.le.trans he)))
  have hei : L.idxOf e < L.length := List.idxOf_lt_length_iff.mpr heL
  have hfi : L.idxOf f < L.length := List.idxOf_lt_length_iff.mpr hfL
  have hdeg := coeffDegree_strict hf
  change L.idxOf f < L.idxOf e
  by_contra h
  have hge : L.idxOf e ≤ L.idxOf f := by omega
  rcases lt_or_eq_of_le hge with hlt | heq
  · have hs := (inverseOrder_sorted E).rel_getElem_of_lt hei hfi hlt
    rw [List.getElem_idxOf hei, List.getElem_idxOf hfi] at hs
    omega
  · have heq' : e = f := by
      rw [← List.getElem_idxOf hei, ← List.getElem_idxOf hfi]
      simp only [heq]
    subst f
    exact lt_irrefl _ hf

private noncomputable def inverseRows {σ : Type} [Fintype σ] [DecidableEq σ]
    (E : σ →₀ ℕ) (v : (σ →₀ ℕ) → ℝ) : ℕ → Unit → ℝ
  | 0, _ => 0
  | j + 1, _ => MvPowerSeries.coeff ((inverseOrder E).getD j 0)
      (MvPowerSeries.invOfUnit (v : MvPowerSeries σ ℝ) 1)

private noncomputable def inverseStep {σ : Type} [Fintype σ] [DecidableEq σ]
    (E : σ →₀ ℕ) (j : ℕ) (v : ((σ →₀ ℕ) ⊕ (ℕ × Unit)) → ℝ) (_ : Unit) : ℝ :=
  let e := (inverseOrder E).getD j 0
  if e = 0 then 1 else
    -(∑ uv ∈ Finset.HasAntidiagonal.antidiagonal e,
      if uv.2 < e then v (Sum.inl uv.1) * v (Sum.inr ((inverseOrder E).idxOf uv.2 + 1, ())) else 0)

private lemma inverseStep_prog {σ : Type} [Fintype σ] [DecidableEq σ]
    (E : σ →₀ ℕ) (j : ℕ) (hj : j < (inverseOrder E).length) :
    HasProg (inverseStep E j) (2 * (Finset.Iic E).card + 1) := by
  classical
  let e := (inverseOrder E).getD j 0
  have he : e ≤ E := by
    apply Finset.mem_Iic.mp
    apply Finset.mem_toList.mp
    apply (inverseOrder_perm E).mem_iff.mp
    change (inverseOrder E).getD j 0 ∈ inverseOrder E
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  by_cases he0 : e = 0
  · apply hp_mono (hp_congr (hp_args (fun _ : Unit => Arg.cst 1) (fun _ => rfl)) ?_) (by omega)
    intro v u
    simp only [Arg.eval, Rat.cast_one]
    change (1 : ℝ) = if e = 0 then 1 else _
    rw [ite_eq_left he0]
  let A := (Finset.HasAntidiagonal.antidiagonal e).filter (fun uv => uv.2 < e)
  let pairs : List (Arg ((σ →₀ ℕ) ⊕ (ℕ × Unit)) × Arg ((σ →₀ ℕ) ⊕ (ℕ × Unit))) :=
    A.toList.map (fun uv => (.inp (Sum.inl uv.1), .inp (Sum.inr ((inverseOrder E).idxOf uv.2 + 1, ()))))
  let q := Prog.sumProd pairs
  have hq : Clean q := by
    apply clean_sumProd
    intro ab hab
    obtain ⟨uv, huv, rfl⟩ := List.mem_map.mp hab
    exact ⟨rfl, rfl⟩
  let r : Prog (((σ →₀ ℕ) ⊕ (ℕ × Unit)) ⊕ Unit) Unit :=
    Prog.op1 .sub (.cst 0) (.inp (Sum.inr ()))
  refine ⟨q.bind r, clean_bind hq ?_, ?_, ?_⟩
  · simp [r, Clean, Prog.op1, BstLean.Part41.argHeavy]
  · intro v u
    change (q.bind r).eval v u = if e = 0 then 1 else _
    rw [ite_eq_right he0]
    simp [q, r, pairs, eval_bind, eval_sumProd, Arg.eval, Op.eval,
      List.map_map, Function.comp_def, Finset.sum_map_toList, A, Finset.sum_filter]
    rfl
  · simp only [cost_bind, q, cost_sumProd, pairs, List.length_map, Finset.length_toList,
      r, cost_op1]
    have ha : A.card ≤ (Finset.Iic E).card :=
      (Finset.card_filter_le _ _).trans (antidiagonal_card_le E e he)
    omega

set_option backward.isDefEq.respectTransparency false in
private lemma inverseStep_eq {σ : Type} [Fintype σ] [DecidableEq σ]
    (E : σ →₀ ℕ) (j : ℕ) (hj : j < (inverseOrder E).length)
    (v : (σ →₀ ℕ) → ℝ) (u : Unit) :
    inverseStep E j (Sum.elim v (tab (inverseRows E) j v)) u = inverseRows E v (j + 1) u := by
  classical
  let L := inverseOrder E
  let e := L.getD j 0
  have heL : e ∈ L := by
    change L.getD j 0 ∈ L
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have he : e ≤ E := Finset.mem_Iic.mp (Finset.mem_toList.mp
    ((inverseOrder_perm E).mem_iff.mp heL))
  have hnod : L.Nodup := (inverseOrder_perm E).nodup_iff.mpr (Finset.nodup_toList _)
  have heidx : L.idxOf e = j := by
    dsimp [e]
    rw [List.getD_eq_getElem _ _ hj]
    exact hnod.idxOf_getElem j hj
  change (if e = 0 then 1 else
    -(∑ uv ∈ Finset.HasAntidiagonal.antidiagonal e,
      if uv.2 < e then v uv.1 * tab (inverseRows E) j v (L.idxOf uv.2 + 1, ()) else 0)) =
    MvPowerSeries.coeff e (MvPowerSeries.invOfUnit (v : MvPowerSeries σ ℝ) 1)
  rw [MvPowerSeries.coeff_invOfUnit]
  simp only [inv_one, Units.val_one, neg_mul, one_mul]
  split_ifs with he0
  · rfl
  congr 1
  apply Finset.sum_congr rfl
  intro uv huv
  by_cases hlt : uv.2 < e
  · have hidx : L.idxOf uv.2 < j := by
      have hh := inverseOrder_dependency E he hlt
      change L.idxOf uv.2 < L.idxOf e at hh
      rwa [heidx] at hh
    have huvL : uv.2 ∈ L := (inverseOrder_perm E).mem_iff.mpr
      (Finset.mem_toList.mpr (Finset.mem_Iic.mpr (hlt.le.trans he)))
    have hidxlen : L.idxOf uv.2 < L.length := List.idxOf_lt_length_iff.mpr huvL
    simp only [hlt, ite_true, tab, inverseRows, show L.idxOf uv.2 + 1 ≤ j by omega]
    rw [List.getD_eq_getElem _ _ hidxlen, List.getElem_idxOf hidxlen]
    rfl
  · simp only [hlt, ite_false]

private lemma ringInvProg_exists {σ : Type} [Fintype σ] [DecidableEq σ] (E : σ →₀ ℕ) :
    ∃ p : Prog (σ →₀ ℕ) (σ →₀ ℕ), Clean p ∧
      (∀ (φ : MvPowerSeries σ ℝ) e, e ≤ E →
        p.eval (fun f => MvPowerSeries.coeff f φ) e = MvPowerSeries.coeff e (MvPowerSeries.invOfUnit φ 1)) ∧
      p.cost ≤ 3 * (Finset.Iic E).card ^ 2 := by
  classical
  let L := inverseOrder E
  have h0 : HasProg (fun v => inverseRows E v 0) 0 := by
    apply hp_congr (hp_args (ι := σ →₀ ℕ) (fun _ : Unit => .cst 0) (fun _ => rfl))
    intro v u
    cases u
    simp [Arg.eval, inverseRows]
  have ht := hp_table (inverseRows E) (inverseStep E) 0
    (fun _ => 2 * (Finset.Iic E).card + 1) h0 L.length
    (fun j hj => inverseStep_prog E j hj) (fun j hj => inverseStep_eq E j hj)
  obtain ⟨q, hq, heq, hc⟩ := ht
  let p := q.mapOut (fun e => (L.idxOf e + 1, ()))
  refine ⟨p, ⟨hq.1, fun e => hq.2 _⟩, ?_, ?_⟩
  · intro φ e he
    have hem : e ∈ L := (inverseOrder_perm E).mem_iff.mpr
      (Finset.mem_toList.mpr (Finset.mem_Iic.mpr he))
    have hi : L.idxOf e < L.length := List.idxOf_lt_length_iff.mpr hem
    simp only [p, eval_mapOut, heq, tab, inverseRows, show L.idxOf e + 1 ≤ L.length by omega,
      ite_true]
    rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi]
    rfl
  · have hl : L.length = (Finset.Iic E).card := by
      simpa using (inverseOrder_perm E).length_eq
    have hb : 1 ≤ (Finset.Iic E).card := Finset.one_le_card.mpr ⟨0, by simp⟩
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, zero_add, hl] at hc
    change q.cost ≤ _
    exact hc.trans (by nlinarith)

private lemma ringInvProg_exists_delta (d k Kq : ℕ) :
    ∃ p : Prog (Fin (k / 2 + 1) →₀ ℕ) (Fin (k / 2 + 1) →₀ ℕ), Clean p ∧
      (∀ (φ : MvPowerSeries (Fin (k / 2 + 1)) ℝ) e, e ≤ ringUpper (k / 2) d Kq →
        p.eval (fun f => MvPowerSeries.coeff f φ) e =
          MvPowerSeries.coeff e (MvPowerSeries.invOfUnit φ 1)) ∧
      p.cost ≤ 3 * deltaR d k Kq ^ 2 := by
  simpa [ringUpper_card, deltaR] using ringInvProg_exists (ringUpper (k / 2) d Kq)

private lemma sparse_product_adjustment {σ ι : Type} [Fintype ι] [DecidableEq ι]
    (φ ψ : ι → MvPowerSeries σ ℝ) (S : Finset ι)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 1)
    (hoff : ∀ i, i ∉ S → ψ i = φ i) :
    (∏ i, φ i) * (∏ i ∈ S, MvPowerSeries.invOfUnit (φ i) 1 * ψ i) = ∏ i, ψ i := by
  have hs : S ⊆ Finset.univ := Finset.subset_univ _
  calc
    _ = ((∏ i ∈ Finset.univ \ S, φ i) * ∏ i ∈ S, φ i) *
        (∏ i ∈ S, MvPowerSeries.invOfUnit (φ i) 1 * ψ i) := by
      rw [Finset.prod_sdiff hs]
    _ = (∏ i ∈ Finset.univ \ S, φ i) *
        (∏ i ∈ S, φ i * (MvPowerSeries.invOfUnit (φ i) 1 * ψ i)) := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
    _ = (∏ i ∈ Finset.univ \ S, ψ i) * ∏ i ∈ S, ψ i := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        exact (hoff i (Finset.mem_sdiff.mp hi).2).symm
      · apply Finset.prod_congr rfl
        intro i hi
        rw [← mul_assoc, MvPowerSeries.mul_invOfUnit (φ i) 1 (by simpa using hφ i), one_mul]
    _ = _ := Finset.prod_sdiff hs

private noncomputable def gaussianCoordSeries (l a : ℕ) (b : ℝ) :
    MvPowerSeries (Fin (l + 1)) ℝ :=
  fun e => b ^ (e 0) *
    ((2 * (a + (∑ r : Fin l, e r.succ) + e 0) - 1).doubleFactorial : ℝ) /
      ((e 0).factorial : ℝ)

private lemma gaussianCoordSeries_const (l : ℕ) (b : ℝ) :
    MvPowerSeries.constantCoeff (gaussianCoordSeries l 0 b) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [MvPowerSeries.coeff_apply, gaussianCoordSeries, Nat.doubleFactorial]

private lemma realizable_gaussianCoordSeries (l a : ℕ) (i : Fin n) (e : Fin (l + 1) →₀ ℕ) :
    Realizable (fun b : Fin n → ℝ => MvPowerSeries.coeff e (gaussianCoordSeries l a (b i))) := by
  change Realizable (fun b : Fin n → ℝ => b i ^ (e 0) *
    ((2 * (a + (∑ r : Fin l, e r.succ) + e 0) - 1).doubleFactorial : ℝ) /
      ((e 0).factorial : ℝ))
  exact realizable_div
    (realizable_mul (realizable_pow (realizable_inp i) (e 0)) (realizable_nat _)) (realizable_nat _)

private noncomputable def exponentSupport (β : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => β i ≠ 0)

private lemma exponentSupport_card (β : Fin n → ℕ) :
    (exponentSupport β).card ≤ ∑ i, β i := by
  classical
  calc
    _ = ∑ i ∈ exponentSupport β, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ exponentSupport β, β i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      omega
    _ ≤ ∑ i, β i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

private lemma gaussian_product_adjustment (l : ℕ) (β : Fin n → ℕ) (b : Fin n → ℝ) :
    (∏ i, gaussianCoordSeries l 0 (b i)) *
      (∏ i ∈ exponentSupport β,
        MvPowerSeries.invOfUnit (gaussianCoordSeries l 0 (b i)) 1 * gaussianCoordSeries l (β i) (b i)) =
      ∏ i, gaussianCoordSeries l (β i) (b i) := by
  classical
  apply sparse_product_adjustment _ _ (exponentSupport β)
  · intro i
    exact gaussianCoordSeries_const l (b i)
  · intro i hi
    have hβ : β i = 0 := by simpa [exponentSupport] using hi
    rw [hβ]

private abbrev MomentIndex (n d k : ℕ) :=
  Σ l : Fin (k / 2 + 1), Mono n ((k - 2 * l.1) * d / 2)

private lemma card_mono (n d : ℕ) : Fintype.card (Mono n d) = (n + d).choose d := by
  classical
  simp only [Mono, Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_multichoose,
    ← Nat.choose_symm_add (a := d) (b := n)]
  simp [Nat.add_comm]

private lemma MomentIndex_card (n d k : ℕ) :
    Fintype.card (MomentIndex n d k) = Vonce n d k := by
  change Fintype.card (Σ l : Fin (k / 2 + 1), Mono n ((k - 2 * l.1) * d / 2)) = _
  rw [Fintype.card_sigma]
  simp only [card_mono, Vonce]
  exact Fin.sum_univ_eq_sum_range
    (fun l => (n + (k - 2 * l) * d / 2).choose ((k - 2 * l) * d / 2)) (k / 2 + 1)


/-! ## Escalation: the costed program -/

private lemma hp_seq {ι κ ν : Type} {f : (ι → ℝ) → κ → ℝ} {g : (κ → ℝ) → ν → ℝ} {a b : ℕ}
    (hf : HasProg f a) (hg : HasProg g b) : HasProg (fun v => g (f v)) (a + b) := by
  have h := hp_bind hf (hp_mapIn hg (Sum.inr : κ → ι ⊕ κ))
  exact hp_congr h (fun v k => by simp [Function.comp_def])

private lemma hp_parS {ι κ : Type} [Fintype κ] [DecidableEq κ]
    {f : (ι → ℝ) → κ → ℝ} (c : κ → ℕ)
    (hf : ∀ k, HasProg (fun v (_ : Unit) => f v k) (c k)) :
    HasProg f (∑ k, c k) := by
  classical
  choose p hp ep cp using hf
  refine ⟨Prog.par p Finset.univ.toList, clean_par p hp _, ?_, ?_⟩
  · intro v k
    rw [eval_par_mem _ _ _ _ (by simp), ep]
  · rw [cost_par]
    calc
      _ ≤ (Finset.univ.toList.map fun k : κ => c k).sum := by
        apply List.sum_le_sum
        intro k _; exact cp k
      _ = _ := by rw [Finset.sum_map_toList]

private lemma hp_parL {ι κ : Type} [DecidableEq κ] {f : (ι → ℝ) → κ → ℝ} {c : ℕ}
    (l : List κ) (hf : ∀ k ∈ l, HasProg (fun v (_ : Unit) => f v k) c) :
    HasProg (fun v k => if k ∈ l then f v k else 0) (l.length * c) := by
  classical
  have hf' : ∀ k, ∃ p : Prog ι Unit, Clean p ∧ (∀ v u, p.eval v u = if k ∈ l then f v k else 0) ∧
      p.cost ≤ if k ∈ l then c else 0 := by
    intro k
    by_cases hk : k ∈ l
    · obtain ⟨p, hp, ep, cp⟩ := hf k hk
      exact ⟨p, hp, fun v u => by simp [hk, ep], by simp [hk, cp]⟩
    · refine ⟨Prog.ofArgs (fun _ => .cst 0), ⟨by simp [Prog.ofArgs], fun _ => rfl⟩, ?_, by simp⟩
      intro v u; simp [hk, Arg.eval]
  choose p hp ep cp using hf'
  refine ⟨Prog.par p l, clean_par p hp _, ?_, ?_⟩
  · intro v k
    by_cases hk : k ∈ l
    · rw [eval_par_mem _ _ _ _ hk, ep]
    · rw [eval_par_not_mem _ _ _ _ hk]; simp [hk]
  · rw [cost_par]
    calc
      _ ≤ (l.map fun _ => c).sum := by
        apply List.sum_le_sum
        intro k hk
        have := cp k
        simp only [hk, ite_true] at this
        exact this
      _ = _ := by simp

private lemma clean_of_heavy {ι κ : Type} [Fintype κ] {p : Prog ι κ}
    (h : heavyCount p = 0) : Clean p := by
  unfold heavyCount at h
  have h1 := Nat.eq_zero_of_add_eq_zero_right h
  have h2 := Nat.eq_zero_of_add_eq_zero_left h
  constructor
  · intro I hI
    have := List.sum_eq_zero_iff.mp h1 _ (List.mem_map.mpr ⟨I, hI, rfl⟩)
    omega
  · intro o
    exact (Finset.sum_eq_zero_iff.mp h2) o (Finset.mem_univ o)

private lemma hp_consts {ι κ : Type} [Fintype κ] (q : κ → ℚ) (β : ℕ)
    (hq : ∀ k, (q k).num.natAbs < 2 ^ β ∧ (q k).den < 2 ^ β) :
    HasProg (fun (_ : ι → ℝ) k => (q k : ℝ)) (4 * β * Fintype.card κ) := by
  classical
  let p : Prog ι κ := Prog.ofArgs (fun k => .cst (q k))
  have hb : ∀ r ∈ BstLean.Part41.heavyConsts p, r.num.natAbs < 2 ^ β ∧ r.den < 2 ^ β := by
    intro r hr
    simp only [BstLean.Part41.heavyConsts, p, Prog.ofArgs, List.flatMap_nil, List.nil_append,
      List.mem_filterMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hr
    obtain ⟨a, ⟨k, rfl⟩, ha⟩ := hr
    by_cases h : q k = 0 ∨ q k = 1
    · simp [h] at ha
    · simp only [h, ite_false, Option.some.injEq] at ha
      subst ha; exact hq k
  obtain ⟨p', hp', he, hc⟩ := BstLean.Part41.inline_consts p β hb
  refine ⟨p', clean_of_heavy hp', fun v k => by rw [he]; rfl, ?_⟩
  have hh : heavyCount p ≤ Fintype.card κ := by
    unfold heavyCount
    simp only [p, Prog.ofArgs, List.map_nil, List.sum_nil, zero_add]
    calc
      _ ≤ ∑ _k : κ, 1 := by
        apply Finset.sum_le_sum; intro k _
        simp only [BstLean.Part41.argHeavy]; split_ifs <;> omega
      _ = _ := by simp
  have : p.cost = 0 := rfl
  calc
    _ ≤ p.cost + 4 * β * heavyCount p := hc
    _ ≤ _ := by rw [this, zero_add]; exact Nat.mul_le_mul_left _ hh

private lemma hp_pow {ι : Type} (x : ι) (t : ℕ) : HasProg (fun v (_ : Unit) => v x ^ t) t := by
  induction t with
  | zero =>
    exact hp_congr (hp_args (fun _ : Unit => Arg.cst (ι := ι) 1) (fun _ => rfl))
      (fun v u => by simp [Arg.eval])
  | succ t ih =>
    have h := hp_bind ih (hp_op .mul (Arg.inp (Sum.inr ())) (Arg.inp (Sum.inl x)) rfl rfl)
    exact hp_congr h (fun v u => by simp [Arg.eval, Op.eval, pow_succ])

private lemma EqUpTo.inv {σ : Type} [Fintype σ] [DecidableEq σ] {E : σ →₀ ℕ}
    {φ ψ : MvPowerSeries σ ℝ} (h : EqUpTo E φ ψ) :
    EqUpTo E (MvPowerSeries.invOfUnit φ 1) (MvPowerSeries.invOfUnit ψ 1) := by
  intro e he
  induction hdeg : coeffDegree e using Nat.strong_induction_on generalizing e with
  | _ m ih =>
    rw [MvPowerSeries.coeff_invOfUnit, MvPowerSeries.coeff_invOfUnit]
    split_ifs with h0
    · rfl
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : x.1 + x.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have h1 : x.1 ≤ E := by
      rw [← hx'] at he
      exact (le_add_of_nonneg_right (by positivity : 0 ≤ x.2)).trans he
    have h2 : x.2 ≤ E := by
      rw [← hx'] at he
      exact (le_add_of_nonneg_left (by positivity : 0 ≤ x.1)).trans he
    split_ifs with hlt
    · rw [h _ h1, ih (coeffDegree x.2) (hdeg ▸ coeffDegree_strict hlt) x.2 h2 rfl]
    · rfl

private lemma EqUpTo.refl' {σ : Type} {E : σ →₀ ℕ} (φ : MvPowerSeries σ ℝ) : EqUpTo E φ φ :=
  fun _ _ => rfl

private lemma EqUpTo.listProd {σ ι : Type} [DecidableEq σ] {E : σ →₀ ℕ}
    (L : List ι) (φ ψ : ι → MvPowerSeries σ ℝ) (h : ∀ i ∈ L, EqUpTo E (φ i) (ψ i)) :
    EqUpTo E (L.map φ).prod (L.map ψ).prod := by
  induction L with
  | nil => exact EqUpTo.refl' _
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact EqUpTo.mul (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- Tables indexed by `α × β`, built from one program per `a : α`. -/
private lemma hp_rows {ι α β : Type} [Fintype α] [DecidableEq α]
    {f : (ι → ℝ) → α × β → ℝ} {c : ℕ}
    (hf : ∀ a, HasProg (fun v b => f v (a, b)) c) :
    HasProg f (Fintype.card α * c) := by
  classical
  have key : ∀ l : List α, HasProg (fun v ab => if ab.1 ∈ l then f v ab else 0) (l.length * c) := by
    intro l
    induction l with
    | nil =>
      exact hp_mono (hp_congr (hp_args (ι := ι) (κ := α × β) (fun _ => Arg.cst 0) (fun _ => rfl))
        (fun v ab => by simp [Arg.eval])) (Nat.zero_le _)
    | cons a l ih =>
      have hp := hp_mapOut (hp_pair (hf a) ih)
        (fun ab : α × β => if ab.1 = a then Sum.inl ab.2 else Sum.inr ab)
      refine hp_mono (hp_congr hp ?_) (by simp [Nat.succ_mul, Nat.add_comm])
      intro v ab
      by_cases h : ab.1 = a
      · simp only [h, ite_true, Sum.elim_inl, List.mem_cons_self]
        rw [← h]
      · simp [h]
  exact hp_congr (hp_mono (key Finset.univ.toList) (by simp)) (fun v ab => by simp)

/-! ## Ring numerator (fork) -/

private noncomputable def subBox (L Kq d l : ℕ) : Fin (L + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cases Kq (fun r : Fin L => if r.val < l then d else 0))

private noncomputable def ringN (L l d Kq : ℕ) (β : Fin n → ℕ) (b : Fin n → ℝ) : ℝ :=
  ∑ e ∈ Finset.Iic (subBox L Kq d l),
    MvPowerSeries.coeff e (∏ i, gaussianCoordSeries L (β i) (b i)) /
      rhoD (n : ℝ) (∑ i, β i + coeffDegree e)

/-- Exponent count vector of a word of monomials. -/
private def wc {s : ℕ} (w : Fin s → Mono n d) (i : Fin n) : ℕ := ∑ t, (w t).2.1.count i


/-! ## Helpers for `ring_numerator` -/

private lemma sum_count_univ (s : Multiset (Fin n)) : ∑ i, s.count i = Multiset.card s :=
  Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)

private lemma mono_ext {p q : Mono n d} (h : p.2.1 = q.2.1) : p = q := by
  obtain ⟨D, s⟩ := p
  obtain ⟨D', s'⟩ := q
  have hD : D = D' := Fin.ext (by
    have h1 := s.2
    have h2 := s'.2
    simp only at h
    rw [← h1, ← h2, h])
  subst hD
  congr 1
  exact Subtype.ext h

private noncomputable def mkMono (m : Fin n → ℕ) : Mono n d :=
  if h : ∑ i, m i ≤ d then ⟨⟨∑ i, m i, by omega⟩, (Sym.equivNatSumOfFintype (Fin n) _).symm ⟨m, rfl⟩⟩
  else default

private lemma mkMono_deg (m : Fin n → ℕ) (h : ∑ i, m i ≤ d) : (((mkMono (d := d) m).1 : ℕ)) = ∑ i, m i := by
  unfold mkMono; rw [dite_cond_eq_true (eq_true h)]

private lemma mkMono_count (m : Fin n → ℕ) (h : ∑ i, m i ≤ d) (i : Fin n) :
    (mkMono (d := d) m).2.1.count i = m i := by
  unfold mkMono; rw [dite_cond_eq_true (eq_true h)]
  change ((Sym.equivNatSumOfFintype (Fin n) _).symm ⟨m, rfl⟩ : Multiset (Fin n)).count i = m i
  rw [Sym.coe_equivNatSumOfFintype_symm_apply]
  simp [Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]

private lemma mkMono_of (p : Mono n d) : mkMono (d := d) (fun i => p.2.1.count i) = p := by
  have hs : ∑ i, p.2.1.count i ≤ d := by
    rw [sum_count_univ, p.2.2]; exact Nat.lt_succ_iff.mp p.1.2
  apply mono_ext
  ext i
  exact mkMono_count _ hs i

/-- The z-bounds. -/
private def Dz (d l : ℕ) {L : ℕ} (r : Fin L) : ℕ := if r.val < l then d else 0

private noncomputable def Eof {L : ℕ} (j : ℕ) (a : Fin L → Mono n d) : Fin (L + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cases j (fun r => ((a r).1 : ℕ)))

private noncomputable def Cof {L : ℕ} (T : Fin n → ℕ) (a : Fin L → Mono n d) :
    Fin n →₀ (Fin (L + 1) →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm (fun i =>
    Finsupp.equivFunOnFinite.symm (Fin.cases (T i) (fun r => (a r).2.1.count i)))

private noncomputable def phiIdx {L : ℕ} (x : (Σ _ : ℕ, Fin n → ℕ) × (Fin L → Mono n d)) :
    Σ _ : (Fin (L + 1) →₀ ℕ), (Fin n →₀ (Fin (L + 1) →₀ ℕ)) :=
  ⟨Eof x.1.1 x.2, Cof x.1.2 x.2⟩

private noncomputable def psiIdx {L : ℕ} (z : Σ _ : (Fin (L + 1) →₀ ℕ), (Fin n →₀ (Fin (L + 1) →₀ ℕ))) :
    (Σ _ : ℕ, Fin n → ℕ) × (Fin L → Mono n d) :=
  (⟨z.1 0, fun i => z.2 i 0⟩, fun r => mkMono (fun i => z.2 i r.succ))

private noncomputable def idxA (L l Kq : ℕ) : Finset ((Σ _ : ℕ, Fin n → ℕ) × (Fin L → Mono n d)) :=
  ((Finset.range (Kq + 1)).sigma (fun j => Finset.piAntidiag Finset.univ j)) ×ˢ
    Fintype.piFinset (fun r : Fin L => Finset.univ.filter (fun p : Mono n d => (p.1 : ℕ) ≤ Dz d l r))

private noncomputable def idxB (L l Kq : ℕ) :
    Finset (Σ _ : (Fin (L + 1) →₀ ℕ), (Fin n →₀ (Fin (L + 1) →₀ ℕ))) :=
  (Finset.Iic (subBox L Kq d l)).sigma (fun e => Finset.finsuppAntidiag Finset.univ e)

private lemma subBox_zero (L Kq d l : ℕ) : subBox L Kq d l 0 = Kq := by
  simp [subBox]

private lemma subBox_succ (L Kq d l : ℕ) (r : Fin L) : subBox L Kq d l r.succ = Dz d l r := by
  simp [subBox, Dz]

private lemma Dz_le (d l : ℕ) {L : ℕ} (r : Fin L) : Dz d l r ≤ d := by
  unfold Dz; split_ifs <;> omega

private lemma idx_bij {L : ℕ} (l Kq : ℕ) (F : (Σ _ : (Fin (L + 1) →₀ ℕ), (Fin n →₀ (Fin (L + 1) →₀ ℕ))) → ℝ) :
    ∑ x ∈ idxA (n := n) (d := d) L l Kq, F (phiIdx x) = ∑ z ∈ idxB (n := n) (d := d) L l Kq, F z := by
  classical
  apply Finset.sum_nbij' phiIdx psiIdx
  · rintro ⟨⟨j, T⟩, a⟩ hx
    simp only [idxA, Finset.mem_product, Finset.mem_sigma, Finset.mem_range,
      Finset.mem_piAntidiag, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx
    obtain ⟨⟨hj, hT, -⟩, ha⟩ := hx
    simp only [idxB, phiIdx, Finset.mem_sigma, Finset.mem_Iic, Finset.mem_finsuppAntidiag]
    refine ⟨?_, ?_, by simp⟩
    · rw [Finsupp.le_def]
      intro r
      cases r using Fin.cases with
      | zero => simp [Eof, subBox_zero]; omega
      | succ r => simpa [Eof, subBox_succ] using ha r
    · ext r
      rw [Finsupp.finsetSum_apply]
      cases r using Fin.cases with
      | zero => simpa [Eof, Cof] using hT
      | succ r =>
        simp only [Cof, Eof, Finsupp.coe_equivFunOnFinite_symm, Fin.cases_succ]
        exact (sum_count_univ _).trans (a r).2.2
  · rintro ⟨e, c⟩ hz
    simp only [idxB, Finset.mem_sigma, Finset.mem_Iic, Finset.mem_finsuppAntidiag] at hz
    obtain ⟨he, hc, -⟩ := hz
    rw [Finsupp.le_def] at he
    have hsum : ∀ r, ∑ i, c i r = e r := by
      intro r; rw [← hc, Finsupp.finsetSum_apply]
    simp only [idxA, psiIdx, Finset.mem_product, Finset.mem_sigma, Finset.mem_range,
      Finset.mem_piAntidiag, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, hsum 0, by simp⟩, ?_⟩
    · have := he 0; rw [subBox_zero] at this; omega
    · intro r
      have h1 := he r.succ
      rw [subBox_succ] at h1
      have h2 : ∑ i, c i r.succ ≤ d := (hsum r.succ).symm ▸ h1.trans (Dz_le d l r)
      rw [mkMono_deg _ h2, hsum r.succ]; exact h1
  · rintro ⟨⟨j, T⟩, a⟩ hx
    simp only [psiIdx, phiIdx]
    refine Prod.ext (Sigma.ext ?_ (heq_of_eq ?_)) (funext fun r => ?_)
    · simp [Eof]
    · funext i; simp [Cof]
    · have : (fun i => (Cof T a) i r.succ) = fun i => (a r).2.1.count i := by
        funext i; simp [Cof]
      simp only [this]
      exact mkMono_of (a r)
  · rintro ⟨e, c⟩ hz
    simp only [idxB, Finset.mem_sigma, Finset.mem_Iic, Finset.mem_finsuppAntidiag] at hz
    obtain ⟨he, hc, -⟩ := hz
    rw [Finsupp.le_def] at he
    have hsum : ∀ r, ∑ i, c i r = e r := by
      intro r; rw [← hc, Finsupp.finsetSum_apply]
    have h2 : ∀ r : Fin L, ∑ i, c i r.succ ≤ d := fun r =>
      (hsum r.succ).symm ▸ ((subBox_succ L Kq d l r) ▸ he r.succ).trans (Dz_le d l r)
    simp only [psiIdx, phiIdx]
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · ext r
      cases r using Fin.cases with
      | zero => simp [Eof]
      | succ r => simp [Eof, mkMono_deg _ (h2 r), hsum]
    · ext i r
      cases r using Fin.cases with
      | zero => simp [Cof]
      | succ r =>
        simp only [Cof, Finsupp.coe_equivFunOnFinite_symm, Fin.cases_succ]
        exact mkMono_count _ (h2 r) i
  · intro x hx; rfl


private lemma monoVal_eq (x : Fin n → ℝ) (s : Multiset (Fin n)) :
    BstLean.Part36.monoVal x s = ∏ i, x i ^ s.count i := by
  classical
  unfold BstLean.Part36.monoVal
  rw [Finset.prod_multiset_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi), pow_zero]

private noncomputable def msOf (e : Fin n → ℕ) : Multiset (Fin n) := ∑ i, e i • ({i} : Multiset (Fin n))

private lemma count_msOf (e : Fin n → ℕ) (i : Fin n) : (msOf e).count i = e i := by
  classical
  simp [msOf, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]

private lemma card_msOf (e : Fin n → ℕ) : Multiset.card (msOf e) = ∑ i, e i := by
  simp [msOf, Multiset.card_sum]

private lemma mono_integral (hn : 1 ≤ n) (e : Fin n → ℕ) :
    (∫ x, ∏ i, x i ^ e i ∂uniformSphere n) =
      (∏ i, BstLean.Part29.gaussMom (e i)) / rhoD (n : ℝ) ((∑ i, e i) / 2) := by
  have h := (BstLean.Part36.sphere_multiset (uniformSphere n)
    (BstLean.Part33.uniformSphere_prod n _ hn) (msOf e) le_rfl).2
  simp only [monoVal_eq, count_msOf, card_msOf] at h
  rw [h]
  simp [BstLean.Part36.gpm, count_msOf]

private lemma mono_integrable (hn : 1 ≤ n) (e : Fin n → ℕ) :
    Integrable (fun x : Fin n → ℝ => ∏ i, x i ^ e i) (uniformSphere n) :=
  sphere_cont_integrable hn (by fun_prop)

private lemma prodW (x : Fin n → ℝ) {s : ℕ} (w : Fin s → Mono n d) :
    ∏ t, phiM x (w t) = ∏ i, x i ^ wc w i := by
  simp only [phiM, monoVal_eq, wc]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow_eq_pow_sum]

private lemma prod_ite_lt (A : ℝ) {L l : ℕ} (hl : l ≤ L) :
    ∏ r : Fin L, (if r.val < l then A else 1) = A ^ l := by
  rw [Fin.prod_univ_eq_prod_range (fun r => if r < l then A else 1) L,
    ← Finset.prod_range_mul_prod_Ico _ hl]
  rw [Finset.prod_congr rfl (fun r hr => if_pos (Finset.mem_range.mp hr)),
    Finset.prod_const, Finset.card_range]
  rw [Finset.prod_eq_one (fun r hr => if_neg (by have := (Finset.mem_Ico.mp hr).1; omega)),
    mul_one]

private lemma sum_deg_zero (f : Mono n d → ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p : Mono n d => (p.1 : ℕ) ≤ 0), f p = f default := by
  have : Finset.univ.filter (fun p : Mono n d => (p.1 : ℕ) ≤ 0) = {default} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      apply mono_ext
      have h1 : Multiset.card p.2.1 = 0 := by rw [p.2.2]; omega
      rw [Multiset.card_eq_zero.mp h1]
      rfl
    · rintro rfl; simp; rfl
  rw [this, Finset.sum_singleton]

private lemma phiSq_pow (x : Fin n → ℝ) {L l : ℕ} (hl : l ≤ L) :
    phiSq d x ^ l = ∑ a ∈ Fintype.piFinset (fun r : Fin L =>
        Finset.univ.filter (fun p : Mono n d => (p.1 : ℕ) ≤ Dz d l r)),
      ∏ i, x i ^ (2 * ∑ r, (a r).2.1.count i) := by
  have h1 : phiSq d x ^ l = ∏ r : Fin L, ∑ p ∈ Finset.univ.filter
      (fun p : Mono n d => (p.1 : ℕ) ≤ Dz d l r), phiM x p ^ 2 := by
    rw [← prod_ite_lt (phiSq d x) hl]
    apply Finset.prod_congr rfl
    intro r _
    unfold Dz
    split_ifs with h
    · rw [Finset.filter_true_of_mem (fun p _ => Nat.lt_succ_iff.mp p.1.2)]
      rfl
    · rw [sum_deg_zero]
      show (1 : ℝ) = (Multiset.map x (0 : Multiset (Fin n))).prod ^ 2
      simp
  rw [h1, Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [phiM, monoVal_eq]
  simp_rw [← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => by ring)

private lemma taylor_qth (x b : Fin n → ℝ) (Kq : ℕ) :
    BstLean.Part37.taylorExp Kq (BstLean.Part37.qth b x) =
      ∑ y ∈ (Finset.range (Kq + 1)).sigma (fun j => Finset.piAntidiag Finset.univ j),
        ∏ i, (b i ^ y.2 i / ((y.2 i).factorial : ℝ) * x i ^ (2 * y.2 i)) := by
  unfold BstLean.Part37.taylorExp BstLean.Part37.qth
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  have hs : ∑ i, T i = j := (Finset.mem_piAntidiag.mp hT).1
  have hm := Nat.multinomial_spec Finset.univ T
  rw [hs] at hm
  have hm' : ((∏ i, ((T i).factorial : ℝ)) * (Nat.multinomial Finset.univ T : ℝ)) =
      (j.factorial : ℝ) := by exact_mod_cast hm
  have hpos : (0 : ℝ) < ∏ i, ((T i).factorial : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos _)
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, ← hm']
  have hne : (Nat.multinomial Finset.univ T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  field_simp
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

private lemma integrand_expand (x b : Fin n → ℝ) {s : ℕ} (L l Kq : ℕ) (hl : l ≤ L)
    (w : Fin s → Mono n d) :
    (phiSq d x ^ l * ∏ t, phiM x (w t)) *
      BstLean.Part37.taylorExp Kq (BstLean.Part37.qth b x) =
      ∑ y ∈ (Finset.range (Kq + 1)).sigma (fun j => Finset.piAntidiag Finset.univ j),
        ∑ a ∈ Fintype.piFinset (fun r : Fin L =>
            Finset.univ.filter (fun p : Mono n d => (p.1 : ℕ) ≤ Dz d l r)),
          (∏ i, b i ^ y.2 i / ((y.2 i).factorial : ℝ)) *
            ∏ i, x i ^ (wc w i + 2 * y.2 i + 2 * ∑ r, (a r).2.1.count i) := by
  rw [phiSq_pow x hl, prodW, taylor_qth, Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring


private lemma coeff_Cof {L : ℕ} (T : Fin n → ℕ) (a : Fin L → Mono n d) (i : Fin n) (c : ℕ) (bb : ℝ) :
    MvPowerSeries.coeff (Cof T a i) (gaussianCoordSeries L c bb) =
      bb ^ T i * ((2 * (c + ∑ r, (a r).2.1.count i + T i) - 1).doubleFactorial : ℝ) /
        ((T i).factorial : ℝ) := by
  show gaussianCoordSeries L c bb (Cof T a i) = _
  simp [gaussianCoordSeries, Cof]

private lemma coeffDegree_Eof {L : ℕ} (j : ℕ) (a : Fin L → Mono n d) :
    coeffDegree (Eof j a) = j + ∑ r, ((a r).1 : ℕ) := by
  simp [coeffDegree, Eof, Fin.sum_univ_succ]

private lemma sumA {L : ℕ} (a : Fin L → Mono n d) :
    ∑ i, ∑ r, (a r).2.1.count i = ∑ r, ((a r).1 : ℕ) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => (sum_count_univ _).trans (a r).2.2)

private lemma term_eq {L : ℕ} (β : Fin n → ℕ) (b : Fin n → ℝ) (j : ℕ) (T : Fin n → ℕ) (hT : ∑ i, T i = j)
    (a : Fin L → Mono n d) :
    (∏ i, b i ^ T i / ((T i).factorial : ℝ)) *
      ((∏ i, BstLean.Part29.gaussMom (2 * β i + 2 * T i + 2 * ∑ r, (a r).2.1.count i)) /
        rhoD (n : ℝ) ((∑ i, (2 * β i + 2 * T i + 2 * ∑ r, (a r).2.1.count i)) / 2)) =
      (∏ i, MvPowerSeries.coeff (Cof T a i) (gaussianCoordSeries L (β i) (b i))) /
        rhoD (n : ℝ) (∑ i, β i + coeffDegree (Eof j a)) := by
  have hdeg : (∑ i, (2 * β i + 2 * T i + 2 * ∑ r, (a r).2.1.count i)) / 2 =
      ∑ i, β i + coeffDegree (Eof j a) := by
    rw [coeffDegree_Eof, ← hT, ← sumA]
    have : ∑ i, (2 * β i + 2 * T i + 2 * ∑ r, (a r).2.1.count i) =
        2 * (∑ i, β i + (∑ i, T i + ∑ i, ∑ r, (a r).2.1.count i)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hdeg, ← mul_div_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [coeff_Cof]
  have h2 : 2 * β i + 2 * T i + 2 * ∑ r, (a r).2.1.count i =
      2 * (β i + ∑ r, (a r).2.1.count i + T i) := by ring
  rw [h2]
  simp only [BstLean.Part29.gaussMom, even_two_mul, if_true]
  ring

private theorem ring_numerator (hn : 1 ≤ n) {s : ℕ} (L l Kq : ℕ) (hl : l ≤ L) (w : Fin s → Mono n d)
    (b : Fin n → ℝ) :
    (∫ x, (phiSq d x ^ l * ∏ t, phiM x (w t)) *
      BstLean.Part37.taylorExp Kq (BstLean.Part37.qth b x) ∂uniformSphere n) =
      if ∀ i, Even (wc w i) then ringN L l d Kq (fun i => wc w i / 2) b else 0 := by
  classical
  have hI : (∫ x, (phiSq d x ^ l * ∏ t, phiM x (w t)) *
      BstLean.Part37.taylorExp Kq (BstLean.Part37.qth b x) ∂uniformSphere n) =
      ∑ y ∈ (Finset.range (Kq + 1)).sigma (fun j => Finset.piAntidiag Finset.univ j),
        ∑ a ∈ Fintype.piFinset (fun r : Fin L =>
            Finset.univ.filter (fun p : Mono n d => (p.1 : ℕ) ≤ Dz d l r)),
          (∏ i, b i ^ y.2 i / ((y.2 i).factorial : ℝ)) *
            ((∏ i, BstLean.Part29.gaussMom (wc w i + 2 * y.2 i + 2 * ∑ r, (a r).2.1.count i)) /
              rhoD (n : ℝ) ((∑ i, (wc w i + 2 * y.2 i + 2 * ∑ r, (a r).2.1.count i)) / 2)) := by
    simp_rw [integrand_expand _ b L l Kq hl w]
    rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _
      (fun a _ => (mono_integrable hn _).const_mul _))]
    apply Finset.sum_congr rfl
    intro y _
    rw [integral_finsetSum _ (fun a _ => (mono_integrable hn _).const_mul _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_const_mul, mono_integral hn]
  rw [hI]
  split_ifs with hev
  · have hβ : ∀ i, wc w i = 2 * (wc w i / 2) := fun i => (Nat.two_mul_div_two_of_even (hev i)).symm
    have hR : ringN L l d Kq (fun i => wc w i / 2) b =
        ∑ z ∈ idxB (n := n) (d := d) L l Kq,
          (∏ i, MvPowerSeries.coeff (z.2 i) (gaussianCoordSeries L (wc w i / 2) (b i))) /
            rhoD (n : ℝ) (∑ i, wc w i / 2 + coeffDegree z.1) := by
      unfold ringN idxB
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro e _
      rw [MvPowerSeries.coeff_prod, Finset.sum_div]
    rw [hR, ← idx_bij, idxA, Finset.sum_product]
    apply Finset.sum_congr rfl
    rintro ⟨j, T⟩ hy
    have hT : ∑ i, T i = j := (Finset.mem_piAntidiag.mp (Finset.mem_sigma.mp hy).2).1
    apply Finset.sum_congr rfl
    intro a _
    have := term_eq (fun i => wc w i / 2) b j T hT a
    simp only [← hβ] at this
    exact this
  · push Not at hev
    obtain ⟨i0, hi0⟩ := hev
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro a _
    have : ¬ Even (wc w i0 + 2 * y.2 i0 + 2 * ∑ r, (a r).2.1.count i0) := by
      rw [Nat.even_add, Nat.even_add]; simp [hi0]
    have hz : ∏ i, BstLean.Part29.gaussMom (wc w i + 2 * y.2 i + 2 * ∑ r, (a r).2.1.count i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i0) (by unfold BstLean.Part29.gaussMom; exact if_neg this)
    rw [hz]; simp


/-! ## Ring constants built from one -/

private abbrev CIdx (M Kq : ℕ) := Fin (M + 1) ⊕ Fin (Kq + 1) ⊕ Fin (M + 1)

private def rhoN (n m : ℕ) : ℕ := ∏ r ∈ Finset.range m, (n + 2 * r)

private def constN (n M Kq : ℕ) : CIdx M Kq → ℕ
  | .inl m => (2 * (m : ℕ) - 1).doubleFactorial
  | .inr (.inl t) => (t : ℕ).factorial
  | .inr (.inr m) => rhoN n m

private lemma df_le (m : ℕ) : (2 * m - 1).doubleFactorial ≤ (2 * m) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m =>
      have he : 2 * (m + 1 + 1) - 1 = (2 * (m + 1) - 1) + 2 := by omega
      rw [he, Nat.doubleFactorial_add_two]
      have h1 : (2 * (m + 1)) ^ (m + 1) ≤ (2 * (m + 1 + 1)) ^ (m + 1) :=
        Nat.pow_le_pow_left (by omega) _
      calc
        _ ≤ (2 * (m + 1) - 1 + 2) * (2 * (m + 1)) ^ (m + 1) := Nat.mul_le_mul_left _ ih
        _ ≤ (2 * (m + 1 + 1)) * (2 * (m + 1 + 1)) ^ (m + 1) :=
          Nat.mul_le_mul (by omega) h1
        _ = _ := by ring

private lemma pow_lt_bR (n d k Kq X m : ℕ) (hX : X ≤ n + 2 * (k * d + Kq))
    (hm : m ≤ k * d + Kq) : X ^ m < 2 ^ bR n d k Kq := by
  set Y := n + 2 * (k * d + Kq)
  set g := Nat.log 2 Y
  have hY : Y < 2 ^ (g + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h1 : X ^ m ≤ 2 ^ ((g + 1) * m) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (hX.trans hY.le) _
  have h2 : (g + 1) * m < bR n d k Kq := by
    unfold bR
    have : m < (k * d + Kq + 2) ^ 2 := by nlinarith
    calc
      (g + 1) * m < (g + 2) * (k * d + Kq + 2) ^ 2 := by
        apply Nat.mul_lt_mul_of_le_of_lt (by omega) this (by omega)
      _ = _ := by ring
  exact h1.trans_lt (Nat.pow_lt_pow_right (by norm_num) h2)

private lemma constN_lt (n d k Kq : ℕ) (c : CIdx (k * d + Kq) Kq) :
    constN n (k * d + Kq) Kq c < 2 ^ bR n d k Kq := by
  rcases c with m | t | m
  · have hm := m.2
    exact (df_le m).trans_lt (pow_lt_bR n d k Kq _ _ (by omega) (by omega))
  · have ht := t.2
    exact (Nat.factorial_le_pow _).trans_lt (pow_lt_bR n d k Kq _ _ (by omega) (by omega))
  · have hm := m.2
    have h : rhoN n m ≤ (n + 2 * (m : ℕ)) ^ (m : ℕ) := by
      unfold rhoN
      have := Finset.prod_le_pow_card (Finset.range m) (fun r => n + 2 * r) (n + 2 * (m : ℕ))
        (fun r hr => by have := Finset.mem_range.mp hr; omega)
      simpa using this
    exact h.trans_lt (pow_lt_bR n d k Kq _ _ (by omega) (by omega))

/-- Stage 1: from `b`, keep `b` and add the constants and the powers `b_i^t`, `t ≤ Kq`. -/
private abbrev In1 (n M Kq : ℕ) := Fin n ⊕ (CIdx M Kq ⊕ (Fin n × Fin (Kq + 1)))

private noncomputable def S1 (n M Kq : ℕ) (b : Fin n → ℝ) : In1 n M Kq → ℝ :=
  Sum.elim b (Sum.elim (fun c => (constN n M Kq c : ℝ)) (fun it => b it.1 ^ (it.2 : ℕ)))

private lemma stage1 (n d k Kq : ℕ) :
    HasProg (fun b => S1 n (k * d + Kq) Kq b)
      (4 * bR n d k Kq * (2 * (k * d + Kq + 1) + (Kq + 1)) + n * ((Kq + 1) * Kq)) := by
  have hc := hp_consts (ι := Fin n) (fun c : CIdx (k * d + Kq) Kq => (constN n (k * d + Kq) Kq c : ℚ))
    (bR n d k Kq) (fun c => by
      have h := constN_lt n d k Kq c
      constructor
      · simpa using h
      · simp only [Rat.den_natCast]; exact Nat.one_lt_two_pow_iff.mpr (by
          unfold bR; positivity))
  have hp : HasProg (fun (b : Fin n → ℝ) (it : Fin n × Fin (Kq + 1)) => b it.1 ^ (it.2 : ℕ))
      (n * ((Kq + 1) * Kq)) := by
    have := hp_rows (α := Fin n) (β := Fin (Kq + 1)) (ι := Fin n)
      (f := fun b it => b it.1 ^ (it.2 : ℕ)) (c := (Kq + 1) * Kq) (fun i => by
        have h := hp_par (ι := Fin n) (κ := Fin (Kq + 1)) (c := Kq)
          (f := fun b (t : Fin (Kq + 1)) => b i ^ (t : ℕ))
          (fun t => hp_mono (hp_pow i t) (by have := t.2; omega))
        simpa using h)
    simpa using this
  have h := hp_keep (hp_pair hc hp)
  refine hp_mono (hp_congr h ?_) ?_
  · intro b o
    rcases o with i | c | it <;> simp [S1]
  · simp only [CIdx, Fintype.card_sum, Fintype.card_fin]
    apply Nat.add_le_add_right; apply le_of_eq; ring

/-! ## Stage 2: the shared product and the inverses -/

private def toSer {σ : Type} (g : (σ →₀ ℕ) → ℝ) : MvPowerSeries σ ℝ := g

private lemma coeff_toSer {σ : Type} (g : (σ →₀ ℕ) → ℝ) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (toSer g) = g e := rfl

section stage2
variable (n d k Kq : ℕ)

private def dfI (m : ℕ) : In1 n (k * d + Kq) Kq :=
  .inr (.inl (.inl ⟨min m (k * d + Kq), by omega⟩))
private def faI (t : ℕ) : In1 n (k * d + Kq) Kq :=
  .inr (.inl (.inr (.inl ⟨min t Kq, by omega⟩)))
private def rhoI (m : ℕ) : In1 n (k * d + Kq) Kq :=
  .inr (.inl (.inr (.inr ⟨min m (k * d + Kq), by omega⟩)))
private def powI (i : Fin n) (t : ℕ) : In1 n (k * d + Kq) Kq :=
  .inr (.inr (i, ⟨min t Kq, by omega⟩))

private noncomputable def coefVal (u : In1 n (k * d + Kq) Kq → ℝ) (a : ℕ) (i : Fin n)
    (e : Fin (k / 2 + 1) →₀ ℕ) : ℝ :=
  u (powI n d k Kq i (e 0)) * u (dfI n d k Kq (a + ∑ r : Fin (k / 2), e r.succ + e 0)) /
    u (faI n d k Kq (e 0))

private lemma hp_coef (a : ℕ) (i : Fin n) (e : Fin (k / 2 + 1) →₀ ℕ) :
    HasProg (fun u (_ : Unit) => coefVal n d k Kq u a i e) 2 := by
  have h := hp_bind (hp_op .mul (Arg.inp (powI n d k Kq i (e 0)))
      (Arg.inp (dfI n d k Kq (a + ∑ r : Fin (k / 2), e r.succ + e 0))) rfl rfl)
    (hp_op .div (Arg.inp (Sum.inr ())) (Arg.inp (Sum.inl (faI n d k Kq (e 0)))) rfl rfl)
  exact hp_congr h (fun u _ => by simp [Arg.eval, Op.eval, coefVal])

private lemma half_mul_le : k / 2 * d ≤ k * d / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  calc k / 2 * d * 2 = (k / 2 * 2) * d := by ring
    _ ≤ k * d := Nat.mul_le_mul_right _ (Nat.div_mul_le_self k 2)

private lemma sum_succ_le (e : Fin (k / 2 + 1) →₀ ℕ) (he : e ≤ ringUpper (k / 2) d Kq) :
    ∑ r : Fin (k / 2), e r.succ ≤ k / 2 * d := by
  have h : ∀ r : Fin (k / 2), e r.succ ≤ d := by
    intro r
    have := he r.succ
    simpa [ringUpper] using this
  calc ∑ r : Fin (k / 2), e r.succ ≤ ∑ _r : Fin (k / 2), d := Finset.sum_le_sum (fun r _ => h r)
    _ = _ := by simp

private lemma e0_le (e : Fin (k / 2 + 1) →₀ ℕ) (he : e ≤ ringUpper (k / 2) d Kq) : e 0 ≤ Kq := by
  have := he 0
  simpa [ringUpper] using this

private lemma coefVal_eq (b : Fin n → ℝ) (a : ℕ) (ha : a ≤ k * d / 2) (i : Fin n)
    (e : Fin (k / 2 + 1) →₀ ℕ) (he : e ≤ ringUpper (k / 2) d Kq) :
    coefVal n d k Kq (S1 n (k * d + Kq) Kq b) a i e =
      MvPowerSeries.coeff e (gaussianCoordSeries (k / 2) a (b i)) := by
  have h1 := sum_succ_le d k Kq e he
  have h2 := e0_le d k Kq e he
  have h3 := half_mul_le d k
  have h4 : k * d / 2 + k * d / 2 ≤ k * d := by omega
  have hm : min (a + ∑ r : Fin (k / 2), e r.succ + e 0) (k * d + Kq) =
      a + ∑ r : Fin (k / 2), e r.succ + e 0 := min_eq_left (by omega)
  have ht : min (e 0) Kq = e 0 := min_eq_left h2
  simp only [coefVal, S1, powI, dfI, faI, Sum.elim_inr, Sum.elim_inl, constN, hm, ht]
  rfl

private abbrev Out2a := In1 n (k * d + Kq) Kq ⊕ (Fin n × (Fin (k / 2 + 1) →₀ ℕ))
private abbrev Out2 := Out2a n d k Kq ⊕ ((Fin n × (Fin (k / 2 + 1) →₀ ℕ)) ⊕ (Fin (k / 2 + 1) →₀ ℕ))

private lemma card_box : (Finset.Iic (ringUpper (k / 2) d Kq)).card = deltaR d k Kq := by
  rw [ringUpper_card]; rfl

private lemma stage2 : ∃ F : (In1 n (k * d + Kq) Kq → ℝ) → Out2 n d k Kq → ℝ,
    HasProg F (n * deltaR d k Kq * 2 + n * (3 * deltaR d k Kq ^ 2) + 2 * n * deltaR d k Kq ^ 2) ∧
    ∀ b : Fin n → ℝ,
      (∀ o, F (S1 n (k * d + Kq) Kq b) (.inl (.inl o)) = S1 n (k * d + Kq) Kq b o) ∧
      (∀ i, ∀ e ≤ ringUpper (k / 2) d Kq, F (S1 n (k * d + Kq) Kq b) (.inr (.inl (i, e))) =
        MvPowerSeries.coeff e (MvPowerSeries.invOfUnit (gaussianCoordSeries (k / 2) 0 (b i)) 1)) ∧
      (∀ e ≤ ringUpper (k / 2) d Kq, F (S1 n (k * d + Kq) Kq b) (.inr (.inr e)) =
        MvPowerSeries.coeff e (∏ i, gaussianCoordSeries (k / 2) 0 (b i))) := by
  classical
  set E := ringUpper (k / 2) d Kq
  set l0 := ((Finset.univ : Finset (Fin n)) ×ˢ Finset.Iic E).toList
  have h0 := hp_parL (f := fun u (ie : Fin n × (Fin (k / 2 + 1) →₀ ℕ)) =>
    coefVal n d k Kq u 0 ie.1 ie.2) l0 (fun ie _ => hp_coef n d k Kq 0 ie.1 ie.2)
  have h2a := hp_keep h0
  obtain ⟨ip, hip, hie, hic⟩ := ringInvProg_exists E
  have hinv : HasProg (fun (w : Out2a n d k Kq → ℝ) (ie : Fin n × (Fin (k / 2 + 1) →₀ ℕ)) =>
      ip.eval (fun e => w (.inr (ie.1, e))) ie.2) (n * (3 * deltaR d k Kq ^ 2)) := by
    have := hp_rows (α := Fin n) (β := Fin (k / 2 + 1) →₀ ℕ)
      (f := fun (w : Out2a n d k Kq → ℝ) (ie : Fin n × (Fin (k / 2 + 1) →₀ ℕ)) =>
        ip.eval (fun e => w (.inr (ie.1, e))) ie.2) (c := 3 * deltaR d k Kq ^ 2) (fun i => by
          have h := hp_mapIn (⟨ip, hip, fun _ _ => rfl, by rw [← card_box]; exact hic⟩ :
            HasProg (fun v e => ip.eval v e) (3 * deltaR d k Kq ^ 2))
            (fun e => (Sum.inr (i, e) : Out2a n d k Kq))
          exact hp_congr h (fun w e => rfl))
    simpa using this
  have hP : HasProg (fun (w : Out2a n d k Kq → ℝ) e =>
      (ringProdProg E (List.finRange n)).eval (fun ie => w (.inr ie)) e)
      (2 * n * deltaR d k Kq ^ 2) := by
    have h := hp_mapIn (⟨ringProdProg E (List.finRange n), ringProdProg_clean E _, fun _ _ => rfl,
      by have := ringProdProg_cost E (List.finRange n)
         rw [show (Finset.Iic E).card = deltaR d k Kq from card_box d k Kq,
           List.length_finRange] at this
         exact this⟩ :
        HasProg (fun v e => (ringProdProg E (List.finRange n)).eval v e) (2 * n * deltaR d k Kq ^ 2))
      (fun ie => (Sum.inr ie : Out2a n d k Kq))
    exact hp_congr h (fun w e => rfl)
  have h2b := hp_keep (hp_pair hinv hP)
  have hall := hp_seq h2a h2b
  refine ⟨_, hp_mono hall ?_, ?_⟩
  · have hl : l0.length = n * deltaR d k Kq := by
      rw [Finset.length_toList, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        card_box d k Kq]
    rw [hl]; omega
  intro b
  have hie' : ∀ g : (Fin (k / 2 + 1) →₀ ℕ) → ℝ, ∀ e ≤ E,
      ip.eval g e = MvPowerSeries.coeff e (MvPowerSeries.invOfUnit (toSer g) 1) :=
    fun g e he => hie (toSer g) e he
  have hpe : ∀ g : Fin n × (Fin (k / 2 + 1) →₀ ℕ) → ℝ, ∀ e ≤ E,
      (ringProdProg E (List.finRange n)).eval g e =
        MvPowerSeries.coeff e (∏ i, toSer (fun f => g (i, f))) := by
    intro g e he
    have h := ringProdProg_eval E e he (List.finRange n) (fun i => toSer (fun f => g (i, f)))
    rw [Fin.prod_univ_def]
    exact h
  have hG : ∀ i, ∀ e ≤ E, (if (i, e) ∈ l0 then coefVal n d k Kq (S1 n (k * d + Kq) Kq b) 0 i e
      else 0) = MvPowerSeries.coeff e (gaussianCoordSeries (k / 2) 0 (b i)) := by
    intro i e he
    rw [if_pos (by simp [l0, Finset.mem_Iic.mpr he])]
    exact coefVal_eq n d k Kq b 0 (Nat.zero_le _) i e he
  refine ⟨fun o => rfl, ?_, ?_⟩
  · intro i e he
    simp only [Sum.elim_inr, Sum.elim_inl]
    refine (hie' _ e he).trans (EqUpTo.inv ?_ e he)
    intro f hf
    simp only [coeff_toSer, Sum.elim_inr]
    rw [if_pos (by simp [l0, Finset.mem_Iic.mpr hf])]
    exact coefVal_eq n d k Kq b 0 (Nat.zero_le _) i f hf
  · intro e he
    simp only [Sum.elim_inr, Sum.elim_inl]
    refine (hpe _ e he).trans ?_
    rw [Fin.prod_univ_def, Fin.prod_univ_def]
    refine EqUpTo.listProd _ _ _ (fun i _ f hf => ?_) e he
    simp only [coeff_toSer]
    rw [if_pos (by simp [l0, Finset.mem_Iic.mpr hf])]
    exact coefVal_eq n d k Kq b 0 (Nat.zero_le _) i f hf

end stage2

/-! ## Stage 3: one value per moment index -/

private lemma hp_sumL {κ : Type} (l : List κ) :
    HasProg (fun (v : κ → ℝ) (_ : Unit) => (l.map v).sum) (l.length - 1) := by
  refine ⟨Prog.sumArgs (l.map Arg.inp), clean_sumArgs _ ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    rfl
  · intro v u
    simp [eval_sumArgs, List.map_map, Function.comp_def, Arg.eval]
  · simp [cost_sumArgs]

private lemma subBox_le_upper (L Kq d l : ℕ) : subBox L Kq d l ≤ ringUpper L d Kq := by
  intro r
  refine Fin.cases ?_ (fun r => ?_) r
  · simp [subBox, ringUpper]
  · simp only [subBox, ringUpper, Finsupp.coe_equivFunOnFinite_symm, Fin.cases_succ]
    split_ifs <;> omega

section stage3
variable (n d k Kq : ℕ)

private def toOut2 (o : In1 n (k * d + Kq) Kq) : Out2 n d k Kq := .inl (.inl o)

/-- What stage 2 guarantees about its outputs. -/
private def Good2 (b : Fin n → ℝ) (z : Out2 n d k Kq → ℝ) : Prop :=
  (∀ o, z (toOut2 n d k Kq o) = S1 n (k * d + Kq) Kq b o) ∧
  (∀ i, ∀ e ≤ ringUpper (k / 2) d Kq, z (.inr (.inl (i, e))) =
    MvPowerSeries.coeff e (MvPowerSeries.invOfUnit (gaussianCoordSeries (k / 2) 0 (b i)) 1)) ∧
  (∀ e ≤ ringUpper (k / 2) d Kq, z (.inr (.inr e)) =
    MvPowerSeries.coeff e (∏ i, gaussianCoordSeries (k / 2) 0 (b i)))

private abbrev MI := MomentIndex n d k

private def betaOf (x : MI n d k) (i : Fin n) : ℕ := x.2.2.1.count i

private noncomputable def Qv : ℕ :=
  k * d * deltaR d k Kq + 2 * (1 + k * d) * deltaR d k Kq ^ 2 + 2 * deltaR d k Kq

private lemma betaOf_sum (x : MI n d k) : ∑ i, betaOf n d k x i ≤ (k - 2 * x.1.1) * d / 2 := by
  unfold betaOf
  rw [sum_count_univ, x.2.2.2]
  exact Nat.lt_succ_iff.mp x.2.1.2

private lemma stage3_val (x : MI n d k) : ∃ F : (Out2 n d k Kq → ℝ) → Unit → ℝ,
    HasProg F (Qv d k Kq) ∧ ∀ b z, Good2 n d k Kq b z →
      F z () = ringN (k / 2) x.1.1 d Kq (betaOf n d k x) b := by
  classical
  set E := ringUpper (k / 2) d Kq
  set β := betaOf n d k x
  set S := exponentSupport β
  set El := subBox (k / 2) Kq d x.1.1
  have hβ := betaOf_sum n d k x
  have hS : S.card ≤ k * d / 2 := (exponentSupport_card β).trans (hβ.trans (by
    apply Nat.div_le_div_right; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)))
  -- 3a: the coefficients of `G_{β_i}(b_i)` for `i ∈ S`
  set la := (S ×ˢ Finset.Iic E).toList
  have h3a := hp_keep (hp_parL (f := fun (z : Out2 n d k Kq → ℝ) (ie : Fin n × (Fin (k / 2 + 1) →₀ ℕ)) =>
      coefVal n d k Kq (fun o => z (toOut2 n d k Kq o)) (β ie.1) ie.1 ie.2) la
    (fun ie _ => hp_mapIn (hp_coef n d k Kq (β ie.1) ie.1 ie.2) (toOut2 n d k Kq)))
  -- 3b: the product
  set LL : List (Option (Fin n ⊕ Fin n)) :=
    none :: (S.toList.map (fun i => some (Sum.inl i)) ++ S.toList.map (fun i => some (Sum.inr i)))
  let rmap : Option (Fin n ⊕ Fin n) × (Fin (k / 2 + 1) →₀ ℕ) →
      Out2 n d k Kq ⊕ (Fin n × (Fin (k / 2 + 1) →₀ ℕ))
    | (none, e) => .inl (.inr (.inr e))
    | (some (.inl i), e) => .inl (.inr (.inl (i, e)))
    | (some (.inr i), e) => .inr (i, e)
  have h3b := hp_keep (hp_mapIn (⟨ringProdProg E LL, ringProdProg_clean E LL, fun _ _ => rfl,
      le_rfl⟩ : HasProg (fun v e => (ringProdProg E LL).eval v e) (ringProdProg E LL).cost) rmap)
  -- 3c: the weighted sum
  set lc := (Finset.Iic El).toList
  let rhoA : (Fin (k / 2 + 1) →₀ ℕ) → (Out2 n d k Kq ⊕ (Fin n × (Fin (k / 2 + 1) →₀ ℕ))) ⊕
      (Fin (k / 2 + 1) →₀ ℕ) := fun e =>
    .inl (.inl (toOut2 n d k Kq (rhoI n d k Kq (∑ i, β i + coeffDegree e))))
  have h3c := hp_seq (hp_parL (f := fun w e => w (.inr e) / w (rhoA e)) lc
      (fun e _ => hp_congr (hp_op (ι := (Out2 n d k Kq ⊕ (Fin n × (Fin (k / 2 + 1) →₀ ℕ))) ⊕
        (Fin (k / 2 + 1) →₀ ℕ)) .div (Arg.inp (.inr e)) (Arg.inp (rhoA e)) rfl rfl)
        (fun v u => by simp [Arg.eval, Op.eval]))) (hp_sumL lc)
  have hall := hp_seq h3a (hp_seq h3b h3c)
  refine ⟨_, hp_mono hall ?_, ?_⟩
  · have hla : la.length = S.card * deltaR d k Kq := by
      rw [Finset.length_toList, Finset.card_product, card_box d k Kq]
    have hLL : LL.length = 1 + 2 * S.card := by
      simp [LL]; ring
    have hpc := ringProdProg_cost E LL
    rw [hLL, card_box d k Kq] at hpc
    have hlc : lc.length ≤ deltaR d k Kq := by
      rw [Finset.length_toList, ← card_box d k Kq]
      exact Finset.card_le_card (Finset.Iic_subset_Iic.mpr (subBox_le_upper _ _ _ _))
    rw [hla]
    unfold Qv
    have h1 : S.card * deltaR d k Kq * 2 ≤ k * d * deltaR d k Kq := by
      have : S.card * 2 ≤ k * d := by omega
      nlinarith
    have h2 : 2 * (1 + 2 * S.card) * deltaR d k Kq ^ 2 ≤ 2 * (1 + k * d) * deltaR d k Kq ^ 2 := by
      have : 2 * S.card ≤ k * d := by omega
      apply Nat.mul_le_mul_right; omega
    have h3 : lc.length * 1 + (lc.length - 1) ≤ 2 * deltaR d k Kq := by omega
    omega
  · intro b z hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hS1 : (fun o => z (toOut2 n d k Kq o)) = S1 n (k * d + Kq) Kq b := funext hz1
    -- the product
    let φt : Option (Fin n ⊕ Fin n) → MvPowerSeries (Fin (k / 2 + 1)) ℝ
      | none => ∏ i, gaussianCoordSeries (k / 2) 0 (b i)
      | some (.inl i) => MvPowerSeries.invOfUnit (gaussianCoordSeries (k / 2) 0 (b i)) 1
      | some (.inr i) => gaussianCoordSeries (k / 2) (β i) (b i)
    have hβ' : ∑ j, β j ≤ (k - 2 * x.1.1) * d / 2 := hβ
    have hβle : ∀ i, β i ≤ k * d / 2 := by
      intro i
      have h1 : β i ≤ ∑ j, β j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : (k - 2 * x.1.1) * d / 2 ≤ k * d / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
      omega
    have hprod : (LL.map φt).prod = ∏ i, gaussianCoordSeries (k / 2) (β i) (b i) := by
      simp only [LL, List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_map]
      rw [show (S.toList.map (φt ∘ fun i => some (Sum.inl i))).prod =
          ∏ i ∈ S, MvPowerSeries.invOfUnit (gaussianCoordSeries (k / 2) 0 (b i)) 1 from
          Finset.prod_map_toList _ _,
        show (S.toList.map (φt ∘ fun i => some (Sum.inr i))).prod =
          ∏ i ∈ S, gaussianCoordSeries (k / 2) (β i) (b i) from Finset.prod_map_toList _ _,
        ← Finset.prod_mul_distrib]
      exact gaussian_product_adjustment (k / 2) β b
    have hR : ∀ W : Out2 n d k Kq ⊕ (Fin n × (Fin (k / 2 + 1) →₀ ℕ)) → ℝ,
        (∀ o ∈ LL, EqUpTo E (toSer (fun f => W (rmap (o, f)))) (φt o)) →
        ∀ e ≤ E, (ringProdProg E LL).eval (W ∘ rmap) e =
          MvPowerSeries.coeff e (∏ i, gaussianCoordSeries (k / 2) (β i) (b i)) := by
      intro W hW e he
      rw [← hprod]
      exact (ringProdProg_eval E e he LL (fun o => toSer (fun f => W (rmap (o, f))))).trans
        (EqUpTo.listProd LL _ φt hW e he)
    -- the weighted sum
    simp only [Sum.elim_inr, Sum.elim_inl]
    rw [List.map_congr_left (fun e he => if_pos he), Finset.sum_map_toList]
    unfold ringN
    apply Finset.sum_congr rfl
    intro e he
    have heE : e ≤ E := (Finset.mem_Iic.mp he).trans (subBox_le_upper _ _ _ _)
    simp only [rhoA, Sum.elim_inl]
    congr 1
    · refine hR _ ?_ e heE
      intro o ho f hf
      rcases o with _ | (i | i)
      · exact hz3 f hf
      · exact hz2 i f hf
      · have hi : i ∈ S := by simpa [LL] using ho
        simp only [coeff_toSer, rmap, Sum.elim_inr]
        rw [if_pos (by simp [la, hi, Finset.mem_Iic.mpr hf]), hS1]
        exact coefVal_eq n d k Kq b (β i) (hβle i) i f hf
    rw [hz1]
    have hm : ∑ i, β i + coeffDegree e ≤ k * d + Kq := by
      have he' := Finset.mem_Iic.mp he
      have h0 : e 0 ≤ Kq := by simpa [El, subBox] using he' 0
      have hsucc : ∑ r : Fin (k / 2), e r.succ ≤ x.1.1 * d := by
        calc ∑ r : Fin (k / 2), e r.succ ≤ ∑ r : Fin (k / 2), (if r.val < x.1.1 then d else 0) :=
              Finset.sum_le_sum (fun r _ => by simpa [El, subBox] using he' r.succ)
          _ = (Finset.univ.filter (fun r : Fin (k / 2) => r.val < x.1.1)).card * d := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
          _ ≤ x.1.1 * d := by
              apply Nat.mul_le_mul_right
              calc _ ≤ (Finset.range x.1.1).card :=
                    Finset.card_le_card_of_injOn (fun r => r.val)
                      (fun r hr => by simpa using (Finset.mem_filter.mp hr).2)
                      (fun a _ b _ h => Fin.ext h)
                _ = x.1.1 := Finset.card_range _
      have hdeg : coeffDegree e = e 0 + ∑ r : Fin (k / 2), e r.succ := by
        unfold coeffDegree; rw [Fin.sum_univ_succ]
      have h2l : 2 * x.1.1 ≤ k := by
        have := x.1.2; omega
      have hk1 : (k - 2 * x.1.1) * d / 2 ≤ (k - 2 * x.1.1) * d := Nat.div_le_self _ _
      have hk2 : (k - 2 * x.1.1) * d + x.1.1 * d ≤ k * d := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    simp only [S1, rhoI, Sum.elim_inr, Sum.elim_inl, constN, min_eq_left hm, rhoN, rhoD]
    push_cast
    rfl

end stage3

/-! ## Stage 4: all values, normalized -/

private def x0 (n d k : ℕ) : MomentIndex n d k := ⟨0, default⟩

private lemma stage34 (n d k Kq : ℕ) : ∃ F : (Out2 n d k Kq → ℝ) → MomentIndex n d k → ℝ,
    HasProg F (Vonce n d k * Qv d k Kq + Vonce n d k) ∧ ∀ b z, Good2 n d k Kq b z → ∀ x,
      F z x = ringN (k / 2) x.1.1 d Kq (betaOf n d k x) b /
        ringN (k / 2) 0 d Kq (fun _ => 0) b := by
  classical
  choose F3 hF3 eF3 using fun x : MomentIndex n d k => stage3_val n d k Kq x
  have h1 := hp_par (f := fun z (x : MomentIndex n d k) => F3 x z ()) (c := Qv d k Kq)
    (fun x => hp_congr (hF3 x) (fun z u => rfl))
  have h2 := hp_par (ι := MomentIndex n d k) (f := fun v x => v x / v (x0 n d k)) (c := 1)
    (fun x => hp_congr (hp_op .div (Arg.inp x) (Arg.inp (x0 n d k)) rfl rfl)
      (fun v u => by simp [Arg.eval, Op.eval]))
  refine ⟨_, hp_mono (hp_seq h1 h2) (by rw [MomentIndex_card]; omega), ?_⟩
  intro b z hz x
  simp only
  rw [eF3 x b z hz, eF3 (x0 n d k) b z hz]
  rfl



/-! ## Stage 5: the key weights -/

private lemma w5_cQ_nat (j l : ℕ) (hl : 2 * l ≤ j) :
    cQ j l = ((j.choose (2 * l) * (2 * l - 1).doubleFactorial : ℕ) : ℚ) := by
  have hf : (2 * l).factorial = 2 ^ l * l.factorial * (2 * l - 1).doubleFactorial := by
    by_cases hz : l = 0
    · subst l; simp
    · have he : 2 * l - 1 + 1 = 2 * l := by omega
      have h := Nat.factorial_eq_mul_doubleFactorial (2 * l - 1)
      rw [he, Nat.doubleFactorial_two_mul] at h
      exact h
  have hc := Nat.choose_mul_factorial_mul_factorial hl
  rw [hf] at hc
  unfold cQ
  apply (div_eq_iff (by positivity :
    (l.factorial : ℚ) * 2 ^ l * ((j - 2 * l).factorial : ℚ) ≠ 0)).mpr
  have hq : (j.choose (2 * l) : ℚ) * (2 ^ l * (l.factorial : ℚ) *
      ((2 * l - 1).doubleFactorial : ℚ)) * ((j - 2 * l).factorial : ℚ) = (j.factorial : ℚ) := by
    exact_mod_cast hc
  push_cast
  linear_combination -hq

private lemma w5_cQ_bounds (j l : ℕ) :
    0 ≤ cQ j l ∧ cQ j l ≤ (j.factorial : ℚ) := by
  constructor
  · unfold cQ; positivity
  · unfold cQ
    have hden : (1 : ℚ) ≤ (l.factorial : ℚ) * 2 ^ l * ((j - 2 * l).factorial : ℚ) := by
      have h1 : (1 : ℚ) ≤ (l.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos l
      have h2 : (1 : ℚ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℚ) ≤ ((j - 2 * l).factorial : ℚ) := by
        exact_mod_cast Nat.factorial_pos (j - 2 * l)
      nlinarith [mul_le_mul h1 h2 (by positivity) (by positivity),
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)]
    exact div_le_self (by positivity) hden

private def rhoNat (n m : ℕ) : ℕ := ∏ t ∈ Finset.range m, (n + 2 * t)
private lemma w5_rat_nat_div_den_dvd (a b : ℕ) : ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have h : (a : ℚ) / (b : ℚ) = Rat.divInt (a : ℤ) (b : ℤ) := by
    simp [Rat.divInt_eq_div]
  rw [h]
  exact_mod_cast Rat.den_dvd (a : ℤ) (b : ℤ)

private lemma w5_kapQ_den_dvd (j l : ℕ) (hl : 2 * l ≤ j) :
    (kapQ n d j l).den ∣
      ∏ i ∈ Finset.range l, (Fintype.card (CoefIdxD n d) + 2 * (j - 2 * l) + 2 * i) := by
  rw [kapQ, w5_cQ_nat j l hl]
  have hp : (∏ i ∈ Finset.range l, (BstLean.Part41.DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i)) =
      ((∏ i ∈ Finset.range l,
        (Fintype.card (CoefIdxD n d) + 2 * (j - 2 * l) + 2 * i) : ℕ) : ℚ) := by
    simp [BstLean.Part41.DQ]
  rw [hp]
  exact w5_rat_nat_div_den_dvd _ _

private lemma w5_kapQ_den_le (hn : 1 ≤ n) (j l k : ℕ) (hl : 2 * l ≤ j) (hj : j ≤ k) :
    (kapQ n d j l).den ≤ (Fintype.card (CoefIdxD n d) + 2 * k) ^ l := by
  have hd := w5_kapQ_den_dvd (n := n) (d := d) j l hl
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : 0 < Fintype.card (CoefIdxD n d) := Fintype.card_pos
  have hpos : 0 < ∏ i ∈ Finset.range l,
      (Fintype.card (CoefIdxD n d) + 2 * (j - 2 * l) + 2 * i) :=
    Finset.prod_pos (fun _ _ => by omega)
  calc
    _ ≤ _ := Nat.le_of_dvd hpos hd
    _ ≤ ∏ _i ∈ Finset.range l, (Fintype.card (CoefIdxD n d) + 2 * k) := by
      apply Finset.prod_le_prod
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

private lemma w5_rat_int_div_den_dvd (a : ℤ) (b : ℕ) : ((a : ℚ) / (b : ℚ)).den ∣ b := by
  have h : (a : ℚ) / (b : ℚ) = Rat.divInt a (b : ℤ) := by
    simp [Rat.divInt_eq_div]
  rw [h]
  exact_mod_cast Rat.den_dvd a (b : ℤ)

private lemma w5_muQ_den_dvd (s i : ℕ) (hi : 2 * i ≤ s) :
    (muQ n d s i).den ∣
      ∏ m ∈ Finset.Icc 1 i, (Fintype.card (CoefIdxD n d) + 2 * s - 2 - 2 * m) := by
  rw [muQ, w5_cQ_nat s i hi]
  have hp : (∏ m ∈ Finset.Icc 1 i, (BstLean.Part41.DQ n d + 2 * (s : ℚ) - 2 - 2 * m)) =
      ((∏ m ∈ Finset.Icc 1 i,
        (Fintype.card (CoefIdxD n d) + 2 * s - 2 - 2 * m) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    have hsub : 2 * m ≤ Fintype.card (CoefIdxD n d) + 2 * s - 2 := by omega
    have hsub' : 2 ≤ Fintype.card (CoefIdxD n d) + 2 * s := by omega
    rw [Nat.cast_sub hsub, Nat.cast_sub hsub']
    simp [BstLean.Part41.DQ]
  rw [hp]
  have hnum : (-1 : ℚ) ^ i *
      ((s.choose (2 * i) * (2 * i - 1).doubleFactorial : ℕ) : ℚ) =
      (((-1 : ℤ) ^ i * (s.choose (2 * i) * (2 * i - 1).doubleFactorial : ℕ) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [hnum]
  exact w5_rat_int_div_den_dvd _ _

private lemma w5_muQ_den_le (hn : 1 ≤ n) (s i k : ℕ) (hi : 2 * i ≤ s) (hs : s ≤ k) :
    (muQ n d s i).den ≤ (Fintype.card (CoefIdxD n d) + 2 * k) ^ i := by
  have hd := w5_muQ_den_dvd (n := n) (d := d) s i hi
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : 0 < Fintype.card (CoefIdxD n d) := Fintype.card_pos
  have hpos : 0 < ∏ m ∈ Finset.Icc 1 i,
      (Fintype.card (CoefIdxD n d) + 2 * s - 2 - 2 * m) := by
    apply Finset.prod_pos
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    omega
  calc
    _ ≤ _ := Nat.le_of_dvd hpos hd
    _ ≤ ∏ _m ∈ Finset.Icc 1 i, (Fintype.card (CoefIdxD n d) + 2 * k) := by
      apply Finset.prod_le_prod
      intro m hm
      omega
    _ = _ := by simp

private lemma w5_kapQ_abs_le (hn : 1 ≤ n) (j l : ℕ) :
    |kapQ n d j l| ≤ (j.factorial : ℚ) := by
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : (1 : ℚ) ≤ BstLean.Part41.DQ n d := by
    unfold BstLean.Part41.DQ
    exact_mod_cast Fintype.card_pos (α := CoefIdxD n d)
  have hp : (1 : ℚ) ≤ ∏ i ∈ Finset.range l,
      (BstLean.Part41.DQ n d + 2 * ((j - 2 * l : ℕ) : ℚ) + 2 * i) := by
    apply Finset.one_le_prod₀
    intro i hi
    have h1 : (0 : ℚ) ≤ 2 * ((j - 2 * l : ℕ) : ℚ) := by positivity
    have h2 : (0 : ℚ) ≤ 2 * i := by positivity
    linarith
  unfold kapQ
  rw [abs_of_nonneg (div_nonneg (w5_cQ_bounds j l).1 (by linarith))]
  exact (div_le_self (w5_cQ_bounds j l).1 hp).trans (w5_cQ_bounds j l).2

private lemma w5_muQ_abs_le (hn : 1 ≤ n) (s i : ℕ) (hi : 2 * i ≤ s) :
    |muQ n d s i| ≤ (s.factorial : ℚ) := by
  let a : Fin n := ⟨0, by omega⟩
  let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
  have hc : (1 : ℚ) ≤ BstLean.Part41.DQ n d := by
    unfold BstLean.Part41.DQ
    exact_mod_cast Fintype.card_pos (α := CoefIdxD n d)
  have hp : (1 : ℚ) ≤ ∏ m ∈ Finset.Icc 1 i, (BstLean.Part41.DQ n d + 2 * (s : ℚ) - 2 - 2 * m) := by
    apply Finset.one_le_prod₀
    intro m hm
    obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
    have hsm : 2 + 2 * m ≤ 2 * s := by omega
    have hh : (2 : ℚ) + 2 * m ≤ 2 * s := by exact_mod_cast hsm
    linarith
  unfold muQ
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (w5_cQ_bounds s i).1, abs_of_nonneg (by linarith : (0 : ℚ) ≤ _)]
  exact (div_le_self (w5_cQ_bounds s i).1 hp).trans (w5_cQ_bounds s i).2

private lemma w5_orbSize_le (q : Multiset (Mono n d)) : orbSize q ≤ q.card.factorial := by
  classical
  unfold orbSize
  exact Nat.div_le_self _ _

private lemma w5_mul_den_le (a b : ℚ) : (a * b).den ≤ a.den * b.den :=
  Nat.le_of_dvd (by positivity) (Rat.mul_den_dvd a b)

private lemma w5_rat_num_le (q : ℚ) (A B : ℕ) (hden : q.den ≤ A) (hval : |q| ≤ (B : ℚ)) :
    q.num.natAbs ≤ A * B := by
  have he : (q.num.natAbs : ℚ) = |q| * (q.den : ℚ) := by
    have hq := q.num_div_den
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have hh := congrArg abs hq
    rw [abs_div, abs_of_pos hd, ← Int.cast_abs, ← Nat.cast_natAbs] at hh
    exact (div_eq_iff hd.ne').mp hh
  have hd' : (q.den : ℚ) ≤ A := by exact_mod_cast hden
  have h : (q.num.natAbs : ℚ) ≤ (A * B : ℕ) := by
    rw [he, Nat.cast_mul, mul_comm (A : ℚ)]
    exact mul_le_mul hval hd' (by positivity) (by positivity)
  exact_mod_cast h

private lemma w5_heights_of_le (k : ℕ) (q : ℚ) (hnum : q.num.natAbs ≤ BstLean.Part41.Hgt n d k)
    (hden : q.den ≤ BstLean.Part41.Hgt n d k) :
    q.num.natAbs < 2 ^ bQ n d k ∧ q.den < 2 ^ bQ n d k := by
  have h : BstLean.Part41.Hgt n d k < 2 ^ bQ n d k := Nat.lt_pow_succ_log_self (by decide) _
  exact ⟨hnum.trans_lt h, hden.trans_lt h⟩



private lemma w5_mset_wordOf {α : Type} [Inhabited α] (a : ℕ) (q : Multiset α)
    (hq : q.card = a) : mset (wordOf a q) = q := by
  subst a
  unfold mset wordOf
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun t : Fin q.card => q.toList.getD t.val default) = q.toList := by
    have hh : q.toList.length = q.card := Multiset.length_toList q
    rw [← hh]
    simpa only [List.getD_eq_get, Fin.eta] using List.ofFn_get q.toList
  rw [he, Multiset.coe_toList]

private lemma w5_mset_glue_le {α : Type} (j i : ℕ) (hi : 2 * i ≤ j)
    (c : Fin i → α) (w : Fin (j - 2 * i) → α) : mset w ≤ mset (BstLean.Part41.glue j i c w) := by
  classical
  let e : Fin (j - 2 * i) ↪ Fin j :=
    ⟨fun t => ⟨2 * i + t.val, by omega⟩,
      fun t u h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
  have he : ∀ t, BstLean.Part41.glue j i c w (e t) = w t := by
    intro t
    change (if h : 2 * i + t.val < 2 * i then _ else _) = _
    rw [dite_eq_right (by omega)]
    congr 1
    apply Fin.ext
    change 2 * i + t.val - 2 * i = t.val
    omega
  have hm : (Finset.univ.map e).val.map (BstLean.Part41.glue j i c w) = mset w := by
    simp only [Finset.map_val, Multiset.map_map, Function.comp_def, he, mset]
  rw [← hm]
  exact Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ _))

private def w5_wco (o : Multiset (Mono n d)) (i : Fin n) : ℕ := (o.map (fun p => p.2.1.count i)).sum

private lemma w5_wc_eq {s : ℕ} (w : Fin s → Mono n d) (i : Fin n) : wc w i = w5_wco (mset w) i := by
  simp [wc, w5_wco, mset, Multiset.map_map, Function.comp_def, Finset.sum_eq_multiset_sum]

private noncomputable def w5_g {k : ℕ} (κ : KeyF n d k) (c : Fin κ.2.2.1.1 → Mono n d) :
    Multiset (Mono n d) :=
  mset (BstLean.Part41.glue (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 c (wordOf _ κ.2.2.2.2.1))

private noncomputable def w5_cnt {k : ℕ} (κ : KeyF n d k) (o : Multiset (Mono n d)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c => w5_g κ c = o)).card

private noncomputable def w5_P {k : ℕ} (K : ℕ → ℕ → Finset (Multiset (Mono n d))) (κ : KeyF n d k) :
    Finset (Multiset (Mono n d)) := by
  classical
  exact if 2 * κ.2.1.1 = κ.1.1 then {0}
    else (K κ.1.1 κ.2.1.1).filter (fun o => κ.2.2.2.2.1 ≤ o ∧ ∀ i, Even (w5_wco o i))

private noncomputable def w5_c {k : ℕ} (κ : KeyF n d k) (o : Multiset (Mono n d)) : ℚ :=
  if 2 * κ.2.1.1 = κ.1.1 then kapQ n d κ.1.1 κ.2.1.1
  else kapQ n d κ.1.1 κ.2.1.1 * muQ n d (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 *
    (orbSize κ.2.2.2.2.1 : ℚ) * (w5_cnt κ o : ℚ)

private def w5_lF {k : ℕ} (κ : KeyF n d k) : Fin (k / 2 + 1) := ⟨min κ.2.1.1 (k / 2), by omega⟩

private noncomputable def w5_idx {k : ℕ} (κ : KeyF n d k) (o : Multiset (Mono n d)) :
    MomentIndex n d k := ⟨w5_lF κ, mkMono (fun i => w5_wco o i / 2)⟩

private lemma w5_key {k : ℕ} {K : ℕ → ℕ → Finset (Multiset (Mono n d))} {κ : KeyF n d k}
    (h : κ ∈ keys43 k K) :
    κ.1.1 ≤ k ∧ 2 * κ.2.1.1 ≤ κ.1.1 ∧ 2 * κ.2.2.1.1 ≤ κ.1.1 - 2 * κ.2.1.1 ∧
      Multiset.card κ.2.2.2.2.1 = κ.1.1 - 2 * κ.2.1.1 - 2 * κ.2.2.1.1 ∧
      (2 * κ.2.1.1 = κ.1.1 → κ.2.2.1.1 = 0 ∧ κ.2.2.2.1.1 = 0 ∧ 1 ≤ κ.1.1) ∧
      (2 * κ.2.1.1 ≠ κ.1.1 → (κ.1.1, κ.2.1.1) ∈ levels k) := by
  classical
  have hk : IsKey k K κ := by
    unfold keys43 at h
    exact (Finset.mem_filter.mp (by convert h)).2
  have hj := κ.1.2
  have hc : Multiset.card κ.2.2.2.2.1 = κ.2.2.2.1.1 := κ.2.2.2.2.2
  rcases hk with ⟨⟨r, hr⟩, h1, h2, h3, h4⟩ | ⟨h1, h2, h3, -⟩
  · refine ⟨by omega, by omega, by omega, by omega, fun _ => ⟨h3, h4, h1⟩, fun h => by omega⟩
  · have hl := Finset.mem_filter.mp h1
    refine ⟨by omega, by omega, h2, by omega, fun h => by omega, fun _ => h1⟩


private lemma w5_c_heights (hn : 1 ≤ n) {k : ℕ} {K : ℕ → ℕ → Finset (Multiset (Mono n d))}
    {κ : KeyF n d k} (h : κ ∈ keys43 k K) (o : Multiset (Mono n d)) :
    (w5_c κ o).num.natAbs < 2 ^ bQ n d k ∧ (w5_c κ o).den < 2 ^ bQ n d k := by
  classical
  obtain ⟨hj, hl, hi, hcard, -, -⟩ := w5_key h
  set j := κ.1.1
  set l := κ.2.1.1
  set i := κ.2.2.1.1
  set s := j - 2 * l
  let A := Fintype.card (CoefIdxD n d) + 2 * k
  let N := Fintype.card (Mono n d)
  have hc : 1 ≤ Fintype.card (CoefIdxD n d) := by
    let a : Fin n := ⟨0, by omega⟩
    let : Nonempty (CoefIdxD n d) := ⟨⟨0, (Sym.nil, a)⟩⟩
    exact Fintype.card_pos
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hN : 1 ≤ N := Fintype.card_pos
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hfk : (1 : ℚ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hjf : (j.factorial : ℚ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
  have hsf : (s.factorial : ℚ) ≤ k.factorial := by
    exact_mod_cast Nat.factorial_le (show s ≤ k by omega)
  have hqf : (orbSize κ.2.2.2.2.1 : ℚ) ≤ k.factorial := by
    exact_mod_cast (w5_orbSize_le κ.2.2.2.2.1).trans
      (Nat.factorial_le (by rw [hcard]; omega))
  have hkap : (kapQ n d j l).den ≤ A ^ l := w5_kapQ_den_le hn j l k hl hj
  have habs : |kapQ n d j l| ≤ k.factorial := (w5_kapQ_abs_le hn j l).trans hjf
  have hmu : (muQ n d s i).den ≤ A ^ i := w5_muQ_den_le hn s i k hi (by omega)
  have hmuabs : |muQ n d s i| ≤ k.factorial := (w5_muQ_abs_le hn s i hi).trans hsf
  have hcnt : (w5_cnt κ o : ℚ) ≤ (N : ℚ) ^ k := by
    have h1 : w5_cnt κ o ≤ N ^ i := by
      unfold w5_cnt
      calc _ ≤ (Finset.univ : Finset (Fin i → Mono n d)).card := Finset.card_filter_le _ _
        _ = N ^ i := by simp [N]
    have h2 : N ^ i ≤ N ^ k := Nat.pow_le_pow_right hN (by omega)
    exact_mod_cast h1.trans h2
  -- bounds: den ≤ A^(2k), |c| ≤ k!^3 N^k
  have hden : (w5_c κ o).den ≤ A ^ (2 * k) := by
    unfold w5_c
    split_ifs
    · exact hkap.trans (Nat.pow_le_pow_right hA (by omega))
    · have e1 := w5_mul_den_le (kapQ n d j l * muQ n d s i * (orbSize κ.2.2.2.2.1 : ℚ))
        ((w5_cnt κ o : ℕ) : ℚ)
      have e2 := w5_mul_den_le (kapQ n d j l * muQ n d s i) ((orbSize κ.2.2.2.2.1 : ℕ) : ℚ)
      have e3 := w5_mul_den_le (kapQ n d j l) (muQ n d s i)
      simp only [Rat.den_natCast, mul_one] at e1 e2
      calc _ ≤ A ^ l * A ^ i := (e1.trans (e2.trans e3)).trans (Nat.mul_le_mul hkap hmu)
        _ ≤ A ^ (2 * k) := by rw [← pow_add]; exact Nat.pow_le_pow_right hA (by omega)
  have hval : |w5_c κ o| ≤ ((k.factorial ^ 3 * N ^ k : ℕ) : ℚ) := by
    unfold w5_c
    split_ifs
    · calc _ ≤ (k.factorial : ℚ) := habs
        _ ≤ _ := by
          push_cast
          have : (1 : ℚ) ≤ (N : ℚ) ^ k := one_le_pow₀ hNq
          have h3 : (k.factorial : ℚ) ≤ (k.factorial : ℚ) ^ 3 := by
            nlinarith [sq_nonneg ((k.factorial : ℚ) - 1)]
          nlinarith
    · simp only [abs_mul, abs_of_nonneg (show (0 : ℚ) ≤ (orbSize κ.2.2.2.2.1 : ℚ) by positivity),
        abs_of_nonneg (show (0 : ℚ) ≤ (w5_cnt κ o : ℚ) by positivity)]
      push_cast
      calc _ ≤ ((k.factorial : ℚ) * k.factorial * k.factorial) * (N : ℚ) ^ k := by
            apply mul_le_mul _ hcnt (by positivity) (by positivity)
            exact mul_le_mul (mul_le_mul habs hmuabs (abs_nonneg _) (by positivity)) hqf
              (by positivity) (by positivity)
        _ = _ := by ring
  have hnum : (w5_c κ o).num.natAbs ≤ A ^ (2 * k) * (k.factorial ^ 3 * N ^ k) :=
    w5_rat_num_le _ _ _ hden hval
  have hgt : BstLean.Part41.Hgt n d k = (∏ t ∈ Finset.range (k * d), (n + 2 * t)) *
      (A ^ (2 * k) * (k.factorial ^ 3 * N ^ k)) * (d + 1) ^ k := by
    simp only [BstLean.Part41.Hgt, A, N]; ring
  have hP : 1 ≤ ∏ t ∈ Finset.range (k * d), (n + 2 * t) :=
    Finset.one_le_prod' (fun t _ => by omega)
  have hle : A ^ (2 * k) * (k.factorial ^ 3 * N ^ k) ≤ BstLean.Part41.Hgt n d k := by
    rw [hgt]
    calc _ = 1 * (A ^ (2 * k) * (k.factorial ^ 3 * N ^ k)) * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hP) (Nat.one_le_pow _ _ (by omega))
  have hB : 1 ≤ k.factorial ^ 3 * N ^ k := Nat.mul_le_mul (Nat.one_le_pow _ _ (Nat.factorial_pos k))
    (Nat.one_le_pow _ _ hN)
  apply w5_heights_of_le k
  · exact hnum.trans hle
  · exact hden.trans ((Nat.le_mul_of_pos_right _ hB).trans hle)


private lemma w5_keyF_ext {k : ℕ} {κ κ' : KeyF n d k} (h1 : κ.1.1 = κ'.1.1) (h2 : κ.2.1.1 = κ'.2.1.1)
    (h3 : κ.2.2.1.1 = κ'.2.2.1.1) (h4 : κ.2.2.2.2.1 = κ'.2.2.2.2.1) : κ = κ' := by
  obtain ⟨j, l, i, a, q⟩ := κ
  obtain ⟨j', l', i', a', q'⟩ := κ'
  simp only at h1 h2 h3 h4
  have ha : a = a' := Fin.ext (by rw [← q.2, ← q'.2, h4])
  subst ha
  have hq : q = q' := Subtype.ext h4
  subst hq
  rw [Fin.ext h1, Fin.ext h2, Fin.ext h3]

private lemma w5_card (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    ((keys43 k K).sigma (w5_P K)).card ≤
      ∑ jl ∈ levels k, 2 ^ (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card + k := by
  classical
  rw [Finset.card_sigma, ← Finset.sum_filter_add_sum_filter_not (keys43 k K)
    (fun κ => 2 * κ.2.1.1 = κ.1.1)]
  rw [add_comm]
  apply Nat.add_le_add
  · -- non-scalar keys
    set ns := (keys43 k K).filter (fun κ => ¬ 2 * κ.2.1.1 = κ.1.1)
    rw [← Finset.card_sigma]
    let T := (levels k).sigma (fun jl => (K jl.1 jl.2).sigma (fun o => o.powerset.toFinset))
    have hT : T.card ≤ ∑ jl ∈ levels k, 2 ^ (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card := by
      rw [Finset.card_sigma]
      apply Finset.sum_le_sum
      intro jl hjl
      rw [Finset.card_sigma]
      calc _ ≤ ∑ _o ∈ K jl.1 jl.2, 2 ^ (jl.1 - 2 * jl.2) := by
            apply Finset.sum_le_sum
            intro o ho
            calc _ ≤ Multiset.card o.powerset := Multiset.toFinset_card_le _
              _ = _ := by rw [Multiset.card_powerset, hK jl hjl o ho]
        _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    refine le_trans ?_ hT
    apply Finset.card_le_card_of_injOn
      (fun x => (⟨(x.1.1.1, x.1.2.1.1), ⟨x.2, x.1.2.2.2.2.1⟩⟩ :
        Σ _ : ℕ × ℕ, Σ _ : Multiset (Mono n d), Multiset (Mono n d)))
    · intro x hx
      obtain ⟨hκ, ho⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hκ, hns⟩ := Finset.mem_filter.mp hκ
      have hlev := (w5_key hκ).2.2.2.2.2 hns
      unfold w5_P at ho
      rw [if_neg hns] at ho
      obtain ⟨hoK, hqo, -⟩ := Finset.mem_filter.mp ho
      simp only [T, Finset.mem_coe, Finset.mem_sigma, Multiset.mem_toFinset, Multiset.mem_powerset]
      exact ⟨hlev, hoK, hqo⟩
    · intro x hx y hy hxy
      obtain ⟨hκx, -⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hκy, -⟩ := Finset.mem_sigma.mp hy
      have kx := w5_key (Finset.mem_filter.mp hκx).1
      have ky := w5_key (Finset.mem_filter.mp hκy).1
      simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at hxy
      obtain ⟨⟨hj, hl⟩, ho, hq⟩ := hxy
      have hi : x.1.2.2.1.1 = y.1.2.2.1.1 := by
        have h1 := kx.2.2.2.1
        have h2 := ky.2.2.2.1
        rw [hq] at h1
        omega
      have hκ := w5_keyF_ext hj hl hi hq
      exact Sigma.ext hκ (heq_of_eq ho)
  · -- scalar keys
    have hP : ∀ κ ∈ (keys43 k K).filter (fun κ => 2 * κ.2.1.1 = κ.1.1), (w5_P K κ).card = 1 := by
      intro κ hκ
      unfold w5_P
      rw [if_pos (Finset.mem_filter.mp hκ).2]
      rfl
    rw [Finset.sum_congr rfl hP, Finset.sum_const, smul_eq_mul, mul_one]
    calc _ ≤ (Finset.Icc 1 k).card := by
          apply Finset.card_le_card_of_injOn (fun κ => κ.1.1)
          · intro κ hκ
            obtain ⟨hκ, hs⟩ := Finset.mem_filter.mp hκ
            have kk := w5_key hκ
            simp only [Finset.mem_coe, Finset.mem_Icc]
            exact ⟨(kk.2.2.2.2.1 hs).2.2, kk.1⟩
          · intro x hx y hy hxy
            obtain ⟨hx, hsx⟩ := Finset.mem_filter.mp hx
            obtain ⟨hy, hsy⟩ := Finset.mem_filter.mp hy
            have kx := (w5_key hx).2.2.2.2.1 hsx
            have ky := (w5_key hy).2.2.2.2.1 hsy
            simp only at hxy
            have hq : x.2.2.2.2.1 = y.2.2.2.2.1 := by
              have cx : Multiset.card x.2.2.2.2.1 = 0 := by
                have := x.2.2.2.2.2; have := kx.2.1; omega
              have cy : Multiset.card y.2.2.2.2.1 = 0 := by
                have := y.2.2.2.2.2; have := ky.2.1; omega
              rw [Multiset.card_eq_zero.mp cx, Multiset.card_eq_zero.mp cy]
            exact w5_keyF_ext hxy (by omega) (by omega) hq
      _ = k := by simp


private lemma w5_fiber {α β : Type} [Fintype α] [DecidableEq β] (g : α → β) (K : Finset β)
    (H : β → ℝ) :
    ∑ c, (if g c ∈ K then H (g c) else 0) =
      ∑ o ∈ K, ((Finset.univ.filter (fun c => g c = o)).card : ℝ) * H o := by
  have h1 : ∀ c, (if g c ∈ K then H (g c) else 0) = ∑ o ∈ K, if g c = o then H o else 0 := by
    intro c; rw [Finset.sum_ite_eq]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

private lemma w5_correct (hn : 1 ≤ n) {k : ℕ} {K : ℕ → ℕ → Finset (Multiset (Mono n d))}
    (μ : Measure (Fin n → ℝ)) (v : MomentIndex n d k → ℝ)
    (hv : ∀ (l : Fin (k / 2 + 1)) (s : ℕ), s ≤ k - 2 * l.1 → ∀ w : Fin s → Mono n d,
      HR μ l.1 w = if ∀ i, Even (wc w i) then v ⟨l, mkMono (fun i => wc w i / 2)⟩ else 0)
    {κ : KeyF n d k} (hκ : κ ∈ keys43 k K) :
    ∑ o ∈ w5_P K κ, (w5_c κ o : ℝ) * v (w5_idx κ o) = wKeyR μ K κ := by
  classical
  obtain ⟨hj, hl, hi, hcard, hsc, hns⟩ := w5_key hκ
  have hlF : (w5_lF κ).1 = κ.2.1.1 := min_eq_left (by omega)
  let Hm : Multiset (Mono n d) → ℝ := fun o =>
    if ∀ i, Even (w5_wco o i) then v (w5_idx κ o) else 0
  have hHR : ∀ w : Fin (κ.1.1 - 2 * κ.2.1.1) → Mono n d, HR μ κ.2.1.1 w = Hm (mset w) := by
    intro w
    calc HR μ κ.2.1.1 w = HR μ (w5_lF κ).1 w := by rw [hlF]
      _ = _ := hv (w5_lF κ) _ (by rw [hlF]; omega) w
      _ = Hm (mset w) := by simp only [w5_wc_eq]; rfl
  by_cases hs : 2 * κ.2.1.1 = κ.1.1
  · have hP : w5_P K κ = {0} := by unfold w5_P; rw [if_pos hs]
    rw [hP, Finset.sum_singleton]
    unfold wKeyR
    rw [if_pos hs, hHR]
    have h0 : mset (fun _ : Fin (κ.1.1 - 2 * κ.2.1.1) => (default : Mono n d)) = 0 := by
      apply Multiset.card_eq_zero.mp
      simp [mset]; omega
    rw [h0]
    have hw0 : ∀ i, w5_wco (0 : Multiset (Mono n d)) i = 0 := fun i => by simp [w5_wco]
    simp only [Hm, hw0]
    rw [if_pos (fun _ => ⟨0, rfl⟩)]
    unfold w5_c; rw [if_pos hs]
  · have hP : w5_P K κ = (K κ.1.1 κ.2.1.1).filter
        (fun o => κ.2.2.2.2.1 ≤ o ∧ ∀ i, Even (w5_wco o i)) := by
      unfold w5_P; rw [if_neg hs]
    unfold wKeyR
    rw [if_neg hs]
    unfold trL
    have hsum : ∑ c : Fin κ.2.2.1.1 → Mono n d,
        HKR μ (K κ.1.1 κ.2.1.1) κ.2.1.1 (BstLean.Part41.glue (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 c
          (wordOf _ κ.2.2.2.2.1)) =
        ∑ c, (if w5_g κ c ∈ K κ.1.1 κ.2.1.1 then Hm (w5_g κ c) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      unfold HKR
      split_ifs with h1 h2 h2
      · exact hHR _
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rfl
    rw [hsum, w5_fiber]
    have hq : ∀ c, κ.2.2.2.2.1 ≤ w5_g κ c := by
      intro c
      unfold w5_g
      have := w5_mset_glue_le (κ.1.1 - 2 * κ.2.1.1) κ.2.2.1.1 hi c (wordOf _ κ.2.2.2.2.1)
      rwa [w5_mset_wordOf _ _ hcard] at this
    rw [Finset.mul_sum, ← Finset.sum_filter_of_ne (s := K κ.1.1 κ.2.1.1)
      (p := fun o => κ.2.2.2.2.1 ≤ o ∧ ∀ i, Even (w5_wco o i)), hP]
    · apply Finset.sum_congr rfl
      intro o ho
      have hev := ((Finset.mem_filter.mp ho).2).2
      simp only [Hm, if_pos hev]
      unfold w5_c w5_cnt
      rw [if_neg hs]
      push_cast
      ring
    · intro o _ hne
      have hne' := (mul_ne_zero_iff.mp hne).2
      obtain ⟨hc, hH⟩ := mul_ne_zero_iff.mp hne'
      have hc' : (Finset.univ.filter (fun c => w5_g κ c = o)).card ≠ 0 := by
        intro h0; apply hc; simp [h0]
      obtain ⟨c, hc⟩ := Finset.card_ne_zero.mp hc'
      have hco := (Finset.mem_filter.mp hc).2
      refine ⟨hco ▸ hq c, ?_⟩
      by_contra hodd
      exact hH (by simp only [Hm, if_neg hodd])

private theorem stage5 (hn : 1 ≤ n) (k : ℕ) (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    ∃ F : (MomentIndex n d k → ℝ) → KeyF n d k → ℝ,
      HasProg F ((2 * ∑ jl ∈ levels k, 2 ^ (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card + k + 1) *
        (4 * bQ n d k + 2)) ∧
      ∀ (μ : Measure (Fin n → ℝ)) (v : MomentIndex n d k → ℝ),
        (∀ (l : Fin (k / 2 + 1)) (s : ℕ), s ≤ k - 2 * l.1 → ∀ w : Fin s → Mono n d,
          HR μ l.1 w = if ∀ i, Even (wc w i) then v ⟨l, mkMono (fun i => wc w i / 2)⟩ else 0) →
        ∀ κ ∈ keys43 k K, F v κ = wKeyR μ K κ := by
  classical
  set S := (keys43 k K).sigma (w5_P K)
  let cst : {x // x ∈ S} → ℚ := fun x => w5_c x.1.1 x.1.2
  have hc := hp_keep (hp_consts (ι := MomentIndex n d k) cst (bQ n d k)
    (fun x => w5_c_heights hn (Finset.mem_sigma.mp x.2).1 _))
  let Wf : (MomentIndex n d k ⊕ {x // x ∈ S} → ℝ) → KeyF n d k → ℝ := fun u κ =>
    if h : κ ∈ keys43 k K then
      ∑ o : {o // o ∈ w5_P K κ}, u (Sum.inr ⟨⟨κ, o.1⟩, Finset.mem_sigma.mpr ⟨h, o.2⟩⟩) *
        u (Sum.inl (w5_idx κ o.1))
    else 0
  have hW : HasProg Wf (∑ κ, if κ ∈ keys43 k K then 2 * (w5_P K κ).card else 0) := by
    apply hp_parS
    intro κ
    by_cases h : κ ∈ keys43 k K
    · have := hp_dot (ι := MomentIndex n d k ⊕ {x // x ∈ S}) (κ := {o // o ∈ w5_P K κ})
        (fun o => Arg.inp (Sum.inr ⟨⟨κ, o.1⟩, Finset.mem_sigma.mpr ⟨h, o.2⟩⟩))
        (fun o => Arg.inp (Sum.inl (w5_idx κ o.1))) (fun _ => rfl) (fun _ => rfl)
      refine hp_mono (hp_congr this ?_) ?_
      · intro u _; simp [Wf, h, Arg.eval]
      · simp only [h, ite_true, Fintype.card_coe]; omega
    · refine hp_mono (hp_congr (hp_args (ι := MomentIndex n d k ⊕ {x // x ∈ S}) (κ := Unit)
        (fun _ => Arg.cst 0) (fun _ => rfl)) (fun u _ => by simp [Wf, h, Arg.eval])) (Nat.zero_le _)
  have hall := hp_seq hc hW
  refine ⟨_, hp_mono hall ?_, ?_⟩
  · have hsum : (∑ κ, if κ ∈ keys43 k K then 2 * (w5_P K κ).card else 0) = 2 * S.card := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sigma,
        Finset.mul_sum]
    rw [hsum, Fintype.card_coe]
    have hS : S.card ≤ _ := w5_card k K hK
    set T := ∑ jl ∈ levels k, 2 ^ (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card
    calc 4 * bQ n d k * S.card + 2 * S.card = S.card * (4 * bQ n d k + 2) := by ring
      _ ≤ (2 * T + k + 1) * (4 * bQ n d k + 2) := Nat.mul_le_mul_right _ (by omega)
  · intro μ v hv κ hκ
    simp only [Wf, dif_pos hκ, Sum.elim_inl, Sum.elim_inr]
    rw [← w5_correct hn μ v hv hκ, ← Finset.sum_coe_sort (w5_P K κ)]



/-! ## Assembly -/

private lemma sum_half_le (s : Finset (Fin n)) (a : Fin n → ℕ) :
    ∑ i ∈ s, a i / 2 ≤ (∑ i ∈ s, a i) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num), Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.div_mul_le_self _ _)

private lemma wc_sum_le {s : ℕ} (w : Fin s → Mono n d) : ∑ i, wc w i ≤ s * d := by
  unfold wc
  rw [Finset.sum_comm]
  calc ∑ t, ∑ i, (w t).2.1.count i = ∑ t, ((w t).1 : ℕ) := by
        apply Finset.sum_congr rfl; intro t _; rw [sum_count_univ, (w t).2.2]
    _ ≤ ∑ _t : Fin s, d := Finset.sum_le_sum (fun t _ => Nat.lt_succ_iff.mp (w t).1.2)
    _ = s * d := by simp

private lemma HR_ring (hn : 1 ≤ n) (b : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i) (Kq : ℕ) (L l : ℕ)
    (hl : l ≤ L) {s : ℕ} (w : Fin s → Mono n d) :
    HR (BstLean.Part37.binghamK n Kq b) l w =
      (if ∀ i, Even (wc w i) then ringN L l d Kq (fun i => wc w i / 2) b else 0) /
        ringN L 0 d Kq (fun _ => 0) b := by
  unfold HR
  rw [integral_binghamK_nonneg hn b hb Kq, ring_numerator hn L l Kq hl w b]
  congr 1
  have h0 := ring_numerator (d := d) hn L 0 Kq (Nat.zero_le _) (Fin.elim0 : Fin 0 → Mono n d) b
  simp only [pow_zero, Finset.univ_eq_empty, Finset.prod_empty, mul_one, one_mul] at h0
  rw [BstLean.Part37.ZK, h0]
  have hw : ∀ i, wc (Fin.elim0 : Fin 0 → Mono n d) i = 0 := fun i => by simp [wc]
  simp [hw]

/-- **The one-time program**: from `θ'` it returns the key weights of the surrogate, for every `θ'`
with its minimum at `i0`, with only the constants `0` and `1`, at cost `≤ onceCost`. -/
theorem momProg43_exists (hn : 1 ≤ n) (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (i0 : Fin n) (Kq : ℕ)
    (K : ℕ → ℕ → Finset (Multiset (Mono n d)))
    (hK : ∀ jl ∈ levels k, ∀ o ∈ K jl.1 jl.2, Multiset.card o = jl.1 - 2 * jl.2) :
    ∃ pm : Prog (Fin n) (KeyF n d k), heavyCount pm = 0 ∧
      (∀ θ' : Fin n → ℝ, (∀ j, θ' i0 ≤ θ' j) → MomSpec43 pm K i0 Kq θ') ∧
      (pm.cost : ℝ) ≤ onceCost n d k Kq K := by
  classical
  have hshift : HasProg (fun θ i => BstLean.Part42.bsh θ i0 i) n :=
    ⟨shiftProg i0, shiftProg_clean i0, fun θ i => shiftProg_eval i0 θ i, (shiftProg_cost i0).le⟩
  obtain ⟨F2, hF2, eF2⟩ := stage2 n d k Kq
  obtain ⟨F4, hF4, eF4⟩ := stage34 n d k Kq
  obtain ⟨F5, hF5, eF5⟩ := stage5 (d := d) hn k K hK
  have hall := hp_seq hshift (hp_seq (stage1 n d k Kq) (hp_seq hF2 (hp_seq hF4 hF5)))
  obtain ⟨pm, hpm, epm, cpm⟩ := hall
  refine ⟨pm, clean_heavyCount hpm, ?_, ?_⟩
  · intro θ hmin κ hκ
    rw [epm]
    set b := BstLean.Part42.bsh θ i0
    have hb : ∀ i, 0 ≤ b i := bsh_nonneg θ i0 hmin
    have hG : Good2 n d k Kq b (F2 (S1 n (k * d + Kq) Kq b)) := eF2 b
    apply eF5 (BstLean.Part37.binghamK n Kq b) _ _ κ hκ
    intro l s hs w
    rw [eF4 b _ hG, HR_ring hn b hb Kq (k / 2) l.1 (Nat.lt_succ_iff.mp l.2) w]
    split_ifs with he
    · congr 2
      funext i
      unfold betaOf
      dsimp only
      refine (mkMono_count (d := (k - 2 * l.1) * d / 2) (fun i => wc w i / 2) ?_ i).symm
      calc ∑ i, wc w i / 2 ≤ (∑ i, wc w i) / 2 := sum_half_le _ _
        _ ≤ (k - 2 * l.1) * d / 2 :=
          Nat.div_le_div_right ((wc_sum_le w).trans (Nat.mul_le_mul_right _ hs))
    · simp
  · have hδ : Kq + 1 ≤ deltaR d k Kq := by
      unfold deltaR; exact Nat.le_mul_of_pos_right _ (by positivity)
    set δ := deltaR d k Kq with hδdef
    set V := Vonce n d k
    set B := bR n d k Kq
    set P := k * d + 2
    have hP : 2 ≤ P := by omega
    have hδ1 : 1 ≤ δ := by omega
    have hn' : 1 ≤ n := hn
    have hKK : (Kq + 1) * Kq ≤ δ ^ 2 := by nlinarith
    have hδδ : δ ≤ δ ^ 2 := by nlinarith
    have ha : n + n * ((Kq + 1) * Kq) + n * δ * 2 + n * (3 * δ ^ 2) + 2 * n * δ ^ 2 ≤
        16 * n * P * δ ^ 2 := by
      have h1 : n ≤ n * δ ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
      have h2 : n * ((Kq + 1) * Kq) ≤ n * δ ^ 2 := Nat.mul_le_mul_left _ hKK
      have h3 : n * δ * 2 ≤ 2 * (n * δ ^ 2) := by nlinarith
      have h4 : 9 * (n * δ ^ 2) ≤ 16 * n * P * δ ^ 2 := by
        have : n * δ ^ 2 * 9 ≤ n * δ ^ 2 * (16 * P) := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      nlinarith
    have hb : 4 * B * (2 * (k * d + Kq + 1) + (Kq + 1)) ≤ 16 * n * P * δ * (4 * B) := by
      have h1 : 2 * (k * d + Kq + 1) + (Kq + 1) ≤ 16 * n * P * δ := by
        have h2 : P * (Kq + 1) ≤ n * P * δ := by
          calc P * (Kq + 1) ≤ P * δ := Nat.mul_le_mul_left _ hδ
            _ ≤ n * (P * δ) := Nat.le_mul_of_pos_left _ (by omega)
            _ = n * P * δ := by ring
        have h3 : k * d + 2 * Kq + 2 ≤ P * (Kq + 1) := by
          show k * d + 2 * Kq + 2 ≤ (k * d + 2) * (Kq + 1)
          have : (k * d + 2) * (Kq + 1) = k * d * Kq + k * d + 2 * Kq + 2 := by ring
          omega
        have h4 : 16 * n * P * δ = 16 * (n * P * δ) := by ring
        omega
      calc 4 * B * (2 * (k * d + Kq + 1) + (Kq + 1)) ≤ 4 * B * (16 * n * P * δ) :=
            Nat.mul_le_mul_left _ h1
        _ = _ := by ring
    have hc : V * Qv d k Kq + V ≤ 16 * V * P * (δ ^ 2 + δ * (4 * B + 4)) := by
      have h1 : Qv d k Kq + 1 ≤ 16 * P * (δ ^ 2 + δ * (4 * B + 4)) := by
        unfold Qv
        rw [← hδdef]
        have e1 : k * d * δ ≤ P * δ := Nat.mul_le_mul_right _ (by omega)
        have e2 : 2 * (1 + k * d) * δ ^ 2 ≤ 2 * P * δ ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
        have e3 : P * δ ≤ P * (δ * (4 * B + 4)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
        have e4 : 2 * δ + 1 ≤ 3 * (P * δ) := by nlinarith
        nlinarith
      calc V * Qv d k Kq + V = V * (Qv d k Kq + 1) := by ring
        _ ≤ V * (16 * P * (δ ^ 2 + δ * (4 * B + 4))) := Nat.mul_le_mul_left _ h1
        _ = _ := by ring
    have hnat : pm.cost ≤ 16 * (n + V) * P * (δ ^ 2 + δ * (4 * B + 4)) + 16 * Kq ^ 2 + 64 +
        (2 * ∑ jl ∈ levels k, 2 ^ (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card + k + 1) *
          (4 * bQ n d k + 2) := by
      have hexp : 16 * (n + V) * P * (δ ^ 2 + δ * (4 * B + 4)) =
          16 * n * P * δ ^ 2 + 16 * n * P * δ * (4 * B) + 16 * n * P * δ * 4 +
            16 * V * P * (δ ^ 2 + δ * (4 * B + 4)) := by ring
      rw [hexp]
      omega
    calc (pm.cost : ℝ) ≤ ((16 * (n + V) * P * (δ ^ 2 + δ * (4 * B + 4)) + 16 * Kq ^ 2 + 64 +
        (2 * ∑ jl ∈ levels k, 2 ^ (jl.1 - 2 * jl.2) * (K jl.1 jl.2).card + k + 1) *
          (4 * bQ n d k + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = onceCost n d k Kq K := by
        unfold onceCost
        simp only [P, V, B, δ]
        push_cast
        ring

end BstLean.Part43
