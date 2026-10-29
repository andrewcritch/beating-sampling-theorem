import BstLean.Part49Prog

/-!
# Part 49, file 2: Option f for every `d_f ≤ d_M + 1`, every diagonal `θ`, every `m`, every `f`

Specification: `delegations/statements/p49-spec.md`. Report: `delegations/answers/p49-spec-opus.md`.

For `1 ≤ k = d_f ≤ d + 1`, `d = d_M ≥ 1`, every `n ≥ 2` (in particular every `n ≥ 100`), every `θ`
and every `ε > 0`, there are programs `pw` (from `θ` and the coefficients `M` of `m` to the weights)
and `pg` (from `f` and the weights to `g`), with the constants `0` and `1` only, such that for every
`M` and every `f = (f₀, T)` with symmetric `T`:
`|pg(f, pw(θ, M)) − B(θ, M, f)| ≤ (ε/20) · sd_{x∼D(θ)} f(m(x))`, `cost(pg) = 2 L49 < 𝔅(ε)`,
`cost(pw) ≤ Cpw49`, and for every `k' ≥ k0_49`, `cost(pw)/k' + cost(pg) < 𝔅(ε) = max(2P, 0.91P/ε²)`.

Mechanism: `pw` computes the moments of Part 43's surrogate `Q̃ = surrT n θ ε`, contracted with the
coefficients of `m`; `pg(f, pw(θ, M)) = B_{Q̃}(M)` exactly (`g_eq_BQ`); Part 43's `surr_bias` bounds
`|B_D − B_{Q̃}|` by `η_Q sd_D`, `η_Q ≤ ε/20`.

Build-time control (not charged): the argmin `i0` of `θ` and the truncation order `Kof43 (spread θ) ε`.
-/

namespace BstLean.Part49

open MeasureTheory BstLean.Cost
open BstLean.Part36 (CoefIdxD DD mapMD monoVal)
open BstLean.Part41 (Mono phiM phiSq mset wordOf Tens TSymm fval contr trL orbSize heavyCount Pn
  baseline levels kapQ muQ cQ IsSymmT glue)
open BstLean.Part43 (KeyF keys43 IsKey wKeyR BofQ varFQ surrT Kof43 bmin etaQ onceCost MomSpec43
  HR HKR)
open BstLean.Part40 (SphLaw SignSym)

variable {n d : ℕ}

/-! ## §1 Orbits (adapted from Part 43, `Part43GProg`) -/

lemma mset_wordOf {α : Type} [Inhabited α] (a : ℕ) (q : Multiset α)
    (hq : q.card = a) : mset (wordOf a q) = q := by
  subst a
  unfold mset wordOf
  rw [Fin.univ_val_map]
  have he : List.ofFn (fun t : Fin q.card => q.toList.getD t.val default) = q.toList := by
    have hh : q.toList.length = q.card := Multiset.length_toList q
    rw [← hh]
    simpa only [List.getD_eq_get, Fin.eta] using List.ofFn_get q.toList
  rw [he, Multiset.coe_toList]

lemma orbit_perm {α : Type} [Fintype α] {s : ℕ} (u w : Fin s → α)
    (h : mset u = mset w) : ∃ σ : Equiv.Perm (Fin s), w ∘ σ = u := by
  classical
  have hcard (a : α) : Fintype.card {t : Fin s // u t = a} =
      Fintype.card {t : Fin s // w t = a} := by
    have hh := congrArg (Multiset.count a) h
    simpa only [mset, Multiset.count_map, Multiset.countP_eq_card_filter,
      ← Finset.filter_val, Fintype.card_subtype, Finset.card_def, eq_comm] using hh
  let e (a : α) := Fintype.equivOfCardEq (hcard a)
  let σ := (Equiv.sigmaFiberEquiv u).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv w))
  refine ⟨σ, ?_⟩
  funext t
  exact (e (u t) ⟨t, rfl⟩).property

lemma prodX_mset {α : Type} [DecidableEq α] {s : ℕ} (w : Fin s → α) :
    (∏ t, MvPolynomial.X (w t) : MvPolynomial α ℝ) =
      MvPolynomial.monomial (mset w).toFinsupp 1 := by
  induction s with
  | zero => simp [mset, Multiset.toFinsupp_zero]
  | succ s ih =>
    have hm : mset w = mset (fun t : Fin s => w t.castSucc) + {w (Fin.last s)} := by
      simp only [mset, Fin.univ_val_map, List.ofFn_succ', List.concat_eq_append,
        ← Multiset.coe_add, Multiset.coe_singleton]
    rw [Fin.prod_univ_castSucc, ih, hm, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]

lemma orbit_card {α : Type} [Fintype α] [DecidableEq α] (s : ℕ) (q : Sym α s) :
    (((Finset.univ : Finset (Fin s → α)).filter (fun w => mset w = q.val)).card : ℝ) =
      orbSize q.val := by
  have hpoly : ((∑ a : α, MvPolynomial.X a : MvPolynomial α ℝ) ^ s) =
      ∑ w : Fin s → α, MvPolynomial.monomial (mset w).toFinsupp 1 := by
    rw [← Fin.prod_const, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact prodX_mset w
  have hh := congrArg (fun p : MvPolynomial α ℝ => p.coeff q.val.toFinsupp) hpoly
  have he : ∀ w : Fin s → α, (mset w).toFinsupp = q.val.toFinsupp ↔ mset w = q.val := by
    intro w
    exact Multiset.toFinsupp.injective.eq_iff
  have hn : q.val.toFinsupp.multinomial = orbSize q.val := by
    simp only [Finsupp.multinomial, Multiset.toFinsupp_sum_eq, Finsupp.prod,
      Multiset.toFinsupp_support, Multiset.toFinsupp_apply, orbSize]
  have hs : q.val.toFinsupp.sum (fun _ m => m) = s :=
    (Multiset.toFinsupp_sum_eq _).trans q.property
  simpa only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_sum_X_pow_of_fintype, Multiset.toFinsupp_sum_eq, q.property,
    hs, ite_true, he, hn, Finset.sum_boole] using hh.symm

/-- Group a sum over words by orbit (fiberwise form). -/
lemma sum_fiber_orbit {α : Type} [Fintype α] [DecidableEq α] (s : ℕ) (F : (Fin s → α) → ℝ) :
    ∑ w, F w = ∑ q : Sym α s, ∑ w ∈ Finset.univ.filter (fun w : Fin s → α => mset w = q.val), F w := by
  let f : (Fin s → α) → Sym α s := fun w => ⟨mset w, by simp [mset]⟩
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := f) (f := F) (by simp)]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr
  · ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  · intro _ _; rfl

lemma sum_by_orbit {α : Type} [Fintype α] [DecidableEq α] [Inhabited α]
    (s : ℕ) (F : (Fin s → α) → ℝ)
    (hF : ∀ u w, mset u = mset w → F u = F w) :
    ∑ w, F w = ∑ q : Sym α s, (orbSize q.val : ℝ) * F (wordOf s q.val) := by
  rw [sum_fiber_orbit]
  apply Finset.sum_congr rfl
  intro q _
  calc
    _ = ∑ w ∈ Finset.univ.filter (fun w => mset w = q.val), F (wordOf s q.val) := by
      apply Finset.sum_congr rfl
      intro w hw
      apply hF
      rw [(Finset.mem_filter.mp hw).2, mset_wordOf _ _ q.property]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, orbit_card]

lemma symm_of_perm {α : Type} [Fintype α] {s : ℕ} (F : (Fin s → α) → ℝ)
    (hF : ∀ (σ : Equiv.Perm (Fin s)) w, F (w ∘ σ) = F w) :
    ∀ u w, mset u = mset w → F u = F w := by
  intro u w h
  obtain ⟨σ, hσ⟩ := orbit_perm u w h
  rw [← hσ, hF]

lemma mset_comp_perm {α : Type} {s : ℕ} (w : Fin s → α) (σ : Equiv.Perm (Fin s)) :
    mset (w ∘ σ) = mset w := by
  unfold mset
  rw [← Multiset.map_map]
  congr 1
  have := Finset.map_univ_equiv σ
  have h2 := congrArg Finset.val this
  simpa [Finset.map_val] using h2

/-! ## §2 Continuity and integrability -/

lemma continuous_monoVal (s : Multiset (Fin n)) : Continuous (fun x : Fin n → ℝ => monoVal x s) := by
  unfold monoVal
  exact continuous_multiset_prod s (fun b _ => continuous_apply b)

lemma continuous_mapMD (M : CoefIdxD n d → ℝ) (a : Fin n) :
    Continuous (fun x => mapMD M x a) := by
  unfold mapMD
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro β _
  exact continuous_const.mul (continuous_monoVal _)

lemma sph_integrable {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ]
    (hs : ∀ᵐ x ∂μ, ∑ i, x i ^ 2 = 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

/-! ## §3 The weights and the exact identity for a law on the sphere -/

/-- `m(x)_p = Σ_u M_{p,u} φ_u(x)`. -/
lemma mapMD_eq (M : CoefIdxD n d → ℝ) (x : Fin n → ℝ) (p : Fin n) :
    mapMD M x p = ∑ u : Mono n d, M ⟨u.1, (u.2, p)⟩ * phiM x u := by
  unfold mapMD phiM
  rw [Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ β : Sym (Fin n) i,
    BstLean.Part36.coefD M i β p * monoVal x β.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro β _
  simp [BstLean.Part36.coefD, i.2]

/-- `H_μ(β) = E_μ ∏_t φ_{β_t}(x)`. -/
noncomputable def Hm (μ : Measure (Fin n → ℝ)) {j : ℕ} (β : Fin j → Mono n d) : ℝ :=
  ∫ x, ∏ t, phiM x (β t) ∂μ

/-- `G_s(β) = Σ_{a ∈ orbit s} ∏_t M_{β_t, a_t}`. -/
noncomputable def Gs (M : CoefIdxD n d → ℝ) {j : ℕ} (s : Sym (Fin n) j) (β : Fin j → Mono n d) : ℝ :=
  ∑ a ∈ orb s, ∏ t, M ⟨(β t).1, ((β t).2, a t)⟩

/-- The weight `W_μ(j, s) = Σ_{a ∈ orbit s} E_μ ∏_t m(x)_{a_t}`. -/
noncomputable def Wt (μ : Measure (Fin n → ℝ)) (M : CoefIdxD n d → ℝ) {j : ℕ} (s : Sym (Fin n) j) : ℝ :=
  ∑ a ∈ orb s, ∫ x, ∏ t, mapMD M x (a t) ∂μ

lemma Hm_perm (μ : Measure (Fin n → ℝ)) {j : ℕ} (σ : Equiv.Perm (Fin j)) (β : Fin j → Mono n d) :
    Hm μ (β ∘ σ) = Hm μ β := by
  unfold Hm
  congr 1
  funext x
  exact Equiv.prod_comp σ (fun t => phiM x (β t))

lemma Gs_perm (M : CoefIdxD n d → ℝ) {j : ℕ} (s : Sym (Fin n) j) (σ : Equiv.Perm (Fin j))
    (β : Fin j → Mono n d) : Gs M s (β ∘ σ) = Gs M s β := by
  classical
  unfold Gs
  apply Finset.sum_nbij' (fun a => a ∘ σ.symm) (fun a => a ∘ σ)
  · intro a ha
    simp only [orb, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [mset_comp_perm, ha]
  · intro a ha
    simp only [orb, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [mset_comp_perm, ha]
  · intro a _
    funext t; simp
  · intro a _
    funext t; simp
  · intro a _
    rw [← Equiv.prod_comp σ (fun t => M ⟨(β t).1, ((β t).2, (a ∘ σ.symm) t)⟩)]
    simp

/-- **The weight through the moments**: `W_μ(j, s) = Σ_q |q| H_μ(word q) G_s(word q)`. -/
lemma Wt_eq (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (M : CoefIdxD n d → ℝ) {j : ℕ}
    (s : Sym (Fin n) j) :
    Wt μ M s = ∑ q : Sym (Mono n d) j,
      ((orbSize q.1 : ℝ) * Hm μ (wordOf j q.1)) * Gs M s (wordOf j q.1) := by
  classical
  haveI := hμ.prob
  have hexp : ∀ (a : Fin j → Fin n) (x : Fin n → ℝ), ∏ t, mapMD M x (a t) =
      ∑ β : Fin j → Mono n d, (∏ t, M ⟨(β t).1, ((β t).2, a t)⟩) * ∏ t, phiM x (β t) := by
    intro a x
    simp only [mapMD_eq]
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.prod_mul_distrib]
  have hint : ∀ a : Fin j → Fin n, ∫ x, ∏ t, mapMD M x (a t) ∂μ =
      ∑ β : Fin j → Mono n d, (∏ t, M ⟨(β t).1, ((β t).2, a t)⟩) * Hm μ β := by
    intro a
    simp only [hexp]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro β _
      rw [integral_const_mul]
      rfl
    · intro β _
      apply Integrable.const_mul
      apply sph_integrable hμ.sphere
      exact continuous_finset_prod _ (fun t _ => continuous_monoVal _)
  unfold Wt
  simp only [hint]
  rw [Finset.sum_comm]
  have hF : ∀ β : Fin j → Mono n d, ∑ a ∈ orb s, (∏ t, M ⟨(β t).1, ((β t).2, a t)⟩) * Hm μ β =
      Hm μ β * Gs M s β := by
    intro β
    unfold Gs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp only [hF]
  rw [sum_by_orbit j (fun β => Hm μ β * Gs M s β)
    (symm_of_perm _ (fun σ w => by rw [Hm_perm, Gs_perm]))]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- **`B_μ` through the weights**, for symmetric `T` and a probability law on the sphere. -/
lemma BofQ_eq [Inhabited (Fin n)] (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (k : ℕ) (f0 : ℝ)
    (T : Tens n) (hT : TSymm k T) (M : CoefIdxD n d → ℝ) :
    BofQ μ k f0 T M = f0 + ∑ js ∈ F49 n k, T js.1 (wordOf js.1 js.2.1) * Wt μ M js.2 := by
  classical
  haveI := hμ.prob
  have hcont : ∀ (j : ℕ) (a : Fin j → Fin n), Continuous (fun x => ∏ t, mapMD M x (a t)) :=
    fun j a => continuous_finset_prod _ (fun t _ => continuous_mapMD M (a t))
  have hpt : ∀ x, fval k f0 T (mapMD M x) =
      f0 + ∑ j ∈ Finset.Icc 1 k, ∑ a : Fin j → Fin n, T j a * ∏ t, mapMD M x (a t) := by
    intro x; rfl
  unfold BofQ
  simp only [hpt]
  rw [integral_add (integrable_const _), integral_const, integral_finset_sum]
  rotate_left
  · intro j _
    exact integrable_finset_sum _ (fun a _ => (sph_integrable hμ.sphere (hcont j a)).const_mul _)
  · exact integrable_finset_sum _ (fun j _ =>
      integrable_finset_sum _ (fun a _ => (sph_integrable hμ.sphere (hcont j a)).const_mul _))
  simp only [probReal_univ, one_smul]
  congr 1
  have hj : ∀ j ∈ Finset.Icc 1 k, ∫ x, ∑ a : Fin j → Fin n, T j a * ∏ t, mapMD M x (a t) ∂μ =
      ∑ s : Sym (Fin n) j, T j (wordOf j s.1) * Wt μ M s := by
    intro j hj
    rw [integral_finset_sum _ (fun a _ => (sph_integrable hμ.sphere (hcont j a)).const_mul _)]
    simp only [integral_const_mul]
    rw [sum_fiber_orbit]
    apply Finset.sum_congr rfl
    intro s _
    unfold Wt
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : mset a = s.1 := (Finset.mem_filter.mp ha).2
    congr 1
    have hm : mset (wordOf j s.1) = mset a := by rw [ha', mset_wordOf _ _ s.2]
    obtain ⟨σ, hσ⟩ := orbit_perm (wordOf j s.1) a hm
    rw [← hσ]
    exact (hT j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 σ a).symm
  rw [Finset.sum_congr rfl hj]
  -- reindex `Σ_{j ∈ Icc 1 k} Σ_s` as a sum over `F49`
  rw [F49, Finset.sum_sigma, Finset.sum_filter]
  set g : ℕ → ℝ := fun j => if 1 ≤ j ∧ j ≤ k then
    ∑ s : Sym (Fin n) j, T j (wordOf j s.1) * Wt μ M s else 0 with hg
  have h1 : (∑ j ∈ Finset.range (k + 1), g j) = ∑ j ∈ Finset.Icc 1 k,
      ∑ s : Sym (Fin n) j, T j (wordOf j s.1) * Wt μ M s := by
    rw [hg, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [← h1, ← Fin.sum_univ_eq_sum_range g]
  apply Finset.sum_congr rfl
  intro j _
  have hjk : j.val ≤ k := Nat.lt_succ_iff.mp j.2
  by_cases h : 1 ≤ j.val
  · simp [hg, h, hjk]
  · simp [hg, h]

/-! ## §4 The moment weights of Part 43 at the keys `(j, 0, 0, q)` -/

lemma key49_mem {k : ℕ} (j : Fin (k + 1)) (hj : 1 ≤ j.val) (q : Sym (Mono n d) j) :
    key49 j q ∈ keys43 k (Kall n d) := by
  classical
  unfold keys43
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [key49, levels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_range]
    have := j.2
    omega
  · simp [key49]
  · simp [key49]
  · refine ⟨q.1, ?_, le_refl _⟩
    simp only [key49, Kall, if_true]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ q)

lemma glue_zero {ι : Type} (j : ℕ) (c : Fin 0 → ι) (w : Fin (j - 2 * 0) → ι) :
    glue j 0 c w = w := by
  funext t
  simp [glue]

lemma wKeyR_key49 (μ : Measure (Fin n → ℝ)) {k : ℕ} (j : Fin (k + 1)) (hj : 1 ≤ j.val)
    (q : Sym (Mono n d) j) :
    wKeyR μ (Kall n d) (key49 j q) = (orbSize q.1 : ℝ) * Hm μ (wordOf j q.1) := by
  classical
  have hne : ¬ (2 * 0 = j.val) := by omega
  have hkap : (kapQ n d j.val 0 : ℝ) = 1 := by
    simp [kapQ, cQ, Nat.factorial_ne_zero]
  have hmu : (muQ n d j.val 0 : ℝ) = 1 := by
    simp [muQ, cQ, Nat.factorial_ne_zero]
  have hmem : mset (wordOf j.val q.1) ∈ Kall n d j.val 0 := by
    rw [mset_wordOf _ _ q.2]
    simp only [Kall, if_true]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
  change (if 2 * 0 = j.val then _ else
      (kapQ n d j.val 0 : ℝ) * (muQ n d (j.val - 2 * 0) 0 : ℝ) * (orbSize q.1 : ℝ) *
        trL 0 (HKR μ (s := j.val - 2 * 0) (Kall n d j.val 0) 0) (wordOf _ q.1)) = _
  rw [if_neg hne]
  change (kapQ n d j.val 0 : ℝ) * (muQ n d j.val 0 : ℝ) * (orbSize q.1 : ℝ) *
      (∑ c : Fin 0 → Mono n d, HKR μ (s := j.val) (Kall n d j.val 0) 0
        (glue j.val 0 c (wordOf j.val q.1))) = _
  rw [hkap, hmu, Fintype.sum_unique, glue_zero]
  unfold HKR
  rw [if_pos hmem]
  unfold HR Hm
  simp

/-! ## §5 The weights computed by `pw49` -/

/-- The surrogate weights: `pw49 pm` returns `W_{Q̃}(j, s)` at every used index, whenever `pm` returns
Part 43's key weights of `Q̃` at the keys `(j, 0, 0, q)`. -/
lemma pw49_eval_Wt {k : ℕ} (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (pm : Prog (Fin n) (KeyF n d k)) (θ : Fin n → ℝ)
    (hpm : ∀ κ ∈ keys43 k (Kall n d), pm.eval θ κ = wKeyR μ (Kall n d) κ)
    (M : CoefIdxD n d → ℝ) (js : WIdx n k) (hjs : js ∈ F49 n k) :
    (pw49 pm).eval (Sum.elim θ M) js = Wt μ M js.2 := by
  have hj : 1 ≤ js.1.val := (mem_F49 js).mp hjs
  rw [pw49_eval pm θ M js hjs, Wt_eq μ hμ M js.2, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q _
  dsimp only
  rw [hpm _ (key49_mem js.1 hj q), wKeyR_key49 μ js.1 hj q, Gs, Finset.mul_sum]

/-- **Exactness for the surrogate**: `g = pg(f, pw(θ, M)) = B_μ(M)` for every `M` and every symmetric
`f`, with `μ` the law whose key weights `pm` returns. -/
theorem g_eq_BQ [Inhabited (Fin n)] {k : ℕ} (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (pm : Prog (Fin n) (KeyF n d k)) (θ : Fin n → ℝ)
    (hpm : ∀ κ ∈ keys43 k (Kall n d), pm.eval θ κ = wKeyR μ (Kall n d) κ)
    (M : CoefIdxD n d → ℝ) (f0 : ℝ) (T : Tens n) (hT : TSymm k T) :
    (pg49 n k).eval (inpG f0 T ((pw49 pm).eval (Sum.elim θ M))) () = BofQ μ k f0 T M := by
  rw [pg49_eval, BofQ_eq μ hμ k f0 T hT M]
  congr 1
  apply Finset.sum_congr rfl
  intro js hjs
  rw [pw49_eval_Wt μ hμ pm θ hpm M js hjs]

end BstLean.Part49
