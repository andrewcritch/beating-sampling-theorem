import BstLean.Part130All

/-!
# Part 132, item 2 (tools): compositions of `κ`, supporting lines, the perspective function

Role: `delegations/statements/p132-spec.md`. Paper source: `delegations/answers/onW4c-cx.md` §2
("Exact layer formulas and the perspective argument"), `onW4-opus-prover.md` T1, T2.

* `KGood G`: `G` is continuous, and on `[−1, 1]` it is nondecreasing, convex and 1-Lipschitz, with
  `G 1 = 1` and `G (−1) ≥ 0`. `kGood_kappa`, `KGood.comp_kappa`, `kGood_iterate`: `κ` and every
  composition `κ^{∘(j+1)}` are of this class.
* `KGood.support`: at every `t ∈ [−1, 1]` there is a supporting line `s ↦ a + b·s` of `G` with
  `0 ≤ a ≤ G 0`, `0 ≤ b ≤ 1` (the paper's `a = G − tG′`, `b = G′`; no derivative is used here).
* `persp G p c = p·G(c/p)`: the perspective function `L_G` (value `0` at `p = 0`).
  `persp_ge` (supporting plane), `persp_eq` (equality at the reference cosine), `persp_le`
  (the Lipschitz bound T2(3)(ii): `L_G(P) ≤ L_G(P̄) + G(0)|δp| + |δc|`).
* `nrm`, `cosv`, `psi G y y' = |y||y′|·G(cos(y, y′))`: the same for two vectors.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130

/-! ## The class of kernel functions -/

/-- The properties of `G = κ^{∘j}` that the perspective argument uses. -/
structure KGood (G : ℝ → ℝ) : Prop where
  cont : Continuous G
  mono : MonotoneOn G (Icc (-1) 1)
  conv : ConvexOn ℝ (Icc (-1) 1) G
  lip : ∀ {s t : ℝ}, -1 ≤ t → t ≤ s → s ≤ 1 → G s - G t ≤ s - t
  one : G 1 = 1
  nonneg : 0 ≤ G (-1)

theorem kGood_kappa : KGood kappa where
  cont := continuous_kappa
  mono := kappa_monotoneOn
  conv := kappa_convexOn
  lip := fun ht hts hs => (kappa_lipschitz ht hts hs).2
  one := kappa_one
  nonneg := by rw [kappa_neg_one]

lemma kappa_mem_Icc {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : kappa t ∈ Icc (-1 : ℝ) 1 := by
  have := kappa_mem ht.1 ht.2
  exact ⟨by linarith, this.2⟩

namespace KGood

variable {G : ℝ → ℝ}

lemma nonneg_on (hG : KGood G) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : 0 ≤ G t :=
  hG.nonneg.trans (hG.mono ⟨le_refl _, by norm_num⟩ ht ht.1)

lemma le_one (hG : KGood G) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : G t ≤ 1 := by
  have := hG.mono ht ⟨by norm_num, le_refl _⟩ ht.2
  rwa [hG.one] at this

lemma self_le (hG : KGood G) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : t ≤ G t := by
  have := hG.lip ht.1 ht.2 (le_refl 1)
  rw [hG.one] at this
  linarith

lemma zero_mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

/-- `G ∘ κ` is of the class if `G` is. -/
theorem comp_kappa (hG : KGood G) : KGood (G ∘ kappa) where
  cont := hG.cont.comp continuous_kappa
  mono := fun a ha b hb hab =>
    hG.mono (kappa_mem_Icc ha) (kappa_mem_Icc hb) (kappa_monotoneOn ha hb hab)
  conv := by
    refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
    have h1 := kappa_convexOn.2 hx hy ha hb hab
    have hmem : a • x + b • y ∈ Icc (-1 : ℝ) 1 := (convex_Icc (-1 : ℝ) 1) hx hy ha hb hab
    have hmem2 : a • kappa x + b • kappa y ∈ Icc (-1 : ℝ) 1 :=
      (convex_Icc (-1 : ℝ) 1) (kappa_mem_Icc hx) (kappa_mem_Icc hy) ha hb hab
    have h2 := hG.mono (kappa_mem_Icc hmem) hmem2 h1
    have h3 := hG.conv.2 (kappa_mem_Icc hx) (kappa_mem_Icc hy) ha hb hab
    exact h2.trans h3
  lip := fun {s t} ht hts hs => by
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨ht.trans hts, hs⟩
    have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨ht, hts.trans hs⟩
    have h1 := kappa_lipschitz ht hts hs
    have h2 := hG.lip (kappa_mem_Icc ht').1 (by linarith [h1.1]) (kappa_mem_Icc hs').2
    simp only [Function.comp]
    linarith [h1.2]
  one := by simp [Function.comp, kappa_one, hG.one]
  nonneg := by
    simp only [Function.comp, kappa_neg_one]
    exact hG.nonneg_on zero_mem

/-- **The supporting line.** At every `t ∈ [−1, 1]` there are `a, b` with `0 ≤ a ≤ G 0`,
`0 ≤ b ≤ 1`, `a + b·t = G t` and `a + b·s ≤ G s` on `[−1, 1]`. -/
theorem support (hG : KGood G) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ G 0 ∧ 0 ≤ b ∧ b ≤ 1 ∧ a + b * t = G t ∧
      ∀ s ∈ Icc (-1 : ℝ) 1, a + b * s ≤ G s := by
  -- first a slope `b`
  have key : ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 ∧ ∀ s ∈ Icc (-1 : ℝ) 1, G t + b * (s - t) ≤ G s := by
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · refine ⟨1, zero_le_one, le_refl _, fun s hs => ?_⟩
      subst h1
      have := hG.lip hs.1 hs.2 (le_refl 1)
      linarith
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · refine ⟨0, le_refl _, zero_le_one, fun s hs => ?_⟩
      have := hG.mono ht hs (h0 ▸ hs.1)
      linarith
    -- interior point: the supremum of the left slopes
    let S : Set ℝ := (fun s => (G t - G s) / (t - s)) '' Ico (-1) t
    have hne : S.Nonempty := ⟨_, ⟨-1, ⟨le_refl _, h0⟩, rfl⟩⟩
    have hle1 : ∀ x ∈ S, x ≤ 1 := by
      rintro x ⟨s, hs, rfl⟩
      have hpos : 0 < t - s := by linarith [hs.2]
      rw [div_le_one hpos]
      exact hG.lip hs.1 hs.2.le ht.2
    have hbdd : BddAbove S := ⟨1, hle1⟩
    refine ⟨sSup S, ?_, csSup_le hne hle1, fun s hs => ?_⟩
    · have hmem : (G t - G (-1)) / (t - (-1)) ∈ S := ⟨-1, ⟨le_refl _, h0⟩, rfl⟩
      refine le_trans ?_ (le_csSup hbdd hmem)
      have := hG.mono ⟨le_refl _, by norm_num⟩ ht ht.1
      exact div_nonneg (by linarith) (by linarith)
    · rcases lt_trichotomy s t with hst | hst | hst
      · have hmem : (G t - G s) / (t - s) ∈ S := ⟨s, ⟨hs.1, hst⟩, rfl⟩
        have h2 := le_csSup hbdd hmem
        have hpos : 0 < t - s := by linarith
        rw [div_le_iff₀ hpos] at h2
        nlinarith
      · subst hst; simp
      · have h2 : sSup S ≤ (G s - G t) / (s - t) := by
          refine csSup_le hne ?_
          rintro x ⟨r, hr, rfl⟩
          exact hG.conv.slope_mono_adjacent ⟨hr.1, (hr.2.trans h1).le⟩ hs hr.2 hst
        have hpos : 0 < s - t := by linarith
        rw [le_div_iff₀ hpos] at h2
        linarith
  obtain ⟨b, hb0, hb1, hb⟩ := key
  refine ⟨G t - b * t, b, ?_, ?_, hb0, hb1, by ring, fun s hs => ?_⟩
  · rcases le_total t 0 with h | h
    · have := hG.nonneg_on ht
      nlinarith
    · have := hG.self_le ht
      nlinarith
  · have := hb 0 zero_mem
    linarith
  · have := hb s hs
    linarith

end KGood

/-- Every composition `κ^{∘(j+1)}` is of the class. -/
theorem kGood_iterate (j : ℕ) : KGood (kappa^[j + 1]) := by
  induction j with
  | zero => simpa using kGood_kappa
  | succ j ih =>
    rw [Function.iterate_succ]
    exact ih.comp_kappa

/-! ## The perspective function `L_G(p, c) = p·G(c/p)` -/

/-- The perspective function `L_G(p, c) = p·G(c/p)` (value `0` at `p = 0`). -/
noncomputable def persp (G : ℝ → ℝ) (p c : ℝ) : ℝ := p * G (c / p)

lemma div_mem_Icc {p c : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p) : c / p ∈ Icc (-1 : ℝ) 1 := by
  rcases eq_or_lt_of_le hp with h | h
  · rw [← h]; simp
  · rw [abs_le] at hc
    exact ⟨by rw [le_div_iff₀ h]; linarith, by rw [div_le_iff₀ h]; linarith⟩

lemma persp_nonneg {G : ℝ → ℝ} (hG : KGood G) {p c : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p) :
    0 ≤ persp G p c :=
  mul_nonneg hp (hG.nonneg_on (div_mem_Icc hp hc))

/-- **The supporting plane**: `a·p + b·c ≤ L_G(p, c)` on the cone, for a supporting line
`s ↦ a + b·s` of `G`. -/
lemma persp_ge {G : ℝ → ℝ} {a b : ℝ} (hab : ∀ s ∈ Icc (-1 : ℝ) 1, a + b * s ≤ G s) {p c : ℝ}
    (hp : 0 ≤ p) (hc : |c| ≤ p) : a * p + b * c ≤ persp G p c := by
  unfold persp
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    have : c = 0 := abs_nonpos_iff.mp hc
    simp [this]
  · have h1 := hab _ (div_mem_Icc hp hc)
    have h2 := mul_le_mul_of_nonneg_left h1 hp
    have h3 : p * (a + b * (c / p)) = a * p + b * c := by field_simp
    linarith

/-- Equality in the supporting plane at the reference cosine `t`: if `c = t·p`. -/
lemma persp_eq {G : ℝ → ℝ} {a b t : ℝ} (heq : a + b * t = G t) {p c : ℝ} (hc : c = t * p) :
    persp G p c = a * p + b * c := by
  unfold persp
  rcases eq_or_ne p 0 with h | h
  · subst h; simp [hc]
  · have : c / p = t := by rw [hc]; field_simp
    rw [this, ← heq, hc]; ring

/-- **The Lipschitz bound of the perspective** (paper T2(3)(ii)):
`L_G(p, c) ≤ L_G(p̄, c̄) + G(0)·|p − p̄| + |c − c̄|` for two points of the cone. -/
lemma persp_le {G : ℝ → ℝ} (hG : KGood G) {p c p' c' : ℝ} (hp : 0 ≤ p) (hc : |c| ≤ p)
    (hp' : 0 ≤ p') (hc' : |c'| ≤ p') :
    persp G p c ≤ persp G p' c' + G 0 * |p - p'| + |c - c'| := by
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support (div_mem_Icc hp hc)
  have h1 : persp G p c = a * p + b * c := by
    rcases eq_or_lt_of_le hp with h | h
    · subst h
      have : c = 0 := abs_nonpos_iff.mp hc
      simp [persp, this]
    · exact persp_eq heq (by field_simp)
  have h2 := persp_ge hab hp' hc'
  have h3 : a * (p - p') ≤ G 0 * |p - p'| := by
    calc a * (p - p') ≤ a * |p - p'| := mul_le_mul_of_nonneg_left (le_abs_self _) ha0
      _ ≤ G 0 * |p - p'| := mul_le_mul_of_nonneg_right ha1 (abs_nonneg _)
  have h4 : b * (c - c') ≤ |c - c'| := by
    calc b * (c - c') ≤ b * |c - c'| := mul_le_mul_of_nonneg_left (le_abs_self _) hb0
      _ ≤ 1 * |c - c'| := mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ = |c - c'| := one_mul _
  nlinarith

/-! ## Two vectors -/

variable {ι : Type*} [Fintype ι]

/-- `|y| = √(Σ y_i²)`. -/
noncomputable def nrm (y : ι → ℝ) : ℝ := Real.sqrt (normSq y)

/-- The cosine of two vectors, `⟨y, y′⟩/(|y||y′|)`; `0` if one of them is `0`. -/
noncomputable def cosv (y y' : ι → ℝ) : ℝ := dotp y y' / (nrm y * nrm y')

/-- `Ψ_G(y, y′) = |y||y′|·G(cos(y, y′)) = L_G(|y||y′|, ⟨y, y′⟩)`. -/
noncomputable def psi (G : ℝ → ℝ) (y y' : ι → ℝ) : ℝ := nrm y * nrm y' * G (cosv y y')

lemma psi_eq_persp (G : ℝ → ℝ) (y y' : ι → ℝ) :
    psi G y y' = persp G (nrm y * nrm y') (dotp y y') := rfl

lemma kernelPhi_eq_psi (h h' : ι → ℝ) : kernelPhi h h' = psi kappa h h' := rfl

lemma nrm_nonneg (y : ι → ℝ) : 0 ≤ nrm y := Real.sqrt_nonneg _

lemma nrm_sq (y : ι → ℝ) : nrm y ^ 2 = normSq y := Real.sq_sqrt (normSq_nonneg y)

lemma nrm_mul_self (y : ι → ℝ) : nrm y * nrm y = normSq y := Real.mul_self_sqrt (normSq_nonneg y)

lemma nrm_mul_nonneg (y y' : ι → ℝ) : 0 ≤ nrm y * nrm y' :=
  mul_nonneg (nrm_nonneg y) (nrm_nonneg y')

/-- Cauchy–Schwarz: `|⟨y, y′⟩| ≤ |y||y′|`. -/
lemma abs_dotp_le_nrm (y y' : ι → ℝ) : |dotp y y'| ≤ nrm y * nrm y' := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y y'
  have h2 : dotp y y' ^ 2 ≤ (nrm y * nrm y') ^ 2 := by
    rw [mul_pow, nrm_sq, nrm_sq]
    exact h
  exact (sq_le_sq₀ (abs_nonneg _) (nrm_mul_nonneg y y')).mp (by rwa [sq_abs])

lemma cosv_mem (y y' : ι → ℝ) : cosv y y' ∈ Icc (-1 : ℝ) 1 :=
  div_mem_Icc (nrm_mul_nonneg y y') (abs_dotp_le_nrm y y')

lemma dotp_eq_cosv_mul (y y' : ι → ℝ) : dotp y y' = cosv y y' * (nrm y * nrm y') := by
  unfold cosv
  rcases eq_or_ne (nrm y * nrm y') 0 with h | h
  · have := abs_dotp_le_nrm y y'
    rw [h] at this
    rw [abs_nonpos_iff.mp this, h]; simp
  · rw [div_mul_cancel₀ _ h]

lemma nrm_mul_le (y y' : ι → ℝ) : nrm y * nrm y' ≤ (normSq y + normSq y') / 2 := by
  have h1 := nrm_sq y
  have h2 := nrm_sq y'
  nlinarith [sq_nonneg (nrm y - nrm y')]

lemma psi_nonneg {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) : 0 ≤ psi G y y' :=
  mul_nonneg (nrm_mul_nonneg y y') (hG.nonneg_on (cosv_mem y y'))

lemma psi_le_nrm {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) : psi G y y' ≤ nrm y * nrm y' := by
  have := hG.le_one (cosv_mem y y')
  unfold psi
  nlinarith [nrm_mul_nonneg y y']

/-- The supporting plane for two vectors. -/
lemma psi_ge {G : ℝ → ℝ} {a b : ℝ} (hab : ∀ s ∈ Icc (-1 : ℝ) 1, a + b * s ≤ G s)
    (y y' : ι → ℝ) : a * (nrm y * nrm y') + b * dotp y y' ≤ psi G y y' :=
  persp_ge hab (nrm_mul_nonneg y y') (abs_dotp_le_nrm y y')

/-- The Lipschitz bound for two vectors against a reference point `(p̄, c̄)` of the cone. -/
lemma psi_le {G : ℝ → ℝ} (hG : KGood G) (y y' : ι → ℝ) {p' c' : ℝ} (hp' : 0 ≤ p')
    (hc' : |c'| ≤ p') :
    psi G y y' ≤ persp G p' c' + G 0 * |nrm y * nrm y' - p'| + |dotp y y' - c'| :=
  persp_le hG (nrm_mul_nonneg y y') (abs_dotp_le_nrm y y') hp' hc'

lemma continuous_nrm : Continuous (nrm : (ι → ℝ) → ℝ) :=
  Real.continuous_sqrt.comp continuous_normSq

lemma measurable_cosv :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => cosv p.1 p.2) := by
  unfold cosv
  exact continuous_dotp.measurable.div
    (((continuous_nrm.comp continuous_fst).mul (continuous_nrm.comp continuous_snd)).measurable)

lemma measurable_psi {G : ℝ → ℝ} (hG : Continuous G) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => psi G p.1 p.2) := by
  unfold psi
  exact (((continuous_nrm.comp continuous_fst).mul
    (continuous_nrm.comp continuous_snd)).measurable).mul (hG.measurable.comp measurable_cosv)

lemma nrm_of_normSq_one {x : ι → ℝ} (hx : normSq x = 1) : nrm x = 1 := by
  unfold nrm; rw [hx, Real.sqrt_one]

/-- For unit vectors, `Ψ_G(x, x′) = G(⟨x, x′⟩)`. -/
lemma psi_unit (G : ℝ → ℝ) {x x' : ι → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    psi G x x' = G (dotp x x') := by
  unfold psi cosv
  rw [nrm_of_normSq_one hx, nrm_of_normSq_one hx']
  simp

end BstLean.Part132

open BstLean.Part132 in
#print axioms KGood.support
open BstLean.Part132 in
#print axioms kGood_iterate
open BstLean.Part132 in
#print axioms persp_le
